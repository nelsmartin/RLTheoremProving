import leanclient as lc
import torch
import json
import numpy as np
from torch import nn
from torch.distributions import Categorical
import matplotlib.pyplot as plt
import re
from collections import Counter

PROJECT_PATH = "/Users/nelsmartin/Lean/RL"
client = lc.LeanLSPClient(PROJECT_PATH)
file_path = "RL/RLTest.lean"
sfc = client.create_file_client(file_path)

sfc.open_file()

def read_printjson_output():
    diagnostics = sfc.get_diagnostics().diagnostics
    goal = None
    ldecls = None
    for d in diagnostics:
        msg = d.get("message", "")
        if msg.startswith("@@GOAL_JSON@@"):
            json_str = msg[len("@@GOAL_JSON@@"):].strip()
            goal = json.loads(json_str)
        elif msg.startswith("@@LDECL_JSON@@"):
            json_str = msg[len("@@LDECL_JSON@@"):].strip()
            ldecls = json.loads(json_str)
    return goal, ldecls

def get_goal_str():
    goal, _ = read_printjson_output()
    if not goal:
        return None
    return goal['goal'].split('⊢ ')[1]

def get_ldecls():
    ldecls = []
    _, ldecls_json = read_printjson_output()
    for ldecl in ldecls_json:
        ldecls.append(ldecl['userName'])
    return ldecls


# ============================================================================
# IMPROVED STATE REPRESENTATION
# ============================================================================

class GoalEncoder:
    """
    Semantic encoder for Lean goals that captures mathematical structure
    instead of raw characters.
    """
    def __init__(self, feature_dim=128):
        self.feature_dim = feature_dim
        
    def encode(self, goal_str: str) -> torch.Tensor:
        """
        Extract semantic features from goal string.
        Returns a fixed-size feature vector.
        """
        features = np.zeros(self.feature_dim, dtype=np.float32)
        
        if not goal_str:
            return torch.tensor(features)
        
        # === STRUCTURAL FEATURES (0-19) ===
        
        # Length features (normalized)
        features[0] = min(len(goal_str) / 100.0, 1.0)
        features[1] = goal_str.count(' ') / 20.0  # Number of tokens (rough)
        
        # Operator counts (normalized)
        features[2] = min(goal_str.count('*') / 10.0, 1.0)  # Multiplications
        features[3] = min(goal_str.count('+') / 10.0, 1.0)  # Additions
        features[4] = min(goal_str.count('=') / 5.0, 1.0)   # Equals
        features[5] = min(goal_str.count('(') / 10.0, 1.0)  # Parentheses depth
        features[6] = min(goal_str.count('[') / 5.0, 1.0)   # Brackets
        
        # === VARIABLE FEATURES (20-39) ===
        
        # Extract variable names (single letters or short names)
        variables = re.findall(r'\b[a-z]\b', goal_str.lower())
        var_counts = Counter(variables)
        
        features[20] = min(len(var_counts) / 5.0, 1.0)  # Unique variable count
        features[21] = min(len(variables) / 20.0, 1.0)  # Total variable occurrences
        
        # Most common variables (one-hot-ish encoding)
        var_to_idx = {'a': 22, 'b': 23, 'c': 24, 'd': 25, 'x': 26, 
                      'y': 27, 'z': 28, 'n': 29, 'm': 30, 'k': 31}
        for var, idx in var_to_idx.items():
            if var in var_counts:
                features[idx] = min(var_counts[var] / 5.0, 1.0)
        
        # === PATTERN FEATURES (40-79) ===
        
        # Common mathematical patterns
        patterns = [
            r'\* \(',         # Multiplication before parenthesis
            r'\) \*',         # Multiplication after parenthesis
            r'\d+ \*',        # Number times something
            r'\* \d+',        # Something times number
            r'Nat\.mul',      # Explicit multiplication
            r'Nat\.add',      # Explicit addition
            r'mul_assoc',     # Associativity
            r'mul_comm',      # Commutativity
            r'add_assoc',
            r'add_comm',
            r'\( \w+ \* \w+ \)',  # Simple products in parens
        ]
        
        for i, pattern in enumerate(patterns):
            if i + 40 < self.feature_dim:
                matches = len(re.findall(pattern, goal_str))
                features[40 + i] = min(matches / 3.0, 1.0)
        
        # === N-GRAM FEATURES (80-127) ===
        
        # Character bigrams and trigrams for capturing local structure
        # Hash them to fixed positions
        for i in range(len(goal_str) - 1):
            if i + 1 < len(goal_str):
                # Bigram hash
                bigram_hash = (ord(goal_str[i]) * 256 + ord(goal_str[i+1])) % 32
                features[80 + bigram_hash] = min(features[80 + bigram_hash] + 0.2, 1.0)
        
        # Trigrams for even more context
        for i in range(len(goal_str) - 2):
            if i + 2 < len(goal_str):
                trigram_hash = (ord(goal_str[i]) * 256 * 256 + 
                              ord(goal_str[i+1]) * 256 + 
                              ord(goal_str[i+2])) % 16
                features[112 + trigram_hash] = min(features[112 + trigram_hash] + 0.2, 1.0)
        
        return torch.tensor(features)


# Initialize encoder
encoder = GoalEncoder(feature_dim=128)

def encode_goal(goal: str) -> torch.Tensor:
    """Wrapper for encoder"""
    return encoder.encode(goal)


# ============================================================================
# NETWORK AND TRAINING CODE
# ============================================================================

def mask_logits(logits, valid_count):
    if valid_count < logits.shape[0]:
        logits = logits.clone()
        logits[valid_count:] = -1e9
    return logits

def apply_action(action, ldecls):
    rule, i, j = action
    if rule == 0:
        tactic = "my_rw [Nat.mul_assoc]"
    else:
        a = ldecls[i]
        b = ldecls[j]
        tactic = f"my_rw [Nat.mul_comm {a} {b}]"
    
    content = sfc.get_file_content()
    lines = content.split("\n")
    
    print_idx = None
    for idx in reversed(range(len(lines))):
        if lines[idx].strip() == "printJSON":
            print_idx = idx
            break
    
    if print_idx is None:
        raise RuntimeError("printJSON not found in file")
    
    indent = lines[print_idx][:len(lines[print_idx]) - len(lines[print_idx].lstrip())]
    new_lines = (
        lines[:print_idx]
        + [f"{indent}{tactic}", f"{indent}printJSON"]
        + lines[print_idx + 1:]
    )
    new_content = "\n".join(new_lines)
    
    change = lc.DocumentContentChange(
        text=new_content,
        start=[0, 0],
        end=[len(lines) + 5, 0],
    )
    sfc.update_file([change])

def is_done():
    return get_goal_str() is None

def compute_reward(prev_goal, current_goal, done):
    """Shaped reward function that gives intermediate feedback"""
    if done:
        return 100.0  # Large reward for success
    
    # Reward for making progress (simplification)
    if current_goal and prev_goal:
        len_diff = len(prev_goal) - len(current_goal)
        if len_diff > 0:
            return 0.5  # Positive reward for simplification
        elif len_diff < 0:
            return -0.2  # Penalty for making goal more complex
    
    return -0.01  # Small step penalty


class ActorCriticNet(nn.Module):
    def __init__(self, state_dim, max_vars):
        super().__init__()
        # Larger network for richer state representation
        self.shared = nn.Sequential(
            nn.Linear(state_dim, 256),
            nn.ReLU(),
            nn.Dropout(0.1),
            nn.Linear(256, 256),
            nn.ReLU(),
            nn.Dropout(0.1),
            nn.Linear(256, 128),
            nn.ReLU(),
        )
        
        self.rule_head = nn.Linear(128, 2)
        self.i_head = nn.Linear(128, max_vars)
        self.j_head = nn.Linear(128, max_vars)
        self.value_head = nn.Linear(128, 1)
    
    def forward(self, x):
        h = self.shared(x)
        return (
            self.rule_head(h),
            self.i_head(h),
            self.j_head(h),
            self.value_head(h)
        )


def sample_action_with_entropy(net, state, num_vars, epsilon=0.0, temperature=1.0):
    if np.random.random() < epsilon:
        rule = np.random.randint(0, 2)
        if rule == 0:
            action = (0, None, None)
        else:
            i = np.random.randint(0, num_vars)
            j = np.random.randint(0, num_vars)
            action = (1, i, j)
        
        rule_logits, i_logits, j_logits, value = net(state)
        
        rule_dist = Categorical(logits=rule_logits / temperature)
        logp = rule_dist.log_prob(torch.tensor(rule))
        entropy = rule_dist.entropy()
        
        if rule == 1:
            i_logits = mask_logits(i_logits, num_vars)
            j_logits = mask_logits(j_logits, num_vars)
            i_dist = Categorical(logits=i_logits / temperature)
            j_dist = Categorical(logits=j_logits / temperature)
            logp = logp + i_dist.log_prob(torch.tensor(i)) + j_dist.log_prob(torch.tensor(j))
            entropy = entropy + i_dist.entropy() + j_dist.entropy()
        
        return action, logp, value, entropy
    
    rule_logits, i_logits, j_logits, value = net(state)

    rule_dist = Categorical(logits=rule_logits / temperature)
    rule = rule_dist.sample()
    logp = rule_dist.log_prob(rule)
    entropy = rule_dist.entropy()

    if rule.item() == 0:
        return (0, None, None), logp, value, entropy

    i_logits = mask_logits(i_logits, num_vars)
    j_logits = mask_logits(j_logits, num_vars)

    i_dist = Categorical(logits=i_logits / temperature)
    j_dist = Categorical(logits=j_logits / temperature)

    i = i_dist.sample()
    j = j_dist.sample()

    logp = logp + i_dist.log_prob(i) + j_dist.log_prob(j)
    entropy = entropy + i_dist.entropy() + j_dist.entropy()

    return (1, i.item(), j.item()), logp, value, entropy


def run_episode(net, max_steps=2, epsilon=0.0, temperature=1.0):
    log_probs = []
    rewards = []
    values = []
    entropies = []
    
    prev_goal = get_goal_str()
    
    for step in range(max_steps):
        goal = get_goal_str()
        ldecls = get_ldecls()
        num_vars = len(ldecls)

        state = encode_goal(goal)
        action, logp, value, entropy = sample_action_with_entropy(
            net, state, num_vars, epsilon, temperature
        )

        apply_action(action, ldecls)

        done = is_done()
        current_goal = get_goal_str()
        reward = compute_reward(prev_goal, current_goal, done)

        log_probs.append(logp)
        values.append(value)
        rewards.append(reward)
        entropies.append(entropy)
        
        prev_goal = current_goal
        
        if done:
            break
    
    log_probs = torch.stack(log_probs)
    values = torch.cat(values)
    rewards = torch.tensor(rewards, dtype=torch.float32)
    entropies = torch.stack(entropies)
    
    return log_probs, values, rewards, entropies


def compute_returns(rewards, gamma=0.99):
    returns = []
    G = 0
    for r in reversed(rewards.tolist()):
        G = r + gamma * G
        returns.insert(0, G)
    return torch.tensor(returns, dtype=torch.float32)


def actor_critic_loss_with_adaptive_entropy(log_probs, values, rewards, entropies, 
                                             gamma=0.99, base_entropy_coef=0.3,
                                             target_entropy=0.5):
    returns = compute_returns(rewards, gamma)
    
    advantages = returns - values.detach()
    
    if len(advantages) > 1:
        advantages = (advantages - advantages.mean()) / (advantages.std() + 1e-8)
    
    actor_loss = -(log_probs * advantages).mean()
    critic_loss = nn.functional.mse_loss(values, returns)
    entropy = entropies.mean()
    
    entropy_deficit = max(0, target_entropy - entropy.item())
    adaptive_coef = base_entropy_coef + 2.0 * entropy_deficit
    
    total_loss = actor_loss + 0.5 * critic_loss - adaptive_coef * entropy
    
    return total_loss, actor_loss.item(), critic_loss.item(), entropy.item(), adaptive_coef


def get_epsilon(episode, start_eps=0.4, end_eps=0.1, decay_episodes=1500):
    if episode >= decay_episodes:
        return end_eps
    return start_eps - (start_eps - end_eps) * (episode / decay_episodes)


def get_temperature(episode, start_temp=1.5, end_temp=1.0, decay_episodes=1200):
    if episode >= decay_episodes:
        return end_temp
    return start_temp - (start_temp - end_temp) * (episode / decay_episodes)


# ============================================================================
# TRAINING
# ============================================================================

STATE_DIM = 128  # Semantic feature dimension
net = ActorCriticNet(STATE_DIM, max_vars=4)
optimizer = torch.optim.Adam(net.parameters(), lr=5e-4)

returns_per_episode = []
losses_per_episode = []
actor_losses_per_episode = []
critic_losses_per_episode = []
entropies_per_episode = []
epsilons_per_episode = []
temperatures_per_episode = []
entropy_coefs_per_episode = []
success_episodes = []

print("=" * 100)
print("TRAINING WITH IMPROVED SEMANTIC STATE REPRESENTATION")
print("=" * 100)
print(f"State dimension: {STATE_DIM} (semantic features)")
print(f"Feature breakdown:")
print(f"  - Structural features (0-19): length, operators, parentheses")
print(f"  - Variable features (20-39): variable counts and occurrences")
print(f"  - Pattern features (40-79): mathematical patterns (mul_assoc, mul_comm, etc.)")
print(f"  - N-gram features (80-127): bigrams and trigrams for local structure")
print("=" * 100)
print(f"\n{'Episode':<8} {'Return':<8} {'Loss':<8} {'Actor':<8} {'Critic':<8} {'Entropy':<8} {'EntCoef':<8} {'Eps':<8} {'Temp':<8}")
print("-" * 100)

consecutive_low_entropy = 0
ENTROPY_THRESHOLD = 0.1
RESTART_THRESHOLD = 50

for episode in range(3000):  # Extended training
    sfc.open_file()

    epsilon = get_epsilon(episode)
    temperature = get_temperature(episode)
    
    log_probs, values, rewards, entropies = run_episode(net, epsilon=epsilon, temperature=temperature)
    
    loss, actor_loss, critic_loss, entropy, entropy_coef = actor_critic_loss_with_adaptive_entropy(
        log_probs, values, rewards, entropies, base_entropy_coef=0.3, target_entropy=0.5
    )

    optimizer.zero_grad()
    loss.backward()
    torch.nn.utils.clip_grad_norm_(net.parameters(), 1.0)
    optimizer.step()

    total_return = rewards.sum().item()
    returns_per_episode.append(total_return)
    losses_per_episode.append(loss.item())
    actor_losses_per_episode.append(actor_loss)
    critic_losses_per_episode.append(critic_loss)
    entropies_per_episode.append(entropy)
    epsilons_per_episode.append(epsilon)
    temperatures_per_episode.append(temperature)
    entropy_coefs_per_episode.append(entropy_coef)
    
    if total_return > 50:  # Success
        success_episodes.append(episode)

    if entropy < ENTROPY_THRESHOLD:
        consecutive_low_entropy += 1
    else:
        consecutive_low_entropy = 0
    
    if consecutive_low_entropy >= RESTART_THRESHOLD:
        print(f"\n*** ENTROPY COLLAPSE AT EPISODE {episode} - REINITIALIZING ***\n")
        net = ActorCriticNet(STATE_DIM, max_vars=4)
        optimizer = torch.optim.Adam(net.parameters(), lr=5e-4)
        consecutive_low_entropy = 0

    if episode % 10 == 0:
        success_rate = sum(1 for r in returns_per_episode[-100:] if r > 50) / min(len(returns_per_episode), 100) * 100
        print(f"{episode:<8} {total_return:<8.3f} {loss.item():<8.3f} "
              f"{actor_loss:<8.3f} {critic_loss:<8.3f} {entropy:<8.3f} "
              f"{entropy_coef:<8.3f} {epsilon:<8.3f} {temperature:<8.3f}  "
              f"[Success rate: {success_rate:.1f}%]")

# ============================================================================
# ANALYSIS AND PLOTTING
# ============================================================================

print("\n" + "=" * 100)
print("TRAINING COMPLETE")
print("=" * 100)

final_success_rate = sum(1 for r in returns_per_episode[-100:] if r > 50) / min(len(returns_per_episode), 100) * 100
total_successes = sum(1 for r in returns_per_episode if r > 50)

print(f"Final 100-episode success rate: {final_success_rate:.1f}%")
print(f"Total successful episodes: {total_successes} / {len(returns_per_episode)} ({total_successes/len(returns_per_episode)*100:.1f}%)")
print(f"Final entropy: {entropies_per_episode[-1]:.4f}")
print(f"Entropy stayed above threshold: {'YES ✓' if min(entropies_per_episode) > ENTROPY_THRESHOLD else 'NO ✗'}")
print("=" * 100)

# Enhanced plotting
fig = plt.figure(figsize=(18, 12))
episodes = np.arange(len(returns_per_episode))
window = 50

# 1. Returns with success rate
ax1 = plt.subplot(3, 3, 1)
ax1.scatter(episodes, returns_per_episode, alpha=0.3, s=5, c=['green' if r > 50 else 'blue' for r in returns_per_episode])
if len(returns_per_episode) >= window:
    ma = np.convolve(returns_per_episode, np.ones(window)/window, mode='valid')
    ax1.plot(episodes[window-1:], ma, 'r-', linewidth=2, label=f'{window}-ep MA')
ax1.set_xlabel('Episode')
ax1.set_ylabel('Return')
ax1.set_title('Episode Returns (green = success)')
ax1.legend()
ax1.grid(True, alpha=0.3)

ax1_twin = ax1.twinx()
success_rate = []
for i in range(0, len(returns_per_episode), window):
    batch = returns_per_episode[i:i+window]
    success_rate.append(sum(1 for r in batch if r > 50) / len(batch) * 100)
ax1_twin.plot(np.arange(0, len(returns_per_episode), window), 
              success_rate, 'g--', linewidth=2, alpha=0.7)
ax1_twin.set_ylabel('Success Rate (%)', color='g')
ax1_twin.tick_params(axis='y', labelcolor='g')

# 2. Total Loss
ax2 = plt.subplot(3, 3, 2)
ax2.plot(episodes, losses_per_episode, alpha=0.5)
if len(losses_per_episode) >= window:
    ma_loss = np.convolve(losses_per_episode, np.ones(window)/window, mode='valid')
    ax2.plot(episodes[window-1:], ma_loss, 'r-', linewidth=2)
ax2.set_xlabel('Episode')
ax2.set_ylabel('Loss')
ax2.set_title('Total Loss')
ax2.grid(True, alpha=0.3)

# 3. Actor vs Critic
ax3 = plt.subplot(3, 3, 3)
if len(actor_losses_per_episode) >= window:
    ma_actor = np.convolve(actor_losses_per_episode, np.ones(window)/window, mode='valid')
    ma_critic = np.convolve(critic_losses_per_episode, np.ones(window)/window, mode='valid')
    ax3.plot(episodes[window-1:], ma_actor, 'b-', linewidth=2, label='Actor')
    ax3.plot(episodes[window-1:], ma_critic, 'orange', linewidth=2, label='Critic')
ax3.set_xlabel('Episode')
ax3.set_ylabel('Loss')
ax3.set_title('Actor vs Critic Loss')
ax3.legend()
ax3.grid(True, alpha=0.3)

# 4. Entropy
ax4 = plt.subplot(3, 3, 4)
ax4.plot(episodes, entropies_per_episode, 'purple', alpha=0.5)
if len(entropies_per_episode) >= window:
    ma_entropy = np.convolve(entropies_per_episode, np.ones(window)/window, mode='valid')
    ax4.plot(episodes[window-1:], ma_entropy, 'purple', linewidth=2)
ax4.axhline(y=0.5, color='g', linestyle='--', alpha=0.7, label='Target (0.5)')
ax4.axhline(y=0.1, color='r', linestyle='--', alpha=0.7, label='Danger Zone')
ax4.set_xlabel('Episode')
ax4.set_ylabel('Entropy')
ax4.set_title('Policy Entropy')
ax4.legend()
ax4.grid(True, alpha=0.3)
ax4.set_ylim(bottom=0)

# 5. Success Rate Over Time
ax5 = plt.subplot(3, 3, 5)
ax5.plot(np.arange(0, len(returns_per_episode), window), 
         success_rate, 'g-', linewidth=2, marker='o')
ax5.set_xlabel('Episode')
ax5.set_ylabel('Success Rate (%)')
ax5.set_title('Success Rate over Training')
ax5.grid(True, alpha=0.3)

# 6. Epsilon and Temperature
ax6 = plt.subplot(3, 3, 6)
ax6.plot(episodes, epsilons_per_episode, 'brown', linewidth=2, label='Epsilon')
ax6_twin = ax6.twinx()
ax6_twin.plot(episodes, temperatures_per_episode, 'teal', linewidth=2, label='Temperature')
ax6.set_xlabel('Episode')
ax6.set_ylabel('Epsilon', color='brown')
ax6_twin.set_ylabel('Temperature', color='teal')
ax6.set_title('Exploration Parameters')
ax6.grid(True, alpha=0.3)
ax6.legend(loc='upper left')
ax6_twin.legend(loc='upper right')

# 7. Adaptive Entropy Coefficient
ax7 = plt.subplot(3, 3, 7)
ax7.plot(episodes, entropy_coefs_per_episode, 'magenta', linewidth=2)
ax7.set_xlabel('Episode')
ax7.set_ylabel('Entropy Coefficient')
ax7.set_title('Adaptive Entropy Regularization Strength')
ax7.grid(True, alpha=0.3)

# 8. Success Distribution
ax8 = plt.subplot(3, 3, 8)
if success_episodes:
    ax8.hist(success_episodes, bins=30, color='green', alpha=0.7, edgecolor='black')
    ax8.set_xlabel('Episode')
    ax8.set_ylabel('Count')
    ax8.set_title(f'Distribution of Successful Episodes (n={len(success_episodes)})')
    ax8.grid(True, alpha=0.3)
else:
    ax8.text(0.5, 0.5, 'No successes yet', ha='center', va='center', fontsize=14)
    ax8.set_title('Distribution of Successful Episodes')

# 9. Summary Stats
ax9 = plt.subplot(3, 3, 9)
ax9.axis('off')
summary_text = f"""
FINAL STATISTICS

State Representation:
• Semantic features: {STATE_DIM}D
• Character encoding: NO

Performance:
• Final success rate: {final_success_rate:.1f}%
• Total successes: {total_successes}
• Best 100-ep rate: {max(success_rate) if success_rate else 0:.1f}%

Health Metrics:
• Final entropy: {entropies_per_episode[-1]:.3f}
• Min entropy: {min(entropies_per_episode):.3f}
• Avg entropy: {np.mean(entropies_per_episode):.3f}

Status: {'✓ HEALTHY' if min(entropies_per_episode) > 0.1 else '✗ COLLAPSED'}
"""
ax9.text(0.1, 0.5, summary_text, fontsize=11, family='monospace',
         verticalalignment='center', bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

plt.tight_layout()
plt.savefig('semantic_encoding_training.png', dpi=150, bbox_inches='tight')
plt.show()

print("\nPlot saved as 'semantic_encoding_training.png'")