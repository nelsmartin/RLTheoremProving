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
    if ldecls_json:
        for ldecl in ldecls_json:
            ldecls.append(ldecl['userName'])
    return ldecls


# ============================================================================
# ENHANCED STATE ENCODER - Task-Specific Features
# ============================================================================

class GoalEncoder:
    """
    Semantic encoder optimized for multiplication commutativity/associativity tasks
    """
    def __init__(self, feature_dim=64):
        self.feature_dim = feature_dim
        
    def encode(self, goal_str: str, ldecls: list) -> torch.Tensor:
        """
        Extract task-specific features from goal string.
        """
        features = np.zeros(self.feature_dim, dtype=np.float32)
        
        if not goal_str:
            return torch.tensor(features)
        
        # === BASIC FEATURES (0-9) ===
        features[0] = min(len(goal_str) / 50.0, 1.0)  # Length
        features[1] = goal_str.count('*') / 5.0        # Multiplications
        features[2] = goal_str.count('(') / 3.0        # Parentheses (associativity)
        features[3] = goal_str.count('=') / 2.0        # Equals
        
        # === VARIABLE FEATURES (10-19) ===
        # Track which variables appear and in what order
        var_list = ['a', 'b', 'c', 'd']
        for i, var in enumerate(var_list):
            if var in goal_str.lower():
                features[10 + i] = goal_str.lower().count(var) / 3.0
        
        # === STRUCTURAL PATTERNS (20-39) ===
        # These are KEY for the specific task
        
        # Pattern: "a * b * c" (left-associated, needs assoc)
        if re.search(r'[a-z]\s*\*\s*[a-z]\s*\*\s*[a-z]', goal_str):
            features[20] = 1.0
        
        # Pattern: "a * (b * c)" (right-associated)
        if re.search(r'[a-z]\s*\*\s*\(\s*[a-z]\s*\*\s*[a-z]\s*\)', goal_str):
            features[21] = 1.0
        
        # Pattern: "a * (c * b)" (target form)
        if re.search(r'[a-z]\s*\*\s*\(\s*c\s*\*\s*b\s*\)', goal_str):
            features[22] = 1.0
        
        # Pattern: "a * (b * c)" (intermediate form)
        if re.search(r'[a-z]\s*\*\s*\(\s*b\s*\*\s*c\s*\)', goal_str):
            features[23] = 1.0
        
        # Check if goal sides are equal (done!)
        if '=' in goal_str:
            parts = goal_str.split('=')
            if len(parts) == 2:
                left = parts[0].strip().replace(' ', '')
                right = parts[1].strip().replace(' ', '')
                if left == right:
                    features[24] = 1.0  # Goal is trivially true
        
        # === STEP INDICATOR (40-41) ===
        # Estimate which step we're on based on structure
        
        # If no parentheses on left, probably step 0 (need mul_assoc)
        left_side = goal_str.split('=')[0] if '=' in goal_str else goal_str
        if '(' not in left_side and '*' in left_side:
            features[40] = 1.0  # Likely need mul_assoc
        
        # If parentheses exist but b and c are in wrong order, need mul_comm
        if re.search(r'\(\s*b\s*\*\s*c\s*\)', goal_str):
            features[41] = 1.0  # Likely need mul_comm b c
        
        # === VARIABLE ORDERING (42-51) ===
        # For mul_comm, we need to know which variables to swap
        
        # Extract variable positions in the goal
        vars_in_order = re.findall(r'\b[a-z]\b', goal_str.lower())
        
        # Encode first few variable positions
        for i, var in enumerate(vars_in_order[:10]):
            if var in ['a', 'b', 'c', 'd']:
                var_idx = ord(var) - ord('a')
                features[42 + i] = var_idx / 3.0  # Normalize to [0, 1]
        
        # === LDECLS CONTEXT (52-55) ===
        # Information about available local declarations
        if ldecls:
            features[52] = len(ldecls) / 4.0
            for i, decl in enumerate(ldecls[:4]):
                if decl.lower() in ['a', 'b', 'c', 'd']:
                    features[53 + (ord(decl.lower()) - ord('a'))] = 1.0
        
        # === N-GRAM FEATURES (56-63) ===
        # Compact representation of goal structure
        for i in range(min(8, len(goal_str) - 2)):
            trigram = goal_str[i:i+3]
            trigram_hash = hash(trigram) % 8
            features[56 + trigram_hash] = min(features[56 + trigram_hash] + 0.3, 1.0)
        
        return torch.tensor(features)


encoder = GoalEncoder(feature_dim=64)

def encode_goal(goal: str, ldecls: list = None) -> torch.Tensor:
    """Wrapper for encoder"""
    if ldecls is None:
        ldecls = []
    return encoder.encode(goal, ldecls)


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
        if i < len(ldecls) and j < len(ldecls):
            a = ldecls[i]
            b = ldecls[j]
            tactic = f"my_rw [Nat.mul_comm {a} {b}]"
        else:
            # Fallback if indices are invalid
            tactic = "my_rw [Nat.mul_comm]"
    
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

def compute_reward(prev_goal, current_goal, done, step):
    """Shaped reward optimized for 2-step task"""
    if done:
        # HUGE reward for success - make this very attractive
        return 1000.0
    
    # Step-based shaped rewards
    if step == 0:
        # After first step, reward if we added parentheses (mul_assoc worked)
        if current_goal and prev_goal:
            if '(' in current_goal and '(' not in prev_goal:
                return 10.0  # Good! Applied mul_assoc
            elif current_goal == prev_goal:
                return -5.0  # Bad! No change
    
    elif step == 1:
        # After second step, check if we're closer to solution
        if current_goal and 'c * b' in current_goal:
            return 50.0  # Very good! We have c * b now
    
    # Small penalty for each step
    return -0.1


class ActorCriticNet(nn.Module):
    def __init__(self, state_dim, max_vars):
        super().__init__()
        # Deeper network for better memorization
        self.shared = nn.Sequential(
            nn.Linear(state_dim, 128),
            nn.ReLU(),
            nn.Linear(128, 128),
            nn.ReLU(),
            nn.Linear(128, 64),
            nn.ReLU(),
        )
        
        self.rule_head = nn.Linear(64, 2)
        self.i_head = nn.Linear(64, max_vars)
        self.j_head = nn.Linear(64, max_vars)
        self.value_head = nn.Linear(64, 1)
    
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
            i = np.random.randint(0, num_vars) if num_vars > 0 else 0
            j = np.random.randint(0, num_vars) if num_vars > 0 else 0
            action = (1, i, j)
        
        rule_logits, i_logits, j_logits, value = net(state)
        
        rule_dist = Categorical(logits=rule_logits / temperature)
        logp = rule_dist.log_prob(torch.tensor(rule))
        entropy = rule_dist.entropy()
        
        if rule == 1 and num_vars > 0:
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

    if num_vars > 0:
        i_logits = mask_logits(i_logits, num_vars)
        j_logits = mask_logits(j_logits, num_vars)

        i_dist = Categorical(logits=i_logits / temperature)
        j_dist = Categorical(logits=j_logits / temperature)

        i = i_dist.sample()
        j = j_dist.sample()

        logp = logp + i_dist.log_prob(i) + j_dist.log_prob(j)
        entropy = entropy + i_dist.entropy() + j_dist.entropy()

        return (1, i.item(), j.item()), logp, value, entropy
    else:
        return (1, 0, 0), logp, value, entropy


def run_episode(net, max_steps=2, epsilon=0.0, temperature=1.0):
    log_probs = []
    rewards = []
    values = []
    entropies = []
    
    prev_goal = get_goal_str()
    
    for step in range(max_steps):
        goal = get_goal_str()
        ldecls = get_ldecls()
        num_vars = len(ldecls) if ldecls else 0

        state = encode_goal(goal, ldecls)
        action, logp, value, entropy = sample_action_with_entropy(
            net, state, num_vars, epsilon, temperature
        )

        apply_action(action, ldecls)

        done = is_done()
        current_goal = get_goal_str()
        reward = compute_reward(prev_goal, current_goal, done, step)

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


def compute_returns(rewards, gamma=0.95):  # Higher gamma for short episodes
    returns = []
    G = 0
    for r in reversed(rewards.tolist()):
        G = r + gamma * G
        returns.insert(0, G)
    return torch.tensor(returns, dtype=torch.float32)


def actor_critic_loss_with_adaptive_entropy(log_probs, values, rewards, entropies, 
                                             gamma=0.95, base_entropy_coef=0.2,
                                             target_entropy=0.5):
    returns = compute_returns(rewards, gamma)
    
    advantages = returns - values.detach()
    
    if len(advantages) > 1:
        advantages = (advantages - advantages.mean()) / (advantages.std() + 1e-8)
    
    actor_loss = -(log_probs * advantages).mean()
    critic_loss = nn.functional.mse_loss(values, returns)
    entropy = entropies.mean()
    
    # Adaptive entropy - but lower target for memorization task
    entropy_deficit = max(0, target_entropy - entropy.item())
    adaptive_coef = base_entropy_coef + 1.0 * entropy_deficit
    
    total_loss = actor_loss + 0.5 * critic_loss - adaptive_coef * entropy
    
    return total_loss, actor_loss.item(), critic_loss.item(), entropy.item(), adaptive_coef


def get_epsilon(episode, start_eps=0.5, end_eps=0.01, decay_episodes=1000):
    """Aggressive epsilon decay - we want to memorize, not explore forever"""
    if episode >= decay_episodes:
        return end_eps
    return start_eps - (start_eps - end_eps) * (episode / decay_episodes)


def get_temperature(episode, start_temp=1.5, end_temp=0.8, decay_episodes=800):
    """Lower final temperature for more deterministic policy"""
    if episode >= decay_episodes:
        return end_temp
    return start_temp - (start_temp - end_temp) * (episode / decay_episodes)


# ============================================================================
# TRAINING
# ============================================================================

STATE_DIM = 64
net = ActorCriticNet(STATE_DIM, max_vars=4)
optimizer = torch.optim.Adam(net.parameters(), lr=1e-3)  # Higher LR for faster learning

returns_per_episode = []
losses_per_episode = []
actor_losses_per_episode = []
critic_losses_per_episode = []
entropies_per_episode = []
epsilons_per_episode = []
temperatures_per_episode = []
entropy_coefs_per_episode = []
success_episodes = []
actions_taken = []  # Track what actions lead to success

print("=" * 100)
print("TRAINING FOR 2-STEP MEMORIZATION TASK")
print("=" * 100)
print("Task: a * b * c = a * (c * b)")
print("Solution: [mul_assoc] → [mul_comm b c]")
print(f"State dimension: {STATE_DIM} (task-optimized features)")
print("=" * 100)
print(f"\n{'Episode':<8} {'Return':<10} {'Loss':<8} {'Entropy':<8} {'Eps':<6} {'Temp':<6} {'Success%':<10}")
print("-" * 100)

consecutive_low_entropy = 0
ENTROPY_THRESHOLD = 0.05  # Lower threshold for memorization
RESTART_THRESHOLD = 100

for episode in range(2000):
    sfc.open_file()

    epsilon = get_epsilon(episode)
    temperature = get_temperature(episode)
    
    log_probs, values, rewards, entropies = run_episode(net, max_steps=2, epsilon=epsilon, temperature=temperature)
    
    loss, actor_loss, critic_loss, entropy, entropy_coef = actor_critic_loss_with_adaptive_entropy(
        log_probs, values, rewards, entropies, gamma=0.95, base_entropy_coef=0.2, target_entropy=0.5
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
    
    if total_return > 500:  # Success
        success_episodes.append(episode)

    if entropy < ENTROPY_THRESHOLD:
        consecutive_low_entropy += 1
    else:
        consecutive_low_entropy = 0
    
    if consecutive_low_entropy >= RESTART_THRESHOLD:
        print(f"\n*** ENTROPY COLLAPSE AT EPISODE {episode} - REINITIALIZING ***\n")
        net = ActorCriticNet(STATE_DIM, max_vars=4)
        optimizer = torch.optim.Adam(net.parameters(), lr=1e-3)
        consecutive_low_entropy = 0

    if episode % 10 == 0:
        recent_successes = sum(1 for r in returns_per_episode[-100:] if r > 500)
        success_rate = recent_successes / min(len(returns_per_episode), 100) * 100
        print(f"{episode:<8} {total_return:<10.1f} {loss.item():<8.3f} "
              f"{entropy:<8.3f} {epsilon:<6.3f} {temperature:<6.3f} {success_rate:<10.1f}%")

# ============================================================================
# FINAL EVALUATION
# ============================================================================

print("\n" + "=" * 100)
print("FINAL EVALUATION (100 episodes with epsilon=0)")
print("=" * 100)

eval_successes = 0
for _ in range(100):
    sfc.open_file()
    _, _, rewards, _ = run_episode(net, max_steps=2, epsilon=0.0, temperature=1.0)
    if rewards.sum().item() > 500:
        eval_successes += 1

print(f"Evaluation success rate: {eval_successes}% (with greedy policy)")
print("=" * 100)

# ============================================================================
# PLOTTING
# ============================================================================

fig = plt.figure(figsize=(16, 10))
episodes = np.arange(len(returns_per_episode))
window = 50

# 1. Returns
ax1 = plt.subplot(2, 3, 1)
colors = ['green' if r > 500 else 'red' for r in returns_per_episode]
ax1.scatter(episodes, returns_per_episode, alpha=0.5, s=10, c=colors)
if len(returns_per_episode) >= window:
    ma = np.convolve(returns_per_episode, np.ones(window)/window, mode='valid')
    ax1.plot(episodes[window-1:], ma, 'b-', linewidth=2)
ax1.axhline(y=500, color='orange', linestyle='--', label='Success threshold')
ax1.set_xlabel('Episode')
ax1.set_ylabel('Return')
ax1.set_title('Episode Returns')
ax1.legend()
ax1.grid(True, alpha=0.3)

# 2. Success Rate
ax2 = plt.subplot(2, 3, 2)
success_rate = []
for i in range(0, len(returns_per_episode), window):
    batch = returns_per_episode[i:i+window]
    success_rate.append(sum(1 for r in batch if r > 500) / len(batch) * 100)
ax2.plot(np.arange(0, len(returns_per_episode), window), success_rate, 'g-', linewidth=2, marker='o')
ax2.axhline(y=eval_successes, color='red', linestyle='--', label=f'Final: {eval_successes}%')
ax2.set_xlabel('Episode')
ax2.set_ylabel('Success Rate (%)')
ax2.set_title('Success Rate Over Training')
ax2.legend()
ax2.grid(True, alpha=0.3)
ax2.set_ylim(0, 105)

# 3. Loss
ax3 = plt.subplot(2, 3, 3)
ax3.plot(episodes, losses_per_episode, alpha=0.3)
if len(losses_per_episode) >= window:
    ma = np.convolve(losses_per_episode, np.ones(window)/window, mode='valid')
    ax3.plot(episodes[window-1:], ma, 'r-', linewidth=2)
ax3.set_xlabel('Episode')
ax3.set_ylabel('Loss')
ax3.set_title('Training Loss')
ax3.grid(True, alpha=0.3)

# 4. Entropy
ax4 = plt.subplot(2, 3, 4)
ax4.plot(episodes, entropies_per_episode, 'purple', alpha=0.5)
if len(entropies_per_episode) >= window:
    ma = np.convolve(entropies_per_episode, np.ones(window)/window, mode='valid')
    ax4.plot(episodes[window-1:], ma, 'purple', linewidth=2)
ax4.axhline(y=0.5, color='g', linestyle='--', alpha=0.5, label='Target')
ax4.set_xlabel('Episode')
ax4.set_ylabel('Entropy')
ax4.set_title('Policy Entropy')
ax4.legend()
ax4.grid(True, alpha=0.3)

# 5. Epsilon and Temperature
ax5 = plt.subplot(2, 3, 5)
ax5.plot(episodes, epsilons_per_episode, 'brown', label='Epsilon')
ax5_twin = ax5.twinx()
ax5_twin.plot(episodes, temperatures_per_episode, 'teal', label='Temperature')
ax5.set_xlabel('Episode')
ax5.set_ylabel('Epsilon', color='brown')
ax5_twin.set_ylabel('Temperature', color='teal')
ax5.set_title('Exploration Decay')
ax5.legend(loc='upper left')
ax5_twin.legend(loc='upper right')
ax5.grid(True, alpha=0.3)

# 6. Summary
ax6 = plt.subplot(2, 3, 6)
ax6.axis('off')
final_success = sum(1 for r in returns_per_episode[-100:] if r > 500)
summary = f"""
MEMORIZATION TASK RESULTS

Task: a * b * c = a * (c * b)
Expected: ~100% success (2 deterministic steps)

Training Performance:
• Final 100-ep success: {final_success}%
• Evaluation success: {eval_successes}%
• Total successes: {len(success_episodes)}/{len(returns_per_episode)}

Convergence:
• Episodes to 50% success: {next((i*window for i, sr in enumerate(success_rate) if sr >= 50), 'N/A')}
• Episodes to 90% success: {next((i*window for i, sr in enumerate(success_rate) if sr >= 90), 'N/A')}

Status: {'✓ SOLVED' if eval_successes >= 90 else '⚠ NEEDS MORE TRAINING' if eval_successes >= 50 else '✗ NOT LEARNING'}
"""
ax6.text(0.1, 0.5, summary, fontsize=10, family='monospace',
         verticalalignment='center', bbox=dict(boxstyle='round', facecolor='lightblue' if eval_successes >= 90 else 'lightyellow'))

plt.tight_layout()
plt.savefig('memorization_task_results.png', dpi=150)
plt.show()

print("\nPlot saved as 'memorization_task_results.png'")