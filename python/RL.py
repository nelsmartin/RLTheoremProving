import leanclient as lc
import torch
import json
import numpy as np
from torch import nn
from torch.distributions import Categorical
import matplotlib.pyplot as plt

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
# ULTRA-SIMPLE APPROACH: Direct Policy Table
# ============================================================================

class SimplePolicyTable(nn.Module):
    """
    Learns a direct mapping: step_number -> action
    For 2-step problems, this is the simplest approach.
    """
    def __init__(self, max_steps=2):
        super().__init__()
        # For each step, output: [rule_logit_0, rule_logit_1, i_logits..., j_logits...]
        # Rule: 2 options (mul_assoc vs mul_comm)
        # Variables: 4 options each for i and j
        
        self.step_0_rule = nn.Parameter(torch.zeros(2))
        self.step_0_i = nn.Parameter(torch.zeros(4))
        self.step_0_j = nn.Parameter(torch.zeros(4))
        
        self.step_1_rule = nn.Parameter(torch.zeros(2))
        self.step_1_i = nn.Parameter(torch.zeros(4))
        self.step_1_j = nn.Parameter(torch.zeros(4))
        
        # Add temperature parameter for exploration
        self.temperature = 1.0
    
    def forward(self, step):
        if step == 0:
            return self.step_0_rule, self.step_0_i, self.step_0_j
        else:
            return self.step_1_rule, self.step_1_i, self.step_1_j
    
    def set_temperature(self, temp):
        self.temperature = temp


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


def sample_action(policy, step, num_vars, epsilon=0.0):
    """Sample action from policy table"""
    if np.random.random() < epsilon:
        # Random exploration
        rule = np.random.randint(0, 2)
        i = np.random.randint(0, max(1, num_vars))
        j = np.random.randint(0, max(1, num_vars))
        action = (rule, i, j)
        
        rule_logits, i_logits, j_logits = policy(step)
        rule_dist = Categorical(logits=rule_logits / policy.temperature)
        i_dist = Categorical(logits=i_logits[:num_vars] / policy.temperature)
        j_dist = Categorical(logits=j_logits[:num_vars] / policy.temperature)
        
        logp = rule_dist.log_prob(torch.tensor(rule))
        logp = logp + i_dist.log_prob(torch.tensor(i))
        logp = logp + j_dist.log_prob(torch.tensor(j))
        
        entropy = rule_dist.entropy() + i_dist.entropy() + j_dist.entropy()
        
        return action, logp, entropy
    
    # Policy sampling
    rule_logits, i_logits, j_logits = policy(step)
    
    rule_dist = Categorical(logits=rule_logits / policy.temperature)
    rule = rule_dist.sample()
    
    i_dist = Categorical(logits=i_logits[:num_vars] / policy.temperature)
    i = i_dist.sample()
    
    j_dist = Categorical(logits=j_logits[:num_vars] / policy.temperature)
    j = j_dist.sample()
    
    logp = rule_dist.log_prob(rule) + i_dist.log_prob(i) + j_dist.log_prob(j)
    entropy = rule_dist.entropy() + i_dist.entropy() + j_dist.entropy()
    
    return (rule.item(), i.item(), j.item()), logp, entropy


def run_episode(policy, max_steps=2, epsilon=0.0):
    """Run one episode"""
    log_probs = []
    entropies = []
    
    for step in range(max_steps):
        goal = get_goal_str()
        if goal is None:
            return True, log_probs, entropies  # Success!
            
        ldecls = get_ldecls()
        num_vars = len(ldecls) if ldecls else 3
        
        action, logp, entropy = sample_action(policy, step, num_vars, epsilon)
        
        log_probs.append(logp)
        entropies.append(entropy)
        
        apply_action(action, ldecls)
        
        if is_done():
            return True, log_probs, entropies
    
    # Failed to complete in max_steps
    return False, log_probs, entropies


def compute_loss(log_probs, entropies, success, entropy_coef=0.1):
    """
    Simple REINFORCE loss:
    - If success: maximize log_probs (reward = 1)
    - If failure: minimize log_probs (reward = 0)
    - Always maximize entropy
    """
    if len(log_probs) == 0:
        return torch.tensor(0.0)
    
    log_probs = torch.stack(log_probs)
    entropies = torch.stack(entropies)
    
    if success:
        # Maximize probability of actions that led to success
        policy_loss = -log_probs.sum()
    else:
        # Minimize probability of actions that led to failure
        policy_loss = log_probs.sum()
    
    # Always encourage exploration
    entropy_bonus = -entropies.mean()
    
    return policy_loss + entropy_coef * entropy_bonus


# ============================================================================
# TRAINING
# ============================================================================

policy = SimplePolicyTable(max_steps=2)
optimizer = torch.optim.Adam(policy.parameters(), lr=0.1)  # High LR for fast learning

returns_per_episode = []
losses_per_episode = []
entropies_per_episode = []

print("=" * 100)
print("ULTRA-SIMPLE POLICY TABLE LEARNING")
print("=" * 100)
print("Approach: Learn a direct step -> action mapping")
print("No complex neural networks, no value functions, just pure policy learning")
print("=" * 100)
print(f"\n{'Episode':<8} {'Success':<8} {'Loss':<10} {'Entropy':<8} {'Success%':<10} {'Temp':<8}")
print("-" * 100)

success_count = 0
window = 50

for episode in range(500):
    sfc.open_file()
    
    # Aggressive epsilon decay
    epsilon = max(0.1, 0.8 - 0.7 * (episode / 300))
    
    # Temperature annealing for controlled exploration
    temperature = max(0.5, 2.0 - 1.5 * (episode / 300))
    policy.set_temperature(temperature)
    
    # Run episode
    success, log_probs, entropies = run_episode(policy, max_steps=2, epsilon=epsilon)
    
    if success:
        success_count += 1
        returns_per_episode.append(1.0)
    else:
        returns_per_episode.append(0.0)
    
    # Compute loss
    loss = compute_loss(log_probs, entropies, success, entropy_coef=0.1)
    
    # Update policy
    optimizer.zero_grad()
    loss.backward()
    torch.nn.utils.clip_grad_norm_(policy.parameters(), 1.0)
    optimizer.step()
    
    losses_per_episode.append(loss.item())
    
    avg_entropy = sum(e.item() for e in entropies) / len(entropies) if entropies else 0.0
    entropies_per_episode.append(avg_entropy)
    
    if episode % 10 == 0:
        recent_success = sum(returns_per_episode[-window:])
        success_rate = recent_success / min(len(returns_per_episode), window) * 100
        print(f"{episode:<8} {'✓' if success else '✗':<8} {loss.item():<10.3f} "
              f"{avg_entropy:<8.3f} {success_rate:<10.1f}% {temperature:<8.2f}")

# ============================================================================
# FINAL EVALUATION
# ============================================================================

print("\n" + "=" * 100)
print("FINAL EVALUATION (100 episodes, greedy policy)")
print("=" * 100)

policy.set_temperature(0.1)  # Very low temperature = nearly deterministic
eval_successes = 0

for _ in range(100):
    sfc.open_file()
    success, _, _ = run_episode(policy, max_steps=2, epsilon=0.0)
    if success:
        eval_successes += 1

print(f"Greedy policy success rate: {eval_successes}%")
print(f"Total training successes: {success_count}")

# Print learned policy
print("\n" + "=" * 100)
print("LEARNED POLICY")
print("=" * 100)

with torch.no_grad():
    rule_0, i_0, j_0 = policy(0)
    rule_1, i_1, j_1 = policy(1)
    
    print("Step 0:")
    print(f"  Rule probabilities: mul_assoc={torch.softmax(rule_0, 0)[0]:.3f}, mul_comm={torch.softmax(rule_0, 0)[1]:.3f}")
    print(f"  Variable i: {torch.softmax(i_0, 0).numpy()}")
    print(f"  Variable j: {torch.softmax(j_0, 0).numpy()}")
    
    print("\nStep 1:")
    print(f"  Rule probabilities: mul_assoc={torch.softmax(rule_1, 0)[0]:.3f}, mul_comm={torch.softmax(rule_1, 0)[1]:.3f}")
    print(f"  Variable i: {torch.softmax(i_1, 0).numpy()}")
    print(f"  Variable j: {torch.softmax(j_1, 0).numpy()}")

print("=" * 100)

# ============================================================================
# PLOTTING
# ============================================================================

fig, axes = plt.subplots(2, 2, figsize=(14, 10))

# Success over time
axes[0, 0].scatter(range(len(returns_per_episode)), returns_per_episode, 
                   alpha=0.5, s=10, c=['green' if r > 0.5 else 'red' for r in returns_per_episode])
if len(returns_per_episode) >= window:
    ma = np.convolve(returns_per_episode, np.ones(window)/window, mode='valid')
    axes[0, 0].plot(range(window-1, len(returns_per_episode)), ma, 'b-', linewidth=2)
axes[0, 0].set_title('Episode Outcomes (green=success)')
axes[0, 0].set_xlabel('Episode')
axes[0, 0].set_ylabel('Success')
axes[0, 0].grid(True, alpha=0.3)

# Success rate
success_rate = []
for i in range(0, len(returns_per_episode), 10):
    batch = returns_per_episode[i:min(i+window, len(returns_per_episode))]
    success_rate.append(sum(batch) / len(batch) * 100)
axes[0, 1].plot(range(0, len(returns_per_episode), 10), success_rate, 
                'g-', linewidth=2, marker='o')
axes[0, 1].axhline(y=eval_successes, color='r', linestyle='--', 
                   label=f'Final: {eval_successes}%')
axes[0, 1].set_title('Success Rate Over Training')
axes[0, 1].set_xlabel('Episode')
axes[0, 1].set_ylabel('Success Rate (%)')
axes[0, 1].legend()
axes[0, 1].grid(True, alpha=0.3)
axes[0, 1].set_ylim(0, 105)

# Loss
axes[1, 0].plot(losses_per_episode, alpha=0.5)
if len(losses_per_episode) >= 20:
    ma = np.convolve(losses_per_episode, np.ones(20)/20, mode='valid')
    axes[1, 0].plot(range(19, len(losses_per_episode)), ma, 'r-', linewidth=2)
axes[1, 0].set_title('Training Loss')
axes[1, 0].set_xlabel('Episode')
axes[1, 0].set_ylabel('Loss')
axes[1, 0].grid(True, alpha=0.3)

# Entropy
axes[1, 1].plot(entropies_per_episode, 'purple', alpha=0.5)
if len(entropies_per_episode) >= 20:
    ma = np.convolve(entropies_per_episode, np.ones(20)/20, mode='valid')
    axes[1, 1].plot(range(19, len(entropies_per_episode)), ma, 'purple', linewidth=2)
axes[1, 1].set_title('Policy Entropy (Exploration)')
axes[1, 1].set_xlabel('Episode')
axes[1, 1].set_ylabel('Entropy')
axes[1, 1].grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('simple_policy_table.png', dpi=150)
plt.show()

print("\nPlot saved as 'simple_policy_table.png'")