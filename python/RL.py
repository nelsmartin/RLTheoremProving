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
MAX_LEN = 32  # or 512

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

def get_goal_str(): # do this from lean, please
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
   

def encode_goal(goal: str, max_len=MAX_LEN):
    arr = np.zeros(max_len, dtype=np.float32)
    for i, ch in enumerate(goal[:max_len]):
        arr[i] = ord(ch) / 127.0  # normalize to [0,1]
    return torch.tensor(arr)


class PolicyNet(nn.Module):
    def __init__(self, state_dim, max_vars):
        super().__init__()
        self.shared = nn.Sequential(
            nn.Linear(state_dim, 512),
            nn.ReLU(),
            nn.Linear(512, 256),
            nn.ReLU(),
        )

        self.rule_head = nn.Linear(256, 2)
        self.i_head = nn.Linear(256, max_vars)
        self.j_head = nn.Linear(256, max_vars)

    def forward(self, x):
        h = self.shared(x)
        return (
            self.rule_head(h),
            self.i_head(h),
            self.j_head(h),
        )

def mask_logits(logits, valid_count):
    if valid_count < logits.shape[0]:
        logits = logits.clone()
        logits[valid_count:] = -1e9
    return logits

def sample_action(net, state, num_vars):
    rule_logits, i_logits, j_logits = net(state)

    rule_dist = Categorical(logits=rule_logits)
    rule = rule_dist.sample()
    logp = rule_dist.log_prob(rule)

    if rule.item() == 0:
        return (0, None, None), logp

    i_logits = mask_logits(i_logits, num_vars)
    j_logits = mask_logits(j_logits, num_vars)

    i_dist = Categorical(logits=i_logits)
    j_dist = Categorical(logits=j_logits)

    i = i_dist.sample()
    j = j_dist.sample()

    logp = logp + i_dist.log_prob(i) + j_dist.log_prob(j)

    return (1, i.item(), j.item()), logp


def apply_action(action, ldecls):
    rule, i, j = action

    if rule == 0:
        tactic = "my_rw [Nat.mul_assoc]"
    else:
        a = ldecls[i]
        b = ldecls[j]
        tactic = f"my_rw [Nat.mul_comm {a} {b}]"

    # --- 1. Read file ---
    content = sfc.get_file_content()
    lines = content.split("\n")

    # --- 2. Find last `printJSON` ---
    print_idx = None
    for idx in reversed(range(len(lines))):
        if lines[idx].strip() == "printJSON":
            print_idx = idx
            break

    if print_idx is None:
        raise RuntimeError("printJSON not found in file")

    # --- 3. Replace printJSON with tactic + printJSON ---
    indent = lines[print_idx][:len(lines[print_idx]) - len(lines[print_idx].lstrip())]

    new_lines = (
        lines[:print_idx]
        + [f"{indent}{tactic}", f"{indent}printJSON"]
        + lines[print_idx + 1 :]
    )

    new_content = "\n".join(new_lines)

    # --- 4. Replace entire file (simplest + safest) ---
    change = lc.DocumentContentChange(
        text=new_content,
        start=[0, 0],
        end=[len(lines) + 5, 0],  # safely past EOF
    )

    sfc.update_file([change])


def is_done():
    if get_goal_str():
        return False
    return True
    
def compute_reward(done):
    if done:
        return 10.0
    return -0.01  # small step penalty


def run_episode(net, max_steps=4):
    log_probs = []
    rewards = []
    # print("GOAL BEFORE: ", get_goal_str())
    for step in range(max_steps):
        # --- 1. Get current Lean state ---
        
        goal = get_goal_str()
        
        ldecls = get_ldecls()
        num_vars = len(ldecls)

        # --- 2. Encode goal for neural network ---
        state = encode_goal(goal)

        # --- 3. Sample action from policy ---
        action, logp = sample_action(net, state, num_vars)

        # --- 4. Apply action in Lean ---
        apply_action(action, ldecls)

        # --- 5. Compute reward and check termination ---
        done = is_done()
        reward = compute_reward(done)

        log_probs.append(logp)
        rewards.append(reward)
        if done:
            break
    # print(sfc.get_file_content())
    # print("GOAL AFTER: ", get_goal_str())
    return log_probs, rewards


def compute_returns(rewards, gamma=0.99):
    returns = []
    G = 0
    for r in reversed(rewards):
        G = r + gamma * G
        returns.insert(0, G)
    return torch.tensor(returns)

def reinforce_loss(log_probs, rewards):
    returns = compute_returns(rewards)
    returns = (returns - returns.mean()) / (returns.std() + 1e-8)
    loss = 0
    for logp, G in zip(log_probs, returns):
        loss -= logp * G
    return loss

class ActorCriticNet(nn.Module):
    def __init__(self, state_dim, max_vars):
        super().__init__()
        self.shared = nn.Sequential(
            nn.Linear(state_dim, 512),
            nn.ReLU(),
            nn.Linear(512, 256),
            nn.ReLU(),
        )
        
        self.rule_head = nn.Linear(256, 2)
        self.i_head = nn.Linear(256, max_vars)
        self.j_head = nn.Linear(256, max_vars)
        self.value_head = nn.Linear(256, 1)  # NEW
    
    def forward(self, x):
        h = self.shared(x)
        return (
            self.rule_head(h),
            self.i_head(h),
            self.j_head(h),
            self.value_head(h)  # NEW
        )
    
def actor_critic_loss(log_probs, values, rewards, gamma=0.99):
    returns = compute_returns(rewards, gamma)
    
    advantages = returns - values.detach()
    advantages = (advantages - advantages.mean()) / (advantages.std() + 1e-8)
    
    actor_loss = -(log_probs * advantages).mean()
    critic_loss = nn.MSELoss()(values, returns)
    
    return actor_loss + 0.5 * critic_loss

net = PolicyNet(MAX_LEN, max_vars=4)
optimizer = torch.optim.Adam(net.parameters(), lr=1e-4)

returns_per_episode = []
losses_per_episode = []

for episode in range(2000):
    sfc.open_file()  # reset file each episode

    log_probs, rewards = run_episode(net)
    
    loss = reinforce_loss(log_probs, rewards)

    optimizer.zero_grad()
    loss.backward()
    optimizer.step()

    total_return = sum(rewards)  # <-- remove .item()
    returns_per_episode.append(total_return)
    losses_per_episode.append(loss.item())  # loss is tensor

    if episode % 10 == 0:
        print(f"Episode {episode}, return={total_return:.3f}, loss={loss.item():.3f}")



plt.figure(figsize=(12, 5))

# Returns
plt.subplot(1, 2, 1)
plt.plot(returns_per_episode)
plt.title("Episode Returns")
plt.xlabel("Episode")
plt.ylabel("Return")

# Loss
plt.subplot(1, 2, 2)
plt.plot(losses_per_episode)
plt.title("Policy Loss")
plt.xlabel("Episode")
plt.ylabel("Loss")

plt.tight_layout()
plt.show()