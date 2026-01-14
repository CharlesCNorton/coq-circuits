"""
Generate safetensors weights for NOT gate from Coq proof.
"""

import torch
from safetensors.torch import save_file
import os

# Weights from Coq proof
# Definition not_weights := [-1].
# Definition not_bias := 0.

weights_dict = {
    'weight': torch.tensor([-1.0]),
    'bias': torch.tensor([0.0]),
}

# Create output directory
os.makedirs('weights/boolean', exist_ok=True)

# Save to safetensors
output_path = 'weights/boolean/not.safetensors'
save_file(weights_dict, output_path)

print(f"Saved NOT gate weights to {output_path}")
print(f"  weight: {weights_dict['weight'].tolist()}")
print(f"  bias: {weights_dict['bias'].tolist()}")
