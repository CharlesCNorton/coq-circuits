"""
Test NOT gate by loading actual safetensors weights.
"""

import torch
from safetensors.torch import load_file

def test_not_weights():
    """Test by loading actual safetensors file"""
    print("Testing NOT gate from safetensors...")

    # Load actual weights
    weights = load_file('weights/boolean/not.safetensors')

    print(f"Loaded weights: {weights['weight'].tolist()}")
    print(f"Loaded bias: {weights['bias'].tolist()}")
    print()

    # Test function using loaded weights
    def not_gate(x):
        x_tensor = torch.tensor([float(x)])
        weighted_sum = (x_tensor * weights['weight']).sum() + weights['bias']
        return int(weighted_sum >= 0)

    print("Input | Expected | Output | Pass")
    print("------|----------|--------|-----")

    test_cases = [
        (0, 1),  # NOT(0) = 1
        (1, 0),  # NOT(1) = 0
    ]

    all_pass = True
    for inp, expected in test_cases:
        output = not_gate(inp)
        passed = (output == expected)
        all_pass = all_pass and passed
        status = "PASS" if passed else "FAIL"
        print(f"  {inp}   |    {expected}     |   {output}    | {status}")

    print()
    if all_pass:
        print("All tests passed! Safetensors weights verified.")
        return True
    else:
        print("Some tests failed!")
        return False

if __name__ == "__main__":
    success = test_not_weights()
    exit(0 if success else 1)
