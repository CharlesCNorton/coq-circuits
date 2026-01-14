"""
Test NOT gate weights extracted from Coq proof.
Verifies: gate([-1], 0, [x]) = NOT(x)
"""

import numpy as np

def heaviside(x):
    """Heaviside step function: x >= 0 -> 1, else 0"""
    return 1.0 if x >= 0 else 0.0

def gate(weights, bias, inputs):
    """Threshold gate: dot(weights, inputs) + bias >= 0"""
    dot_product = sum(w * x for w, x in zip(weights, inputs))
    return heaviside(dot_product + bias)

def not_circuit(x):
    """NOT gate with weights from Coq proof"""
    weights = [-1]
    bias = 0
    return int(gate(weights, bias, [x]))

def test_not_gate():
    """Exhaustive test on all inputs"""
    print("Testing NOT gate...")
    print("Input | Expected | Output | Pass")
    print("------|----------|--------|-----")

    test_cases = [
        (0, 1),  # NOT(0) = 1
        (1, 0),  # NOT(1) = 0
    ]

    all_pass = True
    for inp, expected in test_cases:
        output = not_circuit(inp)
        passed = (output == expected)
        all_pass = all_pass and passed
        status = "PASS" if passed else "FAIL"
        print(f"  {inp}   |    {expected}     |   {output}    | {status}")

    print()
    if all_pass:
        print("All tests passed! NOT gate verified.")
    else:
        print("Some tests failed!")

    return all_pass

if __name__ == "__main__":
    success = test_not_gate()
    exit(0 if success else 1)
