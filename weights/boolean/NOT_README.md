# tiny-NOT-prover

Formally verified NOT gate. Single threshold neuron computing negation with 100% accuracy.

## Architecture

| Component | Value |
|-----------|-------|
| Inputs | 1 |
| Outputs | 1 |
| Neurons | 1 |
| Parameters | 2 |
| Weights | [-1] |
| Bias | 0 |
| Activation | Heaviside step |

## Key Properties

- 100% accuracy (2/2 inputs correct)
- Coq-proven correctness
- Single threshold neuron
- Integer weights
- Involutive: NOT(NOT(x)) = x

## Usage

```python
import torch
from safetensors.torch import load_file

weights = load_file('not.safetensors')

def not_gate(x):
    # Heaviside: weighted_sum + bias >= 0
    return int((x * weights['weight'] + weights['bias']) >= 0)

# Test
print(not_gate(0))  # 1
print(not_gate(1))  # 0
```

## Verification

**Coq Theorem**:
```coq
Theorem not_correct : forall x, not_circuit x = negb x.
```

Proven axiom-free. Full proof: [coq-circuits/Boolean/NOT.v](https://github.com/CharlesCNorton/coq-circuits)

## Citation

```bibtex
@software{tiny_not_prover_2025,
  title={tiny-NOT-prover: Formally Verified NOT Gate},
  author={Norton, Charles},
  url={https://huggingface.co/phanerozoic/tiny-NOT-prover},
  year={2025}
}
```
