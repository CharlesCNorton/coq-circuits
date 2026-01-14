# Coq Circuits

Formally verified threshold logic circuits with axiom-free Coq proofs.

## Status: Repository Unification in Progress

This repository is being prepared to unify the following verified circuits:
- [majority-verified](https://github.com/CharlesCNorton/majority-verified) - Single-gate majority threshold circuit
- [mod3-verified](https://github.com/CharlesCNorton/mod3-verified) - First MOD-3 threshold circuit
- [mod5-verified](https://github.com/CharlesCNorton/mod5-verified) - MOD-5 threshold circuit
- [mod7-verified](https://github.com/CharlesCNorton/mod7-verified) - MOD-7 threshold circuit
- [modm-verified](https://github.com/CharlesCNorton/modm-verified) - Parametric MOD-m proof for any m ≥ 2

Weights for all circuits are available on [HuggingFace](https://huggingface.co/phanerozoic).

## Overview

Formally verified threshold logic circuits built using algebraically-constructed weight functions, proven correct in Coq/Rocq. All circuits use Heaviside step activation and are compatible with neuromorphic hardware (Loihi, TrueNorth, Akida).

## Circuit Categories

### Modular Arithmetic (12 circuits)
MOD-2 through MOD-12 with parametric proof covering any m ≥ 2.

### Boolean Logic (9 circuits)
AND, OR, NAND, NOR, XOR, XNOR, NOT, Implies, BiImplies.

### Threshold Functions (13 circuits)
Majority, minority, k-out-of-n, at-least-k, at-most-k, exactly-k variants.

### Arithmetic Circuits (17 circuits)
Adders, multipliers, comparators, incrementers, decrementers.

### Error Detection (11 circuits)
Parity checkers, Hamming codes, CRC, checksums.

### Pattern Recognition (10 circuits)
Hamming distance, symmetry detection, run-length encoding, one-hot detection.

### Combinational Logic (10 circuits)
Multiplexers, demultiplexers, encoders, decoders, barrel shifters.

**Total: 82 verified threshold logic circuits**

## Verification Methodology

All circuits proven correct using three independent methods:

1. **Exhaustive Verification** - `vm_compute` over all inputs
2. **Constructive Verification** - Universal quantifier proofs
3. **Algebraic Verification** - Mathematical correctness proofs

All proofs are axiom-free.

## Repository Structure

```
coq-circuits/
├── coq/                    # Coq proof files
│   ├── Base/              # Shared definitions and tactics
│   ├── Modular/           # MOD-m circuits
│   ├── Boolean/           # Boolean logic gates
│   ├── Threshold/         # Threshold functions
│   ├── Arithmetic/        # Arithmetic circuits
│   ├── ErrorDetection/    # Error detection circuits
│   ├── PatternRecognition/# Pattern recognition circuits
│   ├── Combinational/     # Combinational logic
│   └── Extraction/        # OCaml extraction modules
├── extracted/             # Extracted OCaml code
├── weights/               # Verified weights (.safetensors)
├── ocaml/                 # OCaml build configuration
├── docs/                  # Documentation
├── examples/              # Usage examples
└── scripts/               # Build and automation scripts
```

## Workflow

### 1. Define Circuit in Coq
Write formal definition with weight functions.

### 2. Prove Correctness
Provide exhaustive, constructive, and algebraic proofs.

### 3. Extract to OCaml
Generate executable code via Coq extraction.

### 4. Generate Weights
Export weights to `.safetensors` format.

### 5. Upload to HuggingFace
Publish verified weights and model cards.

## Building

```bash
# Compile all Coq proofs
./scripts/build_all_coq.sh

# Extract OCaml code
./scripts/extract_all_ocaml.sh

# Generate weights
./scripts/generate_all_weights.sh

# Verify all proofs are axiom-free
./scripts/verify_all_proofs.sh
```

## Usage

See `examples/` directory for inference examples using extracted OCaml code.

## HuggingFace Models

All verified weights available at:
- [phanerozoic/tiny-mod2-prover](https://huggingface.co/phanerozoic/tiny-parity-prover)
- [phanerozoic/tiny-mod3-prover](https://huggingface.co/phanerozoic/tiny-mod3-prover)
- [phanerozoic/tiny-mod5-prover](https://huggingface.co/phanerozoic/tiny-mod5-prover)
- [phanerozoic/tiny-mod7-prover](https://huggingface.co/phanerozoic/tiny-mod7-prover)

Additional circuits will be published as they are completed.

## License

MIT

## Citation

```bibtex
@software{coq_circuits_2025,
  title={Coq Circuits: Formally Verified Threshold Logic},
  author={Norton, Charles},
  url={https://github.com/CharlesCNorton/coq-circuits},
  year={2025}
}
```
