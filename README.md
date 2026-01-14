# Coq Circuits

Formally verified threshold logic circuits with axiom-free Coq proofs.

## Status

**Progress**: 6/82 circuits complete (7.3%)

Unifying existing repos:
- [majority-verified](https://github.com/CharlesCNorton/majority-verified)
- [mod3-verified](https://github.com/CharlesCNorton/mod3-verified)
- [mod5-verified](https://github.com/CharlesCNorton/mod5-verified)
- [mod7-verified](https://github.com/CharlesCNorton/mod7-verified)
- [modm-verified](https://github.com/CharlesCNorton/modm-verified)

Weights: [HuggingFace/phanerozoic](https://huggingface.co/phanerozoic)

## Overview

Threshold logic circuits built using algebraically-constructed weight functions. All circuits use Heaviside step activation and are compatible with neuromorphic hardware (Loihi, TrueNorth, Akida).

### Circuit Categories (82 total)

- **Modular Arithmetic**: MOD-2 through MOD-12 (12 circuits)
- **Boolean Logic**: AND, OR, NAND, NOR, XOR, XNOR, NOT, Implies, BiImplies (9 circuits)
- **Threshold Functions**: Majority, k-out-of-n variants (13 circuits)
- **Arithmetic**: Adders, multipliers, comparators (17 circuits)
- **Error Detection**: Parity, Hamming codes, CRC (11 circuits)
- **Pattern Recognition**: Hamming distance, symmetry (10 circuits)
- **Combinational Logic**: Muxes, encoders, decoders (10 circuits)

### Verification

All circuits proven correct using three independent methods:
1. **Exhaustive**: `vm_compute` over all inputs
2. **Constructive**: Universal quantifier proofs
3. **Algebraic**: Mathematical correctness proofs

All proofs axiom-free.

## Repository Structure

```
coq-circuits/
├── coq/
│   ├── Base/              # Core definitions, tactics, verification
│   ├── Boolean/           # Boolean logic gates
│   ├── Modular/           # MOD-m circuits
│   ├── Threshold/         # Threshold functions
│   ├── Arithmetic/        # Arithmetic circuits
│   ├── ErrorDetection/    # Error detection
│   ├── PatternRecognition/# Pattern recognition
│   └── Combinational/     # Combinational logic
├── LICENSE
└── README.md
```

## Workflow

### 1. Define Circuit in Coq
```coq
Definition circuit_weights : list Z := [...].
Definition circuit_bias : Z := ...
Definition circuit (xs : list bool) : bool := gate circuit_weights circuit_bias xs.
```

### 2. Prove Correctness
```coq
Theorem circuit_correct : forall x0 ... x7,
  circuit [x0;...;x7] = specification [x0;...;x7].
Proof. intros. destruct x0,...,x7; reflexivity. Qed.

Print Assumptions circuit_correct.  (* Must be axiom-free *)
```

### 3. Generate Weights
Extract weight values to `.safetensors` format.

### 4. Test Weights
Load `.safetensors` and verify inference matches Coq proof on all inputs.

### 5. Upload to HuggingFace
Publish to `phanerozoic/tiny-[CIRCUIT]-prover` with model card.

## Naming Conventions

- **Coq files**: PascalCase (`Boolean/NOT.v`, `Arithmetic/HalfAdder.v`)
- **HuggingFace**: `phanerozoic/tiny-[CIRCUIT]-prover`
- **Weights**: Local only, uploaded to HF (not in repo)

## Building

```bash
cd coq-circuits/coq
coqc -R . "" Base/Definitions.v
coqc -R . "" Boolean/NOT.v
# etc.
```

## Completed Circuits

### Base Library (5/5)
- [x] Base/Definitions.v
- [x] Base/Tactics.v
- [x] Base/WeightPatterns.v
- [x] Base/Verification.v
- [x] Base/Composition.v

### Boolean Logic (1/9)
- [x] Boolean/NOT.v → [tiny-NOT-prover](https://huggingface.co/phanerozoic/tiny-NOT-prover)
- [ ] Boolean/AND.v
- [ ] Boolean/OR.v
- [ ] Boolean/NAND.v
- [ ] Boolean/NOR.v
- [ ] Boolean/XOR.v
- [ ] Boolean/XNOR.v
- [ ] Boolean/Implies.v
- [ ] Boolean/BiImplies.v

## Development Checklist

### Phase 1: Base Library ✓
Items 1-5 complete

### Phase 2: Boolean Logic (Items 6-14)
- [x] 6. NOT.v
- [ ] 7. AND.v ← **Current**
- [ ] 8. OR.v
- [ ] 9. NAND.v
- [ ] 10. NOR.v
- [ ] 11. XOR.v
- [ ] 12. XNOR.v
- [ ] 13. Implies.v
- [ ] 14. BiImplies.v

**Sanity Test 1**: Compose NAND gates to build AND

### Phase 3: Threshold Functions (Items 15-28)
Majority, minority, k-out-of-n variants

**Sanity Test 2**: Verify Majority = FiveOutOfEight = AtLeastK(5)

### Phase 4: Modular Arithmetic (Items 29-40)
MOD-m parametric proof + instances through MOD-12

**Sanity Test 3**: Verify MOD-2 = XOR = Parity

### Phases 5-25
Arithmetic, error detection, pattern recognition, combinational logic, OCaml extraction, weight generation, HuggingFace publishing, integration testing.

Total: 132 items

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
