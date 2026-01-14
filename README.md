# Coq Circuits

Formally verified threshold logic circuits with axiom-free Coq proofs.

## Status

**Progress**: 14/82 circuits complete (17.1%)

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
├── LICENSE
├── README.md
│
├── coq/
│   ├── _CoqProject              ✓
│   ├── Makefile (planned)
│   │
│   ├── Base/
│   │   ├── Definitions.v         ✓
│   │   ├── Tactics.v             ✓
│   │   ├── WeightPatterns.v      ✓
│   │   ├── Verification.v        ✓
│   │   └── Composition.v         ✓
│   │
│   ├── Boolean/
│   │   ├── NOT.v                 ✓
│   │   ├── AND.v                 ✓
│   │   ├── OR.v
│   │   ├── NAND.v
│   │   ├── NOR.v
│   │   ├── XOR.v
│   │   ├── XNOR.v
│   │   ├── Implies.v
│   │   └── BiImplies.v
│   │
│   ├── Modular/
│   │   ├── ModMParametric.v
│   │   ├── Mod2.v
│   │   ├── Mod3.v
│   │   ├── Mod4.v
│   │   ├── Mod5.v
│   │   ├── Mod6.v
│   │   ├── Mod7.v
│   │   ├── Mod8.v
│   │   ├── Mod9.v
│   │   ├── Mod10.v
│   │   ├── Mod11.v
│   │   └── Mod12.v
│   │
│   ├── Threshold/
│   │   ├── Majority.v
│   │   ├── Minority.v
│   │   ├── KOutOfN.v
│   │   ├── OneOutOfEight.v
│   │   ├── TwoOutOfEight.v
│   │   ├── ThreeOutOfEight.v
│   │   ├── FourOutOfEight.v
│   │   ├── FiveOutOfEight.v
│   │   ├── SixOutOfEight.v
│   │   ├── SevenOutOfEight.v
│   │   ├── AllOutOfEight.v
│   │   ├── AtLeastK.v
│   │   ├── AtMostK.v
│   │   └── ExactlyK.v
│   │
│   ├── Arithmetic/
│   │   ├── HalfAdder.v
│   │   ├── FullAdder.v
│   │   ├── RippleCarry2Bit.v
│   │   ├── RippleCarry4Bit.v
│   │   ├── RippleCarry8Bit.v
│   │   ├── Incrementer8Bit.v
│   │   ├── Decrementer8Bit.v
│   │   ├── Multiplier2x2.v
│   │   ├── Multiplier4x4.v
│   │   ├── Equality8Bit.v
│   │   ├── GreaterThan8Bit.v
│   │   ├── LessThan8Bit.v
│   │   ├── GreaterOrEqual8Bit.v
│   │   ├── LessOrEqual8Bit.v
│   │   ├── Max8Bit.v
│   │   ├── Min8Bit.v
│   │   └── AbsoluteDifference8Bit.v
│   │
│   ├── ErrorDetection/
│   │   ├── ParityChecker8Bit.v
│   │   ├── ParityGenerator8Bit.v
│   │   ├── EvenParityChecker.v
│   │   ├── OddParityChecker.v
│   │   ├── Checksum8Bit.v
│   │   ├── HammingEncode4Bit.v
│   │   ├── HammingDecode7Bit.v
│   │   ├── HammingSyndrome.v
│   │   ├── CRC4.v
│   │   ├── CRC8.v
│   │   └── LongitudinalParity.v
│   │
│   ├── PatternRecognition/
│   │   ├── HammingDistance8Bit.v
│   │   ├── AllOnes.v
│   │   ├── AllZeros.v
│   │   ├── LeadingOnes.v
│   │   ├── TrailingOnes.v
│   │   ├── Symmetry8Bit.v
│   │   ├── Alternating8Bit.v
│   │   ├── RunLength.v
│   │   ├── PopCount.v
│   │   └── OneHotDetector.v
│   │
│   ├── Combinational/
│   │   ├── Multiplexer2to1.v
│   │   ├── Multiplexer4to1.v
│   │   ├── Multiplexer8to1.v
│   │   ├── Demultiplexer1to2.v
│   │   ├── Demultiplexer1to4.v
│   │   ├── Demultiplexer1to8.v
│   │   ├── Encoder8to3.v
│   │   ├── Decoder3to8.v
│   │   ├── PriorityEncoder8Bit.v
│   │   └── BarrelShifter8Bit.v
│   │
│   └── Extraction/
│       ├── ExtractModular.v
│       ├── ExtractBoolean.v
│       ├── ExtractThreshold.v
│       ├── ExtractArithmetic.v
│       ├── ExtractErrorDetection.v
│       ├── ExtractPatternRecognition.v
│       └── ExtractCombinational.v
```

**Total: 82 circuits across 7 categories**

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

### Boolean Logic (9/9) ✓
- [x] Boolean/NOT.v → [tiny-NOT-prover](https://huggingface.co/phanerozoic/tiny-NOT-prover)
- [x] Boolean/AND.v → [tiny-AND-prover](https://huggingface.co/phanerozoic/tiny-AND-prover)
- [x] Boolean/OR.v → [tiny-OR-prover](https://huggingface.co/phanerozoic/tiny-OR-prover)
- [x] Boolean/NAND.v → [tiny-NAND-prover](https://huggingface.co/phanerozoic/tiny-NAND-prover)
- [x] Boolean/NOR.v → [tiny-NOR-prover](https://huggingface.co/phanerozoic/tiny-NOR-prover)
- [x] Boolean/XOR.v → [tiny-XOR-prover](https://huggingface.co/phanerozoic/tiny-XOR-prover)
- [x] Boolean/XNOR.v → [tiny-XNOR-prover](https://huggingface.co/phanerozoic/tiny-XNOR-prover)
- [x] Boolean/Implies.v → [tiny-Implies-prover](https://huggingface.co/phanerozoic/tiny-Implies-prover)
- [x] Boolean/BiImplies.v → [tiny-BiImplies-prover](https://huggingface.co/phanerozoic/tiny-BiImplies-prover)

## Development Checklist

### Phase 1: Base Library ✓
Items 1-5 complete

### Phase 2: Boolean Logic (Items 6-14) ✓
- [x] 6. NOT.v
- [x] 7. AND.v
- [x] 8. OR.v
- [x] 9. NAND.v
- [x] 10. NOR.v
- [x] 11. XOR.v
- [x] 12. XNOR.v
- [x] 13. Implies.v
- [x] 14. BiImplies.v

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
