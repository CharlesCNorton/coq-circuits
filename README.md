# Coq Circuits

Formally verified threshold logic circuits with axiom-free Coq proofs.

## Status

**Progress**: 71/82 circuits complete (86.6%)

**Uploaded to HuggingFace**: 31 models

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
- **Error**: Parity, Hamming codes, CRC (11 circuits)
- **Pattern**: Hamming distance, symmetry, detectors (10 circuits)
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
│   │   ├── OR.v                  ✓
│   │   ├── NAND.v                ✓
│   │   ├── NOR.v                 ✓
│   │   ├── XOR.v                 ✓
│   │   ├── XNOR.v                ✓
│   │   ├── Implies.v             ✓
│   │   └── BiImplies.v           ✓
│   │
│   ├── Modular/
│   │   ├── ModMParametric.v      ✓
│   │   ├── Mod2.v                ✓
│   │   ├── Mod3.v                ✓
│   │   ├── Mod4.v                ✓
│   │   ├── Mod5.v                ✓
│   │   ├── Mod6.v                ✓
│   │   ├── Mod7.v                ✓
│   │   ├── Mod8.v                ✓
│   │   ├── Mod9.v                ✓
│   │   ├── Mod10.v               ✓
│   │   ├── Mod11.v               ✓
│   │   └── Mod12.v               ✓
│   │
│   ├── Threshold/
│   │   ├── Majority.v            ✓
│   │   ├── Minority.v            ✓
│   │   ├── KOutOfN.v             ✓
│   │   ├── OneOutOfEight.v       ✓
│   │   ├── TwoOutOfEight.v       ✓
│   │   ├── ThreeOutOfEight.v     ✓
│   │   ├── FourOutOfEight.v      ✓
│   │   ├── FiveOutOfEight.v      ✓
│   │   ├── SixOutOfEight.v       ✓
│   │   ├── SevenOutOfEight.v     ✓
│   │   ├── AllOutOfEight.v       ✓
│   │   ├── AtLeastK.v            ✓
│   │   ├── AtMostK.v             ✓
│   │   └── ExactlyK.v            ✓
│   │
│   ├── Arithmetic/
│   │   ├── HalfAdder.v           ✓
│   │   ├── FullAdder.v           ✓
│   │   ├── RippleCarry2Bit.v     ✓
│   │   ├── RippleCarry4Bit.v     ✓
│   │   ├── RippleCarry8Bit.v     ✓
│   │   ├── Incrementer8Bit.v     ✓
│   │   ├── Decrementer8Bit.v     ✓
│   │   ├── Multiplier2x2.v
│   │   ├── Multiplier4x4.v
│   │   ├── Equality8Bit.v        ✓
│   │   ├── GreaterThan8Bit.v
│   │   ├── LessThan8Bit.v
│   │   ├── GreaterOrEqual8Bit.v
│   │   ├── LessOrEqual8Bit.v
│   │   ├── Max8Bit.v
│   │   ├── Min8Bit.v
│   │   └── AbsoluteDifference8Bit.v
│   │
│   ├── Error/
│   │   ├── ParityChecker8Bit.v   ✓
│   │   ├── ParityGenerator8Bit.v ✓
│   │   ├── EvenParityChecker.v   ✓
│   │   ├── OddParityChecker.v    ✓
│   │   ├── Checksum8Bit.v        ✓
│   │   ├── HammingEncode4Bit.v
│   │   ├── HammingDecode7Bit.v
│   │   ├── HammingSyndrome.v
│   │   ├── CRC4.v
│   │   ├── CRC8.v
│   │   └── LongitudinalParity.v
│   │
│   ├── Pattern/
│   │   ├── HammingDistance8Bit.v ✓
│   │   ├── AllOnes.v             ✓
│   │   ├── AllZeros.v            ✓
│   │   ├── LeadingOnes.v         ✓
│   │   ├── TrailingOnes.v        ✓
│   │   ├── Symmetry8Bit.v        ✓
│   │   ├── Alternating8Bit.v     ✓
│   │   ├── RunLength.v           ✓
│   │   ├── PopCount.v            ✓
│   │   └── OneHotDetector.v      ✓
│   │
│   ├── Combinational/
│   │   ├── Multiplexer2to1.v     ✓
│   │   ├── Multiplexer4to1.v     ✓
│   │   ├── Multiplexer8to1.v     ✓
│   │   ├── Demultiplexer1to2.v   ✓
│   │   ├── Demultiplexer1to4.v   ✓
│   │   ├── Demultiplexer1to8.v   ✓
│   │   ├── Encoder8to3.v         ✓
│   │   ├── Decoder3to8.v         ✓
│   │   ├── PriorityEncoder8Bit.v ✓
│   │   └── BarrelShifter8Bit.v   ✓
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

**For each circuit, complete ALL steps before moving to the next circuit:**

### 1. Write Coq Proof
Create `.v` file in appropriate category directory (e.g., `coq/Arithmetic/FullAdder.v`).

```coq
Definition circuit_weights : list Z := [...].
Definition circuit_bias : Z := ...
Definition circuit (xs : list bool) : bool := gate circuit_weights circuit_bias xs.

Theorem circuit_correct : forall x0 ... x7,
  circuit [x0;...;x7] = specification [x0;...;x7].
Proof. intros. destruct x0,...,x7; reflexivity. Qed.

Print Assumptions circuit_correct.  (* Must be axiom-free *)
```

### 2. Compile Coq Proof
Verify the proof compiles without errors:
```bash
coqc -R coq "" coq/[Category]/[Circuit].v
```

### 3. Generate Weights
Extract weight values from Coq definitions to `.safetensors` format:
- Create Python script to convert Coq weights to PyTorch tensors
- Save to `weights/[category]/[circuit].safetensors`
- Include all layer weights and biases

### 4. Test Weights Exhaustively
Load `.safetensors` and verify outputs match specification on all valid inputs:
- Test every possible input combination
- Verify output equals expected behavior
- Confirm no weight corruption during serialization

### 5. Create HuggingFace README
Write `weights/[category]/[Circuit]_README.md` with:
- Architecture table (inputs, outputs, neurons, parameters, weights, bias)
- Key properties (accuracy, verification method)
- Usage example with Python code
- Coq theorem statement
- Link to proof: `[coq-circuits/Category/Circuit.v](https://github.com/CharlesCNorton/coq-circuits/blob/main/coq/Category/Circuit.v)`
- Citation

### 6. Upload to HuggingFace
**Single command per circuit:**
```bash
python -c "from huggingface_hub import HfApi, create_repo; api = HfApi(); \
  create_repo('phanerozoic/tiny-[Circuit]-verified', repo_type='model', exist_ok=True); \
  api.upload_file(path_or_fileobj='weights/[category]/[circuit].safetensors', \
    path_in_repo='[circuit].safetensors', repo_id='phanerozoic/tiny-[Circuit]-verified', repo_type='model'); \
  api.upload_file(path_or_fileobj='weights/[category]/[Circuit]_README.md', \
    path_in_repo='README.md', repo_id='phanerozoic/tiny-[Circuit]-verified', repo_type='model'); \
  api.add_collection_item('phanerozoic/tiny-verified-logic-circuits', \
    'phanerozoic/tiny-[Circuit]-verified', 'model'); \
  print('[Circuit] uploaded')"
```

### 7. Update Main README Tree
Add checkmark (✓) to circuit in the repository structure tree above.

**CRITICAL:** Complete one circuit fully (steps 1-7) before starting the next. Do not batch process multiple circuits.

### 6. Sanity Testing (Dual Schema)

Beyond proving individual circuits correct, we verify mathematical relationships between circuits using two complementary verification methods.

#### Level 1: Coq Proof Equivalence

Relationships between circuits are proven formally using universal quantification and axiom-free verification:

- **Compositional Relationships**: Prove complex circuits can be built from simpler primitives
- **Architectural Equivalences**: Prove different implementations compute identical functions
- **Cross-Category Equivalences**: Prove functions from different domains are equivalent on restricted inputs
- **Parametric Instantiations**: Prove specialized circuits match their parametric definitions

#### Level 2: Runtime Weight Verification

Concrete weight files uploaded to HuggingFace are tested to ensure they implement proven relationships:

- **Composition Tests**: Simulate circuit composition from primitive weights, verify outputs match composite implementations
- **Identity Tests**: For proven equivalent circuits, verify weights are identical or related by proven transformations
- **Algebraic Pattern Tests**: Verify weights follow expected mathematical patterns, confirm biases match specifications

This dual approach bridges the gap between formal proof and practical implementation: abstract correctness proven in Coq is verified to hold for deployed weight files.

## Naming Conventions

- **Coq files**: PascalCase (`Boolean/NOT.v`, `Arithmetic/HalfAdder.v`)
- **HuggingFace**: `phanerozoic/tiny-[CIRCUIT]-verified`
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
- [x] Boolean/NOT.v → [tiny-NOT-verified](https://huggingface.co/phanerozoic/tiny-NOT-verified)
- [x] Boolean/AND.v → [tiny-AND-verified](https://huggingface.co/phanerozoic/tiny-AND-verified)
- [x] Boolean/OR.v → [tiny-OR-verified](https://huggingface.co/phanerozoic/tiny-OR-verified)
- [x] Boolean/NAND.v → [tiny-NAND-verified](https://huggingface.co/phanerozoic/tiny-NAND-verified)
- [x] Boolean/NOR.v → [tiny-NOR-verified](https://huggingface.co/phanerozoic/tiny-NOR-verified)
- [x] Boolean/XOR.v → [tiny-XOR-verified](https://huggingface.co/phanerozoic/tiny-XOR-verified)
- [x] Boolean/XNOR.v → [tiny-XNOR-verified](https://huggingface.co/phanerozoic/tiny-XNOR-verified)
- [x] Boolean/Implies.v → [tiny-Implies-verified](https://huggingface.co/phanerozoic/tiny-Implies-verified)
- [x] Boolean/BiImplies.v → [tiny-BiImplies-verified](https://huggingface.co/phanerozoic/tiny-BiImplies-verified)

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

### Phase 3: Threshold Functions (Items 15-28) ✓
- [x] 15. Majority.v → [tiny-Majority-verified](https://huggingface.co/phanerozoic/tiny-Majority-verified)
- [x] 16. Minority.v → [tiny-Minority-verified](https://huggingface.co/phanerozoic/tiny-Minority-verified)
- [x] 17. KOutOfN.v (parametric)
- [x] 18. OneOutOfEight.v → [tiny-1OutOf8-verified](https://huggingface.co/phanerozoic/tiny-1OutOf8-verified)
- [x] 19. TwoOutOfEight.v → [tiny-2OutOf8-verified](https://huggingface.co/phanerozoic/tiny-2OutOf8-verified)
- [x] 20. ThreeOutOfEight.v → [tiny-3OutOf8-verified](https://huggingface.co/phanerozoic/tiny-3OutOf8-verified)
- [x] 21. FourOutOfEight.v → [tiny-4OutOf8-verified](https://huggingface.co/phanerozoic/tiny-4OutOf8-verified)
- [x] 22. FiveOutOfEight.v → [tiny-5OutOf8-verified](https://huggingface.co/phanerozoic/tiny-5OutOf8-verified)
- [x] 23. SixOutOfEight.v → [tiny-6OutOf8-verified](https://huggingface.co/phanerozoic/tiny-6OutOf8-verified)
- [x] 24. SevenOutOfEight.v → [tiny-7OutOf8-verified](https://huggingface.co/phanerozoic/tiny-7OutOf8-verified)
- [x] 25. AllOutOfEight.v → [tiny-AllOutOf8-verified](https://huggingface.co/phanerozoic/tiny-AllOutOf8-verified)
- [x] 26. AtLeastK.v (parametric)
- [x] 27. AtMostK.v (parametric)
- [x] 28. ExactlyK.v (parametric)

**Sanity Test 2**: Verify Majority = FiveOutOfEight = AtLeastK(5) ✓

### Phase 4: Modular Arithmetic (Items 29-40) ✓
- [x] 29. ModMParametric.v
- [x] 30. Mod2.v → [tiny-parity-verified](https://huggingface.co/phanerozoic/tiny-parity-verified)
- [x] 31. Mod3.v → [tiny-mod3-verified](https://huggingface.co/phanerozoic/tiny-mod3-verified)
- [x] 32. Mod4.v → [tiny-mod4-verified](https://huggingface.co/phanerozoic/tiny-mod4-verified)
- [x] 33. Mod5.v → [tiny-mod5-verified](https://huggingface.co/phanerozoic/tiny-mod5-verified)
- [x] 34. Mod6.v → [tiny-mod6-verified](https://huggingface.co/phanerozoic/tiny-mod6-verified)
- [x] 35. Mod7.v → [tiny-mod7-verified](https://huggingface.co/phanerozoic/tiny-mod7-verified)
- [x] 36. Mod8.v → [tiny-mod8-verified](https://huggingface.co/phanerozoic/tiny-mod8-verified)
- [x] 37. Mod9.v → [tiny-mod9-verified](https://huggingface.co/phanerozoic/tiny-mod9-verified)
- [x] 38. Mod10.v → [tiny-mod10-verified](https://huggingface.co/phanerozoic/tiny-mod10-verified)
- [x] 39. Mod11.v → [tiny-mod11-verified](https://huggingface.co/phanerozoic/tiny-mod11-verified)
- [x] 40. Mod12.v → [tiny-mod12-verified](https://huggingface.co/phanerozoic/tiny-mod12-verified)

**Sanity Test 3**: Verify MOD-2 = XOR = Parity ✓

### Phase 5: Arithmetic (Items 41-57)
- [x] 41. HalfAdder.v
- [x] 42. FullAdder.v
- [x] 43. RippleCarry2Bit.v
- [x] 44. RippleCarry4Bit.v
- [x] 45. RippleCarry8Bit.v
- [x] 46. Incrementer8Bit.v
- [x] 47. Decrementer8Bit.v
- [ ] 48. Multiplier2x2.v
- [ ] 49. Multiplier4x4.v
- [x] 50. Equality8Bit.v
- [ ] 51. GreaterThan8Bit.v
- [ ] 52. LessThan8Bit.v
- [ ] 53. GreaterOrEqual8Bit.v
- [ ] 54. LessOrEqual8Bit.v
- [ ] 55. Max8Bit.v
- [ ] 56. Min8Bit.v
- [ ] 57. AbsoluteDifference8Bit.v

**Sanity Test 4**: Verify RippleCarry8Bit = composition of FullAdders

### Phase 6: Error Detection (Items 58-68)
- [x] 58. ParityChecker8Bit.v
- [x] 59. ParityGenerator8Bit.v
- [x] 60. EvenParityChecker.v
- [x] 61. OddParityChecker.v
- [ ] 62. Checksum8Bit.v
- [ ] 63. HammingEncode4Bit.v
- [ ] 64. HammingDecode7Bit.v
- [ ] 65. HammingSyndrome.v
- [ ] 66. CRC4.v
- [ ] 67. CRC8.v
- [ ] 68. LongitudinalParity.v

**Sanity Test 10**: EvenParity = NOT(OddParity)
**Sanity Test 11**: ParityGenerator8Bit = MOD-2 residue 1

### Phase 7: Pattern Recognition (Items 69-78)
- [ ] 69. HammingDistance8Bit.v
- [x] 70. AllOnes.v
- [x] 71. AllZeros.v
- [ ] 72. LeadingOnes.v
- [ ] 73. TrailingOnes.v
- [ ] 74. Symmetry8Bit.v
- [ ] 75. Alternating8Bit.v
- [ ] 76. RunLength.v
- [ ] 77. PopCount.v
- [x] 78. OneHotDetector.v

**Sanity Test 6**: AllOnes = AllOutOfEight (8-of-8 threshold)
**Sanity Test 7**: AllZeros = NOT(OneOutOfEight)
**Sanity Test 8**: PopCount = hamming_weight
**Sanity Test 9**: OneHotDetector = ExactlyK(1)
**Sanity Test 12**: HammingDistance(A,B) = PopCount(XOR(A,B))

### Phase 8: Combinational Logic (Items 79-88)
- [x] 79. Multiplexer2to1.v
- [x] 80. Multiplexer4to1.v
- [ ] 81. Multiplexer8to1.v
- [ ] 82. Demultiplexer1to2.v
- [ ] 83. Demultiplexer1to4.v
- [ ] 84. Demultiplexer1to8.v
- [ ] 85. Encoder8to3.v
- [ ] 86. Decoder3to8.v
- [ ] 87. PriorityEncoder8Bit.v
- [ ] 88. BarrelShifter8Bit.v

**Sanity Test 18**: Mux2to1(s,a,b) = OR(AND(NOT(s),a), AND(s,b))
**Sanity Test 19**: Decoder3to8 ∘ Encoder8to3 = identity (on valid inputs)

### Remaining Phases
- Phase 9: Comparators (GreaterThan, LessThan, etc.)
- Phase 10: Min/Max/AbsDiff
- Phase 11: Multipliers
- Phase 12-20: Extraction, weights, HuggingFace, integration

## Sanity Test Summary

| Test | Relationship | Status |
|------|--------------|--------|
| ST1 | NAND ∘ NAND = AND | Pending |
| ST2 | Majority = FiveOutOfEight = AtLeastK(5) | ✓ Done |
| ST3 | MOD-2 = XOR = Parity | ✓ Done |
| ST4 | RippleCarry8Bit = 8 × FullAdder | Pending |
| ST5 | NOR ∘ NOR = OR | Pending |
| ST6 | AllOnes = AllOutOfEight | Pending |
| ST7 | AllZeros = NOT(OneOutOfEight) | Pending |
| ST8 | PopCount = hamming_weight | Pending |
| ST9 | OneHotDetector = ExactlyK(1) | Pending |
| ST10 | EvenParity = NOT(OddParity) | Pending |
| ST11 | ParityGenerator = MOD-2 residue 1 | Pending |
| ST12 | HammingDistance(A,B) = PopCount(XOR(A,B)) | Pending |
| ST13 | Equality8Bit = AND(XNOR(a_i,b_i)...) | Pending |
| ST14 | GreaterThan = NOT(LessOrEqual) | Pending |
| ST15 | LessThan = NOT(GreaterOrEqual) | Pending |
| ST16 | Max(A,B) = IF GT(A,B) THEN A ELSE B | Pending |
| ST17 | Incrementer = RippleCarry(A, 0x01) | Pending |
| ST18 | Mux2to1 = OR(AND(NOT(s),a), AND(s,b)) | Pending |
| ST19 | Decoder ∘ Encoder = identity | Pending |
| ST20 | CRC divisibility properties | Pending |

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
