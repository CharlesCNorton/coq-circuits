# Coq Circuits

Formally verified threshold logic circuits in Coq, culminating in a Turing-complete 8-bit computer.

## Status: Complete

**108 verified modules** across 10 categories. All proofs axiom-free.

Weights: [HuggingFace/phanerozoic](https://huggingface.co/phanerozoic)

## Overview

Threshold logic circuits using Heaviside step activation, compatible with neuromorphic hardware (Loihi, TrueNorth, Akida).

```
output = 1  if  sum(weight * input) + bias >= 0
output = 0  otherwise
```

## 8-Bit Threshold Computer

A complete, formally verified 8-bit computer built entirely from threshold neurons.

| Component | Files | Status |
|-----------|-------|--------|
| Base Library | 5 | Complete |
| Boolean Logic | 11 | Complete |
| Modular Arithmetic | 13 | Complete |
| Threshold Functions | 14 | Complete |
| Arithmetic | 19 | Complete |
| Error Detection | 12 | Complete |
| Pattern Recognition | 15 | Complete |
| Combinational Logic | 12 | Complete |
| ALU (16 ops, flags) | 3 | Complete |
| Control (JMP, Jcc, LD/ST, stack) | 4 | Complete |

### Architecture

- **Registers**: R0-R3 (8-bit)
- **ALU**: ADD, SUB, AND, OR, XOR, NOT, SHL, SHR, INC, DEC, CMP, NEG, PASS, ZERO, ONES, NOP
- **Flags**: Zero, Negative, Carry, Overflow
- **Control Flow**: JMP, JZ, JNZ, JC, JNC, JN, JP, JV, JNV
- **Memory**: LD, ST (256-byte address space)
- **Stack**: PUSH, POP, CALL, RET

### Verification

All circuits proven correct using:
1. **Exhaustive**: `vm_compute` over all inputs
2. **Constructive**: Universal quantifier proofs
3. **Algebraic**: Mathematical correctness proofs

All proofs axiom-free (`Print Assumptions` returns `Closed under the global context`).

## Repository Structure

```
coq-circuits/
├── computer/
│   ├── assembler.py              # Assembler for threshold computer
│   ├── neural_computer_architecture.json
│   └── README.md
│
└── coq/
    ├── _CoqProject
    │
    ├── Base/                     # 5 files
    │   ├── Definitions.v
    │   ├── Tactics.v
    │   ├── WeightPatterns.v
    │   ├── Verification.v
    │   └── Composition.v
    │
    ├── Boolean/                  # 11 files
    │   ├── NOT.v, AND.v, OR.v
    │   ├── NAND.v, NOR.v
    │   ├── XOR.v, XNOR.v
    │   ├── Implies.v, BiImplies.v
    │   └── SanityTest1.v, SanityTest5.v
    │
    ├── Modular/                  # 13 files
    │   ├── ModMParametric.v
    │   ├── Mod2.v .. Mod12.v
    │   └── SanityTest3.v
    │
    ├── Threshold/                # 14 files
    │   ├── Majority.v, Minority.v
    │   ├── KOutOfN.v
    │   ├── OneOutOfEight.v .. AllOutOfEight.v
    │   └── AtLeastK.v, AtMostK.v, ExactlyK.v
    │
    ├── Arithmetic/               # 19 files
    │   ├── HalfAdder.v, FullAdder.v
    │   ├── RippleCarry2Bit.v, RippleCarry4Bit.v, RippleCarry8Bit.v
    │   ├── Incrementer8Bit.v, Decrementer8Bit.v
    │   ├── Multiplier2x2.v, Multiplier4x4.v
    │   ├── Equality8Bit.v, GreaterThan8Bit.v, LessThan8Bit.v
    │   ├── GreaterOrEqual8Bit.v, LessOrEqual8Bit.v
    │   ├── Max8Bit.v, Min8Bit.v, AbsoluteDifference8Bit.v
    │   └── SanityTest13.v, SanityTest17.v
    │
    ├── Error/                    # 12 files
    │   ├── ParityChecker8Bit.v, ParityGenerator8Bit.v
    │   ├── EvenParityChecker.v, OddParityChecker.v
    │   ├── Checksum8Bit.v
    │   ├── HammingEncode4Bit.v, HammingDecode7Bit.v, HammingSyndrome.v
    │   ├── CRC4.v, CRC8.v
    │   ├── LongitudinalParity.v
    │   └── SanityTest10.v
    │
    ├── Pattern/                  # 15 files
    │   ├── AllOnes.v, AllZeros.v
    │   ├── LeadingOnes.v, TrailingOnes.v
    │   ├── Symmetry8Bit.v, Alternating8Bit.v
    │   ├── HammingDistance8Bit.v, RunLength.v
    │   ├── PopCount.v, OneHotDetector.v
    │   └── SanityTest6.v .. SanityTest12.v
    │
    ├── Combinational/            # 12 files
    │   ├── Multiplexer2to1.v, Multiplexer4to1.v, Multiplexer8to1.v
    │   ├── Demultiplexer1to2.v, Demultiplexer1to4.v, Demultiplexer1to8.v
    │   ├── Encoder8to3.v, Decoder3to8.v
    │   ├── PriorityEncoder8Bit.v, BarrelShifter8Bit.v
    │   └── SanityTest18.v, SanityTest19.v
    │
    ├── ALU/                      # 3 files
    │   ├── ALUFlags.v
    │   ├── ALUControl.v
    │   └── ALU8Bit.v
    │
    └── Control/                  # 4 files
        ├── Jump.v
        ├── ConditionalJump.v
        ├── MemoryAccess.v
        └── Stack.v
```

## Building

```bash
cd coq-circuits/coq
coqc -R . "" Base/Definitions.v
coqc -R . "" Base/Tactics.v
coqc -R . "" Base/WeightPatterns.v
coqc -R . "" Base/Verification.v
coqc -R . "" Base/Composition.v
# ... remaining files in dependency order
```

## Sanity Tests

Cross-circuit verification proving mathematical relationships:

| Test | Relationship | File |
|------|--------------|------|
| ST1 | NAND(NAND(x,y), NAND(x,y)) = AND(x,y) | SanityTest1.v |
| ST3 | MOD-2 = XOR = Parity | SanityTest3.v |
| ST5 | NOR(NOR(x,y), NOR(x,y)) = OR(x,y) | SanityTest5.v |
| ST6 | AllOnes = 8-of-8 threshold | SanityTest6.v |
| ST7 | AllZeros = NOT(1-of-8) | SanityTest7.v |
| ST8 | PopCount = hamming_weight | SanityTest8.v |
| ST9 | OneHot = ExactlyK(1) | SanityTest9.v |
| ST10 | EvenParity = NOT(OddParity) | SanityTest10.v |
| ST12 | HammingDist(A,B) = PopCount(XOR(A,B)) | SanityTest12.v |
| ST13 | Equality = AND(XNOR(ai,bi)...) | SanityTest13.v |
| ST17 | Incrementer = RippleCarry(A, 1) | SanityTest17.v |
| ST18 | Mux = OR(AND(NOT(s),a), AND(s,b)) | SanityTest18.v |
| ST19 | Decoder(Encoder(x)) = x | SanityTest19.v |

## License

MIT

## Citation

```bibtex
@software{coq_circuits_2025,
  title={Coq Circuits: Formally Verified Threshold Logic Computer},
  author={Norton, Charles},
  url={https://github.com/CharlesCNorton/coq-circuits},
  year={2025}
}
```
