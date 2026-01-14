# Coq Circuits Development Checklist

Complete circuits in this order to ensure constructive development with proper dependency management and sanity testing.

## Phase 1: Base Library (Items 1-5)

- [ ] 1. `coq/Base/Definitions.v` - Core definitions (hamming_weight, dot, gate, layer)
- [ ] 2. `coq/Base/Tactics.v` - Standard proof tactics
- [ ] 3. `coq/Base/WeightPatterns.v` - Weight generation functions
- [ ] 4. `coq/Base/Verification.v` - Verification framework (all_inputs, verify_all)
- [ ] 5. `coq/Base/Composition.v` - Circuit composition rules

**Milestone**: Base library complete and tested

---

## Phase 2: Boolean Logic Gates (Items 6-14)

### Single Input
- [ ] 6. `coq/Boolean/NOT.v` - NOT gate (simplest: single input)

### Two Inputs (Basic)
- [ ] 7. `coq/Boolean/AND.v` - AND gate
- [ ] 8. `coq/Boolean/OR.v` - OR gate
- [ ] 9. `coq/Boolean/NAND.v` - NAND gate
- [ ] 10. `coq/Boolean/NOR.v` - NOR gate

### Two Inputs (Derived)
- [ ] 11. `coq/Boolean/XOR.v` - XOR gate
- [ ] 12. `coq/Boolean/XNOR.v` - XNOR gate
- [ ] 13. `coq/Boolean/Implies.v` - Implies gate
- [ ] 14. `coq/Boolean/BiImplies.v` - BiImplies gate

**Sanity Test 1**: Compose NAND gates to build AND, verify equivalence
```coq
(* AND(a,b) = NAND(NAND(a,b), NAND(a,b)) *)
```

**Milestone**: All Boolean gates verified and composition tested

---

## Phase 3: Threshold Functions (Items 15-27)

### Basic Thresholds
- [ ] 15. `coq/Threshold/Majority.v` - Majority (≥5 of 8 bits) [MIGRATE FROM majority-verified]
- [ ] 16. `coq/Threshold/Minority.v` - Minority (≤3 of 8 bits)

### Exact k-out-of-n
- [ ] 17. `coq/Threshold/OneOutOfEight.v` - Exactly 1 bit set
- [ ] 18. `coq/Threshold/TwoOutOfEight.v` - Exactly 2 bits set
- [ ] 19. `coq/Threshold/ThreeOutOfEight.v` - Exactly 3 bits set
- [ ] 20. `coq/Threshold/FourOutOfEight.v` - Exactly 4 bits set
- [ ] 21. `coq/Threshold/FiveOutOfEight.v` - Exactly 5 bits set
- [ ] 22. `coq/Threshold/SixOutOfEight.v` - Exactly 6 bits set
- [ ] 23. `coq/Threshold/SevenOutOfEight.v` - Exactly 7 bits set
- [ ] 24. `coq/Threshold/AllOutOfEight.v` - All 8 bits set

### Parametric Thresholds
- [ ] 25. `coq/Threshold/AtLeastK.v` - At least k bits set (parametric)
- [ ] 26. `coq/Threshold/AtMostK.v` - At most k bits set (parametric)
- [ ] 27. `coq/Threshold/ExactlyK.v` - Exactly k bits set (parametric)
- [ ] 28. `coq/Threshold/KOutOfN.v` - General k-out-of-n (fully parametric)

**Sanity Test 2**: Verify Majority = FiveOutOfEight = AtLeastK(5)
```coq
(* Test that different implementations produce identical results *)
```

**Milestone**: All threshold functions verified and equivalences tested

---

## Phase 4: Modular Arithmetic (Items 29-40)

### Parametric Foundation
- [ ] 29. `coq/Modular/ModMParametric.v` - General MOD-m proof (m ≥ 2) [MIGRATE FROM modm-verified]

### Specific Instances
- [ ] 30. `coq/Modular/Mod2.v` - MOD-2 (Parity/XOR) [MIGRATE FROM existing parity]
- [ ] 31. `coq/Modular/Mod3.v` - MOD-3 [MIGRATE FROM mod3-verified]
- [ ] 32. `coq/Modular/Mod4.v` - MOD-4
- [ ] 33. `coq/Modular/Mod5.v` - MOD-5 [MIGRATE FROM mod5-verified]
- [ ] 34. `coq/Modular/Mod6.v` - MOD-6
- [ ] 35. `coq/Modular/Mod7.v` - MOD-7 [MIGRATE FROM mod7-verified]
- [ ] 36. `coq/Modular/Mod8.v` - MOD-8
- [ ] 37. `coq/Modular/Mod9.v` - MOD-9
- [ ] 38. `coq/Modular/Mod10.v` - MOD-10
- [ ] 39. `coq/Modular/Mod11.v` - MOD-11
- [ ] 40. `coq/Modular/Mod12.v` - MOD-12

**Sanity Test 3**: Verify MOD-2 = XOR of all bits = Parity
```coq
(* Test that Mod2.predict = XOR.predict = ParityChecker *)
```

**Milestone**: All MOD-m circuits verified through m=12

---

## Phase 5: Arithmetic - Building Blocks (Items 41-43)

### Basic Adders
- [ ] 41. `coq/Arithmetic/HalfAdder.v` - Half adder (sum + carry from 2 bits)
- [ ] 42. `coq/Arithmetic/FullAdder.v` - Full adder (sum + carry from 3 bits)

**Sanity Test 4a**: Build 2-bit adder from 1 half + 1 full adder
```coq
(* Compose: HalfAdder + FullAdder = 2-bit ripple carry *)
```

- [ ] 43. `coq/Arithmetic/RippleCarry2Bit.v` - 2-bit ripple carry adder

**Sanity Test 4b**: Verify composed adder = RippleCarry2Bit
```coq
(* Test composition matches direct implementation *)
```

**Milestone**: Basic adder building blocks verified

---

## Phase 6: Arithmetic - Multi-Bit Adders (Items 44-45)

- [ ] 44. `coq/Arithmetic/RippleCarry4Bit.v` - 4-bit ripple carry adder
- [ ] 45. `coq/Arithmetic/RippleCarry8Bit.v` - 8-bit ripple carry adder

**Sanity Test 5**: Compose two 4-bit adders to build 8-bit adder
```coq
(* Verify compositional construction matches direct implementation *)
```

**Milestone**: All ripple carry adders complete

---

## Phase 7: Arithmetic - Increment/Decrement (Items 46-47)

- [ ] 46. `coq/Arithmetic/Incrementer8Bit.v` - 8-bit incrementer (+1)
- [ ] 47. `coq/Arithmetic/Decrementer8Bit.v` - 8-bit decrementer (-1)

**Sanity Test 6**: Verify Incrementer uses RippleCarry with constant 1
```coq
(* Test: Incrementer(x) = RippleCarry(x, 00000001) *)
```

**Milestone**: Inc/Dec operations verified

---

## Phase 8: Arithmetic - Comparators (Items 48-52)

### Basic Comparisons
- [ ] 48. `coq/Arithmetic/Equality8Bit.v` - Equality checker (a = b)
- [ ] 49. `coq/Arithmetic/GreaterThan8Bit.v` - Greater than (a > b)
- [ ] 50. `coq/Arithmetic/LessThan8Bit.v` - Less than (a < b)
- [ ] 51. `coq/Arithmetic/GreaterOrEqual8Bit.v` - Greater or equal (a ≥ b)
- [ ] 52. `coq/Arithmetic/LessOrEqual8Bit.v` - Less or equal (a ≤ b)

**Sanity Test 7**: Verify comparison relationships
```coq
(* Test: GreaterOrEqual(a,b) = OR(GreaterThan(a,b), Equality(a,b)) *)
(* Test: LessThan(a,b) = NOT(GreaterOrEqual(a,b)) *)
```

**Milestone**: All comparators verified with consistency checks

---

## Phase 9: Arithmetic - Max/Min (Items 53-54)

- [ ] 53. `coq/Arithmetic/Max8Bit.v` - Maximum of two 8-bit values
- [ ] 54. `coq/Arithmetic/Min8Bit.v` - Minimum of two 8-bit values

**Sanity Test 8**: Verify Max/Min use comparators
```coq
(* Test: Max(a,b) = if GreaterThan(a,b) then a else b *)
(* Test: Min(a,b) = if LessThan(a,b) then a else b *)
```

**Milestone**: Max/Min operations verified

---

## Phase 10: Arithmetic - Multipliers (Items 55-56)

- [ ] 55. `coq/Arithmetic/Multiplier2x2.v` - 2-bit × 2-bit multiplier
- [ ] 56. `coq/Arithmetic/Multiplier4x4.v` - 4-bit × 4-bit multiplier

**Sanity Test 9**: Build 4×4 multiplier from 2×2 multipliers + adders
```coq
(* Test compositional construction *)
```

**Milestone**: Multipliers verified

---

## Phase 11: Arithmetic - Advanced Operations (Item 57)

- [ ] 57. `coq/Arithmetic/AbsoluteDifference8Bit.v` - |a - b|

**Sanity Test 10**: Verify uses comparator + adder/subtractor
```coq
(* Test: AbsDiff(a,b) = if a>b then a-b else b-a *)
```

**Milestone**: All arithmetic circuits complete (17 total)

---

## Phase 12: Error Detection - Basic Parity (Items 58-61)

- [ ] 58. `coq/ErrorDetection/ParityChecker8Bit.v` - Even parity checker
- [ ] 59. `coq/ErrorDetection/ParityGenerator8Bit.v` - Parity bit generator
- [ ] 60. `coq/ErrorDetection/EvenParityChecker.v` - Even parity checker (explicit)
- [ ] 61. `coq/ErrorDetection/OddParityChecker.v` - Odd parity checker

**Sanity Test 11**: Verify ParityChecker = Mod2
```coq
(* Test: ParityChecker8Bit = Mod2 = XOR of all bits *)
```

**Milestone**: Basic parity circuits verified

---

## Phase 13: Error Detection - Advanced (Items 62-68)

### Checksums
- [ ] 62. `coq/ErrorDetection/Checksum8Bit.v` - Simple checksum
- [ ] 63. `coq/ErrorDetection/LongitudinalParity.v` - Longitudinal parity check

### Hamming Codes
- [ ] 64. `coq/ErrorDetection/HammingEncode4Bit.v` - Hamming(7,4) encoder
- [ ] 65. `coq/ErrorDetection/HammingDecode7Bit.v` - Hamming(7,4) decoder
- [ ] 66. `coq/ErrorDetection/HammingSyndrome.v` - Syndrome calculator

### CRC
- [ ] 67. `coq/ErrorDetection/CRC4.v` - CRC-4
- [ ] 68. `coq/ErrorDetection/CRC8.v` - CRC-8

**Sanity Test 12**: Verify Hamming encode/decode round-trip
```coq
(* Test: HammingDecode(HammingEncode(x)) = x for all valid x *)
```

**Milestone**: All error detection circuits complete (11 total)

---

## Phase 14: Pattern Recognition - Basic Detectors (Items 69-74)

- [ ] 69. `coq/PatternRecognition/AllOnes.v` - All bits set (11111111)
- [ ] 70. `coq/PatternRecognition/AllZeros.v` - All bits clear (00000000)
- [ ] 71. `coq/PatternRecognition/OneHotDetector.v` - Exactly one bit set
- [ ] 72. `coq/PatternRecognition/LeadingOnes.v` - Count leading 1s
- [ ] 73. `coq/PatternRecognition/TrailingOnes.v` - Count trailing 1s
- [ ] 74. `coq/PatternRecognition/PopCount.v` - Population count (Hamming weight)

**Sanity Test 13**: Verify PopCount outputs actual Hamming weight
```coq
(* Test: PopCount(x) = hamming_weight(x) as output value *)
```

**Sanity Test 14**: Verify OneHotDetector = ExactlyK(1)
```coq
(* Test consistency with threshold functions *)
```

**Milestone**: Basic pattern detectors verified

---

## Phase 15: Pattern Recognition - Advanced (Items 75-78)

- [ ] 75. `coq/PatternRecognition/Symmetry8Bit.v` - Palindrome detector
- [ ] 76. `coq/PatternRecognition/Alternating8Bit.v` - 01010101 or 10101010 detector
- [ ] 77. `coq/PatternRecognition/RunLength.v` - Longest run of 1s
- [ ] 78. `coq/PatternRecognition/HammingDistance8Bit.v` - Hamming distance between inputs

**Sanity Test 15**: Verify Alternating uses XOR pattern
```coq
(* Test: Alternating(x) checks xi XOR x(i+1) = 1 for all i *)
```

**Milestone**: All pattern recognition complete (10 total)

---

## Phase 16: Combinational - Multiplexers (Items 79-81)

- [ ] 79. `coq/Combinational/Multiplexer2to1.v` - 2-to-1 mux
- [ ] 80. `coq/Combinational/Multiplexer4to1.v` - 4-to-1 mux
- [ ] 81. `coq/Combinational/Multiplexer8to1.v` - 8-to-1 mux

**Sanity Test 16**: Build 4-to-1 mux from three 2-to-1 muxes
```coq
(* Test compositional construction *)
```

**Milestone**: All multiplexers verified

---

## Phase 17: Combinational - Demultiplexers (Items 82-84)

- [ ] 82. `coq/Combinational/Demultiplexer1to2.v` - 1-to-2 demux
- [ ] 83. `coq/Combinational/Demultiplexer1to4.v` - 1-to-4 demux
- [ ] 84. `coq/Combinational/Demultiplexer1to8.v` - 1-to-8 demux

**Sanity Test 17**: Verify mux/demux reversibility
```coq
(* Test: Demux(Mux(inputs, sel), sel) = inputs *)
```

**Milestone**: All demultiplexers verified

---

## Phase 18: Combinational - Encoders/Decoders (Items 85-86)

- [ ] 85. `coq/Combinational/Encoder8to3.v` - 8-to-3 priority encoder
- [ ] 86. `coq/Combinational/Decoder3to8.v` - 3-to-8 decoder

**Sanity Test 18**: Verify encoder/decoder are inverses
```coq
(* Test: Encoder(Decoder(x)) = x for valid x *)
(* Test: Decoder(Encoder(onehot)) = onehot *)
```

**Milestone**: Encoders/decoders verified

---

## Phase 19: Combinational - Advanced (Items 87-88)

- [ ] 87. `coq/Combinational/PriorityEncoder8Bit.v` - Priority encoder (highest bit)
- [ ] 88. `coq/Combinational/BarrelShifter8Bit.v` - Barrel shifter

**Sanity Test 19**: Verify barrel shifter composition
```coq
(* Test: Multiple shifts compose correctly *)
(* Test: Shift(Shift(x, a), b) = Shift(x, a+b) *)
```

**Milestone**: All combinational circuits complete (10 total)

---

## Phase 20: OCaml Extraction (Items 89-95)

- [ ] 89. `coq/Extraction/ExtractModular.v` - Extract all MOD-m circuits
- [ ] 90. `coq/Extraction/ExtractBoolean.v` - Extract all Boolean gates
- [ ] 91. `coq/Extraction/ExtractThreshold.v` - Extract all threshold functions
- [ ] 92. `coq/Extraction/ExtractArithmetic.v` - Extract all arithmetic circuits
- [ ] 93. `coq/Extraction/ExtractErrorDetection.v` - Extract error detection
- [ ] 94. `coq/Extraction/ExtractPatternRecognition.v` - Extract pattern recognition
- [ ] 95. `coq/Extraction/ExtractCombinational.v` - Extract combinational logic

**Milestone**: All OCaml code extracted

---

## Phase 21: Weight Generation (Items 96-102)

Generate `.safetensors` files for each category:

- [ ] 96. Generate all Modular weights (12 files)
- [ ] 97. Generate all Boolean weights (9 files)
- [ ] 98. Generate all Threshold weights (13 files)
- [ ] 99. Generate all Arithmetic weights (17 files)
- [ ] 100. Generate all Error Detection weights (11 files)
- [ ] 101. Generate all Pattern Recognition weights (10 files)
- [ ] 102. Generate all Combinational weights (10 files)

**Milestone**: All 82 weight files generated

---

## Phase 22: HuggingFace Publishing (Items 103-109)

Upload models to HuggingFace by category:

- [ ] 103. Upload Modular circuits (12 models)
- [ ] 104. Upload Boolean circuits (9 models)
- [ ] 105. Upload Threshold circuits (13 models)
- [ ] 106. Upload Arithmetic circuits (17 models)
- [ ] 107. Upload Error Detection circuits (11 models)
- [ ] 108. Upload Pattern Recognition circuits (10 models)
- [ ] 109. Upload Combinational circuits (10 models)

**Milestone**: All 82 models on HuggingFace

---

## Phase 23: Integration Testing (Items 110-115)

### Composition Tests
- [ ] 110. Test Boolean gate compositions (NAND → AND, etc.)
- [ ] 111. Test threshold function equivalences
- [ ] 112. Test modular = parity for MOD-2
- [ ] 113. Test arithmetic compositions (half+full → ripple)
- [ ] 114. Test mux/demux reversibility
- [ ] 115. Test encoder/decoder inverses

### Cross-Category Tests
- [ ] 116. Test parity checker = MOD-2 = XOR chain
- [ ] 117. Test PopCount = Hamming weight output
- [ ] 118. Test Majority = 5-out-of-8 = AtLeastK(5)
- [ ] 119. Test incrementer uses ripple carry
- [ ] 120. Test max/min use comparators

**Milestone**: All composition and integration tests pass

---

## Phase 24: Documentation (Items 121-127)

- [ ] 121. Complete `docs/getting-started.md`
- [ ] 122. Complete `docs/framework-design.md`
- [ ] 123. Complete `docs/proof-patterns.md`
- [ ] 124. Complete `docs/weight-patterns.md`
- [ ] 125. Complete `docs/composition.md`
- [ ] 126. Complete all category docs (7 files)
- [ ] 127. Complete all example docs (4 files)

**Milestone**: Complete documentation

---

## Phase 25: Repository Cleanup (Items 128-132)

- [ ] 128. Add deprecation notices to old repos
- [ ] 129. Update all old repo READMEs to point to `coq-circuits`
- [ ] 130. Create migration guide
- [ ] 131. Archive old repositories
- [ ] 132. Update HuggingFace model cards with new repo links

**Final Milestone**: Repository unification complete

---

## Summary Statistics

- **Total Items**: 132
- **Coq Circuits**: 82
- **Sanity Tests**: 19
- **Integration Tests**: 10
- **Major Milestones**: 25

## Progress Tracking

- [ ] Phase 1: Base Library (5 items)
- [ ] Phase 2: Boolean Logic (9 items + 1 test)
- [ ] Phase 3: Threshold Functions (13 items + 1 test)
- [ ] Phase 4: Modular Arithmetic (12 items + 1 test)
- [ ] Phase 5-11: Arithmetic Circuits (17 items + 5 tests)
- [ ] Phase 12-13: Error Detection (11 items + 2 tests)
- [ ] Phase 14-15: Pattern Recognition (10 items + 2 tests)
- [ ] Phase 16-19: Combinational Logic (10 items + 4 tests)
- [ ] Phase 20: OCaml Extraction (7 items)
- [ ] Phase 21: Weight Generation (7 items)
- [ ] Phase 22: HuggingFace Publishing (7 items)
- [ ] Phase 23: Integration Testing (11 items)
- [ ] Phase 24: Documentation (7 items)
- [ ] Phase 25: Repository Cleanup (5 items)

**Current Status**: 0/132 complete (0%)
