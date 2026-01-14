# Complete Repository Structure

```
coq-circuits/
├── README.md                          # Project overview and status
├── WORKFLOW.md                        # Development workflow guide
├── STRUCTURE.md                       # This file
├── LICENSE                           # MIT License
├── .gitignore                        # Git ignore rules
├── CONTRIBUTING.md                   # (To be created)
├── CITATION.cff                      # (To be created)
│
├── coq/
│   ├── _CoqProject                   # Coq build configuration
│   ├── Makefile                      # (To be created)
│   │
│   ├── Base/
│   │   ├── Definitions.v             # Core: hamming_weight, dot, gate, layer
│   │   ├── Tactics.v                 # Standard proof tactics
│   │   ├── WeightPatterns.v          # Weight generation functions
│   │   ├── Verification.v            # all_inputs, verify_all templates
│   │   └── Composition.v             # Circuit composition rules
│   │
│   ├── Modular/
│   │   ├── ModMParametric.v          # General proof for any m >= 2
│   │   ├── Mod2.v                    # Parity/XOR
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
│   ├── Boolean/
│   │   ├── AND.v
│   │   ├── OR.v
│   │   ├── NAND.v
│   │   ├── NOR.v
│   │   ├── XOR.v
│   │   ├── XNOR.v
│   │   ├── NOT.v
│   │   ├── Implies.v
│   │   └── BiImplies.v
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
│
├── extracted/
│   ├── README.md                     # Note: generated files
│   ├── modular/
│   │   ├── mod2.ml
│   │   ├── mod2.mli
│   │   ├── mod3.ml
│   │   ├── mod3.mli
│   │   ├── mod4.ml
│   │   ├── mod4.mli
│   │   ├── mod5.ml
│   │   ├── mod5.mli
│   │   ├── mod6.ml
│   │   ├── mod6.mli
│   │   ├── mod7.ml
│   │   ├── mod7.mli
│   │   ├── mod8.ml
│   │   ├── mod8.mli
│   │   ├── mod9.ml
│   │   ├── mod9.mli
│   │   ├── mod10.ml
│   │   ├── mod10.mli
│   │   ├── mod11.ml
│   │   ├── mod11.mli
│   │   ├── mod12.ml
│   │   └── mod12.mli
│   │
│   ├── boolean/
│   │   ├── and_gate.ml
│   │   ├── and_gate.mli
│   │   ├── or_gate.ml
│   │   ├── or_gate.mli
│   │   ├── nand_gate.ml
│   │   ├── nand_gate.mli
│   │   ├── nor_gate.ml
│   │   ├── nor_gate.mli
│   │   ├── xor_gate.ml
│   │   ├── xor_gate.mli
│   │   ├── xnor_gate.ml
│   │   ├── xnor_gate.mli
│   │   ├── not_gate.ml
│   │   ├── not_gate.mli
│   │   ├── implies_gate.ml
│   │   ├── implies_gate.mli
│   │   ├── biimplies_gate.ml
│   │   └── biimplies_gate.mli
│   │
│   ├── threshold/
│   │   ├── majority.ml
│   │   ├── majority.mli
│   │   ├── minority.ml
│   │   ├── minority.mli
│   │   ├── k_out_of_n.ml
│   │   ├── k_out_of_n.mli
│   │   ├── at_least_k.ml
│   │   ├── at_least_k.mli
│   │   ├── at_most_k.ml
│   │   ├── at_most_k.mli
│   │   ├── exactly_k.ml
│   │   └── exactly_k.mli
│   │
│   ├── arithmetic/
│   │   ├── half_adder.ml
│   │   ├── half_adder.mli
│   │   ├── full_adder.ml
│   │   ├── full_adder.mli
│   │   ├── ripple_carry.ml
│   │   ├── ripple_carry.mli
│   │   ├── incrementer.ml
│   │   ├── incrementer.mli
│   │   ├── decrementer.ml
│   │   ├── decrementer.mli
│   │   ├── multiplier.ml
│   │   ├── multiplier.mli
│   │   ├── comparator.ml
│   │   ├── comparator.mli
│   │   ├── equality.ml
│   │   ├── equality.mli
│   │   ├── max_min.ml
│   │   ├── max_min.mli
│   │   ├── absolute_diff.ml
│   │   └── absolute_diff.mli
│   │
│   ├── error_detection/
│   │   ├── parity_checker.ml
│   │   ├── parity_checker.mli
│   │   ├── parity_generator.ml
│   │   ├── parity_generator.mli
│   │   ├── checksum.ml
│   │   ├── checksum.mli
│   │   ├── hamming.ml
│   │   ├── hamming.mli
│   │   ├── crc.ml
│   │   └── crc.mli
│   │
│   ├── pattern_recognition/
│   │   ├── hamming_distance.ml
│   │   ├── hamming_distance.mli
│   │   ├── all_ones_zeros.ml
│   │   ├── all_ones_zeros.mli
│   │   ├── symmetry.ml
│   │   ├── symmetry.mli
│   │   ├── alternating.ml
│   │   ├── alternating.mli
│   │   ├── run_length.ml
│   │   ├── run_length.mli
│   │   ├── popcount.ml
│   │   ├── popcount.mli
│   │   ├── one_hot.ml
│   │   └── one_hot.mli
│   │
│   └── combinational/
│       ├── multiplexer.ml
│       ├── multiplexer.mli
│       ├── demultiplexer.ml
│       ├── demultiplexer.mli
│       ├── encoder.ml
│       ├── encoder.mli
│       ├── decoder.ml
│       ├── decoder.mli
│       ├── priority_encoder.ml
│       ├── priority_encoder.mli
│       ├── barrel_shifter.ml
│       └── barrel_shifter.mli
│
├── weights/
│   ├── README.md                     # Weight format documentation
│   ├── modular/
│   │   ├── mod2.safetensors
│   │   ├── mod3.safetensors
│   │   ├── mod4.safetensors
│   │   ├── mod5.safetensors
│   │   ├── mod6.safetensors
│   │   ├── mod7.safetensors
│   │   ├── mod8.safetensors
│   │   ├── mod9.safetensors
│   │   ├── mod10.safetensors
│   │   ├── mod11.safetensors
│   │   └── mod12.safetensors
│   │
│   ├── boolean/
│   │   ├── and.safetensors
│   │   ├── or.safetensors
│   │   ├── nand.safetensors
│   │   ├── nor.safetensors
│   │   ├── xor.safetensors
│   │   ├── xnor.safetensors
│   │   ├── not.safetensors
│   │   ├── implies.safetensors
│   │   └── biimplies.safetensors
│   │
│   ├── threshold/
│   │   ├── majority.safetensors
│   │   ├── minority.safetensors
│   │   ├── one_out_of_eight.safetensors
│   │   ├── two_out_of_eight.safetensors
│   │   ├── three_out_of_eight.safetensors
│   │   ├── four_out_of_eight.safetensors
│   │   ├── five_out_of_eight.safetensors
│   │   ├── six_out_of_eight.safetensors
│   │   ├── seven_out_of_eight.safetensors
│   │   └── all_out_of_eight.safetensors
│   │
│   ├── arithmetic/
│   │   ├── half_adder.safetensors
│   │   ├── full_adder.safetensors
│   │   ├── ripple_carry_2bit.safetensors
│   │   ├── ripple_carry_4bit.safetensors
│   │   ├── ripple_carry_8bit.safetensors
│   │   ├── incrementer_8bit.safetensors
│   │   ├── decrementer_8bit.safetensors
│   │   ├── multiplier_2x2.safetensors
│   │   ├── multiplier_4x4.safetensors
│   │   ├── equality_8bit.safetensors
│   │   ├── greater_than_8bit.safetensors
│   │   ├── less_than_8bit.safetensors
│   │   ├── gte_8bit.safetensors
│   │   ├── lte_8bit.safetensors
│   │   ├── max_8bit.safetensors
│   │   ├── min_8bit.safetensors
│   │   └── abs_diff_8bit.safetensors
│   │
│   ├── error_detection/
│   │   ├── parity_checker_8bit.safetensors
│   │   ├── parity_generator_8bit.safetensors
│   │   ├── even_parity.safetensors
│   │   ├── odd_parity.safetensors
│   │   ├── checksum_8bit.safetensors
│   │   ├── hamming_encode_4bit.safetensors
│   │   ├── hamming_decode_7bit.safetensors
│   │   ├── hamming_syndrome.safetensors
│   │   ├── crc4.safetensors
│   │   ├── crc8.safetensors
│   │   └── longitudinal_parity.safetensors
│   │
│   ├── pattern_recognition/
│   │   ├── hamming_distance_8bit.safetensors
│   │   ├── all_ones.safetensors
│   │   ├── all_zeros.safetensors
│   │   ├── leading_ones.safetensors
│   │   ├── trailing_ones.safetensors
│   │   ├── symmetry_8bit.safetensors
│   │   ├── alternating_8bit.safetensors
│   │   ├── run_length.safetensors
│   │   ├── popcount.safetensors
│   │   └── one_hot.safetensors
│   │
│   └── combinational/
│       ├── mux_2to1.safetensors
│       ├── mux_4to1.safetensors
│       ├── mux_8to1.safetensors
│       ├── demux_1to2.safetensors
│       ├── demux_1to4.safetensors
│       ├── demux_1to8.safetensors
│       ├── encoder_8to3.safetensors
│       ├── decoder_3to8.safetensors
│       ├── priority_encoder_8bit.safetensors
│       └── barrel_shifter_8bit.safetensors
│
├── ocaml/
│   ├── dune-project
│   ├── dune
│   ├── threshold_verified.opam
│   └── lib/
│       ├── dune
│       └── threshold_verified.ml
│
├── docs/
│   ├── index.md
│   ├── getting-started.md
│   ├── framework-design.md
│   ├── proof-patterns.md
│   ├── weight-patterns.md
│   ├── composition.md
│   ├── extraction.md
│   ├── api-reference.md
│   │
│   ├── circuits/
│   │   ├── modular.md
│   │   ├── boolean.md
│   │   ├── threshold.md
│   │   ├── arithmetic.md
│   │   ├── error-detection.md
│   │   ├── pattern-recognition.md
│   │   └── combinational.md
│   │
│   └── examples/
│       ├── basic-usage.md
│       ├── composition.md
│       ├── custom-circuits.md
│       └── neuromorphic-deployment.md
│
├── examples/
│   ├── simple_inference.ml
│   ├── compose_circuits.ml
│   ├── batch_processing.ml
│   └── neuromorphic_export.ml
│
├── benchmarks/
│   ├── performance.ml
│   ├── accuracy.ml
│   └── results.md
│
└── scripts/
    ├── build_all_coq.sh
    ├── extract_all_ocaml.sh
    ├── generate_all_weights.sh
    ├── verify_all_proofs.sh
    ├── upload_to_hf.sh
    └── generate_docs.sh
```

## Statistics

- **Total Categories**: 7
- **Total Circuits**: 82
- **Coq Files**: 87 (.v files)
- **Extraction Modules**: 7
- **Extracted OCaml Files**: 164 (.ml + .mli)
- **Weight Files**: 82 (.safetensors)

## Current Status

Repository structure created. Ready for:
1. Base library implementation
2. Circuit migration from existing repos
3. New circuit development
