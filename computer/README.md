---
license: mit
tags:
- formal-verification
- coq
- threshold-logic
- neuromorphic
- computer
- alu
---

# tiny-NeuralComputer-verified

A complete 8-bit computer built entirely from formally verified threshold logic circuits. All computation uses weights - no traditional logic gates.

## Architecture

| Component | Value |
|-----------|-------|
| Registers | 4 × 8-bit (R0-R3) |
| Memory | 256 bytes |
| Program Counter | 8-bit |
| Instruction Width | 16-bit |
| ALU Operations | 16 |
| Status Flags | 4 (Z, N, C, V) |
| Total Neurons | ~1000 |
| Total Parameters | 582 weight tensors |

## Instruction Format (16-bit)

```
[15:12] opcode   - ALU operation (4 bits)
[11:10] dest     - destination register (2 bits)
[9:8]   src1     - source register 1 (2 bits)
[7:6]   src2     - source register 2 (2 bits)
[5:0]   immediate - immediate value (6 bits, sign-extended)
```

## ALU Operations

| Opcode | Mnemonic | Operation |
|--------|----------|-----------|
| 0000 | ADD | dest = src1 + src2 |
| 0001 | SUB | dest = src1 - src2 |
| 0010 | AND | dest = src1 & src2 |
| 0011 | OR | dest = src1 \| src2 |
| 0100 | XOR | dest = src1 ^ src2 |
| 0101 | NOT | dest = ~src1 |
| 0110 | SHL | dest = src1 << 1 |
| 0111 | SHR | dest = src1 >> 1 |
| 1000 | INC | dest = src1 + 1 |
| 1001 | DEC | dest = src1 - 1 |
| 1010 | CMP | flags = src1 - src2 |
| 1011 | NEG | dest = -src1 |
| 1100 | MOV | dest = src1 |
| 1101 | LDI | dest = immediate |
| 1110 | ONES | dest = 0xFF |
| 1111 | NOP | no operation |

## Status Flags

- **Z (Zero)**: Result is zero
- **N (Negative)**: MSB of result is 1
- **C (Carry)**: Carry out from arithmetic
- **V (Overflow)**: Signed overflow occurred

## Composition

This computer is composed from 89 verified circuits:

- **9 Boolean gates**: AND, OR, NOT, NAND, NOR, XOR, XNOR, Implies, BiImplies
- **12 Modular circuits**: MOD-2 through MOD-12
- **14 Threshold functions**: Majority, k-out-of-n variants
- **17 Arithmetic circuits**: Adders, multipliers, comparators
- **11 Error detection**: Parity, Hamming, CRC
- **10 Pattern recognition**: PopCount, symmetry, detectors
- **10 Combinational**: Muxes, encoders, decoders
- **3 ALU components**: ALU8Bit, ALUControl, ALUFlags

## Usage

```python
from safetensors.torch import load_file

# Load the complete computer
weights = load_file('neural_computer.safetensors')

print(f"Loaded {len(weights)} weight tensors")

# Access individual circuit weights
and_weights = {k: v for k, v in weights.items() if k.startswith('and.')}
alu_weights = {k: v for k, v in weights.items() if k.startswith('alu8bit.')}
```

## Example Program

```asm
LDI R0, 5      ; R0 = 5
LDI R1, 3      ; R1 = 3
ADD R2, R0, R1 ; R2 = R0 + R1 = 8
NOP
```

Assembles to:
```
0000: D005  ; LDI R0, 5
0002: D403  ; LDI R1, 3
0004: 0840  ; ADD R2, R0, R1
0006: F000  ; NOP
```

## Verification

All 89 component circuits are formally verified in Coq with:
- Exhaustive testing on all inputs
- Universal quantifier proofs
- Algebraic correctness proofs
- Zero axioms (axiom-free)

Full proofs: [coq-circuits](https://github.com/CharlesCNorton/coq-circuits)

## Citation

```bibtex
@software{tiny_neuralcomputer_verified_2025,
  title={tiny-NeuralComputer-verified: Formally Verified 8-Bit Threshold Logic Computer},
  author={Norton, Charles},
  url={https://huggingface.co/phanerozoic/tiny-NeuralComputer-verified},
  year={2025}
}
```
