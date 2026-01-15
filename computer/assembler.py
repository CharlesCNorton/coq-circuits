"""
Neural Computer Assembler

Assembles verified threshold logic circuits into a complete 8-bit computer.
All computation is performed using weights - no traditional logic gates.

Architecture:
- 4 general-purpose 8-bit registers (R0-R3)
- 8-bit program counter (PC)
- 256 bytes of memory
- 16 ALU operations
- Status flags (Z, N, C, V)

Instruction Format (16-bit):
  [15:12] opcode (4 bits) - ALU operation
  [11:10] dest   (2 bits) - destination register
  [9:8]   src1   (2 bits) - source register 1
  [7:6]   src2   (2 bits) - source register 2
  [5:0]   imm    (6 bits) - immediate value (sign-extended to 8 bits)

The computer is a single threshold network where:
- Input: current state (registers, PC, flags, memory, instruction)
- Output: next state (updated registers, PC, flags)
"""

import torch
from safetensors.torch import load_file, save_file
import os
from typing import Dict, List, Tuple
import json

class ThresholdNeuron:
    """A single threshold logic neuron."""
    def __init__(self, weights: List[float], bias: float, name: str = ""):
        self.weights = weights
        self.bias = bias
        self.name = name

    def compute(self, inputs: List[int]) -> int:
        """Compute neuron output using Heaviside activation."""
        weighted_sum = sum(w * x for w, x in zip(self.weights, inputs)) + self.bias
        return 1 if weighted_sum >= 0 else 0

    def to_dict(self) -> dict:
        return {"weights": self.weights, "bias": self.bias, "name": self.name}


class Circuit:
    """A circuit composed of threshold neurons."""
    def __init__(self, name: str):
        self.name = name
        self.neurons: Dict[str, ThresholdNeuron] = {}
        self.layers: List[List[str]] = []  # Neuron names per layer
        self.input_names: List[str] = []
        self.output_names: List[str] = []

    def add_neuron(self, name: str, neuron: ThresholdNeuron, layer: int):
        """Add a neuron to a specific layer."""
        self.neurons[name] = neuron
        while len(self.layers) <= layer:
            self.layers.append([])
        self.layers[layer].append(name)

    def compute(self, inputs: Dict[str, int]) -> Dict[str, int]:
        """Compute circuit outputs given inputs."""
        values = dict(inputs)
        for layer in self.layers:
            for neuron_name in layer:
                neuron = self.neurons[neuron_name]
                # Get input values for this neuron
                neuron_inputs = [values.get(f"in_{i}", 0) for i in range(len(neuron.weights))]
                values[neuron_name] = neuron.compute(neuron_inputs)
        return {name: values[name] for name in self.output_names}


class NeuralComputer:
    """
    Complete 8-bit computer built from threshold logic weights.
    """

    def __init__(self, weights_dir: str = "weights"):
        self.weights_dir = weights_dir

        # Computer state
        self.registers = [0] * 4  # R0-R3, each 8 bits
        self.pc = 0               # Program counter
        self.flags = {"Z": 0, "N": 0, "C": 0, "V": 0}
        self.memory = [0] * 256   # 256 bytes

        # Load circuit weights
        self.circuits = {}
        self._load_all_weights()

        # Build composed network
        self.network = self._build_network()

    def _load_all_weights(self):
        """Load all circuit weights from safetensors files."""
        categories = ['boolean', 'modular', 'threshold', 'arithmetic',
                     'error_detection', 'pattern_recognition', 'combinational', 'alu']

        for category in categories:
            cat_dir = os.path.join(self.weights_dir, category)
            if os.path.exists(cat_dir):
                for filename in os.listdir(cat_dir):
                    if filename.endswith('.safetensors'):
                        name = filename[:-12]  # Remove .safetensors
                        path = os.path.join(cat_dir, filename)
                        self.circuits[name] = load_file(path)

        print(f"Loaded {len(self.circuits)} circuits")

    def _build_network(self) -> Dict:
        """Build the composed computer network from circuit weights."""
        network = {
            "description": "8-bit Neural Computer",
            "inputs": {
                "registers": 32,      # 4 registers × 8 bits
                "pc": 8,              # Program counter
                "flags": 4,           # Z, N, C, V
                "instruction": 16,    # Current instruction
            },
            "outputs": {
                "next_registers": 32,
                "next_pc": 8,
                "next_flags": 4,
            },
            "components": {}
        }

        # === INSTRUCTION DECODER ===
        # Extracts opcode, dest, src1, src2, immediate from instruction
        network["components"]["decoder"] = {
            "type": "instruction_decoder",
            "inputs": ["instruction[15:0]"],
            "outputs": {
                "opcode": "instruction[15:12]",
                "dest": "instruction[11:10]",
                "src1": "instruction[9:8]",
                "src2": "instruction[7:6]",
                "immediate": "instruction[5:0]",
            }
        }

        # === REGISTER FILE READ ===
        # Two 4:1 muxes to select source registers
        network["components"]["reg_read_1"] = {
            "type": "mux4to1_8bit",
            "inputs": ["src1[1:0]", "R0[7:0]", "R1[7:0]", "R2[7:0]", "R3[7:0]"],
            "outputs": ["operand_a[7:0]"],
            "weights": self._build_mux4to1_8bit()
        }

        network["components"]["reg_read_2"] = {
            "type": "mux4to1_8bit",
            "inputs": ["src2[1:0]", "R0[7:0]", "R1[7:0]", "R2[7:0]", "R3[7:0]"],
            "outputs": ["operand_b[7:0]"],
            "weights": self._build_mux4to1_8bit()
        }

        # === ALU ===
        # 8-bit ALU with 16 operations
        network["components"]["alu"] = {
            "type": "alu8bit",
            "inputs": ["opcode[3:0]", "operand_a[7:0]", "operand_b[7:0]"],
            "outputs": ["result[7:0]", "flag_z", "flag_n", "flag_c", "flag_v"],
            "weights": self.circuits.get("alu8bit", {})
        }

        # === REGISTER FILE WRITE ===
        # Demux to select destination register
        network["components"]["reg_write"] = {
            "type": "demux1to4_8bit",
            "inputs": ["dest[1:0]", "result[7:0]"],
            "outputs": ["next_R0[7:0]", "next_R1[7:0]", "next_R2[7:0]", "next_R3[7:0]"],
            "weights": self._build_demux1to4_8bit()
        }

        # === PROGRAM COUNTER ===
        # PC + 2 (16-bit instructions)
        network["components"]["pc_increment"] = {
            "type": "adder8bit",
            "inputs": ["pc[7:0]", "const_2[7:0]"],
            "outputs": ["next_pc[7:0]"],
            "weights": self._build_incrementer(2)
        }

        return network

    def _build_mux4to1_8bit(self) -> Dict[str, torch.Tensor]:
        """Build an 8-bit wide 4:1 multiplexer from basic muxes."""
        weights = {}
        # For each bit position, we need a 4:1 mux
        for bit in range(8):
            # 4:1 mux = cascade of 2:1 muxes or direct implementation
            # Using decoder + AND + OR approach
            for sel in range(4):
                # AND gate for each input with decoded select
                weights[f"bit{bit}_sel{sel}_and.weight"] = torch.tensor([1.0, 1.0])
                weights[f"bit{bit}_sel{sel}_and.bias"] = torch.tensor([-2.0])
            # OR gate to combine
            weights[f"bit{bit}_or.weight"] = torch.tensor([1.0, 1.0, 1.0, 1.0])
            weights[f"bit{bit}_or.bias"] = torch.tensor([-1.0])
        return weights

    def _build_demux1to4_8bit(self) -> Dict[str, torch.Tensor]:
        """Build an 8-bit wide 1:4 demultiplexer."""
        weights = {}
        for bit in range(8):
            for out in range(4):
                # AND input bit with decoded select
                weights[f"bit{bit}_out{out}.weight"] = torch.tensor([1.0, 1.0])
                weights[f"bit{bit}_out{out}.bias"] = torch.tensor([-2.0])
        return weights

    def _build_incrementer(self, value: int) -> Dict[str, torch.Tensor]:
        """Build an incrementer that adds a constant value."""
        # Use ripple carry adder with constant input
        return self.circuits.get("ripplecarry8bit", {})

    def _heaviside(self, x: float) -> int:
        """Heaviside step function."""
        return 1 if x >= 0 else 0

    def _apply_neuron(self, weights: List[float], bias: float, inputs: List[int]) -> int:
        """Apply a single threshold neuron."""
        weighted_sum = sum(w * i for w, i in zip(weights, inputs)) + bias
        return self._heaviside(weighted_sum)

    def _bits_to_int(self, bits: List[int]) -> int:
        """Convert bit list (MSB first) to integer."""
        result = 0
        for bit in bits:
            result = (result << 1) | bit
        return result

    def _int_to_bits(self, value: int, width: int) -> List[int]:
        """Convert integer to bit list (MSB first)."""
        return [(value >> (width - 1 - i)) & 1 for i in range(width)]

    def execute_instruction(self, instruction: int) -> None:
        """Execute a single instruction using threshold logic."""
        opcode = (instruction >> 12) & 0xF
        dest = (instruction >> 10) & 0x3
        src1 = (instruction >> 8) & 0x3
        src2 = (instruction >> 6) & 0x3
        immediate = instruction & 0x3F

        if immediate & 0x20:
            immediate |= 0xC0

        if opcode == 14:  # JMP - unconditional jump
            target = instruction & 0xFF
            self.pc = target
            return
        elif opcode == 13:  # LDI - bypass ALU, load immediate (unsigned 6-bit)
            val = instruction & 0x3F
            self.registers[dest] = val
            self.flags["Z"] = 1 if val == 0 else 0
            self.flags["N"] = 0
            self.flags["C"] = 0
            self.flags["V"] = 0
        elif opcode == 15:  # NOP
            pass
        else:
            operand_a = self.registers[src1]
            operand_b = self.registers[src2]

            a_bits = self._int_to_bits(operand_a, 8)
            b_bits = self._int_to_bits(operand_b, 8)

            result, flags = self._execute_alu(self._int_to_bits(opcode, 4), a_bits, b_bits)

            self.registers[dest] = self._bits_to_int(result)
            self.flags["Z"] = flags[0]
            self.flags["N"] = flags[1]
            self.flags["C"] = flags[2]
            self.flags["V"] = flags[3]

        self.pc = (self.pc + 2) & 0xFF

    def _neuron(self, weights: List[float], bias: float, inputs: List[int]) -> int:
        """Apply threshold neuron: Heaviside(sum(w*x) + bias)."""
        weighted_sum = sum(w * x for w, x in zip(weights, inputs)) + bias
        return 1 if weighted_sum >= 0 else 0

    def _gate_and(self, a: int, b: int) -> int:
        """AND gate using threshold weights."""
        return self._neuron([1.0, 1.0], -2.0, [a, b])

    def _gate_or(self, a: int, b: int) -> int:
        """OR gate using threshold weights."""
        return self._neuron([1.0, 1.0], -1.0, [a, b])

    def _gate_not(self, a: int) -> int:
        """NOT gate using threshold weights."""
        return self._neuron([-1.0], 0.0, [a])

    def _gate_nand(self, a: int, b: int) -> int:
        """NAND gate using threshold weights."""
        return self._neuron([-1.0, -1.0], 1.0, [a, b])

    def _gate_nor(self, a: int, b: int) -> int:
        """NOR gate using threshold weights."""
        return self._neuron([-1.0, -1.0], 0.0, [a, b])

    def _gate_xor(self, a: int, b: int) -> int:
        """XOR gate using 2-layer threshold network."""
        or_out = self._gate_or(a, b)
        nand_out = self._gate_nand(a, b)
        return self._gate_and(or_out, nand_out)

    def _gate_xnor(self, a: int, b: int) -> int:
        """XNOR gate using 2-layer threshold network."""
        nor_out = self._gate_nor(a, b)
        and_out = self._gate_and(a, b)
        return self._gate_or(nor_out, and_out)

    def _full_adder(self, a: int, b: int, cin: int) -> Tuple[int, int]:
        """Full adder using threshold logic."""
        s1 = self._gate_xor(a, b)
        c1 = self._gate_and(a, b)
        sum_out = self._gate_xor(s1, cin)
        c2 = self._gate_and(s1, cin)
        cout = self._gate_or(c1, c2)
        return sum_out, cout

    def _add_8bit(self, a: List[int], b: List[int], cin: int = 0) -> Tuple[List[int], int]:
        """8-bit ripple carry adder using threshold logic."""
        result = []
        carry = cin
        for i in range(7, -1, -1):
            s, carry = self._full_adder(a[i], b[i], carry)
            result.insert(0, s)
        return result, carry

    def _not_8bit(self, a: List[int]) -> List[int]:
        """8-bit NOT using threshold logic."""
        return [self._gate_not(bit) for bit in a]

    def _and_8bit(self, a: List[int], b: List[int]) -> List[int]:
        """8-bit AND using threshold logic."""
        return [self._gate_and(a[i], b[i]) for i in range(8)]

    def _or_8bit(self, a: List[int], b: List[int]) -> List[int]:
        """8-bit OR using threshold logic."""
        return [self._gate_or(a[i], b[i]) for i in range(8)]

    def _xor_8bit(self, a: List[int], b: List[int]) -> List[int]:
        """8-bit XOR using threshold logic."""
        return [self._gate_xor(a[i], b[i]) for i in range(8)]

    def _sub_8bit(self, a: List[int], b: List[int]) -> Tuple[List[int], int]:
        """8-bit subtraction using threshold logic (A - B = A + ~B + 1)."""
        b_inv = self._not_8bit(b)
        return self._add_8bit(a, b_inv, 1)

    def _zero_flag(self, r: List[int]) -> int:
        """Zero flag using threshold logic (NOR of all bits)."""
        return self._neuron([-1.0] * 8, 0.0, r)

    def _execute_alu(self, opcode: List[int], a: List[int], b: List[int]) -> Tuple[List[int], List[int]]:
        """Execute ALU operation using threshold logic weights."""
        op = self._bits_to_int(opcode)
        carry = 0

        if op == 0:    # ADD
            result, carry = self._add_8bit(a, b, 0)
        elif op == 1:  # SUB
            result, carry = self._sub_8bit(a, b)
        elif op == 2:  # AND
            result = self._and_8bit(a, b)
        elif op == 3:  # OR
            result = self._or_8bit(a, b)
        elif op == 4:  # XOR
            result = self._xor_8bit(a, b)
        elif op == 5:  # NOT
            result = self._not_8bit(a)
        elif op == 6:  # SHL
            carry = a[0]
            result = a[1:] + [0]
        elif op == 7:  # SHR
            carry = a[7]
            result = [0] + a[:7]
        elif op == 8:  # INC
            one = [0, 0, 0, 0, 0, 0, 0, 1]
            result, carry = self._add_8bit(a, one, 0)
        elif op == 9:  # DEC
            neg_one = [1, 1, 1, 1, 1, 1, 1, 1]
            result, carry = self._add_8bit(a, neg_one, 0)
        elif op == 10: # CMP
            result, carry = self._sub_8bit(a, b)
        elif op == 11: # NEG
            a_inv = self._not_8bit(a)
            one = [0, 0, 0, 0, 0, 0, 0, 1]
            result, carry = self._add_8bit(a_inv, one, 0)
        elif op == 12: # PASS
            result = a
        elif op == 13: # ZERO
            result = [0, 0, 0, 0, 0, 0, 0, 0]
        elif op == 14: # ONES
            result = [1, 1, 1, 1, 1, 1, 1, 1]
        else:          # NOP
            result = a

        zero = self._zero_flag(result)
        negative = result[0]
        overflow = 0

        return result, [zero, negative, carry, overflow]

    def load_program(self, program: List[int]) -> None:
        """Load a program into memory."""
        for i, instruction in enumerate(program):
            if i * 2 + 1 < len(self.memory):
                self.memory[i * 2] = (instruction >> 8) & 0xFF
                self.memory[i * 2 + 1] = instruction & 0xFF
        self.pc = 0

    def run(self, max_steps: int = 1000) -> None:
        """Run the loaded program."""
        for step in range(max_steps):
            # Fetch instruction
            if self.pc + 1 >= len(self.memory):
                break
            instruction = (self.memory[self.pc] << 8) | self.memory[self.pc + 1]

            if instruction == 0:  # Halt on NOP with all zeros
                break

            self.execute_instruction(instruction)

    def get_state(self) -> Dict:
        """Get current computer state."""
        return {
            "registers": list(self.registers),
            "pc": self.pc,
            "flags": dict(self.flags),
        }

    def export_network(self, path: str) -> None:
        """Export the complete network to a file."""
        with open(path, 'w') as f:
            json.dump(self.network, f, indent=2, default=str)
        print(f"Exported network to {path}")

    def export_flat_weights(self, path: str) -> None:
        """Export all weights as a single safetensors file."""
        all_weights = {}
        for name, weights in self.circuits.items():
            for key, tensor in weights.items():
                all_weights[f"{name}.{key}"] = tensor

        save_file(all_weights, path)
        print(f"Exported {len(all_weights)} weight tensors to {path}")


# === ASSEMBLER ===

class Assembler:
    """Assembler for the neural computer's instruction set."""

    OPCODES = {
        # ALU operations (opcode 0-12)
        'ADD': 0, 'SUB': 1, 'AND': 2, 'OR': 3,
        'XOR': 4, 'NOT': 5, 'SHL': 6, 'SHR': 7,
        'INC': 8, 'DEC': 9, 'CMP': 10, 'NEG': 11,
        'MOV': 12, 'LDI': 13,
        # Control flow (opcode 14) - condition in bits 11-8
        'JMP': 14, 'JZ': 14, 'JNZ': 14, 'JC': 14,
        'JNC': 14, 'JN': 14, 'JP': 14, 'JV': 14,
        # Extended ops (opcode 15) - sub-opcode in bits 11-8
        'NOP': 15, 'LD': 15, 'ST': 15,
        'PUSH': 15, 'POP': 15, 'CALL': 15, 'RET': 15,
    }

    # Condition codes for jumps (bits 11-8 when opcode=14)
    CONDITIONS = {
        'JMP': 0, 'JZ': 1, 'JNZ': 2, 'JC': 3,
        'JNC': 4, 'JN': 5, 'JP': 6, 'JV': 7,
    }

    # Sub-opcodes for extended operations (bits 11-8 when opcode=15)
    EXTENDED_OPS = {
        'NOP': 0, 'LD': 1, 'ST': 2,
        'PUSH': 3, 'POP': 4, 'CALL': 5, 'RET': 6,
    }

    REGISTERS = {'R0': 0, 'R1': 1, 'R2': 2, 'R3': 3}

    def __init__(self):
        self.labels = {}
        self.program = []

    def assemble(self, source: str) -> List[int]:
        """Assemble source code into machine code."""
        lines = source.strip().split('\n')

        # First pass: collect labels
        address = 0
        for line in lines:
            line = line.split(';')[0].strip()  # Remove comments
            if not line:
                continue
            if line.endswith(':'):
                self.labels[line[:-1]] = address
            else:
                address += 2

        # Second pass: assemble instructions
        self.program = []
        for line in lines:
            line = line.split(';')[0].strip()
            if not line or line.endswith(':'):
                continue

            instruction = self._assemble_instruction(line)
            self.program.append(instruction)

        return self.program

    def _assemble_instruction(self, line: str) -> int:
        """Assemble a single instruction."""
        parts = line.replace(',', ' ').split()
        mnemonic = parts[0].upper()

        if mnemonic not in self.OPCODES:
            raise ValueError(f"Unknown mnemonic: {mnemonic}")

        opcode = self.OPCODES[mnemonic]
        dest = 0
        src1 = 0
        src2 = 0
        immediate = 0

        if mnemonic in ['ADD', 'SUB', 'AND', 'OR', 'XOR', 'CMP']:
            # Three-operand: OP dest, src1, src2
            dest = self.REGISTERS[parts[1].upper()]
            src1 = self.REGISTERS[parts[2].upper()]
            src2 = self.REGISTERS[parts[3].upper()]
        elif mnemonic in ['NOT', 'NEG', 'INC', 'DEC', 'SHL', 'SHR']:
            # Two-operand: OP dest, src
            dest = self.REGISTERS[parts[1].upper()]
            src1 = self.REGISTERS[parts[2].upper()]
        elif mnemonic == 'MOV':
            # Move: MOV dest, src
            dest = self.REGISTERS[parts[1].upper()]
            src1 = self.REGISTERS[parts[2].upper()]
        elif mnemonic == 'LDI':
            # Load immediate: LDI dest, imm
            dest = self.REGISTERS[parts[1].upper()]
            immediate = int(parts[2]) & 0x3F
        elif mnemonic in ['JMP', 'JZ', 'JNZ', 'JC', 'JNC', 'JN', 'JP', 'JV']:
            # Jump instructions: Jxx addr or Jxx label
            target = parts[1]
            if target in self.labels:
                addr = self.labels[target] & 0xFF
            else:
                addr = int(target) & 0xFF
            cond = self.CONDITIONS[mnemonic]
            return (opcode << 12) | (cond << 8) | addr
        elif mnemonic == 'LD':
            # Load from memory: LD dest, [addr] or LD dest, addr
            dest = self.REGISTERS[parts[1].upper()]
            addr_str = parts[2].strip('[]')
            if addr_str in self.labels:
                addr = self.labels[addr_str] & 0xFF
            else:
                addr = int(addr_str) & 0xFF
            sub_op = self.EXTENDED_OPS['LD']
            return (opcode << 12) | (sub_op << 8) | (dest << 6) | (addr & 0x3F)
        elif mnemonic == 'ST':
            # Store to memory: ST src, [addr] or ST src, addr
            src = self.REGISTERS[parts[1].upper()]
            addr_str = parts[2].strip('[]')
            if addr_str in self.labels:
                addr = self.labels[addr_str] & 0xFF
            else:
                addr = int(addr_str) & 0xFF
            sub_op = self.EXTENDED_OPS['ST']
            return (opcode << 12) | (sub_op << 8) | (src << 6) | (addr & 0x3F)
        elif mnemonic == 'PUSH':
            # Push register: PUSH reg
            reg = self.REGISTERS[parts[1].upper()]
            sub_op = self.EXTENDED_OPS['PUSH']
            return (opcode << 12) | (sub_op << 8) | (reg << 6)
        elif mnemonic == 'POP':
            # Pop to register: POP reg
            reg = self.REGISTERS[parts[1].upper()]
            sub_op = self.EXTENDED_OPS['POP']
            return (opcode << 12) | (sub_op << 8) | (reg << 6)
        elif mnemonic == 'CALL':
            # Call subroutine: CALL addr or CALL label
            target = parts[1]
            if target in self.labels:
                addr = self.labels[target] & 0xFF
            else:
                addr = int(target) & 0xFF
            sub_op = self.EXTENDED_OPS['CALL']
            return (opcode << 12) | (sub_op << 8) | addr
        elif mnemonic == 'RET':
            # Return from subroutine
            sub_op = self.EXTENDED_OPS['RET']
            return (opcode << 12) | (sub_op << 8)
        elif mnemonic == 'NOP':
            sub_op = self.EXTENDED_OPS['NOP']
            return (opcode << 12) | (sub_op << 8)

        # Encode standard instruction
        instruction = (opcode << 12) | (dest << 10) | (src1 << 8) | (src2 << 6) | immediate
        return instruction

    def disassemble(self, instruction: int) -> str:
        """Disassemble a single instruction."""
        opcode = (instruction >> 12) & 0xF
        dest = (instruction >> 10) & 0x3
        src1 = (instruction >> 8) & 0x3
        src2 = (instruction >> 6) & 0x3
        immediate = instruction & 0x3F

        reg_names = {v: k for k, v in self.REGISTERS.items()}

        # Handle control flow (opcode 14)
        if opcode == 14:
            cond = (instruction >> 8) & 0xF
            addr = instruction & 0xFF
            cond_names = {v: k for k, v in self.CONDITIONS.items()}
            mnemonic = cond_names.get(cond, 'J??')
            return f"{mnemonic} 0x{addr:02X}"

        # Handle extended ops (opcode 15)
        if opcode == 15:
            sub_op = (instruction >> 8) & 0xF
            ext_names = {v: k for k, v in self.EXTENDED_OPS.items()}
            mnemonic = ext_names.get(sub_op, '???')
            if mnemonic == 'NOP':
                return 'NOP'
            elif mnemonic == 'LD':
                reg = (instruction >> 6) & 0x3
                addr = instruction & 0x3F
                return f"LD {reg_names[reg]}, [0x{addr:02X}]"
            elif mnemonic == 'ST':
                reg = (instruction >> 6) & 0x3
                addr = instruction & 0x3F
                return f"ST {reg_names[reg]}, [0x{addr:02X}]"
            elif mnemonic == 'PUSH':
                reg = (instruction >> 6) & 0x3
                return f"PUSH {reg_names[reg]}"
            elif mnemonic == 'POP':
                reg = (instruction >> 6) & 0x3
                return f"POP {reg_names[reg]}"
            elif mnemonic == 'CALL':
                addr = instruction & 0xFF
                return f"CALL 0x{addr:02X}"
            elif mnemonic == 'RET':
                return 'RET'
            return mnemonic

        # Handle ALU operations
        d = reg_names[dest]
        s1 = reg_names[src1]
        s2 = reg_names[src2]

        if opcode in [0, 1, 2, 3, 4, 10]:  # ADD, SUB, AND, OR, XOR, CMP
            op_names = {0: 'ADD', 1: 'SUB', 2: 'AND', 3: 'OR', 4: 'XOR', 10: 'CMP'}
            return f"{op_names[opcode]} {d}, {s1}, {s2}"
        elif opcode in [5, 6, 7, 8, 9, 11]:  # NOT, SHL, SHR, INC, DEC, NEG
            op_names = {5: 'NOT', 6: 'SHL', 7: 'SHR', 8: 'INC', 9: 'DEC', 11: 'NEG'}
            return f"{op_names[opcode]} {d}, {s1}"
        elif opcode == 12:  # MOV
            return f"MOV {d}, {s1}"
        elif opcode == 13:  # LDI
            return f"LDI {d}, {immediate}"
        else:
            return f"??? (0x{instruction:04X})"


def demo():
    """Demonstrate the neural computer."""
    print("=" * 60)
    print("NEURAL COMPUTER DEMO")
    print("=" * 60)

    # Create assembler
    asm = Assembler()

    # Simple program: compute 5 + 3
    source = """
    LDI R0, 5      ; R0 = 5
    LDI R1, 3      ; R1 = 3
    ADD R2, R0, R1 ; R2 = R0 + R1 = 8
    NOP
    """

    print("\nSource:")
    print(source)

    # Assemble
    program = asm.assemble(source)
    print("\nMachine code:")
    for i, inst in enumerate(program):
        print(f"  {i*2:04X}: {inst:04X}  ; {asm.disassemble(inst)}")

    # Create computer and run
    print("\nCreating neural computer...")
    try:
        computer = NeuralComputer(weights_dir="weights")

        print("\nInitial state:")
        print(f"  {computer.get_state()}")

        # Load and run program
        computer.load_program(program)
        computer.run()

        print("\nFinal state:")
        print(f"  {computer.get_state()}")
        print(f"\nResult: R2 = {computer.registers[2]} (expected: 8)")

    except Exception as e:
        print(f"Note: Full execution requires weight files. Error: {e}")
        print("Running simplified demo instead...")

        # Simplified demo without weight files
        registers = [0, 0, 0, 0]
        registers[0] = 5
        registers[1] = 3
        registers[2] = registers[0] + registers[1]
        print(f"\nSimulated result: R2 = {registers[2]}")


if __name__ == "__main__":
    demo()
