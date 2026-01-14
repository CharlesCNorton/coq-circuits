# Coq Circuits Development Workflow

This document defines the standard workflow for creating verified threshold logic circuits.

## Phase 1: Circuit Design

### 1.1 Mathematical Specification
Define the Boolean function to implement:
- Input domain (typically 8-bit binary)
- Output range (Boolean or natural number)
- Correctness property

### 1.2 Weight Function Design
Design algebraic weight pattern:
- Determine layer architecture
- Define weight functions (not individual weights)
- Calculate bias values

Example for MOD-m:
```coq
Definition weight_at (m : Z) (i : Z) : Z :=
  if Z.eqb (i mod m) 0 then (1 - m) else 1.
```

## Phase 2: Coq Implementation

### 2.1 Import Base Library
```coq
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.WeightPatterns.
Require Import Base.Verification.
```

### 2.2 Define Core Function
```coq
Fixpoint hamming_weight (xs : list bool) : nat := ...

Definition target_function (xs : list bool) : nat := ...
```

### 2.3 Define Network Architecture
```coq
Definition layer1_neurons : list (list Z * Z) := ...
Definition layer2_neurons : list (list Z * Z) := ...
Definition output_neurons : list (list Z * Z) := ...

Definition network (xs : list bool) : list bool := ...
Definition predict (xs : list bool) : nat := ...
```

### 2.4 Write Proofs

#### Exhaustive Verification
```coq
Theorem network_correct_exhaustive : verify_all = true.
Proof. vm_compute. reflexivity. Qed.
```

#### Constructive Verification
```coq
Theorem network_correct_constructive : forall x0 x1 x2 x3 x4 x5 x6 x7,
  predict [x0; x1; x2; x3; x4; x5; x6; x7] =
  target_function [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros x0 x1 x2 x3 x4 x5 x6 x7.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.
```

#### Algebraic Verification
```coq
Definition cumsum (k : nat) : Z := ...

Theorem cumsum_eq_target : forall k,
  (k <= 8)%nat -> cumsum k = Z.of_nat (target_function_value k).
Proof. ... Qed.
```

### 2.5 Verify Axiom-Free
```coq
Print Assumptions network_correct_exhaustive.
Print Assumptions network_correct_constructive.
Print Assumptions cumsum_eq_target.
```

All should output: `Closed under the global context`

## Phase 3: OCaml Extraction

### 3.1 Create Extraction Module
```coq
(* In coq/Extraction/ExtractCircuitName.v *)
Require Extraction.
Require Import CategoryName.CircuitName.

Extraction Language OCaml.
Extraction "extracted/category/circuit_name.ml" predict network.
```

### 3.2 Compile Extraction
```bash
coqc -R coq "" coq/Extraction/ExtractCircuitName.v
```

### 3.3 Verify Extracted Code
Check that extracted OCaml compiles:
```bash
ocamlc -c extracted/category/circuit_name.ml
```

## Phase 4: Weight Generation

### 4.1 Extract Weight Values
Run extracted OCaml code to enumerate all weights and biases.

### 4.2 Convert to Tensors
Format as PyTorch tensors or NumPy arrays.

### 4.3 Save as SafeTensors
```python
from safetensors.torch import save_file
import torch

weights_dict = {
    'layer1.weight': torch.tensor(...),
    'layer1.bias': torch.tensor(...),
    'layer2.weight': torch.tensor(...),
    'layer2.bias': torch.tensor(...),
    'output.weight': torch.tensor(...),
    'output.bias': torch.tensor(...),
}

save_file(weights_dict, 'weights/category/circuit_name.safetensors')
```

## Phase 5: HuggingFace Publishing

### 5.1 Create Model Card
Write `README.md` with:
- Circuit description
- Architecture table
- Verification summary
- Usage example
- Citation

### 5.2 Upload to HuggingFace
```bash
huggingface-cli upload phanerozoic/circuit-name-verified \
  weights/category/circuit_name.safetensors \
  --repo-type model
```

### 5.3 Link Documentation
Update main README with link to HuggingFace model.

## Phase 6: Testing and Validation

### 6.1 Exhaustive Testing
Run inference on all 256 inputs, verify matches Coq proof.

### 6.2 Performance Benchmarking
Measure inference time and throughput.

### 6.3 Cross-Validation
Compare extracted OCaml output with SafeTensors inference.

## Naming Conventions

### Coq Files
- PascalCase: `ModMParametric.v`, `HalfAdder.v`
- Match category subdirectory

### OCaml Files
- snake_case: `mod_m_parametric.ml`, `half_adder.ml`
- Include `.mli` interface files

### SafeTensors Files
- snake_case: `mod_m_parametric.safetensors`
- Match directory structure

### HuggingFace Models
- kebab-case: `circuit-name-verified`
- Prefix: `phanerozoic/`

## File Organization Standard

Each circuit requires:
```
coq/Category/CircuitName.v              # Coq proof
coq/Extraction/ExtractCircuitName.v     # Extraction module
extracted/category/circuit_name.ml      # Extracted OCaml
extracted/category/circuit_name.mli     # OCaml interface
weights/category/circuit_name.safetensors  # Verified weights
docs/circuits/category.md               # Documentation
```

## Checklist

Before considering a circuit complete:

- [ ] Coq proof compiles without errors
- [ ] Exhaustive verification passes
- [ ] Constructive verification passes
- [ ] Algebraic verification passes (if applicable)
- [ ] All proofs are axiom-free
- [ ] OCaml extraction succeeds
- [ ] Extracted code compiles
- [ ] Weights generated in SafeTensors format
- [ ] Exhaustive testing passes (256/256)
- [ ] HuggingFace model uploaded
- [ ] Model card written
- [ ] Documentation updated
- [ ] Examples provided

## Standards Compliance

All circuits must:
- Use 8-bit inputs (list bool of length 8)
- Use Heaviside activation (x >= 0 → 1)
- Provide three proof types
- Be axiom-free
- Follow naming conventions
- Include distribution statistics
- Document weight patterns
