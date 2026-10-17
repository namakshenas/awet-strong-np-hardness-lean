# AWET strong NP-hardness, verified in Lean 4

A machine-checked verification of **Part I** of

> N. G. Hall, H. Kellerer, M. Song, *Asymmetric Weighted Earliness–Tardiness: Scheduling with a Nonrestrictive Common Due Date*, arXiv:2609.16046v1 (2026).

Part I proves that AWET with the common due date d = Σ p_j is **strongly NP-complete**. This repository formalizes that proof in a single Lean 4 file.

## Contents

| File | Description |
|---|---|
| `AWET_PartI.lean` | The complete formal proof (one file, 5,002 lines, 336 theorems) |
| `AWET_PartI_Lean_Verification_Report.pdf` | A 25-page report walking through the proof step by step |

## Main result

`AWET.AWET_strong_reduction` proves that, for every RXC3 instance X:

- X has an exact cover **if and only if** the AWET instance built in Section 8 of the paper has a schedule (with arbitrary real start times) of cost at most B = ⌊A + Γ⌋;
- the instance has 8n + 1 jobs, and every number in it is at most (n + 1)^650.

The file also proves the canonical reformulation (Lemma I.3, Proposition I.4) and reproduces the numbers of the paper's worked examples (Appendix B).

**Status:** no `sorry`, no warnings, and only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No errors were found in the paper.

**Taken as given, as in the paper:** the NP-completeness of RXC3 (Gonzalez, 1985) and the polynomial running time of the construction.

## How to check

1. Install Lean 4 (v4.35.0) and create a Lake project that depends on Mathlib `v4.35.0`.
2. Copy `AWET_PartI.lean` into the project.
3. Run:

   ```
   lake env lean AWET_PartI.lean
   ```

It compiles in about one minute. The only output is three `#print axioms` lines, each listing `[propext, Classical.choice, Quot.sound]`.

## Acknowledgement

The formalization and report were produced with the help of an AI model (Claude, Anthropic). All credit for the mathematics belongs to the authors of the paper.
