# Centered cocircular central configurations

Companion to *Centered Cocircular Central Configurations for Homogeneous and Logarithmic Potentials*, Chih-Yao Wu. [Paper (94 pages)](paper/paper.pdf) · [TeX sources](paper/source.zip) · [Verification](VERIFICATION.md).

The formal theorem covers every real exponent `α ≥ 0` and every finite `n ≥ 2`. Its hypotheses are positive masses, distinct positions on a circle of positive radius, center of mass equal to the circle center, and the complete force equations. Its conclusion is an equal-mass regular polygon. At `α = 0`, the force is the logarithmic-potential force; it is not obtained by differentiating a constant potential.

```lean
import ACS12

example {n : ℕ} {α : ℝ} (F : ACS12.Configuration n α)
    (hn : 2 ≤ n) (hα : 0 ≤ α) : ACS12.IsEqualMassRegular F :=
  F.rigidity hn hα
```

## Build and review

Install elan and Git, then run in this directory:

```sh
lake exe cache get
lake build ACS12
lake env lean ACS12/Audit.lean
lake env lean ACS12/Paper.lean
```

Lean and Mathlib are pinned in `lean-toolchain` and `lakefile.toml`. The first build needs network access. Each project in this repository is built independently.

Start with `ACS12/FullRange.lean` and follow the definitions of `Configuration` and `IsEqualMassRegular`. `ACS12/Paper.lean` indexes selected numbered manuscript statements; it does not assert that every sentence of the paper is formalized. `ACS12/Audit.lean` prints the theorem hypotheses and axiom dependencies. The manuscript also presents a self-contained mathematical proof.

AI agents developed the argument, exposition, and formalization under Chih-Yao Wu's coordination. The complete manuscript has not received an independent human expert review. Kernel checking and checking that the definitions express the intended mathematical problem are separate review tasks.

The paper is distributed under CC BY 4.0. No additional software license is granted here for the ACS12 source; dependencies retain their own licenses.
