# Lean formalizations

The Lean formalizations for the paper are kept in their original public
RamanujanMachine repositories, not in this repository. Use the pinned
revisions below; later commits in those repositories are not part of the
paper's supplement.

| Project | Pinned revision |
|---|---|
| [meijerg_zeta3_zeta4](https://github.com/RamanujanMachine/meijerg_zeta3_zeta4) | [`639a790897ec`](https://github.com/RamanujanMachine/meijerg_zeta3_zeta4/tree/639a790897ecbd9fec2e7d337e58c5be6e6aa1f1) |
| [zeta2_four_trajectory_matrices](https://github.com/RamanujanMachine/zeta2_four_trajectory_matrices) | [`a0e8ac417cdd`](https://github.com/RamanujanMachine/zeta2_four_trajectory_matrices/tree/a0e8ac417cddc6ffa88e43cfd68d2b58ea339517) |
| [zetas_irr](https://github.com/RamanujanMachine/zetas_irr) | [`d9d52233b153`](https://github.com/RamanujanMachine/zetas_irr/tree/d9d52233b15383206bc426ba86dadd66f6737b16) |

Toolchains and mathlib pins are recorded in
[lean_upstreams.json](../provenance/lean_upstreams.json).

**Verification status:** the theorem statements below were checked in the
source. The projects have not been independently compiled for this release.
A successful build would still leave the explicitly assumed prime number
theorem described below. Python results do not certify the Lean proofs.

## Which project proves which statement?

| Project | Source entry point | Statement in the source |
|---|---|---|
| ζ(3), ζ(4) approximation rates | [Blueprint_5255.lean](https://github.com/RamanujanMachine/meijerg_zeta3_zeta4/blob/639a790897ecbd9fec2e7d337e58c5be6e6aa1f1/lean/Meijer5255/Blueprint_5255.lean) | `Meijer5255.main_joint`: liminf approximation exponent > 0.01634832; `Meijer5255.main_pure3`: > 0.22626234. These exports are approximation-rate statements. They do not themselves state irrationality or irrationality-measure bounds. |
| ζ(2) irrationality measure | [MainTheorem.lean](https://github.com/RamanujanMachine/zeta2_four_trajectory_matrices/blob/a0e8ac417cddc6ffa88e43cfd68d2b58ea339517/Zeta2FourTrajectoryMatrices/MainTheorem.lean) | `zeta2_irrationality_measure`: μ(ζ(2)) ≤ 62636575/13537936 < 4.62675. |
| Linear independence | [blueprint.lean](https://github.com/RamanujanMachine/zetas_irr/blob/d9d52233b15383206bc426ba86dadd66f6737b16/blueprint.lean), [Blueprint_pfq54.lean](https://github.com/RamanujanMachine/zetas_irr/blob/d9d52233b15383206bc426ba86dadd66f6737b16/pfq54_formalization_handoff/Blueprint_pfq54.lean) | `ZetasIrr.theorem_1_6`: linear independence of 1, ζ(3), ζ(4) over ℚ. `Pfq54.main_theorem` also states independence and an eventual approximation-exponent bound ≥ 1/375. |

The first project's definition assigns an infinite exponent to an exact
approximant. Its positive exponent conclusion alone therefore does not prove
irrationality. The independence project has a separate irrationality argument.
The older 1/375 rate is distinct from the current Section 6 notebook rates.
No formal bridge equating every notebook normalization and divisor with these
Lean developments has been checked.

## Explicit prime-number-theorem assumptions

- [Meijer5255/PNT.lean](https://github.com/RamanujanMachine/meijerg_zeta3_zeta4/blob/639a790897ecbd9fec2e7d337e58c5be6e6aa1f1/lean/Meijer5255/PNT.lean#L18), line 18:
  one `sorry` in `Meijer5255.PNT.prime_number_theorem`.
- [arith_rate.lean](https://github.com/RamanujanMachine/zeta2_four_trajectory_matrices/blob/a0e8ac417cddc6ffa88e43cfd68d2b58ea339517/Zeta2FourTrajectoryMatrices/ArithmeticRate/arith_rate.lean#L78), line 78:
  `axiom Zeta2ArithRate.prime_number_theorem`.
- [log_Delta_le.lean](https://github.com/RamanujanMachine/zetas_irr/blob/d9d52233b15383206bc426ba86dadd66f6737b16/blueprints/log_Delta_le.lean#L133), line 133:
  one `sorry` in the prime-number-theorem declaration.

All three assume the asymptotic formula θ(x)/x → 1. These are explicitly
unproved inputs in the formalizations.

## Building a project

Install Lean via elan. Clone the repository and check out the pinned
revision, for example:

```sh
git clone https://github.com/RamanujanMachine/zetas_irr.git
cd zetas_irr
git checkout d9d52233b15383206bc426ba86dadd66f6737b16
lake exe cache get
lake build
```

All projects specify Lean `v4.35.0-rc4`, with different pinned mathlib
revisions; keep each project's `lake-manifest.json` and do not run
`lake update`. For `zetas_irr`, the default `lake build` only builds a small
stub; build the blueprint files explicitly (for example
`lake env lean blueprint.lean`) to check the main theorems.

The other files in those repositories (drafts, handoff notes, older
certificates) predate the paper and are not part of its supplement.
