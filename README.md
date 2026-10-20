# New Directions in Irrationality — Supplementary Material

Elyasheev Leibtag, Hila Barkan, Rotem Kalisch, Shachar Weinbaum,
Michael Shalyt, and Ido Kaminer

Release candidate **1.0.0-rc2**, prepared 19 October 2026.

This package makes the computational ingredients of Section 6 and
Appendices B.1–B.4 reproducible. It also includes selected exact checks for
the π integral construction, a ζ(5) initial-state readout, and the
harmonic-weighted Gregory series. The manuscript source and its referenced
figures are included for identification and comparison.

The Section 6 notebooks recover the numerical conclusions

- μ(Aζ(3)+Bζ(4)) < 66.3 for each fixed nonzero rational pair (A,B);
- μ(ζ(2)) < 4.62675;
- μ(ζ(3)) < 5.4197.

These conclusions use the analytical and uniform arithmetic arguments stated
in the paper. Successful Python execution verifies the documented
computational ingredients; it is not a complete formal verification of the
paper. Exact identities, exhaustive finite certificates and finite examples
are distinguished in the notebooks.

## Lean formalizations (original repositories)

The Lean formalizations are not copied into this repository. They live in
their original public RamanujanMachine repositories. The paper refers to
the following exact revisions:

| Lean project | Pinned revision | Recorded commit date (UTC) |
|---|---|---|
| [meijerg_zeta3_zeta4](https://github.com/RamanujanMachine/meijerg_zeta3_zeta4/tree/639a790897ecbd9fec2e7d337e58c5be6e6aa1f1) | `639a790897ec` | 13 October 2026, 19:40:07 |
| [zeta2_four_trajectory_matrices](https://github.com/RamanujanMachine/zeta2_four_trajectory_matrices/tree/a0e8ac417cddc6ffa88e43cfd68d2b58ea339517) | `a0e8ac417cdd` | 13 October 2026, 08:59:32 |
| [zetas_irr](https://github.com/RamanujanMachine/zetas_irr/tree/d9d52233b15383206bc426ba86dadd66f6737b16) | `d9d52233b153` | 13 October 2026, 08:51:30 |

The full commit identifiers and dependency pins are recorded in
[the upstream revision record](provenance/lean_upstreams.json). The dates are
the timestamps recorded in the original Git commits; they identify the
revisions and are not independently certified proof-completion dates. See the
[Lean guide](lean/README.md) for the theorem statements, the explicit
prime-number-theorem assumptions and how to build each project.

## Reading the supplement

Start with [the notebook guide](python/00_guide.ipynb), then follow the three
subjects in [the notebook map](python/README.md). The notebooks contain saved
outputs and can be read without running them.

| Topic | Entry point |
|---|---|
| Simultaneous ζ(3), ζ(4) approximation | [Matrices, sums and minors](python/joint/01_matrices_sums_and_minors.ipynb) |
| ζ(2) | [CMF and closed forms](python/zeta2/01_zeta2_cmf_and_closed_forms.ipynb) |
| Pure ζ(3) | [Approximants and rates](python/pure_zeta3/01_pure_zeta3_approximants_and_rates.ipynb) |
| Additional exact calculations | [Additional calculations](additional/README.md) |
| Lean sources and proof assumptions | [Lean guide](lean/README.md) |
| Match a paper claim to code | [Coverage and statement map](COVERAGE.md) |
| Conventions and proof inputs | [Notation and scope](python/NOTATION_AND_SCOPE.md) |
| What was actually rerun | [Verification](VERIFICATION.md) |
| Corrections needed in the supplied manuscript | [Manuscript alignment](MANUSCRIPT_ALIGNMENT.md) |

## Reproduce the calculations

Use Python 3.12. From this extracted directory:

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python verify_release.py
python run_all.py
```

On Windows, activate with `.venv\Scripts\activate`.
Internet access is needed to install dependencies; the calculations use
local inputs. Do not use `-O`, `-OO` or `PYTHONOPTIMIZE`, which disable
assertions. See [REPRODUCING.md](REPRODUCING.md) for individual commands,
outputs, environments and verification limits.


