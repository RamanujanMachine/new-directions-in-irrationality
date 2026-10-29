# Lean formalization: linear independence of 1, L(2,χ₋₃), ζ(2)

Kernel-checked Lean 4 proof that 1, C = L(2,χ₋₃) and Z = ζ(2) are linearly
independent over ℚ, obtained from one explicit CMF trajectory (the Meijer G
field MG(5,2,5,5,1) at z = 1, restricted to rank three: a single third-order
recurrence). This is the main theorem of Calegari, Dimitrov and Tang,
[arXiv:2408.15403](https://arxiv.org/abs/2408.15403). The result will appear in
the next version of *New Directions in Irrationality*
([arXiv:2610.27799](https://arxiv.org/abs/2610.27799)); the computational
proof is in [`additional/l2chi3_zeta2/`](../../additional/l2chi3_zeta2/).

## Main theorems (`Zeta2L2Chi3/Main.lean`)

```lean
theorem Zeta2L2Chi3.main_linIndep : LinearIndependent ℚ ![(1 : ℝ), C, Z]

theorem Zeta2L2Chi3.main_irrational (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    Irrational (alpha A B)

theorem Zeta2L2Chi3.main_delta (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ∃ c : ℝ, 1 / 10000 < c ∧ ∀ᶠ N : ℕ in atTop, c ≤ delta (alpha A B) (readout N A B)
```

The constants are defined directly as series (`Zeta2L2Chi3/Defs.lean`):
`Z = ∑_{k≥0} 1/(k+1)²` (with `Z_eq_pi : Z = π²/6`),
`C = ∑_{k≥0} (1/(3k+1)² − 1/(3k+2)²)`, and
`alpha A B = A(C + 2Z/3) + B(C − 2Z/3)`.

The formalization covers the whole argument, with nothing assumed:

| Part | Lean |
|---|---|
| Trajectory, rank-three restriction, pairing and readouts equal the exact approximants | `readout_eq_w`, `Bres_eq_Bhat`, `fvec_eq`, `phi_transport`, `alg03_check` |
| Special state: initial value, recessiveness, limits C and ζ(2), exponential error | `S_eq`, `S_initial`, `S_recessive`, `w0_lower`, `readout_error`, `C_error`, `Z_error` |
| All-prime arithmetic content bound for the reduced denominators | `main_content`, `lemmaA`, `dualBound_sound`, `content_rate`, `density_bound` |
| liminf δ > 1/10000, irrationality, linear independence | `main_delta`, `main_irrational`, `main_linIndep` |

The limits are identified by residue calculus (`Psi`, `SeriesState`,
`DualTransport`); no Barnes integral is needed. The error bound uses the
certified rational exponent E₀ = 64.47615 (the exact value is
E = 64.4761596918…), which is all the later steps need. The only analytic
number theory imported is `WeakPNT_AP` from PrimeNumberTheoremAnd, used for the
prime-density sum; it is proved there, not assumed.

## Axioms and checks

No `sorry`, `admit`, `native_decide`, `ofReduceBool` or `axiom` declaration
occurs in the project. The 1,158 dual and 528 forward chamber certificates are
evaluated by the kernel with `decide +kernel`. `Zeta2L2Chi3/Audit.lean` prints
the axioms of every final theorem; each depends only on
`propext`, `Classical.choice`, `Quot.sound` (`alg03_check` only on `propext`).
The recorded output is in [`AXIOM_AUDIT.txt`](AXIOM_AUDIT.txt).

The reference build (Lean 4.35.0, 9,234 jobs, 0 errors) was made in the
original development repository. For this release the modules and namespace
were renamed to `Zeta2L2Chi3`; this is a purely textual change, and the
recorded audit is shown with the new names.

## Pinned versions

| Component | Version |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` (`lean-toolchain`) |
| PrimeNumberTheoremAnd | `127b50e33f6033e2147921167a117af96d9ba4ea` (`lakefile.toml`) |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` (`lake-manifest.json`) |

## Building

```sh
cd lean/zeta2_L2chi3_independence
lake exe cache get
lake build
lake env lean Zeta2L2Chi3/Audit.lean
```

Do not run `lake update`. The kernel-checked chamber certificates
(`Arith/FwdCert`, `Arith/DualCert*`, `Arith/DualChk*`) take about one hour of
CPU in total. On a 16 GB machine, build them one module at a time, for example
`lake build Zeta2L2Chi3.Arith.DualChk9_3`; a single module peaks at about
3.5–4.6 GB.

## Module map

| Topic | Modules |
|---|---|
| Constants and mixtures | `Defs` |
| Trajectory matrices | `Data`, `Matrices` |
| Pairing identity | `Alg03`, `FAssembly` |
| Determinant normalization | `Arith/DeltaVal`, `Arith/DeltaCert` |
| Readouts | `Matrices` |
| Dual special state | `Dual`, `Residue`, `PartialFrac`, `SeriesState` |
| Dual transport | `CertDefs`, `Cert0`–`Cert2`, `TransportId`, `TransportTH`, `GDeriv`, `DualTransport` |
| Content and reduced fractions | `Content`, `Assembly` |
| Limit identification | `Psi`, `SeriesState`, `DualTransport` |
| Asymptotics and error rate | `CrudeBound`, `Dichotomy`, `Gauge`, `Rates`, `NV`, `Target2/W0Lower`, `Target2/ErrorBound` |
| Forward construction and transport | `Forward`, `FInit`, `FPfun`, `PartialFrac2`, `FShift`, `FCertDefs`, `FCert0`–`FCert3`, `FTransportId`, `FTransport`, `Arith/FwdExplicit`, `Arith/FwdPoly`, `Arith/FwdRat` |
| Forward valuations | `Arith/FwdLarge`, `Arith/FwdLarge2`, `Arith/FwdAssemble`, `Arith/FwdVal` |
| Valuation lemmas and harmonic numbers | `Arith/Taylor`, `Arith/LemmaAAux*`, `Arith/LemmaA`, `Arith/Harmonic` |
| Dual lattice bound | `Arith/Lagrange`, `Arith/LatticeAux`, `Arith/Lattice`, `Arith/Checker` |
| Families and cells | `Arith/Defs`, `Arith/Family`, `Arith/CellAux`, `Arith/Cell` |
| Chamber certificates | `Arith/ChamberData`, `Arith/DualCert*`, `Arith/DualData*`, `Arith/DualChk*`, `Arith/CellBounds`, `Arith/FwdCert` |
| Small primes and Legendre counting | `Arith/FwdSmallP`, `Arith/FwdSmallR`, `Arith/FwdLegendre`, `Arith/DeltaLeg`, `Arith/DeltaFam`, `Arith/DeltaBounds` |
| Prime-density sum | `Arith/Sum`, `Arith/Density` |
| Height rate | `Rates`, `Target2/Stirling`, `Target2/PhiNum`, `Target2/QfWeights`, `Target2/QfStirling`, `Target2/QfLower`, `Target2/DeltaLower` |
| Numerics | `Numerics`, `PolyCheck` |
| Nonvanishing | `NV`, `Assembly` |
| Final assembly | `Generic`, `Assembly`, `Reduction`, `Main` |

[`ARITH_BLUEPRINT.md`](ARITH_BLUEPRINT.md) outlines the arithmetic content
bound.
