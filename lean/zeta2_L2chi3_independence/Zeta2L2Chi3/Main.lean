/-
# Linear independence of 1, L(2,χ₋₃), ζ(2) from one CMF trajectory (MG55 / 5F4): final theorems

Target 1 (construction ↔ exact approximants): `readout_eq_w`, `Bres_eq_Bhat`, `fvec_eq`.
Target 2 (special state, limits, error bound): `S_eq`, `S_initial`, `S_recessive`, `w0_lower`,
  `readout_error`, `C_error`, `Z_error`.
Target 3 (all-prime arithmetic content): `contentBound`.
Target 4 (irrationality measure): `main_delta`, `main_irrational`, `main_linIndep`.

Every statement below depends only on `propext`, `Classical.choice`, `Quot.sound`
(see `Zeta2L2Chi3/Audit.lean`).
-/
import Zeta2L2Chi3.Arith.Final
import Zeta2L2Chi3.Target2.ErrorBound

namespace Zeta2L2Chi3

open Filter

/-- **Target 3.** `cont(w_n) ≥ exp((-1.3335 - ε) n)` eventually (reduced content of the cofactor). -/
theorem main_content : ContentBound := Arith.contentBound

/-- **Target 4.** For every fixed nonzero `(A, B)`, `liminf δ_N(A, B) > 1/10000`. -/
theorem main_delta (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ∃ c : ℝ, 1 / 10000 < c ∧ ∀ᶠ N : ℕ in atTop, c ≤ delta (alpha A B) (readout N A B) :=
  delta_of_content Arith.contentBound A B hAB

/-- **Target 4.** Every nonzero mixture `A(C + 2ζ(2)/3) + B(C - 2ζ(2)/3)` is irrational. -/
theorem main_irrational (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) : Irrational (alpha A B) :=
  irrational_of_content Arith.contentBound A B hAB

/-- **Target 4.** `1, C = L(2, χ₋₃), ζ(2)` are linearly independent over `ℚ`. -/
theorem main_linIndep : LinearIndependent ℚ ![(1 : ℝ), C, Z] :=
  linIndep_of_content Arith.contentBound

end Zeta2L2Chi3
