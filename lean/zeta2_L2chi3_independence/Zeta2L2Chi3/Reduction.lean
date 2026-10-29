/-
# Reduction of the final theorems to the arithmetic content bound

With the proved spectral rates (`decay_rate`, `growth_rate`) and the verified logarithm bounds
(`Numerics`), the only remaining input of `RateHyp` is the content bound `ContentBound`
(`∀ ε > 0, eventually exp((β₀ - ε) n) ≤ cont(w_n)` with `β₀ = -1.3335`).
-/
import Zeta2L2Chi3.Assembly
import Zeta2L2Chi3.Rates
import Zeta2L2Chi3.Numerics

open Filter Real

noncomputable section

namespace Zeta2L2Chi3

/-- rational upper bound for the decay rate `log(s∞ r_h)` -/
def Lg0 : ℝ := -32908139 / 10 ^ 6
/-- rational upper bound for the growth rate `log(s∞ R_h)` -/
def LB0 : ℝ := 31568021 / 10 ^ 6
/-- the arithmetic content exponent -/
def β0 : ℝ := -13335 / 10000

/-- the arithmetic content bound (the remaining obligation ARITH) -/
def ContentBound : Prop := ∀ ε > 0, ∀ᶠ n : ℕ in atTop, exp ((β0 - ε) * n) ≤ ((cont (w n) : ℚ) : ℝ)

lemma exp_mono_rate {L L' ε : ℝ} (h : L ≤ L') (n : ℕ) : exp ((L + ε) * n) ≤ exp ((L' + ε) * n) :=
  exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n))

theorem rateHyp_of_content (hc : ContentBound) : RateHyp Lg0 LB0 β0 where
  decay ε hε := (decay_rate ε hε).mono fun n hn k =>
    (hn k).trans (exp_mono_rate (by simpa [Lg0, rh] using log_sr_le) n)
  growth ε hε := (growth_rate ε hε).mono fun n hn i j =>
    (hn i j).trans (exp_mono_rate (by simpa [LB0, Rh] using log_sR_le) n)
  content := hc

lemma hE0 : Lg0 + LB0 < β0 := by norm_num [Lg0, LB0, β0]
lemma hH0 : β0 < 2 * LB0 := by norm_num [LB0, β0]
lemma hδ0 : 1 / 10000 < (β0 - Lg0 - LB0) / (2 * LB0 - β0) := by norm_num [Lg0, LB0, β0]

theorem irrational_of_content (hc : ContentBound) (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    Irrational (alpha A B) :=
  irrational_of_rates (rateHyp_of_content hc) hE0 A B hAB

theorem linIndep_of_content (hc : ContentBound) : LinearIndependent ℚ ![(1 : ℝ), C, Z] :=
  linIndep_of_rates (rateHyp_of_content hc) hE0

theorem delta_of_content (hc : ContentBound) (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ∃ c : ℝ, 1 / 10000 < c ∧ ∀ᶠ N : ℕ in atTop, c ≤ delta (alpha A B) (readout N A B) :=
  delta_of_rates (rateHyp_of_content hc) hE0 hH0 hδ0 A B hAB

end Zeta2L2Chi3
