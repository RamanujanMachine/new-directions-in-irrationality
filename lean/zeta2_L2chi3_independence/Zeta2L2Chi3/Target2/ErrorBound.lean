/-
# Target 2: the special state and the exponential error bound

* `S_initial`: the special state at `n = 0` is `B̂₀` read against `(1, 9C/2 + 3Z, 2Z)`.
* `S_recessive`: `|S_n| ≤ exp((-32.908139 + ε) n)` (decay), while `|w_n 0| ≥ exp((63.136035 - ε) n)`
  (`w0_lower`).
* `readout_error`: for every fixed `(A, B)`, `|α(A,B) - r_N(A,B)| ≤ exp(-(64.47615 - ε) N)` eventually;
  in particular `r_N(1,1)/2 → C = L(2,χ₋₃)` and `(3/4) r_N(1,-1) → ζ(2)` at that rate.

The rate `64.47615` is the explicit rational lower bound `63.136035 + 32.908139 - 31.568021` for the
error exponent `E = 64.4761596918…` (raw cofactor height lower rate minus the decay and growth rates).
-/
import Zeta2L2Chi3.Target2.W0Lower
import Zeta2L2Chi3.Reduction

namespace Zeta2L2Chi3.Arith

open Filter Real

/-- the explicit error exponent -/
noncomputable def E0 : ℝ := 6447615 / 100000

theorem S_initial (k : Fin 3) :
    S 0 k = ((Bhat0 0 k : ℚ) : ℝ) + (9 * C / 2 + 3 * Z) * ((Bhat0 1 k : ℚ) : ℝ) +
      2 * Z * ((Bhat0 2 k : ℚ) : ℝ) := by
  rw [S_eq_Bhat]
  simp [ξ1, ξ2, Bhat]

theorem S_recessive : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ k : Fin 3, |S n k| ≤ exp ((Lg0 + ε) * n) :=
  fun ε hε => (decay_rate ε hε).mono fun n hn k =>
    (hn k).trans (exp_mono_rate (by simpa [Lg0, rh] using log_sr_le) n)

theorem Bhat_growth : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ i j : Fin 3,
    |((Bhat n i j : ℚ) : ℝ)| ≤ exp ((LB0 + ε) * n) :=
  fun ε hε => (growth_rate ε hε).mono fun n hn i j =>
    (hn i j).trans (exp_mono_rate (by simpa [LB0, Rh] using log_sR_le) n)

theorem readout_error (A B : ℤ) : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    |alpha A B - (readout N A B : ℝ)| ≤ exp (-(E0 - ε) * N) := by
  intro ε hε
  have hη : 0 < ε / 4 := by positivity
  set K : ℝ := 4 * |(A + B : ℝ)| + 12 * |(B : ℝ)| with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [S_recessive _ hη, Bhat_growth _ hη, w0_lower _ hη,
    eventually_const_le_exp (K + 1) _ hη] with n hd hg hw hc
  have hw0pos : 0 < |((w n 0 : ℚ) : ℝ)| := lt_of_lt_of_le (exp_pos _) hw
  have hw0 : ((w n 0 : ℚ) : ℝ) ≠ 0 := abs_pos.1 hw0pos
  have hb := linform_bound n A B _ _ hd hg
  have hr : ((readout n A B : ℚ) : ℝ) = 2 * ((A + B) * ((w n 1 : ℚ) : ℝ) - 3 * B * ((w n 2 : ℚ) : ℝ)) /
      (9 * ((w n 0 : ℚ) : ℝ)) := by
    rw [readout_eq_w]; push_cast; ring
  have hdiff : alpha A B - ((readout n A B : ℚ) : ℝ) =
      (9 * ((w n 0 : ℚ) : ℝ) * alpha A B - 2 * ((A + B) * ((w n 1 : ℚ) : ℝ) - 3 * B * ((w n 2 : ℚ) : ℝ))) /
        (9 * ((w n 0 : ℚ) : ℝ)) := by
    rw [hr]; field_simp
  rw [hdiff, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9)]
  have hden : exp ((63136035 / 10 ^ 6 - ε / 4) * n) ≤ 9 * |((w n 0 : ℚ) : ℝ)| := by linarith
  have hnum : (4 * |(A + B : ℝ)| + 12 * |(B : ℝ)|) * (exp ((Lg0 + ε / 4) * n) * exp ((LB0 + ε / 4) * n))
      ≤ exp ((ε / 4) * n) * exp ((Lg0 + LB0 + ε / 2) * n) := by
    rw [← exp_add]
    have : (Lg0 + ε / 4) * n + (LB0 + ε / 4) * n = (Lg0 + LB0 + ε / 2) * n := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
  calc |9 * ((w n 0 : ℚ) : ℝ) * alpha A B - 2 * ((A + B) * ((w n 1 : ℚ) : ℝ) - 3 * B * ((w n 2 : ℚ) : ℝ))| /
        (9 * |((w n 0 : ℚ) : ℝ)|)
      ≤ exp ((ε / 4) * n) * exp ((Lg0 + LB0 + ε / 2) * n) / exp ((63136035 / 10 ^ 6 - ε / 4) * n) :=
        div_le_div₀ (by positivity) (hb.trans hnum) (exp_pos _) hden
    _ = exp ((Lg0 + LB0 - 63136035 / 10 ^ 6 + ε) * n) := by
        rw [← exp_add, ← exp_sub]; congr 1; ring
    _ ≤ exp (-(E0 - ε) * n) := by
        apply exp_le_exp.2
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
        norm_num [Lg0, LB0, E0]; linarith

/-- `C = L(2, χ₋₃)` is the limit of `r_N(1,1)/2` with error `exp(-(E0 - ε) N)` -/
theorem C_error : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, |C - (readout N 1 1 : ℝ) / 2| ≤ exp (-(E0 - ε) * N) := by
  intro ε hε
  filter_upwards [readout_error 1 1 ε hε] with N h
  have : alpha 1 1 = 2 * C := by rw [alpha_eq]; push_cast; ring
  rw [this] at h
  calc |C - (readout N 1 1 : ℝ) / 2| = |2 * C - (readout N 1 1 : ℝ)| / 2 := by
        rw [← abs_of_pos (by norm_num : (0 : ℝ) < 2), ← abs_div]; congr 1; ring
    _ ≤ |2 * C - (readout N 1 1 : ℝ)| := by linarith [abs_nonneg (2 * C - (readout N 1 1 : ℝ))]
    _ ≤ _ := h

/-- `ζ(2)` is the limit of `(3/4) r_N(1,-1)` with error `exp(-(E0 - ε) N)` -/
theorem Z_error : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    |Z - 3 / 4 * (readout N 1 (-1) : ℝ)| ≤ exp (-(E0 - ε) * N) := by
  intro ε hε
  filter_upwards [readout_error 1 (-1) ε hε] with N h
  have : alpha 1 (-1) = 4 / 3 * Z := by rw [alpha_eq]; push_cast; ring
  rw [this] at h
  calc |Z - 3 / 4 * (readout N 1 (-1) : ℝ)| = 3 / 4 * |4 / 3 * Z - (readout N 1 (-1) : ℝ)| := by
        rw [← abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4), ← abs_mul]; congr 1; ring
    _ ≤ |4 / 3 * Z - (readout N 1 (-1) : ℝ)| := by
        linarith [abs_nonneg (4 / 3 * Z - (readout N 1 (-1) : ℝ))]
    _ ≤ _ := h

end Zeta2L2Chi3.Arith
