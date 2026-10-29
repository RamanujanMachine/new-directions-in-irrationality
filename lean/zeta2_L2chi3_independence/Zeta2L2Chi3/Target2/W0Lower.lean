/-
# Lower bound for the cofactor `w₀` (raw height)

`w_n 0 = (1944/35) Δ_n q^f_n` with `q^f_n = fvecQ n 0 = Σ_{k=0}^{8n+1} (N(k)/D_k(k)) P_n(k)` a sum with
positive weights `N(k)/D_k(k)` (double-pole coefficients of `R_n`) and `P_n(k) < 0` near the saddle
`k ≈ y* n` (ARITHMETIC_ARGUMENT §10).  Stirling bounds give
`log Δ_n ≥ (σ_det - ε) n`, `σ_det = log C₀ + Σ m A log A ≈ 30.2278993400888`, and
`log |q^f_n| ≥ (φ(y*) - ε) n`, `φ(y*) ≈ 32.9081400145689`.

Proofs: `Target2/DeltaLower.lean` (`σ_det = 32 log 2 + 5 log 5`), `Target2/QfLower.lean`
(split at `⌈4.4 n⌉`, saddle point `⌈6.13 n⌉`), built on `Target2/Stirling.lean`,
`Target2/PhiNum.lean`, `Target2/QfWeights.lean`, `Target2/QfStirling.lean`.
-/
import Zeta2L2Chi3.Arith.FwdVal
import Zeta2L2Chi3.Arith.DeltaVal
import Zeta2L2Chi3.Target2.DeltaLower
import Zeta2L2Chi3.Target2.QfLower

namespace Zeta2L2Chi3.Arith

open Filter

theorem log_Delta_lower : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (30227899 / 10 ^ 6 - ε) * n ≤ Real.log (Δ n : ℝ) := log_Delta_lower'

theorem log_qf_lower : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (32908136 / 10 ^ 6 - ε) * n ≤ Real.log |(fvecQ n 0 : ℝ)| := log_qf_lower'

theorem w0_lower : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    Real.exp ((63136035 / 10 ^ 6 - ε) * n) ≤ |((w n 0 : ℚ) : ℝ)| := by
  intro ε hε
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'e : ε' ≤ ε := min_le_left _ _
  filter_upwards [log_Delta_lower (ε' / 2) (by positivity), log_qf_lower (ε' / 2) (by positivity),
    eventually_ge_atTop 1] with n h1 h2 hn
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (Δ n : ℝ) ≠ 0 := by exact_mod_cast Delta_ne_zero n
  have hq : ((fvecQ n 0 : ℚ) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, abs_zero, Real.log_zero] at h2
    nlinarith
  have hw : ((w n 0 : ℚ) : ℝ) = 1944 / 35 * (Δ n : ℝ) * ((fvecQ n 0 : ℚ) : ℝ) := by
    have h := fvecQ_eq n 0
    have hD' : Δ n ≠ 0 := Delta_ne_zero n
    have : w n 0 = 1944 / 35 * Δ n * fvecQ n 0 := by
      rw [h]; field_simp
    rw [this]; push_cast; ring
  have hw0 : ((w n 0 : ℚ) : ℝ) ≠ 0 := by
    rw [hw]; exact mul_ne_zero (mul_ne_zero (by norm_num) hD) hq
  have hlog : Real.log |((w n 0 : ℚ) : ℝ)| =
      Real.log (1944 / 35) + Real.log (Δ n : ℝ) + Real.log |((fvecQ n 0 : ℚ) : ℝ)| := by
    rw [Real.log_abs, Real.log_abs, hw, Real.log_mul (mul_ne_zero (by norm_num) hD) hq,
      Real.log_mul (by norm_num) hD]
  have hc : 0 < Real.log (1944 / 35 : ℝ) := Real.log_pos (by norm_num)
  rw [← Real.exp_log (abs_pos.2 hw0)]
  apply Real.exp_le_exp.2
  rw [hlog]
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

end Zeta2L2Chi3.Arith
