import Mathlib

/-!
# Rigorous rational bounds for real logarithms

We use the series `log ((1+t)/(1-t)) = 2 ∑ t^(2k+1)/(2k+1)` (for `0 ≤ t < 1`), whose partial
sums `logS m t` are lower bounds and whose tail is bounded by a geometric series.
-/

noncomputable section

namespace Zeta2L2Chi3

open Real

/-- Partial sum `logS m t = 2 ∑_{k<m} t^(2k+1)/(2k+1)` (computable, rational). -/
def logS : ℕ → ℚ → ℚ
  | 0, _ => 0
  | m + 1, t => logS m t + 2 * t ^ (2 * m + 1) / (2 * m + 1)

/-- Geometric bound on the tail of the series after `m` terms. -/
def logTail (m : ℕ) (t : ℚ) : ℚ := 2 * t ^ (2 * m + 1) / ((2 * m + 1) * (1 - t ^ 2))

theorem S_cast (m : ℕ) (t : ℚ) :
    ((logS m t : ℚ) : ℝ) =
      ∑ k ∈ Finset.range m, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (t : ℝ) ^ (2 * k + 1) := by
  induction m with
  | zero => simp [logS]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, logS]
    push_cast
    ring

theorem tail_cast (m : ℕ) (t : ℚ) :
    ((logTail m t : ℚ) : ℝ) = 2 * (t : ℝ) ^ (2 * m + 1) / ((2 * m + 1) * (1 - (t : ℝ) ^ 2)) := by
  simp [logTail]

/-- Real-variable two-sided bound for the series of `log (1+t) - log (1-t)`. -/
theorem log_series_bounds (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1))
        ≤ log (1 + t) - log (1 - t) ∧
      log (1 + t) - log (1 - t) ≤
        (∑ k ∈ Finset.range m, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1)) +
          2 * t ^ (2 * m + 1) / ((2 * m + 1) * (1 - t ^ 2)) := by
  have habs : |t| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := hasSum_log_sub_log_of_abs_lt_one habs
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1) := fun k => by
    positivity
  refine ⟨sum_le_hasSum (Finset.range m) (fun k _ => hnn k) h, ?_⟩
  have ht := (hasSum_nat_add_iff' m).mpr h
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg t) ht2).mul_left
    (2 / (2 * (m : ℝ) + 1) * t ^ (2 * m + 1))
  have hle := hasSum_le (fun k => ?_) ht hg
  · have h1t : 0 < 1 - t ^ 2 := by linarith
    have : 2 / (2 * (m : ℝ) + 1) * t ^ (2 * m + 1) * (1 - t ^ 2)⁻¹ =
        2 * t ^ (2 * m + 1) / ((2 * m + 1) * (1 - t ^ 2)) := by
      field_simp
    linarith
  · have hp : t ^ (2 * (k + m) + 1) = t ^ (2 * m + 1) * (t ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [hp]
    push_cast
    have hA : 0 ≤ t ^ (2 * m + 1) * (t ^ 2) ^ k := by positivity
    have hd : 1 / (2 * ((k : ℝ) + m) + 1) ≤ 1 / (2 * (m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    calc (2 : ℝ) * (1 / (2 * ((k : ℝ) + m) + 1)) * (t ^ (2 * m + 1) * (t ^ 2) ^ k)
        ≤ 2 * (1 / (2 * (m : ℝ) + 1)) * (t ^ (2 * m + 1) * (t ^ 2) ^ k) := by gcongr
      _ = 2 / (2 * (m : ℝ) + 1) * t ^ (2 * m + 1) * (t ^ 2) ^ k := by ring

/-- Bounds on `log u` for a rational `u ≥ 1`, with `t = (u-1)/(u+1)`. -/
theorem log_bounds_of (u : ℚ) (hu : 1 ≤ u) (m : ℕ) (t : ℚ) (ht : t = (u - 1) / (u + 1)) :
    ((logS m t : ℚ) : ℝ) ≤ Real.log u ∧ Real.log u ≤ ((logS m t : ℚ) : ℝ) + ((logTail m t : ℚ) : ℝ) := by
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have htr : (t : ℝ) = (u - 1) / (u + 1) := by rw [ht]; push_cast; ring
  have h0 : 0 ≤ (t : ℝ) := by rw [htr]; apply div_nonneg <;> linarith
  have h1 : (t : ℝ) < 1 := by
    rw [htr, div_lt_one (by linarith)]; linarith
  have hlog : Real.log u = log (1 + t) - log (1 - t) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    congr 1
    rw [htr]
    field_simp
    ring
  rw [S_cast, tail_cast, hlog]
  exact log_series_bounds t h0 h1 m

/-- Bounds on `log u` for a rational `0 < u ≤ 1`, with `t = (1-u)/(1+u)`. -/
theorem log_bounds_of_le_one (u : ℚ) (hu0 : 0 < u) (hu : u ≤ 1) (m : ℕ) (t : ℚ)
    (ht : t = (1 - u) / (1 + u)) :
    -(((logS m t : ℚ) : ℝ) + ((logTail m t : ℚ) : ℝ)) ≤ Real.log u ∧
      Real.log u ≤ -((logS m t : ℚ) : ℝ) := by
  have hpos : 0 < u⁻¹ := inv_pos.mpr hu0
  have h1 : 1 ≤ u⁻¹ := one_le_inv₀ hu0 |>.mpr hu
  have ht' : t = (u⁻¹ - 1) / (u⁻¹ + 1) := by
    rw [ht]; field_simp
  have := log_bounds_of u⁻¹ h1 m t ht'
  rw [Rat.cast_inv, Real.log_inv] at this
  constructor <;> linarith [this.1, this.2]

/-! ### `log 2` and `log 3` -/

theorem log_two_bounds :
    (693147180559945 / 10 ^ 15 : ℝ) < Real.log 2 ∧ Real.log 2 < 693147180559946 / 10 ^ 15 := by
  have h := log_bounds_of 2 (by norm_num) 30 (1 / 3) (by norm_num)
  have hl : (693147180559945 / 10 ^ 15 : ℚ) < logS 30 (1 / 3) := by decide +kernel
  have hu : logS 30 (1 / 3) + logTail 30 (1 / 3) < (693147180559946 / 10 ^ 15 : ℚ) := by
    decide +kernel
  have hl' : ((693147180559945 / 10 ^ 15 : ℚ) : ℝ) < ((logS 30 (1 / 3) : ℚ) : ℝ) := by
    exact_mod_cast hl
  have hu' : ((logS 30 (1 / 3) : ℚ) : ℝ) + ((logTail 30 (1 / 3) : ℚ) : ℝ) <
      ((693147180559946 / 10 ^ 15 : ℚ) : ℝ) := by exact_mod_cast hu
  push_cast at hl' hu' h
  constructor <;> linarith [h.1, h.2]

theorem log_three_bounds :
    (1098612288668109 / 10 ^ 15 : ℝ) < Real.log 3 ∧ Real.log 3 < 1098612288668110 / 10 ^ 15 := by
  have h := log_bounds_of 3 (by norm_num) 50 (1 / 2) (by norm_num)
  have hl : (1098612288668109 / 10 ^ 15 : ℚ) < logS 50 (1 / 2) := by decide +kernel
  have hu : logS 50 (1 / 2) + logTail 50 (1 / 2) < (1098612288668110 / 10 ^ 15 : ℚ) := by
    decide +kernel
  have hl' : ((1098612288668109 / 10 ^ 15 : ℚ) : ℝ) < ((logS 50 (1 / 2) : ℚ) : ℝ) := by
    exact_mod_cast hl
  have hu' : ((logS 50 (1 / 2) : ℚ) : ℝ) + ((logTail 50 (1 / 2) : ℚ) : ℝ) <
      ((1098612288668110 / 10 ^ 15 : ℚ) : ℝ) := by exact_mod_cast hu
  push_cast at hl' hu' h
  constructor <;> linarith [h.1, h.2]

/-! ### The two spectral rates -/

theorem log_sr_le :
    Real.log (156660580321280 * (325999287587431765 / 10 ^ 46)) ≤ -32908139 / 10 ^ 6 := by
  have hx : (0 : ℝ) < 156660580321280 * (325999287587431765 / 10 ^ 46) := by norm_num
  have hle : (156660580321280 * (325999287587431765 / 10 ^ 46) : ℝ) ≤
      ((7187638 / 10 ^ 7 : ℚ) : ℝ) / 2 ^ 47 := by norm_num
  have h1 := Real.log_le_log hx hle
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow] at h1
  have h := log_bounds_of_le_one (7187638 / 10 ^ 7) (by norm_num) (by norm_num) 20
    (2812362 / 17187638) (by norm_num)
  have hc : -logS 20 (2812362 / 17187638) - 47 * (693147180559945 / 10 ^ 15 : ℚ) ≤
      -32908139 / 10 ^ 6 := by decide +kernel
  have hc' : -((logS 20 (2812362 / 17187638) : ℚ) : ℝ) - 47 * ((693147180559945 / 10 ^ 15 : ℚ) : ℝ)
      ≤ ((-32908139 / 10 ^ 6 : ℚ) : ℝ) := by exact_mod_cast hc
  have h2 := log_two_bounds.1
  push_cast at hc' h1 h
  linarith [h.2]

theorem log_sR_le :
    Real.log (156660580321280 * (32723294395333 / 10 ^ 14)) ≤ 31568021 / 10 ^ 6 := by
  have hx : (0 : ℝ) < 156660580321280 * (32723294395333 / 10 ^ 14) := by norm_num
  have hle : (156660580321280 * (32723294395333 / 10 ^ 14) : ℝ) ≤
      ((14570249 / 10 ^ 7 : ℚ) : ℝ) * 2 ^ 45 := by norm_num
  have h1 := Real.log_le_log hx hle
  have h3 : Real.log (((14570249 / 10 ^ 7 : ℚ) : ℝ) * 2 ^ 45) =
      Real.log ((14570249 / 10 ^ 7 : ℚ) : ℝ) + 45 * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  rw [h3] at h1
  have h := log_bounds_of (14570249 / 10 ^ 7) (by norm_num) 20
    (4570249 / 24570249) (by norm_num)
  have hc : logS 20 (4570249 / 24570249) + logTail 20 (4570249 / 24570249) +
      45 * (693147180559946 / 10 ^ 15 : ℚ) ≤ 31568021 / 10 ^ 6 := by decide +kernel
  have hc' : ((logS 20 (4570249 / 24570249) : ℚ) : ℝ) + ((logTail 20 (4570249 / 24570249) : ℚ) : ℝ) +
      45 * ((693147180559946 / 10 ^ 15 : ℚ) : ℝ) ≤ ((31568021 / 10 ^ 6 : ℚ) : ℝ) := by
    exact_mod_cast hc
  have h2 := log_two_bounds.2
  push_cast at hc' h1 h
  linarith [h.2]

theorem log_sR_pos : 0 < Real.log (156660580321280 * (32723294395333 / 10 ^ 14)) :=
  Real.log_pos (by norm_num)

end Zeta2L2Chi3
