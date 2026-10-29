/-
# Elementary Stirling-type bounds

`LF x = x log x - x` is an antiderivative of `log`.  From `log(1+u) ≤ u` and `log(1+u) ≥ u/(1+u)` we
get, for `u > 0`, `d ≥ 0`, `d log u ≤ LF(u+d) - LF u ≤ d log(u+d)`; telescoping gives two-sided
bounds for `log ∏_{i<M} (a+i)` (rising factorials with real start `a`).
-/
import Mathlib

namespace Zeta2L2Chi3.Arith

open Real Finset

/-- `LF x = x log x - x` -/
noncomputable def LF (x : ℝ) : ℝ := x * Real.log x - x

lemma LF_zero : LF 0 = 0 := by simp [LF]

lemma LF_one : LF 1 = -1 := by simp [LF]

lemma LF_incr_lower {u d : ℝ} (hu : 0 < u) (hd : 0 ≤ d) : d * Real.log u ≤ LF (u + d) - LF u := by
  unfold LF
  have hud : 0 < u + d := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hud hu)
  rw [Real.log_div hud.ne' hu.ne', inv_div] at h
  have h2 : 1 - u / (u + d) = d / (u + d) := by field_simp; ring
  rw [h2, div_le_iff₀ hud] at h
  nlinarith

lemma LF_incr_upper {u d : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) : LF (u + d) - LF u ≤ d * Real.log (u + d) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [LF]; linarith
  unfold LF
  have hud : 0 < u + d := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hud hu)
  rw [Real.log_div hud.ne' hu.ne'] at h
  have h2 : (u + d) / u - 1 = d / u := by field_simp; ring
  rw [h2, le_div_iff₀ hu] at h
  nlinarith

lemma LF_ge_neg_one {x : ℝ} (hx : 0 ≤ x) : -1 ≤ LF x := by
  rcases le_total 1 x with h | h
  · have := LF_incr_lower (u := 1) (d := x - 1) one_pos (by linarith)
    simp only [Real.log_one, mul_zero, add_sub_cancel] at this
    rw [LF_one] at this; linarith
  · have := LF_incr_upper (u := x) (d := 1 - x) hx (by linarith)
    simp only [add_sub_cancel, Real.log_one, mul_zero] at this
    rw [LF_one] at this; linarith

lemma LF_nonpos {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) : LF x ≤ 0 := by
  unfold LF
  have := Real.log_nonpos hx h1
  nlinarith

lemma LF_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : LF x ≤ LF y := by
  have := LF_incr_lower (u := x) (d := y - x) (by linarith) (by linarith)
  have h0 : 0 ≤ (y - x) * Real.log x := mul_nonneg (by linarith) (Real.log_nonneg hx)
  rw [add_sub_cancel] at this; linarith

/-- the Lipschitz-type comparison -/
lemma LF_close {X Y c M : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hc : |X - Y| ≤ c) (hXM : X ≤ M) (hYM : Y ≤ M)
    (hM : 1 ≤ M) : |LF X - LF Y| ≤ c * Real.log M + 1 := by
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hc0 : 0 ≤ c := (abs_nonneg _).trans hc
  -- key one-sided bound for `A ≤ B`
  have key : ∀ A B : ℝ, 0 ≤ A → A ≤ B → B ≤ M → B - A ≤ c →
      LF B - LF A ≤ c * Real.log M ∧ -1 ≤ LF B - LF A := by
    intro A B hA hAB hBM hBA
    constructor
    · have h := LF_incr_upper (u := A) (d := B - A) hA (by linarith)
      rw [add_sub_cancel] at h
      rcases le_total 1 B with hB1 | hB1
      · have hl : Real.log B ≤ Real.log M := Real.log_le_log (by linarith) hBM
        have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
        have : (B - A) * Real.log B ≤ c * Real.log M := by
          apply mul_le_mul hBA hl hlB hc0
        linarith
      · have hlB : Real.log B ≤ 0 := Real.log_nonpos (by linarith) hB1
        have : (B - A) * Real.log B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hlB
        nlinarith
    · rcases le_total A 1 with hA1 | hA1
      · have := LF_nonpos hA hA1
        have := LF_ge_neg_one (le_trans hA hAB)
        linarith
      · have := LF_mono hA1 hAB
        linarith
  have hcl : 0 ≤ c * Real.log M := mul_nonneg hc0 hlM
  rw [abs_le]
  rcases le_total X Y with hXY | hXY
  · have hYX : Y - X ≤ c := by rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hc; exact hc
    obtain ⟨h1, h2⟩ := key X Y hX hXY hYM hYX
    constructor <;> linarith
  · have hXY' : X - Y ≤ c := by rw [abs_of_nonneg (by linarith)] at hc; exact hc
    obtain ⟨h1, h2⟩ := key Y X hY hXY hXM hXY'
    constructor <;> linarith

/-- homogeneity -/
lemma LF_mul (N z : ℝ) (hN : 0 < N) : LF (N * z) = N * z * Real.log N + N * LF z := by
  unfold LF
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [Real.log_mul hN.ne' hz]
  ring

/-! ### Rising factorials with real start -/

lemma prod_pos_of {a : ℝ} (ha : 0 < a) (M : ℕ) : 0 < ∏ i ∈ range M, (a + i) :=
  prod_pos fun i _ => by positivity

lemma log_prod_upper (a : ℝ) (ha : 0 < a) (M : ℕ) :
    Real.log (∏ i ∈ range M, (a + i)) ≤ LF (a + M) - LF a := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [prod_range_succ, Real.log_mul (prod_pos_of ha M).ne' (by positivity)]
    have h := LF_incr_lower (u := a + M) (d := 1) (by positivity) zero_le_one
    push_cast
    rw [show a + ((M : ℝ) + 1) = a + M + 1 by ring]
    linarith

lemma log_prod_lower (a : ℝ) (ha : 1 ≤ a) (M : ℕ) :
    LF (a + M - 1) - LF (a - 1) ≤ Real.log (∏ i ∈ range M, (a + i)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [prod_range_succ, Real.log_mul (prod_pos_of (by linarith) M).ne' (by positivity)]
    have h := LF_incr_upper (u := a + M - 1) (d := 1)
      (by linarith [show (0:ℝ) ≤ M from M.cast_nonneg]) zero_le_one
    push_cast
    rw [show a + ((M : ℝ) + 1) - 1 = a + M by ring]
    rw [show a + M - 1 + 1 = a + M by ring] at h
    linarith

/-- lower bound for a start in `(0, 1]` -/
lemma log_prod_lower' (a : ℝ) (ha : 0 < a) (M : ℕ) (hM : 1 ≤ M) :
    Real.log a + LF (a + M - 1) - LF a ≤ Real.log (∏ i ∈ range M, (a + i)) := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [prod_range_succ']
  have h := log_prod_lower (a + 1) (by linarith) M'
  have e : ∏ i ∈ range M', (a + ((i + 1 : ℕ) : ℝ)) = ∏ i ∈ range M', (a + 1 + i) :=
    prod_congr rfl fun i _ => by push_cast; ring
  simp only [Nat.cast_zero, add_zero]
  rw [e, Real.log_mul (prod_pos_of (by linarith) M').ne' ha.ne']
  push_cast
  rw [show a + 1 + M' - 1 = a + (M' + 1) - 1 by ring, show a + 1 - 1 = a by ring] at h
  linarith

end Zeta2L2Chi3.Arith

namespace Zeta2L2Chi3.Arith

open Filter

/-- `C (log (a n + b) + 1) ≤ ε n` eventually -/
lemma eventually_log_small (C ε a b : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, C * (Real.log (a * n + b) + 1) ≤ ε * n := by
  set C' := max C 1 with hC'
  have hC1 : 1 ≤ C' := le_max_right _ _
  have hδ : 0 < ε / (4 * C') / a := by positivity
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ ε / (4 * C') / a * x := by
    have := Real.isLittleO_log_id_atTop.bound hδ
    filter_upwards [this, eventually_ge_atTop 1] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (by simp; linarith)] at hx
    simpa using hx
  have h2 : Tendsto (fun n : ℕ => a * n + b) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop)
  filter_upwards [h2.eventually h1, h2.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop ⌈b / a + 2 * C' / ε⌉₊] with n hn hn1 hn2
  have hn2' : b / a + 2 * C' / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  have hl0 : 0 ≤ Real.log (a * n + b) := Real.log_nonneg hn1
  have hb' : b ≤ a * n := by
    have : b / a ≤ n := by linarith [show 0 ≤ 2 * C' / ε by positivity]
    rwa [div_le_iff₀ ha, mul_comm] at this
  have hc' : 2 * C' ≤ ε * n := by
    have : 2 * C' / ε ≤ n := by linarith [show 0 ≤ b / a by positivity]
    rw [div_le_iff₀ hε] at this; linarith
  have e1 : ε / (4 * C') / a * (a * n + b) ≤ ε / (2 * C') * n := by
    have h4 : ε / (4 * C') / a * (a * n + b) ≤ ε / (4 * C') / a * (2 * a * n) := by
      gcongr; linarith
    have h5 : ε / (4 * C') / a * (2 * a * n) = ε / (2 * C') * n := by field_simp; ring
    linarith
  have hlog : Real.log (a * n + b) ≤ ε / (2 * C') * n := hn.trans e1
  have hCC : C * (Real.log (a * n + b) + 1) ≤ C' * (Real.log (a * n + b) + 1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have h6 : C' * Real.log (a * n + b) ≤ C' * (ε / (2 * C') * n) :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  have e2 : C' * (ε / (2 * C') * n) = ε * n / 2 := by field_simp
  nlinarith

end Zeta2L2Chi3.Arith
