/-
# Lower bound for `log |q^f_n|`

`q^f_n = Σ_{k ≤ 8n+1} w(n,k) P_n(k)` with `w > 0`.  For `k ≥ ⌈4.4 n⌉` we have `P_n(k) ≤ 0`, and
`P_n(k₁) ≤ -4000 n⁴` at `k₁ = ⌈6.13 n⌉`; the terms with `k < ⌈4.4 n⌉` are bounded by
`10⁵ n⁴ exp(31.2 n + Err)` (monotonicity of `φ` on `[0, 6.1302]` and `φ(4.4) ≤ 31.2`), while
`w(n,k₁) ≥ exp(32.9081395 n - Err)`.  Hence `|q^f_n| ≥ exp(32.9081395 n - Err)` eventually.
-/
import Zeta2L2Chi3.Target2.QfStirling

namespace Zeta2L2Chi3.Arith

open Real Finset Filter

/-- the cubic `P_n(t)` over `ℝ` -/
noncomputable def PR (n : ℕ) (t : ℝ) : ℝ :=
  (19440 * (n : ℝ) ^ 4 + 13812 * n ^ 3 + 3219 * n ^ 2 + 308 * n + 11) / 3 -
    (4320 * (n : ℝ) ^ 3 + 4410 * n ^ 2 + 1045 * n + 69) * t / 6 - (1080 * (n : ℝ) ^ 2 + 315 * n + 7) * t ^ 2 / 6 +
    3 * t ^ 3

lemma Pcub_real (n k : ℕ) : ((Pcub n (k : ℚ) : ℚ) : ℝ) = PR n k := by
  rw [Pcub_eq, PR]; push_cast; ring

theorem fvecQ_zero_real (n : ℕ) :
    ((fvecQ n 0 : ℚ) : ℝ) = ∑ k ∈ range (8 * n + 2), ((wQ n k : ℚ) : ℝ) * PR n k := by
  rw [fvecQ_zero_eq, Rat.cast_sum]
  exact sum_congr rfl fun k _ => by rw [Rat.cast_mul, Pcub_real]

/-! ### Polynomial estimates -/

lemma PR_nonpos (n : ℕ) (hn : 34 ≤ n) (t : ℝ) (ht : 22 * (n : ℝ) / 5 ≤ t) (ht' : t ≤ 8 * n + 2) :
    PR n t ≤ 0 := by
  have hN : (34 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ)
  have ht0 : 0 ≤ t := by linarith
  have h1 : 3 * t ^ 3 ≤ 3 * (8 * N + 2) * t ^ 2 := by nlinarith [sq_nonneg t]
  have h2 : (720 * N ^ 3) * (22 * N / 5) ≤ (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) / 6 * t := by
    have : 720 * N ^ 3 ≤ (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) / 6 := by nlinarith
    exact mul_le_mul this ht (by positivity) (by positivity)
  have h3 : (180 * N ^ 2) * (22 * N / 5) ^ 2 ≤
      ((1080 * N ^ 2 + 315 * N + 7) / 6 - 3 * (8 * N + 2)) * t ^ 2 := by
    have a : 180 * N ^ 2 ≤ (1080 * N ^ 2 + 315 * N + 7) / 6 - 3 * (8 * N + 2) := by nlinarith
    have b : (22 * N / 5) ^ 2 ≤ t ^ 2 := by
      have : 0 ≤ 22 * N / 5 := by positivity
      nlinarith
    exact mul_le_mul a b (by positivity) (by nlinarith)
  have h4 : (19440 * N ^ 4 + 13812 * N ^ 3 + 3219 * N ^ 2 + 308 * N + 11) / 3 ≤
      6480 * N ^ 4 + 5784 * N ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (show (1:ℝ) ≤ N by linarith) 2]
  have h5 : 5784 * N ^ 3 ≤ 172 * N ^ 4 := by
    have : 0 ≤ N ^ 3 := by positivity
    nlinarith
  unfold PR
  nlinarith

lemma PR_k1 (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 613 * (n : ℝ) / 100 ≤ t) (ht' : t ≤ 613 * (n : ℝ) / 100 + 1) :
    PR n t ≤ -4000 * (n : ℝ) ^ 4 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ)
  have hs0 : 0 ≤ 613 * N / 100 := by positivity
  have h1 : (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) / 6 * (613 * N / 100) ≤
      (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) / 6 * t :=
    mul_le_mul_of_nonneg_left ht (by positivity)
  have h2 : (1080 * N ^ 2 + 315 * N + 7) / 6 * (613 * N / 100) ^ 2 ≤
      (1080 * N ^ 2 + 315 * N + 7) / 6 * t ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h3 : t ^ 3 ≤ (613 * N / 100 + 1) ^ 3 := by
    have : 0 ≤ t := by linarith
    exact pow_le_pow_left₀ this ht' 3
  have key : (19440 * N ^ 4 + 13812 * N ^ 3 + 3219 * N ^ 2 + 308 * N + 11) / 3 -
      (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) / 6 * (613 * N / 100) -
      (1080 * N ^ 2 + 315 * N + 7) / 6 * (613 * N / 100) ^ 2 + 3 * (613 * N / 100 + 1) ^ 3 ≤
      -4000 * N ^ 4 := by
    have hN2 : 1 ≤ N ^ 2 := by nlinarith
    have hN3 : N ^ 2 ≤ N ^ 3 := by nlinarith
    have hN4 : N ^ 3 ≤ N ^ 4 := by nlinarith
    nlinarith
  unfold PR
  have e1 : (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) * t / 6 =
    (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) / 6 * t := by ring
  have e2 : (1080 * N ^ 2 + 315 * N + 7) * t ^ 2 / 6 = (1080 * N ^ 2 + 315 * N + 7) / 6 * t ^ 2 := by ring
  rw [e1, e2]
  linarith

lemma PR_abs (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 8 * n + 2) :
    |PR n t| ≤ 100000 * (n : ℝ) ^ 4 := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ)
  have ht10 : t ≤ 10 * N := by linarith
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have hN3 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have hN4 : N ^ 3 ≤ N ^ 4 := by nlinarith
  have a0 : 0 ≤ (19440 * N ^ 4 + 13812 * N ^ 3 + 3219 * N ^ 2 + 308 * N + 11) / 3 := by positivity
  have a0' : (19440 * N ^ 4 + 13812 * N ^ 3 + 3219 * N ^ 2 + 308 * N + 11) / 3 ≤ 12300 * N ^ 4 := by
    nlinarith
  have a1 : 0 ≤ (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) * t / 6 := by positivity
  have a1' : (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) * t / 6 ≤ 16500 * N ^ 4 := by
    have : (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) * t ≤
        (4320 * N ^ 3 + 4410 * N ^ 2 + 1045 * N + 69) * (10 * N) :=
      mul_le_mul_of_nonneg_left ht10 (by positivity)
    nlinarith
  have a2 : 0 ≤ (1080 * N ^ 2 + 315 * N + 7) * t ^ 2 / 6 := by positivity
  have a2' : (1080 * N ^ 2 + 315 * N + 7) * t ^ 2 / 6 ≤ 23500 * N ^ 4 := by
    have ht2 : t ^ 2 ≤ (10 * N) ^ 2 := pow_le_pow_left₀ ht0 ht10 2
    have : (1080 * N ^ 2 + 315 * N + 7) * t ^ 2 ≤ (1080 * N ^ 2 + 315 * N + 7) * (10 * N) ^ 2 :=
      mul_le_mul_of_nonneg_left ht2 (by positivity)
    nlinarith
  have a3 : 0 ≤ 3 * t ^ 3 := by positivity
  have a3' : 3 * t ^ 3 ≤ 3000 * N ^ 4 := by
    have ht3 : t ^ 3 ≤ (10 * N) ^ 3 := pow_le_pow_left₀ ht0 ht10 3
    nlinarith
  unfold PR
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Weight estimates at the two cut points -/

/-- error term of the weight estimate -/
noncomputable def Err (n : ℕ) : ℝ := 30 * (Real.log (20 * n + 3) + 1)

lemma w_upper (n k : ℕ) (hn : 1 ≤ n) (hk : 5 * k < 22 * n) :
    ((wQ n k : ℚ) : ℝ) ≤ Real.exp (312 / 10 * n + Err n) := by
  have hk7 : k ≤ 7 * n := by omega
  have hpos := wQ_pos n k (by omega)
  have h := log_w_close n k hn hk7
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : (0 : ℝ) ≤ k / n := by positivity
  have hy1 : (k : ℝ) / n ≤ 22 / 5 := by
    rw [div_le_iff₀ hN]
    have : (5 * k : ℝ) ≤ 22 * n := by exact_mod_cast hk.le
    linarith
  have hmono : phi (k / n) ≤ phi (22 / 5) :=
    phi_monotoneOn ⟨hy0, by unfold Ytop; linarith⟩ ⟨by norm_num, by unfold Ytop; norm_num⟩ hy1
  have hb := phi_b_upper
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.2
  rw [abs_le] at h
  unfold Err
  nlinarith [h.2]

lemma w_lower (n k : ℕ) (hn : 4950 ≤ n) (hk1 : 613 * n ≤ 100 * k) (hk2 : 100 * k ≤ 613 * n + 99) :
    Real.exp (329081395 / 10 ^ 7 * n - Err n) ≤ ((wQ n k : ℚ) : ℝ) := by
  have hk7 : k ≤ 7 * n := by omega
  have hpos := wQ_pos n k (by omega)
  have h := log_w_close n k (by omega) hk7
  have hN : (4950 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hy0 : (613 : ℝ) / 100 ≤ k / n := by
    rw [le_div_iff₀ hN0]
    have : (613 * n : ℝ) ≤ 100 * k := by exact_mod_cast hk1
    linarith
  have hy1 : (k : ℝ) / n ≤ Ytop := by
    unfold Ytop
    rw [div_le_iff₀ hN0]
    have : (100 * k : ℝ) ≤ 613 * n + 99 := by exact_mod_cast hk2
    nlinarith
  have hmono : phi (613 / 100) ≤ phi (k / n) :=
    phi_monotoneOn ⟨by norm_num, by unfold Ytop; norm_num⟩ ⟨by linarith, hy1⟩ hy0
  have ha := phi_a_lower
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.2
  rw [abs_le] at h
  unfold Err
  nlinarith [h.1]

/-! ### The main estimate -/

theorem qf_lower_main : ∀ᶠ n : ℕ in atTop,
    Real.exp (329081395 / 10 ^ 7 * n - Err n) ≤ |((fvecQ n 0 : ℚ) : ℝ)| := by
  filter_upwards [eventually_ge_atTop 4950, eventually_log_small 66 1 20 3 one_pos (by norm_num)
    (by norm_num)] with n hn hlog
  have hN : (4950 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by linarith
  set K0 := (22 * n + 4) / 5 with hK0
  set k1 := (613 * n + 99) / 100 with hk1
  have hK0a : 22 * n ≤ 5 * K0 := by omega
  have hK0b : 5 * K0 ≤ 22 * n + 4 := by omega
  have hk1a : 613 * n ≤ 100 * k1 := by omega
  have hk1b : 100 * k1 ≤ 613 * n + 99 := by omega
  set X := Real.exp (312 / 10 * n + Err n) with hX
  set Y := Real.exp (329081395 / 10 ^ 7 * n - Err n) with hY
  have hYpos : 0 < Y := Real.exp_pos _
  rw [fvecQ_zero_real, ← sum_range_add_sum_Ico _ (show K0 ≤ 8 * n + 2 by omega)]
  -- low part
  have hlow : ∑ k ∈ range K0, ((wQ n k : ℚ) : ℝ) * PR n k ≤ K0 * (100000 * (n : ℝ) ^ 4 * X) := by
    have : ∀ k ∈ range K0, ((wQ n k : ℚ) : ℝ) * PR n k ≤ 100000 * (n : ℝ) ^ 4 * X := by
      intro k hk
      have hk' := mem_range.1 hk
      have hw := wQ_pos n k (by omega)
      have hwu := w_upper n k (by omega) (by omega)
      have hP := PR_abs n (by omega) k (k.cast_nonneg) (by
        have : (k : ℝ) ≤ 8 * n + 1 := by exact_mod_cast (show k ≤ 8 * n + 1 by omega)
        linarith)
      calc ((wQ n k : ℚ) : ℝ) * PR n k ≤ ((wQ n k : ℚ) : ℝ) * |PR n k| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hw.le
        _ ≤ X * (100000 * (n : ℝ) ^ 4) := mul_le_mul hwu hP (abs_nonneg _) (Real.exp_pos _).le
        _ = 100000 * (n : ℝ) ^ 4 * X := by ring
    have h := sum_le_sum this
    rw [sum_const, card_range, nsmul_eq_mul] at h
    exact h
  -- high part
  have hk1mem : k1 ∈ Ico K0 (8 * n + 2) := mem_Ico.2 ⟨by omega, by omega⟩
  have hhigh : ∑ k ∈ Ico K0 (8 * n + 2), ((wQ n k : ℚ) : ℝ) * PR n k ≤
      ((wQ n k1 : ℚ) : ℝ) * PR n k1 := by
    rw [← add_sum_erase _ _ hk1mem]
    have : ∑ k ∈ (Ico K0 (8 * n + 2)).erase k1, ((wQ n k : ℚ) : ℝ) * PR n k ≤ 0 := by
      refine sum_nonpos fun k hk => ?_
      have hk' := mem_Ico.1 (mem_of_mem_erase hk)
      have hw := wQ_pos n k (by omega)
      have hP : PR n k ≤ 0 := PR_nonpos n (by omega) k (by
          have : (22 * n : ℝ) ≤ 5 * k := by
            have := hK0a.trans (Nat.mul_le_mul_left 5 hk'.1); exact_mod_cast this
          linarith) (by
          have : (k : ℝ) ≤ 8 * n + 1 := by exact_mod_cast (show k ≤ 8 * n + 1 by omega)
          linarith)
      exact mul_nonpos_of_nonneg_of_nonpos hw.le hP
    linarith
  have hwk1 := w_lower n k1 hn hk1a hk1b
  have hPk1 : PR n k1 ≤ -4000 * (n : ℝ) ^ 4 := PR_k1 n (by omega) k1
    (by have : (613 * n : ℝ) ≤ 100 * k1 := by exact_mod_cast hk1a
        linarith)
    (by have : (100 * k1 : ℝ) ≤ 613 * n + 99 := by exact_mod_cast hk1b
        linarith)
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hN1
  have htop : ((wQ n k1 : ℚ) : ℝ) * PR n k1 ≤ -4000 * (n : ℝ) ^ 4 * Y := by
    have h1 : ((wQ n k1 : ℚ) : ℝ) * PR n k1 ≤ ((wQ n k1 : ℚ) : ℝ) * (-4000 * (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hPk1 (wQ_pos n k1 (by omega)).le
    have h2 : Y * (4000 * (n : ℝ) ^ 4) ≤ ((wQ n k1 : ℚ) : ℝ) * (4000 * (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_right hwk1 (by positivity)
    nlinarith
  -- comparison of the exponentials
  have hcmp : (K0 : ℝ) * (100000 * X) ≤ 2000 * Y := by
    have hK0r : (K0 : ℝ) ≤ 5 * n := by
      have : (5 * K0 : ℝ) ≤ 22 * n + 4 := by exact_mod_cast hK0b
      linarith
    have hl0 : 0 ≤ Real.log (20 * n + 3) := Real.log_nonneg (by linarith)
    have hlogn : Real.log (250 * n) ≤ 6 + Real.log (20 * n + 3) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      have h250 : Real.log 250 ≤ 6 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.exp_one_gt_d9
        have h3 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
        have h4 : (2.7 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith) 6
        rw [h3]; nlinarith
      have := Real.log_le_log (by positivity) (show (n : ℝ) ≤ 20 * n + 3 by linarith)
      linarith
    have hexp : 250 * (n : ℝ) ≤ Real.exp ((329081395 / 10 ^ 7 - 312 / 10) * n - 2 * Err n) := by
      rw [← Real.log_le_iff_le_exp (by positivity)]
      unfold Err
      nlinarith
    have : (K0 : ℝ) * (100000 * X) ≤ 5 * n * (100000 * X) :=
      mul_le_mul_of_nonneg_right hK0r (by positivity)
    have e : Real.exp ((329081395 / 10 ^ 7 - 312 / 10) * n - 2 * Err n) * X = Y := by
      rw [hX, hY, ← Real.exp_add]; congr 1; ring
    nlinarith [Real.exp_pos (312 / 10 * n + Err n)]
  have hsum : ∑ k ∈ range K0, ((wQ n k : ℚ) : ℝ) * PR n k +
      ∑ k ∈ Ico K0 (8 * n + 2), ((wQ n k : ℚ) : ℝ) * PR n k ≤ -Y := by
    have : (K0 : ℝ) * (100000 * (n : ℝ) ^ 4 * X) ≤ 2000 * (n : ℝ) ^ 4 * Y := by
      have := mul_le_mul_of_nonneg_left hcmp (show (0 : ℝ) ≤ (n : ℝ) ^ 4 by positivity)
      linarith
    nlinarith
  rw [abs_of_neg (by linarith)]
  linarith

theorem log_qf_lower' : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (32908136 / 10 ^ 6 - ε) * n ≤ Real.log |(fvecQ n 0 : ℝ)| := by
  intro ε hε
  filter_upwards [qf_lower_main, eventually_log_small 30 ε 20 3 hε (by norm_num) (by norm_num)]
    with n h1 h2
  have h := Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp] at h
  unfold Err at h
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

end Zeta2L2Chi3.Arith
