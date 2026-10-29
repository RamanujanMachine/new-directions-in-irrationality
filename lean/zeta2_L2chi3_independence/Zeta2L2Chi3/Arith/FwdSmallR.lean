/-
# Small primes: the real form of the bound

With `L = ⌊log_q(144n+24)⌋ + 1` (so `q^L > 144n + 24`) and `144n + 24 ≤ n^9` (`n ≥ 2`):
`v_q(f_n) ≥ -λ_q n - 17 - 63 log n / log q`.
-/
import Zeta2L2Chi3.Arith.FwdSmallP

open Finset

noncomputable section

namespace Zeta2L2Chi3.Arith

theorem fvecE_val_real (q : ℕ) [hq : Fact q.Prime] (n : ℕ) (hn : 2 ≤ n) (i : Fin 3)
    (h0 : fvecE n i ≠ 0) :
    -(lam q : ℝ) * n - 17 - 63 * (Real.log n / Real.log q) ≤ (padicValRat q (fvecE n i) : ℝ) := by
  set m := 144 * n + 24 with hm
  set L := Nat.log q m + 1 with hL
  have hqL : m < q ^ L := Nat.lt_pow_succ_log_self hq.out.one_lt m
  have hv := (fvecE_small (q := q) n L hqL i).resolve_left h0
  have hv' : (-(lam q : ℝ) * n - 10 - 7 * L) ≤ (padicValRat q (fvecE n i) : ℝ) := by
    exact_mod_cast hv
  -- `L ≤ 9 log n / log q + 1`
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hm9 : m ≤ n ^ 9 := by
    have : 2 ^ 8 ≤ n ^ 8 := Nat.pow_le_pow_left hn 8
    have : n ^ 9 = n ^ 8 * n := by ring
    nlinarith
  have hpow : q ^ Nat.log q m ≤ m := Nat.pow_log_le_self q (by omega)
  have hlog : (Nat.log q m : ℝ) * Real.log q ≤ 9 * Real.log n := by
    have h1 : ((q ^ Nat.log q m : ℕ) : ℝ) ≤ ((n ^ 9 : ℕ) : ℝ) := by exact_mod_cast hpow.trans hm9
    have hpos : (0 : ℝ) < ((q ^ Nat.log q m : ℕ) : ℝ) := by
      exact_mod_cast pow_pos hq.out.pos _
    have h2 := Real.log_le_log hpos h1
    push_cast at h2
    rwa [Real.log_pow, Real.log_pow] at h2
  have hNl : (Nat.log q m : ℝ) ≤ 9 * (Real.log n / Real.log q) := by
    rw [mul_div_assoc', le_div_iff₀ hlogq]; exact hlog
  have hLr : (L : ℝ) = Nat.log q m + 1 := by rw [hL]; push_cast; ring
  rw [hLr] at hv'
  linarith

theorem lam_two : lam 2 = 6 := rfl
theorem lam_three : lam 3 = 9 := rfl
theorem lam_ge_five (q : ℕ) (hq : 5 ≤ q) : lam q = 0 := by
  unfold lam; rw [if_neg (by omega), if_neg (by omega)]

theorem log_ge_half (n : ℕ) (hn : 2 ≤ n) : 1 / 2 ≤ Real.log n := by
  have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have := Real.log_two_gt_d9
  linarith

end Zeta2L2Chi3.Arith
