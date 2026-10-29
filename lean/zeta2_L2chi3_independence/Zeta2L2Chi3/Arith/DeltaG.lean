/-
# `g(n)` and the gamma factorization of `Δ_n` (helper for `DeltaVal`)

The definitions `C0X`, `gfunX` coincide definitionally with `C0`, `gfun` of `DeltaVal`.
-/
import Zeta2L2Chi3.Arith.DeltaCert

namespace Zeta2L2Chi3.Arith
open Zeta2L2Chi3

def C0X : ℚ := 2 ^ 8 * 3 ^ 30

def gfunX (n : ℕ) : ℚ :=
  3936600 * (8 * n + 1) * (9 * n + 1) * (15 * n + 2) * (20 * n + 3) * (24 * n + 1) ^ 2 /
  ((2 * n + 1) * (3 * n + 1) ^ 2 * (6 * n + 1) * (8 * n + 3) * (9 * n + 2) * (10 * n + 3) *
    (12 * n + 1) * (15 * n + 1) * (15 * n + 4) * (18 * n + 1) ^ 2 * (24 * n + 5) * (30 * n + 7))

lemma gfunX_fr (n : ℕ) : gfunX n = 3936600 * PL gN n / PL gD n := by
  simp only [gfunX, PL, gN, gD, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  push_cast; ring

theorem gfunX_pos (n : ℕ) : 0 < gfunX n := by
  rw [gfunX_fr]
  have hx : (0 : ℚ) ≤ n := by positivity
  exact div_pos (mul_pos (by norm_num) (PL_pos _ gN_pos _ hx)) (PL_pos _ gD_pos _ hx)

lemma gammaF_pm : ∀ fm ∈ gammaF, fm.2 = 1 ∨ fm.2 = -1 := by decide +kernel

lemma one_step (n : ℕ) : (Q n).det = C0X * (gfunX (n + 1) / gfunX n) *
    (gammaF.map fun fm => (∏ i ∈ Finset.range fm.1.la,
      (fm.1.be + ((fm.1.la * n : ℕ) : ℚ) + i)) ^ fm.2).prod := by
  rw [det_Q_step, gamma_fr gammaF gammaF_pm n, gfunX_fr, gfunX_fr]
  push_cast
  rw [PL_succ, PL_succ]
  simp only [stepN2, stepD2, PL_append, C0X, div_eq_mul_inv, mul_inv, inv_inv]
  ring

lemma rf_step (β : ℚ) (A n : ℕ) : rf β (A * (n + 1)) =
    rf β (A * n) * ∏ i ∈ Finset.range A, (β + ((A * n : ℕ) : ℚ) + i) := by
  unfold rf
  rw [mul_add, mul_one, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast; ring

theorem Delta_gammaX (n : ℕ) :
    Δ n = C0X ^ n * (gfunX n / gfunX 0) *
      (gammaF.map (fun fm => (rf (fm.1.be) (fm.1.la * n)) ^ fm.2)).prod := by
  induction n with
  | zero => simp [Δ, W, rf, div_self (gfunX_pos 0).ne']
  | succ n ih =>
    rw [show Δ (n + 1) = Δ n * (Q n).det from by simp [Δ, W, Matrix.det_mul], ih, one_step]
    simp only [rf_step, mul_zpow, List.prod_map_mul]
    have h0 := (gfunX_pos 0).ne'
    have hn := (gfunX_pos n).ne'
    field_simp
    ring


end Zeta2L2Chi3.Arith
