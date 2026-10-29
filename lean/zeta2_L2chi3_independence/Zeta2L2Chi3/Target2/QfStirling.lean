/-
# Stirling estimate for the double-pole weights

`|log w(n,k) - n φ(k/n)| ≤ 30 (log (20n+3) + 1)` for `1 ≤ n`, `k ≤ 7n`.
-/
import Zeta2L2Chi3.Target2.QfWeights

namespace Zeta2L2Chi3.Arith

open Real Finset Filter

lemma LF_near {N X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h1 : X - Y ≤ 3) (h2 : Y - X ≤ 3)
    (hX' : X ≤ 20 * N + 3) (hY' : Y ≤ 20 * N + 3) (hN : 1 ≤ N) :
    LF Y - (3 * Real.log (20 * N + 3) + 1) ≤ LF X ∧ LF X ≤ LF Y + (3 * Real.log (20 * N + 3) + 1) := by
  have h := LF_close (c := 3) (M := 20 * N + 3) hX hY (abs_le.2 ⟨by linarith, by linarith⟩) hX' hY'
    (by linarith)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

lemma H_eq (N x : ℝ) (hN : 0 < N) :
    LF (x + 12 * N) - LF (x + 2 * N) + LF (x + 6 * N) - LF x + LF (x + 5 * N) - LF (x + 2 * N) - LF x -
      LF (10 * N - x) - LF (x + N) - LF (8 * N - x) = N * phi (x / N) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = N * y := ⟨x / N, by field_simp⟩
  rw [mul_div_cancel_left₀ y hN.ne', show N * y + 12 * N = N * (y + 12) by ring,
    show N * y + 2 * N = N * (y + 2) by ring, show N * y + 6 * N = N * (y + 6) by ring,
    show N * y + 5 * N = N * (y + 5) by ring, show 10 * N - N * y = N * (10 - y) by ring,
    show N * y + N = N * (y + 1) by ring, show 8 * N - N * y = N * (8 - y) by ring]
  simp only [LF_mul N _ hN]
  rw [phi_eq_LF]
  ring

set_option maxHeartbeats 1000000 in
theorem log_w_close (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ 7 * n) :
    |Real.log ((wQ n k : ℚ) : ℝ) - n * phi (k / n)| ≤ 30 * (Real.log (20 * n + 3) + 1) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hx7 : (k : ℝ) ≤ 7 * n := by exact_mod_cast hk
  set x : ℝ := (k : ℝ) with hxdef
  set N : ℝ := (n : ℝ) with hNdef
  -- comparisons with the homogeneous arguments
  have a1 := LF_near (N := N) (X := x + 2 * N + 1 + (10 * N + 1)) (Y := x + 12 * N)
    (by positivity) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have a2 := LF_near (N := N) (X := x + 2 * N + 1) (Y := x + 2 * N)
    (by positivity) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have a3 := LF_near (N := N) (X := x + 2 * N + 1 + (10 * N + 1) - 1) (Y := x + 12 * N)
    (by linarith) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have a4 := LF_near (N := N) (X := x + 2 * N + 1 - 1) (Y := x + 2 * N)
    (by linarith) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have b1 := LF_near (N := N) (X := x + 4 / 3 + (6 * N + 1)) (Y := x + 6 * N)
    (by positivity) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have b2 := LF_near (N := N) (X := x + 4 / 3) (Y := x)
    (by positivity) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have b3 := LF_near (N := N) (X := x + 4 / 3 + (6 * N + 1) - 1) (Y := x + 6 * N)
    (by linarith) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have b4 := LF_near (N := N) (X := x + 4 / 3 - 1) (Y := x)
    (by linarith) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have d1 := LF_near (N := N) (X := x + 2 * N + 3 / 2 + (3 * N + 1)) (Y := x + 5 * N)
    (by positivity) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have d2 := LF_near (N := N) (X := x + 2 * N + 3 / 2) (Y := x + 2 * N)
    (by positivity) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have d3 := LF_near (N := N) (X := x + 2 * N + 3 / 2 + (3 * N + 1) - 1) (Y := x + 5 * N)
    (by linarith) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have d4 := LF_near (N := N) (X := x + 2 * N + 3 / 2 - 1) (Y := x + 2 * N)
    (by linarith) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have e1 := LF_near (N := N) (X := 1 + x) (Y := x)
    (by positivity) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have e2 := LF_near (N := N) (X := 1 + x - 1) (Y := x)
    (by linarith) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have f1 := LF_near (N := N) (X := 1 + (10 * N + 1 - x)) (Y := 10 * N - x)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have f2 := LF_near (N := N) (X := 1 + (10 * N + 1 - x) - 1) (Y := 10 * N - x)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have g1 := LF_near (N := N) (X := 1 + (x + N)) (Y := x + N)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have g2 := LF_near (N := N) (X := 1 + (x + N) - 1) (Y := x + N)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have h1 := LF_near (N := N) (X := 1 + (8 * N + 1 - x)) (Y := 8 * N - x)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hN
  have h2 := LF_near (N := N) (X := 1 + (8 * N + 1 - x) - 1) (Y := 8 * N - x)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hN
  rw [wQ_real n k (by omega), NF_real, fact_real, fact_real, fact_real, fact_real]
  have c10 : ((10 * n + 1 - k : ℕ) : ℝ) = 10 * N + 1 - x := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c8 : ((8 * n + 1 - k : ℕ) : ℝ) = 8 * N + 1 - x := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have ckn : ((k + n : ℕ) : ℝ) = x + N := by push_cast; ring
  set A := ∏ i ∈ range (10 * n + 1), (x + 2 * N + 1 + i)
  set B := ∏ i ∈ range (6 * n + 1), (x + 4 / 3 + i)
  set C := ∏ i ∈ range (3 * n + 1), (x + 2 * N + 3 / 2 + i)
  set D := ∏ i ∈ range k, ((1 : ℝ) + i)
  set E := ∏ i ∈ range (10 * n + 1 - k), ((1 : ℝ) + i)
  set F := ∏ i ∈ range (k + n), ((1 : ℝ) + i)
  set G := ∏ i ∈ range (8 * n + 1 - k), ((1 : ℝ) + i)
  have hA : 0 < A := prod_pos_of (by positivity) _
  have hB : 0 < B := prod_pos_of (by positivity) _
  have hC : 0 < C := prod_pos_of (by positivity) _
  have hD : 0 < D := prod_pos_of one_pos _
  have hE : 0 < E := prod_pos_of one_pos _
  have hF : 0 < F := prod_pos_of one_pos _
  have hG : 0 < G := prod_pos_of one_pos _
  have hlog : Real.log (A * B * C / (D * E * F * G)) = Real.log A + Real.log B + Real.log C -
      (Real.log D + Real.log E + Real.log F + Real.log G) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  rw [hlog]
  -- rising-factorial bounds
  have Au := log_prod_upper (x + 2 * N + 1) (by positivity) (10 * n + 1)
  have Al := log_prod_lower (x + 2 * N + 1) (by linarith) (10 * n + 1)
  have Bu := log_prod_upper (x + 4 / 3) (by positivity) (6 * n + 1)
  have Bl := log_prod_lower (x + 4 / 3) (by linarith) (6 * n + 1)
  have Cu := log_prod_upper (x + 2 * N + 3 / 2) (by positivity) (3 * n + 1)
  have Cl := log_prod_lower (x + 2 * N + 3 / 2) (by linarith) (3 * n + 1)
  have Du := log_prod_upper 1 one_pos k
  have Dl := log_prod_lower 1 le_rfl k
  have Eu := log_prod_upper 1 one_pos (10 * n + 1 - k)
  have El := log_prod_lower 1 le_rfl (10 * n + 1 - k)
  have Fu := log_prod_upper 1 one_pos (k + n)
  have Fl := log_prod_lower 1 le_rfl (k + n)
  have Gu := log_prod_upper 1 one_pos (8 * n + 1 - k)
  have Gl := log_prod_lower 1 le_rfl (8 * n + 1 - k)
  rw [c10] at Eu El
  rw [c8] at Gu Gl
  rw [ckn] at Fu Fl
  push_cast at Au Al Bu Bl Cu Cl
  simp only [LF_one, LF_zero, sub_self] at Du Dl Eu El Fu Fl Gu Gl
  have hH := H_eq N x (by linarith)
  rw [abs_le]
  constructor
  · linarith [a3.1, a4.2, b3.1, b4.2, d3.1, d4.2, e1.2, f1.2, g1.2, h1.2]
  · linarith [a1.2, a2.1, b1.2, b2.1, d1.2, d2.1, e2.1, f2.1, g2.1, h2.1]

end Zeta2L2Chi3.Arith
