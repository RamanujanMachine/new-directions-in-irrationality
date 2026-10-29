/-
# The dual packet lemma (Lemma A)

For a prime `p ≥ 5` with `p² > 144 n + 24`, the columns `k = 1, 2` of
`(p² B₀', B_T, B_H, B_I + B_T + B_H)` lie in the `ℤ_(p)`-span of the weighted generators of the
packet types of all residue classes `r < p`.  Here `B₀' = B₀ - c_T B_T - c_H B_H` removes the class
constants of the regular harmonic part (`c_I = 0`).
-/
import Zeta2L2Chi3.Arith.Lattice
import Zeta2L2Chi3.Arith.Family
import Zeta2L2Chi3.Dual
import Zeta2L2Chi3.Arith.Harmonic
import Zeta2L2Chi3.Arith.Taylor
import Zeta2L2Chi3.Arith.Lagrange
import Zeta2L2Chi3.Arith.LemmaAAux3

namespace Zeta2L2Chi3.Arith

/-- the modified constant row -/
def B0' (n p k : ℕ) : ℚ := B0 n k - cT p * BT n k - cH p * BH n k

/-- the column vector `(p² B₀', B_T, B_H, B_I + B_T + B_H)` -/
def colVec (n p k : ℕ) : Fin 4 → ℚ :=
  ![(p : ℚ) ^ 2 * B0' n p k, BT n k, BH n k, BI n k + BT n k + BH n k]

open Finset LA in
/-- the column vector is the row vector of the concrete zero/pole data -/
theorem colVec_eq (n p k : ℕ) : colVec n p k = rowVec p (Zd n) (Pd n p) k (Pd n p) := by
  have hI : ∀ g : Rec → ℚ, ((recs (dualP[0]!) n 0 (fun j => hwI n j)).map g).sum =
      ∑ j ∈ range (10 * n + 2), g (iP n j, 0, hwI n j) := by
    intro g; rw [sum_recs, lenI]; apply sum_congr rfl; intro j _; rw [cI]
  have hT : ∀ g : Rec → ℚ, ((recs (dualP[1]!) n 1 (fun j => hwT j + cT p)).map g).sum =
      ∑ j ∈ range (6 * n + 2), g (tP j, 1, hwT j + cT p) := by
    intro g; rw [sum_recs, lenT]; apply sum_congr rfl; intro j _; rw [cT']
  have hH : ∀ g : Rec → ℚ, ((recs (dualP[2]!) n 2 (fun j => hwH n j + cH p)).map g).sum =
      ∑ j ∈ range (3 * n + 2), g (hP n j, 2, hwH n j + cH p) := by
    intro g; rw [sum_recs, lenH]; apply sum_congr rfl; intro j _; rw [cH']
  have hsum : ∀ g : Rec → ℚ, ((Pd n p).map g).sum =
      ∑ j ∈ range (10 * n + 2), g (iP n j, 0, hwI n j) +
      ∑ j ∈ range (6 * n + 2), g (tP j, 1, hwT j + cT p) +
      ∑ j ∈ range (3 * n + 2), g (hP n j, 2, hwH n j + cH p) := by
    intro g
    rw [Pd, List.map_append, List.map_append, List.sum_append, List.sum_append, hI, hT, hH]
  funext i
  fin_cases i
  · simp only [colVec, rowVec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    congr 1
    rw [hsum]
    simp only [vres_I, vres_T, vres_H]
    have eI : ∑ j ∈ range (10 * n + 2), -resI n j * hwI n j * (iP n j : ℚ) ^ k =
        -(∑ j ∈ range (10 * n + 2), resI n j * hwI n j * (iP n j : ℚ) ^ k) := by
      rw [← sum_neg_distrib]; apply sum_congr rfl; intro j _; ring
    have eT : ∑ j ∈ range (6 * n + 2), -resT n j * (hwT j + cT p) * (tP j : ℚ) ^ k =
        -(∑ j ∈ range (6 * n + 2), resT n j * hwT j * (tP j : ℚ) ^ k) +
          cT p * ∑ j ∈ range (6 * n + 2), -resT n j * (tP j : ℚ) ^ k := by
      rw [mul_sum, ← sum_neg_distrib, ← sum_add_distrib]; apply sum_congr rfl; intro j _; ring
    have eH : ∑ j ∈ range (3 * n + 2), -resH n j * (hwH n j + cH p) * (hP n j : ℚ) ^ k =
        -(∑ j ∈ range (3 * n + 2), resH n j * hwH n j * (hP n j : ℚ) ^ k) +
          cH p * ∑ j ∈ range (3 * n + 2), -resH n j * (hP n j : ℚ) ^ k := by
      rw [mul_sum, ← sum_neg_distrib, ← sum_add_distrib]; apply sum_congr rfl; intro j _; ring
    rw [eI, eT, eH]
    simp only [B0', B0, BT, BH]
    ring
  · simp only [colVec, rowVec, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hsum]
    simp only [ind, vres_T]
    simp [BT]
  · show BH n k = ((Pd n p).map (fun q => ind 2 q * (vres (Zd n) (Pd n p) q.1 * q.1 ^ k))).sum
    rw [hsum]
    simp only [ind, vres_H]
    simp [BH]
  · show BI n k + BT n k + BH n k = ((Pd n p).map (fun q => vres (Zd n) (Pd n p) q.1 * q.1 ^ k)).sum
    rw [hsum]
    simp only [vres_I, vres_T, vres_H]
    simp [BI, BT, BH]

theorem lemmaA (n p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hbig : 144 * n + 24 < p ^ 2) (k : ℕ)
    (hk : k = 1 ∨ k = 2) :
    InSpan p ((List.range p).flatMap (fun r => (dualTypeAt n p r).gens)) (colVec n p k) := by
  have hk1 : 1 ≤ k := by omega
  rw [colVec_eq]
  exact LA.total_inSpan (LA.Zd n) (LA.Pd n p) (LA.hyp_dual n hp5 hbig) (LA.huniq_dual n hp5) k hk1
    (dualTypeAt n p) (fun r hr => (LA.typ_eq n r hp5 hr).symm)

end Zeta2L2Chi3.Arith
