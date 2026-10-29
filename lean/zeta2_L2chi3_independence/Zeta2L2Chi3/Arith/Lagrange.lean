/-
# Total residue sums of a packet kernel

For a packet type with distinct pole T-values, `Σ_b R_b b^j` is the sum of all residues of
`T^j f(T)`: it vanishes when `h + j ≤ -2` and equals `1` when `h + j = -1`.
-/
import Zeta2L2Chi3.Arith.Defs

namespace Zeta2L2Chi3.Arith

open Polynomial

private lemma zprod_monic (zs : List ℚ) :
    ((zs.map (fun a => X - C a)).prod).Monic ∧
      ((zs.map (fun a => X - C a)).prod).natDegree = zs.length := by
  induction zs with
  | nil => simp
  | cons a zs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨(monic_X_sub_C a).mul ih.1, ?_⟩
    rw [(monic_X_sub_C a).natDegree_mul ih.1, ih.2, natDegree_X_sub_C]; omega

/-- the sum `Σ_b R_b b^j` as the coefficient of `X^{m-1}` of `X^j ∏ (X - a)` -/
private lemma V3_eq_coeff (t : PType) (hnd : (t.ps.map Prod.fst).Nodup) (j : ℕ)
    (hdeg : j + t.zs.length < t.ps.length) :
    t.V j 3 = (X ^ j * (t.zs.map (fun a => X - C a)).prod).coeff (t.ps.length - 1) := by
  classical
  set L := t.ps.map Prod.fst with hL
  set s := L.toFinset with hs
  have hcard : s.card = t.ps.length := by
    rw [hs, List.toFinset_card_of_nodup hnd, hL, List.length_map]
  set P : ℚ[X] := X ^ j * (t.zs.map (fun a => X - C a)).prod with hP
  obtain ⟨hmon, hnat⟩ := zprod_monic t.zs
  have hPdeg : P.natDegree = j + t.zs.length := by
    rw [hP, (monic_X_pow j).natDegree_mul hmon, natDegree_X_pow, hnat]
  have hPlt : P.degree < s.card := by
    rw [hcard]
    exact (degree_le_natDegree).trans_lt (by rw [hPdeg]; exact_mod_cast hdeg)
  have key := Lagrange.coeff_eq_sum (s := s) (v := id) (Set.injOn_id _) hPlt
  rw [hcard] at key
  rw [key]
  simp only [PType.V, id]
  have h1 : (t.ps.map (fun q => t.R q.1 * q.1 ^ j)) = L.map (fun b => t.R b * b ^ j) := by
    rw [hL, List.map_map]; rfl
  rw [h1, ← List.sum_toFinset _ hnd]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hev : P.eval b = b ^ j * (t.zs.map (fun a => b - a)).prod := by
    rw [hP, eval_mul, eval_pow, eval_X, eval_list_prod, List.map_map]
    congr 2
    exact List.map_congr_left (fun a _ => by simp)
  rw [hev]
  have hden : ((t.ps.filter (fun q => q.1 ≠ b)).map (fun q => b - q.1)).prod =
      ∏ b' ∈ s.erase b, (b - b') := by
    have e1 : (t.ps.filter (fun q => q.1 ≠ b)).map (fun q => b - q.1) =
        (L.filter (fun x => x ≠ b)).map (fun x => b - x) := by
      rw [hL, List.filter_map, List.map_map]; rfl
    rw [e1, ← List.prod_toFinset _ (hnd.filter _), List.toFinset_filter]
    congr 1
    ext x; simp [hs, and_comm]
  simp only [PType.R]
  rw [hden]
  ring

theorem PType.V3_low (t : PType) (hnd : (t.ps.map Prod.fst).Nodup) (j : ℕ) (hj : t.h + j ≤ -2) :
    t.V j 3 = 0 := by
  have hj' : j + t.zs.length + 2 ≤ t.ps.length := by unfold PType.h at hj; omega
  rw [V3_eq_coeff t hnd j (by omega)]
  apply coeff_eq_zero_of_natDegree_lt
  obtain ⟨hmon, hnat⟩ := zprod_monic t.zs
  rw [(monic_X_pow j).natDegree_mul hmon, natDegree_X_pow, hnat]
  omega

theorem PType.V3_top (t : PType) (hnd : (t.ps.map Prod.fst).Nodup) (j : ℕ) (hj : t.h + j = -1) :
    t.V j 3 = 1 := by
  have hj' : j + t.zs.length + 1 = t.ps.length := by unfold PType.h at hj; omega
  rw [V3_eq_coeff t hnd j (by omega)]
  obtain ⟨hmon, hnat⟩ := zprod_monic t.zs
  have hm : (X ^ j * (t.zs.map (fun a => X - C a)).prod).Monic := (monic_X_pow j).mul hmon
  have hd : (X ^ j * (t.zs.map (fun a => X - C a)).prod).natDegree = t.ps.length - 1 := by
    rw [(monic_X_pow j).natDegree_mul hmon, natDegree_X_pow, hnat]; omega
  rw [← hd]
  exact hm.coeff_natDegree

end Zeta2L2Chi3.Arith
