/-
# The polynomial part of `t^j R_n` (`j ≤ 3`)

With `Z` the multiset of zeros of `R_n` and `P` the multiset of poles (with multiplicity),
`#Z = 19n+3`, `#P = 19n+4`, and `e_i` the elementary symmetric functions, the polynomial part of
`t^j R_n` is

* `q_0 = 0`, `q_1 = 1`, `q_2 = X + c₁`, `q_3 = X² + c₁ X + c₂`, where
* `c₁ = e₁(P) - e₁(Z)`, `c₂ = e₂(Z) - e₂(P) + c₁ e₁(P)`.

Proof: `X^j N - q_j D` has degree `< deg D` (top coefficients via Vieta), so
`t^j R_n(t) - q_j(t) → 0` as `t → ∞`; comparing with the partial fraction form, `fq n j - q_j` is a
polynomial tending to `0`, hence zero.
-/
import Zeta2L2Chi3.Arith.FwdExplicit

open Polynomial Finset Filter Topology

noncomputable section

namespace Zeta2L2Chi3.Arith

/-- the zeros of `R_n` -/
def ZQ (n : ℕ) : Multiset ℚ :=
  (range (10 * n + 1)).val.map (fun i : ℕ => -(2 * n + 1 + i : ℚ)) +
  (range (6 * n + 1)).val.map (fun i : ℕ => -(4 / 3 + i : ℚ)) +
  (range (3 * n + 1)).val.map (fun i : ℕ => -(2 * n + 3 / 2 + i : ℚ))

/-- the poles of `R_n`, with multiplicity -/
def PQ (n : ℕ) : Multiset ℚ :=
  (range (10 * n + 2)).val.map (fun i : ℕ => (i : ℚ)) + (range (9 * n + 2)).val.map (fun i : ℕ => (i : ℚ) - n)

def c1 (n : ℕ) : ℚ := (PQ n).esymm 1 - (ZQ n).esymm 1
def c2 (n : ℕ) : ℚ := (ZQ n).esymm 2 - (PQ n).esymm 2 + c1 n * (PQ n).esymm 1

/-- the coefficients of the polynomial part `q_j` (`j ≤ 3`) -/
def qc (n j i : ℕ) : ℚ :=
  match j, i with
  | 1, 0 => 1
  | 2, 0 => c1 n
  | 2, 1 => 1
  | 3, 0 => c2 n
  | 3, 1 => c1 n
  | 3, 2 => 1
  | _, _ => 0

/-- the polynomial part `q_j` -/
def qQ (n j : ℕ) : ℚ[X] := ∑ i ∈ range 3, Polynomial.C (qc n j i) * X ^ i

lemma card_ZQ (n : ℕ) : Multiset.card (ZQ n) = 19 * n + 3 := by
  simp [ZQ]; ring

lemma card_PQ (n : ℕ) : Multiset.card (PQ n) = 19 * n + 4 := by
  simp [PQ]; ring

lemma esymm_map_cast (s : Multiset ℚ) (k : ℕ) :
    (s.map (Rat.cast : ℚ → ℝ)).esymm k = ((s.esymm k : ℚ) : ℝ) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def]
  rw [Rat.cast_multiset_sum, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  simp [Rat.cast_multiset_prod]

/-! ### The numerator and denominator as products of linear factors -/

lemma prod_map_cast_range (m : ℕ) (f : ℕ → ℚ) :
    ((((range m).val.map f).map (Rat.cast : ℚ → ℝ)).map (fun t => X - Polynomial.C t)).prod =
      ∏ i ∈ range m, (X - Polynomial.C ((f i : ℚ) : ℝ)) := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_map, Multiset.map_map]
  rfl

lemma RNumPoly_eq (n : ℕ) :
    RNumPoly n = (((ZQ n).map (Rat.cast : ℚ → ℝ)).map (fun t => X - Polynomial.C t)).prod := by
  simp only [ZQ, Multiset.map_add, Multiset.prod_add, prod_map_cast_range, RNumPoly]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    exact prod_congr rfl fun i _ => by push_cast; simp [sub_eq_add_neg]

lemma prod_Icc_int {M : Type*} [CommMonoid M] (c d : ℤ) (m : ℕ) (hd : d = c + m - 1) (f : ℤ → M) :
    ∏ l ∈ Icc c d, f l = ∏ i ∈ range m, f (c + i) := by
  refine Finset.prod_nbij' (fun l => (l - c).toNat) (fun i => c + i) ?_ ?_ ?_ ?_ ?_
  · intro l hl; simp only [mem_Icc, mem_range] at hl ⊢; omega
  · intro i hi; simp only [mem_Icc, mem_range] at hi ⊢; omega
  · intro l hl; simp only [mem_Icc] at hl; omega
  · intro i _; simp
  · intro l hl; simp only [mem_Icc] at hl; congr 1; omega

lemma prod_KZ_pow {M : Type*} [CommMonoid M] (n : ℕ) (f : ℤ → M) :
    ∏ l ∈ KZ n, f l ^ eZ n l = (∏ i ∈ range (10 * n + 2), f i) * ∏ i ∈ range (9 * n + 2), f (i - n) := by
  classical
  have he : ∀ l ∈ KZ n, f l ^ eZ n l =
      (if l ∈ Icc (0 : ℤ) (10 * (n : ℤ) + 1) then f l else 1) * (if l ∈ Icc (-(n : ℤ)) (8 * n + 1) then f l else 1) := by
    intro l hl
    rw [mem_KZ] at hl
    simp only [eZ, mem_Icc]
    split_ifs <;> first | omega | simp [sq]
  rw [prod_congr rfl he, prod_mul_distrib, prod_ite_mem, prod_ite_mem]
  have h1 : KZ n ∩ Icc (0 : ℤ) (10 * (n : ℤ) + 1) = Icc (0 : ℤ) (10 * (n : ℤ) + 1) := by
    ext l; simp only [mem_inter, mem_KZ, mem_Icc]; omega
  have h2 : KZ n ∩ Icc (-(n : ℤ)) (8 * n + 1) = Icc (-(n : ℤ)) (8 * n + 1) := by
    ext l; simp only [mem_inter, mem_KZ, mem_Icc]; omega
  rw [h1, h2, prod_Icc_int 0 _ (10 * n + 2) (by push_cast; ring),
    prod_Icc_int (-(n : ℤ)) _ (9 * n + 2) (by push_cast; ring)]
  congr 1
  · exact prod_congr rfl fun i _ => by simp
  · exact prod_congr rfl fun i _ => by congr 1; ring

/-- the denominator polynomial -/
def Dpoly (n : ℕ) : ℝ[X] := ∏ x ∈ KF n, (X - Polynomial.C x) ^ eF n x

lemma Dpoly_eq (n : ℕ) : Dpoly n = (((PQ n).map (Rat.cast : ℚ → ℝ)).map (fun t => X - Polynomial.C t)).prod := by
  rw [Dpoly, KF, prod_image (fun _ _ _ _ h => Int.cast_injective h)]
  simp only [eF_cast]
  rw [← KZ, prod_KZ_pow n (fun l => X - Polynomial.C (l : ℝ))]
  simp only [PQ, Multiset.map_add, Multiset.prod_add, prod_map_cast_range]
  congr 1 <;> exact prod_congr rfl fun i _ => by push_cast; rfl

lemma Dpoly_eval (n : ℕ) (t : ℝ) : (Dpoly n).eval t = ∏ x ∈ KF n, (t - x) ^ eF n x := by
  simp [Dpoly, eval_prod]

/-! ### Vieta: top coefficients -/

section vieta
variable (s : Multiset ℝ)

lemma pc_top : (s.map (fun t => X - Polynomial.C t)).prod.coeff (Multiset.card s) = 1 := by
  rw [Multiset.prod_X_sub_C_coeff s le_rfl]; simp

lemma pc_one (h : 1 ≤ Multiset.card s) :
    (s.map (fun t => X - Polynomial.C t)).prod.coeff (Multiset.card s - 1) = -s.esymm 1 := by
  rw [Multiset.prod_X_sub_C_coeff s (Nat.sub_le _ _), show Multiset.card s - (Multiset.card s - 1) = 1 by omega]
  ring

lemma pc_two (h : 2 ≤ Multiset.card s) :
    (s.map (fun t => X - Polynomial.C t)).prod.coeff (Multiset.card s - 2) = s.esymm 2 := by
  rw [Multiset.prod_X_sub_C_coeff s (Nat.sub_le _ _), show Multiset.card s - (Multiset.card s - 2) = 2 by omega]
  ring

lemma pc_gt (k : ℕ) (h : Multiset.card s < k) : (s.map (fun t => X - Polynomial.C t)).prod.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  rwa [natDegree_multiset_prod_X_sub_C_eq_card]

end vieta

lemma qQ_map_coeff (n j : ℕ) (P : ℝ[X]) (i : ℕ) :
    ((qQ n j).map (algebraMap ℚ ℝ) * P).coeff i =
      ∑ l ∈ range 3, ((qc n j l : ℚ) : ℝ) * (if l ≤ i then P.coeff (i - l) else 0) := by
  simp only [qQ, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    Finset.sum_mul, finsetSum_coeff]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  rfl

theorem deg_rem_lt (n j : ℕ) (hj : j ≤ 3) :
    (X ^ j * RNumPoly n - (qQ n j).map (algebraMap ℚ ℝ) * Dpoly n).degree < (Dpoly n).degree := by
  set ZR := (ZQ n).map (Rat.cast : ℚ → ℝ)
  set PR := (PQ n).map (Rat.cast : ℚ → ℝ)
  set c := 19 * n + 3 with hc
  have hZc : Multiset.card ZR = c := by have := card_ZQ n; simp only [ZR, Multiset.card_map]; omega
  have hPc : Multiset.card PR = c + 1 := by have := card_PQ n; simp only [PR, Multiset.card_map]; omega
  have hDm : (Dpoly n).Monic := by
    rw [Dpoly_eq]; exact monic_multiset_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hDdeg : (Dpoly n).natDegree = c + 1 := by
    rw [Dpoly_eq, natDegree_multiset_prod_X_sub_C_eq_card, hPc]
  rw [degree_eq_natDegree hDm.ne_zero, hDdeg, degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_sub, coeff_X_pow_mul', qQ_map_coeff, RNumPoly_eq, Dpoly_eq]
  -- the top coefficients
  have hN0 := pc_top ZR
  have hN1 := pc_one ZR (by omega)
  have hN2 := pc_two ZR (by omega)
  have hNz := pc_gt ZR
  have hD0 := pc_top PR
  have hD1 := pc_one PR (by omega)
  have hD2 := pc_two PR (by omega)
  have hDz := pc_gt PR
  rw [hZc] at hN0 hN1 hN2 hNz
  rw [hPc] at hD0 hD1 hD2 hDz
  simp only [Nat.add_sub_cancel] at hD1 hD2
  rw [show c + 1 - 2 = c - 1 by omega] at hD2
  have e1Z : ZR.esymm 1 = (((ZQ n).esymm 1 : ℚ) : ℝ) := esymm_map_cast _ _
  have e2Z : ZR.esymm 2 = (((ZQ n).esymm 2 : ℚ) : ℝ) := esymm_map_cast _ _
  have e1P : PR.esymm 1 = (((PQ n).esymm 1 : ℚ) : ℝ) := esymm_map_cast _ _
  have e2P : PR.esymm 2 = (((PQ n).esymm 2 : ℚ) : ℝ) := esymm_map_cast _ _
  rw [e1Z] at hN1; rw [e2Z] at hN2; rw [e1P] at hD1; rw [e2P] at hD2
  have hi' : (c + 1 : ℕ) ≤ i := by exact_mod_cast hi
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [if_pos (by omega : 0 ≤ i), if_pos (by omega : 1 ≤ i), if_pos (by omega : 2 ≤ i),
    if_pos (by omega : j ≤ i)]
  interval_cases j
  · simp only [qc, Rat.cast_zero, zero_mul, add_zero]
    rw [hNz _ (by omega)]; ring
  · simp only [qc, Rat.cast_zero, Rat.cast_one, zero_mul, add_zero, one_mul, Nat.sub_zero]
    rcases (show i = c + 1 ∨ c + 1 < i by omega) with rfl | h
    · rw [Nat.add_sub_cancel, hN0, hD0]; ring
    · rw [hNz _ (by omega), hDz _ (by omega)]; ring
  · simp only [qc, Rat.cast_zero, Rat.cast_one, zero_mul, add_zero, one_mul, Nat.sub_zero, c1]
    rcases (show i = c + 1 ∨ i = c + 2 ∨ c + 2 < i by omega) with rfl | rfl | h
    · rw [show c + 1 - 2 = c - 1 by omega, Nat.add_sub_cancel, hN1, hD0, hD1]; push_cast; ring
    · rw [Nat.add_sub_cancel, show c + 2 - 1 = c + 1 by omega, hN0, hD0, hDz _ (by omega)]; ring
    · rw [hNz _ (by omega), hDz _ (by omega), hDz _ (by omega)]; ring
  · simp only [qc, Rat.cast_zero, Rat.cast_one, zero_mul, add_zero, one_mul, Nat.sub_zero, c2, c1]
    rcases (show i = c + 1 ∨ i = c + 2 ∨ i = c + 3 ∨ c + 3 < i by omega) with rfl | rfl | rfl | h
    · rw [show c + 1 - 3 = c - 2 by omega, show c + 1 - 2 = c - 1 by omega, Nat.add_sub_cancel,
        hN2, hD0, hD1, hD2]
      push_cast; ring
    · rw [show c + 2 - 3 = c - 1 by omega, show c + 2 - 2 = c by omega,
        show c + 2 - 1 = c + 1 by omega, hN1, hD0, hD1, hDz _ (by omega)]
      push_cast; ring
    · rw [Nat.add_sub_cancel, show c + 3 - 2 = c + 1 by omega, hN0, hD0, hDz _ (by omega),
        hDz _ (by omega)]
      ring
    · rw [hNz _ (by omega), hDz _ (by omega), hDz _ (by omega), hDz _ (by omega)]; ring

/-! ### Identification of `fq` -/

theorem fq_eq (n j : ℕ) (hj : j ≤ 3) : fq n j = (qQ n j).map (algebraMap ℚ ℝ) := by
  set Q := (qQ n j).map (algebraMap ℚ ℝ)
  have hdeg := deg_rem_lt n j hj
  have h1 := Polynomial.div_tendsto_atTop_zero_of_degree_lt _ _ hdeg
  have h2 : Tendsto (fun t : ℝ => ∑ x ∈ KF n, (fa n j x / (t - x) ^ 2 + fb n j x / (t - x))) atTop
      (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ x ∈ KF n, (0 + 0) by simp]
    refine tendsto_finsetSum _ fun x _ => ?_
    have hx : Tendsto (fun t : ℝ => t - x) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
    exact (tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hx)).add
      (tendsto_const_nhds.div_atTop hx)
  have key : Tendsto (fun t => (fq n j - Q).eval t) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 0 - 0 by simp]
    refine (h1.sub h2).congr' ?_
    filter_upwards [eventually_gt_atTop ((10 * n + 1 : ℕ) : ℝ)] with t ht
    have htK : t ∉ KF n := by
      intro h
      obtain ⟨l, hl, rfl⟩ := mem_image.1 h
      rw [mem_Icc] at hl
      have : (l : ℝ) ≤ 10 * n + 1 := by exact_mod_cast hl.2
      push_cast at ht
      linarith
    have hspec := fdata_spec n j t htK
    have hD : (Dpoly n).eval t ≠ 0 := by
      rw [Dpoly_eval]
      refine prod_ne_zero_iff.2 fun x hx => pow_ne_zero _ (sub_ne_zero.2 fun h => htK (h ▸ hx))
    rw [← Dpoly_eval] at hspec
    rw [eval_sub, eval_sub, show eval t (Q * Dpoly n) = eval t Q * eval t (Dpoly n) from eval_mul,
      sub_div, mul_div_cancel_right₀ _ hD, hspec, pfEval]
    ring
  rw [Polynomial.tendsto_nhds_iff] at key
  exact sub_eq_zero.1 (leadingCoeff_eq_zero.1 key.1)

end Zeta2L2Chi3.Arith
