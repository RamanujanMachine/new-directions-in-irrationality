/-
# The special state as an explicit series (ANA05, END01)

`S n k = ∑_{m ≥ 0} (d/ds)[s^k F_n(s)]_{s = -(m+1)}`.  Using the partial fraction expansion of
`s^k F_n` (all poles simple and positive, degree `≤ -2`) we prove

`S n k = B₀(n,k) + (9C/2 + 3Z) B_T(n,k) + 2Z B_H(n,k)`   (`S_eq`).

The period constants come from splitting reciprocal-square series; no independence of `C, Z` is
used.
-/
import Zeta2L2Chi3.TransportTH
import Zeta2L2Chi3.PartialFrac
import Zeta2L2Chi3.Psi
import Zeta2L2Chi3.CastRows

open Filter Topology Finset Polynomial

noncomputable section

namespace Zeta2L2Chi3

/-! ### Residues of `F_m` at integer points -/

/-- the residue of `F_m` at the integer `z` -/
def resFI (m : ℕ) (z : ℤ) : ℝ :=
  if h : 2 * m ≤ z ∧ z < 12 * m + 2 then resI m (z - 2 * m).toNat else 0

lemma P2_cont_I (m : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / P2 m s) (z : ℝ) := by
  refine continuousAt_inv_prod _ _ _ fun i _ h => ?_
  exact ne_of_sixth (1 / 3 + i - z) (i - z) 2 (by decide) (by push_cast; ring) (by linarith)

lemma P3_cont_I (m : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / P3 m s) (z : ℝ) := by
  refine continuousAt_inv_prod _ _ _ fun i _ h => ?_
  exact ne_of_sixth (2 * m + 1 / 2 + i - z) (2 * m + i - z) 3 (by decide) (by push_cast; ring) (by linarith)

theorem hasRes_F_I (m : ℕ) (z : ℤ) : HasRes (F m) (z : ℝ) (resFI m z) := by
  have hcF : ∀ s, F m s = (1 / P1 m s) * (FNum m s * (1 / P2 m s) * (1 / P3 m s)) := by
    intro s; rw [F_eq]; ring
  have hcont : ContinuousAt (fun s => FNum m s * (1 / P2 m s) * (1 / P3 m s)) (z : ℝ) :=
    ((continuous_FNum m).continuousAt.mul (P2_cont_I m z)).mul (P3_cont_I m z)
  by_cases hz : 2 * m ≤ z ∧ z < 12 * m + 2
  · obtain ⟨hz0, hz1⟩ := hz
    set t := (z - 2 * m).toNat
    have ht : (t : ℤ) = z - 2 * m := Int.toNat_of_nonneg (by omega)
    have ht' : (t : ℝ) = z - 2 * m := by exact_mod_cast ht
    have htr : t ∈ range (10 * m + 2) := by simp only [mem_range]; omega
    have h1 := hasRes_inv_prod (range (10 * m + 2)) (fun i : ℕ => (2 * m + i : ℝ)) (z : ℝ) htr
      (by simp only [ht']; ring)
      (fun i _ hi h => hi (by exact_mod_cast (by linarith : (i : ℝ) = t)))
    have := (h1.mul_cont hcont).congr (Eventually.of_forall fun s => (hcF s).symm)
    convert this using 1
    simp only [resFI, dif_pos (And.intro hz0 hz1), resI]
    simp only [rf_eq_prod]
    have hθ : (iP m t : ℝ) = z := by simp only [iP, ht']; ring
    rw [hθ]
    simp only [P2, P3]
    have hne2 : ∏ i ∈ range (6 * m + 2), ((1 / 3 + i : ℝ) - z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i _ h =>
        ne_of_sixth (1 / 3 + i - z) (i - z) 2 (by decide) (by push_cast; ring) (by linarith)
    have hne3 : ∏ i ∈ range (3 * m + 2), ((2 * m + 1 / 2 + i : ℝ) - z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i _ h =>
        ne_of_sixth (2 * m + 1 / 2 + i - z) (2 * m + i - z) 3 (by decide) (by push_cast; ring) (by linarith)
    have hne1 : ∏ i ∈ (range (10 * m + 2)).erase t, ((2 * m + i : ℝ) - z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i hi h => by
        have := Finset.ne_of_mem_erase hi
        exact this (by exact_mod_cast (by linarith : (i : ℝ) = t))
    generalize ∏ i ∈ (range (10 * m + 2)).erase t, ((2 * m + i : ℝ) - z) = A at hne1 ⊢
    generalize ∏ i ∈ range (6 * m + 2), ((1 / 3 + i : ℝ) - z) = B2 at hne2 ⊢
    generalize ∏ i ∈ range (3 * m + 2), ((2 * m + 1 / 2 + i : ℝ) - z) = B3 at hne3 ⊢
    field_simp
  · have hcont1 : ContinuousAt (fun s => 1 / P1 m s) (z : ℝ) := by
      refine continuousAt_inv_prod _ _ _ fun i hi h => hz ?_
      have : (2 * m + i : ℤ) = z := by exact_mod_cast h
      simp only [mem_range] at hi
      omega
    have := HasRes.of_continuousAt (hcont1.mul hcont)
    rw [show resFI m z = 0 by simp [resFI, hz]]
    exact this.congr (Eventually.of_forall fun s => (hcF s).symm)

/-! ### The pole set -/

def imgI (n : ℕ) : Finset ℝ := (range (10 * n + 2)).image (fun i : ℕ => (2 * n + i : ℝ))
def imgT (n : ℕ) : Finset ℝ := (range (6 * n + 2)).image (fun i : ℕ => (1 / 3 + i : ℝ))
def imgH (n : ℕ) : Finset ℝ := (range (3 * n + 2)).image (fun i : ℕ => (2 * n + 1 / 2 + i : ℝ))

/-- the poles of `F_n` -/
def Λ (n : ℕ) : Finset ℝ := imgI n ∪ imgT n ∪ imgH n

lemma injI (n : ℕ) : Set.InjOn (fun i : ℕ => (2 * n + i : ℝ)) (range (10 * n + 2)) :=
  fun a _ b _ h => by simpa using h
lemma injT : ∀ m : ℕ, Set.InjOn (fun i : ℕ => (1 / 3 + i : ℝ)) (range m) :=
  fun _ a _ b _ h => by simpa using h
lemma injH (n : ℕ) : Set.InjOn (fun i : ℕ => (2 * n + 1 / 2 + i : ℝ)) (range (3 * n + 2)) :=
  fun a _ b _ h => by simpa using h

lemma disjIT (n : ℕ) : Disjoint (imgI n) (imgT n) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx'
  exact ne_of_sixth (2 * n + i - (1 / 3 + j)) (2 * n + i - j) (-2) (by decide)
    (by push_cast; ring) (by rw [hj]; ring)

lemma disjIT_H (n : ℕ) : Disjoint (imgI n ∪ imgT n) (imgH n) := by
  rw [Finset.disjoint_union_left]
  constructor <;> rw [Finset.disjoint_left] <;> intro x hx hx' <;>
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx <;>
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx'
  · exact ne_of_sixth (2 * n + i - (2 * n + 1 / 2 + j)) (i - j) (-3) (by decide)
      (by push_cast; ring) (by rw [hj]; ring)
  · exact ne_of_sixth (1 / 3 + i - (2 * n + 1 / 2 + j)) (i - 2 * n - j) (-1) (by decide)
      (by push_cast; ring) (by rw [hj]; ring)

lemma FDen_eq_prodΛ (n : ℕ) (s : ℝ) : FDen n s = ∏ l ∈ Λ n, (l - s) := by
  rw [FDen_eq, Λ, Finset.prod_union (disjIT_H n), Finset.prod_union (disjIT n), imgI, imgT, imgH,
    Finset.prod_image (injI n), Finset.prod_image (injT _), Finset.prod_image (injH n)]
  rfl

lemma card_Λ (n : ℕ) : (Λ n).card = 19 * n + 6 := by
  rw [Λ, Finset.card_union_of_disjoint (disjIT_H n), Finset.card_union_of_disjoint (disjIT n),
    imgI, imgT, imgH, Finset.card_image_of_injOn (injI n), Finset.card_image_of_injOn (injT _),
    Finset.card_image_of_injOn (injH n)]
  simp; ring

lemma Λ_nonneg (n : ℕ) (l : ℝ) (hl : l ∈ Λ n) : 0 ≤ l := by
  simp only [Λ, imgI, imgT, imgH, Finset.mem_union, Finset.mem_image] at hl
  rcases hl with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩ <;> positivity

/-! ### The numerator as a polynomial -/

def FNumPoly (n : ℕ) : ℝ[X] :=
  (∏ i ∈ range (10 * n + 1), (X + Polynomial.C (1 + (i : ℝ)))) *
    ∏ i ∈ range (9 * n + 1), (X + Polynomial.C (1 - (n : ℝ) + i))

lemma eval_FNumPoly (n : ℕ) (s : ℝ) : (FNumPoly n).eval s = FNum n s := by
  simp only [FNumPoly, FNum, rf, eval_mul, eval_prod, eval_add, eval_X, eval_C]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => by ring

lemma natDegree_FNumPoly (n : ℕ) : (FNumPoly n).natDegree ≤ 19 * n + 2 := by
  unfold FNumPoly
  refine natDegree_mul_le.trans ?_
  have h1 : (∏ i ∈ range (10 * n + 1), (X + Polynomial.C (1 + (i : ℝ)))).natDegree ≤ 10 * n + 1 := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (natDegree_X_add_C _).le).trans ?_
    simp
  have h2 : (∏ i ∈ range (9 * n + 1), (X + Polynomial.C (1 - (n : ℝ) + i))).natDegree ≤ 9 * n + 1 := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (natDegree_X_add_C _).le).trans ?_
    simp
  omega

/-- `X^k · FNum` -/
def pk (n k : ℕ) : ℝ[X] := X ^ k * FNumPoly n

lemma eval_pk (n k : ℕ) (s : ℝ) : (pk n k).eval s = s ^ k * FNum n s := by
  simp [pk, eval_FNumPoly]

lemma natDegree_pk (n k : ℕ) (hk : k ≤ 2) : (pk n k).natDegree + 1 < (Λ n).card := by
  rw [card_Λ]
  have := natDegree_FNumPoly n
  have h : (pk n k).natDegree ≤ k + (19 * n + 2) :=
    natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le (R := ℝ) k) this)
  omega

/-- partial fraction expansion of `s^k F_n(s)` -/
theorem sF_partialFrac (n k : ℕ) (hk : k ≤ 2) (s : ℝ) (hs : s ∉ Λ n) :
    s ^ k * F n s = ∑ l ∈ Λ n, pfCoeff (Λ n) (pk n k) l / (s - l) := by
  rw [← partialFrac (Λ n) (pk n k) (by have := natDegree_pk n k hk; omega) s hs, eval_pk,
    ← FDen_eq_prodΛ, F]
  ring

/-- the partial fraction sum has residue `c_l` at `l` -/
lemma hasRes_pfsum (Λ' : Finset ℝ) (c : ℝ → ℝ) (l : ℝ) :
    HasRes (fun s => ∑ μ ∈ Λ', c μ / (s - μ)) l (if l ∈ Λ' then c l else 0) := by
  classical
  have hsplit : ∀ s, ∑ μ ∈ Λ', c μ / (s - μ) =
      (if l ∈ Λ' then c l / (s - l) else 0) + ∑ μ ∈ Λ'.erase l, c μ / (s - μ) := by
    intro s
    split_ifs with h
    · rw [← Finset.add_sum_erase _ _ h]
    · rw [Finset.erase_eq_of_notMem h, zero_add]
  have hcont : ContinuousAt (fun s => ∑ μ ∈ Λ'.erase l, c μ / (s - μ)) l := by
    show Tendsto _ _ _
    exact tendsto_finsetSum _ fun μ hμ =>
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hμ)))).tendsto
  have h2 := HasRes.of_continuousAt hcont
  split_ifs with h
  · have h1 : HasRes (fun s => c l / (s - l)) l (c l) := by
      unfold HasRes
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have : s - l ≠ 0 := sub_ne_zero.2 hs
      field_simp
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr (Eventually.of_forall fun s => by rw [hsplit s, if_pos h])
  · exact h2.congr (Eventually.of_forall fun s => by rw [hsplit s, if_neg h, zero_add])

/-! ### Identification of the partial fraction coefficients -/

lemma pfCoeff_eq_res (n k : ℕ) (hk : k ≤ 2) (l : ℝ) (hl : l ∈ Λ n) (r : ℝ)
    (hr : HasRes (F n) l r) : pfCoeff (Λ n) (pk n k) l = l ^ k * r := by
  have h1 : HasRes (fun s => s ^ k * F n s) l (l ^ k * r) :=
    hr.cont_mul (Y := fun s => s ^ k) (continuous_pow k).continuousAt
  have h2 := hasRes_pfsum (Λ n) (fun μ => pfCoeff (Λ n) (pk n k) μ) l
  rw [if_pos hl] at h2
  have h3 := h1.congr ((eventually_nmem_finset (Λ n) l).mono fun s hs => sF_partialFrac n k hk s hs)
  exact h2.unique h3

lemma pfCoeff_T (n k : ℕ) (hk : k ≤ 2) (j : ℕ) (hj : j < 6 * n + 2) :
    pfCoeff (Λ n) (pk n k) (1 / 3 + j) = (tP j : ℝ) ^ k * resT n j := by
  have hl : (1 / 3 + j : ℝ) ∈ Λ n := by
    simp only [Λ, imgT, Finset.mem_union, Finset.mem_image, mem_range]
    exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
  have hr := hasRes_F_T n (j : ℤ)
  have e : θT (j : ℤ) = 1 / 3 + j := by simp [θT]
  rw [e] at hr
  rw [pfCoeff_eq_res n k hk _ hl _ hr]
  have hc : (0 : ℤ) ≤ j ∧ (j : ℤ) < 6 * n + 2 := ⟨by omega, by omega⟩
  rw [resFT, dif_pos hc, Int.toNat_natCast]; simp [tP]

lemma pfCoeff_H (n k : ℕ) (hk : k ≤ 2) (j : ℕ) (hj : j < 3 * n + 2) :
    pfCoeff (Λ n) (pk n k) (2 * n + 1 / 2 + j) = (hP n j : ℝ) ^ k * resH n j := by
  have hl : (2 * n + 1 / 2 + j : ℝ) ∈ Λ n := by
    simp only [Λ, imgH, Finset.mem_union, Finset.mem_image, mem_range]
    exact Or.inr ⟨j, hj, rfl⟩
  have hr := hasRes_F_H n ((2 * n + j : ℕ) : ℤ)
  have e : θH ((2 * n + j : ℕ) : ℤ) = 2 * n + 1 / 2 + j := by simp [θH]; ring
  rw [e] at hr
  rw [pfCoeff_eq_res n k hk _ hl _ hr]
  have hc : 2 * (n : ℤ) ≤ ((2 * n + j : ℕ) : ℤ) ∧ ((2 * n + j : ℕ) : ℤ) < 5 * n + 2 :=
    ⟨by push_cast; omega, by push_cast; omega⟩
  have ht : (((2 * n + j : ℕ) : ℤ) - 2 * n).toNat = j := by push_cast; omega
  simp only [resFH, dif_pos hc, ht, hP]

lemma pfCoeff_I (n k : ℕ) (hk : k ≤ 2) (j : ℕ) (hj : j < 10 * n + 2) :
    pfCoeff (Λ n) (pk n k) (2 * n + j) = (iP n j : ℝ) ^ k * resI n j := by
  have hl : (2 * n + j : ℝ) ∈ Λ n := by
    simp only [Λ, imgI, Finset.mem_union, Finset.mem_image, mem_range]
    exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
  have hr := hasRes_F_I n ((2 * n + j : ℕ) : ℤ)
  have e : (((2 * n + j : ℕ) : ℤ) : ℝ) = 2 * n + j := by push_cast; ring
  rw [e] at hr
  rw [pfCoeff_eq_res n k hk _ hl _ hr]
  have hc : 2 * (n : ℤ) ≤ ((2 * n + j : ℕ) : ℤ) ∧ ((2 * n + j : ℕ) : ℤ) < 12 * n + 2 :=
    ⟨by push_cast; omega, by push_cast; omega⟩
  have ht : (((2 * n + j : ℕ) : ℤ) - 2 * n).toNat = j := by push_cast; omega
  simp only [resFI, dif_pos hc, ht, iP]

/-- sums over the pole set split into the three blocks -/
lemma sum_Λ (n : ℕ) (g : ℝ → ℝ) :
    ∑ l ∈ Λ n, g l = (∑ j ∈ range (10 * n + 2), g (2 * n + j)) +
      (∑ j ∈ range (6 * n + 2), g (1 / 3 + j)) + ∑ j ∈ range (3 * n + 2), g (2 * n + 1 / 2 + j) := by
  rw [Λ, Finset.sum_union (disjIT_H n), Finset.sum_union (disjIT n), imgI, imgT, imgH,
    Finset.sum_image (injI n), Finset.sum_image (injT _), Finset.sum_image (injH n)]

/-- `B_I = -B_T - B_H` (sum of all residues of `s^k F_n` vanishes). -/
theorem BI_eq (n k : ℕ) (hk : k ≤ 2) : (BI n k : ℝ) = -BT n k - BH n k := by
  have h := sum_pfCoeff_eq_zero (Λ n) (pk n k) (natDegree_pk n k hk)
  rw [sum_Λ] at h
  rw [Finset.sum_congr rfl fun j hj => pfCoeff_I n k hk j (mem_range.1 hj),
    Finset.sum_congr rfl fun j hj => pfCoeff_T n k hk j (mem_range.1 hj),
    Finset.sum_congr rfl fun j hj => pfCoeff_H n k hk j (mem_range.1 hj)] at h
  simp only [BI, BT, BH, neg_mul, Finset.sum_neg_distrib]
  linarith [show ∑ j ∈ range (10 * n + 2), (iP n j : ℝ) ^ k * resI n j
      = ∑ j ∈ range (10 * n + 2), resI n j * iP n j ^ k from
        Finset.sum_congr rfl fun _ _ => mul_comm _ _,
    show ∑ j ∈ range (6 * n + 2), (tP j : ℝ) ^ k * resT n j
      = ∑ j ∈ range (6 * n + 2), resT n j * tP j ^ k from Finset.sum_congr rfl fun _ _ => mul_comm _ _,
    show ∑ j ∈ range (3 * n + 2), (hP n j : ℝ) ^ k * resH n j
      = ∑ j ∈ range (3 * n + 2), resH n j * hP n j ^ k from Finset.sum_congr rfl fun _ _ => mul_comm _ _]

/-! ### The series -/

/-- the special-function state `S n k = ∑_{m≥0} (s^k F_n)'(-(m+1))` -/
def S (n k : ℕ) : ℝ := ∑' m : ℕ, deriv (fun s : ℝ => s ^ k * F n s) (-((m : ℝ) + 1))

lemma deriv_sF (n k : ℕ) (hk : k ≤ 2) (x : ℝ) (hx : x < 0) :
    deriv (fun s : ℝ => s ^ k * F n s) x =
      ∑ l ∈ Λ n, -(pfCoeff (Λ n) (pk n k) l) / (x - l) ^ 2 := by
  have hev : (fun s : ℝ => s ^ k * F n s) =ᶠ[𝓝 x]
      fun s => ∑ l ∈ Λ n, pfCoeff (Λ n) (pk n k) l / (s - l) := by
    filter_upwards [Iio_mem_nhds hx] with s hs
    refine sF_partialFrac n k hk s fun hmem => ?_
    have := Λ_nonneg n s hmem
    simp only [Set.mem_Iio] at hs; linarith
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun s => ∑ l ∈ Λ n, pfCoeff (Λ n) (pk n k) l / (s - l))
      (∑ l ∈ Λ n, -(pfCoeff (Λ n) (pk n k) l) / (x - l) ^ 2) x := by
    apply HasDerivAt.fun_sum
    intro l hl
    have hne : x - l ≠ 0 := by have := Λ_nonneg n l hl; intro h; linarith
    have := ((hasDerivAt_id x).sub_const l).inv hne
    have h2 := this.const_mul (pfCoeff (Λ n) (pk n k) l)
    convert h2 using 1
    · ext s; simp [div_eq_mul_inv]
    · simp; ring
  exact hd.deriv

lemma summable_inv_sq_shift (l : ℝ) (hl : 0 ≤ l) :
    Summable (fun m : ℕ => 1 / ((m : ℝ) + 1 + l) ^ 2) := by
  have := summable_shift_sq (1 + l) (by linarith)
  refine this.congr fun m => by ring_nf

theorem S_eq_sum (n k : ℕ) (hk : k ≤ 2) :
    S n k = ∑ l ∈ Λ n, -(pfCoeff (Λ n) (pk n k) l) * ∑' m : ℕ, 1 / ((m : ℝ) + 1 + l) ^ 2 := by
  unfold S
  have h : ∀ m : ℕ, deriv (fun s : ℝ => s ^ k * F n s) (-((m : ℝ) + 1)) =
      ∑ l ∈ Λ n, -(pfCoeff (Λ n) (pk n k) l) * (1 / ((m : ℝ) + 1 + l) ^ 2) := by
    intro m
    rw [deriv_sF n k hk _ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : (-((m : ℝ) + 1) - l) ^ 2 = ((m : ℝ) + 1 + l) ^ 2 := by ring
    rw [this]; ring
  simp_rw [h]
  rw [Summable.tsum_finsetSum fun l hl => (summable_inv_sq_shift l (Λ_nonneg n l hl)).mul_left _]
  exact Finset.sum_congr rfl fun l _ => tsum_mul_left

lemma tsum_T (j : ℕ) : ∑' m : ℕ, 1 / ((m : ℝ) + 1 + (1 / 3 + j)) ^ 2 = psiT - hwT j := by
  have hs := summable_shift_sq (1 / 3 : ℝ) (by norm_num)
  have := hs.sum_add_tsum_nat_add (j + 1)
  unfold psiT hwT
  rw [← this]
  have e : ∀ m : ℕ, 1 / (((m + (j + 1) : ℕ) : ℝ) + 1 / 3) ^ 2 = 1 / ((m : ℝ) + 1 + (1 / 3 + j)) ^ 2 :=
    fun m => by push_cast; ring_nf
  simp only [e]; ring

lemma tsum_H (n j : ℕ) :
    ∑' m : ℕ, 1 / ((m : ℝ) + 1 + (2 * n + 1 / 2 + j)) ^ 2 = psiH - hwH n j := by
  have hs := summable_shift_sq (1 / 2 : ℝ) (by norm_num)
  have := hs.sum_add_tsum_nat_add (2 * n + j + 1)
  unfold psiH hwH
  rw [← this]
  have e : ∀ m : ℕ, 1 / (((m + (2 * n + j + 1) : ℕ) : ℝ) + 1 / 2) ^ 2 =
      1 / ((m : ℝ) + 1 + (2 * n + 1 / 2 + j)) ^ 2 := fun m => by push_cast; ring_nf
  simp only [e]; ring

lemma tsum_I (n j : ℕ) : ∑' m : ℕ, 1 / ((m : ℝ) + 1 + (2 * n + j)) ^ 2 = Z - hwI n j := by
  have := summable_Z.sum_add_tsum_nat_add (2 * n + j)
  unfold hwI
  rw [show Z = ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2 from rfl, ← this]
  have e : ∀ m : ℕ, 1 / (((m + (2 * n + j) : ℕ) : ℝ) + 1) ^ 2 = 1 / ((m : ℝ) + 1 + (2 * n + j)) ^ 2 :=
    fun m => by push_cast; ring_nf
  simp only [e]; ring

/-- **The special state is an explicit linear form in `1, C, Z`.** -/
lemma block_sum (t : Finset ℕ) (k : ℕ) (x r w : ℕ → ℝ) (K : ℝ) :
    ∑ j ∈ t, -(x j ^ k * r j) * (K - w j) =
      ∑ j ∈ t, r j * w j * x j ^ k + K * ∑ j ∈ t, -r j * x j ^ k := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem S_eq (n k : ℕ) (hk : k ≤ 2) :
    S n k = B0 n k + (9 * C / 2 + 3 * Z) * BT n k + 2 * Z * BH n k := by
  rw [S_eq_sum n k hk, sum_Λ]
  have hI : ∑ j ∈ range (10 * n + 2), -(pfCoeff (Λ n) (pk n k) (2 * n + j)) *
      ∑' m : ℕ, 1 / ((m : ℝ) + 1 + (2 * n + j)) ^ 2 =
      ∑ j ∈ range (10 * n + 2), -((iP n j : ℝ) ^ k * resI n j) * (Z - hwI n j) :=
    Finset.sum_congr rfl fun j hj => by rw [pfCoeff_I n k hk j (mem_range.1 hj), tsum_I]
  have hT : ∑ j ∈ range (6 * n + 2), -(pfCoeff (Λ n) (pk n k) (1 / 3 + j)) *
      ∑' m : ℕ, 1 / ((m : ℝ) + 1 + (1 / 3 + j)) ^ 2 =
      ∑ j ∈ range (6 * n + 2), -((tP j : ℝ) ^ k * resT n j) * (psiT - hwT j) :=
    Finset.sum_congr rfl fun j hj => by rw [pfCoeff_T n k hk j (mem_range.1 hj), tsum_T]
  have hH : ∑ j ∈ range (3 * n + 2), -(pfCoeff (Λ n) (pk n k) (2 * n + 1 / 2 + j)) *
      ∑' m : ℕ, 1 / ((m : ℝ) + 1 + (2 * n + 1 / 2 + j)) ^ 2 =
      ∑ j ∈ range (3 * n + 2), -((hP n j : ℝ) ^ k * resH n j) * (psiH - hwH n j) :=
    Finset.sum_congr rfl fun j hj => by rw [pfCoeff_H n k hk j (mem_range.1 hj), tsum_H]
  rw [hI, hT, hH, block_sum, block_sum, block_sum]
  have hBI := BI_eq n k hk
  have c1 : 9 * C / 2 + 3 * Z = psiT - Z := by rw [psiT_eq]; ring
  have c2 : 2 * Z = psiH - Z := by rw [psiH_eq]; ring
  rw [c1, c2]
  simp only [BI, BT, BH, B0] at hBI ⊢
  linear_combination Z * hBI

end Zeta2L2Chi3
