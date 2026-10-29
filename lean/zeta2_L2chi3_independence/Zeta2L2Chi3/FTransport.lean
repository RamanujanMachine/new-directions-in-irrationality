/-
# Transport of the forward rows (FWD02)

`φ¹(n+1) = c(n)⁻¹ φ¹(n) M(n)`, `φᵀ(n+1) = c(n)⁻¹ φᵀ(n) M(n)`, `φᴴ(n+1) = c(n)⁻¹ φᴴ(n) M(n)`.

Proof outline.  With the certificate quotient `G_j` (`Gf`, file `FTransportId`),
`L_j(t) = t^j R_{n+1}(t) - c⁻¹ ∑_l M_{lj} t^l R_n(t) = G_j(t) - G_j(t-1)` off a finite set.
Both sides are written in partial-fraction form on the common pole set `SF n`; by uniqueness
(`pf_unique`) the data agree (`L_eq_delta`).  The functionals `DP`, `p_ρ^{(m)}` of a difference
`X(t) - X(t-1)` are computed in `FPfun` (`sum_da`, `pfun_delta`); shifting the start of
`p_ρ^{(m)}` (`pfun_succ`) produces boundary values of `t^j R_{n+1}`, which cancel against
values of `Ĝ_j` (the partial-fraction form of `G_j`) by evaluating the identity `L = ΔĜ` at the
boundary points (`D3`) and the vanishing of `R_n` there (`n ≥ 1`) or an explicit computation
(`n = 0`).
-/
import Zeta2L2Chi3.FTransportId
import Zeta2L2Chi3.FPfun

open Polynomial Finset

noncomputable section

namespace Zeta2L2Chi3

/-! ### Partial-fraction data of `G_j` -/

def NGpoly (n : ℕ) (j : Fin 4) : ℝ[X] :=
  Polynomial.C (κF n) * RNumPoly n * (FNcert j).polyS (n : ℝ)

lemma NGpoly_eval (n : ℕ) (j : Fin 4) (t : ℝ) :
    (NGpoly n j).eval t = κF n * RNum n t * (FNcert j).val (n : ℝ) t := by
  simp [NGpoly, RNumPoly_eval, PE.eval_polyS]

lemma gdata_exists (n : ℕ) (j : Fin 4) :
    ∃ (q : ℝ[X]) (a b : ℝ → ℝ), (∀ k ∈ KG n, eG n k ≤ 1 → a k = 0) ∧
      (∀ k ∈ KG n, eG n k = 0 → b k = 0) ∧
      ∀ t ∉ KG n, (NGpoly n j).eval t / ∏ k ∈ KG n, (t - k) ^ eG n k = pfEval (KG n) q a b t :=
  pf_exists (KG n) (eG n) (fun k _ => eG_le n k) _

/-- partial-fraction data of `G_j` -/
def gq (n : ℕ) (j : Fin 4) : ℝ[X] := Classical.choose (gdata_exists n j)
def ga (n : ℕ) (j : Fin 4) : ℝ → ℝ := Classical.choose (Classical.choose_spec (gdata_exists n j))
def gb (n : ℕ) (j : Fin 4) : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (gdata_exists n j)))

lemma gdata_spec (n : ℕ) (j : Fin 4) (t : ℝ) (ht : t ∉ KG n) :
    (NGpoly n j).eval t / ∏ k ∈ KG n, (t - k) ^ eG n k =
      pfEval (KG n) (gq n j) (ga n j) (gb n j) t :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (gdata_exists n j)))).2.2 t ht

/-- `Ĝ_j`: the partial-fraction form of `G_j` -/
def GE (n : ℕ) (j : Fin 4) (t : ℝ) : ℝ := pfEval (KG n) (gq n j) (ga n j) (gb n j) t

/-- `X̂_{m,l}`: the partial-fraction form of `t^l R_m` -/
def XE (m l : ℕ) (t : ℝ) : ℝ := pfEval (KF m) (fq m l) (fa m l) (fb m l) t

lemma XE_eq (m l : ℕ) (t : ℝ) (ht : t ∉ KF m) : XE m l t = t ^ l * RNum m t / RDen m t := by
  rw [XE, ← fdata_spec m l t ht, eval_mul, eval_pow, eval_X, RNumPoly_eval, DF_eq]

lemma GE_eq (n : ℕ) (j : Fin 4) (t : ℝ) (ht : t ∉ KG n) : GE n j t = Gf n j t := by
  rw [GE, ← gdata_spec n j t ht, NGpoly_eval, DG_eq, Gf]

/-! ### Membership bookkeeping -/

lemma int_ne_half (z k : ℤ) : (z : ℝ) ≠ k + 1 / 2 := by
  intro h
  have h1 : ((2 * z : ℤ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by push_cast; linarith
  have h2 : 2 * z = 2 * k + 1 := by exact_mod_cast h1
  omega

lemma int_ne_third (z k : ℤ) : (z : ℝ) ≠ k - 1 / 3 := by
  intro h
  have h1 : ((3 * z : ℤ) : ℝ) = ((3 * k - 1 : ℤ) : ℝ) := by push_cast; linarith
  have h2 : 3 * z = 3 * k - 1 := by exact_mod_cast h1
  omega

lemma notMem_KF_neg (m : ℕ) (x : ℝ) (hx : x < -(m : ℝ)) : x ∉ KF m := by
  rw [KF, mem_intImage]
  rintro ⟨z, hz, -, rfl⟩
  have : ((-(m : ℤ) : ℤ) : ℝ) ≤ z := by exact_mod_cast hz
  push_cast at this
  linarith

lemma KF_mono (n : ℕ) : KF n ⊆ KF (n + 1) := by
  unfold KF
  apply image_subset_image
  intro z
  simp only [mem_Icc]
  push_cast
  omega

lemma mem_KG_iff (n : ℕ) (x : ℝ) : x ∈ KG n ↔
    (∃ z : ℤ, 0 ≤ z ∧ z ≤ 10 * n + 11 ∧ (z : ℝ) = x) ∨
    (x = -(2 * (n : ℝ) + 1) ∨ x = -(2 * (n : ℝ) + 2) ∨ x = -(2 * (n : ℝ) + 3 / 2) ∨
      x = -(2 * (n : ℝ) + 5 / 2)) ∨
    (∃ z : ℤ, -(n : ℤ) - 1 ≤ z ∧ z ≤ 8 * n + 9 ∧ (z : ℝ) = x) := by
  simp only [KG, KG1, KG2, mem_union, mem_intImage, mem_insert, mem_singleton, or_assoc]

lemma notMem_KG (n : ℕ) (x : ℝ) (hz : ∀ z : ℤ, (z : ℝ) = x → z < -(n : ℤ) - 1)
    (h1 : x ≠ -(2 * (n : ℝ) + 1)) (h2 : x ≠ -(2 * (n : ℝ) + 2))
    (h3 : x ≠ -(2 * (n : ℝ) + 3 / 2)) (h4 : x ≠ -(2 * (n : ℝ) + 5 / 2)) : x ∉ KG n := by
  rw [mem_KG_iff]
  rintro (⟨z, hz0, -, hzx⟩ | (h | h | h | h) | ⟨z, hz0, -, hzx⟩)
  · have := hz z hzx; omega
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h
  · have := hz z hzx; omega

/-- the common pole set -/
def SF (n : ℕ) : Finset ℝ := KG n ∪ (KG n).image (· + 1) ∪ KF (n + 1)

/-- the zeros of `As` -/
def EF (n : ℕ) : Finset ℝ :=
  {-(12 * (n : ℝ) + 1), -(6 * (n : ℝ) + 4 / 3), -(5 * (n : ℝ) + 3 / 2), 10 * (n : ℝ) + 2,
    8 * (n : ℝ) + 2}

lemma KG_sub_SF (n : ℕ) : KG n ⊆ SF n := fun x hx => by
  simp only [SF, mem_union]; exact Or.inl (Or.inl hx)

lemma KGimg_sub_SF (n : ℕ) : (KG n).image (· + 1) ⊆ SF n := fun x hx => by
  simp only [SF, mem_union]; exact Or.inl (Or.inr hx)

lemma KF1_sub_SF (n : ℕ) : KF (n + 1) ⊆ SF n := fun x hx => by
  simp only [SF, mem_union]; exact Or.inr hx

lemma KF_sub_SF (n : ℕ) : KF n ⊆ SF n := (KF_mono n).trans (KF1_sub_SF n)

lemma notMem_SF (n : ℕ) (t : ℝ) (ht : t ∉ SF n) :
    t ∉ KG n ∧ t - 1 ∉ KG n ∧ t ∉ KF (n + 1) ∧ t ∉ KF n := by
  refine ⟨fun h => ht (KG_sub_SF n h), fun h => ht (KGimg_sub_SF n ?_),
    fun h => ht (KF1_sub_SF n h), fun h => ht (KF_sub_SF n h)⟩
  exact mem_image.2 ⟨t - 1, h, by ring⟩

lemma KG_ne (n : ℕ) (t : ℝ) (ht : t ∉ KG n) :
    RDen n t ≠ 0 ∧ frdenAR n t ≠ 0 ∧ frdenBR n t ≠ 0 := by
  have hne : ∏ k ∈ KG n, (t - k) ^ eG n k ≠ 0 :=
    prod_ne_zero_iff.2 fun k hk => pow_ne_zero _ (sub_ne_zero.2 fun h' => ht (h' ▸ hk))
  rw [DG_eq, RDen_succ] at hne
  exact ⟨fun h => hne (by rw [h]; ring), fun h => hne (by rw [h]; ring),
    fun h => hne (by rw [h]; ring)⟩

lemma EF_ne (n : ℕ) (t : ℝ) (ht : t ∉ EF n) : fAsNR n t ≠ 0 ∧ fAsDR n t ≠ 0 := by
  simp only [EF, mem_insert, mem_singleton, not_or] at ht
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht
  refine ⟨?_, ?_⟩
  · simp only [fAsNR]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> intro h0
    · exact h1 (by linarith)
    · exact h2 (by linarith)
    · exact h3 (by linarith)
  · simp only [fAsDR]
    refine mul_ne_zero ?_ ?_ <;> intro h0
    · exact h4 (by linarith)
    · exact h5 (by linarith)

/-! ### The data of `L_j` -/

/-- the weights `c⁻¹ M_{lj}` -/
def wt (n : ℕ) (j l : Fin 4) : ℝ := (cval n)⁻¹ * Mval n l j

def qL (n : ℕ) (j : Fin 4) : ℝ[X] := fq (n + 1) j - ∑ l : Fin 4, Polynomial.C (wt n j l) * fq n l
def aL (n : ℕ) (j : Fin 4) : ℝ → ℝ := fun k =>
  ind (KF (n + 1)) (fa (n + 1) j) k - ∑ l : Fin 4, wt n j l * ind (KF n) (fa n l) k
def bL (n : ℕ) (j : Fin 4) : ℝ → ℝ := fun k =>
  ind (KF (n + 1)) (fb (n + 1) j) k - ∑ l : Fin 4, wt n j l * ind (KF n) (fb n l) k

lemma pfEval_L (n : ℕ) (j : Fin 4) (t : ℝ) :
    pfEval (SF n) (qL n j) (aL n j) (bL n j) t = XE (n + 1) j t - ∑ l : Fin 4, wt n j l * XE n l t := by
  have h := pfEval_lin (SF n) (fq (n + 1) j) (ind (KF (n + 1)) (fa (n + 1) j))
    (ind (KF (n + 1)) (fb (n + 1) j)) (wt n j) (fun l => fq n l) (fun l => ind (KF n) (fa n l))
    (fun l => ind (KF n) (fb n l)) t
  unfold qL aL bL
  rw [h, pfEval_ext _ _ (KF1_sub_SF n)]
  simp only [pfEval_ext _ _ (KF_sub_SF n), XE]

lemma pfun_L (n : ℕ) (j : Fin 4) (ρ : ℝ) (m : ℤ) :
    pfun (SF n) (qL n j) (aL n j) (bL n j) ρ m =
      pfun (KF (n + 1)) (fq (n + 1) j) (fa (n + 1) j) (fb (n + 1) j) ρ m -
        ∑ l : Fin 4, wt n j l * pfun (KF n) (fq n l) (fa n l) (fb n l) ρ m := by
  have h := pfun_lin (SF n) (fq (n + 1) j) (ind (KF (n + 1)) (fa (n + 1) j))
    (ind (KF (n + 1)) (fb (n + 1) j)) (wt n j) (fun l => fq n l) (fun l => ind (KF n) (fa n l))
    (fun l => ind (KF n) (fb n l)) ρ m
  unfold qL aL bL
  rw [h, pfun_ext _ _ (KF1_sub_SF n)]
  simp only [pfun_ext _ _ (KF_sub_SF n)]

lemma sum_aL (n : ℕ) (j : Fin 4) :
    ∑ k ∈ SF n, aL n j k = phi1 (n + 1) j - ∑ l : Fin 4, wt n j l * phi1 n l := by
  unfold aL
  rw [sum_sub_distrib, sum_ind _ _ (KF1_sub_SF n), sum_comm]
  simp only [← mul_sum, sum_ind _ _ (KF_sub_SF n), phi1]

/-! ### The identity `L = ΔĜ` on partial-fraction data -/

theorem stepA (n : ℕ) (j : Fin 4) (t : ℝ) (ht : t ∉ SF n ∪ EF n) :
    pfEval (SF n) (qL n j) (aL n j) (bL n j) t =
      pfEval (SF n) (dq (gq n j)) (da (KG n) (ga n j)) (da (KG n) (gb n j)) t := by
  rw [mem_union, not_or] at ht
  obtain ⟨hS, hE⟩ := ht
  obtain ⟨h1, h2, h3, h4⟩ := notMem_SF n t hS
  rw [pfEval_L, pfEval_delta (KG n) (SF n) (KG_sub_SF n) (KGimg_sub_SF n), XE_eq _ _ t h3]
  show _ = GE n j t - GE n j (t - 1)
  rw [GE_eq n j t h1, GE_eq n j (t - 1) h2]
  rw [sum_congr rfl fun l _ => by rw [XE_eq n l t h4]]
  obtain ⟨hD, hA, hB⟩ := KG_ne n t h1
  obtain ⟨hD1, hA1, hB1⟩ := KG_ne n (t - 1) h2
  obtain ⟨hAsN, hAsD⟩ := EF_ne n t hE
  exact fwd_tele n j t hD hD1 hA hA1 hB hB1 hAsN hAsD

theorem L_eq_delta (n : ℕ) (j : Fin 4) :
    qL n j = dq (gq n j) ∧ ∀ k ∈ SF n,
      aL n j k = da (KG n) (ga n j) k ∧ bL n j k = da (KG n) (gb n j) k :=
  pf_unique (SF n) _ _ _ _ _ _ (EF n) (fun t ht => stepA n j t ht)

/-! ### `G_j` has no half-integer poles -/

lemma aL_far (n : ℕ) (j : Fin 4) (x : ℝ) (hx : x < -((n : ℝ) + 1)) :
    aL n j x = 0 ∧ bL n j x = 0 := by
  have h1 : x ∉ KF (n + 1) := notMem_KF_neg _ _ (by push_cast; linarith)
  have h2 : x ∉ KF n := notMem_KF_neg _ _ (by linarith)
  simp [aL, bL, ind, h1, h2]

theorem IntData_G (n : ℕ) (j : Fin 4) : IntData (KG n) (ga n j) (gb n j) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hB := (L_eq_delta n j).2
  have m1 : -(2 * (n : ℝ) + 3 / 2) ∈ KG n := by rw [mem_KG_iff]; simp
  have m2 : -(2 * (n : ℝ) + 5 / 2) ∈ KG n := by rw [mem_KG_iff]; simp
  have m3 : -(2 * (n : ℝ) + 7 / 2) ∉ KG n := by
    refine notMem_KG n _ (fun z hz => absurd hz (by
      have := int_ne_half z (-(2 * n + 4)); push_cast at this; convert this using 1; ring_nf)) ?_ ?_ ?_ ?_ <;>
      intro h <;> linarith
  have e2 : -(2 * (n : ℝ) + 5 / 2) - 1 = -(2 * (n : ℝ) + 7 / 2) := by ring
  have e1 : -(2 * (n : ℝ) + 3 / 2) - 1 = -(2 * (n : ℝ) + 5 / 2) := by ring
  -- the coefficients at `-(2n+5/2)` vanish
  have z2 : ga n j (-(2 * (n : ℝ) + 5 / 2)) = 0 ∧ gb n j (-(2 * (n : ℝ) + 5 / 2)) = 0 := by
    obtain ⟨ha, hb⟩ := hB _ (KG_sub_SF n m2)
    obtain ⟨ha0, hb0⟩ := aL_far n j (-(2 * (n : ℝ) + 5 / 2)) (by linarith)
    simp only [da, ind, e2, m2, m3, ↓reduceIte, sub_zero] at ha hb
    exact ⟨by linarith, by linarith⟩
  have z1 : ga n j (-(2 * (n : ℝ) + 3 / 2)) = 0 ∧ gb n j (-(2 * (n : ℝ) + 3 / 2)) = 0 := by
    obtain ⟨ha, hb⟩ := hB _ (KG_sub_SF n m1)
    obtain ⟨ha0, hb0⟩ := aL_far n j (-(2 * (n : ℝ) + 3 / 2)) (by linarith)
    simp only [da, ind, e1, m1, m2, ↓reduceIte, z2.1, z2.2, sub_zero] at ha hb
    exact ⟨by linarith, by linarith⟩
  intro k hk
  rw [mem_KG_iff] at hk
  rcases hk with ⟨z, -, -, rfl⟩ | (rfl | rfl | rfl | rfl) | ⟨z, -, -, rfl⟩
  · left; simp
  · left
    have : -(2 * (n : ℝ) + 1) = ((-(2 * (n : ℤ) + 1) : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_intCast]
  · left
    have : -(2 * (n : ℝ) + 2) = ((-(2 * (n : ℤ) + 2) : ℤ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_intCast]
  · exact Or.inr z1
  · exact Or.inr z2
  · left; simp

/-! ### Consequences -/

theorem D1 (n : ℕ) (j : Fin 4) : ∑ k ∈ SF n, aL n j k = 0 := by
  rw [sum_congr rfl fun k hk => ((L_eq_delta n j).2 k hk).1]
  exact sum_da _ _ (KG_sub_SF n) (KGimg_sub_SF n) _

theorem D2 (n : ℕ) (j : Fin 4) (ρ : ℝ) (m : ℤ) (x : ℝ) (hx : x = -(ρ + m)) :
    pfun (SF n) (qL n j) (aL n j) (bL n j) ρ m = -GE n j x - κU (gq n j) := by
  rw [pfun_congr _ _ _ _ _ _ (L_eq_delta n j).2, (L_eq_delta n j).1,
    pfun_delta (KG n) (SF n) (KG_sub_SF n) (KGimg_sub_SF n) _ _ _ (IntData_G n j), hx]
  rfl

theorem D3 (n : ℕ) (j : Fin 4) (t : ℝ) :
    XE (n + 1) j t - ∑ l : Fin 4, wt n j l * XE n l t = GE n j t - GE n j (t - 1) := by
  rw [← pfEval_L, pfEval_congr _ _ _ _ _ _ (L_eq_delta n j).2, (L_eq_delta n j).1,
    pfEval_delta (KG n) (SF n) (KG_sub_SF n) (KGimg_sub_SF n)]
  rfl

lemma IntData_KF (m l : ℕ) : IntData (KF m) (fa m l) (fb m l) := fun k hk => by
  obtain ⟨z, -, -, rfl⟩ := mem_intImage.1 hk
  left; simp

lemma pfun_KF_succ (m l : ℕ) (ρ : ℝ) (μ μ' : ℤ) (x : ℝ) (hμ : μ' = μ + 1) (hx : x = -(ρ + μ)) :
    pfun (KF m) (fq m l) (fa m l) (fb m l) ρ μ' =
      pfun (KF m) (fq m l) (fa m l) (fb m l) ρ μ + XE m l x := by
  subst hμ hx
  exact pfun_succ _ _ _ _ (IntData_KF m l) ρ μ

/-! ### Boundary values -/

lemma RNum_zero1 (n : ℕ) (t : ℝ) (i : ℕ) (hi : i < 10 * n + 1) (h : t + 2 * n + 1 + i = 0) :
    RNum n t = 0 := by
  unfold RNum
  rw [show rf (t + 2 * n + 1) (10 * n + 1) = 0 from prod_eq_zero (mem_range.2 hi) h]
  ring

lemma RNum_zero2 (n : ℕ) (t : ℝ) (i : ℕ) (hi : i < 6 * n + 1) (h : t + 4 / 3 + i = 0) :
    RNum n t = 0 := by
  unfold RNum
  rw [show rf (t + 4 / 3) (6 * n + 1) = 0 from prod_eq_zero (mem_range.2 hi) h]
  ring

lemma RNum_zero3 (n : ℕ) (t : ℝ) (i : ℕ) (hi : i < 3 * n + 1) (h : t + 2 * n + 3 / 2 + i = 0) :
    RNum n t = 0 := by
  unfold RNum
  rw [show rf (t + 2 * n + 3 / 2) (3 * n + 1) = 0 from prod_eq_zero (mem_range.2 hi) h]
  ring

lemma XE_zero (m l : ℕ) (t : ℝ) (ht : t ∉ KF m) (hR : RNum m t = 0) : XE m l t = 0 := by
  rw [XE_eq _ _ _ ht, hR]; ring

lemma GE_zero (n : ℕ) (j : Fin 4) (t : ℝ) (ht : t ∉ KG n) (hR : RNum n t = 0) : GE n j t = 0 := by
  rw [GE_eq _ _ _ ht, Gf, hR]; ring

lemma notMem_KG_43 (n : ℕ) : (-4 / 3 : ℝ) ∉ KG n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine notMem_KG n _ (fun z hz => absurd hz (by
    have := int_ne_third z (-1); push_cast at this; convert this using 1; ring_nf)) ?_ ?_ ?_ ?_
  · intro h
    have h' : ((6 * n + 3 : ℕ) : ℝ) = 4 := by push_cast; linarith
    have : 6 * n + 3 = 4 := by exact_mod_cast h'
    omega
  all_goals intro h; linarith

lemma notMem_KG_p3 (n : ℕ) : -(2 * (n : ℝ) + 3) ∉ KG n := by
  refine notMem_KG n _ (fun z hz => ?_) ?_ ?_ ?_ ?_
  · have : ((z : ℤ) : ℝ) = ((-(2 * (n : ℤ) + 3) : ℤ) : ℝ) := by rw [hz]; push_cast; ring
    have : z = -(2 * (n : ℤ) + 3) := by exact_mod_cast this
    omega
  all_goals intro h; linarith

lemma notMem_KG_h3 (n : ℕ) : -(2 * (n : ℝ) + 7 / 2) ∉ KG n := by
  refine notMem_KG n _ (fun z hz => absurd hz (by
    have := int_ne_half z (-(2 * n + 4)); push_cast at this; convert this using 1; ring_nf)) ?_ ?_ ?_ ?_ <;>
    intro h <;> linarith

theorem Z1 (n : ℕ) (j : Fin 4) : GE n j (-4 / 3) = 0 :=
  GE_zero n j _ (notMem_KG_43 n) (RNum_zero2 n _ 0 (by omega) (by norm_num))

theorem Z2 (n l : ℕ) : XE n l (-(2 * (n : ℝ) + 1)) = 0 :=
  XE_zero n l _ (notMem_KF_neg _ _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    (RNum_zero1 n _ 0 (by omega) (by push_cast; ring))

theorem Z3 (n l : ℕ) : XE n l (-(2 * (n : ℝ) + 3 / 2)) = 0 :=
  XE_zero n l _ (notMem_KF_neg _ _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    (RNum_zero3 n _ 0 (by omega) (by push_cast; ring))

/-! ### The case `n = 0`: explicit values -/

set_option maxRecDepth 100000 in
theorem BT0_Q (j : Fin 4) :
    (FNcert j).val (0 : ℚ) (-3) * (-5) / (4 * (43589145600 * (-479001600)) * (3 / 2)) =
      hornerR Data.cden (0 : ℚ) * (hornerR (Data.Mnum 0 j) 0 + hornerR (Data.Mnum 1 j) 0 * (-2) +
        hornerR (Data.Mnum 2 j) 0 * 4 + hornerR (Data.Mnum 3 j) 0 * (-8)) * ((-1 / 3) / 36) := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 100000 in
theorem BH0_Q (j : Fin 4) :
    (FNcert j).val (0 : ℚ) (-(7 / 2)) * (-65 / 6) /
        (4 * ((412685556908625 / 4096) * (-2635284526875 / 2048)) * (15 / 2)) =
      hornerR Data.cden (0 : ℚ) * (hornerR (Data.Mnum 0 j) 0 +
        hornerR (Data.Mnum 1 j) 0 * (-(5 / 2)) + hornerR (Data.Mnum 2 j) 0 * (25 / 4) +
        hornerR (Data.Mnum 3 j) 0 * (-(125 / 8))) * ((-7 / 4) / (1225 / 16)) := by
  fin_cases j <;> decide +kernel

lemma val_cast0 (e : PE) (s : ℚ) : e.val (0 : ℝ) (s : ℝ) = ((e.val (0 : ℚ) s : ℚ) : ℝ) := by
  have := PE.val_map (Rat.castHom ℝ) e 0 s
  simp only [Rat.coe_castHom, Rat.cast_zero] at this
  exact this.symm

lemma hornerR_cast0 (l : List ℤ) : hornerR l (0 : ℝ) = ((hornerR l (0 : ℚ) : ℚ) : ℝ) := by
  have := hornerR_map (Rat.castHom ℝ) l 0
  simp only [Rat.coe_castHom, Rat.cast_zero] at this
  exact this.symm

theorem BT0 (j : Fin 4) :
    Gf 0 j (-3) = ∑ l : Fin 4, wt 0 j l * ((-2 : ℝ) ^ (l : ℕ) * RNum 0 (-2) / RDen 0 (-2)) := by
  have hq := congrArg (fun x : ℚ => (x : ℝ)) (BT0_Q j)
  push_cast at hq
  have hR3 : RNum 0 (-3) = -5 := by norm_num [RNum, rf, prod_range_succ]
  have hD13 : RDen 1 (-3) = 43589145600 * (-479001600) := by
    norm_num [RDen, rf, prod_range_succ]
  have hA3 : frdenAR 0 (-3) = 3 / 2 := by norm_num [frdenAR]
  have hR2 : RNum 0 (-2) = -1 / 3 := by norm_num [RNum, rf, prod_range_succ]
  have hD2 : RDen 0 (-2) = 36 := by norm_num [RDen, rf, prod_range_succ]
  have cN : (FNcert j).val (0 : ℝ) (-3) = (((FNcert j).val (0 : ℚ) (-3) : ℚ) : ℝ) := by
    rw [← val_cast0]; norm_num
  simp only [Gf, κF, wt, cval, Mval, Fin.sum_univ_four, Nat.cast_zero, zero_add, hR3, hD13, hA3,
    hR2, hD2, cN, hornerR_cast0, inv_div]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue, h3]
  norm_num only
  linear_combination (1 / (((hornerR (Data.cnum 0 0) (0 : ℚ) : ℚ) : ℝ) *
    ((hornerR Data.Mden (0 : ℚ) : ℚ) : ℝ))) * hq

theorem BH0 (j : Fin 4) :
    Gf 0 j (-(7 / 2)) = ∑ l : Fin 4,
      wt 0 j l * ((-(5 / 2) : ℝ) ^ (l : ℕ) * RNum 0 (-(5 / 2)) / RDen 0 (-(5 / 2))) := by
  have hq := congrArg (fun x : ℚ => (x : ℝ)) (BH0_Q j)
  push_cast at hq
  have hR3 : RNum 0 (-(7 / 2)) = -65 / 6 := by norm_num [RNum, rf, prod_range_succ]
  have hD13 : RDen 1 (-(7 / 2)) = (412685556908625 / 4096) * (-2635284526875 / 2048) := by
    norm_num [RDen, rf, prod_range_succ]
  have hA3 : frdenAR 0 (-(7 / 2)) = 15 / 2 := by norm_num [frdenAR]
  have hR2 : RNum 0 (-(5 / 2)) = -7 / 4 := by norm_num [RNum, rf, prod_range_succ]
  have hD2 : RDen 0 (-(5 / 2)) = 1225 / 16 := by norm_num [RDen, rf, prod_range_succ]
  have cN : (FNcert j).val (0 : ℝ) (-(7 / 2)) =
      (((FNcert j).val (0 : ℚ) (-(7 / 2)) : ℚ) : ℝ) := by
    rw [← val_cast0]; norm_num
  simp only [Gf, κF, wt, cval, Mval, Fin.sum_univ_four, Nat.cast_zero, zero_add, hR3, hD13, hA3,
    hR2, hD2, cN, hornerR_cast0, inv_div]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue, h3]
  norm_num only
  linear_combination (1 / (((hornerR (Data.cnum 0 0) (0 : ℚ) : ℚ) : ℝ) *
    ((hornerR Data.Mden (0 : ℚ) : ℚ) : ℝ))) * hq

/-! ### The remaining boundary identities -/

theorem bdryT (n : ℕ) (j : Fin 4) :
    GE n j (-(2 * (n : ℝ) + 3)) = ∑ l : Fin 4, wt n j l * XE n l (-(2 * (n : ℝ) + 2)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [GE_eq n j _ (notMem_KG_p3 n),
    sum_congr rfl fun l _ => by rw [XE_eq n l _ (notMem_KF_neg _ _ (by linarith))]]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_add]
    exact BT0 j
  · rw [Gf, RNum_zero1 n _ 2 (by omega) (by push_cast; ring)]
    simp only [mul_zero, zero_mul, zero_div]
    symm
    refine sum_eq_zero fun l _ => ?_
    rw [RNum_zero1 n _ 1 (by omega) (by push_cast; ring)]
    ring

theorem bdryH (n : ℕ) (j : Fin 4) :
    GE n j (-(2 * (n : ℝ) + 7 / 2)) = ∑ l : Fin 4, wt n j l * XE n l (-(2 * (n : ℝ) + 5 / 2)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [GE_eq n j _ (notMem_KG_h3 n),
    sum_congr rfl fun l _ => by rw [XE_eq n l _ (notMem_KF_neg _ _ (by linarith))]]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_add]
    exact BH0 j
  · rw [Gf, RNum_zero3 n _ 2 (by omega) (by push_cast; ring)]
    simp only [mul_zero, zero_mul, zero_div]
    symm
    refine sum_eq_zero fun l _ => ?_
    rw [RNum_zero3 n _ 1 (by omega) (by push_cast; ring)]
    ring

/-! ### The transport identities -/

lemma rhs_eq (n : ℕ) (j : Fin 4) (A B : ℕ → ℝ) :
    (cval n)⁻¹ * ∑ l : Fin 4, (A l - B l) * Mval n l j =
      ∑ l : Fin 4, wt n j l * A l - ∑ l : Fin 4, wt n j l * B l := by
  rw [← sum_sub_distrib, mul_sum]
  exact sum_congr rfl fun l _ => by simp only [wt]; ring

theorem phi1_transport (n : ℕ) (j : Fin 4) :
    phi1 (n + 1) j = (cval n)⁻¹ * ∑ l : Fin 4, phi1 n l * Mval n l j := by
  have h := sum_aL n j
  rw [D1] at h
  have hR : (cval n)⁻¹ * ∑ l : Fin 4, phi1 n l * Mval n l j = ∑ l : Fin 4, wt n j l * phi1 n l := by
    rw [mul_sum]
    exact sum_congr rfl fun l _ => by simp only [wt]; ring
  rw [hR]
  linarith

theorem phiT_transport (n : ℕ) (j : Fin 4) :
    phiT (n + 1) j = (cval n)⁻¹ * ∑ l : Fin 4, phiT n l * Mval n l j := by
  unfold phiT
  rw [rhs_eq n j (fun l => pfun (KF n) (fq n l) (fa n l) (fb n l) (1 / 3) 1)
    (fun l => pfun (KF n) (fq n l) (fa n l) (fb n l) 1 (2 * n))]
  have pA := D2 n j (1 / 3) 1 (-4 / 3) (by push_cast; ring)
  have pB := D2 n j 1 (2 * n) (-(2 * n + 1)) (by push_cast; ring)
  rw [pfun_L] at pA pB
  have h1 := pfun_KF_succ (n + 1) j 1 (2 * n + 1) (2 * ((n + 1 : ℕ) : ℤ)) (-(2 * n + 2))
    (by push_cast; ring) (by push_cast; ring)
  have h2 := pfun_KF_succ (n + 1) j 1 (2 * n) (2 * n + 1) (-(2 * n + 1)) rfl (by push_cast; ring)
  have d1 := D3 n j (-(2 * n + 1))
  rw [show -(2 * (n : ℝ) + 1) - 1 = -(2 * n + 2) by ring] at d1
  have d2 := D3 n j (-(2 * n + 2))
  rw [show -(2 * (n : ℝ) + 2) - 1 = -(2 * n + 3) by ring] at d2
  have z1 := Z1 n j
  have z2 : ∑ l : Fin 4, wt n j l * XE n l (-(2 * n + 1)) = 0 :=
    sum_eq_zero fun l _ => by rw [Z2]; ring
  have bt := bdryT n j
  linarith

theorem phiH_transport (n : ℕ) (j : Fin 4) :
    phiH (n + 1) j = (cval n)⁻¹ * ∑ l : Fin 4, phiH n l * Mval n l j := by
  unfold phiH
  rw [rhs_eq n j (fun l => pfun (KF n) (fq n l) (fa n l) (fb n l) (1 / 2) (2 * n + 1))
    (fun l => pfun (KF n) (fq n l) (fa n l) (fb n l) 1 (2 * n))]
  have pC := D2 n j (1 / 2) (2 * n + 1) (-(2 * n + 3 / 2)) (by push_cast; ring)
  have pB := D2 n j 1 (2 * n) (-(2 * n + 1)) (by push_cast; ring)
  rw [pfun_L] at pB pC
  have h1 := pfun_KF_succ (n + 1) j 1 (2 * n + 1) (2 * ((n + 1 : ℕ) : ℤ)) (-(2 * n + 2))
    (by push_cast; ring) (by push_cast; ring)
  have h2 := pfun_KF_succ (n + 1) j 1 (2 * n) (2 * n + 1) (-(2 * n + 1)) rfl (by push_cast; ring)
  have h3 := pfun_KF_succ (n + 1) j (1 / 2) (2 * n + 2) (2 * ((n + 1 : ℕ) : ℤ) + 1)
    (-(2 * n + 5 / 2)) (by push_cast; ring) (by push_cast; ring)
  have h4 := pfun_KF_succ (n + 1) j (1 / 2) (2 * n + 1) (2 * n + 2) (-(2 * n + 3 / 2))
    (by ring) (by push_cast; ring)
  have d1 := D3 n j (-(2 * n + 1))
  rw [show -(2 * (n : ℝ) + 1) - 1 = -(2 * n + 2) by ring] at d1
  have d2 := D3 n j (-(2 * n + 2))
  rw [show -(2 * (n : ℝ) + 2) - 1 = -(2 * n + 3) by ring] at d2
  have d3 := D3 n j (-(2 * n + 3 / 2))
  rw [show -(2 * (n : ℝ) + 3 / 2) - 1 = -(2 * n + 5 / 2) by ring] at d3
  have d4 := D3 n j (-(2 * n + 5 / 2))
  rw [show -(2 * (n : ℝ) + 5 / 2) - 1 = -(2 * n + 7 / 2) by ring] at d4
  have z2 : ∑ l : Fin 4, wt n j l * XE n l (-(2 * n + 1)) = 0 :=
    sum_eq_zero fun l _ => by rw [Z2]; ring
  have z3 : ∑ l : Fin 4, wt n j l * XE n l (-(2 * n + 3 / 2)) = 0 :=
    sum_eq_zero fun l _ => by rw [Z3]; ring
  have bt := bdryT n j
  have bh := bdryH n j
  linarith

/-- **Transport of the forward rows**: `φ(n+1) = c(n)⁻¹ φ(n) M(n)` for the three rows. -/
theorem phi_transport (n : ℕ) (j : Fin 4) :
    phi1 (n + 1) j = (cval n)⁻¹ * ∑ l : Fin 4, phi1 n l * Mval n l j ∧
    phiT (n + 1) j = (cval n)⁻¹ * ∑ l : Fin 4, phiT n l * Mval n l j ∧
    phiH (n + 1) j = (cval n)⁻¹ * ∑ l : Fin 4, phiH n l * Mval n l j :=
  ⟨phi1_transport n j, phiT_transport n j, phiH_transport n j⟩

end Zeta2L2Chi3
