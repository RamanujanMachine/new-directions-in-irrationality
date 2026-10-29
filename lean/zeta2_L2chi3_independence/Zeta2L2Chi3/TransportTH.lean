/-
# Transport of the residue rows `B_T` and `B_H` (END02, part 2)

Taking residues of `f_k = G_k - G_k(· - 1)` at all points `1/3 + z` (resp. `1/2 + z`), `z ∈ ℤ`,
and summing over the (finite) set of relevant `z`, the `G_k` contributions telescope.  This gives
`B_T(n+1) = -B_T(n) Q(n)` and `B_H(n+1) = -B_H(n) Q(n)`.
-/
import Zeta2L2Chi3.TransportId
import Zeta2L2Chi3.Residue

open Filter Topology Finset

noncomputable section

namespace Zeta2L2Chi3

/-! ### Product forms -/

lemma rf_eq_prod {K : Type*} [Field K] (c s : K) (m : ℕ) :
    rf (c - s) m = ∏ i ∈ range m, ((c + i) - s) := by
  unfold rf; exact Finset.prod_congr rfl fun i _ => by ring

/-- The three denominator blocks of `F_m`. -/
def P1 (m : ℕ) (s : ℝ) : ℝ := ∏ i ∈ range (10 * m + 2), ((2 * m + i : ℝ) - s)
def P2 (m : ℕ) (s : ℝ) : ℝ := ∏ i ∈ range (6 * m + 2), ((1 / 3 + i : ℝ) - s)
def P3 (m : ℕ) (s : ℝ) : ℝ := ∏ i ∈ range (3 * m + 2), ((2 * m + 1 / 2 + i : ℝ) - s)

lemma FDen_eq (m : ℕ) (s : ℝ) : FDen m s = P1 m s * P2 m s * P3 m s := by
  simp only [FDen, P1, P2, P3, rf_eq_prod]

lemma F_eq (m : ℕ) (s : ℝ) :
    F m s = FNum m s * ((1 / P1 m s) * (1 / P2 m s) * (1 / P3 m s)) := by
  rw [F, FDen_eq]; field_simp

lemma continuous_FNum (m : ℕ) : Continuous (fun s : ℝ => FNum m s) := by
  unfold FNum rf
  exact (continuous_finset_prod _ fun i _ => by fun_prop).mul
    (continuous_finset_prod _ fun i _ => by fun_prop)

lemma PE.continuous_val (e : PE) (x : ℝ) : Continuous (fun s : ℝ => e.val x s) := by
  induction e with
  | lit L =>
    simp only [PE.val]
    induction L with
    | nil => simp [litVal]; exact continuous_const
    | cons l ls ih => simp only [litVal]; exact continuous_const.add (continuous_id.mul ih)
  | add a b iha ihb => exact iha.add ihb
  | sub a b iha ihb => exact iha.sub ihb
  | mul a b iha ihb => exact iha.mul ihb
  | shift a ih => exact ih.comp (continuous_id.sub continuous_const)

/-! ### Fractional-part bookkeeping -/

/-- third points `1/3 + z` -/
def θT (z : ℤ) : ℝ := 1 / 3 + z
/-- half points `1/2 + z` -/
def θH (z : ℤ) : ℝ := 1 / 2 + z

lemma ne_of_sixth (a : ℝ) (z k : ℤ) (hk : ¬ (6 : ℤ) ∣ k) (h : a = z + k / 6) : a ≠ 0 := by
  rw [h]; exact int_add_sixth_ne z k hk

/-! ### Residues of `F_m` at third points -/

/-- the residue of `F_m` at `1/3 + z` -/
noncomputable def resFT (m : ℕ) (z : ℤ) : ℝ :=
  if h : 0 ≤ z ∧ z < 6 * m + 2 then resT m z.toNat else 0

lemma P1_cont (m : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / P1 m s) (θT z) := by
  refine continuousAt_inv_prod _ _ _ fun i _ => ?_
  intro h
  exact ne_of_sixth (2 * m + i - θT z) (2 * m + i - z) (-2) (by decide)
    (by simp [θT]; push_cast; ring) (by linarith)

lemma P3_cont_T (m : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / P3 m s) (θT z) := by
  refine continuousAt_inv_prod _ _ _ fun i _ => ?_
  intro h
  exact ne_of_sixth (2 * m + 1 / 2 + i - θT z) (2 * m + i - z) 1 (by decide)
    (by simp [θT]; push_cast; ring) (by linarith)

theorem hasRes_F_T (m : ℕ) (z : ℤ) : HasRes (F m) (θT z) (resFT m z) := by
  have hcF : ∀ s, F m s = (1 / P2 m s) * (FNum m s * (1 / P1 m s) * (1 / P3 m s)) := by
    intro s; rw [F_eq]; ring
  have hcont : ContinuousAt (fun s => FNum m s * (1 / P1 m s) * (1 / P3 m s)) (θT z) :=
    ((continuous_FNum m).continuousAt.mul (P1_cont m z)).mul (P3_cont_T m z)
  by_cases hz : 0 ≤ z ∧ z < 6 * m + 2
  · obtain ⟨hz0, hz1⟩ := hz
    set t := z.toNat
    have ht : (t : ℤ) = z := Int.toNat_of_nonneg hz0
    have htr : t ∈ range (6 * m + 2) := by simp only [mem_range]; omega
    have h2 := hasRes_inv_prod (range (6 * m + 2)) (fun i : ℕ => (1 / 3 + i : ℝ)) (θT z) htr
      (by simp [θT, ← ht]) (fun i _ hi h => hi (by
        simp only [θT, ← ht] at h; push_cast at h; exact_mod_cast (by linarith : (i : ℝ) = t)))
    have := (h2.mul_cont hcont).congr (Eventually.of_forall fun s => (hcF s).symm)
    convert this using 1
    simp only [resFT, dif_pos (And.intro hz0 hz1), resT]
    simp only [rf_eq_prod]
    have hθ : (tP t : ℝ) = θT z := by simp [tP, θT, ← ht]
    rw [hθ]
    simp only [P1, P3]
    have e1 : ∀ i : ℕ, (1 / 3 + (i : ℝ) - θT z) = ((1 / 3 + i : ℝ) - θT z) := fun i => rfl
    have hne1 : ∏ i ∈ range (10 * m + 2), ((2 * m + i : ℝ) - θT z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i _ h => by
        exact ne_of_sixth (2 * m + i - θT z) (2 * m + i - z) (-2) (by decide)
          (by simp [θT]; push_cast; ring) (by linarith)
    have hne3 : ∏ i ∈ range (3 * m + 2), ((2 * m + 1 / 2 + i : ℝ) - θT z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i _ h => by
        exact ne_of_sixth (2 * m + 1 / 2 + i - θT z) (2 * m + i - z) 1 (by decide)
          (by simp [θT]; push_cast; ring) (by linarith)
    have hne2 : ∏ i ∈ (range (6 * m + 2)).erase t, ((1 / 3 + i : ℝ) - θT z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i hi h => by
        have := Finset.ne_of_mem_erase hi
        simp only [θT, ← ht] at h; push_cast at h
        exact this (by exact_mod_cast (by linarith : (i : ℝ) = t))
    field_simp
    ring
  · have hcont2 : ContinuousAt (fun s => 1 / P2 m s) (θT z) := by
      refine continuousAt_inv_prod _ _ _ fun i hi h => hz ?_
      simp only [θT] at h
      have : (i : ℝ) = z := by linarith
      have : (i : ℤ) = z := by exact_mod_cast this
      simp only [mem_range] at hi
      omega
    have := HasRes.of_continuousAt (hcont2.mul hcont)
    rw [show resFT m z = 0 by simp [resFT, hz]]
    exact this.congr (Eventually.of_forall fun s => (hcF s).symm)

/-! ### Residues of `F_m` at half points -/

/-- the residue of `F_m` at `1/2 + z` -/
noncomputable def resFH (m : ℕ) (z : ℤ) : ℝ :=
  if h : 2 * m ≤ z ∧ z < 5 * m + 2 then resH m (z - 2 * m).toNat else 0

lemma P1_cont_H (m : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / P1 m s) (θH z) := by
  refine continuousAt_inv_prod _ _ _ fun i _ => ?_
  intro h
  exact ne_of_sixth (2 * m + i - θH z) (2 * m + i - z) (-3) (by decide)
    (by simp [θH]; ring) (by linarith)

lemma P2_cont_H (m : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / P2 m s) (θH z) := by
  refine continuousAt_inv_prod _ _ _ fun i _ => ?_
  intro h
  exact ne_of_sixth (1 / 3 + i - θH z) (i - z) (-1) (by decide)
    (by simp [θH]; ring) (by linarith)

theorem hasRes_F_H (m : ℕ) (z : ℤ) : HasRes (F m) (θH z) (resFH m z) := by
  have hcF : ∀ s, F m s = (1 / P3 m s) * (FNum m s * (1 / P1 m s) * (1 / P2 m s)) := by
    intro s; rw [F_eq]; ring
  have hcont : ContinuousAt (fun s => FNum m s * (1 / P1 m s) * (1 / P2 m s)) (θH z) :=
    ((continuous_FNum m).continuousAt.mul (P1_cont_H m z)).mul (P2_cont_H m z)
  by_cases hz : 2 * m ≤ z ∧ z < 5 * m + 2
  · obtain ⟨hz0, hz1⟩ := hz
    set t := (z - 2 * m).toNat
    have ht : (t : ℤ) = z - 2 * m := Int.toNat_of_nonneg (by omega)
    have htr : t ∈ range (3 * m + 2) := by simp only [mem_range]; omega
    have h2 := hasRes_inv_prod (range (3 * m + 2)) (fun i : ℕ => (2 * m + 1 / 2 + i : ℝ)) (θH z) htr
      (by simp only [θH]; have : (t : ℝ) = z - 2 * m := by exact_mod_cast ht
          rw [this]; ring)
      (fun i _ hi h => hi (by
        simp only [θH] at h
        have h' : (t : ℝ) = z - 2 * m := by exact_mod_cast ht
        exact_mod_cast (by linarith : (i : ℝ) = t)))
    have := (h2.mul_cont hcont).congr (Eventually.of_forall fun s => (hcF s).symm)
    convert this using 1
    simp only [resFH, dif_pos (And.intro hz0 hz1), resH]
    simp only [rf_eq_prod]
    have hθ : (hP m t : ℝ) = θH z := by
      have h' : (t : ℝ) = z - 2 * m := by exact_mod_cast ht
      simp only [hP, θH, h']; ring
    rw [hθ]
    simp only [P1, P2]
    have hne1 : ∏ i ∈ range (10 * m + 2), ((2 * m + i : ℝ) - θH z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i _ h => by
        exact ne_of_sixth (2 * m + i - θH z) (2 * m + i - z) (-3) (by decide)
          (by simp [θH]; ring) (by linarith)
    have hne2 : ∏ i ∈ range (6 * m + 2), ((1 / 3 + i : ℝ) - θH z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i _ h => by
        exact ne_of_sixth (1 / 3 + i - θH z) (i - z) (-1) (by decide)
          (by simp [θH]; ring) (by linarith)
    have hne3 : ∏ i ∈ (range (3 * m + 2)).erase t, ((2 * m + 1 / 2 + i : ℝ) - θH z) ≠ 0 :=
      prod_affine_ne _ _ _ fun i hi h => by
        have := Finset.ne_of_mem_erase hi
        simp only [θH] at h
        have h' : (t : ℝ) = z - 2 * m := by exact_mod_cast ht
        exact this (by exact_mod_cast (by linarith : (i : ℝ) = t))
    field_simp
    ring
  · have hcont3 : ContinuousAt (fun s => 1 / P3 m s) (θH z) := by
      refine continuousAt_inv_prod _ _ _ fun i hi h => hz ?_
      simp only [θH] at h
      have : (2 * m + i : ℝ) = z := by linarith
      have : (2 * m + i : ℤ) = z := by exact_mod_cast this
      simp only [mem_range] at hi
      omega
    have := HasRes.of_continuousAt (hcont3.mul hcont)
    rw [show resFH m z = 0 by simp [resFH, hz]]
    exact this.congr (Eventually.of_forall fun s => (hcF s).symm)

/-! ### The certificate quotient `G_k` near class points -/

def R12 (n : ℕ) (s : ℝ) : ℝ := ∏ i ∈ range 12, ((12 * n + 2 + i : ℝ) - s)
def R6 (n : ℕ) (s : ℝ) : ℝ := ∏ i ∈ range 6, ((6 * n + 7 / 3 + i : ℝ) - s)
def R5 (n : ℕ) (s : ℝ) : ℝ := ∏ i ∈ range 5, ((5 * n + 5 / 2 + i : ℝ) - s)

lemma rdenR_eq (n : ℕ) (s : ℝ) : rdenR (n : ℝ) s = R12 n s * R6 n s * R5 n s := rfl

/-- the continuous numerator part of `G_k` -/
def Gnum (n : ℕ) (k : Fin 3) (s : ℝ) : ℝ :=
  (Ncert k).val (n : ℝ) s / (12 * (3 * n + 1) * hornerR Data.Qden (n : ℝ))

lemma Gk_eq (n : ℕ) (k : Fin 3) (s : ℝ) :
    Gk n k s = F n s * Gnum n k s * ((1 / R12 n s) * (1 / R6 n s) * (1 / R5 n s)) := by
  simp only [Gk, Gnum, rdenR_eq]
  by_cases h : R12 n s * R6 n s * R5 n s = 0
  · rcases mul_eq_zero.1 h with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h'' <;> simp [h'']
    · simp [h']
  · field_simp

lemma Gnum_cont (n : ℕ) (k : Fin 3) (ρ : ℝ) : ContinuousAt (Gnum n k) ρ :=
  ((PE.continuous_val _ _).div_const _).continuousAt

lemma F_cont_of (m : ℕ) (ρ : ℝ) (h1 : ContinuousAt (fun s => 1 / P1 m s) ρ)
    (h2 : ContinuousAt (fun s => 1 / P2 m s) ρ) (h3 : ContinuousAt (fun s => 1 / P3 m s) ρ) :
    ContinuousAt (F m) ρ := by
  have : (F m) = fun s => FNum m s * ((1 / P1 m s) * (1 / P2 m s) * (1 / P3 m s)) :=
    funext (F_eq m)
  rw [this]
  exact (continuous_FNum m).continuousAt.mul ((h1.mul h2).mul h3)

lemma R12_cont_T (n : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / R12 n s) (θT z) :=
  continuousAt_inv_prod _ _ _ fun i _ h => ne_of_sixth (12 * n + 2 + i - θT z) (12 * n + 2 + i - z)
    (-2) (by decide) (by simp [θT]; ring) (by linarith)

lemma R5_cont_T (n : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / R5 n s) (θT z) :=
  continuousAt_inv_prod _ _ _ fun i _ h => ne_of_sixth (5 * n + 5 / 2 + i - θT z) (5 * n + 2 + i - z)
    1 (by decide) (by simp [θT]; ring) (by linarith)

lemma R12_cont_H (n : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / R12 n s) (θH z) :=
  continuousAt_inv_prod _ _ _ fun i _ h => ne_of_sixth (12 * n + 2 + i - θH z) (12 * n + 2 + i - z)
    (-3) (by decide) (by simp [θH]; ring) (by linarith)

lemma R6_cont_H (n : ℕ) (z : ℤ) : ContinuousAt (fun s => 1 / R6 n s) (θH z) :=
  continuousAt_inv_prod _ _ _ fun i _ h => ne_of_sixth (6 * n + 7 / 3 + i - θH z) (6 * n + 2 + i - z)
    (-1) (by decide) (by simp [θH]; ring) (by linarith)

lemma P2_cont_T_of (m : ℕ) (z : ℤ) (hz : z < 0 ∨ 6 * m + 2 ≤ z) :
    ContinuousAt (fun s => 1 / P2 m s) (θT z) := by
  refine continuousAt_inv_prod _ _ _ fun i hi h => ?_
  simp only [θT] at h
  have : (i : ℤ) = z := by exact_mod_cast (by linarith : (i : ℝ) = z)
  simp only [mem_range] at hi; omega

lemma R6_cont_T_of (n : ℕ) (z : ℤ) (hz : z < 6 * n + 2 ∨ 6 * n + 8 ≤ z) :
    ContinuousAt (fun s => 1 / R6 n s) (θT z) := by
  refine continuousAt_inv_prod _ _ _ fun i hi h => ?_
  simp only [θT] at h
  have : (6 * n + 2 + i : ℤ) = z := by exact_mod_cast (by linarith : (6 * n + 2 + i : ℝ) = z)
  simp only [mem_range] at hi; omega

lemma P3_cont_H_of (m : ℕ) (z : ℤ) (hz : z < 2 * m ∨ 5 * m + 2 ≤ z) :
    ContinuousAt (fun s => 1 / P3 m s) (θH z) := by
  refine continuousAt_inv_prod _ _ _ fun i hi h => ?_
  simp only [θH] at h
  have : (2 * m + i : ℤ) = z := by exact_mod_cast (by linarith : (2 * m + i : ℝ) = z)
  simp only [mem_range] at hi; omega

lemma R5_cont_H_of (n : ℕ) (z : ℤ) (hz : z < 5 * n + 2 ∨ 5 * n + 7 ≤ z) :
    ContinuousAt (fun s => 1 / R5 n s) (θH z) := by
  refine continuousAt_inv_prod _ _ _ fun i hi h => ?_
  simp only [θH] at h
  have : (5 * n + 2 + i : ℤ) = z := by exact_mod_cast (by linarith : (5 * n + 2 + i : ℝ) = z)
  simp only [mem_range] at hi; omega

theorem exists_hasRes_G_T (n : ℕ) (k : Fin 3) (z : ℤ) : ∃ r, HasRes (Gk n k) (θT z) r := by
  have hG := funext (Gk_eq n k)
  by_cases h1 : 0 ≤ z ∧ z < 6 * n + 2
  · have hc : ContinuousAt (fun s => Gnum n k s * ((1 / R12 n s) * (1 / R6 n s) * (1 / R5 n s)))
        (θT z) :=
      (Gnum_cont n k _).mul (((R12_cont_T n z).mul (R6_cont_T_of n z (Or.inl h1.2))).mul
        (R5_cont_T n z))
    refine ⟨_, ((hasRes_F_T n z).mul_cont hc).congr (Eventually.of_forall fun s => ?_)⟩
    rw [hG]; ring
  by_cases h2 : 6 * n + 2 ≤ z ∧ z < 6 * n + 8
  · set t := (z - (6 * n + 2)).toNat
    have ht : (t : ℤ) = z - (6 * n + 2) := Int.toNat_of_nonneg (by omega)
    have ht' : (t : ℝ) = z - (6 * n + 2) := by exact_mod_cast ht
    have htr : t ∈ range 6 := by simp only [mem_range]; omega
    have h6 := hasRes_inv_prod (range 6) (fun i : ℕ => (6 * n + 7 / 3 + i : ℝ)) (θT z) htr
      (by simp only [θT]; rw [ht']; ring)
      (fun i _ hi h => hi (by
        simp only [θT] at h
        exact_mod_cast (by linarith : (i : ℝ) = t)))
    have hF : ContinuousAt (F n) (θT z) :=
      F_cont_of n _ (P1_cont n z) (P2_cont_T_of n z (Or.inr h2.1)) (P3_cont_T n z)
    have hc : ContinuousAt (fun s => F n s * Gnum n k s * ((1 / R12 n s) * (1 / R5 n s))) (θT z) :=
      (hF.mul (Gnum_cont n k _)).mul ((R12_cont_T n z).mul (R5_cont_T n z))
    refine ⟨_, (h6.mul_cont hc).congr (Eventually.of_forall fun s => ?_)⟩
    rw [hG]; simp only [R6]; ring
  · refine ⟨0, HasRes.of_continuousAt ?_⟩
    rw [hG]
    exact ((F_cont_of n _ (P1_cont n z) (P2_cont_T_of n z (by omega)) (P3_cont_T n z)).mul
      (Gnum_cont n k _)).mul (((R12_cont_T n z).mul (R6_cont_T_of n z (by omega))).mul
        (R5_cont_T n z))

theorem G_cont_T (n : ℕ) (k : Fin 3) (z : ℤ) (hz : z < 0 ∨ 6 * n + 8 ≤ z) :
    ContinuousAt (Gk n k) (θT z) := by
  rw [funext (Gk_eq n k)]
  exact ((F_cont_of n _ (P1_cont n z) (P2_cont_T_of n z (by omega)) (P3_cont_T n z)).mul
    (Gnum_cont n k _)).mul (((R12_cont_T n z).mul (R6_cont_T_of n z (by omega))).mul
      (R5_cont_T n z))

theorem exists_hasRes_G_H (n : ℕ) (k : Fin 3) (z : ℤ) : ∃ r, HasRes (Gk n k) (θH z) r := by
  have hG := funext (Gk_eq n k)
  by_cases h1 : 2 * n ≤ z ∧ z < 5 * n + 2
  · have hc : ContinuousAt (fun s => Gnum n k s * ((1 / R12 n s) * (1 / R6 n s) * (1 / R5 n s)))
        (θH z) :=
      (Gnum_cont n k _).mul (((R12_cont_H n z).mul (R6_cont_H n z)).mul
        (R5_cont_H_of n z (Or.inl h1.2)))
    refine ⟨_, ((hasRes_F_H n z).mul_cont hc).congr (Eventually.of_forall fun s => ?_)⟩
    rw [hG]; ring
  by_cases h2 : 5 * n + 2 ≤ z ∧ z < 5 * n + 7
  · set t := (z - (5 * n + 2)).toNat
    have ht : (t : ℤ) = z - (5 * n + 2) := Int.toNat_of_nonneg (by omega)
    have ht' : (t : ℝ) = z - (5 * n + 2) := by exact_mod_cast ht
    have htr : t ∈ range 5 := by simp only [mem_range]; omega
    have h5 := hasRes_inv_prod (range 5) (fun i : ℕ => (5 * n + 5 / 2 + i : ℝ)) (θH z) htr
      (by simp only [θH]; rw [ht']; ring)
      (fun i _ hi h => hi (by
        simp only [θH] at h
        exact_mod_cast (by linarith : (i : ℝ) = t)))
    have hF : ContinuousAt (F n) (θH z) :=
      F_cont_of n _ (P1_cont_H n z) (P2_cont_H n z) (P3_cont_H_of n z (Or.inr h2.1))
    have hc : ContinuousAt (fun s => F n s * Gnum n k s * ((1 / R12 n s) * (1 / R6 n s))) (θH z) :=
      (hF.mul (Gnum_cont n k _)).mul ((R12_cont_H n z).mul (R6_cont_H n z))
    refine ⟨_, (h5.mul_cont hc).congr (Eventually.of_forall fun s => ?_)⟩
    rw [hG]; simp only [R5]; ring
  · refine ⟨0, HasRes.of_continuousAt ?_⟩
    rw [hG]
    exact ((F_cont_of n _ (P1_cont_H n z) (P2_cont_H n z) (P3_cont_H_of n z (by omega))).mul
      (Gnum_cont n k _)).mul (((R12_cont_H n z).mul (R6_cont_H n z)).mul
        (R5_cont_H_of n z (by omega)))

theorem G_cont_H (n : ℕ) (k : Fin 3) (z : ℤ) (hz : z < 2 * n ∨ 5 * n + 7 ≤ z) :
    ContinuousAt (Gk n k) (θH z) := by
  rw [funext (Gk_eq n k)]
  exact ((F_cont_of n _ (P1_cont_H n z) (P2_cont_H n z) (P3_cont_H_of n z (by omega))).mul
    (Gnum_cont n k _)).mul (((R12_cont_H n z).mul (R6_cont_H n z)).mul
      (R5_cont_H_of n z (by omega)))

/-! ### The finitely many bad points -/

def ZP (n : ℕ) : Finset ℝ :=
  (range (10 * n + 2)).image (fun i : ℕ => (2 * n + i : ℝ)) ∪
  (range (6 * n + 2)).image (fun i : ℕ => (1 / 3 + i : ℝ)) ∪
  (range (3 * n + 2)).image (fun i : ℕ => (2 * n + 1 / 2 + i : ℝ))

def ZR (n : ℕ) : Finset ℝ :=
  (range 12).image (fun i : ℕ => (12 * n + 2 + i : ℝ)) ∪
  (range 6).image (fun i : ℕ => (6 * n + 7 / 3 + i : ℝ)) ∪
  (range 5).image (fun i : ℕ => (5 * n + 5 / 2 + i : ℝ))

def ZA (n : ℕ) : Finset ℝ :=
  {-(10 * (n : ℝ) + 2), -(8 * (n : ℝ) + 2), 12 * (n : ℝ) + 1, 6 * (n : ℝ) + 4 / 3, 5 * (n : ℝ) + 3 / 2}

lemma prod_ne_of_nmem {ι : Type*} (S : Finset ι) (a : ι → ℝ) (s : ℝ)
    (h : s ∉ S.image a) : ∏ i ∈ S, (a i - s) ≠ 0 := by
  classical
  refine prod_affine_ne S a s fun i hi heq => h ?_
  exact Finset.mem_image.2 ⟨i, hi, heq⟩

lemma FDen_ne_of (n : ℕ) (s : ℝ) (h : s ∉ ZP n) : FDen n s ≠ 0 := by
  simp only [ZP, Finset.mem_union, not_or] at h
  rw [FDen_eq]
  exact mul_ne_zero (mul_ne_zero (prod_ne_of_nmem _ _ _ h.1.1) (prod_ne_of_nmem _ _ _ h.1.2))
    (prod_ne_of_nmem _ _ _ h.2)

lemma rdenR_ne_of (n : ℕ) (s : ℝ) (h : s ∉ ZR n) : rdenR (n : ℝ) s ≠ 0 := by
  simp only [ZR, Finset.mem_union, not_or] at h
  rw [rdenR_eq]
  exact mul_ne_zero (mul_ne_zero (prod_ne_of_nmem _ _ _ h.1.1) (prod_ne_of_nmem _ _ _ h.1.2))
    (prod_ne_of_nmem _ _ _ h.2)

lemma AR_ne_of (n : ℕ) (s : ℝ) (h : s ∉ ZA n) : AR (n : ℝ) s ≠ 0 := by
  simp only [ZA, Finset.mem_insert, Finset.mem_singleton, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [AR]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_ <;>
    intro h0 <;> [exact h1 (by linarith); exact h2 (by linarith); exact h3 (by linarith);
      exact h4 (by linarith); exact h5 (by linarith)]

def Bad (n : ℕ) : Finset ℝ :=
  ZP n ∪ (ZP n).image (· + 1) ∪ ZR n ∪ (ZR n).image (· + 1) ∪ (ZA n).image (· + 1)

lemma nmem_image_add_one {S : Finset ℝ} {s : ℝ} (h : s ∉ S.image (· + 1)) : s - 1 ∉ S := by
  intro h'; exact h (Finset.mem_image.2 ⟨s - 1, h', by ring⟩)

theorem f_eq_G_eventually (n : ℕ) (k : Fin 3) (ρ : ℝ) :
    ∀ᶠ s in 𝓝[≠] ρ, fk n k s = Gk n k s - Gk n k (s - 1) := by
  filter_upwards [eventually_nmem_finset (Bad n) ρ] with s hs
  simp only [Bad, Finset.mem_union, not_or] at hs
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hs
  exact f_eq_G_sub_G n k s (FDen_ne_of n s h1) (FDen_ne_of n _ (nmem_image_add_one h2))
    (rdenR_ne_of n s h3) (rdenR_ne_of n _ (nmem_image_add_one h4))
    (AR_ne_of n _ (nmem_image_add_one h5))

/-! ### Residues of `f_k` -/

lemma hasRes_fk (n : ℕ) (k : Fin 3) (ρ : ℝ) (r₁ r₀ : ℝ) (h1 : HasRes (F (n + 1)) ρ r₁)
    (h0 : HasRes (F n) ρ r₀) :
    HasRes (fk n k) ρ (ρ ^ (k : ℕ) * r₁ + ∑ j : Fin 3, Qk n j k * ρ ^ (j : ℕ) * r₀) := by
  have ha := h1.cont_mul (Y := fun s : ℝ => s ^ (k : ℕ)) (continuous_pow _).continuousAt
  have hb := HasRes.sum (Finset.univ : Finset (Fin 3)) (X := fun j s => Qk n j k * s ^ (j : ℕ) * F n s)
    (r := fun j => Qk n j k * ρ ^ (j : ℕ) * r₀) fun j _ => by
      have := h0.cont_mul (Y := fun s : ℝ => Qk n j k * s ^ (j : ℕ))
        (continuousAt_const.mul (continuous_pow _).continuousAt)
      simpa [mul_assoc] using this
  exact ha.add hb

/-- residues of `G_k` at third points -/
noncomputable def rGT (n : ℕ) (k : Fin 3) (z : ℤ) : ℝ := Classical.choose (exists_hasRes_G_T n k z)

lemma hasRes_rGT (n : ℕ) (k : Fin 3) (z : ℤ) : HasRes (Gk n k) (θT z) (rGT n k z) :=
  Classical.choose_spec (exists_hasRes_G_T n k z)

noncomputable def rGH (n : ℕ) (k : Fin 3) (z : ℤ) : ℝ := Classical.choose (exists_hasRes_G_H n k z)

lemma hasRes_rGH (n : ℕ) (k : Fin 3) (z : ℤ) : HasRes (Gk n k) (θH z) (rGH n k z) :=
  Classical.choose_spec (exists_hasRes_G_H n k z)

lemma θT_sub_one (z : ℤ) : θT z - 1 = θT (z - 1) := by simp [θT]; ring
lemma θH_sub_one (z : ℤ) : θH z - 1 = θH (z - 1) := by simp [θH]; ring

theorem res_identity_T (n : ℕ) (k : Fin 3) (z : ℤ) :
    (θT z) ^ (k : ℕ) * resFT (n + 1) z + ∑ j : Fin 3, Qk n j k * (θT z) ^ (j : ℕ) * resFT n z =
      rGT n k z - rGT n k (z - 1) := by
  have hf := hasRes_fk n k (θT z) _ _ (hasRes_F_T (n + 1) z) (hasRes_F_T n z)
  have hG := hasRes_rGT n k z
  have hG1 : HasRes (fun s => Gk n k (s - 1)) (θT z) (rGT n k (z - 1)) := by
    apply HasRes.shift; rw [θT_sub_one]; exact hasRes_rGT n k (z - 1)
  have := (hG.sub hG1).congr (f_eq_G_eventually n k (θT z) |>.mono fun s hs => hs.symm)
  exact hf.unique this

theorem res_identity_H (n : ℕ) (k : Fin 3) (z : ℤ) :
    (θH z) ^ (k : ℕ) * resFH (n + 1) z + ∑ j : Fin 3, Qk n j k * (θH z) ^ (j : ℕ) * resFH n z =
      rGH n k z - rGH n k (z - 1) := by
  have hf := hasRes_fk n k (θH z) _ _ (hasRes_F_H (n + 1) z) (hasRes_F_H n z)
  have hG := hasRes_rGH n k z
  have hG1 : HasRes (fun s => Gk n k (s - 1)) (θH z) (rGH n k (z - 1)) := by
    apply HasRes.shift; rw [θH_sub_one]; exact hasRes_rGH n k (z - 1)
  have := (hG.sub hG1).congr (f_eq_G_eventually n k (θH z) |>.mono fun s hs => hs.symm)
  exact hf.unique this

/-! ### Summation -/

lemma sum_resFT (m j J : ℕ) (hJ : 6 * m + 2 ≤ J) :
    ∑ t ∈ range J, (θT (t : ℤ)) ^ j * resFT m t = -(BT m j : ℝ) := by
  rw [← Finset.sum_range_add_sum_Ico _ hJ]
  have h2 : ∑ t ∈ Finset.Ico (6 * m + 2) J, (θT (t : ℤ)) ^ j * resFT m t = 0 :=
    Finset.sum_eq_zero fun t ht => by
      simp only [Finset.mem_Ico] at ht
      simp [resFT, show ¬((t : ℤ) < 6 * m + 2) by omega]
  rw [h2, add_zero, BT, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [mem_range] at ht
  have hc : (0 : ℤ) ≤ t ∧ (t : ℤ) < 6 * m + 2 := ⟨by omega, by omega⟩
  simp only [resFT, dif_pos hc, Int.toNat_natCast]
  have : θT (t : ℤ) = tP t := by simp [θT, tP]
  rw [this]; ring

lemma sum_resFH (m j J : ℕ) (hJ : 5 * m + 2 ≤ J) :
    ∑ t ∈ range J, (θH (t : ℤ)) ^ j * resFH m t = -(BH m j : ℝ) := by
  have hJ' : 2 * m ≤ 5 * m + 2 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hJ, ← Finset.sum_range_add_sum_Ico _ hJ']
  have h1 : ∑ t ∈ range (2 * m), (θH (t : ℤ)) ^ j * resFH m t = 0 :=
    Finset.sum_eq_zero fun t ht => by
      simp only [mem_range] at ht
      simp [resFH, show ¬(2 * (m : ℤ) ≤ t) by omega]
  have h3 : ∑ t ∈ Finset.Ico (5 * m + 2) J, (θH (t : ℤ)) ^ j * resFH m t = 0 :=
    Finset.sum_eq_zero fun t ht => by
      simp only [Finset.mem_Ico] at ht
      simp [resFH, show ¬((t : ℤ) < 5 * m + 2) by omega]
  rw [h1, h3, zero_add, add_zero, BH, ← Finset.sum_neg_distrib, Finset.sum_Ico_eq_sum_range]
  rw [show 5 * m + 2 - 2 * m = 3 * m + 2 by omega]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [mem_range] at ht
  have hc : 2 * (m : ℤ) ≤ ((2 * m + t : ℕ) : ℤ) ∧ ((2 * m + t : ℕ) : ℤ) < 5 * m + 2 :=
    ⟨by push_cast; omega, by push_cast; omega⟩
  simp only [resFH, dif_pos hc]
  have ht' : (((2 * m + t : ℕ) : ℤ) - 2 * m).toNat = t := by push_cast; omega
  rw [ht']
  have : θH ((2 * m + t : ℕ) : ℤ) = hP m t := by simp [θH, hP]; ring
  rw [this]; ring

/-- telescoping of the `G_k` residues -/
lemma telescope (g : ℤ → ℝ) (J : ℕ) :
    ∑ t ∈ range J, (g t - g (t - 1)) = g (J - 1) - g (-1) := by
  have := Finset.sum_range_sub (fun t : ℕ => g ((t : ℤ) - 1)) J
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.cast_zero, zero_sub] at this
  rw [← this]

theorem BT_succ_real (n : ℕ) (k : Fin 3) :
    (BT (n + 1) k : ℝ) = -∑ j : Fin 3, (BT n j : ℝ) * Qk n j k := by
  have hsum := Finset.sum_congr rfl fun (t : ℕ) (_ : t ∈ range (6 * n + 9)) =>
    res_identity_T n k (t : ℤ)
  rw [telescope (rGT n k)] at hsum
  have e1 : rGT n k ((6 * n + 9 : ℕ) - 1) = 0 :=
    (hasRes_rGT n k _).unique (HasRes.of_continuousAt (G_cont_T n k _ (Or.inr (by push_cast; omega))))
  have e2 : rGT n k (-1) = 0 :=
    (hasRes_rGT n k _).unique (HasRes.of_continuousAt (G_cont_T n k _ (Or.inl (by norm_num))))
  rw [e1, e2, sub_zero, Finset.sum_add_distrib, sum_resFT (n + 1) k _ (by omega)] at hsum
  have h2 : ∑ t ∈ range (6 * n + 9), ∑ j : Fin 3, Qk n j k * (θT (t : ℤ)) ^ (j : ℕ) * resFT n t =
      -∑ j : Fin 3, (BT n j : ℝ) * Qk n j k := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [sum_resFT n j _ (by omega)]; ring
  rw [h2] at hsum
  linarith

theorem BH_succ_real (n : ℕ) (k : Fin 3) :
    (BH (n + 1) k : ℝ) = -∑ j : Fin 3, (BH n j : ℝ) * Qk n j k := by
  have hsum := Finset.sum_congr rfl fun (t : ℕ) (_ : t ∈ range (5 * n + 8)) =>
    res_identity_H n k (t : ℤ)
  rw [telescope (rGH n k)] at hsum
  have e1 : rGH n k ((5 * n + 8 : ℕ) - 1) = 0 :=
    (hasRes_rGH n k _).unique (HasRes.of_continuousAt (G_cont_H n k _ (Or.inr (by push_cast; omega))))
  have e2 : rGH n k (-1) = 0 :=
    (hasRes_rGH n k _).unique (HasRes.of_continuousAt (G_cont_H n k _ (Or.inl (by omega))))
  rw [e1, e2, sub_zero, Finset.sum_add_distrib, sum_resFH (n + 1) k _ (by omega)] at hsum
  have h2 : ∑ t ∈ range (5 * n + 8), ∑ j : Fin 3, Qk n j k * (θH (t : ℤ)) ^ (j : ℕ) * resFH n t =
      -∑ j : Fin 3, (BH n j : ℝ) * Qk n j k := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [sum_resFH n j _ (by omega)]; ring
  rw [h2] at hsum
  linarith

end Zeta2L2Chi3
