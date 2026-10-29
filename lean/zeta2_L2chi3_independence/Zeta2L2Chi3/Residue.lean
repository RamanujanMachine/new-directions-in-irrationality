/-
# A minimal residue calculus for real functions with simple poles

`HasRes X ρ r` means `(s - ρ) X(s) → r` as `s → ρ`, `s ≠ ρ`.
-/
import Mathlib

open Filter Topology Finset

namespace Zeta2L2Chi3

/-- `X` has residue `r` at `ρ` (simple pole or regular point). -/
def HasRes (X : ℝ → ℝ) (ρ r : ℝ) : Prop := Tendsto (fun s => (s - ρ) * X s) (𝓝[≠] ρ) (𝓝 r)

namespace HasRes

lemma unique {X : ℝ → ℝ} {ρ r r' : ℝ} (h : HasRes X ρ r) (h' : HasRes X ρ r') : r = r' :=
  tendsto_nhds_unique h h'

lemma add {X Y : ℝ → ℝ} {ρ r r' : ℝ} (h : HasRes X ρ r) (h' : HasRes Y ρ r') :
    HasRes (fun s => X s + Y s) ρ (r + r') := by
  unfold HasRes at *; simpa [mul_add] using h.add h'

lemma sub {X Y : ℝ → ℝ} {ρ r r' : ℝ} (h : HasRes X ρ r) (h' : HasRes Y ρ r') :
    HasRes (fun s => X s - Y s) ρ (r - r') := by
  unfold HasRes at *; simpa [mul_sub] using h.sub h'

lemma mul_cont {X Y : ℝ → ℝ} {ρ r : ℝ} (h : HasRes X ρ r) (hY : ContinuousAt Y ρ) :
    HasRes (fun s => X s * Y s) ρ (r * Y ρ) := by
  unfold HasRes at *
  have hY' : Tendsto Y (𝓝[≠] ρ) (𝓝 (Y ρ)) := hY.tendsto.mono_left nhdsWithin_le_nhds
  simpa [mul_assoc] using h.mul hY'

lemma cont_mul {X Y : ℝ → ℝ} {ρ r : ℝ} (h : HasRes X ρ r) (hY : ContinuousAt Y ρ) :
    HasRes (fun s => Y s * X s) ρ (Y ρ * r) := by
  have := h.mul_cont hY
  simpa [mul_comm] using this

lemma sum {ι : Type*} (t : Finset ι) {X : ι → ℝ → ℝ} {ρ : ℝ} {r : ι → ℝ}
    (h : ∀ i ∈ t, HasRes (X i) ρ (r i)) : HasRes (fun s => ∑ i ∈ t, X i s) ρ (∑ i ∈ t, r i) := by
  unfold HasRes at *
  simp only [Finset.mul_sum]
  exact tendsto_finset_sum t h

lemma congr {X Y : ℝ → ℝ} {ρ r : ℝ} (h : HasRes X ρ r) (hXY : ∀ᶠ s in 𝓝[≠] ρ, X s = Y s) :
    HasRes Y ρ r := by
  unfold HasRes at *
  exact h.congr' (hXY.mono fun s hs => by rw [hs])

lemma of_continuousAt {X : ℝ → ℝ} {ρ : ℝ} (h : ContinuousAt X ρ) : HasRes X ρ 0 := by
  unfold HasRes
  have : Tendsto (fun s => (s - ρ) * X s) (𝓝 ρ) (𝓝 ((ρ - ρ) * X ρ)) :=
    ((continuous_id.sub continuous_const).continuousAt.tendsto).mul h.tendsto
  simpa using this.mono_left nhdsWithin_le_nhds

/-- Shift: if `X` has residue `r` at `ρ - 1` then `s ↦ X(s-1)` has residue `r` at `ρ`. -/
lemma shift {X : ℝ → ℝ} {ρ r : ℝ} (h : HasRes X (ρ - 1) r) : HasRes (fun s => X (s - 1)) ρ r := by
  unfold HasRes at *
  have hmap : Tendsto (fun s : ℝ => s - 1) (𝓝[≠] ρ) (𝓝[≠] (ρ - 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((continuous_id.sub continuous_const).tendsto ρ).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h'; exact hs (by linarith)
  have := h.comp hmap
  refine this.congr fun s => ?_
  simp only [Function.comp_apply]; ring_nf

end HasRes

/-- Points outside a finite set, near (but not at) `ρ`. -/
lemma eventually_nmem_finset (S : Finset ℝ) (ρ : ℝ) : ∀ᶠ s in 𝓝[≠] ρ, s ∉ S := by
  have hcl : IsClosed ((S.erase ρ : Finset ℝ) : Set ℝ) := (S.erase ρ).finite_toSet.isClosed
  have hmem : ((S.erase ρ : Finset ℝ) : Set ℝ)ᶜ ∈ 𝓝 ρ :=
    hcl.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs hne
  simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_erase, not_and] at hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
  intro hS; exact hs hne hS

/-! ### Products of affine factors -/

lemma continuousAt_prod_affine {ι : Type*} (S : Finset ι) (a : ι → ℝ) (ρ : ℝ) :
    ContinuousAt (fun s => ∏ i ∈ S, (a i - s)) ρ :=
  (continuous_finset_prod S fun i _ => continuous_const.sub continuous_id).continuousAt

lemma prod_affine_ne {ι : Type*} (S : Finset ι) (a : ι → ℝ) (ρ : ℝ) (h : ∀ i ∈ S, a i ≠ ρ) :
    ∏ i ∈ S, (a i - ρ) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (h i hi)

/-- `1/∏ (a_i - s)` at a simple zero `a_{i₀} = ρ`. -/
lemma hasRes_inv_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℝ) (ρ : ℝ) {i₀ : ι}
    (hi₀ : i₀ ∈ S) (hρ : a i₀ = ρ) (hd : ∀ i ∈ S, i ≠ i₀ → a i ≠ ρ) :
    HasRes (fun s => 1 / ∏ i ∈ S, (a i - s)) ρ (-1 / ∏ i ∈ S.erase i₀, (a i - ρ)) := by
  have hne : ∏ i ∈ S.erase i₀, (a i - ρ) ≠ 0 :=
    prod_affine_ne _ _ _ fun i hi => hd i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  have hcont : ContinuousAt (fun s => -1 / ∏ i ∈ S.erase i₀, (a i - s)) ρ :=
    continuousAt_const.div (continuousAt_prod_affine _ _ _) hne
  unfold HasRes
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  rw [← Finset.mul_prod_erase S _ hi₀, hρ]
  have h1 : ρ - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  by_cases h2 : ∏ i ∈ S.erase i₀, (a i - s) = 0
  · rw [h2]; simp
  · field_simp; ring

lemma continuousAt_inv_prod {ι : Type*} (S : Finset ι) (a : ι → ℝ) (ρ : ℝ) (h : ∀ i ∈ S, a i ≠ ρ) :
    ContinuousAt (fun s => 1 / ∏ i ∈ S, (a i - s)) ρ :=
  continuousAt_const.div (continuousAt_prod_affine _ _ _) (prod_affine_ne _ _ _ h)

/-! ### Fractional parts never vanish -/

lemma int_add_sixth_ne (z k : ℤ) (hk : ¬ (6 : ℤ) ∣ k) : (z : ℝ) + k / 6 ≠ 0 := by
  intro h
  have h' : ((6 * z + k : ℤ) : ℝ) = 0 := by push_cast; linarith
  have := Int.cast_eq_zero.mp h'
  exact hk ⟨-z, by linarith⟩

end Zeta2L2Chi3
