/-
# Auxiliary lemmas for `Lattice.lean`

Soundness of descriptors, of the pivot elimination `elimDesc`, of the projection classification
`classify`, and of `projBound`, stated for abstract weighted lists of generators.
-/
import Zeta2L2Chi3.Arith.Checker
import Zeta2L2Chi3.Arith.Valuation
import Zeta2L2Chi3.Arith.Lagrange

namespace Zeta2L2Chi3.Arith

/-! ### Descriptors match vectors -/

/-- a descriptor matches a vector of `ℚ⁴` -/
def DMatch (d : Desc) (v : Fin 4 → ℚ) : Prop :=
  (∀ k q, d.co k = some q → v k = q) ∧ (d.rel = true → v 1 + v 2 = v 3)

/-- an eliminated descriptor matches (the first three coordinates of) a vector of `ℚ⁴` -/
def DMatch3 (d : Desc3) (v : Fin 4 → ℚ) : Prop :=
  (∀ (k : Fin 3) q, d.co k = some q → v k.castSucc = q) ∧ (d.rel = true → v 1 + v 2 = 0)

theorem exactDesc_match (v : Fin 4 → ℚ) : DMatch (exactDesc v) v := by
  refine ⟨fun k q h => ?_, fun h => ?_⟩
  · simp only [exactDesc, Option.some.injEq] at h; exact h
  · simp [exactDesc] at h

theorem sum_filter12 (l : List (ℚ × ℕ)) (f : ℚ × ℕ → ℚ) (hl : ∀ q ∈ l, q.2 = 1 ∨ q.2 = 2) :
    ((l.filter (fun q => q.2 = 1)).map f).sum + ((l.filter (fun q => q.2 = 2)).map f).sum =
      (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    rcases hl a List.mem_cons_self with h | h
    · simp [h]; linarith
    · simp [h]; linarith

theorem structDesc_match (t : PType) (hnd : (t.ps.map Prod.fst).Nodup)
    (hlab : ∀ q ∈ t.ps, q.2 ≤ 2) (j : ℕ) : DMatch (structDesc t j) (t.V j) := by
  refine ⟨fun k q h => ?_, fun h => ?_⟩
  · fin_cases k
    · simp only [structDesc] at h
      split_ifs at h with h0
      cases h
      simp only [PType.V, neg_eq_zero]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hx
      have h1 : q'.1 ≤ 0 := by simpa using (List.all_eq_true.1 h0 q' hq')
      have h2 : Hq q'.1 = 0 := by
        have : ⌈q'.1⌉.toNat = 0 := Int.toNat_eq_zero.2 (Int.ceil_le.2 (by simpa using h1))
        simp [Hq, this]
      simp [h2]
    · simp only [structDesc] at h
      split_ifs at h with h0
      cases h
      have : t.ps.filter (fun q => q.2 = 1) = [] := by
        rw [List.filter_eq_nil_iff]; intro a ha hc
        exact h0 (List.any_eq_true.2 ⟨a, ha, hc⟩)
      simp [PType.V, this]
    · simp only [structDesc] at h
      split_ifs at h with h0
      cases h
      have : t.ps.filter (fun q => q.2 = 2) = [] := by
        rw [List.filter_eq_nil_iff]; intro a ha hc
        exact h0 (List.any_eq_true.2 ⟨a, ha, hc⟩)
      simp [PType.V, this]
    · simp only [structDesc] at h
      split_ifs at h with h0 h1
      · cases h; exact t.V3_low hnd j h0
      · cases h; exact t.V3_top hnd j h1
  · simp only [structDesc, Bool.not_eq_true', List.any_eq_false] at h
    have hl : ∀ q ∈ t.ps, q.2 = 1 ∨ q.2 = 2 := by
      intro q hq
      have h1 := hlab q hq
      have h2 : q.2 ≠ 0 := by simpa using h q hq
      omega
    have := sum_filter12 t.ps (fun q => t.R q.1 * q.1 ^ j) hl
    simpa [PType.V] using this

/-! ### Pivot elimination -/

theorem elimDesc_match {d0 d : Desc} {g0 g : Fin 4 → ℚ} {s : ℚ} (h0 : DMatch d0 g0)
    (hd : DMatch d g) :
    DMatch3 (elimDesc d0 s d) (g - (g 3 / s) • g0) := by
  unfold elimDesc
  cases h3 : d.co 3 with
  | none =>
    refine ⟨fun k q hq => ?_, fun h => by simp at h⟩
    simp only at hq
    split at hq
    · rename_i b hb
      split_ifs at hq with hb0
      subst hb0
      simp [h0.1 _ _ hb, hd.1 _ _ hq]
    · simp at hq
  | some a =>
    have ha : g 3 = a := hd.1 _ _ h3
    simp only
    split_ifs with ha0
    · subst ha0
      refine ⟨fun k q hq => ?_, fun h => ?_⟩
      · simp [ha, hd.1 _ _ hq]
      · have := hd.2 h
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, zero_div, zero_mul, sub_zero]
        rw [this, ha]
    · refine ⟨fun k q hq => ?_, fun h => by simp at h⟩
      simp only at hq
      split at hq
      · rename_i c b hc hb
        simp only [Option.some.injEq] at hq
        subst hq
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd.1 _ _ hc, h0.1 _ _ hb, ha]
        ring
      · simp at hq

/-! ### Classification -/

/-- soundness of a classification for a projected vector `(x, y)` -/
def ClsSound : Cls → ℚ → ℚ → Prop
  | .zero, x, y => x = 0 ∧ y = 0
  | .dir u v, x, y => (u ≠ 0 ∨ v ≠ 0) ∧ x * v - y * u = 0
  | .unk, _, _ => True

theorem par_det {a b x y u v : ℚ} (hab : a ≠ 0 ∨ b ≠ 0) (h1 : x * b - y * a = 0)
    (h2 : u * b - v * a = 0) : x * v - y * u = 0 := by
  rcases hab with ha | hb
  · have : a * (x * v - y * u) = 0 := by linear_combination u * h1 - x * h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ha
    · exact h
  · have : b * (x * v - y * u) = 0 := by linear_combination v * h1 - y * h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb
    · exact h

theorem inSpan_sound {c : Cls} {x y u v : ℚ} (hc : ClsSound c x y) (hcs : c.inSpan u v = true) : x * v - y * u = 0 := by
  cases c with
  | zero => obtain ⟨rfl, rfl⟩ := hc; ring
  | dir a b =>
    obtain ⟨hab, h1⟩ := hc
    have h2 : u * b - v * a = 0 := by simpa [Cls.inSpan] using hcs
    exact par_det hab h1 h2
  | unk => simp [Cls.inSpan] at hcs

theorem classify_sound (d : Desc3) (u : Fin 4 → ℚ) (hd : DMatch3 d u) (a b : Fin 3) (th : Bool)
    (hth : th = true → a = 1 ∧ b = 2) :
    ClsSound (classify d a b th) (u a.castSucc) (u b.castSucc) := by
  have hrel : (th && d.rel) = true →
      ClsSound (.dir 1 (-1)) (u a.castSucc) (u b.castSucc) := by
    intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨rfl, rfl⟩ := hth h.1
    have := hd.2 h.2
    refine ⟨by norm_num, ?_⟩
    have e1 : (1 : Fin 3).castSucc = 1 := rfl
    have e2 : (2 : Fin 3).castSucc = 2 := rfl
    rw [e1, e2]; linarith
  unfold classify
  cases ha : d.co a with
  | none =>
    cases hb : d.co b with
    | none =>
      simp only
      split_ifs with h
      · exact hrel h
      · trivial
    | some y =>
      have hy := hd.1 _ _ hb
      simp only
      split_ifs with h0 h
      · exact ⟨by norm_num, by rw [hy, h0]; ring⟩
      · exact hrel h
      · trivial
  | some x =>
    have hx := hd.1 _ _ ha
    cases hb : d.co b with
    | none =>
      simp only
      split_ifs with h0 h
      · exact ⟨by norm_num, by rw [hx, h0]; ring⟩
      · exact hrel h
      · trivial
    | some y =>
      have hy := hd.1 _ _ hb
      simp only
      split_ifs with h0
      · exact ⟨by rw [hx, h0.1], by rw [hy, h0.2]⟩
      · refine ⟨?_, by rw [hx, hy]; ring⟩
        by_contra hc; push Not at hc; exact h0 hc

/-! ### `projBound` -/

theorem minW_le {l : List ℤ} {x : ℤ} (h : x ∈ l) : minW l ≤ x := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    show min a (minW l) ≤ x
    rcases List.mem_cons.1 h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

theorem minW_cases (l : List ℤ) : minW l = bigW ∨ minW l ∈ l := by
  induction l with
  | nil => left; rfl
  | cons a l ih =>
    show min a (minW l) = bigW ∨ min a (minW l) ∈ a :: l
    rcases min_choice a (minW l) with h | h <;> rw [h]
    · right; exact List.mem_cons_self
    · rcases ih with h' | h'
      · left; exact h'
      · right; exact List.mem_cons_of_mem _ h'

/-- `projBound` after the filtering step -/
def PB (nz : List (ℤ × Cls)) : ℤ :=
  let w1 := minW (nz.map (·.1))
  match nz.findIdx? (fun c => decide (c.1 = w1)) with
  | none => 2 * bigW
  | some idx =>
    let first : ℤ × Cls := nz[idx]!
    let rest := nz.eraseIdx idx
    match first.2 with
    | .dir u v => w1 + minW ((rest.filter (fun c => !c.2.inSpan u v)).map (·.1))
    | _ => w1 + minW (rest.map (·.1))

theorem projBound_eq (G : List (ℤ × Desc3)) (i j : Fin 3) (th : Bool) :
    projBound G i j th =
      PB ((G.map (fun g => (g.1, classify g.2 i j th))).filter (fun c => !c.2.isZero)) := rfl

theorem core_bound (R : List ℕ) (hR : R.Nodup) (w : ℕ → ℤ) (cl : ℕ → Cls) (x y : ℕ → ℚ)
    (hs : ∀ j ∈ R, ClsSound (cl j) (x j) (y j)) {i l : ℕ} (hi : i ∈ R) (hl : l ∈ R)
    (hil : i ≠ l) (hdet : x i * y l - y i * x l ≠ 0) :
    PB (R.map (fun j => (w j, cl j))) ≤ w i + w l := by
  have hdet' : x l * y i - y l * x i ≠ 0 := by intro h; apply hdet; linarith
  unfold PB
  dsimp only
  generalize hN : R.map (fun j => (w j, cl j)) = N
  have hmem : ∀ j ∈ R, minW (N.map (·.1)) ≤ w j := fun j hj =>
    minW_le (by rw [← hN]; simp only [List.map_map]; exact List.mem_map.2 ⟨j, hj, rfl⟩)
  split
  · rename_i hnone
    rw [List.findIdx?_eq_none_iff] at hnone
    have hne : ∀ j ∈ R, w j ≠ minW (N.map (·.1)) := fun j hj h => by
      have := hnone (w j, cl j) (by rw [← hN]; exact List.mem_map.2 ⟨j, hj, rfl⟩)
      simp [h] at this
    rcases minW_cases (N.map (·.1)) with hb | hb
    · have := hmem i hi; have := hmem l hl; have := hne i hi; have := hne l hl
      unfold bigW at *; omega
    · obtain ⟨c, hc, hc1⟩ := List.mem_map.1 hb
      have := hnone c hc; simp [hc1] at this
  · rename_i idx hidx
    rw [List.findIdx?_eq_some_iff_getElem] at hidx
    obtain ⟨hlt, hp, -⟩ := hidx
    have hlt' : idx < R.length := by rw [← hN] at hlt; simpa using hlt
    have hNidx : N[idx]! = (w R[idx], cl R[idx]) := by
      subst hN; simp [hlt']
    have hNidx' : N[idx] = (w R[idx], cl R[idx]) := by
      subst hN; simp
    have hwr : w R[idx] = minW (N.map (·.1)) := by
      rw [hNidx'] at hp; simpa using hp
    have hrest : N.eraseIdx idx = (R.erase R[idx]).map (fun j => (w j, cl j)) := by
      rw [← hN, List.eraseIdx_map, hR.erase_getElem]
    have hrR : R[idx] ∈ R := List.getElem_mem _
    have hmemrest : ∀ j ∈ R, j ≠ R[idx] → (w j, cl j) ∈ N.eraseIdx idx := fun j hj hjr => by
      rw [hrest]; exact List.mem_map.2 ⟨j, (hR.mem_erase_iff).2 ⟨hjr, hj⟩, rfl⟩
    generalize R[idx] = r at hNidx hwr hrR hmemrest
    have hsr := hs r hrR
    simp only [hNidx]
    split
    · rename_i u v hcl
      rw [hcl] at hsr
      obtain ⟨huv, hr0⟩ := hsr
      have key : ∀ j ∈ R, j ≠ r → (cl j).inSpan u v = false →
          minW (((N.eraseIdx idx).filter (fun c => !c.2.inSpan u v)).map (·.1)) ≤ w j :=
        fun j hj hjr hsp =>
          minW_le (List.mem_map.2 ⟨(w j, cl j), List.mem_filter.2 ⟨hmemrest j hj hjr,
            by simp [hsp]⟩, rfl⟩)
      have onl : ∀ j ∈ R, (cl j).inSpan u v = true → x j * v - y j * u = 0 :=
        fun j hj h => inSpan_sound (hs j hj) h
      by_cases hir : i = r
      · subst hir
        have hl' : (cl l).inSpan u v = false := by
          by_contra hc
          exact hdet (par_det huv hr0 (onl l hl (by simpa using hc)))
        have := key l hl (Ne.symm hil) hl'
        omega
      · by_cases hlr : l = r
        · subst hlr
          have hi' : (cl i).inSpan u v = false := by
            by_contra hc
            exact hdet' (par_det huv hr0 (onl i hi (by simpa using hc)))
          have := key i hi hir hi'
          omega
        · by_cases hi' : (cl i).inSpan u v = false
          · have := key i hi hir hi'; have := hmem l hl; omega
          · by_cases hl' : (cl l).inSpan u v = false
            · have := key l hl hlr hl'; have := hmem i hi; omega
            · exfalso
              simp only [Bool.not_eq_false] at hi' hl'
              exact hdet (par_det huv (onl i hi hi') (onl l hl hl'))
    · rename_i hcl
      have key : ∀ j ∈ R, j ≠ r → minW ((N.eraseIdx idx).map (·.1)) ≤ w j :=
        fun j hj hjr => minW_le (List.mem_map.2 ⟨(w j, cl j), hmemrest j hj hjr, rfl⟩)
      by_cases hir : i = r
      · subst hir; have := key l hl (Ne.symm hil); omega
      · have := key i hi hir; have := hmem l hl; omega

/-! ### Stage 2: minor bounds from eliminated descriptors -/

section
variable {p : ℕ} [Fact p.Prime]

theorem VGe.mul0 {x y : ℚ} (hx : VGe p 0 x) (hy : VGe p 0 y) : VGe p 0 (x * y) := by
  simpa using VGe.mul hx hy

theorem ClsSound.zero_of_isZero {c : Cls} {x y : ℚ} (h : ClsSound c x y) (hz : c.isZero = true) :
    x = 0 ∧ y = 0 := by
  cases c with
  | zero => exact h
  | dir _ _ => simp [Cls.isZero] at hz
  | unk => simp [Cls.isZero] at hz

theorem stage2 (n : ℕ) (w : ℕ → ℤ) (D : ℕ → Desc3) (u : ℕ → Fin 4 → ℚ)
    (hM : ∀ i < n, DMatch3 (D i) (u i)) (hI : ∀ i < n, ∀ k, VGe p 0 (u i k))
    (α β : ℕ → ℚ) (hα : ∀ i, VGe p 0 (α i)) (hβ : ∀ i, VGe p 0 (β i)) (c₁ c₂ : Fin 4 → ℚ)
    (hc₁ : ∀ k : Fin 3,
      c₁ k.castSucc = ∑ i ∈ Finset.range n, α i * (p : ℚ) ^ w i * u i k.castSucc)
    (hc₂ : ∀ k : Fin 3,
      c₂ k.castSucc = ∑ i ∈ Finset.range n, β i * (p : ℚ) ^ w i * u i k.castSucc)
    (a b : Fin 3) (th : Bool) (hth : th = true → a = 1 ∧ b = 2) :
    VGe p (projBound ((List.range n).map (fun i => (w i, D i))) a b th)
      (c₁ a.castSucc * c₂ b.castSucc - c₁ b.castSucc * c₂ a.castSucc) := by
  set B := projBound ((List.range n).map (fun i => (w i, D i))) a b th with hB
  have pair : ∀ i < n, ∀ l < n,
      u i a.castSucc * u l b.castSucc - u i b.castSucc * u l a.castSucc ≠ 0 → B ≤ w i + w l := by
    intro i hi l hl hdet
    set cl : ℕ → Cls := fun j => classify (D j) a b th with hcl
    have hsnd : ∀ j < n, ClsSound (cl j) (u j a.castSucc) (u j b.castSucc) :=
      fun j hj => classify_sound _ _ (hM j hj) a b th hth
    set R := (List.range n).filter (fun j => !(cl j).isZero) with hR
    have hBeq : B = PB (R.map fun j => (w j, cl j)) := by
      rw [hB, projBound_eq, List.map_map, List.filter_map]; rfl
    have hil : i ≠ l := by rintro rfl; apply hdet; ring
    have hiR : i ∈ R := by
      refine List.mem_filter.2 ⟨List.mem_range.2 hi, ?_⟩
      by_contra hc
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
      obtain ⟨h1, h2⟩ := (hsnd i hi).zero_of_isZero hc
      apply hdet; rw [h1, h2]; ring
    have hlR : l ∈ R := by
      refine List.mem_filter.2 ⟨List.mem_range.2 hl, ?_⟩
      by_contra hc
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
      obtain ⟨h1, h2⟩ := (hsnd l hl).zero_of_isZero hc
      apply hdet; rw [h1, h2]; ring
    rw [hBeq]
    exact core_bound R (List.nodup_range.filter _) w cl (fun j => u j a.castSucc)
      (fun j => u j b.castSucc)
      (fun j hj => hsnd j (List.mem_range.1 (List.mem_filter.1 hj).1)) hiR hlR hil hdet
  rw [hc₁ a, hc₂ b, hc₁ b, hc₂ a, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply VGe.finset_sum; intro i hi
  rw [← Finset.sum_sub_distrib]
  apply VGe.finset_sum; intro l hl
  have hi' := Finset.mem_range.1 hi
  have hl' := Finset.mem_range.1 hl
  have e : α i * (p : ℚ) ^ w i * u i a.castSucc * (β l * (p : ℚ) ^ w l * u l b.castSucc) -
      α i * (p : ℚ) ^ w i * u i b.castSucc * (β l * (p : ℚ) ^ w l * u l a.castSucc) =
      (α i * β l * (u i a.castSucc * u l b.castSucc - u i b.castSucc * u l a.castSucc)) *
        ((p : ℚ) ^ w i * (p : ℚ) ^ w l) := by ring
  rw [e]
  by_cases h0 : u i a.castSucc * u l b.castSucc - u i b.castSucc * u l a.castSucc = 0
  · rw [h0, mul_zero, zero_mul]; exact VGe.zero _
  · have := VGe.mul (VGe.mul0 (VGe.mul0 (hα i) (hβ l))
      (VGe.sub (VGe.mul0 (hI i hi' a.castSucc) (hI l hl' b.castSucc))
        (VGe.mul0 (hI i hi' b.castSucc) (hI l hl' a.castSucc))))
      (VGe.mul (VGe.zpow (p := p) (w i)) (VGe.zpow (p := p) (w l)))
    rw [zero_add] at this
    exact VGe.mono this (pair i hi' l hl' h0)

/-! ### Stage 1: pivot elimination -/

/-- the pivot test of `dualBoundOf` -/
def isPivD (g : ℤ × Desc) : Bool := match g.2.co 3 with
  | some s => decide (g.1 = 0 ∧ (s = 1 ∨ s = -1))
  | none => false

/-- the pivot index of `dualBoundOf` -/
def pidxOf (G : List (ℤ × Desc)) : Option ℕ :=
  match G.findIdx? (fun g => isPivD g && (List.finRange 4).all (fun k => (g.2.co k).isSome)) with
  | some i => some i
  | none => G.findIdx? isPivD

/-- the eliminated descriptors of `dualBoundOf` -/
def G3Of (G : List (ℤ × Desc)) : List (ℤ × Desc3) :=
  match pidxOf G with
  | some pidx =>
    let piv := G[pidx]!
    let s := (piv.2.co 3).getD 1
    G.mapIdx (fun i g => (g.1, if i = pidx then zeroDesc3 else elimDesc piv.2 s g.2))
  | none => G.map (fun g => (g.1, ⟨fun k => g.2.co k.castSucc, false⟩))

/-- the final combination of `dualBoundOf` -/
def bound3 (G3 : List (ℤ × Desc3)) : ℤ :=
  min (projBound G3 1 2 true) (min (projBound G3 0 1 false - 2) (projBound G3 0 2 false - 2))

theorem dualBoundOf_eq (Ts : List PType) (ex : ℕ → PType → Bool) :
    dualBoundOf Ts ex =
      bound3 (G3Of ((Ts.zipIdx).flatMap (fun ti => ti.1.descs (ex ti.2 ti.1)))) := rfl

theorem pidxOf_spec {G : List (ℤ × Desc)} {i : ℕ} (h : pidxOf G = some i) :
    ∃ hi : i < G.length, isPivD G[i] = true := by
  unfold pidxOf at h
  split at h
  · rename_i j hj
    cases h
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
    simp only [Bool.and_eq_true] at hp
    exact ⟨hlt, hp.1⟩
  · obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
    exact ⟨hlt, hp⟩

theorem stage1 (n : ℕ) (w : ℕ → ℤ) (v : ℕ → Fin 4 → ℚ) (d : ℕ → Desc)
    (hM : ∀ i < n, DMatch (d i) (v i)) (hI : ∀ i < n, ∀ k, VGe p 0 (v i k)) :
    ∃ D : ℕ → Desc3, ∃ u : ℕ → Fin 4 → ℚ,
      G3Of ((List.range n).map (fun i => (w i, d i))) = (List.range n).map (fun i => (w i, D i)) ∧
      (∀ i < n, DMatch3 (D i) (u i)) ∧ (∀ i < n, ∀ k, VGe p 0 (u i k)) ∧
      ∀ (a : ℕ → ℚ) (c : Fin 4 → ℚ), c = ∑ i ∈ Finset.range n, a i • v i → c 3 = 0 →
        ∀ k : Fin 3, c k.castSucc = ∑ i ∈ Finset.range n, a i * u i k.castSucc := by
  have hsum : ∀ (a : ℕ → ℚ) (c : Fin 4 → ℚ), c = ∑ i ∈ Finset.range n, a i • v i →
      ∀ k, c k = ∑ i ∈ Finset.range n, a i * v i k := by
    intro a c hc k; rw [hc, Finset.sum_apply]; rfl
  unfold G3Of
  cases hp : pidxOf ((List.range n).map (fun i => (w i, d i))) with
  | none =>
    refine ⟨fun i => ⟨fun k => (d i).co k.castSucc, false⟩, v, ?_, ?_, hI, ?_⟩
    · simp only [List.map_map]; rfl
    · intro i hi; exact ⟨fun k q h => (hM i hi).1 _ _ h, fun h => by simp at h⟩
    · intro a c hc _ k; exact hsum a c hc _
  | some pidx =>
    obtain ⟨hlt, hpiv⟩ := pidxOf_spec hp
    have hlt' : pidx < n := by simpa using hlt
    have hG : ((List.range n).map (fun i => (w i, d i)))[pidx] = (w pidx, d pidx) := by simp
    rw [hG] at hpiv
    unfold isPivD at hpiv
    cases h3 : (d pidx).co 3 with
    | none => simp [h3] at hpiv
    | some s =>
      simp only [h3, decide_eq_true_eq] at hpiv
      obtain ⟨-, hs⟩ := hpiv
      have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
      have hv3 : v pidx 3 = s := (hM pidx hlt').1 3 s h3
      refine ⟨fun i => if i = pidx then zeroDesc3 else elimDesc (d pidx) s (d i),
        fun i => v i - (v i 3 / s) • v pidx, ?_, ?_, ?_, ?_⟩
      · have hG' : ((List.range n).map (fun i => (w i, d i)))[pidx]! = (w pidx, d pidx) := by
          simp [hlt']
        simp only [hG', h3, Option.getD_some]
        apply List.ext_getElem
        · simp
        · intro i h1 h2; simp
      · intro i hi
        by_cases hip : i = pidx
        · subst hip
          simp only [↓reduceIte]
          have : v i - (v i 3 / s) • v i = 0 := by rw [hv3, div_self hs0, one_smul, sub_self]
          rw [this]
          exact ⟨fun k q hq => by simp [zeroDesc3] at hq; simp [hq],
            fun h => by simp [zeroDesc3] at h⟩
        · simp only [hip, ↓reduceIte]
          exact elimDesc_match (hM pidx hlt') (hM i hi)
      · intro i hi k
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have hinv : VGe p 0 (1 / s) := by
          rcases hs with rfl | rfl
          · simpa using VGe.natCast (p := p) 1
          · simpa using VGe.intCast (p := p) (-1)
        rw [div_eq_mul_one_div]
        exact VGe.sub (hI i hi k) (VGe.mul0 (VGe.mul0 (hI i hi 3) hinv) (hI pidx hlt' k))
      · intro a c hc hc3 k
        rw [hsum a c hc k.castSucc]
        have h3' := hsum a c hc 3
        rw [hc3] at h3'
        have : ∑ i ∈ Finset.range n, a i * (v i - (v i 3 / s) • v pidx) k.castSucc =
            ∑ i ∈ Finset.range n, a i * v i k.castSucc -
              (∑ i ∈ Finset.range n, a i * v i 3) * (v pidx k.castSucc / s) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro i _
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [this, ← h3']; ring

/-- abstract soundness of the dual bound for a weighted list of matched generators -/
theorem abstract_sound (n : ℕ) (w : ℕ → ℤ) (v : ℕ → Fin 4 → ℚ) (d : ℕ → Desc)
    (hM : ∀ i < n, DMatch (d i) (v i)) (hI : ∀ i < n, ∀ k, VGe p 0 (v i k))
    (α β : ℕ → ℚ) (hα : ∀ i, VGe p 0 (α i)) (hβ : ∀ i, VGe p 0 (β i)) (c₁ c₂ : Fin 4 → ℚ)
    (h₁ : c₁ = ∑ i ∈ Finset.range n, (α i * (p : ℚ) ^ w i) • v i)
    (h₂ : c₂ = ∑ i ∈ Finset.range n, (β i * (p : ℚ) ^ w i) • v i)
    (h₁₃ : c₁ 3 = 0) (h₂₃ : c₂ 3 = 0) :
    VGe p (bound3 (G3Of ((List.range n).map (fun i => (w i, d i)))))
        (c₁ 1 * c₂ 2 - c₁ 2 * c₂ 1) ∧
    VGe p (bound3 (G3Of ((List.range n).map (fun i => (w i, d i)))) + 2)
        (c₁ 0 * c₂ 1 - c₁ 1 * c₂ 0) ∧
    VGe p (bound3 (G3Of ((List.range n).map (fun i => (w i, d i)))) + 2)
        (c₁ 0 * c₂ 2 - c₁ 2 * c₂ 0) := by
  obtain ⟨D, u, hG3, hM3, hI3, hred⟩ := stage1 n w v d hM hI
  have hc₁ := hred _ c₁ h₁ h₁₃
  have hc₂ := hred _ c₂ h₂ h₂₃
  have S := fun a b th hth => stage2 n w D u hM3 hI3 α β hα hβ c₁ c₂ hc₁ hc₂ a b th hth
  rw [hG3]; unfold bound3
  set G3 := (List.range n).map (fun i => (w i, D i))
  have m1 := min_le_left (projBound G3 1 2 true)
    (min (projBound G3 0 1 false - 2) (projBound G3 0 2 false - 2))
  have m2 := min_le_right (projBound G3 1 2 true)
    (min (projBound G3 0 1 false - 2) (projBound G3 0 2 false - 2))
  have m3 := min_le_left (projBound G3 0 1 false - 2) (projBound G3 0 2 false - 2)
  have m4 := min_le_right (projBound G3 0 1 false - 2) (projBound G3 0 2 false - 2)
  refine ⟨?_, ?_, ?_⟩
  · exact VGe.mono (S 1 2 true (fun _ => ⟨rfl, rfl⟩)) m1
  · exact VGe.mono (S 0 1 false (fun h => by simp at h)) (by omega)
  · exact VGe.mono (S 0 2 false (fun h => by simp at h)) (by omega)

end

end Zeta2L2Chi3.Arith
