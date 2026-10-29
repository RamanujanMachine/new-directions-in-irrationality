/-
# Lattice spans, descriptors and soundness of the dual bound

If two columns lie in the `ℤ_(p)`-span of weighted `p`-integral generators `p^{w} g` and have zero
total coordinate, their projected 2×2 minors have valuation at least `dualBoundOf` (resp. `+2`).
-/
import Zeta2L2Chi3.Arith.Checker
import Zeta2L2Chi3.Arith.Valuation
import Zeta2L2Chi3.Arith.Lagrange
import Zeta2L2Chi3.Arith.LatticeAux

namespace Zeta2L2Chi3.Arith

/-- `c` lies in the `ℤ_(p)`-span of the vectors `p^{w} g`, `(w, g) ∈ G` -/
def InSpan (p : ℕ) {m : ℕ} (G : List (ℤ × (Fin m → ℚ))) (c : Fin m → ℚ) : Prop :=
  ∃ α : ℕ → ℚ, (∀ i, VGe p 0 (α i)) ∧
    c = ∑ i ∈ Finset.range G.length, (α i * (p : ℚ) ^ (G[i]!).1) • (G[i]!).2

/-- the 2×2 minor of the columns `c₁, c₂` in the rows `i, j` -/
def minor {m : ℕ} (i j : Fin m) (c₁ c₂ : Fin m → ℚ) : ℚ := c₁ i * c₂ j - c₁ j * c₂ i

theorem getElem!_eq_of_lt {α : Type*} [Inhabited α] {l : List α} {i : ℕ} (h : i < l.length) :
    l[i]! = l[i] := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem map_eq_map_range {α β : Type*} [Inhabited α] (f : α → β) (l : List α) :
    l.map f = (List.range l.length).map (fun i => f l[i]!) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [getElem!_eq_of_lt (by simpa using h1)]

section
variable {p : ℕ} [Fact p.Prime]

theorem InSpan.add {m : ℕ} {G : List (ℤ × (Fin m → ℚ))} {c d : Fin m → ℚ} (hc : InSpan p G c)
    (hd : InSpan p G d) : InSpan p G (c + d) := by
  obtain ⟨α, hα, rfl⟩ := hc
  obtain ⟨β, hβ, rfl⟩ := hd
  refine ⟨fun i => α i + β i, fun i => VGe.add (hα i) (hβ i), ?_⟩
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← add_smul, add_mul]

theorem InSpan.zero {m : ℕ} (G : List (ℤ × (Fin m → ℚ))) : InSpan p G 0 :=
  ⟨fun _ => 0, fun _ => VGe.zero 0, by simp⟩

/-- spans are monotone in the generator list (as sets) -/
theorem InSpan.mono {m : ℕ} {G G' : List (ℤ × (Fin m → ℚ))} (hG : ∀ g ∈ G, g ∈ G') {c : Fin m → ℚ}
    (hc : InSpan p G c) : InSpan p G' c := by
  classical
  obtain ⟨α, hα, rfl⟩ := hc
  have hex : ∀ i (hi : i < G.length), ∃ j, ∃ h : j < G'.length, G'[j] = G[i] :=
    fun i hi => List.getElem_of_mem (hG _ (List.getElem_mem hi))
  choose! f hf hfe using hex
  refine ⟨fun j => ∑ i ∈ Finset.range G.length, if f i = j then α i else 0,
    fun j => VGe.finset_sum (fun i _ => ?_), ?_⟩
  · split_ifs
    · exact hα i
    · exact VGe.zero 0
  symm
  calc ∑ j ∈ Finset.range G'.length,
        ((∑ i ∈ Finset.range G.length, if f i = j then α i else 0) * (p : ℚ) ^ (G'[j]!).1) •
          (G'[j]!).2
      = ∑ j ∈ Finset.range G'.length, ∑ i ∈ Finset.range G.length,
          (if f i = j then (α i * (p : ℚ) ^ (G'[j]!).1) • (G'[j]!).2 else 0) := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_mul, Finset.sum_smul]
        apply Finset.sum_congr rfl; intro i _
        split_ifs <;> simp
    _ = ∑ i ∈ Finset.range G.length, ∑ j ∈ Finset.range G'.length,
          (if f i = j then (α i * (p : ℚ) ^ (G'[j]!).1) • (G'[j]!).2 else 0) :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.range G.length, (α i * (p : ℚ) ^ (G[i]!).1) • (G[i]!).2 := by
        apply Finset.sum_congr rfl; intro i hi
        have hi' := Finset.mem_range.1 hi
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_range.2 (hf i hi'), ↓reduceIte]
        rw [getElem!_eq_of_lt (hf i hi'), getElem!_eq_of_lt hi', hfe i hi']

/-- a single generator, with a `p`-integral coefficient and a weight shift -/
theorem InSpan.gen {m : ℕ} {G : List (ℤ × (Fin m → ℚ))} {g : ℤ × (Fin m → ℚ)} (hg : g ∈ G) (a : ℚ)
    (ha : VGe p 0 a) (k : ℤ) (hk : 0 ≤ k) : InSpan p G ((a * (p : ℚ) ^ (g.1 + k)) • g.2) := by
  classical
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨fun i => if i = j then a * (p : ℚ) ^ k else 0, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · have := VGe.mul ha (VGe.zpow (p := p) k)
      exact VGe.mono this (by omega)
    · exact VGe.zero 0
  · rw [Finset.sum_eq_single j]
    · dsimp only
      rw [getElem!_eq_of_lt hj, zpow_add₀ hp0]
      simp only [↓reduceIte]
      congr 1; ring
    · intro b _ hb; simp [hb]
    · intro hj'; exact absurd (Finset.mem_range.2 hj) hj'

/-! ### `p`-integrality of the generators -/

theorem not_dvd_six (hp5 : 5 ≤ p) : ¬ p ∣ 6 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases p
  · norm_num at h
  · exact absurd (Fact.out : Nat.Prime 6) (by norm_num)

theorem six_int {x : ℚ} (hd : x.den ∣ 6) : ∃ m : ℤ, 6 * x = m := by
  obtain ⟨c, hc⟩ := hd
  refine ⟨x.num * c, ?_⟩
  have h := Rat.mul_den_eq_num x
  rw [show (6 : ℚ) = ((6 : ℕ) : ℚ) by norm_num, hc]
  push_cast
  rw [← h]; ring

theorem pint_of_six {x : ℚ} {m : ℤ} (h : 6 * x = m) (hp5 : 5 ≤ p) : VGe p 0 x := by
  have hx : x = m * (6 : ℚ)⁻¹ := by rw [← h]; field_simp
  rw [hx]
  have h6 : padicValRat p 6 = 0 := by
    rw [show (6 : ℚ) = ((6 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (not_dvd_six hp5)]
    rfl
  have := VGe.inv (p := p) (show (6 : ℚ) ≠ 0 by norm_num)
  rw [h6, neg_zero] at this
  exact VGe.mul0 (VGe.intCast m) this

theorem val_zero_of_six {x : ℚ} {m : ℤ} (hx : x ≠ 0) (h : 6 * x = m) (hm : |(m : ℚ)| < p)
    (hp5 : 5 ≤ p) : padicValRat p x = 0 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hx
    have : (6 : ℚ) * x = 0 := by rw [h]; simp
    simpa using this
  have hx' : x = (m : ℚ) / 6 := by rw [← h]; ring
  have hnd : ¬ (p : ℤ) ∣ m := by
    intro hd
    have h1 : (p : ℤ) ≤ |m| := Int.le_of_dvd (abs_pos.2 hm0) ((dvd_abs _ _).2 hd)
    have h2 : |m| < (p : ℤ) := by
      have : ((|m| : ℤ) : ℚ) < ((p : ℤ) : ℚ) := by push_cast; exact hm
      exact_mod_cast this
    omega
  rw [hx', padicValRat.div (by exact_mod_cast hm0) (by norm_num), padicValRat.of_int,
    show (6 : ℚ) = ((6 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
    padicValInt.eq_zero_of_not_dvd hnd, padicValNat.eq_zero_of_not_dvd (not_dvd_six hp5)]
  simp

theorem inv_pint_of_six {x : ℚ} {m : ℤ} (hx : x ≠ 0) (h : 6 * x = m) (hm : |(m : ℚ)| < p)
    (hp5 : 5 ≤ p) : VGe p 0 x⁻¹ := by
  have := VGe.inv (p := p) hx
  rwa [val_zero_of_six hx h hm hp5, neg_zero] at this

theorem unit_prod (l : List ℚ) (hl : ∀ y ∈ l, y ≠ 0 ∧ padicValRat p y = 0) :
    l.prod ≠ 0 ∧ padicValRat p l.prod = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    obtain ⟨h3, h4⟩ := hl a List.mem_cons_self
    rw [List.prod_cons]
    exact ⟨mul_ne_zero h3 h1, by rw [padicValRat.mul h3 h1, h2, h4]; rfl⟩

theorem unitVec_pint (k' k : Fin 4) : VGe p 0 (unitVec k' k) := by
  unfold unitVec
  split_ifs
  · simpa using VGe.natCast (p := p) 1
  · exact VGe.zero 0

theorem Hq_mem (b y : ℚ) (hy : y ∈ ((List.range ⌈b⌉.toNat).map (fun i => 1 / (b - i) ^ 2))) :
    ∃ i : ℕ, i < ⌈b⌉.toNat ∧ y = 1 / (b - i) ^ 2 := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
  simp only [bind, pure, List.mem_flatMap, List.mem_range, List.mem_singleton] at hr
  obtain ⟨k, hk, rfl⟩ := hr
  exact ⟨k, hk, rfl⟩

theorem PType.V_pint (t : PType) (hp5 : 5 ≤ p)
    (hsmall : ∀ x ∈ t.zs ++ t.ps.map Prod.fst, x.den ∣ 6 ∧ 12 * |x| < p) (j : ℕ) (k : Fin 4) :
    VGe p 0 (t.V j k) := by
  have hbnd : ∀ x ∈ t.zs ++ t.ps.map Prod.fst, -((p : ℚ) / 12) < x ∧ x < (p : ℚ) / 12 := by
    intro x hx
    have := (hsmall x hx).2
    exact abs_lt.1 (by linarith)
  have hsub : ∀ x ∈ t.zs ++ t.ps.map Prod.fst, ∀ y ∈ t.zs ++ t.ps.map Prod.fst,
      ∃ m : ℤ, 6 * (x - y) = m ∧ |(m : ℚ)| < p := by
    intro x hx y hy
    obtain ⟨m1, h1⟩ := six_int (hsmall x hx).1
    obtain ⟨m2, h2⟩ := six_int (hsmall y hy).1
    refine ⟨m1 - m2, by push_cast; rw [← h1, ← h2]; ring, ?_⟩
    have := hbnd x hx; have := hbnd y hy
    push_cast; rw [← h1, ← h2]
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  have hpole : ∀ q ∈ t.ps, q.1 ∈ t.zs ++ t.ps.map Prod.fst :=
    fun q hq => List.mem_append_right _ (List.mem_map_of_mem hq)
  have hR : ∀ q ∈ t.ps, VGe p 0 (t.R q.1) := by
    intro q hq
    unfold PType.R
    rw [div_eq_mul_inv]
    apply VGe.mul0
    · apply VGe.list_prod; intro y hy
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
      obtain ⟨m, hm, -⟩ := hsub _ (hpole q hq) a (List.mem_append_left _ ha)
      exact pint_of_six hm hp5
    · obtain ⟨hne, hv⟩ := unit_prod (p := p)
        (((t.ps.filter (fun q' => q'.1 ≠ q.1)).map (fun q' => q.1 - q'.1))) (by
          intro y hy
          obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hy
          obtain ⟨hq'1, hq'2⟩ := List.mem_filter.1 hq'
          have hne : q.1 - q'.1 ≠ 0 := sub_ne_zero.2 (Ne.symm (by simpa using hq'2))
          obtain ⟨m, hm, hmb⟩ := hsub _ (hpole q hq) _ (hpole q' hq'1)
          exact ⟨hne, val_zero_of_six hne hm hmb hp5⟩)
      have := VGe.inv (p := p) hne
      rwa [hv, neg_zero] at this
  have hP : ∀ q ∈ t.ps, VGe p 0 (q.1 ^ j) := by
    intro q hq
    obtain ⟨m, hm⟩ := six_int (hsmall _ (hpole q hq)).1
    simpa using VGe.pow j (pint_of_six hm hp5)
  have hH : ∀ q ∈ t.ps, VGe p 0 (Hq q.1) := by
    intro q hq
    unfold Hq
    apply VGe.list_sum; intro y hy
    obtain ⟨i, hi, rfl⟩ := Hq_mem _ _ hy
    have hi0 := Int.lt_ceil.1 (Int.lt_toNat.1 hi)
    have hi1 : (i : ℚ) < q.1 := by exact_mod_cast hi0
    obtain ⟨m1, h1⟩ := six_int (hsmall _ (hpole q hq)).1
    have hne : q.1 - i ≠ 0 := by linarith
    have hm : 6 * (q.1 - i) = ((m1 - 6 * i : ℤ) : ℚ) := by push_cast; rw [← h1]; ring
    have hmb : |((m1 - 6 * i : ℤ) : ℚ)| < p := by
      rw [← hm]
      have := (hbnd _ (hpole q hq)).2
      rw [abs_of_pos (by linarith)]
      have : (0 : ℚ) ≤ i := by positivity
      linarith
    have := VGe.pow 2 (inv_pint_of_six hne hm hmb hp5)
    rw [one_div, ← inv_pow]
    simpa using this
  fin_cases k
  · simp only [PType.V]
    apply VGe.neg; apply VGe.list_sum; intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    exact VGe.mul0 (VGe.mul0 (hR q hq) (hP q hq)) (hH q hq)
  · simp only [PType.V]
    apply VGe.list_sum; intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    have hq := List.mem_of_mem_filter hq
    exact VGe.mul0 (hR q hq) (hP q hq)
  · simp only [PType.V]
    apply VGe.list_sum; intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    have hq := List.mem_of_mem_filter hq
    exact VGe.mul0 (hR q hq) (hP q hq)
  · simp only [PType.V]
    apply VGe.list_sum; intro y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    exact VGe.mul0 (hR q hq) (hP q hq)

/-- generators of a packet type whose T-values are small compared with `p` are `p`-integral -/
theorem PType.gens_pint (t : PType) (hp5 : 5 ≤ p)
    (hsmall : ∀ x ∈ t.zs ++ t.ps.map Prod.fst, x.den ∣ 6 ∧ 12 * |x| < p) :
    ∀ g ∈ t.gens, ∀ k, VGe p 0 (g.2 k) := by
  intro g hg k
  unfold PType.gens at hg
  split_ifs at hg
  · simp at hg
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (⟨i, -, rfl⟩ | rfl) | ⟨k', -, rfl⟩
    · exact t.V_pint hp5 hsmall _ k
    · exact unitVec_pint 0 k
    · exact unitVec_pint k' k

/-! ### Soundness of the dual bound -/

/-- generators of a packet type together with their descriptors -/
def PType.trip (t : PType) (e : Bool) : List (ℤ × (Fin 4 → ℚ) × Desc) :=
  if t.ps = [] then [] else
  ((List.range (Jt + 1 - t.jmin)).map (fun i => (t.h + 1 + (t.jmin + i : ℕ), t.V (t.jmin + i),
      if e then exactDesc (t.V (t.jmin + i)) else structDesc t (t.jmin + i)))) ++
  [(t.regW, unitVec 0, exactDesc (unitVec 0))] ++
  (List.finRange 4).map (fun k => (t.h + Jt + 2, unitVec k, exactDesc (unitVec k)))

theorem PType.gens_trip (t : PType) (e : Bool) :
    t.gens = (t.trip e).map (fun x => (x.1, x.2.1)) := by
  unfold PType.gens PType.trip
  split_ifs <;> simp [List.map_map, Function.comp_def]

theorem PType.descs_trip (t : PType) (e : Bool) :
    t.descs e = (t.trip e).map (fun x => (x.1, x.2.2)) := by
  unfold PType.descs PType.trip
  split_ifs <;> simp [List.map_map, Function.comp_def]

theorem PType.trip_match (t : PType) (e : Bool) (hnd : (t.ps.map Prod.fst).Nodup)
    (hlab : ∀ q ∈ t.ps, q.2 ≤ 2) : ∀ x ∈ t.trip e, DMatch x.2.2 x.2.1 := by
  intro x hx
  unfold PType.trip at hx
  split_ifs at hx
  · simp at hx
  all_goals
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with (⟨i, -, rfl⟩ | rfl) | ⟨k, -, rfl⟩
    · first | exact exactDesc_match _ | exact structDesc_match t hnd hlab _
    · exact exactDesc_match _
    · exact exactDesc_match _

/-- soundness of the dual bound -/
theorem dualBound_sound (Ts : List PType) (ex : ℕ → PType → Bool)
    (hint : ∀ t ∈ Ts, ∀ g ∈ t.gens, ∀ k, VGe p 0 (g.2 k))
    (hnd : ∀ t ∈ Ts, (t.ps.map Prod.fst).Nodup)
    (hlab : ∀ t ∈ Ts, ∀ q ∈ t.ps, q.2 ≤ 2)
    (c₁ c₂ : Fin 4 → ℚ) (h₁ : InSpan p (Ts.flatMap PType.gens) c₁)
    (h₂ : InSpan p (Ts.flatMap PType.gens) c₂) (h₁₃ : c₁ 3 = 0) (h₂₃ : c₂ 3 = 0) :
    VGe p (dualBoundOf Ts ex) (minor 1 2 c₁ c₂) ∧
    VGe p (dualBoundOf Ts ex + 2) (minor 0 1 c₁ c₂) ∧
    VGe p (dualBoundOf Ts ex + 2) (minor 0 2 c₁ c₂) := by
  set L := Ts.zipIdx.flatMap (fun ti => ti.1.trip (ex ti.2 ti.1)) with hL
  have hGv : Ts.flatMap PType.gens = L.map (fun x => (x.1, x.2.1)) := by
    rw [hL, List.map_flatMap]
    conv_lhs => rw [← List.zipIdx_map_fst 0 Ts, List.flatMap_map]
    congr 1; funext ti; exact PType.gens_trip _ _
  have hGd : Ts.zipIdx.flatMap (fun ti => ti.1.descs (ex ti.2 ti.1)) =
      L.map (fun x => (x.1, x.2.2)) := by
    rw [hL, List.map_flatMap]; congr 1; funext ti; exact PType.descs_trip _ _
  have hmemL : ∀ x ∈ L, ∃ t ∈ Ts, ∃ e, x ∈ t.trip e := by
    intro x hx; rw [hL, List.mem_flatMap] at hx; obtain ⟨ti, hti, hx⟩ := hx
    exact ⟨ti.1, List.fst_mem_of_mem_zipIdx hti, _, hx⟩
  have hLi : ∀ i < L.length, L[i]! ∈ L := fun i hi => by
    rw [getElem!_eq_of_lt hi]; exact List.getElem_mem hi
  have hM : ∀ i < L.length, DMatch (L[i]!).2.2 (L[i]!).2.1 := fun i hi => by
    obtain ⟨t, ht, e, hx⟩ := hmemL _ (hLi i hi)
    exact t.trip_match e (hnd t ht) (hlab t ht) _ hx
  have hI : ∀ i < L.length, ∀ k, VGe p 0 ((L[i]!).2.1 k) := fun i hi k => by
    obtain ⟨t, ht, e, hx⟩ := hmemL _ (hLi i hi)
    exact hint t ht _ (by rw [t.gens_trip e]; exact List.mem_map_of_mem hx) k
  have hGv' := hGv.trans (map_eq_map_range _ L)
  rw [dualBoundOf_eq, hGd, map_eq_map_range _ L]
  rw [hGv'] at h₁ h₂
  have conv : ∀ (α : ℕ → ℚ) (c : Fin 4 → ℚ),
      c = ∑ i ∈ Finset.range ((List.range L.length).map
          (fun i => (fun x : ℤ × (Fin 4 → ℚ) × Desc => (x.1, x.2.1)) L[i]!)).length,
        (α i * (p : ℚ) ^ (((List.range L.length).map
          (fun i => (fun x : ℤ × (Fin 4 → ℚ) × Desc => (x.1, x.2.1)) L[i]!))[i]!).1) •
          (((List.range L.length).map
          (fun i => (fun x : ℤ × (Fin 4 → ℚ) × Desc => (x.1, x.2.1)) L[i]!))[i]!).2 →
      c = ∑ i ∈ Finset.range L.length, (α i * (p : ℚ) ^ (L[i]!).1) • (L[i]!).2.1 := by
    intro α c hc
    rw [hc]
    simp only [List.length_map, List.length_range]
    apply Finset.sum_congr rfl; intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [getElem!_eq_of_lt (by simpa using hi')]
    simp
  obtain ⟨α, hα, hα'⟩ := h₁
  obtain ⟨β, hβ, hβ'⟩ := h₂
  exact abstract_sound L.length (fun i => (L[i]!).1) (fun i => (L[i]!).2.1) (fun i => (L[i]!).2.2)
    hM hI α β hα hβ c₁ c₂ (conv α c₁ hα') (conv β c₂ hβ') h₁₃ h₂₃

end

end Zeta2L2Chi3.Arith
