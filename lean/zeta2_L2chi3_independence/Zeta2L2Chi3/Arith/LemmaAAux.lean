/-
# Auxiliary machinery for Lemma A

A generic version of the dual packet lemma: for a list of zeros `Z` and of pole records `P`
(value, label, harmonic weight), the class-`r` contribution to the residue rows lies in the
span of the generators of the class-`r` packet type.
-/
import Zeta2L2Chi3.Arith.Valuation
import Zeta2L2Chi3.Arith.Family
import Zeta2L2Chi3.Arith.Harmonic
import Zeta2L2Chi3.Arith.Taylor
import Zeta2L2Chi3.Arith.Lagrange

namespace Zeta2L2Chi3.Arith
namespace LA

/-! ### List lemmas -/

theorem sum_map_filter {α : Type*} (l : List α) (P : α → Bool) (g : α → ℚ) :
    ((l.filter P).map g).sum = (l.map (fun x => if P x then g x else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

theorem prod_map_split {α : Type*} (l : List α) (P : α → Bool) (g : α → ℚ) :
    (l.map g).prod = ((l.filter P).map g).prod * ((l.filter (fun x => !P x)).map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : P a
    · simp [h, ih]; ring
    · simp [h, ih]; ring

theorem sum_map_fin6 {α : Type*} (l : List α) (f : α → Fin 6 → ℚ) :
    (l.map (fun x => ∑ j, f x j)).sum = ∑ j, (l.map (fun x => f x j)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sum_add_distrib]

theorem sum_map_mul_left' {α : Type*} (l : List α) (c : ℚ) (f : α → ℚ) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem sum_map_add' {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem prod_map_const' {α : Type*} (l : List α) (c : ℚ) :
    (l.map (fun _ => c)).prod = c ^ l.length := by
  simp

theorem prod_map_mul' {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map (fun x => f x * g x)).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem prod_map_inv' {α : Type*} (l : List α) (f : α → ℚ) :
    (l.map (fun x => 1 / f x)).prod = 1 / (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, one_div_mul_one_div]


/-! ### Classes, T-values, residues -/

/-- `x` lies in the residue class `r` -/
def cls (p r : ℕ) (x : ℚ) : Bool := decide ((p : ℤ) ∣ (x - r).num)

/-- the T-value `(x - r)/p` -/
def Tv (p r : ℕ) (x : ℚ) : ℚ := (x - r) / p

/-- a pole record: value, label, harmonic weight -/
abbrev Rec := ℚ × ℕ × ℚ

/-- `v_x = ∏_z (x - z) / ∏_{l ≠ x} (l - x)` -/
def vres (Z : List ℚ) (P : List Rec) (x : ℚ) : ℚ :=
  (Z.map (fun z => x - z)).prod / ((P.filter (fun q => q.1 ≠ x)).map (fun q => q.1 - x)).prod

/-- the packet type of the class `r` -/
def typ (p : ℕ) (Z : List ℚ) (P : List Rec) (r jmin : ℕ) : PType :=
  ⟨(Z.filter (cls p r)).map (Tv p r),
    (P.filter (fun q => cls p r q.1)).map (fun q => (Tv p r q.1, q.2.1)), jmin⟩

/-- label indicator -/
def ind (c : ℕ) (q : Rec) : ℚ := if q.2.1 = c then 1 else 0

/-- the row sums `(p² B₀', B_T, B_H, B_all)` over a sublist `L` of the poles -/
def rowVec (p : ℕ) (Z : List ℚ) (P : List Rec) (k : ℕ) (L : List Rec) : Fin 4 → ℚ :=
  ![(p : ℚ) ^ 2 * -(L.map (fun q => vres Z P q.1 * q.2.2 * q.1 ^ k)).sum,
    (L.map (fun q => ind 1 q * (vres Z P q.1 * q.1 ^ k))).sum,
    (L.map (fun q => ind 2 q * (vres Z P q.1 * q.1 ^ k))).sum,
    (L.map (fun q => vres Z P q.1 * q.1 ^ k)).sum]

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem p_ne_zero' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

theorem vge1_of_cls {r : ℕ} {x : ℚ} (hd : ¬ p ∣ x.den) (hc : cls p r x = true) :
    VGe p 1 (x - r) := by
  rw [VGe.one_iff (by rwa [Rat.sub_natCast_den])]
  simpa [cls] using hc

theorem Tv_int {r : ℕ} {x : ℚ} (hd : ¬ p ∣ x.den) (hc : cls p r x = true) :
    VGe p 0 (Tv p r x) := by
  have := (vge1_of_cls hd hc).mul (VGe.zpow (p := p) (-1))
  simp only [Tv]
  convert this using 1
  · norm_num
  · rw [zpow_neg_one, div_eq_mul_inv]

theorem Tv_inj {r : ℕ} {x y : ℚ} : Tv p r x = Tv p r y ↔ x = y := by
  have := p_ne_zero' (p := p)
  simp only [Tv]
  constructor
  · intro h; field_simp at h; linarith
  · rintro rfl; rfl

theorem unit_of_not_cls {r : ℕ} {x : ℚ} (hd : ¬ p ∣ x.den) (hc : cls p r x = false) :
    (r : ℚ) - x ≠ 0 ∧ padicValRat p ((r : ℚ) - x) = 0 := by
  have hc' : ¬ (p : ℤ) ∣ (x - r).num := by simpa [cls] using hc
  have hne : x - r ≠ 0 := by intro h; apply hc'; rw [h]; simp
  have hd' : ¬ p ∣ (x - r).den := by rwa [Rat.sub_natCast_den]
  refine ⟨fun h => hne (by linarith), ?_⟩
  rw [show (r : ℚ) - x = -(x - r) by ring, padicValRat.neg, padicValRat_def,
    padicValNat.eq_zero_of_not_dvd hd', padicValInt, padicValNat.eq_zero_of_not_dvd ?_]
  · simp
  · intro h; apply hc'; exact Int.natCast_dvd.mpr h

theorem val_div_p {y : ℚ} (hy : y ≠ 0) (h1 : VGe p 1 y) (h2 : padicValRat p y ≤ 1) :
    padicValRat p (y / p) = 0 := by
  have h1' := h1.resolve_left hy
  rw [padicValRat.div hy p_ne_zero', padicValRat.self hp.out.one_lt]; omega

theorem vge_one_div_sq {y : ℚ} (hy : y ≠ 0) (hv : padicValRat p y = 0) : VGe p 0 (1 / y ^ 2) := by
  right; rw [one_div, padicValRat.inv, padicValRat.pow]; simp [hv]

theorem vge_div_unit {a y : ℚ} (ha : VGe p 0 a) (hy : y ≠ 0) (hv : padicValRat p y = 0) :
    VGe p 0 (a / y) := by
  have := ha.mul (VGe.inv (p := p) hy)
  rw [hv, neg_zero, add_zero] at this
  rwa [div_eq_mul_inv]

theorem unit_list_prod (l : List ℚ) (h : ∀ y ∈ l, y ≠ 0 ∧ padicValRat p y = 0) :
    l.prod ≠ 0 ∧ padicValRat p l.prod = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := h a (by simp)
    obtain ⟨h3, h4⟩ := ih (fun y hy => h y (by simp [hy]))
    rw [List.prod_cons]
    exact ⟨mul_ne_zero h1 h3, by rw [padicValRat.mul h1 h3, h2, h4]; simp⟩

theorem Hq_int {r : ℕ} {x : ℚ} (hd : ¬ p ∣ x.den) (hc : cls p r x = true)
    (hH : ∀ m : ℕ, (m : ℚ) < x → padicValRat p (x - m) ≤ 1) : VGe p 0 (Hq (Tv p r x)) := by
  unfold Hq
  apply VGe.list_sum
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨i', hi', rfl⟩ := hy
  simp at hi'
  obtain ⟨i, hi, rfl⟩ := hi'
  have hlt : (i : ℚ) < Tv p r x := by
    exact_mod_cast Int.lt_ceil.mp hi
  have hp0 := p_ne_zero' (p := p)
  have hpos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have heq : Tv p r x - i = (x - ((r + i * p : ℕ) : ℚ)) / p := by
    simp only [Tv]; push_cast; field_simp; ring
  have hxm : ((r + i * p : ℕ) : ℚ) < x := by
    have : (i : ℚ) * p < x - r := by
      have := (lt_div_iff₀ hpos).mp (by simpa [Tv] using hlt); linarith
    push_cast; linarith
  have hv1 : VGe p 1 (x - ((r + i * p : ℕ) : ℚ)) := by
    have h2 : VGe p 1 ((i : ℚ) * p) := by
      have := (VGe.natCast (p := p) i).mul (VGe.zpow (p := p) 1)
      simpa using this
    have := (vge1_of_cls hd hc).sub h2
    convert this using 1; push_cast; ring
  have hne : x - ((r + i * p : ℕ) : ℚ) ≠ 0 := by linarith
  have h0 := val_div_p hne hv1 (hH _ hxm)
  rw [heq]
  exact vge_one_div_sq (div_ne_zero hne hp0) h0

theorem Gsq_int {r : ℕ} (hr : r < p) : VGe p 0 (Gsq r) := by
  unfold Gsq
  apply VGe.finset_sum
  intro a ha
  rw [Finset.mem_range] at ha
  have h1 : ((a : ℚ) + 1) = ((a + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [h1]
  refine vge_one_div_sq (by positivity) ?_
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro h; have := Nat.le_of_dvd (by omega) h; omega

end

/-! ### The residue factorization -/

theorem filter_one_length {L : List Rec} (hnd : (L.map Prod.fst).Nodup) {q0 : Rec} (hq0 : q0 ∈ L) :
    (L.filter (fun q => q.1 ≠ q0.1)).length + 1 = L.length := by
  have h := List.length_eq_length_filter_add (l := L) (fun q => decide (q.1 ≠ q0.1))
  have h1 : (L.filter (fun q => !decide (q.1 ≠ q0.1))).length = 1 := by
    set M := L.filter (fun q => !decide (q.1 ≠ q0.1)) with hM
    have hsub : (M.map Prod.fst).Sublist (L.map Prod.fst) := (List.filter_sublist).map _
    have hndM : (M.map Prod.fst).Nodup := hnd.sublist hsub
    have hall : ∀ y ∈ M.map Prod.fst, y = q0.1 := by
      intro y hy
      simp only [hM, List.mem_map, List.mem_filter] at hy
      obtain ⟨a, ⟨_, ha⟩, rfl⟩ := hy
      simpa using ha
    have hrep : M.map Prod.fst = List.replicate (M.map Prod.fst).length q0.1 :=
      List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    have hmem : q0 ∈ M := by simp [hM, hq0]
    have hle : (M.map Prod.fst).length ≤ 1 := by
      rw [hrep] at hndM; exact List.nodup_replicate.mp hndM
    have hpos : 0 < M.length := List.length_pos_of_mem hmem
    simp only [List.length_map] at hle; omega
  omega

theorem alg_id (pp N An D Dn s : ℚ) (a m : ℕ) (hs : s * s = 1) :
    (pp ^ a * N * An) / (s ^ m * pp ^ m * D * Dn) = s ^ m * (pp ^ a / pp ^ m) * (N / D) * (An / Dn) := by
  have h1 : (s ^ m)⁻¹ = s ^ m := by
    apply inv_eq_of_mul_eq_one_right; rw [← mul_pow, hs, one_pow]
  simp only [div_eq_mul_inv, mul_inv, h1]
  ring

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem vres_factor (Z : List ℚ) (P : List Rec) (r jmin : ℕ) (hnd : (P.map Prod.fst).Nodup)
    (q0 : Rec) (hq0 : q0 ∈ P) (hc : cls p r q0.1 = true) :
    vres Z P q0.1 = (-1) ^ ((P.filter (fun q => cls p r q.1)).length - 1) *
      (p : ℚ) ^ ((typ p Z P r jmin).h + 1) * (typ p Z P r jmin).R (Tv p r q0.1) *
      (((Z.filter (fun z => !cls p r z)).map (fun z => q0.1 - z)).prod /
        ((P.filter (fun q => !cls p r q.1)).map (fun q => q.1 - q0.1)).prod) := by
  set x := q0.1 with hx
  set Pr := P.filter (fun q => cls p r q.1) with hPr
  have hp0 := p_ne_zero' (p := p)
  have hnum : (Z.map (fun z => x - z)).prod = (p : ℚ) ^ (Z.filter (cls p r)).length *
      ((typ p Z P r jmin).zs.map (fun a => Tv p r x - a)).prod *
      ((Z.filter (fun z => !cls p r z)).map (fun z => x - z)).prod := by
    rw [prod_map_split Z (cls p r)]
    congr 1
    simp only [typ, List.map_map]
    rw [← prod_map_const' (Z.filter (cls p r)) (p : ℚ), ← prod_map_mul']
    congr 1
    apply List.map_congr_left
    intro z _
    simp only [Function.comp, Tv]; field_simp; ring
  have hPrnd : (Pr.map Prod.fst).Nodup := hnd.sublist ((List.filter_sublist).map _)
  have hq0r : q0 ∈ Pr := by rw [hPr, List.mem_filter]; exact ⟨hq0, hc⟩
  have hlen : (Pr.filter (fun q => q.1 ≠ x)).length + 1 = Pr.length :=
    filter_one_length hPrnd hq0r
  have hden : ((P.filter (fun q => q.1 ≠ x)).map (fun q => q.1 - x)).prod =
      (-1) ^ (Pr.length - 1) * (p : ℚ) ^ (Pr.length - 1) *
      (((typ p Z P r jmin).ps.filter (fun q => q.1 ≠ Tv p r x)).map (fun q => Tv p r x - q.1)).prod *
      ((P.filter (fun q => !cls p r q.1)).map (fun q => q.1 - x)).prod := by
    rw [prod_map_split (P.filter (fun q => q.1 ≠ x)) (fun q => cls p r q.1)]
    have e1 : (P.filter (fun q => q.1 ≠ x)).filter (fun q => !cls p r q.1) =
        P.filter (fun q => !cls p r q.1) := by
      rw [List.filter_filter]; apply List.filter_congr; intro q _
      by_cases h : cls p r q.1
      · simp [h]
      · have : q.1 ≠ x := by intro heq; rw [heq] at h; exact h hc
        simp [h, this]
    have e2 : (P.filter (fun q => q.1 ≠ x)).filter (fun q => cls p r q.1) =
        Pr.filter (fun q => q.1 ≠ x) := by
      rw [List.filter_filter, hPr, List.filter_filter]; apply List.filter_congr; intro q _
      simp [Bool.and_comm]
    have e3 : ((typ p Z P r jmin).ps.filter (fun q => q.1 ≠ Tv p r x)) =
        (Pr.filter (fun q => q.1 ≠ x)).map (fun q => (Tv p r q.1, q.2.1)) := by
      simp only [typ]; rw [List.filter_map]; congr 1; apply List.filter_congr; intro q _
      simp [Function.comp, Tv_inj]
    rw [e1, e2, e3, List.map_map]
    congr 1
    have hl : Pr.length - 1 = (Pr.filter (fun q => q.1 ≠ x)).length := by omega
    rw [hl, ← prod_map_const' _ (-1 : ℚ), ← prod_map_const' _ (p : ℚ), ← prod_map_mul',
      ← prod_map_mul']
    congr 1; apply List.map_congr_left; intro q _
    simp only [Function.comp, Tv]; field_simp; ring
  unfold vres
  rw [hnum, hden, alg_id _ _ _ _ _ _ _ _ (by norm_num)]
  have hh : (typ p Z P r jmin).h + 1 =
      ((Z.filter (cls p r)).length : ℤ) - ((Pr.length - 1 : ℕ) : ℤ) := by
    have : 1 ≤ Pr.length := by omega
    simp only [PType.h, typ, List.length_map]
    rw [Nat.cast_sub this]; ring
  rw [hh, zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
  rfl

end

/-! ### The unit part and its Taylor representation -/

/-- `Φ(T) = ± ∏_{z ∉ r} (r - z + pT) ∏_{l ∉ r} (l - r - pT)⁻¹ · (r + pT)^k` -/
def Phi (p : ℕ) (Z : List ℚ) (P : List Rec) (r k : ℕ) (T : ℚ) : ℚ :=
  (-1) ^ ((P.filter (fun q => cls p r q.1)).length - 1) *
   ((((Z.filter (fun z => !cls p r z)).map (fun z => ((r : ℚ) - z) + p * T)).prod) *
    ((((P.filter (fun q => !cls p r q.1)).map
      (fun q => -1 * (1 / (((r : ℚ) - q.1) + p * T)))).prod) *
     ((r : ℚ) + p * T) ^ k))

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem vres_mul_pow (Z : List ℚ) (P : List Rec) (r jmin k : ℕ) (hnd : (P.map Prod.fst).Nodup)
    (q0 : Rec) (hq0 : q0 ∈ P) (hc : cls p r q0.1 = true) :
    vres Z P q0.1 * q0.1 ^ k = (p : ℚ) ^ ((typ p Z P r jmin).h + 1) *
      (typ p Z P r jmin).R (Tv p r q0.1) * Phi p Z P r k (Tv p r q0.1) := by
  rw [vres_factor Z P r jmin hnd q0 hq0 hc]
  have hp0 := p_ne_zero' (p := p)
  have hx : (r : ℚ) + p * Tv p r q0.1 = q0.1 := by simp only [Tv]; field_simp; ring
  have e1 : (Z.filter (fun z => !cls p r z)).map (fun z => ((r : ℚ) - z) + p * Tv p r q0.1) =
      (Z.filter (fun z => !cls p r z)).map (fun z => q0.1 - z) := by
    apply List.map_congr_left; intro z _; linear_combination hx
  have e2 : (P.filter (fun q => !cls p r q.1)).map
      (fun q => -1 * (1 / (((r : ℚ) - q.1) + p * Tv p r q0.1))) =
      (P.filter (fun q => !cls p r q.1)).map (fun q => 1 / (q.1 - q0.1)) := by
    apply List.map_congr_left; intro q _
    rw [show ((r : ℚ) - q.1) + p * Tv p r q0.1 = -(q.1 - q0.1) by linear_combination hx,
      one_div_neg_eq_neg_one_div]; ring
  simp only [Phi]
  rw [e1, e2, prod_map_inv', hx]
  ring

theorem mul_cond {r : ℕ} {Φ Ψ : ℚ → ℚ} {u v : Fin 6 → ℚ} (h1 : TaylorRep p Φ u)
    (h2 : TaylorRep p Ψ v) (hv : r = 0 → v 0 = 0) :
    ∃ w, TaylorRep p (fun T => Φ T * Ψ T) w ∧ (r = 0 → w 0 = 0) := by
  by_cases hr : r = 0
  · obtain ⟨w, hw, hw0⟩ := TaylorRep.mul_zero0 h1 h2 (hv hr); exact ⟨w, hw, fun _ => hw0⟩
  · obtain ⟨w, hw⟩ := TaylorRep.mul h1 h2; exact ⟨w, hw, fun h => absurd h hr⟩

theorem Phi_taylor (Z : List ℚ) (P : List Rec) (r k : ℕ) (hk : 1 ≤ k)
    (hZd : ∀ z ∈ Z, ¬ p ∣ z.den) (hPd : ∀ q ∈ P, ¬ p ∣ q.1.den) :
    ∃ u, TaylorRep p (Phi p Z P r k) u ∧ (r = 0 → u 0 = 0) := by
  obtain ⟨u1, h1⟩ := TaylorRep.const (p := p)
    ((-1 : ℚ) ^ ((P.filter (fun q => cls p r q.1)).length - 1))
    (by have := (VGe.intCast (p := p) (-1)).pow ((P.filter (fun q => cls p r q.1)).length - 1)
        simpa using this)
  obtain ⟨u2, h2⟩ := TaylorRep.list_prod (p := p) (Z.filter (fun z => !cls p r z))
    (fun z T => ((r : ℚ) - z) + p * T)
    (fun z hz => TaylorRep.linear _ ((VGe.natCast r).sub
      (VGe.of_den (hZd z (List.mem_of_mem_filter hz)))))
  obtain ⟨u3, h3⟩ := TaylorRep.list_prod (p := p) (P.filter (fun q => !cls p r q.1))
    (fun q T => -1 * (1 / (((r : ℚ) - q.1) + p * T))) (fun q hq => by
      have hd := hPd q (List.mem_of_mem_filter hq)
      have hc : cls p r q.1 = false := by simpa using (List.mem_filter.mp hq).2
      obtain ⟨a, ha⟩ := TaylorRep.const (p := p) (-1) (by simpa using VGe.intCast (p := p) (-1))
      obtain ⟨b, hb⟩ := TaylorRep.inv_linear (p := p) ((r : ℚ) - q.1)
        (unit_of_not_cls hd hc).1 (unit_of_not_cls hd hc).2
      exact TaylorRep.mul ha hb)
  obtain ⟨u4, h4, h40⟩ := TaylorRep.pow_linear (p := p) (r : ℚ) (VGe.natCast r) k
  obtain ⟨w1, hw1, hw10⟩ := mul_cond (r := r) h3 h4 (fun hr => h40 (by simp [hr]) hk)
  obtain ⟨w2, hw2, hw20⟩ := mul_cond h2 hw1 hw10
  obtain ⟨w3, hw3, hw30⟩ := mul_cond h1 hw2 hw20
  exact ⟨w3, hw3, hw30⟩

end

/-! ### Expansion, integrality of residues, summation over classes -/

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem expand {α : Type*} (L : List α) (G R b : α → ℚ) (u : Fin 6 → ℚ) (Φ : ℚ → ℚ) (c : ℤ) :
    (L.map (fun q => G q * ((p : ℚ) ^ c * R q * Φ (b q)))).sum =
      ∑ j : Fin 6, (u j * (p : ℚ) ^ (c + ((j : ℕ) : ℤ))) *
        (L.map (fun q => G q * (R q * b q ^ (j : ℕ)))).sum +
      (L.map (fun q => G q * ((p : ℚ) ^ c * R q *
        (Φ (b q) - ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * b q ^ (j : ℕ))))).sum := by
  have hp0 := p_ne_zero' (p := p)
  have key : ∀ q, G q * ((p : ℚ) ^ c * R q * Φ (b q)) =
      (∑ j : Fin 6, (u j * (p : ℚ) ^ (c + ((j : ℕ) : ℤ))) * (G q * (R q * b q ^ (j : ℕ)))) +
      G q * ((p : ℚ) ^ c * R q *
        (Φ (b q) - ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * b q ^ (j : ℕ))) := by
    intro q
    have : ∑ j : Fin 6, (u j * (p : ℚ) ^ (c + ((j : ℕ) : ℤ))) * (G q * (R q * b q ^ (j : ℕ))) =
        G q * ((p : ℚ) ^ c * R q * ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * b q ^ (j : ℕ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [zpow_add₀ hp0, zpow_natCast]; ring
    rw [this]; ring
  rw [List.map_congr_left (fun q _ => key q), sum_map_add', sum_map_fin6]
  congr 1; apply Finset.sum_congr rfl; intro j _; rw [sum_map_mul_left']

theorem R_int (Z : List ℚ) (P : List Rec) (r jmin : ℕ) (hZd : ∀ z ∈ Z, ¬ p ∣ z.den)
    (hPd : ∀ q ∈ P, ¬ p ∣ q.1.den)
    (hdiff : ∀ q ∈ P, ∀ q' ∈ P, q.1 ≠ q'.1 → padicValRat p (q.1 - q'.1) ≤ 1)
    (q0 : Rec) (hq0 : q0 ∈ P) (hc : cls p r q0.1 = true) :
    VGe p 0 ((typ p Z P r jmin).R (Tv p r q0.1)) := by
  unfold PType.R
  have hden := unit_list_prod (p := p)
    (((typ p Z P r jmin).ps.filter (fun q => q.1 ≠ Tv p r q0.1)).map (fun q => Tv p r q0.1 - q.1)) (by
      intro y hy
      simp only [typ, List.mem_map, List.mem_filter] at hy
      obtain ⟨q', ⟨⟨q, ⟨hqP, hqc⟩, rfl⟩, hne⟩, rfl⟩ := hy
      have hne' : q0.1 ≠ q.1 := by
        intro h; apply (show ¬ (Tv p r q.1 = Tv p r q0.1) by simpa using hne); rw [h]
      have e : Tv p r q0.1 - Tv p r q.1 = (q0.1 - q.1) / p := by simp only [Tv]; ring
      have h1 : VGe p 1 (q0.1 - q.1) := by
        have := (vge1_of_cls (hPd q0 hq0) hc).sub (vge1_of_cls (hPd q hqP) hqc)
        convert this using 1; ring
      have hz : q0.1 - q.1 ≠ 0 := sub_ne_zero.mpr hne'
      simp only
      rw [e]
      exact ⟨div_ne_zero hz p_ne_zero', val_div_p hz h1 (hdiff q0 hq0 q hqP hne')⟩)
  refine vge_div_unit ?_ hden.1 hden.2
  apply VGe.list_prod
  intro y hy
  simp only [typ, List.mem_map, List.mem_filter] at hy
  obtain ⟨a, ⟨z, ⟨hz, hzc⟩, rfl⟩, rfl⟩ := hy
  exact (Tv_int (hPd q0 hq0) hc).sub (Tv_int (hZd z hz) hzc)

theorem sum_classes (P : List Rec) (g : Rec → ℚ)
    (huniq : ∀ q ∈ P, ∃! r, r < p ∧ cls p r q.1 = true) :
    ∑ r ∈ Finset.range p, ((P.filter (fun q => cls p r q.1)).map g).sum = (P.map g).sum := by
  induction P with
  | nil => simp
  | cons a P ih =>
    have h1 : ∀ r, (((a :: P).filter (fun q => cls p r q.1)).map g).sum =
        (if cls p r a.1 = true then g a else 0) + ((P.filter (fun q => cls p r q.1)).map g).sum := by
      intro r; by_cases h : cls p r a.1 = true <;> simp [List.filter_cons, h]
    rw [Finset.sum_congr rfl (fun r _ => h1 r), Finset.sum_add_distrib,
      ih (fun q hq => huniq q (by simp [hq])), List.map_cons, List.sum_cons]
    congr 1
    obtain ⟨r0, ⟨hr0, hc0⟩, hu⟩ := huniq a (by simp)
    rw [Finset.sum_eq_single r0]
    · simp [hc0]
    · intro b hb hne
      have : ¬ cls p b a.1 = true := fun h => hne (hu b ⟨Finset.mem_range.mp hb, h⟩)
      simp [this]
    · intro h; exact absurd (Finset.mem_range.mpr hr0) h

theorem rowVec_sum (Z : List ℚ) (P : List Rec) (k : ℕ)
    (huniq : ∀ q ∈ P, ∃! r, r < p ∧ cls p r q.1 = true) :
    ∑ r ∈ Finset.range p, rowVec p Z P k (P.filter (fun q => cls p r q.1)) = rowVec p Z P k P := by
  funext i
  rw [Finset.sum_apply]
  fin_cases i
  · simp only [rowVec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [← Finset.mul_sum, Finset.sum_neg_distrib, sum_classes P _ huniq]
  · simp only [rowVec, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact sum_classes P _ huniq
  · simp only [rowVec]
    exact sum_classes P _ huniq
  · simp only [rowVec]
    exact sum_classes P _ huniq

end

end LA
end Zeta2L2Chi3.Arith
