/-
# Auxiliary lemmas for `Cell.lean`

* `floor_split'` : `⌊(A - r)/p⌋ = A / p - [A % p < r]`.
* `lin_cell` : a linear function `α t + β` (`α ∈ ℤ \ 0`) whose values at the ends of a wall-free
  cell do not straddle an integer stays (with margin) inside one unit interval.
* `assemble` : the purely order-theoretic part: if the residues `ρ_E` induce the same preorder as
  the keys, then `{E : ρ_E < r}` is a candidate set.
* `cell_floors'` : the cell theorem.
-/
import Zeta2L2Chi3.Arith.Checker

namespace Zeta2L2Chi3.Arith
namespace CellAux

open Filter

/-! ### Floors -/

theorem floor_split' (A : ℤ) (p r : ℕ) (hp : 0 < p) (hr : r < p) :
    ⌊((A : ℚ) - r) / p⌋ = A / (p : ℤ) - (if A % (p : ℤ) < r then 1 else 0) := by
  have hp' : (0:ℚ) < p := by exact_mod_cast hp
  have hpz : (0:ℤ) < p := by exact_mod_cast hp
  have h1 := Int.emod_add_mul_ediv A p
  have h2 := Int.emod_nonneg A hpz.ne'
  have h3 := Int.emod_lt_of_pos A hpz
  rw [Int.floor_eq_iff]
  generalize A / (p:ℤ) = q at h1 ⊢
  generalize A % (p:ℤ) = ρ at h1 h2 h3 ⊢
  have hA : (A:ℚ) = ρ + p * q := by exact_mod_cast h1.symm
  have hr' : (r:ℚ) < p := by exact_mod_cast hr
  have h2' : (0:ℚ) ≤ ρ := by exact_mod_cast h2
  have h3' : (ρ:ℚ) < p := by exact_mod_cast h3
  rw [hA]
  split_ifs with h
  · have h4 : ρ + 1 ≤ (r:ℤ) := Int.add_one_le_of_lt h
    have h' : (ρ:ℚ) + 1 ≤ r := by exact_mod_cast h4
    push_cast
    constructor
    · rw [le_div_iff₀ hp']; nlinarith
    · rw [div_lt_iff₀ hp']; nlinarith
  · have h4 : (r:ℤ) ≤ ρ := by omega
    have h' : (r:ℚ) ≤ ρ := by exact_mod_cast h4
    push_cast
    constructor
    · rw [le_div_iff₀ hp']; nlinarith
    · rw [div_lt_iff₀ hp']; nlinarith

/-! ### Distance to the integers -/

theorem fracQ_nonneg (x : ℚ) : 0 ≤ fracQ x := by
  unfold fracQ; linarith [Int.floor_le x]

theorem fracQ_lt_one (x : ℚ) : fracQ x < 1 := by
  unfold fracQ; linarith [Int.lt_floor_add_one x]

/-- a lower bound for the distance from `β + ℤ \ {0}` to `0` -/
def distZ (β : ℚ) : ℚ := if fracQ β = 0 then 1 else min (fracQ β) (1 - fracQ β)

theorem distZ_pos (β : ℚ) : 0 < distZ β := by
  unfold distZ; split_ifs with h
  · norm_num
  · exact lt_min (lt_of_le_of_ne (fracQ_nonneg β) (Ne.symm h)) (by linarith [fracQ_lt_one β])

theorem distZ_le (β : ℚ) (j : ℤ) (h : β - j ≠ 0) : distZ β ≤ |β - j| := by
  unfold distZ
  have hf : fracQ β = β - ⌊β⌋ := rfl
  split_ifs with h0
  · have hb : β - j = ((⌊β⌋ - j : ℤ) : ℚ) := by push_cast; linarith
    rw [hb] at h ⊢
    have h5 : (⌊β⌋ - j : ℤ) ≠ 0 := by exact_mod_cast h
    have h6 : (1:ℤ) ≤ |⌊β⌋ - j| := Int.one_le_abs h5
    rw [← Int.cast_abs]; exact_mod_cast h6
  · rcases le_or_gt j ⌊β⌋ with hj | hj
    · have h5 : (j:ℚ) ≤ ⌊β⌋ := by exact_mod_cast hj
      have hpos : fracQ β ≤ β - j := by linarith
      rw [abs_of_nonneg (by linarith [fracQ_nonneg β])]
      exact le_trans (min_le_left _ _) hpos
    · have hj' : ⌊β⌋ + 1 ≤ j := hj
      have h5 : (⌊β⌋:ℚ) + 1 ≤ j := by exact_mod_cast hj'
      have h6 : β - j ≤ fracQ β - 1 := by linarith
      rw [abs_of_neg (by linarith [fracQ_lt_one β])]
      exact le_trans (min_le_right _ _) (by linarith)

/-! ### Linear functions on a wall-free cell -/

theorem lin_cell (α : ℤ) (hα : α ≠ 0) (β lo hi x0 y ε : ℚ) (L : ℕ) (hlo : lo < x0) (hhi : x0 < hi)
    (hni : noIntBetween (α * lo + β) (α * hi + β) = true)
    (hy1 : L + lo + ε ≤ y) (hy2 : y ≤ L + hi - ε) :
    ∃ m : ℤ, (m : ℚ) < α * (L + x0) + β ∧ α * (L + x0) + β < m + 1 ∧
      m + |(α:ℚ)| * ε ≤ α * y + β ∧ α * y + β ≤ m + 1 - |(α:ℚ)| * ε := by
  unfold noIntBetween at hni
  rw [decide_eq_true_eq] at hni
  set u := (α:ℚ) * lo + β with hu
  set v := (α:ℚ) * hi + β with hv
  refine ⟨⌊min u v⌋ + α * L, ?_⟩
  have hfl := Int.floor_le (min u v)
  push_cast
  rcases lt_or_gt_of_ne hα with hneg | hpos
  · have ha : (α:ℚ) < 0 := by exact_mod_cast hneg
    have h1 : (α:ℚ) * (hi - x0) < 0 := mul_neg_of_neg_of_pos ha (by linarith)
    have h2 : (α:ℚ) * (x0 - lo) < 0 := mul_neg_of_neg_of_pos ha (by linarith)
    have h3 : (α:ℚ) * (L + hi - ε - y) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le (by linarith)
    have h4 : (α:ℚ) * (y - (L + lo + ε)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha.le (by linarith)
    have huv : v ≤ u := by rw [hu, hv]; nlinarith
    rw [min_eq_right huv] at hfl hni ⊢
    rw [max_eq_left huv] at hni
    rw [abs_of_neg ha]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · have ha : (0:ℚ) < α := by exact_mod_cast hpos
    have h1 : 0 < (α:ℚ) * (hi - x0) := mul_pos ha (by linarith)
    have h2 : 0 < (α:ℚ) * (x0 - lo) := mul_pos ha (by linarith)
    have h3 : 0 ≤ (α:ℚ) * (L + hi - ε - y) := mul_nonneg ha.le (by linarith)
    have h4 : 0 ≤ (α:ℚ) * (y - (L + lo + ε)) := mul_nonneg ha.le (by linarith)
    have huv : u ≤ v := by rw [hu, hv]; nlinarith
    rw [min_eq_left huv] at hfl hni ⊢
    rw [max_eq_right huv] at hni
    rw [abs_of_pos ha]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-! ### Endpoints -/

/-- the linear function `g_E(t) = a t + b - q*_E(x*)`; `ρ_E = p g_E(n/p) + c` -/
def gfun (E : Endpt) (xs t : ℚ) : ℚ := E.a * t + E.b - qstar E xs

theorem keyOf_fst (E : Endpt) (xs : ℚ) : (keyOf E xs).1 = gfun E xs xs := by
  unfold keyOf gfun qstar fracQ
  simp only []
  split_ifs <;> push_cast <;> linarith

theorem keyOf_snd (E : Endpt) (xs : ℚ) : (keyOf E xs).2 = E.c := by
  unfold keyOf
  simp only []
  split_ifs <;> rfl

theorem endpt_a_ne (E : Endpt) (ha : E.a ≠ 0) (lo hi x0 y ε : ℚ) (L : ℕ) (hlo : lo < x0)
    (hhi : x0 < hi) (hni : noIntBetween (E.a * lo + E.b) (E.a * hi + E.b) = true)
    (hy1 : L + lo + ε ≤ y) (hy2 : y ≤ L + hi - ε) :
    fracQ (E.a * (L + x0) + E.b) ≠ 0 ∧ |(E.a:ℚ)| * ε ≤ gfun E (L + x0) y ∧
      gfun E (L + x0) y ≤ 1 - |(E.a:ℚ)| * ε := by
  obtain ⟨m, h1, h2, h3, h4⟩ := lin_cell E.a ha E.b lo hi x0 y ε L hlo hhi hni hy1 hy2
  have hfl : ⌊(E.a:ℚ) * (L + x0) + E.b⌋ = m := by
    rw [Int.floor_eq_iff]; exact ⟨h1.le, h2⟩
  have hfr : fracQ (E.a * (L + x0) + E.b) ≠ 0 := by
    unfold fracQ; rw [hfl]; intro h; linarith
  have hq : qstar E (L + x0) = m := by unfold qstar; rw [ite_eq_right hfr, hfl]
  refine ⟨hfr, ?_, ?_⟩ <;> unfold gfun <;> rw [hq] <;> linarith

theorem rho_range (E : Endpt) (lo hi x0 y ε p K : ℚ) (L : ℕ) (hp : 0 < p) (hεK : p * ε = K)
    (hlo : lo < x0) (hhi : x0 < hi)
    (hni : E.a = 0 ∨ noIntBetween (E.a * lo + E.b) (E.a * hi + E.b) = true)
    (hy1 : L + lo + ε ≤ y) (hy2 : y ≤ L + hi - ε)
    (hK : |E.c| < K) (hP : |E.c| < p * distZ E.b) :
    0 ≤ p * gfun E (L + x0) y + E.c ∧ p * gfun E (L + x0) y + E.c < p := by
  have hc1 := le_abs_self E.c
  have hc2 := neg_abs_le E.c
  by_cases ha : E.a = 0
  · unfold gfun qstar
    rw [ha] at hni ⊢
    simp only [Int.cast_zero, zero_mul, zero_add] at hni ⊢
    unfold distZ at hP
    have hf : fracQ E.b = E.b - ⌊E.b⌋ := rfl
    split_ifs at hP ⊢ with h0 h1
    · push_cast; constructor <;> nlinarith
    · push_cast; constructor <;> nlinarith
    · have m1 := mul_le_mul_of_nonneg_left (min_le_left (fracQ E.b) (1 - fracQ E.b)) hp.le
      have m2 := mul_le_mul_of_nonneg_left (min_le_right (fracQ E.b) (1 - fracQ E.b)) hp.le
      constructor <;> nlinarith
  · have hni' : noIntBetween (E.a * lo + E.b) (E.a * hi + E.b) = true := hni.resolve_left ha
    obtain ⟨-, g1, g2⟩ := endpt_a_ne E ha lo hi x0 y ε L hlo hhi hni' hy1 hy2
    have ha1 : (1:ℚ) ≤ |(E.a:ℚ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs ha
    have hK0 : 0 ≤ K := le_trans (abs_nonneg _) hK.le
    have m1 := mul_le_mul_of_nonneg_left g1 hp.le
    have m2 := mul_le_mul_of_nonneg_left g2 hp.le
    have e1 : p * (|(E.a:ℚ)| * ε) = |(E.a:ℚ)| * K := by rw [← hεK]; ring
    have e2 : K ≤ |(E.a:ℚ)| * K := le_mul_of_one_le_left hK0 ha1
    constructor <;> nlinarith

theorem ord_abs (H Hs D p : ℚ)
    (h : (H = 0 ∧ Hs = 0) ∨ (0 < Hs ∧ |D| < p * H) ∨ (Hs < 0 ∧ p * H < -|D|)) :
    p * H + D ≤ 0 ↔ Hs < 0 ∨ (Hs = 0 ∧ D ≤ 0) := by
  have h1 := le_abs_self D
  have h2 := neg_abs_le D
  rcases h with ⟨rfl, rfl⟩ | ⟨hs, hd⟩ | ⟨hs, hd⟩
  · simp
  · constructor
    · intro h; linarith
    · rintro (h | ⟨h, _⟩) <;> linarith
  · constructor
    · intro _; left; exact hs
    · intro _; linarith

theorem rho_order (E F : Endpt) (lo hi x0 y ε p K : ℚ) (L : ℕ) (hp : 0 < p) (hεK : p * ε = K)
    (hlo : lo < x0) (hhi : x0 < hi)
    (hni : E.a = F.a ∨ noIntBetween ((E.a - F.a) * lo + (E.b - F.b))
      ((E.a - F.a) * hi + (E.b - F.b)) = true)
    (hy1 : L + lo + ε ≤ y) (hy2 : y ≤ L + hi - ε)
    (hK : |E.c - F.c| < K) (hP : |E.c - F.c| < p * distZ (E.b - F.b)) :
    p * gfun E (L + x0) y + E.c ≤ p * gfun F (L + x0) y + F.c ↔
      keyLe (keyOf E (L + x0)) (keyOf F (L + x0)) = true := by
  set xs : ℚ := L + x0 with hxs
  have hkey : keyLe (keyOf E xs) (keyOf F xs) = true ↔
      gfun E xs xs - gfun F xs xs < 0 ∨ (gfun E xs xs - gfun F xs xs = 0 ∧ E.c - F.c ≤ 0) := by
    simp only [keyLe, keyOf_fst, keyOf_snd, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · left; linarith
      · right; constructor <;> linarith
    · rintro (h | ⟨h1, h2⟩)
      · left; linarith
      · right; constructor <;> linarith
  rw [hkey]
  have hlhs : (p * gfun E xs y + E.c ≤ p * gfun F xs y + F.c) ↔
      p * (gfun E xs y - gfun F xs y) + (E.c - F.c) ≤ 0 := by
    rw [mul_sub]; constructor <;> intro h <;> linarith
  rw [hlhs]
  apply ord_abs
  have hD1 := le_abs_self (E.c - F.c)
  have hD2 := neg_abs_le (E.c - F.c)
  have hdiff : ∀ t, gfun E xs t - gfun F xs t =
      ((E.a - F.a : ℤ) : ℚ) * t + (E.b - F.b) - ((qstar E xs - qstar F xs : ℤ) : ℚ) := by
    intro t; unfold gfun; push_cast; ring
  rw [hdiff, hdiff]
  set j : ℤ := qstar E xs - qstar F xs
  by_cases hab : E.a = F.a
  · have h0 : ((E.a - F.a : ℤ) : ℚ) = 0 := by rw [hab]; simp
    rw [h0]
    simp only [zero_mul, zero_add]
    by_cases hz : E.b - F.b - (j:ℚ) = 0
    · left; exact ⟨hz, hz⟩
    · have hd := distZ_le (E.b - F.b) j hz
      have hm := mul_le_mul_of_nonneg_left hd hp.le
      rcases lt_or_gt_of_ne hz with hn | hpos
      · right; right
        rw [abs_of_neg hn] at hm
        exact ⟨hn, by linarith⟩
      · right; left
        rw [abs_of_pos hpos] at hm
        exact ⟨hpos, by linarith⟩
  · have hni' : noIntBetween (((E.a - F.a : ℤ) : ℚ) * lo + (E.b - F.b))
        (((E.a - F.a : ℤ) : ℚ) * hi + (E.b - F.b)) = true := by
      push_cast; exact hni.resolve_left hab
    have hα : E.a - F.a ≠ 0 := sub_ne_zero.mpr hab
    obtain ⟨m, h1, h2, h3, h4⟩ := lin_cell (E.a - F.a) hα (E.b - F.b) lo hi x0 y ε L hlo hhi hni'
      hy1 hy2
    have ha1 : (1:ℚ) ≤ |((E.a - F.a : ℤ) : ℚ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hα
    have hK0 : 0 ≤ K := le_trans (abs_nonneg _) hK.le
    have e2 : K ≤ |((E.a - F.a : ℤ) : ℚ)| * K := le_mul_of_one_le_left hK0 ha1
    rcases le_or_gt j m with hj | hj
    · have hj' : (j:ℚ) ≤ m := by exact_mod_cast hj
      right; left
      refine ⟨by rw [← hxs] at h1; linarith, ?_⟩
      have g1 : |((E.a - F.a : ℤ) : ℚ)| * ε ≤
          ((E.a - F.a : ℤ) : ℚ) * y + (E.b - F.b) - j := by linarith
      have m1 := mul_le_mul_of_nonneg_left g1 hp.le
      have e1 : p * (|((E.a - F.a : ℤ) : ℚ)| * ε) = |((E.a - F.a : ℤ) : ℚ)| * K := by
        rw [← hεK]; ring
      linarith
    · have hj2 : m + 1 ≤ j := hj
      have hj' : (m:ℚ) + 1 ≤ j := by exact_mod_cast hj2
      right; right
      refine ⟨by rw [← hxs] at h2; linarith, ?_⟩
      have g1 : ((E.a - F.a : ℤ) : ℚ) * y + (E.b - F.b) - j ≤
          -(|((E.a - F.a : ℤ) : ℚ)| * ε) := by linarith
      have m1 := mul_le_mul_of_nonneg_left g1 hp.le
      have e1 : p * (|((E.a - F.a : ℤ) : ℚ)| * ε) = |((E.a - F.a : ℤ) : ℚ)| * K := by
        rw [← hεK]; ring
      linarith

theorem rho_top (E : Endpt) (lo hi x0 y ε p : ℚ) (L : ℕ)
    (hlo : lo < x0) (hhi : x0 < hi)
    (hni : E.a = 0 ∨ noIntBetween (E.a * lo + E.b) (E.a * hi + E.b) = true)
    (hy1 : L + lo + ε ≤ y) (hy2 : y ≤ L + hi - ε) (ht : isTop1 E (L + x0) = true) :
    p * gfun E (L + x0) y + E.c = p - 1 := by
  unfold isTop1 at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨hf, hc⟩ := ht
  by_cases ha : E.a = 0
  · unfold gfun qstar
    rw [ite_eq_left hf, hc]
    rw [ha] at hf ⊢
    simp only [Int.cast_zero, zero_mul, zero_add] at hf ⊢
    unfold fracQ at hf
    rw [ite_eq_right (by norm_num : ¬ (0:ℚ) ≤ -1)]
    push_cast
    linear_combination p * hf
  · exact absurd hf (endpt_a_ne E ha lo hi x0 y ε L hlo hhi (hni.resolve_left ha) hy1 hy2).1

/-! ### The order-theoretic assembly -/

theorem getElem!_mem (Es : List Endpt) (i : ℕ) (hi : i < Es.length) : Es[i]! ∈ Es := by
  rw [getElem!_pos Es i hi]; exact List.getElem_mem hi

theorem assemble (Es : List Endpt) (x : ℚ) (ρ : Endpt → ℚ) (r : ℚ)
    (h0 : ∀ E ∈ Es, 0 ≤ ρ E)
    (hord : ∀ E ∈ Es, ∀ F ∈ Es, ρ E ≤ ρ F ↔ keyLe (keyOf E x) (keyOf F x) = true)
    (htop : ∀ F ∈ Es, ρ F < r → isTop1 F x = false) :
    ∃ S ∈ candSets Es x, (∀ i < Es.length, S.getD i false = decide (ρ (Es[i]!) < r)) ∧
      (r = 0 → S = Es.map (fun _ => false)) := by
  by_cases hex : ∃ F ∈ Es, ρ F < r
  · obtain ⟨F, hF, hFmax⟩ : ∃ F ∈ (Es.filter (fun E => decide (ρ E < r))).toFinset,
        ∀ E ∈ (Es.filter (fun E => decide (ρ E < r))).toFinset, ρ E ≤ ρ F := by
      obtain ⟨F0, hF0, hF0r⟩ := hex
      have hne : (Es.filter (fun E => decide (ρ E < r))).toFinset.Nonempty :=
        ⟨F0, by simp [hF0, hF0r]⟩
      exact Finset.exists_max_image _ ρ hne
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hF hFmax
    refine ⟨Es.map (fun E => keyLe (keyOf E x) (keyOf F x)), ?_, ?_, ?_⟩
    · unfold candSets
      apply List.mem_cons_of_mem
      exact List.mem_map.2 ⟨F, List.mem_filter.2 ⟨hF.1, by simp [htop F hF.1 hF.2]⟩, rfl⟩
    · intro i hi
      have hmem := getElem!_mem Es i hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, ← getElem!_pos Es i hi]
      have key := hord _ hmem F hF.1
      by_cases hlt : ρ (Es[i]!) < r
      · rw [decide_eq_true hlt]
        exact key.1 (hFmax _ ⟨hmem, hlt⟩)
      · rw [decide_eq_false hlt]
        rw [← Bool.not_eq_true]
        intro hk
        exact hlt (lt_of_le_of_lt (key.2 hk) hF.2)
    · intro hr
      have := h0 F hF.1
      linarith [hF.2]
  · refine ⟨Es.map (fun _ => false), List.mem_cons_self, ?_, fun _ => rfl⟩
    intro i hi
    push Not at hex
    have hmem := getElem!_mem Es i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
    exact (decide_eq_false (not_lt.2 (hex _ hmem))).symm

/-! ### Eventually -/

theorem ev_list {α : Type*} (l : List α) {P : α → ℕ → Prop}
    (h : ∀ a ∈ l, ∀ᶠ p in atTop, P a p) : ∀ᶠ p in atTop, ∀ a ∈ l, P a p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.forall_mem_cons] at h ⊢
    exact h.1.and (ih h.2)

theorem ev_gt (C : ℚ) : ∀ᶠ p : ℕ in atTop, C < (p : ℚ) :=
  tendsto_natCast_atTop_atTop.eventually_gt_atTop C

theorem ev_gt_mul (C d : ℚ) (hd : 0 < d) : ∀ᶠ p : ℕ in atTop, C < (p : ℚ) * d :=
  (ev_gt (C / d)).mono fun _ hp => by rwa [div_lt_iff₀ hd] at hp

/-! ### The cell theorem -/

theorem cell_floors' (e : ℕ) (Es : List Endpt) (lo hi x0 : ℚ) (hw : wallFree Es lo hi x0 = true)
    (hint : ∀ E ∈ Es, ∀ n p : ℕ, p % 6 = e → ∃ z : ℤ, E.val n p = z) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p r : ℕ, P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p → r < p →
      ∃ S ∈ candSets Es (L + x0),
        (∀ i < Es.length, (Es[i]!).floorAt n p r = floorsOf Es (L + x0) S i) ∧
        (r = 0 → S = Es.map (fun _ => false)) := by
  simp only [wallFree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at hw
  obtain ⟨⟨⟨hlo, hhi⟩, hwE⟩, hwEF⟩ := hw
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ E ∈ Es, ∀ F ∈ Es, |E.c| < K ∧ |E.c - F.c| < K := by
    have : ∀ᶠ K : ℕ in atTop, ∀ E ∈ Es, ∀ F ∈ Es, |E.c| < K ∧ |E.c - F.c| < K :=
      ev_list Es fun E _ => ev_list Es fun F _ => (ev_gt _).and (ev_gt _)
    exact this.exists
  obtain ⟨P0, hP0⟩ : ∃ P0 : ℕ, ∀ p : ℕ, P0 ≤ p → (1:ℚ) ≤ p ∧ ∀ E ∈ Es, ∀ F ∈ Es,
      |E.c| < p * distZ E.b ∧ |E.c - F.c| < p * distZ (E.b - F.b) := by
    have : ∀ᶠ p : ℕ in atTop, (1:ℚ) ≤ p ∧ ∀ E ∈ Es, ∀ F ∈ Es,
        |E.c| < p * distZ E.b ∧ |E.c - F.c| < p * distZ (E.b - F.b) :=
      ((ev_gt 0).mono fun p hp => by
          have : (0:ℕ) < p := by exact_mod_cast hp
          exact_mod_cast this).and
        (ev_list Es fun E _ => ev_list Es fun F _ =>
          (ev_gt_mul _ _ (distZ_pos _)).and (ev_gt_mul _ _ (distZ_pos _)))
    exact eventually_atTop.1 this
  refine ⟨P0, K, fun n p r hpP hpe h1 h2 hr => ?_⟩
  obtain ⟨hp1, hP⟩ := hP0 p hpP
  have hpq : (0:ℚ) < p := by linarith
  have hp0 : 0 < p := by exact_mod_cast hpq
  set y : ℚ := (n:ℚ) / p with hy
  set ε : ℚ := (K:ℚ) / p with hε
  have hεK : (p:ℚ) * ε = K := by rw [hε]; field_simp
  have hy1 : (L:ℚ) + lo + ε ≤ y := by
    rw [hy, le_div_iff₀ hpq, hε]
    have : ((L:ℚ) + lo + K / p) * p = ((L:ℚ) + lo) * p + K := by field_simp
    rw [this]; exact h1
  have hy2 : y ≤ (L:ℚ) + hi - ε := by
    rw [hy, div_le_iff₀ hpq, hε]
    have : ((L:ℚ) + hi - K / p) * p = ((L:ℚ) + hi) * p - K := by field_simp
    rw [this]; linarith
  set ρ : Endpt → ℚ := fun E => (p:ℚ) * gfun E (L + x0) y + E.c with hρ
  have hval : ∀ E : Endpt, E.val n p - p * qstar E (L + x0) = ρ E := by
    intro E; simp only [hρ, Endpt.val, gfun, hy]; field_simp; ring
  have hrange : ∀ E ∈ Es, 0 ≤ ρ E ∧ ρ E < p := fun E hE =>
    rho_range E lo hi x0 y ε p K L hpq hεK hlo hhi (hwE E hE) hy1 hy2 (hK E hE E hE).1
      (hP E hE E hE).1
  have hfloor : ∀ E ∈ Es, E.floorAt n p r = qstar E (L + x0) - (if ρ E < r then 1 else 0) := by
    intro E hE
    obtain ⟨z, hz⟩ := hint E hE n p hpe
    unfold Endpt.floorAt
    rw [hz, floor_split' z p r hp0 hr]
    have hw' : (((z - p * qstar E (L + x0) : ℤ)) : ℚ) = ρ E := by
      rw [← hval E, hz]; push_cast; ring
    obtain ⟨g1, g2⟩ := hrange E hE
    have hdm : z / (p:ℤ) = qstar E (L + x0) ∧ z % (p:ℤ) = z - p * qstar E (L + x0) := by
      rw [Int.ediv_emod_unique (by exact_mod_cast hp0)]
      refine ⟨by ring, ?_, ?_⟩
      · have : (0:ℚ) ≤ ((z - p * qstar E (L + x0) : ℤ) : ℚ) := by rw [hw']; exact g1
        exact_mod_cast this
      · have : ((z - p * qstar E (L + x0) : ℤ) : ℚ) < ((p:ℤ):ℚ) := by rw [hw']; push_cast; exact g2
        exact_mod_cast this
    rw [hdm.1, hdm.2]
    have hiff : (z - p * qstar E (L + x0) < (r:ℤ)) ↔ ρ E < r := by
      rw [← hw']; constructor <;> intro h
      · exact_mod_cast h
      · exact_mod_cast h
    by_cases hc : ρ E < r
    · rw [ite_eq_left hc, ite_eq_left (hiff.2 hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.1 h))]
  have hord : ∀ E ∈ Es, ∀ F ∈ Es, ρ E ≤ ρ F ↔
      keyLe (keyOf E (L + x0)) (keyOf F (L + x0)) = true := fun E hE F hF =>
    rho_order E F lo hi x0 y ε p K L hpq hεK hlo hhi (hwEF E hE F hF) hy1 hy2 (hK E hE F hF).2
      (hP E hE F hF).2
  have htop : ∀ F ∈ Es, ρ F < r → isTop1 F (L + x0) = false := by
    intro F hF hlt
    rw [← Bool.not_eq_true]
    intro ht
    have := rho_top F lo hi x0 y ε p L hlo hhi (hwE F hF) hy1 hy2 ht
    have hr' : (r:ℚ) + 1 ≤ p := by exact_mod_cast hr
    have : ρ F = p - 1 := this
    linarith
  obtain ⟨S, hS, hget, hr0⟩ := assemble Es (L + x0) ρ r (fun E hE => (hrange E hE).1) hord htop
  refine ⟨S, hS, fun i hi => ?_, fun h => hr0 (by rw [h]; simp)⟩
  rw [hfloor _ (getElem!_mem Es i hi)]
  unfold floorsOf
  rw [hget i hi]
  simp only [decide_eq_true_eq]

/-- at `r = 0` only the single-endpoint wall conditions are needed -/
theorem cell_floors_zero1' (e : ℕ) (Es : List Endpt) (lo hi x0 : ℚ)
    (hw : wallFree1 Es lo hi x0 = true)
    (_hint : ∀ E ∈ Es, ∀ n p : ℕ, p % 6 = e → ∃ z : ℤ, E.val n p = z) (L : ℕ) :
    ∃ P0 K : ℕ, ∀ n p : ℕ, P0 ≤ p → p % 6 = e →
      ((L : ℚ) + lo) * p + K ≤ n → (n : ℚ) + K ≤ ((L : ℚ) + hi) * p →
      ∀ E ∈ Es, E.floorAt n p 0 = qstar E (L + x0) := by
  simp only [wallFree1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at hw
  obtain ⟨⟨hlo, hhi⟩, hwE⟩ := hw
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ E ∈ Es, |E.c| < K :=
    (ev_list Es fun E _ => ev_gt _).exists
  obtain ⟨P0, hP0⟩ : ∃ P0 : ℕ, ∀ p : ℕ, P0 ≤ p → (1:ℚ) ≤ p ∧ ∀ E ∈ Es,
      |E.c| < p * distZ E.b := by
    have : ∀ᶠ p : ℕ in atTop, (1:ℚ) ≤ p ∧ ∀ E ∈ Es, |E.c| < p * distZ E.b :=
      ((ev_gt 0).mono fun p hp => by
          have : (0:ℕ) < p := by exact_mod_cast hp
          exact_mod_cast this).and
        (ev_list Es fun E _ => ev_gt_mul _ _ (distZ_pos _))
    exact eventually_atTop.1 this
  refine ⟨P0, K, fun n p hpP hpe h1 h2 E hE => ?_⟩
  obtain ⟨hp1, hP⟩ := hP0 p hpP
  have hpq : (0:ℚ) < p := by linarith
  set y : ℚ := (n:ℚ) / p with hy
  set ε : ℚ := (K:ℚ) / p with hε
  have hεK : (p:ℚ) * ε = K := by rw [hε]; field_simp
  have hy1 : (L:ℚ) + lo + ε ≤ y := by
    rw [hy, le_div_iff₀ hpq, hε]
    have : ((L:ℚ) + lo + K / p) * p = ((L:ℚ) + lo) * p + K := by field_simp
    rw [this]; exact h1
  have hy2 : y ≤ (L:ℚ) + hi - ε := by
    rw [hy, div_le_iff₀ hpq, hε]
    have : ((L:ℚ) + hi - K / p) * p = ((L:ℚ) + hi) * p - K := by field_simp
    rw [this]; linarith
  have hval : E.val n p - p * qstar E (L + x0) = (p:ℚ) * gfun E (L + x0) y + E.c := by
    simp only [Endpt.val, gfun, hy]; field_simp; ring
  obtain ⟨g1, g2⟩ := rho_range E lo hi x0 y ε p K L hpq hεK hlo hhi (hwE E hE) hy1 hy2
    (hK E hE) (hP E hE)
  unfold Endpt.floorAt
  rw [Int.floor_eq_iff, Nat.cast_zero, sub_zero, le_div_iff₀ hpq, div_lt_iff₀ hpq]
  constructor <;> nlinarith

end CellAux
end Zeta2L2Chi3.Arith
