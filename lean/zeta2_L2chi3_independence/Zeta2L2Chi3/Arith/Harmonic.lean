/-
# The harmonic weights modulo p

For a pole `ρ` in the residue class `r` with T-value `T = (ρ - r)/p`, the harmonic weight splits as
`h(ρ) - c_θ = p⁻² H(T) + G(r) + O(p)`: the `p`-divisible terms give `p⁻² H(T)`, the remaining terms
are congruent mod `p` to `G(r) - c_θ` (full periods vanish since `Σ_{a<p} a⁻² ≡ 0`).
-/
import Zeta2L2Chi3.Arith.Valuation
import Zeta2L2Chi3.Dual

namespace Zeta2L2Chi3.Arith

/-- `G(m) = Σ_{a=1}^{m} a⁻²` -/
def Gsq (m : ℕ) : ℚ := ∑ a ∈ Finset.range m, 1 / ((a : ℚ) + 1) ^ 2

/-- `3⁻¹ mod p` and `2⁻¹ mod p` in `[1, p)` -/
def inv3 (p : ℕ) : ℕ := if p % 3 = 1 then (2 * p + 1) / 3 else (p + 1) / 3
def inv2 (p : ℕ) : ℕ := (p + 1) / 2

/-- class constants of the third and half families -/
def cT (p : ℕ) : ℚ := Gsq (inv3 p - 1)
def cH (p : ℕ) : ℚ := Gsq (inv2 p - 1)

section
variable {p : ℕ} [hp : Fact p.Prime]

open Finset

/-! ### Auxiliary lemmas -/

private lemma VGe.mul0' {x y : ℚ} (hx : VGe p 0 x) (hy : VGe p 0 y) : VGe p 0 (x * y) := by
  simpa using hx.mul hy

private lemma VGe.p_one' : VGe p 1 (p : ℚ) := by
  simpa using VGe.zpow (p := p) 1

private lemma not_dvd_den_of_VGe0 {x : ℚ} (h : VGe p 0 x) : ¬ p ∣ x.den := by
  intro hd
  rcases h with h0 | h
  · subst h0
    simp only [Rat.den_zero, Nat.dvd_one] at hd
    exact hp.out.ne_one hd
  · have hnum : ¬ p ∣ x.num.natAbs := by
      intro hn
      have h1 := Nat.dvd_gcd hn hd
      rw [x.reduced] at h1
      exact hp.out.ne_one (Nat.dvd_one.mp h1)
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hnum] at h
    have := one_le_padicValNat_of_dvd (p := p) x.den_ne_zero hd
    omega

private lemma VGe1_of_cast {x : ℚ} (hd : ¬ p ∣ x.den) (h : (x : ZMod p) = 0) : VGe p 1 x := by
  rw [VGe.one_iff hd]
  rw [Rat.cast_def, div_eq_zero_iff] at h
  rcases h with h | h
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  · exact absurd ((ZMod.natCast_eq_zero_iff _ _).mp h) hd

omit hp in
private lemma padicValRat_nat_small {m : ℕ} (h0 : 0 < m) (h : m < p) :
    padicValRat p (m : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun hd => absurd (Nat.le_of_dvd h0 hd) (by omega))

private lemma inv_nat_vge0 {m : ℕ} (h0 : 0 < m) (h : m < p) : VGe p 0 (1 / (m : ℚ)) := by
  rw [one_div]
  have := VGe.inv (p := p) (x := (m : ℚ)) (by exact_mod_cast h0.ne')
  rwa [padicValRat_nat_small h0 h, neg_zero] at this

private lemma eq_of_VGe1_sub {r s : ℕ} (hr : r < p) (hs : s < p) (h : VGe p 1 ((r : ℚ) - s)) :
    r = s := by
  have e : ((r : ℚ) - s) = (((r : ℤ) - s : ℤ) : ℚ) := by push_cast; ring
  rw [e, VGe.one_iff (by rw [Rat.den_intCast]; exact hp.out.not_dvd_one), Rat.num_intCast] at h
  obtain ⟨k, hk⟩ := h
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · nlinarith
  · subst hk0; omega
  · nlinarith

private lemma cast_Gsq (m : ℕ) (hm : m < p) :
    ¬ p ∣ (Gsq m).den ∧ ((Gsq m : ℚ) : ZMod p) = ∑ a ∈ range m, (((a : ZMod p) + 1)⁻¹) ^ 2 := by
  induction m with
  | zero =>
    simp only [Gsq, range_zero, sum_empty, Rat.den_zero, Nat.dvd_one, Rat.cast_zero, and_true]
    exact hp.out.ne_one
  | succ m ih =>
    obtain ⟨hd, hc⟩ := ih (by omega)
    set q : ℚ := 1 / ((m : ℚ) + 1) ^ 2 with hq
    have hq' : q = (((m + 1) ^ 2 : ℕ) : ℚ)⁻¹ := by rw [hq]; push_cast; ring
    have hqden : q.den = (m + 1) ^ 2 := by rw [hq', Rat.inv_natCast_den_of_pos (by positivity)]
    have hpm : ¬ p ∣ (m + 1) ^ 2 := fun h => by
      have := Nat.le_of_dvd (by omega) (hp.out.dvd_of_dvd_pow h); omega
    have hqd : ((q.den : ℕ) : ZMod p) ≠ 0 := by
      rw [hqden, Ne, ZMod.natCast_eq_zero_iff]; exact hpm
    have hdd : (((Gsq m).den : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hd
    have hGs : Gsq (m + 1) = Gsq m + q := by rw [Gsq, sum_range_succ]; rfl
    have hqcast : ((q : ℚ) : ZMod p) = (((m : ZMod p) + 1)⁻¹) ^ 2 := by
      have h1 : q * (((m + 1) ^ 2 : ℕ) : ℚ) = 1 := by
        rw [hq']; field_simp
      have h2 := congrArg (fun x : ℚ => (x : ZMod p)) h1
      rw [Rat.cast_mul_of_ne_zero hqd (by simp), Rat.cast_natCast, Rat.cast_one] at h2
      push_cast at h2
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_left h2
    refine ⟨?_, ?_⟩
    · rw [hGs]; apply not_dvd_den_of_VGe0
      exact (VGe.of_den hd).add (VGe.of_den (by rw [hqden]; exact hpm))
    · rw [hGs, Rat.cast_add_of_ne_zero hdd hqd, hc, hqcast, sum_range_succ]

private lemma sum_range_zmod (f : ZMod p → ZMod p) :
    ∑ a ∈ range p, f (a : ZMod p) = ∑ x : ZMod p, f x := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.sum_bij' (fun a _ => (a : ZMod p)) (fun x _ => x.val) (by simp)
    (fun x _ => by simpa using ZMod.val_lt x) (fun a ha => ?_) (fun x _ => ZMod.natCast_zmod_val x)
    (fun _ _ => rfl)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp ha)]

private lemma sum_inv_sq_zmod (hp5 : 5 ≤ p) :
    ∑ a ∈ range (p - 1), (((a : ZMod p) + 1)⁻¹) ^ 2 = 0 := by
  have h1 : ∑ a ∈ range (p - 1), (((a : ZMod p) + 1)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
    rw [← sum_range_zmod (fun x => (x⁻¹) ^ 2)]
    have := Finset.sum_range_succ' (fun a => (((a : ℕ) : ZMod p))⁻¹ ^ 2) (p - 1)
    rw [Nat.sub_add_cancel hp.out.one_le] at this
    rw [this]
    simp
  rw [h1]
  have h2 : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
    Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x ^ 2)
  rw [h2]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]; omega

/-- `Σ_{a=1}^{p-1} a⁻² ≡ 0 (mod p)` -/
private lemma Gsq_full (hp5 : 5 ≤ p) : VGe p 1 (Gsq (p - 1)) := by
  obtain ⟨hd, hc⟩ := cast_Gsq (p := p) (p - 1) (by omega)
  exact VGe1_of_cast hd (by rw [hc]; exact sum_inv_sq_zmod hp5)

/-- `Σ_{a=1}^{(p-1)/2} a⁻² ≡ 0 (mod p)` -/
private lemma Gsq_half (hp5 : 5 ≤ p) : VGe p 1 (Gsq ((p - 1) / 2)) := by
  have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
  set h := (p - 1) / 2 with hh
  have hp2 : p - 1 = h + h := by omega
  obtain ⟨hd, hc⟩ := cast_Gsq (p := p) h (by omega)
  refine VGe1_of_cast hd ?_
  rw [hc]
  have hS := sum_inv_sq_zmod (p := p) hp5
  rw [hp2, Finset.sum_range_add] at hS
  have hrefl : ∑ x ∈ range h, (((h + x : ℕ) : ZMod p) + 1)⁻¹ ^ 2 =
      ∑ x ∈ range h, (((x : ℕ) : ZMod p) + 1)⁻¹ ^ 2 := by
    rw [← Finset.sum_range_reflect]
    refine sum_congr rfl (fun x hx => ?_)
    have hx' := mem_range.mp hx
    have e : (h + (h - 1 - x) + 1 + (x + 1) : ℕ) = p := by omega
    have e2 := congrArg (Nat.cast : ℕ → ZMod p) e
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at e2
    have : (((h + (h - 1 - x) : ℕ) : ZMod p) + 1) = -((x : ZMod p) + 1) := by
      push_cast
      linear_combination e2
    rw [this, inv_neg, neg_sq]
  rw [hrefl] at hS
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h2; have := Nat.le_of_dvd (by norm_num) h2; omega
  have : (2 : ZMod p) * ∑ x ∈ range h, (((x : ℕ) : ZMod p) + 1)⁻¹ ^ 2 = 0 := by
    rw [two_mul]; exact hS
  rcases mul_eq_zero.mp this with h3 | h3
  · exact absurd (by exact_mod_cast h3) h2
  · exact h3

private lemma Hq_eq (b : ℚ) : Hq b = ∑ i ∈ range ⌈b⌉.toNat, 1 / (b - (i : ℚ)) ^ 2 := by
  unfold Hq
  generalize ⌈b⌉.toNat = k
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ← ih, List.range_succ]; simp

private lemma Hq_of_nonpos {b : ℚ} (hb : b ≤ 0) : Hq b = 0 := by
  have h1 : ⌈b⌉.toNat = 0 := by
    have : ⌈b⌉ ≤ 0 := Int.ceil_le.mpr (by simpa using hb)
    omega
  rw [Hq_eq, h1]; simp

private lemma Hq_succ {b : ℚ} (hb : -1 < b) : Hq (b + 1) = 1 / (b + 1) ^ 2 + Hq b := by
  have h0 : 0 ≤ ⌈b⌉ := by
    have := Int.lt_ceil.mpr (show ((-1 : ℤ) : ℚ) < b by simpa using hb); omega
  have h1 : ⌈b + 1⌉.toNat = ⌈b⌉.toNat + 1 := by rw [Int.ceil_add_one]; omega
  rw [Hq_eq, Hq_eq, h1, sum_range_succ', add_comm]
  congr 1
  · simp
  · refine sum_congr rfl (fun i _ => ?_)
    push_cast
    ring_nf

/-- the general harmonic split, by induction on the number of terms -/
private theorem harm_gen (hp5 : 5 ≤ p) (θ : ℚ) (s : ℕ) (hθ0 : 0 < θ) (hθs : θ ≤ s) (hs1 : 1 ≤ s)
    (hsp : s < p) (hθ : VGe p 1 (θ - s)) (N : ℕ) : ∀ r : ℕ, r < p → VGe p 1 (θ + N - 1 - r) →
    VGe p 1 ((∑ l ∈ range N, 1 / ((l : ℚ) + θ) ^ 2) + Gsq (s - 1) -
      Hq ((θ + N - 1 - r) / p) / (p : ℚ) ^ 2 - Gsq r) := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  induction N with
  | zero =>
    intro r hr hcl
    have hrs : r = s - 1 := by
      have h1 := hθ.sub hcl
      have e : ((θ - s) - (θ + ((0 : ℕ) : ℚ) - 1 - r)) = ((r : ℚ) - ((s - 1 : ℕ) : ℚ)) := by
        push_cast [Nat.cast_sub hs1]; ring
      rw [e] at h1
      exact eq_of_VGe1_sub hr (by omega) h1
    subst hrs
    have : (θ + ((0 : ℕ) : ℚ) - 1 - ((s - 1 : ℕ) : ℚ)) / p ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hp0.le
      push_cast [Nat.cast_sub hs1]; linarith
    rw [Hq_of_nonpos this]; simp [VGe.zero]
  | succ N ih =>
    intro r' hr' hcl
    have hN : (0 : ℚ) ≤ N := N.cast_nonneg
    rcases Nat.eq_zero_or_pos r' with h0 | hpos
    · subst h0
      have hcl' : VGe p 1 (θ + N - 1 - ((p - 1 : ℕ) : ℚ)) := by
        have e : θ + N - 1 - ((p - 1 : ℕ) : ℚ) = (θ + ((N + 1 : ℕ) : ℚ) - 1 - ((0 : ℕ) : ℚ)) - p := by
          push_cast [Nat.cast_sub hp.out.one_le]; ring
        rw [e]; exact hcl.sub VGe.p_one'
      have key := (ih (p - 1) (by omega) hcl').add (Gsq_full hp5)
      have hT : (θ + N - 1 - ((p - 1 : ℕ) : ℚ)) / p = (θ + N) / p - 1 := by
        push_cast [Nat.cast_sub hp.out.one_le]; field_simp; ring
      rw [hT] at key
      have hb : -1 < (θ + N) / p - 1 := by
        have : 0 < (θ + N) / p := div_pos (by linarith) hp0
        linarith
      have hH := Hq_succ hb
      rw [sub_add_cancel] at hH
      have e2 : (θ + ((N + 1 : ℕ) : ℚ) - 1 - ((0 : ℕ) : ℚ)) / p = (θ + N) / p := by push_cast; ring
      rw [e2, hH, sum_range_succ]
      convert key using 1
      simp only [Gsq, range_zero, sum_empty]
      have : θ + N ≠ 0 := by linarith
      field_simp
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, r' = k + 1 := ⟨r' - 1, by omega⟩
      have e : θ + ((N + 1 : ℕ) : ℚ) - 1 - ((k + 1 : ℕ) : ℚ) = θ + N - 1 - k := by push_cast; ring
      rw [e] at hcl ⊢
      have key := ih k (by omega) hcl
      have hk : padicValRat p ((k : ℚ) + 1) = 0 := by
        have := padicValRat_nat_small (p := p) (m := k + 1) (by omega) hr'
        push_cast at this; exact this
      have hxy : VGe p 1 (((k : ℚ) + 1) - ((N : ℚ) + θ)) := by
        have := hcl.neg; convert this using 1; ring
      have hc := VGe.inv_sq_congr (p := p) hk (by positivity) (by positivity) hxy
      have := key.sub hc
      convert this using 1
      rw [sum_range_succ]
      simp only [Gsq, sum_range_succ]
      ring

private lemma third_vge0 (hp5 : 5 ≤ p) : VGe p 0 ((1 : ℚ) / 3) := by
  simpa using inv_nat_vge0 (p := p) (m := 3) (by norm_num) (by omega)

private lemma half_vge0 (hp5 : 5 ≤ p) : VGe p 0 ((1 : ℚ) / 2) := by
  simpa using inv_nat_vge0 (p := p) (m := 2) (by norm_num) (by omega)

private lemma inv3_spec (hp5 : 5 ≤ p) :
    1 ≤ inv3 p ∧ inv3 p < p ∧ VGe p 1 ((1 : ℚ) / 3 - inv3 p) := by
  have h3 : p % 3 ≠ 0 := by
    intro h
    have := hp.out.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h); omega
  have hthird := third_vge0 (p := p) hp5
  unfold inv3
  split_ifs with h1
  · refine ⟨by omega, by omega, ?_⟩
    have e : 3 * ((2 * p + 1) / 3) = 2 * p + 1 := by omega
    have e' : (((2 * p + 1) / 3 : ℕ) : ℚ) = (2 * p + 1) / 3 := by
      have := congrArg (Nat.cast : ℕ → ℚ) e; push_cast at this; linarith
    rw [e', show (1 : ℚ) / 3 - (2 * p + 1) / 3 = p * -(2 * (1 / 3)) by ring]
    have h2 : VGe p 0 (-(2 * ((1 : ℚ) / 3))) := (by simpa using (VGe.natCast (p := p) 2).mul0' hthird : VGe p 0 (2 * ((1 : ℚ) / 3))).neg
    simpa using VGe.p_one'.mul h2
  · refine ⟨by omega, by omega, ?_⟩
    have e : 3 * ((p + 1) / 3) = p + 1 := by omega
    have e' : (((p + 1) / 3 : ℕ) : ℚ) = (p + 1) / 3 := by
      have := congrArg (Nat.cast : ℕ → ℚ) e; push_cast at this; linarith
    rw [e', show (1 : ℚ) / 3 - (p + 1) / 3 = p * -(1 / 3) by ring]
    simpa using VGe.p_one'.mul hthird.neg

private lemma inv2_spec (hp5 : 5 ≤ p) :
    1 ≤ inv2 p ∧ inv2 p < p ∧ VGe p 1 ((1 : ℚ) / 2 - inv2 p) := by
  have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
  unfold inv2
  refine ⟨by omega, by omega, ?_⟩
  have e : 2 * ((p + 1) / 2) = p + 1 := by omega
  have e' : (((p + 1) / 2 : ℕ) : ℚ) = (p + 1) / 2 := by
    have := congrArg (Nat.cast : ℕ → ℚ) e; push_cast at this; linarith
  rw [e', show (1 : ℚ) / 2 - (p + 1) / 2 = p * -(1 / 2) by ring]
  simpa using VGe.p_one'.mul (half_vge0 hp5).neg

/-- the third family: `h(ρ) + c_T ≡ p⁻² H(T) + G(r) (mod p)` -/
theorem harm_split_T (hp5 : 5 ≤ p) (n j r : ℕ) (hbig : 144 * n + 24 < p ^ 2) (hj : j < 6 * n + 2)
    (hr : r < p) (hcls : (p : ℤ) ∣ ((tP j : ℚ) - r).num) :
    VGe p 1 ((hwT j : ℚ) + cT p - Hq (((tP j : ℚ) - r) / p) / (p : ℚ) ^ 2 - Gsq r) := by
  obtain ⟨hs1, hsp, hθ⟩ := inv3_spec (p := p) hp5
  have h0 : VGe p 0 ((tP j : ℚ) - r) := by
    unfold tP; exact ((third_vge0 hp5).add (VGe.natCast j)).sub (VGe.natCast r)
  have hcl := (VGe.one_iff (not_dvd_den_of_VGe0 h0)).mpr hcls
  have e : (tP j : ℚ) - r = 1 / 3 + ((j + 1 : ℕ) : ℚ) - 1 - r := by unfold tP; push_cast; ring
  rw [e] at hcl ⊢
  have hs1' : (1 : ℚ) ≤ inv3 p := by exact_mod_cast hs1
  have := harm_gen hp5 (1 / 3) (inv3 p) (by norm_num) (by linarith) hs1 hsp hθ (j + 1) r hr hcl
  unfold hwT cT; exact this

theorem harm_split_H (hp5 : 5 ≤ p) (n j r : ℕ) (hbig : 144 * n + 24 < p ^ 2) (hj : j < 3 * n + 2)
    (hr : r < p) (hcls : (p : ℤ) ∣ ((hP n j : ℚ) - r).num) :
    VGe p 1 ((hwH n j : ℚ) - cH p - Hq (((hP n j : ℚ) - r) / p) / (p : ℚ) ^ 2 - Gsq r) := by
  obtain ⟨hs1, hsp, hθ⟩ := inv2_spec (p := p) hp5
  have h0 : VGe p 0 ((hP n j : ℚ) - r) := by
    unfold hP
    exact ((((VGe.natCast 2).mul0' (VGe.natCast n)).add (half_vge0 hp5)).add
      (VGe.natCast j)).sub (VGe.natCast r)
  have hcl := (VGe.one_iff (not_dvd_den_of_VGe0 h0)).mpr hcls
  have e : (hP n j : ℚ) - r = 1 / 2 + ((2 * n + j + 1 : ℕ) : ℚ) - 1 - r := by
    unfold hP; push_cast; ring
  rw [e] at hcl ⊢
  have hs1' : (1 : ℚ) ≤ inv2 p := by exact_mod_cast hs1
  have hgen := harm_gen hp5 (1 / 2) (inv2 p) (by norm_num) (by linarith) hs1 hsp hθ
    (2 * n + j + 1) r hr hcl
  have hhalf : VGe p 1 (Gsq (inv2 p - 1)) := by
    have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
    have : inv2 p - 1 = (p - 1) / 2 := by unfold inv2; omega
    rw [this]; exact Gsq_half hp5
  have h2 : VGe p 1 (2 * Gsq (inv2 p - 1)) := by
    simpa using (VGe.natCast (p := p) 2).mul hhalf
  have := hgen.sub h2
  unfold hwH cH
  convert this using 1
  ring

/-- the half family in the `+` form used by Lemma A (`c_H ≡ 0 mod p`) -/
theorem harm_split_H_plus (hp5 : 5 ≤ p) (n j r : ℕ) (hbig : 144 * n + 24 < p ^ 2) (hj : j < 3 * n + 2)
    (hr : r < p) (hcls : (p : ℤ) ∣ ((hP n j : ℚ) - r).num) :
    VGe p 1 ((hwH n j : ℚ) + cH p - Hq (((hP n j : ℚ) - r) / p) / (p : ℚ) ^ 2 - Gsq r) := by
  have h1 := harm_split_H hp5 n j r hbig hj hr hcls
  have hhalf : VGe p 1 (Gsq (inv2 p - 1)) := by
    have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
    have : inv2 p - 1 = (p - 1) / 2 := by unfold inv2; omega
    rw [this]; exact Gsq_half hp5
  have h2 : VGe p 1 (2 * cH p) := by
    unfold cH; simpa using (VGe.natCast (p := p) 2).mul hhalf
  have := h1.add h2
  convert this using 1
  ring

theorem harm_split_I (hp5 : 5 ≤ p) (n j r : ℕ) (hbig : 144 * n + 24 < p ^ 2) (hj : j < 10 * n + 2)
    (hr : r < p) (hcls : (p : ℤ) ∣ ((iP n j : ℚ) - r).num) :
    VGe p 1 ((hwI n j : ℚ) - Hq (((iP n j : ℚ) - r) / p) / (p : ℚ) ^ 2 - Gsq r) := by
  have h0 : VGe p 0 ((iP n j : ℚ) - r) := by
    unfold iP
    exact (((VGe.natCast 2).mul0' (VGe.natCast n)).add (VGe.natCast j)).sub (VGe.natCast r)
  have hcl := (VGe.one_iff (not_dvd_den_of_VGe0 h0)).mpr hcls
  have e : (iP n j : ℚ) - r = 1 + ((2 * n + j : ℕ) : ℚ) - 1 - r := by
    unfold iP; push_cast; ring
  rw [e] at hcl ⊢
  have := harm_gen hp5 1 1 (by norm_num) (by norm_num) le_rfl (by omega) (by simp [VGe.zero])
    (2 * n + j) r hr hcl
  unfold hwI
  convert this using 1
  simp [Gsq]

end

end Zeta2L2Chi3.Arith
