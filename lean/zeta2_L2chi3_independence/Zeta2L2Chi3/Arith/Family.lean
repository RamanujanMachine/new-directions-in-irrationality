/-
# Residue classes of arithmetic families

For a prime `p ≥ 5` with `p ≡ e (mod 6)` and a family `c + i` (`i < len`, `den be ∣ 6`), the members
`s` with `s ≡ r (mod p)` (i.e. `p ∣ num (s - r)`) are exactly `r + p T` for `T` running through
`run ⌊(A_lo - r)/p⌋ ⌊(A_hi - r)/p⌋ (-be k)`, in increasing order.
-/
import Zeta2L2Chi3.Arith.Valuation

namespace Zeta2L2Chi3.Arith

theorem kinv_spec (d e : ℕ) (hd : d ∣ 6) (he : e = 1 ∨ e = 5) : d ∣ kinv d e * e + 1 := by
  have h6 : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> rcases he with rfl | rfl <;> first | decide | (exfalso; revert hd; decide)

theorem kinv_lt (d e : ℕ) (hd : 0 < d) : kinv d e < d := by
  unfold kinv
  cases h : (List.range d).find? (fun k => (k * e + 1) % d = 0) with
  | none => simpa using hd
  | some k => simpa using List.mem_range.mp (List.mem_of_find?_eq_some h)

theorem den_dvd_kinv_mul_add_one (f : Fam) (hf : f.be.den ∣ 6) (e : ℕ) (he : e = 1 ∨ e = 5)
    (p : ℕ) (hpe : p % 6 = e) : f.be.den ∣ kinv f.be.den e * p + 1 := by
  have h1 := kinv_spec _ e hf he
  obtain ⟨q, rfl⟩ : ∃ q, p = 6 * q + e := ⟨p / 6, by omega⟩
  have : kinv f.be.den e * (6 * q + e) + 1 = (kinv f.be.den e * e + 1) + 6 * (kinv f.be.den e * q) := by
    ring
  rw [this]
  exact dvd_add h1 (dvd_mul_of_dvd_left hf _)

theorem Fam.lo_val_eq (f : Fam) (hf : f.be.den ∣ 6) (e : ℕ) (he : e = 1 ∨ e = 5) (p n : ℕ)
    (hpe : p % 6 = e) : ∃ t : ℕ, (f.lo e).val n p = ((f.al * n - 1 + f.be.num * t : ℤ) : ℚ) := by
  obtain ⟨t, ht⟩ := den_dvd_kinv_mul_add_one f hf e he p hpe
  refine ⟨t, ?_⟩
  have ht' : (kinv f.be.den e : ℚ) * p + 1 = f.be.den * t := by exact_mod_cast ht
  have hnum : (f.be.den : ℚ) * f.be = f.be.num := Rat.den_mul_eq_num f.be
  simp only [Endpt.val, Fam.lo, Fam.shift]
  push_cast
  linear_combination f.be * ht' + (t : ℚ) * hnum

/-- endpoint values are integers -/
theorem Fam.lo_val_int (f : Fam) (hf : f.be.den ∣ 6) (e : ℕ) (he : e = 1 ∨ e = 5) (p n : ℕ)
    (hpe : p % 6 = e) : ∃ z : ℤ, (f.lo e).val n p = z := by
  obtain ⟨t, ht⟩ := Fam.lo_val_eq f hf e he p n hpe
  exact ⟨_, ht⟩

theorem Fam.hi_val_eq_lo (f : Fam) (e : ℕ) (p n : ℕ) :
    (f.hi e).val n p = (f.lo e).val n p + f.len n := by
  simp only [Endpt.val, Fam.hi, Fam.lo, Fam.len]
  push_cast; ring

theorem Fam.hi_val_int (f : Fam) (hf : f.be.den ∣ 6) (e : ℕ) (he : e = 1 ∨ e = 5) (p n : ℕ)
    (hpe : p % 6 = e) : ∃ z : ℤ, (f.hi e).val n p = z := by
  obtain ⟨z, hz⟩ := Fam.lo_val_int f hf e he p n hpe
  exact ⟨z + f.len n, by rw [Fam.hi_val_eq_lo, hz]; push_cast; ring⟩

/-- `p ∣ num x` can be tested on any fraction `N / D` representing `x` with `p ∤ D` -/
theorem dvd_num_iff {p : ℕ} (hp : p.Prime) (x : ℚ) (N D : ℤ) (hD : ¬ (p : ℤ) ∣ D)
    (hx : x = N / D) : (p : ℤ) ∣ x.num ↔ (p : ℤ) ∣ N := by
  have hD0 : D ≠ 0 := by rintro rfl; exact hD (dvd_zero _)
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hden : (x.den : ℤ) ∣ D := by rw [hx]; exact Zeta2L2Chi3.den_div_dvd N D
  have hpden : ¬ (p : ℤ) ∣ x.den := fun h => hD (h.trans hden)
  have key : x.num * D = N * x.den := by
    have h1 : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
    have : (x.num : ℚ) * D = N * x.den := by
      rw [h1]; nth_rewrite 1 [hx]; field_simp
    exact_mod_cast this
  constructor
  · intro h
    have : (p : ℤ) ∣ N * x.den := by rw [← key]; exact dvd_mul_of_dvd_left h D
    exact (hpI.dvd_mul.mp this).resolve_right hpden
  · intro h
    have : (p : ℤ) ∣ x.num * D := by rw [key]; exact dvd_mul_of_dvd_left h _
    exact (hpI.dvd_mul.mp this).resolve_right hD

/-- every rational with denominator prime to `p` lies in exactly one residue class `r < p` -/
theorem exists_unique_class (p : ℕ) [Fact p.Prime] (x : ℚ) (hd : ¬ p ∣ x.den) :
    ∃! r : ℕ, r < p ∧ (p : ℤ) ∣ (x - r).num := by
  have hpP : p.Prime := Fact.out
  have hdI : ¬ (p : ℤ) ∣ (x.den : ℤ) := by rwa [Int.natCast_dvd_natCast]
  have hiff : ∀ r : ℕ, (p : ℤ) ∣ (x - r).num ↔ (x.num : ZMod p) = (r : ZMod p) * (x.den : ZMod p) := by
    intro r
    rw [dvd_num_iff hpP (x - r) (x.num - r * x.den) x.den hdI (by
      have hd0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
      push_cast
      rw [eq_div_iff hd0, sub_mul, Rat.mul_den_eq_num])]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
  have hu : (x.den : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hd
  refine ⟨((x.num : ZMod p) * (x.den : ZMod p)⁻¹).val, ⟨ZMod.val_lt _, ?_⟩, ?_⟩
  · rw [hiff, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hu, mul_one]
  · rintro r ⟨hr, hrd⟩
    rw [hiff] at hrd
    have h1 : (r : ZMod p) = (x.num : ZMod p) * (x.den : ZMod p)⁻¹ := by
      rw [hrd, mul_assoc, mul_inv_cancel₀ hu, mul_one]
    have h2 := congrArg ZMod.val h1
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hr] at h2

/-- `⌊(x+1)/p⌋ = ⌊x/p⌋ + [p ∣ x+1]` -/
theorem ediv_add_one (x p : ℤ) (hp : 0 < p) :
    (x + 1) / p = x / p + if p ∣ x + 1 then 1 else 0 := by
  have h1 := Int.emod_add_mul_ediv x p
  have h2 := Int.emod_nonneg x hp.ne'
  have h3 := Int.emod_lt_of_pos x hp
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    rw [hm, Int.mul_ediv_cancel_left _ hp.ne']
    have h4 : p * (m - x / p - 1) = x % p + 1 - p := by linear_combination -hm - h1
    rcases lt_trichotomy (m - x / p - 1) 0 with h5 | h5 | h5
    · nlinarith
    · linarith
    · nlinarith
  · have h4 : x % p + 1 ≠ p := fun h' => h ⟨x / p + 1, by linear_combination -h1 + h'⟩
    rw [add_zero]
    exact ((Int.ediv_emod_unique (a := x + 1) (r := x % p + 1) (q := x / p) hp).mpr ⟨by linear_combination h1, by omega, by omega⟩).1

/-- the multiples of `p` in `(a, a + len]`, divided by `p`, in increasing order -/
theorem filter_dvd_map_ediv (a : ℤ) (len p : ℕ) (hp : 0 < p) :
    ((List.range len).filter (fun i : ℕ => decide ((p : ℤ) ∣ a + 1 + (i : ℤ)))).map
        (fun i : ℕ => (a + 1 + i) / (p : ℤ))
      = (List.range ((a + len) / (p : ℤ) - a / p).toNat).map (fun m : ℕ => a / (p : ℤ) + 1 + m) := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  induction len with
  | zero => simp
  | succ len ih =>
    have hmono : a / (p : ℤ) ≤ (a + len) / p := Int.ediv_le_ediv hpz (by omega)
    have hstep := ediv_add_one (a + len) p hpz
    have he : a + 1 + (len : ℤ) = a + len + 1 := by ring
    have he' : a + ((len + 1 : ℕ) : ℤ) = a + len + 1 := by push_cast; ring
    rw [List.range_succ, List.filter_append, List.map_append, ih, he']
    by_cases h : (p : ℤ) ∣ a + len + 1
    · simp only [h, ↓reduceIte] at hstep
      have e1 : ((a + len + 1) / (p : ℤ) - a / p).toNat = ((a + len) / (p : ℤ) - a / p).toNat + 1 := by
        rw [hstep]; omega
      rw [e1, List.range_succ, List.map_append]
      simp only [List.filter_cons, List.filter_nil, he, h, decide_true, ↓reduceIte, List.map_cons,
        List.map_nil]
      congr 2
      rw [hstep]; omega
    · simp only [h, ↓reduceIte, add_zero] at hstep
      rw [hstep]
      simp [he, h]

/-- the members of a family in the residue class `r`, with their `T`-values -/
theorem family_class (f : Fam) (hf : f.be.den ∣ 6) (e : ℕ) (he : e = 1 ∨ e = 5)
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hpe : p % 6 = e) (n r : ℕ) (hr : r < p) :
    ((List.range (f.len n)).filter (fun i => decide ((p : ℤ) ∣ (f.c n + i - r).num))).map
        (fun i => (f.c n + i - r) / p)
      = run ((f.lo e).floorAt n p r) ((f.hi e).floorAt n p r) (-(f.shift e)) := by
  have hpP : p.Prime := Fact.out
  have hp0 : 0 < p := hpP.pos
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpP
  have hpd : ¬ (p : ℤ) ∣ (f.be.den : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro h
    have h6 := h.trans hf
    have : p ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    rcases (show p = 5 ∨ p = 6 by omega) with rfl | rfl
    · norm_num at h6
    · norm_num at hpP
  obtain ⟨A, hA⟩ := Fam.lo_val_int f hf e he p n hpe
  have hAdef : (A : ℚ) = f.al * n + f.be * (kinv f.be.den e : ℚ) * p + (f.be - 1) := by
    rw [← hA]; simp only [Endpt.val, Fam.lo, Fam.shift]
  have hnum : (f.be.den : ℚ) * f.be = f.be.num := Rat.den_mul_eq_num f.be
  have hd0 : (f.be.den : ℚ) ≠ 0 := by exact_mod_cast f.be.den_ne_zero
  have hFlo : (f.lo e).floorAt n p r = (A - r) / (p : ℤ) := by
    rw [Endpt.floorAt, hA, ← Rat.floor_intCast_div_natCast]; push_cast; rfl
  have hFhi : (f.hi e).floorAt n p r = (A - r + f.len n) / (p : ℤ) := by
    rw [Endpt.floorAt, Fam.hi_val_eq_lo, hA, ← Rat.floor_intCast_div_natCast]
    congr 1; push_cast; ring
  have hmem : ∀ i : ℕ, (p : ℤ) ∣ (f.c n + i - r).num ↔ (p : ℤ) ∣ (A - r) + 1 + i := by
    intro i
    rw [dvd_num_iff hpP _ (f.be.num + f.be.den * (f.al * n + i - r)) f.be.den hpd (by
      push_cast
      rw [eq_div_iff hd0]
      simp only [Fam.c]
      linear_combination hnum)]
    have key : (f.be.den : ℤ) * ((A - r) + 1 + i)
        = (f.be.num + f.be.den * (f.al * n + i - r)) + p * (f.be.num * kinv f.be.den e) := by
      have : (f.be.den : ℚ) * ((A - r) + 1 + i)
          = (f.be.num + f.be.den * (f.al * n + i - r)) + p * (f.be.num * kinv f.be.den e) := by
        rw [hAdef]
        linear_combination ((kinv f.be.den e : ℚ) * p + 1) * hnum
      exact_mod_cast this
    constructor
    · intro h
      have : (p : ℤ) ∣ f.be.den * ((A - r) + 1 + i) := by
        rw [key]; exact dvd_add h (dvd_mul_right _ _)
      exact (hpI.dvd_mul.mp this).resolve_left hpd
    · intro h
      have : (p : ℤ) ∣ (f.be.num + f.be.den * (f.al * n + i - r)) + p * (f.be.num * kinv f.be.den e) := by
        rw [← key]; exact dvd_mul_of_dvd_right h _
      exact (dvd_add_left (dvd_mul_right _ _)).mp this
  have hval : ∀ i : ℕ, (p : ℤ) ∣ (A - r) + 1 + i →
      (f.c n + i - r) / p = ((((A - r) + 1 + i) / (p : ℤ) : ℤ) : ℚ) + -(f.shift e) := by
    intro i hi
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [Int.cast_div hi (by exact_mod_cast hp0.ne')]
    push_cast
    simp only [Fam.shift, Fam.c]
    rw [hAdef]
    field_simp
    ring
  have hL : (do let a ← List.range (f.len n); pure (a : ℚ) : List ℚ)
      = (List.range (f.len n)).map Nat.cast := by simp [List.map_eq_flatMap]
  have hL2 : ∀ N : ℕ, (do let a ← List.range N; pure (a : ℤ) : List ℤ)
      = (List.range N).map Nat.cast := by intro N; simp [List.map_eq_flatMap]
  rw [hFlo, hFhi, hL, List.filter_map, List.map_map]
  have hfilt : (List.range (f.len n)).filter
        ((fun i : ℚ => decide ((p : ℤ) ∣ (f.c n + i - r).num)) ∘ (Nat.cast : ℕ → ℚ))
      = (List.range (f.len n)).filter (fun i : ℕ => decide ((p : ℤ) ∣ (A - r) + 1 + (i : ℤ))) :=
    List.filter_congr (fun i _ => by simp only [Function.comp_apply, hmem i])
  rw [hfilt, List.map_congr_left
    (g := (fun j : ℤ => (j : ℚ) + -(f.shift e)) ∘ (fun i : ℕ => ((A - r) + 1 + (i : ℤ)) / (p : ℤ)))
    (fun i hi => by
      rw [Function.comp_apply, Function.comp_apply]
      exact hval i (by simpa using (List.mem_filter.mp hi).2)),
    ← List.map_map, filter_dvd_map_ediv (A - r) (f.len n) p hp0, run, hL2, List.map_map]
  rw [List.map_map]; rfl

end Zeta2L2Chi3.Arith
