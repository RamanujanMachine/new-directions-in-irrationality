/-
# Valuations of the explicit forward coefficients at a large prime

For a prime `p ≥ 7` with `p² > 144n + 24` and a pole `k` of `R_n` in the residue class
`r = k mod p`, every factor `k - z`, `k - l` of `N(k)/D_k(k)` is a nonzero rational with
denominator `1, 2` or `3` and numerator of absolute value `< p²`, so its valuation is `1` if it lies
in the class of `r` and `0` otherwise.  Counting the class members of each family with
`family_class` gives `v_p(N(k)/D_k(k)) = h(r) + e_k`, where `h(r) = fwdH (floors at r)`.
Consequently `v_p(a_k) ≥ h + 2`, `v_p(b_k) ≥ h + 1`.
-/
import Zeta2L2Chi3.Arith.FwdRat
import Zeta2L2Chi3.Arith.Family

open Finset

noncomputable section

namespace Zeta2L2Chi3.Arith

/-! ### Generic valuation lemmas -/

section generic
variable {p : ℕ} [hp : Fact p.Prime]

theorem natAbs_lt_of {a : ℤ} {B : ℕ} (h1 : a < B) (h2 : -(B : ℤ) < a) : a.natAbs < B := by
  rcases Int.natAbs_eq a with h | h <;> omega

theorem val_small {x : ℚ} {a : ℤ} {d : ℕ} (hd : 0 < d) (hpd : ¬ p ∣ d) (hxa : x * d = a)
    (ha0 : a ≠ 0) (hap : a.natAbs < p ^ 2) : padicValRat p x = if (p : ℤ) ∣ a then 1 else 0 := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hx : x = (a : ℚ) / (d : ℚ) := by rw [← hxa]; field_simp
  rw [hx, padicValRat.div (by exact_mod_cast ha0) hd0, padicValRat.of_int, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hpd]
  split_ifs with h
  · have h1 := (padicValInt_dvd_iff (p := p) 1 a).1 (by simpa using h)
    have h2 : ¬ (2 ≤ padicValInt p a) := by
      intro h2
      have h3 := (padicValInt_dvd_iff (p := p) 2 a).2 (Or.inr h2)
      have h4 : p ^ 2 ∣ a.natAbs := by
        have := Int.natAbs_dvd_natAbs.2 h3
        simpa [Int.natAbs_pow] using this
      have := Nat.le_of_dvd (Int.natAbs_pos.2 ha0) h4
      omega
    rcases h1 with h1 | h1
    · exact absurd h1 ha0
    · push_cast; omega
  · rw [padicValInt.eq_zero_of_not_dvd h]; simp

theorem factor_val (k : ℤ) (r : ℕ) (hkr : (p : ℤ) ∣ k - r) (s : ℚ) (a : ℤ) (d : ℕ) (hd : 0 < d)
    (hpd : ¬ p ∣ d) (hs : ((k : ℚ) - s) * d = a) (ha0 : a ≠ 0) (hap : a.natAbs < p ^ 2) :
    padicValRat p ((k : ℚ) - s) = if (p : ℤ) ∣ (s - r).num then 1 else 0 := by
  rw [val_small hd hpd hs ha0 hap]
  have hD : ¬ (p : ℤ) ∣ (d : ℤ) := by rwa [Int.natCast_dvd_natCast]
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have key := dvd_num_iff hp.out (s - r) ((k - r) * d - a) d hD (by
    push_cast; rw [eq_div_iff hd0]; linear_combination -hs)
  have h1 : (p : ℤ) ∣ (k - r) * d := dvd_mul_of_dvd_left hkr _
  have key2 : (p : ℤ) ∣ (k - r) * d - a ↔ (p : ℤ) ∣ a := by
    constructor
    · intro h; have := dvd_sub h1 h; simpa using this
    · intro h; exact dvd_sub h1 h
  simp only [key, key2]

theorem pvr_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a s))
      (prod_ne_zero_iff.2 fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

theorem fwd_sum_ite_eq_length (m : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ i ∈ range m, (if P i then (1 : ℤ) else 0) =
      (((List.range m).filter (fun i => decide (P i))).length : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, List.range_succ, List.filter_append]
    by_cases h : P m <;> simp [h]

theorem p_mod_six (hp5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).1 h; omega
  omega

theorem fwd_floorAt_mono (f : Fam) (e n r : ℕ) :
    (f.lo e).floorAt n p r ≤ (f.hi e).floorAt n p r := by
  unfold Endpt.floorAt
  apply Int.floor_le_floor
  rw [Fam.hi_val_eq_lo]
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  apply div_le_div_of_nonneg_right _ hp0.le
  have : (0 : ℚ) ≤ f.len n := Nat.cast_nonneg _
  linarith

/-- the number of members of a family in the class of `r` -/
theorem fwd_fam_count (f : Fam) (hf : f.be.den ∣ 6) (hp5 : 5 ≤ p) (n r : ℕ) (hr : r < p) :
    ∑ i ∈ range (f.len n), (if (p : ℤ) ∣ (f.c n + i - r).num then (1 : ℤ) else 0) =
      (f.hi (p % 6)).floorAt n p r - (f.lo (p % 6)).floorAt n p r := by
  rw [fwd_sum_ite_eq_length]
  have h := congrArg List.length (family_class f hf (p % 6) (p_mod_six hp5) p hp5 rfl n r hr)
  have hL : (do let a ← List.range (f.len n); pure (a : ℚ) : List ℚ) =
      (List.range (f.len n)).map Nat.cast := by simp [List.map_eq_flatMap]
  rw [List.length_map, hL, List.filter_map, List.length_map] at h
  have h' : ((List.range (f.len n)).filter
      (fun i : ℕ => decide ((p : ℤ) ∣ (f.c n + i - r).num))).length = _ := h
  have hL2 : ∀ N : ℕ, (do let a ← List.range N; pure (a : ℤ) : List ℤ) =
      (List.range N).map Nat.cast := by intro N; simp [List.map_eq_flatMap]
  rw [h', run, List.length_map, hL2, List.length_map, List.length_range]
  have := fwd_floorAt_mono (p := p) f (p % 6) n r
  omega

/-- a family product of factors with valuation `[class r]` -/
theorem famprod_val (f : Fam) (hf : f.be.den ∣ 6) (hp5 : 5 ≤ p) (n r : ℕ) (hr : r < p) (k : ℤ)
    (hkr : (p : ℤ) ∣ k - r) (d : ℕ) (hd : 0 < d) (hpd : ¬ p ∣ d) (A : ℕ → ℤ)
    (hA : ∀ i < f.len n, ((k : ℚ) - (f.c n + i)) * d = A i) (hA0 : ∀ i < f.len n, A i ≠ 0)
    (hAp : ∀ i < f.len n, (A i).natAbs < p ^ 2) :
    padicValRat p (∏ i ∈ range (f.len n), ((k : ℚ) - (f.c n + i))) =
      (f.hi (p % 6)).floorAt n p r - (f.lo (p % 6)).floorAt n p r := by
  rw [pvr_prod, ← fwd_fam_count f hf hp5 n r hr]
  · refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [factor_val k r hkr _ (A i) d hd hpd (hA i hi') (hA0 i hi') (hAp i hi')]
  · intro i hi h
    have hi' := mem_range.1 hi
    have := hA i hi'
    rw [h, zero_mul, eq_comm, Int.cast_eq_zero] at this
    exact hA0 i hi' this

/-- the pole-family version: the factor at `k` itself is replaced by `1` -/
theorem famprod_val_pole (f : Fam) (hf0 : f.be = 0) (hp5 : 5 ≤ p) (n r : ℕ) (hr : r < p) (k : ℤ)
    (hkr : (p : ℤ) ∣ k - r) (hA : ∀ i < f.len n, (k - (f.al * n + i)).natAbs < p ^ 2) :
    padicValRat p (∏ i ∈ range (f.len n),
        (if f.al * n + (i : ℤ) = k then (1 : ℚ) else (k : ℚ) - ((f.al * n + i : ℤ) : ℚ))) =
      (f.hi (p % 6)).floorAt n p r - (f.lo (p % 6)).floorAt n p r -
        (if f.al * n ≤ k ∧ k < f.al * n + f.len n then 1 else 0) := by
  have hf : f.be.den ∣ 6 := by rw [hf0]; decide
  have hc : ∀ i : ℕ, f.c n + i = ((f.al * n + i : ℤ) : ℚ) := fun i => by
    simp [Fam.c, hf0]
  rw [pvr_prod, ← fwd_fam_count f hf hp5 n r hr]
  · have hsum : ∑ i ∈ range (f.len n), (if f.al * n + (i : ℤ) = k then (1 : ℤ) else 0) =
        if f.al * n ≤ k ∧ k < f.al * n + f.len n then 1 else 0 := by
      split_ifs with h
      · rw [sum_eq_single (k - f.al * n).toNat]
        · rw [if_pos (by omega)]
        · intro b _ hb; rw [if_neg (by omega)]
        · intro hb; exfalso; exact hb (mem_range.2 (by omega))
      · exact sum_eq_zero fun i hi => by have := mem_range.1 hi; rw [if_neg (by omega)]
    rw [← hsum, ← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    by_cases hik : f.al * n + (i : ℤ) = k
    · rw [if_pos hik, if_pos hik, padicValRat.one, hc]
      have : (p : ℤ) ∣ (((f.al * n + i : ℤ) : ℚ) - r).num := by
        rw [show (((f.al * n + i : ℤ) : ℚ) - r) = ((f.al * n + i - r : ℤ) : ℚ) by push_cast; ring,
          Rat.num_intCast, hik]
        exact hkr
      rw [if_pos this]; simp
    · rw [if_neg hik, if_neg hik, ← hc i]
      rw [factor_val k r hkr _ (k - (f.al * n + i)) 1 one_pos (Nat.Prime.not_dvd_one hp.out)
        (by rw [hc]; push_cast; ring) (by omega) (hA i hi')]
      simp
  · intro i _
    split_ifs with h
    · exact one_ne_zero
    · rw [sub_ne_zero]; intro h'; exact h (by exact_mod_cast h'.symm)

end generic

/-! ### The forward families -/

def famZ0 : Fam := ⟨-12, -1, 10, 1⟩
def famZ1 : Fam := ⟨-6, -4 / 3, 6, 1⟩
def famZ2 : Fam := ⟨-5, -3 / 2, 3, 1⟩
def famP0 : Fam := ⟨0, 0, 10, 2⟩
def famP1 : Fam := ⟨-1, 0, 9, 2⟩

lemma fwdH_eq (n p r e : ℕ) :
    fwdH (fun E => ((endpts (fwdZ ++ fwdP) e)[E]!).floorAt n p r) =
      ((famZ0.hi e).floorAt n p r - (famZ0.lo e).floorAt n p r) +
      ((famZ1.hi e).floorAt n p r - (famZ1.lo e).floorAt n p r) +
      ((famZ2.hi e).floorAt n p r - (famZ2.lo e).floorAt n p r) -
      ((famP0.hi e).floorAt n p r - (famP0.lo e).floorAt n p r) -
      ((famP1.hi e).floorAt n p r - (famP1.lo e).floorAt n p r) := rfl

lemma prod_range_rev (m : ℕ) (A : ℚ) :
    ∏ i ∈ range m, (A + i) = ∏ i ∈ range m, (A + ((m : ℚ) - 1) - i) := by
  rw [← prod_range_reflect]
  refine prod_congr rfl fun i hi => ?_
  have := mem_range.1 hi
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

lemma NF_fam (n : ℕ) (k : ℤ) : NF n (k : ℚ) =
    (∏ i ∈ range (famZ0.len n), ((k : ℚ) - (famZ0.c n + i))) *
    (∏ i ∈ range (famZ1.len n), ((k : ℚ) - (famZ1.c n + i))) *
    (∏ i ∈ range (famZ2.len n), ((k : ℚ) - (famZ2.c n + i))) := by
  unfold NF rf
  simp only [famZ0, famZ1, famZ2, Fam.len, Fam.c]
  rw [prod_range_rev (10 * n + 1), prod_range_rev (6 * n + 1), prod_range_rev (3 * n + 1)]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_ <;>
    exact prod_congr rfl fun i _ => by push_cast; ring

lemma DF_fam (n : ℕ) (k : ℤ) (hk : k ∈ KZ n) : DF n k (k : ℚ) =
    (∏ i ∈ range (famP0.len n),
        (if famP0.al * n + (i : ℤ) = k then (1 : ℚ) else (k : ℚ) - ((famP0.al * n + i : ℤ) : ℚ))) *
    (∏ i ∈ range (famP1.len n),
        (if famP1.al * n + (i : ℤ) = k then (1 : ℚ) else (k : ℚ) - ((famP1.al * n + i : ℤ) : ℚ))) := by
  set g : ℤ → ℚ := fun l => if l = k then 1 else (k : ℚ) - l with hg
  have h1 : DF n k (k : ℚ) = ∏ l ∈ KZ n, g l ^ eZ n l := by
    rw [← mul_prod_erase _ _ hk, hg]
    simp only [if_true, one_pow, one_mul]
    exact prod_congr rfl fun l hl => by rw [if_neg (ne_of_mem_erase hl)]
  rw [h1, prod_KZ_pow]
  simp only [famP0, famP1, Fam.len, hg]
  congr 1
  · exact prod_congr rfl fun i _ => by push_cast; simp
  · exact prod_congr rfl fun i _ => by push_cast; congr 1 <;> ring_nf

/-! ### The valuation of `N(k)/D_k(k)` -/

section large
variable {p : ℕ} [hp : Fact p.Prime]

theorem vNF (hp5 : 5 ≤ p) (n : ℕ) (hbig : 144 * n + 24 < p ^ 2) (k : ℤ) (hk : k ∈ KZ n) (r : ℕ)
    (hr : r < p) (hkr : (p : ℤ) ∣ k - r) :
    padicValRat p (NF n (k : ℚ)) =
      ((famZ0.hi (p % 6)).floorAt n p r - (famZ0.lo (p % 6)).floorAt n p r) +
      ((famZ1.hi (p % 6)).floorAt n p r - (famZ1.lo (p % 6)).floorAt n p r) +
      ((famZ2.hi (p % 6)).floorAt n p r - (famZ2.lo (p % 6)).floorAt n p r) := by
  rw [mem_KZ] at hk
  have hb : (144 * n + 24 : ℤ) < ((p ^ 2 : ℕ) : ℤ) := by exact_mod_cast hbig
  have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h0 : NF n (k : ℚ) ≠ 0 := NF_ne_zero n k (mem_KZ.2 hk)
  rw [NF_fam] at h0 ⊢
  have hn1 := left_ne_zero_of_mul h0
  have hn2 := left_ne_zero_of_mul hn1
  have hn3 := right_ne_zero_of_mul hn1
  have hn4 := right_ne_zero_of_mul h0
  rw [padicValRat.mul hn1 hn4, padicValRat.mul hn2 hn3]
  have a0 : ∀ i < famZ0.len n, ((k : ℚ) - (famZ0.c n + i)) * (1 : ℕ) =
      ((k + 12 * (n : ℤ) + 1 - (i : ℤ) : ℤ) : ℚ) := by
    intro i _; simp [famZ0, Fam.c]; ring
  have a1 : ∀ i < famZ1.len n, ((k : ℚ) - (famZ1.c n + i)) * (3 : ℕ) =
      ((3 * k + 18 * (n : ℤ) + 4 - 3 * (i : ℤ) : ℤ) : ℚ) := by
    intro i _; simp [famZ1, Fam.c]; ring
  have a2 : ∀ i < famZ2.len n, ((k : ℚ) - (famZ2.c n + i)) * (2 : ℕ) =
      ((2 * k + 10 * (n : ℤ) + 3 - 2 * (i : ℤ) : ℤ) : ℚ) := by
    intro i _; simp [famZ2, Fam.c]; ring
  have z0 : ∀ i < famZ0.len n, (k + 12 * (n : ℤ) + 1 - (i : ℤ)) ≠ 0 := by
    intro i hi; simp only [famZ0, Fam.len] at hi; omega
  have z1 : ∀ i < famZ1.len n, (3 * k + 18 * (n : ℤ) + 4 - 3 * (i : ℤ)) ≠ 0 := by
    intro i hi; simp only [famZ1, Fam.len] at hi; omega
  have z2 : ∀ i < famZ2.len n, (2 * k + 10 * (n : ℤ) + 3 - 2 * (i : ℤ)) ≠ 0 := by
    intro i hi; simp only [famZ2, Fam.len] at hi; omega
  generalize hP : p ^ 2 = P at hb
  have b0 : ∀ i < famZ0.len n, (k + 12 * (n : ℤ) + 1 - (i : ℤ)).natAbs < P := by
    intro i hi; simp only [famZ0, Fam.len] at hi; apply natAbs_lt_of <;> omega
  have b1 : ∀ i < famZ1.len n, (3 * k + 18 * (n : ℤ) + 4 - 3 * (i : ℤ)).natAbs < P := by
    intro i hi; simp only [famZ1, Fam.len] at hi; apply natAbs_lt_of <;> omega
  have b2 : ∀ i < famZ2.len n, (2 * k + 10 * (n : ℤ) + 3 - 2 * (i : ℤ)).natAbs < P := by
    intro i hi; simp only [famZ2, Fam.len] at hi; apply natAbs_lt_of <;> omega
  subst hP
  rw [famprod_val famZ0 (by decide) hp5 n r hr k hkr 1 one_pos (Nat.Prime.not_dvd_one hp.out) _ a0 z0 b0,
    famprod_val famZ1 (by norm_num [famZ1]) hp5 n r hr k hkr 3 (by norm_num) hp3 _ a1 z1 b1,
    famprod_val famZ2 (by norm_num [famZ2]) hp5 n r hr k hkr 2 (by norm_num) hp2 _ a2 z2 b2]

theorem vDF (hp5 : 5 ≤ p) (n : ℕ) (hbig : 144 * n + 24 < p ^ 2) (k : ℤ) (hk : k ∈ KZ n) (r : ℕ)
    (hr : r < p) (hkr : (p : ℤ) ∣ k - r) :
    padicValRat p (DF n k (k : ℚ)) =
      ((famP0.hi (p % 6)).floorAt n p r - (famP0.lo (p % 6)).floorAt n p r) +
      ((famP1.hi (p % 6)).floorAt n p r - (famP1.lo (p % 6)).floorAt n p r) - eZ n k := by
  have hk' := mem_KZ.1 hk
  have hb : (144 * n + 24 : ℤ) < ((p ^ 2 : ℕ) : ℤ) := by exact_mod_cast hbig
  have h0 : DF n k (k : ℚ) ≠ 0 := DF_self_ne_zero n k
  rw [DF_fam n k hk] at h0 ⊢
  generalize hP : p ^ 2 = P at hb
  have b0 : ∀ i < famP0.len n, (k - (famP0.al * n + i)).natAbs < P := by
    intro i hi; simp only [famP0, Fam.len] at hi ⊢; apply natAbs_lt_of <;> omega
  have b1 : ∀ i < famP1.len n, (k - (famP1.al * n + i)).natAbs < P := by
    intro i hi; simp only [famP1, Fam.len] at hi ⊢; apply natAbs_lt_of <;> omega
  subst hP
  rw [padicValRat.mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0),
    famprod_val_pole famP0 rfl hp5 n r hr k hkr b0, famprod_val_pole famP1 rfl hp5 n r hr k hkr b1]
  simp only [famP0, famP1, Fam.len, eZ]
  split_ifs <;> push_cast <;> omega

theorem vND (hp5 : 5 ≤ p) (n : ℕ) (hbig : 144 * n + 24 < p ^ 2) (k : ℤ) (hk : k ∈ KZ n) (r : ℕ)
    (hr : r < p) (hkr : (p : ℤ) ∣ k - r) :
    padicValRat p (NF n (k : ℚ) / DF n k (k : ℚ)) =
      fwdH (fun E => ((endpts (fwdZ ++ fwdP) (p % 6))[E]!).floorAt n p r) + eZ n k := by
  rw [padicValRat.div (NF_ne_zero n k hk) (DF_self_ne_zero n k), vNF hp5 n hbig k hk r hr hkr,
    vDF hp5 n hbig k hk r hr hkr, fwdH_eq]
  ring

/-! ### Consequences for `a_k`, `b_k` -/

/-- `1/y` for `y` with a small numerator -/
theorem vge_inv_small {y : ℚ} {a : ℤ} {d : ℕ} (hd : 0 < d) (hpd : ¬ p ∣ d) (hya : y * d = a)
    (hap : a.natAbs < p ^ 2) (j : ℕ) : VGe p (-(j : ℤ)) (1 / y ^ j) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · right; subst hj; simp
  by_cases ha : a = 0
  · left
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have : y = 0 := by
      rw [ha, Int.cast_zero] at hya
      exact (mul_eq_zero.1 hya).resolve_right hd0
    simp [this, zero_pow_eq, hj.ne']
  · have hy : y ≠ 0 := by
      rintro rfl; rw [zero_mul, eq_comm, Int.cast_eq_zero] at hya; exact ha hya
    right
    rw [one_div, padicValRat.inv, padicValRat.pow, val_small hd hpd hya ha hap]
    split_ifs <;> simp

end large

end Zeta2L2Chi3.Arith
