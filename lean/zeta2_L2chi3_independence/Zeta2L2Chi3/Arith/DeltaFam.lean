/-
# Valuations of the rising factorials `(β)_N` of the gamma factorization of `Δ_n`
-/
import Zeta2L2Chi3.Arith.DeltaLeg
import Zeta2L2Chi3.Arith.Family
import Zeta2L2Chi3.Dual

open Finset

namespace Zeta2L2Chi3.Arith

open Zeta2L2Chi3

lemma padicValRat_prod_range (q : ℕ) [Fact q.Prime] (f : ℕ → ℚ) (N : ℕ)
    (h : ∀ i < N, f i ≠ 0) :
    padicValRat q (∏ i ∈ range N, f i) = ∑ i ∈ range N, padicValRat q (f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prod_range_succ, sum_range_succ,
      padicValRat.mul (prod_ne_zero_iff.2 fun i hi => h i (by simp at hi; omega)) (h N (by omega)),
      ih fun i hi => h i (by omega)]

lemma padicValRat_list_prod (q : ℕ) [Fact q.Prime] (l : List ℚ) (h : ∀ x ∈ l, x ≠ 0) :
    padicValRat q l.prod = (l.map (padicValRat q)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl : l.prod ≠ 0 := List.prod_ne_zero fun h0 => h 0 (List.mem_cons_of_mem _ h0) rfl
    rw [List.prod_cons, List.map_cons, List.sum_cons, padicValRat.mul (h a (by simp)) hl,
      ih fun x hx => h x (by simp [hx])]

/-- the numerator of a positive `β`, as a natural number -/
def Fam.u (f : Fam) : ℕ := f.be.num.toNat

lemma Fam.u_pos (f : Fam) (h : 0 < f.be) : 0 < f.u := by
  have := Rat.num_pos.2 h
  unfold Fam.u; omega

lemma Fam.be_eq (f : Fam) (h : 0 < f.be) : f.be = (f.u : ℚ) / (f.be.den : ℚ) := by
  have hn : 0 < f.be.num := Rat.num_pos.2 h
  rw [show ((f.u : ℕ) : ℚ) = (f.be.num : ℚ) by
    unfold Fam.u; exact_mod_cast Int.toNat_of_nonneg hn.le]
  exact (Rat.num_div_den _).symm

lemma Fam.term_eq (f : Fam) (h : 0 < f.be) (i : ℕ) :
    f.be + i = ((f.u + f.be.den * i : ℕ) : ℚ) / f.be.den := by
  have hd : (f.be.den : ℚ) ≠ 0 := by exact_mod_cast f.be.den_ne_zero
  conv_lhs => rw [f.be_eq h]
  push_cast
  field_simp

/-- `v_q((β)_N) = Σ_{i<N} v_q(u + d i) - N v_q(d)` for `β = u/d > 0` -/
lemma rf_val (q : ℕ) [Fact q.Prime] (f : Fam) (h : 0 < f.be) (N : ℕ) :
    padicValRat q (rf f.be N) =
      ∑ i ∈ range N, (padicValNat q (f.u + f.be.den * i) : ℤ) - N * padicValNat q f.be.den := by
  have hu := f.u_pos h
  unfold rf
  rw [padicValRat_prod_range q _ N (fun i _ => by
    have : (0 : ℚ) ≤ i := by positivity
    exact ne_of_gt (by linarith))]
  have : ∀ i ∈ range N, padicValRat q (f.be + i) =
      (padicValNat q (f.u + f.be.den * i) : ℤ) - padicValNat q f.be.den := by
    intro i _
    rw [f.term_eq h i, padicValRat.div (by positivity) (by exact_mod_cast f.be.den_ne_zero),
      padicValRat.of_nat, padicValRat.of_nat]
  rw [sum_congr rfl this, sum_sub_distrib]
  simp

lemma rf_val_real (q : ℕ) [Fact q.Prime] (f : Fam) (h : 0 < f.be) (N : ℕ) :
    (padicValRat q (rf f.be N) : ℝ) =
      ∑ i ∈ range N, (padicValNat q (f.u + f.be.den * i) : ℝ) - N * padicValNat q f.be.den := by
  rw [rf_val q f h N]
  simp only [Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

lemma rf_ne_zero (f : Fam) (h : 0 < f.be) (N : ℕ) : rf f.be N ≠ 0 := by
  unfold rf
  refine prod_ne_zero_iff.2 fun i _ => ?_
  have : (0 : ℚ) ≤ i := by positivity
  exact ne_of_gt (by linarith)

/-! ### The families of `gammaF` -/

/-- the shape of the families in `gammaF` -/
def GoodF (f : Fam) : Prop :=
  f.al = 0 ∧ f.mu = 0 ∧ 0 < f.be ∧ f.be ≤ 1 ∧ f.be.den ∣ 6 ∧ f.la ≤ 12

instance (f : Fam) : Decidable (GoodF f) := by unfold GoodF; infer_instance

lemma gammaF_good : ∀ fm ∈ gammaF, GoodF fm.1 := by decide +kernel

lemma GoodF.u_le {f : Fam} (hf : GoodF f) : f.u ≤ f.be.den := by
  have h1 : f.be = (f.u : ℚ) / f.be.den := f.be_eq hf.2.2.1
  have hd : (0 : ℚ) < f.be.den := by exact_mod_cast f.be.den_pos
  have h2 : (f.u : ℚ) ≤ f.be.den := by
    have := hf.2.2.2.1
    rw [h1, div_le_one hd] at this
    exact this
  exact_mod_cast h2

lemma GoodF.den_le {f : Fam} (hf : GoodF f) : f.be.den ≤ 6 :=
  Nat.le_of_dvd (by norm_num) hf.2.2.2.2.1

/-- the terms of the progression are `≤ 72 n` -/
lemma GoodF.term_le {f : Fam} (hf : GoodF f) (n i : ℕ) (hi : i < f.la * n) :
    f.u + f.be.den * i ≤ 72 * n := by
  have h1 := hf.u_le
  have h2 := hf.den_le
  have h3 := hf.2.2.2.2.2
  have : f.u + f.be.den * i ≤ f.be.den * (i + 1) := by rw [mul_add]; omega
  have h4 : i + 1 ≤ 12 * n := by
    have : f.la * n ≤ 12 * n := Nat.mul_le_mul_right n h3
    omega
  calc f.u + f.be.den * i ≤ f.be.den * (i + 1) := this
    _ ≤ 6 * (12 * n) := Nat.mul_le_mul h2 h4
    _ = 72 * n := by ring

/-! ### Large primes: valuation `= ` number of members in the class `0` -/

lemma bind_pure_eq_map {α β : Type} (l : List α) (f : α → β) :
    (do let a ← l; pure (f a) : List β) = l.map f := by
  induction l <;> simp_all

lemma sum_ite_eq_length (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    (∑ i ∈ range N, (if P i then (1 : ℤ) else 0)) =
      ((List.range N).filter (fun i => decide (P i))).length := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, List.range_succ, List.filter_append, List.length_append]
    by_cases h : P N <;> simp [h]

lemma not_dvd_den_of_ge5 (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (d : ℕ) (hd : d ∣ 6) :
    ¬ p ∣ d := by
  intro h
  have : p ∣ 2 * 3 := dvd_trans h hd
  rcases (Nat.Prime.dvd_mul hp.out).1 this with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := Nat.le_of_dvd (by norm_num) h3; omega

lemma mod6_of_ge5 (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).1 h; omega
  omega

lemma floorAt_mono (f : Fam) (e n p r : ℕ) :
    (f.lo e).floorAt n p r ≤ (f.hi e).floorAt n p r := by
  unfold Endpt.floorAt
  apply Int.floor_le_floor
  have hv : (f.hi e).val n p = (f.lo e).val n p + f.la * n + f.mu := by
    simp only [Fam.hi, Fam.lo, Endpt.val]; push_cast; ring
  rw [hv]
  have : (0 : ℚ) ≤ (f.la : ℚ) * n + f.mu := by positivity
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem fam_count (f : Fam) (hf : GoodF f) (n p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hbig : 144 * n + 24 < p ^ 2) :
    padicValRat p (rf f.be (f.la * n)) =
      (f.hi (p % 6)).floorAt n p 0 - (f.lo (p % 6)).floorAt n p 0 := by
  obtain ⟨hal, hmu, hpos, -, hd6, -⟩ := id hf
  have hpd := not_dvd_den_of_ge5 p hp5 _ hd6
  rw [rf_val p f hpos, padicValNat.eq_zero_of_not_dvd hpd, Nat.cast_zero, mul_zero, sub_zero]
  have hu := f.u_pos hpos
  -- each term has valuation `[p ∣ a]`
  have hterm : ∀ i ∈ range (f.la * n), (padicValNat p (f.u + f.be.den * i) : ℤ) =
      if p ∣ f.u + f.be.den * i then 1 else 0 := by
    intro i hi
    have hle := GoodF.term_le hf n i (mem_range.1 hi)
    have ha0 : 0 < f.u + f.be.den * i := by omega
    have hlt : f.u + f.be.den * i < p ^ 2 := by omega
    rw [padicValNat_eq_sum_dvd p _ 2 ha0 hlt]
    have hn2 : ¬ p ^ 2 ∣ f.u + f.be.den * i := fun h => absurd (Nat.le_of_dvd ha0 h) (by omega)
    rw [sum_range_succ, sum_range_one]
    simp only [zero_add, pow_one, Nat.reduceAdd, if_neg hn2, add_zero]
    split_ifs <;> simp
  have key : ∀ i : ℕ, ((p : ℤ) ∣ (f.c n + i - ((0 : ℕ) : ℚ)).num ↔ p ∣ f.u + f.be.den * i) := by
    intro i
    have hx : f.c n + i - ((0 : ℕ) : ℚ) = f.be + i := by simp [Fam.c, hal]
    rw [hx]
    have hden : ¬ p ∣ (f.be + i).den := by rw [Rat.add_natCast_den]; exact hpd
    have hne : f.be + i ≠ 0 := by
      have : (0 : ℚ) ≤ i := by positivity
      exact ne_of_gt (by linarith)
    rw [← VGe.one_iff (p := p) hden, VGe.iff hne, f.term_eq hpos i,
      padicValRat.div (by positivity) (by exact_mod_cast f.be.den_ne_zero), padicValRat.of_nat,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpd]
    have := padicValNat_dvd_iff_le (p := p) (n := 1) (a := f.u + f.be.den * i) (by omega)
    rw [pow_one] at this
    rw [this]
    simp only [Nat.cast_zero, sub_zero]
    constructor <;> intro h <;> omega
  rw [sum_congr rfl hterm, sum_ite_eq_length]
  have hfc := congrArg List.length
    (family_class f hd6 (p % 6) (mod6_of_ge5 p hp5) p hp5 rfl n 0 hp.out.pos)
  rw [bind_pure_eq_map, List.length_map, List.filter_map, List.length_map] at hfc
  have hrun : ∀ (a b : ℤ) (c : ℚ), (run a b c).length = (b - a).toNat := by
    intro a b c; simp [run, bind_pure_eq_map]
  rw [hrun] at hfc
  have hfilter : (List.range (f.la * n)).filter (fun i => decide (p ∣ f.u + f.be.den * i)) =
      (List.range (f.len n)).filter
        (fun i : ℕ => decide ((p : ℤ) ∣ (f.c n + (i : ℚ) - ((0 : ℕ) : ℚ)).num)) := by
    rw [show f.len n = f.la * n by simp [Fam.len, hmu]]
    apply List.filter_congr
    intro i _
    simp only [decide_eq_decide]
    exact (key i).symm
  rw [hfilter]
  have h2 : ((List.range (f.len n)).filter
      (fun i : ℕ => decide ((p : ℤ) ∣ (f.c n + (i : ℚ) - ((0 : ℕ) : ℚ)).num))).length =
      ((f.hi (p % 6)).floorAt n p 0 - (f.lo (p % 6)).floorAt n p 0).toNat := hfc
  rw [h2, Int.toNat_of_nonneg (sub_nonneg.2 (floorAt_mono f _ n p 0))]

/-! ### Small primes: deviation bounds -/

lemma fam_dev (q : ℕ) [hq : Fact q.Prime] (f : Fam) (hf : GoodF f) (n K : ℕ)
    (hK : 72 * n < q ^ K) (hqd : ¬ q ∣ f.be.den) :
    |(padicValRat q (rf f.be (f.la * n)) : ℝ) - ((f.la * n : ℕ) : ℝ) * Gs q K| ≤ K := by
  rw [rf_val_real q f hf.2.2.1, padicValNat.eq_zero_of_not_dvd hqd]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  exact sum_val_ap q f.u f.be.den (f.la * n) K (f.u_pos hf.2.2.1) hqd
    (fun i hi => lt_of_le_of_lt (hf.term_le n i hi) hK)

lemma fam_exact (q : ℕ) [hq : Fact q.Prime] (f : Fam) (hf : GoodF f) (n : ℕ)
    (hqd : q ∣ f.be.den) :
    (padicValRat q (rf f.be (f.la * n)) : ℝ) = -(((f.la * n : ℕ) : ℝ) * padicValNat q f.be.den) := by
  have hpos := hf.2.2.1
  rw [rf_val_real q f hpos, sum_val_ap_zero q _ _ _ hqd ?_]
  · ring
  · intro h
    have hc := f.be.reduced
    have hn := Rat.num_pos.2 hpos
    have : f.be.num.natAbs = f.u := by unfold Fam.u; omega
    rw [this] at hc
    exact hq.out.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hc) hqd)

end Zeta2L2Chi3.Arith
