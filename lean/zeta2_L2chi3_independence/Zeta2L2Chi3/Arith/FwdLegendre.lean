/-
# Legendre-type counting

For a prime `q`, `v_q(a) = #{t < L : q^{t+1} ∣ a}` once `|a| < q^L` (and `≥` always), and in an
arithmetic progression `α + β i` (`i < len`, `q ∤ β`) the number of terms divisible by `M = q^s`
lies in `[len/M - 1, len/M + 1]`.  Hence products of progressions have valuations
`len · G - L ≤ v` (lower bound) and pole products `v ≤ m · G + L`, `G = Σ_{t<L} q^{-(t+1)}`.
-/
import Zeta2L2Chi3.Arith.FwdLarge2

open Finset

noncomputable section

namespace Zeta2L2Chi3.Arith

section
variable {q : ℕ} [hq : Fact q.Prime]

/-- the number of levels `t < L` with `q^{t+1} ∣ a` -/
def lev (q L : ℕ) (a : ℤ) : ℕ := ((range L).filter (fun t => (q : ℤ) ^ (t + 1) ∣ a)).card

theorem lev_le_padicValInt (a : ℤ) (ha : a ≠ 0) (L : ℕ) : lev q L a ≤ padicValInt q a := by
  unfold lev
  calc _ ≤ (range (padicValInt q a)).card := card_le_card (fun t ht => by
          simp only [mem_filter, mem_range] at ht ⊢
          rcases (padicValInt_dvd_iff (p := q) (t + 1) a).1 ht.2 with h | h
          · exact absurd h ha
          · omega)
    _ = _ := card_range _

theorem padicValInt_lt_of (a : ℤ) (ha : a ≠ 0) (L : ℕ) (hL : a.natAbs < q ^ L) :
    padicValInt q a < L := by
  have h1 : (q : ℤ) ^ (padicValInt q a) ∣ a := (padicValInt_dvd_iff _ a).2 (Or.inr le_rfl)
  have h2 : q ^ padicValInt q a ∣ a.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 h1; simpa [Int.natAbs_pow] using this
  have h3 := Nat.le_of_dvd (Int.natAbs_pos.2 ha) h2
  by_contra h
  have := Nat.pow_le_pow_right hq.out.pos (not_lt.1 h)
  omega

theorem padicValInt_le_lev (a : ℤ) (ha : a ≠ 0) (L : ℕ) (hL : a.natAbs < q ^ L) :
    padicValInt q a ≤ lev q L a := by
  have hv := padicValInt_lt_of a ha L hL
  unfold lev
  calc padicValInt q a = (range (padicValInt q a)).card := (card_range _).symm
    _ ≤ _ := card_le_card (fun t ht => by
        simp only [mem_filter, mem_range] at ht ⊢
        exact ⟨by omega, (padicValInt_dvd_iff (p := q) (t + 1) a).2 (Or.inr (by omega))⟩)

/-- counting multiples in an arithmetic progression -/
theorem count_ap (M : ℕ) (hM : 0 < M) (α β : ℤ) (hβ : IsCoprime β (M : ℤ)) (len : ℕ) :
    ((len : ℚ) / M - 1 ≤ ((range len).filter (fun i : ℕ => (M : ℤ) ∣ α + β * i)).card) ∧
    ((((range len).filter (fun i : ℕ => (M : ℤ) ∣ α + β * i)).card : ℚ) ≤ len / M + 1) := by
  obtain ⟨u, v, huv⟩ := hβ
  set w := u * α with hw
  have hiff : ∀ i : ℕ, (M : ℤ) ∣ α + β * i ↔ (M : ℤ) ∣ w + i := by
    intro i
    constructor
    · intro h
      have : (M : ℤ) ∣ u * (α + β * i) + M * (v * i) :=
        dvd_add (dvd_mul_of_dvd_right h u) (dvd_mul_right _ _)
      convert this using 1
      linear_combination (-(i : ℤ)) * huv
    · intro h
      have : (M : ℤ) ∣ β * (w + i) + M * (v * α) :=
        dvd_add (dvd_mul_of_dvd_right h β) (dvd_mul_right _ _)
      convert this using 1
      linear_combination (-α) * huv
  have hc : ((range len).filter (fun i : ℕ => (M : ℤ) ∣ α + β * i)).card =
      ((Ico w (w + len)).filter (fun x => (M : ℤ) ∣ x)).card := by
    refine card_nbij' (fun i => w + i) (fun x => (x - w).toNat) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_Ico] at hi ⊢
      exact ⟨⟨by omega, by omega⟩, (hiff i).1 hi.2⟩
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_Ico] at hx ⊢
      refine ⟨by omega, (hiff _).2 ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      convert hx.2 using 1; ring
    · intro i _; simp
    · intro x hx
      simp only [coe_filter, Set.mem_setOf_eq, mem_Ico] at hx
      simp only
      omega
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have key := Int.Ico_filter_dvd_card w (w + len) hM'
  rw [hc]
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  set A : ℚ := (((w + len : ℤ) : ℚ)) / ((M : ℤ) : ℚ)
  set B : ℚ := ((w : ℚ)) / ((M : ℤ) : ℚ)
  have hAB : A - B = len / M := by
    simp only [A, B]; push_cast; field_simp; ring
  have e1 := Int.le_ceil A
  have e2 := Int.ceil_lt_add_one A
  have e3 := Int.le_ceil B
  have e4 := Int.ceil_lt_add_one B
  set N := ((Ico w (w + len)).filter (fun x => (M : ℤ) ∣ x)).card with hN
  have hNq : (N : ℚ) = max ((⌈A⌉ : ℚ) - ⌈B⌉) 0 := by
    have := congrArg (fun z : ℤ => (z : ℚ)) key
    push_cast at this
    exact this
  have h1 : (len : ℚ) / M - 1 ≤ N := by
    rw [hNq]; refine le_trans ?_ (le_max_left _ _); linarith
  have h2 : (N : ℚ) ≤ len / M + 1 := by
    rw [hNq]
    refine max_le (by linarith) ?_
    have : (0 : ℚ) ≤ len / M := by positivity
    linarith
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem isCoprime_pow_of (β : ℤ) (hβ : ¬ (q : ℤ) ∣ β) (s : ℕ) : IsCoprime β ((q ^ s : ℕ) : ℤ) := by
  have hpI : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
  push_cast
  exact ((Prime.coprime_iff_not_dvd hpI).2 hβ).symm.pow_right

/-- `G = Σ_{t<L} q^{-(t+1)}` -/
def fGs (q L : ℕ) : ℚ := ∑ t ∈ range L, 1 / (q : ℚ) ^ (t + 1)

theorem fGs_nonneg (L : ℕ) : 0 ≤ fGs q L := sum_nonneg fun t _ => by positivity

theorem fGs_mul (L : ℕ) : ((q : ℚ) - 1) * fGs q L = 1 - 1 / (q : ℚ) ^ L := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  induction L with
  | zero => simp [fGs]
  | succ L ih =>
    rw [fGs, sum_range_succ, ← fGs, mul_add, ih]
    field_simp
    ring

theorem fGs_le (L : ℕ) : ((q : ℚ) - 1) * fGs q L ≤ 1 := by
  rw [fGs_mul]
  have : 0 ≤ 1 / (q : ℚ) ^ L := by positivity
  linarith

/-- sum of level counts of an arithmetic progression: lower bound -/
theorem levsum_lower (α β : ℤ) (hβ : ¬ (q : ℤ) ∣ β) (len L : ℕ) :
    (len : ℚ) * fGs q L - L ≤
      ∑ t ∈ range L, (((range len).filter (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ α + β * i)).card : ℚ) := by
  rw [fGs, mul_sum, show (L : ℚ) = ∑ t ∈ range L, (1 : ℚ) by simp, ← sum_sub_distrib]
  refine sum_le_sum fun t _ => ?_
  have h := (count_ap (q ^ (t + 1)) (pow_pos hq.out.pos _) α β (isCoprime_pow_of β hβ _) len).1
  push_cast at h
  convert h using 1; field_simp

theorem levsum_upper (α β : ℤ) (hβ : ¬ (q : ℤ) ∣ β) (len L : ℕ) :
    ∑ t ∈ range L, (((range len).filter (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ α + β * i)).card : ℚ) ≤
      (len : ℚ) * fGs q L + L := by
  rw [fGs, mul_sum, show (L : ℚ) = ∑ t ∈ range L, (1 : ℚ) by simp, ← sum_add_distrib]
  refine sum_le_sum fun t _ => ?_
  have h := (count_ap (q ^ (t + 1)) (pow_pos hq.out.pos _) α β (isCoprime_pow_of β hβ _) len).2
  push_cast at h
  convert h using 1; field_simp

/-- swapping the level sum and the product index -/
theorem sum_lev (len L : ℕ) (a : ℕ → ℤ) :
    ∑ i ∈ range len, (lev q L (a i) : ℤ) =
      ∑ t ∈ range L, (((range len).filter (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ a i)).card : ℤ) := by
  simp only [lev, card_filter]
  push_cast
  exact sum_comm

/-- valuation of a product of `x_i = (α + β i)/d`: lower bound by level counts -/
theorem prod_lower (len d : ℕ) (hd : 0 < d) (α β : ℤ) (x : ℕ → ℚ)
    (hx : ∀ i < len, x i * d = α + β * i) (h0 : ∀ i < len, α + β * i ≠ 0) (L : ℕ) :
    ∑ t ∈ range L, (((range len).filter (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ α + β * i)).card : ℤ) -
      len * (padicValNat q d : ℤ) ≤ padicValRat q (∏ i ∈ range len, x i) := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hxe : ∀ i < len, x i = ((α + β * i : ℤ) : ℚ) / d := fun i hi => by
    rw [eq_div_iff hd0, hx i hi]; push_cast; ring
  rw [pvr_prod _ _ (fun i hi => by
    rw [hxe i (mem_range.1 hi)]
    exact div_ne_zero (by exact_mod_cast h0 i (mem_range.1 hi)) hd0)]
  rw [← sum_lev len L (fun i => α + β * i)]
  have : (len : ℤ) * padicValNat q d = ∑ i ∈ range len, (padicValNat q d : ℤ) := by simp
  rw [this, ← sum_sub_distrib]
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  rw [hxe i hi', padicValRat.div (by exact_mod_cast h0 i hi') hd0, padicValRat.of_int,
    padicValRat.of_nat]
  have := lev_le_padicValInt (q := q) _ (h0 i hi') L
  omega

/-- valuation of a pole product: upper bound by level counts -/
theorem prod_upper_pole (m : ℕ) (c k : ℤ) (L : ℕ) (hL : ∀ i < m, (k - (c + i)).natAbs < q ^ L) :
    padicValRat q (∏ i ∈ range m,
        (if c + (i : ℤ) = k then (1 : ℚ) else (k : ℚ) - ((c + i : ℤ) : ℚ))) ≤
      ∑ t ∈ range L, (((range m).filter
        (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ (k - c) + (-1) * i)).card : ℤ) := by
  rw [pvr_prod _ _ (fun i _ => by
    split_ifs with h
    · exact one_ne_zero
    · rw [sub_ne_zero]; intro h'; exact h (by exact_mod_cast h'.symm))]
  rw [← sum_lev m L (fun i => (k - c) + (-1) * i)]
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  split_ifs with h
  · simp
  · have hne : k - (c + i) ≠ 0 := by omega
    rw [show (k : ℚ) - ((c + i : ℤ) : ℚ) = ((k - (c + i) : ℤ) : ℚ) by push_cast; ring,
      padicValRat.of_int]
    have := padicValInt_le_lev (q := q) _ hne L (hL i hi')
    rw [show k - c + (-1) * (i : ℤ) = k - (c + i) by ring]
    exact_mod_cast this

/-- `1/y^j` for `y = a/d`, `|a| < q^L` -/
theorem vge_inv_lev {y : ℚ} {a : ℤ} {d : ℕ} (hd : 0 < d) (hya : y * d = a) (L : ℕ)
    (hap : a.natAbs < q ^ L) (j : ℕ) : VGe q (-(j * L : ℤ)) (1 / y ^ j) := by
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
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hye : y = (a : ℚ) / d := by rw [← hya]; field_simp
    right
    rw [one_div, padicValRat.inv, padicValRat.pow, hye, padicValRat.div (by exact_mod_cast ha) hd0,
      padicValRat.of_int, padicValRat.of_nat]
    have := padicValInt_lt_of (q := q) a ha L hap
    have h2 : (0 : ℤ) ≤ padicValNat q d := by positivity
    have h3 : ((padicValInt q a : ℕ) : ℤ) ≤ L := by exact_mod_cast this.le
    have h4 : (j : ℤ) * (((padicValInt q a : ℕ) : ℤ) - padicValNat q d) ≤ j * L :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

end

end Zeta2L2Chi3.Arith
