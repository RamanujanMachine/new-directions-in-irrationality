/-
# Valuations of the forward vector at small primes

For any prime `q` and `L` with `q^L > 144n + 24`, with `G = Σ_{t<L} q^{-(t+1)} ≤ 1/(q-1)`:

* `v_q(N(k)) ≥ (10n+1)G - L + [q ≠ 3]((6n+1)G - L) - [q = 3](6n+1) + [q ≠ 2]((3n+1)G - L) - [q = 2](3n+1)`,
* `v_q(D_k(k)) ≤ (19n+4)G + 2L`,

so `v_q(N(k)/D_k(k)) ≥ -λ_q n - 3 - 5L` with `λ_2 = 6`, `λ_3 = 9`, `λ_q = 0` (`q ≥ 5`); the
harmonic sums and logarithmic derivatives cost `O(L)` and the fixed-denominator parts `O(1)`:
`v_q(f_n) ≥ -λ_q n - 10 - 7L`.
-/
import Zeta2L2Chi3.Arith.FwdLegendre

open Finset

noncomputable section

namespace Zeta2L2Chi3.Arith

/-- the linear coefficient of the forward bound at `q` -/
def lam (q : ℕ) : ℤ := if q = 2 then 6 else if q = 3 then 9 else 0

section
variable {q : ℕ} [hq : Fact q.Prime]

theorem fam_lower (len d : ℕ) (hd : 0 < d) (α β : ℤ) (x : ℕ → ℚ)
    (hx : ∀ i < len, x i * d = α + β * i) (h0 : ∀ i < len, α + β * i ≠ 0) (L : ℕ) :
    (if (q : ℤ) ∣ β then (-(len * padicValNat q d : ℤ) : ℚ)
      else (len : ℚ) * fGs q L - L - len * (padicValNat q d : ℤ)) ≤
      padicValRat q (∏ i ∈ range len, x i) := by
  have h := prod_lower (q := q) len d hd α β x hx h0 L
  generalize padicValNat q d = V at h ⊢
  generalize padicValRat q (∏ i ∈ range len, x i) = P at h ⊢
  have h' : ((∑ t ∈ range L, (((range len).filter
      (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ α + β * i)).card : ℤ) - len * (V : ℤ) : ℤ) : ℚ) ≤
      (P : ℚ) := by exact_mod_cast h
  push_cast at h' ⊢
  split_ifs with hβ
  · have : (0 : ℚ) ≤ ∑ t ∈ range L, (((range len).filter
        (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ α + β * i)).card : ℚ) := sum_nonneg fun _ _ => by positivity
    linarith
  · have := levsum_lower (q := q) α β hβ len L
    linarith

theorem vNF_lower (n : ℕ) (k : ℤ) (hk : k ∈ KZ n) (L : ℕ) :
    (10 * n + 1 : ℚ) * fGs q L - L +
      (if q = 3 then -(6 * n + 1 : ℚ) else (6 * n + 1 : ℚ) * fGs q L - L) +
      (if q = 2 then -(3 * n + 1 : ℚ) else (3 * n + 1 : ℚ) * fGs q L - L) ≤
      padicValRat q (NF n (k : ℚ)) := by
  have hk' := mem_KZ.1 hk
  have h0 : NF n (k : ℚ) ≠ 0 := NF_ne_zero n k hk
  have f0 := fam_lower (q := q) (famZ0.len n) 1 one_pos (k + 12 * n + 1) (-1)
    (fun i => (k : ℚ) - (famZ0.c n + i)) (fun i _ => by simp [famZ0, Fam.c]; ring)
    (fun i hi => by simp only [famZ0, Fam.len] at hi; omega) L
  have f1 := fam_lower (q := q) (famZ1.len n) 3 (by norm_num) (3 * k + 18 * n + 4) (-3)
    (fun i => (k : ℚ) - (famZ1.c n + i)) (fun i _ => by simp [famZ1, Fam.c]; ring)
    (fun i hi => by simp only [famZ1, Fam.len] at hi; omega) L
  have f2 := fam_lower (q := q) (famZ2.len n) 2 (by norm_num) (2 * k + 10 * n + 3) (-2)
    (fun i => (k : ℚ) - (famZ2.c n + i)) (fun i _ => by simp [famZ2, Fam.c]; ring)
    (fun i hi => by simp only [famZ2, Fam.len] at hi; omega) L
  beta_reduce at f0 f1 f2
  rw [NF_fam] at h0 ⊢
  have hn1 := left_ne_zero_of_mul h0
  have hn2 := left_ne_zero_of_mul hn1
  have hn3 := right_ne_zero_of_mul hn1
  have hn4 := right_ne_zero_of_mul h0
  rw [padicValRat.mul hn1 hn4, padicValRat.mul hn2 hn3]
  generalize padicValRat q (∏ i ∈ range (famZ0.len n), ((k : ℚ) - (famZ0.c n + i))) = V0 at f0 ⊢
  generalize padicValRat q (∏ i ∈ range (famZ1.len n), ((k : ℚ) - (famZ1.c n + i))) = V1 at f1 ⊢
  generalize padicValRat q (∏ i ∈ range (famZ2.len n), ((k : ℚ) - (famZ2.c n + i))) = V2 at f2 ⊢
  have hq1 : ¬ (q : ℤ) ∣ -1 := by
    rw [Int.dvd_neg, ← Int.natCast_one, Int.natCast_dvd_natCast]; exact hq.out.not_dvd_one
  have p1 : padicValNat q 1 = 0 := padicValNat.eq_zero_of_not_dvd hq.out.not_dvd_one
  rw [if_neg hq1, p1] at f0
  have e3 : (q : ℤ) ∣ -3 ↔ q = 3 := by
    rw [Int.dvd_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, Int.natCast_dvd_natCast]
    exact (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_three)
  have e2 : (q : ℤ) ∣ -2 ↔ q = 2 := by
    rw [Int.dvd_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Int.natCast_dvd_natCast]
    exact (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two)
  have v3 : q ≠ 3 → padicValNat q 3 = 0 := fun h =>
    padicValNat.eq_zero_of_not_dvd fun h' => h ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_three).1 h')
  have v2 : q ≠ 2 → padicValNat q 2 = 0 := fun h =>
    padicValNat.eq_zero_of_not_dvd fun h' => h ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 h')
  have g1 : (if q = 3 then -(6 * n + 1 : ℚ) else (6 * n + 1 : ℚ) * fGs q L - L) ≤ V1 := by
    by_cases h3 : q = 3
    · have hs : padicValNat q 3 = 1 := by subst h3; exact padicValNat_self
      rw [if_pos (e3.2 h3), hs] at f1
      rw [if_pos h3]
      simp only [famZ1, Fam.len] at f1
      push_cast at f1
      linarith
    · rw [if_neg (mt e3.1 h3), v3 h3] at f1
      rw [if_neg h3]
      simp only [famZ1, Fam.len] at f1
      push_cast at f1
      linarith
  have g2 : (if q = 2 then -(3 * n + 1 : ℚ) else (3 * n + 1 : ℚ) * fGs q L - L) ≤ V2 := by
    by_cases h2 : q = 2
    · have hs : padicValNat q 2 = 1 := by subst h2; exact padicValNat_self
      rw [if_pos (e2.2 h2), hs] at f2
      rw [if_pos h2]
      simp only [famZ2, Fam.len] at f2
      push_cast at f2
      linarith
    · rw [if_neg (mt e2.1 h2), v2 h2] at f2
      rw [if_neg h2]
      simp only [famZ2, Fam.len] at f2
      push_cast at f2
      linarith
  simp only [famZ0, Fam.len] at f0
  push_cast at f0 ⊢
  linarith

theorem vDF_upper (n : ℕ) (k : ℤ) (hk : k ∈ KZ n) (L : ℕ) (hL : 144 * n + 24 < q ^ L) :
    (padicValRat q (DF n k (k : ℚ)) : ℚ) ≤ (19 * n + 4 : ℚ) * fGs q L + 2 * L := by
  have hk' := mem_KZ.1 hk
  have h0 : DF n k (k : ℚ) ≠ 0 := DF_self_ne_zero n k
  rw [DF_fam n k hk] at h0 ⊢
  rw [padicValRat.mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0)]
  have hq1 : ¬ (q : ℤ) ∣ -1 := by
    rw [Int.dvd_neg, ← Int.natCast_one, Int.natCast_dvd_natCast]; exact hq.out.not_dvd_one
  have hb : ∀ (c : ℤ) (m : ℕ), -(n : ℤ) ≤ c → c + m ≤ 10 * n + 2 →
      ∀ i < m, (k - (c + i)).natAbs < q ^ L := by
    intro c m hc hcm i hi
    have : (k - (c + i)).natAbs ≤ 144 * n + 24 := by
      rcases Int.natAbs_eq (k - (c + i)) with h | h <;> omega
    omega
  have u0 := prod_upper_pole (q := q) (famP0.len n) (famP0.al * n) k L
    (hb _ _ (by simp [famP0]) (by simp [famP0, Fam.len] <;> omega))
  have u1 := prod_upper_pole (q := q) (famP1.len n) (famP1.al * n) k L
    (hb _ _ (by simp [famP1]) (by simp [famP1, Fam.len] <;> omega))
  have w0 := levsum_upper (q := q) (k - famP0.al * n) (-1) hq1 (famP0.len n) L
  have w1 := levsum_upper (q := q) (k - famP1.al * n) (-1) hq1 (famP1.len n) L
  generalize padicValRat q (∏ i ∈ range (famP0.len n),
    (if famP0.al * n + (i : ℤ) = k then (1 : ℚ) else (k : ℚ) - ((famP0.al * n + i : ℤ) : ℚ))) = D0 at u0 ⊢
  generalize padicValRat q (∏ i ∈ range (famP1.len n),
    (if famP1.al * n + (i : ℤ) = k then (1 : ℚ) else (k : ℚ) - ((famP1.al * n + i : ℤ) : ℚ))) = D1 at u1 ⊢
  have u0' : (D0 : ℚ) ≤ ∑ t ∈ range L, ((((range (famP0.len n)).filter
      (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ k - famP0.al * n + (-1) * i)).card : ℕ) : ℚ) := by
    exact_mod_cast u0
  have u1' : (D1 : ℚ) ≤ ∑ t ∈ range L, ((((range (famP1.len n)).filter
      (fun i : ℕ => (q : ℤ) ^ (t + 1) ∣ k - famP1.al * n + (-1) * i)).card : ℕ) : ℚ) := by
    exact_mod_cast u1
  have l0 : ((famP0.len n : ℕ) : ℚ) = 10 * n + 2 := by simp [famP0, Fam.len]
  have l1 : ((famP1.len n : ℕ) : ℚ) = 9 * n + 2 := by simp [famP1, Fam.len]
  rw [l0] at w0
  rw [l1] at w1
  push_cast
  linarith

theorem vND_lower (n : ℕ) (k : ℤ) (hk : k ∈ KZ n) (L : ℕ) (hL : 144 * n + 24 < q ^ L) :
    -lam q * n - 3 - 5 * L ≤ padicValRat q (NF n (k : ℚ) / DF n k (k : ℚ)) := by
  have h1 := vNF_lower (q := q) n k hk L
  have h2 := vDF_upper (q := q) n k hk L hL
  have hG := fGs_le (q := q) L
  have hG0 := fGs_nonneg (q := q) L
  have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hq.out.two_le
  have key : ((-lam q * n - 3 - 5 * L : ℤ) : ℚ) ≤
      ((padicValRat q (NF n (k : ℚ) / DF n k (k : ℚ)) : ℤ) : ℚ) := by
    rw [padicValRat.div (NF_ne_zero n k hk) (DF_self_ne_zero n k)]
    push_cast
    have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    unfold lam
    by_cases h2q : q = 2
    · subst h2q
      simp only [if_true, show (2 : ℕ) ≠ 3 by norm_num, if_false] at h1 ⊢
      norm_num at hG
      push_cast at h1 ⊢
      nlinarith
    · by_cases h3q : q = 3
      · subst h3q
        simp only [if_true, show (3 : ℕ) ≠ 2 by norm_num, if_false] at h1 ⊢
        norm_num at hG
        push_cast at h1 ⊢
        nlinarith
      · simp only [h2q, h3q, if_false] at h1 ⊢
        push_cast at h1 ⊢
        have : fGs q L ≤ 1 := by nlinarith
        nlinarith
  exact_mod_cast key

theorem vge_ND_small (n : ℕ) (k : ℤ) (hk : k ∈ KZ n) (L : ℕ) (hL : 144 * n + 24 < q ^ L) :
    VGe q (-lam q * n - 3 - 5 * L) (NF n (k : ℚ) / DF n k (k : ℚ)) :=
  Or.inr (vND_lower n k hk L hL)

theorem SN_SD_small (n : ℕ) (k : ℤ) (hk : k ∈ KZ n) (L : ℕ) (hL : 144 * n + 24 < q ^ L) :
    VGe q (-(L : ℤ)) (SNF n (k : ℚ) - SDF n k (k : ℚ)) := by
  have hk' := mem_KZ.1 hk
  have hs : ∀ a : ℤ, a ≤ 144 * n + 24 → -(144 * n + 24 : ℤ) ≤ a → a.natAbs < q ^ L := by
    intro a h1 h2
    have : a.natAbs ≤ 144 * n + 24 := by rcases Int.natAbs_eq a with h | h <;> omega
    omega
  have inv1 : ∀ {y : ℚ} {a : ℤ} {d : ℕ}, 0 < d → y * d = a → a.natAbs < q ^ L →
      VGe q (-(L : ℤ)) (1 / y) := fun hd hya hap => by
    have := vge_inv_lev (q := q) hd hya L hap 1; simpa using this
  refine VGe.sub ((VGe.add ?_ ?_).add ?_) ?_
  · refine VGe.finset_sum fun i hi => ?_
    have := mem_range.1 hi
    exact inv1 (d := 1) one_pos (a := k + 2 * n + 1 + i) (by push_cast; ring) (hs _ (by omega) (by omega))
  · refine VGe.finset_sum fun i hi => ?_
    have := mem_range.1 hi
    exact inv1 (d := 3) (by norm_num) (a := 3 * k + 4 + 3 * i) (by push_cast; ring)
      (hs _ (by omega) (by omega))
  · refine VGe.finset_sum fun i hi => ?_
    have := mem_range.1 hi
    exact inv1 (d := 2) (by norm_num) (a := 2 * k + 4 * n + 3 + 2 * i) (by push_cast; ring)
      (hs _ (by omega) (by omega))
  · refine VGe.finset_sum fun l hl => ?_
    have hl' := mem_KZ.1 (mem_of_mem_erase hl)
    rw [div_eq_mul_one_div]
    have := (VGe.natCast (p := q) (eZ n l)).mul (inv1 (y := (k : ℚ) - l) (d := 1) one_pos
      (a := k - l) (by push_cast; ring) (hs _ (by omega) (by omega)))
    simpa using this

theorem aQ_small (n j : ℕ) (k : ℤ) (hk : k ∈ KZ n) (L : ℕ) (hL : 144 * n + 24 < q ^ L) :
    VGe q (-lam q * n - 3 - 5 * L) (aQ n j k) := by
  unfold aQ gQ
  split_ifs
  · have h1 : VGe q 0 ((k : ℚ) ^ j) := by
      have := VGe.pow j (VGe.intCast (p := q) k); simpa using this
    have := h1.mul (vge_ND_small n k hk L hL)
    simpa using this
  · exact VGe.zero _

theorem bQ_small (n j : ℕ) (k : ℤ) (hk : k ∈ KZ n) (L : ℕ) (hL : 144 * n + 24 < q ^ L) :
    VGe q (-lam q * n - 3 - 6 * L) (bQ n j k) := by
  have h1 : ∀ m : ℕ, VGe q 0 ((k : ℚ) ^ m) := fun m => by
    have := VGe.pow m (VGe.intCast (p := q) k); simpa using this
  have hND := vge_ND_small n k hk L hL
  unfold bQ gQ
  split_ifs
  · have hs : VGe q (-(L : ℤ)) ((j : ℚ) * (k : ℚ) ^ (j - 1) +
        (k : ℚ) ^ j * (SNF n (k : ℚ) - SDF n k (k : ℚ))) := by
      refine VGe.add ?_ ?_
      · exact ((VGe.natCast j).mul (h1 _)).mono (by simp)
      · have := (h1 j).mul (SN_SD_small n k hk L hL); simpa using this
    have := hs.mul hND
    exact this.mono (by omega)
  · exact ((h1 j).mul hND).mono (by omega)

theorem HsigQ_small (n : ℕ) (L : ℕ) (hL : 144 * n + 24 < q ^ L) (k : ℤ) (hk : k ∈ KZ n)
    (m : ℤ) (hm0 : 0 ≤ m) (hm1 : m ≤ 2 * n + 1) (ρ : ℚ) (hρ : ρ ∈ rhoSet) (j : ℕ) :
    VGe q (-(j * L : ℤ)) (HsigQ j ρ (k + m)) := by
  have hk' := mem_KZ.1 hk
  have hkm : (k + m).natAbs ≤ 12 * n + 2 := by rcases Int.natAbs_eq (k + m) with h | h <;> omega
  have gen : ∀ (d : ℕ) (ρd : ℤ), 0 < d → ρ * d = ρd → d ≤ 3 → ρd = 1 →
      VGe q (-(j * L : ℤ)) (HsigQ j ρ (k + m)) := by
    intro d ρd hd hρd hd3 hρ1
    unfold HsigQ
    have hs : ∀ w : ℤ, w.natAbs ≤ 12 * n + 2 → (ρd + d * w).natAbs < q ^ L := by
      intro w hw
      have hw' : -(12 * n + 2 : ℤ) ≤ w ∧ w ≤ 12 * n + 2 := by
        rcases Int.natAbs_eq w with h | h <;> constructor <;> omega
      have hdw : -(36 * n + 6 : ℤ) ≤ d * w ∧ d * w ≤ 36 * n + 6 := by
        have hd' : (d : ℤ) ≤ 3 := by exact_mod_cast hd3
        have hd0 : (0 : ℤ) ≤ d := by positivity
        constructor <;> nlinarith
      have : (ρd + d * w).natAbs ≤ 144 * n + 24 := by
        rcases Int.natAbs_eq (ρd + d * w) with h | h <;> omega
      omega
    split_ifs with hm
    · refine VGe.finset_sum fun l hl => ?_
      have hl' := mem_range.1 hl
      exact vge_inv_lev hd (a := ρd + d * l) (by push_cast; rw [add_mul, hρd]; ring) L
        (hs l (by omega)) j
    · refine VGe.neg (VGe.finset_sum fun l hl => ?_)
      have hl' := mem_range.1 hl
      exact vge_inv_lev hd (a := ρd + d * (k + m + l))
        (by push_cast; rw [add_mul, add_mul, add_mul, hρd]; ring) L (hs _ (by omega)) j
  simp only [rhoSet, mem_insert, mem_singleton] at hρ
  rcases hρ with rfl | rfl | rfl
  · exact gen 3 1 (by norm_num) (by norm_num) le_rfl rfl
  · exact gen 2 1 (by norm_num) (by norm_num) (by norm_num) rfl
  · exact gen 1 1 one_pos (by norm_num) (by norm_num) rfl

/-- the small-prime bound for the explicit forward vector -/
theorem fvecE_small (n : ℕ) (L : ℕ) (hL : 144 * n + 24 < q ^ L) (i : Fin 3) :
    VGe q (-lam q * n - 10 - 7 * L) (fvecE n i) := by
  have hlam : 0 ≤ lam q := by unfold lam; split_ifs <;> norm_num
  have key := fvecE_vge (p := q) n (-lam q * n - 9 - 7 * L) (-(2 * L : ℤ)) (-(L : ℤ)) (6 * (-1))
    (-1) (fun _ => -lam q * n - 3 - 5 * L) (fun _ => -lam q * n - 3 - 6 * L)
    (fun j _ k hk => aQ_small n j k hk L hL) (fun j _ k hk => bQ_small n j k hk L hL)
    (fun k hk m hm0 hm1 ρ hρ => ⟨by simpa using HsigQ_small n L hL k hk m hm0 hm1 ρ hρ 2,
      by simpa using HsigQ_small n L hL k hk m hm0 hm1 ρ hρ 1⟩)
    (fun j _ x hx => UQ_vge (by norm_num) six_general n j x hx)
    (fun j => KQ_vge six_general n j)
    (fun k _ => ⟨by nlinarith [Nat.cast_nonneg (α := ℤ) n, Nat.cast_nonneg (α := ℤ) L],
      by omega, by omega⟩)
    (by nlinarith [Nat.cast_nonneg (α := ℤ) n, Nat.cast_nonneg (α := ℤ) L]) i
  convert key using 1
  ring

end

end Zeta2L2Chi3.Arith
