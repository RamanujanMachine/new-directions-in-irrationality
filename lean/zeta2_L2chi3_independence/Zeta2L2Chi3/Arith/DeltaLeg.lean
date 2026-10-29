/-
# Legendre-type valuation counts in arithmetic progressions

For a prime `q ∤ d`, `Σ_{i<N} v_q(u + d i) = Σ_{k<K} #{i < N : q^{k+1} ∣ u + d i}` once all terms are
`< q^K`, and each count is `N/q^{k+1} ± 1`.
-/
import Mathlib

open Finset

namespace Zeta2L2Chi3.Arith

/-- `v_q(a) = #{k < K : q^(k+1) ∣ a}` for `0 < a < q^K` -/
lemma padicValNat_eq_sum_dvd (q : ℕ) [hq : Fact q.Prime] (a K : ℕ) (ha : 0 < a) (haK : a < q ^ K) :
    padicValNat q a = ∑ k ∈ range K, if q ^ (k + 1) ∣ a then 1 else 0 := by
  rw [Finset.sum_boole]
  have hv : padicValNat q a < K := by
    by_contra h
    push Not at h
    have : q ^ K ∣ a := (padicValNat_dvd_iff_le ha.ne').2 h
    exact absurd (Nat.le_of_dvd ha this) (by omega)
  have : (range K).filter (fun k => q ^ (k + 1) ∣ a) = range (padicValNat q a) := by
    ext k
    simp only [mem_filter, mem_range]
    rw [padicValNat_dvd_iff_le ha.ne']
    omega
  rw [this, card_range, Nat.cast_id]

/-- the solutions of `M ∣ u + d i` form one residue class mod `M` -/
lemma exists_class (u d M : ℕ) (hM : 0 < M) (hcop : Nat.Coprime d M) :
    ∃ c : ℕ, ∀ i : ℕ, M ∣ u + d * i ↔ i ≡ c [MOD M] := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨(-(u : ZMod M) * (d : ZMod M)⁻¹).val, fun i => ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  have hdd := ZMod.coe_mul_inv_eq_one d hcop
  push_cast
  constructor
  · intro h
    linear_combination (d : ZMod M)⁻¹ * h - (i : ZMod M) * hdd
  · intro h
    rw [h]
    linear_combination (-(u : ZMod M)) * hdd

lemma natDiv_bounds (N M : ℕ) (hM : 0 < M) :
    (N : ℝ) / M - 1 ≤ ((N / M : ℕ) : ℝ) ∧ ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (N : ℝ) = M * ((N / M : ℕ) : ℝ) + ((N % M : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N M).symm
  have h2 : ((N % M : ℕ) : ℝ) < M := by exact_mod_cast Nat.mod_lt N hM
  have h3 : (0 : ℝ) ≤ ((N % M : ℕ) : ℝ) := by positivity
  constructor
  · rw [sub_le_iff_le_add, div_le_iff₀ hMr]
    linarith
  · rw [le_div_iff₀ hMr]
    linarith

/-- the count of `i < N` with `M ∣ u + d i` is `N/M ± 1` -/
lemma count_ap_bounds (u d M N : ℕ) (hM : 0 < M) (hcop : Nat.Coprime d M) :
    (N : ℝ) / M - 1 ≤ (((range N).filter (fun i => M ∣ u + d * i)).card : ℝ) ∧
      (((range N).filter (fun i => M ∣ u + d * i)).card : ℝ) ≤ N / M + 1 := by
  obtain ⟨c, hc⟩ := exists_class u d M hM hcop
  have hcard : ((range N).filter (fun i => M ∣ u + d * i)).card =
      N / M + if c % M < N % M then 1 else 0 := by
    rw [← Nat.count_modEq_card _ hM c, Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp only [mem_filter, mem_range, hc]
  rw [hcard]
  obtain ⟨h1, h2⟩ := natDiv_bounds N M hM
  push_cast
  split_ifs <;> constructor <;> push_cast <;> linarith

/-- `G q K = Σ_{k<K} q^{-(k+1)}` -/
noncomputable def Gs (q : ℝ) (K : ℕ) : ℝ := ∑ k ∈ range K, 1 / q ^ (k + 1)

lemma Gs_eq (q : ℝ) (hq : 1 < q) (K : ℕ) : Gs q K = (1 - 1 / q ^ K) / (q - 1) := by
  have hq0 : q - 1 ≠ 0 := by linarith
  have hq1 : q ≠ 0 := by linarith
  induction K with
  | zero => simp [Gs]
  | succ K ih =>
    unfold Gs at ih ⊢
    rw [sum_range_succ, ih]
    field_simp
    ring

lemma Gs_le (q : ℝ) (hq : 1 < q) (K : ℕ) : Gs q K ≤ 1 / (q - 1) := by
  rw [Gs_eq q hq]
  have : 0 < q - 1 := by linarith
  have : 0 ≤ 1 / q ^ K := by positivity
  gcongr
  linarith

lemma Gs_ge (q : ℝ) (hq : 1 < q) (K : ℕ) : 1 / (q - 1) - 1 / ((q - 1) * q ^ K) ≤ Gs q K := by
  rw [Gs_eq q hq]
  have : 0 < q - 1 := by linarith
  have : 0 < q ^ K := by positivity
  apply le_of_eq
  field_simp

/-- the valuation sum of an arithmetic progression with difference prime to `q` -/
lemma sum_val_ap (q : ℕ) [hq : Fact q.Prime] (u d N K : ℕ) (hu : 0 < u) (hd : ¬ q ∣ d)
    (hK : ∀ i < N, u + d * i < q ^ K) :
    |(∑ i ∈ range N, (padicValNat q (u + d * i) : ℝ)) - N * Gs q K| ≤ K := by
  have hcop : ∀ k : ℕ, Nat.Coprime d (q ^ (k + 1)) := fun k =>
    Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hd))
  have hsum : (∑ i ∈ range N, (padicValNat q (u + d * i) : ℝ)) =
      ∑ k ∈ range K, (((range N).filter (fun i => q ^ (k + 1) ∣ u + d * i)).card : ℝ) := by
    have : ∀ i ∈ range N, (padicValNat q (u + d * i) : ℝ) =
        ∑ k ∈ range K, (if q ^ (k + 1) ∣ u + d * i then (1 : ℝ) else 0) := by
      intro i hi
      rw [padicValNat_eq_sum_dvd q _ K (by positivity) (hK i (mem_range.1 hi))]
      push_cast
      rfl
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_boole]
  rw [hsum, Gs, mul_sum, ← sum_sub_distrib]
  calc |∑ k ∈ range K, ((((range N).filter (fun i => q ^ (k + 1) ∣ u + d * i)).card : ℝ) -
        N * (1 / (q : ℝ) ^ (k + 1)))|
      ≤ ∑ k ∈ range K, |(((range N).filter (fun i => q ^ (k + 1) ∣ u + d * i)).card : ℝ) -
        N * (1 / (q : ℝ) ^ (k + 1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range K, (1 : ℝ) := by
        refine sum_le_sum fun k _ => ?_
        have hM : 0 < q ^ (k + 1) := pow_pos hq.out.pos _
        obtain ⟨h1, h2⟩ := count_ap_bounds u d (q ^ (k + 1)) N hM (hcop k)
        push_cast at h1 h2
        rw [abs_le]
        constructor <;> [skip; skip] <;> rw [mul_one_div] <;> linarith
    _ = K := by simp

/-- with `q ∣ d` and `q ∤ u`, no term of the progression is divisible by `q` -/
lemma sum_val_ap_zero (q : ℕ) [hq : Fact q.Prime] (u d N : ℕ) (hd : q ∣ d) (hu : ¬ q ∣ u) :
    (∑ i ∈ range N, (padicValNat q (u + d * i) : ℝ)) = 0 := by
  refine sum_eq_zero fun i _ => ?_
  rw [padicValNat.eq_zero_of_not_dvd]
  · simp
  · intro h
    exact hu ((Nat.dvd_add_left (dvd_mul_of_dvd_left hd i)).1 h)

end Zeta2L2Chi3.Arith
