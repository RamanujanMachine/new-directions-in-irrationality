/-
# The large-prime bounds for `a_k`, `b_k` and the harmonic sums

For `p ≥ 5` prime with `p² > 144n + 24` and `k ∈ KZ n` in the class `r = k mod p`:
`v_p(a_k) ≥ h(r) + 2`, `v_p(b_k) ≥ h(r) + 1` (`h = hF n p r`), the signed harmonic sums
`H^{(j)}_ρ(k + m)` (`ρ ∈ {1/3, 1/2, 1}`, `0 ≤ m ≤ 2n+1`) have valuation `≥ -j`.
-/
import Zeta2L2Chi3.Arith.FwdLarge
import Zeta2L2Chi3.Arith.FwdConst

open Finset

noncomputable section

namespace Zeta2L2Chi3.Arith

/-- the packet excess `h(r)` of the forward kernel in the class `r` -/
def hF (n p r : ℕ) : ℤ := fwdH (fun E => ((endpts (fwdZ ++ fwdP) (p % 6))[E]!).floorAt n p r)

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem class_of (k : ℤ) : (k % p).toNat < p ∧ (p : ℤ) ∣ k - ((k % p).toNat : ℕ) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have h1 := Int.emod_nonneg k hp0.ne'
  have h2 := Int.emod_lt_of_pos k hp0
  have h3 : (((k % p).toNat : ℕ) : ℤ) = k % p := Int.toNat_of_nonneg h1
  refine ⟨by omega, ?_⟩
  rw [h3]
  exact ⟨k / p, by have := Int.emod_add_mul_ediv k p; linarith⟩

theorem natAbs_lt_sq {a : ℤ} {n : ℕ} (hbig : 144 * n + 24 < p ^ 2) (h1 : a ≤ 144 * n + 24)
    (h2 : -(144 * n + 24 : ℤ) ≤ a) : a.natAbs < p ^ 2 := by
  have : a.natAbs ≤ 144 * n + 24 := by rcases Int.natAbs_eq a with h | h <;> omega
  exact lt_of_le_of_lt this hbig

theorem vge_inv_small1 {y : ℚ} {a : ℤ} {d : ℕ} (hd : 0 < d) (hpd : ¬ p ∣ d) (hya : y * d = a)
    (hap : a.natAbs < p ^ 2) : VGe p (-1) (1 / y) := by
  have := vge_inv_small hd hpd hya hap 1
  simpa using this

theorem SN_SD_vge (hp5 : 5 ≤ p) (n : ℕ) (hbig : 144 * n + 24 < p ^ 2) (k : ℤ) (hk : k ∈ KZ n) :
    VGe p (-1) (SNF n (k : ℚ) - SDF n k (k : ℚ)) := by
  have hk' := mem_KZ.1 hk
  have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp1 : ¬ p ∣ 1 := Nat.Prime.not_dvd_one hp.out
  refine VGe.sub ((VGe.add ?_ ?_).add ?_) ?_
  · refine VGe.finset_sum fun i hi => ?_
    have := mem_range.1 hi
    exact vge_inv_small1 one_pos hp1 (a := k + 2 * n + 1 + i) (by push_cast; ring)
      (natAbs_lt_sq hbig (by omega) (by omega))
  · refine VGe.finset_sum fun i hi => ?_
    have := mem_range.1 hi
    exact vge_inv_small1 (d := 3) (by norm_num) hp3 (a := 3 * k + 4 + 3 * i) (by push_cast; ring)
      (natAbs_lt_sq hbig (by omega) (by omega))
  · refine VGe.finset_sum fun i hi => ?_
    have := mem_range.1 hi
    exact vge_inv_small1 (d := 2) (by norm_num) hp2 (a := 2 * k + 4 * n + 3 + 2 * i)
      (by push_cast; ring) (natAbs_lt_sq hbig (by omega) (by omega))
  · refine VGe.finset_sum fun l hl => ?_
    have hl' := mem_KZ.1 (mem_of_mem_erase hl)
    rw [div_eq_mul_one_div]
    have := (VGe.natCast (p := p) (eZ n l)).mul (vge_inv_small1 one_pos hp1 (y := (k : ℚ) - l) (a := k - l)
      (by push_cast; ring) (natAbs_lt_sq hbig (by omega) (by omega)))
    simpa using this

theorem vge_ND (hp5 : 5 ≤ p) (n : ℕ) (hbig : 144 * n + 24 < p ^ 2) (k : ℤ) (hk : k ∈ KZ n) :
    VGe p (hF n p (k % p).toNat + eZ n k) (NF n (k : ℚ) / DF n k (k : ℚ)) := by
  obtain ⟨hr, hkr⟩ := class_of (p := p) k
  right
  rw [vND hp5 n hbig k hk _ hr hkr]
  rfl

theorem aQ_vge (hp5 : 5 ≤ p) (n j : ℕ) (hbig : 144 * n + 24 < p ^ 2) (k : ℤ) (hk : k ∈ KZ n) :
    VGe p (hF n p (k % p).toNat + 2) (aQ n j k) := by
  unfold aQ gQ
  split_ifs with he
  · have h1 : VGe p 0 ((k : ℚ) ^ j) := by
      have := VGe.pow j (VGe.intCast (p := p) k); simpa using this
    have := h1.mul (vge_ND hp5 n hbig k hk)
    rw [he] at this
    simpa using this
  · exact VGe.zero _

theorem bQ_vge (hp5 : 5 ≤ p) (n j : ℕ) (hbig : 144 * n + 24 < p ^ 2) (k : ℤ) (hk : k ∈ KZ n) :
    VGe p (hF n p (k % p).toNat + 1) (bQ n j k) := by
  have h1 : ∀ m : ℕ, VGe p 0 ((k : ℚ) ^ m) := fun m => by
    have := VGe.pow m (VGe.intCast (p := p) k); simpa using this
  have hND := vge_ND hp5 n hbig k hk
  unfold bQ gQ
  split_ifs with he
  · have hs : VGe p (-1) ((j : ℚ) * (k : ℚ) ^ (j - 1) + (k : ℚ) ^ j * (SNF n (k : ℚ) - SDF n k (k : ℚ))) := by
      refine VGe.add ?_ ?_
      · exact ((VGe.natCast j).mul (h1 _)).mono (by norm_num)
      · have := (h1 j).mul (SN_SD_vge hp5 n hbig k hk); simpa using this
    have := hs.mul hND
    rw [he] at this
    convert this using 1; push_cast; ring
  · have he1 : eZ n k = 1 := by unfold eZ at he ⊢; split_ifs at he ⊢ <;> simp_all
    have := (h1 j).mul hND
    rw [he1] at this
    simpa using this

theorem HsigQ_vge (j : ℕ) (ρ : ℚ) (d : ℕ) (ρd : ℤ) (hρ : ρ * d = ρd) (hd : 0 < d)
    (hpd : ¬ p ∣ d) (m : ℤ) (hb : ∀ w : ℤ, w.natAbs ≤ m.natAbs → (ρd + d * w).natAbs < p ^ 2) :
    VGe p (-(j : ℤ)) (HsigQ j ρ m) := by
  unfold HsigQ
  split_ifs with hm
  · refine VGe.finset_sum fun l hl => ?_
    have hl' := mem_range.1 hl
    exact vge_inv_small hd hpd (a := ρd + d * l) (by push_cast; rw [add_mul, hρ]; ring)
      (hb l (by omega)) j
  · refine VGe.neg (VGe.finset_sum fun l hl => ?_)
    have hl' := mem_range.1 hl
    exact vge_inv_small hd hpd (a := ρd + d * (m + l)) (by push_cast; rw [add_mul, add_mul, hρ]; ring)
      (hb (m + l) (by omega)) j

theorem HsigQ_large (hp5 : 5 ≤ p) (n : ℕ) (hbig : 144 * n + 24 < p ^ 2) (k : ℤ) (hk : k ∈ KZ n)
    (m : ℤ) (hm0 : 0 ≤ m) (hm1 : m ≤ 2 * n + 1) (ρ : ℚ) (hρ : ρ ∈ rhoSet) (j : ℕ) :
    VGe p (-(j : ℤ)) (HsigQ j ρ (k + m)) := by
  have hk' := mem_KZ.1 hk
  have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hkm : (k + m).natAbs ≤ 12 * n + 2 := by rcases Int.natAbs_eq (k + m) with h | h <;> omega
  simp only [rhoSet, mem_insert, mem_singleton] at hρ
  rcases hρ with rfl | rfl | rfl
  · refine HsigQ_vge j _ 3 1 (by norm_num) (by norm_num) hp3 _ fun w hw => ?_
    have : w.natAbs ≤ 12 * n + 2 := hw.trans hkm
    exact natAbs_lt_sq hbig (by rcases Int.natAbs_eq w with h | h <;> push_cast <;> omega)
      (by rcases Int.natAbs_eq w with h | h <;> push_cast <;> omega)
  · refine HsigQ_vge j _ 2 1 (by norm_num) (by norm_num) hp2 _ fun w hw => ?_
    have : w.natAbs ≤ 12 * n + 2 := hw.trans hkm
    exact natAbs_lt_sq hbig (by rcases Int.natAbs_eq w with h | h <;> push_cast <;> omega)
      (by rcases Int.natAbs_eq w with h | h <;> push_cast <;> omega)
  · refine HsigQ_vge j _ 1 1 (by norm_num) one_pos (Nat.Prime.not_dvd_one hp.out) _ fun w hw => ?_
    have : w.natAbs ≤ 12 * n + 2 := hw.trans hkm
    exact natAbs_lt_sq hbig (by rcases Int.natAbs_eq w with h | h <;> push_cast <;> omega)
      (by rcases Int.natAbs_eq w with h | h <;> push_cast <;> omega)

end

end Zeta2L2Chi3.Arith
