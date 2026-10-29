/-
# p-adic Taylor representations of unit products

`TaylorRep p Φ u`: for all `p`-integral `T`, `Φ T` is `p`-integral and
`Φ T ≡ Σ_{j<6} u_j p^j T^j (mod p⁶)`, with `p`-integral `u_j`.
-/
import Zeta2L2Chi3.Arith.Valuation

namespace Zeta2L2Chi3.Arith

def TaylorRep (p : ℕ) (Φ : ℚ → ℚ) (u : Fin 6 → ℚ) : Prop :=
  (∀ j, VGe p 0 (u j)) ∧ ∀ T, VGe p 0 T →
    VGe p 0 (Φ T) ∧ VGe p 6 (Φ T - ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ))

section
variable {p : ℕ} [Fact p.Prime]

private lemma VGe.mul0 {x y : ℚ} (hx : VGe p 0 x) (hy : VGe p 0 y) : VGe p 0 (x * y) := by
  simpa using hx.mul hy

private lemma VGe.pow0 {x : ℚ} (m : ℕ) (hx : VGe p 0 x) : VGe p 0 (x ^ m) := by
  simpa using hx.pow m

private lemma VGe.p_one : VGe p 1 (p : ℚ) := by
  simpa using VGe.zpow (p := p) 1

private lemma VGe.pT {T : ℚ} (hT : VGe p 0 T) : VGe p 1 ((p : ℚ) * T) := by
  simpa using (VGe.p_one (p := p)).mul hT

private lemma VGe.pT6 {T : ℚ} (hT : VGe p 0 T) : VGe p 6 (((p : ℚ) * T) ^ 6) := by
  simpa using (VGe.pT (p := p) hT).pow 6

private lemma VGe.of6 {x y : ℚ} (hx : VGe p 6 x) (hy : VGe p 0 y) : VGe p 6 (x * y) := by
  simpa using hx.mul hy

/-- closure tactic for `VGe p 0` of ring expressions -/
local macro "vge0" : tactic => `(tactic| repeat' (first
  | assumption
  | apply VGe.add | apply VGe.sub | apply VGe.neg | apply VGe.mul0 | apply VGe.pow0
  | exact VGe.natCast _ | exact VGe.intCast _ | exact VGe.zero _))

omit [Fact p.Prime] in
private lemma ev_eq (u : Fin 6 → ℚ) (T : ℚ) :
    ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ) =
      u 0 + u 1 * (p * T) + u 2 * (p * T) ^ 2 + u 3 * (p * T) ^ 3 + u 4 * (p * T) ^ 4 +
        u 5 * (p * T) ^ 5 := by
  simp only [Fin.sum_univ_six]
  simp
  ring

private lemma ev_vge0 {u : Fin 6 → ℚ} (hu : ∀ j, VGe p 0 (u j)) {T : ℚ} (hT : VGe p 0 T) :
    VGe p 0 (∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ)) := by
  rw [ev_eq]
  have := hu 0; have := hu 1; have := hu 2; have := hu 3; have := hu 4; have := hu 5
  have hy : VGe p 0 ((p : ℚ) * T) := (VGe.pT hT).mono (by norm_num)
  vge0

private lemma const' (c : ℚ) (hc : VGe p 0 c) : TaylorRep p (fun _ => c) ![c, 0, 0, 0, 0, 0] := by
  refine ⟨fun j => ?_, fun T _ => ⟨hc, ?_⟩⟩
  · fin_cases j <;> simp [hc, VGe.zero]
  · rw [ev_eq]; simp [VGe.zero]

private lemma linear' (c : ℚ) (hc : VGe p 0 c) :
    TaylorRep p (fun T => c + p * T) ![c, 1, 0, 0, 0, 0] := by
  have h1 : VGe p 0 (1 : ℚ) := by simpa using VGe.natCast (p := p) 1
  refine ⟨fun j => ?_, fun T hT => ⟨?_, ?_⟩⟩
  · fin_cases j <;> simp [hc, h1, VGe.zero]
  · exact hc.add ((VGe.pT hT).mono (by norm_num))
  · rw [ev_eq]; simp [VGe.zero]

/-- the truncated convolution -/
private def conv (u v : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![u 0 * v 0, u 0 * v 1 + u 1 * v 0, u 0 * v 2 + u 1 * v 1 + u 2 * v 0,
    u 0 * v 3 + u 1 * v 2 + u 2 * v 1 + u 3 * v 0,
    u 0 * v 4 + u 1 * v 3 + u 2 * v 2 + u 3 * v 1 + u 4 * v 0,
    u 0 * v 5 + u 1 * v 4 + u 2 * v 3 + u 3 * v 2 + u 4 * v 1 + u 5 * v 0]

private lemma mul' {Φ Ψ : ℚ → ℚ} {u v : Fin 6 → ℚ} (h₁ : TaylorRep p Φ u) (h₂ : TaylorRep p Ψ v) :
    TaylorRep p (fun T => Φ T * Ψ T) (conv u v) := by
  obtain ⟨hu, hΦ⟩ := h₁
  obtain ⟨hv, hΨ⟩ := h₂
  have := hu 0; have := hu 1; have := hu 2; have := hu 3; have := hu 4; have := hu 5
  have := hv 0; have := hv 1; have := hv 2; have := hv 3; have := hv 4; have := hv 5
  refine ⟨fun j => ?_, fun T hT => ?_⟩
  · fin_cases j <;> simp [conv] <;> vge0
  obtain ⟨hΦ0, hΦ6⟩ := hΦ T hT
  obtain ⟨hΨ0, hΨ6⟩ := hΨ T hT
  refine ⟨hΦ0.mul0 hΨ0, ?_⟩
  set A := ∑ j : Fin 6, u j * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ) with hA
  set B := ∑ j : Fin 6, v j * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ) with hB
  have hB0 : VGe p 0 B := ev_vge0 hv hT
  have hy0 : VGe p 0 ((p : ℚ) * T) := (VGe.pT hT).mono (by norm_num)
  set Q := (u 1 * v 5 + u 2 * v 4 + u 3 * v 3 + u 4 * v 2 + u 5 * v 1) +
    (u 2 * v 5 + u 3 * v 4 + u 4 * v 3 + u 5 * v 2) * (p * T) +
    (u 3 * v 5 + u 4 * v 4 + u 5 * v 3) * (p * T) ^ 2 +
    (u 4 * v 5 + u 5 * v 4) * (p * T) ^ 3 + u 5 * v 5 * (p * T) ^ 4 with hQ
  have hQ0 : VGe p 0 Q := by
    rw [hQ]; vge0
  have hW : A * B - ∑ j : Fin 6, conv u v j * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ) =
      ((p : ℚ) * T) ^ 6 * Q := by
    rw [hA, hB, ev_eq, ev_eq, ev_eq, hQ]
    simp only [conv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have e : Φ T * Ψ T - ∑ j : Fin 6, conv u v j * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ) =
      Φ T * (Ψ T - B) + (Φ T - A) * B +
        (A * B - ∑ j : Fin 6, conv u v j * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ)) := by
    ring
  rw [e, hW]
  refine (VGe.add ?_ ?_).add (VGe.of6 (VGe.pT6 hT) hQ0)
  · simpa [mul_comm] using hΨ6.mul hΦ0
  · exact VGe.of6 hΦ6 hB0

theorem TaylorRep.const (c : ℚ) (hc : VGe p 0 c) : ∃ u, TaylorRep p (fun _ => c) u :=
  ⟨_, const' c hc⟩
/-- `T ↦ c + p T` -/
theorem TaylorRep.linear (c : ℚ) (hc : VGe p 0 c) : ∃ u, TaylorRep p (fun T => c + p * T) u :=
  ⟨_, linear' c hc⟩
/-- `T ↦ 1 / (c + p T)` for a unit `c` -/
theorem TaylorRep.inv_linear (c : ℚ) (hc0 : c ≠ 0) (hc : padicValRat p c = 0) :
    ∃ u, TaylorRep p (fun T => 1 / (c + p * T)) u := by
  have hci : VGe p 0 c⁻¹ := by simpa [hc] using VGe.inv (p := p) hc0
  have hc1 : VGe p 0 c := Or.inr hc.ge
  refine ⟨fun j => c⁻¹ * (-c⁻¹) ^ (j : ℕ), fun j => ?_, fun T hT => ?_⟩
  · exact hci.mul0 (hci.neg.pow0 _)
  have hpT : VGe p 1 ((p : ℚ) * T) := VGe.pT hT
  -- `c + pT` is a unit
  have hne : c + p * T ≠ 0 := by
    intro h0
    have h2 : VGe p 1 c := by
      have := hpT.neg; rwa [show -((p : ℚ) * T) = c by linarith] at this
    have := h2.resolve_left hc0; omega
  have hval : padicValRat p (c + p * T) = 0 := by
    have h0 : 0 ≤ padicValRat p (c + p * T) :=
      (hc1.add (hpT.mono (by norm_num))).resolve_left hne
    by_contra hne'
    have h1 : VGe p 1 (c + p * T) := Or.inr (by omega)
    have h2 := (h1.sub hpT)
    rw [add_sub_cancel_right] at h2
    have := h2.resolve_left hc0; omega
  have hinv : VGe p 0 (c + p * T)⁻¹ := by simpa [hval] using VGe.inv (p := p) hne
  refine ⟨by simpa using hinv, ?_⟩
  have e : 1 / (c + p * T) - ∑ j : Fin 6, c⁻¹ * (-c⁻¹) ^ (j : ℕ) * (p : ℚ) ^ (j : ℕ) * T ^ (j : ℕ) =
      ((p : ℚ) * T) ^ 6 * (c⁻¹ ^ 6 * (c + p * T)⁻¹) := by
    simp only [Fin.sum_univ_six]
    simp
    field_simp
    ring
  rw [e]
  exact VGe.of6 (VGe.pT6 hT) ((hci.pow0 6).mul0 hinv)
theorem TaylorRep.mul {Φ Ψ : ℚ → ℚ} {u v : Fin 6 → ℚ} (h₁ : TaylorRep p Φ u) (h₂ : TaylorRep p Ψ v) :
    ∃ w, TaylorRep p (fun T => Φ T * Ψ T) w :=
  ⟨_, mul' h₁ h₂⟩
theorem TaylorRep.list_prod {ι : Type*} (l : List ι) (Φ : ι → ℚ → ℚ)
    (h : ∀ i ∈ l, ∃ u, TaylorRep p (Φ i) u) : ∃ u, TaylorRep p (fun T => (l.map (fun i => Φ i T)).prod) u := by
  induction l with
  | nil => simpa using TaylorRep.const (p := p) 1 (by simpa using VGe.natCast (p := p) 1)
  | cons a l ih =>
    obtain ⟨u, hu⟩ := h a (by simp)
    obtain ⟨v, hv⟩ := ih (fun i hi => h i (by simp [hi]))
    simpa using TaylorRep.mul hu hv
/-- `T ↦ (r + p T)^k` with `u_0 = 0` when `r = 0`, `k ≥ 1` -/
theorem TaylorRep.pow_linear (r : ℚ) (hr : VGe p 0 r) (k : ℕ) :
    ∃ u, TaylorRep p (fun T => (r + p * T) ^ k) u ∧ (r = 0 → 1 ≤ k → u 0 = 0) := by
  induction k with
  | zero =>
    obtain ⟨u, hu⟩ := TaylorRep.const (p := p) 1 (by simpa using VGe.natCast (p := p) 1)
    exact ⟨u, by simpa using hu, fun _ h => absurd h (by norm_num)⟩
  | succ k ih =>
    obtain ⟨u, hu, -⟩ := ih
    refine ⟨conv u ![r, 1, 0, 0, 0, 0], ?_, fun hr0 _ => by simp [conv, hr0]⟩
    have := mul' hu (linear' r hr)
    simpa [pow_succ] using this
/-- if `u_0 = 0` for one factor, the product has `w_0 = 0` -/
theorem TaylorRep.mul_zero0 {Φ Ψ : ℚ → ℚ} {u v : Fin 6 → ℚ} (h₁ : TaylorRep p Φ u) (h₂ : TaylorRep p Ψ v)
    (hv : v 0 = 0) : ∃ w, TaylorRep p (fun T => Φ T * Ψ T) w ∧ w 0 = 0 :=
  ⟨_, mul' h₁ h₂, by simp [conv, hv]⟩

end

end Zeta2L2Chi3.Arith
