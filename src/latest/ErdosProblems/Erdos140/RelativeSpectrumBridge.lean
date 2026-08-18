import ErdosProblems.Erdos140.RelativeChangDefinitions
import ErdosProblems.Erdos140.BohrEstimates

/-!
# Normalization bridge for the relative large spectrum

This file identifies the weighted spectrum of an indicator inside a finite
Bohr carrier with the unnormalised indicator spectrum used by `Chang.lean`.
The factors of the carrier cardinality are recorded explicitly.
-/

open Finset
open scoped BigOperators

namespace Erdos140.RelativeSpectrumBridge

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-! ## A general constant-on-the-ambient-set bridge -/

/-- If `w` is constant with value `c` on an ambient set containing `X`, then
the weighted mass of `1_X` is `c * |X|`. -/
theorem sum_finsetIndicator_mul_eq_const_mul_card
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) :
    ∑ x : G, finsetIndicator X x * w x = c * X.card := by
  classical
  calc
    ∑ x : G, finsetIndicator X x * w x = ∑ x ∈ X, c := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [finsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [finsetIndicator, hxX]
    _ = c * X.card := by simp [mul_comm]

/-- Fourier-sum version of `sum_finsetIndicator_mul_eq_const_mul_card`. -/
theorem sum_finsetIndicator_mul_character_eq_const_mul
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (psi : AddChar G ℂ) :
    ∑ x : G, ((finsetIndicator X x * w x : ℝ) : ℂ) * psi x =
      (c : ℂ) * Chang.spectrumSum X psi := by
  classical
  calc
    ∑ x : G, ((finsetIndicator X x * w x : ℝ) : ℂ) * psi x =
        ∑ x ∈ X, (c : ℂ) * psi x := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [finsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [finsetIndicator, hxX]
    _ = (c : ℂ) * Chang.spectrumSum X psi := by
      rw [Chang.spectrumSum, Finset.mul_sum]

/-- A positive weight which is constant on the ambient set does not change
the large spectrum of an indicator. -/
theorem mem_relativeLargeSpectrum_of_eq_const_iff
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (hc : 0 < c)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ RelativeChangSanders.relativeLargeSpectrum w (finsetIndicator X) eta ↔
      psi ∈ Chang.largeSpectrum X eta := by
  classical
  rw [RelativeChangSanders.mem_relativeLargeSpectrum, Chang.mem_largeSpectrum]
  rw [sum_finsetIndicator_mul_eq_const_mul_card hXB hw]
  rw [sum_finsetIndicator_mul_character_eq_const_mul hXB hw]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  constructor
  · intro h
    have hh : c * (eta * (X.card : ℝ)) ≤
        c * ‖Chang.spectrumSum X psi‖ := by
      calc
        c * (eta * (X.card : ℝ)) = eta * (c * (X.card : ℝ)) := by ring
        _ ≤ c * ‖Chang.spectrumSum X psi‖ := h
    nlinarith
  · intro h
    calc
      eta * (c * (X.card : ℝ)) = c * (eta * (X.card : ℝ)) := by ring
      _ ≤ c * ‖Chang.spectrumSum X psi‖ :=
        mul_le_mul_of_nonneg_left h hc.le

/-- The mass of `1_X` against the uniform probability weight on `B.carrier`
is exactly the relative density `|X| / |B|`. -/
theorem sum_finsetIndicator_mul_normalizedIndicator_eq
    (B : BohrData G) {X : Finset G} (hXB : X ⊆ B.carrier) :
    ∑ x : G, finsetIndicator X x * normalizedIndicator B.carrier x =
      (X.card : ℝ) / B.carrier.card := by
  classical
  calc
    ∑ x : G, finsetIndicator X x * normalizedIndicator B.carrier x =
        ∑ x ∈ X, (B.carrier.card : ℝ)⁻¹ := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [finsetIndicator, normalizedIndicator, hx, hXB hx]
      · simp
      · intro x hxU hxX
        simp [finsetIndicator, hxX]
    _ = (X.card : ℝ) / B.carrier.card := by
      simp [div_eq_mul_inv]

/-- The corresponding weighted Fourier sum is the unnormalised Fourier sum
of `X`, divided by the cardinality of the ambient carrier. -/
theorem sum_finsetIndicator_mul_normalizedIndicator_mul_character_eq
    (B : BohrData G) {X : Finset G} (hXB : X ⊆ B.carrier)
    (psi : AddChar G ℂ) :
    ∑ x : G,
        ((finsetIndicator X x * normalizedIndicator B.carrier x : ℝ) : ℂ) * psi x =
      (B.carrier.card : ℂ)⁻¹ * Chang.spectrumSum X psi := by
  classical
  calc
    ∑ x : G,
        ((finsetIndicator X x * normalizedIndicator B.carrier x : ℝ) : ℂ) * psi x =
        ∑ x ∈ X, (B.carrier.card : ℂ)⁻¹ * psi x := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [finsetIndicator, normalizedIndicator, hx, hXB hx]
      · simp
      · intro x hxU hxX
        simp [finsetIndicator, hxX]
    _ = (B.carrier.card : ℂ)⁻¹ * Chang.spectrumSum X psi := by
      rw [Chang.spectrumSum, Finset.mul_sum]

/-- Membership in the relative weighted spectrum is exactly membership in
Chang's unnormalised large spectrum.  No ambient-group factor occurs. -/
theorem mem_relativeLargeSpectrum_iff
    (B : BohrData G) {X : Finset G} (hXB : X ⊆ B.carrier)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ RelativeChangSanders.relativeLargeSpectrum
        (normalizedIndicator B.carrier) (finsetIndicator X) eta ↔
      psi ∈ Chang.largeSpectrum X eta := by
  classical
  rw [RelativeChangSanders.mem_relativeLargeSpectrum, Chang.mem_largeSpectrum]
  rw [sum_finsetIndicator_mul_normalizedIndicator_eq B hXB]
  rw [sum_finsetIndicator_mul_normalizedIndicator_mul_character_eq B hXB]
  have hcard : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.carrier_nonempty.card_pos
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  constructor <;> intro h
  · calc
      eta * (X.card : ℝ) = (B.carrier.card : ℝ) *
          (eta * ((X.card : ℝ) / B.carrier.card)) := by
        field_simp [hcard.ne']
      _ ≤ (B.carrier.card : ℝ) *
          ((B.carrier.card : ℝ)⁻¹ * ‖Chang.spectrumSum X psi‖) :=
        mul_le_mul_of_nonneg_left h hcard.le
      _ = ‖Chang.spectrumSum X psi‖ := by field_simp [hcard.ne']
  · calc
      eta * ((X.card : ℝ) / B.carrier.card) =
          (B.carrier.card : ℝ)⁻¹ * (eta * (X.card : ℝ)) := by
        field_simp [hcard.ne']
      _ ≤ (B.carrier.card : ℝ)⁻¹ * ‖Chang.spectrumSum X psi‖ :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hcard.le)

end Erdos140.RelativeSpectrumBridge

#print axioms Erdos140.RelativeSpectrumBridge.sum_finsetIndicator_mul_normalizedIndicator_eq
#print axioms Erdos140.RelativeSpectrumBridge.sum_finsetIndicator_mul_eq_const_mul_card
#print axioms Erdos140.RelativeSpectrumBridge.mem_relativeLargeSpectrum_of_eq_const_iff
#print axioms Erdos140.RelativeSpectrumBridge.mem_relativeLargeSpectrum_iff
