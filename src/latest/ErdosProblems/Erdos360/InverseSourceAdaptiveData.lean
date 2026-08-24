/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.CanonicalClosureCoordinates
import ErdosProblems.Erdos360.ElementarySourceAdaptiveData
import ErdosProblems.Erdos360.LocalDyadicInverseCompletion

/-!
# Inverse-driven source-adaptive selector data

This packages the normalized inverse/sieve phase increment into the exact
source-adaptive certificate consumed by the ordinary subset-sum argument.
-/

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

theorem exists_CFPSourceAdaptiveSelectorData_of_normalizedFiberLossConditions
    (A C : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    {t : ℕ} [NeZero t] (ht : 0 < t)
    (R₀ : Finset (ZMod t)) (hdiverse : PhaseDiverse ht R₀)
    (residueTarget phaseQ D L k : ℕ)
    (saturatedTarget unsaturatedTarget : ℕ) (sat : ℕ → ℕ)
    (n y sieveLevel sieveQ κ : ℕ) (ratio : ℝ)
    (hD : 0 < D) (hL : 0 < L)
    (hhalf : 2 * k ≤ R₀.card)
    (hQroom : ∀ i < k,
      4 * phaseQ ≤
        (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card)
    (hLroom : ∀ i < k,
      4 * L ≤
        (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card)
    (coordinateEquiv : ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ sat i →
      let R := sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i
      let H := AddSubgroup.closure (R : Set (ZMod t))
      ZMod (Nat.card H) ≃+ H)
    (coordinateBase : ∀ i (hi : i < k),
      IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ sat i → ℕ)
    (hconditions : ∀ i (hi : i < k)
      (hu : IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ sat i),
      let R := sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i
      let H := AddSubgroup.closure (R : Set (ZMod t))
      let U := sourceAdaptiveFiber R₀ {0} R
        (sourceAdaptiveMinFiberCenter R₀ {0} R)
      let X := liftFinsetToClosure R
      @NormalizedFiberLossPhaseConditions A C n y sieveLevel sieveQ κ (D - 1)
        ratio t inferInstance H (by exact ⟨Nat.ne_of_gt Nat.card_pos⟩)
        (coordinateEquiv i hi hu) (coordinateBase i hi hu) U X)
    (hsaturated : ∀ i < k,
      saturatedTarget ≤
        sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i *
          sat (sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i))
    (hgrowthBudget :
      (Nat.log 2 t + 1) *
          (2 * (Nat.log 2 t + 1) + (phaseQ / L + 1)) ≤ k)
    (hunsaturated : unsaturatedTarget ≤ D *
      (k - (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) + (phaseQ / L + 1))))
    (htarget : residueTarget ≤ min saturatedTarget unsaturatedTarget) :
    Nonempty (CFPSourceAdaptiveSelectorData ht R₀ hdiverse residueTarget) := by
  have hinc := sourceAdaptive_unsaturated_increment_of_normalizedFiberLossConditions
    A C hsieve ht R₀ {0} (by simp) hdiverse phaseQ D sat
      k n y sieveLevel sieveQ κ ratio hD hhalf
      coordinateEquiv coordinateBase hconditions
  refine ⟨
    { phaseQ := phaseQ
      largeGain := L
      unsaturatedGain := D
      phaseCount := k
      saturatedTarget := saturatedTarget
      unsaturatedTarget := unsaturatedTarget
      saturation := sat
      largeGain_pos := hL
      half := hhalf
      phaseQ_room := hQroom
      largeGain_room := hLroom
      unsaturatedIncrement := hinc
      saturated_bound := hsaturated
      growth_budget := by simpa using hgrowthBudget
      unsaturated_bound := by simpa using hunsaturated
      target_bound := htarget }⟩

/-! ## The exact CFP growth-threshold package -/

/-- Source-adaptive data with the two growth estimates in their exact CFP
form.  In particular `phaseQ` is only required to occupy less than one
quarter of the generated subgroup, not one quarter of the remainder. -/
structure CFPSourceAdaptiveSharpSelectorData
    {t : ℕ} [NeZero t] (ht : 0 < t) (R₀ : Finset (ZMod t))
    (hdiverse : PhaseDiverse ht R₀) (residueTarget : ℕ) where
  phaseQ : ℕ
  largeGain : ℕ
  unsaturatedGain : ℕ
  phaseCount : ℕ
  saturatedTarget : ℕ
  unsaturatedTarget : ℕ
  saturation : ℕ → ℕ
  largeGain_pos : 0 < largeGain
  half : 2 * phaseCount ≤ R₀.card
  growth_ambient : ∀ i < phaseCount,
    4 * phaseQ < Nat.card (AddSubgroup.closure
      ((sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i :
        Finset (ZMod t)) : Set (ZMod t)))
  largeGain_room : ∀ i < phaseCount,
    16 * largeGain ≤
      (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card
  unsaturatedIncrement : ∀ i < phaseCount,
    IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ saturation i →
      unsaturatedGain +
          (sourceAdaptivePhaseSums ht R₀ {0} (by simp) hdiverse phaseQ i).card ≤
        (sourceAdaptivePhaseSums ht R₀ {0} (by simp) hdiverse
          phaseQ (i + 1)).card
  saturated_bound : ∀ i < phaseCount,
    saturatedTarget ≤
      sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i *
        saturation
          (sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i)
  growth_budget :
    (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) + (phaseQ / largeGain + 1)) ≤ phaseCount
  unsaturated_bound : unsaturatedTarget ≤ unsaturatedGain *
    (phaseCount - (Nat.log 2 t + 1) *
      (2 * (Nat.log 2 t + 1) + (phaseQ / largeGain + 1)))
  target_bound : residueTarget ≤ min saturatedTarget unsaturatedTarget

theorem CFPSourceAdaptiveSharpSelectorData.card_le_full_modular_subsetSum
    {t : ℕ} [NeZero t] {ht : 0 < t} {R₀ : Finset (ZMod t)}
    {hdiverse : PhaseDiverse ht R₀} {residueTarget : ℕ}
    (h : CFPSourceAdaptiveSharpSelectorData ht R₀ hdiverse residueTarget) :
    residueTarget ≤ (({0} : Finset (ZMod t)) + R₀.subsetSum).card := by
  apply h.target_bound.trans
  exact sourceAdaptive_modular_phase_machine_cfp
    ht R₀ {0} (by simp) hdiverse h.phaseQ t h.largeGain
    h.unsaturatedGain h.phaseCount h.saturatedTarget h.unsaturatedTarget
    h.saturation h.largeGain_pos h.half h.growth_ambient h.largeGain_room
    (fun _ _ ↦ sourceAdaptiveModulus_le_ambient
      ht R₀ {0} (by simp) hdiverse h.phaseQ _)
    h.unsaturatedIncrement h.saturated_bound h.growth_budget
    h.unsaturated_bound

theorem occupiedResidues_lower_of_source_adaptive_sharp_selector
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (A.image fun a : ℕ ↦ (a : ZMod t)))
    {residueTarget : ℕ}
    (h : CFPSourceAdaptiveSharpSelectorData ht
      (A.image fun a : ℕ ↦ (a : ZMod t)) hdiverse residueTarget) :
    residueTarget ≤ (occupiedResidues A.subsetSum t).card := by
  have hgrowth := h.card_le_full_modular_subsetSum
  have hsub :
      (({0} : Finset (ZMod t)) +
        (A.image fun a : ℕ ↦ (a : ZMod t)).subsetSum) ⊆
        occupiedResidues A.subsetSum t := by
    rw [finset_singleton_zero_add]
    simpa [occupiedResidues] using
      (subsetSum_image_subset_image_subsetSum
        (Nat.castAddMonoidHom (ZMod t)) A)
  exact hgrowth.trans (Finset.card_le_card hsub)

/-- Package normalized inverse/sieve phase hypotheses into the exact CFP
source-adaptive certificate. -/
theorem exists_CFPSourceAdaptiveSharpSelectorData_of_normalizedFiberLossConditions
    (A C : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    {t : ℕ} [NeZero t] (ht : 0 < t)
    (R₀ : Finset (ZMod t)) (hdiverse : PhaseDiverse ht R₀)
    (residueTarget phaseQ D L k : ℕ)
    (saturatedTarget unsaturatedTarget : ℕ) (sat : ℕ → ℕ)
    (n y sieveLevel sieveQ κ : ℕ) (ratio : ℝ)
    (hD : 0 < D) (hL : 0 < L)
    (hhalf : 2 * k ≤ R₀.card)
    (hgrowthAmbient : ∀ i < k,
      4 * phaseQ < Nat.card (AddSubgroup.closure
        ((sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i :
          Finset (ZMod t)) : Set (ZMod t))))
    (hLroom : ∀ i < k,
      16 * L ≤
        (sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i).card)
    (coordinateEquiv : ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ sat i →
      let R := sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i
      let H := AddSubgroup.closure (R : Set (ZMod t))
      ZMod (Nat.card H) ≃+ H)
    (coordinateBase : ∀ i (hi : i < k),
      IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ sat i → ℕ)
    (hconditions : ∀ i (hi : i < k)
      (hu : IsSourceAdaptiveUnsaturatedStep ht R₀ {0} (by simp) hdiverse
        phaseQ sat i),
      let R := sourceAdaptiveRemainder ht R₀ {0} (by simp) hdiverse phaseQ i
      let H := AddSubgroup.closure (R : Set (ZMod t))
      let U := sourceAdaptiveFiber R₀ {0} R
        (sourceAdaptiveMinFiberCenter R₀ {0} R)
      let X := liftFinsetToClosure R
      @NormalizedFiberLossPhaseConditions A C n y sieveLevel sieveQ κ (D - 1)
        ratio t inferInstance H (by exact ⟨Nat.ne_of_gt Nat.card_pos⟩)
        (coordinateEquiv i hi hu) (coordinateBase i hi hu) U X)
    (hsaturated : ∀ i < k,
      saturatedTarget ≤
        sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i *
          sat (sourceAdaptiveModulus ht R₀ {0} (by simp) hdiverse phaseQ i))
    (hgrowthBudget :
      (Nat.log 2 t + 1) *
          (2 * (Nat.log 2 t + 1) + (phaseQ / L + 1)) ≤ k)
    (hunsaturated : unsaturatedTarget ≤ D *
      (k - (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) + (phaseQ / L + 1))))
    (htarget : residueTarget ≤ min saturatedTarget unsaturatedTarget) :
    Nonempty (CFPSourceAdaptiveSharpSelectorData ht R₀ hdiverse residueTarget) := by
  have hinc := sourceAdaptive_unsaturated_increment_of_normalizedFiberLossConditions
    A C hsieve ht R₀ {0} (by simp) hdiverse phaseQ D sat
      k n y sieveLevel sieveQ κ ratio hD hhalf
      coordinateEquiv coordinateBase hconditions
  exact ⟨
    { phaseQ := phaseQ
      largeGain := L
      unsaturatedGain := D
      phaseCount := k
      saturatedTarget := saturatedTarget
      unsaturatedTarget := unsaturatedTarget
      saturation := sat
      largeGain_pos := hL
      half := hhalf
      growth_ambient := hgrowthAmbient
      largeGain_room := hLroom
      unsaturatedIncrement := hinc
      saturated_bound := hsaturated
      growth_budget := hgrowthBudget
      unsaturated_bound := hunsaturated
      target_bound := htarget }⟩

end Erdos360

#print axioms Erdos360.exists_CFPSourceAdaptiveSelectorData_of_normalizedFiberLossConditions
