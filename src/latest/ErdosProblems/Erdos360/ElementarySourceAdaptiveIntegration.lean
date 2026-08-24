/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.SourceAdaptiveIntegration
import ErdosProblems.Erdos360.ElementaryNormalizedFiberSelector

/-!
# Elementary unsaturated increments in the source-adaptive recursion

This file feeds the generated-subgroup almost-period bound into the existing
source-adaptive phase machine.  The threshold `Q` makes the canonical fibre
larger than `8(D-1)`, while the saturation function keeps it below half of
the generated subgroup.  The wide-remainder budget supplies more than
`8(D-1)` remaining shifts.
-/

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- Every unsaturated source-adaptive phase gains `D` residues under the
three elementary cardinal conditions required by the normalized selector. -/
theorem sourceAdaptive_unsaturated_increment_elementary
    {b : ℕ} [NeZero b]
    (hb : 0 < b) (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) (phaseQ D : ℕ) (sat : ℕ → ℕ)
    (k : ℕ) (hD : 1 < D) (hQlarge : 8 * (D - 1) ≤ phaseQ)
    (hhalf : 2 * k ≤ R₀.card)
    (hsatHalf : ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse phaseQ sat i →
      let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse phaseQ i
      let H := AddSubgroup.closure (R : Set (ZMod b))
      2 * sat (sourceAdaptiveModulus hb R₀ E hE hdiverse phaseQ i) ≤
        Nat.card H)
    (hRlarge : ∀ i < k,
      8 * (D - 1) <
        (sourceAdaptiveRemainder hb R₀ E hE hdiverse phaseQ i).card) :
    ∀ i < k,
      IsSourceAdaptiveUnsaturatedStep hb R₀ E hE hdiverse phaseQ sat i →
      D + (sourceAdaptivePhaseSums hb R₀ E hE hdiverse phaseQ i).card ≤
        (sourceAdaptivePhaseSums hb R₀ E hE hdiverse
          phaseQ (i + 1)).card := by
  intro i hi hu
  let R := sourceAdaptiveRemainder hb R₀ E hE hdiverse phaseQ i
  let S := sourceAdaptivePhaseSums hb R₀ E hE hdiverse phaseQ i
  let u := sourceAdaptiveMinFiberCenter R₀ E R
  have hiCard : i ≤ R₀.card := by omega
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    rw [card_sourceAdaptiveRemainder
      hb R₀ E hE hdiverse phaseQ hiCard]
    omega
  have hbounds := sourceAdaptiveMinFiber_bounds_of_unsaturated
    hb R₀ E hE hdiverse phaseQ sat (i := i) (by omega) hu
  let H := AddSubgroup.closure ((R : Finset (ZMod b)) : Set (ZMod b))
  let U := normalizedCosetFiber H S u
  have hUlarge : 8 * (D - 1) < (subgroupCoordinates U).card := by
    rw [card_subgroupCoordinates]
    have hgt : phaseQ < U.card := by
      simpa [R, S, u, U, H, sourceAdaptiveFiber,
        sourceAdaptivePhaseSums, sourceAdaptivePhaseSet] using hbounds.2.1
    omega
  have hUsparse : 4 * (subgroupCoordinates U).card <
      2 * Fintype.card (ZMod (Nat.card H)) := by
    rw [card_subgroupCoordinates, ZMod.card]
    have hlt : U.card <
        sat (sourceAdaptiveModulus hb R₀ E hE hdiverse phaseQ i) := by
      simpa [R, S, u, U, H, sourceAdaptiveFiber,
        sourceAdaptivePhaseSums, sourceAdaptivePhaseSet] using hbounds.2.2
    have hs := hsatHalf i hi hu
    dsimp only at hs
    change 2 * sat
        (sourceAdaptiveModulus hb R₀ E hE hdiverse phaseQ i) ≤
      Nat.card H at hs
    omega
  have hglobal := normalizedFiberMaxPick_global_increment_elementary
    R S u hR hD hUlarge hUsparse (hRlarge i hi)
  have hpick := sourceAdaptivePhasePick_eq_normalized_of_unsaturated
    hb R₀ E hE hdiverse phaseQ sat hu
  have hsucc := sourceAdaptivePhaseSums_succ
    hb R₀ E hE hdiverse phaseQ (show i < R₀.card by omega)
  rw [hsucc, hpick]
  simpa [R, S, u, sourceAdaptiveFiber, sourceAdaptivePhaseSums,
    sourceAdaptivePhaseSet, normalizedFiberMaxPick, hR] using hglobal

end Erdos360

#print axioms Erdos360.sourceAdaptive_unsaturated_increment_elementary
