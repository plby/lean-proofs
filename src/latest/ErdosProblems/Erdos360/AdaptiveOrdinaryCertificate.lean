/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ModularInverseBridge
import ErdosProblems.Erdos360.OrdinaryGrowth
import ErdosProblems.Erdos360.LowerAssembly

/-!
# Adaptive modular growth as an ordinary subset-sum certificate

This module is the source-faithful replacement for the coarse one-scale
shortcut.  It packages the parameters of the adaptive CFP phase machine,
proves that its output consists of residues of genuine integer subset sums,
and then feeds the resulting residue gain into the ordinary pivot argument.

The package contains no cardinal-growth conclusion.  Its substantive input
is the exact almost-period escape condition proved by
`ModularInverseBridge` from the inverse theorem and the progression sieve.
-/

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

/-- All parameters and hypotheses of the adaptive modular phase machine for
one pivot.  The seed residue set is `R₀` and the initial sumset is `{0}`.
The final field only compares the requested residue gain with the two genuine
outputs (saturated and unsaturated) of the phase machine. -/
structure CFPAdaptiveSelectorData
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
  phaseQ_room : ∀ i < phaseCount,
    4 * phaseQ ≤
      (cfpRemainder ht R₀ {0} (by simp) hdiverse i).card
  largeGain_room : ∀ i < phaseCount,
    4 * largeGain ≤
      (cfpRemainder ht R₀ {0} (by simp) hdiverse i).card
  inverseEscape : CFPPickedShiftEscapesAlmostPeriods
    ht R₀ {0} (by simp) hdiverse phaseQ unsaturatedGain saturation phaseCount
  saturated_bound : ∀ i < phaseCount,
    saturatedTarget ≤ cfpModulus ht R₀ {0} (by simp) hdiverse i *
      saturation (cfpModulus ht R₀ {0} (by simp) hdiverse i)
  growth_budget :
    (Nat.log 2 t + 1) *
        (2 * (Nat.log 2 t + 1) + (phaseQ / largeGain + 1)) ≤ phaseCount
  unsaturated_bound : unsaturatedTarget ≤ unsaturatedGain *
    (phaseCount - (Nat.log 2 t + 1) *
      (2 * (Nat.log 2 t + 1) + (phaseQ / largeGain + 1)))
  target_bound : residueTarget ≤ min saturatedTarget unsaturatedTarget

/-- The adaptive selector supplies the requested number of modular subset
sums.  This theorem is exactly `cfp_modular_growth_of_adaptive_selector`
specialized to the ambient modulus and the singleton initial set. -/
theorem CFPAdaptiveSelectorData.card_le_full_modular_subsetSum
    {t : ℕ} [NeZero t] {ht : 0 < t} {R₀ : Finset (ZMod t)}
    {hdiverse : PhaseDiverse ht R₀} {residueTarget : ℕ}
    (h : CFPAdaptiveSelectorData ht R₀ hdiverse residueTarget) :
    residueTarget ≤ ({0} + R₀.subsetSum).card := by
  apply h.target_bound.trans
  exact cfp_modular_growth_of_adaptive_selector_ambient
    ht R₀ {0} (by simp) hdiverse
    h.phaseQ h.largeGain h.unsaturatedGain h.phaseCount
    h.saturatedTarget h.unsaturatedTarget h.saturation
    h.largeGain_pos h.half h.phaseQ_room h.largeGain_room
    h.inverseEscape h.saturated_bound h.growth_budget h.unsaturated_bound

/-- The modular sums furnished by the adaptive machine are occupied residue
classes of actual subset sums of the integer seed. -/
theorem occupiedResidues_lower_of_adaptive_selector
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (A.image fun a : ℕ ↦ (a : ZMod t)))
    {residueTarget : ℕ}
    (h : CFPAdaptiveSelectorData ht
      (A.image fun a : ℕ ↦ (a : ZMod t)) hdiverse residueTarget) :
    residueTarget ≤ (occupiedResidues A.subsetSum t).card := by
  have hgrowth := h.card_le_full_modular_subsetSum
  have hsub :
      ({0} + (A.image fun a : ℕ ↦ (a : ZMod t)).subsetSum) ⊆
        occupiedResidues A.subsetSum t := by
    rw [finset_singleton_zero_add]
    simpa [occupiedResidues] using
      (subsetSum_image_subset_image_subsetSum
        (Nat.castAddMonoidHom (ZMod t)) A)
  exact hgrowth.trans (Finset.card_le_card hsub)

/-- Instance-free semantic form of the modular-growth fact needed at one
pivot.  Detailed selector packages (the original `CFPAdaptiveSelectorData`
and the source-adaptive recursion) both construct this exact conclusion.
Keeping the downstream interface semantic prevents the ordinary argument
from depending on a particular implementation of the modular recursion. -/
def HasCFPAdaptivePivotGrowth
    (A : Finset ℕ) (t residueTarget : ℕ) : Prop :=
  0 < t ∧ residueTarget ≤ (occupiedResidues A.subsetSum t).card

/-- The original adaptive-selector package implies the semantic pivot
growth predicate. -/
theorem hasCFPAdaptivePivotGrowth_of_adaptive_selector
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (A.image fun a : ℕ ↦ (a : ZMod t)))
    {residueTarget : ℕ}
    (h : CFPAdaptiveSelectorData ht
      (A.image fun a : ℕ ↦ (a : ZMod t)) hdiverse residueTarget) :
    HasCFPAdaptivePivotGrowth A t residueTarget := by
  exact ⟨ht, occupiedResidues_lower_of_adaptive_selector ht A hdiverse h⟩

/-- Unpack an instance-free adaptive pivot package into the occupied-residue
lower bound needed by the ordinary pivot-growth theorem. -/
theorem occupiedResidues_lower_of_hasCFPAdaptivePivotGrowth
    {A : Finset ℕ} {t residueTarget : ℕ}
    (h : HasCFPAdaptivePivotGrowth A t residueTarget) :
    residueTarget ≤ (occupiedResidues A.subsetSum t).card := by
  exact h.2

/-- A seed/pivot decomposition with adaptive modular data at every pivot
produces the exact ordinary-growth certificate consumed by the Lev layer. -/
theorem exists_CFPOrdinaryGrowthCertificate_of_adaptive_pivots
    {P seed pivots : Finset ℕ} {residueGain diversity nzero diameter : ℕ}
    (hunion : seed ∪ pivots = P)
    (hdisjoint : Disjoint seed pivots)
    (hadaptive : ∀ t ∈ pivots,
      HasCFPAdaptivePivotGrowth seed t residueGain)
    (htarget : nzero ≤ seed.subsetSum.card + pivots.card * residueGain)
    (hdiversity : 0 < diversity)
    (hdiverse : DiverseSampling.DiverseNat P diversity)
    (hsum : (∑ z ∈ P, z) ≤ diameter) :
    Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter) := by
  refine ⟨
    { seed := seed
      pivots := pivots
      residueGain := residueGain
      diversity := diversity
      union_eq := hunion
      disjoint := hdisjoint
      pivots_pos := ?_
      residues := ?_
      target := htarget
      diversity_pos := hdiversity
      diverse := by simpa [hunion] using hdiverse
      sum_le := hsum }⟩
  · intro t ht
    exact (hadaptive t ht).1
  · intro t ht
    exact occupiedResidues_lower_of_hasCFPAdaptivePivotGrowth (hadaptive t ht)

end Erdos360

#print axioms Erdos360.CFPAdaptiveSelectorData.card_le_full_modular_subsetSum
#print axioms Erdos360.occupiedResidues_lower_of_adaptive_selector
#print axioms Erdos360.exists_CFPOrdinaryGrowthCertificate_of_adaptive_pivots
