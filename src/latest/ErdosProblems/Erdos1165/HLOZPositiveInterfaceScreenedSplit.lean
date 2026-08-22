/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceScreenedEvent

/-!
# Splitting a raw positive-interface event at the honest screen

The conditional product controls the concrete screened event.  For any raw
growth event this file isolates the paths which have not been reconstructed
by that screen and gives the resulting sharp-cost-plus-remainder estimate.
No estimate of the remainder is assumed or synthesized here.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZPositiveInterfaceScreenedSplit

open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZPositiveInterfaceScreenedEvent
open HLOZProposition48Candidates
open HLOZSharpProductNumerics
open HLOZSharpWindowProductClosure
open LazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The part of a raw interface event which is not covered by the honest
positive-interface stopped-coordinate screen. -/
def positiveInterfaceUnscreenedRemainder
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) (raw : Set WalkPath) : Set WalkPath :=
  raw \ positiveInterfaceScreenedEvent t o m k externalThreshold hm hk
    threshold shell bound

theorem measurableSet_positiveInterfaceUnscreenedRemainder
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) {raw : Set WalkPath} (hraw : MeasurableSet raw) :
    MeasurableSet (positiveInterfaceUnscreenedRemainder t o m k
      externalThreshold hm hk threshold shell bound raw) :=
  hraw.diff (measurableSet_positiveInterfaceScreenedEvent t o m k
    externalThreshold hm hk threshold shell bound)

/-- Every raw path is either covered by the honest screen or belongs to the
explicit unscreened remainder. -/
theorem raw_subset_screened_union_unscreened
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) (raw : Set WalkPath) :
    raw ⊆
      positiveInterfaceScreenedEvent t o m k externalThreshold hm hk
          threshold shell bound ∪
        positiveInterfaceUnscreenedRemainder t o m k externalThreshold hm hk
          threshold shell bound raw := by
  intro s hs
  by_cases hscreen : s ∈ positiveInterfaceScreenedEvent t o m k
      externalThreshold hm hk threshold shell bound
  · exact Or.inl hscreen
  · exact Or.inr ⟨hs, hscreen⟩

/-- The exact quantitative status of an arbitrary raw positive-interface
event: the stopped product pays the sharp cost, and only the explicitly
named unscreened remainder is left. -/
theorem simpleRandomWalk_raw_le_sharp_add_unscreened
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : SharpWindowArithmeticAt m)
    (hactive : m / 2 ≤ externalThreshold)
    (threshold : ℕ → ℕ) (shell bound : ℕ) (raw : Set WalkPath) :
    simpleRandomWalk raw ≤
      ENNReal.ofReal (sharpInterfaceCost threshold shell) +
        simpleRandomWalk (positiveInterfaceUnscreenedRemainder t o m k
          externalThreshold hm hk threshold shell bound raw) := by
  let screen := positiveInterfaceScreenedEvent t o m k externalThreshold
    hm hk threshold shell bound
  let remainder := positiveInterfaceUnscreenedRemainder t o m k
    externalThreshold hm hk threshold shell bound raw
  have hscreen := (positiveInterfaceScreenedProductData t o m k
    externalThreshold hm hk harithmetic hactive threshold shell bound).measure_next_le
  calc
    simpleRandomWalk raw ≤ simpleRandomWalk (screen ∪ remainder) :=
      measure_mono (raw_subset_screened_union_unscreened t o m k
        externalThreshold hm hk threshold shell bound raw)
    _ ≤ simpleRandomWalk screen + simpleRandomWalk remainder :=
      measure_union_le screen remainder
    _ ≤ ENNReal.ofReal (sharpInterfaceCost threshold shell) +
        simpleRandomWalk remainder := by
      simpa only [screen, remainder, add_comm] using
        add_le_add_right hscreen (simpleRandomWalk remainder)

end

end Erdos1165.HLOZPositiveInterfaceScreenedSplit
