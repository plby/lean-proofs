import Wikipedia.HopfProblem.DegreeCollapseRelativeSheetPassage
import Wikipedia.HopfProblem.DegreeCollapseRegularLevelPaths

/-!
# The actual upper level of an ordered index-three critical point is connected

Index ordering and separation of the native surgery windows give both
endpoint-obstruction bounds. The existing flow-cylinder path theorem then
constructs paths in this original regular level; its connectedness is not
an additional geometric hypothesis.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.pathConnectedSpace_index_three_upper_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    (z₀ : (S.data p).UpperLevel) : PathConnectedSpace (S.data p).UpperLevel := by
  apply S.pathConnectedSpace_middle_level hf hdim (S.data p).upper_regular
    (z₀ := z₀)
  · intro r hr
    have hpr : f p < f r := (S.toSurgeryWindows.value_lt_upper p).trans_le hr
    simpa only [hp] using horder p r hpr
  · intro r hr
    rcases lt_trichotomy (f r) (f p) with h | h | h
    · simpa only [hp] using horder r p h
    · have he : r = p := Subtype.ext (S.distinct r.property p.property h)
      rw [he, hp]
    · have hsep := S.separated p r h
      have hlow := S.toSurgeryWindows.lower_lt_value r
      exact ((not_lt_of_ge hr) (hsep.trans hlow)).elim

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
