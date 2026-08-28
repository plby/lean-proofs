import Wikipedia.HopfProblem.HolomorphicMeromorphicValue

/-!
# Regularity and canonical values depend only on the native germ

Sections on different open domains have the same regularity and
ordinary value whenever their actual fraction-stalk germs at the same
point agree. These statements use only the original pointwise
definitions and require no connectedness assumption.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- Regularity is a property of the original fraction germ, independent
of which actual section and open neighborhood represent it. -/
theorem regularAt_iff_of_germ_eq {U V : Opens M}
    (s : Section I M U) (t : Section I M V) (x : M)
    (hxU : x ∈ U) (hxV : x ∈ V) (h : s ⟨x, hxU⟩ = t ⟨x, hxV⟩) :
    RegularAt I M s ⟨x, hxU⟩ ↔ RegularAt I M t ⟨x, hxV⟩ := by
  simp only [RegularAt, h]

/-- The canonical ordinary value depends only on the actual germ,
including the convention of zero at nonregular germs. -/
theorem value_eq_of_germ_eq {U V : Opens M}
    (s : Section I M U) (t : Section I M V) (x : M)
    (hxU : x ∈ U) (hxV : x ∈ V) (h : s ⟨x, hxU⟩ = t ⟨x, hxV⟩) :
    value I M s ⟨x, hxU⟩ = value I M t ⟨x, hxV⟩ := by
  classical
  let ev : Germ I M x → ℂ := fun a =>
    if hp : ∃ p : HolomorphicStalk I M x, ofHolomorphicGerm I M x p = a then
      HolomorphicFunctionSheaf.stalkEval I M x (Classical.choose hp) else 0
  exact congrArg ev h

end Wikipedia.HopfProblem.HolomorphicMeromorphic
