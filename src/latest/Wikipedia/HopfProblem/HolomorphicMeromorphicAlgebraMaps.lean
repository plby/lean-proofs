import Wikipedia.HopfProblem.HolomorphicMeromorphicField
import Wikipedia.HopfProblem.HolomorphicMeromorphicValue

/-!
# Scalar-compatible maps of the actual meromorphic section algebras

The native holomorphic inclusion and the literal restriction maps preserve
the existing complex constants, on every open subset.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- The original holomorphic functions embed as a complex algebra. -/
def ofHolomorphicAlgHom (U : Opens M) :
    HolomorphicFunctionSheaf.Section I M U →ₐ[ℂ] Section I M U where
  __ := ofHolomorphicRingHom I M U
  commutes' _ := rfl

@[simp] theorem ofHolomorphicAlgHom_apply (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    ofHolomorphicAlgHom I M U f = ofHolomorphic I M U f := rfl

/-- Actual restriction respects the native scalar action. -/
def restrictionAlgHom {U V : Opens M} (h : U ≤ V) :
    Section I M V →ₐ[ℂ] Section I M U where
  __ := restrictionRingHom I M h
  commutes' c := by
    change restrict I M h (ofHolomorphic I M V
      (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M V) c)) =
        ofHolomorphic I M U (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M U) c)
    rw [← ofHolomorphic_restrict]
    rfl

@[simp] theorem restrictionAlgHom_apply {U V : Opens M} (h : U ≤ V)
    (s : Section I M V) : restrictionAlgHom I M h s = restrict I M h s := rfl

/-- The ordinary value depends on the original fraction germ, and hence
does not change on restriction. -/
@[simp] theorem value_restrict {U V : Opens M} (h : U ≤ V)
    (s : Section I M V) (x : U) :
    value I M (restrict I M h s) x = value I M s (Set.inclusion h x) := rfl

end Wikipedia.HopfProblem.HolomorphicMeromorphic
