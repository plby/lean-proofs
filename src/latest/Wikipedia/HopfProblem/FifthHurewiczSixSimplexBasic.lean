import Wikipedia.HopfProblem.FifthHurewiczFiveSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexBasic

/-!
# Actual six-simplices based on their whole four-skeleton

These are direct specializations of the checked generic simplex-boundary
data.  Every five-dimensional face retains its original continuous map
and has its entire boundary based.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz HigherHurewicz.SimplexGeometry

/-- The actual geometric four-skeleton of the standard six-simplex. -/
abbrev sixSimplexFourSkeleton : Set (Simplex 6) := simplexTwoBoundary 6

/-- An original singular six-simplex with its whole four-skeleton based. -/
abbrev BasedSixSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  BasedSimplexBoundary 6 x

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The original five-dimensional singular face, with its whole boundary based. -/
abbrev basedSixSimplexFace (τ : BasedSixSimplex x) (i : Fin 7) : BasedFiveSimplex x :=
  basedSimplexBoundaryFace τ i

@[simp] theorem basedSixSimplexFace_apply (τ : BasedSixSimplex x)
    (i : Fin 7) (s : Simplex 5) :
    (basedSixSimplexFace τ i).val s = τ.val (simplexFace 5 i s) := rfl

/-- Actual facewise boundary data give the full four-skeleton condition. -/
def BasedSixSimplex.ofFaces (τ : C(Simplex 6, X))
    (h : ∀ i : Fin 7, ∀ s ∈ fiveSimplexBoundary,
      (τ.comp (simplexFace 5 i)) s = x) : BasedSixSimplex x :=
  BasedSimplexBoundary.ofFaces τ h

@[simp] theorem BasedSixSimplex.ofFaces_val (τ : C(Simplex 6, X))
    (h : ∀ i : Fin 7, ∀ s ∈ fiveSimplexBoundary,
      (τ.comp (simplexFace 5 i)) s = x) :
    (BasedSixSimplex.ofFaces τ h).val = τ := rfl

@[simp] theorem basedSixSimplexFace_ofFaces_val (τ : C(Simplex 6, X))
    (h : ∀ i : Fin 7, ∀ s ∈ fiveSimplexBoundary,
      (τ.comp (simplexFace 5 i)) s = x) (i : Fin 7) :
    (basedSixSimplexFace (BasedSixSimplex.ofFaces τ h) i).val =
      τ.comp (simplexFace 5 i) := rfl

end Wikipedia.HopfProblem.FifthHurewicz
