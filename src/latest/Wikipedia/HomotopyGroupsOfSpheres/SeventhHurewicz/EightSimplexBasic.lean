import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.SevenSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexBasic

/-!
# Actual eight-simplices based on their whole six-skeleton

These are direct specializations of the checked generic simplex-boundary
data.  Every seven-dimensional face retains its original continuous map
and has its entire boundary based.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz HigherHurewicz.SimplexGeometry

/-- The actual geometric six-skeleton of the standard eight-simplex. -/
abbrev eightSimplexSixSkeleton : Set (Simplex 8) := simplexTwoBoundary 8

/-- An original singular eight-simplex with its whole six-skeleton based. -/
abbrev BasedEightSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  BasedSimplexBoundary 8 x

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The original seven-dimensional singular face, with its whole boundary based. -/
abbrev basedEightSimplexFace (τ : BasedEightSimplex x) (i : Fin 9) : BasedSevenSimplex x :=
  basedSimplexBoundaryFace τ i

@[simp] theorem basedEightSimplexFace_apply (τ : BasedEightSimplex x)
    (i : Fin 9) (s : Simplex 7) :
    (basedEightSimplexFace τ i).val s = τ.val (simplexFace 7 i s) := rfl

/-- Actual facewise boundary data give the full six-skeleton condition. -/
def BasedEightSimplex.ofFaces (τ : C(Simplex 8, X))
    (h : ∀ i : Fin 9, ∀ s ∈ sevenSimplexBoundary,
      (τ.comp (simplexFace 7 i)) s = x) : BasedEightSimplex x :=
  BasedSimplexBoundary.ofFaces τ h

@[simp] theorem BasedEightSimplex.ofFaces_val (τ : C(Simplex 8, X))
    (h : ∀ i : Fin 9, ∀ s ∈ sevenSimplexBoundary,
      (τ.comp (simplexFace 7 i)) s = x) :
    (BasedEightSimplex.ofFaces τ h).val = τ := rfl

@[simp] theorem basedEightSimplexFace_ofFaces_val (τ : C(Simplex 8, X))
    (h : ∀ i : Fin 9, ∀ s ∈ sevenSimplexBoundary,
      (τ.comp (simplexFace 7 i)) s = x) (i : Fin 9) :
    (basedEightSimplexFace (BasedEightSimplex.ofFaces τ h) i).val =
      τ.comp (simplexFace 7 i) := rfl

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
