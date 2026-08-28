import Wikipedia.HopfProblem.SixthHurewiczSixSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexBasic

/-!
# Actual seven-simplices based on their whole five-skeleton

These are direct specializations of the checked generic simplex-boundary
data.  Every six-dimensional face retains its original continuous map
and has its entire boundary based.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz HigherHurewicz.SimplexGeometry

/-- The actual geometric five-skeleton of the standard seven-simplex. -/
abbrev sevenSimplexFiveSkeleton : Set (Simplex 7) := simplexTwoBoundary 7

/-- An original singular seven-simplex with its whole five-skeleton based. -/
abbrev BasedSevenSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  BasedSimplexBoundary 7 x

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The original six-dimensional singular face, with its whole boundary based. -/
abbrev basedSevenSimplexFace (τ : BasedSevenSimplex x) (i : Fin 8) : BasedSixSimplex x :=
  basedSimplexBoundaryFace τ i

@[simp] theorem basedSevenSimplexFace_apply (τ : BasedSevenSimplex x)
    (i : Fin 8) (s : Simplex 6) :
    (basedSevenSimplexFace τ i).val s = τ.val (simplexFace 6 i s) := rfl

/-- Actual facewise boundary data give the full five-skeleton condition. -/
def BasedSevenSimplex.ofFaces (τ : C(Simplex 7, X))
    (h : ∀ i : Fin 8, ∀ s ∈ sixSimplexBoundary,
      (τ.comp (simplexFace 6 i)) s = x) : BasedSevenSimplex x :=
  BasedSimplexBoundary.ofFaces τ h

@[simp] theorem BasedSevenSimplex.ofFaces_val (τ : C(Simplex 7, X))
    (h : ∀ i : Fin 8, ∀ s ∈ sixSimplexBoundary,
      (τ.comp (simplexFace 6 i)) s = x) :
    (BasedSevenSimplex.ofFaces τ h).val = τ := rfl

@[simp] theorem basedSevenSimplexFace_ofFaces_val (τ : C(Simplex 7, X))
    (h : ∀ i : Fin 8, ∀ s ∈ sixSimplexBoundary,
      (τ.comp (simplexFace 6 i)) s = x) (i : Fin 8) :
    (basedSevenSimplexFace (BasedSevenSimplex.ofFaces τ h) i).val =
      τ.comp (simplexFace 6 i) := rfl

end Wikipedia.HopfProblem.SixthHurewicz
