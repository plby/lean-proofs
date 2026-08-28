import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry

/-!
# Three-dimensional faces of an actual based four-simplex

The whole two-skeleton is the locus of two distinct zero barycentric
coordinates. Facewise based-boundary data imply this literal condition
using the inverse of the actual simplex face map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

/-- The full geometric two-skeleton of the actual standard four-simplex. -/
def fourSimplexTwoSkeleton : Set (Simplex 4) :=
  {s | ∃ i j : Fin 5, i ≠ j ∧ s i = 0 ∧ s j = 0}

/-- A continuous singular four-simplex whose whole two-skeleton is based. -/
def BasedFourSimplex {X : Type} [TopologicalSpace X] (x : X) :=
  {τ : C(Simplex 4, X) // ∀ s ∈ fourSimplexTwoSkeleton, τ s = x}

theorem simplexFace_threeSimplexBoundary (i : Fin 5) (s : Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : simplexFace 3 i s ∈ fourSimplexTwoSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm,
    simplexFace_apply_self 3 i s, (simplexFace_apply_succAbove 3 i s j).trans hj⟩

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original three-dimensional singular face, with its based boundary. -/
def basedFourSimplexFace (τ : BasedFourSimplex x) (i : Fin 5) : BasedThreeSimplex x :=
  ⟨τ.val.comp (simplexFace 3 i),
    fun s hs => τ.property _ (simplexFace_threeSimplexBoundary i s hs)⟩

@[simp] theorem basedFourSimplexFace_apply (τ : BasedFourSimplex x)
    (i : Fin 5) (s : Simplex 3) :
    (basedFourSimplexFace τ i).val s = τ.val (simplexFace 3 i s) := rfl

/-- Facewise boundary data give the actual whole-two-skeleton condition. -/
def BasedFourSimplex.ofFaces (τ : C(Simplex 4, X))
    (h : ∀ i : Fin 5, ∀ s ∈ threeSimplexBoundary, (τ.comp (simplexFace 3 i)) s = x) :
    BasedFourSimplex x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := simplexFaceInverse 3 i ⟨s, hi⟩
    have ht : t ∈ threeSimplexBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (simplexFace 3 i t) = x at he
    rw [show simplexFace 3 i t = s from simplexFace_inverse 3 i ⟨s, hi⟩] at he
    exact he⟩

@[simp] theorem BasedFourSimplex.ofFaces_val (τ : C(Simplex 4, X))
    (h : ∀ i : Fin 5, ∀ s ∈ threeSimplexBoundary, (τ.comp (simplexFace 3 i)) s = x) :
    (BasedFourSimplex.ofFaces τ h).val = τ := rfl

@[simp] theorem basedFourSimplexFace_ofFaces_val (τ : C(Simplex 4, X))
    (h : ∀ i : Fin 5, ∀ s ∈ threeSimplexBoundary, (τ.comp (simplexFace 3 i)) s = x)
    (i : Fin 5) :
    (basedFourSimplexFace (BasedFourSimplex.ofFaces τ h) i).val =
      τ.comp (simplexFace 3 i) := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
