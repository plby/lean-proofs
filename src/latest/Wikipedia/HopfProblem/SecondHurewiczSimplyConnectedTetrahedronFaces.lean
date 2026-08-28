import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry

/-!
# Facewise data base the whole tetrahedral one-skeleton

The inverse of the literal barycentric face map converts two vanishing
coordinates to a point on the boundary of that face.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Facewise based-boundary data imply the actual whole-skeleton condition. -/
def BasedTetrahedron.ofFaces (τ : C(Simplex 3, X))
    (h : ∀ i : Fin 4, ∀ s ∈ triangleBoundary, (τ.comp (simplexFace 2 i)) s = x) :
    BasedTetrahedron x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := simplexFaceInverse 2 i ⟨s, hi⟩
    have ht : t ∈ triangleBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (simplexFace 2 i t) = x at he
    rw [show simplexFace 2 i t = s from simplexFace_inverse 2 i ⟨s, hi⟩] at he
    exact he⟩

@[simp] theorem BasedTetrahedron.ofFaces_val (τ : C(Simplex 3, X))
    (h : ∀ i : Fin 4, ∀ s ∈ triangleBoundary, (τ.comp (simplexFace 2 i)) s = x) :
    (BasedTetrahedron.ofFaces τ h).val = τ := rfl

@[simp] theorem basedTetrahedronFace_ofFaces_val (τ : C(Simplex 3, X))
    (h : ∀ i : Fin 4, ∀ s ∈ triangleBoundary, (τ.comp (simplexFace 2 i)) s = x)
    (i : Fin 4) :
    (basedTetrahedronFace (BasedTetrahedron.ofFaces τ h) i).val =
      τ.comp (simplexFace 2 i) := rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
