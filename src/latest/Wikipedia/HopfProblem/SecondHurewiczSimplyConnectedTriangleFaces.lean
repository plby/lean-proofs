import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleGluedLoops
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry

/-!
# Face-based interfaces for actual based triangles

The inverse of the genuine simplex face map identifies a zero coordinate
with an actual face point. This connects the cube constructions to coherent
simplexwise homotopies expressed with Mathlib's original cosimplicial faces.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

/-- A property on every point of an actual face holds whenever its omitted
barycentric coordinate is zero. -/
theorem triangleProperty_of_face {P : Simplex 2 → Prop} (i : Fin 3)
    (h : ∀ u, P (simplexFace 1 i u)) (s : Simplex 2) (hs : s i = 0) : P s := by
  simpa only [simplexFace_inverse] using h (simplexFaceInverse 1 i ⟨s, hs⟩)

/-- Construct a based triangle from equality of its three actual face maps. -/
def BasedTriangle.ofFaces (τ : C(Simplex 2, X))
    (hτ : ∀ i : Fin 3, τ.comp (simplexFace 1 i) = ContinuousMap.const (Simplex 1) x) :
    BasedTriangle x :=
  ⟨τ, fun s ⟨i, hs⟩ => triangleProperty_of_face (P := fun s => τ s = x) i
    (fun u => ContinuousMap.congr_fun (hτ i) u) s hs⟩

@[simp] theorem BasedTriangle.ofFaces_val (τ : C(Simplex 2, X))
    (hτ : ∀ i : Fin 3, τ.comp (simplexFace 1 i) = ContinuousMap.const (Simplex 1) x) :
    (BasedTriangle.ofFaces τ hτ).val = τ := rfl

/-- Equivalent pointwise interface for the actual three face maps. -/
def BasedTriangle.ofFaceValues (τ : C(Simplex 2, X))
    (hτ : ∀ (i : Fin 3) (s : Simplex 1), τ (simplexFace 1 i s) = x) :
    BasedTriangle x :=
  ⟨τ, fun s ⟨i, hs⟩ => triangleProperty_of_face (P := fun s => τ s = x) i (hτ i) s hs⟩

@[simp] theorem BasedTriangle.ofFaceValues_val (τ : C(Simplex 2, X))
    (hτ : ∀ (i : Fin 3) (s : Simplex 1), τ (simplexFace 1 i s) = x) :
    (BasedTriangle.ofFaceValues τ hτ).val = τ := rfl

/-- The endpoint gluing construction with all compatibility hypotheses
expressed on original simplex faces, as produced by coherent normalization. -/
def basedTrianglesHomotopy_of_faces {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, L (r, simplexFace 1 1 s) = U (r, simplexFace 1 1 s))
    (hL : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, L (r, simplexFace 1 i s) = x)
    (hU : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, U (r, simplexFace 1 i s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy τ υ L U
    (fun r s hs => triangleProperty_of_face (P := fun s => L (r, s) = U (r, s))
      1 (hdiag r) s hs)
    (fun r s hs => hs.elim
      (triangleProperty_of_face (P := fun s => L (r, s) = x) 0 (hL r 0 (by decide)) s)
      (triangleProperty_of_face (P := fun s => L (r, s) = x) 2 (hL r 2 (by decide)) s))
    (fun r s hs => hs.elim
      (triangleProperty_of_face (P := fun s => U (r, s) = x) 0 (hU r 0 (by decide)) s)
      (triangleProperty_of_face (P := fun s => U (r, s) = x) 2 (hU r 2 (by decide)) s))

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
