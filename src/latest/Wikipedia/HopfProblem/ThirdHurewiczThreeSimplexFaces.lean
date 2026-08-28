import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry

/-!
# Actual face data for whole-boundary-based three-simplices

The original simplex face inverse turns a vanishing barycentric coordinate
into an actual face point. Thus equality on all four face maps gives the
whole-boundary condition used by the native cube representative.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {x : X}

theorem threeSimplexProperty_of_face {P : Simplex 3 → Prop} (i : Fin 4)
    (h : ∀ u, P (simplexFace 2 i u)) (s : Simplex 3) (hs : s i = 0) : P s := by
  simpa only [simplexFace_inverse] using h (simplexFaceInverse 2 i ⟨s, hs⟩)

/-- A whole-boundary-based three-simplex from its four actual face-map equalities. -/
def BasedThreeSimplex.ofFaces (τ : C(Simplex 3, X))
    (hτ : ∀ i : Fin 4, τ.comp (simplexFace 2 i) = ContinuousMap.const (Simplex 2) x) :
    BasedThreeSimplex x :=
  ⟨τ, fun s ⟨i, hs⟩ => threeSimplexProperty_of_face (P := fun s => τ s = x) i
    (fun u => ContinuousMap.congr_fun (hτ i) u) s hs⟩

@[simp] theorem BasedThreeSimplex.ofFaces_val (τ : C(Simplex 3, X))
    (hτ : ∀ i : Fin 4, τ.comp (simplexFace 2 i) = ContinuousMap.const (Simplex 2) x) :
    (BasedThreeSimplex.ofFaces τ hτ).val = τ := rfl

/-- The corresponding pointwise interface for the original four face maps. -/
def BasedThreeSimplex.ofFaceValues (τ : C(Simplex 3, X))
    (hτ : ∀ (i : Fin 4) (s : Simplex 2), τ (simplexFace 2 i s) = x) :
    BasedThreeSimplex x :=
  ⟨τ, fun s ⟨i, hs⟩ => threeSimplexProperty_of_face (P := fun s => τ s = x) i
    (hτ i) s hs⟩

@[simp] theorem BasedThreeSimplex.ofFaceValues_val (τ : C(Simplex 3, X))
    (hτ : ∀ (i : Fin 4) (s : Simplex 2), τ (simplexFace 2 i s) = x) :
    (BasedThreeSimplex.ofFaceValues τ hτ).val = τ := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
