import Mathlib.LinearAlgebra.Pi

/-!
# A product with only one possibly nonzero coordinate

Evaluation at that coordinate is an actual linear equivalence. No finiteness
of the index set is needed for this algebraic observation.
-/

noncomputable section

namespace NoExoticSixSphere.PiSingleCoordinate

variable {ι : Type*} (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℤ (V i)]

def equiv (i : ι) (hzero : ∀ j, j ≠ i → Subsingleton (V j)) :
    (∀ j, V j) ≃ₗ[ℤ] V i := by
  classical
  let evaluation : (∀ j, V j) →+ V i :=
    { toFun := fun v ↦ v i
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  apply AddEquiv.toIntLinearEquiv
  apply AddEquiv.ofBijective evaluation
  constructor
  · intro f g he
    funext j
    by_cases hj : j = i
    · subst j
      exact he
    · let := hzero j hj
      exact Subsingleton.elim _ _
  · intro x
    exact ⟨Pi.single i x, Pi.single_eq_same i x⟩

theorem equiv_apply (i : ι) (hzero : ∀ j, j ≠ i → Subsingleton (V j)) (v : ∀ j, V j) :
    equiv V i hzero v = v i := rfl

end NoExoticSixSphere.PiSingleCoordinate
