import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore

/-!
# Native cocycle data on a common intersection cover

Two independent covers give a common cover indexed by pairs. Restricting
either bundle cocycle to this cover preserves its holomorphicity. The
preferred index is the pair of the two original preferred indices.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
    (A : TransitionData M ι) (B : TransitionData M κ)

/-- The first cocycle restricted to the exact common intersection cover. -/
def leftRefinement : TransitionData M (ι × κ) where
  baseSet i := A.baseSet i.1 ∩ B.baseSet i.2
  isOpen_baseSet i := (A.isOpen_baseSet i.1).inter (B.isOpen_baseSet i.2)
  indexAt x := (A.indexAt x, B.indexAt x)
  mem_baseSet_at x := ⟨A.mem_baseSet_at x, B.mem_baseSet_at x⟩
  transition i j x := A.transition i.1 j.1 x
  transition_self i x hx := A.transition_self i.1 x hx.1
  transition_comp i j k x hx := A.transition_comp i.1 j.1 k.1 x
    ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩
  continuousOn_transition i j :=
    (A.continuousOn_transition i.1 j.1).mono fun _ hx => ⟨hx.1.1, hx.2.1⟩

/-- The second cocycle restricted to the same exact common intersection cover. -/
def rightRefinement : TransitionData M (ι × κ) where
  baseSet i := A.baseSet i.1 ∩ B.baseSet i.2
  isOpen_baseSet i := (A.isOpen_baseSet i.1).inter (B.isOpen_baseSet i.2)
  indexAt x := (A.indexAt x, B.indexAt x)
  mem_baseSet_at x := ⟨A.mem_baseSet_at x, B.mem_baseSet_at x⟩
  transition i j x := B.transition i.2 j.2 x
  transition_self i x hx := B.transition_self i.2 x hx.2
  transition_comp i j k x hx := B.transition_comp i.2 j.2 k.2 x
    ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩
  continuousOn_transition i j :=
    (B.continuousOn_transition i.2 j.2).mono fun _ hx => ⟨hx.1.2, hx.2.2⟩

@[simp] theorem leftRefinement_baseSet (i : ι × κ) :
    (leftRefinement A B).baseSet i = A.baseSet i.1 ∩ B.baseSet i.2 := rfl

@[simp] theorem rightRefinement_baseSet (i : ι × κ) :
    (rightRefinement A B).baseSet i = A.baseSet i.1 ∩ B.baseSet i.2 := rfl

@[simp] theorem leftRefinement_indexAt (x : M) :
    (leftRefinement A B).indexAt x = (A.indexAt x, B.indexAt x) := rfl

@[simp] theorem rightRefinement_indexAt (x : M) :
    (rightRefinement A B).indexAt x = (A.indexAt x, B.indexAt x) := rfl

@[simp] theorem leftRefinement_transition (i j : ι × κ) (x : M) :
    (leftRefinement A B).transition i j x = A.transition i.1 j.1 x := rfl

@[simp] theorem rightRefinement_transition (i j : ι × κ) (x : M) :
    (rightRefinement A B).transition i j x = B.transition i.2 j.2 x := rfl

/-- Refinement identifies the original first fibre with the refined fibre
by the literal identity continuous complex-linear map. -/
def leftRefinementFiberEquiv (x : M) :
    A.core.Fiber x ≃L[ℂ] (leftRefinement A B).core.Fiber x :=
  ContinuousLinearEquiv.refl ℂ ℂ

/-- The same native identity identification for the second bundle. -/
def rightRefinementFiberEquiv (x : M) :
    B.core.Fiber x ≃L[ℂ] (rightRefinement A B).core.Fiber x :=
  ContinuousLinearEquiv.refl ℂ ℂ

@[simp] theorem leftRefinementFiberEquiv_apply (x : M) (v : A.core.Fiber x) :
    leftRefinementFiberEquiv A B x v = id (α := ℂ) v := rfl

@[simp] theorem leftRefinementFiberEquiv_symm_apply (x : M)
    (v : (leftRefinement A B).core.Fiber x) :
    (leftRefinementFiberEquiv A B x).symm v = id (α := ℂ) v := rfl

@[simp] theorem rightRefinementFiberEquiv_apply (x : M) (v : B.core.Fiber x) :
    rightRefinementFiberEquiv A B x v = id (α := ℂ) v := rfl

@[simp] theorem rightRefinementFiberEquiv_symm_apply (x : M)
    (v : (rightRefinement A B).core.Fiber x) :
    (rightRefinementFiberEquiv A B x).symm v = id (α := ℂ) v := rfl

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

instance leftRefinement_isHolomorphic [A.IsHolomorphic I] :
    (leftRefinement A B).IsHolomorphic I where
  contMDiffOn_transition i j :=
    (A.transition_holomorphic I i.1 j.1).mono fun _ hx => ⟨hx.1.1, hx.2.1⟩

instance rightRefinement_isHolomorphic [B.IsHolomorphic I] :
    (rightRefinement A B).IsHolomorphic I where
  contMDiffOn_transition i j :=
    (B.transition_holomorphic I i.2 j.2).mono fun _ hx => ⟨hx.1.2, hx.2.2⟩

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
