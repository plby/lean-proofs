import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Equiv

/-!
# Fundamental groups of strong deformation retracts

This file supplies the pointed topological implication needed for the
elliptic filling. The retraction and its homotopy are actual continuous
maps. Fixedness on the image of the inclusion ensures that the induced
homotopies of loops preserve their basepoints.
-/

noncomputable section

namespace Wikipedia.HopfProblem

variable {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (r : C(X, A)) (hir : r.comp i = ContinuousMap.id A)

include hir in
/-- Equality of the continuous-map composite gives the pointwise retraction
identity, including the identity used to transport loop basepoints. -/
theorem retraction_leftInverse : Function.LeftInverse r i :=
  fun a => congrArg (fun f : C(A, A) => f a) hir

variable (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i))

/-- Applying a relative deformation to a loop gives a based homotopy to
the loop obtained by retracting and then including it. -/
def retractionLoopHomotopy (a : A) (γ : Path (i a) (i a)) :
    γ.Homotopy (((γ.map r.continuous).cast
      (retraction_leftInverse i r hir a).symm
      (retraction_leftInverse i r hir a).symm).map i.continuous) where
  toFun ts := H (ts.1, γ ts.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk (γ.continuous.comp continuous_snd))
  map_zero_left s := H.map_zero_left (γ s)
  map_one_left s := H.map_one_left (γ s)
  prop' t s hs := by
    apply H.eq_fst t
    have hγ : γ s = i a := by
      rcases hs with hs | hs
      · simpa only [hs] using γ.source
      · rw [Set.mem_singleton_iff] at hs
        simpa only [hs] using γ.target
    exact ⟨a, hγ.symm⟩

/-- The inclusion of a strong deformation retract induces an isomorphism
of the actual fundamental groups at every point of the retract. -/
def retractionFundamentalGroupEquiv (a : A) :
    FundamentalGroup A a ≃* FundamentalGroup X (i a) where
  __ := FundamentalGroup.map i a
  invFun := FundamentalGroup.mapOfEq r (retraction_leftInverse i r hir a)
  left_inv γ := by
    rw [FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact retraction_leftInverse i r hir (γ t)
  right_inv γ := by
    rw [FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply Path.Homotopic.Quotient.eq.mpr
    exact ⟨(retractionLoopHomotopy i r hir H a γ).symm⟩

@[simp] theorem retractionFundamentalGroupEquiv_toMonoidHom (a : A) :
    (retractionFundamentalGroupEquiv i r hir H a).toMonoidHom =
      FundamentalGroup.map i a := rfl

@[simp] theorem retractionFundamentalGroupEquiv_apply (a : A)
    (γ : FundamentalGroup A a) :
    retractionFundamentalGroupEquiv i r hir H a γ = FundamentalGroup.map i a γ := rfl

@[simp] theorem retractionFundamentalGroupEquiv_symm_apply (a : A)
    (γ : FundamentalGroup X (i a)) :
    (retractionFundamentalGroupEquiv i r hir H a).symm γ =
      FundamentalGroup.mapOfEq r (retraction_leftInverse i r hir a) γ := rfl

/-- Forgetting the fixed-point condition gives the ordinary homotopy
equivalence between the retract and the ambient space. -/
def retractionHomotopyEquiv : ContinuousMap.HomotopyEquiv A X where
  toFun := i
  invFun := r
  left_inv := by rw [hir]
  right_inv := ⟨H.toHomotopy.symm⟩

@[simp] theorem retractionHomotopyEquiv_apply (a : A) :
    retractionHomotopyEquiv i r hir H a = i a := rfl

@[simp] theorem retractionHomotopyEquiv_symm_apply (x : X) :
    (retractionHomotopyEquiv i r hir H).symm x = r x := rfl

end Wikipedia.HopfProblem
