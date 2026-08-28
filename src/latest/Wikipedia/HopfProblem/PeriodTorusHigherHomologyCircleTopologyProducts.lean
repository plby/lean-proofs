import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Constructions.SumProd

/-!
# Products and sums of homotopy equivalences for the circle cover

The projection from a product with a contractible space is an actual homotopy
equivalence. Homotopy equivalences also combine over topological sums. The
formulas below retain the underlying projection and the two summand maps.
-/

noncomputable section

open ContinuousMap

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology

/-- A point occurring in an actual contraction of a contractible space. -/
def contractionPoint (S : Type*) [TopologicalSpace S] [ContractibleSpace S] : S :=
  Classical.choose (id_nullhomotopic S)

/-- The chosen point comes with a homotopy from its constant map to the identity. -/
theorem contractionPoint_homotopic (S : Type*) [TopologicalSpace S]
    [ContractibleSpace S] :
    (ContinuousMap.const S (contractionPoint S)).Homotopic (ContinuousMap.id S) :=
  (Classical.choose_spec (id_nullhomotopic S)).symm

/-- Projection from a product with a contractible factor is a homotopy equivalence. -/
def contractibleProdHomotopyEquiv (S X : Type*) [TopologicalSpace S]
    [TopologicalSpace X] [ContractibleSpace S] : (S × X) ≃ₕ X where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const X (contractionPoint S)).prodMk (ContinuousMap.id X)
  left_inv := (contractionPoint_homotopic S).prodMap (.refl (ContinuousMap.id X))
  right_inv := .refl (ContinuousMap.id X)

@[simp] theorem contractibleProdHomotopyEquiv_apply (S X : Type*)
    [TopologicalSpace S] [TopologicalSpace X] [ContractibleSpace S] (p : S × X) :
    contractibleProdHomotopyEquiv S X p = p.2 := rfl

/-- The forward continuous map is definitionally the second projection. -/
@[simp] theorem contractibleProdHomotopyEquiv_projection_toContinuousMap
    (S X : Type*) [TopologicalSpace S] [TopologicalSpace X] [ContractibleSpace S] :
    (contractibleProdHomotopyEquiv S X).toFun = ContinuousMap.snd := rfl

@[simp] theorem contractibleProdHomotopyEquiv_symm_apply (S X : Type*)
    [TopologicalSpace S] [TopologicalSpace X] [ContractibleSpace S] (x : X) :
    (contractibleProdHomotopyEquiv S X).symm x = (contractionPoint S, x) := rfl

@[simp] theorem contractibleProdHomotopyEquiv_symm_apply_snd (S X : Type*)
    [TopologicalSpace S] [TopologicalSpace X] [ContractibleSpace S] (x : X) :
    ((contractibleProdHomotopyEquiv S X).symm x).2 = x := rfl

variable {A A' B B' : Type*}
  [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B']

/-- The map of topological sums induced by two continuous maps. -/
def sumContinuousMap (f : C(A, A')) (g : C(B, B')) : C(A ⊕ B, A' ⊕ B') :=
  ⟨Sum.map f g, f.continuous.sumMap g.continuous⟩

@[simp] theorem sumContinuousMap_apply (f : C(A, A')) (g : C(B, B')) (x : A ⊕ B) :
    sumContinuousMap f g x = Sum.map f g x := rfl

/-- Two homotopies combine into a homotopy on their actual topological sums. -/
def sumHomotopy {f₀ f₁ : C(A, A')} {g₀ g₁ : C(B, B')}
    (F : f₀.Homotopy f₁) (G : g₀.Homotopy g₁) :
    (sumContinuousMap f₀ g₀).Homotopy (sumContinuousMap f₁ g₁) where
  toFun := Sum.elim (fun p => Sum.inl (F p)) (fun p => Sum.inr (G p)) ∘
    Homeomorph.prodSumDistrib
  continuous_toFun :=
    ((continuous_inl.comp F.continuous).sumElim (continuous_inr.comp G.continuous)).comp
      Homeomorph.prodSumDistrib.continuous
  map_zero_left := by
    intro x
    cases x with
    | inl a => exact congrArg Sum.inl (F.map_zero_left a)
    | inr b => exact congrArg Sum.inr (G.map_zero_left b)
  map_one_left := by
    intro x
    cases x with
    | inl a => exact congrArg Sum.inl (F.map_one_left a)
    | inr b => exact congrArg Sum.inr (G.map_one_left b)

/-- Homotopy equivalences induce a homotopy equivalence of topological sums. -/
def sumHomotopyEquiv (eA : A ≃ₕ A') (eB : B ≃ₕ B') : (A ⊕ B) ≃ₕ (A' ⊕ B') where
  toFun := sumContinuousMap eA.toFun eB.toFun
  invFun := sumContinuousMap eA.invFun eB.invFun
  left_inv := by
    rcases eA.left_inv with ⟨F⟩
    rcases eB.left_inv with ⟨G⟩
    refine ⟨(sumHomotopy F G).cast ?_ ?_⟩
    · ext x
      cases x <;> rfl
    · ext x
      cases x <;> rfl
  right_inv := by
    rcases eA.right_inv with ⟨F⟩
    rcases eB.right_inv with ⟨G⟩
    refine ⟨(sumHomotopy F G).cast ?_ ?_⟩
    · ext x
      cases x <;> rfl
    · ext x
      cases x <;> rfl

@[simp] theorem sumHomotopyEquiv_apply (eA : A ≃ₕ A') (eB : B ≃ₕ B') (x : A ⊕ B) :
    sumHomotopyEquiv eA eB x = Sum.map eA eB x := rfl

@[simp] theorem sumHomotopyEquiv_symm_apply (eA : A ≃ₕ A') (eB : B ≃ₕ B')
    (x : A' ⊕ B') :
    (sumHomotopyEquiv eA eB).symm x = Sum.map eA.symm eB.symm x := rfl

@[simp] theorem sumHomotopyEquiv_inl (eA : A ≃ₕ A') (eB : B ≃ₕ B') (a : A) :
    sumHomotopyEquiv eA eB (Sum.inl a) = Sum.inl (eA a) := rfl

@[simp] theorem sumHomotopyEquiv_inr (eA : A ≃ₕ A') (eB : B ≃ₕ B') (b : B) :
    sumHomotopyEquiv eA eB (Sum.inr b) = Sum.inr (eB b) := rfl

@[simp] theorem sumHomotopyEquiv_symm_inl (eA : A ≃ₕ A') (eB : B ≃ₕ B') (a : A') :
    (sumHomotopyEquiv eA eB).symm (Sum.inl a) = Sum.inl (eA.symm a) := rfl

@[simp] theorem sumHomotopyEquiv_symm_inr (eA : A ≃ₕ A') (eB : B ≃ₕ B') (b : B') :
    (sumHomotopyEquiv eA eB).symm (Sum.inr b) = Sum.inr (eB.symm b) := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology
