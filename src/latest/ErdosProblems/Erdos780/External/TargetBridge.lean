import ErdosProblems.Erdos780.External.SourceFlags
import ErdosProblems.Erdos780.External.TargetChains

namespace TargetBridge

open TargetChains

noncomputable section

variable {X V : Type*} [Fintype V] [LinearOrder V]

def wedgePrepend (v : V) : FullChain ℤ V →ₗ[ℤ] FullChain ℤ V :=
  (toExterior ℤ V).symm.toLinearMap ∘ₗ
    (LinearMap.mulLeft ℤ (ExteriorAlgebra.ι ℤ (Finsupp.single v 1))) ∘ₗ
      (toExterior ℤ V).toLinearMap

@[simp]
theorem toExterior_wedgePrepend (v : V) (c : FullChain ℤ V) :
    toExterior ℤ V (wedgePrepend v c) =
      ExteriorAlgebra.ι ℤ (Finsupp.single v 1) * toExterior ℤ V c := by
  simp [wedgePrepend]

def labelList (lab : X → V) : List X → FullChain ℤ V
  | [] => (toExterior ℤ V).symm 1
  | x :: xs => wedgePrepend (lab x) (labelList lab xs)

@[simp]
theorem toExterior_labelList_nil (lab : X → V) :
    toExterior ℤ V (labelList lab []) = 1 := by
  simp [labelList]

@[simp]
theorem toExterior_labelList_cons (lab : X → V) (x : X) (xs : List X) :
    toExterior ℤ V (labelList lab (x :: xs)) =
      ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) *
        toExterior ℤ V (labelList lab xs) := by
  simp [labelList]

def labelLists (lab : X → V) : SourceFlags.Chain X →ₗ[ℤ] FullChain ℤ V :=
  (Finsupp.lift (FullChain ℤ V) ℤ (List X)) (labelList lab)

@[simp]
theorem labelLists_basis (lab : X → V) (l : List X) :
    labelLists lab (SourceFlags.basis l) = labelList lab l := by
  simp [labelLists, SourceFlags.basis]

theorem labelLists_prepend (lab : X → V) (x : X) (c : SourceFlags.Chain X) :
    labelLists lab (SourceFlags.prepend x c) =
      wedgePrepend (lab x) (labelLists lab c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • SourceFlags.basis l by
        simp [SourceFlags.basis]]
      simp [labelList]

theorem boundary_labelList (lab : X → V) (l : List X) :
    boundary ℤ V (labelList lab l) =
      labelLists lab (SourceFlags.boundaryBasis l) := by
  induction l with
  | nil =>
      apply (toExterior ℤ V).injective
      simp [labelList, SourceFlags.boundaryBasis, exteriorContraction,
        CliffordAlgebra.contractLeft_one]
  | cons x xs ih =>
      rw [SourceFlags.boundaryBasis_cons, map_sub, labelLists_basis,
        labelLists_prepend]
      apply (toExterior ℤ V).injective
      rw [map_sub, toExterior_boundary, toExterior_labelList_cons,
        toExterior_wedgePrepend]
      change CliffordAlgebra.contractLeft (augmentation ℤ V)
          (ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) *
            toExterior ℤ V (labelList lab xs)) = _
      rw [CliffordAlgebra.contractLeft_ι_mul, augmentation_single, one_smul]
      have ihE := congrArg (toExterior ℤ V) ih
      rw [show CliffordAlgebra.contractLeft (augmentation ℤ V)
          (toExterior ℤ V (labelList lab xs)) =
          toExterior ℤ V (labelLists lab (SourceFlags.boundaryBasis xs)) by
        simpa [exteriorContraction] using ihE]

theorem labelLists_boundary (lab : X → V) (c : SourceFlags.Chain X) :
    boundary ℤ V (labelLists lab c) =
      labelLists lab (SourceFlags.boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • SourceFlags.basis l by
        simp [SourceFlags.basis]]
      simp only [map_smul, labelLists_basis, SourceFlags.boundary_basis]
      rw [boundary_labelList]

/-! The direct tuple formula requested by the target-chain construction. -/
theorem labelList_eq_ιMulti (lab : X → V) (l : List X) :
    toExterior ℤ V (labelList lab l) =
      ExteriorAlgebra.ιMulti ℤ l.length
        (fun i => Finsupp.single (lab (l.get i)) 1) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [toExterior_labelList_cons]
      change _ = ExteriorAlgebra.ιMulti ℤ xs.length.succ
        (fun i : Fin xs.length.succ =>
          Finsupp.single (lab ((x :: xs).get i)) 1)
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 1

theorem labelList_eq_zero_of_repeated (lab : X → V) (l : List X)
    (h : ¬ Function.Injective (fun i => lab (l.get i))) :
    labelList lab l = 0 := by
  apply (toExterior ℤ V).injective
  rw [map_zero, labelList_eq_ιMulti]
  apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
  intro hinj
  apply h
  intro i j hij
  apply hinj
  exact congrArg (fun v : V => Finsupp.single v (1 : ℤ)) hij

end

end TargetBridge
