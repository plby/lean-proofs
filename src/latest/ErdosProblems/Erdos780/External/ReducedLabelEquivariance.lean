import ErdosProblems.Erdos780.External.SignedTargetOrbits

namespace ReducedLabelEquivariance

open TargetChains
open ZpTuckerScratch

variable {p n m : ℕ} [NeZero p]

noncomputable local instance : LinearOrder (LabelChainMap.TargetVertex p m) :=
  LabelChainMap.targetLinearOrder

theorem normalizedBasis_eq_labelList
    (lab : LabelChainMap.SourceVertex p n → LabelChainMap.TargetVertex p m)
    (l : List (LabelChainMap.SourceVertex p n)) :
    LabelChainMap.normalizedBasis lab l = TargetBridge.labelList lab l := by
  apply (TargetChains.toExterior ℤ (LabelChainMap.TargetVertex p m)).injective
  rw [LabelChainMap.toExterior_normalizedBasis]
  induction l with
  | nil => simp [LabelChainMap.exteriorFlag]
  | cons x xs ih =>
      rw [TargetBridge.toExterior_labelList_cons]
      simp only [LabelChainMap.exteriorFlag_cons, ih]

theorem normalizedMap_eq_labelLists
    (lab : LabelChainMap.SourceVertex p n → LabelChainMap.TargetVertex p m)
    (c : SourceFlags.Chain (LabelChainMap.SourceVertex p n)) :
    LabelChainMap.normalizedMap lab c = TargetBridge.labelLists lab c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • SourceFlags.basis l by
        simp [SourceFlags.basis]]
      simp only [map_smul, LabelChainMap.normalizedMap_basis,
        TargetBridge.labelLists_basis, normalizedBasis_eq_labelList]

theorem positiveLabelLists_eq_projectNormalized
    (lab : LabelChainMap.SourceVertex p n → LabelChainMap.TargetVertex p m)
    (c : SourceFlags.Chain (LabelChainMap.SourceVertex p n)) :
    PositiveTarget.labelLists lab c =
      TargetChains.projectPositive ℤ (LabelChainMap.TargetVertex p m)
        (LabelChainMap.normalizedMap lab c) := by
  apply Subtype.ext
  simp only [PositiveTarget.labelLists, LinearMap.comp_apply,
    normalizedMap_eq_labelLists]

/-- The reduced exterior labeling map is equivariant for the literal
positive target action. -/
theorem positiveLabelLists_equivariant
    (lab : LabelChainMap.SourceVertex p n → LabelChainMap.TargetVertex p m)
    (heq : IsEquivariant lab) (a : ZMod p)
    (c : SourceFlags.Chain (LabelChainMap.SourceVertex p n)) :
    PositiveTarget.labelLists lab
        (SourceFlags.mapVertices (NonzeroSignedVector.shift a) c) =
      SignedTargetOrbits.targetAct a (PositiveTarget.labelLists lab c) := by
  rw [positiveLabelLists_eq_projectNormalized,
    positiveLabelLists_eq_projectNormalized,
    LabelChainMap.normalizedMap_equivariant lab heq]
  apply Subtype.ext
  exact congrArg Subtype.val
    (TargetChains.projectPositive_map_projectPositive
      (LabelChainMap.targetShift a) (LabelChainMap.normalizedMap lab c)).symm

end ReducedLabelEquivariance
