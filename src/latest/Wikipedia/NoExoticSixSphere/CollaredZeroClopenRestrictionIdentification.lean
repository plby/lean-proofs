import Wikipedia.NoExoticSixSphere.CollaredZeroClopenRestrictionComparison

/-!
# Identify a component boundary with its actual original zero subset

When a clopen state restriction retains the whole zero set, its native
zero manifold is compared directly with the original zero manifold. When
the retained zero set is a specified open subset, equality of those sets
specializes the existing framed comparison. Every normal column and both
native atlases are retained.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredZero.ClopenRestriction

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  (U : Opens S.Space) (hU : IsClosed (U : Set S.Space))

def zeroDiffeomorphOfFull (hfull : S.zeroOpen U = ⊤) :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    (S.restrictClopen U hU).Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ S.Zero := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  let e : S.zeroOpen U ≃ S.Zero :=
    { toFun := Subtype.val
      invFun := fun p ↦ ⟨p, by rw [hfull]; trivial⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let D : S.zeroOpen U ≃ₘ⟮𝓡 6, 𝓡 6⟯ S.Zero :=
    { toEquiv := e
      contMDiff_toFun := contMDiff_subtype_val
      contMDiff_invFun :=
        (ContMDiff.subtypeVal_comp_iff (S.zeroOpen U) e.symm).mp contMDiff_id }
  exact (S.restrictClopenZeroDiffeomorph U hU).trans D

def comparisonOfFull (m : S.Space) (m' : (S.restrictClopen U hU).Space)
    (hfull : S.zeroOpen U = ⊤) :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    StabilizedFramedDiffeomorph
      (CollaredZero.embedding (S.restrictClopen U hU))
      (CollaredZero.normalFrame (S.restrictClopen U hU) m')
      (CollaredZero.embedding S) (CollaredZero.normalFrame S m) := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  refine
    { extra := 0
      ambient := LinearIsometryEquiv.refl ℝ (Vector S.embedding.ambientDimension)
      normal := LinearIsometryEquiv.refl ℝ (Vector (S.embedding.ambientDimension - 6))
      diffeomorph := zeroDiffeomorphOfFull S U hU hfull
      embedding_eq := ?_
      frame_eq := ?_ }
  · intro p
    change S.embedding.toFun p.val.val =
      appendZeroMap S.embedding.ambientDimension 0 (S.embedding.toFun p.val.val)
    rw [FramedBlock.appendZero_zero]
  · intro p v
    change (CollaredZero.normalFrame S m).ambient
        (S.restrictClopenZeroDiffeomorph U hU p).val v =
      BlockSum.operator 0 ((CollaredZero.normalFrame (S.restrictClopen U hU) m').ambient p) v
    rw [BlockSum.operator_zero]
    exact (sixFrame S U hU m m' p v).symm

def comparisonOfFullSymm (m : S.Space) (m' : (S.restrictClopen U hU).Space)
    (hfull : S.zeroOpen U = ⊤) :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    StabilizedFramedDiffeomorph
      (CollaredZero.embedding S) (CollaredZero.normalFrame S m)
      (CollaredZero.embedding (S.restrictClopen U hU))
      (CollaredZero.normalFrame (S.restrictClopen U hU) m') := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  exact StabilizedFramedDiffeomorph.symmOfZero (comparisonOfFull S U hU m m' hfull) rfl

def comparisonOfZeroOpenEq (m : S.Space) (m' : (S.restrictClopen U hU).Space)
    (V : Opens S.Zero) (hV : IsClosed (V : Set S.Zero)) (h : S.zeroOpen U = V) :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    StabilizedFramedDiffeomorph
      (CollaredZero.embedding (S.restrictClopen U hU))
      (CollaredZero.normalFrame (S.restrictClopen U hU) m')
      (ClopenEmbedding.restrict (CollaredZero.embedding S) V hV)
      (ClopenEmbedding.restrictNormalFrame (CollaredZero.embedding S) V hV
        (CollaredZero.normalFrame S m)) := by
  subst V
  exact comparison S U hU m m'

end NoExoticSixSphere.CollaredZero.ClopenRestriction
