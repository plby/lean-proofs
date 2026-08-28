import Wikipedia.NoExoticSixSphere.StabilizedFramedDiffeomorph
import Wikipedia.NoExoticSixSphere.CollaredSeamSixFrame
import Wikipedia.NoExoticSixSphere.CollaredZeroReversalFrame
import Wikipedia.NoExoticSixSphere.CollaredZeroComponentFrame

/-!
# Constructed stabilized framed comparisons for the actual collared-state operations

Each state uses its native zero atlas and its constructed induced normal
frame. The reference boundary point only supplies a nonempty ambient
manifold; the frame has already been proved independent of that choice.
Surgery, reversal, and component restriction now produce actual framed
diffeomorphism data, including the exact ambient and normal isometries.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse
open LowSurgery FramedAttachingProduct RoundedTrace NativeSurgery

variable {B : Type} [TopologicalSpace B]

def referencePoint (S : LowCollaredSevenState B) (b : B) : S.Space := (S.collar.zeroPoint b).val

def Comparison (S U : LowCollaredSevenState B) (b : B) : Type :=
  letI := S.zeroAtlas; letI := U.zeroAtlas;
  StabilizedFramedDiffeomorph (embedding S) (normalFrame S (referencePoint S b))
    (embedding U) (normalFrame U (referencePoint U b))

def comparisonRefl (S : LowCollaredSevenState B) (b : B) : Comparison S S b := by
  let := S.zeroAtlas
  exact StabilizedFramedDiffeomorph.refl (embedding S) (normalFrame S (referencePoint S b))

def comparisonTrans {S U V : LowCollaredSevenState B} {b : B}
    (F : Comparison S U b) (G : Comparison U V b) : Comparison S V b := by
  let := S.zeroAtlas
  let := U.zeroAtlas
  let := V.zeroAtlas
  exact StabilizedFramedDiffeomorph.trans F G

def performComparison (S : LowCollaredSevenState B) (b : B) {d : ℕ}
    {f : Sphere d → S.Space} (A : FramedAttachingProduct S.embedding S.normalFrame f)
    (hA : A.radius = 2) (T : TimeData A) (hT : T.time = S.time) :
    Comparison S (S.perform A hA T hT) b := by
  let U := S.perform A hA T hT
  let := S.zeroAtlas
  let := U.zeroAtlas
  let m := referencePoint S b
  let m' := referencePoint U b
  let Q := CollaredSeam.performSixColumnChange S A hA T hT m m'
  refine StabilizedFramedDiffeomorph.ofReverseNormal (1 + (1 + (d + 1)))
    (S.performZeroDiffeomorph A hA T hT)
    (LinearIsometryEquiv.refl ℝ
      (Vector (S.embedding.ambientDimension + (1 + (1 + (d + 1)))))) Q ?_ ?_
  · intro p
    exact CollaredSeam.perform_embedding S A hA T hT p
  · intro p v
    exact CollaredSeam.perform_sixFrame S A hA T hT m m' p v

def reverseComparison (S : LowCollaredSevenState B) (b : B) : Comparison S S.reverse b := by
  let := S.zeroAtlas
  let := S.reverse.zeroAtlas
  let m := referencePoint S b
  let m' := referencePoint S.reverse b
  let Q := CollaredSeam.reversalSixColumnChange S m
  refine
    { extra := 0
      ambient := LinearIsometryEquiv.refl ℝ (Vector S.embedding.ambientDimension)
      normal := Q.symm
      diffeomorph := S.reverseZeroDiffeomorph
      embedding_eq := ?_
      frame_eq := ?_ }
  · intro p
    change S.embedding.toFun (S.reverseZeroDiffeomorph p).val =
      appendZeroMap S.embedding.ambientDimension 0 (S.embedding.toFun p.val)
    rw [S.reverseZeroDiffeomorph_point, FramedBlock.appendZero_zero]
  · intro p v
    change (normalFrame S.reverse m').ambient (S.reverseZeroDiffeomorph p) (Q.symm v) =
      BlockSum.operator 0 ((normalFrame S m).ambient p) v
    rw [normalFrame_point_independent S.reverse m m', BlockSum.operator_zero]
    have h := CollaredSeam.reverse_sixFrame S m p (Q.symm v)
    change (normalFrame S.reverse m).ambient (S.reverseZeroDiffeomorph p) (Q.symm v) =
      (normalFrame S m).ambient p (Q (Q.symm v)) at h
    exact h.trans (congrArg ((normalFrame S m).ambient p) (Q.apply_symm_apply v))

theorem reverseComparison_extra (S : LowCollaredSevenState B) (b : B) :
    letI := S.zeroAtlas; letI := S.reverse.zeroAtlas;
    (reverseComparison S b).extra = 0 := by
  let := S.zeroAtlas
  let := S.reverse.zeroAtlas
  rfl

section Component

variable [PathConnectedSpace B]

def componentComparison (S : LowCollaredSevenState B) (b : B) :
    Comparison (S.component b) S b := by
  let : LocallyPathConnectedSpace S.Space :=
    ChartedSpace.locallyPathConnectedSpace (Vector 7) S.Space
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  let m := referencePoint S b
  let m' := referencePoint (S.component b) b
  refine
    { extra := 0
      ambient := LinearIsometryEquiv.refl ℝ (Vector S.embedding.ambientDimension)
      normal := LinearIsometryEquiv.refl ℝ (Vector (S.embedding.ambientDimension - 6))
      diffeomorph := S.componentZeroDiffeomorph b
      embedding_eq := ?_
      frame_eq := ?_ }
  · intro p
    change S.embedding.toFun (S.componentZeroDiffeomorph b p).val =
      appendZeroMap S.embedding.ambientDimension 0 ((S.component b).embedding.toFun p.val)
    rw [S.componentZeroDiffeomorph_point]
    change S.embedding.toFun p.val.val =
      appendZeroMap S.embedding.ambientDimension 0 (S.embedding.toFun p.val.val)
    exact (FramedBlock.appendZero_zero S.embedding.ambientDimension _).symm
  · intro p v
    change (normalFrame S m).ambient (S.componentZeroDiffeomorph b p) v =
      BlockSum.operator 0 ((normalFrame (S.component b) m').ambient p) v
    rw [BlockSum.operator_zero]
    exact (CollaredSeam.component_sixFrame S b m m' p v).symm

theorem componentComparison_extra (S : LowCollaredSevenState B) (b : B) :
    letI := S.zeroAtlas; letI := (S.component b).zeroAtlas;
    (componentComparison S b).extra = 0 := by
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  rfl

def componentComparisonSymm (S : LowCollaredSevenState B) (b : B) :
    Comparison S (S.component b) b := by
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  exact StabilizedFramedDiffeomorph.symmOfZero (componentComparison S b)
    (componentComparison_extra S b)

end Component
end NoExoticSixSphere.CollaredZero
