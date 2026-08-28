import Wikipedia.NoExoticSixSphere.HomotopyPullbackDiagonal
import Wikipedia.NoExoticSixSphere.VariableEndpointPathTransport
import Wikipedia.NoExoticSixSphere.EndingPathLoopAppend
import Wikipedia.HopfProblem.OrbitPairHomotopyFiber

/-!
# Moving the first endpoint in the actual pullback projection fiber

A fiber point includes a path from its first source endpoint to the
fixed basepoint. Shorten that path while transporting the inner target
path with its own terminal value. The deformation starts at the exact
original fiber point and ends over the fixed first endpoint.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem OrbitPair

namespace NoExoticSixSphere.HomotopyPullbackDiagonal

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (F : C(X, Y)) (x : X)

abbrev ProjectionFiber := HomotopyFiber.Space (left F) x

def secondPoint : C(ProjectionFiber F x, X) :=
  (right F).comp (HomotopyFiber.projection (left F) x)

def innerPath : C(ProjectionFiber F x, C(I, Y)) :=
  ⟨fun q ↦ q.val.1.val.2, continuous_snd.comp
    (continuous_subtype_val.comp (HomotopyFiber.projection (left F) x).continuous)⟩

def basePath : C(ProjectionFiber F x, EndingPath.Space x) :=
  ⟨fun q ↦ ⟨q.val.2, q.property.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

def sourceCurve : C(I × ProjectionFiber F x, X) := HomotopyFiber.evaluation (left F) x

theorem innerPath_source (q : ProjectionFiber F x) :
    innerPath F x q 0 = F (sourceCurve F x (0, q)) :=
  q.val.1.property.1.trans (congrArg F q.property.1.symm)

def transportedPaths : C(I × ProjectionFiber F x, C(I, Y)) :=
  PathFamilyTransport.family F (innerPath F x) (sourceCurve F x) (innerPath_source F x)

def movingPoint : C(I × ProjectionFiber F x, Space F) where
  toFun q := ⟨((sourceCurve F x q, secondPoint F x q.2), transportedPaths F x q),
    PathFamilyTransport.family_source F _ _ _ q.1 q.2,
    (PathFamilyTransport.family_target F _ _ _ q.1 q.2).trans q.2.val.1.property.2⟩
  continuous_toFun := (((sourceCurve F x).continuous.prodMk
    ((secondPoint F x).continuous.comp continuous_snd)).prodMk
      (transportedPaths F x).continuous).subtype_mk _

theorem movingPoint_zero (q : ProjectionFiber F x) : movingPoint F x (0, q) = q.val.1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact Prod.ext q.property.1 rfl
  · exact PathFamilyTransport.family_initial F _ _ _ q

def fiberDeformation : C(I × ProjectionFiber F x, ProjectionFiber F x) where
  toFun q := ⟨(movingPoint F x q, (EndingPath.shorten q.1 (basePath F x q.2)).val),
    EndingPath.shorten_source q.1 (basePath F x q.2),
    (EndingPath.shorten q.1 (basePath F x q.2)).property⟩
  continuous_toFun := ((movingPoint F x).continuous.prodMk
    (continuous_subtype_val.comp (EndingPath.continuous_shorten.comp
      (continuous_fst.prodMk ((basePath F x).continuous.comp continuous_snd))))).subtype_mk _

theorem fiberDeformation_zero (q : ProjectionFiber F x) : fiberDeformation F x (0, q) = q := by
  apply Subtype.ext
  exact Prod.ext (movingPoint_zero F x q)
    (congrArg Subtype.val (EndingPath.shorten_zero (basePath F x q)))

theorem fiberDeformation_first (s : I) (q : ProjectionFiber F x) :
    left F (fiberDeformation F x (s, q)).val.1 = q.val.2 s := rfl

theorem fiberDeformation_one_first (q : ProjectionFiber F x) :
    left F (fiberDeformation F x (1, q)).val.1 = x := q.property.2

theorem fiberDeformation_one_basePath (q : ProjectionFiber F x) :
    (fiberDeformation F x (1, q)).val.2 = ContinuousMap.const I x :=
  congrArg Subtype.val (EndingPath.shorten_one (basePath F x q))

end NoExoticSixSphere.HomotopyPullbackDiagonal
