import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy
import Wikipedia.NoExoticSixSphere.FiberQuotientComparison

/-!
# The actual fiber lift of a characteristic disk boundary

A characteristic disk gives a nullhomotopy of its attaching map after
inclusion. Contracting the disk to a selected boundary point produces a
based map into the original homotopy fiber. Projection recovers the exact
attaching map, while the quotient-loop coordinate follows the literal
straight segments in the characteristic disk.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DiskBoundaryFiberLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (a : C(DiskCylinder.Sphere (E := E), X))
  (F : C(DiskCylinder.Disk (E := E), Y))
  (hF : ∀ s, F (DiskCylinder.boundaryToDisk s) = f (a s))
  (b : DiskCylinder.Sphere (E := E)) (x : X) (hx : a b = x)

def boundaryNullhomotopy :
    (f.comp a).HomotopyRel (ContinuousMap.const _ (f x)) {b} :=
  (DiskBoundary.contraction F b).cast (ContinuousMap.ext hF)
    (by rw [hF b, hx])

def lift : C(DiskCylinder.Sphere (E := E), HomotopyFiber.Space f (f x)) :=
  HomotopyFiber.lift f (f x) a (boundaryNullhomotopy f a F hF b x hx).toHomotopy

theorem projection_lift :
    (HomotopyFiber.projection f (f x)).comp (lift f a F hF b x hx) = a := rfl

theorem lift_path (s : DiskCylinder.Sphere (E := E)) (t : unitInterval) :
    (lift f a F hF b x hx s).val.2 t =
      F (DiskBoundary.segment (DiskCylinder.boundaryToDisk b)
        (t, DiskCylinder.boundaryToDisk s)) := rfl

theorem lift_basepoint : lift f a F hF b x hx b = HomotopyFiber.basepoint f x := by
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · apply ContinuousMap.ext
    intro t
    change F (DiskBoundary.segment (DiskCylinder.boundaryToDisk b)
      (t, DiskCylinder.boundaryToDisk b)) = f x
    rw [DiskBoundary.segment_fixed, hF b, hx]

theorem projection_map_lift {N : Type*}
    (c : HomotopyGroup N (DiskCylinder.Sphere (E := E)) b) :
    HigherHomotopy.map (N := N) (HomotopyFiber.projection f (f x))
      (HomotopyFiber.projection_basepoint f x)
        (HigherHomotopy.map (N := N) (lift f a F hF b x hx)
          (lift_basepoint f a F hF b x hx) c) =
      HigherHomotopy.map (N := N) a hx c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

variable {Z : Type*} [TopologicalSpace Z]
  (q : C(Y, Z)) (z : Z) (hq : ∀ y, q (f y) = z)

def quotientLoops : C(DiskCylinder.Sphere (E := E), Path z z) :=
  (FiberQuotientComparison.toLoops f q z hq x).comp (lift f a F hF b x hx)

theorem quotientLoops_apply (s : DiskCylinder.Sphere (E := E)) (t : unitInterval) :
    quotientLoops f a F hF b x hx q z hq s t =
      q (F (DiskBoundary.segment (DiskCylinder.boundaryToDisk b)
        (t, DiskCylinder.boundaryToDisk s))) := rfl

theorem quotientLoops_basepoint :
    quotientLoops f a F hF b x hx q z hq b = Path.refl z := by
  change FiberQuotientComparison.toLoops f q z hq x (lift f a F hF b x hx b) = _
  rw [lift_basepoint]
  exact FiberQuotientComparison.toLoops_basepoint f q z hq x

end NoExoticSixSphere.DiskBoundaryFiberLift
