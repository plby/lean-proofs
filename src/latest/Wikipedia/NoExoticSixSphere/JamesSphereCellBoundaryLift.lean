import Wikipedia.NoExoticSixSphere.DiskBoundaryFiberLift
import Wikipedia.NoExoticSixSphere.JamesSphereFiniteFiberQuotient

/-!
# The genuine second James cell and its based boundary lift

The attaching map is obtained from the original characteristic disk by
the proved one-letter homeomorphism. The all-zero cube corner maps to
the sphere pole. Straight contraction to that corner gives an explicit
based lift into the actual finite James fiber, with no choice of a
nullhomotopy or replacement of the original cell map.
-/

noncomputable section

open Metric Set
open scoped Topology unitInterval
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.CellBoundary

abbrev Coordinates (n : ℕ) := Fin (2 * n) → ℝ
abbrev Boundary (n : ℕ) := sphere (0 : Coordinates n) 1

def attaching (n : ℕ) : C(Boundary n, Sphere n) :=
  ((SecondStageCone.lowerSphere n).symm : C(_, _)).comp (PuncturedStage.attaching n 1).hom

theorem characteristic_boundary (n : ℕ) (s : Boundary n) :
    Cell.closedPresentation n 2 (DiskCylinder.boundaryToDisk s) =
      SecondStageCone.attaching n (attaching n s) := by
  apply Subtype.ext
  have h := congrArg (fun y : StageAttachment.lower n 1 ↦ y.val.val)
    ((SecondStageCone.lowerSphere n).apply_symm_apply (PuncturedStage.attaching n 1 s))
  exact h.symm

def cornerDisk (n : ℕ) : DiskCylinder.Disk (E := Coordinates n) :=
  ⟨JamesCellCube.unscale (2 * n) 0, JamesCellCube.unscale_mem_closedBall (2 * n) 0⟩

theorem array_corner (n : ℕ) (hn : 0 < n) :
    Cell.array n 2 (cornerDisk n).val = fun _ ↦ spherePole n := by
  funext i
  change SmoothCube.quotient n (JamesCellCube.block n 2
    (JamesCellCube.cube (2 * n) (JamesCellCube.unscale (2 * n) 0)) i) = spherePole n
  rw [JamesCellCube.cube_unscale]
  exact SmoothCube.quotient_boundary n _ ⟨⟨0, hn⟩, Or.inl rfl⟩

theorem characteristic_corner (n : ℕ) (hn : 0 < n) :
    Cell.characteristic n 2 (cornerDisk n).val = 1 := by
  change James.word (spherePole n) (List.ofFn (Cell.array n 2 (cornerDisk n).val)) = 1
  rw [array_corner n hn]
  simp only [List.ofFn_succ, List.ofFn_zero, James.word_cons, James.word_nil,
    James.letter_basepoint, one_mul]

def corner (n : ℕ) (hn : 0 < n) : Boundary n :=
  ⟨(cornerDisk n).val, by
    apply (PuncturedStage.boundary_iff n 1 (cornerDisk n)).mp
    change James.size (spherePole n) (Cell.characteristic n 2 (cornerDisk n).val) ≤ 1
    rw [characteristic_corner n hn]
    exact Nat.zero_le 1⟩

theorem boundary_corner (n : ℕ) (hn : 0 < n) :
    DiskCylinder.boundaryToDisk (corner n hn) = cornerDisk n := rfl

theorem attaching_corner (n : ℕ) (hn : 0 < n) :
    attaching n (corner n hn) = spherePole n := by
  apply SecondStageCone.attaching_injective n
  rw [← characteristic_boundary, boundary_corner]
  apply Subtype.ext
  exact (characteristic_corner n hn).trans (James.letter_basepoint (spherePole n)).symm

def lift (n : ℕ) (hn : 0 < n) : C(Boundary n, FiniteFiberQuotient.Fiber n (spherePole n)) :=
  DiskBoundaryFiberLift.lift (SecondStageCone.attaching n) (attaching n)
    (Cell.closedPresentation n 2) (characteristic_boundary n) (corner n hn)
      (spherePole n) (attaching_corner n hn)

theorem lift_corner (n : ℕ) (hn : 0 < n) :
    lift n hn (corner n hn) = FiniteFiberQuotient.basepoint n (spherePole n) :=
  DiskBoundaryFiberLift.lift_basepoint (SecondStageCone.attaching n) (attaching n)
    (Cell.closedPresentation n 2) (characteristic_boundary n) (corner n hn)
      (spherePole n) (attaching_corner n hn)

theorem lift_projection (n : ℕ) (hn : 0 < n) (s : Boundary n) :
    (lift n hn s).val.1 = attaching n s := rfl

theorem lift_path (n : ℕ) (hn : 0 < n) (s : Boundary n) (t : unitInterval) :
    (lift n hn s).val.2 t = Cell.closedPresentation n 2
      (DiskBoundary.segment (cornerDisk n) (t, DiskCylinder.boundaryToDisk s)) := rfl

theorem quotient_loop (n : ℕ) (hn : 0 < n) (s : Boundary n) (t : unitInterval) :
    FiniteFiberQuotient.toLoops n (spherePole n) (lift n hn s) t =
      SecondStage.quotientMap n (Cell.closedPresentation n 2
        (DiskBoundary.segment (cornerDisk n) (t, DiskCylinder.boundaryToDisk s))) := rfl

def liftHom (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d] :=
  HigherHomotopy.mapMonoidHom (N := Fin d) (lift n hn) (lift_corner n hn)

theorem projection_liftHom (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d]
    (c : π_ d (Boundary n) (corner n hn)) :
    HigherHomotopy.map (N := Fin d)
      (HomotopyFiber.projection (SecondStageCone.attaching n)
        (SecondStageCone.attaching n (spherePole n)))
      (HomotopyFiber.projection_basepoint (SecondStageCone.attaching n) (spherePole n))
        (liftHom n hn d c) = HigherHomotopy.map (N := Fin d) (attaching n)
          (attaching_corner n hn) c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

end NoExoticSixSphere.JamesSphere.CellBoundary
