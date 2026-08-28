import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy
import Wikipedia.SmoothSixDPoincare.FundamentalGroupMapTools

/-!

# Every original based loop is the image of a literal unit-circle map

The one-dimensional cube quotient gives a fixed actual loop on S1.
Each original based loop descends through that quotient, and mapping
the fixed circle loop recovers its original path class exactly. This
factorization also retains nullity after any continuous map, including
the actual inclusion into a surgery body.
-/

noncomputable section

open Function ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.CircleLoopRepresentatives

open NoExoticSixSphere SmoothCube
open Wikipedia.SmoothSixDPoincare

def parameterLoop : Path (spherePole 1) (spherePole 1) :=
  genLoopEquivOfUnique (Fin 1) (toGenLoop ⟨ContinuousMap.id (Sphere 1), rfl⟩)

def parameterClass : FundamentalGroup (Sphere 1) (spherePole 1) :=
  Path.Homotopic.Quotient.mk parameterLoop

variable {X : Type*} [TopologicalSpace X] {x : X}

def ofLoop (p : Path x x) : C(Sphere 1, X) :=
  descend (by decide : 0 < 1) ((genLoopEquivOfUnique (Fin 1)).symm p)

theorem ofLoop_pole (p : Path x x) : ofLoop p (spherePole 1) = x :=
  descend_pole (by decide : 0 < 1) _

theorem ofLoop_parameterClass (p : Path x x) :
    FundamentalGroup.mapOfEq (ofLoop p) (ofLoop_pole p) parameterClass =
      Path.Homotopic.Quotient.mk p := by
  rw [FundamentalGroup.mapOfEq_apply]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  change ofLoop p (quotient 1 (fun _ ↦ t)) = p t
  exact descend_quotient (by decide : 0 < 1) _ _

theorem exists_circleMap (x : X) (c : FundamentalGroup X x) :
    ∃ f : C(Sphere 1, X), ∃ h : f (spherePole 1) = x,
      FundamentalGroup.mapOfEq f h parameterClass = c := by
  obtain ⟨p⟩ := c
  exact ⟨ofLoop p, ofLoop_pole p, ofLoop_parameterClass p⟩

theorem mapOfEq_rfl (f : C(Sphere 1, X)) :
    FundamentalGroup.mapOfEq f (rfl : f (spherePole 1) = f (spherePole 1)) =
      FundamentalGroup.map f (spherePole 1) := by
  apply MonoidHom.ext
  intro g
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [FundamentalGroup.mapOfEq_apply]
    rfl

theorem mapped_class_eq_one_iff {f : C(Sphere 1, X)} (h : f (spherePole 1) = x)
    {c : FundamentalGroup X x} (hc : FundamentalGroup.mapOfEq f h parameterClass = c)
    {Y : Type*} [TopologicalSpace Y] (q : C(X, Y)) :
    FundamentalGroup.map q x c = 1 ↔
      FundamentalGroup.map (q.comp f) (spherePole 1) parameterClass = 1 := by
  subst x
  rw [← hc, mapOfEq_rfl, FundamentalGroupTools.map_comp]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.CircleLoopRepresentatives
