import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepAction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticFibreTopology

/-!
# The actual delta-circle action on the original central elliptic surfaces

Each native central surface is already homeomorphic, by its original
inclusion, to the entire corresponding sphere fibre. The original global
circle action preserves that fibre. Restricting it and using this proved
homeomorphism gives a continuous action on the original central surface,
with no change of its quotient topology or complex atlas.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open EllipticFilling

local notation "Circle" => PeriodTorusHigherHomology.CircleTopology.Circle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The original central-surface inclusion, bundled as a continuous map. -/
def centralInclusionMap (j : Elliptic.Kind) : C(SpecialCentralSurface j, Space) :=
  ⟨EllipticGeometry.centralSurfaceInclusion j,
    EllipticGeometry.centralSurfaceInclusion_continuous j⟩

@[simp] theorem centralInclusionMap_apply (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    centralInclusionMap j x = EllipticGeometry.centralSurfaceInclusion j x := rfl

/-- Fibre preservation of the actual global action keeps every point
of the original central surface in its literal global elliptic fibre. -/
theorem actionMap_central_mem_fibre (j : Elliptic.Kind) (t : Circle)
    (x : SpecialCentralSurface j) :
    actionMap (t, centralInclusionMap j x) ∈
      projectionSphere ⁻¹' {EllipticGeometry.sphereValue j} := by
  let := VerticalAction.action
  change projectionSphere (actionMap (t, centralInclusionMap j x)) =
    EllipticGeometry.sphereValue j
  exact (VerticalAction.projectionSphere_action (circleParameter t)
    (centralInclusionMap j x)).trans
      (EllipticGeometry.projectionSphere_centralSurfaceInclusion j x)

/-- Restriction of the actual global action to the original quotient
surface, through its already proved native fibre homeomorphism. -/
def centralActionMap (j : Elliptic.Kind) :
    C(Circle × SpecialCentralSurface j, SpecialCentralSurface j) where
  toFun p := (EllipticGeometry.centralSurfaceFibreHomeomorph j).symm
    ⟨actionMap (p.1, centralInclusionMap j p.2), actionMap_central_mem_fibre j p.1 p.2⟩
  continuous_toFun :=
    (EllipticGeometry.centralSurfaceFibreHomeomorph j).symm.continuous.comp
      ((actionMap.continuous.comp
        (continuous_fst.prodMk
          ((centralInclusionMap j).continuous.comp continuous_snd))).subtype_mk _)

/-- This action is literally intertwined by the original central
inclusion, rather than merely by an abstract equivalence of spaces. -/
theorem centralInclusionMap_actionMap (j : Elliptic.Kind) (t : Circle)
    (x : SpecialCentralSurface j) :
    centralInclusionMap j (centralActionMap j (t, x)) =
      actionMap (t, centralInclusionMap j x) :=
  EllipticGeometry.centralSurfaceFibreHomeomorph_symm_inclusion j _

/-- Equivariance in the circle-first convention used by the actual
singular-homology sweep. -/
theorem actionMap_centralInclusion (j : Elliptic.Kind) (t : Circle)
    (x : SpecialCentralSurface j) :
    actionMap (t, centralInclusionMap j x) =
      centralInclusionMap j (centralActionMap j (t, x)) :=
  (centralInclusionMap_actionMap j t x).symm

@[simp] theorem centralActionMap_zero (j : Elliptic.Kind) (x : SpecialCentralSurface j) :
    centralActionMap j (0, x) = x := by
  apply EllipticGeometry.centralSurfaceInclusion_injective j
  change centralInclusionMap j (centralActionMap j (0, x)) = centralInclusionMap j x
  rw [centralInclusionMap_actionMap]
  let := circleAction
  exact zero_vadd Circle (centralInclusionMap j x)

theorem centralActionMap_add (j : Elliptic.Kind) (s t : Circle)
    (x : SpecialCentralSurface j) :
    centralActionMap j (s + t, x) = centralActionMap j (s, centralActionMap j (t, x)) := by
  apply EllipticGeometry.centralSurfaceInclusion_injective j
  change centralInclusionMap j (centralActionMap j (s + t, x)) =
    centralInclusionMap j (centralActionMap j (s, centralActionMap j (t, x)))
  rw [centralInclusionMap_actionMap, centralInclusionMap_actionMap,
    centralInclusionMap_actionMap]
  let := circleAction
  exact add_vadd s t (centralInclusionMap j x)

/-- The genuine period-one additive circle action on the original
special central elliptic quotient surface. -/
@[instance_reducible]
def centralCircleAction (j : Elliptic.Kind) : AddAction Circle (SpecialCentralSurface j) where
  vadd t x := centralActionMap j (t, x)
  zero_vadd := centralActionMap_zero j
  add_vadd := centralActionMap_add j

@[simp] theorem centralCircleAction_vadd (j : Elliptic.Kind) (t : Circle)
    (x : SpecialCentralSurface j) :
    letI := centralCircleAction j
    t +ᵥ x = centralActionMap j (t, x) := rfl

theorem centralCircleAction_continuous (j : Elliptic.Kind) :
    letI := centralCircleAction j
    ContinuousVAdd Circle (SpecialCentralSurface j) := by
  let := centralCircleAction j
  exact ⟨(centralActionMap j).continuous⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
