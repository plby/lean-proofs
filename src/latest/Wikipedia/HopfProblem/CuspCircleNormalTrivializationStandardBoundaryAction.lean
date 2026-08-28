import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealSphere
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFourCircleParameter

/-!
# The literal standard circle action on the product of unit spheres

The standard normal boundary is the genuine unit two-sphere in real
three-space times the genuine unit three-sphere in real four-space.
The original period-one circle fixes the first factor and acts on the
second by the explicit real rotation. No action is transported from
the threefold or from an abstract boundary model.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

local notation "Circle" => AddCircle (1 : ℝ)

/-- The standard unit three-sphere in genuine Euclidean real four-space. -/
abbrev UnitThreeSphere := Metric.sphere (0 : RealFour.Space) 1

/-- The literal product of the standard real unit two-sphere and three-sphere. -/
abbrev StandardNormalBoundary := RealSphere.UnitTwoSphere × UnitThreeSphere

/-- The circle fixes the base and applies the actual real rotation to the unit normal. -/
def standardBoundaryCircleAction (t : Circle) (p : StandardNormalBoundary) :
    StandardNormalBoundary :=
  (p.1, ⟨RealFour.circleRotation t p.2, by
    simpa only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
      using p.2.property⟩)

@[simp] theorem standardBoundaryCircleAction_fst (t : Circle) (p : StandardNormalBoundary) :
    (standardBoundaryCircleAction t p).1 = p.1 := rfl

@[simp] theorem standardBoundaryCircleAction_snd_coe (t : Circle)
    (p : StandardNormalBoundary) :
    ((standardBoundaryCircleAction t p).2 : RealFour.Space) =
      RealFour.circleRotation t p.2 := rfl

@[simp] theorem standardBoundaryCircleAction_zero (p : StandardNormalBoundary) :
    standardBoundaryCircleAction 0 p = p := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change RealFour.circleRotation 0 (p.2 : RealFour.Space) = p.2
    rw [RealFour.circleRotation_zero]
    rfl

theorem standardBoundaryCircleAction_add (s t : Circle) (p : StandardNormalBoundary) :
    standardBoundaryCircleAction (s + t) p =
      standardBoundaryCircleAction s (standardBoundaryCircleAction t p) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change RealFour.circleRotation (s + t) (p.2 : RealFour.Space) =
      RealFour.circleRotation s (RealFour.circleRotation t p.2)
    rw [RealFour.circleRotation_add]
    rfl

/-- Joint continuity uses the original circle topology and the ordinary sphere topologies. -/
theorem standardBoundaryCircleAction_continuous :
    Continuous (fun q : Circle × StandardNormalBoundary =>
      standardBoundaryCircleAction q.1 q.2) := by
  have ht : Continuous (fun q : Circle × StandardNormalBoundary => q.1) := continuous_fst
  have hp : Continuous (fun q : Circle × StandardNormalBoundary => q.2) := continuous_snd
  have hn : Continuous (fun q : Circle × StandardNormalBoundary => q.2.2) := hp.snd
  have hv : Continuous (fun q : Circle × StandardNormalBoundary =>
      (q.2.2 : RealFour.Space)) := continuous_subtype_val.comp hn
  have hpair : Continuous (fun q : Circle × StandardNormalBoundary =>
      (q.1, (q.2.2 : RealFour.Space))) := ht.prodMk hv
  have hr := RealFour.continuous_circleRotation.comp
    (f := fun q : Circle × StandardNormalBoundary => (q.1, (q.2.2 : RealFour.Space))) hpair
  have hs : Continuous (fun q : Circle × StandardNormalBoundary =>
      (standardBoundaryCircleAction q.1 q.2).2) := hr.subtype_mk _
  exact hp.fst.prodMk hs

/-- The literal action as a genuine additive-circle action. -/
@[instance_reducible]
def standardBoundaryCircleAddAction : AddAction Circle StandardNormalBoundary where
  vadd := standardBoundaryCircleAction
  zero_vadd := standardBoundaryCircleAction_zero
  add_vadd := standardBoundaryCircleAction_add

@[simp] theorem standardBoundaryCircleAddAction_vadd (t : Circle) (p : StandardNormalBoundary) :
    letI := standardBoundaryCircleAddAction
    t +ᵥ p = standardBoundaryCircleAction t p := rfl

/-- The native continuous action map on the literal product of unit spheres. -/
def standardBoundaryCircleActionMap : C(Circle × StandardNormalBoundary, StandardNormalBoundary) :=
  ⟨fun q => standardBoundaryCircleAction q.1 q.2, standardBoundaryCircleAction_continuous⟩

@[simp] theorem standardBoundaryCircleActionMap_apply (t : Circle) (p : StandardNormalBoundary) :
    standardBoundaryCircleActionMap (t, p) = standardBoundaryCircleAction t p := rfl

theorem standardBoundaryCircleAddAction_continuous :
    letI := standardBoundaryCircleAddAction
    ContinuousVAdd Circle StandardNormalBoundary := by
  let := standardBoundaryCircleAddAction
  exact ⟨standardBoundaryCircleAction_continuous⟩

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
