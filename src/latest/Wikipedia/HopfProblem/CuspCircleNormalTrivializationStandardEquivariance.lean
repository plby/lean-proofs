import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardNeighborhood
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFourCircleParameter

/-!
# The standard two-block circle rotation in the actual normal neighborhood

The standard real four-dimensional normal action consists of two equal
rotation blocks. The native standard-product diffeomorphism and compact
disk embedding intertwine these explicit blocks with the original
period-one action on the threefold.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

attribute [local instance] Threefold.chartedSpace

/-- The standard two equal rotation blocks act on the actual open unit four-ball. -/
def standardCircleAction (t : Circle) (p : StandardOpenNormalProduct) :
    StandardOpenNormalProduct :=
  (p.1, ⟨RealFour.circleRotation t (p.2 : RealFour.Space), by
    change RealFour.circleRotation t (p.2 : RealFour.Space) ∈ ball (0 : RealFour.Space) 1
    rw [mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
    exact mem_ball_zero_iff.mp p.2.property⟩)

@[simp] theorem standardCircleAction_fst (t : Circle) (p : StandardOpenNormalProduct) :
    (standardCircleAction t p).1 = p.1 := rfl

@[simp] theorem standardCircleAction_snd_coe (t : Circle) (p : StandardOpenNormalProduct) :
    ((standardCircleAction t p).2 : RealFour.Space) = RealFour.circleRotation t p.2 := rfl

@[simp] theorem standardCircleAction_zero (p : StandardOpenNormalProduct) :
    standardCircleAction 0 p = p := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact congrFun (congrArg (fun e : RealFour.Space ≃ₗᵢ[ℝ] RealFour.Space => (e :
      RealFour.Space → RealFour.Space)) RealFour.circleRotation_zero) p.2

theorem standardCircleAction_add (s t : Circle) (p : StandardOpenNormalProduct) :
    standardCircleAction (s + t) p = standardCircleAction s (standardCircleAction t p) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change RealFour.circleRotation (s + t) (p.2 : RealFour.Space) =
      RealFour.circleRotation s (RealFour.circleRotation t p.2)
    rw [RealFour.circleRotation_add]
    rfl

/-- The standard-product action is an actual additive action on the given open manifold. -/
@[instance_reducible] def standardCircleAddAction : AddAction Circle StandardOpenNormalProduct where
  vadd := standardCircleAction
  zero_vadd := standardCircleAction_zero
  add_vadd := standardCircleAction_add

theorem standardCircleAction_continuous :
    Continuous (fun q : Circle × StandardOpenNormalProduct => standardCircleAction q.1 q.2) := by
  have hv : Continuous (fun q : Circle × StandardOpenNormalProduct =>
      (q.2.2 : RealFour.Space)) := continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hi : Continuous (fun q : Circle × StandardOpenNormalProduct =>
      (q.1, (q.2.2 : RealFour.Space))) :=
    (continuous_fst : Continuous (fun q : Circle × StandardOpenNormalProduct => q.1)).prodMk hv
  have hr : Continuous (fun q : Circle × StandardOpenNormalProduct =>
      RealFour.circleRotation q.1 (q.2.2 : RealFour.Space)) := by
    simpa only [Function.comp_def] using RealFour.continuous_circleRotation.comp hi
  have hn : Continuous (fun q : Circle × StandardOpenNormalProduct =>
      (standardCircleAction q.1 q.2).2) := by
    apply continuous_induced_rng.mpr
    exact hr
  have hb : Continuous (fun q : Circle × StandardOpenNormalProduct => q.2.1) :=
    continuous_fst.comp continuous_snd
  exact hb.prodMk hn

/-- Exact equivariance of the literal inverse real-coordinate formula. -/
theorem standardUnitToNormal_circleAction (t : Circle) (p : StandardOpenNormalProduct) :
    standardUnitToNormalDiffeomorph (standardCircleAction t p) =
      roundCircleAction t (standardUnitToNormalDiffeomorph p) := by
  apply Subtype.ext
  rw [standardUnitToNormalDiffeomorph_coe, roundCircleAction_coe,
    standardUnitToNormalDiffeomorph_coe]
  apply Prod.ext
  · rfl
  · change RealFour.coordinateEquiv.symm
        (injectiveRadius • RealFour.circleRotation t (p.2 : RealFour.Space)) =
      (DeltaSweep.circleParameter t : ℂ) •
        RealFour.coordinateEquiv.symm (injectiveRadius • (p.2 : RealFour.Space))
    rw [← (RealFour.circleRotation t).map_smul,
      RealFour.coordinateEquiv_symm_circleRotation]

/-- The standard native diffeomorphism intertwines the literal original and standard actions. -/
theorem standardNeighborhoodDiffeomorph_circleAction (t : Circle) (p : StandardOpenNormalProduct) :
    neighborhoodCircleAction t (standardNeighborhoodDiffeomorph p) =
      standardNeighborhoodDiffeomorph (standardCircleAction t p) := by
  change neighborhoodCircleAction t (normalNeighborhoodDiffeomorph
      (standardUnitToNormalDiffeomorph p)) =
    normalNeighborhoodDiffeomorph (standardUnitToNormalDiffeomorph (standardCircleAction t p))
  rw [normalNeighborhoodDiffeomorph_circleAction, standardUnitToNormal_circleAction]

theorem standardNeighborhood_circleAction (t : Circle) (p : StandardOpenNormalProduct) :
    DeltaSweep.actionMap (t, (standardNeighborhoodDiffeomorph p : Threefold.Space)) =
      (standardNeighborhoodDiffeomorph (standardCircleAction t p) : Threefold.Space) :=
  congrArg (fun x : fixedCurveNeighborhood => (x : Threefold.Space))
    (standardNeighborhoodDiffeomorph_circleAction t p)

/-- The same explicit rotation blocks preserve the standard closed unit disk. -/
def standardClosedCircleAction (t : Circle) (p : StandardClosedNormalProduct) :
    StandardClosedNormalProduct :=
  (p.1, ⟨RealFour.circleRotation t (p.2 : RealFour.Space), by
    rw [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp p.2.property⟩)

@[simp] theorem standardClosedCircleAction_snd_coe (t : Circle) (p : StandardClosedNormalProduct) :
    ((standardClosedCircleAction t p).2 : RealFour.Space) = RealFour.circleRotation t p.2 := rfl

theorem standardClosedIntoOpen_circleAction (t : Circle) (p : StandardClosedNormalProduct) :
    standardClosedIntoOpen (standardClosedCircleAction t p) =
      standardCircleAction t (standardClosedIntoOpen p) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (1 / 2 : ℝ) • RealFour.circleRotation t (p.2 : RealFour.Space) =
      RealFour.circleRotation t ((1 / 2 : ℝ) • (p.2 : RealFour.Space))
    exact ((RealFour.circleRotation t).map_smul (1 / 2 : ℝ) (p.2 : RealFour.Space)).symm

/-- The actual compact standard disk embedding has precisely the same original circle action. -/
theorem standardClosedDiskMap_circleAction (t : Circle) (p : StandardClosedNormalProduct) :
    DeltaSweep.actionMap (t, standardClosedDiskMap p) =
      standardClosedDiskMap (standardClosedCircleAction t p) := by
  calc
    DeltaSweep.actionMap (t, standardClosedDiskMap p) =
        DeltaSweep.actionMap (t,
          (standardNeighborhoodDiffeomorph (standardClosedIntoOpen p) : Threefold.Space)) :=
      congrArg (fun x => DeltaSweep.actionMap (t, x)) (standardClosedDiskMap_eq_open_chart p)
    _ = (standardNeighborhoodDiffeomorph
        (standardCircleAction t (standardClosedIntoOpen p)) : Threefold.Space) :=
      standardNeighborhood_circleAction t (standardClosedIntoOpen p)
    _ = (standardNeighborhoodDiffeomorph
        (standardClosedIntoOpen (standardClosedCircleAction t p)) : Threefold.Space) :=
      congrArg (fun q => (standardNeighborhoodDiffeomorph q : Threefold.Space))
        (standardClosedIntoOpen_circleAction t p).symm
    _ = standardClosedDiskMap (standardClosedCircleAction t p) :=
      (standardClosedDiskMap_eq_open_chart (standardClosedCircleAction t p)).symm

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
