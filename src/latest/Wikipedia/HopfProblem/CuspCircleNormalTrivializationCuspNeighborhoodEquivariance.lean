import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspNeighborhood
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspEquivarianceCircle

/-!
# Circle-equivariance of the actual injective fixed-curve neighborhood

The uniform round normal domain is preserved by scalar multiplication.
Its diffeomorphism onto the original threefold neighborhood intertwines
that action with the original period-one circle action. Consequently the
actual open image is circle invariant, with no change of its atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

attribute [local instance] Threefold.chartedSpace

/-- The literal unit scalar action on the injective round normal domain. -/
def roundNormalAction (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (p : roundNormalProduct) :
    roundNormalProduct :=
  ⟨(p.val.1, (u : ℂ) • p.val.2), by
    change radiusSq ((u : ℂ) • p.val.2) < injectiveRadius ^ 2
    rw [radiusSq_unit_smul (u : ℂ) hu]
    exact p.property⟩

@[simp] theorem roundNormalAction_coe (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : roundNormalProduct) :
    (roundNormalAction u hu p : RiemannSphere × Fibre) = (p.val.1, (u : ℂ) • p.val.2) := rfl

@[simp] theorem roundToSmall_roundNormalAction (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : roundNormalProduct) :
    roundToSmall (roundNormalAction u hu p) = normalProductAction u hu (roundToSmall p) := rfl

theorem roundProductMap_normalAction (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (p : roundNormalProduct) :
    actionBiholomorph u (roundProductMap p) = roundProductMap (roundNormalAction u hu p) :=
  globalProductMap_normalProductAction u hu (roundToSmall p)

/-- The same literal round action for the original additive-circle parameter. -/
def roundCircleAction (t : Circle) (p : roundNormalProduct) : roundNormalProduct :=
  roundNormalAction (DeltaSweep.circleParameter t)
    (FixedCoordinates.CircleOrbit.circleParameter_norm t) p

@[simp] theorem roundCircleAction_coe (t : Circle) (p : roundNormalProduct) :
    (roundCircleAction t p : RiemannSphere × Fibre) =
      (p.val.1, (DeltaSweep.circleParameter t : ℂ) • p.val.2) := rfl

@[simp] theorem roundToSmall_roundCircleAction (t : Circle) (p : roundNormalProduct) :
    roundToSmall (roundCircleAction t p) = normalCircleAction t (roundToSmall p) := rfl

@[simp] theorem roundCircleAction_zero (p : roundNormalProduct) : roundCircleAction 0 p = p := by
  apply Subtype.ext
  change (p.val.1, (DeltaSweep.circleParameter 0 : ℂ) • p.val.2) = p.val
  rw [DeltaSweep.circleParameter_zero, Units.val_one, one_smul]

theorem roundCircleAction_add (s t : Circle) (p : roundNormalProduct) :
    roundCircleAction (s + t) p = roundCircleAction s (roundCircleAction t p) := by
  apply Subtype.ext
  change (p.val.1, (DeltaSweep.circleParameter (s + t) : ℂ) • p.val.2) =
    (p.val.1, (DeltaSweep.circleParameter s : ℂ) •
      ((DeltaSweep.circleParameter t : ℂ) • p.val.2))
  rw [DeltaSweep.circleParameter_add, Units.val_mul, mul_smul]

/-- The group laws hold on the actual round open submanifold. -/
@[instance_reducible] def roundCircleAddAction : AddAction Circle roundNormalProduct where
  vadd := roundCircleAction
  zero_vadd := roundCircleAction_zero
  add_vadd := roundCircleAction_add

theorem roundCircleAction_continuous :
    Continuous (fun q : Circle × roundNormalProduct => roundCircleAction q.1 q.2) := by
  have hp : Continuous (fun q : Circle × roundNormalProduct =>
      (q.2 : RiemannSphere × Fibre)) := continuous_subtype_val.comp continuous_snd
  have ht : Continuous (fun q : Circle × roundNormalProduct =>
      (DeltaSweep.circleParameter q.1 : ℂ)) :=
    (Units.continuous_val.comp DeltaSweep.circleParameter_continuous).comp continuous_fst
  exact (hp.fst.prodMk (ht.smul hp.snd)).subtype_mk _

theorem roundProductMap_circleAction (t : Circle) (p : roundNormalProduct) :
    DeltaSweep.actionMap (t, roundProductMap p) = roundProductMap (roundCircleAction t p) :=
  roundProductMap_normalAction _ _ p

theorem actionMap_mem_fixedCurveNeighborhood (t : Circle) {x : Threefold.Space}
    (hx : x ∈ fixedCurveNeighborhood) :
    DeltaSweep.actionMap (t, x) ∈ fixedCurveNeighborhood := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨roundCircleAction t p, (roundProductMap_circleAction t p).symm⟩

/-- The original global circle action, restricted to its proved invariant open neighborhood. -/
def neighborhoodCircleAction (t : Circle) (x : fixedCurveNeighborhood) : fixedCurveNeighborhood :=
  ⟨DeltaSweep.actionMap (t, x), actionMap_mem_fixedCurveNeighborhood t x.property⟩

@[simp] theorem neighborhoodCircleAction_coe (t : Circle) (x : fixedCurveNeighborhood) :
    (neighborhoodCircleAction t x : Threefold.Space) = DeltaSweep.actionMap (t, x) := rfl

/-- The actual native real-analytic diffeomorphism is exactly circle equivariant. -/
theorem normalNeighborhoodDiffeomorph_circleAction (t : Circle) (p : roundNormalProduct) :
    neighborhoodCircleAction t (normalNeighborhoodDiffeomorph p) =
      normalNeighborhoodDiffeomorph (roundCircleAction t p) := by
  apply Subtype.ext
  exact roundProductMap_circleAction t p

theorem normalNeighborhoodDiffeomorph_inverse_circleAction
    (t : Circle) (x : fixedCurveNeighborhood) :
    normalNeighborhoodDiffeomorph.symm (neighborhoodCircleAction t x) =
      roundCircleAction t (normalNeighborhoodDiffeomorph.symm x) := by
  apply normalNeighborhoodDiffeomorph.injective
  change normalNeighborhoodDiffeomorph
      (normalNeighborhoodDiffeomorph.symm (neighborhoodCircleAction t x)) =
    normalNeighborhoodDiffeomorph (roundCircleAction t (normalNeighborhoodDiffeomorph.symm x))
  rw [normalNeighborhoodDiffeomorph.apply_symm_apply,
    ← normalNeighborhoodDiffeomorph_circleAction,
    normalNeighborhoodDiffeomorph.apply_symm_apply]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
