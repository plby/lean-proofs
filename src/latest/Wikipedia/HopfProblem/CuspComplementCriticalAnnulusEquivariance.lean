import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusCircleWeights
import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusModel

/-!
# The genuine circle action on the surviving critical annuli

The source action is literal multiplication in the original finite
complex parameter. The target action is independently the restriction
of the original global delta-circle action, not an action transported
through a homeomorphism. The original annulus parametrization intertwines
them, and both actual normal-boundary levels are preserved.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- Unit modulus preserves the literal two radius inequalities in the original parameter. -/
def annulusUnitAction (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : Annulus b) : Annulus b :=
  ⟨curveMultiplier b u * z.val, by
    change closedRadius ≤ ‖curveMultiplier b u * z.val‖ ∧
      ‖curveMultiplier b u * z.val‖ ≤ outerRadius b
    rw [curveMultiplier_norm_mul b u hu]
    exact z.property⟩

@[simp] theorem annulusUnitAction_coe (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : Annulus b) :
    (annulusUnitAction b u hu z : ℂ) = curveMultiplier b u * z.val := rfl

theorem annulusUnitAction_norm (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1)
    (z : Annulus b) : ‖(annulusUnitAction b u hu z : ℂ)‖ = ‖z.val‖ :=
  curveMultiplier_norm_mul b u hu z.val

/-- The original period-one parameter acts with the already proved opposite weights. -/
def annulusCircleAction (b : Bool) (t : Circle) : Annulus b → Annulus b :=
  annulusUnitAction b (DeltaSweep.circleParameter t)
    (FixedCoordinates.CircleOrbit.circleParameter_norm t)

@[simp] theorem annulusCircleAction_coe (b : Bool) (t : Circle) (z : Annulus b) :
    (annulusCircleAction b t z : ℂ) =
      curveMultiplier b (DeltaSweep.circleParameter t) * z.val := rfl

theorem annulusCircleAction_norm (b : Bool) (t : Circle) (z : Annulus b) :
    ‖(annulusCircleAction b t z : ℂ)‖ = ‖z.val‖ :=
  annulusUnitAction_norm b _ (FixedCoordinates.CircleOrbit.circleParameter_norm t) z

@[simp] theorem annulusCircleAction_zero (b : Bool) (z : Annulus b) :
    annulusCircleAction b 0 z = z := by
  apply Subtype.ext
  change curveMultiplier b (DeltaSweep.circleParameter 0) * z.val = z.val
  rw [DeltaSweep.circleParameter_zero, curveMultiplier_one, one_mul]

theorem annulusCircleAction_add (b : Bool) (s t : Circle) (z : Annulus b) :
    annulusCircleAction b (s + t) z = annulusCircleAction b s (annulusCircleAction b t z) := by
  apply Subtype.ext
  change curveMultiplier b (DeltaSweep.circleParameter (s + t)) * z.val =
    curveMultiplier b (DeltaSweep.circleParameter s) *
      (curveMultiplier b (DeltaSweep.circleParameter t) * z.val)
  rw [DeltaSweep.circleParameter_add, curveMultiplier_mul, mul_assoc]

theorem annulusCircleAction_continuous (b : Bool) :
    Continuous (fun p : Circle × Annulus b => annulusCircleAction b p.1 p.2) := by
  have h : Continuous (fun p : Circle × Annulus b =>
      curveMultiplier b (DeltaSweep.circleParameter p.1) * p.2.val) :=
    ((curveMultiplier_circle_continuous b).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  exact h.subtype_mk _

@[instance_reducible] def annulusCircleAddAction (b : Bool) : AddAction Circle (Annulus b) where
  vadd := annulusCircleAction b
  zero_vadd := annulusCircleAction_zero b
  add_vadd := annulusCircleAction_add b

theorem annulusCircleAddAction_continuous (b : Bool) :
    letI := annulusCircleAddAction b
    ContinuousVAdd Circle (Annulus b) := by
  let := annulusCircleAddAction b
  exact ⟨annulusCircleAction_continuous b⟩

/-- Exact equivariance of the original map under every unit-modulus multiplicative parameter. -/
theorem annulusMap_unitAction (b : Bool) (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : Annulus b) :
    actionBiholomorph u (annulusMap b z) = annulusMap b (annulusUnitAction b u hu z) :=
  actionBiholomorph_doubleCurve_finite b u z.val

theorem annulusMap_circleAction (b : Bool) (t : Circle) (z : Annulus b) :
    DeltaSweep.actionMap (t, annulusMap b z) = annulusMap b (annulusCircleAction b t z) :=
  deltaAction_doubleCurve_finite b t z.val

/-- The actual delta action preserves the actual surviving curve, by its native point formula. -/
theorem deltaAction_mem_remainingCurve (b : Bool) (t : Circle) {x : Threefold.Space}
    (hx : x ∈ remainingCurve b) : DeltaSweep.actionMap (t, x) ∈ remainingCurve b := by
  obtain ⟨z, rfl⟩ := (annulusMap_range b).symm ▸ hx
  rw [annulusMap_circleAction]
  exact annulusMap_mem_remainingCurve b (annulusCircleAction b t z)

/-- Restriction of the original ambient action, with its unchanged underlying map. -/
def remainingCurveCircleAction (b : Bool) (t : Circle) (x : remainingCurve b) :
    remainingCurve b :=
  ⟨DeltaSweep.actionMap (t, (x : Threefold.Space)), deltaAction_mem_remainingCurve b t x.property⟩

@[simp] theorem remainingCurveCircleAction_coe (b : Bool) (t : Circle)
    (x : remainingCurve b) :
    (remainingCurveCircleAction b t x : Threefold.Space) =
      DeltaSweep.actionMap (t, (x : Threefold.Space)) := rfl

@[simp] theorem remainingCurveCircleAction_zero (b : Bool) (x : remainingCurve b) :
    remainingCurveCircleAction b 0 x = x := by
  apply Subtype.ext
  let := DeltaSweep.circleAction
  change (0 : Circle) +ᵥ (x : Threefold.Space) = (x : Threefold.Space)
  exact zero_vadd Circle _

theorem remainingCurveCircleAction_add (b : Bool) (s t : Circle) (x : remainingCurve b) :
    remainingCurveCircleAction b (s + t) x =
      remainingCurveCircleAction b s (remainingCurveCircleAction b t x) := by
  apply Subtype.ext
  let := DeltaSweep.circleAction
  change (s + t) +ᵥ (x : Threefold.Space) = s +ᵥ (t +ᵥ (x : Threefold.Space))
  exact add_vadd s t _

/-- Joint continuity comes directly from the original ambient action and subtype topology. -/
theorem remainingCurveCircleAction_continuous (b : Bool) :
    Continuous (fun p : Circle × remainingCurve b => remainingCurveCircleAction b p.1 p.2) := by
  have h : Continuous (fun p : Circle × remainingCurve b =>
      DeltaSweep.actionMap (p.1, (p.2 : Threefold.Space))) :=
    DeltaSweep.actionMap.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact h.subtype_mk _

@[instance_reducible] def remainingCurveCircleAddAction (b : Bool) :
    AddAction Circle (remainingCurve b) where
  vadd := remainingCurveCircleAction b
  zero_vadd := remainingCurveCircleAction_zero b
  add_vadd := remainingCurveCircleAction_add b

theorem remainingCurveCircleAddAction_continuous (b : Bool) :
    letI := remainingCurveCircleAddAction b
    ContinuousVAdd Circle (remainingCurve b) := by
  let := remainingCurveCircleAddAction b
  exact ⟨remainingCurveCircleAction_continuous b⟩

/-- The fixed original annulus homeomorphism intertwines the two independently defined actions. -/
theorem annulusHomeomorph_circleAction (b : Bool) (t : Circle) (z : Annulus b) :
    annulusHomeomorph b (annulusCircleAction b t z) =
      remainingCurveCircleAction b t (annulusHomeomorph b z) := by
  apply Subtype.ext
  exact (annulusMap_circleAction b t z).symm

theorem annulusHomeomorph_symm_circleAction (b : Bool) (t : Circle) (x : remainingCurve b) :
    (annulusHomeomorph b).symm (remainingCurveCircleAction b t x) =
      annulusCircleAction b t ((annulusHomeomorph b).symm x) := by
  apply (annulusHomeomorph b).injective
  rw [Homeomorph.apply_symm_apply, annulusHomeomorph_circleAction,
    Homeomorph.apply_symm_apply]

/-- The preserved levels are the actual ambient normal frontier, not replacement boundary marks. -/
theorem remainingCurveCircleAction_frontier_iff (b : Bool) (t : Circle)
    (x : remainingCurve b) :
    (remainingCurveCircleAction b t x : Threefold.Space) ∈ frontier closedDiskNeighborhood ↔
      (x : Threefold.Space) ∈ frontier closedDiskNeighborhood := by
  obtain ⟨z, rfl⟩ := (annulusHomeomorph b).surjective x
  change DeltaSweep.actionMap (t, annulusMap b z) ∈ frontier closedDiskNeighborhood ↔
    annulusMap b z ∈ frontier closedDiskNeighborhood
  rw [annulusMap_circleAction, annulusMap_mem_frontier_iff,
    annulusMap_mem_frontier_iff, annulusCircleAction_norm]

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
