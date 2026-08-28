import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspEquivariance

/-!
# The original additive circle on the actual normal product

The parameter is the unchanged `DeltaSweep.circleParameter`, with its
original period-one normalization. It gives a genuine continuous additive
circle action, and the actual global product map intertwines this action
with the original action and real-time flow on the threefold.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction
open SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- The normal rotation uses precisely the original additive circle parameter. -/
def normalCircleAction (t : Circle) (p : smallNormalProduct) : smallNormalProduct :=
  normalProductAction (DeltaSweep.circleParameter t)
    (FixedCoordinates.CircleOrbit.circleParameter_norm t) p

@[simp] theorem normalCircleAction_coe (t : Circle) (p : smallNormalProduct) :
    (normalCircleAction t p : RiemannSphere × Fibre) =
      ((p : RiemannSphere × Fibre).1,
        (DeltaSweep.circleParameter t : ℂ) • (p : RiemannSphere × Fibre).2) := rfl

@[simp] theorem normalCircleAction_zero (p : smallNormalProduct) :
    normalCircleAction 0 p = p := by
  apply Subtype.ext
  change ((p : RiemannSphere × Fibre).1,
    (DeltaSweep.circleParameter 0 : ℂ) • (p : RiemannSphere × Fibre).2) =
      (p : RiemannSphere × Fibre)
  rw [DeltaSweep.circleParameter_zero, Units.val_one, one_smul]

theorem normalCircleAction_add (s t : Circle) (p : smallNormalProduct) :
    normalCircleAction (s + t) p = normalCircleAction s (normalCircleAction t p) := by
  apply Subtype.ext
  change ((p : RiemannSphere × Fibre).1,
    (DeltaSweep.circleParameter (s + t) : ℂ) • (p : RiemannSphere × Fibre).2) =
      ((p : RiemannSphere × Fibre).1,
        (DeltaSweep.circleParameter s : ℂ) •
          ((DeltaSweep.circleParameter t : ℂ) • (p : RiemannSphere × Fibre).2))
  rw [DeltaSweep.circleParameter_add, Units.val_mul, mul_smul]

/-- The actual additive-circle action, with its group laws proved on the original subtype. -/
@[instance_reducible]
def normalCircleAddAction : AddAction Circle smallNormalProduct where
  vadd := normalCircleAction
  zero_vadd := normalCircleAction_zero
  add_vadd := normalCircleAction_add

@[simp] theorem normalCircleAddAction_vadd (t : Circle) (p : smallNormalProduct) :
    letI := normalCircleAddAction
    t +ᵥ p = normalCircleAction t p := rfl

/-- The action is jointly continuous in the original circle and normal-product topologies. -/
theorem normalCircleAction_continuous :
    Continuous (fun q : Circle × smallNormalProduct => normalCircleAction q.1 q.2) := by
  have hp : Continuous (fun q : Circle × smallNormalProduct =>
      (q.2 : RiemannSphere × Fibre)) := continuous_subtype_val.comp continuous_snd
  have ht : Continuous (fun q : Circle × smallNormalProduct =>
      (DeltaSweep.circleParameter q.1 : ℂ)) :=
    (Units.continuous_val.comp DeltaSweep.circleParameter_continuous).comp continuous_fst
  exact (hp.fst.prodMk (ht.smul hp.snd)).subtype_mk _

/-- The genuine continuous action map on the unchanged small normal product. -/
def normalCircleActionMap : C(Circle × smallNormalProduct, smallNormalProduct) :=
  ⟨fun q => normalCircleAction q.1 q.2, normalCircleAction_continuous⟩

@[simp] theorem normalCircleActionMap_apply (t : Circle) (p : smallNormalProduct) :
    normalCircleActionMap (t, p) = normalCircleAction t p := rfl

theorem normalCircleAddAction_continuous :
    letI := normalCircleAddAction
    ContinuousVAdd Circle smallNormalProduct := by
  let := normalCircleAddAction
  exact ⟨normalCircleActionMap.continuous⟩

@[simp] theorem normalCircleAction_zeroSection (t : Circle) (p : RiemannSphere) :
    normalCircleAction t (zeroSection p) = zeroSection p :=
  normalProductAction_zeroSection _ _ p

@[simp] theorem normalCircleAction_radiusSq (t : Circle) (p : smallNormalProduct) :
    radiusSq (normalCircleAction t p : RiemannSphere × Fibre).2 =
      radiusSq (p : RiemannSphere × Fibre).2 :=
  normalProductAction_radiusSq _ _ p

@[simp] theorem normalCircleAction_norm (t : Circle) (p : smallNormalProduct) :
    ‖(normalCircleAction t p : RiemannSphere × Fibre).2‖ =
      ‖(p : RiemannSphere × Fibre).2‖ :=
  normalProductAction_norm _ _ p

/-- Literal intertwining with the actual global additive-circle action on the threefold. -/
theorem globalProductMap_circleAction (t : Circle) (p : smallNormalProduct) :
    DeltaSweep.actionMap (t, globalProductMap p) =
      globalProductMap (normalCircleAction t p) :=
  globalProductMap_normalProductAction _ _ p

/-- The same intertwining statement for the two actual native additive-action instances. -/
theorem globalProductMap_vadd (t : Circle) (p : smallNormalProduct) :
    letI := normalCircleAddAction
    letI := DeltaSweep.circleAction
    t +ᵥ globalProductMap p = globalProductMap (t +ᵥ p) := by
  let := normalCircleAddAction
  let := DeltaSweep.circleAction
  exact globalProductMap_circleAction t p

/-- The same formula for the original real-time flow, with its unchanged normalization. -/
theorem globalProductMap_realFlow (t : ℝ) (p : smallNormalProduct) :
    flow (t : ℂ) (globalProductMap p) =
      globalProductMap (normalCircleAction (t : Circle) p) := by
  rw [← DeltaSweep.actionMap_real]
  exact globalProductMap_circleAction (t : Circle) p

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
