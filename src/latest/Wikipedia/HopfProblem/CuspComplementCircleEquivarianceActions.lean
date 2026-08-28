import Wikipedia.HopfProblem.CuspComplementCircleEquivarianceSource

/-!
# The literal circle actions on the carved source and actual complement

The source action is the restriction of the original finite diagonal maps.
The target action is independently the restriction of the already constructed
global delta-circle action. Their exact equivariance follows from the original
coordinate maps, and both actions are jointly continuous.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspComplement

open SpecialPeriods SpecialPeriods.Threefold Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- The original coordinate circle action restricted to the precise carved subset. -/
def carvedCircleAction (t : Circle) (p : carvedCoordinates) : carvedCoordinates :=
  ⟨finiteCoordinateCircleAction t p.val,
    (finiteCoordinateCircleAction_mem_carved_iff t p.val).mpr p.property⟩

@[simp] theorem carvedCircleAction_coe (t : Circle) (p : carvedCoordinates) :
    (carvedCircleAction t p : FiniteCoordinates) = finiteCoordinateCircleAction t p.val := rfl

@[simp] theorem carvedCircleAction_zero (p : carvedCoordinates) :
    carvedCircleAction 0 p = p := by
  apply Subtype.ext
  exact finiteCoordinateCircleAction_zero p.val

theorem carvedCircleAction_add (s t : Circle) (p : carvedCoordinates) :
    carvedCircleAction (s + t) p = carvedCircleAction s (carvedCircleAction t p) := by
  apply Subtype.ext
  exact finiteCoordinateCircleAction_add s t p.val

@[instance_reducible] def carvedCircleAddAction : AddAction Circle carvedCoordinates where
  vadd := carvedCircleAction
  zero_vadd := carvedCircleAction_zero
  add_vadd := carvedCircleAction_add

theorem carvedCircleAction_continuous :
    Continuous (fun q : Circle × carvedCoordinates => carvedCircleAction q.1 q.2) :=
  (finiteCoordinateCircleAction_continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem carvedCircleAddAction_continuous :
    letI := carvedCircleAddAction
    ContinuousVAdd Circle carvedCoordinates := by
  let := carvedCircleAddAction
  exact ⟨carvedCircleAction_continuous⟩

/-- The original global circle action restricted directly to the actual cap complement. -/
def capComplementCircleAction (t : Circle) (x : capComplement) : capComplement :=
  ⟨DeltaSweep.actionMap (t, x), (actionMap_mem_capComplement_iff t x).mpr x.property⟩

@[simp] theorem capComplementCircleAction_coe (t : Circle) (x : capComplement) :
    (capComplementCircleAction t x : Threefold.Space) = DeltaSweep.actionMap (t, x) := rfl

@[simp] theorem capComplementCircleAction_zero (x : capComplement) :
    capComplementCircleAction 0 x = x := by
  apply Subtype.ext
  exact globalCircle_zero x.val

theorem capComplementCircleAction_add (s t : Circle) (x : capComplement) :
    capComplementCircleAction (s + t) x =
      capComplementCircleAction s (capComplementCircleAction t x) := by
  apply Subtype.ext
  exact globalCircle_add s t x.val

@[instance_reducible] def capComplementCircleAddAction : AddAction Circle capComplement where
  vadd := capComplementCircleAction
  zero_vadd := capComplementCircleAction_zero
  add_vadd := capComplementCircleAction_add

theorem capComplementCircleAction_continuous :
    Continuous (fun q : Circle × capComplement => capComplementCircleAction q.1 q.2) :=
  (DeltaSweep.actionMap.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem capComplementCircleAddAction_continuous :
    letI := capComplementCircleAddAction
    ContinuousVAdd Circle capComplement := by
  let := capComplementCircleAddAction
  exact ⟨capComplementCircleAction_continuous⟩

/-- The original representative map intertwines the independently defined actual actions. -/
theorem presentationMap_carvedCircleAction (t : Circle) (p : carvedCoordinates) :
    presentationMap (carvedCircleAction t p) =
      capComplementCircleAction t (presentationMap p) := by
  apply Subtype.ext
  exact coordinateMap_finiteCoordinateCircleAction t p.val

/-- Equivariance also holds for the two explicit additive-action instances. -/
theorem presentationMap_vadd (t : Circle) (p : carvedCoordinates) :
    letI := carvedCircleAddAction
    letI := capComplementCircleAddAction
    presentationMap (t +ᵥ p) = t +ᵥ presentationMap p := by
  let := carvedCircleAddAction
  let := capComplementCircleAddAction
  exact presentationMap_carvedCircleAction t p

end Wikipedia.HopfProblem.CuspComplement
