import Wikipedia.HopfProblem.CuspComplementFiniteCoordinates
import Wikipedia.HopfProblem.CuspComplementCoordinatesCircle
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspNeighborhoodEquivariance

/-!
# The original circle preserves the actual carved cusp cap

The fixed normal neighborhood is preserved through its already checked native
normal coordinates. The finite cap coordinates carry the literal diagonal
action, with unchanged cubic time. These facts prove invariance of both the
actual compact complement and its carved native-coordinate source.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization ToricCharts ToricFan
open SpecialPeriods SpecialPeriods.Threefold VerticalAction Homology

local notation "Circle" => AddCircle (1 : ℝ)
local notation "E₃" => CoordinateSpace 3

theorem globalCircle_zero (x : Threefold.Space) : DeltaSweep.actionMap (0, x) = x := by
  let := DeltaSweep.circleAction
  change (0 : Circle) +ᵥ x = x
  exact zero_vadd Circle x

theorem globalCircle_add (s t : Circle) (x : Threefold.Space) :
    DeltaSweep.actionMap (s + t, x) =
      DeltaSweep.actionMap (s, DeltaSweep.actionMap (t, x)) := by
  let := DeltaSweep.circleAction
  change (s + t) +ᵥ x = s +ᵥ (t +ᵥ x)
  exact add_vadd s t x

theorem globalCircle_neg_apply (t : Circle) (x : Threefold.Space) :
    DeltaSweep.actionMap (-t, DeltaSweep.actionMap (t, x)) = x := by
  rw [← globalCircle_add, neg_add_cancel, globalCircle_zero]

/-- Actual norm-one scalar action preserves the literal ambient interior of the fixed disk. -/
theorem actionBiholomorph_mem_interior_closedDiskNeighborhood
    (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) {x : Threefold.Space}
    (hx : x ∈ interior closedDiskNeighborhood) :
    actionBiholomorph u x ∈ interior closedDiskNeighborhood := by
  obtain ⟨p, rfl⟩ := interior_subset hx
  change actionBiholomorph u (roundProductMap (closedProductIntoRound p)) ∈ _
  rw [roundProductMap_normalAction u hu]
  apply (roundProductMap_mem_interior_closedDiskNeighborhood_iff _).mpr
  change radiusSq ((u : ℂ) • p.2.val) < closedRadius ^ 2
  rw [radiusSq_unit_smul (u : ℂ) hu]
  exact (roundProductMap_mem_interior_closedDiskNeighborhood_iff
    (closedProductIntoRound p)).mp hx

theorem actionMap_mem_interior_closedDiskNeighborhood (t : Circle)
    {x : Threefold.Space} (hx : x ∈ interior closedDiskNeighborhood) :
    DeltaSweep.actionMap (t, x) ∈ interior closedDiskNeighborhood :=
  actionBiholomorph_mem_interior_closedDiskNeighborhood
    (DeltaSweep.circleParameter t) (FixedCoordinates.CircleOrbit.circleParameter_norm t) hx

theorem actionMap_mem_interior_closedDiskNeighborhood_iff (t : Circle)
    (x : Threefold.Space) :
    DeltaSweep.actionMap (t, x) ∈ interior closedDiskNeighborhood ↔
      x ∈ interior closedDiskNeighborhood := by
  constructor
  · intro hx
    have h := actionMap_mem_interior_closedDiskNeighborhood (-t) hx
    rwa [globalCircle_neg_apply] at h
  · exact actionMap_mem_interior_closedDiskNeighborhood t

theorem finiteDiagonal_one (z : E₃) : FixedCoordinates.diagonal 1 z = z := by
  ext j
  fin_cases j <;> simp [FixedCoordinates.diagonal_apply]

theorem finiteDiagonal_mul (u v : ℂˣ) (z : E₃) :
    FixedCoordinates.diagonal (u * v) z =
      FixedCoordinates.diagonal u (FixedCoordinates.diagonal v z) := by
  simp only [FixedCoordinates.diagonal_apply]
  ext j
  fin_cases j
  · change ((u * v : ℂˣ) : ℂ)⁻¹ * z 0 = (u : ℂ)⁻¹ * ((v : ℂ)⁻¹ * z 0)
    rw [Units.val_mul, mul_inv_rev]
    ring
  · rfl
  · change ((u * v : ℂˣ) : ℂ) * z 2 = (u : ℂ) * ((v : ℂ) * z 2)
    rw [Units.val_mul, mul_assoc]

/-- The original period-one circle acts by the frozen literal finite coordinate maps. -/
def finiteCoordinateCircleAction (t : Circle) (p : FiniteCoordinates) : FiniteCoordinates :=
  Coordinates.capAction capRadius (DeltaSweep.circleParameter t)
    (FixedCoordinates.CircleOrbit.circleParameter_norm t) p

@[simp] theorem finiteCoordinateCircleAction_index (t : Circle) (p : FiniteCoordinates) :
    (finiteCoordinateCircleAction t p).1 = p.1 := rfl

@[simp] theorem finiteCoordinateCircleAction_coordinates (t : Circle)
    (p : FiniteCoordinates) :
    ((finiteCoordinateCircleAction t p).2 : E₃) =
      FixedCoordinates.diagonal (DeltaSweep.circleParameter t) p.2 := rfl

@[simp] theorem finiteCoordinateCircleAction_zero (p : FiniteCoordinates) :
    finiteCoordinateCircleAction 0 p = p := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change FixedCoordinates.diagonal (DeltaSweep.circleParameter 0) p.2 = p.2
    rw [DeltaSweep.circleParameter_zero, finiteDiagonal_one]

theorem finiteCoordinateCircleAction_add (s t : Circle) (p : FiniteCoordinates) :
    finiteCoordinateCircleAction (s + t) p =
      finiteCoordinateCircleAction s (finiteCoordinateCircleAction t p) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change FixedCoordinates.diagonal (DeltaSweep.circleParameter (s + t)) p.2 =
      FixedCoordinates.diagonal (DeltaSweep.circleParameter s)
        (FixedCoordinates.diagonal (DeltaSweep.circleParameter t) p.2)
    rw [DeltaSweep.circleParameter_add, finiteDiagonal_mul]

theorem circleDiagonal_continuous :
    Continuous (fun q : Circle × E₃ =>
      FixedCoordinates.diagonal (DeltaSweep.circleParameter q.1) q.2) := by
  have hv : Continuous (fun q : Circle × E₃ => (DeltaSweep.circleParameter q.1 : ℂ)) :=
    (Units.continuous_val.comp DeltaSweep.circleParameter_continuous).comp continuous_fst
  have hi : Continuous (fun q : Circle × E₃ => (DeltaSweep.circleParameter q.1 : ℂ)⁻¹) := by
    simpa only [Function.comp_def, Units.val_inv_eq_inv_val] using
      (Units.continuous_coe_inv.comp DeltaSweep.circleParameter_continuous).comp continuous_fst
  have hz (j : Fin 3) : Continuous (fun q : Circle × E₃ => q.2 j) :=
    (continuous_apply j).comp continuous_snd
  apply continuous_pi
  intro j
  fin_cases j
  · simpa [FixedCoordinates.diagonal_apply, Function.comp_def] using
      continuous_mul.comp (hi.prodMk (hz 0))
  · simpa [FixedCoordinates.diagonal_apply] using hz 1
  · simpa [FixedCoordinates.diagonal_apply, Function.comp_def] using
      continuous_mul.comp (hv.prodMk (hz 2))

theorem finiteCoordinateCircleAction_continuous :
    Continuous (fun q : Circle × FiniteCoordinates =>
      finiteCoordinateCircleAction q.1 q.2) := by
  have hp : Continuous (fun q : Circle × FiniteCoordinates => (q.2.2 : E₃)) :=
    continuous_subtype_val.comp continuous_snd.snd
  have hc : Continuous (fun q : Circle × FiniteCoordinates =>
      Coordinates.coordinateAction capRadius (DeltaSweep.circleParameter q.1)
        (FixedCoordinates.CircleOrbit.circleParameter_norm q.1) q.2.2) :=
    (circleDiagonal_continuous.comp (continuous_fst.prodMk hp)).subtype_mk _
  exact continuous_snd.fst.prodMk hc

/-- These are the already proved original global maps, not a transported action. -/
theorem coordinateMap_finiteCoordinateCircleAction (t : Circle) (p : FiniteCoordinates) :
    coordinateMap (finiteCoordinateCircleAction t p) =
      DeltaSweep.actionMap (t, coordinateMap p) :=
  Coordinates.toGlobal_capAction capRadius capRadius_lt_cuspRadius
    (DeltaSweep.circleParameter t) (FixedCoordinates.CircleOrbit.circleParameter_norm t) p

theorem coordinateMap_time_finiteCoordinateCircleAction (t : Circle)
    (p : FiniteCoordinates) :
    CuspGeometry.cuspCoordinate (coordinateMap (finiteCoordinateCircleAction t p)) =
      CuspGeometry.cuspCoordinate (coordinateMap p) := by
  rw [coordinateMap_time, coordinateMap_time]
  exact Coordinates.coordinateAction_time capRadius (DeltaSweep.circleParameter t)
    (FixedCoordinates.CircleOrbit.circleParameter_norm t) p.2

/-- The actual cusp parameter is unchanged at every point of the original cap. -/
theorem actionMap_cuspCoordinate_of_mem_cap (t : Circle) {x : Threefold.Space}
    (hx : x ∈ cap) :
    CuspGeometry.cuspCoordinate (DeltaSweep.actionMap (t, x)) =
      CuspGeometry.cuspCoordinate x := by
  obtain ⟨p, rfl⟩ := coordinateMap_range.symm ▸ hx
  rw [← coordinateMap_finiteCoordinateCircleAction]
  exact coordinateMap_time_finiteCoordinateCircleAction t p

theorem actionMap_mem_cap (t : Circle) {x : Threefold.Space} (hx : x ∈ cap) :
    DeltaSweep.actionMap (t, x) ∈ cap := by
  obtain ⟨p, rfl⟩ := coordinateMap_range.symm ▸ hx
  rw [← coordinateMap_finiteCoordinateCircleAction]
  exact coordinateMap_mem_cap (finiteCoordinateCircleAction t p)

theorem actionMap_mem_cap_iff (t : Circle) (x : Threefold.Space) :
    DeltaSweep.actionMap (t, x) ∈ cap ↔ x ∈ cap := by
  constructor
  · intro hx
    have h := actionMap_mem_cap (-t) hx
    rwa [globalCircle_neg_apply] at h
  · exact actionMap_mem_cap t

/-- The literal actual compact complement is invariant under the original circle. -/
theorem actionMap_mem_capComplement_iff (t : Circle) (x : Threefold.Space) :
    DeltaSweep.actionMap (t, x) ∈ capComplement ↔ x ∈ capComplement := by
  change (DeltaSweep.actionMap (t, x) ∈ cap ∧
      DeltaSweep.actionMap (t, x) ∉ interior closedDiskNeighborhood) ↔
    (x ∈ cap ∧ x ∉ interior closedDiskNeighborhood)
  rw [actionMap_mem_cap_iff, actionMap_mem_interior_closedDiskNeighborhood_iff]

/-- The same literal diagonal maps preserve precisely the already defined carved source. -/
theorem finiteCoordinateCircleAction_mem_carved_iff (t : Circle) (p : FiniteCoordinates) :
    finiteCoordinateCircleAction t p ∈ carvedCoordinates ↔ p ∈ carvedCoordinates := by
  rw [mem_carvedCoordinates_iff, mem_carvedCoordinates_iff,
    coordinateMap_finiteCoordinateCircleAction,
    actionMap_mem_interior_closedDiskNeighborhood_iff]

end Wikipedia.HopfProblem.CuspComplement
