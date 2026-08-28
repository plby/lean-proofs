import Wikipedia.HopfProblem.CuspCircleOrbitLocalAlgebra
import Wikipedia.HopfProblem.CuspCircleOrbitLocalParameter
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCoordinates
import Wikipedia.HopfProblem.ToricAxisCharts

/-!
# Genuine local orbit coordinates for the original cusp circle action

The Hopf invariant is applied to the actual normal coordinates in the
unchanged cusp coordinate domain. Its fibres are exactly the orbits of
the original period-one circle parameter, and the original coordinate
cover intertwines those orbits with the actual global action.

The literal transition across the fixed curve is also retained, both
before and after taking these invariant coordinates. No global orbit
space, tubular neighborhood, or sphere identification is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

open ToricCharts ToricFan
open _root_.Wikipedia.HopfProblem.ToricFan.Triangle
open Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

local notation "E₃" => CoordinateSpace 3
local notation "Circle" => AddCircle (1 : ℝ)

/-- The original middle coordinate and the opposite-weight normal invariant. -/
def localOrbitMap (z : Domain) : ℂ × ℂ × ℝ :=
  ((z : E₃) 1, hopfMap ((z : E₃) 0, (z : E₃) 2))

@[simp] theorem localOrbitMap_apply (z : Domain) :
    localOrbitMap z = ((z : E₃) 1, 2 * (z : E₃) 0 * (z : E₃) 2,
      Complex.normSq ((z : E₃) 0) - Complex.normSq ((z : E₃) 2)) := rfl

theorem localOrbitMap_continuous : Continuous localOrbitMap := by
  unfold localOrbitMap
  exact ((continuous_apply 1).comp continuous_subtype_val).prodMk
    (hopfMap_continuous.comp
      (((continuous_apply 0).comp continuous_subtype_val).prodMk
        ((continuous_apply 2).comp continuous_subtype_val)))

/-- Invariance uses the actual coordinate action, not just its tangent weights. -/
theorem localOrbitMap_coordinateAction (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : Domain) :
    localOrbitMap (coordinateAction u z) = localOrbitMap z := by
  apply Prod.ext
  · simp [localOrbitMap, coordinateAction_coe, diagonal_apply]
  · change hopfMap ((coordinateAction u z : E₃) 0, (coordinateAction u z : E₃) 2) = _
    rw [coordinateAction_coe, diagonal_apply]
    exact hopfMap_unitNormalAction u hu ((z : E₃) 0, (z : E₃) 2)

/-- Exact local orbit fibres on the original domain, including every zero-coordinate case. -/
theorem localOrbitMap_eq_iff (z w : Domain) :
    localOrbitMap z = localOrbitMap w ↔
      ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ coordinateAction u z = w := by
  constructor
  · intro h
    have hbase : (z : E₃) 1 = (w : E₃) 1 := congrArg Prod.fst h
    have hnormal : hopfMap ((z : E₃) 0, (z : E₃) 2) =
        hopfMap ((w : E₃) 0, (w : E₃) 2) := congrArg Prod.snd h
    obtain ⟨u, hu, hact⟩ := exists_unitNormalAction_of_hopfMap_eq hnormal
    refine ⟨u, hu, Subtype.ext ?_⟩
    rw [coordinateAction_coe, diagonal_apply]
    ext i
    fin_cases i
    · exact congrArg Prod.fst hact
    · exact hbase
    · exact congrArg Prod.snd hact
  · rintro ⟨u, hu, rfl⟩
    exact (localOrbitMap_coordinateAction u hu z).symm

/-- The orbit parameter is precisely the original additive circle `ℝ/ℤ`. -/
theorem localOrbitMap_eq_iff_circle (z w : Domain) :
    localOrbitMap z = localOrbitMap w ↔
      ∃ t : Circle, coordinateAction (DeltaSweep.circleParameter t) z = w := by
  rw [localOrbitMap_eq_iff]
  constructor
  · rintro ⟨u, hu, hact⟩
    obtain ⟨t, rfl⟩ := exists_circleParameter_of_norm_eq_one u hu
    exact ⟨t, hact⟩
  · rintro ⟨t, hact⟩
    exact ⟨DeltaSweep.circleParameter t, circleParameter_norm t, hact⟩

/-- The original cusp coordinate cover intertwines the two actual circle actions. -/
theorem globalMap_circle_coordinateAction (t : Circle) (a : Triangle) (z : Domain) :
    DeltaSweep.actionMap (t, globalMap a z) =
      globalMap a (coordinateAction (DeltaSweep.circleParameter t) z) := by
  change actionBiholomorph (DeltaSweep.circleParameter t) (globalMap a z) = _
  exact globalMap_coordinateAction (DeltaSweep.circleParameter t) a z

/-- Equal local invariant coordinates give an orbit of the unchanged global action. -/
theorem same_global_circle_orbit_of_localOrbitMap_eq (a : Triangle) {z w : Domain}
    (h : localOrbitMap z = localOrbitMap w) :
    ∃ t : Circle, DeltaSweep.actionMap (t, globalMap a z) = globalMap a w := by
  obtain ⟨t, hact⟩ := (localOrbitMap_eq_iff_circle z w).mp h
  exact ⟨t, by rw [globalMap_circle_coordinateAction, hact]⟩

/-- The native exponent matrix between the two charts of the fixed curve. -/
theorem normalTransition_matrix :
    transition ToricSpace.referenceTriangle (upperNeighbour 1) =
      !![1, 1, 0; 0, -1, 0; 0, 1, 1] := by
  decide

/-- The literal original monomial coordinate change. -/
theorem normalTransition_apply (z : E₃) :
    chartChange ToricSpace.referenceTriangle (upperNeighbour 1) z =
      ![z 0 * z 1, (z 1)⁻¹, z 1 * z 2] := by
  change monomial (transition ToricSpace.referenceTriangle (upperNeighbour 1)) z = _
  rw [normalTransition_matrix]
  ext j
  fin_cases j <;> simp [monomial, Fin.prod_univ_succ]

/-- The exact overlap, without an extra nonzero-normal-coordinate restriction. -/
theorem normalTransition_source (z : E₃) :
    z ∈ (chartChange ToricSpace.referenceTriangle (upperNeighbour 1)).source ↔ z 1 ≠ 0 := by
  rw [chartChange_source, normalTransition_matrix]
  simp [domain, Fin.forall_fin_succ]

/-- The transition remains the original equality after the cusp covering and gluing. -/
theorem globalMap_normalTransition {z w : Domain} (hz : (z : E₃) 1 ≠ 0)
    (hw : (w : E₃) = ![(z : E₃) 0 * (z : E₃) 1, ((z : E₃) 1)⁻¹,
      (z : E₃) 1 * (z : E₃) 2]) :
    globalMap ToricSpace.referenceTriangle z = globalMap (upperNeighbour 1) w := by
  have hi : ToricSpace.inclusion ToricSpace.referenceTriangle (z : E₃) =
      ToricSpace.inclusion (upperNeighbour 1) (w : E₃) := by
    apply (ToricSpace.inclusion_eq_iff _ _ _ _).mpr
    exact ⟨(normalTransition_source z).mpr hz, (normalTransition_apply z).trans hw.symm⟩
  have ht : tubeMap ToricSpace.referenceTriangle z = tubeMap (upperNeighbour 1) w :=
    Subtype.ext hi
  simp only [globalMap, Function.comp_apply, quotientMap, ht]

/-- The actual overlap induces the indicated transformation of orbit coordinates. -/
theorem localOrbitMap_normalTransition {z w : Domain}
    (hw : (w : E₃) = ![(z : E₃) 0 * (z : E₃) 1, ((z : E₃) 1)⁻¹,
      (z : E₃) 1 * (z : E₃) 2]) :
    localOrbitMap w = (((z : E₃) 1)⁻¹,
      ((z : E₃) 1) ^ 2 * (localOrbitMap z).2.1,
      Complex.normSq ((z : E₃) 1) * (localOrbitMap z).2.2) := by
  simp only [localOrbitMap, hopfMap]
  rw [hw]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change 2 * ((z : E₃) 0 * (z : E₃) 1) * ((z : E₃) 1 * (z : E₃) 2) =
        ((z : E₃) 1) ^ 2 * (2 * (z : E₃) 0 * (z : E₃) 2)
      ring
    · change Complex.normSq ((z : E₃) 0 * (z : E₃) 1) -
          Complex.normSq ((z : E₃) 1 * (z : E₃) 2) =
        Complex.normSq ((z : E₃) 1) *
          (Complex.normSq ((z : E₃) 0) - Complex.normSq ((z : E₃) 2))
      simp only [Complex.normSq_mul]
      ring

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
