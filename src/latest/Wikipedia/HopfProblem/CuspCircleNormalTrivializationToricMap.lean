import Wikipedia.HopfProblem.CuspCircleNormalTrivializationToricBase
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCoordinates

/-!
# The actual map from the trivial real normal product to the toric space

The map uses the lower toric chart at finite base points and the upper
chart at infinity. The original toric overlap proves that the same map
has its expected formula on the entire upper affine chart, and that no
additional identifications occur.
-/

noncomputable section

open Set Topology OnePoint

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts ToricFan

/-- The actual inverse normal-coordinate parametrization of either toric chart. -/
def toricChartMap (b : Bool) : Model → ToricSpace.Space :=
  ToricSpace.inclusion (chartTriangle b) ∘ (chartCoordinates b).symm

@[simp] theorem toricChartMap_apply (b : Bool) (q : Model) :
    toricChartMap b q =
      ToricSpace.inclusion (chartTriangle b) ((chartCoordinates b).symm q) := rfl

theorem toricChartMap_injective (b : Bool) : Function.Injective (toricChartMap b) :=
  (ToricSpace.inclusion_openEmbedding (chartTriangle b)).injective.comp
    (chartCoordinates b).symm.injective

/-- The literal two chart maps have exactly the usual inversion identification. -/
theorem toricChartMap_cross_eq_iff (a b : ℂ) (v w : Fibre) :
    toricChartMap false (a, v) = toricChartMap true (b, w) ↔
      a ≠ 0 ∧ b = a⁻¹ ∧ v = w := by
  constructor
  · intro h
    have ht := (ToricSpace.inclusion_eq_iff (chartTriangle false) (chartTriangle true)
      ((chartCoordinates false).symm (a, v))
      ((chartCoordinates true).symm (b, w))).mp h
    have ha : a ≠ 0 :=
      (SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit.normalTransition_source
        ((chartCoordinates false).symm (a, v))).mp ht.1
    have hz : (chartCoordinates false).symm (a, v) 1 ≠ 0 := ha
    have he := congrArg (chartCoordinates true) ht.2
    change chartCoordinates true
        (Triangle.chartChange ToricSpace.referenceTriangle (Triangle.upperNeighbour 1)
          ((chartCoordinates false).symm (a, v))) =
      chartCoordinates true ((chartCoordinates true).symm (b, w)) at he
    rw [chartCoordinates_transition _ hz, (chartCoordinates true).apply_symm_apply] at he
    change (a⁻¹, (chartCoordinates false ((chartCoordinates false).symm (a, v))).2) =
      (b, w) at he
    rw [(chartCoordinates false).apply_symm_apply] at he
    exact ⟨ha, (congrArg Prod.fst he).symm, congrArg Prod.snd he⟩
  · rintro ⟨ha, rfl, rfl⟩
    exact chartParameters_overlap a ha _

/-- The product map, defined by the original lower chart and the upper endpoint. -/
def fromProduct (p : RiemannSphere × Fibre) : ToricSpace.Space :=
  p.1.elim (toricChartMap true (0, p.2)) (fun a => toricChartMap false (a, p.2))

@[simp] theorem fromProduct_coe (a : ℂ) (v : Fibre) :
    fromProduct ((a : RiemannSphere), v) = toricChartMap false (a, v) := rfl

@[simp] theorem fromProduct_infty (v : Fibre) :
    fromProduct ((∞ : RiemannSphere), v) = toricChartMap true (0, v) := rfl

/-- The map has the upper chart formula on that entire affine chart, not only at infinity. -/
theorem fromProduct_infinityParametrization (a : ℂ) (v : Fibre) :
    fromProduct (RiemannSphere.infinityParametrization a, v) = toricChartMap true (a, v) := by
  by_cases ha : a = 0
  · subst a
    rw [RiemannSphere.infinityParametrization_zero, fromProduct_infty]
  · rw [RiemannSphere.infinityParametrization_of_ne ha, fromProduct_coe]
    simpa only [toricChartMap_apply, inv_inv] using
      chartParameters_overlap a⁻¹ (inv_ne_zero ha) v

@[simp] theorem fromProduct_baseProductChart (b : Bool) (q : Model) :
    fromProduct (baseProductChart b q) = toricChartMap b q := by
  rcases q with ⟨a, v⟩
  cases b
  · rfl
  · exact fromProduct_infinityParametrization a v

theorem fromProduct_comp_baseProductChart (b : Bool) :
    fromProduct ∘ baseProductChart b = toricChartMap b :=
  funext (fromProduct_baseProductChart b)

/-- On every original toric affine chart the constructed map is literally its inclusion. -/
@[simp] theorem fromProduct_chartCoordinates (b : Bool) (z : CoordinateSpace 3) :
    fromProduct (baseProductChart b (chartCoordinates b z)) =
      ToricSpace.inclusion (chartTriangle b) z := by
  rw [fromProduct_baseProductChart, toricChartMap_apply,
    (chartCoordinates b).symm_apply_apply]

/-- Equality of actual toric chart images is equality in the base/normal product. -/
theorem baseProductChart_eq_of_toricChartMap_eq (b c : Bool) (q r : Model)
    (h : toricChartMap b q = toricChartMap c r) :
    baseProductChart b q = baseProductChart c r := by
  rcases q with ⟨a, v⟩
  rcases r with ⟨d, w⟩
  cases b <;> cases c
  · exact congrArg (baseProductChart false) (toricChartMap_injective false h)
  · obtain ⟨ha, hd, hv⟩ := (toricChartMap_cross_eq_iff a d v w).mp h
    subst d
    subst w
    exact Prod.ext (RiemannSphere.standardCharts.affineMap_inversion false a ha) rfl
  · obtain ⟨hd, ha, hw⟩ := (toricChartMap_cross_eq_iff d a w v).mp h.symm
    subst a
    subst v
    exact Prod.ext (RiemannSphere.standardCharts.affineMap_inversion false d hd).symm rfl
  · exact congrArg (baseProductChart true) (toricChartMap_injective true h)

/-- The global product map is injective in the actual toric gluing. -/
theorem fromProduct_injective : Function.Injective fromProduct := by
  intro p r h
  obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
  obtain ⟨c, s, rfl⟩ := baseProductChart_cover r
  rw [fromProduct_baseProductChart, fromProduct_baseProductChart] at h
  exact baseProductChart_eq_of_toricChartMap_eq b c q s h

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
