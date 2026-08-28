import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusAxes
import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusSeparation
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundaryFrontier

/-!
# Exact intersections with the unchanged normal neighborhood

The original double-curve classification forces every normal
representative onto a pole axis. The original curve and axis
parametrizations are injective, so these representatives are precisely
the displayed lower and upper vectors. This gives exhaustive closed,
open, and frontier membership, with the literal original affine
parameter and its correction-dependent upper transition.
-/

noncomputable section

open Set Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open ToricFan.Triangle CuspCircleNormalTrivialization
open SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data

attribute [local instance] Threefold.space_t2Space

/-- The original closed normal point belongs to the actual ambient
interior exactly at strict normal radius. -/
theorem closedProductMap_mem_interior_iff (p : ClosedNormalProduct) :
    closedProductMap p ∈ interior closedDiskNeighborhood ↔
      radiusSq p.2.val < closedRadius ^ 2 :=
  roundProductMap_mem_interior_closedDiskNeighborhood_iff (closedProductIntoRound p)

/-- Every closed normal representative of a finite original curve point
is exactly one of its two explicit pole representatives. -/
theorem closedProductMap_eq_finite_iff (b : Bool) (z : ℂ) (p : ClosedNormalProduct) :
    closedProductMap p =
        CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) ↔
      (p.1 = ((0 : ℂ) : RiemannSphere) ∧ p.2.val = lowerNormal b z) ∨
        (z ≠ 0 ∧ p.1 = (∞ : RiemannSphere) ∧
          p.2.val = upperNormal b (kappa b * z⁻¹)) := by
  constructor
  · intro he
    have hc : closedProductMap p ∈ CuspGeometry.doubleCurve (curveIndex b) := by
      rw [he]
      exact CuspGeometry.doubleCurveParametrization_mem _ _
    obtain ⟨ha, w, hw⟩ | ⟨ha, w, hw⟩ :=
      (closedProductMap_mem_doubleCurve_iff b p).mp hc
    · have hn : radiusSq (lowerNormal b w) ≤ closedRadius ^ 2 := by
        rw [← hw]
        exact p.2.property
      have hp : p = (((0 : ℂ) : RiemannSphere), ⟨lowerNormal b w, hn⟩) :=
        Prod.ext ha (Subtype.ext hw)
      have he' :
          CuspGeometry.doubleCurveParametrization (curveIndex b) (w : RiemannSphere) =
            CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) := by
        rw [← closedProductMap_lowerNormal b w hn, ← hp]
        exact he
      have hwz : w = z := OnePoint.coe_injective
        ((CuspGeometry.doubleCurveParametrization_isEmbedding (curveIndex b)).injective he')
      exact Or.inl ⟨ha, hw.trans (congrArg (lowerNormal b) hwz)⟩
    · have hn : radiusSq (upperNormal b w) ≤ closedRadius ^ 2 := by
        rw [← hw]
        exact p.2.property
      have hp : p = ((∞ : RiemannSphere), ⟨upperNormal b w, hn⟩) :=
        Prod.ext ha (Subtype.ext hw)
      have hz : z ≠ 0 := by
        intro hz
        subst z
        have hzero : radiusSq (lowerNormal b 0) ≤ closedRadius ^ 2 := by
          rw [lowerNormal_zero, radiusSq_zero]
          exact sq_nonneg _
        have he0 : closedProductMap p =
            closedProductMap (((0 : ℂ) : RiemannSphere), ⟨lowerNormal b 0, hzero⟩) :=
          he.trans (closedProductMap_lowerNormal b 0 hzero).symm
        have hb : p.1 = ((0 : ℂ) : RiemannSphere) :=
          congrArg Prod.fst (closedProductMap_injective he0)
        exact OnePoint.infty_ne_coe (0 : ℂ) (ha.symm.trans hb)
      have he' :
          CuspGeometry.inclusion
              (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
                (upperNeighbour 1) (curveIndex b) w) =
            CuspGeometry.inclusion
              (CuspQuotient.axisMap (CD).correction (CD).radius (CD).radius_pos
                (upperNeighbour 1) (curveIndex b) (kappa b * z⁻¹)) := by
        rw [← closedProductMap_upperNormal b w hn, ← hp, ← doubleCurve_upper b z hz]
        exact he
      have hwz : w = kappa b * z⁻¹ :=
        CuspQuotient.axisMap_injective (CD).correction (CD).radius (CD).radius_pos
          (upperNeighbour 1) (curveIndex b)
          (CuspGeometry.inclusion_openEmbedding.injective he')
      exact Or.inr ⟨hz, ha, hw.trans (congrArg (upperNormal b) hwz)⟩
  · rintro (⟨ha, hv⟩ | ⟨hz, ha, hv⟩)
    · have hn : radiusSq (lowerNormal b z) ≤ closedRadius ^ 2 := by
        rw [← hv]
        exact p.2.property
      have hp : p = (((0 : ℂ) : RiemannSphere), ⟨lowerNormal b z, hn⟩) :=
        Prod.ext ha (Subtype.ext hv)
      rw [hp]
      exact closedProductMap_lowerNormal b z hn
    · have hn : radiusSq (upperNormal b (kappa b * z⁻¹)) ≤ closedRadius ^ 2 := by
        rw [← hv]
        exact p.2.property
      have hp : p = ((∞ : RiemannSphere), ⟨upperNormal b (kappa b * z⁻¹), hn⟩) :=
        Prod.ext ha (Subtype.ext hv)
      rw [hp]
      exact closedProductMap_upperNormal_finite b z hz hn

/-- The actual closed neighborhood removes exactly the two original
closed pole discs, including their boundary circles. -/
theorem finite_mem_closedDiskNeighborhood_iff (b : Bool) (z : ℂ) :
    CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) ∈
        closedDiskNeighborhood ↔
      ‖z‖ ≤ closedRadius ∨ outerRadius b ≤ ‖z‖ := by
  constructor
  · rintro ⟨p, he⟩
    obtain ⟨_, hv⟩ | ⟨hz, _, hv⟩ := (closedProductMap_eq_finite_iff b z p).mp he
    · left
      apply (radiusSq_lowerNormal_le_iff b z).mp
      rw [← hv]
      exact p.2.property
    · right
      apply (upper_norm_le_iff b z hz).mp
      apply (radiusSq_upperNormal_le_iff b _).mp
      rw [← hv]
      exact p.2.property
  · rintro (hz | hz)
    · have hn := (radiusSq_lowerNormal_le_iff b z).mpr hz
      exact ⟨(((0 : ℂ) : RiemannSphere), ⟨lowerNormal b z, hn⟩),
        closedProductMap_lowerNormal b z hn⟩
    · have hz0 : z ≠ 0 := norm_pos_iff.mp ((outerRadius_pos b).trans_le hz)
      have hn := (radiusSq_upperNormal_le_iff b _).mpr ((upper_norm_le_iff b z hz0).mpr hz)
      exact ⟨((∞ : RiemannSphere), ⟨upperNormal b (kappa b * z⁻¹), hn⟩),
        closedProductMap_upperNormal_finite b z hz0 hn⟩

/-- The actual ambient interior removes precisely the two open pole
discs, with no additional deck representatives. -/
theorem finite_mem_interior_closedDiskNeighborhood_iff (b : Bool) (z : ℂ) :
    CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) ∈
        interior closedDiskNeighborhood ↔
      ‖z‖ < closedRadius ∨ outerRadius b < ‖z‖ := by
  constructor
  · intro hx
    obtain ⟨p, he⟩ := interior_subset hx
    have hn : radiusSq p.2.val < closedRadius ^ 2 :=
      (closedProductMap_mem_interior_iff p).mp (he.symm ▸ hx)
    obtain ⟨_, hv⟩ | ⟨hz, _, hv⟩ := (closedProductMap_eq_finite_iff b z p).mp he
    · exact Or.inl ((radiusSq_lowerNormal_lt_iff b z).mp (hv ▸ hn))
    · exact Or.inr ((upper_norm_lt_iff b z hz).mp
        ((radiusSq_upperNormal_lt_iff b _).mp (hv ▸ hn)))
  · rintro (hz | hz)
    · have hn := (radiusSq_lowerNormal_lt_iff b z).mpr hz
      rw [← closedProductMap_lowerNormal b z hn.le]
      exact (closedProductMap_mem_interior_iff _).mpr hn
    · have hz0 : z ≠ 0 := norm_pos_iff.mp ((outerRadius_pos b).trans hz)
      have hn := (radiusSq_upperNormal_lt_iff b _).mpr ((upper_norm_lt_iff b z hz0).mpr hz)
      rw [← closedProductMap_upperNormal_finite b z hz0 hn.le]
      exact (closedProductMap_mem_interior_iff _).mpr hn

/-- The original infinity endpoint is deleted; it is the original
upper triple point on the fixed curve. -/
theorem infty_mem_interior_closedDiskNeighborhood (b : Bool) :
    CuspGeometry.doubleCurveParametrization (curveIndex b) (∞ : RiemannSphere) ∈
      interior closedDiskNeighborhood := by
  rw [CuspGeometry.doubleCurveParametrization_infty,
    ← CuspGeometry.doubleCurveParametrization_infty 1]
  exact doubleCurve_subset_interior_closedDiskNeighborhood
    (CuspGeometry.doubleCurveParametrization_mem 1 ∞)

/-- Both annular boundary circles land on the true ambient frontier,
and exhaust its intersection with the original finite curve. -/
theorem finite_mem_frontier_closedDiskNeighborhood_iff (b : Bool) (z : ℂ) :
    CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) ∈
        frontier closedDiskNeighborhood ↔
      ‖z‖ = closedRadius ∨ ‖z‖ = outerRadius b := by
  rw [closedDiskNeighborhood_isCompact.isClosed.frontier_eq]
  simp only [mem_sdiff, finite_mem_closedDiskNeighborhood_iff,
    finite_mem_interior_closedDiskNeighborhood_iff, not_or, not_lt]
  constructor
  · rintro ⟨hl | hr, hcl, hro⟩
    · exact Or.inl (le_antisymm hl hcl)
    · exact Or.inr (le_antisymm hro hr)
  · rintro (h | h)
    · rw [h]
      exact ⟨Or.inl le_rfl, le_rfl, (closedRadius_lt_outerRadius b).le⟩
    · rw [h]
      exact ⟨Or.inr le_rfl, (closedRadius_lt_outerRadius b).le, le_rfl⟩

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
