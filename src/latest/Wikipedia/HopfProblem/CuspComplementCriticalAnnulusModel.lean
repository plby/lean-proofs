import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusMembership
import Wikipedia.HopfProblem.CuspComplementCriticalAnnulusLocus

/-!
# The actual surviving critical curves as closed annuli

The annulus is a literal band in the original complex affine parameter,
with the fixed normal radius and the original upper deck factor. Its
homeomorphism to the remaining curve is the restriction of the original
sphere parametrization. Both ambient curves and the deleted neighborhood
are unchanged.
-/

noncomputable section

open Set Topology Metric
open scoped OnePoint

namespace Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.space_t2Space

/-- The exact closed annulus in the original affine curve parameter. -/
def annulus (b : Bool) : Set ℂ :=
  {z | closedRadius ≤ ‖z‖ ∧ ‖z‖ ≤ outerRadius b}

abbrev Annulus (b : Bool) := {z : ℂ // z ∈ annulus b}

theorem annulus_isCompact (b : Bool) : IsCompact (annulus b) := by
  have he : annulus b = closedBall (0 : ℂ) (outerRadius b) \ ball 0 closedRadius := by
    ext z
    simp only [annulus, mem_ofPred_eq, mem_sdiff, mem_closedBall, mem_ball,
      dist_zero_right, not_lt, and_comm]
  rw [he]
  exact (isCompact_closedBall (0 : ℂ) (outerRadius b)).inter_right isOpen_ball.isClosed_compl

instance annulusCompactSpace (b : Bool) : CompactSpace (Annulus b) :=
  isCompact_iff_compactSpace.mp (annulus_isCompact b)

theorem annulus_ne_zero (b : Bool) (z : Annulus b) : z.val ≠ 0 :=
  norm_pos_iff.mp (closedRadius_pos.trans_le z.property.1)

/-- The subset is cut out of the actual original double curve. -/
def remainingCurve (b : Bool) : Set Threefold.Space :=
  CuspGeometry.doubleCurve (curveIndex b) \ interior closedDiskNeighborhood

/-- The cut is the actual intersection with the carved cusp cap. -/
theorem remainingCurve_eq_inter_capComplement (b : Bool) :
    remainingCurve b = CuspGeometry.doubleCurve (curveIndex b) ∩ capComplement := by
  ext x
  constructor
  · rintro ⟨hc, hn⟩
    exact ⟨hc, doubleCurve_subset_cap (curveIndex b) hc, hn⟩
  · rintro ⟨hc, _, hn⟩
    exact ⟨hc, hn⟩

/-- Exact affine-parameter membership in the remaining original curve. -/
theorem finite_mem_remainingCurve_iff (b : Bool) (z : ℂ) :
    CuspGeometry.doubleCurveParametrization (curveIndex b) (z : RiemannSphere) ∈
        remainingCurve b ↔ z ∈ annulus b := by
  simp only [remainingCurve, mem_sdiff, CuspGeometry.doubleCurveParametrization_mem,
    finite_mem_interior_closedDiskNeighborhood_iff, true_and, not_or, not_lt,
    annulus, mem_ofPred_eq]

/-- The original sphere parametrization restricted to the literal closed annulus. -/
def annulusMap (b : Bool) (z : Annulus b) : Threefold.Space :=
  CuspGeometry.doubleCurveParametrization (curveIndex b) (z.val : RiemannSphere)

theorem annulusMap_continuous (b : Bool) : Continuous (annulusMap b) :=
  (CuspGeometry.doubleCurveParametrization_continuous (curveIndex b)).comp
    (OnePoint.continuous_coe.comp continuous_subtype_val)

theorem annulusMap_injective (b : Bool) : Function.Injective (annulusMap b) := by
  intro z w h
  apply Subtype.ext
  exact OnePoint.coe_injective
    ((CuspGeometry.doubleCurveParametrization_isEmbedding (curveIndex b)).injective h)

theorem annulusMap_isClosedEmbedding (b : Bool) : IsClosedEmbedding (annulusMap b) :=
  (annulusMap_continuous b).isClosedEmbedding (annulusMap_injective b)

theorem annulusMap_mem_remainingCurve (b : Bool) (z : Annulus b) :
    annulusMap b z ∈ remainingCurve b :=
  (finite_mem_remainingCurve_iff b z.val).mpr z.property

/-- No additional points survive outside the displayed annulus. -/
theorem annulusMap_range (b : Bool) : range (annulusMap b) = remainingCurve b := by
  apply subset_antisymm
  · rintro _ ⟨z, rfl⟩
    exact annulusMap_mem_remainingCurve b z
  · rintro x ⟨hc, hn⟩
    rw [← CuspGeometry.doubleCurveParametrization_range] at hc
    obtain ⟨p, hp⟩ := hc
    induction p using OnePoint.rec with
    | infty =>
        exact False.elim (hn (hp ▸ infty_mem_interior_closedDiskNeighborhood b))
    | coe z =>
        have hcut : CuspGeometry.doubleCurveParametrization (curveIndex b)
            (z : RiemannSphere) ∈ remainingCurve b :=
          ⟨CuspGeometry.doubleCurveParametrization_mem (curveIndex b) (z : RiemannSphere),
            fun hi => hn (hp ▸ hi)⟩
        have hz : z ∈ annulus b := (finite_mem_remainingCurve_iff b z).mp hcut
        exact ⟨⟨z, hz⟩, hp⟩

/-- A homeomorphism onto the actual remaining curve, using the original map. -/
def annulusHomeomorph (b : Bool) : Annulus b ≃ₜ remainingCurve b :=
  (annulusMap_isClosedEmbedding b).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (annulusMap_range b))

@[simp] theorem annulusHomeomorph_coe (b : Bool) (z : Annulus b) :
    (annulusHomeomorph b z : Threefold.Space) = annulusMap b z := rfl

theorem remainingCurve_isCompact (b : Bool) : IsCompact (remainingCurve b) := by
  rw [← annulusMap_range]
  exact isCompact_range (annulusMap_continuous b)

theorem remainingCurve_disjoint : Disjoint (remainingCurve false) (remainingCurve true) :=
  remainingCriticalPieces_disjoint

/-- These two actual annuli exhaust the ambient projection-critical
locus remaining in the carved cap. Boundary-restricted critical points
are a different statement. -/
theorem remainingCriticalLocus_eq_annuli :
    CuspGeometry.cuspCriticalLocus ∩ capComplement =
      remainingCurve false ∪ remainingCurve true :=
  cuspCriticalLocus_inter_capComplement

/-- The true inner frontier meets either annulus in exactly its two
parameter-radius levels. -/
theorem annulusMap_mem_frontier_iff (b : Bool) (z : Annulus b) :
    annulusMap b z ∈ frontier closedDiskNeighborhood ↔
      ‖z.val‖ = closedRadius ∨ ‖z.val‖ = outerRadius b :=
  finite_mem_frontier_closedDiskNeighborhood_iff b z.val

end Wikipedia.HopfProblem.CuspComplement.CriticalAnnulus
