import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationCritical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalization
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspRationalCurves

/-!
# Fibre and critical-point classification of the actual compact threefold

The constructed sphere projection has exactly the critical values
`∞`, `0`, and `1`. Its critical locus is the union of the entire fibres at
zero and one with the three rational double curves of the infinity fibre.

All finite fibres carry the proved ambient-slice complex atlases. The
two multiple fibres are the genuine order-three and order-four affine
quotient surfaces, with exact cubic and quartic projection charts at
every point. Every other finite fibre is an actual special period torus.

At infinity the original toric surface maps properly and holomorphically
onto the whole literal fibre. Its finite fibres count the actual local
branches. The native analytic product charts identify the singular fibre
locally with one, two, or three coordinate planes. Its three double
curves are actual holomorphic sphere images meeting at the two triple
points. No decomposition into three global surface components, or
unproved ring-theoretic normalization property, is asserted.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace

/-- Every actual sphere fibre is compact and connected, including the
singular infinity fibre and the two multiple fibres. -/
theorem sphereFibre_compact_connected (b : RiemannSphere) :
    IsCompact (SphereFibre b) ∧ IsConnected (SphereFibre b) :=
  ⟨Threefold.projectionSphere_fibre_compact b,
    Threefold.projectionSphere_fibre_isConnected b⟩

/-- The actual critical part of the infinity fibre is exactly the
union of the images of its three genuine holomorphic sphere maps. -/
theorem cusp_criticalLocus_eq_rationalCurves :
    criticalLocus ∩ CuspGeometry.sphereCuspFibre =
      ⋃ i : Fin 3, range (CuspGeometry.doubleCurveParametrization i) := by
  simp only [criticalLocus_inter_cuspFibre,
    CuspGeometry.doubleCurveParametrization_range, CuspGeometry.doubleStratum_eq_union]

/-- The finite fibre of the actual toric component map has at least two
points precisely at a critical point of the global sphere projection. -/
theorem cusp_component_card_critical_iff (x : CuspGeometry.sphereCuspFibre) :
    2 ≤ (CuspGeometry.componentToFibre ⁻¹' {x}).ncard ↔
      (x : Threefold.Space) ∈ criticalLocus := by
  rw [CuspGeometry.componentToFibre_fibre_card]
  exact (CuspGeometry.mem_doubleStratum_iff x).symm.trans
    (cusp_critical_iff_mem_doubleStratum x x.property).symm

/-- A single preimage under the actual toric component map is
equivalent to a surjective global projection differential. -/
theorem cusp_component_card_one_iff_surjective (x : CuspGeometry.sphereCuspFibre) :
    (CuspGeometry.componentToFibre ⁻¹' {x}).ncard = 1 ↔
      Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (x : Threefold.Space)) := by
  rw [CuspGeometry.componentToFibre_fibre_card]
  exact (CuspGeometry.fibre_mfderiv_surjective_iff x).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification
