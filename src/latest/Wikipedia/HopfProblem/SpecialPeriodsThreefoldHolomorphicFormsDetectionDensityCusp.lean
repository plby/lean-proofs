import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry

/-!
# Density of the noncentral locus in the actual cusp piece

The dense torus of the original toric variety remains dense in the open
cusp tube.  Its image under the original continuous quotient projection
is dense in the full cusp piece and has nonzero toric parameter.  Thus
every point of the actual central cusp fibre is approached by regular
points, without any change of topology or atlas.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.DetectionDensity

/-- The original nonzero monomial locus is dense in every actual toric cusp quotient. -/
theorem cusp_projection_ne_zero_dense
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Dense {q : CuspQuotient.QuotientSpace C ε | CuspQuotient.projection C ε q ≠ 0} := by
  have hs : Function.Surjective (CuspQuotient.quotientMap C ε) := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => exact ⟨x, rfl⟩
  apply hs.denseRange.dense_of_mapsTo (CuspQuotient.quotientMap_continuous C ε)
    (CuspQuotient.tube_torus_dense ε)
  intro x hx
  exact (ToricSpace.mem_openTorus_iff (x : ToricSpace.Space)).mp hx

/-- Density in the literal full cusp piece used by the global gluing. -/
theorem cusp_parameter_ne_zero_dense :
    Dense {x : CuspGeometry.LocalSpace | CuspGeometry.parameter x ≠ 0} :=
  cusp_projection_ne_zero_dense CuspGeometry.data.correction CuspGeometry.data.radius

/-- The regular locus on the cusp patch is exactly the nonzero locus
of its unchanged original toric parameter. -/
theorem cusp_inclusion_mem_regular_iff (x : CuspGeometry.LocalSpace) :
    CuspGeometry.inclusion x ∈ regularLocus ↔ CuspGeometry.parameter x ≠ 0 := by
  rw [mem_regularLocus, CuspGeometry.projection_inclusion]
  exact CuspPiece.projectionToBase_mem_regular_iff specialCuspData specialBaseCover x

theorem cusp_regular_preimage_dense :
    Dense (CuspGeometry.inclusion ⁻¹' (regularLocus : Set Space)) := by
  have he : CuspGeometry.inclusion ⁻¹' (regularLocus : Set Space) =
      {x : CuspGeometry.LocalSpace | CuspGeometry.parameter x ≠ 0} :=
    Set.ext cusp_inclusion_mem_regular_iff
  rw [he]
  exact cusp_parameter_ne_zero_dense

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.DetectionDensity
