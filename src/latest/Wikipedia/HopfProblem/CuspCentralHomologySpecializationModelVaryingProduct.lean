import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProduct
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelVarying

/-!
# Marked product coordinates on the actual varying-twist fibre

The original change of twist transfers the proved positive-real frozen
model to the literal fibre of the varying cusp quotient. The independent
prescribed collapse becomes the same actual marked product collapse.
Continuity of the supplied holomorphic period data gives a sufficiently
small radius on which these homeomorphisms exist; no fibre identification
or collapse factorization is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspHoneycomb
open PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε)

/-- Marked compact phases and base periods give the literal varying-twist
positive-real fibre, through the actual straightening homeomorphism. -/
def varyingProductFibreHomeomorph :
    (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C ε (ρ : ℂ) :=
  (sourceProductHomeomorph (C 0)).symm.trans
    (varyingSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD)

theorem varyingProductFibreHomeomorph_sourceCoordinates (p : PhasePlane) :
    varyingProductFibreHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
        (sourceProductCoordinates (C 0) p) =
      varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD p := by
  change varyingSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
    ((sourceProductHomeomorph (C 0)).symm (sourceProductCoordinates (C 0) p)) = _
  have hp : sourceProductHomeomorph (C 0) (sourceProjection (C 0) p) =
      sourceProductCoordinates (C 0) p := rfl
  rw [← hp, Homeomorph.symm_apply_apply, varyingSourceHomeomorph_projection]

/-- The actual integral base marking is `β`, with normalized honeycomb
position `B₀ β` and the explicitly retained frozen phase shear. -/
theorem varyingProductFibreHomeomorph_coordinateProjection
    (u : CompactFibreTorus) (y : Plane) :
    varyingProductFibreHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
        (u, coordinateProjection 2 y) =
      varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD
        (u * sourcePhaseCharacter (C 0) (realCuspVector y), realCuspVector y) := by
  change varyingSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
    ((sourceProductHomeomorph (C 0)).symm (u, coordinateProjection 2 y)) = _
  rw [sourceProductHomeomorph_symm_coordinateProjection, varyingSourceHomeomorph_projection]

/-- The map on the original varying-twist fibre is the independently
prescribed collapse, exactly, not merely a map with the same shape. -/
theorem prescribedActualFibreCollapse_varyingProductFibreHomeomorph
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : CompactFibreTorus × ProductTorus 2) :
    prescribedActualFibreCollapse C ε hε hηε (ρ : ℂ)
        (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)
        (varyingProductFibreHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p) =
      productCollapse C ε hε p :=
  prescribedActualFibreCollapse_varyingSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
    η hρη hηε ((sourceProductHomeomorph (C 0)).symm p)

/-- Holomorphic period data supply an actual small radius and all positive-real
marked fibre models, with the proved prescribed-collapse factorization. -/
theorem exists_positiveReal_product_models (r : ℝ) (hr : 0 < r)
    (hCr : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ < r ∧ δ < 1 ∧
      ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ < δ →
        ∃ e : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C δ (ρ : ℂ),
          ∀ (η : ℝ) (hρη : ρ ≤ η) (hηδ : η < δ) (p : CompactFibreTorus × ProductTorus 2),
            prescribedActualFibreCollapse C δ hδ hηδ (ρ : ℂ)
                (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)
                (e p) = productCollapse C δ hδ p := by
  obtain ⟨δ, hδ, hδr, hδ1, hRCδ, hRDδ⟩ :=
    exists_common_frozen_radius C hr (fun i j => (hCr i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hCr i j).mono (Metric.ball_subset_ball hδr.le)
  refine ⟨δ, hδ, hδr, hδ1, ?_⟩
  intro ρ hρ hρδ
  refine ⟨varyingProductFibreHomeomorph C ρ hρ δ hδ hδ1 hρδ hCδ hRCδ hRDδ, ?_⟩
  intro η hρη hηδ p
  exact prescribedActualFibreCollapse_varyingProductFibreHomeomorph
    C ρ hρ δ hδ hδ1 hρδ hCδ hRCδ hRDδ η hρη hηδ p

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
