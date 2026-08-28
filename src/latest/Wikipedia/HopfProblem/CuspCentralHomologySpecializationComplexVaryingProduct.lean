import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexVarying
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProduct

/-!
# Marked product coordinates for complex-level varying specialization

The actual source quotient gives marked compact-phase and base-torus
coordinates on each literal complex-time varying-twist fibre.  The
independently prescribed collapse is exactly compensated rotation in
these coordinates, and is therefore homotopic to the original product
collapse.  Holomorphic period data supply a common admissible radius for
all positive levels and all real lifts of the base angle.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse CuspHoneycomb
open SingularMayerVietoris PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- Compensated central rotation in the original marked product coordinates. -/
def productRotation (r : ℝ) :
    C(CompactFibreTorus × ProductTorus 2, QuotientCentralFibre C ε) :=
  (sourceRotation C ε hε r).comp
    ((sourceProductHomeomorph (C 0)).symm :
      C(CompactFibreTorus × ProductTorus 2, SourceModel (C 0)))

theorem productRotation_sourceCoordinates (r : ℝ) (p : PhasePlane) :
    productRotation C ε hε r (sourceProductCoordinates (C 0) p) =
      centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  change sourceRotation C ε hε r
    ((sourceProductHomeomorph (C 0)).symm (sourceProductCoordinates (C 0) p)) = _
  have hp : sourceProductHomeomorph (C 0) (sourceProjection (C 0) p) =
      sourceProductCoordinates (C 0) p := rfl
  rw [← hp, Homeomorph.symm_apply_apply, sourceRotation_projection]

/-- The marked base coordinate is still the integral period coordinate,
and both the frozen fibre shear and the complex base phase are retained. -/
theorem productRotation_coordinateProjection (r : ℝ) (u : CompactFibreTorus) (y : Plane) :
    productRotation C ε hε r (u, coordinateProjection 2 y) =
      centralProject C ε hε (rotatingCentralPoint (C 0) r
        (u * sourcePhaseCharacter (C 0) (realCuspVector y), realCuspVector y)) := by
  change sourceRotation C ε hε r
    ((sourceProductHomeomorph (C 0)).symm (u, coordinateProjection 2 y)) = _
  rw [sourceProductHomeomorph_symm_coordinateProjection, sourceRotation_projection]

@[simp] theorem productRotation_zero : productRotation C ε hε 0 = productCollapse C ε hε := by
  rw [productRotation, sourceRotation_zero]
  rfl

/-- The actual compensated rotation is homotopic to the original marked collapse. -/
def productRotationHomotopy (r : ℝ) :
    (productCollapse C ε hε).Homotopy (productRotation C ε hε r) :=
  (sourceRotationHomotopy C ε hε r).compContinuousMap
    ((sourceProductHomeomorph (C 0)).symm :
      C(CompactFibreTorus × ProductTorus 2, SourceModel (C 0)))

theorem productRotation_homologyMap (r : ℝ) (n : ℕ) :
    singularHomologyMap (productRotation C ε hε r) n =
      singularHomologyMap (productCollapse C ε hε) n :=
  (homotopy_homologyMap (productRotationHomotopy C ε hε r) n).symm

variable (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε) (r : ℝ)

/-- The marked product gives the literal varying-twist fibre at the
chosen complex time, through genuine inverse straightening. -/
def varyingComplexProductFibreHomeomorph :
    (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  (sourceProductHomeomorph (C 0)).symm.trans
    (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r)

theorem varyingComplexProductFibreHomeomorph_sourceCoordinates (p : PhasePlane) :
    varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r
        (sourceProductCoordinates (C 0) p) =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p := by
  change varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
    ((sourceProductHomeomorph (C 0)).symm (sourceProductCoordinates (C 0) p)) = _
  have hp : sourceProductHomeomorph (C 0) (sourceProjection (C 0) p) =
      sourceProductCoordinates (C 0) p := rfl
  rw [← hp, Homeomorph.symm_apply_apply, varyingComplexSourceHomeomorph_projection]

theorem varyingComplexProductFibreHomeomorph_coordinateProjection
    (u : CompactFibreTorus) (y : Plane) :
    varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r
        (u, coordinateProjection 2 y) =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r
        (u * sourcePhaseCharacter (C 0) (realCuspVector y), realCuspVector y) := by
  change varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
    ((sourceProductHomeomorph (C 0)).symm (u, coordinateProjection 2 y)) = _
  rw [sourceProductHomeomorph_symm_coordinateProjection, varyingComplexSourceHomeomorph_projection]

/-- Exact factorization of the independently prescribed varying-fibre
collapse, including the actual complex base phase. -/
theorem prescribedActualFibreCollapse_varyingComplexProductFibreHomeomorph
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : CompactFibreTorus × ProductTorus 2) :
    prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r p) =
      productRotation C ε hε r p :=
  prescribedActualFibreCollapse_varyingComplexSourceHomeomorph
    C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε ((sourceProductHomeomorph (C 0)).symm p)

theorem varyingComplexCollapseMap_comp_product (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε).comp
      (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
        C(CompactFibreTorus × ProductTorus 2, ActualQuotientFibre C ε (rotatedLevel ρ r))) =
      productRotation C ε hε r :=
  ContinuousMap.ext (prescribedActualFibreCollapse_varyingComplexProductFibreHomeomorph
    C ε hε ρ hρ hε1 hρε hC hRC hRD r η hρη hηε)

/-- A genuine homotopy, not just a coordinate analogy, identifies the
complex-level specialization with the original product collapse. -/
def varyingComplexProductCollapseHomotopy (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    (productCollapse C ε hε).Homotopy
      ((varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε).comp
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
          C(CompactFibreTorus × ProductTorus 2, ActualQuotientFibre C ε (rotatedLevel ρ r)))) := by
  rw [varyingComplexCollapseMap_comp_product]
  exact productRotationHomotopy C ε hε r

/-- In every singular homology degree, actual specialization has the
same marked map as the original positive-level product collapse. -/
theorem varyingComplexProductCollapseMap_homology (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (n : ℕ) (a : SingularHomology (CompactFibreTorus × ProductTorus 2) n) :
    singularHomologyMap
      (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε) n
      (homeomorphHomologyEquiv
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r) n a) =
      singularHomologyMap (productCollapse C ε hε) n a := by
  change (singularHomologyMap
      (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε) n).comp
      (singularHomologyMap
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
          C(CompactFibreTorus × ProductTorus 2,
            ActualQuotientFibre C ε (rotatedLevel ρ r))) n) a = _
  rw [← singularHomologyMap_comp, varyingComplexCollapseMap_comp_product,
    productRotation_homologyMap]

/-- Holomorphic period data provide a common small radius and literal
marked fibre models for all positive radii and all real base angles. -/
theorem exists_complex_product_models (R : ℝ) (hR : 0 < R)
    (hCR : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 R)) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ < R ∧ δ < 1 ∧
      ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ < δ → ∀ r : ℝ,
        ∃ e : (CompactFibreTorus × ProductTorus 2) ≃ₜ
            ActualQuotientFibre C δ (rotatedLevel ρ r),
          ∀ (η : ℝ) (hρη : ρ ≤ η) (hηδ : η < δ) (p : CompactFibreTorus × ProductTorus 2),
            prescribedActualFibreCollapse C δ hδ hηδ (rotatedLevel ρ r)
                (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
                (e p) = productRotation C δ hδ r p := by
  obtain ⟨δ, hδ, hδR, hδ1, hRCδ, hRDδ⟩ :=
    exists_common_frozen_radius C hR (fun i j => (hCR i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hCR i j).mono (Metric.ball_subset_ball hδR.le)
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro ρ hρ hρδ r
  refine ⟨varyingComplexProductFibreHomeomorph C δ hδ ρ hρ hδ1 hρδ hCδ hRCδ hRDδ r, ?_⟩
  intro η hρη hηδ p
  exact prescribedActualFibreCollapse_varyingComplexProductFibreHomeomorph
    C δ hδ ρ hρ hδ1 hρδ hCδ hRCδ hRDδ r η hρη hηδ p

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
