import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexVaryingProduct
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexArgument

/-!
# Actual prescribed specialization at every nonzero complex level

Every fixed nonzero time has a genuine marked product homeomorphism.
Under that homeomorphism the independently prescribed collapse is joined
to the original product collapse by an actual homotopy, and its integral
singular homology map agrees in every degree.  The final existence theorem
derives a common admissible radius from the holomorphic period data.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The asserted property of a constructed product model.  The map in
this property is always the original independently prescribed collapse;
it is not defined by transporting the product collapse. -/
def IsPrescribedProductModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (t : ℂ) (ht : t ≠ 0)
    (e : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C ε t) : Prop :=
  ∀ (η : ℝ) (htη : ‖t‖ ≤ η) (hηε : η < ε),
    ∃ hc : Continuous (prescribedActualFibreCollapse C ε hε hηε t ht htη),
      (productCollapse C ε hε).Homotopic
        ((⟨prescribedActualFibreCollapse C ε hε hηε t ht htη, hc⟩ :
          C(ActualQuotientFibre C ε t, QuotientCentralFibre C ε)).comp
            (e : C(CompactFibreTorus × ProductTorus 2, ActualQuotientFibre C ε t))) ∧
      ∀ (n : ℕ) (a : SingularHomology (CompactFibreTorus × ProductTorus 2) n),
        singularHomologyMap
          (⟨prescribedActualFibreCollapse C ε hε hηε t ht htη, hc⟩ :
            C(ActualQuotientFibre C ε t, QuotientCentralFibre C ε)) n
          (homeomorphHomologyEquiv e n a) =
            singularHomologyMap (productCollapse C ε hε) n a

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε)

/-- The compensated model at a chosen radius and real angle satisfies
the actual homotopy and all-degree homology identities. -/
theorem varyingComplexProductFibreHomeomorph_isPrescribedProductModel
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ < ε) (r : ℝ) :
    IsPrescribedProductModel C ε hε (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
      (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r) := by
  intro η htη hηε
  have hρη : ρ ≤ η := by rwa [norm_rotatedLevel ρ r hρ.le] at htη
  refine ⟨prescribedActualFibreCollapse_varyingComplex_continuous
    C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε, ?_, ?_⟩
  · exact ⟨varyingComplexProductCollapseHomotopy
      C ε hε ρ hρ hε1 hρε hC hRC hRD r η hρη hηε⟩
  · intro n a
    exact varyingComplexProductCollapseMap_homology
      C ε hε ρ hρ hε1 hρε hC hRC hRD r η hρη hηε n a

include hε1 hC hRC hRD in
/-- Every nonzero complex time in the admissible disc has a genuine
product model with the actual prescribed-specialization identities. -/
theorem exists_product_model_at_nonzero_level (t : ℂ) (ht : t ≠ 0) (htε : ‖t‖ < ε) :
    ∃ e : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C ε t,
      IsPrescribedProductModel C ε hε t ht e := by
  have hρ : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hm : ∃ e : (CompactFibreTorus × ProductTorus 2) ≃ₜ
      ActualQuotientFibre C ε (rotatedLevel ‖t‖ (argumentTurns t)),
      IsPrescribedProductModel C ε hε (rotatedLevel ‖t‖ (argumentTurns t))
        (rotatedLevel_ne_zero ‖t‖ (argumentTurns t) hρ) e :=
    ⟨varyingComplexProductFibreHomeomorph
        C ε hε ‖t‖ hρ hε1 htε hC hRC hRD (argumentTurns t),
      varyingComplexProductFibreHomeomorph_isPrescribedProductModel
        C ε hε hε1 hC hRC hRD ‖t‖ hρ htε (argumentTurns t)⟩
  have transfer (u : ℂ) (hu : u ≠ 0) (hut : u = t)
      (huModel : ∃ e : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C ε u,
        IsPrescribedProductModel C ε hε u hu e) :
      ∃ e : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C ε t,
        IsPrescribedProductModel C ε hε t ht e := by
    subst u
    exact huModel
  exact transfer _ _ (rotatedLevel_norm_argumentTurns t) hm

/-- Holomorphic period data alone supply a common small disc in which
every nonzero complex fibre has the proved actual specialization model.
The fibre homeomorphism is independent of the containing closed-tube radius. -/
theorem exists_all_nonzero_product_models (R : ℝ) (hR : 0 < R)
    (hCR : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 R)) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ < R ∧ δ < 1 ∧
      ∀ (t : ℂ) (ht : t ≠ 0), ‖t‖ < δ →
        ∃ e : (CompactFibreTorus × ProductTorus 2) ≃ₜ ActualQuotientFibre C δ t,
          IsPrescribedProductModel C δ hδ t ht e := by
  obtain ⟨δ, hδ, hδR, hδ1, hRCδ, hRDδ⟩ :=
    exists_common_frozen_radius C hR (fun i j => (hCR i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hCR i j).mono (Metric.ball_subset_ball hδR.le)
  refine ⟨δ, hδ, hδR, hδ1, ?_⟩
  intro t ht htδ
  exact exists_product_model_at_nonzero_level C δ hδ hδ1 hCδ hRCδ hRDδ t ht htδ

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
