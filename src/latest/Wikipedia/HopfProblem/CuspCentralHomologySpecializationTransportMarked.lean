import Wikipedia.HopfProblem.CuspCentralHomologySpecializationNative

/-!
# Transporting the actual marked specialization calculation

An actual homeomorphism of a fibre, together with an actual homotopy to
the marked collapse, transports its proved integral homology calculation.
The subsequent existence theorem supplies these geometric data; no
homology representation, surjectivity, or kernel formula is a hypothesis
of this transport lemma.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    {X : Type} [TopologicalSpace X] (E : ProductTorus 4 ≃ₜ X)
    (f : C(X, QuotientCentralFibre C r))
    (h : (markedCollapse C r hr).Homotopic (f.comp (E : C(ProductTorus 4, X))))

include h in
/-- The actual map in the actual inverse-homeomorphism homology coordinates. -/
theorem markedSpecialization_homology_map (n : ℕ) (a : SingularHomology X n) :
    singularHomologyMap f n a = singularHomologyMap (markedCollapse C r hr) n
      ((homeomorphHomologyEquiv E n).symm a) := by
  have heq := homotopic_homologyMap h n
  rw [singularHomologyMap_comp] at heq
  have ha := LinearMap.congr_fun heq ((homeomorphHomologyEquiv E n).symm a)
  change singularHomologyMap (markedCollapse C r hr) n
      ((homeomorphHomologyEquiv E n).symm a) =
    singularHomologyMap f n
      (homeomorphHomologyEquiv E n ((homeomorphHomologyEquiv E n).symm a)) at ha
  rw [LinearEquiv.apply_symm_apply] at ha
  exact ha.symm

include hC h in
theorem markedSpecialization_homology_surjective (n : ℕ) :
    Function.Surjective (singularHomologyMap f n) := by
  intro b
  obtain ⟨a, ha⟩ := markedCollapse_homology_surjective C r hr hC n b
  refine ⟨homeomorphHomologyEquiv E n a, ?_⟩
  rw [markedSpecialization_homology_map C r hr E f h n, LinearEquiv.symm_apply_apply]
  exact ha

include hC h in
/-- Exact integral relations for the actual fibre map. -/
theorem markedSpecialization_homology_eq_zero_iff (n : ℕ) (a : SingularHomology X n) :
    singularHomologyMap f n a = 0 ↔
      ∃ b : SingularHomology (ProductTorus 4) n,
        singularHomologyMap (torusMatrixMap M₀) n b - b =
          (homeomorphHomologyEquiv E n).symm a := by
  rw [markedSpecialization_homology_map C r hr E f h n,
    markedCollapse_homology_eq_zero_iff C r hr hC n]

include hC h in
/-- The degree-two relations in the original integral exterior-period marking. -/
theorem markedSpecialization_homologyTwo_eq_zero_iff (a : SingularHomology X 2) :
    singularHomologyMap f 2 a = 0 ↔
      ∃ v : latticeExterior 2, exteriorPower.map 2 M₀.mulVecLin v - v =
        coordinateTorusH2ExteriorEquiv ((homeomorphHomologyEquiv E 2).symm a) := by
  rw [markedSpecialization_homology_map C r hr E f h 2,
    markedCollapse_homologyTwo_eq_zero_iff C r hr hC]

include hC h in
/-- The degree-three relations use the actual exterior-cube action. -/
theorem markedSpecialization_homologyThree_eq_zero_iff (a : SingularHomology X 3) :
    singularHomologyMap f 3 a = 0 ↔
      ∃ v : latticeExterior 3, exteriorPower.map 3 M₀.mulVecLin v - v =
        coordinateTorusH3ExteriorEquiv ((homeomorphHomologyEquiv E 3).symm a) := by
  rw [markedSpecialization_homology_map C r hr E f h 3,
    markedCollapse_homologyThree_eq_zero_iff C r hr hC]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
