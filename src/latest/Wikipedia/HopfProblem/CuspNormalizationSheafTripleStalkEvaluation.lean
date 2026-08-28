import Wikipedia.HopfProblem.CuspNormalizationSheafCuspDifferentials
import Wikipedia.HopfProblem.CuspNormalizationSheafTripleStalkEvaluationBasic

/-!
# Actual curve evaluation at the triple-point stalks

Actual constant holomorphic sections make evaluation surjective at its
support. The first curve summand of the actual boundary biproduct maps
to that evaluation under the signed last differential.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace
open CuspQuotient.NormalizationCurves

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- On the first actual curve summand, the alternating differential is
exactly its positively signed actual evaluation morphism. -/
theorem boundary_inclusion_zero_deltaOneAt (t : Fin 2) :
    biproduct.ι (curveSheaf C ε hε hε1 hC hR) 0 ≫
      deltaOneAt C ε hε hε1 hC hR t = curveEvaluation C ε hε hε1 hC hR 0 t := by
  simp only [deltaOneAt, Preadditive.comp_add, Preadditive.comp_sub,
    biproduct.ι_π_self_assoc,
    biproduct.ι_π_ne_assoc _ (by decide : (0 : Fin 3) ≠ 1),
    biproduct.ι_π_ne_assoc _ (by decide : (0 : Fin 3) ≠ 2), zero_comp, sub_zero, add_zero]

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
