import Wikipedia.HopfProblem.CuspNormalizationSheafBoundaryAugmentationEvaluation
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactAugmentation

/-!
# The actual last differential is the oriented analytic augmentation

At an actual triple point with a full active branch set, the analytic
augmentation of the actual boundary-stalk coordinates has precisely the
same three scalar coefficients and signs as the actual last sheaf
differential. The scalar target is the proved actual triple-stalk
equivalence, so this is a comparison of the actual sheaf maps.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryAugmentation

open CuspQuotient ToricCharts ToricSpace ToricFan NormalizationCurves
  NormalizationLocalCoordinates SheafResolution SheafGermComplex

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- The literal augmentation formula for any active set proved to be
the full triple, without transporting its dependent curve coordinates. -/
theorem orientedAugmentation_eq_signed_of_full (s : Triangle) (S : Finset (Fin 3))
    (hS : S = Finset.univ) (g : IncidentCurve s S → AxisGerm) :
    orientedAugmentation s S g =
      Germs.eval (0 : ℂ) (g (fullIncidentCurve s S hS 0)) -
        Germs.eval (0 : ℂ) (g (fullIncidentCurve s S hS 1)) +
        Germs.eval (0 : ℂ) (g (fullIncidentCurve s S hS 2)) := by
  simp only [orientedAugmentation, dif_pos hS]
  rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "Base" => TopCat.of (CentralSpace C ε)
local notation "e" => normalizationChart C ε hε hε1 hC hR a s
local notation "p" => triplePoint C ε hε

/-- In the genuine boundary and triple stalk comparisons, the actual
last differential has exactly the actual oriented analytic augmentation. -/
theorem orientedAugmentation_eq_deltaOne_at_triplePoint (t : Fin 2)
    (hx : (p t).val ∈ (e).source)
    (hfull : Germs.activeBranches ((e) (p t).val) = Finset.univ)
    (β : (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk (p t)) :
    orientedAugmentation s (Germs.activeBranches ((e) (p t).val))
        (SheafBoundaryStalk.boundaryStalkEquivAt C ε hε hε1 hC hR a s (p t) hx β) =
      tripleStalkEquiv C ε hε hε1 hC hR t
        ((SheafBiproduct.stalkFunctor Base (p t)).map (deltaOne C ε hε hε1 hC hR) β) := by
  rw [orientedAugmentation_eq_signed_of_full s _ hfull]
  simp only [boundaryStalkEquivAt_eval_at_triplePoint]
  exact (tripleStalkEquiv_deltaOne_signed C ε hε hε1 hC hR t β).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryAugmentation
