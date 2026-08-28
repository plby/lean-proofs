import Wikipedia.HopfProblem.CuspNormalizationSheafBoundaryAugmentationTriple

/-!
# The actual last-map kernel has zero analytic augmentation

If the actual last sheaf differential kills an actual boundary-stalk
element, its actual analytic coordinates have zero oriented augmentation.
For a full active set this follows from the actual triple-point
comparison; for every smaller active set the augmentation is zero.
The proved analytic exactness then supplies an actual analytic
branch-germ preimage, for transport back through the normalization-stalk
equivalence in the middle exactness proof.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryAugmentation

open CuspQuotient ToricCharts ToricSpace ToricFan NormalizationCurves
  NormalizationLocalCoordinates SheafResolution SheafGermComplex

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "Base" => TopCat.of (CentralSpace C ε)
local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The kernel condition for the actual last differential implies the
zero augmentation condition on the actual analytic curve coordinates. -/
theorem orientedAugmentation_eq_zero_of_deltaOne_eq_zero (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source)
    (β : (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x)
    (hβ : (SheafBiproduct.stalkFunctor Base x).map (deltaOne C ε hε hε1 hC hR) β = 0) :
    orientedAugmentation s (Germs.activeBranches ((e) x.val))
      (SheafBoundaryStalk.boundaryStalkEquivAt C ε hε hε1 hC hR a s x hx β) = 0 := by
  classical
  by_cases hfull : Germs.activeBranches ((e) x.val) = Finset.univ
  · obtain ⟨t, rfl⟩ := exists_triplePoint_of_full_active C ε hε hε1 hC hR a s x hx hfull
    exact (orientedAugmentation_eq_deltaOne_at_triplePoint
      C ε hε hε1 hC hR a s t hx hfull β).trans
      ((congrArg (tripleStalkEquiv C ε hε hε1 hC hR t) hβ).trans
        (map_zero (tripleStalkEquiv C ε hε hε1 hC hR t)))
  · exact orientedAugmentation_eq_zero_of_ne s _ hfull _

/-- Actual analytic exactness produces a branch-germ preimage for the
actual coordinates of every actual boundary stalk killed by the last map. -/
theorem exists_orientedDifference_preimage_of_deltaOne_eq_zero (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source)
    (β : (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x)
    (hβ : (SheafBiproduct.stalkFunctor Base x).map (deltaOne C ε hε hε1 hC hR) β = 0) :
    ∃ f : Germs.activeBranches ((e) x.val) → Germs.BranchGerm,
      orientedDifference s (Germs.activeBranches ((e) x.val)) f =
        SheafBoundaryStalk.boundaryStalkEquivAt C ε hε hε1 hC hR a s x hx β :=
  (orientedDifference_aug_exact s (Germs.activeBranches ((e) x.val)) _).mp
    (orientedAugmentation_eq_zero_of_deltaOne_eq_zero C ε hε hε1 hC hR a s x hx β hβ)

end Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryAugmentation
