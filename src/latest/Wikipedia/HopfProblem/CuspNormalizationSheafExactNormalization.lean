import Wikipedia.HopfProblem.CuspNormalizationSheafBoundaryStalkMap
import Wikipedia.HopfProblem.CuspNormalizationSheafNormalizationStalkPullback
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactUniform
import Wikipedia.HopfProblem.CuspNormalization
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Exactness at the actual normalization direct image

The genuine reduced-function stalk, the genuine normalization stalk, and
the genuine double-curve stalks have independently proved analytic-germ
coordinates. The actual first and second sheaf arrows become literal
restriction and oriented axis difference. Analytic inclusion-exclusion
therefore proves exactness on every actual stalk, hence on the actual
sheaves by Mathlib's stalk exactness criterion.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace ToricFan
open CuspQuotient.NormalizationLocalCoordinates
open SheafNormalizationStalk SheafBoundaryStalk

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Every actual cusp-normalization chart gives exactness of the literal
first two stalk maps. No analytic extension or local exactness is an input. -/
theorem normalizationStalkMaps_exact (a : Tube (disc ε)) (s : Triangle)
    (x : CentralSpace C ε)
    (hx : x.val ∈ (normalizationChart C ε hε hε1 hC hR a s).source) :
    Function.Exact (normalizationStalkMap C ε hε hε1 hC hR x)
      (deltaZeroStalkMap C ε hε hε1 hC hR x) := by
  let b := normalizationChart C ε hε hε1 hC hR a s x.val
  let e₀ := reducedStalkEquiv C ε hε hε1 hC hR a s x hx
  let e₁ := normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx
  let e₂ := boundaryStalkEquivAt C ε hε hε1 hC hR a s x hx
  intro φ
  constructor
  · intro hφ
    have hmodel : orientedDifference s (Germs.activeBranches b) (e₁ φ) = 0 := by
      rw [← deltaZeroStalkMap_conjugacy C ε hε hε1 hC hR a s x hx, hφ, map_zero]
    obtain ⟨ψ, hψ⟩ := (orientedDifference_exact s (Germs.activeBranches b) (e₁ φ)).mp hmodel
    refine ⟨e₀.symm ψ, ?_⟩
    apply e₁.injective
    change normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx
      (normalizationStalkMap C ε hε hε1 hC hR x (e₀.symm ψ)) = e₁ φ
    rw [normalizationStalkMap_conjugacy]
    change Germs.restrictionToBranches (Germs.activeBranches b) (e₀ (e₀.symm ψ)) = e₁ φ
    rw [e₀.apply_symm_apply]
    exact hψ
  · rintro ⟨ψ, rfl⟩
    apply e₂.injective
    change boundaryStalkEquivAt C ε hε hε1 hC hR a s x hx
        (deltaZeroStalkMap C ε hε hε1 hC hR x
          (normalizationStalkMap C ε hε hε1 hC hR x ψ)) = e₂ 0
    rw [deltaZeroStalkMap_conjugacy, normalizationStalkMap_conjugacy, map_zero]
    exact orientedDifference_restriction s (Germs.activeBranches b) (e₀ ψ)

/-- Categorical exactness at the actual normalization stalk in an
arbitrary genuine adapted chart. -/
theorem normalizationComplex_stalk_exact (a : Tube (disc ε)) (s : Triangle)
    (x : CentralSpace C ε)
    (hx : x.val ∈ (normalizationChart C ε hε hε1 hC hR a s).source) :
    ((normalizationComplex C ε hε hε1 hC hR).map
      (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x)).Exact :=
  (ShortComplex.ab_exact_iff_function_exact _).mpr
    (normalizationStalkMaps_exact C ε hε hε1 hC hR a s x hx)

/-- The actual reduced holomorphic sheaf is exactly the kernel of the
actual signed boundary difference on the normalization direct image. -/
theorem normalizationComplex_exact : (normalizationComplex C ε hε hε1 hC hR).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (normalizationComplex C ε hε hε1 hC hR)).mpr
  intro x
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  obtain ⟨a, s, _, hx, _⟩ :=
    componentProjection_local_coordinate_normalization C ε hε hε1 hC hR x.val
  exact normalizationComplex_stalk_exact C ε hε hε1 hC hR a s x hx

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
