import Wikipedia.HopfProblem.CuspNormalizationSheafManifoldStalk
import Wikipedia.HopfProblem.CuspNormalizationBranches
import Wikipedia.HopfProblem.CuspNormalizationGermsRestriction

/-!
# Genuine holomorphic stalks at the actual normalization branch points

The inverse of the actual translated affine branch parametrization is a
proved maximal-atlas chart on the original ray divisor.  Applying the
categorical manifold-stalk comparison in this chart identifies the stalk
at `branchAffine C s j w` with the actual analytic-germ ring of complex
two-space at zero.  Its section formula uses the literal branch map at
`w + z`, not an abstractly reindexed or transported stalk.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk

open CuspQuotient ToricCharts ToricComponent ToricFan ToricSpace

local notation "E₂" => CoordinateSpace 2

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : Triangle) (j : Fin 3) (w : E₂)

/-- The actual branch point lies in the domain of the inverse branch chart. -/
theorem branchChart_source :
    branchAffine C s j w ∈ (branchParametrization C s j).symm.source := by
  change branchAffine C s j w ∈ (branchParametrization C s j).target
  rw [branchParametrization_target]
  exact mem_range_self w

/-- The inverse branch chart has precisely the original affine coordinate. -/
@[simp] theorem branchChart_coordinates :
    (branchParametrization C s j).symm (branchAffine C s j w) = w :=
  (branchParametrization C s j).left_inv (by simp)

/-- The actual categorical holomorphic stalk at a branch point, in
the genuine centered branch coordinates. -/
def branchStalkEquiv :
    (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E₂) (rayDivisor 0)).stalk
        (branchAffine C s j w) ≃+* Germs.BranchGerm :=
  SheafManifoldStalk.centeredChartEquiv (branchParametrization C s j).symm
    (branchChart_mem_maximalAtlas C s j) (branchAffine C s j w)
    (branchChart_source C s j w)

/-- A literal section representative in centered actual branch coordinates. -/
def branchSectionRepresentative (U : Opens (rayDivisor 0))
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E₂) (rayDivisor 0) U) : E₂ → ℂ :=
  fun z => HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E₂) U f
    (branchAffine C s j (w + z))

theorem centeredRepresentative_branch (U : Opens (rayDivisor 0))
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E₂) (rayDivisor 0) U) :
    SheafManifoldStalk.centeredRepresentative (branchParametrization C s j).symm
        (branchAffine C s j w) U f = branchSectionRepresentative C s j w U f := by
  funext z
  change HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E₂) U f
      (branchAffine C s j ((branchParametrization C s j).symm (branchAffine C s j w) + z)) =
    HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E₂) U f (branchAffine C s j (w + z))
  rw [branchChart_coordinates]

theorem branchSectionRepresentative_analyticAt (U : Opens (rayDivisor 0))
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E₂) (rayDivisor 0) U)
    (hwU : branchAffine C s j w ∈ U) :
    AnalyticAt ℂ (branchSectionRepresentative C s j w U f) (0 : E₂) := by
  have h := SheafManifoldStalk.centeredRepresentative_analyticAt
    (branchParametrization C s j).symm (branchChart_mem_maximalAtlas C s j)
    (branchAffine C s j w) (branchChart_source C s j w) U f hwU
  rw [centeredRepresentative_branch] at h
  exact h

@[simp] theorem branchSectionRepresentative_zero (U : Opens (rayDivisor 0))
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E₂) (rayDivisor 0) U)
    (hwU : branchAffine C s j w ∈ U) :
    branchSectionRepresentative C s j w U f 0 = f ⟨branchAffine C s j w, hwU⟩ := by
  change HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E₂) U f
    (branchAffine C s j (w + 0)) = _
  rw [add_zero, HolomorphicFunctionSheaf.extendManifoldSection_apply]

/-- The comparison computes on literal categorical section germs by
the actual translated affine branch parametrization. -/
@[simp] theorem branchStalkEquiv_germ (U : Opens (rayDivisor 0))
    (hwU : branchAffine C s j w ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E₂) (rayDivisor 0) U) :
    branchStalkEquiv C s j w
        ((HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E₂) (rayDivisor 0)).germ U
          (branchAffine C s j w) hwU f) =
      Germs.ofAnalytic (branchSectionRepresentative C s j w U f)
        (branchSectionRepresentative_analyticAt C s j w U f hwU) := by
  have h := SheafManifoldStalk.centeredChartEquiv_germ
    (branchParametrization C s j).symm (branchChart_mem_maximalAtlas C s j)
    (branchAffine C s j w) (branchChart_source C s j w) U hwU f
  refine h.trans ((Germs.ofAnalytic_eq_iff _ _ _ _).mpr ?_)
  exact Eventually.of_forall fun z => congrFun (centeredRepresentative_branch C s j w U f) z

/-- The actual stalk comparison preserves evaluation at its base point. -/
@[simp] theorem eval_branchStalkEquiv
    (φ : (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E₂) (rayDivisor 0)).stalk
      (branchAffine C s j w)) :
    Germs.eval (0 : E₂) (branchStalkEquiv C s j w φ) =
      HolomorphicFunctionSheaf.stalkEval 𝓘(ℂ, E₂) (rayDivisor 0) (branchAffine C s j w) φ :=
  SheafManifoldStalk.eval_centeredChartEquiv (branchParametrization C s j).symm
    (branchChart_mem_maximalAtlas C s j) (branchAffine C s j w)
    (branchChart_source C s j w) φ

@[simp] theorem eval_branchStalkEquiv_germ (U : Opens (rayDivisor 0))
    (hwU : branchAffine C s j w ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E₂) (rayDivisor 0) U) :
    Germs.eval (0 : E₂) (branchStalkEquiv C s j w
        ((HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E₂) (rayDivisor 0)).germ U
          (branchAffine C s j w) hwU f)) = f ⟨branchAffine C s j w, hwU⟩ := by
  rw [branchStalkEquiv_germ, Germs.eval_ofAnalytic, branchSectionRepresentative_zero]

end Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk
