import Wikipedia.HopfProblem.CuspNormalizationSheafCuspTerms
import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalk
import Wikipedia.HopfProblem.CuspNormalizationGermsChartFibre

/-!
# Actual normalization fibres and actual pushforward stalks

The finite-fibre comparison applies to the actual closed normalization
map into the central-fibre subspace. The coordinate labels enumerate
its actual fibre by the already proved local normalization diagram.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk

open CuspQuotient ToricCharts ToricSpace ToricComponent ToricFan SheafResolution

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual additive normalization pushforward stalk is the product
of the actual ring-valued holomorphic stalks over its finite fibre. -/
def finiteStalkEquiv (x : CentralSpace C ε) :
    (normalizationSheaf C ε hε).presheaf.stalk x ≃+
      ∀ y : normalizationMap C ε hε ⁻¹' {x},
        (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)).stalk
          y.val :=
  SheafForgetStalk.pushforwardStalkAddEquiv (normalizationMap C ε hε)
    (normalization_isClosedMap C ε hε)
    (HolomorphicFunctionSheaf.sheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)) x
    (normalization_fibre_finite C ε hε hε1 hC hR x)

/-- On a literal pushforward section germ, each factor is its actual
ring-valued section germ at the corresponding point of the fibre. -/
@[simp] theorem finiteStalkEquiv_germ (x : CentralSpace C ε)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U))
    (y : normalizationMap C ε hε ⁻¹' {x}) :
    finiteStalkEquiv C ε hε hε1 hC hR x
        ((normalizationSheaf C ε hε).presheaf.germ U x hxU f) y =
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)).germ
        ((Opens.map (normalizationMap C ε hε)).obj U) y.val
        (SheafFiniteStalk.fiber_mem_preimage (normalizationMap C ε hε) x y U hxU) f :=
  SheafForgetStalk.pushforwardStalkAddEquiv_germ (normalizationMap C ε hε)
    (normalization_isClosedMap C ε hε)
    (HolomorphicFunctionSheaf.sheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)) x
    (normalization_fibre_finite C ε hε hε1 hC hR x) U hxU f y

variable (a : Tube (disc ε)) (s : Triangle) (b : CoordinateSpace 3)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The coordinate labels enumerate the actual fibre of the
normalization with central-subspace codomain. This equivalence changes
only the proof of the fibre condition, not the source point. -/
def actualFibreEquiv (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) :
    Germs.activeBranches b ≃ (normalizationMap C ε hε ⁻¹' {x}) :=
  (Germs.activeFibreEquiv C ε hε hε1 hC hR a s b hb).trans
    (Equiv.subtypeEquivRight fun y => by
      change componentProjection C ε hε y = (e).symm b ↔ normalizationMap C ε hε y = x
      constructor
      · intro hy
        exact Subtype.ext (hy.trans hxb.symm)
      · intro hy
        exact (congrArg Subtype.val hy).trans hxb)

@[simp] theorem actualFibreEquiv_val (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) (j : Germs.activeBranches b) :
    (actualFibreEquiv C ε hε hε1 hC hR a s b hb x hxb j).val =
      branchAffine C s j (removeCoordinate j b) := rfl

/-- Each actual branch centre lies in every inverse image neighbourhood
of the chosen central point. -/
theorem branch_mem_preimage (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U) (j : Germs.activeBranches b) :
    branchAffine C s j (removeCoordinate j b) ∈
      (Opens.map (normalizationMap C ε hε)).obj U :=
  SheafFiniteStalk.fiber_mem_preimage (normalizationMap C ε hε) x
    (actualFibreEquiv C ε hε hε1 hC hR a s b hb x hxb j) U hxU

end Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk
