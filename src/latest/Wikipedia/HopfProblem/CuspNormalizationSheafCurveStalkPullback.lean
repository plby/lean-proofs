import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkPullbackGerms
import Wikipedia.HopfProblem.CuspNormalizationSheafNormalizationStalk

/-!
# The actual second normalization arrow in analytic-germ coordinates

The actual positive and negative double-curve pullbacks induce the
corresponding coordinate-axis restrictions on genuine stalks. Subtracting
them gives the actual signed boundary map of the sheaf resolution.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

open CuspQuotient ToricCharts ToricSpace ToricComponent ToricFan
  NormalizationCurves NormalizationLocalCoordinates SheafResolution SheafNormalizationStalk
  SheafGermComplex

local notation "I₂" => 𝓘(ℂ, CoordinateSpace 2)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

variable (a : Tube (disc ε)) (s : Triangle) (b : CoordinateSpace 3)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The actual positive double-curve stalk map is the actual positive
coordinate-axis restriction under the genuine stalk comparisons. -/
theorem plusStalkMap_conjugacy (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) (k : Fin 3)
    (hk : sourcePair s k ⊆ Germs.activeBranches b)
    (φ : (normalizationSheaf C ε hε).presheaf.stalk x) :
    curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk
        (plusStalkMap C ε hε hε1 hC hR k x φ) =
      axisRestriction (plusAxisIndex s k)
        (normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb φ
          (chartPlusIndex s b k hk)) := by
  obtain ⟨U, hxU, f, rfl⟩ := (normalizationSheaf C ε hε).presheaf.exists_germ_eq φ
  change HolomorphicFunctionSheaf.Section I₂ (rayDivisor 0)
    ((Opens.map (normalizationMap C ε hε)).obj U) at f
  exact plusStalkMap_conjugacy_germ C ε hε hε1 hC hR a s b hb x hxb k hk U hxU f

/-- The actual negative double-curve stalk map is the actual negative
coordinate-axis restriction under the genuine stalk comparisons. -/
theorem minusStalkMap_conjugacy (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) (k : Fin 3)
    (hk : sourcePair s k ⊆ Germs.activeBranches b)
    (φ : (normalizationSheaf C ε hε).presheaf.stalk x) :
    curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk
        (minusStalkMap C ε hε hε1 hC hR k x φ) =
      axisRestriction (minusAxisIndex s k)
        (normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb φ
          (chartMinusIndex s b k hk)) := by
  obtain ⟨U, hxU, f, rfl⟩ := (normalizationSheaf C ε hε).presheaf.exists_germ_eq φ
  change HolomorphicFunctionSheaf.Section I₂ (rayDivisor 0)
    ((Opens.map (normalizationMap C ε hε)).obj U) at f
  exact minusStalkMap_conjugacy_germ C ε hε hε1 hC hR a s b hb x hxb k hk U hxU f

/-- The actual signed second arrow is the difference of the actual
coordinate-axis restrictions in the source's own branch ordering. -/
theorem boundaryStalkMap_conjugacy (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) (k : Fin 3)
    (hk : sourcePair s k ⊆ Germs.activeBranches b)
    (φ : (normalizationSheaf C ε hε).presheaf.stalk x) :
    curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk
        (boundaryStalkMap C ε hε hε1 hC hR k x φ) =
      axisRestriction (plusAxisIndex s k)
          (normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb φ
            (chartPlusIndex s b k hk)) -
        axisRestriction (minusAxisIndex s k)
          (normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb φ
            (chartMinusIndex s b k hk)) := by
  rw [boundaryStalkMap_eq, AddMonoidHom.sub_apply, map_sub,
    plusStalkMap_conjugacy, minusStalkMap_conjugacy]

omit b in
/-- The same actual second-arrow diagram at the chart coordinate of `x`. -/
theorem boundaryStalkMap_conjugacyAt (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source) (k : Fin 3)
    (hk : sourcePair s k ⊆ Germs.activeBranches ((e) x.val))
    (φ : (normalizationSheaf C ε hε).presheaf.stalk x) :
    curveStalkEquivAt C ε hε hε1 hC hR a s x hx k hk
        (boundaryStalkMap C ε hε hε1 hC hR k x φ) =
      axisRestriction (plusAxisIndex s k)
          (normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx φ
            (chartPlusIndex s ((e) x.val) k hk)) -
        axisRestriction (minusAxisIndex s k)
          (normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx φ
            (chartMinusIndex s ((e) x.val) k hk)) :=
  boundaryStalkMap_conjugacy C ε hε hε1 hC hR a s ((e) x.val) ((e).map_source hx)
    x ((e).left_inv hx).symm k hk φ

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
