import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkPullbackMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalkPullbackRepresentatives

/-!
# Signed curve pullbacks on actual section germs

The actual stalk maps are computed on literal section germs, using the
proved actual chart representatives and their coordinate-axis identities.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

open CuspQuotient ToricCharts ToricSpace ToricFan NormalizationCurves
  NormalizationLocalCoordinates SheafResolution SheafNormalizationStalk SheafGermComplex

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : CoordinateSpace 3)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- On every actual section germ the positive pullback becomes the
positive coordinate-axis restriction. -/
theorem plusStalkMap_conjugacy_germ (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) (k : Fin 3)
    (hk : sourcePair s k ⊆ Germs.activeBranches b)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) :
    curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk
        (plusStalkMap C ε hε hε1 hC hR k x
          ((normalizationSheaf C ε hε).presheaf.germ U x hxU f)) =
      axisRestriction (plusAxisIndex s k)
        (normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb
          ((normalizationSheaf C ε hε).presheaf.germ U x hxU f)
          (chartPlusIndex s b k hk)) := by
  let g : CurveSection C ε hε hε1 hC hR k
      ((Opens.map (sourceCurveMap C ε hε k)).obj U) :=
    (plusPullback C ε hε hε1 hC hR k).hom.app (op U) f
  have hcurve := curveStalkEquiv_germ C ε hε hε1 hC hR a s b hb x hxb k hk U hxU g
  have hnorm := normalizationStalkEquiv_germ C ε hε hε1 hC hR a s b hb x hxb U hxU f
    (chartPlusIndex s b k hk)
  refine ((congrArg (curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk)
    (plusStalkMap_germ C ε hε hε1 hC hR k x U hxU f)).trans hcurve).trans ?_
  refine Eq.trans ?_ (congrArg (axisRestriction (plusAxisIndex s k)) hnorm.symm)
  rw [axisRestriction_ofAnalytic]
  apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall
    (congrFun (axisRepresentative_plusPullback C ε hε hε1 hC hR s b k hk U f))

/-- On every actual section germ the negative pullback becomes the
negative coordinate-axis restriction. -/
theorem minusStalkMap_conjugacy_germ (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) (k : Fin 3)
    (hk : sourcePair s k ⊆ Germs.activeBranches b)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) :
    curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk
        (minusStalkMap C ε hε hε1 hC hR k x
          ((normalizationSheaf C ε hε).presheaf.germ U x hxU f)) =
      axisRestriction (minusAxisIndex s k)
        (normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb
          ((normalizationSheaf C ε hε).presheaf.germ U x hxU f)
          (chartMinusIndex s b k hk)) := by
  let g : CurveSection C ε hε hε1 hC hR k
      ((Opens.map (sourceCurveMap C ε hε k)).obj U) :=
    (minusPullback C ε hε hε1 hC hR k).hom.app (op U) f
  have hcurve := curveStalkEquiv_germ C ε hε hε1 hC hR a s b hb x hxb k hk U hxU g
  have hnorm := normalizationStalkEquiv_germ C ε hε hε1 hC hR a s b hb x hxb U hxU f
    (chartMinusIndex s b k hk)
  refine ((congrArg (curveStalkEquiv C ε hε hε1 hC hR a s b hb x hxb k hk)
    (minusStalkMap_germ C ε hε hε1 hC hR k x U hxU f)).trans hcurve).trans ?_
  refine Eq.trans ?_ (congrArg (axisRestriction (minusAxisIndex s k)) hnorm.symm)
  rw [axisRestriction_ofAnalytic]
  apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall
    (congrFun (axisRepresentative_minusPullback C ε hε hε1 hC hR s b k hk U f))

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
