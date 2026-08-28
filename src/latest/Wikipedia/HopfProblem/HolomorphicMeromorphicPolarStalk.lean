import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarPlane
import Wikipedia.HopfProblem.HolomorphicMeromorphicGerms
import Wikipedia.HopfProblem.PeriodTori

/-!
# Polar denominator ideals in original complex-surface stalks

The original categorical holomorphic stalk is compared to the actual
two-variable analytic-germ ring through its genuine manifold chart and an
actual affine complex coordinate change. Denominator principality is
therefore proved for every genuine meromorphic germ of a complex surface,
and in particular for every actual period torus.

This concerns the full fraction field of the original holomorphic stalk.
There is no restriction to meromorphic functions supplied as bundle ratios.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
open Wikipedia.HopfProblem.CuspNormalization.Germs

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarStalk

open PolarAlgebra

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- Actual centered complex surface coordinates on the original
categorical holomorphic local ring. -/
def surfaceStalkEquiv (e : (ℂ × ℂ) ≃L[ℂ] E) (x : M) :
    HolomorphicStalk I M x ≃+* CoordinateDivision.O₂ :=
  (HolomorphicFunctionSheaf.chartStalkEquiv I x).trans
    (Coordinates.affinePullbackEquiv e 0 (extChartAt I x x))

@[simp] theorem surfaceStalkEquiv_eval (e : (ℂ × ℂ) ≃L[ℂ] E)
    (x : M) (s : HolomorphicStalk I M x) :
    eval (0 : ℂ × ℂ) (surfaceStalkEquiv I M e x s) =
      HolomorphicFunctionSheaf.stalkEval I M x s := by
  simp only [surfaceStalkEquiv, RingEquiv.trans_apply,
    Coordinates.eval_affinePullbackEquiv, HolomorphicFunctionSheaf.eval_chartStalkEquiv]

/-- The actual polar denominator ideal of every genuine meromorphic
surface germ is principal. -/
theorem denominatorIdeal_isPrincipal (e : (ℂ × ℂ) ≃L[ℂ] E)
    (x : M) (s : Germ I M x) :
    (denominatorIdeal (HolomorphicStalk I M x) s).IsPrincipal :=
  PolarPlane.denominatorIdeal_isPrincipal_of_equiv (surfaceStalkEquiv I M e x) s

/-- A genuine local numerator and a nonzero generator of the entire polar
denominator ideal. This is obtained for every fraction-stalk element. -/
theorem exists_denominator_generator (e : (ℂ × ℂ) ≃L[ℂ] E)
    (x : M) (s : Germ I M x) :
    ∃ p q : HolomorphicStalk I M x, q ≠ 0 ∧
      s = ofHolomorphicGerm I M x p / ofHolomorphicGerm I M x q ∧
      denominatorIdeal (HolomorphicStalk I M x) s = Ideal.span ({q} : Set _) := by
  obtain ⟨q, hq⟩ := denominatorIdeal_isPrincipal I M e x s
  have hq0 : q ≠ 0 := by
    intro hz
    apply PolarAlgebra.denominatorIdeal_ne_bot (HolomorphicStalk I M x) s
    simpa [hz] using hq
  have hqmem : q ∈ denominatorIdeal (HolomorphicStalk I M x) s := by
    rw [hq]
    exact Ideal.subset_span (Set.mem_singleton q)
  obtain ⟨p, hp⟩ := hqmem
  have hqK : ofHolomorphicGerm I M x q ≠ 0 := by
    simpa only [ne_eq, ofHolomorphicGerm_eq_zero_iff] using hq0
  refine ⟨p, q, hq0, ?_, hq⟩
  apply (eq_div_iff hqK).mpr
  exact (mul_comm _ _).trans hp

/-- Membership in the full polar denominator ideal is literal divisibility
by the constructed generator. -/
theorem exists_denominator_divisibility (e : (ℂ × ℂ) ≃L[ℂ] E)
    (x : M) (s : Germ I M x) :
    ∃ q : HolomorphicStalk I M x, q ≠ 0 ∧
      ∀ h : HolomorphicStalk I M x,
        (∃ p : HolomorphicStalk I M x,
          ofHolomorphicGerm I M x h * s = ofHolomorphicGerm I M x p) ↔ q ∣ h := by
  obtain ⟨p, q, hq0, hs, hq⟩ := exists_denominator_generator I M e x s
  refine ⟨q, hq0, fun h => ?_⟩
  change h ∈ denominatorIdeal (HolomorphicStalk I M x) s ↔ q ∣ h
  rw [hq, Ideal.mem_span_singleton]

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarStalk

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarStalk

/-- Unconditional denominator principality for the full genuine
meromorphic stalk of every actual period torus. -/
theorem periodTorus_denominatorIdeal_isPrincipal (p : PeriodDomain) (x : p.Torus)
    (s : Germ 𝓘(ℂ, ComplexPlane₂) p.Torus x) :
    (PolarAlgebra.denominatorIdeal
      (HolomorphicStalk 𝓘(ℂ, ComplexPlane₂) p.Torus x) s).IsPrincipal :=
  denominatorIdeal_isPrincipal 𝓘(ℂ, ComplexPlane₂) p.Torus
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm x s

/-- Actual reduced local numerator/denominator data on every period torus. -/
theorem periodTorus_exists_denominator_generator (p : PeriodDomain) (x : p.Torus)
    (s : Germ 𝓘(ℂ, ComplexPlane₂) p.Torus x) :
    ∃ a b : HolomorphicStalk 𝓘(ℂ, ComplexPlane₂) p.Torus x, b ≠ 0 ∧
      s = ofHolomorphicGerm 𝓘(ℂ, ComplexPlane₂) p.Torus x a /
        ofHolomorphicGerm 𝓘(ℂ, ComplexPlane₂) p.Torus x b ∧
      PolarAlgebra.denominatorIdeal
        (HolomorphicStalk 𝓘(ℂ, ComplexPlane₂) p.Torus x) s = Ideal.span ({b} : Set _) :=
  exists_denominator_generator 𝓘(ℂ, ComplexPlane₂) p.Torus
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm x s

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarStalk
