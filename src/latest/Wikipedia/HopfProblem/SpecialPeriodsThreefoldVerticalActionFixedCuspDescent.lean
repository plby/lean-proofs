import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCusp

/-!
# Fixed points descend through the original cusp covering

For every actual tube representative, being fixed by all times is
equivalent to the same condition on its image in the genuine cusp
quotient.  The nontrivial implication uses the continuous orbit curve
and the discrete fibres of the original quotient covering.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCusp

open ToricCharts ToricSpace

/-- A fixed-point orbit in an original cusp tube is continuous in the
complex time, for the original subspace topology. -/
theorem tubeFlow_curve_continuous (D : TopologicalSpace.Opens ℂ) (x : Tube D) :
    Continuous (fun s : ℂ => Cusp.tubeFlow D s x) := by
  have h : Continuous (fun p : ℂ × ToricSpace.Space => Cusp.toricFlow p.1 p.2) :=
    Cusp.toricFlow_joint_holomorphic.continuous
  have hx : Continuous (fun s : ℂ => Cusp.toricFlow s (x : ToricSpace.Space)) :=
    h.comp (f := fun s : ℂ => (s, (x : ToricSpace.Space)))
      (continuous_id.prodMk continuous_const)
  exact hx.subtype_mk _

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
  (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε hε1 hC hR

/-- A fixed quotient point has every actual tube representative fixed;
the converse follows from the literal quotient-flow formula. -/
theorem flow_quotientMap_fixed_iff (x : Tube (CuspQuotient.disc ε)) :
    (∀ s : ℂ, Cusp.flow C ε s (CuspQuotient.quotientMap C ε x) =
      CuspQuotient.quotientMap C ε x) ↔
      ∀ s : ℂ, Cusp.tubeFlow (CuspQuotient.disc ε) s x = x := by
  constructor
  · intro hx
    have hq : IsLocalHomeomorph (CuspQuotient.quotientMap C ε) := by
      let := tubeAction C (CuspQuotient.disc ε)
      exact (CuspQuotient.quotientMap_covering C ε hε hε1 hC hR).isCoveringMap.isLocalHomeomorph
    exact FixedDescent.eq_const_of_isLocalHomeomorph hq
      (tubeFlow_curve_continuous (CuspQuotient.disc ε) x)
      (Cusp.tubeFlow_zero (CuspQuotient.disc ε) x)
      (fun s => (Cusp.flow_quotientMap C ε s x).symm.trans (hx s))
  · intro hx s
    rw [Cusp.flow_quotientMap, hx s]

/-- The same fixed-lift criterion, with the original toric representative
instead of its open-tube subtype. -/
theorem flow_quotientMap_toric_fixed_iff (x : Tube (CuspQuotient.disc ε)) :
    (∀ s : ℂ, Cusp.flow C ε s (CuspQuotient.quotientMap C ε x) =
      CuspQuotient.quotientMap C ε x) ↔
      ∀ s : ℂ, Cusp.toricFlow s (x : ToricSpace.Space) = (x : ToricSpace.Space) := by
  rw [flow_quotientMap_fixed_iff C ε hε hε1 hC hR x]
  constructor
  · intro hx s
    exact congrArg Subtype.val (hx s)
  · intro hx s
    exact Subtype.ext (hx s)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCusp
