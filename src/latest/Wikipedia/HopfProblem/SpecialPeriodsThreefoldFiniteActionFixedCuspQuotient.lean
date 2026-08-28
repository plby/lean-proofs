import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedCuspBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedCuspDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCusp

/-!
# Finite-order fixed points descend through the actual cusp deck quotient

A quotient-fixed representative differs from its vertical translate by an
actual lattice deck transformation. Iteration, commutation with that deck
action, freeness, and torsion-freeness force the deck transformation to be
trivial. The existing toric fixed-locus calculation then identifies exactly
the native double curve of direction one.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Cusp

open ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
  (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε hε1 hC hR

/-- A finite-order quotient fixed point has every actual tube representative fixed.
This uses the torsion-free deck group, not connectedness of the time parameter. -/
theorem quotientAction_quotientMap_fixed_iff (u : ℂˣ) (hfin : IsOfFinOrder u)
    (x : Tube (CuspQuotient.disc ε)) :
    quotientAction C ε u (CuspQuotient.quotientMap C ε x) = CuspQuotient.quotientMap C ε x ↔
      tubeMap (CuspQuotient.disc ε) u x = x := by
  constructor
  · intro hx
    let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
    let := CuspQuotient.free_action C ε hε hε1 hC hR
    have horbit : tubeMap (CuspQuotient.disc ε) u x ∈
        MulAction.orbit CuspQuotient.LatticeGroup x := Quotient.exact hx
    obtain ⟨g, hg⟩ := horbit
    obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
    apply fixed_of_finite_iterate_of_deck (Γ := CuspQuotient.LatticeGroup)
      (tubeMap (CuspQuotient.disc ε) u)
      (fun g y => tubeMap_translate C (CuspQuotient.disc ε) u g.toAdd y) n hn x
    · rw [tubeMap_iterate, hpow, tubeMap_one]
    · exact ⟨g, hg.symm⟩
  · intro hx
    rw [quotientAction_quotientMap, hx]

/-- The same finite-order fixed-lift criterion in the original toric space. -/
theorem quotientAction_quotientMap_toric_fixed_iff (u : ℂˣ) (hfin : IsOfFinOrder u)
    (x : Tube (CuspQuotient.disc ε)) :
    quotientAction C ε u (CuspQuotient.quotientMap C ε x) = CuspQuotient.quotientMap C ε x ↔
      torusAction (fibreMultiplier ![1, u]) (x : ToricSpace.Space) = (x : ToricSpace.Space) := by
  rw [quotientAction_quotientMap_fixed_iff C ε hε hε1 hC hR u hfin x]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- A single nonidentity finite-order scalar fixes precisely the actual cusp double curve. -/
theorem quotientAction_fixed_iff_doubleCurve (u : ℂˣ) (hu : u ≠ 1) (hfin : IsOfFinOrder u)
    (x : CuspQuotient.QuotientSpace C ε) :
    quotientAction C ε u x = x ↔ x ∈ CuspQuotient.doubleCurve C ε hε 1 := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  exact (quotientAction_quotientMap_toric_fixed_iff C ε hε hε1 hC hR u hfin a).trans
    ((VerticalAction.FixedToric.torusAction_vertical_fixed_iff u hu a).trans
      (CuspQuotient.mem_doubleCurve_quotientMap C ε hε a 1).symm)

/-- Literal equality of the finite-order fixed set and the existing native double curve. -/
theorem quotientAction_fixed_set (u : ℂˣ) (hu : u ≠ 1) (hfin : IsOfFinOrder u) :
    {x : CuspQuotient.QuotientSpace C ε | quotientAction C ε u x = x} =
      CuspQuotient.doubleCurve C ε hε 1 := by
  ext x
  exact quotientAction_fixed_iff_doubleCurve C ε hε hε1 hC hR u hu hfin x

/-- The actual finite-order criterion agrees with the full additive fixed locus. -/
theorem quotientAction_fixed_iff_all_flow (u : ℂˣ) (hu : u ≠ 1) (hfin : IsOfFinOrder u)
    (x : CuspQuotient.QuotientSpace C ε) :
    quotientAction C ε u x = x ↔ ∀ s : ℂ, VerticalAction.Cusp.flow C ε s x = x :=
  (quotientAction_fixed_iff_doubleCurve C ε hε hε1 hC hR u hu hfin x).trans
    (VerticalAction.FixedCusp.flow_fixed_iff_doubleCurve C ε hε hε1 hC hR x).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Cusp
