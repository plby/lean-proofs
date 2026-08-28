import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyGlobalFourierBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultPairs

/-!
# Native global coefficient pairs and their literal Haar means
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier

open FourierLinear

/-- Apply the actual scalar comparison to the two native form coefficients. -/
def pairSectionEquiv (p : PeriodDomain) :
    Dolbeault.PairSection p ⊤ ≃ₗ[ℂ] Pair :=
  (LinearEquiv.prodCongr (sectionEquiv p) (sectionEquiv p)).trans
    (LinearEquiv.finTwoArrow ℂ Smooth).symm

@[simp] theorem pairSectionEquiv_apply (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤) :
    pairSectionEquiv p s = ![sectionEquiv p s.1, sectionEquiv p s.2] := rfl

@[simp] theorem pairSectionEquiv_symm_apply (p : PeriodDomain) (a : Pair) :
    (pairSectionEquiv p).symm a =
      ((sectionEquiv p).symm (a 0), (sectionEquiv p).symm (a 1)) := rfl

/-- The genuine constant pair of native smooth sections. -/
def constantPairSection (p : PeriodDomain) (c : Fin 2 → ℂ) : Dolbeault.PairSection p ⊤ :=
  (ContMDiffMap.const (c 0), ContMDiffMap.const (c 1))

@[simp] theorem pairSectionEquiv_constant (p : PeriodDomain) (c : Fin 2 → ℂ) :
    pairSectionEquiv p (constantPairSection p c) = constantPair c := by
  funext i
  fin_cases i
  · exact sectionEquiv_constant p (c 0)
  · exact sectionEquiv_constant p (c 1)

/-- The two original coefficient Haar means, as a map on actual native global forms. -/
def pairMean (p : PeriodDomain) : Dolbeault.PairSection p ⊤ →ₗ[ℂ] (Fin 2 → ℂ) :=
  FourierLinear.pairMean.comp (pairSectionEquiv p).toLinearMap

@[simp] theorem pairMean_apply_zero (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤) :
    pairMean p s 0 = mean p s.1 := rfl

@[simp] theorem pairMean_apply_one (p : PeriodDomain) (s : Dolbeault.PairSection p ⊤) :
    pairMean p s 1 = mean p s.2 := rfl

@[simp] theorem pairMean_constant (p : PeriodDomain) (c : Fin 2 → ℂ) :
    pairMean p (constantPairSection p c) = c := by
  change FourierLinear.pairMean (pairSectionEquiv p (constantPairSection p c)) = c
  rw [pairSectionEquiv_constant, pairMean_constantPair]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier
