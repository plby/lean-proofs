/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CountableExtension
import ErdosProblems.Erdos599.RegularExtension
import ErdosProblems.Erdos599.SingularExactFrontierMatrix

/-!
# Extension induction step with exact-frontier lower hypotheses

Regular and countable branches use the ordinary projection of the lower
induction hypothesis.  The singular branch retains the exact frontiers and
uses the literal quotient row machine from Assertion 9.17.
-/

noncomputable section

open Cardinal

namespace Erdos599
namespace CardinalInduction

open SingularExactFrontierMatrix

universe u

variable {V : Type u}

/-- Aharoni--Berger's singular extension step in its source-faithful public
form. -/
theorem singularExtensionClauseAt
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered) :
    ExtensionClauseAt Gamma kappa :=
  singularExtensionClauseAt_of_exactFrontierInductionBelow
    kappa hkappa hsingular hlower Gamma hGamma

/-- Exact-frontier assembly with the still-independent regular-cardinal
extension construction exposed as a single branch theorem.  This lemma is
the case split used by the final dispatcher: the countable branch is
unconditional, the singular branch consumes the retained exact frontiers,
and only the regular branch is delegated to its Section 8/9 construction.

Keeping this seam explicit prevents an unfinished regular provider from
being smuggled into the exact-frontier induction while allowing the singular
matrix to be integrated and checked independently. -/
theorem extensionClauseStepExact_of_regularStep
    (regularStep : ∀ rho : Cardinal.{u},
      UniversalCardinalInductionBelow V rho → rho.IsRegular →
      aleph0 < rho → UniversalExtensionClauseAt V rho)
    (kappa : Cardinal.{u})
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa) :
    UniversalExtensionClauseAt V kappa := by
  let hlowerOrdinary : UniversalCardinalInductionBelow V kappa :=
    hlower.toUniversalCardinalInductionBelow
  intro Gamma hGamma
  cases extensionCardinalCase kappa with
  | zero hkappa =>
      subst kappa
      exact extensionClauseAt_zero Gamma
  | countable _ hkappa =>
      exact extensionClauseAt_countable Gamma hGamma hkappa
  | uncountableRegular hkappa hregular =>
      exact regularStep kappa hlowerOrdinary hregular hkappa Gamma hGamma
  | uncountableSingular hkappa hsingular =>
      exact singularExtensionClauseAt
        kappa hkappa hsingular hlower Gamma hGamma

/-- Variant of the exact-frontier dispatcher which retains the stronger
lower hypothesis in the regular branch as well.  The exact half-way
frontier is used by the regular source-9.15 construction to obtain a
terminal-clean stop-over; the countable and singular branches are
unchanged. -/
theorem extensionClauseStepExact_of_exactRegularStep
    (regularStep : ∀ rho : Cardinal.{u},
      UniversalExactFrontierCardinalInductionBelow V rho → rho.IsRegular →
      aleph0 < rho → UniversalExtensionClauseAt V rho)
    (kappa : Cardinal.{u})
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa) :
    UniversalExtensionClauseAt V kappa := by
  intro Gamma hGamma
  cases extensionCardinalCase kappa with
  | zero hkappa =>
      subst kappa
      exact extensionClauseAt_zero Gamma
  | countable _ hkappa =>
      exact extensionClauseAt_countable Gamma hGamma hkappa
  | uncountableRegular hkappa hregular =>
      exact regularStep kappa hlower hregular hkappa Gamma hGamma
  | uncountableSingular hkappa hsingular =>
      exact singularExtensionClauseAt
        kappa hkappa hsingular hlower Gamma hGamma

#print axioms singularExtensionClauseAt
#print axioms extensionClauseStepExact_of_regularStep
#print axioms extensionClauseStepExact_of_exactRegularStep

end CardinalInduction
end Erdos599
