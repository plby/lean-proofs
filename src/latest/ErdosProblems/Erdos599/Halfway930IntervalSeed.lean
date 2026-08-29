/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930ContactRequest
import ErdosProblems.Erdos599.HalfwayOldStageIntervalSeed

/-!
# The joint Assertion 9.30 / Assertion 9.31 closure seed

The interval seed must retain two independent bounded pieces: the complete
carrier of the safe hammock member selected by 9.30, and the complete
selected-reference components touching the exceptional old-stage intervals
changed by 9.31.  Starting only from `continuation930ContactSeed` loses the
first piece in both nontrivial 9.30 branches.

This file forms the literal joint union and proves the cardinal, containment,
and roof invariants consumed by the common closing transaction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace Contact930Request

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u z : V}

/-- Endpoint eligibility needed to put the selected hammock inside the
later roof.  The identity branch has no selected hammock. -/
def IsClubEligible (R : Contact930Request C W u) : Prop :=
  match R with
  | .identity .. => True
  | .terminalOutside .. =>
      HammockEligible C.before C.innerRoof C.outerRoof u .infinity
  | .imaginarySuccessor v .. =>
      HammockEligible C.before C.innerRoof C.outerRoof u (.vertex v)

/-- Eligibility and the public hammock-roof theorem put every branch seed
inside the selected later roof. -/
theorem seed_subset_outerRoof
    (R : Contact930Request C W u)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (heligible : R.IsClubEligible) :
    R.seed ⊆ C.outerRoof := by
  cases R with
  | identity =>
      exact continuation930ContactSeed.subset_outerRoof C W hW hbefore href
  | terminalOutside whole_terminal outside_slice Q hsafe hstart hinfinite havoid =>
      apply continuation930ContactSeed.selected_subset_outerRoof
        C W Q hW hbefore href
      exact hSafeRoof Q hsafe
  | imaginarySuccessor v hedge himaginary Q hsafe hstart hend havoid =>
      apply continuation930ContactSeed.selected_subset_outerRoof
        C W Q hW hbefore href
      exact hSafeRoof Q hsafe

/-- The complete joint seed of the selected 9.30 branch and the exceptional
old-stage interval exchange. -/
def intervalSeed
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z) : Set V :=
  T.augmentedIntervalSeed R.seed

/-- The joint seed is still `kappa`-small. -/
theorem intervalSeed_mk_le
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent) :
    #(R.intervalSeed T) ≤ kappa := by
  apply T.mk_augmentedIntervalSeed_le
  exact R.seed_mk_le hW

/-- The entire branch-specific 9.30 seed survives literally. -/
theorem seed_subset_intervalSeed
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z) :
    R.seed ⊆ R.intervalSeed T :=
  T.baseSeed_subset_augmentedIntervalSeed R.seed

/-- Every exceptional interval component is explicitly present in the joint
seed, rather than represented only through the reference components which
touch it. -/
theorem exceptionalComponents_subset_intervalSeed
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z) :
    T.exceptionalComponents ⊆ R.intervalSeed T :=
  T.exceptionalComponents_subset_augmentedIntervalSeed R.seed

/-- Consequently the selected local first-hit front is literally carried by
the common closure seed. -/
theorem front_support_subset_intervalSeed
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z) :
    T.front.support ⊆ R.intervalSeed T :=
  T.front_support_subset_exceptional.trans
    (R.exceptionalComponents_subset_intervalSeed T)

/-- The independently defined old-stage interval seed is contained in the
joint request seed. -/
theorem contactIntervalSeed_subset
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z) :
    T.contactIntervalSeed W ⊆ R.intervalSeed T := by
  apply Set.union_subset
  · exact R.contactSeed_subset.trans Set.subset_union_left
  · exact Set.subset_union_right

/-- Every selected-reference component touching the exceptional old-stage
exchange is swallowed in full by the joint seed. -/
theorem exceptionalReference_support_subset
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z)
    {p : Gamma.DPath} (hp : p ∈ C.selectedReference)
    (hcontact : (p.support ∩ T.exceptionalComponents).Nonempty) :
    p.support ⊆ R.intervalSeed T :=
  (T.reference_support_subset_contactIntervalSeed W hp hcontact).trans
    (R.contactIntervalSeed_subset T)

/-- The joint request/interval seed is roofed under the exact public club
eligibility hypotheses. -/
theorem intervalSeed_subset_outerRoof
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (heligible : R.IsClubEligible) :
    R.intervalSeed T ⊆ C.outerRoof :=
  T.augmentedIntervalSeed_subset_outerRoof
    (R.seed_subset_outerRoof hW hbefore href hSafeRoof heligible)
    href

end Contact930Request

/-- With the endpoint-location invariant retained by the club scheduler, the
unconditional 9.30 choice can be made together with its exact closure
eligibility certificate. -/
theorem exists_clubEligibleContact930Request
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hpersistent : C.persistent ⊆ C.newSlice)
    (hu : u ∈ W.realPart.terminals)
    (huLocation : u ∈ C.before ∩ C.innerRoof)
    (himaginaryLocation : ∀ v,
      IsImaginaryEdge Gamma C.selectedReference kappa u v →
        v ∈ C.before ∩ C.outerRoof) :
    ∃ R : Contact930Request C W u, R.IsClubEligible := by
  rcases real_terminal_is_terminal_or_has_imaginary_edge_mem hu with
      huterminal | ⟨v, huv, himaginary⟩
  · by_cases huSlice : u ∈ C.newSlice
    · exact ⟨Contact930Request.identity huterminal huSlice, trivial⟩
    · obtain ⟨Q, hsafe, hstart, hinfinite, havoid⟩ :=
        continuation930ContactSeed.exists_terminalOutside_member_avoiding_reserved
          C W hW hpersistent huterminal huSlice
      exact ⟨Contact930Request.terminalOutside huterminal huSlice Q
        hsafe hstart hinfinite havoid, ⟨huLocation, trivial⟩⟩
  · obtain ⟨Q, hsafe, hstart, hend, havoid⟩ :=
      continuation930ContactSeed.exists_imaginarySuccessor_member_avoiding_reserved
        C W hW himaginary
    exact ⟨Contact930Request.imaginarySuccessor v huv himaginary Q
      hsafe hstart hend havoid, ⟨huLocation,
        himaginaryLocation v himaginary⟩⟩

end LinkageBlueprint
end Blueprint
end Erdos599
