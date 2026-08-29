/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLocalizedProtectedCleanSlice
import ErdosProblems.Erdos599.RegularRows
import ErdosProblems.Erdos599.SliceCandidateChoice

/-!
# Causal registration of a localized protected half-way output

The fair half-way construction may complete more sources than the current
request.  Its whole completed carrier must therefore be visible before a
later roof is chosen.  This file chooses, using only the current stage web
and request, the union of that carrier with one height witness for the
actual stopover.

There is no exact-frontier premise here.  The choice is total, with the
empty set used when the visible coordinate has no localized protected
geometry.  At a coordinate where the fair construction supplies one, the
chosen set recovers an actual geometry and has cardinality strictly below
the regular induction cardinal.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLocalizedProtectedRegistration

open Blueprint.LinkageBlueprint.CardinalInduction

universe u

variable {V : Type u}

/-- The large-source registration consists of one actual protected geometry,
one height witness for its stopover, and the whole completed target carrier.
The lower cardinal is existential because it is chosen by the fair
half-way construction, but its strict bound is part of the visible
certificate. -/
def IsProtectedRegistrationWitness
    (Q : DWeb V) (U : Set V) (kappa : Cardinal.{u}) (Z : Set V) : Prop :=
  ∃ rho : Cardinal.{u}, rho < kappa ∧
    ∃ A₀ : Set V, U ⊆ A₀ ∧
      ∃ D : LocalizedProtectedHalfwayGeometry Q A₀ rho,
        ∃ X : Set V,
          IsHeightWitness Q D.stopover X ∧ #X ≤ rho ∧
            Z = X ∪ Q.vertexSet D.targetPaths

/-- When the whole stage source is already small, lower extension supplies a
full target linkage.  Registering its entire carrier is the truthful finite
source alternative: no bounded-height half-way output is asserted. -/
def IsFullTargetRegistrationWitness
    (Q : DWeb V) (kappa : Cardinal.{u}) (Z : Set V) : Prop :=
  ∃ P : Set Q.DPath, #Q.source < kappa ∧
    IsLinkageBetween Q Q.source Q.target P ∧
      Z = Q.vertexSet P

/-- The exact visible registration dichotomy.  A coordinate stores either
the protected half-way carrier and height witness, or the carrier of a full
target linkage when the entire stage source is small. -/
def IsRegistrationWitness
    (Q : DWeb V) (U : Set V) (kappa : Cardinal.{u}) (Z : Set V) : Prop :=
  IsProtectedRegistrationWitness Q U kappa Z ∨
    IsFullTargetRegistrationWitness Q kappa Z

/-- All protected registrations determined by one visible web/request
coordinate. -/
def registrationSets
    (Q : DWeb V) (U : Set V) (kappa : Cardinal.{u}) : Set (Set V) :=
  {Z | IsRegistrationWitness Q U kappa Z}

/-- Total causal choice of a protected height-and-carrier registration. -/
noncomputable def registration
    (Q : DWeb V) (U : Set V) (kappa : Cardinal.{u}) : Set V :=
  SliceCandidate.chooseVertexSet (registrationSets Q U kappa)

/-- Ladder-facing form of the visible choice. -/
noncomputable def registrationAt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) : Set V :=
  registration (L.stageWeb delta) (request delta gamma) kappa

/-- An actual lower-cardinal protected output makes the visible family of
registrations nonempty. -/
theorem registrationSets_nonempty
    {Q : DWeb V} {U : Set V} {kappa : Cardinal.{u}}
    (h : ∃ rho : Cardinal.{u}, rho < kappa ∧
      Nonempty (LocalizedProtectedHalfwayGeometry Q U rho)) :
    (registrationSets Q U kappa).Nonempty := by
  obtain ⟨rho, hrho, ⟨D⟩⟩ := h
  obtain ⟨X, hX, hXcard⟩ := D.height
  exact ⟨X ∪ Q.vertexSet D.targetPaths,
    Or.inl ⟨rho, hrho, U, Set.Subset.rfl, D, X, hX, hXcard, rfl⟩⟩

/-- A full target linkage on a small whole source makes the alternative
visible registration family nonempty. -/
theorem registrationSets_nonempty_of_fullTarget
    {Q : DWeb V} {U : Set V} {kappa : Cardinal.{u}}
    {P : Set Q.DPath} (hsource : #Q.source < kappa)
    (hP : IsLinkageBetween Q Q.source Q.target P) :
    (registrationSets Q U kappa).Nonempty := by
  exact ⟨Q.vertexSet P, Or.inr ⟨P, hsource, hP, rfl⟩⟩

/-- Recover the actual protected geometry and height witness chosen by the
visible registration. -/
theorem exists_witness_with_registration
    {Q : DWeb V} {U : Set V} {kappa : Cardinal.{u}}
    (h : (registrationSets Q U kappa).Nonempty) :
    IsProtectedRegistrationWitness Q U kappa (registration Q U kappa) ∨
      IsFullTargetRegistrationWitness Q kappa (registration Q U kappa) := by
  have hmem := SliceCandidate.chooseVertexSet_mem
    h
  exact hmem

/-- The protected choice is strictly small whenever the visible stage web
is normalized.  In the empty case the total choice is empty. -/
theorem mk_registration_lt
    {Q : DWeb V} {U : Set V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : Q.IsNormalized) :
    #(registration Q U kappa) < kappa := by
  classical
  by_cases hnonempty : (registrationSets Q U kappa).Nonempty
  · have hmem := SliceCandidate.chooseVertexSet_mem hnonempty
    change #(SliceCandidate.chooseVertexSet
      (registrationSets Q U kappa)) < kappa
    rcases hmem with
      ⟨rho, hrho, A₀, hUA₀, D, X, hX, hXcard, hregistration⟩ |
      ⟨P, hsource, hP, hregistration⟩
    · rw [hregistration]
      exact RegularCardinal.mk_union_lt hregular
        (hXcard.trans_lt hrho)
        (RegularLocalizedProtectedCleanSlice.LocalizedProtectedHalfwayGeometry.targetCarrier_small
          D hNorm huncountable hrho)
    · rw [hregistration]
      exact SingularSafeCarrierCardinal.mk_vertexSet_lt_of_mk_initial_lt
        huncountable hP (by simpa only [hP.initialSet_eq] using hsource)
  · have hempty : registration Q U kappa = ∅ := by
      rw [registration, SliceCandidate.chooseVertexSet, dif_neg hnonempty]
    rw [hempty, Cardinal.mk_emptyCollection]
    exact Cardinal.aleph0_pos.trans huncountable

/-- Prefix transport is literal extensionality: only the visible stage web
and the request value enter the chosen family. -/
theorem registrationAt_congr_stageData
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L L' : Gamma.KappaLadder kappa}
    {request request' : Ladder.Stage kappa → Ladder.Stage kappa → Set V}
    {delta gamma : Ladder.Stage kappa}
    (hwarp : L.warpAt delta = L'.warpAt delta)
    (hrequest : request delta gamma = request' delta gamma) :
    registrationAt L request delta gamma =
      registrationAt L' request' delta gamma := by
  have hstage : L.stageWeb delta = L'.stageWeb delta := by
    simp only [DWeb.KappaLadder.stageWeb, DWeb.stageWebOf, hwarp]
  simp only [registrationAt, hstage, hrequest]

/-- Pair-owned form: retain the existing closure entry and add the whole
protected half-way registration at the same visible coordinate. -/
noncomputable def protectedPairEntry
    (G : DWeb V) {kappa : Cardinal.{u}}
    (huncountable : aleph0 < kappa) (F : Set G.DPath)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → RegularRows.CausalState kappa V)
    (delta gamma : Set.Iio a) : Set V :=
  RegularRows.CausalRegular.twoWarpRowRegistration G F
      ((RegularRows.CausalRegular.priorLadder G a prior).warpAt gamma.1)
      (prior delta.1 delta.2).row ∪
    registrationAt (RegularRows.CausalRegular.priorLadder G a prior)
      (RegularRows.CausalRegular.priorRequest G huncountable.le a prior)
      delta.1 gamma.1

/-- One protected pair entry still has size at most the regular cardinal. -/
theorem mk_protectedPairEntry_le
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → RegularRows.CausalState kappa V)
    (delta gamma : Set.Iio a) :
    #(protectedPairEntry G huncountable F a prior delta gamma) ≤
      kappa := by
  apply (Cardinal.mk_union_le _ _).trans
  apply Cardinal.add_le_of_le hregular.aleph0_le
  · exact RegularRows.CausalRegular.mk_twoWarpRowRegistration_le G
      hregular.aleph0_le hF
        (RegularRows.CausalRegular.canonicalLadderCore_warpAt_isWarp_of_normalized
          G hNorm kappa (RegularRows.CausalRegular.preferredOfPrior a prior)
            gamma.1)
        (prior delta.1 delta.2).row_mk_le
  · exact (mk_registration_lt hregular huncountable
      (RegularCandidateProvider.stageWeb_isNormalized hNorm
        (RegularRows.CausalRegular.priorLadder G a prior) delta.1)).le

end RegularLocalizedProtectedRegistration
end CardinalInduction
end Erdos599
