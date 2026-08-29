/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProgressiveExchange

/-!
# A global admissible schedule for the singular matrix

The finite obstruction in `SingularSafeBatchCounterexampleQuotient` shows
that a successor cannot be requested from every geometrically valid row.
Assertion 9.17 only needs one infinite coherent run.  This file records that
strictly weaker, construction-specific selection principle.

An `AdmissibleTransition` contains the lower quotient half-way witnesses
actually used at one horizontal stage, and identifies their restored ambient
rows with the next progressive state.  A `GlobalSchedule` chooses these
transitions for all natural-number stages at once.  Consequently it never
asserts that an arbitrary `ProgressiveState` has a successor.

The final theorem reduces the singular extension clause to existence of this
global schedule.  Thus the remaining strict-large obligation is a genuine
global selection/fixed-point theorem, rather than the false local successor
rule.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularGlobalSchedule

open SingularExtension SingularMatrix SingularProgressiveExchange

universe u

variable {V : Type u}

/-- A construction-specific transition between two progressive rows.  The
chosen column exchanges contain the quotient half-way families and all
ambient restoration data.  `paths_next` says that the next state is exactly
the simultaneous row assembled from those choices. -/
structure AdmissibleTransition
    (G : DWeb V) (fixed : Set G.DPath)
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (S T : ProgressiveState G kappa hkappa hsingular) where
  exchange : ∀ i : Index kappa, ColumnExchange G fixed S i
  sources_next :
    T.row.sources = nextTargetSources G fixed S.row
  paths_next : ∀ i : Index kappa,
    T.row.paths i = (exchange i).paths

namespace AdmissibleTransition

theorem forward
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    {S T : ProgressiveState G kappa hkappa hsingular}
    (h : AdmissibleTransition G fixed S T) (i : Index kappa) :
    G.ForwardExtension (S.row.paths i) (T.row.paths i) := by
  rw [h.paths_next i]
  exact (h.exchange i).forward

theorem links
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    {S T : ProgressiveState G kappa hkappa hsingular}
    (h : AdmissibleTransition G fixed S T) (i : Index kappa) :
    LinksToTarget G (T.row.paths i) (T.row.sources i) := by
  rw [h.paths_next i, h.sources_next]
  exact (h.exchange i).links

end AdmissibleTransition

/-- One globally selected infinite branch through the progressive exchange
tree.  Unlike `ProgressiveExchangeRule`, this structure has no quantifier
over rows outside the selected branch. -/
structure GlobalSchedule
    (G : DWeb V) (fixed : Set G.DPath)
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (initialSources : Index kappa → Set V) where
  state : ℕ → ProgressiveState G kappa hkappa hsingular
  sources_zero : (state 0).row.sources = initialSources
  step : ∀ n : ℕ,
    AdmissibleTransition G fixed (state n) (state (n + 1))

namespace GlobalSchedule

/-- Forget the quotient witnesses and private split certificates.  The
selected branch is exactly the future-proof machine consumed by the matrix
limit. -/
noncomputable def toTargetRowMachine
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    {initialSources : Index kappa → Set V}
    (S : GlobalSchedule G fixed kappa hkappa hsingular initialSources) :
    TargetRowMachine G fixed initialSources where
  State := ULift.{u} ℕ
  row n := (S.state n.down).row
  initial := ⟨0⟩
  next n := ⟨n.down + 1⟩
  sources_initial := S.sources_zero
  sources_next n := (S.step n.down).sources_next
  forward_next n i := (S.step n.down).forward i

/-- The globally selected schedule directly supplies the target rows of
Assertion 9.18. -/
noncomputable def toTargetRows
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (S : GlobalSchedule G fixed kappa hkappa hsingular
      (sourceLayer A₀ kappa hcard hkappa hsingular)) :
    TargetRows G fixed A₀ kappa hkappa hsingular hcard :=
  S.toTargetRowMachine.toTargetRows

end GlobalSchedule

/-- The exact global strict-large selection principle.  The source layers
and fixed complementary linkage are known before the whole omega branch is
chosen; only rows on that branch require admissible successors. -/
def GlobalScheduleSelectionAt
    (G : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular) : Prop :=
  ∀ (A₀ : Set V), A₀ ⊆ G.source → (hcard : #A₀ = kappa) →
    ∀ fixed : Set G.DPath,
      IsLinkageBetween G (G.source \ A₀) G.target fixed →
      Nonempty (GlobalSchedule G fixed kappa hkappa hsingular
        (sourceLayer A₀ kappa hcard hkappa hsingular))

/-- A global admissible schedule is sufficient for the singular extension
clause.  This is the public-facing consumer of the corrected global
selection theorem. -/
theorem singularExtensionClauseAt_of_normalizedGlobalSchedule
    (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V)
    (hschedule : GlobalScheduleSelectionAt Gamma.normalized
      kappa hkappa hsingular) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_normalizedTargetRowMachine
    kappa hkappa hsingular Gamma
  intro A₀ hA₀ hcard fixed hfixed
  exact (Classical.choice
    (hschedule A₀ hA₀ hcard fixed hfixed)).toTargetRowMachine

end SingularGlobalSchedule
end CardinalInduction
end Erdos599
