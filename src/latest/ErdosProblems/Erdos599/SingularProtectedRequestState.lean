/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeBatch

/-!
# An iterable two-track state for protected singular requests

The protected singular construction has an important one-step shift.  The
batch chosen at the present stage must know the requests which will become
current at the following stage, but the requests for the stage after that may
be computed from the chosen batch.  This file packages exactly that shift.

A `ProtectedRequestState` carries an unhindered residual web, its current
coordinates, and one look-ahead reserve.  Both coordinate sets have the same
cardinality below the induction cardinal.  The lower half-way clause is
applied to the source restriction on their union.  Its separating stop-over
produces a new unhindered quotient and transports the old reserve, without
cardinal loss, to the new current coordinates.

Crucially, the next reserve is selected only after the batch is known.  As
long as it is a source set of the new quotient with the same cardinality, the
union of the new current and reserve coordinates again induces an unhindered
source subweb.  Thus no post-choice fixed-point assumption is needed for the
protected request web itself.

This state does not assert that arbitrary completed ambient paths may be
deleted.  That distinct carrier-protection obligation belongs to the ambient
restoration layer.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProtectedRequestState

open SingularSafeBatch

universe u

variable {V : Type u}

/-- One residual request state with a current track and one look-ahead track.
The no-incoming-source field is retained because it is exactly what makes
arbitrary source restrictions preserve unhinderedness. -/
structure ProtectedRequestState (mu : Cardinal.{u}) where
  web : DWeb V
  unhindered : web.IsUnhindered
  noEdgeEnters : web.NoEdgeEnters web.source
  current : Set V
  reserve : Set V
  current_source : current ⊆ web.source
  reserve_source : reserve ⊆ web.source
  current_card : #current = mu
  reserve_card : #reserve = mu

namespace ProtectedRequestState

variable {mu : Cardinal.{u}}

/-- The lower-cardinal web used at this state is unhindered.  This is the
central invariant: it follows from the state's residual unhinderedness and is
not a separately postulated future-safety field. -/
theorem protected_unhindered (S : ProtectedRequestState (V := V) mu) :
    (protectedRequestWeb S.web S.current S.reserve).IsUnhindered := by
  exact S.unhindered.sourceSubweb S.web S.noEdgeEnters
    (Set.union_subset S.current_source S.reserve_source)

/-- The protected request web again has no edges entering its distinguished
source. -/
theorem protected_noEdgeEnters (S : ProtectedRequestState (V := V) mu) :
    (protectedRequestWeb S.web S.current S.reserve).NoEdgeEnters
      (protectedRequestWeb S.web S.current S.reserve).source :=
  noEdgeEnters_protectedRequestWeb S.noEdgeEnters
    S.current_source S.reserve_source

/-- A chosen protected batch changes the old reserve coordinates into the
current coordinates of its unhindered quotient. -/
def quotientWeb (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu) : DWeb V :=
  (protectedRequestWeb S.web S.current S.reserve).quotient B.boundary

/-- The quotient left by a protected batch is unhindered. -/
theorem quotientWeb_unhindered (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu) :
    (S.quotientWeb B).IsUnhindered :=
  B.quotient_unhindered

/-- No edge enters the source of the next quotient. -/
theorem quotientWeb_noEdgeEnters (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu) :
    (S.quotientWeb B).NoEdgeEnters (S.quotientWeb B).source := by
  exact DWeb.NoEdgeEnters.quotient
    (protectedRequestWeb S.web S.current S.reserve)
    S.protected_noEdgeEnters

/-- Install an arbitrary post-choice look-ahead reserve in the quotient of a
chosen batch.  The old reserve frontier is the next current track. -/
def nextState (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu)
    (nextReserve : Set V)
    (hnextReserve : nextReserve ⊆ (S.quotientWeb B).source)
    (hnextReserveCard : #nextReserve = mu) :
    ProtectedRequestState (V := V) mu where
  web := S.quotientWeb B
  unhindered := S.quotientWeb_unhindered B
  noEdgeEnters := S.quotientWeb_noEdgeEnters B
  current := B.reserveFrontier
  reserve := nextReserve
  current_source := B.reserveFrontier_subset_quotientSource
  reserve_source := hnextReserve
  current_card := B.mk_reserveFrontier_eq.trans S.reserve_card
  reserve_card := hnextReserveCard

@[simp] theorem nextState_web (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu)
    (nextReserve : Set V)
    (hnextReserve : nextReserve ⊆ (S.quotientWeb B).source)
    (hnextReserveCard : #nextReserve = mu) :
    (S.nextState B nextReserve hnextReserve hnextReserveCard).web =
      S.quotientWeb B := rfl

@[simp] theorem nextState_current (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu)
    (nextReserve : Set V)
    (hnextReserve : nextReserve ⊆ (S.quotientWeb B).source)
    (hnextReserveCard : #nextReserve = mu) :
    (S.nextState B nextReserve hnextReserve hnextReserveCard).current =
      B.reserveFrontier := rfl

@[simp] theorem nextState_reserve (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu)
    (nextReserve : Set V)
    (hnextReserve : nextReserve ⊆ (S.quotientWeb B).source)
    (hnextReserveCard : #nextReserve = mu) :
    (S.nextState B nextReserve hnextReserve hnextReserveCard).reserve =
      nextReserve := rfl

/-- The exact current-plus-post-choice-lookahead web in the successor state
is unhindered. -/
theorem nextState_protected_unhindered
    (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu)
    (nextReserve : Set V)
    (hnextReserve : nextReserve ⊆ (S.quotientWeb B).source)
    (hnextReserveCard : #nextReserve = mu) :
    (protectedRequestWeb (S.quotientWeb B) B.reserveFrontier
      nextReserve).IsUnhindered := by
  exact (S.nextState B nextReserve hnextReserve
    hnextReserveCard).protected_unhindered

end ProtectedRequestState

variable {mu : Cardinal.{u}}

/-- One successor package.  The next reserve is allowed to depend on the
chosen batch; this is the order of choice needed by competitor closure. -/
structure ProtectedRequestSuccessor
    (S : ProtectedRequestState (V := V) mu)
    (reserveAfter :
      ProtectedBatch S.web S.current S.reserve mu → Set V) where
  batch : ProtectedBatch S.web S.current S.reserve mu
  reserveAfter_source : reserveAfter batch ⊆
    (S.quotientWeb batch).source
  reserveAfter_card : #(reserveAfter batch) = mu

namespace ProtectedRequestSuccessor

variable {S : ProtectedRequestState (V := V) mu}
variable {reserveAfter :
  ProtectedBatch S.web S.current S.reserve mu → Set V}

/-- The successor state determined by the chosen batch and its post-choice
reserve.  This is a definition rather than an overridable structure field,
so its web and coordinate tracks reduce definitionally. -/
def next (T : ProtectedRequestSuccessor S reserveAfter) :
    ProtectedRequestState (V := V) mu :=
  S.nextState T.batch (reserveAfter T.batch)
    T.reserveAfter_source T.reserveAfter_card

@[simp] theorem next_web
    (T : ProtectedRequestSuccessor S reserveAfter) :
    T.next.web = S.quotientWeb T.batch := rfl

@[simp] theorem next_current
    (T : ProtectedRequestSuccessor S reserveAfter) :
    T.next.current = T.batch.reserveFrontier := rfl

@[simp] theorem next_reserve
    (T : ProtectedRequestSuccessor S reserveAfter) :
    T.next.reserve = reserveAfter T.batch := rfl

/-- The successor package exposes the exact invariant consumed by the next
lower-cardinal protected batch. -/
theorem next_protected_unhindered
    (T : ProtectedRequestSuccessor S reserveAfter) :
    (protectedRequestWeb T.next.web T.next.current
      T.next.reserve).IsUnhindered :=
  T.next.protected_unhindered

end ProtectedRequestSuccessor

/-- Unconditional protected-state successor.  The lower half-way clause sees
the reserve stored in `S`; the next reserve is evaluated only after that
batch has been selected. -/
theorem exists_successor_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (S : ProtectedRequestState (V := V) mu)
    (reserveAfter :
      ProtectedBatch S.web S.current S.reserve mu → Set V)
    (hreserveAfterSource : ∀ B, reserveAfter B ⊆
      (S.quotientWeb B).source)
    (hreserveAfterCard : ∀ B, #(reserveAfter B) = mu) :
    Nonempty (ProtectedRequestSuccessor S reserveAfter) := by
  obtain ⟨B⟩ := exists_protectedBatch_of_lower
    hlower hmu hmuInfinite S.web S.unhindered S.noEdgeEnters
      S.current_source S.reserve_source S.current_card
  exact ⟨
    { batch := B
      reserveAfter_source := hreserveAfterSource B
      reserveAfter_card := hreserveAfterCard B }⟩

/-- A canonical successor always exists: re-use the transported old reserve
as the following look-ahead reserve.  This form is useful for initializing
and testing the state recursion; construction-specific machines normally use
`exists_successor_of_lower` with their post-choice competitor reserve. -/
theorem exists_successor_selfReserve_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (S : ProtectedRequestState (V := V) mu) :
    Nonempty (ProtectedRequestSuccessor S
      (fun B ↦ B.reserveFrontier)) := by
  apply exists_successor_of_lower hlower hmu hmuInfinite S
  · intro B
    exact B.reserveFrontier_subset_quotientSource
  · intro B
    exact B.mk_reserveFrontier_eq.trans S.reserve_card

/-! ## Automatic padding of a post-choice request -/

/-- A successor whose post-choice reserve contains a requested batch-dependent
set.  The requested set itself may have cardinal strictly below the scale;
`nextReserve` pads it inside the quotient source to the exact scale needed by
the following lower-cardinal invocation. -/
structure CoveredProtectedRequestSuccessor
    (S : ProtectedRequestState (V := V) mu)
    (requestedAfter :
      ProtectedBatch S.web S.current S.reserve mu → Set V) where
  batch : ProtectedBatch S.web S.current S.reserve mu
  nextReserve : Set V
  requested_subset : requestedAfter batch ⊆ nextReserve
  nextReserve_source : nextReserve ⊆ (S.quotientWeb batch).source
  nextReserve_card : #nextReserve = mu

namespace CoveredProtectedRequestSuccessor

variable {S : ProtectedRequestState (V := V) mu}
variable {requestedAfter :
  ProtectedBatch S.web S.current S.reserve mu → Set V}

/-- The successor state determined by the padded post-choice request. -/
def next (T : CoveredProtectedRequestSuccessor S requestedAfter) :
    ProtectedRequestState (V := V) mu :=
  S.nextState T.batch T.nextReserve
    T.nextReserve_source T.nextReserve_card

@[simp] theorem next_current
    (T : CoveredProtectedRequestSuccessor S requestedAfter) :
    T.next.current = T.batch.reserveFrontier := rfl

@[simp] theorem next_reserve
    (T : CoveredProtectedRequestSuccessor S requestedAfter) :
    T.next.reserve = T.nextReserve := rfl

/-- The requested post-choice coordinates are present in the successor's
look-ahead track. -/
theorem requested_subset_next_reserve
    (T : CoveredProtectedRequestSuccessor S requestedAfter) :
    requestedAfter T.batch ⊆ T.next.reserve := by
  simpa only [next_reserve] using T.requested_subset

/-- The successor's current-plus-padded-lookahead web is unhindered. -/
theorem next_protected_unhindered
    (T : CoveredProtectedRequestSuccessor S requestedAfter) :
    (protectedRequestWeb T.next.web T.next.current
      T.next.reserve).IsUnhindered :=
  T.next.protected_unhindered

end CoveredProtectedRequestSuccessor

/-- Every bounded post-choice request can be padded inside the newly chosen
quotient source.  The transported old reserve itself witnesses that this
source has cardinal at least `mu`. -/
theorem exists_covered_successor_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (S : ProtectedRequestState (V := V) mu)
    (requestedAfter :
      ProtectedBatch S.web S.current S.reserve mu → Set V)
    (hrequestedSource : ∀ B, requestedAfter B ⊆
      (S.quotientWeb B).source)
    (hrequestedCard : ∀ B, #(requestedAfter B) ≤ mu) :
    Nonempty (CoveredProtectedRequestSuccessor S requestedAfter) := by
  obtain ⟨B⟩ := exists_protectedBatch_of_lower
    hlower hmu hmuInfinite S.web S.unhindered S.noEdgeEnters
      S.current_source S.reserve_source S.current_card
  have hmuSource : mu ≤ #(S.quotientWeb B).source := by
    calc
      mu = #S.reserve := S.reserve_card.symm
      _ = #B.reserveFrontier := B.mk_reserveFrontier_eq.symm
      _ ≤ #(S.quotientWeb B).source := Cardinal.mk_subtype_mono
        B.reserveFrontier_subset_quotientSource
  obtain ⟨R, hrequestR, hRsource, hRcard⟩ :=
    exists_superset_mk_eq_of_mk_le
      (hrequestedSource B) (hrequestedCard B) hmuSource hmuInfinite
  exact ⟨
    { batch := B
      nextReserve := R
      requested_subset := hrequestR
      nextReserve_source := hRsource
      nextReserve_card := hRcard }⟩

/-! ## A genuine omega recursion of protected request states -/

/-- A post-choice reserve policy.  This is coordinate data, not a safety
assumption: the safety of the resulting protected request web is derived
from the state quotient.  In particular, the policy may inspect the chosen
batch before naming the following look-ahead coordinates. -/
structure ReservePolicy (mu : Cardinal.{u}) where
  reserveAfter : ∀ S : ProtectedRequestState (V := V) mu,
    ProtectedBatch S.web S.current S.reserve mu → Set V
  reserveAfter_source : ∀ S B, reserveAfter S B ⊆
    (S.quotientWeb B).source
  reserveAfter_card : ∀ S B, #(reserveAfter S B) = mu

/-- Raw post-choice requests, such as competitors of the selected displayed
row.  Only the natural source and upper-cardinality bounds are fields; exact
scale padding is constructed below. -/
structure BoundedRequestRule (mu : Cardinal.{u}) where
  requestedAfter : ∀ S : ProtectedRequestState (V := V) mu,
    ProtectedBatch S.web S.current S.reserve mu → Set V
  requestedAfter_source : ∀ S B, requestedAfter S B ⊆
    (S.quotientWeb B).source
  requestedAfter_card : ∀ S B, #(requestedAfter S B) ≤ mu

namespace BoundedRequestRule

variable {mu : Cardinal.{u}}

/-- The quotient source always has room for an exact-`mu` superset of the
bounded post-choice request. -/
theorem exists_paddedReserve
    (Q : BoundedRequestRule (V := V) mu)
    (hmuInfinite : aleph0 ≤ mu)
    (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu) :
    ∃ R : Set V,
      Q.requestedAfter S B ⊆ R ∧
      R ⊆ (S.quotientWeb B).source ∧ #R = mu := by
  have hmuSource : mu ≤ #(S.quotientWeb B).source := by
    calc
      mu = #S.reserve := S.reserve_card.symm
      _ = #B.reserveFrontier := B.mk_reserveFrontier_eq.symm
      _ ≤ #(S.quotientWeb B).source := Cardinal.mk_subtype_mono
        B.reserveFrontier_subset_quotientSource
  exact exists_superset_mk_eq_of_mk_le
    (Q.requestedAfter_source S B) (Q.requestedAfter_card S B)
      hmuSource hmuInfinite

/-- Canonically pad a bounded post-choice request. -/
noncomputable def paddedReserve
    (Q : BoundedRequestRule (V := V) mu)
    (hmuInfinite : aleph0 ≤ mu)
    (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu) : Set V :=
  Classical.choose (Q.exists_paddedReserve hmuInfinite S B)

theorem requestedAfter_subset_paddedReserve
    (Q : BoundedRequestRule (V := V) mu)
    (hmuInfinite : aleph0 ≤ mu)
    (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu) :
    Q.requestedAfter S B ⊆ Q.paddedReserve hmuInfinite S B :=
  (Classical.choose_spec
    (Q.exists_paddedReserve hmuInfinite S B)).1

theorem paddedReserve_source
    (Q : BoundedRequestRule (V := V) mu)
    (hmuInfinite : aleph0 ≤ mu)
    (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu) :
    Q.paddedReserve hmuInfinite S B ⊆ (S.quotientWeb B).source :=
  (Classical.choose_spec
    (Q.exists_paddedReserve hmuInfinite S B)).2.1

theorem paddedReserve_card
    (Q : BoundedRequestRule (V := V) mu)
    (hmuInfinite : aleph0 ≤ mu)
    (S : ProtectedRequestState (V := V) mu)
    (B : ProtectedBatch S.web S.current S.reserve mu) :
    #(Q.paddedReserve hmuInfinite S B) = mu :=
  (Classical.choose_spec
    (Q.exists_paddedReserve hmuInfinite S B)).2.2

/-- Turn the natural bounded request rule into the exact reserve policy used
by the global protected recursion. -/
noncomputable def toReservePolicy
    (Q : BoundedRequestRule (V := V) mu)
    (hmuInfinite : aleph0 ≤ mu) : ReservePolicy (V := V) mu where
  reserveAfter := fun S B ↦ Q.paddedReserve hmuInfinite S B
  reserveAfter_source := fun S B ↦ Q.paddedReserve_source hmuInfinite S B
  reserveAfter_card := fun S B ↦ Q.paddedReserve_card hmuInfinite S B

end BoundedRequestRule

namespace ReservePolicy

variable {kappa mu : Cardinal.{u}}

/-- Choose the lower-cardinal batch prescribed by a reserve policy. -/
noncomputable def successor
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (R : ReservePolicy (V := V) mu)
    (S : ProtectedRequestState (V := V) mu) :
    ProtectedRequestSuccessor S (R.reserveAfter S) :=
  Classical.choice (exists_successor_of_lower
    hlower hmu hmuInfinite S (R.reserveAfter S)
      (R.reserveAfter_source S) (R.reserveAfter_card S))

/-- The actual state transition selected by the policy. -/
noncomputable def step
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (R : ReservePolicy (V := V) mu)
    (S : ProtectedRequestState (V := V) mu) :
    ProtectedRequestState (V := V) mu :=
  (R.successor hlower hmu hmuInfinite S).next

/-- Iterate the protected request transition through omega. -/
noncomputable def stateAt
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (R : ReservePolicy (V := V) mu)
    (initial : ProtectedRequestState (V := V) mu) :
    ℕ → ProtectedRequestState (V := V) mu
  | 0 => initial
  | n + 1 => R.step hlower hmu hmuInfinite
      (stateAt hlower hmu hmuInfinite R initial n)

@[simp] theorem stateAt_zero
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (R : ReservePolicy (V := V) mu)
    (initial : ProtectedRequestState (V := V) mu) :
    R.stateAt hlower hmu hmuInfinite initial 0 = initial := rfl

@[simp] theorem stateAt_succ
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (R : ReservePolicy (V := V) mu)
    (initial : ProtectedRequestState (V := V) mu) (n : ℕ) :
    R.stateAt hlower hmu hmuInfinite initial (n + 1) =
      R.step hlower hmu hmuInfinite
        (R.stateAt hlower hmu hmuInfinite initial n) := rfl

/-- Every stage of the global run has the exact protected safety invariant.
No finite-horizon compactness or post-choice fixed point is used. -/
theorem stateAt_protected_unhindered
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (R : ReservePolicy (V := V) mu)
    (initial : ProtectedRequestState (V := V) mu) (n : ℕ) :
    (protectedRequestWeb
      (R.stateAt hlower hmu hmuInfinite initial n).web
      (R.stateAt hlower hmu hmuInfinite initial n).current
      (R.stateAt hlower hmu hmuInfinite initial n).reserve).IsUnhindered :=
  (R.stateAt hlower hmu hmuInfinite initial n).protected_unhindered

/-- At every transition, the next current track is literally the frontier of
the look-ahead track stored at the preceding stage. -/
theorem stateAt_current_succ
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (R : ReservePolicy (V := V) mu)
    (initial : ProtectedRequestState (V := V) mu) (n : ℕ) :
    (R.stateAt hlower hmu hmuInfinite initial (n + 1)).current =
      (R.successor hlower hmu hmuInfinite
        (R.stateAt hlower hmu hmuInfinite initial n)).batch.reserveFrontier :=
  rfl

/-- Canonical policy which carries the previous look-ahead track forward
again.  It proves that the global protected recursion is inhabited without
any selection hypothesis. -/
def selfReserve : ReservePolicy (V := V) mu where
  reserveAfter := fun _S B ↦ B.reserveFrontier
  reserveAfter_source := fun _S B ↦
    B.reserveFrontier_subset_quotientSource
  reserveAfter_card := fun S B ↦
    B.mk_reserveFrontier_eq.trans S.reserve_card

end ReservePolicy

namespace BoundedRequestRule

variable {kappa mu : Cardinal.{u}}

/-- Along the global run induced by a bounded request rule, the next
look-ahead track contains the request computed from the batch selected at the
current stage.  This is the precise order-of-choice property needed for a
competitor rule: select the batch, compute its competitors, then pad them in
the already produced quotient. -/
theorem requestedAfter_subset_stateAt_reserve_succ
    (Q : BoundedRequestRule (V := V) mu)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    (initial : ProtectedRequestState (V := V) mu) (n : ℕ) :
    let R := Q.toReservePolicy hmuInfinite
    let S := R.stateAt hlower hmu hmuInfinite initial n
    Q.requestedAfter S
        (R.successor hlower hmu hmuInfinite S).batch ⊆
      (R.stateAt hlower hmu hmuInfinite initial (n + 1)).reserve := by
  dsimp only
  change Q.requestedAfter
      ((Q.toReservePolicy hmuInfinite).stateAt
        hlower hmu hmuInfinite initial n)
      ((Q.toReservePolicy hmuInfinite).successor
        hlower hmu hmuInfinite
        ((Q.toReservePolicy hmuInfinite).stateAt
          hlower hmu hmuInfinite initial n)).batch ⊆
    Q.paddedReserve hmuInfinite
      ((Q.toReservePolicy hmuInfinite).stateAt
        hlower hmu hmuInfinite initial n)
      ((Q.toReservePolicy hmuInfinite).successor
        hlower hmu hmuInfinite
        ((Q.toReservePolicy hmuInfinite).stateAt
          hlower hmu hmuInfinite initial n)).batch
  exact Q.requestedAfter_subset_paddedReserve hmuInfinite _ _

end BoundedRequestRule

#print axioms ProtectedRequestState.protected_unhindered
#print axioms ProtectedRequestState.nextState_protected_unhindered
#print axioms exists_successor_of_lower
#print axioms exists_successor_selfReserve_of_lower
#print axioms exists_covered_successor_of_lower
#print axioms BoundedRequestRule.toReservePolicy
#print axioms BoundedRequestRule.requestedAfter_subset_stateAt_reserve_succ
#print axioms ReservePolicy.stateAt_protected_unhindered
#print axioms ReservePolicy.stateAt_current_succ

end SingularProtectedRequestState
end CardinalInduction
end Erdos599
