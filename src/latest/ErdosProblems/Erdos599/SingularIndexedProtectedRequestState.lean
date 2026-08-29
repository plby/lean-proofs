/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProtectedRequestState

/-!
# Simultaneous protected request recursion for singular columns

The competitor set in one singular column depends on the rows selected in
all columns.  Consequently a product of independently chosen one-column
reserve policies has the wrong order of quantifiers.  This file packages the
simultaneous version: first choose one lower-cardinal protected batch in every
column, then allow a bounded request rule to inspect that entire family, pad
each resulting request inside its own quotient source, and finally advance
all columns at once.

All unhinderedness assertions are derived from the protected quotients.  The
only fields of an `IndexedBoundedRequestRule` are the source inclusion and
cardinality estimate which the singular competitor calculation is supposed
to provide.  No ambient carrier-deletion assertion is included here.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularIndexedProtectedRequestState

open SingularProtectedRequestState SingularSafeBatch

universe u

variable {V : Type u}

/-- A family of protected request states, one for each singular column. -/
structure IndexedState (I : Type u) (scale : I → Cardinal.{u}) where
  column : ∀ i, ProtectedRequestState (V := V) (scale i)

/-- A simultaneous family of lower-cardinal protected batches. -/
abbrev BatchFamily {I : Type u} {scale : I → Cardinal.{u}}
    (S : IndexedState (V := V) I scale) :=
  ∀ i, ProtectedBatch (S.column i).web (S.column i).current
    (S.column i).reserve (scale i)

/-- Choose all column batches before computing any of the new requests. -/
noncomputable def selectedBatches
    {I : Type u} {scale : I → Cardinal.{u}}
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale) : BatchFamily S :=
  fun i ↦ Classical.choice <|
    exists_protectedBatch_of_lower hlower (hbelow i) (hinfinite i)
      (S.column i).web (S.column i).unhindered
      (S.column i).noEdgeEnters (S.column i).current_source
      (S.column i).reserve_source (S.column i).current_card

/-- A genuinely simultaneous post-choice request rule.  It may inspect the
whole selected batch family before asking for the next reserve in any one
column. -/
structure IndexedBoundedRequestRule
    (I : Type u) (scale : I → Cardinal.{u}) where
  requestedAfter : ∀ (S : IndexedState (V := V) I scale),
    BatchFamily S → I → Set V
  requestedAfter_source : ∀ S B i, requestedAfter S B i ⊆
    ((S.column i).quotientWeb (B i)).source
  requestedAfter_card : ∀ S B i,
    #(requestedAfter S B i) ≤ scale i

namespace IndexedBoundedRequestRule

variable {I : Type u} {scale : I → Cardinal.{u}}

/-- Every simultaneous bounded request has an exact-scale padding in its
column quotient.  The transported old reserve witnesses enough room. -/
theorem exists_paddedReserve
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale)
    (B : BatchFamily S) (i : I) :
    ∃ R : Set V,
      Q.requestedAfter S B i ⊆ R ∧
      R ⊆ ((S.column i).quotientWeb (B i)).source ∧
      #R = scale i := by
  have hscaleSource :
      scale i ≤ #((S.column i).quotientWeb (B i)).source := by
    calc
      scale i = #(S.column i).reserve := (S.column i).reserve_card.symm
      _ = #(B i).reserveFrontier := (B i).mk_reserveFrontier_eq.symm
      _ ≤ #((S.column i).quotientWeb (B i)).source :=
        Cardinal.mk_subtype_mono
          (B i).reserveFrontier_subset_quotientSource
  exact exists_superset_mk_eq_of_mk_le
    (Q.requestedAfter_source S B i) (Q.requestedAfter_card S B i)
      hscaleSource (hinfinite i)

/-- The chosen exact-scale padding of one simultaneous request. -/
noncomputable def paddedReserve
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale)
    (B : BatchFamily S) (i : I) : Set V :=
  Classical.choose (Q.exists_paddedReserve hinfinite S B i)

theorem requestedAfter_subset_paddedReserve
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale)
    (B : BatchFamily S) (i : I) :
    Q.requestedAfter S B i ⊆ Q.paddedReserve hinfinite S B i :=
  (Classical.choose_spec
    (Q.exists_paddedReserve hinfinite S B i)).1

theorem paddedReserve_source
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale)
    (B : BatchFamily S) (i : I) :
    Q.paddedReserve hinfinite S B i ⊆
      ((S.column i).quotientWeb (B i)).source :=
  (Classical.choose_spec
    (Q.exists_paddedReserve hinfinite S B i)).2.1

theorem paddedReserve_card
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale)
    (B : BatchFamily S) (i : I) :
    #(Q.paddedReserve hinfinite S B i) = scale i :=
  (Classical.choose_spec
    (Q.exists_paddedReserve hinfinite S B i)).2.2

/-- Advance every column after the entire family of batches and requests has
been selected. -/
noncomputable def step
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale) :
    IndexedState (V := V) I scale := by
  let B := selectedBatches hlower hbelow hinfinite S
  exact
    { column := fun i ↦
        (S.column i).nextState (B i)
          (Q.paddedReserve hinfinite S B i)
          (Q.paddedReserve_source hinfinite S B i)
          (Q.paddedReserve_card hinfinite S B i) }

/-- The batch family used by the simultaneous transition. -/
noncomputable def batchAt
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale) : BatchFamily S :=
  selectedBatches hlower hbelow hinfinite S

/-- The post-choice request is contained in the next look-ahead track. -/
theorem requestedAfter_subset_step_reserve
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale) (i : I) :
    Q.requestedAfter S (Q.batchAt hlower hbelow hinfinite S) i ⊆
      ((Q.step hlower hbelow hinfinite S).column i).reserve := by
  change Q.requestedAfter S
      (selectedBatches hlower hbelow hinfinite S) i ⊆
    Q.paddedReserve hinfinite S
      (selectedBatches hlower hbelow hinfinite S) i
  exact Q.requestedAfter_subset_paddedReserve hinfinite S _ i

/-- The old look-ahead frontier is literally the next current track. -/
theorem step_current
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale) (i : I) :
    ((Q.step hlower hbelow hinfinite S).column i).current =
      (Q.batchAt hlower hbelow hinfinite S i).reserveFrontier :=
  rfl

/-- Every column of the simultaneous successor again has the exact protected
unhinderedness invariant. -/
theorem step_protected_unhindered
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (S : IndexedState (V := V) I scale) (i : I) :
    let T := (Q.step hlower hbelow hinfinite S).column i
    (protectedRequestWeb T.web T.current T.reserve).IsUnhindered := by
  dsimp only
  exact (Q.step hlower hbelow hinfinite S).column i |>.protected_unhindered

/-- The simultaneous omega recursion. -/
noncomputable def stateAt
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (initial : IndexedState (V := V) I scale) :
    ℕ → IndexedState (V := V) I scale
  | 0 => initial
  | n + 1 => Q.step hlower hbelow hinfinite
      (stateAt Q hlower hbelow hinfinite initial n)

@[simp] theorem stateAt_zero
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (initial : IndexedState (V := V) I scale) :
    Q.stateAt hlower hbelow hinfinite initial 0 = initial := rfl

@[simp] theorem stateAt_succ
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (initial : IndexedState (V := V) I scale) (n : ℕ) :
    Q.stateAt hlower hbelow hinfinite initial (n + 1) =
      Q.step hlower hbelow hinfinite
        (Q.stateAt hlower hbelow hinfinite initial n) := rfl

/-- Every column at every stage of the simultaneous run has an unhindered
current-plus-lookahead request web. -/
theorem stateAt_protected_unhindered
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (initial : IndexedState (V := V) I scale) (n : ℕ) (i : I) :
    let S := (Q.stateAt hlower hbelow hinfinite initial n).column i
    (protectedRequestWeb S.web S.current S.reserve).IsUnhindered := by
  dsimp only
  exact (Q.stateAt hlower hbelow hinfinite initial n).column i
    |>.protected_unhindered

/-- At every omega transition, the globally computed post-choice request in
each column is contained in that column's next look-ahead reserve. -/
theorem requestedAfter_subset_stateAt_reserve_succ
    {kappa : Cardinal.{u}}
    (Q : IndexedBoundedRequestRule (V := V) I scale)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hbelow : ∀ i, scale i < kappa)
    (hinfinite : ∀ i, aleph0 ≤ scale i)
    (initial : IndexedState (V := V) I scale) (n : ℕ) (i : I) :
    let S := Q.stateAt hlower hbelow hinfinite initial n
    Q.requestedAfter S (Q.batchAt hlower hbelow hinfinite S) i ⊆
      ((Q.stateAt hlower hbelow hinfinite initial (n + 1)).column i).reserve := by
  dsimp only
  exact Q.requestedAfter_subset_step_reserve
    hlower hbelow hinfinite _ i

end IndexedBoundedRequestRule

#print axioms selectedBatches
#print axioms IndexedBoundedRequestRule.requestedAfter_subset_step_reserve
#print axioms IndexedBoundedRequestRule.stateAt_protected_unhindered
#print axioms IndexedBoundedRequestRule.requestedAfter_subset_stateAt_reserve_succ

end SingularIndexedProtectedRequestState
end CardinalInduction
end Erdos599
