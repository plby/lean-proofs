/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCardinal
import ErdosProblems.Erdos599.LadderSchedule
import ErdosProblems.Erdos599.LadderRoofRecursion
import ErdosProblems.Erdos599.SingularCardinal
import ErdosProblems.Erdos599.SliceCandidate

/-!
# The cumulative rows and preferred-marker schedule in the regular case

The regular-cardinal construction in Section 9 of Aharoni--Berger builds
sets `Z_a`, each of cardinality at most `kappa`, while simultaneously building
a `kappa`-ladder.  This file packages the set-theoretic part of that
construction.

There are two separate bookkeeping facts.

* At most `kappa` rows, each of size at most `kappa`, have a union of size at
  most `kappa`.  Consequently the whole union admits a one-request-per-stage
  schedule on `Ladder.Stage kappa`.
* Feeding that schedule to the canonical ladder roofs every scheduled vertex.
  Thus the union of all the rows is contained in the ladder's limiting roof.

The first part is independent of graphs and ladders.  The final theorem is the
precise bridge to the preferred-marker API in `LadderSchedule` and is the
formal form of source Assertion 9.14.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularRows

universe u

open RegularCardinal

variable {kappa : Cardinal.{u}} {X : Type u}

/-! ## Cardinally bounded row systems -/

/-- A family of the source's closing-up rows, together with the cardinal
bound maintained by recursion (9.13a). -/
structure RowSystem (kappa : Cardinal.{u}) (X : Type u) where
  row : RegularCardinal.Stage kappa -> Set X
  row_mk_le : ∀ a, #(row a) <= kappa

namespace RowSystem

/-- The final closing-up set obtained by taking the union of all rows. -/
def carrier (R : RowSystem kappa X) : Set X :=
  RegularCardinal.rowUnion R.row

@[simp]
theorem mem_carrier {R : RowSystem kappa X} {x : X} :
    x ∈ R.carrier ↔ ∃ a, x ∈ R.row a := by
  exact RegularCardinal.mem_rowUnion

/-- A row is contained in the final closing-up set. -/
theorem row_subset_carrier (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa) :
    R.row a ⊆ R.carrier := by
  intro x hx
  exact mem_carrier.mpr ⟨a, hx⟩

/-- The union of `kappa` many rows of size at most `kappa` still has size at
most `kappa`.  `Stage kappa` lives in the ordinal universe, so the proof uses
the lifted-universe indexed-union estimate explicitly. -/
theorem mk_carrier_le (R : RowSystem kappa X) (hkappa : aleph0 <= kappa) :
    #R.carrier <= kappa := by
  have hLift :
      Cardinal.lift.{u + 1} #R.carrier <=
        Cardinal.lift.{u + 1} kappa := by
    change Cardinal.lift.{u + 1} #( ⋃ a, R.row a) <=
      Cardinal.lift.{u + 1} kappa
    refine (Cardinal.mk_iUnion_le_lift R.row).trans ?_
    rw [Stationary.mk_below]
    exact Cardinal.mul_le_of_le
      (Cardinal.aleph0_le_lift.mpr hkappa)
      (by simpa only [Cardinal.lift_lift] using
        (le_rfl : Cardinal.lift.{u + 1} kappa <=
          Cardinal.lift.{u + 1} kappa))
      (ciSup_le' fun a => Cardinal.lift_le.mpr (R.row_mk_le a))
  exact Cardinal.lift_le.mp hLift

/-- A canonical embedding of the final row union into the ladder stages. -/
def carrierEmbedding (R : RowSystem kappa X) (hkappa : aleph0 <= kappa) :
    R.carrier ↪ RegularCardinal.Stage kappa :=
  Classical.choice
    (RegularCardinal.nonempty_embedding_stage_of_mk_le
      (R.mk_carrier_le hkappa))

/-- The one-request-per-stage preferred-marker stream obtained by enumerating
the entire closing-up set. -/
def preferred (R : RowSystem kappa X) (hkappa : aleph0 <= kappa) :
    RegularCardinal.Stage kappa -> Option X :=
  RegularCardinal.enumerateAlong (R.carrierEmbedding hkappa)

/-- Every vertex in the final row union is requested by the preferred stream
at a (unique, though uniqueness is not needed) ladder stage. -/
theorem exists_preferred_eq_some (R : RowSystem kappa X)
    (hkappa : aleph0 <= kappa) {x : X} (hx : x ∈ R.carrier) :
    ∃ a, R.preferred hkappa a = some x := by
  let xs : R.carrier := ⟨x, hx⟩
  exact ⟨R.carrierEmbedding hkappa xs,
    RegularCardinal.enumerateAlong_apply (R.carrierEmbedding hkappa) xs⟩

/-- Row-by-row form of schedule coverage. -/
theorem exists_preferred_eq_some_of_mem_row (R : RowSystem kappa X)
    (hkappa : aleph0 <= kappa) {a : RegularCardinal.Stage kappa} {x : X}
    (hx : x ∈ R.row a) :
    ∃ b, R.preferred hkappa b = some x :=
  R.exists_preferred_eq_some hkappa (R.row_subset_carrier a hx)

/-! ### The source's diagonal fair enumeration (9.13) -/

/-- The row-by-row partial enumeration used in the source's diagonal
argument. -/
def diagonalEnumeration (R : RowSystem kappa X) :
    RegularCardinal.Stage kappa ->
      RegularCardinal.Stage kappa -> Option X :=
  RegularCardinal.rowEnumeration R.row R.row_mk_le

/-- The diagonal enumeration covers every row. -/
theorem diagonalEnumeration_enumerates (R : RowSystem kappa X) :
    RegularCardinal.EnumeratesRows R.row R.diagonalEnumeration :=
  RegularCardinal.rowEnumeration_enumerates R.row R.row_mk_le

/-- The part of the row table whose row and column coordinates are both
strictly below `a`. -/
def diagonal (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa) : Set X :=
  RegularCardinal.diagonalSlice R.diagonalEnumeration a

theorem diagonal_mono (R : RowSystem kappa X)
    {a b : RegularCardinal.Stage kappa} (hab : a <= b) :
    R.diagonal a ⊆ R.diagonal b :=
  RegularCardinal.diagonalSlice_mono R.diagonalEnumeration hab

/-- Assertion 9.13: every `< kappa` subset of the final closing-up set is
contained in a single diagonal. -/
theorem exists_diagonal_superset (R : RowSystem kappa X)
    (hkappa : kappa.IsRegular) {U : Set X}
    (hU : U ⊆ R.carrier) (hUcard : #U < kappa) :
    ∃ a : RegularCardinal.Stage kappa, U ⊆ R.diagonal a :=
  RegularCardinal.exists_diagonalSlice_superset hkappa
    R.diagonalEnumeration_enumerates hU hUcard

/-- Club-strengthened 9.13, above an already fixed stage. -/
theorem exists_club_diagonal_superset_above
    (R : RowSystem kappa X) (hkappa : kappa.IsRegular)
    {C : Set (RegularCardinal.Stage kappa)}
    (hC : Stationary.IsClubBelow kappa C) {U : Set X}
    (hU : U ⊆ R.carrier) (hUcard : #U < kappa)
    (a : RegularCardinal.Stage kappa) :
    ∃ b ∈ C, a < b ∧ U ⊆ R.diagonal b :=
  RegularCardinal.exists_mem_club_diagonalSlice_superset_above hkappa hC
    R.diagonalEnumeration_enumerates hU hUcard a

/-! ### A bounded-priority order on row entries -/

/-- A value returned by the canonical row enumeration really belongs to
the row being enumerated. -/
theorem diagonalEnumeration_value_mem (R : RowSystem kappa X)
    {a b : RegularCardinal.Stage kappa} {x : X}
    (h : R.diagonalEnumeration a b = some x) :
    x ∈ R.row a := by
  classical
  unfold diagonalEnumeration RegularCardinal.rowEnumeration at h
  unfold RegularCardinal.enumerateAlong at h
  split at h
  next hpre =>
    have hs := Classical.choose_spec hpre
    have hx : (Classical.choose hpre).1 = x := Option.some.inj h
    simpa [hx] using (Classical.choose hpre).2
  next hpre => simp at h

/-- Every member of the final row union has a row and column coordinate in
the canonical row enumeration. -/
theorem exists_enumeration_coordinate (R : RowSystem kappa X)
    (x : R.carrier) :
    ∃ c : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa,
      R.diagonalEnumeration c.1 c.2 = some x.1 := by
  obtain ⟨a, hxa⟩ := RowSystem.mem_carrier.mp x.2
  obtain ⟨b, hb⟩ := R.diagonalEnumeration_enumerates a x.1 hxa
  exact ⟨(a, b), hb⟩

/-- A fixed coordinate assigned to every member of the row union. -/
def coordinate (R : RowSystem kappa X) (x : R.carrier) :
    RegularCardinal.Stage kappa × RegularCardinal.Stage kappa :=
  Classical.choose (R.exists_enumeration_coordinate x)

@[simp]
theorem coordinate_spec (R : RowSystem kappa X) (x : R.carrier) :
    R.diagonalEnumeration (R.coordinate x).1 (R.coordinate x).2 =
      some x.1 :=
  Classical.choose_spec (R.exists_enumeration_coordinate x)

theorem coordinate_injective (R : RowSystem kappa X) :
    Function.Injective R.coordinate := by
  intro x y hxy
  apply Subtype.ext
  have hx := R.coordinate_spec x
  have hy := R.coordinate_spec y
  rw [hxy] at hx
  exact Option.some.inj (hx.symm.trans hy)

/-- Shell-first lexicographic key.  Both coordinates below a fixed key are
bounded, which is the cardinal fact needed for fair scheduling. -/
def coordinateKey
    (c : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa) :
    Ordinal.{u} × (Ordinal.{u} × Ordinal.{u}) :=
  (max c.1.1 c.2.1, (c.1.1, c.2.1))

theorem coordinateKey_injective :
    Function.Injective (coordinateKey (kappa := kappa)) := by
  intro c d h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z => z.2.1) h
  · apply Subtype.ext
    exact congrArg (fun z => z.2.2) h

/-- The shell-first well-order on row/column coordinates. -/
def CoordinatePriority
    (c d : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa) :
    Prop :=
  (Prod.Lex (fun a b : Ordinal.{u} => a < b)
    (Prod.Lex (fun a b : Ordinal.{u} => a < b)
      (fun a b : Ordinal.{u} => a < b))).onFun
        (coordinateKey (kappa := kappa)) c d

noncomputable instance coordinatePriority_isWellOrder :
    IsWellOrder
      (RegularCardinal.Stage kappa × RegularCardinal.Stage kappa)
      (CoordinatePriority (kappa := kappa)) :=
  (coordinateKey_injective (kappa := kappa)).isWellOrder _

/-- The induced bounded-priority well-order on the actual row entries. -/
def Priority (R : RowSystem kappa X) (x y : R.carrier) : Prop :=
  CoordinatePriority (R.coordinate x) (R.coordinate y)

noncomputable instance priority_isWellOrder (R : RowSystem kappa X) :
    IsWellOrder R.carrier R.Priority :=
  (R.coordinate_injective).isWellOrder _

/-- The shell of a coordinate pair. -/
def coordinateShell
    (c : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa) :
    RegularCardinal.Stage kappa :=
  max c.1 c.2

theorem coordinateShell_le_of_priority
    {c d : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa}
    (h : CoordinatePriority c d) :
    coordinateShell c <= coordinateShell d := by
  change max c.1.1 c.2.1 <= max d.1.1 d.2.1
  unfold CoordinatePriority Function.onFun coordinateKey at h
  rw [Prod.lex_iff] at h
  rcases h with h | h
  · exact h.le
  · exact le_of_eq h.1

/-- An initial interval of the stage order has cardinality strictly below
`kappa`. -/
theorem mk_stage_Iic_lt (hkappa : aleph0 <= kappa)
    (a : RegularCardinal.Stage kappa) :
    #(Set.Iic a) < Cardinal.lift.{u + 1} kappa := by
  let e : Set.Iic a ↪ Set.Iio (a.1 + 1) :=
    ⟨fun b => ⟨b.1.1, by
        change b.1.1 < a.1 + 1
        exact b.2.trans_lt (lt_succ a.1)⟩, by
      intro b c h
      have hv : b.1.1 = c.1.1 :=
        congrArg (fun z : Set.Iio (a.1 + 1) => z.1) h
      exact Subtype.ext (Subtype.ext hv)⟩
  apply (Cardinal.mk_le_of_injective e.injective).trans_lt
  rw [Cardinal.mk_Iio_ordinal]
  apply Cardinal.lift_lt.mpr
  apply Cardinal.lt_ord.mp
  exact (Cardinal.isSuccLimit_ord hkappa).succ_lt a.2

/-- Embed the predecessors of an entry into the square of the bounded shell
containing its two enumeration coordinates. -/
def predecessorEmbedding (R : RowSystem kappa X) (x : R.carrier) :
    {y : R.carrier // R.Priority y x} ↪
      Set.Iic (coordinateShell (R.coordinate x)) ×
        Set.Iic (coordinateShell (R.coordinate x)) where
  toFun y :=
    (⟨(R.coordinate y.1).1,
      le_trans (le_max_left _ _)
        (coordinateShell_le_of_priority y.2)⟩,
     ⟨(R.coordinate y.1).2,
      le_trans (le_max_right _ _)
        (coordinateShell_le_of_priority y.2)⟩)
  inj' := by
    intro y z h
    apply Subtype.ext
    apply R.coordinate_injective
    apply Prod.ext
    · exact congrArg (fun q => q.1.1) h
    · exact congrArg (fun q => q.2.1) h

/-- Every priority initial segment has cardinality `< kappa`.  This is the
bounded-predecessor property that prevents starvation in the causal
one-request-per-stage scheduler. -/
theorem mk_priority_predecessors_lt (R : RowSystem kappa X)
    (hkappa : aleph0 <= kappa) (x : R.carrier) :
    #({y : R.carrier // R.Priority y x}) < kappa := by
  apply Cardinal.lift_lt.mp
  apply (Cardinal.lift_mk_le_lift_mk_of_injective
    (R.predecessorEmbedding x).injective).trans_lt
  rw [Cardinal.mk_prod, Cardinal.lift_mul]
  apply Cardinal.mul_lt_of_lt (Cardinal.aleph0_le_lift.mpr hkappa)
  · rw [Cardinal.lift_id'.{u, u + 1}, Cardinal.lift_id]
    exact mk_stage_Iic_lt hkappa (coordinateShell (R.coordinate x))
  · rw [Cardinal.lift_id'.{u, u + 1}, Cardinal.lift_id]
    exact mk_stage_Iic_lt hkappa (coordinateShell (R.coordinate x))

/-! ### The causal least-priority scheduler -/

/-- Entries selected at stages strictly before `a`. -/
def selectedBefore (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa, b < a -> Option R.carrier) :
    Set R.carrier :=
  {x | ∃ b, ∃ hba : b < a, prior b hba = some x}

/-- Eligible entries at a scheduler stage: entries already visible in the
diagonal table and not previously selected. -/
def availableAt (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa, b < a -> Option R.carrier) :
    Set R.carrier :=
  {x | x.1 ∈ R.diagonal a ∧ x ∉ R.selectedBefore a prior}

/-- Select the least-priority available entry, if there is one. -/
noncomputable def chooseAt (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa, b < a -> Option R.carrier) :
    Option R.carrier := by
  classical
  exact if h : (R.availableAt a prior).Nonempty then
    some ((IsWellFounded.wf (r := R.Priority)).min
      (R.availableAt a prior) h)
  else none

/-- The causal fair selection stream, defined by well-founded recursion on
the stage ordinal. -/
noncomputable def fairChosen (R : RowSystem kappa X) :
    RegularCardinal.Stage kappa -> Option R.carrier :=
  WellFoundedLT.fix fun a prior => R.chooseAt a prior

theorem fairChosen_eq (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa) :
    R.fairChosen a =
      R.chooseAt a (fun b _hba => R.fairChosen b) := by
  rw [fairChosen, WellFoundedLT.fix_eq]

/-- Ambient-valued form of the causal stream, ready to be used as the
ladder's preferred-marker argument. -/
def fairPreferred (R : RowSystem kappa X) :
    RegularCardinal.Stage kappa -> Option X :=
  fun a => (R.fairChosen a).map Subtype.val

theorem chooseAt_mem_availableAt (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa, b < a -> Option R.carrier)
    {x : R.carrier} (hx : R.chooseAt a prior = some x) :
    x ∈ R.availableAt a prior := by
  classical
  unfold chooseAt at hx
  split at hx
  next hne =>
    exact Option.some.inj hx ▸
      (IsWellFounded.wf (r := R.Priority)).min_mem
        (R.availableAt a prior) hne
  next hne => simp at hx

theorem fairChosen_mem_availableAt (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa) {x : R.carrier}
    (hx : R.fairChosen a = some x) :
    x ∈ R.availableAt a (fun b _hba => R.fairChosen b) := by
  rw [fairChosen_eq] at hx
  exact R.chooseAt_mem_availableAt a _ hx

theorem exists_chooseAt_eq_some_of_nonempty (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa, b < a -> Option R.carrier)
    (hne : (R.availableAt a prior).Nonempty) :
    ∃ x, R.chooseAt a prior = some x := by
  classical
  unfold chooseAt
  rw [dif_pos hne]
  exact ⟨_, rfl⟩

/-- The selected entry is priority-minimal among the available entries. -/
theorem not_priority_chooseAt (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa, b < a -> Option R.carrier)
    {x y : R.carrier} (hx : R.chooseAt a prior = some x)
    (hy : y ∈ R.availableAt a prior) :
    ¬ R.Priority y x := by
  classical
  unfold chooseAt at hx
  split at hx
  next hne =>
    have hxmin :
        (IsWellFounded.wf (r := R.Priority)).min
          (R.availableAt a prior) hne = x :=
      Option.some.inj hx
    rw [← hxmin]
    exact (IsWellFounded.wf (r := R.Priority)).not_lt_min
      (R.availableAt a prior) hy
  next hne => simp at hx

theorem not_priority_fairChosen (R : RowSystem kappa X)
    (a : RegularCardinal.Stage kappa) {x y : R.carrier}
    (hx : R.fairChosen a = some x)
    (hy : y ∈ R.availableAt a (fun b _hba => R.fairChosen b)) :
    ¬ R.Priority y x := by
  rw [fairChosen_eq] at hx
  exact R.not_priority_chooseAt a _ hx hy

/-- The causal scheduler never selects the same row entry twice. -/
theorem fairChosen_ne_of_lt (R : RowSystem kappa X)
    {a b : RegularCardinal.Stage kappa} (hab : a < b)
    {x : R.carrier} (hax : R.fairChosen a = some x) :
    R.fairChosen b ≠ some x := by
  intro hbx
  have hxavail := R.fairChosen_mem_availableAt b hbx
  exact hxavail.2 ⟨a, hab, hax⟩

theorem fairPreferred_eq_some_iff (R : RowSystem kappa X)
    {a : RegularCardinal.Stage kappa} {x : X} :
    R.fairPreferred a = some x ↔
      ∃ xs : R.carrier, R.fairChosen a = some xs ∧ xs.1 = x := by
  cases h : R.fairChosen a with
  | none => simp [fairPreferred, h]
  | some xs => simp [fairPreferred, h]

/-- The first stage by which both coordinates assigned to `x` are visible
in the diagonal table. -/
def activationStage (R : RowSystem kappa X) (hkappa : aleph0 <= kappa)
    (x : R.carrier) : RegularCardinal.Stage kappa :=
  ⟨(coordinateShell (R.coordinate x)).1 + 1,
    (Cardinal.isSuccLimit_ord hkappa).succ_lt
      (coordinateShell (R.coordinate x)).2⟩

theorem mem_diagonal_of_activationStage_le (R : RowSystem kappa X)
    (hkappa : aleph0 <= kappa) (x : R.carrier)
    {a : RegularCardinal.Stage kappa} (ha : R.activationStage hkappa x <= a) :
    x.1 ∈ R.diagonal a := by
  refine ⟨(R.coordinate x).1, (R.coordinate x).2, ?_, ?_,
    R.coordinate_spec x⟩
  · apply lt_of_lt_of_le _ ha
    change (R.coordinate x).1.1 <
      (coordinateShell (R.coordinate x)).1 + 1
    exact (le_max_left _ _).trans_lt (lt_succ _)
  · apply lt_of_lt_of_le _ ha
    change (R.coordinate x).2.1 <
      (coordinateShell (R.coordinate x)).1 + 1
    exact (le_max_right _ _).trans_lt (lt_succ _)

/-- If a visible entry has never been selected, the scheduler necessarily
selects some entry at the current stage. -/
theorem exists_fairChosen_eq_some_of_visible_of_never
    (R : RowSystem kappa X) {a : RegularCardinal.Stage kappa}
    (x : R.carrier) (hvisible : x.1 ∈ R.diagonal a)
    (hnever : ∀ b, R.fairChosen b ≠ some x) :
    ∃ y, R.fairChosen a = some y := by
  have hxAvailable :
      x ∈ R.availableAt a (fun b _hba => R.fairChosen b) := by
    refine ⟨hvisible, ?_⟩
    rintro ⟨b, hba, hb⟩
    exact hnever b hb
  rw [R.fairChosen_eq a]
  exact R.exists_chooseAt_eq_some_of_nonempty a _ ⟨x, hxAvailable⟩

/-- The entry selected while `x` is visible and starving lies strictly
before `x` in the bounded priority order. -/
theorem priority_fairChosen_of_visible_of_never
    (R : RowSystem kappa X) {a : RegularCardinal.Stage kappa}
    (x y : R.carrier) (hvisible : x.1 ∈ R.diagonal a)
    (hnever : ∀ b, R.fairChosen b ≠ some x)
    (hy : R.fairChosen a = some y) :
    R.Priority y x := by
  have hxAvailable :
      x ∈ R.availableAt a (fun b _hba => R.fairChosen b) := by
    refine ⟨hvisible, ?_⟩
    rintro ⟨b, hba, hb⟩
    exact hnever b hb
  have hnotxy : ¬ R.Priority x y :=
    R.not_priority_fairChosen a hy hxAvailable
  have hyxne : y ≠ x := by
    intro hyx
    apply hnever a
    simpa [hyx] using hy
  by_contra hnotyx
  exact hyxne (Std.Trichotomous.trichotomous (r := R.Priority)
    y x hnotyx hnotxy)

/-- When `x` is assumed to starve, choose the entry emitted at every stage
after `x` becomes visible. -/
noncomputable def starvingChoice (R : RowSystem kappa X)
    (hkappa : aleph0 <= kappa) (x : R.carrier)
    (hnever : ∀ b, R.fairChosen b ≠ some x)
    (a : Set.Ici (R.activationStage hkappa x)) : R.carrier :=
  Classical.choose <| R.exists_fairChosen_eq_some_of_visible_of_never x
    (R.mem_diagonal_of_activationStage_le hkappa x a.2) hnever

@[simp]
theorem fairChosen_starvingChoice (R : RowSystem kappa X)
    (hkappa : aleph0 <= kappa) (x : R.carrier)
    (hnever : ∀ b, R.fairChosen b ≠ some x)
    (a : Set.Ici (R.activationStage hkappa x)) :
    R.fairChosen a.1 = some (R.starvingChoice hkappa x hnever a) :=
  Classical.choose_spec <| R.exists_fairChosen_eq_some_of_visible_of_never x
    (R.mem_diagonal_of_activationStage_le hkappa x a.2) hnever

theorem starvingChoice_priority (R : RowSystem kappa X)
    (hkappa : aleph0 <= kappa) (x : R.carrier)
    (hnever : ∀ b, R.fairChosen b ≠ some x)
    (a : Set.Ici (R.activationStage hkappa x)) :
    R.Priority (R.starvingChoice hkappa x hnever a) x := by
  exact R.priority_fairChosen_of_visible_of_never x _
    (R.mem_diagonal_of_activationStage_le hkappa x a.2) hnever
    (R.fairChosen_starvingChoice hkappa x hnever a)

/-- Starvation would inject the entire final interval of stages into the
strict priority predecessors of the starving entry. -/
noncomputable def starvationEmbedding (R : RowSystem kappa X)
    (hkappa : aleph0 <= kappa) (x : R.carrier)
    (hnever : ∀ b, R.fairChosen b ≠ some x) :
    Set.Ici (R.activationStage hkappa x) ↪
      {y : R.carrier // R.Priority y x} where
  toFun a := ⟨R.starvingChoice hkappa x hnever a,
    R.starvingChoice_priority hkappa x hnever a⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    rcases lt_trichotomy a.1 b.1 with halt | heq | hblt
    · have hdistinct := R.fairChosen_ne_of_lt halt
        (R.fairChosen_starvingChoice hkappa x hnever a)
      apply hdistinct
      have hv : R.starvingChoice hkappa x hnever a =
          R.starvingChoice hkappa x hnever b :=
        congrArg Subtype.val hab
      simpa [hv] using R.fairChosen_starvingChoice hkappa x hnever b
    · exact hne heq
    · have hdistinct := R.fairChosen_ne_of_lt hblt
        (R.fairChosen_starvingChoice hkappa x hnever b)
      apply hdistinct
      have hv : R.starvingChoice hkappa x hnever a =
          R.starvingChoice hkappa x hnever b :=
        congrArg Subtype.val hab
      simpa [hv] using R.fairChosen_starvingChoice hkappa x hnever a

/-- No entry starves in the causal least-priority scheduler.  The proof is
the regular-cardinal counting argument implicit in source 9.13: starvation
would inject a stationary tail of size `kappa` into a priority initial
segment of size strictly below `kappa`. -/
theorem exists_fairChosen_eq_some (R : RowSystem kappa X)
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (x : R.carrier) :
    ∃ a, R.fairChosen a = some x := by
  by_contra hstarves
  push Not at hstarves
  let a0 := R.activationStage hkappa.aleph0_le x
  letI : Nonempty (RegularCardinal.Stage kappa) := ⟨a0⟩
  have htailStat : Stationary.IsStationaryBelow kappa (Set.Ici a0) :=
    (Stationary.isClub_Ici a0).isStationary
      (RegularCardinal.cof_stage_ne_aleph0 hkappa hkappaUncountable)
  have htailCard : #(Set.Ici a0) = Cardinal.lift.{u + 1, u} kappa :=
    Stationary.mk_eq_lift_of_isStationaryBelow hkappa htailStat
  change #(Set.Ici (R.activationStage hkappa.aleph0_le x)) =
    Cardinal.lift.{u + 1, u} kappa at htailCard
  have hinj := Cardinal.lift_mk_le_lift_mk_of_injective
    (R.starvationEmbedding hkappa.aleph0_le x hstarves).injective
  have hsmall := R.mk_priority_predecessors_lt hkappa.aleph0_le x
  have hsmallLift :
      Cardinal.lift.{u + 1, u} #({y : R.carrier // R.Priority y x}) <
        Cardinal.lift.{u + 1, u} kappa :=
    Cardinal.lift_lt.mpr hsmall
  have hinj' :
      Cardinal.lift.{u + 1, u} kappa ≤
        Cardinal.lift.{u + 1, u} #({y : R.carrier // R.Priority y x}) := by
    simpa only [htailCard, Cardinal.lift_lift, Cardinal.lift_id] using hinj
  exact (not_lt_of_ge hinj') hsmallLift

/-- Ambient-valued coverage theorem for the causal preferred stream. -/
theorem exists_fairPreferred_eq_some (R : RowSystem kappa X)
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    {x : X} (hx : x ∈ R.carrier) :
    ∃ a, R.fairPreferred a = some x := by
  let xs : R.carrier := ⟨x, hx⟩
  obtain ⟨a, ha⟩ := R.exists_fairChosen_eq_some hkappa
    hkappaUncountable xs
  refine ⟨a, ?_⟩
  simp only [fairPreferred, ha, Option.map_some]
  rfl

/-! ## Cumulative rows -/

/-- The cumulative row through `a`: the fixed base together with every
increment inserted at a stage at most `a`. -/
def cumulativeRow (base : Set X)
    (increment : RegularCardinal.Stage kappa -> Set X)
    (a : RegularCardinal.Stage kappa) : Set X :=
  base ∪ ⋃ b ∈ Set.Iic a, increment b

theorem base_subset_cumulativeRow (base : Set X)
    (increment : RegularCardinal.Stage kappa -> Set X)
    (a : RegularCardinal.Stage kappa) :
    base ⊆ cumulativeRow base increment a :=
  fun _ hx => Or.inl hx

theorem increment_subset_cumulativeRow (base : Set X)
    (increment : RegularCardinal.Stage kappa -> Set X)
    (a : RegularCardinal.Stage kappa) :
    increment a ⊆ cumulativeRow base increment a := by
  intro x hx
  exact Or.inr (Set.mem_iUnion.2 ⟨a,
    Set.mem_iUnion.2 ⟨(by simp), hx⟩⟩)

theorem cumulativeRow_mono (base : Set X)
    (increment : RegularCardinal.Stage kappa -> Set X) :
    Monotone (cumulativeRow base increment) := by
  intro a b hab x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr <| by
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hx
      obtain ⟨hca, hxc⟩ := Set.mem_iUnion.1 hc
      exact Set.mem_iUnion.2 ⟨c,
        Set.mem_iUnion.2 ⟨hca.trans hab, hxc⟩⟩

/-- Each cumulative row has size at most `kappa` when the base and every
increment do. -/
theorem mk_cumulativeRow_le (hkappa : aleph0 <= kappa)
    {base : Set X} {increment : RegularCardinal.Stage kappa -> Set X}
    (hbase : #base <= kappa) (hincrement : ∀ a, #(increment a) <= kappa)
    (a : RegularCardinal.Stage kappa) :
    #(cumulativeRow base increment a) <= kappa := by
  have hInc : #(⋃ b ∈ Set.Iic a, increment b : Set X) <= kappa := by
    have hLift :
        Cardinal.lift.{u + 1} #(⋃ b ∈ Set.Iic a, increment b : Set X) <=
          Cardinal.lift.{u + 1} kappa := by
      refine (Cardinal.mk_biUnion_le_lift increment (Set.Iic a)).trans ?_
      exact Cardinal.mul_le_of_le
        (Cardinal.aleph0_le_lift.mpr hkappa)
        (by
          have hset : #(Set.Iic a) <= Cardinal.lift.{u + 1} kappa :=
            (Cardinal.mk_set_le (Set.Iic a)).trans_eq
              (Stationary.mk_below kappa)
          simpa only [Cardinal.lift_lift] using
            (Cardinal.lift_le.mpr hset))
        (ciSup_le' fun b => Cardinal.lift_le.mpr (hincrement b))
    exact Cardinal.lift_le.mp hLift
  exact (Cardinal.mk_union_le base
    (⋃ b ∈ Set.Iic a, increment b)).trans
      (Cardinal.add_le_of_le hkappa hbase hInc)

/-- The cumulative construction, packaged as a bounded row system. -/
def ofCumulative (hkappa : aleph0 <= kappa)
    (base : Set X) (increment : RegularCardinal.Stage kappa -> Set X)
    (hbase : #base <= kappa) (hincrement : ∀ a, #(increment a) <= kappa) :
    RowSystem kappa X where
  row := cumulativeRow base increment
  row_mk_le := mk_cumulativeRow_le hkappa hbase hincrement

end RowSystem

/-! ## Joint causal generation of rows and preferred markers

The static `RowSystem` above is convenient once all rows are known.  In the
regular proof, however, the row born at stage `a` may only use ladder data
known before `a`.  The following recursion therefore stores the new row and
the single scheduled vertex in one state.  Its scheduler sees only earlier
states.  This is the non-circular interface needed by (9.13a). -/

/-- One state of the joint row/schedule recursion. -/
structure CausalState (kappa : Cardinal.{u}) (X : Type u) where
  row : Set X
  row_mk_le : #row <= kappa
  chosen : Option X

/-- A causal row rule: the row at `a` is computed solely from states at
strictly smaller stages. -/
structure CausalRowRule (kappa : Cardinal.{u}) (X : Type u) where
  nextRow : ∀ a : RegularCardinal.Stage kappa,
    (∀ b : RegularCardinal.Stage kappa, b < a -> CausalState kappa X) ->
      Set X
  nextRow_mk_le : ∀ a prior, #(nextRow a prior) <= kappa

/-! ### Bounded pre-registration tables -/

/-- A union indexed by an arbitrary set of stages preserves a `≤ kappa`
bound when every entry has that bound. -/
theorem mk_iUnion_stageSet_le (hkappa : aleph0 <= kappa)
    {I : Set (RegularCardinal.Stage kappa)}
    (entry : I -> Set X) (hentry : ∀ i, #(entry i) <= kappa) :
    #(⋃ i, entry i) <= kappa := by
  have hLift :
      Cardinal.lift.{u + 1} #(⋃ i, entry i) <=
        Cardinal.lift.{u + 1} kappa := by
    refine (Cardinal.mk_iUnion_le_lift entry).trans ?_
    apply Cardinal.mul_le_of_le (Cardinal.aleph0_le_lift.mpr hkappa)
    · have hI : #I <= Cardinal.lift.{u + 1} kappa :=
        (Cardinal.mk_set_le I).trans_eq (Stationary.mk_below kappa)
      simpa only [Cardinal.lift_lift] using Cardinal.lift_le.mpr hI
    · exact ciSup_le' fun i => Cardinal.lift_le.mpr (hentry i)
  exact Cardinal.lift_le.mp hLift

/-- Union of all pair-indexed registrations whose two owners are earlier
than `a`. -/
def pairRegistrations (a : RegularCardinal.Stage kappa)
    (entry : Set.Iio a -> Set.Iio a -> Set X) : Set X :=
  ⋃ i, ⋃ j, entry i j

theorem mk_pairRegistrations_le (hkappa : aleph0 <= kappa)
    (a : RegularCardinal.Stage kappa)
    (entry : Set.Iio a -> Set.Iio a -> Set X)
    (hentry : ∀ i j, #(entry i j) <= kappa) :
    #(pairRegistrations a entry) <= kappa := by
  apply mk_iUnion_stageSet_le hkappa
  intro i
  apply mk_iUnion_stageSet_le hkappa
  exact hentry i

/-- Union of the triple-indexed candidate-maverick registrations whose
three owner coordinates are earlier than `a`. -/
def tripleRegistrations (a : RegularCardinal.Stage kappa)
    (entry : Set.Iio a -> Set.Iio a -> Set.Iio a -> Set X) : Set X :=
  ⋃ i, ⋃ j, ⋃ l, entry i j l

theorem mk_tripleRegistrations_le (hkappa : aleph0 <= kappa)
    (a : RegularCardinal.Stage kappa)
    (entry : Set.Iio a -> Set.Iio a -> Set.Iio a -> Set X)
    (hentry : ∀ i j l, #(entry i j l) <= kappa) :
    #(tripleRegistrations a entry) <= kappa := by
  apply mk_iUnion_stageSet_le hkappa
  intro i
  apply mk_iUnion_stageSet_le hkappa
  intro j
  apply mk_iUnion_stageSet_le hkappa
  exact hentry i j

theorem pair_entry_subset_registrations
    (a : RegularCardinal.Stage kappa)
    (entry : Set.Iio a -> Set.Iio a -> Set X) (i j : Set.Iio a) :
    entry i j ⊆ pairRegistrations a entry := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, hx⟩⟩

theorem triple_entry_subset_registrations
    (a : RegularCardinal.Stage kappa)
    (entry : Set.Iio a -> Set.Iio a -> Set.Iio a -> Set X)
    (i j l : Set.Iio a) :
    entry i j l ⊆ tripleRegistrations a entry := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j,
    Set.mem_iUnion.2 ⟨l, hx⟩⟩⟩

/-- Source-shaped constructor for (9.13a): every new row contains a fixed
base, all earlier pair-owned height registrations, and all earlier
triple-owned candidate-maverick registrations.  The entry functions may
inspect only the supplied strict-prior joint states. -/
def ofRegistrationTables (hkappa : aleph0 <= kappa)
    (base : Set X) (hbase : #base <= kappa)
    (pairEntry : ∀ (a : RegularCardinal.Stage kappa),
      (∀ b : RegularCardinal.Stage kappa, b < a -> CausalState kappa X) ->
        Set.Iio a -> Set.Iio a -> Set X)
    (tripleEntry : ∀ (a : RegularCardinal.Stage kappa),
      (∀ b : RegularCardinal.Stage kappa, b < a -> CausalState kappa X) ->
        Set.Iio a -> Set.Iio a -> Set.Iio a -> Set X)
    (hpair : ∀ a prior i j, #(pairEntry a prior i j) <= kappa)
    (htriple : ∀ a prior i j l,
      #(tripleEntry a prior i j l) <= kappa) :
    CausalRowRule kappa X where
  nextRow a prior :=
    (base ∪ pairRegistrations a (pairEntry a prior)) ∪
      tripleRegistrations a (tripleEntry a prior)
  nextRow_mk_le a prior := by
    have hp : #(pairRegistrations a (pairEntry a prior)) <= kappa :=
      mk_pairRegistrations_le hkappa a _ (hpair a prior)
    have ht : #(tripleRegistrations a (tripleEntry a prior)) <= kappa :=
      mk_tripleRegistrations_le hkappa a _ (htriple a prior)
    have hbp : #((base ∪ pairRegistrations a (pairEntry a prior)) : Set X)
        <= kappa :=
      (Cardinal.mk_union_le _ _).trans
        (Cardinal.add_le_of_le hkappa hbase hp)
    exact (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le hkappa hbp ht)

namespace CausalState

/-- Canonical column numbering of a bounded row. -/
def rowEmbedding (s : CausalState kappa X) (hkappa : aleph0 <= kappa) :
    s.row ↪ RegularCardinal.Stage kappa :=
  Classical.choice
    (RegularCardinal.nonempty_embedding_stage_of_mk_le s.row_mk_le)

end CausalState

namespace CausalRowRule

/-- Extend the preferences in a strict-prior state family by `none` at the
current and all later stages.  A causal graph row may safely build its
temporary canonical ladder from this stream. -/
def truncatedPreferred (Q : CausalRowRule kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X) :
    RegularCardinal.Stage kappa -> Option X :=
  fun b => if hba : b < a then (prior b hba).chosen else none

/-- Source terminology for `truncatedPreferred`. -/
abbrev priorPreferred (Q : CausalRowRule kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X) :=
  Q.truncatedPreferred a prior

/-- A task visible at stage `a`: a vertex in one of the strictly earlier
rows. -/
abbrev EarlierTask (Q : CausalRowRule kappa X)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X) :=
  Σ b : Set.Iio a, (prior b.1 b.2).row

/-- Stable row/column coordinate of an earlier task. -/
def earlierTaskCoordinate (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa)
    {a : RegularCardinal.Stage kappa}
    {prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X}
    (t : Q.EarlierTask a prior) :
    RegularCardinal.Stage kappa × RegularCardinal.Stage kappa :=
  (t.1.1, (prior t.1.1 t.1.2).rowEmbedding hkappa t.2)

theorem earlierTaskCoordinate_injective (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa)
    {a : RegularCardinal.Stage kappa}
    {prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X} :
    Function.Injective (Q.earlierTaskCoordinate hkappa
      (a := a) (prior := prior)) := by
  rintro ⟨b, x⟩ ⟨c, y⟩ h
  have hbc : b = c := by
    apply Subtype.ext
    exact congrArg Prod.fst h
  subst c
  have hxy : x = y := by
    apply (prior b.1 b.2).rowEmbedding hkappa |>.injective
    exact congrArg Prod.snd h
  subst y
  rfl

/-- Shell-first priority on currently visible tasks. -/
def EarlierPriority (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa)
    {a : RegularCardinal.Stage kappa}
    {prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X}
    (s t : Q.EarlierTask a prior) : Prop :=
  RowSystem.CoordinatePriority (Q.earlierTaskCoordinate hkappa s)
    (Q.earlierTaskCoordinate hkappa t)

noncomputable instance earlierPriority_isWellOrder
    (Q : CausalRowRule kappa X) (hkappa : aleph0 <= kappa)
    {a : RegularCardinal.Stage kappa}
    {prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X} :
    IsWellOrder (Q.EarlierTask a prior) (Q.EarlierPriority hkappa) := by
  change IsWellOrder (Q.EarlierTask a prior)
    ((RowSystem.CoordinatePriority (kappa := kappa)).onFun
      (Q.earlierTaskCoordinate hkappa))
  exact (Q.earlierTaskCoordinate_injective hkappa).isWellOrder _

/-- Ambient vertices selected before the current causal stage. -/
def selectedBefore (Q : CausalRowRule kappa X)
    {a : RegularCardinal.Stage kappa}
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X) : Set X :=
  {x | ∃ b, ∃ hba : b < a, (prior b hba).chosen = some x}

/-- Tasks whose column has appeared by `a` and whose vertex has not already
been emitted.  The row coordinate is automatically `< a`. -/
def availableTasks (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa)
    {a : RegularCardinal.Stage kappa}
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X) : Set (Q.EarlierTask a prior) :=
  {t | (Q.earlierTaskCoordinate hkappa t).2 < a ∧
    t.2.1 ∉ Q.selectedBefore prior}

/-- Least available task in the stable shell-first order. -/
noncomputable def chooseTask (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X) : Option (Q.EarlierTask a prior) := by
  classical
  exact if h : (Q.availableTasks hkappa prior).Nonempty then
    some ((IsWellFounded.wf (r := Q.EarlierPriority hkappa)).min
      (Q.availableTasks hkappa prior) h)
  else none

/-- One joint recursion step.  The new row is generated from the prior
states, while the emitted vertex is chosen only from prior rows. -/
noncomputable def nextState (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X) : CausalState kappa X where
  row := Q.nextRow a prior
  row_mk_le := Q.nextRow_mk_le a prior
  chosen := (Q.chooseTask hkappa a prior).map fun t => t.2.1

/-- The actual joint causal construction. -/
noncomputable def state (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) :
    RegularCardinal.Stage kappa -> CausalState kappa X :=
  WellFoundedLT.fix fun a prior => Q.nextState hkappa a prior

theorem state_eq (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) (a : RegularCardinal.Stage kappa) :
    Q.state hkappa a =
      Q.nextState hkappa a (fun b _hba => Q.state hkappa b) := by
  rw [state, WellFoundedLT.fix_eq]

theorem state_row_eq (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) (a : RegularCardinal.Stage kappa) :
    (Q.state hkappa a).row =
      Q.nextRow a (fun b _hba => Q.state hkappa b) :=
  congrArg CausalState.row (Q.state_eq hkappa a)

/-- Rows produced by the joint recursion, packaged for the static diagonal
and cardinality API. -/
def rowSystem (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) : RowSystem kappa X where
  row a := (Q.state hkappa a).row
  row_mk_le a := (Q.state hkappa a).row_mk_le

/-- The genuinely causal one-request-per-stage stream. -/
def preferred (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) :
    RegularCardinal.Stage kappa -> Option X :=
  fun a => (Q.state hkappa a).chosen

/-- Truncation of the actual prior states agrees with the final causal
stream at every genuinely earlier coordinate. -/
theorem truncatedPreferred_eq_preferred_of_lt
    (Q : CausalRowRule kappa X) (hkappa : aleph0 <= kappa)
    {a b : RegularCardinal.Stage kappa} (hba : b < a) :
    Q.truncatedPreferred a (fun c _hca => Q.state hkappa c) b =
      Q.preferred hkappa b := by
  simp only [truncatedPreferred, dif_pos hba, preferred]

theorem priorPreferred_eq_preferred_of_lt
    (Q : CausalRowRule kappa X) (hkappa : aleph0 <= kappa)
    {a b : RegularCardinal.Stage kappa} (hba : b < a) :
    Q.priorPreferred a (fun c _hca => Q.state hkappa c) b =
      Q.preferred hkappa b :=
  Q.truncatedPreferred_eq_preferred_of_lt hkappa hba

theorem preferred_eq_chooseTask_map (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) (a : RegularCardinal.Stage kappa) :
    Q.preferred hkappa a =
      (Q.chooseTask hkappa a (fun b _hba => Q.state hkappa b)).map
        (fun t => t.2.1) := by
  exact congrArg CausalState.chosen (Q.state_eq hkappa a)

theorem chooseTask_mem_availableTasks (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X)
    {t : Q.EarlierTask a prior} (ht : Q.chooseTask hkappa a prior = some t) :
    t ∈ Q.availableTasks hkappa prior := by
  classical
  unfold chooseTask at ht
  split at ht
  next hne =>
    exact Option.some.inj ht ▸
      (IsWellFounded.wf (r := Q.EarlierPriority hkappa)).min_mem
        (Q.availableTasks hkappa prior) hne
  next hne => simp at ht

theorem not_priority_chooseTask (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X)
    {s t : Q.EarlierTask a prior}
    (hs : Q.chooseTask hkappa a prior = some s)
    (ht : t ∈ Q.availableTasks hkappa prior) :
    ¬ Q.EarlierPriority hkappa t s := by
  classical
  unfold chooseTask at hs
  split at hs
  next hne =>
    have hmin :
        (IsWellFounded.wf (r := Q.EarlierPriority hkappa)).min
          (Q.availableTasks hkappa prior) hne = s :=
      Option.some.inj hs
    rw [← hmin]
    exact (IsWellFounded.wf (r := Q.EarlierPriority hkappa)).not_lt_min
      (Q.availableTasks hkappa prior) ht
  next hne => simp at hs

theorem exists_chooseTask_eq_some_of_nonempty
    (Q : CausalRowRule kappa X) (hkappa : aleph0 <= kappa)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa X)
    (hne : (Q.availableTasks hkappa prior).Nonempty) :
    ∃ t, Q.chooseTask hkappa a prior = some t := by
  classical
  unfold chooseTask
  rw [dif_pos hne]
  exact ⟨_, rfl⟩

/-- Row/column coordinate of a particular entry in an actual causal row. -/
def entryCoordinate (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) (b : RegularCardinal.Stage kappa)
    (x : (Q.state hkappa b).row) :
    RegularCardinal.Stage kappa × RegularCardinal.Stage kappa :=
  (b, (Q.state hkappa b).rowEmbedding hkappa x)

/-- A stage strictly beyond both coordinates of an actual row entry. -/
def activationStage (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) (b : RegularCardinal.Stage kappa)
    (x : (Q.state hkappa b).row) : RegularCardinal.Stage kappa :=
  ⟨(RowSystem.coordinateShell (Q.entryCoordinate hkappa b x)).1 + 1,
    (Cardinal.isSuccLimit_ord hkappa).succ_lt
      (RowSystem.coordinateShell (Q.entryCoordinate hkappa b x)).2⟩

/-- After activation, an entry has a task in the scheduler's current task
type, with its original stable coordinate. -/
def visibleTask (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) {b : RegularCardinal.Stage kappa}
    (x : (Q.state hkappa b).row) {a : RegularCardinal.Stage kappa}
    (ha : Q.activationStage hkappa b x <= a) :
    Q.EarlierTask a (fun c _hca => Q.state hkappa c) := by
  have hba : b < a := by
    apply lt_of_lt_of_le _ ha
    change b.1 <
      (RowSystem.coordinateShell (Q.entryCoordinate hkappa b x)).1 + 1
    exact (le_max_left _ _).trans_lt (lt_succ _)
  exact ⟨⟨b, hba⟩, x⟩

@[simp]
theorem visibleTask_coordinate (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) {b : RegularCardinal.Stage kappa}
    (x : (Q.state hkappa b).row) {a : RegularCardinal.Stage kappa}
    (ha : Q.activationStage hkappa b x <= a) :
    Q.earlierTaskCoordinate hkappa (Q.visibleTask hkappa x ha) =
      Q.entryCoordinate hkappa b x := by
  rfl

theorem visibleTask_mem_available_of_never
    (Q : CausalRowRule kappa X) (hkappa : aleph0 <= kappa)
    {b : RegularCardinal.Stage kappa}
    (x : (Q.state hkappa b).row) {a : RegularCardinal.Stage kappa}
    (ha : Q.activationStage hkappa b x <= a)
    (hnever : ∀ c, Q.preferred hkappa c ≠ some x.1) :
    Q.visibleTask hkappa x ha ∈
      Q.availableTasks hkappa (fun c _hca => Q.state hkappa c) := by
  constructor
  · apply lt_of_lt_of_le _ ha
    change (Q.entryCoordinate hkappa b x).2.1 <
      (RowSystem.coordinateShell (Q.entryCoordinate hkappa b x)).1 + 1
    exact (le_max_right _ _).trans_lt (lt_succ _)
  · rintro ⟨c, hca, hc⟩
    exact hnever c hc

/-- A causal preferred stream never emits one ambient vertex twice. -/
theorem preferred_ne_of_lt (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa)
    {a b : RegularCardinal.Stage kappa} (hab : a < b)
    {x : X} (hax : Q.preferred hkappa a = some x) :
    Q.preferred hkappa b ≠ some x := by
  intro hbx
  rw [Q.preferred_eq_chooseTask_map hkappa b] at hbx
  cases ht : Q.chooseTask hkappa b (fun c _hcb => Q.state hkappa c) with
  | none => simp [ht] at hbx
  | some t =>
      have htAvailable := Q.chooseTask_mem_availableTasks hkappa b _ ht
      have htx : t.2.1 = x := by simpa [ht] using hbx
      exact htAvailable.2 ⟨a, hab, by
        simpa [preferred, htx] using hax⟩

/-- Coordinate equality for tasks from two different later stages still
forces equality of their ambient vertex values. -/
theorem task_value_eq_of_coordinate_eq (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa)
    {a d : RegularCardinal.Stage kappa}
    (s : Q.EarlierTask a (fun c _hca => Q.state hkappa c))
    (t : Q.EarlierTask d (fun c _hcd => Q.state hkappa c))
    (hcoord : Q.earlierTaskCoordinate hkappa s =
      Q.earlierTaskCoordinate hkappa t) :
    s.2.1 = t.2.1 := by
  rcases s with ⟨⟨b, hba⟩, x⟩
  rcases t with ⟨⟨c, hcd⟩, y⟩
  have hbc : b = c := congrArg Prod.fst hcoord
  subst c
  have hxy : x = y := by
    apply (Q.state hkappa b).rowEmbedding hkappa |>.injective
    exact congrArg Prod.snd hcoord
  exact congrArg Subtype.val hxy

/-- Coordinates strictly before a fixed coordinate fit in the square of
its shell. -/
def coordinatePredecessorEmbedding
    (c : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa) :
    {d : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa //
      RowSystem.CoordinatePriority d c} ↪
      Set.Iic (RowSystem.coordinateShell c) ×
        Set.Iic (RowSystem.coordinateShell c) where
  toFun d :=
    (⟨d.1.1, le_trans (le_max_left _ _)
      (RowSystem.coordinateShell_le_of_priority d.2)⟩,
     ⟨d.1.2, le_trans (le_max_right _ _)
      (RowSystem.coordinateShell_le_of_priority d.2)⟩)
  inj' := by
    intro d e h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun q => q.1.1) h
    · exact congrArg (fun q => q.2.1) h

theorem mk_coordinatePredecessors_lt (hkappa : aleph0 <= kappa)
    (c : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa) :
    #({d : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa //
      RowSystem.CoordinatePriority d c}) <
      Cardinal.lift.{u + 1, u} kappa := by
  apply (Cardinal.mk_le_of_injective
    (coordinatePredecessorEmbedding c).injective).trans_lt
  rw [Cardinal.mk_prod]
  apply Cardinal.mul_lt_of_lt (Cardinal.aleph0_le_lift.mpr hkappa)
  · simpa only [Cardinal.lift_id] using
      RowSystem.mk_stage_Iic_lt hkappa (RowSystem.coordinateShell c)
  · simpa only [Cardinal.lift_id] using
      RowSystem.mk_stage_Iic_lt hkappa (RowSystem.coordinateShell c)

/-- Assuming one actual row entry starves, this is the task selected at
each stage of its activation tail. -/
noncomputable def starvingTask (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) {b : RegularCardinal.Stage kappa}
    (x : (Q.state hkappa b).row)
    (hnever : ∀ c, Q.preferred hkappa c ≠ some x.1)
    (a : Set.Ici (Q.activationStage hkappa b x)) :
    Q.EarlierTask a.1 (fun c _hca => Q.state hkappa c) :=
  Classical.choose <| Q.exists_chooseTask_eq_some_of_nonempty hkappa a.1 _
    ⟨Q.visibleTask hkappa x a.2,
      Q.visibleTask_mem_available_of_never hkappa x a.2 hnever⟩

@[simp]
theorem chooseTask_starvingTask (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) {b : RegularCardinal.Stage kappa}
    (x : (Q.state hkappa b).row)
    (hnever : ∀ c, Q.preferred hkappa c ≠ some x.1)
    (a : Set.Ici (Q.activationStage hkappa b x)) :
    Q.chooseTask hkappa a.1 (fun c _hca => Q.state hkappa c) =
      some (Q.starvingTask hkappa x hnever a) :=
  Classical.choose_spec <|
    Q.exists_chooseTask_eq_some_of_nonempty hkappa a.1 _
      ⟨Q.visibleTask hkappa x a.2,
        Q.visibleTask_mem_available_of_never hkappa x a.2 hnever⟩

@[simp]
theorem preferred_starvingTask (Q : CausalRowRule kappa X)
    (hkappa : aleph0 <= kappa) {b : RegularCardinal.Stage kappa}
    (x : (Q.state hkappa b).row)
    (hnever : ∀ c, Q.preferred hkappa c ≠ some x.1)
    (a : Set.Ici (Q.activationStage hkappa b x)) :
    Q.preferred hkappa a.1 =
      some (Q.starvingTask hkappa x hnever a).2.1 := by
  rw [Q.preferred_eq_chooseTask_map hkappa a.1,
    Q.chooseTask_starvingTask hkappa x hnever a]
  rfl

theorem starvingTask_coordinate_priority
    (Q : CausalRowRule kappa X) (hkappa : aleph0 <= kappa)
    {b : RegularCardinal.Stage kappa}
    (x : (Q.state hkappa b).row)
    (hnever : ∀ c, Q.preferred hkappa c ≠ some x.1)
    (a : Set.Ici (Q.activationStage hkappa b x)) :
    RowSystem.CoordinatePriority
      (Q.earlierTaskCoordinate hkappa
        (Q.starvingTask hkappa x hnever a))
      (Q.entryCoordinate hkappa b x) := by
  let s := Q.starvingTask hkappa x hnever a
  let t := Q.visibleTask hkappa x a.2
  have hs : Q.chooseTask hkappa a.1
      (fun c _hca => Q.state hkappa c) = some s :=
    Q.chooseTask_starvingTask hkappa x hnever a
  have ht : t ∈ Q.availableTasks hkappa
      (fun c _hca => Q.state hkappa c) :=
    Q.visibleTask_mem_available_of_never hkappa x a.2 hnever
  have hnotTS : ¬ Q.EarlierPriority hkappa t s :=
    Q.not_priority_chooseTask hkappa a.1 _ hs ht
  have hvalueNe : s.2.1 ≠ x.1 := by
    intro heq
    apply hnever a.1
    simpa [s, heq] using Q.preferred_starvingTask hkappa x hnever a
  change RowSystem.CoordinatePriority
    (Q.earlierTaskCoordinate hkappa s)
    (Q.earlierTaskCoordinate hkappa t)
  by_contra hnotST
  have hcoord := Std.Trichotomous.trichotomous
    (r := RowSystem.CoordinatePriority (kappa := kappa))
    (Q.earlierTaskCoordinate hkappa s)
    (Q.earlierTaskCoordinate hkappa t) hnotST hnotTS
  exact hvalueNe (Q.task_value_eq_of_coordinate_eq hkappa s t hcoord)

/-- Starvation embeds a full tail of stages into the bounded coordinate
predecessors of the starving entry. -/
noncomputable def starvationCoordinateEmbedding
    (Q : CausalRowRule kappa X) (hkappa : aleph0 <= kappa)
    {b : RegularCardinal.Stage kappa}
    (x : (Q.state hkappa b).row)
    (hnever : ∀ c, Q.preferred hkappa c ≠ some x.1) :
    Set.Ici (Q.activationStage hkappa b x) ↪
      {d : RegularCardinal.Stage kappa × RegularCardinal.Stage kappa //
        RowSystem.CoordinatePriority d (Q.entryCoordinate hkappa b x)} where
  toFun a := ⟨Q.earlierTaskCoordinate hkappa
      (Q.starvingTask hkappa x hnever a),
    Q.starvingTask_coordinate_priority hkappa x hnever a⟩
  inj' := by
    intro a d had
    apply Subtype.ext
    by_contra hne
    have hvalue :
        (Q.starvingTask hkappa x hnever a).2.1 =
          (Q.starvingTask hkappa x hnever d).2.1 :=
      Q.task_value_eq_of_coordinate_eq hkappa _ _
        (congrArg Subtype.val had)
    rcases lt_trichotomy a.1 d.1 with halt | heq | hdlt
    · exact (Q.preferred_ne_of_lt hkappa halt
        (Q.preferred_starvingTask hkappa x hnever a)) <| by
        simpa [hvalue] using Q.preferred_starvingTask hkappa x hnever d
    · exact hne heq
    · exact (Q.preferred_ne_of_lt hkappa hdlt
        (Q.preferred_starvingTask hkappa x hnever d)) <| by
        simpa [hvalue] using Q.preferred_starvingTask hkappa x hnever a

/-- Every entry ever generated by a causal bounded row rule is eventually
emitted. -/
theorem exists_preferred_eq_some_of_mem_state_row
    (Q : CausalRowRule kappa X) (hkappa : kappa.IsRegular)
    (hkappaUncountable : aleph0 < kappa)
    {b : RegularCardinal.Stage kappa} {x : X}
    (hx : x ∈ (Q.state hkappa.aleph0_le b).row) :
    ∃ a, Q.preferred hkappa.aleph0_le a = some x := by
  let xs : (Q.state hkappa.aleph0_le b).row := ⟨x, hx⟩
  by_contra hstarves
  push Not at hstarves
  let a0 := Q.activationStage hkappa.aleph0_le b xs
  letI : Nonempty (RegularCardinal.Stage kappa) := ⟨a0⟩
  have htailStat : Stationary.IsStationaryBelow kappa (Set.Ici a0) :=
    (Stationary.isClub_Ici a0).isStationary
      (RegularCardinal.cof_stage_ne_aleph0 hkappa hkappaUncountable)
  have htailCard : #(Set.Ici a0) = Cardinal.lift.{u + 1, u} kappa :=
    Stationary.mk_eq_lift_of_isStationaryBelow hkappa htailStat
  change #(Set.Ici (Q.activationStage hkappa.aleph0_le b xs)) =
    Cardinal.lift.{u + 1, u} kappa at htailCard
  have hinj := Cardinal.mk_le_of_injective
    (Q.starvationCoordinateEmbedding hkappa.aleph0_le xs
      hstarves).injective
  have hsmall := mk_coordinatePredecessors_lt hkappa.aleph0_le
    (Q.entryCoordinate hkappa.aleph0_le b xs)
  have hinj' :
      Cardinal.lift.{u + 1, u} kappa ≤
        #({d : RegularCardinal.Stage kappa ×
            RegularCardinal.Stage kappa //
          RowSystem.CoordinatePriority d
            (Q.entryCoordinate hkappa.aleph0_le b xs)}) := by
    simpa only [htailCard] using hinj
  exact (not_lt_of_ge hinj') hsmall

theorem exists_preferred_eq_some_of_mem_carrier
    (Q : CausalRowRule kappa X) (hkappa : kappa.IsRegular)
    (hkappaUncountable : aleph0 < kappa) {x : X}
    (hx : x ∈ (Q.rowSystem hkappa.aleph0_le).carrier) :
    ∃ a, Q.preferred hkappa.aleph0_le a = some x := by
  obtain ⟨b, hxb⟩ := RowSystem.mem_carrier.mp hx
  exact Q.exists_preferred_eq_some_of_mem_state_row
    hkappa hkappaUncountable hxb

end CausalRowRule

/-! ## The graph-specific causal rows of (9.13a) -/

namespace CausalRegular

variable {V : Type u}

/-! ### Cycle-free row-registration primitives

These are the three small facts about the old linkage and a causal ladder
prefix needed while the rows themselves are being constructed.  They live in
this upstream module rather than `RegularExtension`: the latter consumes the
completed row system, so importing it here would create a genuine module
cycle. -/

/-- Paths of `F` whose support meets `S`, in the cardinal-estimate form used
by `DWeb.mk_pathsMeeting_le`. -/
def rowPathsMeeting (G : DWeb V) (F : Set G.DPath) (S : Set V) : Set G.DPath :=
  {p | p ∈ F ∧ ¬ Disjoint p.support S}

/-- The vertices registered by the old linkage and one causal ladder prefix. -/
def twoWarpRowRegistration (G : DWeb V) (F Y : Set G.DPath)
    (S : Set V) : Set V :=
  G.vertexSet (rowPathsMeeting G F S) ∪
    G.vertexSet (rowPathsMeeting G Y S)

/-- The vertices of all members of a warp meeting a bounded set still have
cardinality at most the same infinite cardinal. -/
theorem mk_vertexSet_rowPathsMeeting_le
    (G : DWeb V) {F : Set G.DPath} {S : Set V} {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hF : G.IsWarp F) (hS : #S ≤ kappa) :
    #(G.vertexSet (rowPathsMeeting G F S)) ≤ kappa := by
  have hpaths : #(rowPathsMeeting G F S) ≤ kappa :=
    (G.mk_pathsMeeting_le F S hF).trans hS
  by_cases hnonempty : (rowPathsMeeting G F S).Nonempty
  · letI : Nonempty (rowPathsMeeting G F S) := hnonempty.to_subtype
    have heq : G.vertexSet (rowPathsMeeting G F S) =
        ⋃ p : rowPathsMeeting G F S, p.1.support := by
      ext x
      simp only [DWeb.vertexSet, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨p, hp, hxp⟩
        exact ⟨⟨p, hp⟩, hxp⟩
      · rintro ⟨p, hxp⟩
        exact ⟨p.1, p.2, hxp⟩
    rw [heq]
    refine (Cardinal.mk_iUnion_le
      (fun p : rowPathsMeeting G F S => p.1.support)).trans ?_
    apply Cardinal.mul_le_of_le hkappa hpaths
    apply ciSup_le
    intro p
    exact p.1.support_countable.le_aleph0.trans hkappa
  · have hempty : rowPathsMeeting G F S = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty, DWeb.vertexSet]
    simp

/-- Both registration contributions preserve the row bound. -/
theorem mk_twoWarpRowRegistration_le
    (G : DWeb V) {F Y : Set G.DPath} {S : Set V}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hF : G.IsWarp F) (hY : G.IsWarp Y) (hS : #S ≤ kappa) :
    #(twoWarpRowRegistration G F Y S) ≤ kappa := by
  apply (Cardinal.mk_union_le _ _).trans
  exact Cardinal.add_le_of_le hkappa
    (mk_vertexSet_rowPathsMeeting_le G hkappa hF hS)
    (mk_vertexSet_rowPathsMeeting_le G hkappa hY hS)

/-- Every ordinary-stage prefix of the normalized canonical ladder is a
warp. -/
theorem canonicalLadderCore_warpAt_isWarp_of_normalized
    (G : DWeb V) (hG : G.IsNormalized) (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V) (a : Ladder.Stage kappa) :
    G.IsWarp ((G.canonicalLadderCore kappa preferred).warpAt a) := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hgeometry := DWeb.KappaLadder.canonicalLadder_geometry
    (G := G) preferred hNoEnter
  exact hgeometry.warpStages (Ladder.Stage.toExtended a)

/-- Row family visible to the construction at stage `a`, extended by empty
rows at the present and future stages. -/
def priorRows {kappa : Cardinal.{u}} (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V) :
    RegularCardinal.Stage kappa -> Set V :=
  fun b => if hba : b < a then (prior b hba).row else ∅

theorem priorRows_mk_le {kappa : Cardinal.{u}}
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V) :
    ∀ b, #(priorRows a prior b) <= kappa := by
  intro b
  by_cases hba : b < a
  · simpa only [priorRows, dif_pos hba] using (prior b hba).row_mk_le
  · simp [priorRows, hba]

/-- Canonical diagonal enumeration of the rows already born before `a`. -/
noncomputable def priorEnumeration {kappa : Cardinal.{u}}
    (hkappa : aleph0 <= kappa) (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V) :
    RegularCardinal.Stage kappa -> RegularCardinal.Stage kappa -> Option V :=
  fun theta gamma => if htheta : theta < a then
    RegularCardinal.enumerateAlong
      ((prior theta htheta).rowEmbedding hkappa) gamma
  else none

/-- Stable enumeration of each actual causal row, using the embedding
stored by that row state rather than recomputing it from a whole family. -/
noncomputable def actualEnumeration {kappa : Cardinal.{u}}
    (Q : CausalRowRule kappa V) (hkappa : aleph0 <= kappa) :
    RegularCardinal.Stage kappa -> RegularCardinal.Stage kappa -> Option V :=
  fun theta => RegularCardinal.enumerateAlong
    ((Q.state hkappa theta).rowEmbedding hkappa)

/-- Schedule obtained from the actual strict-prior states and padded by
`none`; this definition is independent of the row rule being constructed. -/
def preferredOfPrior {kappa : Cardinal.{u}}
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V) :
    RegularCardinal.Stage kappa -> Option V :=
  fun b => if hba : b < a then (prior b hba).chosen else none

/-- Canonical ladder prefix available while the row at `a` is born. -/
noncomputable def priorLadder (G : DWeb V) {kappa : Cardinal.{u}}
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V) : G.KappaLadder kappa :=
  G.canonicalLadderCore kappa (preferredOfPrior a prior)

/-- Source request table built only from prior rows and the current ladder
prefix. -/
noncomputable def priorRequest (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : aleph0 <= kappa) (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V) :
    RegularCardinal.Stage kappa -> RegularCardinal.Stage kappa -> Set V :=
  ControlledSlices.diagonalRequest (priorLadder G a prior).frontier
    (priorEnumeration hkappa a prior)

/-- Pair-owned registration in (9.13a): close the earlier row under the
fixed old linkage and current ladder warp, and pre-register the canonical
half-way height set for the same row/request coordinate. -/
noncomputable def pairEntry (G : DWeb V) {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappaUncountable : aleph0 < kappa) (F : Set G.DPath)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V)
    (delta gamma : Set.Iio a) : Set V :=
  twoWarpRowRegistration G F
      ((priorLadder G a prior).warpAt gamma.1) (prior delta.1 delta.2).row ∪
    SliceCandidate.heightVerticesAt hlower hkappaUncountable
      (priorLadder G a prior)
      (priorRequest G hkappaUncountable.le a prior) delta.1 gamma.1

theorem mk_pairEntry_le (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V)
    (delta gamma : Set.Iio a) :
    #(pairEntry G hlower hkappaUncountable F a prior delta gamma) <=
      kappa := by
  have hY : G.IsWarp ((priorLadder G a prior).warpAt gamma.1) :=
    canonicalLadderCore_warpAt_isWarp_of_normalized
      G hG kappa (preferredOfPrior a prior) gamma.1
  have hclose :
      #(twoWarpRowRegistration G F
        ((priorLadder G a prior).warpAt gamma.1)
        (prior delta.1 delta.2).row) <= kappa :=
    mk_twoWarpRowRegistration_le G hkappa.aleph0_le
      hF hY (prior delta.1 delta.2).row_mk_le
  have hheight := SliceCandidate.mk_heightVerticesAt_le hlower
    hkappaUncountable (priorLadder G a prior)
      (priorRequest G hkappa.aleph0_le a prior)
      delta.1 gamma.1
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le hkappa.aleph0_le hclose hheight)

/-- Triple-owned candidate-maverick registration in (9.13a). -/
noncomputable def tripleEntry (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V)
    (delta beta gamma : Set.Iio a) : Set V :=
  SliceCandidate.candidateVerticesAt G (priorLadder G a prior)
    (priorRequest G hkappa a prior) delta.1 beta.1 gamma.1

theorem mk_tripleEntry_le (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a -> CausalState kappa V)
    (delta beta gamma : Set.Iio a) :
    #(tripleEntry G hkappa.aleph0_le a prior delta beta gamma) <= kappa :=
  SliceCandidate.mk_candidateVerticesAt_le hkappa
    (priorLadder G a prior) (priorRequest G hkappa.aleph0_le a prior)
      delta.1 beta.1 gamma.1

/-- The actual source-shaped causal row rule: base vertices, pair-owned
closure/height registrations, and triple-owned candidate mavericks. -/
noncomputable def rowRule (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base <= kappa) :
    CausalRowRule kappa V :=
  ofRegistrationTables hkappa.aleph0_le base hbase
    (pairEntry G hlower hkappaUncountable F)
    (tripleEntry G hkappa.aleph0_le)
    (mk_pairEntry_le G hkappa hkappaUncountable hG hlower F hF)
    (mk_tripleEntry_le G hkappa)

/-- The final request table associated with the rows and schedule produced
by one causal rule. -/
noncomputable def finalRequest (G : DWeb V) {kappa : Cardinal.{u}}
    (Q : CausalRowRule kappa V) (hkappa : aleph0 <= kappa) :
    RegularCardinal.Stage kappa -> RegularCardinal.Stage kappa -> Set V :=
  ControlledSlices.diagonalRequest
    (G.canonicalLadderCore kappa (Q.preferred hkappa)).frontier
    (actualEnumeration Q hkappa)

theorem priorEnumeration_eq_actual_of_lt
    {kappa : Cardinal.{u}} (Q : CausalRowRule kappa V)
    (hkappa : aleph0 <= kappa)
    {a theta : RegularCardinal.Stage kappa} (htheta : theta < a) :
    priorEnumeration hkappa a (fun b _hba => Q.state hkappa b) theta =
      actualEnumeration Q hkappa theta := by
  funext gamma
  simp only [priorEnumeration, actualEnumeration, dif_pos htheta]

end CausalRegular

/-! ## Prefix invariance of the canonical ladder recursion -/

namespace LadderPrefix

variable {V : Type u} (G : DWeb V)

/-- The accumulated state at ordinal `a` depends only on preferences at
strictly earlier ordinals.  This is the technical bridge allowing a causal
row rule to inspect a schedule truncated at its current stage. -/
theorem ladderAccumulatedStateAux_congr_prefix
    (p q : Ordinal.{u} -> Option V) :
    ∀ a : Ordinal.{u}, (∀ b, b < a -> p b = q b) ->
      G.ladderAccumulatedStateAux (G.ladderSuccessorState p) a =
        G.ladderAccumulatedStateAux (G.ladderSuccessorState q) a := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero =>
      intro _h
      simp [DWeb.ladderAccumulatedStateAux]
  | add_one a ih =>
      intro h
      have hpref : p a = q a := h a (lt_add_one a)
      have hprior :
          G.ladderAccumulatedStateAux (G.ladderSuccessorState p) a =
            G.ladderAccumulatedStateAux (G.ladderSuccessorState q) a :=
        ih (fun b hb => h b (hb.trans (lt_add_one a)))
      unfold DWeb.ladderAccumulatedStateAux at hprior
      simp only [DWeb.ladderAccumulatedStateAux,
        Ordinal.limitRecOn_add_one]
      rw [hprior]
      unfold DWeb.ladderSuccessorState
      rw [hpref]
  | limit a ha ih =>
      intro h
      rw [DWeb.ladderAccumulatedStateAux,
        Ordinal.limitRecOn_limit _ _ _ _ ha,
        DWeb.ladderAccumulatedStateAux,
        Ordinal.limitRecOn_limit _ _ _ _ ha]
      apply congrArg (G.ladderLimitState a ha)
      funext b hb
      exact ih b hb (fun c hc => h c (hc.trans hb))

/-- Stage-valued schedules agreeing below `a` give the same canonical
accumulated state at `a`. -/
theorem canonicalLadderState_eq_of_forall_lt
    {kappa : Cardinal.{u}}
    (p q : RegularCardinal.Stage kappa -> Option V)
    (a : RegularCardinal.Stage kappa)
    (h : ∀ b, b < a -> p b = q b) :
    G.canonicalLadderState kappa p (Ladder.Stage.toExtended a) =
      G.canonicalLadderState kappa q (Ladder.Stage.toExtended a) := by
  apply ladderAccumulatedStateAux_congr_prefix G
  intro b hb
  have hbk : b < kappa.ord := hb.trans a.2
  simpa only [DWeb.extendLadderPreference, dif_pos hbk] using
    h ⟨b, hbk⟩ hb

/-- Consequently the whole accumulated warp at stage `a` is prefix
invariant. -/
theorem canonicalLadderCore_warpAt_eq_of_forall_lt
    {kappa : Cardinal.{u}}
    (p q : RegularCardinal.Stage kappa -> Option V)
    (a : RegularCardinal.Stage kappa)
    (h : ∀ b, b < a -> p b = q b) :
    (G.canonicalLadderCore kappa p).warpAt a =
      (G.canonicalLadderCore kappa q).warpAt a := by
  exact congrArg Prod.fst
    (canonicalLadderState_eq_of_forall_lt G p q a h)

theorem canonicalLadderCore_frontier_eq_of_forall_lt
    {kappa : Cardinal.{u}}
    (p q : RegularCardinal.Stage kappa -> Option V)
    (a : RegularCardinal.Stage kappa)
    (h : ∀ b, b < a -> p b = q b) :
    (G.canonicalLadderCore kappa p).frontier a =
      (G.canonicalLadderCore kappa q).frontier a := by
  unfold DWeb.KappaLadder.frontier DWeb.KappaLadder.stageWeb
  rw [canonicalLadderCore_warpAt_eq_of_forall_lt G p q a h]

theorem canonicalLadderCore_upperRegion_eq_of_forall_lt
    {kappa : Cardinal.{u}}
    (p q : RegularCardinal.Stage kappa -> Option V)
    (a : RegularCardinal.Stage kappa)
    (h : ∀ b, b < a -> p b = q b) :
    (G.canonicalLadderCore kappa p).upperRegion a =
      (G.canonicalLadderCore kappa q).upperRegion a := by
  unfold DWeb.KappaLadder.upperRegion
  rw [canonicalLadderCore_frontier_eq_of_forall_lt G p q a h]

theorem canonicalLadderCore_lowerRegion_eq_of_forall_lt
    {kappa : Cardinal.{u}}
    (p q : RegularCardinal.Stage kappa -> Option V)
    (a : RegularCardinal.Stage kappa)
    (h : ∀ b, b < a -> p b = q b) :
    (G.canonicalLadderCore kappa p).lowerRegion a =
      (G.canonicalLadderCore kappa q).lowerRegion a := by
  unfold DWeb.KappaLadder.lowerRegion
  rw [canonicalLadderCore_frontier_eq_of_forall_lt G p q a h]

/-- Specialized prefix bridge for the actual joint causal recursion.  A
row born at `a` may compute with the ladder driven by `priorPreferred`; its
stage-`a` accumulated warp is exactly the one in the final causal ladder. -/
theorem canonicalLadderCore_priorPreferred_warpAt
    {kappa : Cardinal.{u}} (Q : CausalRowRule kappa V)
    (hkappa : aleph0 <= kappa) (a : RegularCardinal.Stage kappa) :
    (G.canonicalLadderCore kappa
      (Q.priorPreferred a (fun b _hba => Q.state hkappa b))).warpAt a =
      (G.canonicalLadderCore kappa (Q.preferred hkappa)).warpAt a := by
  apply canonicalLadderCore_warpAt_eq_of_forall_lt G
  intro b hba
  exact Q.priorPreferred_eq_preferred_of_lt hkappa hba

end LadderPrefix

/-! ## Connection to a preferred-marker capture API -/

/-- The exact interface supplied by a preferred-marker construction: every
request made at a stage is captured by the designated final set.  Keeping
this interface graph-independent lets `RegularRows` compile before the
ladder geometry; `LadderSchedule` instantiates it with the limiting roof. -/
def CapturesPreferred (preferred : RegularCardinal.Stage kappa -> Option X)
    (captured : Set X) : Prop :=
  ∀ a x, preferred a = some x -> x ∈ captured

/-- Source Assertion 9.14 from the preferred-marker capture API. -/
theorem RowSystem.carrier_subset_of_capturesPreferred
    (R : RowSystem kappa X) (hkappa : aleph0 <= kappa)
    {captured : Set X}
    (hcapture : CapturesPreferred (R.preferred hkappa) captured) :
    R.carrier ⊆ captured := by
  intro x hx
  obtain ⟨a, ha⟩ := R.exists_preferred_eq_some hkappa hx
  exact hcapture a x ha

/-- Row-local form of preferred-stream capture. -/
theorem RowSystem.row_subset_of_capturesPreferred
    (R : RowSystem kappa X) (hkappa : aleph0 <= kappa)
    {captured : Set X}
    (hcapture : CapturesPreferred (R.preferred hkappa) captured)
    (a : RegularCardinal.Stage kappa) :
    R.row a ⊆ captured :=
  (R.row_subset_carrier a).trans
    (R.carrier_subset_of_capturesPreferred hkappa hcapture)

/-! ## Static connection to the bookkeeping-installed canonical ladder -/

namespace LadderCapture

variable {V : Type u} (G : DWeb V)

/-- The canonical ladder's total preferred-request theorem instantiates the
graph-independent capture interface.  Legality belongs to the core after
installing the independent valid bookkeeping; the limiting roof is unchanged
by that installation. -/
theorem capturesPreferred_limitRoof
    (R : RowSystem kappa V) (hkappa : aleph0 <= kappa)
    (hG : G.IsNormalized)
    (hL : (G.canonicalLadderCore kappa
      (R.preferred hkappa)).withValidBookkeeping.IsLegal) :
    CapturesPreferred (R.preferred hkappa)
      (G.canonicalLadderCore kappa (R.preferred hkappa)).limitRoof := by
  intro a x hax
  let b : Ladder.Stage kappa :=
    ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hkappa).succ_lt a.2⟩
  exact DWeb.KappaLadder.canonicalLadderCore_preferred_mem_limitRoof
    (R.preferred hkappa) hG hL a b rfl hax

/-- Static-row form of Assertion 9.14.  The causal joint construction below
is the version used when the rows themselves depend on earlier ladder
stages. -/
theorem carrier_subset_limitRoof
    (R : RowSystem kappa V) (hkappa : aleph0 <= kappa)
    (hG : G.IsNormalized)
    (hL : (G.canonicalLadderCore kappa
      (R.preferred hkappa)).withValidBookkeeping.IsLegal) :
    R.carrier ⊆
      (G.canonicalLadderCore kappa (R.preferred hkappa)).limitRoof :=
  R.carrier_subset_of_capturesPreferred hkappa
    (capturesPreferred_limitRoof G R hkappa hG hL)

/-- The canonical ladder captures every request made by the causal fair
row scheduler. -/
theorem capturesFairPreferred_limitRoof
    (R : RowSystem kappa V) (hkappa : aleph0 <= kappa)
    (hG : G.IsNormalized)
    (hL : (G.canonicalLadderCore kappa
      R.fairPreferred).withValidBookkeeping.IsLegal) :
    CapturesPreferred R.fairPreferred
      (G.canonicalLadderCore kappa R.fairPreferred).limitRoof := by
  intro a x hax
  let b : Ladder.Stage kappa :=
    ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hkappa).succ_lt a.2⟩
  exact DWeb.KappaLadder.canonicalLadderCore_preferred_mem_limitRoof
    R.fairPreferred hG hL a b rfl hax

/-- Causal form of Assertion 9.14.  Each row entry is eventually emitted by
the fair scheduler and therefore belongs to the limiting roof. -/
theorem carrier_subset_limitRoof_fair
    (R : RowSystem kappa V) (hkappa : kappa.IsRegular)
    (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hL : (G.canonicalLadderCore kappa
      R.fairPreferred).withValidBookkeeping.IsLegal) :
    R.carrier ⊆
      (G.canonicalLadderCore kappa R.fairPreferred).limitRoof := by
  intro x hx
  obtain ⟨a, ha⟩ := R.exists_fairPreferred_eq_some hkappa
    hkappaUncountable hx
  exact capturesFairPreferred_limitRoof G R hkappa.aleph0_le hG hL a x ha

/-- Preferred requests from the joint causal row recursion are captured by
the canonical ladder. -/
theorem capturesCausalPreferred_limitRoof
    (Q : CausalRowRule kappa V) (hkappa : aleph0 <= kappa)
    (hG : G.IsNormalized)
    (hL : (G.canonicalLadderCore kappa
      (Q.preferred hkappa)).withValidBookkeeping.IsLegal) :
    CapturesPreferred (Q.preferred hkappa)
      (G.canonicalLadderCore kappa (Q.preferred hkappa)).limitRoof := by
  intro a x hax
  let b : Ladder.Stage kappa :=
    ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hkappa).succ_lt a.2⟩
  exact DWeb.KappaLadder.canonicalLadderCore_preferred_mem_limitRoof
    (Q.preferred hkappa) hG hL a b rfl hax

/-- Source-faithful causal form of (9.14): even when each row is generated
from earlier recursion states, the complete row union is contained in the
limiting roof. -/
theorem causalCarrier_subset_limitRoof
    (Q : CausalRowRule kappa V) (hkappa : kappa.IsRegular)
    (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hL : (G.canonicalLadderCore kappa
      (Q.preferred hkappa.aleph0_le)).withValidBookkeeping.IsLegal) :
    (Q.rowSystem hkappa.aleph0_le).carrier ⊆
      (G.canonicalLadderCore kappa
        (Q.preferred hkappa.aleph0_le)).limitRoof := by
  intro x hx
  obtain ⟨a, ha⟩ := Q.exists_preferred_eq_some_of_mem_carrier
    hkappa hkappaUncountable hx
  exact capturesCausalPreferred_limitRoof G Q hkappa.aleph0_le hG hL a x ha

end LadderCapture

end RegularRows
end CardinalInduction
end Erdos599
