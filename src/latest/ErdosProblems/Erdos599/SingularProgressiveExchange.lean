/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularInitialSplitRow

/-!
# The exact progressive exchange needed in the singular matrix

Assertion 9.17 does not need a successor operation on arbitrary path rows.
It needs a successor only on rows carrying the split stop-over geometry
produced by the preceding step.  This file gives that requirement a precise,
non-circular interface.

For one column, the lower induction hypothesis always supplies a half-way
linkage in the quotient by the current boundary.  The genuinely missing
exchange statement is that one can choose such a quotient linkage together
with an ambient row which

* forward-extends the whole displayed old row,
* links the competitor-closed next source set to the target, and
* again carries a split stop-over.

The theorem at the end proves that columnwise instances of exactly this
exchange assemble, by ordinary choice, into the full omega target-row
machine.  Thus no simultaneous or fixed-point assumption remains hidden in
the recursion machinery itself.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProgressiveExchange

open SingularExtension SingularMatrix SingularBoundarySplit
  SingularTargetRowMachine SingularInitialSplitRow

universe u

variable {V : Type u}

/-- A row state together with the source-size invariants which are needed to
apply the lower-cardinal half-way clause at its successor. -/
structure ProgressiveState (G : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular) where
  splitRow : SplitTargetRowStage G (Index kappa)
  sources_subset : ∀ i, splitRow.row.sources i ⊆ G.source
  sources_card : ∀ i,
    #(splitRow.row.sources i) = scale kappa hkappa hsingular i

namespace ProgressiveState

abbrev row {G : DWeb V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    (S : ProgressiveState G kappa hkappa hsingular) :
    TargetRowStage G (Index kappa) :=
  S.splitRow.row

abbrev split {G : DWeb V} {kappa : Cardinal.{u}}
    {hkappa : aleph0 < kappa} {hsingular : kappa.IsSingular}
    (S : ProgressiveState G kappa hkappa hsingular) (i : Index kappa) :
    SplitStopover G (S.row.paths i) :=
  S.splitRow.split i

end ProgressiveState

/-- The output which the omitted sentence in Assertion 9.17 must construct
for one column.  The quotient witness is recorded explicitly, so this is
strictly sharper than merely postulating the next target row. -/
structure ColumnExchange
    (G : DWeb V) (fixed : Set G.DPath)
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (S : ProgressiveState G kappa hkappa hsingular)
    (i : Index kappa) where
  quotientPaths : Set (G.quotient (S.split i).boundary).DPath
  quotientHalfway : IsHalfwayLinkageOfAltitude
    (G.quotient (S.split i).boundary)
    (requestedFrontier G (S.row.paths i)
      (nextTargetSources G fixed S.row i))
    (scale kappa hkappa hsingular i) quotientPaths
  paths : Set G.DPath
  isWarp : G.IsWarp paths
  finiteCharacter : G.HasFiniteCharacter paths
  initialSet : G.initialSet paths = G.source
  links : LinksToTarget G paths (nextTargetSources G fixed S.row i)
  split : SplitStopover G paths
  forward : G.ForwardExtension (S.row.paths i) paths

/-- The exact selection theorem still required by the strict-large singular
case.  Choices for different columns need not be mutually disjoint: the
matrix limit uses them as separate warps. -/
def ProgressiveExchangeRule
    (G : DWeb V) (fixed : Set G.DPath)
    (kappa : Cardinal.{u}) (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular) : Prop :=
  ∀ (S : ProgressiveState G kappa hkappa hsingular) (i : Index kappa),
    Nonempty (ColumnExchange G fixed S i)

/-- Independently of the exchange problem, the lower induction hypothesis
does produce the quotient half-way object occurring in `ColumnExchange`.
This pins the remaining gap on ambient forward re-entry, rather than on
cardinal bookkeeping or availability of a lower witness. -/
theorem exists_quotientHalfway
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (S : ProgressiveState G kappa hkappa hsingular)
    (i : Index kappa) :
    ∃ U : Set (G.quotient (S.split i).boundary).DPath,
      IsHalfwayLinkageOfAltitude
        (G.quotient (S.split i).boundary)
        (requestedFrontier G (S.row.paths i)
          (nextTargetSources G fixed S.row i))
        (scale kappa hkappa hsingular i) U := by
  exact exists_quotientHalfwayForNext_split hlower hkappa hsingular
    hfixedWarp hfixedInitial S.row
    (fun j ↦ ⟨S.sources_subset j, S.sources_card j⟩)
    S.split i

/-- Choose the next state from columnwise progressive exchanges. -/
noncomputable def nextState
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hexchange : ProgressiveExchangeRule G fixed kappa hkappa hsingular)
    (S : ProgressiveState G kappa hkappa hsingular) :
    ProgressiveState G kappa hkappa hsingular := by
  let E : ∀ i : Index kappa, ColumnExchange G fixed S i :=
    fun i ↦ Classical.choice (hexchange S i)
  let R : TargetRowStage G (Index kappa) :=
    { sources := nextTargetSources G fixed S.row
      paths := fun i ↦ (E i).paths
      isWarp := fun i ↦ (E i).isWarp
      finiteCharacter := fun i ↦ (E i).finiteCharacter
      initialSet := fun i ↦ (E i).initialSet
      links := fun i ↦ (E i).links }
  let T : SplitTargetRowStage G (Index kappa) :=
    { row := R
      split := fun i ↦ (E i).split }
  refine
    { splitRow := T
      sources_subset := ?_
      sources_card := ?_ }
  · intro i
    exact nextTargetSources_subset_source hfixedInitial S.row
      S.sources_subset i
  · intro i
    exact mk_nextTargetSources_eq hfixedWarp S.row
      (scale_infinite kappa hkappa hsingular i)
      (scale_index_le kappa hkappa hsingular i) i
      (S.sources_card i)

@[simp] theorem nextState_sources
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hexchange : ProgressiveExchangeRule G fixed kappa hkappa hsingular)
    (S : ProgressiveState G kappa hkappa hsingular) :
    (nextState hfixedWarp hfixedInitial hexchange S).row.sources =
      nextTargetSources G fixed S.row := by
  rfl

theorem forward_nextState
    {G : DWeb V} {fixed : Set G.DPath}
    {kappa : Cardinal.{u}} {hkappa : aleph0 < kappa}
    {hsingular : kappa.IsSingular}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hexchange : ProgressiveExchangeRule G fixed kappa hkappa hsingular)
    (S : ProgressiveState G kappa hkappa hsingular) (i : Index kappa) :
    G.ForwardExtension (S.row.paths i)
      ((nextState hfixedWarp hfixedInitial hexchange S).row.paths i) := by
  exact (Classical.choice (hexchange S i)).forward

/-- The initial split row carries the exact scale invariants required by
`ProgressiveState`. -/
theorem exists_initialState
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa) :
    ∃ S : ProgressiveState G kappa hkappa hsingular,
      S.row.sources = sourceLayer A₀ kappa hcard hkappa hsingular := by
  obtain ⟨T, hT⟩ := exists_initialSplitTargetRowStage
    hlower hkappa hsingular hG hNorm hA₀ hcard
  refine ⟨{
    splitRow := T
    sources_subset := ?_
    sources_card := ?_
  }, hT⟩
  · intro i
    rw [hT]
    exact (sourceLayer_subset A₀ kappa hcard hkappa hsingular i).trans hA₀
  · intro i
    rw [hT]
    exact sourceLayer_card A₀ kappa hcard hkappa hsingular i

/-- Columnwise progressive exchange is sufficient for the complete private
state machine consumed by Assertion 9.18. -/
noncomputable def targetRowMachine
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hexchange : ProgressiveExchangeRule G fixed kappa hkappa hsingular) :
    TargetRowMachine G fixed
      (sourceLayer A₀ kappa hcard hkappa hsingular) := by
  let S₀ : ProgressiveState G kappa hkappa hsingular :=
    Classical.choose
      (exists_initialState hlower hkappa hsingular hG hNorm hA₀ hcard)
  have hS₀ : S₀.row.sources =
      sourceLayer A₀ kappa hcard hkappa hsingular :=
    Classical.choose_spec
      (exists_initialState hlower hkappa hsingular hG hNorm hA₀ hcard)
  exact
    { State := ProgressiveState G kappa hkappa hsingular
      row := ProgressiveState.row
      initial := S₀
      next := nextState hfixedWarp hfixedInitial hexchange
      sources_initial := hS₀
      sources_next := nextState_sources hfixedWarp hfixedInitial hexchange
      forward_next := forward_nextState hfixedWarp hfixedInitial hexchange }

/-- After the exchange theorem is supplied, the already proved direct-limit
machinery gives the exact target rows of the singular construction. -/
noncomputable def targetRows
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ : Set V} (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (hexchange : ProgressiveExchangeRule G fixed kappa hkappa hsingular) :
    TargetRows G fixed A₀ kappa hkappa hsingular hcard :=
  (targetRowMachine hlower hkappa hsingular hG hNorm hA₀ hcard
    hfixedWarp hfixedInitial hexchange).toTargetRows

#print axioms exists_quotientHalfway
#print axioms targetRowMachine

end SingularProgressiveExchange
end CardinalInduction
end Erdos599
