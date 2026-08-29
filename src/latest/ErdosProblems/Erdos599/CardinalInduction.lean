/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Normalization
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Erdős Problem 599: cardinal bookkeeping for the linkability induction

This file contains the cardinal and ordinal part of Section 9 of
Aharoni--Berger.  The graph-theoretic definitions and the two simultaneous
induction clauses are added below these lemmas once the concrete web, ladder,
safe-link, and alternating-path interfaces are available.

The central bookkeeping points already recorded here are:

* a union of at most `κ` sets of size at most `κ` again has size at most
  `κ`, for infinite `κ`;
* the supremum of at most `κ` ordinals below `(κ⁺).ord` is still below
  `(κ⁺).ord`;
* an ordinal below `(κ⁺).ord` has cardinality at most `κ`;
* the source's exact two-branch definition of a hammock being "maximal up
  to `ρ`".
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction

universe u v

/-! ## Cardinal bounds used by the regular and blueprint constructions -/

/-- A union of at most `κ` sets, each of cardinality at most `κ`, has
cardinality at most `κ`, provided `κ` is infinite.  This is the estimate
used at every closing-up stage in Section 9. -/
theorem mk_iUnion_le_of_le {I X : Type u} [Nonempty I]
    {f : I → Set X} {κ : Cardinal}
    (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) (hf : ∀ i, #(f i) ≤ κ) :
    #( ⋃ i, f i) ≤ κ := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  apply Cardinal.mul_le_of_le hκ hI
  exact ciSup_le hf

/-- Lifted-universe version of `mk_iUnion_le_of_le`. -/
theorem lift_mk_iUnion_le_of_le {I : Type u} {X : Type v} [Nonempty I]
    {f : I → Set X}
    {κ : Cardinal.{max u v}} (hκ : ℵ₀ ≤ κ)
    (hI : Cardinal.lift.{v} #I ≤ κ)
    (hf : ∀ i, Cardinal.lift.{u} #(f i) ≤ κ) :
    Cardinal.lift.{u} #( ⋃ i, f i) ≤ κ := by
  refine (Cardinal.mk_iUnion_le_lift f).trans ?_
  apply Cardinal.mul_le_of_le hκ hI
  exact ciSup_le hf

/-- The union of an increasing sequence indexed by a type of size at most
`κ` has size at most `κ` when each stage does.  Monotonicity is retained in
the interface because downstream uses also need it, although the cardinal
estimate itself does not require it. -/
theorem mk_iUnion_monotone_le {I X : Type u} [Preorder I] [Nonempty I]
    {f : I → Set X} {κ : Cardinal} (_hfmono : Monotone f)
    (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) (hf : ∀ i, #(f i) ≤ κ) :
    #( ⋃ i, f i) ≤ κ :=
  mk_iUnion_le_of_le hκ hI hf

/-- A family indexed by fewer than a regular cardinal, all of whose members
have size below that cardinal, has union of size below the cardinal. -/
theorem mk_iUnion_lt_of_isRegular {I X : Type u} {f : I → Set X}
    {κ : Cardinal} (hκ : κ.IsRegular) (hI : #I < κ)
    (hf : ∀ i, #(f i) < κ) :
    #( ⋃ i, f i) < κ := by
  exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hκ hI).2 hf

/-- The successor-cardinal regularity estimate used when taking a limit of
`κ` many linkage blueprints. -/
theorem iSup_lt_succ_ord {I : Type u} {κ : Cardinal.{u}} {f : I → Ordinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ)
    (hf : ∀ i, f i < (succ κ).ord) :
    iSup f < (succ κ).ord := by
  apply Ordinal.iSup_lt_of_lt_cof
  · rw [(Cardinal.isRegular_succ hκ).cof_ord]
    exact hI.trans_lt (lt_succ κ)
  · exact hf

/-- Every ordinal below the initial ordinal of `κ⁺` has cardinality at most
`κ`.  This is the final altitude estimate in the proof of Theorem 9.2. -/
theorem card_le_of_lt_succ_ord {κ : Cardinal.{u}} {α : Ordinal.{u}}
    (hα : α < (succ κ).ord) :
    α.card ≤ κ := by
  exact Cardinal.card_le_iff.2 hα

/-! ## The exact hammock maximality predicate (Definition 9.21) -/

/-- `H` is maximal up to `ρ` among the sets satisfying `Good`.

The second branch is easy to misstate: `H` itself has cardinality exactly
`ρ`, while a *possibly different* good set of cardinality `ρ⁺` exists. -/
def MaximalUpTo {X : Type u} (Good : Set (Set X)) (ρ : Cardinal)
    (H : Set X) : Prop :=
  (H ∈ Good ∧ Maximal (fun K ↦ K ∈ Good) H ∧ #H ≤ ρ) ∨
    (H ∈ Good ∧ #H = ρ ∧ ∃ K ∈ Good, #K = succ ρ)

theorem MaximalUpTo.mem {X : Type u} {Good : Set (Set X)} {ρ : Cardinal}
    {H : Set X} (hH : MaximalUpTo Good ρ H) : H ∈ Good := by
  rcases hH with hH | hH
  · exact hH.1
  · exact hH.1

theorem MaximalUpTo.card_le {X : Type u} {Good : Set (Set X)} {ρ : Cardinal}
    {H : Set X} (hH : MaximalUpTo Good ρ H) : #H ≤ ρ := by
  rcases hH with hH | hH
  · exact hH.2.2
  · exact hH.2.1.le

/-- An inclusion-maximal good set of size at most `ρ` is maximal up to
`ρ` by the first branch. -/
theorem maximalUpTo_of_maximal {X : Type u} {Good : Set (Set X)}
    {ρ : Cardinal} {H : Set X} (hH : H ∈ Good)
    (hmax : Maximal (fun K ↦ K ∈ Good) H) (hcard : #H ≤ ρ) :
    MaximalUpTo Good ρ H :=
  Or.inl ⟨hH, hmax, hcard⟩

/-- A good set of size exactly `ρ`, in the presence of a good set of size
`ρ⁺`, is maximal up to `ρ` by the second branch. -/
theorem maximalUpTo_of_large {X : Type u} {Good : Set (Set X)}
    {ρ : Cardinal} {H K : Set X} (hH : H ∈ Good) (hHcard : #H = ρ)
    (hK : K ∈ Good) (hKcard : #K = succ ρ) :
    MaximalUpTo Good ρ H :=
  Or.inr ⟨hH, hHcard, K, hK, hKcard⟩

/-- If no good set has size `ρ⁺`, a set maximal up to `ρ` must actually
be inclusion-maximal. -/
theorem MaximalUpTo.maximal_of_no_large {X : Type u}
    {Good : Set (Set X)} {ρ : Cardinal} {H : Set X}
    (hH : MaximalUpTo Good ρ H)
    (hlarge : ∀ K ∈ Good, #K ≠ succ ρ) :
    Maximal (fun K ↦ K ∈ Good) H := by
  rcases hH with hH | hH
  · exact hH.2.1
  · exact False.elim (hlarge hH.2.2.choose hH.2.2.choose_spec.1
      hH.2.2.choose_spec.2)

/-- A maximal-up-to set of size strictly below `ρ` is genuinely maximal;
the large branch has cardinality exactly `ρ`. -/
theorem MaximalUpTo.maximal_of_card_lt {X : Type u}
    {Good : Set (Set X)} {ρ : Cardinal} {H : Set X}
    (hH : MaximalUpTo Good ρ H) (hcard : #H < ρ) :
    Maximal (fun K ↦ K ∈ Good) H := by
  rcases hH with hH | hH
  · exact hH.2.1
  · exact False.elim (hcard.ne hH.2.1)

/-- The Zorn-and-thinning argument behind Assertion 9.22.  Hammock
families satisfy `hthin` by taking subfamilies, while a union of an
inclusion chain of compatible hammocks supplies `hchain`. -/
theorem exists_maximalUpTo {X : Type u} {Good : Set (Set X)}
    (ρ : Cardinal.{u})
    (hchain : ∀ c ⊆ Good, IsChain (· ⊆ ·) c →
      ∃ ub ∈ Good, ∀ s ∈ c, s ⊆ ub)
    (hthin : ∀ K ∈ Good, ∀ {σ : Cardinal.{u}}, σ ≤ #K →
      ∃ H ∈ Good, #H = σ) :
    ∃ H : Set X, MaximalUpTo Good ρ H := by
  by_cases hlarge : ∃ K ∈ Good, succ ρ ≤ #K
  · obtain ⟨K, hK, hKcard⟩ := hlarge
    obtain ⟨H, hH, hHcard⟩ := hthin K hK ((le_succ ρ).trans hKcard)
    obtain ⟨L, hL, hLcard⟩ := hthin K hK hKcard
    exact ⟨H, maximalUpTo_of_large hH hHcard hL hLcard⟩
  · obtain ⟨M, hM⟩ := zorn_subset Good hchain
    refine ⟨M, maximalUpTo_of_maximal hM.1 hM ?_⟩
    by_contra hMcard
    exact hlarge ⟨M, hM.1, succ_le_of_lt (lt_of_not_ge hMcard)⟩

/-! ## Linkages, height, and half-way linkages (Definition 9.1) -/

open DirectedPath

variable {V : Type u}

/-- One finite `A`--`C` path in the source sense: it meets `A ∪ C` only
at its two endpoints and meets `A` only at its initial endpoint.  The latter
clause is the extra condition in "links `A` to `C`" which rules out a path
starting at one source and passing through another. -/
def IsPathBetween (Γ : DWeb V) (A C : Set V) (p : Γ.DPath) : Prop :=
  ∃ q : DirectedPath.FinitePath Γ.graph,
    p = .inl q ∧
      q.support ∩ (A ∪ C) = {q.start, q.finish} ∧
      q.support ∩ A = {q.start}

/-- A finite linkage from `A` to `C` in the graph of `Γ`.

Besides covering `A` and ending in `C`, every member satisfies the source's
definition of an `A`–`C` warp: it meets `A ∪ C` only at its endpoints.
The final `A`-intersection condition records the separate requirement that
the warp link `A` to `C`. -/
def IsLinkageBetween (Γ : DWeb V) (A C : Set V)
    (W : Set Γ.DPath) : Prop :=
  Γ.IsWarp W ∧ Γ.HasFiniteCharacter W ∧
    Γ.initialSet W = A ∧ Γ.terminalFrontier W ⊆ C ∧
      ∀ p ∈ W, IsPathBetween Γ A C p

/-- Linkability of the source of a concrete web to its target. -/
def IsLinkable (Γ : DWeb V) : Prop :=
  ∃ W : Set Γ.DPath, IsLinkageBetween Γ Γ.source Γ.target W

/-- A separator between `A` and the target of `Γ`. -/
def IsSeparatorFrom (Γ : DWeb V) (A C : Set V) : Prop :=
  A ⊆ Γ.roof C

/-- Literal inclusion-minimality among the separators between `A` and the
target.  This records the paper's stated wording in Definition 9.1. -/
def IsMinimalSeparatorFrom (Γ : DWeb V) (A C : Set V) : Prop :=
  Minimal (IsSeparatorFrom Γ A) C

/-- A trimmed separator: each member of `C` is essential for separating
`RF(C)` from the target.  By Definition 2.14 this is exactly `E(C) = C`. -/
def IsTrimmedSeparator (Γ : DWeb V) (C : Set V) : Prop :=
  Γ.essential C = C

/-- Every inclusion-minimal `A`--target separator is trimmed. -/
theorem IsMinimalSeparatorFrom.isTrimmed {Γ : DWeb V} {A C : Set V}
    (hC : IsMinimalSeparatorFrom Γ A C) : IsTrimmedSeparator Γ C := by
  apply Set.Subset.antisymm
  · exact Γ.essential_subset C
  · apply hC.2
    · rw [IsSeparatorFrom, Γ.roof_essential]
      exact hC.1
    · exact Γ.essential_subset C

/-- The suffix of a finite path beginning at `a` meets `B`.  The list
decomposition is the concrete version of the paper's notation `aP`. -/
def FinitePathSuffixMeets {D : Digraph V}
    (q : DirectedPath.FinitePath D) (a : V) (B : Set V) : Prop :=
  ∃ before after : List V,
    q.walk.support = before ++ a :: after ∧
      ∃ b ∈ B, b ∈ a :: after

/-- Source-faithful "`W` links `A₀` to `B`".  The selected component need
not start at `a`: it must meet `A₀` exactly at `a`, and its suffix from `a`
must meet `B`.  Half-way linkages have finite character, so a finite path
witness is the exact specialization needed here. -/
def LinksToTarget (Γ : DWeb V) (W : Set Γ.DPath) (A₀ : Set V) : Prop :=
  ∀ a ∈ A₀, ∃ p ∈ W,
    ∃ q : DirectedPath.FinitePath Γ.graph,
      p = .inl q ∧ q.support ∩ A₀ = {a} ∧
        FinitePathSuffixMeets q a Γ.target

/-- `X` witnesses a height bound for `Z`: it consists of non-source
vertices and, after quotienting by it, some wave has a terminal frontier
whose roof in the original web contains `Z`. -/
def IsHeightWitness (Γ : DWeb V) (Z X : Set V) : Prop :=
  X ⊆ Γ.sourceᶜ ∧
    ∃ W : Set (Γ.quotient X).DPath,
      (Γ.quotient X).IsWave W ∧
      Z ⊆ Γ.roof ((Γ.quotient X).terminalFrontier W)

/-- The cardinalities occurring among height witnesses. -/
def heightCandidates (Γ : DWeb V) (Z : Set V) : Set Cardinal.{u} :=
  { κ | ∃ X : Set V, IsHeightWitness Γ Z X ∧ #X = κ }

/-- Source Section 9 height.  All source uses come with a witness; under
that hypothesis `csInf_mem` below says this infimum is attained. -/
def height (Γ : DWeb V) (Z : Set V) : Cardinal.{u} :=
  sInf (heightCandidates Γ Z)

/-- The height of the web is the height of its whole vertex set. -/
def webHeight (Γ : DWeb V) : Cardinal.{u} :=
  height Γ Set.univ

/-- Bounded form of height, retaining the actual quotient witness needed
later in the construction. -/
def HeightAtMost (Γ : DWeb V) (Z : Set V) (κ : Cardinal.{u}) : Prop :=
  ∃ X : Set V, IsHeightWitness Γ Z X ∧ #X ≤ κ

theorem height_le_of_witness {Γ : DWeb V} {Z X : Set V}
    (hX : IsHeightWitness Γ Z X) : height Γ Z ≤ #X := by
  apply csInf_le'
  exact ⟨X, hX, rfl⟩

theorem height_mem_candidates {Γ : DWeb V} {Z : Set V}
    (hne : (heightCandidates Γ Z).Nonempty) :
    height Γ Z ∈ heightCandidates Γ Z :=
  csInf_mem hne

theorem exists_witness_of_candidates_nonempty {Γ : DWeb V} {Z : Set V}
    (hne : (heightCandidates Γ Z).Nonempty) :
    ∃ X : Set V, IsHeightWitness Γ Z X ∧ #X = height Γ Z :=
  height_mem_candidates hne

/-- The target roofs every vertex: every target path contains its terminal,
which belongs to the target. -/
theorem roof_target (Γ : DWeb V) : Γ.roof Γ.target = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v p hp
  exact ⟨p.finish, p.finish_mem_support, hp.2⟩

/-- The essential part of the whole vertex set is exactly the target.  This
elementary identity supplies a canonical height witness below. -/
theorem essential_univ (Γ : DWeb V) : Γ.essential Set.univ = Γ.target := by
  apply Set.Subset.antisymm
  · intro s hs
    obtain ⟨p, hp, hav⟩ :=
      (Γ.not_mem_roof_iff (Set.univ \ {s}) s).1 hs.2
    have hfinish : p.finish = s := by
      by_contra hne
      exact Set.disjoint_left.1 hav p.finish_mem_support
        ⟨Set.mem_univ _, by simpa⟩
    exact hfinish ▸ hp.2
  · intro s hs
    refine ⟨Set.mem_univ s,
      (Γ.not_mem_roof_iff (Set.univ \ {s}) s).2 ?_⟩
    let p : DirectedPath.FinitePath Γ.graph :=
      { start := s
        finish := s
        walk := .nil
        isPath := DirectedPath.Walk.isPath_nil s }
    refine ⟨p, ⟨rfl, hs⟩, ?_⟩
    apply Set.disjoint_left.2
    intro x hxp hx
    have hxs : x = s := by
      simpa [p, DirectedPath.FinitePath.support] using hxp
    exact hx.2 hxs

/-- Every set has at least one height witness.  Delete all non-source
vertices; the quotient source is the target, whose trivial wave has terminal
frontier the target, and the target roofs the whole original web. -/
theorem heightWitness_source_compl (Γ : DWeb V) (Z : Set V) :
    IsHeightWitness Γ Z Γ.sourceᶜ := by
  refine ⟨Set.Subset.rfl, (Γ.quotient Γ.sourceᶜ).trivialWave, ?_, ?_⟩
  · exact (Γ.quotient Γ.sourceᶜ).isWave_trivialWave
  · rw [(Γ.quotient Γ.sourceᶜ).terminalFrontier_trivialWave,
      DWeb.quotient_source, Set.union_compl_self, essential_univ,
      roof_target]
    exact Set.subset_univ Z

theorem heightCandidates_nonempty (Γ : DWeb V) (Z : Set V) :
    (heightCandidates Γ Z).Nonempty :=
  ⟨#(↑(Γ.sourceᶜ)), Γ.sourceᶜ, heightWitness_source_compl Γ Z, rfl⟩

/-- The minimum in the definition of height is always attained; no
nonemptiness side condition is needed. -/
theorem exists_height_witness (Γ : DWeb V) (Z : Set V) :
    ∃ X : Set V, IsHeightWitness Γ Z X ∧ #X = height Γ Z :=
  exists_witness_of_candidates_nonempty (heightCandidates_nonempty Γ Z)

theorem height_le_source_compl (Γ : DWeb V) (Z : Set V) :
    height Γ Z ≤ #(↑(Γ.sourceᶜ)) :=
  height_le_of_witness (heightWitness_source_compl Γ Z)

/-- A possible stop-over set certifying that `W` is a corrected half-way
linkage.

The paper literally asks that `C` be a globally inclusion-minimal
source--target separator.  Its simultaneous half-way clause is false under
that reading (a source with three private target leaves already gives the
finite obstruction, and disjoint stars give the infinite one).  The proof
only needs the trimmed condition `E(C) = C`, so this formalization makes that
repair explicit while retaining `IsMinimalSeparatorFrom` above for the
literal statement.  The final extension/linkability theorem does not assert
the false global-minimal auxiliary clause. -/
structure IsHalfwayStopover (Γ : DWeb V) (W : Set Γ.DPath)
    (C : Set V) : Prop where
  linkage : IsLinkageBetween Γ Γ.source C W
  /-- The repaired condition used in place of the paper's false global
  inclusion-minimality requirement. -/
  minimal : IsTrimmedSeparator Γ C
  quotient_unhindered : (Γ.quotient C).IsUnhindered

/-- The source-faithful stop-over invariant used internally by the
simultaneous induction.  Trimmedness and separation are independent: the
latter must be retained from the maximal-wave or scheduler construction,
not inferred from `IsHalfwayStopover`. -/
structure IsSeparatingHalfwayStopover (Γ : DWeb V)
    (W : Set Γ.DPath) (C : Set V) : Prop where
  stopover : IsHalfwayStopover Γ W C
  separator : IsSeparatorFrom Γ Γ.source C

namespace IsSeparatingHalfwayStopover

theorem linkage {Γ : DWeb V} {W : Set Γ.DPath} {C : Set V}
    (h : IsSeparatingHalfwayStopover Γ W C) :
    IsLinkageBetween Γ Γ.source C W :=
  h.stopover.linkage

end IsSeparatingHalfwayStopover

/-- The corrected half-way-linkage predicate used by the cardinal induction:
the stop-over is trimmed and its quotient is unhindered. -/
def IsHalfwayLinkage (Γ : DWeb V) (W : Set Γ.DPath) : Prop :=
  ∃ C : Set V, IsHalfwayStopover Γ W C

/-- Heights of all possible stop-over sets for a fixed half-way warp. -/
def halfwayStopoverHeights (Γ : DWeb V) (W : Set Γ.DPath) :
    Set Cardinal.{u} :=
  { κ | ∃ C : Set V, IsHalfwayStopover Γ W C ∧ height Γ C = κ }

/-- The altitude of a half-way linkage is the least height of any possible
stop-over set, exactly as in Definition 9.1. -/
def altitude (Γ : DWeb V) (W : Set Γ.DPath) : Cardinal.{u} :=
  sInf (halfwayStopoverHeights Γ W)

theorem altitude_le_height_of_stopover {Γ : DWeb V} {W : Set Γ.DPath}
    {C : Set V} (hC : IsHalfwayStopover Γ W C) :
    altitude Γ W ≤ height Γ C := by
  apply csInf_le'
  exact ⟨C, hC, rfl⟩

theorem halfwayStopoverHeights_nonempty {Γ : DWeb V}
    {W : Set Γ.DPath} (hW : IsHalfwayLinkage Γ W) :
    (halfwayStopoverHeights Γ W).Nonempty := by
  obtain ⟨C, hC⟩ := hW
  exact ⟨height Γ C, C, hC, rfl⟩

/-- The minimum defining the altitude of a half-way linkage is attained by
an actual stop-over set. -/
theorem exists_minimalAltitudeStopover {Γ : DWeb V} {W : Set Γ.DPath}
    (hW : IsHalfwayLinkage Γ W) :
    ∃ C : Set V, IsHalfwayStopover Γ W C ∧
      height Γ C = altitude Γ W := by
  have hmem : altitude Γ W ∈ halfwayStopoverHeights Γ W :=
    csInf_mem (halfwayStopoverHeights_nonempty hW)
  exact hmem

/-- The qualified half-way linkage promised by Theorem 9.2: its altitude
is at most `κ` and it links every designated source in `A₀` all the way
to the original target. -/
def IsHalfwayLinkageOfAltitude (Γ : DWeb V) (A₀ : Set V)
    (κ : Cardinal.{u}) (W : Set Γ.DPath) : Prop :=
  IsHalfwayLinkage Γ W ∧ LinksToTarget Γ W A₀ ∧ altitude Γ W ≤ κ

namespace IsLinkageBetween

theorem isWarp {Γ : DWeb V} {A C : Set V} {W : Set Γ.DPath}
    (hW : IsLinkageBetween Γ A C W) : Γ.IsWarp W :=
  hW.1

theorem finiteCharacter {Γ : DWeb V} {A C : Set V} {W : Set Γ.DPath}
    (hW : IsLinkageBetween Γ A C W) : Γ.HasFiniteCharacter W :=
  hW.2.1

theorem initialSet_eq {Γ : DWeb V} {A C : Set V} {W : Set Γ.DPath}
    (hW : IsLinkageBetween Γ A C W) : Γ.initialSet W = A :=
  hW.2.2.1

theorem terminalFrontier_subset {Γ : DWeb V} {A C : Set V}
    {W : Set Γ.DPath} (hW : IsLinkageBetween Γ A C W) :
    Γ.terminalFrontier W ⊆ C :=
  hW.2.2.2.1

theorem endpointPure {Γ : DWeb V} {A C : Set V}
    {W : Set Γ.DPath} (hW : IsLinkageBetween Γ A C W) :
    ∀ p ∈ W, IsPathBetween Γ A C p :=
  hW.2.2.2.2

end IsLinkageBetween

/-! ### Transport from the normalized web

Normalization deletes only edges.  Consequently an exact linkage in the
normalized web lifts memberwise to the original web with unchanged support,
initial vertices, and finite terminal frontier.  Recording this for the
canonical Section 9 linkage predicate keeps the safe-link/countable step
independent of normalization. -/

theorem IsPathBetween.liftNormalized {Γ : DWeb V} {A C : Set V}
    {p : Γ.normalized.DPath}
    (h : IsPathBetween Γ.normalized A C p) :
    IsPathBetween Γ A C (Γ.liftNormalizedPath p) := by
  rcases h with ⟨q, rfl, hends, hsource⟩
  let q' : DirectedPath.FinitePath Γ.graph := q.lift
    (fun {_ _} (he : Γ.normalized.graph.Adj _ _) => he.1)
  refine ⟨q', rfl, ?_, ?_⟩
  · rw [show q'.support = q.support by simp [q']]
    simpa [q', DirectedPath.FinitePath.lift] using hends
  · rw [show q'.support = q.support by simp [q']]
    simpa [q', DirectedPath.FinitePath.lift] using hsource

theorem hasFiniteCharacter_liftNormalizedFamily
    (Γ : DWeb V) {W : Set Γ.normalized.DPath}
    (hW : Γ.normalized.HasFiniteCharacter W) :
    Γ.HasFiniteCharacter (Γ.liftNormalizedFamily W) := by
  rintro p ⟨q, hqW, rfl⟩
  obtain ⟨r, rfl⟩ := hW hqW
  let r' : DirectedPath.FinitePath Γ.graph := r.lift
    (fun {_ _} (he : Γ.normalized.graph.Adj _ _) => he.1)
  exact ⟨r', rfl⟩

theorem IsLinkageBetween.liftNormalized {Γ : DWeb V}
    {A C : Set V} {W : Set Γ.normalized.DPath}
    (hW : IsLinkageBetween Γ.normalized A C W) :
    IsLinkageBetween Γ A C (Γ.liftNormalizedFamily W) := by
  refine ⟨hW.isWarp.liftNormalizedFamily,
    hasFiniteCharacter_liftNormalizedFamily Γ hW.finiteCharacter,
    ?_, ?_, ?_⟩
  · simpa only [Γ.initialSet_liftNormalizedFamily] using hW.initialSet_eq
  · simpa only [Γ.terminalFrontier_liftNormalizedFamily] using
      hW.terminalFrontier_subset
  · rintro p ⟨q, hqW, rfl⟩
    exact (hW.endpointPure q hqW).liftNormalized

theorem IsLinkable.of_normalized {Γ : DWeb V}
    (h : IsLinkable Γ.normalized) : IsLinkable Γ := by
  obtain ⟨W, hW⟩ := h
  exact ⟨Γ.liftNormalizedFamily W, hW.liftNormalized⟩

/-- The empty source is linked to every target by the empty warp. -/
theorem empty_linkage (Γ : DWeb V) :
    IsLinkageBetween Γ ∅ Γ.target ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hp.elim
  · intro p hp
    exact hp.elim
  · ext x
    simp [DWeb.initialSet]
  · intro x hx
    rcases hx with ⟨p, hp, -⟩
    exact hp.elim
  · intro p hp
    exact hp.elim

/-- Height bounds are monotone in the set being roofed. -/
theorem HeightAtMost.mono_set {Γ : DWeb V} {Y Z : Set V}
    {κ : Cardinal.{u}} (hYZ : Y ⊆ Z) (hZ : HeightAtMost Γ Z κ) :
    HeightAtMost Γ Y κ := by
  obtain ⟨X, ⟨hXA, W, hW, hroof⟩, hX⟩ := hZ
  exact ⟨X, ⟨hXA, W, hW, hYZ.trans hroof⟩, hX⟩

/-- Height bounds are monotone in the cardinal bound. -/
theorem HeightAtMost.mono_card {Γ : DWeb V} {Z : Set V}
    {κ μ : Cardinal.{u}} (hκμ : κ ≤ μ) (hZ : HeightAtMost Γ Z κ) :
    HeightAtMost Γ Z μ := by
  obtain ⟨X, hX, hcard⟩ := hZ
  exact ⟨X, hX, hcard.trans hκμ⟩

theorem HeightAtMost.height_le {Γ : DWeb V} {Z : Set V}
    {κ : Cardinal.{u}} (hZ : HeightAtMost Γ Z κ) :
    height Γ Z ≤ κ := by
  obtain ⟨X, hX, hcard⟩ := hZ
  exact (height_le_of_witness hX).trans hcard

/-- Because height is attained, the witness-bearing bounded predicate is
equivalent to the cardinal inequality. -/
theorem heightAtMost_iff {Γ : DWeb V} {Z : Set V}
    {κ : Cardinal.{u}} :
    HeightAtMost Γ Z κ ↔ height Γ Z ≤ κ := by
  constructor
  · exact HeightAtMost.height_le
  · intro hheight
    obtain ⟨X, hX, hXcard⟩ := exists_height_witness Γ Z
    exact ⟨X, hX, hXcard.trans_le hheight⟩

/-- A half-way linkage really is a finite source linkage to its recorded
stop-over set. -/
theorem IsHalfwayLinkage.exists_linkage {Γ : DWeb V} {W : Set Γ.DPath}
    (hW : IsHalfwayLinkage Γ W) :
    ∃ C : Set V, IsLinkageBetween Γ Γ.source C W := by
  obtain ⟨C, hC⟩ := hW
  exact ⟨C, hC.linkage⟩

theorem IsHalfwayLinkageOfAltitude.halfway {Γ : DWeb V} {A₀ : Set V}
    {κ : Cardinal.{u}} {W : Set Γ.DPath}
    (hW : IsHalfwayLinkageOfAltitude Γ A₀ κ W) :
    IsHalfwayLinkage Γ W :=
  hW.1

/-- A bounded-altitude half-way linkage admits a stop-over which realizes
its altitude and an explicit quotient witness of the same bound. -/
theorem IsHalfwayLinkageOfAltitude.exists_stopover
    {Γ : DWeb V} {A₀ : Set V} {κ : Cardinal.{u}} {W : Set Γ.DPath}
    (hW : IsHalfwayLinkageOfAltitude Γ A₀ κ W) :
    ∃ C : Set V, IsHalfwayStopover Γ W C ∧ HeightAtMost Γ C κ := by
  obtain ⟨C, hC, hheight⟩ := exists_minimalAltitudeStopover hW.1
  refine ⟨C, hC, heightAtMost_iff.2 ?_⟩
  rw [hheight]
  exact hW.2.2

theorem halfwayLinkageOfAltitude_of_stopover {Γ : DWeb V}
    {A₀ : Set V} {κ : Cardinal.{u}} {W : Set Γ.DPath} {C : Set V}
    (hC : IsHalfwayStopover Γ W C) (hlinks : LinksToTarget Γ W A₀)
    (hheight : HeightAtMost Γ C κ) :
    IsHalfwayLinkageOfAltitude Γ A₀ κ W := by
  refine ⟨⟨C, hC⟩, hlinks, ?_⟩
  exact (altitude_le_height_of_stopover hC).trans hheight.height_le

/-! ## The two simultaneous clauses of source Theorem 9.2 -/

/-- The extension clause `(clubsuit)` at a cardinal `λ`.  The cardinality
is equality, as in the source theorem; later uses may pad a smaller set of
sources before applying this clause. -/
def ExtensionClauseAt (Γ : DWeb V) (κ : Cardinal.{u}) : Prop :=
  ∀ A₀ : Set V, A₀ ⊆ Γ.source → #A₀ = κ →
    (∃ F : Set Γ.DPath,
      IsLinkageBetween Γ (Γ.source \ A₀) Γ.target F) →
    IsLinkable Γ

/-- The half-way-linkage clause `(clubsuit clubsuit)` at `λ`. -/
def HalfwayClauseAt (Γ : DWeb V) (κ : Cardinal.{u}) : Prop :=
  ∀ A₀ : Set V, A₀ ⊆ Γ.source → #A₀ = κ →
    ∃ W : Set Γ.DPath, IsHalfwayLinkageOfAltitude Γ A₀ κ W

/-- Historical exact-frontier strengthening of the half-way clause.

This predicate is retained so that the existing conditional composition
proofs remain available, but it is not a valid universal induction clause.
`HalfwayExactFrontierObstruction.not_separatingHalfwayClauseAt` proves its
failure on countably many disjoint two-leaf stars.  The terminal frontier
of a full target linkage need not separate.  A corrected positive induction
must not assume this predicate for arbitrary unhindered webs. -/
def SeparatingHalfwayClauseAt (Γ : DWeb V) (κ : Cardinal.{u}) : Prop :=
  ∀ A₀ : Set V, A₀ ⊆ Γ.source → #A₀ = κ →
    ∃ (W : Set Γ.DPath) (C : Set V),
      IsSeparatingHalfwayStopover Γ W C ∧
      LinksToTarget Γ W A₀ ∧ HeightAtMost Γ C κ ∧
      Γ.terminalFrontier W = C

/-- Forgetting the retained separator and concrete height witness recovers
the original public half-way conclusion. -/
theorem SeparatingHalfwayClauseAt.halfwayClauseAt
    {Γ : DWeb V} {κ : Cardinal.{u}}
    (h : SeparatingHalfwayClauseAt Γ κ) : HalfwayClauseAt Γ κ := by
  intro A₀ hA₀ hcard
  obtain ⟨W, C, hstop, hlinks, hheight, _hfrontier⟩ := h A₀ hA₀ hcard
  exact ⟨W, halfwayLinkageOfAltitude_of_stopover
    hstop.stopover hlinks hheight⟩

/-- The historical candidate simultaneous induction at `λ`.

The added exact-frontier clause makes this candidate false in general;
see `HalfwayExactFrontierObstruction.not_universalCardinalInductionAt`.
The abstract induction assembly below is a valid conditional theorem, but
its two step premises cannot both be supplied for this candidate.

The source's simultaneous induction ranges over infinite cardinals.  The
extension clause is meaningful (and needed) at every cardinal, whereas the
half-way clause is asserted only when `aleph_0 <= λ`; finite designated
source sets are handled directly by repeated applications of the safe-link
theorem. -/
def CardinalInductionAt (Γ : DWeb V) (κ : Cardinal.{u}) : Prop :=
  ExtensionClauseAt Γ κ ∧ (ℵ₀ ≤ κ → SeparatingHalfwayClauseAt Γ κ)

/-- The induction assertion at `κ`, uniformly for every web on the fixed
vertex type.  Uniformity is essential: the regular and blueprint arguments
apply lower-cardinal clauses, and the current extension clause, to quotient
and deleted auxiliary webs rather than only to the original web. -/
def UniversalCardinalInductionAt (V : Type u) (κ : Cardinal.{u}) : Prop :=
  ∀ Γ : DWeb V, Γ.IsUnhindered → CardinalInductionAt Γ κ

/-- The extension half at `κ`, uniformly over webs on `V`.  In the
simultaneous induction this is established before the half-way half at the
same cardinal, because Assertion 9.31 invokes it at `κ`. -/
def UniversalExtensionClauseAt (V : Type u) (κ : Cardinal.{u}) : Prop :=
  ∀ Γ : DWeb V, Γ.IsUnhindered → ExtensionClauseAt Γ κ

/-- Lower-cardinal induction hypotheses in the exact global form required by
the quotient and deletion constructions. -/
def UniversalCardinalInductionBelow (V : Type u)
    (κ : Cardinal.{u}) : Prop :=
  ∀ μ, μ < κ → UniversalCardinalInductionAt V μ

/-- Abstract well-founded assembly of the two genuinely proved Section 9
steps.  This theorem performs only the logical cardinal induction; the
graph-theoretic step proofs are supplied by `ExtensionClause` and
`HalfwayClause` and are not encoded as fields of any mathematical object. -/
theorem universalCardinalInduction_of_steps
    (extensionStep : ∀ κ : Cardinal.{u},
      UniversalCardinalInductionBelow V κ →
        UniversalExtensionClauseAt V κ)
    (halfwayStep : ∀ κ : Cardinal.{u},
      UniversalCardinalInductionBelow V κ →
      UniversalExtensionClauseAt V κ →
      ℵ₀ ≤ κ →
        ∀ Γ : DWeb V, Γ.IsUnhindered → SeparatingHalfwayClauseAt Γ κ) :
    ∀ κ : Cardinal.{u}, UniversalCardinalInductionAt V κ := by
  intro κ
  induction κ using Cardinal.lt_wf.induction with
  | h κ ih =>
      have hlower : UniversalCardinalInductionBelow V κ :=
        fun μ hμ ↦ ih μ hμ
      have hext : UniversalExtensionClauseAt V κ :=
        extensionStep κ hlower
      intro Γ hΓ
      exact ⟨hext Γ hΓ, fun hκ ↦ halfwayStep κ hlower hext hκ Γ hΓ⟩

theorem CardinalInductionAt.extension {Γ : DWeb V} {κ : Cardinal.{u}}
    (h : CardinalInductionAt Γ κ) : ExtensionClauseAt Γ κ :=
  h.1

theorem CardinalInductionAt.halfway {Γ : DWeb V} {κ : Cardinal.{u}}
    (h : CardinalInductionAt Γ κ) (hκ : ℵ₀ ≤ κ) :
    HalfwayClauseAt Γ κ :=
  (h.2 hκ).halfwayClauseAt

theorem CardinalInductionAt.separatingHalfway
    {Γ : DWeb V} {κ : Cardinal.{u}}
    (h : CardinalInductionAt Γ κ) (hκ : ℵ₀ ≤ κ) :
    SeparatingHalfwayClauseAt Γ κ :=
  h.2 hκ

/-- The last one-line specialization in the proof of Theorem 7.29: apply
the extension clause to all sources.  The complementary source set is
empty, hence has the empty linkage. -/
theorem linkable_of_extension_at_source_card (Γ : DWeb V)
    (h : ExtensionClauseAt Γ #Γ.source) : IsLinkable Γ := by
  apply h Γ.source Subset.rfl rfl
  refine ⟨∅, ?_⟩
  simpa using empty_linkage Γ

/-- The source-cardinal instance of the simultaneous induction conclusion
implies linkability. -/
theorem linkable_of_cardinalInductionAt_source (Γ : DWeb V)
    (h : CardinalInductionAt Γ #Γ.source) : IsLinkable Γ :=
  linkable_of_extension_at_source_card Γ h.extension

end CardinalInduction
end Erdos599
