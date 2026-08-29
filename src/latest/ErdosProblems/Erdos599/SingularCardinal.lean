/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Core
import ErdosProblems.Erdos599.FamilyTools
import ErdosProblems.Erdos599.PathTools
import ErdosProblems.Erdos599.WarpLimits
import ErdosProblems.Erdos599.WaveLimits

/-!
# Erdős Problem 599: the singular-cardinal competitor matrix

This file formalizes the set and cardinal combinatorics in Assertions 9.17
and 9.18 of Aharoni--Berger.  The graph-theoretic induction supplies the
successive half-way linkages.  The work done here is the part independent of
that induction:

* competitors of a set of initial vertices in a union of warps;
* the cardinal bound on competitors (a path is countable, and a warp is
  pairwise vertex-disjoint);
* the increasing omega-iteration which closes a set under competitors; and
* passage from the rows of the matrix to their source unions and concrete
  direct limits of path-extension threads.

In particular, the final closure theorem does not assume that the stage path
families are literally increasing as sets of path records.  Two finite
support witnesses for paths in direct limits can instead be extended into
one common late row.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace SingularCardinal

universe u

open DirectedPath WarpLimits

/-! ## Cofinal cardinal scales -/

/-- An increasing family of cardinals below `lambda` which is cofinal in
`lambda`.  Section 9 uses this with the index type of size `cf lambda`. -/
structure IsCofinalScale {I : Type u} [Preorder I]
    (kappa : I -> Cardinal.{u}) (lambda : Cardinal.{u}) : Prop where
  monotone : Monotone kappa
  infinite : forall i, aleph0 <= kappa i
  below : forall i, kappa i < lambda
  cofinal : forall rho, rho < lambda -> exists i, rho < kappa i

theorem IsCofinalScale.iSup_eq {I : Type u} [Preorder I] [Nonempty I]
    {kappa : I -> Cardinal.{u}} {lambda : Cardinal.{u}}
    (h : IsCofinalScale kappa lambda) : iSup kappa = lambda := by
  apply le_antisymm
  · exact ciSup_le' fun i => (h.below i).le
  · apply le_of_forall_lt
    intro rho hrho
    obtain ⟨i, hi⟩ := h.cofinal rho hrho
    exact hi.trans_le (le_ciSup bddAbove_of_small i)

/-! ## Competitors -/

end SingularCardinal

variable {V : Type u} (Gamma : DWeb V)

namespace DWeb

open DirectedPath WarpLimits

/-- Paths of `W` whose initial vertex belongs to `S`. -/
def startPaths (W : Set Gamma.DPath) (S : Set V) : Set Gamma.DPath :=
  {p | p ∈ W ∧ p.initial ∈ S}

/-- Paths of `W` meeting the support of at least one member of `P`. -/
def pathsMeetingFamily (W P : Set Gamma.DPath) : Set Gamma.DPath :=
  {q | q ∈ W ∧ ∃ p ∈ P, ¬ Disjoint q.support p.support}

/-- Two vertices are competitors in a path family if paths of the family
starting at them meet.  The family need not itself be a warp; in Section 9 it
is a union of `cf lambda` many warps. -/
def Competitors (W : Set Gamma.DPath) (a b : V) : Prop :=
  ∃ p ∈ W, p.initial = a ∧
    ∃ q ∈ W, q.initial = b ∧ ¬ Disjoint p.support q.support

/-- All competitors of vertices in `S`. -/
def competitorClosure (W : Set Gamma.DPath) (S : Set V) : Set V :=
  {b | ∃ a ∈ S, Gamma.Competitors W a b}

@[simp]
theorem mem_startPaths {W : Set Gamma.DPath} {S : Set V} {p : Gamma.DPath} :
    p ∈ Gamma.startPaths W S ↔ p ∈ W ∧ p.initial ∈ S :=
  Iff.rfl

@[simp]
theorem mem_pathsMeetingFamily {W P : Set Gamma.DPath} {q : Gamma.DPath} :
    q ∈ Gamma.pathsMeetingFamily W P ↔
      q ∈ W ∧ ∃ p ∈ P, ¬ Disjoint q.support p.support :=
  Iff.rfl

@[simp]
theorem mem_competitorClosure {W : Set Gamma.DPath} {S : Set V} {b : V} :
    b ∈ Gamma.competitorClosure W S ↔
      ∃ a ∈ S, Gamma.Competitors W a b :=
  Iff.rfl

theorem Competitors.symm {W : Set Gamma.DPath} {a b : V}
    (h : Gamma.Competitors W a b) : Gamma.Competitors W b a := by
  rcases h with ⟨p, hpW, rfl, q, hqW, rfl, hpq⟩
  exact ⟨q, hqW, rfl, p, hpW, rfl, by simpa [disjoint_comm] using hpq⟩

theorem Competitors.mono {W U : Set Gamma.DPath} {a b : V}
    (hWU : W ⊆ U) (h : Gamma.Competitors W a b) :
    Gamma.Competitors U a b := by
  rcases h with ⟨p, hpW, hpa, q, hqW, hqb, hpq⟩
  exact ⟨p, hWU hpW, hpa, q, hWU hqW, hqb, hpq⟩

theorem competitorClosure_mono_paths {W U : Set Gamma.DPath} {S : Set V}
    (hWU : W ⊆ U) :
    Gamma.competitorClosure W S ⊆ Gamma.competitorClosure U S := by
  rintro b ⟨a, haS, hab⟩
  rcases hab with ⟨p, hpW, hpa, q, hqW, hqb, hpq⟩
  exact ⟨a, haS, p, hWU hpW, hpa, q, hWU hqW, hqb, hpq⟩

theorem competitorClosure_mono_sources {W : Set Gamma.DPath} {S T : Set V}
    (hST : S ⊆ T) :
    Gamma.competitorClosure W S ⊆ Gamma.competitorClosure W T := by
  rintro b ⟨a, haS, hab⟩
  exact ⟨a, hST haS, hab⟩

/-- Competitors are exactly the initials of paths which meet a path starting
in the given source set. -/
theorem competitorClosure_eq_initial_image (W : Set Gamma.DPath) (S : Set V) :
    Gamma.competitorClosure W S =
      DirectedPath.Path.initial ''
        Gamma.pathsMeetingFamily W (Gamma.startPaths W S) := by
  ext b
  constructor
  · rintro ⟨a, haS, p, hpW, hpa, q, hqW, hqb, hpq⟩
    refine ⟨q, ?_, hqb⟩
    exact ⟨hqW, p, ⟨hpW, hpa ▸ haS⟩, by simpa [disjoint_comm] using hpq⟩
  · rintro ⟨q, ⟨hqW, p, ⟨hpW, hpaS⟩, hqp⟩, hqb⟩
    exact ⟨p.initial, hpaS, p, hpW, rfl, q, hqW, hqb,
      by simpa [disjoint_comm] using hqp⟩

/-! ## Cardinality of competitors in a union of warps -/

/-- The paths of a warp starting in `S` are no more numerous than `S`.
Choose the initial vertex of each path; disjointness makes this injective. -/
theorem mk_startPaths_le (W : Set Gamma.DPath) (S : Set V)
    (hW : Gamma.IsWarp W) : #(Gamma.startPaths W S) ≤ #S := by
  apply FamilyTools.mk_le_of_pairwiseDisjoint_of_meets
  · exact hW.subset fun _ hp => hp.1
  · intro p hp
    exact ⟨p.initial, hp.2, p.initial_mem_support⟩

/-- The paths of a warp meeting a fixed set `S` are no more numerous than
`S`.  This is the selector argument at the heart of the competitor bound. -/
theorem mk_pathsMeeting_le (W : Set Gamma.DPath) (S : Set V)
    (hW : Gamma.IsWarp W) :
    #({p | p ∈ W ∧ ¬ Disjoint p.support S} : Set Gamma.DPath) ≤ #S := by
  apply FamilyTools.mk_le_of_pairwiseDisjoint_of_meets
  · exact hW.subset fun _ hp => hp.1
  · intro p hp
    rcases Set.not_disjoint_iff.1 hp.2 with ⟨x, hxp, hxS⟩
    exact ⟨x, hxS, hxp⟩

/-- Cardinal bound for an arbitrary indexed union. -/
theorem mk_iUnion_le_of_le {I X : Type u} {f : I → Set X}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hI : #I ≤ kappa) (hf : ∀ i, #(f i) ≤ kappa) :
    #(⋃ i, f i) ≤ kappa := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hkappa hI (ciSup_le' hf)

/-- In a warp, the paths meeting one member `p` have size at most `kappa`
whenever the support of `p` does. -/
theorem mk_pathsMeeting_path_le (W : Set Gamma.DPath) (p : Gamma.DPath)
    (hW : Gamma.IsWarp W) {kappa : Cardinal.{u}}
    (hp : #p.support ≤ kappa) :
    #({q | q ∈ W ∧ ¬ Disjoint q.support p.support} : Set Gamma.DPath) ≤ kappa :=
  (Gamma.mk_pathsMeeting_le W p.support hW).trans hp

/-- Meeting any one member of a path family `P` still gives at most
`kappa` paths in a warp, provided `P` and every one of its supports have
size at most `kappa`. -/
theorem mk_pathsMeetingFamily_le (W P : Set Gamma.DPath)
    (hW : Gamma.IsWarp W) {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hP : #P ≤ kappa)
    (hsupport : ∀ p ∈ P, #p.support ≤ kappa) :
    #(Gamma.pathsMeetingFamily W P) ≤ kappa := by
  let pieces : P → Set Gamma.DPath := fun p =>
    {q | q ∈ W ∧ ¬ Disjoint q.support p.1.support}
  have hsub : Gamma.pathsMeetingFamily W P ⊆ ⋃ p, pieces p := by
    rintro q ⟨hqW, p, hpP, hqp⟩
    exact Set.mem_iUnion.2 ⟨⟨p, hpP⟩, hqW, hqp⟩
  refine (Cardinal.mk_subtype_mono hsub).trans ?_
  apply mk_iUnion_le_of_le hkappa hP
  intro p
  exact Gamma.mk_pathsMeeting_path_le W p.1 hW (hsupport p.1 p.2)

/-- The union of a family of warps has at most `kappa` paths meeting `P`,
when both the family and `P` have size at most `kappa`. -/
theorem mk_pathsMeetingFamily_iUnion_le {I : Type u}
    (W : I → Set Gamma.DPath) (P : Set Gamma.DPath)
    (hW : ∀ i, Gamma.IsWarp (W i)) {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hI : #I ≤ kappa) (hP : #P ≤ kappa)
    (hsupport : ∀ p ∈ P, #p.support ≤ kappa) :
    #(Gamma.pathsMeetingFamily (⋃ i, W i) P) ≤ kappa := by
  have hsub : Gamma.pathsMeetingFamily (⋃ i, W i) P ⊆
      ⋃ i, Gamma.pathsMeetingFamily (W i) P := by
    rintro q ⟨hq, p, hpP, hqp⟩
    obtain ⟨i, hqi⟩ := Set.mem_iUnion.1 hq
    exact Set.mem_iUnion.2 ⟨i, hqi, p, hpP, hqp⟩
  refine (Cardinal.mk_subtype_mono hsub).trans ?_
  apply mk_iUnion_le_of_le hkappa hI
  intro i
  exact Gamma.mk_pathsMeetingFamily_le (W i) P (hW i)
    hkappa hP hsupport

/-- The paths in a union of warps which start in `S` have size at most
`kappa`, provided the index family and `S` do. -/
theorem mk_startPaths_iUnion_le {I : Type u}
    (W : I → Set Gamma.DPath) (S : Set V)
    (hW : ∀ i, Gamma.IsWarp (W i)) {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hI : #I ≤ kappa) (hS : #S ≤ kappa) :
    #(Gamma.startPaths (⋃ i, W i) S) ≤ kappa := by
  have hsub : Gamma.startPaths (⋃ i, W i) S ⊆
      ⋃ i, Gamma.startPaths (W i) S := by
    rintro p ⟨hp, hpS⟩
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hp
    exact Set.mem_iUnion.2 ⟨i, hpi, hpS⟩
  refine (Cardinal.mk_subtype_mono hsub).trans ?_
  apply mk_iUnion_le_of_le hkappa hI
  intro i
  exact (Gamma.mk_startPaths_le (W i) S (hW i)).trans hS

/-- Assertion 9.17's competitor estimate.  A union of at most `kappa`
warps gives a set of at most `kappa` competitors to at most `kappa` source
vertices. -/
theorem mk_competitorClosure_iUnion_le {I : Type u}
    (W : I → Set Gamma.DPath) (S : Set V)
    (hW : ∀ i, Gamma.IsWarp (W i)) {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hI : #I ≤ kappa) (hS : #S ≤ kappa) :
    #(Gamma.competitorClosure (⋃ i, W i) S) ≤ kappa := by
  rw [Gamma.competitorClosure_eq_initial_image]
  refine Cardinal.mk_image_le.trans ?_
  apply Gamma.mk_pathsMeetingFamily_iUnion_le W
    (Gamma.startPaths (⋃ i, W i) S) hW hkappa hI
    (Gamma.mk_startPaths_iUnion_le W S hW hkappa hI hS)
  intro p hp
  exact (DirectedPath.Path.support_countable p).le_aleph0.trans hkappa

/-- Adjoin one fixed warp to an indexed family of warps.  The `none` index
is the fixed warp and `some i` is the `i`-th varying warp. -/
def withFixed {I : Type u} (F : Set Gamma.DPath)
    (W : I → Set Gamma.DPath) : Option I → Set Gamma.DPath
  | none => F
  | some i => W i

@[simp]
theorem iUnion_withFixed {I : Type u} (F : Set Gamma.DPath)
    (W : I → Set Gamma.DPath) :
    (⋃ o, Gamma.withFixed F W o) = F ∪ ⋃ i, W i := by
  ext p
  constructor
  · intro hp
    obtain ⟨o, hpo⟩ := Set.mem_iUnion.1 hp
    cases o with
    | none => exact Or.inl hpo
    | some i => exact Or.inr (Set.mem_iUnion.2 ⟨i, hpo⟩)
  · rintro (hpF | hpW)
    · exact Set.mem_iUnion.2 ⟨none, hpF⟩
    · obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hpW
      exact Set.mem_iUnion.2 ⟨some i, hpi⟩

/-- The form of the competitor estimate used verbatim by the singular
matrix: one fixed warp together with at most `kappa` varying warps. -/
theorem mk_competitorClosure_fixed_iUnion_le {I : Type u}
    (F : Set Gamma.DPath) (W : I → Set Gamma.DPath) (S : Set V)
    (hF : Gamma.IsWarp F) (hW : ∀ i, Gamma.IsWarp (W i))
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hI : #I ≤ kappa) (hS : #S ≤ kappa) :
    #(Gamma.competitorClosure (F ∪ ⋃ i, W i) S) ≤ kappa := by
  let all : Option I → Set Gamma.DPath := Gamma.withFixed F W
  have hall : ∀ o, Gamma.IsWarp (all o) := by
    intro o
    cases o with
    | none => exact hF
    | some i => exact hW i
  have hoption : #(Option I) ≤ kappa := by
    rw [Cardinal.mk_option]
    exact Cardinal.add_le_of_le hkappa hI (one_le_aleph0.trans hkappa)
  rw [← Gamma.iUnion_withFixed F W]
  exact Gamma.mk_competitorClosure_iUnion_le all S hall hkappa hoption hS

/-! ## Omega closure -/

/-- One inflationary competitor-closing step. -/
def competitorStep (W : Set Gamma.DPath) (S : Set V) : Set V :=
  S ∪ Gamma.competitorClosure W S

/-- The finite iterations of `competitorStep`. -/
def competitorIterate (W : Set Gamma.DPath) (S : Set V) : ℕ → Set V
  | 0 => S
  | n + 1 => Gamma.competitorStep W (competitorIterate W S n)

/-- The omega-iteration of competitor closure. -/
def omegaCompetitorClosure (W : Set Gamma.DPath) (S : Set V) : Set V :=
  ⋃ n, Gamma.competitorIterate W S n

theorem competitorStep_mono (W : Set Gamma.DPath) :
    Monotone (Gamma.competitorStep W) := by
  intro S T hST
  exact union_subset_union hST (Gamma.competitorClosure_mono_sources hST)

theorem competitorIterate_subset_succ (W : Set Gamma.DPath) (S : Set V)
    (n : ℕ) :
    Gamma.competitorIterate W S n ⊆ Gamma.competitorIterate W S (n + 1) := by
  intro x hx
  exact Or.inl hx

theorem competitorIterate_mono_nat (W : Set Gamma.DPath) (S : Set V) :
    Monotone (Gamma.competitorIterate W S) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih => exact ih.trans (Gamma.competitorIterate_subset_succ W S n)

/-- If competitors of every `kappa`-sized set have size at most `kappa`,
then every finite closing stage still has size at most `kappa`. -/
theorem mk_competitorIterate_le (W : Set Gamma.DPath) (S : Set V)
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa) (hS : #S ≤ kappa)
    (hcompetitors : ∀ T : Set V, #T ≤ kappa →
      #(Gamma.competitorClosure W T) ≤ kappa) :
    ∀ n, #(Gamma.competitorIterate W S n) ≤ kappa := by
  intro n
  induction n with
  | zero => exact hS
  | succ n ih =>
      refine (Cardinal.mk_union_le _ _).trans ?_
      exact Cardinal.add_le_of_le hkappa ih (hcompetitors _ ih)

/-- Specialized iteration bound for a fixed warp and an indexed family of
warps, the cardinal induction performed in Assertion 9.17. -/
theorem mk_competitorIterate_fixed_iUnion_le {I : Type u}
    (F : Set Gamma.DPath) (W : I → Set Gamma.DPath) (S : Set V)
    (hF : Gamma.IsWarp F) (hW : ∀ i, Gamma.IsWarp (W i))
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hI : #I ≤ kappa) (hS : #S ≤ kappa) :
    ∀ n, #(Gamma.competitorIterate (F ∪ ⋃ i, W i) S n) ≤ kappa :=
  Gamma.mk_competitorIterate_le (F ∪ ⋃ i, W i) S hkappa hS fun T hT =>
    Gamma.mk_competitorClosure_fixed_iUnion_le F W T hF hW hkappa hI hT

theorem subset_omegaCompetitorClosure (W : Set Gamma.DPath) (S : Set V) :
    S ⊆ Gamma.omegaCompetitorClosure W S := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨0, hx⟩

/-- The omega union is genuinely closed under competitors.  No abstract
continuity assumption is needed: a competition has a single source witness,
which already occurs at one finite stage. -/
theorem competitorClosure_omega_subset (W : Set Gamma.DPath) (S : Set V) :
    Gamma.competitorClosure W (Gamma.omegaCompetitorClosure W S) ⊆
      Gamma.omegaCompetitorClosure W S := by
  rintro b ⟨a, ha, hab⟩
  obtain ⟨n, han⟩ := Set.mem_iUnion.1 ha
  exact Set.mem_iUnion.2 ⟨n + 1, Or.inr ⟨a, han, hab⟩⟩

/-- Leastness of the omega competitor closure. -/
theorem omegaCompetitorClosure_minimal (W : Set Gamma.DPath) {S T : Set V}
    (hST : S ⊆ T) (hclosed : Gamma.competitorClosure W T ⊆ T) :
    Gamma.omegaCompetitorClosure W S ⊆ T := by
  have hstage : ∀ n, Gamma.competitorIterate W S n ⊆ T := by
    intro n
    induction n with
    | zero => exact hST
    | succ n ih =>
        exact union_subset ih
          ((Gamma.competitorClosure_mono_sources ih).trans hclosed)
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  exact hstage n hxn

/-- Countably many stages of size at most an infinite `kappa` still have
size at most `kappa`. -/
theorem mk_iUnion_nat_le {X : Type u} {F : ℕ → Set X}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hF : ∀ n, #(F n) ≤ kappa) :
    #(⋃ n, F n) ≤ kappa := by
  let FU : ULift.{u} ℕ → Set X := fun n => F n.down
  have hFU : #(⋃ n, FU n) ≤ kappa :=
    mk_iUnion_le_of_le hkappa (by simpa using hkappa) fun n => hF n.down
  have heq : (⋃ n, FU n) = ⋃ n, F n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n : ULift.{u} ℕ, hxn⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion.2 ⟨n.down, hxn⟩
    · intro hx
      obtain ⟨n : ℕ, hxn⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion.2 ⟨ULift.up n, hxn⟩
  rw [← heq]
  exact hFU

/-- Cardinality form of the omega closing argument. -/
theorem mk_omegaCompetitorClosure_le (W : Set Gamma.DPath) (S : Set V)
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hstage : ∀ n, #(Gamma.competitorIterate W S n) ≤ kappa) :
    #(Gamma.omegaCompetitorClosure W S) ≤ kappa :=
  mk_iUnion_nat_le hkappa hstage

theorem mk_omegaCompetitorClosure_eq (W : Set Gamma.DPath) (S : Set V)
    {kappa : Cardinal.{u}} (hS : #S = kappa)
    (hkappa : aleph0 ≤ kappa)
    (hstage : ∀ n, #(Gamma.competitorIterate W S n) ≤ kappa) :
    #(Gamma.omegaCompetitorClosure W S) = kappa := by
  apply le_antisymm (Gamma.mk_omegaCompetitorClosure_le W S hkappa hstage)
  rw [← hS]
  exact Cardinal.mk_subtype_mono (Gamma.subset_omegaCompetitorClosure W S)

/-! ## Direct limits of omega chains of warps

The paths in a forward-extension chain are generally not eventually equal.
Consequently, a set-theoretic `liminf` of the *path records* is not the
limit used in Assertion 9.18: a path which is strictly extended at every
stage would disappear from that liminf.  We instead take the direct limit
of the extension thread belonging to each initial vertex. -/

/-- An omega sequence of warps in which every row forward-extends the
preceding row. -/
structure ForwardWarpChain where
  stage : ℕ → Set Gamma.DPath
  isWarp : ∀ n, Gamma.IsWarp (stage n)
  forward : ∀ n, Gamma.ForwardExtension (stage n) (stage (n + 1))

namespace ForwardWarpChain

/-- Forward extension along an arbitrary finite interval of the chain. -/
theorem forward_le (C : Gamma.ForwardWarpChain) {m n : ℕ} (hmn : m ≤ n) :
    Gamma.ForwardExtension (C.stage m) (C.stage n) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Gamma.forwardExtension_refl _
  | succ n _ ih =>
      exact Gamma.forwardExtension_trans ih (C.forward n)

/-- All paths in the chain having a prescribed initial vertex. -/
def thread (C : Gamma.ForwardWarpChain) (a : V) : Set Gamma.DPath :=
  {p | ∃ n, p ∈ C.stage n ∧ p.initial = a}

theorem thread_nonempty (C : Gamma.ForwardWarpChain)
    (a : Gamma.initialSet (C.stage 0)) :
    (ForwardWarpChain.thread Gamma C a.1).Nonempty := by
  obtain ⟨p, hp, hpa⟩ := a.2
  exact ⟨p, 0, hp, hpa⟩

/-- A thread is linearly ordered by honest path extension. -/
theorem thread_isChain (C : Gamma.ForwardWarpChain) (a : V) :
    IsChain DirectedPath.Path.Extends (ForwardWarpChain.thread Gamma C a) := by
  rintro p ⟨m, hpm, hpa⟩ q ⟨n, hqn, hqa⟩ hpq
  rcases le_total m n with hmn | hnm
  · obtain ⟨r, hrn, hpr⟩ := (ForwardWarpChain.forward_le Gamma C hmn).1 p hpm
    have hrq : r = q :=
      IsWarp.eq_of_initial_eq Gamma (C.isWarp n) hrn hqn
        ((Gamma.extends_initial hpr).symm.trans (hpa.trans hqa.symm))
    exact Or.inl (hrq ▸ hpr)
  · obtain ⟨r, hrm, hqr⟩ := (ForwardWarpChain.forward_le Gamma C hnm).1 q hqn
    have hrp : r = p :=
      IsWarp.eq_of_initial_eq Gamma (C.isWarp m) hrm hpm
        ((Gamma.extends_initial hqr).symm.trans (hqa.trans hpa.symm))
    exact Or.inr (hrp ▸ hqr)

/-- The direct-limit path of the thread with initial vertex `a`. -/
noncomputable def threadLimit (C : Gamma.ForwardWarpChain)
    (a : Gamma.initialSet (C.stage 0)) : Gamma.DPath :=
  DirectedPath.Path.chainLimit (ForwardWarpChain.thread Gamma C a.1)
    (ForwardWarpChain.thread_nonempty Gamma C a)
    (ForwardWarpChain.thread_isChain Gamma C a.1)

theorem threadLimit_initial (C : Gamma.ForwardWarpChain)
    (a : Gamma.initialSet (C.stage 0)) :
    (ForwardWarpChain.threadLimit Gamma C a).initial = a.1 := by
  obtain ⟨p, n, hpn, hpa⟩ := ForwardWarpChain.thread_nonempty Gamma C a
  exact (Gamma.extends_initial
    (DirectedPath.Path.extends_chainLimit (ForwardWarpChain.thread Gamma C a.1)
      (ForwardWarpChain.thread_nonempty Gamma C a)
      (ForwardWarpChain.thread_isChain Gamma C a.1)
      ⟨n, hpn, hpa⟩)).symm.trans hpa

/-- The direct-limit family, one path for each stage-zero initial vertex. -/
noncomputable def limitPaths (C : Gamma.ForwardWarpChain) : Set Gamma.DPath :=
  Set.range (ForwardWarpChain.threadLimit Gamma C)

theorem mem_limitPaths_iff (C : Gamma.ForwardWarpChain) (p : Gamma.DPath) :
    p ∈ ForwardWarpChain.limitPaths Gamma C ↔
      ∃ a : Gamma.initialSet (C.stage 0),
        ForwardWarpChain.threadLimit Gamma C a = p :=
  Iff.rfl

theorem initialSet_limitPaths (C : Gamma.ForwardWarpChain) :
    Gamma.initialSet (ForwardWarpChain.limitPaths Gamma C) =
      Gamma.initialSet (C.stage 0) := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, ⟨a, rfl⟩, rfl⟩
    simp [ForwardWarpChain.threadLimit_initial Gamma C a, a.2]
  · intro x hx
    let a : Gamma.initialSet (C.stage 0) := ⟨x, hx⟩
    exact ⟨ForwardWarpChain.threadLimit Gamma C a, ⟨a, rfl⟩,
      ForwardWarpChain.threadLimit_initial Gamma C a⟩

/-- A support point of a thread limit already occurs on some finite-stage
member of that thread. -/
theorem mem_support_threadLimit_iff (C : Gamma.ForwardWarpChain)
    (a : Gamma.initialSet (C.stage 0)) (x : V) :
    x ∈ (ForwardWarpChain.threadLimit Gamma C a).support ↔
      ∃ n p, p ∈ C.stage n ∧ p.initial = a.1 ∧ x ∈ p.support := by
  rw [threadLimit, DirectedPath.Path.support_chainLimit]
  simp only [Set.mem_iUnion, thread]
  constructor
  · rintro ⟨p, ⟨n, hpn, hpa⟩, hxp⟩
    exact ⟨n, p, hpn, hpa, hxp⟩
  · rintro ⟨n, p, hpn, hpa, hxp⟩
    exact ⟨p, ⟨n, hpn, hpa⟩, hxp⟩

/-- Direct limits of forward chains remain warps.  The proof moves two
finite support witnesses to one common row and invokes disjointness there. -/
theorem isWarp_limitPaths (C : Gamma.ForwardWarpChain) :
    Gamma.IsWarp (ForwardWarpChain.limitPaths Gamma C) := by
  rintro pa ⟨a, rfl⟩ pb ⟨b, rfl⟩ hab
  apply Set.disjoint_left.2
  intro x hxa hxb
  obtain ⟨m, p, hpm, hpa, hxp⟩ :=
    (ForwardWarpChain.mem_support_threadLimit_iff Gamma C a x).1 hxa
  obtain ⟨n, q, hqn, hqb, hxq⟩ :=
    (ForwardWarpChain.mem_support_threadLimit_iff Gamma C b x).1 hxb
  let k := max m n
  obtain ⟨r, hrk, hpr⟩ :=
    (ForwardWarpChain.forward_le Gamma C (Nat.le_max_left m n)).1 p hpm
  obtain ⟨s, hsk, hqs⟩ :=
    (ForwardWarpChain.forward_le Gamma C (Nat.le_max_right m n)).1 q hqn
  have hxr : x ∈ r.support := Gamma.support_mono_of_extends hpr hxp
  have hxs : x ∈ s.support := Gamma.support_mono_of_extends hqs hxq
  have hrs : r = s := by
    by_contra hrs
    exact Set.disjoint_left.1 (C.isWarp k hrk hsk hrs) hxr hxs
  have habv : a.1 = b.1 := by
    calc
      a.1 = p.initial := hpa.symm
      _ = r.initial := Gamma.extends_initial hpr
      _ = s.initial := congrArg DirectedPath.Path.initial hrs
      _ = q.initial := (Gamma.extends_initial hqs).symm
      _ = b.1 := hqb
  have habeq : a = b := Subtype.ext habv
  exact hab (congrArg (ForwardWarpChain.threadLimit Gamma C) habeq)

/-- Every finite row forward-extends to the direct-limit warp. -/
theorem forwardExtension_limitPaths (C : Gamma.ForwardWarpChain) (n : ℕ) :
    Gamma.ForwardExtension (C.stage n) (ForwardWarpChain.limitPaths Gamma C) := by
  have hi : Gamma.initialSet (C.stage n) = Gamma.initialSet (C.stage 0) :=
    (Gamma.initialSet_eq_of_forwardExtension
      (ForwardWarpChain.forward_le Gamma C (Nat.zero_le n))).symm
  constructor
  · intro p hp
    have hpinit : p.initial ∈ Gamma.initialSet (C.stage n) := ⟨p, hp, rfl⟩
    let a : Gamma.initialSet (C.stage 0) := ⟨p.initial, hi ▸ hpinit⟩
    refine ⟨ForwardWarpChain.threadLimit Gamma C a, ⟨a, rfl⟩, ?_⟩
    exact DirectedPath.Path.extends_chainLimit (ForwardWarpChain.thread Gamma C a.1)
      (ForwardWarpChain.thread_nonempty Gamma C a)
      (ForwardWarpChain.thread_isChain Gamma C a.1) ⟨n, hp, rfl⟩
  · intro q hq
    obtain ⟨a, rfl⟩ := hq
    have han : a.1 ∈ Gamma.initialSet (C.stage n) := hi.symm ▸ a.2
    obtain ⟨p, hp, hpa⟩ := han
    refine ⟨p, hp, ?_⟩
    exact DirectedPath.Path.extends_chainLimit (ForwardWarpChain.thread Gamma C a.1)
      (ForwardWarpChain.thread_nonempty Gamma C a)
      (ForwardWarpChain.thread_isChain Gamma C a.1) ⟨n, hp, hpa⟩

end ForwardWarpChain

/-! ## Source-faithful finite target segments

A half-way path which links `a` to the target may start before `a`, and its
direct limit may be a ray.  The finite information which survives is a
segment beginning at `a`, meeting the target, and lying inside the support
of that half-way path.  This is the concrete interface extracted from the
suffix formulation of `LinksToTarget` in `CardinalInduction`. -/

/-- A finite `a`-to-target segment carried by one member of a path family.
The carrier-purity equation is the source condition used when different
matrix sources are compared in a later common row. -/
structure TargetSegment (W : Set Gamma.DPath) (A : Set V) (a : V) where
  source_mem : a ∈ A
  carrier : Gamma.DPath
  carrier_mem : carrier ∈ W
  carrier_pure : carrier.support ∩ A = {a}
  path : DirectedPath.FinitePath Gamma.graph
  path_start : path.start = a
  path_meets_target : path.walk.Meets Gamma.target
  path_support_subset : path.support ⊆ carrier.support

namespace TargetSegment

/-- Trim the supplied finite segment at its first target vertex. -/
noncomputable def firstTarget {W : Set Gamma.DPath} {A : Set V} {a : V}
    (T : Gamma.TargetSegment W A a) : DirectedPath.FinitePath Gamma.graph :=
  T.path.firstHit Gamma.target T.path_meets_target

@[simp]
theorem firstTarget_start {W : Set Gamma.DPath} {A : Set V} {a : V}
    (T : Gamma.TargetSegment W A a) : T.firstTarget.start = a :=
  T.path_start

@[simp]
theorem firstTarget_finish_mem {W : Set Gamma.DPath} {A : Set V} {a : V}
    (T : Gamma.TargetSegment W A a) : T.firstTarget.finish ∈ Gamma.target :=
  DirectedPath.FinitePath.firstHit_finish_mem _ _ _

theorem firstTarget_support_subset_carrier
    {W : Set Gamma.DPath} {A : Set V} {a : V}
    (T : Gamma.TargetSegment W A a) :
    T.firstTarget.support ⊆ T.carrier.support :=
  (DirectedPath.FinitePath.firstHit_support_subset _ _ _).trans
    T.path_support_subset

/-- The extracted segment contains no designated source except its initial
vertex. -/
theorem firstTarget_source_pure
    {W : Set Gamma.DPath} {A : Set V} {a : V}
    (T : Gamma.TargetSegment W A a) :
    T.firstTarget.support ∩ A = {a} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxA⟩
    rw [← T.carrier_pure]
    exact ⟨TargetSegment.firstTarget_support_subset_carrier Gamma T hx, hxA⟩
  · rintro x hx
    have hxa : x = a := Set.mem_singleton_iff.1 hx
    subst x
    have haSupport : a ∈ T.firstTarget.support := by
      simpa only [TargetSegment.firstTarget_start Gamma T] using
        T.firstTarget.start_mem_support
    exact ⟨haSupport, T.source_mem⟩

/-- First-hit trimming makes the target endpoint pure: no earlier vertex
of the extracted path belongs to the target. -/
theorem firstTarget_no_target_before
    {W : Set Gamma.DPath} {A : Set V} {a : V}
    (T : Gamma.TargetSegment W A a) {x : V}
    (hx : x ∈ T.firstTarget.walk.support.dropLast) :
    x ∉ Gamma.target :=
  DirectedPath.FinitePath.firstHit_no_mem_before _ _ _ hx

end TargetSegment

/-! ## The matrix limit (Assertion 9.18) -/

/-- The path family visible at matrix stage `n`: the fixed linkage `F`
together with the `n`-th row of every column. -/
def matrixStageFamily {I : Type u} (F : Set Gamma.DPath)
    (W : I → ℕ → Set Gamma.DPath) (n : ℕ) : Set Gamma.DPath :=
  F ∪ ⋃ i, W i n

/-- The union of the source sets in one matrix column. -/
def matrixLimitSources {I : Type u} (A : I → ℕ → Set V) (i : I) : Set V :=
  ⋃ n, A i n

end DWeb

namespace SingularCardinal

open DWeb

/-- Data of the `cf lambda` by `omega` matrix from Assertion 9.17.

`Qualified A k W` is a parameter because the source-faithful half-way
predicate is defined in `CardinalInduction`, which imports this file.  The
matrix nevertheless records the concrete warp, source, finiteness, and
forward-extension clauses used to prove Assertion 9.18. -/
structure CompetitorMatrix {I : Type u} [Preorder I]
    (kappa : I → Cardinal.{u}) (A₀ : Set V)
    (Qualified : Set V → Cardinal.{u} → Set Gamma.DPath → Prop) where
  fixed : Set Gamma.DPath
  fixed_isWarp : Gamma.IsWarp fixed
  fixed_finite : Gamma.HasFiniteCharacter fixed
  fixed_initial : Gamma.initialSet fixed = Gamma.source \ A₀
  fixed_target : Gamma.terminalFrontier fixed ⊆ Gamma.target
  sources : I → ℕ → Set V
  paths : I → ℕ → Set Gamma.DPath
  sources_subset_source : ∀ i n, sources i n ⊆ Gamma.source
  sources_card : ∀ i n, #(sources i n) = kappa i
  sources_mono_stage : ∀ i, Monotone (sources i)
  sources_mono_index : ∀ n, Monotone fun i => sources i n
  paths_isWarp : ∀ i n, Gamma.IsWarp (paths i n)
  paths_finite : ∀ i n, Gamma.HasFiniteCharacter (paths i n)
  paths_initial : ∀ i n, Gamma.initialSet (paths i n) = Gamma.source
  qualified : ∀ i n, Qualified (sources i n) (kappa i) (paths i n)
  target_segment : ∀ i n a, a ∈ sources i n →
    Nonempty (Gamma.TargetSegment (paths i n) (sources i n) a)
  forward : ∀ i n,
    Gamma.ForwardExtension (paths i n) (paths i (n + 1))
  cover : ⋃ i, sources i 0 = A₀
  close_succ : ∀ i n,
    Gamma.competitorClosure (Gamma.matrixStageFamily fixed paths n)
      (sources i n) ⊆ sources i (n + 1)

namespace CompetitorMatrix

variable {I : Type u} [Preorder I]
variable {kappa : I → Cardinal.{u}} {A₀ : Set V}
variable {Qualified : Set V → Cardinal.{u} → Set Gamma.DPath → Prop}

def limitSources (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified)
    (i : I) : Set V :=
  matrixLimitSources M.sources i

def columnChain (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified)
    (i : I) : Gamma.ForwardWarpChain where
  stage := M.paths i
  isWarp := M.paths_isWarp i
  forward := M.forward i

noncomputable def limitPaths
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified)
    (i : I) : Set Gamma.DPath :=
  DWeb.ForwardWarpChain.limitPaths Gamma (columnChain Gamma M i)

noncomputable def limitFamily
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) :
    Set Gamma.DPath :=
  M.fixed ∪ ⋃ i, limitPaths Gamma M i

theorem sources_subset_limitSources
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified)
    (i : I) (n : ℕ) : M.sources i n ⊆ limitSources Gamma M i := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨n, hx⟩

theorem limitSources_mono
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) :
    Monotone (limitSources Gamma M) := by
  intro i j hij x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨n, M.sources_mono_index n hij hxn⟩

theorem limitSources_subset_source
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    limitSources Gamma M i ⊆ Gamma.source := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  exact M.sources_subset_source i n hxn

/-- Each direct-limit column is an actual warp. -/
theorem limitPaths_isWarp
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    Gamma.IsWarp (limitPaths Gamma M i) :=
  DWeb.ForwardWarpChain.isWarp_limitPaths Gamma (columnChain Gamma M i)

theorem limitPaths_initialSet
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    Gamma.initialSet (limitPaths Gamma M i) = Gamma.source := by
  rw [limitPaths, DWeb.ForwardWarpChain.initialSet_limitPaths, columnChain,
    M.paths_initial i 0]

theorem paths_forwardExtension_limitPaths
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified)
    (i : I) (n : ℕ) :
    Gamma.ForwardExtension (M.paths i n) (limitPaths Gamma M i) :=
  DWeb.ForwardWarpChain.forwardExtension_limitPaths Gamma
    (columnChain Gamma M i) n

/-! ### Target paths extracted from the limit columns -/

/-- The first row in which a member of a limit source set occurs. -/
noncomputable def sourceStage
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) : ℕ :=
  Classical.choose (Set.mem_iUnion.1 a.2)

theorem sourceStage_mem
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    a.1 ∈ M.sources i (sourceStage Gamma M i a) :=
  Classical.choose_spec (Set.mem_iUnion.1 a.2)

/-- The source-faithful finite target segment supplied at the selected
finite row. -/
noncomputable def stageTargetSegment
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    Gamma.TargetSegment (M.paths i (sourceStage Gamma M i a))
      (M.sources i (sourceStage Gamma M i a)) a.1 :=
  Classical.choice (M.target_segment i (sourceStage Gamma M i a) a.1
    (sourceStage_mem Gamma M i a))

/-- The direct-limit carrier extending the finite-row carrier of `a`. -/
noncomputable def limitAmbient
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) : Gamma.DPath :=
  Classical.choose ((paths_forwardExtension_limitPaths Gamma M i
    (sourceStage Gamma M i a)).1
      (stageTargetSegment Gamma M i a).carrier
      (stageTargetSegment Gamma M i a).carrier_mem)

theorem limitAmbient_mem
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    limitAmbient Gamma M i a ∈ limitPaths Gamma M i :=
  (Classical.choose_spec ((paths_forwardExtension_limitPaths Gamma M i
    (sourceStage Gamma M i a)).1
      (stageTargetSegment Gamma M i a).carrier
      (stageTargetSegment Gamma M i a).carrier_mem)).1

theorem stageCarrier_extends_limitAmbient
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    Gamma.Extends (stageTargetSegment Gamma M i a).carrier
      (limitAmbient Gamma M i a) :=
  (Classical.choose_spec ((paths_forwardExtension_limitPaths Gamma M i
    (sourceStage Gamma M i a)).1
      (stageTargetSegment Gamma M i a).carrier
      (stageTargetSegment Gamma M i a).carrier_mem)).2

/-- The finite final path chosen for `a`: stop its finite witness at the
first target vertex. -/
noncomputable def targetPath
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) : DirectedPath.FinitePath Gamma.graph :=
  (stageTargetSegment Gamma M i a).firstTarget

@[simp]
theorem targetPath_start
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) : (targetPath Gamma M i a).start = a.1 :=
  DWeb.TargetSegment.firstTarget_start Gamma _

@[simp]
theorem targetPath_finish_mem
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    (targetPath Gamma M i a).finish ∈ Gamma.target :=
  DWeb.TargetSegment.firstTarget_finish_mem Gamma _

theorem targetPath_support_subset_limitAmbient
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    (targetPath Gamma M i a).support ⊆ (limitAmbient Gamma M i a).support :=
  (DWeb.TargetSegment.firstTarget_support_subset_carrier
    Gamma (stageTargetSegment Gamma M i a)).trans
      (Gamma.support_mono_of_extends (stageCarrier_extends_limitAmbient Gamma M i a))

/-- The target-trimmed finite paths in one limit column. -/
noncomputable def targetPaths
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    Set Gamma.DPath :=
  Set.range fun a : limitSources Gamma M i =>
    (Sum.inl (targetPath Gamma M i a) : Gamma.DPath)

/-- Distinct limit sources are carried by distinct paths of the direct-limit
warp.  The proof compares the two finite carriers in a common later row and
uses the source-purity clause of a fresh row witness. -/
theorem limitAmbient_ne
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    {a b : limitSources Gamma M i} (hab : a ≠ b) :
    limitAmbient Gamma M i a ≠ limitAmbient Gamma M i b := by
  intro hamb
  let ma := sourceStage Gamma M i a
  let mb := sourceStage Gamma M i b
  let n := max ma mb
  let Ta := stageTargetSegment Gamma M i a
  let Tb := stageTargetSegment Gamma M i b
  obtain ⟨pa, hpa, hapa⟩ :=
    (DWeb.ForwardWarpChain.forward_le Gamma (columnChain Gamma M i)
      (Nat.le_max_left ma mb)).1 Ta.carrier Ta.carrier_mem
  obtain ⟨pb, hpb, hbpb⟩ :=
    (DWeb.ForwardWarpChain.forward_le Gamma (columnChain Gamma M i)
      (Nat.le_max_right ma mb)).1 Tb.carrier Tb.carrier_mem
  have haCarrier : a.1 ∈ Ta.carrier.support :=
    Ta.path_support_subset (by
      simpa only [Ta.path_start] using Ta.path.start_mem_support)
  have hbCarrier : b.1 ∈ Tb.carrier.support :=
    Tb.path_support_subset (by
      simpa only [Tb.path_start] using Tb.path.start_mem_support)
  have hapaSupport : a.1 ∈ pa.support :=
    Gamma.support_mono_of_extends hapa haCarrier
  have hbpbSupport : b.1 ∈ pb.support :=
    Gamma.support_mono_of_extends hbpb hbCarrier
  have haN : a.1 ∈ M.sources i n :=
    M.sources_mono_stage i (Nat.le_max_left ma mb)
      (sourceStage_mem Gamma M i a)
  have hbN : b.1 ∈ M.sources i n :=
    M.sources_mono_stage i (Nat.le_max_right ma mb)
      (sourceStage_mem Gamma M i b)
  let Ra : Gamma.TargetSegment (M.paths i n) (M.sources i n) a.1 :=
    Classical.choice (M.target_segment i n a.1 haN)
  have hpaRa : pa = Ra.carrier := by
    by_contra hne
    exact Set.disjoint_left.1 (M.paths_isWarp i n hpa Ra.carrier_mem hne)
      hapaSupport
      (Ra.path_support_subset (by
        simpa only [Ra.path_start] using Ra.path.start_mem_support))
  have hpane : pa ≠ pb := by
    intro hpab
    have hbRa : b.1 ∈ Ra.carrier.support := by
      rw [← hpaRa, hpab]
      exact hbpbSupport
    have hba : b.1 = a.1 := by
      have : b.1 ∈ ({a.1} : Set V) := by
        rw [← Ra.carrier_pure]
        exact ⟨hbRa, hbN⟩
      exact Set.mem_singleton_iff.1 this
    exact hab (Subtype.ext hba.symm)
  apply hpane
  apply IsWarp.eq_of_initial_eq Gamma (M.paths_isWarp i n) hpa hpb
  calc
    pa.initial = Ta.carrier.initial := (Gamma.extends_initial hapa).symm
    _ = (limitAmbient Gamma M i a).initial :=
      Gamma.extends_initial (stageCarrier_extends_limitAmbient Gamma M i a)
    _ = (limitAmbient Gamma M i b).initial := congrArg _ hamb
    _ = Tb.carrier.initial :=
      (Gamma.extends_initial (stageCarrier_extends_limitAmbient Gamma M i b)).symm
    _ = pb.initial := Gamma.extends_initial hbpb

/-- The extracted target paths form a warp because their supports shrink
the pairwise-disjoint direct-limit carriers. -/
theorem targetPaths_isWarp
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    Gamma.IsWarp (targetPaths Gamma M i) := by
  rintro p ⟨a, rfl⟩ q ⟨b, rfl⟩ hpq
  have hab : a ≠ b := by
    intro hab
    subst b
    exact hpq rfl
  have hamb := limitAmbient_ne Gamma M i hab
  have hdis := limitPaths_isWarp Gamma M i
    (limitAmbient_mem Gamma M i a) (limitAmbient_mem Gamma M i b) hamb
  exact hdis.mono (targetPath_support_subset_limitAmbient Gamma M i a)
    (targetPath_support_subset_limitAmbient Gamma M i b)

/-- The target-trimmed family covers exactly the column's limit sources. -/
theorem initialSet_targetPaths
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    Gamma.initialSet (targetPaths Gamma M i) = limitSources Gamma M i := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, ⟨a, rfl⟩, hpx⟩
    have hax : a.1 = x := (targetPath_start Gamma M i a).symm.trans hpx
    exact hax ▸ a.2
  · intro x hx
    let a : limitSources Gamma M i := ⟨x, hx⟩
    refine ⟨(Sum.inl (targetPath Gamma M i a) : Gamma.DPath), ⟨a, rfl⟩, ?_⟩
    exact targetPath_start Gamma M i a

/-- Every extracted finite path terminates in the target. -/
theorem terminalFrontier_targetPaths_subset
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    Gamma.terminalFrontier (targetPaths Gamma M i) ⊆ Gamma.target := by
  rintro x ⟨p, ⟨a, rfl⟩, hterm⟩
  have : (targetPath Gamma M i a).finish = x := Option.some.inj hterm
  exact this ▸ targetPath_finish_mem Gamma M i a

/-- Every member of the target-trimmed family is finite. -/
theorem targetPaths_finiteCharacter
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    Gamma.HasFiniteCharacter (targetPaths Gamma M i) := by
  rintro p ⟨a, rfl⟩
  exact ⟨targetPath Gamma M i a, rfl⟩

/-- No extracted path contains another source from its limit column.  This
upgrades the finite-row purity equation to the whole omega union, using
disjointness of the corresponding limit carriers. -/
theorem targetPath_source_pure
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    (targetPath Gamma M i a).support ∩ limitSources Gamma M i = {a.1} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxp, hxA⟩
    by_contra hxa
    let b : limitSources Gamma M i := ⟨x, hxA⟩
    have hab : a ≠ b := by
      intro hab
      apply hxa
      exact congrArg Subtype.val hab |>.symm
    have hamb := limitAmbient_ne Gamma M i hab
    have hdis := limitPaths_isWarp Gamma M i
      (limitAmbient_mem Gamma M i a) (limitAmbient_mem Gamma M i b) hamb
    have hxb : x ∈ (targetPath Gamma M i b).support := by
      simpa only [targetPath_start Gamma M i b] using
        (targetPath Gamma M i b).start_mem_support
    exact Set.disjoint_left.1 hdis
      (targetPath_support_subset_limitAmbient Gamma M i a hxp)
      (targetPath_support_subset_limitAmbient Gamma M i b hxb)
  · rintro x hx
    have hxa : x = a.1 := Set.mem_singleton_iff.1 hx
    subst x
    exact ⟨by simpa only [targetPath_start Gamma M i a] using
        (targetPath Gamma M i a).start_mem_support, a.2⟩

/-- First-target trimming leaves no target vertex except the final one. -/
theorem targetPath_target_pure
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    (targetPath Gamma M i a).support ∩ Gamma.target =
      {(targetPath Gamma M i a).finish} := by
  let p := targetPath Gamma M i a
  apply Set.Subset.antisymm
  · rintro x ⟨hxp, hxB⟩
    by_contra hxfinish
    have hlast : p.walk.support.getLast p.walk.support_ne_nil = p.finish :=
      p.walk.getLast_support
    have hxlast : x ≠ p.walk.support.getLast p.walk.support_ne_nil := by
      intro hx
      exact hxfinish (hx.trans hlast)
    have hxdrop : x ∈ p.walk.support.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hxp hxlast
    exact (DWeb.TargetSegment.firstTarget_no_target_before Gamma
      (stageTargetSegment Gamma M i a) hxdrop) hxB
  · rintro x hx
    have hxfinish : x = p.finish := Set.mem_singleton_iff.1 hx
    subst x
    exact ⟨p.finish_mem_support, targetPath_finish_mem Gamma M i a⟩

/-- Each extracted member meets the column sources and the target only at
its two endpoints.  This is the endpoint-purity clause needed by the
canonical `IsLinkageBetween` adapter in `CardinalInduction`. -/
theorem targetPath_endpoint_pure
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (a : limitSources Gamma M i) :
    (targetPath Gamma M i a).support ∩
        (limitSources Gamma M i ∪ Gamma.target) =
      {(targetPath Gamma M i a).start, (targetPath Gamma M i a).finish} := by
  rw [Set.inter_union_distrib_left, targetPath_source_pure Gamma M i a,
    targetPath_target_pure Gamma M i a, targetPath_start Gamma M i a]
  simp only [Set.singleton_union]

/-- A support point of a final path has a witness in a finite matrix row.
The witness has the same initial vertex, which is exactly what competitor
closure needs. -/
theorem limitFamily_support_stage
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified)
    {p : Gamma.DPath} (hp : p ∈ limitFamily Gamma M) {x : V}
    (hxp : x ∈ p.support) :
    ∃ n q, q ∈ Gamma.matrixStageFamily M.fixed M.paths n ∧
      q.initial = p.initial ∧ x ∈ q.support := by
  rcases hp with hpF | hpL
  · exact ⟨0, p, Or.inl hpF, rfl, hxp⟩
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hpL
    obtain ⟨a, rfl⟩ := hpi
    obtain ⟨n, q, hqn, hqa, hxq⟩ :=
      (DWeb.ForwardWarpChain.mem_support_threadLimit_iff Gamma
        (columnChain Gamma M i) a x).1 hxp
    refine ⟨n, q, Or.inr (Set.mem_iUnion.2 ⟨i, hqn⟩), ?_, hxq⟩
    exact hqa.trans (DWeb.ForwardWarpChain.threadLimit_initial Gamma
      (columnChain Gamma M i) a).symm

/-- A path visible in one matrix row extends to a path visible in every
later row. -/
theorem matrixStageFamily_forward
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified)
    {m n : ℕ} (hmn : m ≤ n) {p : Gamma.DPath}
    (hp : p ∈ Gamma.matrixStageFamily M.fixed M.paths m) :
    ∃ q ∈ Gamma.matrixStageFamily M.fixed M.paths n, Gamma.Extends p q := by
  rcases hp with hpF | hpW
  · exact ⟨p, Or.inl hpF, Gamma.extends_refl p⟩
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.1 hpW
    obtain ⟨q, hqn, hpq⟩ :=
      (DWeb.ForwardWarpChain.forward_le Gamma (columnChain Gamma M i) hmn).1 p hpi
    exact ⟨q, Or.inr (Set.mem_iUnion.2 ⟨i, hqn⟩), hpq⟩

/-- The exact closure conclusion of Assertion 9.18, now proved for the
direct thread limits rather than a set liminf of path values. -/
theorem limitSources_closed
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I) :
    Gamma.competitorClosure (limitFamily Gamma M) (limitSources Gamma M i) ⊆
      limitSources Gamma M i := by
  rintro b ⟨a, ha, p, hp, hpa, q, hq, hqb, hpq⟩
  obtain ⟨na, hana⟩ := Set.mem_iUnion.1 ha
  obtain ⟨x, hxp, hxq⟩ := Set.not_disjoint_iff.1 hpq
  obtain ⟨np, p₀, hp₀, hp₀init, hxp₀⟩ :=
    limitFamily_support_stage Gamma M hp hxp
  obtain ⟨nq, q₀, hq₀, hq₀init, hxq₀⟩ :=
    limitFamily_support_stage Gamma M hq hxq
  let n := max na (max np nq)
  obtain ⟨p₁, hp₁, hp₀p₁⟩ := matrixStageFamily_forward Gamma M
    (le_trans (Nat.le_max_left np nq) (Nat.le_max_right na (max np nq))) hp₀
  obtain ⟨q₁, hq₁, hq₀q₁⟩ := matrixStageFamily_forward Gamma M
    (le_trans (Nat.le_max_right np nq) (Nat.le_max_right na (max np nq))) hq₀
  have hp₁init : p₁.initial = a := by
    rw [← Gamma.extends_initial hp₀p₁, hp₀init, hpa]
  have hq₁init : q₁.initial = b := by
    rw [← Gamma.extends_initial hq₀q₁, hq₀init, hqb]
  have hxp₁ : x ∈ p₁.support := Gamma.support_mono_of_extends hp₀p₁ hxp₀
  have hxq₁ : x ∈ q₁.support := Gamma.support_mono_of_extends hq₀q₁ hxq₀
  have hcomp : b ∈ Gamma.competitorClosure
      (Gamma.matrixStageFamily M.fixed M.paths n) (M.sources i n) := by
    refine ⟨a, M.sources_mono_stage i (Nat.le_max_left na (max np nq)) hana,
      p₁, hp₁, hp₁init, q₁, hq₁, hq₁init, ?_⟩
    exact Set.not_disjoint_iff.2 ⟨x, hxp₁, hxq₁⟩
  exact Set.mem_iUnion.2 ⟨n + 1, M.close_succ i n hcomp⟩

/-- Initial coverage is preserved by taking the column unions. -/
theorem cover_limitSources
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) :
    A₀ ⊆ ⋃ i, limitSources Gamma M i := by
  intro x hx
  have hx' : x ∈ ⋃ i, M.sources i 0 := M.cover.symm ▸ hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx'
  exact Set.mem_iUnion.2 ⟨i, sources_subset_limitSources Gamma M i 0 hxi⟩

/-- Each matrix column keeps the prescribed singular-scale cardinal after
taking its omega union. -/
theorem mk_limitSources_eq
    (M : CompetitorMatrix (I := I) Gamma kappa A₀ Qualified) (i : I)
    (hkappa : aleph0 ≤ kappa i) :
    #(limitSources Gamma M i) = kappa i := by
  apply le_antisymm
  · exact mk_iUnion_nat_le hkappa fun n => (M.sources_card i n).le
  · rw [← M.sources_card i 0]
    exact Cardinal.mk_subtype_mono (sources_subset_limitSources Gamma M i 0)

end CompetitorMatrix

end SingularCardinal
end Erdos599
