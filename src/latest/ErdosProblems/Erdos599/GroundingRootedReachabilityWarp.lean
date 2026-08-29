/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleChain
import ErdosProblems.Erdos599.AlternatingMacroChain
import ErdosProblems.Erdos599.PopularSwitching

/-!
# Finite warps from rooted relation reachability

This file packages the relation-theoretic construction used at the end of
the grounding argument.  Starting with any finite relation path from `A`,
we discard everything before its last `A`-vertex.  Thus the retained path
starts in `A` and its remaining interior avoids `A`; no global assertion
about incoming relation edges at source vertices is required.  If the
prescribed boundary is an antichain for directed reachability, the chosen
root--boundary paths are vertex-disjoint.

The antichain hypothesis is essential: for the one-edge relation `a -> b`
and boundary `{a, b}`, both boundary vertices are rooted at `a`, but no
disjoint path family can have both vertices as its terminal frontier.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingRootedReachabilityWarp

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The last vertex of a nonempty list written as a head and a tail. -/
def chainLast : V → List V → V
  | x, [] => x
  | _, y :: ys => chainLast y ys

/-- Turn an adjacency chain into the corresponding endpoint-indexed
directed walk.  Writing the nonempty list as `x :: xs` keeps the endpoints
independent of proof terms. -/
def walkOfChain (x : V) : (xs : List V) →
    (x :: xs).IsChain Gamma.graph.Adj →
      Walk Gamma.graph x (chainLast x xs)
  | [], _ => .nil
  | y :: ys, hchain =>
      .cons hchain.rel (walkOfChain y ys hchain.tail)

@[simp]
theorem support_walkOfChain (x : V) (xs : List V)
    (hchain : (x :: xs).IsChain Gamma.graph.Adj) :
    (walkOfChain (Gamma := Gamma) x xs hchain).support = x :: xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
      change x :: (walkOfChain (Gamma := Gamma) y ys _).support =
        x :: y :: ys
      exact congrArg (List.cons x) (ih y hchain.tail)

@[simp]
theorem chainLast_eq_getLast (x : V) (xs : List V) :
    chainLast x xs = (x :: xs).getLast (by simp) := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
      rw [List.getLast_cons_cons]
      exact ih y

/-- Every edge of the walk obtained from an `E`-chain belongs to `E`. -/
theorem edgeSet_walkOfChain_subset
    {E : Set (V × V)} (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (x : V) (xs : List V)
    (hchain : (x :: xs).IsChain (fun x y => (x, y) ∈ E)) :
    (walkOfChain (Gamma := Gamma) x xs
      (hchain.imp fun _ _ h => hEadj h)).edgeSet ⊆ E := by
  induction xs generalizing x with
  | nil => exact Set.empty_subset E
  | cons y ys ih =>
      intro e he
      change e = (x, y) ∨
        e ∈ (walkOfChain (Gamma := Gamma) y ys _).edgeSet at he
      rcases he with rfl | he
      · exact hchain.rel
      · exact ih y hchain.tail he

/-- A simple finite graph path obtained from a nonempty, duplicate-free
relation chain. -/
def finitePathOfChain
    {E : Set (V × V)} (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (x : V) (xs : List V)
    (hchain : (x :: xs).IsChain (fun x y => (x, y) ∈ E))
    (hnodup : (x :: xs).Nodup) : FinitePath Gamma.graph where
  start := x
  finish := chainLast x xs
  walk := walkOfChain (Gamma := Gamma) x xs
    (hchain.imp fun _ _ h => hEadj h)
  isPath := by
    rw [Walk.isPath_iff, support_walkOfChain]
    exact hnodup

@[simp]
theorem mem_finitePathOfChain_support_iff
    {E : Set (V × V)} (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (x : V) (xs : List V)
    (hchain : (x :: xs).IsChain (fun x y => (x, y) ∈ E))
    (hnodup : (x :: xs).Nodup) (z : V) :
    z ∈ (finitePathOfChain (Gamma := Gamma) hEadj x xs hchain hnodup).support ↔
      z ∈ x :: xs := by
  change z ∈ (walkOfChain (Gamma := Gamma) x xs _).support ↔ _
  rw [support_walkOfChain]

theorem finitePathOfChain_edgeSet_subset
    {E : Set (V × V)} (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (x : V) (xs : List V)
    (hchain : (x :: xs).IsChain (fun x y => (x, y) ∈ E))
    (hnodup : (x :: xs).Nodup) :
    (finitePathOfChain (Gamma := Gamma) hEadj x xs hchain hnodup).edgeSet ⊆ E := by
  exact edgeSet_walkOfChain_subset hEadj x xs hchain

/-! ## Rooted finite paths -/

/-- A concrete finite `E`-path from `A` to a prescribed endpoint, normalized
at its last `A`-vertex.  Consequently no later vertex of the path belongs to
`A`. -/
structure RootedPath (E : Set (V × V)) (A : Set V) (b : V) where
  path : FinitePath Gamma.graph
  edgeSet_subset : path.edgeSet ⊆ E
  start_mem : path.start ∈ A
  finish_eq : path.finish = b
  no_source_after : ∀ {x : V}, x ∈ path.walk.support.tail → x ∉ A

/-- Every finite relation-reachability witness from `A` compiles to a simple
finite graph path with the same endpoint, normalized by taking the suffix
after the last `A`-vertex. -/
theorem exists_rootedPath_of_reflTransGen
    {E : Set (V × V)} (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    {A : Set V} {b : V}
    (hroot : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    Nonempty (RootedPath (Gamma := Gamma) E A b) := by
  classical
  obtain ⟨a, haA, hab⟩ := hroot
  obtain ⟨l, hl, hnodup⟩ :=
    DWeb.exists_nodup_chain_of_reflTransGen hab
  cases l with
  | nil => exact False.elim (hl.1 rfl)
  | cons x xs =>
    have hchain : (x :: xs).IsChain (fun u v ↦ (u, v) ∈ E) :=
      hl.2.1
    let p := finitePathOfChain (Gamma := Gamma) hEadj x xs hchain hnodup
    have hx : x = a := by
      simpa only [List.head?_cons, Option.some.injEq] using hl.2.2.1
    have hfinish : chainLast x xs = b := by
      rw [chainLast_eq_getLast]
      apply Option.some.inj
      exact (List.getLast?_eq_some_getLast (by simp : x :: xs ≠ [])).symm.trans
        hl.2.2.2
    have hpStartA : p.start ∈ A := by
      change x ∈ A
      exact hx ▸ haA
    let hmeet : p.walk.Meets A :=
      ⟨p.start, p.start_mem_support, hpStartA⟩
    let q := p.lastHit A hmeet
    refine ⟨{
      path := q
      edgeSet_subset :=
        (p.lastHit_edgeSet_subset A hmeet).trans
          (finitePathOfChain_edgeSet_subset hEadj x xs hchain hnodup)
      start_mem := p.lastHit_start_mem A hmeet
      finish_eq := ?_
      no_source_after := ?_ }⟩
    · exact hfinish
    · intro z hz
      exact p.lastHit_no_mem_after A hmeet hz

/-- Reachability reverses after transposing the underlying relation. -/
theorem reflTransGen_reverse
    {r : V → V → Prop} {a b : V}
    (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen (fun x y ↦ r y x) b a := by
  induction h with
  | refl => exact .refl
  | @tail c d hac hcd ih =>
      exact Relation.ReflTransGen.trans (r := fun x y ↦ r y x)
        (Relation.ReflTransGen.single (r := fun x y ↦ r y x) hcd) ih

/-- A relation path ending at a vertex without incoming edges has length
zero. -/
theorem eq_of_reflTransGen_of_noIncoming
    {E : Set (V × V)} {a b : V}
    (hab : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b)
    (hno : ¬ HasIncoming E b) : a = b := by
  rcases hab.cases_tail with hba | ⟨c, _hac, hcb⟩
  · exact hba.symm
  · exact False.elim (hno ⟨c, hcb⟩)

/-- Two no-incoming roots which can both reach the same vertex coincide in
a left-unique relation. -/
theorem root_eq_of_reaches_common
    {E : Set (V × V)} (hin : Relator.LeftUnique fun x y ↦ (x, y) ∈ E)
    {a c x : V}
    (hax : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x)
    (hcx : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) c x)
    (hnoa : ¬ HasIncoming E a) (hnoc : ¬ HasIncoming E c) :
    a = c := by
  have hright : Relator.RightUnique (fun u v ↦ (v, u) ∈ E) := by
    intro z y w hzy hzw
    exact hin hzy hzw
  have htotal := Relation.ReflTransGen.total_of_right_unique hright
    (reflTransGen_reverse hax) (reflTransGen_reverse hcx)
  cases htotal with
  | inl hca =>
      exact (eq_of_reflTransGen_of_noIncoming
        (reflTransGen_reverse hca) hnoa).symm
  | inr hac =>
      exact eq_of_reflTransGen_of_noIncoming
        (reflTransGen_reverse hac) hnoc

/-- A finite path using only `E` reaches every one of its support vertices
from its start. -/
theorem finitePath_start_reaches_of_mem_support
    {E : Set (V × V)} (p : FinitePath Gamma.graph)
    (hpE : p.edgeSet ⊆ E) {x : V} (hx : x ∈ p.support) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) p.start x := by
  let q := p.firstHit {x} ⟨x, hx, Set.mem_singleton x⟩
  have hqE : q.edgeSet ⊆ E :=
    (p.firstHit_edgeSet_subset {x} ⟨x, hx, Set.mem_singleton x⟩).trans hpE
  have hreach : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ E) q.start q.finish :=
    Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈ q.edgeSet)
      (p := fun u v ↦ (u, v) ∈ E)
      (fun _ _ h ↦ hqE h) q.start q.finish
        (Alternating.Walk.reflTransGen_edgeSet q.walk)
  have hfinish : q.finish = x := by
    simpa only [Set.mem_singleton_iff] using
      p.firstHit_finish_mem {x} ⟨x, hx, Set.mem_singleton x⟩
  exact hfinish ▸ hreach

/-- A finite path using only `E` reaches its finish from every support
vertex. -/
theorem finitePath_reaches_finish_of_mem_support
    {E : Set (V × V)} (p : FinitePath Gamma.graph)
    (hpE : p.edgeSet ⊆ E) {x : V} (hx : x ∈ p.support) :
    Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) x p.finish := by
  let q := p.suffixFrom x hx
  have hqE : q.edgeSet ⊆ E :=
    (p.suffixFrom_edgeSet_subset x hx).trans hpE
  have hreach : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ E) q.start q.finish :=
    Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈ q.edgeSet)
      (p := fun u v ↦ (u, v) ∈ E)
      (fun _ _ h ↦ hqE h) q.start q.finish
        (Alternating.Walk.reflTransGen_edgeSet q.walk)
  simpa only [q, FinitePath.suffixFrom_start,
    FinitePath.suffixFrom_finish] using hreach

/-! ## The boundary warp -/

/-- No two distinct boundary vertices are comparable by directed
`E`-reachability. -/
def IsReachabilityAntichain (E : Set (V × V)) (B : Set V) : Prop :=
  ∀ ⦃b⦄, b ∈ B → ∀ ⦃c⦄, c ∈ B →
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) b c → b = c

/-- A chosen last-source-normalized path for every boundary point forms an
`XSWarp` when the relation is right-unique and the boundary is a
reachability antichain. -/
noncomputable def rootedPathXSWarp
    {E : Set (V × V)} {A B : Set V}
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hanti : IsReachabilityAntichain E B)
    (hAsource : A ⊆ Gamma.source)
    (route : ∀ b : B, RootedPath (Gamma := Gamma) E A b.1) :
    Popular.XSWarp Gamma B where
  paths := Set.range fun b : B ↦ (route b).path
  disjoint := by
    rintro p ⟨b, rfl⟩ q ⟨c, rfl⟩ hpq
    change Disjoint (route b).path.support (route c).path.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hxb : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
        x b.1 := by
      rw [← (route b).finish_eq]
      exact finitePath_reaches_finish_of_mem_support
        (route b).path (route b).edgeSet_subset hxp
    have hxc : Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
        x c.1 := by
      rw [← (route c).finish_eq]
      exact finitePath_reaches_finish_of_mem_support
        (route c).path (route c).edgeSet_subset hxq
    have htotal := Relation.ReflTransGen.total_of_right_unique hbi.2 hxb hxc
    have hbc : b.1 = c.1 := by
      cases htotal with
      | inl hbc => exact hanti b.2 c.2 hbc
      | inr hcb => exact (hanti c.2 b.2 hcb).symm
    have : b = c := Subtype.ext hbc
    subst c
    exact hpq rfl
  starts_in_source := by
    rintro p ⟨b, rfl⟩
    exact hAsource (route b).start_mem
  ends_in_target := by
    rintro p ⟨b, rfl⟩
    rw [(route b).finish_eq]
    exact b.2

/-- Every boundary vertex is the terminal vertex of its chosen rooted path. -/
theorem rootedPathXSWarp_covers
    {E : Set (V × V)} {A B : Set V}
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hanti : IsReachabilityAntichain E B)
    (hAsource : A ⊆ Gamma.source)
    (route : ∀ b : B, RootedPath (Gamma := Gamma) E A b.1) :
    ∀ b ∈ B, ∃ p ∈
        (rootedPathXSWarp (Gamma := Gamma) hbi hanti hAsource route).paths,
      p.finish = b := by
  intro b hb
  let bs : B := ⟨b, hb⟩
  exact ⟨(route bs).path, ⟨bs, rfl⟩, (route bs).finish_eq⟩

/-- Main finite rooted-reachability construction.  The antichain premise is
the exact one-hit boundary condition needed for the conclusion; without it
the statement is false even for a single directed edge. -/
theorem exists_rootedReachabilityWarp
    {E : Set (V × V)} (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    {A B : Set V} (hAsource : A ⊆ Gamma.source)
    (hanti : IsReachabilityAntichain E B)
    (hroot : ∀ b ∈ B, ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    ∃ P : Popular.XSWarp Gamma B,
      (∀ b ∈ B, ∃ p ∈ P.paths, p.finish = b) ∧
      (∀ p ∈ P.paths, p.edgeSet ⊆ E ∧
        p.start ∈ A ∧
          ∀ {x : V}, x ∈ p.walk.support.tail → x ∉ A) := by
  classical
  let route : ∀ b : B, RootedPath (Gamma := Gamma) E A b.1 :=
    fun b ↦ Classical.choice
      (exists_rootedPath_of_reflTransGen (Gamma := Gamma) hEadj
        (hroot b.1 b.2))
  let P := rootedPathXSWarp (Gamma := Gamma) hbi hanti hAsource route
  refine ⟨P, rootedPathXSWarp_covers hbi hanti hAsource route, ?_⟩
  rintro p ⟨b, rfl⟩
  exact ⟨(route b).edgeSet_subset, (route b).start_mem,
    (route b).no_source_after⟩

/-- DPath-family form of `exists_rootedReachabilityWarp`: the resulting
finite warp starts in the original source and has terminal frontier exactly
`B`. -/
theorem exists_rootedReachability_pathFamily
    {E : Set (V × V)} (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    {A B : Set V} (hAsource : A ⊆ Gamma.source)
    (hanti : IsReachabilityAntichain E B)
    (hroot : ∀ b ∈ B, ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧ Gamma.initialSet W ⊆ Gamma.source ∧
        Gamma.terminalFrontier W = B := by
  obtain ⟨P, hcover, _hpaths⟩ :=
    exists_rootedReachabilityWarp hEadj hbi hAsource hanti hroot
  exact ⟨PopularSwitching.pathFamily P,
    PopularSwitching.pathFamily_isWarp P,
    PopularSwitching.pathFamily_initialSet_subset P,
    PopularSwitching.pathFamily_terminalFrontier_eq P hcover⟩

end GroundingRootedReachabilityWarp
end Erdos599
