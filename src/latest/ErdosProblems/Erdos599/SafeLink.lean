/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteDeletion
import ErdosProblems.Erdos599.CommonQuotient
import ErdosProblems.Erdos599.FamilyTools
import ErdosProblems.Erdos599.Normalization
import ErdosProblems.Erdos599.PathTools
import ErdosProblems.Erdos599.SafeTree
import ErdosProblems.Erdos599.WaveLimits
import Mathlib.Data.Set.Countable
import Mathlib.Order.Zorn

/-!
# Erdős Problem 599: infrastructure for the safe-link theorem

This file contains the source-independent parts of Section 6 of
Aharoni--Berger.  In particular it proves the last-exit argument used in
Lemma 6.2, the countability fact used by the closing-up construction in
Proposition 6.3, and the Zorn argument which produces the maximal reachable
set underlying the tree in the proof of Theorem 6.1.

The definitions are phrased for the endpoint-indexed directed paths in
`DirectedPath.lean`.  They make no finiteness or decidable-equality assumption
on the vertex type.
-/

namespace Erdos599.SafeLink

open Set
open Erdos599.DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

namespace Walk

/-- A directed walk avoids `Q` when none of its vertices belongs to `Q`. -/
def Avoids {u v : V} (p : DirectedPath.Walk D u v) (Q : Set V) : Prop :=
  ∀ x : V, x ∈ p.support → x ∉ Q

/-- The vertices immediately outside a set which are reached by an outgoing
edge from the set. -/
def outBoundary (D : Digraph V) (Q : Set V) : Set V :=
  {y | y ∉ Q ∧ ∃ q ∈ Q, D.Adj q y}

/-- The data at the last exit of a finite directed walk from `Q`.

The suffix begins immediately after the last `Q`-vertex, so it avoids `Q` in
its entirety.  Recording it as an endpoint-indexed walk makes it directly
usable in the roof hypothesis of Aharoni--Berger Lemma 6.2. -/
structure LastExit {u v : V} (p : DirectedPath.Walk D u v) (Q : Set V) where
  inside : V
  outside : V
  edge : D.Adj inside outside
  inside_mem : inside ∈ Q
  outside_not_mem : outside ∉ Q
  suffix : DirectedPath.Walk D outside v
  suffix_avoids : Avoids suffix Q
  support_suffix : suffix.support <:+ p.support

/-- A finite walk which meets `Q` and ends outside `Q` has a last exit from
`Q`. -/
theorem exists_lastExit : ∀ {u v : V} (p : DirectedPath.Walk D u v) (Q : Set V),
    p.Meets Q → v ∉ Q → Nonempty (LastExit p Q)
  | u, _, .nil, Q, hmeet, hv => by
      rcases hmeet with ⟨x, hx, hxQ⟩
      have hxu : x = u := by simpa using hx
      exact (hv (hxu ▸ hxQ)).elim
  | u, v, .cons (v := w) hedge p, Q, hmeet, hv => by
      by_cases hpmeet : p.Meets Q
      · obtain ⟨L⟩ := exists_lastExit p Q hpmeet hv
        refine ⟨{
          inside := L.inside
          outside := L.outside
          edge := L.edge
          inside_mem := L.inside_mem
          outside_not_mem := L.outside_not_mem
          suffix := L.suffix
          suffix_avoids := L.suffix_avoids
          support_suffix := L.support_suffix.trans ?_ }⟩
        simpa using (List.suffix_cons u p.support)
      · have huQ : u ∈ Q := by
          rcases hmeet with ⟨x, hx, hxQ⟩
          simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hx
          exact hx.elim (fun hxu ↦ hxu ▸ hxQ)
            (fun hxp ↦ (hpmeet ⟨x, hxp, hxQ⟩).elim)
        have hpavoids : Avoids p Q := by
          intro x hx hxQ
          exact hpmeet ⟨x, hx, hxQ⟩
        refine ⟨{
          inside := u
          outside := w
          edge := hedge
          inside_mem := huQ
          outside_not_mem := hpavoids w p.start_mem_support
          suffix := p
          suffix_avoids := hpavoids
          support_suffix := ?_ }⟩
        simpa using (List.suffix_cons u p.support)

/-- The suffix supplied by `LastExit` remains a simple path. -/
theorem LastExit.suffix_isPath {u v : V} {p : DirectedPath.Walk D u v}
    {Q : Set V} (L : LastExit p Q) (hp : p.IsPath) : L.suffix.IsPath :=
  L.support_suffix.nodup hp

/-- `S` meets every simple `A`--`B` path avoiding `Q`. -/
def SeparatesAvoiding (D : Digraph V) (A B Q S : Set V) : Prop :=
  ∀ (a b : V) (p : DirectedPath.Walk D a b), p.IsPath →
    a ∈ A → b ∈ B → Avoids p Q → p.Meets S

/-- Every simple path from `y` to `B` which avoids `Q` meets `S`.  This is
the path-level formulation of membership in the roof of `S` in `D - Q`. -/
def RoofedAvoiding (D : Digraph V) (B Q S : Set V) (y : V) : Prop :=
  ∀ (b : V) (p : DirectedPath.Walk D y b), p.IsPath →
    b ∈ B → Avoids p Q → p.Meets S

/-- `S` meets every simple `A`--`B` path. -/
def Separates (D : Digraph V) (A B S : Set V) : Prop :=
  ∀ (a b : V) (p : DirectedPath.Walk D a b), p.IsPath →
    a ∈ A → b ∈ B → p.Meets S

/-- Boundary promotion, the path-theoretic content of Aharoni--Berger
Lemma 6.2.

The published lemma assumes `Q ⊆ V \ (A ∪ B)`.  The proof only needs
`Q ∩ B = ∅`; keeping the stronger source-side assumption out of this
helper is useful when restoring a temporarily deleted source vertex. -/
theorem separates_of_separatesAvoiding_of_outBoundary_roofed
    {A B Q S : Set V} (hQB : Disjoint Q B)
    (hsep : SeparatesAvoiding D A B Q S)
    (hroof : ∀ y ∈ outBoundary D Q, RoofedAvoiding D B Q S y) :
    Separates D A B S := by
  intro a b p hp ha hb
  by_cases hmeet : p.Meets Q
  · obtain ⟨L⟩ := exists_lastExit p Q hmeet
        (fun hbQ ↦ Set.disjoint_left.1 hQB hbQ hb)
    obtain ⟨x, hxSuffix, hxS⟩ := hroof L.outside
      ⟨L.outside_not_mem, L.inside, L.inside_mem, L.edge⟩
      b L.suffix (L.suffix_isPath hp) hb L.suffix_avoids
    exact ⟨x, L.support_suffix.subset hxSuffix, hxS⟩
  · apply hsep a b p hp ha hb
    intro x hx hxQ
    exact hmeet ⟨x, hx, hxQ⟩

/-! ### Transporting an avoiding finite path into a deleted web -/

/-- Regard a walk avoiding `Q` as a walk in the induced graph obtained by
deleting `Q`.  This is the converse, for finite walks, of
`DWeb.liftDeletePath`. -/
def toDelete (Γ : DWeb V) (Q : Set V) :
    ∀ {a b : V} (p : DirectedPath.Walk Γ.graph a b),
      Avoids p Q → DirectedPath.Walk (Γ.delete Q).graph a b
  | a, _, .nil, _ => .nil
  | a, b, .cons (v := c) edge p, havoid => by
      have ha : a ∉ Q := havoid a (by simp)
      have hpavoid : Avoids p Q := by
        intro x hx
        exact havoid x (by simp [hx])
      exact .cons ⟨edge, ha, hpavoid c p.start_mem_support⟩
        (toDelete Γ Q p hpavoid)

@[simp]
theorem support_toDelete (Γ : DWeb V) (Q : Set V)
    {a b : V} (p : DirectedPath.Walk Γ.graph a b) (havoid : Avoids p Q) :
    (toDelete Γ Q p havoid).support = p.support := by
  induction p with
  | nil => rfl
  | cons edge p ih =>
      change _ :: (toDelete Γ Q p _).support = _ :: p.support
      congr 1
      exact ih _

theorem isPath_toDelete (Γ : DWeb V) (Q : Set V)
    {a b : V} {p : DirectedPath.Walk Γ.graph a b}
    (hp : p.IsPath) (havoid : Avoids p Q) :
    (toDelete Γ Q p havoid).IsPath := by
  simpa [DirectedPath.Walk.IsPath] using hp

end Walk

namespace FinitePath

/-- Regard a finite path avoiding `Q` as a path in `Γ.delete Q`. -/
def toDelete (Γ : DWeb V) (Q : Set V)
    (p : DirectedPath.FinitePath Γ.graph)
    (havoid : Walk.Avoids p.walk Q) :
    DirectedPath.FinitePath (Γ.delete Q).graph where
  start := p.start
  finish := p.finish
  walk := Walk.toDelete Γ Q p.walk havoid
  isPath := Walk.isPath_toDelete Γ Q p.isPath havoid

@[simp]
theorem toDelete_start (Γ : DWeb V) (Q : Set V)
    (p : DirectedPath.FinitePath Γ.graph) (havoid : Walk.Avoids p.walk Q) :
    (toDelete Γ Q p havoid).start = p.start :=
  rfl

@[simp]
theorem toDelete_finish (Γ : DWeb V) (Q : Set V)
    (p : DirectedPath.FinitePath Γ.graph) (havoid : Walk.Avoids p.walk Q) :
    (toDelete Γ Q p havoid).finish = p.finish :=
  rfl

@[simp]
theorem support_toDelete (Γ : DWeb V) (Q : Set V)
    (p : DirectedPath.FinitePath Γ.graph) (havoid : Walk.Avoids p.walk Q) :
    (toDelete Γ Q p havoid).support = p.support := by
  ext x
  change x ∈ (Walk.toDelete Γ Q p.walk havoid).support ↔ x ∈ p.walk.support
  rw [Walk.support_toDelete]

end FinitePath

/-- Aharoni--Berger Lemma 6.2 (boundary promotion), for the concrete web
API.  A wave in `Γ - Q` lifts to a wave in `Γ` provided every first
vertex after an exit from `Q` is roofed by its terminal frontier.

The source hypothesis `Q ⊆ V \ (A ∪ B)` is represented by `hQ`; the
lift in the conclusion is necessary because deletion changes the ambient
digraph in the Lean type. -/
theorem lemma_6_2 (Γ : DWeb V) {Q : Set V}
    {U : Set ((Γ.delete Q).DPath)}
    (hQ : Q ⊆ (Γ.source ∪ Γ.target)ᶜ)
    (hU : (Γ.delete Q).IsWave U)
    (hboundary : Walk.outBoundary Γ.graph Q ⊆
      (Γ.delete Q).roof ((Γ.delete Q).terminalFrontier U)) :
    Γ.IsWave (Γ.liftDeleteFamily Q U) := by
  let S : Set V := (Γ.delete Q).terminalFrontier U
  have hQtarget : Disjoint Q Γ.target := by
    apply Set.disjoint_left.2
    intro x hxQ hxB
    exact hQ hxQ (by exact Or.inr hxB)
  have hsepAvoiding : Walk.SeparatesAvoiding Γ.graph Γ.source Γ.target Q S := by
    intro a b p hp ha hb havoid
    let original : DirectedPath.FinitePath Γ.graph :=
      { start := a, finish := b, walk := p, isPath := hp }
    let deleted : DirectedPath.FinitePath (Γ.delete Q).graph :=
      FinitePath.toDelete Γ Q original havoid
    have haQ : a ∉ Q := havoid a p.start_mem_support
    have hbQ : b ∉ Q := havoid b p.end_mem_support
    have hroof := hU.2.2 ⟨ha, haQ⟩
    have hmeet : (Γ.delete Q).Meets deleted S :=
      hroof deleted ⟨rfl, hb, hbQ⟩
    rcases hmeet with ⟨x, hxdeleted, hxS⟩
    have hxwalk : x ∈ p.support := by
      rw [FinitePath.support_toDelete] at hxdeleted
      exact hxdeleted
    exact ⟨x, hxwalk, hxS⟩
  have hroofAvoiding : ∀ y ∈ Walk.outBoundary Γ.graph Q,
      Walk.RoofedAvoiding Γ.graph Γ.target Q S y := by
    intro y hy b p hp hb havoid
    let original : DirectedPath.FinitePath Γ.graph :=
      { start := y, finish := b, walk := p, isPath := hp }
    let deleted : DirectedPath.FinitePath (Γ.delete Q).graph :=
      FinitePath.toDelete Γ Q original havoid
    have hbQ : b ∉ Q := fun hbQ ↦ Set.disjoint_left.1 hQtarget hbQ hb
    have hmeet : (Γ.delete Q).Meets deleted S :=
      hboundary hy deleted ⟨rfl, hb, hbQ⟩
    rcases hmeet with ⟨x, hxdeleted, hxS⟩
    have hxwalk : x ∈ p.support := by
      rw [FinitePath.support_toDelete] at hxdeleted
      exact hxdeleted
    exact ⟨x, hxwalk, hxS⟩
  have hseparates : Walk.Separates Γ.graph Γ.source Γ.target S :=
    Walk.separates_of_separatesAvoiding_of_outBoundary_roofed
      hQtarget hsepAvoiding hroofAvoiding
  apply hU.liftDeleteFamily
  intro a ha p hp
  have hpstart : p.start ∈ Γ.source := by
    rw [hp.1]
    exact ha
  obtain ⟨x, hxp, hxS⟩ :=
    hseparates p.start p.finish p.walk p.isPath hpstart hp.2
  exact ⟨x, hxp, hxS⟩

/-- The source-faithful form of Lemma 6.2 used at the end of Theorem 6.1.
The actually deleted set `D` may contain the distinguished source.  It is
contained in the larger tree set `T`, and `T` is disjoint from the target.
A path which meets `D` is handled at its last exit from `T`; a path avoiding
`D` is handled directly by the wave in `G.delete D`. -/
theorem tree_boundary_promotes_deleted_wave
    (G : DWeb V) {D T : Set V}
    (hDT : D ⊆ T) (hTtarget : Disjoint T G.target)
    {U : Set ((G.delete D).DPath)}
    (hU : (G.delete D).IsWave U)
    (hboundary : Walk.outBoundary G.graph T ⊆
      (G.delete D).roof ((G.delete D).terminalFrontier U)) :
    G.IsWave (G.liftDeleteFamily D U) := by
  let S : Set V := (G.delete D).terminalFrontier U
  apply DWeb.IsWave.liftDeleteFamily G hU
  intro b hb p hp
  by_cases hmeetD : p.walk.Meets D
  · have hmeetT : p.walk.Meets T := by
      obtain ⟨x, hxp, hxD⟩ := hmeetD
      exact ⟨x, hxp, hDT hxD⟩
    have hpfinishT : p.finish ∉ T := by
      intro hfinishT
      exact Set.disjoint_left.1 hTtarget hfinishT hp.2
    obtain ⟨L⟩ := Walk.exists_lastExit p.walk T hmeetT hpfinishT
    have hboundaryL : L.outside ∈ Walk.outBoundary G.graph T :=
      ⟨L.outside_not_mem, L.inside, L.inside_mem, L.edge⟩
    have hsuffixAvoidD : Walk.Avoids L.suffix D := by
      intro x hx hxD
      exact L.suffix_avoids x hx (hDT hxD)
    let original : DirectedPath.FinitePath G.graph :=
      { start := L.outside
        finish := p.finish
        walk := L.suffix
        isPath := L.suffix_isPath p.isPath }
    let deleted : DirectedPath.FinitePath (G.delete D).graph :=
      FinitePath.toDelete G D original hsuffixAvoidD
    have hpfinishD : p.finish ∉ D := fun hfinishD =>
      hpfinishT (hDT hfinishD)
    obtain ⟨x, hxdeleted, hxS⟩ :=
      hboundary hboundaryL deleted ⟨rfl, hp.2, hpfinishD⟩
    have hxsuffix : x ∈ L.suffix.support := by
      change x ∈ deleted.support at hxdeleted
      rw [FinitePath.support_toDelete] at hxdeleted
      exact hxdeleted
    exact ⟨x, L.support_suffix.subset hxsuffix, hxS⟩
  · have havoidD : Walk.Avoids p.walk D := by
      intro x hxp hxD
      exact hmeetD ⟨x, hxp, hxD⟩
    let deleted : DirectedPath.FinitePath (G.delete D).graph :=
      FinitePath.toDelete G D p havoidD
    have hbD : b ∉ D := havoidD b (hp.1 ▸ p.walk.start_mem_support)
    have hpfinishD : p.finish ∉ D :=
      havoidD p.finish p.walk.end_mem_support
    obtain ⟨x, hxdeleted, hxS⟩ := hU.2.2 ⟨hb, hbD⟩ deleted
      ⟨by simpa [deleted] using hp.1, hp.2, hpfinishD⟩
    have hxp : x ∈ p.support := by
      simpa [deleted] using hxdeleted
    exact ⟨x, hxp, hxS⟩

/-- If the deleted part of the tree contains an original source, promotion
produces the contradictory hindrance required in Theorem 6.1. -/
theorem hindrance_of_tree_boundary_wave
    (G : DWeb V) {D T : Set V}
    (hDT : D ⊆ T) (hTtarget : Disjoint T G.target)
    {U : Set ((G.delete D).DPath)}
    (hU : (G.delete D).IsWave U)
    (hboundary : Walk.outBoundary G.graph T ⊆
      (G.delete D).roof ((G.delete D).terminalFrontier U))
    {a : V} (ha : a ∈ G.source) (haD : a ∈ D) :
    G.IsHindrance (G.liftDeleteFamily D U) := by
  refine ⟨tree_boundary_promotes_deleted_wave G hDT hTtarget hU hboundary,
    ?_⟩
  intro heq
  have haInitial : a ∈ G.initialSet (G.liftDeleteFamily D U) :=
    heq.symm ▸ ha
  rw [G.initialSet_liftDeleteFamily D U] at haInitial
  exact (hU.2.1 haInitial).2 haD

/-- A roof-maximal wave absorbs any family of waves once a binary arrow
operation extends the accumulator and absorbs the input wave's roof.  This
is the order-theoretic final step in the `\uparrow` construction of Section 6. -/
theorem exists_wave_roofing_of_absorption
    (G : DWeb V) {Y : Set V}
    (hcover : ∀ y, y ∈ Y → ∃ W : G.Wave,
      y ∈ G.roof (G.terminalFrontier W.1))
    (habsorb : ∀ M U : G.Wave, ∃ Z : G.Wave,
      M ≤ Z ∧ G.RoofLE U.1 Z.1) :
    ∃ M : G.Wave, Y ⊆ G.roof (G.terminalFrontier M.1) := by
  obtain ⟨M, hMmax⟩ := G.exists_maximal_wave
  refine ⟨M, ?_⟩
  intro y hy
  obtain ⟨U, hyU⟩ := hcover y hy
  obtain ⟨Z, hMZ, hUZ⟩ := habsorb M U
  have hZM : Z ≤ M := hMmax hMZ
  have hyZ : y ∈ G.roof (G.terminalFrontier Z.1) := hUZ hyU
  exact (G.roofLE_of_forwardExtension M.property hZM) hyZ

/-- The concrete arrow construction supplies the absorption premise, so any
set covered pointwise by terminal roofs of waves is covered by one wave. -/
theorem exists_wave_roofing
    (G : DWeb V) {Y : Set V}
    (hcover : ∀ y, y ∈ Y → ∃ W : G.Wave,
      y ∈ G.roof (G.terminalFrontier W.1)) :
    ∃ M : G.Wave, Y ⊆ G.roof (G.terminalFrontier M.1) := by
  apply exists_wave_roofing_of_absorption G hcover
  exact fun M U ↦ G.exists_forwardExtension_roofLE M U

/-- Unlike essential frontiers, strict roofs are monotone in their defining
sets.  This elementary fact is used repeatedly in Lemmas 3.18 and 3.27. -/
theorem strictRoof_mono (G : DWeb V) {S T : Set V} (hST : S ⊆ T) :
    G.strictRoof S ⊆ G.strictRoof T := by
  intro z hz
  refine ⟨G.roof_mono hST hz.1, ?_⟩
  intro hzEss
  by_cases hzS : z ∈ S
  · have hzRoofWithout : z ∈ G.roof (S \ {z}) := by
      by_contra h
      exact hz.2 ⟨hzS, h⟩
    have hwithout : S \ {z} ⊆ T \ {z} := by
      intro x hx
      exact ⟨hST hx.1, hx.2⟩
    exact hzEss.2 (G.roof_mono hwithout hzRoofWithout)
  · have hsub : S ⊆ T \ {z} := by
      intro x hx
      exact ⟨hST hx, fun hxz ↦ hzS (hxz ▸ hx)⟩
    exact hzEss.2 (G.roof_mono hsub hz.1)

/-- Aharoni--Berger Lemma 3.18 for the concrete arrow: no essential
terminal of the arrow lies in the strict roof of the left input. -/
theorem arrow_essential_disjoint_strictRoof_left
    (G : DWeb V) {U W : Set G.DPath}
    (hU : G.IsWave U) (hW : G.IsWave W) :
    Disjoint
      (G.essential (G.terminalFrontier (G.arrow U W)))
      (G.strictRoof (G.terminalFrontier U)) := by
  rw [G.essential_terminalFrontier_arrow_eq_union hU hW]
  apply Set.disjoint_left.2
  intro z hzEss hzStrict
  by_cases hzU : z ∈ G.terminalFrontier U
  · have hzRoofWithout : z ∈ G.roof (G.terminalFrontier U \ {z}) := by
      by_contra h
      exact hzStrict.2 ⟨hzU, h⟩
    apply hzEss.2
    have hwithout : G.terminalFrontier U \ {z} ⊆
        (G.terminalFrontier U ∪ G.terminalFrontier W) \ {z} := by
      intro x hx
      exact ⟨Or.inl hx.1, hx.2⟩
    exact G.roof_mono hwithout hzRoofWithout
  · apply hzEss.2
    apply G.roof_mono _ hzStrict.1
    intro x hx
    exact ⟨Or.inl hx, fun hxz ↦ hzU (hxz ▸ hx)⟩

/-- The exact common-upper package from source Lemmas 3.13, 3.17, and
3.18.  Its asymmetric orientation is the one consumed by Corollary 3.28. -/
theorem exists_arrow_commonUpper_with_disjoint
    (G : DWeb V) (Vw R : G.Wave) :
    ∃ C : G.Wave,
      G.RoofLE Vw C.1 ∧ G.RoofLE R C.1 ∧
      Disjoint (G.essential (G.terminalFrontier C.1))
        (G.strictRoof (G.terminalFrontier R.1)) := by
  let C : G.Wave := ⟨G.arrow R.1 Vw.1, G.isWave_arrow R.2 Vw.2⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · exact G.roofLE_arrow_right R.2 Vw.2
  · exact G.roofLE_of_forwardExtension C.2
      (G.forwardExtension_arrow R.1 Vw.1)
  · exact arrow_essential_disjoint_strictRoof_left G R.2 Vw.2

/-! ### Arrowing with a wave in a vertex-deleted web (Lemma 3.14) -/

/-- Every vertex of a deleted-web wave, lifted to the ambient graph, is
roofed by the union of the original wave's frontier and the lifted
frontier, provided the deleted set is roofed by the original wave. -/
theorem liftDelete_vertex_roof_union
    (G : DWeb V) {Y : Set V} {U : Set G.DPath}
    {W : Set (G.delete Y).DPath}
    (_hU : G.IsWave U)
    (hY : Y ⊆ G.roof (G.terminalFrontier U))
    (hW : (G.delete Y).IsWave W) :
    G.vertexSet (G.liftDeleteFamily Y W) ⊆
      G.roof (G.terminalFrontier U ∪
        G.terminalFrontier (G.liftDeleteFamily Y W)) := by
  intro x hx p hp
  by_cases hmeetY : G.Meets p Y
  · obtain ⟨y, hyp, hyY⟩ := hmeetY
    let py := p.suffixFromAux y hyp
    have hpyTarget : G.IsTargetPathFrom y py := ⟨rfl, hp.2⟩
    obtain ⟨z, hzpy, hzU⟩ := hY hyY py hpyTarget
    exact ⟨z, p.suffixFromAux_support_subset y hyp hzpy, Or.inl hzU⟩
  · have havoid : Walk.Avoids p.walk Y := by
      intro z hzp hzY
      exact hmeetY ⟨z, hzp, hzY⟩
    let pd : DirectedPath.FinitePath (G.delete Y).graph :=
      FinitePath.toDelete G Y p havoid
    obtain ⟨q, hqW, hxq⟩ := hx
    obtain ⟨q0, hq0W, _hq0eq⟩ := hqW
    subst q
    have hxDeleted : x ∈ q0.support := by simpa using hxq
    have hxRoofDeleted : x ∈ (G.delete Y).roof
        ((G.delete Y).terminalFrontier W) :=
      (DWeb.IsWave.self_roofing (Γ := G.delete Y) hW)
        ⟨q0, hq0W, hxDeleted⟩
    have hpTargetDeleted : (G.delete Y).IsTargetPathFrom x pd := by
      exact ⟨hp.1, hp.2, havoid p.finish p.finish_mem_support⟩
    obtain ⟨z, hzpd, hzW⟩ := hxRoofDeleted pd hpTargetDeleted
    refine ⟨z, by simpa [pd] using hzpd, Or.inr ?_⟩
    simpa using hzW

/-- The essential-frontier argument underlying Lemma 3.14, stated with
the one exceptional overlap condition needed for a non-wave right input. -/
theorem essential_union_subset_terminalFrontier_arrow_of
    (G : DWeb V) {U W : Set G.DPath}
    (hU : G.IsWave U) (hWwarp : G.IsWarp W)
    (hWinitial : G.initialSet W ⊆ G.source)
    (hWspecial : ∀ z, z ∈ G.vertexSet W →
      z ∈ G.terminalFrontier U → z ∉ G.terminalFrontier W →
      z ∉ G.essential
        (G.terminalFrontier U ∪ G.terminalFrontier W)) :
    G.essential (G.terminalFrontier U ∪ G.terminalFrontier W) ⊆
      G.terminalFrontier (G.arrow U W) := by
  intro z hzEss
  let A := G.terminalFrontier U
  let B := G.terminalFrontier W
  simp only [DWeb.essential] at hzEss
  replace hzEss : z ∈ A ∪ B ∧ z ∉ G.roof ((A ∪ B) \ {z}) := by
    simpa [A, B] using hzEss
  have hzOld : z ∈ A ∪ B := hzEss.1
  have of_mem_A : z ∈ A → z ∈ G.terminalFrontier (G.arrow U W) := by
    intro hzA
    have hzA' : z ∈ G.terminalFrontier U := by simpa [A] using hzA
    obtain ⟨p, hpU, hpTerm⟩ := hzA
    rcases p with f | ray
    · have hfFinish : f.finish = z := Option.some.inj hpTerm
      rcases G.arrowPath_finite_cases U W f hpU with heq | ⟨c, _heq⟩
      · exact ⟨G.arrowPath U W ⟨.inl f, hpU⟩,
          ⟨⟨.inl f, hpU⟩, rfl⟩, by simpa [heq] using hpTerm⟩
      · by_cases hzB : z ∈ B
        · obtain ⟨q, hqW, hqTerm⟩ := hzB
          have hcq : c.path = q := by
            by_contra hne
            exact Set.disjoint_left.1 (hWwarp c.mem_path hqW hne)
              (hfFinish ▸ c.finish_mem) (G.terminal_mem_support hqTerm)
          have hcTerm : c.path.terminal? = some z := hcq ▸ hqTerm
          exact ⟨G.arrowPath U W ⟨.inl f, hpU⟩,
            ⟨⟨.inl f, hpU⟩, rfl⟩,
            G.terminal_arrowPath_of_candidate hWwarp hpU c hcTerm⟩
        · exfalso
          exact hWspecial z
            ⟨c.path, c.mem_path, hfFinish ▸ c.finish_mem⟩
            hzA' (by simpa [B] using hzB)
            (by simpa [A, B] using hzEss)
    · simp at hpTerm
  rcases hzOld with hzA | hzB
  · exact of_mem_A hzA
  · by_cases hzA : z ∈ A
    · exact of_mem_A hzA
    · obtain ⟨q, hqW, hqTerm⟩ := hzB
      rcases q with q | ray
      · have hqFinish : q.finish = z := Option.some.inj hqTerm
        have hqSource : q.start ∈ G.source :=
          hWinitial ⟨.inl q, hqW, rfl⟩
        obtain ⟨r, hrTarget, hrAvoid⟩ :=
          (G.not_mem_roof_iff ((A ∪ B) \ {z}) z).1 hzEss.2
        have hrStart : r.start = q.finish :=
          hrTarget.1.trans hqFinish.symm
        have hrAvoidA : G.Avoids r A := by
          change Disjoint r.support A
          change Disjoint r.support ((A ∪ B) \ {z}) at hrAvoid
          rw [Set.disjoint_left] at hrAvoid ⊢
          intro x hxr hxA
          apply hrAvoid hxr
          exact ⟨Or.inl hxA, by
            intro hxz
            have : x = z := by simpa using hxz
            exact hzA (this ▸ hxA)⟩
        obtain ⟨f, hfU, c, hcPath, _⟩ :=
          G.exists_arrow_candidate_ending hU hqW hqSource hrStart
            hrTarget.2 hrAvoidA
        have hcTerm : c.path.terminal? = some z := by
          rw [hcPath]
          exact hqTerm
        exact ⟨G.arrowPath U W ⟨.inl f, hfU⟩,
          ⟨⟨.inl f, hfU⟩, rfl⟩,
          G.terminal_arrowPath_of_candidate hWwarp hfU c hcTerm⟩
      · simp at hqTerm

/-- A lifted deleted-web wave cannot create an essential overlap at a
terminal of the left wave unless that point is also its own terminal. -/
theorem liftDelete_no_essential_overlap
    (G : DWeb V) {Y : Set V} {U : Set G.DPath}
    {W : Set (G.delete Y).DPath}
    (hY : Y ⊆ G.roof (G.terminalFrontier U))
    (hW : (G.delete Y).IsWave W) :
    ∀ z, z ∈ G.vertexSet (G.liftDeleteFamily Y W) →
      z ∈ G.terminalFrontier U →
      z ∉ G.terminalFrontier (G.liftDeleteFamily Y W) →
      z ∉ G.essential (G.terminalFrontier U ∪
        G.terminalFrontier (G.liftDeleteFamily Y W)) := by
  intro z hzVertex _hzU hzNotW hzEss
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (G.not_mem_roof_iff
      ((G.terminalFrontier U ∪
        G.terminalFrontier (G.liftDeleteFamily Y W)) \ {z}) z).1
      hzEss.2
  have hzNotY : z ∉ Y := by
    obtain ⟨q, ⟨q0, hq0W, rfl⟩, hzq⟩ := hzVertex
    have hqSource := hW.2.1 ⟨q0, hq0W, rfl⟩
    exact Set.disjoint_left.1
      (G.liftDeletePath_avoids Y q0 hqSource.2) hzq
  have hpAvoidY : Walk.Avoids p.walk Y := by
    intro y hyp hyY
    have hyNe : y ≠ z := fun hyz ↦ hzNotY (hyz ▸ hyY)
    let py := p.suffixFromAux y hyp
    have hpyTarget : G.IsTargetPathFrom y py := ⟨rfl, hpTarget.2⟩
    obtain ⟨u, hupy, huU⟩ := hY hyY py hpyTarget
    have hup : u ∈ p.support :=
      p.suffixFromAux_support_subset y hyp hupy
    have huNe : u ≠ z := by
      intro huz
      have hzSuffix : z ∈ (p.suffixData y hyp).walk.support := by
        have hzpy : z ∈ py.support := huz ▸ hupy
        exact hzpy
      have heq : (p.suffixData y hyp).walk.support = p.walk.support := by
        apply List.Nodup.eq_of_head_mem_of_suffix
          (p.suffixData_support_suffix y hyp)
        · have hzhead : p.walk.support.head p.walk.support_ne_nil = z :=
            p.walk.head_support.trans hpTarget.1
          rw [hzhead]
          exact hzSuffix
        · exact p.isPath
      have hheads := congrArg List.head? heq
      have hyz : y = z := by
        rw [List.head?_eq_head (p.suffixData y hyp).walk.support_ne_nil,
          (p.suffixData y hyp).walk.head_support,
          List.head?_eq_head p.walk.support_ne_nil,
          p.walk.head_support] at hheads
        exact (Option.some.inj hheads).trans hpTarget.1
      exact hyNe hyz
    exact Set.disjoint_left.1 hpAvoid hup
      ⟨Or.inl huU, by simpa using huNe⟩
  let pd : DirectedPath.FinitePath (G.delete Y).graph :=
    FinitePath.toDelete G Y p hpAvoidY
  obtain ⟨q, ⟨q0, hq0W, rfl⟩, hzq⟩ := hzVertex
  have hzq0 : z ∈ q0.support := by simpa using hzq
  have hzRoof : z ∈ (G.delete Y).roof
      ((G.delete Y).terminalFrontier W) :=
    (DWeb.IsWave.self_roofing (Γ := G.delete Y) hW)
      ⟨q0, hq0W, hzq0⟩
  have hpdTarget : (G.delete Y).IsTargetPathFrom z pd := by
    exact ⟨hpTarget.1, hpTarget.2,
      hpAvoidY p.finish p.finish_mem_support⟩
  obtain ⟨w, hwpd, hwW⟩ := hzRoof pd hpdTarget
  have hwp : w ∈ p.support := by simpa [pd] using hwpd
  have hwLift : w ∈ G.terminalFrontier
      (G.liftDeleteFamily Y W) := by
    simpa using hwW
  have hwNe : w ≠ z := by
    intro hwz
    exact hzNotW (hwz ▸ hwLift)
  exact Set.disjoint_left.1 hpAvoid hwp
    ⟨Or.inr hwLift, by simpa using hwNe⟩

/-- Source Lemma 3.14: arrowing a wave with a wave in a deletion remains a
wave when the deleted set is roofed by the left wave. -/
theorem isWave_arrow_delete
    (G : DWeb V) {Y : Set V} {U : Set G.DPath}
    {W : Set (G.delete Y).DPath}
    (hU : G.IsWave U)
    (hY : Y ⊆ G.roof (G.terminalFrontier U))
    (hW : (G.delete Y).IsWave W) :
    G.IsWave (G.arrow U (G.liftDeleteFamily Y W)) := by
  let L := G.liftDeleteFamily Y W
  have hLwarp : G.IsWarp L := hW.1.liftDeleteFamily
  have hLinitial : G.initialSet L ⊆ G.source := by
    rw [G.initialSet_liftDeleteFamily]
    exact hW.2.1.trans Set.sdiff_subset
  have hLspecial := liftDelete_no_essential_overlap G hY hW
  have hEss : G.essential
      (G.terminalFrontier U ∪ G.terminalFrontier L) ⊆
      G.terminalFrontier (G.arrow U L) :=
    essential_union_subset_terminalFrontier_arrow_of G hU hLwarp
      hLinitial hLspecial
  have hterminalSubset := G.terminalFrontier_arrow_subset_union U L
  have hroof : G.roof (G.terminalFrontier (G.arrow U L)) =
      G.roof (G.terminalFrontier U ∪ G.terminalFrontier L) := by
    have hEssEq := RelationalRoof.essential_sandwich
      G.graph.Adj G.target hEss hterminalSubset
    calc
      G.roof (G.terminalFrontier (G.arrow U L)) =
          G.roof (G.essential (G.terminalFrontier (G.arrow U L))) :=
        (G.roof_essential _).symm
      _ = G.roof (G.essential
          (G.terminalFrontier U ∪ G.terminalFrontier L)) :=
        congrArg G.roof hEssEq
      _ = G.roof (G.terminalFrontier U ∪ G.terminalFrontier L) :=
        G.roof_essential _
  refine ⟨G.isWarp_arrow hU.1 hLwarp, ?_, ?_⟩
  · rw [← G.initialSet_eq_of_forwardExtension
      (G.forwardExtension_arrow U L)]
    exact hU.2.1
  · rw [hroof]
    exact hU.2.2.trans (G.roof_mono Set.subset_union_left)

/-- The common-upper consequence of Lemma 3.14 used in Assertion 6.8. -/
theorem exists_delete_arrow_commonUpper
    (G : DWeb V) {Y : Set V} {U : Set G.DPath}
    {W : Set (G.delete Y).DPath}
    (hU : G.IsWave U)
    (hY : Y ⊆ G.roof (G.terminalFrontier U))
    (hW : (G.delete Y).IsWave W) :
    ∃ C : G.Wave,
      G.RoofLE U C.1 ∧
      (G.delete Y).terminalFrontier W ⊆
        G.roof (G.terminalFrontier C.1) := by
  let L := G.liftDeleteFamily Y W
  let C : G.Wave :=
    ⟨G.arrow U L, isWave_arrow_delete G hU hY hW⟩
  refine ⟨C, G.roofLE_of_forwardExtension C.2
    (G.forwardExtension_arrow U L), ?_⟩
  intro z hz
  have hzL : z ∈ G.terminalFrontier L := by simpa [L] using hz
  have hroofEq : G.roof (G.terminalFrontier C.1) =
      G.roof (G.terminalFrontier U ∪ G.terminalFrontier L) := by
    let hLwarp : G.IsWarp L := hW.1.liftDeleteFamily
    let hLinitial : G.initialSet L ⊆ G.source := by
      rw [G.initialSet_liftDeleteFamily]
      exact hW.2.1.trans Set.sdiff_subset
    let hLspecial := liftDelete_no_essential_overlap G hY hW
    have hEss := essential_union_subset_terminalFrontier_arrow_of G hU
      hLwarp hLinitial hLspecial
    have hEssEq := RelationalRoof.essential_sandwich
      G.graph.Adj G.target hEss
      (G.terminalFrontier_arrow_subset_union U L)
    calc
      G.roof (G.terminalFrontier C.1) =
          G.roof (G.essential (G.terminalFrontier C.1)) :=
        (G.roof_essential _).symm
      _ = G.roof (G.essential
          (G.terminalFrontier U ∪ G.terminalFrontier L)) :=
        congrArg G.roof hEssEq
      _ = G.roof (G.terminalFrontier U ∪ G.terminalFrontier L) :=
        G.roof_essential _
  rw [hroofEq]
  exact G.subset_roof _ (Or.inr hzL)

/-- The stage-local heart of Assertion 6.8.  A wave in the complement of a
set already lying on a roof-maximal stage wave can be arrowed into that
stage; roof maximality then roofs each of its terminals at the stage. -/
theorem assertion_6_8_stage
    (G : DWeb V) {Y : Set V} {stage : Set G.DPath}
    {ending : Set (G.delete Y).DPath} {z : V}
    (hstage : G.IsWave stage)
    (hstageMax : G.IsRoofMaximal ⟨stage, hstage⟩)
    (hY : Y ⊆ G.vertexSet stage)
    (hending : (G.delete Y).IsWave ending)
    (hz : z ∈ (G.delete Y).terminalFrontier ending) :
    z ∈ G.roof (G.terminalFrontier stage) := by
  have hYRoof : Y ⊆ G.roof (G.terminalFrontier stage) :=
    hY.trans (DWeb.IsWave.self_roofing (Γ := G) hstage)
  obtain ⟨C, hstageC, hendingC⟩ :=
    exists_delete_arrow_commonUpper G hstage hYRoof hending
  have hCstage : G.RoofLE C.1 stage :=
    hstageMax C hstageC
  exact hCstage (hendingC hz)

/-- Deleting `R` and then the remainder of a larger set `X` is deletion
of `X`.  This equality is the dependent transport used in Assertion 6.8. -/
theorem delete_sdiff_of_subset (G : DWeb V) {R X : Set V}
    (hRX : R ⊆ X) :
    (G.delete R).delete (X \ R) = G.delete X := by
  rw [G.delete_delete]
  congr 1
  ext x
  constructor
  · rintro (hxR | ⟨hxX, _⟩)
    · exact hRX hxR
    · exact hxX
  · intro hxX
    by_cases hxR : x ∈ R
    · exact Or.inl hxR
    · exact Or.inr ⟨hxX, hxR⟩

/-! ## The root-deletion base case -/

/-- Deleting one source from an unhindered web remains unhindered.

This is the implicit base case of the tree construction in the proof of
Theorem 6.1.  A hypothetical wave in `Γ - a` is lifted and supplemented by
the trivial path at `a`.  The added singleton deals exactly with paths which
meet the restored source, so a hindrance downstairs would give a hindrance in
`Γ`. -/
theorem delete_source_isUnhindered (Γ : DWeb V) {a : V}
    (hΓ : Γ.IsUnhindered) (ha : a ∈ Γ.source) :
    (Γ.delete {a}).IsUnhindered := by
  rw [(Γ.delete {a}).isUnhindered_iff]
  intro W hW
  let L : Set Γ.DPath := Γ.liftDeleteFamily {a} W
  let R : Set Γ.DPath := insert (Γ.trivialPath a) L
  have hLavoid : Disjoint (Γ.vertexSet L) ({a} : Set V) := by
    exact Γ.vertexSet_liftDeleteFamily_disjoint hW.2.1
  have hLwarp : Γ.IsWarp L := hW.1.liftDeleteFamily
  have hRwarp : Γ.IsWarp R := by
    rintro p hp q hq hpq
    change Disjoint p.support q.support
    rcases hp with rfl | hpL
    · rcases hq with hq | hqL
      · exact (hpq hq.symm).elim
      · rw [Γ.support_trivialPath]
        apply Set.disjoint_left.2
        intro x hxa hxq
        have hxa' : x = a := by simpa using hxa
        subst x
        exact Set.disjoint_left.1 hLavoid
          (Γ.mem_vertexSet.mpr ⟨q, hqL, hxq⟩) (Set.mem_singleton a)
    · rcases hq with rfl | hqL
      · rw [Γ.support_trivialPath]
        apply Set.disjoint_right.2
        intro x hxa hxp
        have hxa' : x = a := by simpa using hxa
        subst x
        exact Set.disjoint_left.1 hLavoid
          (Γ.mem_vertexSet.mpr ⟨p, hpL, hxp⟩) (Set.mem_singleton a)
      · exact hLwarp hpL hqL hpq
  have hRinitial : Γ.initialSet R = insert a ((Γ.delete {a}).initialSet W) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with rfl | hpL
      · exact Set.mem_insert a _
      · exact Set.mem_insert_of_mem a (by
          rw [← Γ.initialSet_liftDeleteFamily {a} W]
          exact ⟨p, hpL, rfl⟩)
    · intro hx
      rcases hx with hxa | hx
      · exact ⟨Γ.trivialPath a, Set.mem_insert _ _,
          (Γ.initial_trivialPath a).trans hxa.symm⟩
      · rw [← Γ.initialSet_liftDeleteFamily {a} W] at hx
        obtain ⟨p, hpL, hpx⟩ := hx
        exact ⟨p, Set.mem_insert_of_mem _ hpL, hpx⟩
  have hRstart : Γ.initialSet R ⊆ Γ.source := by
    rw [hRinitial]
    exact Set.insert_subset ha (hW.2.1.trans Set.sdiff_subset)
  have haFrontier : a ∈ Γ.terminalFrontier R := by
    exact ⟨Γ.trivialPath a, Set.mem_insert _ _, Γ.terminal?_trivialPath a⟩
  have hRseparates : Γ.source ⊆ Γ.roof (Γ.terminalFrontier R) := by
    intro b hb p hp
    by_cases hpmeets : (p.support ∩ ({a} : Set V)).Nonempty
    · obtain ⟨x, hxp, hxa⟩ := hpmeets
      have hxa' : x = a := by simpa using hxa
      exact ⟨x, hxp, hxa' ▸ haFrontier⟩
    · have havoid : Walk.Avoids p.walk ({a} : Set V) := by
        intro x hxp hxa
        exact hpmeets ⟨x, hxp, hxa⟩
      let q : DirectedPath.FinitePath (Γ.delete {a}).graph :=
        FinitePath.toDelete Γ {a} p havoid
      have hbDelete : b ∈ (Γ.delete {a}).source := by
        exact ⟨hb, havoid b (hp.1 ▸ p.walk.start_mem_support)⟩
      have hpfinishDelete : p.finish ∈ (Γ.delete {a}).target := by
        exact ⟨hp.2, havoid p.finish p.walk.end_mem_support⟩
      obtain ⟨x, hxq, hxFrontier⟩ :=
        hW.2.2 hbDelete q
          ⟨by simpa [q] using hp.1, by simpa [q] using hpfinishDelete⟩
      obtain ⟨r, hrW, hrterm⟩ := hxFrontier
      have hxSupport : x ∈ p.support := by
        simpa [q] using hxq
      have hxR : x ∈ Γ.terminalFrontier R := by
        refine ⟨Γ.liftDeletePath {a} r, Set.mem_insert_of_mem _ ?_, ?_⟩
        · exact ⟨r, hrW, rfl⟩
        · simpa using hrterm
      exact ⟨x, hxSupport, hxR⟩
  have hReq : Γ.initialSet R = Γ.source :=
    (Γ.isUnhindered_iff.mp hΓ) R ⟨hRwarp, hRstart, hRseparates⟩
  apply Set.Subset.antisymm hW.2.1
  intro x hx
  have hxa : x ≠ a := hx.2
  have hxR : x ∈ Γ.initialSet R := by
    rw [hReq]
    exact hx.1
  rw [hRinitial] at hxR
  exact hxR.resolve_left hxa

/-- Lifting a safe path from the normalized web preserves safety and makes
its endpoint purity explicit.  This is the strengthened one-point interface
used by the later linkage recursion. -/
theorem exists_endpointPure_safeTargetPath_of_normalized
    (G : DWeb V) {a : V} (h : G.normalized.HasSafeTargetPath a) :
    ∃ p : DirectedPath.FinitePath G.graph,
      G.IsSafeTargetPath a p ∧
      p.support ∩ G.source ⊆ {p.start} ∧
      p.support ∩ G.target ⊆ {p.finish} := by
  obtain ⟨p, hpStart, hpTarget, hpSafe⟩ := h
  let q := G.liftNormalizedFinitePath p
  have hqSafe : G.IsSafeTargetPath a q := by
    refine ⟨hpStart, ?_, ?_⟩
    · change p.finish ∈ G.target
      simpa using hpTarget
    · apply DWeb.IsUnhindered.of_normalized
      rw [G.delete_normalized, G.support_liftNormalizedFinitePath]
      exact hpSafe
  refine ⟨q, hqSafe, ?_, ?_⟩
  · intro x hx
    have hxp : x ∈ p.support := by simpa [q] using hx.1
    have hxStart : x = p.start :=
      DWeb.IsNormalized.eq_start_of_mem_walk
        (Γ := G.normalized) G.normalized_isNormalized p.walk hxp hx.2
    change x = q.start
    exact hxStart
  · intro x hx
    have hxp : x ∈ p.support := by simpa [q] using hx.1
    have hxFinish : x = p.finish :=
      DWeb.IsNormalized.eq_finish_of_mem_walk
        (Γ := G.normalized) G.normalized_isNormalized p.walk hxp hx.2
    change x = q.finish
    exact hxFinish

/-- The maximal rooted tree required in the proof of Theorem 6.1 exists in
every unhindered web.  The seemingly additional base hypothesis in
`DWeb.exists_maximalTreeSet` is discharged by
`delete_source_isUnhindered`. -/
theorem exists_maximalTreeSet_of_isUnhindered (Γ : DWeb V) {a : V}
    (hΓ : Γ.IsUnhindered) (ha : a ∈ Γ.source) :
    ∃ T : Set V, Maximal (Γ.IsTreeSet a) T :=
  Γ.exists_maximalTreeSet ha (delete_source_isUnhindered Γ hΓ ha)

/-- Under the negation of the safe-link conclusion, the maximal rooted tree
can be chosen disjoint from the target.  This is the exact initial setup of
the contradiction proof of Aharoni--Berger Theorem 6.1. -/
theorem exists_maximalTreeSet_disjoint_target
    (Γ : DWeb V) {a : V} (hΓ : Γ.IsUnhindered)
    (ha : a ∈ Γ.source) (hnone : ¬ Γ.HasSafeTargetPath a) :
    ∃ T : Set V, Maximal (Γ.IsTreeSet a) T ∧ Disjoint T Γ.target := by
  obtain ⟨T, hT⟩ := exists_maximalTreeSet_of_isUnhindered Γ hΓ ha
  exact ⟨T, hT, Γ.disjoint_target_of_not_hasSafeTargetPath hT.1 hnone⟩

/-- In a normalized web, an outer-boundary vertex of a rooted tree is not a
source.  This is the only use of the "no edge enters the source" half of
Aharoni--Berger Assumption 2.1 in the maximal-tree step. -/
theorem outerBoundary_subset_source_compl
    (Γ : DWeb V) (hΓ : Γ.IsNormalized) (T : Set V) :
    Γ.outerBoundary T ⊆ Γ.sourceᶜ := by
  rintro y ⟨_hyT, t, _htT, hty⟩ hyA
  exact (hΓ hty).1 hyA

/-- For a maximal rooted tree in a normalized web, every outer-boundary
vertex has a finite obstruction.  This is the exact obstruction assignment
`y ↦ F_y` used by the closing-up construction in Section 6. -/
theorem exists_finite_obstruction_of_maximal_normalized
    (Γ : DWeb V) (hΓ : Γ.IsNormalized) {a : V} {T : Set V}
    (hT : Maximal (Γ.IsTreeSet a) T) {y : V}
    (hy : y ∈ Γ.outerBoundary T) :
    ∃ F : Set V, F.Finite ∧ F ⊆ T \ {a} ∧
      ¬ Γ.SafeAfterRootDeletion a (insert y F) :=
  Γ.exists_finite_obstruction_of_maximal hT hy
    (outerBoundary_subset_source_compl Γ hΓ T hy)

/-- In a normalized web, deleting a source creates no new target paths
from a different vertex.  Thus roofs away from that source lift back to the
ambient web. -/
theorem roof_delete_source_subset_ambient_of_ne
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {S : Set V} {v : V} (hva : v ≠ a)
    (hv : v ∈ (G.delete {a}).roof S) :
    v ∈ G.roof S := by
  intro p hp
  have havoid : Walk.Avoids p.walk ({a} : Set V) := by
    intro x hxp hxa
    have hxa' : x = a := Set.mem_singleton_iff.mp hxa
    have hxSource : x ∈ G.source := hxa'.symm ▸ ha
    have hxStart : x = p.start :=
      hG.eq_start_of_mem_walk p.walk hxp hxSource
    have hxv : x = v := hxStart.trans hp.1
    exact hva (hxv.symm.trans hxa')
  let q : DirectedPath.FinitePath (G.delete {a}).graph :=
    FinitePath.toDelete G {a} p havoid
  have hq : (G.delete {a}).IsTargetPathFrom v q := by
    constructor
    · simpa [q] using hp.1
    · exact ⟨hp.2, havoid p.finish p.finish_mem_support⟩
  obtain ⟨s, hsq, hsS⟩ := hv q hq
  exact ⟨s, by simpa [q] using hsq, hsS⟩

/-- Strict-roof version of `roof_delete_source_subset_ambient_of_ne`. -/
theorem strictRoof_delete_source_subset_ambient_of_ne
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {S : Set V} {v : V} (hva : v ≠ a)
    (hv : v ∈ (G.delete {a}).strictRoof S) :
    v ∈ G.strictRoof S := by
  refine ⟨roof_delete_source_subset_ambient_of_ne G hG ha hva hv.1, ?_⟩
  intro hvEssential
  apply hv.2
  refine ⟨hvEssential.1, ?_⟩
  intro hvDeleteRoof
  exact hvEssential.2
    (roof_delete_source_subset_ambient_of_ne G hG ha hva hvDeleteRoof)

/-- A totalized choice of the finite obstruction `F_y`.  Off the outer
boundary it is empty; on the boundary it is the witness supplied by
maximality. -/
noncomputable def boundaryObstruction
    (Γ : DWeb V) (hΓ : Γ.IsNormalized) {a : V} {T : Set V}
    (hT : Maximal (Γ.IsTreeSet a) T) (y : V) : Set V := by
  classical
  exact if hy : y ∈ Γ.outerBoundary T then
      Classical.choose
        (exists_finite_obstruction_of_maximal_normalized Γ hΓ hT hy)
    else ∅

theorem boundaryObstruction_finite
    (Γ : DWeb V) (hΓ : Γ.IsNormalized) {a : V} {T : Set V}
    (hT : Maximal (Γ.IsTreeSet a) T) (y : V) :
    (boundaryObstruction Γ hΓ hT y).Finite := by
  classical
  by_cases hy : y ∈ Γ.outerBoundary T
  · simp only [boundaryObstruction, dif_pos hy]
    exact (Classical.choose_spec
      (exists_finite_obstruction_of_maximal_normalized Γ hΓ hT hy)).1
  · simp [boundaryObstruction, hy]

theorem boundaryObstruction_subset
    (Γ : DWeb V) (hΓ : Γ.IsNormalized) {a : V} {T : Set V}
    (hT : Maximal (Γ.IsTreeSet a) T) (y : V) :
    boundaryObstruction Γ hΓ hT y ⊆ T \ {a} := by
  classical
  by_cases hy : y ∈ Γ.outerBoundary T
  · simp only [boundaryObstruction, dif_pos hy]
    exact (Classical.choose_spec
      (exists_finite_obstruction_of_maximal_normalized Γ hΓ hT hy)).2.1
  · simp [boundaryObstruction, hy]

theorem boundaryObstruction_isUnsafe
    (Γ : DWeb V) (hΓ : Γ.IsNormalized) {a y : V} {T : Set V}
    (hT : Maximal (Γ.IsTreeSet a) T)
    (hy : y ∈ Γ.outerBoundary T) :
    ¬ Γ.SafeAfterRootDeletion a
      (insert y (boundaryObstruction Γ hΓ hT y)) := by
  classical
  simp only [boundaryObstruction, dif_pos hy]
  exact (Classical.choose_spec
    (exists_finite_obstruction_of_maximal_normalized Γ hΓ hT hy)).2.2

/-- Every off-root subset of a tree set is disjoint from the source that
remains after deleting the root. -/
theorem tree_offRoot_disjoint_delete_source
    (G : DWeb V) {a : V} {T F : Set V} (hT : G.IsTreeSet a T)
    (hF : F ⊆ T \ {a}) :
    Disjoint (G.delete {a}).source F := by
  apply Set.disjoint_left.2
  intro x hxSource hxF
  have hxa : x = a := by
    have hxSingleton := hT.2.1 ⟨(hF hxF).1, hxSource.1⟩
    simpa using hxSingleton
  exact hxSource.2 (hxa ▸ Set.mem_singleton a)

/-- A normalized web remains no-incoming-source after deleting its
distinguished source. -/
theorem delete_root_noEdgeEnters_source
    (G : DWeb V) (hG : G.IsNormalized) (a : V) :
    (G.delete {a}).NoEdgeEnters (G.delete {a}).source := by
  intro x y hxy hy
  exact (hG hxy.1).1 hy.1

/-! ## The last-exit step in Corollary 6.9 -/

/-- The source-exact path argument in Corollary 6.9, isolated from the
preceding ground-wave construction.

The retained family `W'` consists of finite paths.  Each starts either in the
source of the ground web or in the countable set `X ⊆ T`; its terminal avoids
`Q`, while Assertion 6.4(i) says that every terminal lying in `T` belongs to
`Q`.  Hence a path starting in `X` must leave `T`.  Its last exit is in the
outer boundary `Y`, and Assertion 6.8 roofs that boundary point. -/
theorem corollary_6_9_of_boundary_roof
    (G : DWeb V) {ground W' : Set G.DPath} {X T Q Y : Set V}
    (hground : G.IsWave ground)
    (hX : X ⊆ T)
    (hY : Walk.outBoundary G.graph T ⊆ Y)
    (hinitial : ∀ p ∈ W', p.initial ∈ G.source ∪ X)
    (hterminal : ∀ p ∈ W', ∃ t, G.terminal? p = some t ∧ t ∉ Q)
    (hterminalTree : G.terminalFrontier W' ∩ T ⊆ Q)
    (hboundaryRoof : Y ∩ G.vertexSet W' ⊆
      G.roof (G.terminalFrontier ground)) :
    ∀ p ∈ W', (p.support ∩ G.roof (G.terminalFrontier ground)).Nonempty := by
  intro p hp
  rcases hinitial p hp with hpSource | hpX
  · exact ⟨p.initial, p.initial_mem_support, hground.2.2 hpSource⟩
  · obtain ⟨t, hpterm, htQ⟩ := hterminal p hp
    rcases p with p | r
    · have hpfinish : p.finish = t := by
        simpa only [DWeb.terminal?_finite, Option.some.injEq] using hpterm
      have htT : t ∉ T := by
        intro ht
        apply htQ
        exact hterminalTree ⟨⟨Sum.inl p, hp, hpterm⟩, ht⟩
      have hpstartT : p.start ∈ T := hX hpX
      obtain ⟨L⟩ := Walk.exists_lastExit p.walk T
        ⟨p.start, p.walk.start_mem_support, hpstartT⟩
        (hpfinish.symm ▸ htT)
      have houtSupport : L.outside ∈ p.support :=
        L.support_suffix.subset L.suffix.start_mem_support
      have houtY : L.outside ∈ Y := hY
        ⟨L.outside_not_mem, L.inside, L.inside_mem, L.edge⟩
      have houtRoof : L.outside ∈ G.roof (G.terminalFrontier ground) :=
        hboundaryRoof ⟨houtY, G.mem_vertexSet.mpr ⟨Sum.inl p, hp, houtSupport⟩⟩
      exact ⟨L.outside, houtSupport, houtRoof⟩
    · simp at hpterm

/-- The final structural step of Assertion 6.6.  Once Assertion 6.5 rules
out `Q`-vertices as terminals and Lemma 3.28 plus the definition of
non-boundedness rule them out of the strict roof, self-roofing rules them out
of the whole vertex set of the ground wave. -/
theorem assertion_6_6_of_disjoint_terminal_and_strictRoof
    (G : DWeb V) {ground : Set G.DPath} {Q : Set V}
    (hground : G.IsWave ground)
    (hterminal : Disjoint Q (G.terminalFrontier ground))
    (hstrict : Disjoint Q (G.strictRoof (G.terminalFrontier ground))) :
    Disjoint (G.vertexSet ground) Q := by
  rw [Set.disjoint_left]
  intro q hqVertex hqQ
  have hqRoof : q ∈ G.roof (G.terminalFrontier ground) :=
    (DWeb.IsWave.self_roofing (Γ := G) hground) hqVertex
  by_cases hqEssential : q ∈ G.essential (G.terminalFrontier ground)
  · exact Set.disjoint_left.1 hterminal hqQ
      (G.essential_subset _ hqEssential)
  · exact Set.disjoint_left.1 hstrict hqQ ⟨hqRoof, hqEssential⟩

/-! ## Lifting quotient families to a fixed path type

The closing-up construction chooses its `i`th wave in a quotient depending
on `X_i`.  Those path families therefore have distinct Lean types.  The
paper silently regards every quotient path as a path of the original web;
the following image construction makes that coercion explicit. -/

/-- Lift every path of a quotient family back to the underlying web. -/
def liftQuotientFamily (G : DWeb V) (X : Set V)
    (W : Set (G.quotient X).DPath) : Set G.DPath :=
  G.liftQuotientPath X '' W

@[simp]
theorem mem_liftQuotientFamily_iff (G : DWeb V) (X : Set V)
    (W : Set (G.quotient X).DPath) (p : G.DPath) :
    p ∈ liftQuotientFamily G X W ↔
      ∃ q ∈ W, G.liftQuotientPath X q = p :=
  Iff.rfl

/-- Lifting a quotient warp preserves pairwise vertex-disjointness. -/
theorem isWarp_liftQuotientFamily (G : DWeb V) (X : Set V)
    {W : Set (G.quotient X).DPath} (hW : (G.quotient X).IsWarp W) :
    G.IsWarp (liftQuotientFamily G X W) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint (G.liftQuotientPath X p₀).support
    (G.liftQuotientPath X q₀).support
  rw [G.support_liftQuotientPath, G.support_liftQuotientPath]
  apply hW hp₀ hq₀
  intro hp₀q₀
  subst q₀
  exact hpq rfl

/-- Corollary 3.10 in the form needed by the general arrow lemma: when the
commitment set is disjoint from the source, every vertex used by a quotient
wave is roofed by that wave's frontier in the original web. -/
theorem quotientWave_vertexSet_subset_original_roof
    (G : DWeb V) {X : Set V} {W : Set (G.quotient X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceX : Disjoint G.source X)
    (hW : (G.quotient X).IsWave W) :
    (G.quotient X).vertexSet W ⊆
      G.roof ((G.quotient X).terminalFrontier W) := by
  let S := (G.quotient X).terminalFrontier W
  have hEss : G.essential X ⊆ G.roof S :=
    G.essential_subset_original_roof_of_quotient_wave
      hNoEnter hSourceX hW
  have hRoofX : G.roof X ⊆ G.roof S := by
    rw [← G.roof_essential X]
    exact G.roof_cut hEss
  intro x hxVertex p hp
  by_cases hmeet : G.Meets p (G.roof X)
  · obtain ⟨z, hzp, hzRoofX⟩ := hmeet
    let q := p.suffixFromAux z hzp
    have hqTarget : G.IsTargetPathFrom z q := ⟨rfl, hp.2⟩
    obtain ⟨s, hsq, hsS⟩ := hRoofX hzRoofX q hqTarget
    exact ⟨s, p.suffixFromAux_support_subset z hzp hsq, hsS⟩
  · have hstrict : ∀ {z}, z ∈ p.walk.support →
        z ∉ G.strictRoof X := by
      intro z hzp hzStrict
      exact hmeet ⟨z, hzp, hzStrict.1⟩
    have hcommit : ∀ {z}, z ∈ p.walk.support.tail → z ∉ X := by
      intro z hzp hzX
      exact hmeet ⟨z, List.mem_of_mem_tail hzp, G.subset_roof X hzX⟩
    let q := G.restrictFinitePathToQuotient X p hstrict hcommit
    have hqTarget : (G.quotient X).IsTargetPathFrom x q := by
      exact ⟨hp.1, hp.2⟩
    have hxQRoof : x ∈ (G.quotient X).roof S :=
      (DWeb.IsWave.self_roofing (Γ := G.quotient X) hW) hxVertex
    obtain ⟨s, hsq, hsS⟩ := hxQRoof q hqTarget
    exact ⟨s, by
      simpa only [q, G.support_restrictFinitePathToQuotient] using hsq,
      hsS⟩

@[simp]
theorem vertexSet_liftQuotientFamily (G : DWeb V) (X : Set V)
    (W : Set (G.quotient X).DPath) :
    G.vertexSet (liftQuotientFamily G X W) =
      (G.quotient X).vertexSet W := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, hx⟩
    exact ⟨q, hq, by simpa using hx⟩
  · rintro ⟨q, hq, hx⟩
    exact ⟨G.liftQuotientPath X q, ⟨q, hq, rfl⟩, by simpa using hx⟩

@[simp]
theorem initialSet_liftQuotientFamily (G : DWeb V) (X : Set V)
    (W : Set (G.quotient X).DPath) :
    G.initialSet (liftQuotientFamily G X W) =
      (G.quotient X).initialSet W := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, hx⟩
    exact ⟨q, hq, by simpa using hx⟩
  · rintro ⟨q, hq, hx⟩
    exact ⟨G.liftQuotientPath X q, ⟨q, hq, rfl⟩, by simpa using hx⟩

@[simp]
theorem terminalFrontier_liftQuotientFamily (G : DWeb V) (X : Set V)
    (W : Set (G.quotient X).DPath) :
    G.terminalFrontier (liftQuotientFamily G X W) =
      (G.quotient X).terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, hx⟩
    exact ⟨q, hq, by simpa using hx⟩
  · rintro ⟨q, hq, hx⟩
    exact ⟨G.liftQuotientPath X q, ⟨q, hq, rfl⟩, by simpa using hx⟩

/-- A canonical forward-maximal wave in a quotient.  This is a choice from
the proved concrete maximal-wave theorem, not an additional assumption. -/
noncomputable def maximalQuotientWave (G : DWeb V) (X : Set V) :
    (G.quotient X).Wave :=
  Classical.choose (G.quotient X).exists_maximal_wave

theorem maximalQuotientWave_isMax (G : DWeb V) (X : Set V) :
    IsMax (maximalQuotientWave G X) :=
  Classical.choose_spec (G.quotient X).exists_maximal_wave

/-- The canonical maximal quotient wave, represented in the fixed original
path type used by the Section 6 closure recursion. -/
noncomputable def maximalQuotientWaveLift (G : DWeb V) (X : Set V) :
    Set G.DPath :=
  liftQuotientFamily G X (maximalQuotientWave G X).1

theorem isWarp_maximalQuotientWaveLift (G : DWeb V) (X : Set V) :
    G.IsWarp (maximalQuotientWaveLift G X) :=
  isWarp_liftQuotientFamily G X (maximalQuotientWave G X).2.1

/-! ## Bounded tree vertices

The roof in the definition below is evaluated in the original web, exactly
as in Section 6.  Both quotient and deletion paths are explicitly lifted
before their terminal frontier is used. -/

/-- Lift a family first out of a quotient of `G - a`, then out of `G - a`
itself. -/
def liftDeleteQuotientFamily (G : DWeb V) (a : V) (X : Set V)
    (W : Set (((G.delete {a}).quotient X).DPath)) : Set G.DPath :=
  G.liftDeleteFamily {a}
    (liftQuotientFamily (G.delete {a}) X W)

/-- A concrete witness that the tree vertex `t` is bounded in the sense of
the proof of Theorem 6.1. -/
structure BoundedTreeWitness (G : DWeb V) (a : V) (T : Set V)
    (t : V) where
  carrier : Set V
  carrier_countable : carrier.Countable
  carrier_subset_tree : carrier ⊆ T \ {a}
  wave : Set (((G.delete {a}).quotient carrier).DPath)
  isWave : ((G.delete {a}).quotient carrier).IsWave wave
  mem_strictRoof : t ∈ G.strictRoof
    (G.terminalFrontier
      (liftDeleteQuotientFamily G a carrier wave))

/-- A vertex is bounded when it has a countable quotient-wave witness. -/
def IsBoundedTreeVertex (G : DWeb V) (a : V) (T : Set V) (t : V) : Prop :=
  Nonempty (BoundedTreeWitness G a T t)

/-- The non-bounded tree vertices, denoted `Q` in Section 6. -/
def nonBoundedTreeVertices (G : DWeb V) (a : V) (T : Set V) : Set V :=
  {t | t ∈ T ∧ ¬ IsBoundedTreeVertex G a T t}

theorem mem_nonBoundedTreeVertices_iff
    (G : DWeb V) (a : V) (T : Set V) (t : V) :
    t ∈ nonBoundedTreeVertices G a T ↔
      t ∈ T ∧ ¬ IsBoundedTreeVertex G a T t :=
  Iff.rfl

theorem nonBoundedTreeVertices_subset_tree
    (G : DWeb V) (a : V) (T : Set V) :
    nonBoundedTreeVertices G a T ⊆ T := by
  intro t ht
  exact ht.1

theorem insert_root_nonBounded_subset_tree
    (G : DWeb V) {a : V} {T : Set V} (hT : G.IsTreeSet a T) :
    insert a (nonBoundedTreeVertices G a T) ⊆ T := by
  apply Set.insert_subset
  · exact hT.1
  · exact nonBoundedTreeVertices_subset_tree G a T

@[simp]
theorem walk_outBoundary_eq_outerBoundary (G : DWeb V) (T : Set V) :
    Walk.outBoundary G.graph T = G.outerBoundary T :=
  rfl

/-- The final, source-independent assembly of Theorem 6.1.  Once every
outer-boundary point is roofed by some wave in the common deleted web, one
roof-maximal arrow wave roofs the whole boundary.  The last-exit lemma then
lifts it to a hindrance in the original web. -/
theorem isHindered_of_individual_boundary_waves
    (G : DWeb V) {a : V} {T Q : Set V}
    (hdeleted : insert a Q ⊆ T) (hTtarget : Disjoint T G.target)
    (ha : a ∈ G.source)
    (hcover : ∀ y ∈ G.outerBoundary T,
      ∃ U : Set ((G.delete (insert a Q)).DPath),
        (G.delete (insert a Q)).IsWave U ∧
          y ∈ (G.delete (insert a Q)).roof
            ((G.delete (insert a Q)).terminalFrontier U)) :
    G.IsHindered := by
  let H := G.delete (insert a Q)
  have hcover' : ∀ y, y ∈ G.outerBoundary T → ∃ W : H.Wave,
      y ∈ H.roof (H.terminalFrontier W.1) := by
    intro y hy
    obtain ⟨U, hU, hyU⟩ := hcover y hy
    exact ⟨⟨U, hU⟩, hyU⟩
  obtain ⟨M, hM⟩ :=
    exists_wave_roofing H (Y := G.outerBoundary T) hcover'
  exact ⟨G.liftDeleteFamily (insert a Q) M.1,
    hindrance_of_tree_boundary_wave G hdeleted hTtarget M.2
      (by simpa only [walk_outBoundary_eq_outerBoundary] using hM)
      ha (Set.mem_insert a Q)⟩

/-- The final normalized implication in source Theorem 6.1.  Proposition
6.3 is consumed pointwise: for the maximal rooted tree selected under the
negation of safety, every outer-boundary vertex is roofed by a wave in the
one common web obtained by deleting the root and the non-bounded vertices.
The preceding boundary-promotion theorem then produces a hindrance. -/
theorem exists_safeTargetPath_normalized_of_boundary_waves
    (G : DWeb V) (_hGnormalized : G.IsNormalized)
    (hG : G.IsUnhindered) {a : V} (ha : a ∈ G.source)
    (hboundary : ∀ {T : Set V}, Maximal (G.IsTreeSet a) T →
      Disjoint T G.target → ∀ y, y ∈ G.outerBoundary T →
        ∃ U : Set ((G.delete
            (insert a (nonBoundedTreeVertices G a T))).DPath),
          (G.delete (insert a (nonBoundedTreeVertices G a T))).IsWave U ∧
          y ∈ (G.delete
            (insert a (nonBoundedTreeVertices G a T))).roof
              ((G.delete
                (insert a (nonBoundedTreeVertices G a T))).terminalFrontier U)) :
    G.HasSafeTargetPath a := by
  by_contra hnone
  obtain ⟨T, hTmax, hTtarget⟩ :=
    exists_maximalTreeSet_disjoint_target G hG ha hnone
  let Q : Set V := nonBoundedTreeVertices G a T
  have hdeleted : insert a Q ⊆ T :=
    insert_root_nonBounded_subset_tree G hTmax.1
  have hcover : ∀ y ∈ G.outerBoundary T,
      ∃ U : Set ((G.delete (insert a Q)).DPath),
        (G.delete (insert a Q)).IsWave U ∧
          y ∈ (G.delete (insert a Q)).roof
            ((G.delete (insert a Q)).terminalFrontier U) := by
    intro y hy
    simpa only [Q] using hboundary hTmax hTtarget y hy
  exact hG (isHindered_of_individual_boundary_waves G hdeleted hTtarget ha hcover)

/-- Totalized choice of the countable grounding set `G_t`; it is empty at
non-bounded vertices. -/
noncomputable def groundingSet
    (G : DWeb V) (a : V) (T : Set V) (t : V) : Set V := by
  classical
  exact if ht : IsBoundedTreeVertex G a T t then
      (Classical.choice ht).carrier
    else ∅

theorem groundingSet_countable
    (G : DWeb V) (a : V) (T : Set V) (t : V) :
    (groundingSet G a T t).Countable := by
  classical
  by_cases ht : IsBoundedTreeVertex G a T t
  · simp only [groundingSet, dif_pos ht]
    exact (Classical.choice ht).carrier_countable
  · simp [groundingSet, ht]

theorem groundingSet_subset_tree
    (G : DWeb V) (a : V) (T : Set V) (t : V) :
    groundingSet G a T t ⊆ T := by
  classical
  by_cases ht : IsBoundedTreeVertex G a T t
  · simp only [groundingSet, dif_pos ht]
    exact (Classical.choice ht).carrier_subset_tree.trans Set.sdiff_subset
  · simp [groundingSet, ht]

/-- Grounding carriers may be chosen off the distinguished root, which is
already deleted in every quotient appearing in the boundedness definition. -/
theorem groundingSet_subset_offRoot
    (G : DWeb V) (a : V) (T : Set V) (t : V) :
    groundingSet G a T t ⊆ T \ {a} := by
  classical
  by_cases ht : IsBoundedTreeVertex G a T t
  · simp only [groundingSet, dif_pos ht]
    exact (Classical.choice ht).carrier_subset_tree
  · simp [groundingSet, ht]

/-- At a bounded vertex the totalized grounding set retains an actual wave
which strictly roofs that vertex in the original web. -/
theorem exists_wave_for_groundingSet
    (G : DWeb V) (a : V) (T : Set V) {t : V}
    (ht : IsBoundedTreeVertex G a T t) :
    ∃ W : Set (((G.delete {a}).quotient
        (groundingSet G a T t)).DPath),
      ((G.delete {a}).quotient (groundingSet G a T t)).IsWave W ∧
      t ∈ G.strictRoof
        (G.terminalFrontier
          (liftDeleteQuotientFamily G a (groundingSet G a T t) W)) := by
  classical
  let B := Classical.choice ht
  have hcarrier : groundingSet G a T t = B.carrier := by
    simp [groundingSet, ht, B]
  rw [hcarrier]
  exact ⟨B.wave, B.isWave, B.mem_strictRoof⟩

/-- The defining contradiction for `Q`: no non-bounded tree vertex can be
strictly roofed by a quotient wave over a countable subset of the tree. -/
theorem not_mem_strictRoof_of_mem_nonBounded
    (G : DWeb V) (a : V) (T : Set V) {q : V}
    (hq : q ∈ nonBoundedTreeVertices G a T)
    {X : Set V} (hXcount : X.Countable) (hXT : X ⊆ T \ {a})
    {W : Set (((G.delete {a}).quotient X).DPath)}
    (hW : ((G.delete {a}).quotient X).IsWave W) :
    q ∉ G.strictRoof
      (G.terminalFrontier (liftDeleteQuotientFamily G a X W)) := by
  intro hqRoof
  exact hq.2 ⟨{
    carrier := X
    carrier_countable := hXcount
    carrier_subset_tree := hXT
    wave := W
    isWave := hW
    mem_strictRoof := hqRoof }⟩

/-- Assertion 6.6 at one grounding stage.  Corollary 3.28 sends the strict
roof of the stage wave to a maximal wave in the quotient; normalization
then lifts that strict roof across deletion of the distinguished source.
Consequently a non-bounded tree vertex cannot lie on the stage wave. -/
theorem assertion_6_6_stage
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T R Q : Set V} (hT : G.IsTreeSet a T)
    (hRcountable : R.Countable) (hRT : R ⊆ T \ {a})
    {stage : Set (((G.delete {a}).delete R).DPath)}
    (hstage : ((G.delete {a}).delete R).IsWave stage)
    (hterminal : Disjoint Q
      (((G.delete {a}).delete R).terminalFrontier stage))
    (hQ : Q = nonBoundedTreeVertices G a T) :
    Disjoint (((G.delete {a}).delete R).vertexSet stage) Q := by
  let base := G.delete {a}
  let M := maximalQuotientWave base R
  have hNoEnter : base.NoEdgeEnters base.source := by
    intro x y hxy hy
    exact (hG hxy.1).1 hy.1
  have hSourceR : Disjoint base.source R := by
    apply Set.disjoint_left.2
    intro x hxSource hxR
    have hxa : x = a := by
      have hxSingleton := hT.2.1 ⟨(hRT hxR).1, hxSource.1⟩
      simpa using hxSingleton
    exact hxSource.2 (hxa ▸ Set.mem_singleton a)
  have hMwave : (base.quotient R).IsWave M.1 := M.2
  have hMmax : IsMax M := maximalQuotientWave_isMax base R
  have hGreatest : ∀ W : Set (base.quotient R).DPath,
      (base.quotient R).IsWave W → (base.quotient R).RoofLE W M.1 := by
    intro W hW
    exact (base.quotient R).roofLE_of_isMax hMmax ⟨W, hW⟩
  have hstrict :=
    base.delete_strictRoof_subset_original_strictRoof_of_roofGreatest_quotient
      hNoEnter hSourceR hstage hMwave hGreatest
  rw [Set.disjoint_left]
  intro q hqVertex hqQ
  have hqRoof : q ∈ (base.delete R).roof
      ((base.delete R).terminalFrontier stage) :=
    DWeb.IsWave.self_roofing (Γ := base.delete R) hstage hqVertex
  have hqNotTerminal : q ∉ (base.delete R).terminalFrontier stage :=
    fun hqTerminal ↦ Set.disjoint_left.1 hterminal hqQ hqTerminal
  have hqStrict : q ∈ (base.delete R).strictRoof
      ((base.delete R).terminalFrontier stage) := by
    refine ⟨hqRoof, ?_⟩
    intro hqEssential
    exact hqNotTerminal
      ((base.delete R).essential_subset _ hqEssential)
  obtain ⟨p, hp, hqp⟩ := hqVertex
  have hpSource : p.initial ∈ (base.delete R).source :=
    hstage.2.1 ⟨p, hp, rfl⟩
  have hqNotR : q ∉ R := by
    have hdisjoint := base.liftDeletePath_avoids R p hpSource.2
    exact Set.disjoint_left.1 hdisjoint (by simpa using hqp)
  have hqNeA : q ≠ a := by
    have hpNotA : p.initial ∉ ({a} : Set V) := hpSource.1.2
    have hdisjoint := G.liftDeletePath_avoids {a}
      (base.liftDeletePath R p) (by simpa using hpNotA)
    intro hqa
    apply Set.disjoint_left.1 hdisjoint
    · simpa using hqp
    · exact hqa ▸ Set.mem_singleton a
  have hqBaseStrict : q ∈ base.strictRoof
      ((base.quotient R).terminalFrontier M.1) :=
    hstrict ⟨hqStrict, hqNotR⟩
  have hqAmbientStrict : q ∈ G.strictRoof
      ((base.quotient R).terminalFrontier M.1) :=
    strictRoof_delete_source_subset_ambient_of_ne G hG ha hqNeA
      hqBaseStrict
  have hqBounded : IsBoundedTreeVertex G a T q := by
    refine ⟨{
      carrier := R
      carrier_countable := hRcountable
      carrier_subset_tree := hRT
      wave := M.1
      isWave := hMwave
      mem_strictRoof := ?_ }⟩
    simpa [liftDeleteQuotientFamily] using hqAmbientStrict
  rw [hQ] at hqQ
  exact hqQ.2 hqBounded

/-- Removing the unique member of a wave ending at a non-source terminal
produces a hindrance after deleting that terminal.  This is the local
finite-warp argument used in Assertion 6.5. -/
theorem hindered_delete_terminal_of_wave
    (H : DWeb V) {W : Set H.DPath} (hW : H.IsWave W)
    {t : V} (ht : t ∈ H.terminalFrontier W) (htSource : t ∉ H.source) :
    (H.delete {t}).IsHindered := by
  obtain ⟨p, hpW, hpt⟩ := ht
  let pW : W := ⟨p, hpW⟩
  have htSupport : t ∈ p.support := H.terminal_mem_support hpt
  let E := H.eraseMemberRestrictFamily W hW.1 pW htSupport
  have hEwarp : (H.delete {t}).IsWarp E :=
    DWeb.IsWarp.eraseMemberRestrictFamily H hW.1 pW htSupport
  have hEinitial : (H.delete {t}).initialSet E =
      H.initialSet W \ {p.initial} :=
    H.initialSet_eraseMemberRestrictFamily hW.1 pW htSupport
  have hEterminal : (H.delete {t}).terminalFrontier E =
      H.terminalFrontier W \ {t} :=
    H.terminalFrontier_eraseMemberRestrictFamily hW.1 pW htSupport hpt
  have hEsource : (H.delete {t}).initialSet E ⊆
      (H.delete {t}).source := by
    rw [hEinitial]
    intro x hx
    exact ⟨hW.2.1 hx.1, fun hxt ↦ htSource (hxt ▸ hW.2.1 hx.1)⟩
  have hEroof : (H.delete {t}).source ⊆
      (H.delete {t}).roof ((H.delete {t}).terminalFrontier E) := by
    intro a ha q hq
    let qH : DirectedPath.FinitePath H.graph := q.lift H.delete_adj_imp
    have hqH : H.IsTargetPathFrom a qH := ⟨hq.1, hq.2.1⟩
    obtain ⟨x, hxqH, hxTerm⟩ := hW.2.2 ha.1 qH hqH
    have hxq : x ∈ q.support := by simpa [qH] using hxqH
    have hxt : x ≠ t := by
      intro hxt
      have htq : t ∈ q.support := hxt ▸ hxq
      have hqInitial : DirectedPath.Path.initial
          (Sum.inl q : (H.delete ({t} : Set V)).DPath) ∉
            ({t} : Set V) := by
        change q.start ∉ ({t} : Set V)
        simpa [hq.1] using ha.2
      have havoid := H.liftDeletePath_avoids {t}
        (.inl q) hqInitial
      have htLift : t ∈ (H.liftDeletePath {t}
          (Sum.inl q : (H.delete ({t} : Set V)).DPath)).support := by
        rw [H.support_liftDeletePath]
        exact htq
      exact Set.disjoint_left.1 havoid htLift (Set.mem_singleton t)
    refine ⟨x, hxq, ?_⟩
    rw [hEterminal]
    exact ⟨hxTerm, by simpa using hxt⟩
  refine ⟨E, ⟨hEwarp, hEsource, hEroof⟩, ?_⟩
  intro heq
  have hpInitialSource : p.initial ∈ (H.delete {t}).source := by
    have hpSource := hW.2.1 ⟨p, hpW, rfl⟩
    exact ⟨hpSource, fun h ↦ htSource (by simpa using h ▸ hpSource)⟩
  have hpInE : p.initial ∈ (H.delete {t}).initialSet E :=
    heq.symm ▸ hpInitialSource
  rw [hEinitial] at hpInE
  exact hpInE.2 (Set.mem_singleton p.initial)

/-- Assertion 6.5: a ground-stage wave has no terminal in the maximal
tree.  Otherwise the preceding deletion lemma contradicts the finite-safety
invariant of the tree. -/
theorem assertion_6_5
    (G : DWeb V) {a : V} {T R : Set V}
    (hT : G.IsTreeSet a T)
    (hRfin : R.Finite) (hRT : R ⊆ T \ {a})
    {W : Set (G.delete (insert a R)).DPath}
    (hW : (G.delete (insert a R)).IsWave W) :
    Disjoint T ((G.delete (insert a R)).terminalFrontier W) := by
  rw [Set.disjoint_left]
  intro t htT htTerm
  have htNotA : t ≠ a := by
    intro hta
    subst t
    obtain ⟨p, hpW, hpa⟩ := htTerm
    have hpSource := hW.2.1 ⟨p, hpW, rfl⟩
    have havoid := G.liftDeletePath_avoids (insert a R) p hpSource.2
    exact Set.disjoint_left.1 havoid
      (G.terminal_mem_support (by simpa using hpa)) (Set.mem_insert a R)
  have htNotSource : t ∉ (G.delete (insert a R)).source := by
    intro htSource
    have hta : t = a := by
      have := hT.2.1 ⟨htT, htSource.1⟩
      simpa using this
    exact htNotA hta
  have hh := hindered_delete_terminal_of_wave
    (G.delete (insert a R)) hW htTerm htNotSource
  have hsafe := hT.2.2.2 (insert t R) (hRfin.insert t) (by
    apply Set.insert_subset
    · exact ⟨htT, htNotA⟩
    · exact hRT)
  have hunhindered :
      (G.delete (insert a (insert t R))).IsUnhindered := by
    simpa [DWeb.SafeAfterRootDeletion, DWeb.SafeDeletion] using hsafe
  have hh' : (G.delete (insert a (insert t R))).IsHindered := by
    simpa only [DWeb.delete_delete_singleton, Set.insert_comm] using hh
  exact (G.delete (insert a (insert t R))).isUnhindered_iff_not_isHindered.1
    hunhindered hh'

/-- The members of `W` which meet `X`. -/
def pathsMeeting (W : Set (DirectedPath.Path D)) (X : Set V) :
    Set (DirectedPath.Path D) :=
  {p | p ∈ W ∧ (p.support ∩ X).Nonempty}

/-- Only countably many members of a disjoint path family can meet a
countable vertex set. -/
theorem pathsMeeting_countable {W : Set (DirectedPath.Path D)} {X : Set V}
    (hW : W.PairwiseDisjoint DirectedPath.Path.support)
    (hX : X.Countable) : (pathsMeeting W X).Countable := by
  classical
  let f : DirectedPath.Path D → Set V := fun p ↦
    if p ∈ W then p.support ∩ X else ∅
  have hf : Pairwise (Function.onFun Disjoint f) := by
    intro p q hpq
    simp only [f]
    by_cases hp : p ∈ W
    · by_cases hq : q ∈ W
      · have hd := hW hp hq hpq
        apply hd.mono
        · simpa [f, hp] using
            (show p.support ∩ X ⊆ p.support from Set.inter_subset_left)
        · simpa [f, hq] using
            (show q.support ∩ X ⊆ q.support from Set.inter_subset_left)
      · change Disjoint (f p) (f q)
        rw [show f q = ∅ by simp [f, hq]]
        exact Set.disjoint_empty _
    · change Disjoint (f p) (f q)
      rw [show f p = ∅ by simp [f, hp]]
      exact Set.empty_disjoint _
  have hsub : ∀ p, f p ⊆ X := by
    intro p
    by_cases hp : p ∈ W <;> simp [f, hp]
  have hc := Set.countable_ofPred_nonempty_of_disjoint hf hsub hX
  have heq : {p | (f p).Nonempty} = pathsMeeting W X := by
    ext p
    by_cases hp : p ∈ W
    · simp [f, pathsMeeting, hp]
    · simp [f, pathsMeeting, hp]
  rwa [heq] at hc

/-- The vertices on members of `W` which meet `X`. -/
def verticesMeeting (W : Set (DirectedPath.Path D)) (X : Set V) : Set V :=
  ⋃ p ∈ pathsMeeting W X, p.support

/-- The vertices on those warp paths which meet a countable set are
countable.  Rays cause no problem because each ray itself is countable. -/
theorem verticesMeeting_countable {W : Set (DirectedPath.Path D)} {X : Set V}
    (hW : W.PairwiseDisjoint DirectedPath.Path.support)
    (hX : X.Countable) : (verticesMeeting W X).Countable := by
  have hpaths := pathsMeeting_countable hW hX
  exact hpaths.biUnion fun p _ ↦ DirectedPath.Path.support_countable p

/-! ## Countable closing-up -/

/-- The `n`th stage obtained by repeatedly applying `step`, starting at
`X₀`. -/
def closureStage (step : Set V → Set V) (X₀ : Set V) : ℕ → Set V
  | 0 => X₀
  | n + 1 => step (closureStage step X₀ n)

/-- The union of all finite stages of a closing-up process. -/
def omegaClosure (step : Set V → Set V) (X₀ : Set V) : Set V :=
  ⋃ n, closureStage step X₀ n

theorem closureStage_countable {step : Set V → Set V} {X₀ : Set V}
    (hX₀ : X₀.Countable)
    (hstep : ∀ X : Set V, X.Countable → (step X).Countable) :
    ∀ n, (closureStage step X₀ n).Countable
  | 0 => hX₀
  | n + 1 => hstep _ (closureStage_countable hX₀ hstep n)

theorem omegaClosure_countable {step : Set V → Set V} {X₀ : Set V}
    (hX₀ : X₀.Countable)
    (hstep : ∀ X : Set V, X.Countable → (step X).Countable) :
    (omegaClosure step X₀).Countable := by
  apply Set.countable_iUnion
  exact closureStage_countable hX₀ hstep

theorem closureStage_mono {step : Set V → Set V} {X₀ : Set V}
    (hinflate : ∀ X, X ⊆ step X) : Monotone (closureStage step X₀) := by
  apply monotone_nat_of_le_succ
  intro n
  exact hinflate _

theorem closureStage_subset_omegaClosure (step : Set V → Set V)
    (X₀ : Set V) (n : ℕ) :
    closureStage step X₀ n ⊆ omegaClosure step X₀ :=
  Set.subset_iUnion _ n

/-! ### The Section 6 recurrence -/

/-- The literal vertex-set recurrence used in the countable closing-up
part of the proof of Proposition 6.3.

`F z` is the finite obstruction attached to a boundary vertex, `G t` is
the countable witness attached to a bounded tree vertex, and `W i` is the
maximal wave chosen at stage `i`.  The notation
`verticesMeeting (W i) X` is the concrete form of
`V[W_i⟨X_i⟩]` in the paper. -/
def sectionSixClosureStage (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) : ℕ → Set V
  | 0 => F y
  | i + 1 =>
      let X := sectionSixClosureStage F G Y T Q W y i
      X ∪
        (⋃ z ∈ Y ∩ verticesMeeting (W i) X, F z) ∪
        (⋃ t ∈ X \ Q, G t) ∪
        (verticesMeeting (W i) X ∩ T)

/-- The final countable set `X = ⋃ i, X_i` in the Section 6
closing-up construction. -/
def sectionSixClosure (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) : Set V :=
  ⋃ i, sectionSixClosureStage F G Y T Q W y i

theorem sectionSixClosureStage_subset_succ
    (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) (i : ℕ) :
    sectionSixClosureStage F G Y T Q W y i ⊆
      sectionSixClosureStage F G Y T Q W y (i + 1) := by
  intro x hx
  exact Or.inl (Or.inl (Or.inl hx))

theorem sectionSixClosureStage_mono
    (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) :
    Monotone (sectionSixClosureStage F G Y T Q W y) := by
  apply monotone_nat_of_le_succ
  exact sectionSixClosureStage_subset_succ F G Y T Q W y

/-- Every stage in the Section 6 closing-up construction is countable.
This is the exact cardinal argument: disjointness makes the subfamily of a
warp meeting `X_i` countable, each of its paths has countable support, and
only countably many finite `F_z` and countable `G_t` are then added. -/
theorem sectionSixClosureStage_countable
    {F G : V → Set V} {Y T Q : Set V}
    {W : ℕ → Set (DirectedPath.Path D)} {y : V}
    (hF : ∀ z, (F z).Finite) (hG : ∀ t, (G t).Countable)
    (hW : ∀ i, (W i).PairwiseDisjoint DirectedPath.Path.support) :
    ∀ i, (sectionSixClosureStage F G Y T Q W y i).Countable
  | 0 => (hF y).countable
  | i + 1 => by
      let X := sectionSixClosureStage F G Y T Q W y i
      have hX : X.Countable := sectionSixClosureStage_countable hF hG hW i
      have hmeeting : (verticesMeeting (W i) X).Countable :=
        verticesMeeting_countable (hW i) hX
      have hboundary : (Y ∩ verticesMeeting (W i) X).Countable :=
        hmeeting.mono Set.inter_subset_right
      have hFUnion : (⋃ z ∈ Y ∩ verticesMeeting (W i) X, F z).Countable :=
        hboundary.biUnion fun z _ ↦ (hF z).countable
      have hbounded : (X \ Q).Countable := hX.mono Set.sdiff_subset
      have hGUnion : (⋃ t ∈ X \ Q, G t).Countable :=
        hbounded.biUnion fun t _ ↦ hG t
      have htree : (verticesMeeting (W i) X ∩ T).Countable :=
        hmeeting.mono Set.inter_subset_left
      exact ((hX.union hFUnion).union hGUnion).union htree

theorem sectionSixClosure_countable
    {F G : V → Set V} {Y T Q : Set V}
    {W : ℕ → Set (DirectedPath.Path D)} {y : V}
    (hF : ∀ z, (F z).Finite) (hG : ∀ t, (G t).Countable)
    (hW : ∀ i, (W i).PairwiseDisjoint DirectedPath.Path.support) :
    (sectionSixClosure F G Y T Q W y).Countable := by
  apply Set.countable_iUnion
  exact sectionSixClosureStage_countable hF hG hW

theorem sectionSixClosureStage_subset_closure
    (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) (i : ℕ) :
    sectionSixClosureStage F G Y T Q W y i ⊆
      sectionSixClosure F G Y T Q W y :=
  Set.subset_iUnion _ i

theorem sectionSixInitial_subset_closure
    (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) :
    F y ⊆ sectionSixClosure F G Y T Q W y := by
  exact sectionSixClosureStage_subset_closure F G Y T Q W y 0

/-- Closure invariant (b), at every finite stage. -/
theorem sectionSixF_subset_closure
    (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) (i : ℕ) {z : V}
    (hz : z ∈ Y ∩ verticesMeeting (W i)
      (sectionSixClosureStage F G Y T Q W y i)) :
    F z ⊆ sectionSixClosure F G Y T Q W y := by
  intro x hx
  apply sectionSixClosureStage_subset_closure F G Y T Q W y (i + 1)
  exact Or.inl (Or.inl (Or.inr
    (Set.mem_iUnion_of_mem z (Set.mem_iUnion_of_mem hz hx))))

/-- Closure invariant (c)'s set-inclusion part, at every finite stage. -/
theorem sectionSixG_subset_closure
    (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) (i : ℕ) {t : V}
    (ht : t ∈ sectionSixClosureStage F G Y T Q W y i \ Q) :
    G t ⊆ sectionSixClosure F G Y T Q W y := by
  intro x hx
  apply sectionSixClosureStage_subset_closure F G Y T Q W y (i + 1)
  exact Or.inl (Or.inr
    (Set.mem_iUnion_of_mem t (Set.mem_iUnion_of_mem ht hx)))

/-- Closure invariant (d), at every finite stage. -/
theorem sectionSixMeetingTree_subset_closure
    (F G : V → Set V) (Y T Q : Set V)
    (W : ℕ → Set (DirectedPath.Path D)) (y : V) (i : ℕ) :
    verticesMeeting (W i) (sectionSixClosureStage F G Y T Q W y i) ∩ T ⊆
      sectionSixClosure F G Y T Q W y := by
  intro x hx
  apply sectionSixClosureStage_subset_closure F G Y T Q W y (i + 1)
  exact Or.inr hx

/-! ## The maximal reachable set -/

/-- A set usable as a stage of the rooted-tree construction in the proof of
Theorem 6.1.

`Safe F` abstracts the source's exact invariant that deleting the root together
with the finite off-root set `F` leaves an unhindered web.  Thus the quantified
finite sets lie in `T \ {a}`.  This is the invariant stated in the v4 source:
`Γ - a - F` is unhindered for every finite `F ⊆ V(T)` not containing `a`. -/
def IsAdmissibleReachable (D : Digraph V) (A : Set V) (a : V)
    (Safe : Set V → Prop) (T : Set V) : Prop :=
  a ∈ T ∧
    T ∩ A = {a} ∧
    (∀ t ∈ T, ∃ p : DirectedPath.FinitePath D,
      p.start = a ∧ p.finish = t ∧ p.support ⊆ T) ∧
    ∀ F : Set V, F.Finite → F ⊆ T \ {a} → Safe F

/-- A finite subset of the union of an inclusion-chain is contained in one
member of the chain. -/
theorem finite_subset_sUnion_of_chain {c : Set (Set V)}
    (hc : IsChain (· ⊆ ·) c) (hcne : c.Nonempty)
    {F : Set V} (hF : F.Finite) (hFc : F ⊆ ⋃₀ c) :
    ∃ T ∈ c, F ⊆ T := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
      obtain ⟨T, hTc⟩ := hcne
      exact ⟨T, hTc, Set.empty_subset T⟩
  | @insert x F hx hF ih =>
      have hFsub : F ⊆ ⋃₀ c := by
        intro z hz
        exact hFc (Set.mem_insert_of_mem x hz)
      obtain ⟨TF, hTFc, hFTF⟩ := ih hFsub
      have hxc : x ∈ ⋃₀ c := hFc (Set.mem_insert x F)
      obtain ⟨Tx, hTxc, hxTx⟩ := Set.mem_sUnion.1 hxc
      by_cases hEq : Tx = TF
      · subst Tx
        exact ⟨TF, hTFc, Set.insert_subset hxTx hFTF⟩
      · rcases hc hTxc hTFc hEq with hTxTF | hTFTx
        · exact ⟨TF, hTFc, Set.insert_subset (hTxTF hxTx) hFTF⟩
        · exact ⟨Tx, hTxc, Set.insert_subset hxTx (hFTF.trans hTFTx)⟩

/-- Unions of nonempty chains of admissible reachable sets are again
admissible. -/
theorem sUnion_isAdmissibleReachable
    {A : Set V} {a : V} {Safe : Set V → Prop} {c : Set (Set V)}
    (hcsub : c ⊆ {T | IsAdmissibleReachable D A a Safe T})
    (hc : IsChain (· ⊆ ·) c) (hcnonempty : c.Nonempty) :
    IsAdmissibleReachable D A a Safe (⋃₀ c) := by
  have hchain_nonempty : c.Nonempty := hcnonempty
  obtain ⟨T₀, hT₀c⟩ := hcnonempty
  have hT₀ := hcsub hT₀c
  refine ⟨Set.mem_sUnion_of_mem hT₀.1 hT₀c, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨T, hTc, hxT⟩ := Set.mem_sUnion.1 hx.1
      rw [← (hcsub hTc).2.1]
      exact ⟨hxT, hx.2⟩
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.mp hx
      subst x
      have haA : a ∈ A := by
        have : a ∈ T₀ ∩ A := by
          rw [hT₀.2.1]
          exact Set.mem_singleton a
        exact this.2
      exact ⟨Set.mem_sUnion_of_mem hT₀.1 hT₀c, haA⟩
  · intro t ht
    obtain ⟨T, hTc, htT⟩ := Set.mem_sUnion.1 ht
    obtain ⟨p, hpstart, hpfinish, hpT⟩ := (hcsub hTc).2.2.1 t htT
    exact ⟨p, hpstart, hpfinish,
      hpT.trans (Set.subset_sUnion_of_mem hTc)⟩
  · intro F hF hFsub
    have hFsubUnion : F ⊆ ⋃₀ c := hFsub.trans Set.sdiff_subset
    obtain ⟨T, hTc, hFT⟩ :=
      finite_subset_sUnion_of_chain hc hchain_nonempty hF hFsubUnion
    apply (hcsub hTc).2.2.2 F hF
    intro x hx
    exact ⟨hFT hx, (hFsub hx).2⟩

/-- There is an inclusion-maximal admissible reachable set.  This is the
Zorn form of the transfinite rooted-tree construction in Aharoni--Berger's
proof of Theorem 6.1. -/
theorem exists_maximal_isAdmissibleReachable
    {A : Set V} {a : V} {Safe : Set V → Prop}
    (hbase : IsAdmissibleReachable D A a Safe {a}) :
    ∃ T : Set V, Maximal (IsAdmissibleReachable D A a Safe) T := by
  apply zorn_subset
  intro c hcsub hc
  by_cases hcne : c.Nonempty
  · exact ⟨⋃₀ c, sUnion_isAdmissibleReachable hcsub hc hcne,
      fun T hTc ↦ Set.subset_sUnion_of_mem hTc⟩
  · have hcempty : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hcne
    exact ⟨{a}, hbase, by simp [hcempty]⟩

end Erdos599.SafeLink
