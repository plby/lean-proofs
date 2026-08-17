/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.BoundedExpansions
import ErdosProblems.Erdos63.AvoidanceDeep
import ErdosProblems.Erdos63.SubdivisionExtremal
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log

/-!
# Simultaneous protected vertex expansions (Liu--Montgomery Lemma 3.11)

This file develops the finite ingredients of Liu--Montgomery Lemma 3.11:
shortest-cycle contact, bounded-degree ball packing, variable-rate avoiding
growth, extremal labelled path families, and path attachment.  The source
proof uses these simultaneously; in particular it never charges the full
orders of previously built expansions against one new root ball.

The final conclusion records disjointness after removing each prescribed
root.  This is the formulation needed when several requested expansions have
the same centre.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

universe u v

variable {V : Type u}
variable {G : SimpleGraph V}

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A cycle is shortest when no cycle in the graph has smaller length. -/
def IsShortestCycle {c : V} (C : G.Walk c c) : Prop :=
  C.IsCycle ∧ ∀ (x : V) (Q : G.Walk x x), Q.IsCycle → C.length ≤ Q.length

/-! ## Shortest-cycle contact kernels -/

/-- A simple cycle has as many distinct support vertices as edges. -/
theorem cycle_support_toFinset_card_eq_length
    {x : V} (p : G.Walk x x) (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  have hn : p.length ≥ 3 := hp.three_le_length
  rcases p with (_ | ⟨_, _, p⟩) <;>
    simp_all +decide [SimpleGraph.Walk.isCycle_def]
  rw [List.toFinset_card_of_nodup] <;> aesop

/-- Replacing one arc of a shortest cycle by a genuinely different path
cannot shorten that arc. -/
theorem IsShortestCycle.insideArc_length_le_shortcut
    {c a b : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (insideArc outsideArc shortcut : G.Walk a b)
    (houtside : outsideArc.IsPath)
    (hshortcut : shortcut.IsPath) (hne : shortcut ≠ outsideArc)
    (hsplit : C.length = insideArc.length + outsideArc.length) :
    insideArc.length ≤ shortcut.length := by
  obtain ⟨w, -, -, Q, hQ, hQlen⟩ :=
    hshortcut.exists_isCycle_length_le_add_of_ne houtside hne
  have hshort : C.length ≤ Q.length := hC.2 w Q hQ
  omega

/-- Arc-cover form of the local `2r+1` shortest-cycle estimate. -/
theorem IsShortestCycle.card_le_two_mul_add_one_of_arc_cover
    {c a b : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (insideArc outsideArc shortcut : G.Walk a b) (S : Finset V) (r : ℕ)
    (hinside : insideArc.IsPath) (houtside : outsideArc.IsPath)
    (hshortcut : shortcut.IsPath) (hne : shortcut ≠ outsideArc)
    (hsplit : C.length = insideArc.length + outsideArc.length)
    (hshortcutLen : shortcut.length ≤ 2 * r)
    (hcover : S ⊆ insideArc.support.toFinset) :
    S.card ≤ 2 * r + 1 := by
  have hlen : insideArc.length ≤ shortcut.length :=
    hC.insideArc_length_le_shortcut insideArc outsideArc shortcut
      houtside hshortcut hne hsplit
  have hcard : insideArc.support.toFinset.card = insideArc.length + 1 := by
    rw [List.toFinset_card_of_nodup hinside.support_nodup]
    exact insideArc.length_support
  calc
    S.card ≤ insideArc.support.toFinset.card := Finset.card_le_card hcover
    _ = insideArc.length + 1 := hcard
    _ ≤ 2 * r + 1 := Nat.add_le_add_right (hlen.trans hshortcutLen) 1

/-- Two radius-`r` paths to a common root give a simple shortcut of length at
most `2r`, supported inside the same ball. -/
theorem exists_shortcut_between_of_reachWithin_empty
    [Fintype V] {v a b : V} {r : ℕ}
    (ha : ReachWithin G (∅ : Set V) v r a)
    (hb : ReachWithin G (∅ : Set V) v r b) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length ≤ 2 * r ∧
      ∀ z ∈ q.support, z ∈ ballAvoiding G (∅ : Set V) v r := by
  obtain ⟨pa, hpa, hpalen⟩ := ha
  obtain ⟨pb, hpb, hpblen⟩ := hb
  let w : G.Walk a b := pa.reverse.append pb
  let q : G.Walk a b := w.bypass
  refine ⟨q, w.bypass_isPath, ?_, ?_⟩
  · calc
      q.length ≤ w.length := w.length_bypass_le_length
      _ = pa.length + pb.length := by simp [w]
      _ ≤ r + r := Nat.add_le_add hpalen hpblen
      _ = 2 * r := by omega
  · intro z hz
    have hzw : z ∈ w.support := w.support_bypass_subset_support hz
    simp only [w, Walk.mem_support_append_iff] at hzw
    rcases hzw with hza | hzb
    · have hza' : z ∈ pa.support := by
        simpa [Walk.support_reverse] using hza
      exact support_subset_ballAvoiding hpa hpalen z hza'
    · exact support_subset_ballAvoiding hpb hpblen z hzb

/-- If the proposed outside arc contains a vertex outside the ball, the
common-root shortcut is not that arc. -/
theorem exists_shortcut_ne_of_mem_outside_ball
    [Fintype V] {v a b z : V} {r : ℕ}
    (ha : ReachWithin G (∅ : Set V) v r a)
    (hb : ReachWithin G (∅ : Set V) v r b)
    (outsideArc : G.Walk a b) (hz : z ∈ outsideArc.support)
    (hzball : z ∉ ballAvoiding G (∅ : Set V) v r) :
    ∃ q : G.Walk a b,
      q.IsPath ∧ q.length ≤ 2 * r ∧ q ≠ outsideArc := by
  obtain ⟨q, hq, hqlen, hqsupport⟩ :=
    exists_shortcut_between_of_reachWithin_empty ha hb
  refine ⟨q, hq, hqlen, ?_⟩
  intro h
  subst q
  exact hzball (hqsupport z hz)

/-- Outside-arc form of the local shortest-cycle contact estimate. -/
theorem IsShortestCycle.card_le_two_mul_add_one_of_outside_arc
    [Fintype V] {c a b v z : V} {C : G.Walk c c}
    (hC : IsShortestCycle C) (insideArc outsideArc : G.Walk a b)
    (S : Finset V) (r : ℕ)
    (hinside : insideArc.IsPath) (houtside : outsideArc.IsPath)
    (hsplit : C.length = insideArc.length + outsideArc.length)
    (hcover : S ⊆ insideArc.support.toFinset)
    (ha : ReachWithin G (∅ : Set V) v r a)
    (hb : ReachWithin G (∅ : Set V) v r b)
    (hz : z ∈ outsideArc.support)
    (hzball : z ∉ ballAvoiding G (∅ : Set V) v r) :
    S.card ≤ 2 * r + 1 := by
  obtain ⟨q, hq, hqlen, hqne⟩ :=
    exists_shortcut_ne_of_mem_outside_ball ha hb outsideArc hz hzball
  exact hC.card_le_two_mul_add_one_of_arc_cover
    insideArc outsideArc q S r hinside houtside hq hqne hsplit hqlen hcover

/-- Every external neighbor of an avoiding singleton ball lies in the next
ordinary ball. -/
theorem externalNeighborhood_ballAvoidingFrom_singleton_subset_ball
    [Fintype V] (G : SimpleGraph V) (X : Set V) (v : V) (r : ℕ) :
    externalNeighborhood G (ballAvoidingFrom G X {v} r) ⊆
      ballAvoiding G (∅ : Set V) v (r + 1) := by
  classical
  intro y hy
  obtain ⟨hyS, x, hxS, hxy⟩ :=
    (mem_externalNeighborhood G (ballAvoidingFrom G X {v} r) y).1 hy
  obtain ⟨a, ha, p, hp, hlen⟩ :=
    (mem_ballAvoidingFrom G X {v} r x).1 hxS
  have hav : a = v := by simpa using ha
  subst a
  have hynp : y ∉ p.support := by
    intro hyp
    exact hyS (support_subset_ballAvoidingFrom ha hp hlen y hyp)
  rw [mem_ballAvoiding]
  refine ⟨p.concat hxy, ⟨hp.1.concat hynp hxy, ?_⟩, ?_⟩
  · simp
  · simpa only [p.length_concat] using Nat.add_le_add_right hlen 1

/-- A `2r+1` ordinary-ball contact estimate implies the exact
`HasLimitedContact` estimate needed by avoiding growth. -/
theorem hasLimitedContact_three_of_ball_inter_card_le
    [Fintype V] (G : SimpleGraph V) (v : V) (Cset : Finset V)
    (hcontact : ∀ r : ℕ,
      (Cset ∩ ballAvoiding G (∅ : Set V) v r).card ≤ 2 * r + 1) :
    HasLimitedContact G {v} (Cset : Set V) 3 := by
  intro r
  have hsub :
      blockedExternalNeighborhood G (Cset : Set V)
          (ballAvoidingFrom G (Cset : Set V) {v} r) ⊆
        Cset ∩ ballAvoiding G (∅ : Set V) v (r + 1) := by
    intro y hy
    obtain ⟨hyN, hyC⟩ :=
      (mem_blockedExternalNeighborhood G (Cset : Set V)
        (ballAvoidingFrom G (Cset : Set V) {v} r) y).1 hy
    exact Finset.mem_inter.2 ⟨hyC,
      externalNeighborhood_ballAvoidingFrom_singleton_subset_ball
        G (Cset : Set V) v r hyN⟩
  calc
    (blockedExternalNeighborhood G (Cset : Set V)
      (ballAvoidingFrom G (Cset : Set V) {v} r)).card ≤
        (Cset ∩ ballAvoiding G (∅ : Set V) v (r + 1)).card :=
      Finset.card_le_card hsub
    _ ≤ 2 * (r + 1) + 1 := hcontact (r + 1)
    _ ≤ 3 * (r + 1) := by omega

/-- An edge whose endpoints lie on the same distance level closes two
shortest root paths to a short cycle. -/
theorem IsShortestCycle.length_le_two_mul_add_one_of_adj_eq_dist
    {c v a b : V} {C : G.Walk c c} (hC : IsShortestCycle C) {r : ℕ}
    (hab : G.Adj a b)
    (ha : ReachWithin G (∅ : Set V) v r a)
    (hb : ReachWithin G (∅ : Set V) v r b)
    (hdist : G.dist v a = G.dist v b) :
    C.length ≤ 2 * r + 1 := by
  obtain ⟨wa, -, halen⟩ := ha
  obtain ⟨wb, -, hblen⟩ := hb
  have hra : G.Reachable v a := wa.reachable
  have hrb : G.Reachable v b := wb.reachable
  obtain ⟨pa, hpalen⟩ := hra.exists_walk_length_eq_dist
  obtain ⟨pb, hpblen⟩ := hrb.exists_walk_length_eq_dist
  have hpa : pa.IsPath := pa.isPath_of_length_eq_dist hpalen
  have hpb : pb.IsPath := pb.isPath_of_length_eq_dist hpblen
  have hanot : a ∉ pb.support := by
    intro hamem
    have hle := G.dist_le (pb.takeUntil a hamem)
    have hlt := pb.length_takeUntil_lt_length hamem (G.ne_of_adj hab)
    omega
  let q : G.Walk v a := pb.concat hab.symm
  have hq : q.IsPath := hpb.concat hanot hab.symm
  have hne : pa ≠ q := by
    intro heq
    have hlength := congrArg Walk.length heq
    simp only [q, pb.length_concat, hpalen, hpblen] at hlength
    omega
  obtain ⟨x, -, -, Q, hQ, hQlen⟩ :=
    hpa.exists_isCycle_length_le_add_of_ne hq hne
  have hshort : C.length ≤ Q.length := hC.2 x Q hQ
  have hda : G.dist v a ≤ r := (G.dist_le wa).trans halen
  have hdb : G.dist v b ≤ r := (G.dist_le wb).trans hblen
  simp only [q, pb.length_concat, hpalen, hpblen] at hQlen
  omega

/-- At a strict local distance maximum on a cycle, the two incident edges
close two distinct shortest paths. -/
theorem IsShortestCycle.length_le_two_mul_of_strict_local_max
    {c v x y z : V} {C : G.Walk c c} (hC : IsShortestCycle C) {r : ℕ}
    (hyx : G.Adj y x) (hzx : G.Adj z x) (hyz : y ≠ z)
    (hx : ReachWithin G (∅ : Set V) v r x)
    (hy : ReachWithin G (∅ : Set V) v r y)
    (hz : ReachWithin G (∅ : Set V) v r z)
    (hylt : G.dist v y < G.dist v x)
    (hzlt : G.dist v z < G.dist v x) :
    C.length ≤ 2 * r := by
  obtain ⟨wx, -, hxlen⟩ := hx
  obtain ⟨wy, -, -⟩ := hy
  obtain ⟨wz, -, -⟩ := hz
  have hry : G.Reachable v y := wy.reachable
  have hrz : G.Reachable v z := wz.reachable
  obtain ⟨py, hpylen⟩ := hry.exists_walk_length_eq_dist
  obtain ⟨pz, hpzlen⟩ := hrz.exists_walk_length_eq_dist
  have hpy : py.IsPath := py.isPath_of_length_eq_dist hpylen
  have hpz : pz.IsPath := pz.isPath_of_length_eq_dist hpzlen
  have hxnoty : x ∉ py.support := by
    intro hxmem
    have hle := G.dist_le (py.takeUntil x hxmem)
    have htake := py.length_takeUntil_le_length hxmem
    omega
  have hxnotz : x ∉ pz.support := by
    intro hxmem
    have hle := G.dist_le (pz.takeUntil x hxmem)
    have htake := pz.length_takeUntil_le_length hxmem
    omega
  let p : G.Walk v x := py.concat hyx
  let q : G.Walk v x := pz.concat hzx
  have hp : p.IsPath := hpy.concat hxnoty hyx
  have hq : q.IsPath := hpz.concat hxnotz hzx
  have hpq : p ≠ q := by
    intro heq
    have hpen := congrArg Walk.penultimate heq
    simp only [p, q, Walk.penultimate_concat] at hpen
    exact hyz hpen
  obtain ⟨w, -, -, Q, hQ, hQlen⟩ :=
    hp.exists_isCycle_length_le_add_of_ne hq hpq
  have hshort : C.length ≤ Q.length := hC.2 w Q hQ
  have hdx : G.dist v x ≤ r := (G.dist_le wx).trans hxlen
  simp only [p, q, py.length_concat, pz.length_concat,
    hpylen, hpzlen] at hQlen
  omega

/-- If the entire shortest cycle lies in a radius-`r` ball, its length is at
most `2r+1`. -/
theorem IsShortestCycle.length_le_two_mul_add_one_of_support_subset_ball
    [Fintype V] {c v : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (r : ℕ)
    (hcontain : C.support.toFinset ⊆
      ballAvoiding G (∅ : Set V) v r) :
    C.length ≤ 2 * r + 1 := by
  classical
  have hCnonempty : C.support.toFinset.Nonempty :=
    ⟨c, List.mem_toFinset.2 C.start_mem_support⟩
  obtain ⟨x, hxC, hmax⟩ :=
    C.support.toFinset.exists_max_image (G.dist v) hCnonempty
  have hxSupport : x ∈ C.support := List.mem_toFinset.1 hxC
  have hxReach : ReachWithin G (∅ : Set V) v r x :=
    (mem_ballAvoiding G (∅ : Set V) v r x).1 (hcontain hxC)
  let R : G.Walk x x := C.rotate x hxSupport
  have hRcycle : R.IsCycle := by
    simpa [R] using hC.1.rotate hxSupport
  let y : V := R.snd
  let z : V := R.penultimate
  have hyR : y ∈ R.support := by
    apply List.mem_of_mem_tail
    exact R.snd_mem_tail_support hRcycle.not_nil
  have hzR : z ∈ R.support := by
    apply List.mem_of_mem_dropLast
    exact R.penultimate_mem_dropLast_support hRcycle.not_nil
  have hyC : y ∈ C.support := by
    apply (C.mem_support_rotate_iff x hxSupport).1
    simpa [R] using hyR
  have hzC : z ∈ C.support := by
    apply (C.mem_support_rotate_iff x hxSupport).1
    simpa [R] using hzR
  have hyCfin : y ∈ C.support.toFinset := List.mem_toFinset.2 hyC
  have hzCfin : z ∈ C.support.toFinset := List.mem_toFinset.2 hzC
  have hyReach : ReachWithin G (∅ : Set V) v r y :=
    (mem_ballAvoiding G (∅ : Set V) v r y).1 (hcontain hyCfin)
  have hzReach : ReachWithin G (∅ : Set V) v r z :=
    (mem_ballAvoiding G (∅ : Set V) v r z).1 (hcontain hzCfin)
  have hymax : G.dist v y ≤ G.dist v x := hmax y hyCfin
  have hzmax : G.dist v z ≤ G.dist v x := hmax z hzCfin
  have hxy : G.Adj x y := by
    simpa [y] using R.adj_snd hRcycle.not_nil
  have hzx : G.Adj z x := by
    simpa [z] using R.adj_penultimate hRcycle.not_nil
  have hyz : y ≠ z := by
    simpa [y, z] using hRcycle.snd_ne_penultimate
  by_cases hyEq : G.dist v y = G.dist v x
  · exact hC.length_le_two_mul_add_one_of_adj_eq_dist
      hxy hxReach hyReach hyEq.symm
  by_cases hzEq : G.dist v z = G.dist v x
  · exact hC.length_le_two_mul_add_one_of_adj_eq_dist
      hzx hzReach hxReach hzEq
  have hylt : G.dist v y < G.dist v x := lt_of_le_of_ne hymax hyEq
  have hzlt : G.dist v z < G.dist v x := lt_of_le_of_ne hzmax hzEq
  have hshort := hC.length_le_two_mul_of_strict_local_max
    hxy.symm hzx hyz hxReach hyReach hzReach hylt hzlt
  omega

/-- Either the cycle has one contact with `B`, or it splits into two simple
`B`-to-`B` arcs, one covering every contact and the other containing a
vertex outside `B`. -/
theorem exists_cycle_contact_arcs
    {x : V} (C : G.Walk x x) (hC : C.IsCycle) (B : Finset V)
    (hin : ∃ y, y ∈ C.support ∧ y ∈ B)
    (hout : ∃ z, z ∈ C.support ∧ z ∉ B) :
    (∃ a ∈ B, ∀ y, y ∈ C.support → y ∈ B → y = a) ∨
      ∃ (a b z : V) (insideArc outsideArc : G.Walk a b),
        a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ z ∉ B ∧
        insideArc.IsPath ∧ outsideArc.IsPath ∧
        insideArc.length + outsideArc.length = C.length ∧
        C.support.toFinset ∩ B ⊆ insideArc.support.toFinset ∧
        z ∈ outsideArc.support ∧ z ≠ a ∧ z ≠ b ∧
        (∀ y, y ∈ outsideArc.support → y ∈ B → y = a ∨ y = b) := by
  classical
  obtain ⟨z, hzC, hzB⟩ := hout
  let R : G.Walk z z := C.rotate z hzC
  have hR : R.IsCycle := hC.rotate hzC
  have hcontacts : {y ∈ B | y ∈ R.support}.Nonempty := by
    obtain ⟨y, hyC, hyB⟩ := hin
    refine ⟨y, ?_⟩
    simp only [Finset.mem_filter]
    exact ⟨hyB, (Walk.mem_support_rotate_iff C z hzC).2 hyC⟩
  obtain ⟨a, haB, haR, hfirst⟩ :=
    R.exists_mem_support_forall_mem_support_imp_eq B hcontacts
  let p : G.Walk z a := R.takeUntil a haR
  let q : G.Walk a z := R.dropUntil a haR
  have hza : z ≠ a := by
    intro h
    apply hzB
    simpa [h] using haB
  have hp : p.IsPath := by simpa [p] using hR.isPath_takeUntil haR
  have hdecomp : p.append q = R := by simpa [p, q] using R.take_spec haR
  have hq : q.IsPath := by
    have hpne : ¬ p.Nil := Walk.not_nil_of_ne hza
    have hpqcycle : (p.append q).IsCycle := by rw [hdecomp]; exact hR
    exact hpqcycle.isPath_of_append_right hpne
  have hrevcontacts : {y ∈ B | y ∈ q.reverse.support}.Nonempty := by
    refine ⟨a, ?_⟩
    simp only [Finset.mem_filter]
    exact ⟨haB, by simpa [Walk.support_reverse] using q.start_mem_support⟩
  obtain ⟨b, hbB, hbqr, hlast⟩ :=
    q.reverse.exists_mem_support_forall_mem_support_imp_eq B hrevcontacts
  let u : G.Walk z b := q.reverse.takeUntil b hbqr
  let w : G.Walk b a := q.reverse.dropUntil b hbqr
  have hu : u.IsPath := by simpa [u] using hq.reverse.takeUntil hbqr
  have hw : w.IsPath := by simpa [w] using hq.reverse.dropUntil hbqr
  have hsplit : u.append w = q.reverse := by
    simpa [u, w] using q.reverse.take_spec hbqr
  by_cases hab : a = b
  · left
    refine ⟨a, haB, ?_⟩
    intro y hyC hyB
    have hyR : y ∈ R.support := (Walk.mem_support_rotate_iff C z hzC).2 hyC
    have hypq : y ∈ p.support ∨ y ∈ q.support := by
      rw [← Walk.mem_support_append_iff, hdecomp]
      exact hyR
    rcases hypq with hyp | hyq
    · exact hfirst y hyB (by simpa [p] using hyp)
    · have hyqr : y ∈ q.reverse.support := by
        simpa [Walk.support_reverse] using hyq
      have hyuw : y ∈ u.support ∨ y ∈ w.support := by
        rw [← Walk.mem_support_append_iff, hsplit]
        exact hyqr
      rcases hyuw with hyu | hyw
      · have hyb : y = b := hlast y hyB (by simpa [u] using hyu)
        exact hyb.trans hab.symm
      · have hwnil : w.Nil := hw.nil_iff_eq.mpr hab.symm
        have hwsupport : w.support = [b] := Walk.nil_iff_support_eq.mp hwnil
        have hyb : y = b := by simpa [hwsupport] using hyw
        exact hyb.trans hab.symm
  · right
    let insideArc : G.Walk a b := w.reverse
    let outsideArc : G.Walk a b := p.reverse.append u
    have hloop : insideArc.append outsideArc.reverse = R.rotate a haR := by
      calc
        insideArc.append outsideArc.reverse =
            w.reverse.append (u.reverse.append p) := by
          simp [insideArc, outsideArc]
        _ = (w.reverse.append u.reverse).append p := Walk.append_assoc _ _ _
        _ = (u.append w).reverse.append p := by simp
        _ = q.append p := by rw [hsplit]; simp
        _ = R.rotate a haR := by simp [Walk.rotate, p, q]
    have hloopCycle : (insideArc.append outsideArc.reverse).IsCycle := by
      rw [hloop]
      exact hR.rotate haR
    have hinside : insideArc.IsPath := by
      simpa [insideArc] using hw.reverse
    have houtsideReverse : outsideArc.reverse.IsPath :=
      hloopCycle.isPath_of_append_right (Walk.not_nil_of_ne hab)
    have houtside : outsideArc.IsPath :=
      (Walk.isPath_reverse_iff outsideArc).1 houtsideReverse
    have hlength : insideArc.length + outsideArc.length = C.length := by
      have h := congrArg Walk.length hloop
      simpa [R, Walk.length_rotate] using h
    have hcover : C.support.toFinset ∩ B ⊆ insideArc.support.toFinset := by
      intro y hy
      have hyC : y ∈ C.support :=
        List.mem_toFinset.1 (Finset.mem_inter.1 hy).1
      have hyB : y ∈ B := (Finset.mem_inter.1 hy).2
      have hyR : y ∈ R.support :=
        (Walk.mem_support_rotate_iff C z hzC).2 hyC
      have hypq : y ∈ p.support ∨ y ∈ q.support := by
        rw [← Walk.mem_support_append_iff, hdecomp]
        exact hyR
      apply List.mem_toFinset.2
      rcases hypq with hyp | hyq
      · have hya : y = a := hfirst y hyB (by simpa [p] using hyp)
        subst y
        exact insideArc.start_mem_support
      · have hyqr : y ∈ q.reverse.support := by
          simpa [Walk.support_reverse] using hyq
        have hyuw : y ∈ u.support ∨ y ∈ w.support := by
          rw [← Walk.mem_support_append_iff, hsplit]
          exact hyqr
        rcases hyuw with hyu | hyw
        · have hyb : y = b := hlast y hyB (by simpa [u] using hyu)
          subst y
          exact insideArc.end_mem_support
        · simpa [insideArc, Walk.support_reverse] using hyw
    have hzoutside : z ∈ outsideArc.support := by
      change z ∈ (p.reverse.append u).support
      rw [Walk.mem_support_append_iff]
      exact Or.inl p.reverse.end_mem_support
    have hzb : z ≠ b := by
      intro h
      apply hzB
      simpa [h] using hbB
    have houtsideB : ∀ y, y ∈ outsideArc.support → y ∈ B →
        y = a ∨ y = b := by
      intro y hyout hyB
      change y ∈ (p.reverse.append u).support at hyout
      rw [Walk.mem_support_append_iff] at hyout
      rcases hyout with hyp | hyu
      · left
        have hyp' : y ∈ p.support := by
          simpa [Walk.support_reverse] using hyp
        exact hfirst y hyB (by simpa [p] using hyp')
      · right
        exact hlast y hyB (by simpa [u] using hyu)
    exact ⟨a, b, z, insideArc, outsideArc, haB, hbB, hab, hzB,
      hinside, houtside, hlength, hcover, hzoutside, hza, hzb, houtsideB⟩

/-- A shortest cycle meets every ordinary radius-`r` ball in at most
`2r+1` vertices. -/
theorem IsShortestCycle.card_support_inter_ballAvoiding_le
    [Fintype V] {c v : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (r : ℕ) :
    (C.support.toFinset ∩ ballAvoiding G (∅ : Set V) v r).card ≤
      2 * r + 1 := by
  classical
  let B : Finset V := ballAvoiding G (∅ : Set V) v r
  by_cases hcontain : C.support.toFinset ⊆ B
  · have hlen : C.length ≤ 2 * r + 1 :=
      hC.length_le_two_mul_add_one_of_support_subset_ball r (by
        simpa [B] using hcontain)
    calc
      (C.support.toFinset ∩ ballAvoiding G (∅ : Set V) v r).card
          ≤ C.support.toFinset.card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = C.length := cycle_support_toFinset_card_eq_length C hC.1
      _ ≤ 2 * r + 1 := hlen
  · obtain ⟨z, hzCfin, hzB⟩ := Finset.not_subset.mp hcontain
    have hzC : z ∈ C.support := List.mem_toFinset.1 hzCfin
    by_cases hin : ∃ y, y ∈ C.support ∧ y ∈ B
    · rcases exists_cycle_contact_arcs C hC.1 B hin
          ⟨z, hzC, hzB⟩ with hsingle | harcs
      · obtain ⟨a, haB, haunique⟩ := hsingle
        have hsub : C.support.toFinset ∩ B ⊆ {a} := by
          intro y hy
          have hy' := Finset.mem_inter.1 hy
          have hya := haunique y (List.mem_toFinset.1 hy'.1) hy'.2
          simpa [hya]
        have hcard : (C.support.toFinset ∩ B).card ≤ 2 * r + 1 := by
          calc
            (C.support.toFinset ∩ B).card ≤ ({a} : Finset V).card :=
              Finset.card_le_card hsub
            _ = 1 := Finset.card_singleton a
            _ ≤ 2 * r + 1 := by omega
        simpa [B] using hcard
      · obtain ⟨a, b, z, insideArc, outsideArc, haB, hbB, hab, hzB,
          hinside, houtside, hlength, hcover, hzout, hza, hzb,
          houtsideB⟩ := harcs
        have haReach : ReachWithin G (∅ : Set V) v r a :=
          (mem_ballAvoiding G (∅ : Set V) v r a).1 (by
            simpa [B] using haB)
        have hbReach : ReachWithin G (∅ : Set V) v r b :=
          (mem_ballAvoiding G (∅ : Set V) v r b).1 (by
            simpa [B] using hbB)
        have hcard : (C.support.toFinset ∩ B).card ≤ 2 * r + 1 :=
          hC.card_le_two_mul_add_one_of_outside_arc
            insideArc outsideArc (C.support.toFinset ∩ B) r
            hinside houtside hlength.symm hcover haReach hbReach
            hzout (by simpa [B] using hzB)
        simpa [B] using hcard
    · have hempty : C.support.toFinset ∩ B = ∅ := by
        ext y
        constructor
        · intro hy
          have hy' := Finset.mem_inter.1 hy
          exact (hin ⟨y, List.mem_toFinset.1 hy'.1, hy'.2⟩).elim
        · simp
      simp [B, hempty]

/-- Shortest-cycle contact in the form consumed by the growth engine. -/
theorem IsShortestCycle.hasLimitedContact_support_three
    [Fintype V] {c v : V} {C : G.Walk c c} (hC : IsShortestCycle C) :
    HasLimitedContact G {v} (C.support.toFinset : Set V) 3 := by
  apply hasLimitedContact_three_of_ball_inter_card_le
  intro r
  exact hC.card_support_inter_ballAvoiding_le r

/-! ## Elementary avoiding-ball estimates -/

/-- Growing from the radius-one ball of a root and then for another `r`
steps stays inside the radius-`r+1` ball of the root. -/
theorem ballAvoidingFrom_ballAvoiding_one_subset [Fintype V]
    (G : SimpleGraph V) (W : Finset V) (root : V) (r : ℕ) :
    ballAvoidingFrom G (W : Set V) (ballAvoiding G (W : Set V) root 1) r ⊆
      ballAvoiding G (W : Set V) root (r + 1) := by
  classical
  intro y hy
  obtain ⟨a, ha, hay⟩ :=
    (mem_ballAvoidingFrom G (W : Set V)
      (ballAvoiding G (W : Set V) root 1) r y).1 hy
  have hra : ReachWithin G (W : Set V) root 1 a :=
    (mem_ballAvoiding G (W : Set V) root 1 a).1 ha
  have haW : a = root ∨ a ∉ W := hra.eq_root_or_not_mem
  obtain ⟨p, hp, hplen⟩ := hra
  obtain ⟨q, hq, hqlen⟩ := hay
  let w : G.Walk root y := p.append q
  have hwavoid : w.Avoids (W : Set V) ({root} : Set V) := by
    intro z hz hzW
    change z ∈ (p.append q).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hzp | hzq
    · exact hp.2 z hzp hzW
    · have hza : z = a := by
        simpa only [Set.mem_singleton_iff] using hq.2 z hzq hzW
      subst z
      rcases haW with rfl | haW
      · simp
      · exact (haW hzW).elim
  rw [mem_ballAvoiding]
  refine ⟨w.bypass, ⟨w.bypass_isPath,
    hwavoid.of_support_subset w.support_bypass_subset_support⟩, ?_⟩
  calc
    w.bypass.length ≤ w.length := w.length_bypass_le_length
    _ = p.length + q.length := by simp [w]
    _ ≤ 1 + r := Nat.add_le_add hplen hqlen
    _ = r + 1 := by omega

/-- Every neighbor not deleted by `W` belongs to the radius-one avoiding
ball. -/
theorem neighborFinset_sdiff_subset_ballAvoiding_one [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (root : V) :
    G.neighborFinset root \ W ⊆ ballAvoiding G (W : Set V) root 1 := by
  intro y hy
  obtain ⟨hyN, hyW⟩ := Finset.mem_sdiff.1 hy
  have hxy : G.Adj root y := (G.mem_neighborFinset root y).1 hyN
  let p : G.Walk root y := Walk.cons hxy Walk.nil
  rw [mem_ballAvoiding]
  refine ⟨p, ?_, by simp [p]⟩
  refine ⟨?_, ?_⟩
  · simp [p, Walk.cons_isPath_iff, G.ne_of_adj hxy]
  · intro z hz hzW
    simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · simp
    · exact (hyW hzW).elim

/-- The radius-one ball retains minimum degree after paying once for every
deleted vertex. -/
theorem card_ballAvoiding_one_lower_of_minDegree [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (root : V) (d budget : ℕ)
    (hmin : d - 1 ≤ G.degree root) (hW : W.card ≤ budget) :
    d - 1 - budget ≤ (ballAvoiding G (W : Set V) root 1).card := by
  have hneighborSubset : G.neighborFinset root \ W ⊆
      ballAvoiding G (W : Set V) root 1 := by
    intro y hy
    obtain ⟨hyN, hyW⟩ := Finset.mem_sdiff.1 hy
    have hxy : G.Adj root y := (G.mem_neighborFinset root y).1 hyN
    let p : G.Walk root y := Walk.cons hxy Walk.nil
    rw [mem_ballAvoiding]
    refine ⟨p, ?_, by simp [p]⟩
    refine ⟨?_, ?_⟩
    · simp [p, Walk.cons_isPath_iff, G.ne_of_adj hxy]
    · intro z hz hzW
      simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · simp
      · exact (hyW hzW).elim
  have hsub := Finset.card_le_card hneighborSubset
  have hinter : (W ∩ G.neighborFinset root).card ≤ W.card :=
    Finset.card_le_card Finset.inter_subset_left
  rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree] at hsub
  calc
    d - 1 - budget ≤ G.degree root - budget :=
      Nat.sub_le_sub_right hmin budget
    _ ≤ G.degree root - (W ∩ G.neighborFinset root).card :=
      Nat.sub_le_sub_left (hinter.trans hW) _
    _ ≤ (ballAvoiding G (W : Set V) root 1).card := hsub

/-- A radius-one ball only pays the deleted vertices which actually touch
the root. -/
theorem card_ballAvoiding_one_lower_of_blocked [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) (d contact : ℕ)
    (hxU : x ∉ U) (hdeg : d - 1 ≤ G.degree x)
    (hblocked :
      (blockedExternalNeighborhood G (U : Set V) ({x} : Finset V)).card ≤
        contact) :
    d - 1 - contact ≤ (ballAvoiding G (U : Set V) x 1).card := by
  let originalDecRel : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecRel
  have havailable :
      (availableExternalNeighborhood G (U : Set V) ({x} : Finset V)).card ≤
        (ballAvoiding G (U : Set V) x 1).card := by
    apply Finset.card_le_card
    simpa [ballAvoidingFrom] using
      (availableExternalNeighborhood_subset_ballAvoidingFrom_succ
        G (U : Set V) ({x} : Finset V) 0)
  have hsplit := card_available_add_card_blocked
    G (U : Set V) ({x} : Finset V)
  have hextSub :
      (externalNeighborhood G ({x} : Finset V)).card -
          (blockedExternalNeighborhood G (U : Set V) ({x} : Finset V)).card =
        (availableExternalNeighborhood G (U : Set V) ({x} : Finset V)).card := by
    omega
  have hdegreeSub : G.degree x -
      (blockedExternalNeighborhood G (U : Set V) ({x} : Finset V)).card =
      (availableExternalNeighborhood G (U : Set V) ({x} : Finset V)).card := by
    have hneighborChoice :
        externalNeighborhood G ({x} : Finset V) = G.neighborFinset x := by
      ext y
      simp only [mem_externalNeighborhood, Finset.mem_singleton,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨_, y', rfl, hxy⟩
        exact hxy
      · intro hxy
        exact ⟨by simpa using (G.ne_of_adj hxy).symm, x, rfl, hxy⟩
    have hdegreeChoice :
        (externalNeighborhood G ({x} : Finset V)).card = G.degree x := by
      rw [hneighborChoice, G.card_neighborFinset_eq_degree]
    rw [hdegreeChoice] at hextSub
    exact hextSub
  calc
    d - 1 - contact ≤ G.degree x - contact :=
      Nat.sub_le_sub_right hdeg contact
    _ ≤ G.degree x -
        (blockedExternalNeighborhood G (U : Set V) ({x} : Finset V)).card :=
      Nat.sub_le_sub_left hblocked _
    _ = (availableExternalNeighborhood G (U : Set V) ({x} : Finset V)).card :=
      hdegreeSub
    _ ≤ (ballAvoiding G (U : Set V) x 1).card := havailable

/-- Full limited contact supplies the preceding radius-zero hypothesis. -/
theorem card_ballAvoiding_one_lower_of_limitedContact [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) (d contact : ℕ)
    (hxU : x ∉ U) (hdeg : d - 1 ≤ G.degree x)
    (hc : HasLimitedContact G ({x} : Finset V) (U : Set V) contact) :
    d - 1 - contact ≤ (ballAvoiding G (U : Set V) x 1).card := by
  apply card_ballAvoiding_one_lower_of_blocked G U x d contact hxU hdeg
  simpa [ballAvoidingFrom] using hc 0

/-- A high-degree root supplies a radius-one expansion after avoiding any
fixed finite set. -/
theorem exists_starExpansion_avoiding [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : V) (forbidden : Finset V) (D : ℕ) (hD : 0 < D)
    (hdegree : D + forbidden.card ≤ G.degree root) :
    ∃ E : VertexExpansion G root D 1,
      Disjoint (E.verts \ {root}) forbidden := by
  have hball : D ≤ (ballAvoiding G (forbidden : Set V) root 1).card := by
    have h := card_ballAvoiding_one_lower_of_minDegree
      G forbidden root (G.degree root + 1) forbidden.card
      (by omega) le_rfl
    omega
  let Efull := VertexExpansion.ofBallAvoiding G (forbidden : Set V) root 1
  obtain ⟨E, hE⟩ := Efull.proposition3_10 hD hball
  refine ⟨E, ?_⟩
  rw [Finset.disjoint_left]
  intro z hz hzforbidden
  have hzE : z ∈ E.verts := (Finset.mem_sdiff.1 hz).1
  have hzNotRoot : z ∉ ({root} : Finset V) := (Finset.mem_sdiff.1 hz).2
  have hzball : z ∈ ballAvoiding G (forbidden : Set V) root 1 := hE hzE
  have hzcarrier :=
    ballAvoiding_subset_insert_compl G (forbidden : Set V) root 1 hzball
  rcases hzcarrier with hzroot | hzoutside
  · exact hzNotRoot (by simpa using hzroot)
  · exact hzoutside hzforbidden

/-- Allocate radius-one stars at finitely many distinct centres.  Each new
arm avoids the fixed base and all previously allocated stars. -/
theorem exists_pairwise_starExpansion_avoiding [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t D : ℕ} (center : Fin t ↪ V) (base : Finset V)
    (hD : 0 < D) (hcenter : ∀ i, center i ∈ base)
    (hdegree : ∀ i,
      D + base.card + t * D ≤ G.degree (center i)) :
    ∃ star : ∀ i : Fin t, VertexExpansion G (center i) D 1,
      (∀ i, Disjoint ((star i).verts \ {center i}) base) ∧
      (∀ i j, i ≠ j → Disjoint (star i).verts (star j).verts) := by
  classical
  induction t with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ t ih =>
      let last : Fin (t + 1) := Fin.last t
      let centerOld : Fin t ↪ V :=
        ⟨fun i ↦ center i.castSucc,
          fun _ _ h ↦ (Fin.castSucc_injective t) (center.injective h)⟩
      obtain ⟨old, holdBase, holdPair⟩ := ih centerOld
        (fun i ↦ hcenter i.castSucc)
        (fun i ↦ by
          have h := hdegree i.castSucc
          change D + base.card + t * D ≤ G.degree (center i.castSucc)
          calc
            D + base.card + t * D ≤
                D + base.card + (t + 1) * D := by
              nlinarith [hD]
            _ ≤ G.degree (center i.castSucc) := h)
      let oldVerts : Finset V :=
        Finset.univ.biUnion fun i : Fin t ↦ (old i).verts
      have holdVerts : oldVerts.card ≤ t * D := by
        calc
          oldVerts.card ≤
              ∑ i ∈ (Finset.univ : Finset (Fin t)), (old i).verts.card := by
            simpa [oldVerts] using
              (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin t)))
                (t := fun i ↦ (old i).verts))
          _ = t * D := by simp [VertexExpansion.card_verts, Nat.mul_comm]
      let W := base ∪ oldVerts
      have hW : W.card ≤ base.card + t * D := by
        exact (Finset.card_union_le base oldVerts).trans
          (Nat.add_le_add_left holdVerts base.card)
      obtain ⟨lastStar, hlastBase⟩ :=
        exists_starExpansion_avoiding G (center last) W D hD (by
          have h := hdegree last
          nlinarith [hW])
      have castRoot_verts {a b : V} (h : a = b)
          (E : VertexExpansion G a D 1) :
          ((h ▸ E : VertexExpansion G b D 1)).verts = E.verts := by
        cases h
        rfl
      let oldCast (j : Fin t) :
          VertexExpansion G (center j.castSucc) D 1 :=
        (show centerOld j = center j.castSucc by rfl) ▸ old j
      have oldCast_verts (j : Fin t) : (oldCast j).verts = (old j).verts := by
        exact castRoot_verts (show centerOld j = center j.castSucc by rfl) (old j)
      let star : ∀ i : Fin (t + 1), VertexExpansion G (center i) D 1 :=
        fun i ↦ Fin.lastCases lastStar oldCast i
      refine ⟨star, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simpa [star, W] using hlastBase.mono_right Finset.subset_union_left
        | cast i =>
            simp only [star, Fin.lastCases_castSucc]
            rw [oldCast_verts i]
            have hroot : centerOld i = center i.castSucc := by rfl
            rw [← hroot]
            exact holdBase i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
            induction j using Fin.lastCases with
            | last => exact (hij rfl).elim
            | cast j =>
                rw [Finset.disjoint_left]
                intro z hzLast hzOld
                have hzLast' : z ∈ lastStar.verts := by
                  simpa only [star, Fin.lastCases_last] using hzLast
                have hzOldCast : z ∈ (oldCast j).verts := by
                  simpa only [star, Fin.lastCases_castSucc] using hzOld
                have hzOld' : z ∈ (old j).verts := by
                  rw [← oldCast_verts j]
                  exact hzOldCast
                by_cases hz : z = center last
                · subst z
                  have hzold : center last ≠ centerOld j := by
                    intro heq
                    dsimp [centerOld] at heq
                    have hidx := center.injective heq
                    exact hij hidx
                  have htrim : center last ∈
                      (old j).verts \ {centerOld j} :=
                    Finset.mem_sdiff.2 ⟨hzOld', by simpa using hzold⟩
                  exact (Finset.disjoint_left.1 (holdBase j) htrim
                    (hcenter last)).elim
                · have htrim : z ∈ lastStar.verts \ {center last} :=
                    Finset.mem_sdiff.2 ⟨hzLast', by simpa using hz⟩
                  exact (Finset.disjoint_left.1 hlastBase htrim (by
                    apply Finset.mem_union_right
                    apply Finset.mem_biUnion.2
                    exact ⟨j, by simp, hzOld'⟩)).elim
        | cast i =>
            induction j using Fin.lastCases with
            | last =>
                exact (by
                  have h := (show Disjoint lastStar.verts (old i).verts from by
                    rw [Finset.disjoint_left]
                    intro z hzLast hzOld
                    by_cases hz : z = center last
                    · subst z
                      have hzold : center last ≠ centerOld i := by
                        intro heq
                        dsimp [centerOld] at heq
                        have hidx := center.injective heq
                        exact hij hidx.symm
                      have htrim : center last ∈
                          (old i).verts \ {centerOld i} :=
                        Finset.mem_sdiff.2 ⟨hzOld, by simpa using hzold⟩
                      exact (Finset.disjoint_left.1 (holdBase i) htrim
                        (hcenter last)).elim
                    · have htrim : z ∈ lastStar.verts \ {center last} :=
                        Finset.mem_sdiff.2
                          ⟨hzLast, by simpa using hz⟩
                      exact (Finset.disjoint_left.1 hlastBase htrim (by
                        apply Finset.mem_union_right
                        apply Finset.mem_biUnion.2
                        exact ⟨i, by simp, hzOld⟩)).elim)
                  simp only [star, Fin.lastCases_castSucc, Fin.lastCases_last]
                  rw [oldCast_verts i]
                  exact h.symm)
            | cast j =>
                simp only [star, Fin.lastCases_castSucc]
                rw [oldCast_verts i, oldCast_verts j]
                exact holdPair i j (fun h ↦ hij (congrArg Fin.castSucc h))

/-- The preceding finite induction, reindexed by an arbitrary finite type. -/
theorem exists_pairwise_starExpansion_avoiding_finite [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (center : I ↪ V) (base : Finset V)
    (hD : 0 < D) (hcenter : ∀ i, center i ∈ base)
    (hdegree : ∀ i,
      D + base.card + Fintype.card I * D ≤ G.degree (center i)) :
    ∃ star : ∀ i : I, VertexExpansion G (center i) D 1,
      (∀ i, Disjoint ((star i).verts \ {center i}) base) ∧
      (∀ i j, i ≠ j → Disjoint (star i).verts (star j).verts) := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let centerFin : Fin (Fintype.card I) ↪ V :=
    ⟨fun i ↦ center (e i), fun _ _ h ↦ e.injective (center.injective h)⟩
  obtain ⟨starFin, hstarBase, hstarPair⟩ :=
    exists_pairwise_starExpansion_avoiding G centerFin base hD
      (fun i ↦ hcenter (e i)) (fun i ↦ hdegree (e i))
  have hcenterFin (i : I) : centerFin (e.symm i) = center i := by
    change center (e (e.symm i)) = center i
    rw [e.apply_symm_apply]
  have castRoot_verts {a b : V} (h : a = b)
      (F : VertexExpansion G a D 1) :
      ((h ▸ F : VertexExpansion G b D 1)).verts = F.verts := by
    cases h
    rfl
  let star (i : I) : VertexExpansion G (center i) D 1 := by
    exact hcenterFin i ▸ starFin (e.symm i)
  have star_verts (i : I) :
      (star i).verts = (starFin (e.symm i)).verts := by
    dsimp [star]
    apply castRoot_verts
  refine ⟨star, ?_, ?_⟩
  · intro i
    rw [star_verts]
    rw [← hcenterFin i]
    exact hstarBase (e.symm i)
  · intro i j hij
    have heij : e.symm i ≠ e.symm j := fun h ↦ hij (e.symm.injective h)
    rw [star_verts, star_verts]
    exact hstarPair (e.symm i) (e.symm j) heij

/-- Allocate stars at a finite list of centres which may repeat.  Since a
repeated centre is shared, the conclusion is pairwise disjointness of the
trimmed arms, exactly as required by Lemma 3.11. -/
theorem exists_pairwise_trimmed_starExpansion_avoiding [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {t D : ℕ} (center : Fin t → V) (base : Finset V)
    (hD : 0 < D) (hcenter : ∀ i, center i ∈ base)
    (hdegree : ∀ i,
      D + base.card + t * D ≤ G.degree (center i)) :
    ∃ star : ∀ i : Fin t, VertexExpansion G (center i) D 1,
      (∀ i, Disjoint ((star i).verts \ {center i}) base) ∧
      (∀ i j, i ≠ j → Disjoint
        ((star i).verts \ {center i})
        ((star j).verts \ {center j})) := by
  classical
  induction t with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
  | succ t ih =>
      let last : Fin (t + 1) := Fin.last t
      let centerOld : Fin t → V := fun i ↦ center i.castSucc
      obtain ⟨old, holdBase, holdPair⟩ := ih centerOld
        (fun i ↦ hcenter i.castSucc)
        (fun i ↦ by
          have h := hdegree i.castSucc
          change D + base.card + t * D ≤ G.degree (center i.castSucc)
          nlinarith [hD])
      let oldArms : Finset V := Finset.univ.biUnion fun i : Fin t ↦
        (old i).verts \ {centerOld i}
      have holdArms : oldArms.card ≤ t * D := by
        calc
          oldArms.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)),
              ((old i).verts \ {centerOld i}).card := by
            simpa [oldArms] using
              (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin t)))
                (t := fun i ↦ (old i).verts \ {centerOld i}))
          _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin t)), D := by
            apply Finset.sum_le_sum
            intro i hi
            exact (Finset.card_le_card Finset.sdiff_subset).trans
              (old i).card_verts.le
          _ = t * D := by simp
      let W := base ∪ oldArms
      have hW : W.card ≤ base.card + t * D :=
        (Finset.card_union_le base oldArms).trans
          (Nat.add_le_add_left holdArms base.card)
      obtain ⟨lastStar, hlastW⟩ :=
        exists_starExpansion_avoiding G (center last) W D hD (by
          have h := hdegree last
          nlinarith [hW])
      let oldCast (j : Fin t) :
          VertexExpansion G (center j.castSucc) D 1 := old j
      let star : ∀ i : Fin (t + 1), VertexExpansion G (center i) D 1 :=
        fun i ↦ Fin.lastCases lastStar oldCast i
      refine ⟨star, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simpa [star, W] using hlastW.mono_right Finset.subset_union_left
        | cast i =>
            simpa [star, oldCast, centerOld] using holdBase i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
            induction j using Fin.lastCases with
            | last => exact (hij rfl).elim
            | cast j =>
                rw [Finset.disjoint_left]
                intro z hzLast hzOld
                have hzLast' : z ∈ lastStar.verts \ {center last} := by
                  simpa [star] using hzLast
                have hzOld' : z ∈ (old j).verts \ {centerOld j} := by
                  simpa [star, oldCast, centerOld] using hzOld
                exact (Finset.disjoint_left.1 hlastW hzLast' (by
                  apply Finset.mem_union_right
                  apply Finset.mem_biUnion.2
                  exact ⟨j, by simp, hzOld'⟩)).elim
        | cast i =>
            induction j using Fin.lastCases with
            | last =>
                exact (by
                  have h := (show Disjoint
                      ((lastStar.verts \ {center last}))
                      ((old i).verts \ {centerOld i}) from by
                    rw [Finset.disjoint_left]
                    intro z hzLast hzOld
                    exact (Finset.disjoint_left.1 hlastW hzLast (by
                      apply Finset.mem_union_right
                      apply Finset.mem_biUnion.2
                      exact ⟨i, by simp, hzOld⟩)).elim)
                  simpa [star, oldCast, centerOld] using h.symm)
            | cast j =>
                simpa [star, oldCast, centerOld] using
                  holdPair i j (fun h ↦ hij (congrArg Fin.castSucc h))

/-- Reindex the preceding repeated-centre star allocation by any finite
index type. -/
theorem exists_pairwise_trimmed_starExpansion_avoiding_finite [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {I : Type*} [Fintype I] [DecidableEq I] {D : ℕ}
    (center : I → V) (base : Finset V)
    (hD : 0 < D) (hcenter : ∀ i, center i ∈ base)
    (hdegree : ∀ i,
      D + base.card + Fintype.card I * D ≤ G.degree (center i)) :
    ∃ star : ∀ i : I, VertexExpansion G (center i) D 1,
      (∀ i, Disjoint ((star i).verts \ {center i}) base) ∧
      (∀ i j, i ≠ j → Disjoint
        ((star i).verts \ {center i})
        ((star j).verts \ {center j})) := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  obtain ⟨starFin, hbase, hpair⟩ :=
    exists_pairwise_trimmed_starExpansion_avoiding G
      (fun i ↦ center (e i)) base hD
      (fun i ↦ hcenter (e i)) (fun i ↦ hdegree (e i))
  have hcenterFin (i : I) : center (e (e.symm i)) = center i := by
    rw [e.apply_symm_apply]
  have castRoot_verts {a b : V} (h : a = b)
      (F : VertexExpansion G a D 1) :
      ((h ▸ F : VertexExpansion G b D 1)).verts = F.verts := by
    cases h
    rfl
  let star (i : I) : VertexExpansion G (center i) D 1 :=
    hcenterFin i ▸ starFin (e.symm i)
  have star_verts (i : I) :
      (star i).verts = (starFin (e.symm i)).verts := by
    dsimp [star]
    apply castRoot_verts
  refine ⟨star, ?_, ?_⟩
  · intro i
    rw [star_verts]
    rw [← hcenterFin i]
    exact hbase (e.symm i)
  · intro i j hij
    rw [star_verts, star_verts]
    rw [← hcenterFin i, ← hcenterFin j]
    exact hpair (e.symm i) (e.symm j)
      (fun h ↦ hij (e.symm.injective h))

/-! ## Bounded-degree avoiding balls -/

/-- A successor avoiding ball is contained in the preceding ball together
with the ordinary neighborhoods of its vertices. -/
theorem ballAvoidingFrom_succ_subset_union_neighbors [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted : Set V) (A : Finset V) (r : ℕ) :
    ballAvoidingFrom G deleted A (r + 1) ⊆
      ballAvoidingFrom G deleted A r ∪
        (ballAvoidingFrom G deleted A r).biUnion
          (fun v ↦ G.neighborFinset v) := by
  intro y hy
  obtain ⟨a, ha, p, hp, hplen⟩ :=
    (mem_ballAvoidingFrom G deleted A (r + 1) y).1 hy
  by_cases hshort : p.length ≤ r
  · exact Finset.mem_union_left _ <|
      (mem_ballAvoidingFrom G deleted A r y).2 ⟨a, ha, p, hp, hshort⟩
  · have hlen : p.length = r + 1 := by omega
    let z : V := p.getVert r
    have hrlen : r ≤ p.length := by omega
    have hz : z ∈ ballAvoidingFrom G deleted A r := by
      rw [mem_ballAvoidingFrom]
      refine ⟨a, ha, p.take r, ⟨hp.1.take r, ?_⟩, ?_⟩
      · intro w hw hwdeleted
        have hw' : w ∈ p.support := by
          rw [Walk.support_take] at hw
          exact (List.take_prefix (r + 1) p.support).subset hw
        exact hp.2 w hw' hwdeleted
      · simp [Walk.take_length, Nat.min_eq_left hrlen]
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨z, hz, ?_⟩
    rw [G.mem_neighborFinset]
    have hadj := p.adj_getVert_succ (i := r) (by omega)
    have hend : p.getVert (r + 1) = y := by
      rw [← hlen]
      exact p.getVert_length
    simpa [z, hend] using hadj

/-- Moore-type upper bound for an avoiding ball when every undeleted vertex
has degree at most `Delta`. -/
theorem card_ballAvoidingFrom_le_of_degree_bound [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A deleted : Finset V) (Delta radius : ℕ)
    (hAdeleted : Disjoint A deleted)
    (hdegree : ∀ v ∉ deleted, G.degree v ≤ Delta) :
    (ballAvoidingFrom G (deleted : Set V) A radius).card ≤
      A.card * (Delta + 1) ^ radius := by
  have hAoutside : ∀ a ∈ A, a ∉ (deleted : Set V) := by
    intro a haA hadeleted
    exact Finset.disjoint_left.1 hAdeleted haA hadeleted
  induction radius with
  | zero => simp
  | succ r ih =>
      let B := ballAvoidingFrom G (deleted : Set V) A r
      have hBout : ∀ v ∈ B, v ∉ deleted := by
        exact ballAvoidingFrom_avoids_forbidden
          G (deleted : Set V) A r hAoutside
      have hsub : ballAvoidingFrom G (deleted : Set V) A (r + 1) ⊆
          B ∪ B.biUnion (fun v ↦ G.neighborFinset v) := by
        simpa [B] using
          ballAvoidingFrom_succ_subset_union_neighbors
            G (deleted : Set V) A r
      have hneighbors :
          (B.biUnion (fun v ↦ G.neighborFinset v)).card ≤ B.card * Delta := by
        calc
          (B.biUnion (fun v ↦ G.neighborFinset v)).card
              ≤ ∑ v ∈ B, (G.neighborFinset v).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _v ∈ B, Delta := by
            apply Finset.sum_le_sum
            intro v hv
            rw [G.card_neighborFinset_eq_degree]
            exact hdegree v (hBout v hv)
          _ = B.card * Delta := by simp
      calc
        (ballAvoidingFrom G (deleted : Set V) A (Nat.succ r)).card
            ≤ (B ∪ B.biUnion (fun v ↦ G.neighborFinset v)).card := by
              simpa [Nat.succ_eq_add_one] using Finset.card_le_card hsub
        _ ≤ B.card + (B.biUnion (fun v ↦ G.neighborFinset v)).card :=
          Finset.card_union_le B (B.biUnion (fun v ↦ G.neighborFinset v))
        _ ≤ B.card + B.card * Delta :=
          Nat.add_le_add_left hneighbors B.card
        _ = B.card * (Delta + 1) := by
          simp [Nat.mul_add, Nat.add_comm]
        _ ≤ (A.card * (Delta + 1) ^ r) * (Delta + 1) :=
          Nat.mul_le_mul_right (Delta + 1) ih
        _ = A.card * (Delta + 1) ^ (Nat.succ r) := by
          simp [pow_succ, Nat.mul_assoc]

/-! ## A logarithmic Moore bound for a shortest cycle -/

/-- Exact-distance BFS frontier. -/
noncomputable def bfsFrontier [Fintype V] (G : SimpleGraph V)
    (root : V) : ℕ → Finset V
  | 0 => {root}
  | i + 1 =>
      ballAvoiding G (∅ : Set V) root (i + 1) \
        ballAvoiding G (∅ : Set V) root i

theorem bfsFrontier_subset_ball [Fintype V] (G : SimpleGraph V)
    (root : V) (i : ℕ) :
    bfsFrontier G root i ⊆ ballAvoiding G (∅ : Set V) root i := by
  cases i with
  | zero => simp [bfsFrontier]
  | succ i =>
      intro x hx
      exact (Finset.mem_sdiff.1 hx).1

/-- Double-counting adjacencies between two finite vertex sets. -/
theorem sum_card_neighborFinset_inter_comm_moore [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) =
      ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  classical
  calc
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) =
        ∑ a ∈ A, (B.bipartiteAbove G.Adj a).card := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      ext b
      simp [and_comm, G.adj_comm]
    _ = ∑ b ∈ B, (A.bipartiteBelow G.Adj b).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
    _ = ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      ext a
      simp [and_comm, G.adj_comm]

/-- A frontier vertex has at most one neighbor backwards while the shortest
cycle is longer than twice the explored radius. -/
theorem IsShortestCycle.card_neighbor_inter_ball_le_one_of_mem_frontier
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c root x : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (i : ℕ) (hx : x ∈ bfsFrontier G root i)
    (hgirth : 2 * (i + 1) < C.length) :
    (G.neighborFinset x ∩
      ballAvoiding G (∅ : Set V) root i).card ≤ 1 := by
  classical
  cases i with
  | zero =>
      simp only [bfsFrontier] at hx
      have hxroot : x = root := by simpa using hx
      subst x
      simp
  | succ r =>
      rw [Finset.card_le_one_iff]
      intro y z hy hz
      obtain ⟨hyAdj, hyBall⟩ := Finset.mem_inter.1 hy
      obtain ⟨hzAdj, hzBall⟩ := Finset.mem_inter.1 hz
      have hxNot : x ∉ ballAvoiding G (∅ : Set V) root r :=
        (Finset.mem_sdiff.1 hx).2
      have makePath : ∀ (a : V), G.Adj x a →
          a ∈ ballAvoiding G (∅ : Set V) root (r + 1) →
          ∃ p : G.Walk root x,
            p.IsPath ∧ p.length ≤ r + 2 ∧ p.penultimate = a := by
        intro a hxa haBall
        obtain ⟨q, hq, hqlen⟩ :=
          (mem_ballAvoiding G (∅ : Set V) root (r + 1) a).1 haBall
        have hxaNe : x ≠ a := G.ne_of_adj hxa
        have hxq : x ∉ q.support := by
          intro hxSupport
          let t : G.Walk root x := q.takeUntil x hxSupport
          have htlt : t.length < q.length :=
            q.length_takeUntil_lt_length hxSupport hxaNe
          have htlen : t.length ≤ r := by omega
          apply hxNot
          rw [mem_ballAvoiding]
          refine ⟨t, ⟨hq.1.takeUntil hxSupport, ?_⟩, htlen⟩
          simp
        let p : G.Walk root x := q.concat hxa.symm
        refine ⟨p, hq.1.concat hxq hxa.symm, ?_, ?_⟩
        · simpa [p] using Nat.add_le_add_right hqlen 1
        · simp [p, Walk.penultimate_concat]
      have hyAdj' : G.Adj x y := (G.mem_neighborFinset x y).1 hyAdj
      have hzAdj' : G.Adj x z := (G.mem_neighborFinset x z).1 hzAdj
      obtain ⟨py, hpy, hpylen, hpypen⟩ := makePath y hyAdj' hyBall
      obtain ⟨pz, hpz, hpzlen, hpzpen⟩ := makePath z hzAdj' hzBall
      by_contra hyz
      have hpne : py ≠ pz := by
        intro hp
        have hpen := congrArg Walk.penultimate hp
        exact hyz (hpypen.symm.trans (hpen.trans hpzpen))
      obtain ⟨w, hwpy, hwpz, Q, hQ, hQlen⟩ :=
        hpy.exists_isCycle_length_le_add_of_ne hpz hpne
      have hshortest := hC.2 w Q hQ
      omega

/-- A forward edge from one frontier lands in the next frontier. -/
theorem neighbor_sdiff_ball_subset_bfsFrontier_succ [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (i : ℕ)
    {x : V} (hx : x ∈ bfsFrontier G root i) :
    G.neighborFinset x \
        ballAvoiding G (∅ : Set V) root i ⊆
      bfsFrontier G root (i + 1) := by
  classical
  intro y hy
  obtain ⟨hxyN, hyNot⟩ := Finset.mem_sdiff.1 hy
  have hxy : G.Adj x y := (G.mem_neighborFinset x y).1 hxyN
  have hxBall := bfsFrontier_subset_ball G root i hx
  obtain ⟨p, hp, hplen⟩ :=
    (mem_ballAvoiding G (∅ : Set V) root i x).1 hxBall
  have hyp : y ∉ p.support := by
    intro hyp
    exact hyNot (support_subset_ballAvoiding hp hplen y hyp)
  have hyNext : y ∈ ballAvoiding G (∅ : Set V) root (i + 1) := by
    rw [mem_ballAvoiding]
    refine ⟨p.concat hxy, ⟨hp.1.concat hyp hxy, ?_⟩, ?_⟩
    · simp
    · simpa using Nat.add_le_add_right hplen 1
  simpa [bfsFrontier] using Finset.mem_sdiff.2 ⟨hyNext, hyNot⟩

/-- In minimum degree three, each BFS frontier doubles before half the
shortest-cycle length. -/
theorem IsShortestCycle.two_mul_card_bfsFrontier_le_succ
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c root : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (hmin : ∀ v : V, 3 ≤ G.degree v) (i : ℕ)
    (hgirth : 2 * (i + 2) < C.length) :
    2 * (bfsFrontier G root i).card ≤
      (bfsFrontier G root (i + 1)).card := by
  classical
  let B := ballAvoiding G (∅ : Set V) root i
  let F := bfsFrontier G root i
  let F' := bfsFrontier G root (i + 1)
  have hforward : ∀ x ∈ F, 2 ≤ (G.neighborFinset x ∩ F').card := by
    intro x hx
    have hinter : (G.neighborFinset x ∩ B).card ≤ 1 := by
      apply hC.card_neighbor_inter_ball_le_one_of_mem_frontier G i hx
      omega
    have hout : 2 ≤ (G.neighborFinset x \ B).card := by
      have := hmin x
      calc
        2 ≤ G.degree x - 1 := by omega
        _ ≤ G.degree x - (G.neighborFinset x ∩ B).card :=
          Nat.sub_le_sub_left hinter _
        _ = (G.neighborFinset x \ B).card := by
          rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree]
          congr 2
          exact (Finset.inter_comm B (G.neighborFinset x)).symm
    have hsub : G.neighborFinset x \ B ⊆ G.neighborFinset x ∩ F' := by
      intro y hy
      exact Finset.mem_inter.2 ⟨(Finset.mem_sdiff.1 hy).1,
        neighbor_sdiff_ball_subset_bfsFrontier_succ G root i hx hy⟩
    exact hout.trans (Finset.card_le_card hsub)
  have hbackward : ∀ y ∈ F', (G.neighborFinset y ∩ F).card ≤ 1 := by
    intro y hy
    have hbig :
        (G.neighborFinset y ∩
          ballAvoiding G (∅ : Set V) root (i + 1)).card ≤ 1 := by
      apply hC.card_neighbor_inter_ball_le_one_of_mem_frontier G (i + 1) hy
      simpa [Nat.add_assoc] using hgirth
    apply (Finset.card_le_card ?_).trans hbig
    intro z hz
    obtain ⟨hzN, hzF⟩ := Finset.mem_inter.1 hz
    have hzBall : z ∈ ballAvoiding G (∅ : Set V) root i :=
      bfsFrontier_subset_ball G root i hzF
    have hzBall' : z ∈ ballAvoiding G (∅ : Set V) root (i + 1) :=
      ballAvoiding_radius_mono G (∅ : Set V) root (Nat.le_succ i) hzBall
    exact Finset.mem_inter.2 ⟨hzN, hzBall'⟩
  have hlower : 2 * F.card ≤
      ∑ x ∈ F, (G.neighborFinset x ∩ F').card := by
    calc
      2 * F.card = ∑ _x ∈ F, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ F, (G.neighborFinset x ∩ F').card := by
        apply Finset.sum_le_sum
        intro x hx
        exact hforward x hx
  have hupper :
      (∑ y ∈ F', (G.neighborFinset y ∩ F).card) ≤ F'.card := by
    calc
      (∑ y ∈ F', (G.neighborFinset y ∩ F).card)
          ≤ ∑ _y ∈ F', 1 := by
        apply Finset.sum_le_sum
        intro y hy
        exact hbackward y hy
      _ = F'.card := by simp
  rw [sum_card_neighborFinset_inter_comm_moore G F F'] at hlower
  exact hlower.trans hupper

theorem IsShortestCycle.pow_two_le_card_bfsFrontier
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c root : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (hmin : ∀ v : V, 3 ≤ G.degree v) (radius : ℕ)
    (hgirth : ∀ i < radius, 2 * (i + 2) < C.length) :
    2 ^ radius ≤ (bfsFrontier G root radius).card := by
  induction radius with
  | zero => simp [bfsFrontier]
  | succ r ih =>
      rw [pow_succ]
      calc
        2 ^ r * 2 ≤ (bfsFrontier G root r).card * 2 :=
          Nat.mul_le_mul_right 2 (ih fun i hi ↦ hgirth i (hi.trans r.lt_succ_self))
        _ = 2 * (bfsFrontier G root r).card := by omega
        _ ≤ (bfsFrontier G root (r + 1)).card :=
          hC.two_mul_card_bfsFrontier_le_succ G hmin r
            (hgirth r r.lt_succ_self)

/-- Explicit logarithmic Moore bound for a shortest cycle. -/
theorem IsShortestCycle.length_le_two_mul_log_add_two
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    C.length ≤ 2 * (Nat.log 2 (Fintype.card V) + 2) := by
  let radius := Nat.log 2 (Fintype.card V) + 1
  by_contra hbad
  have hgirth : 2 * (radius + 1) < C.length := by omega
  have hiter : 2 ^ radius ≤ (bfsFrontier G c radius).card := by
    apply hC.pow_two_le_card_bfsFrontier G hmin radius
    intro i hi
    have hir : i + 2 ≤ radius + 1 := by omega
    exact (Nat.mul_le_mul_left 2 hir).trans_lt hgirth
  have hfrontier : (bfsFrontier G c radius).card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ (bfsFrontier G c radius)
  have hpow : Fintype.card V < 2 ^ radius := by
    simpa [radius, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two (Fintype.card V)
  omega

/-! ## Finite ball packings -/

/-- A capped packing of equal-radius avoiding balls whose centres lie in a
prescribed available set and whose balls avoid a protected set. -/
def IsCappedBallPacking [Fintype V] (G : SimpleGraph V)
    (deleted available reserved : Finset V) (radius target : ℕ)
    (centers : Finset V) : Prop :=
  centers ⊆ available ∧ centers.card ≤ target ∧
    ((centers : Set V).PairwiseDisjoint
      (fun w ↦ ballAvoiding G (deleted : Set V) w radius)) ∧
    ∀ w ∈ centers,
      Disjoint (ballAvoiding G (deleted : Set V) w radius) reserved

/-- A capped ball packing of maximum cardinality exists. -/
theorem exists_max_card_cappedBallPacking [Fintype V]
    (G : SimpleGraph V) (deleted available reserved : Finset V)
    (radius target : ℕ) :
    ∃ centers : Finset V,
      IsCappedBallPacking G deleted available reserved radius target centers ∧
      ∀ other : Finset V,
        IsCappedBallPacking G deleted available reserved radius target other →
        other.card ≤ centers.card := by
  classical
  let good : Finset (Finset V) := available.powerset.filter
    (IsCappedBallPacking G deleted available reserved radius target)
  have hempty : (∅ : Finset V) ∈ good := by
    simp [good, IsCappedBallPacking]
  obtain ⟨centers, hcenters, hmax⟩ :=
    good.exists_max_image Finset.card ⟨∅, hempty⟩
  have hpacking :
      IsCappedBallPacking G deleted available reserved radius target centers :=
    (Finset.mem_filter.1 hcenters).2
  refine ⟨centers, hpacking, ?_⟩
  intro other hother
  apply hmax other
  apply Finset.mem_filter.2
  exact ⟨Finset.mem_powerset.2 hother.1, hother⟩

/-- Maximality below the cap says that every new available centre either is
already selected, meets the protected set, or its ball meets an old ball. -/
theorem CappedBallPacking.blocked_of_maximal [Fintype V]
    (G : SimpleGraph V) (deleted available reserved : Finset V)
    (radius target : ℕ) (centers : Finset V)
    (hpacking :
      IsCappedBallPacking G deleted available reserved radius target centers)
    (hmax : ∀ other : Finset V,
      IsCappedBallPacking G deleted available reserved radius target other →
        other.card ≤ centers.card)
    (hshort : centers.card < target) (w : V) (hw : w ∈ available) :
    w ∈ centers ∨
      ¬ Disjoint (ballAvoiding G (deleted : Set V) w radius) reserved ∨
      ∃ z ∈ centers, z ≠ w ∧
        ¬ Disjoint (ballAvoiding G (deleted : Set V) w radius)
          (ballAvoiding G (deleted : Set V) z radius) := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨hwnew, hwprotected, hwold⟩ := hnone
  have hinsert : IsCappedBallPacking G deleted available reserved radius target
      (insert w centers) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hw
      · exact hpacking.1 hz
    · simp [hwnew]
      omega
    · intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact hwold b hb (Ne.symm hab)
      · exact (hwold a ha hab).symm
      · exact hpacking.2.2.1 ha hb hab
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hwprotected
      · exact hpacking.2.2.2 z hz
  have hcard := hmax (insert w centers) hinsert
  simp [hwnew] at hcard

/-- Intersecting singleton avoiding balls put either centre in the
radius-sum ball about the other, provided both centres are undeleted. -/
theorem mem_ballAvoiding_of_not_disjoint_singleton_balls [Fintype V]
    (G : SimpleGraph V) (deleted : Finset V) {x y : V} {r s : ℕ}
    (hx : x ∉ deleted) (hy : y ∉ deleted)
    (hmeet : ¬ Disjoint (ballAvoiding G (deleted : Set V) x r)
      (ballAvoiding G (deleted : Set V) y s)) :
    x ∈ ballAvoiding G (deleted : Set V) y (r + s) := by
  classical
  rw [Finset.not_disjoint_iff] at hmeet
  obtain ⟨z, hzx, hzy⟩ := hmeet
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_common_ball G (deleted : Set V)
      {x} {y} r s (by simpa [ballAvoidingFrom] using hzx)
      (by simpa [ballAvoidingFrom] using hzy)
  have hax : a = x := by simpa using ha
  have hby : b = y := by simpa using hb
  subst a
  subst b
  rw [mem_ballAvoiding]
  refine ⟨p.reverse, ⟨hp.1.reverse, ?_⟩, by simpa using hplen⟩
  intro z hz hzdeleted
  have hz' : z ∈ p.support := by simpa [p.support_reverse] using hz
  have hzxy : z = x ∨ z = y := by simpa using hp.2 z hz' hzdeleted
  rcases hzxy with rfl | rfl
  · exact (hx hzdeleted).elim
  · exact (hy hzdeleted).elim

/-- If a capped packing is maximal below its cap, the available set is
covered by the radius-doubled ball around the chosen centres and protected
vertices. -/
theorem available_subset_doubled_ball_of_maximal_packing [Fintype V]
    (G : SimpleGraph V) (deleted available reserved centers : Finset V)
    (radius target : ℕ)
    (havailable : Disjoint available deleted)
    (hreserved : Disjoint reserved deleted)
    (hpacking :
      IsCappedBallPacking G deleted available reserved radius target centers)
    (hmax : ∀ other : Finset V,
      IsCappedBallPacking G deleted available reserved radius target other →
        other.card ≤ centers.card)
    (hshort : centers.card < target) :
    available ⊆ ballAvoidingFrom G (deleted : Set V)
      (centers ∪ reserved) (2 * radius) := by
  classical
  intro w hw
  have hwdeleted : w ∉ deleted := by
    intro hwd
    exact Finset.disjoint_left.1 havailable hw hwd
  rcases CappedBallPacking.blocked_of_maximal G deleted available reserved
      radius target centers hpacking hmax hshort w hw with
      hwcenter | hwprotected | ⟨z, hzcenter, hzw, hmeet⟩
  · exact (mem_ballAvoidingFrom G (deleted : Set V)
      (centers ∪ reserved) (2 * radius) w).2
      ⟨w, Finset.mem_union_left _ hwcenter,
        reachWithin_refl G (deleted : Set V) w (2 * radius)⟩
  · rw [Finset.not_disjoint_iff] at hwprotected
    obtain ⟨y, hyball, hyprotected⟩ := hwprotected
    have hydeleted : y ∉ deleted := by
      intro hyd
      exact Finset.disjoint_left.1 hreserved hyprotected hyd
    obtain ⟨p, hp, hplen⟩ :=
      (mem_ballAvoiding G (deleted : Set V) w radius y).1 hyball
    have hrev : p.reverse.IsAvoidingPath (deleted : Set V) ({y} : Set V) := by
      refine ⟨hp.1.reverse, ?_⟩
      intro a ha hadeleted
      have ha' : a ∈ p.support := by simpa [p.support_reverse] using ha
      have haw : a = w := by simpa using hp.2 a ha' hadeleted
      subst a
      exact (hwdeleted hadeleted).elim
    exact (mem_ballAvoidingFrom G (deleted : Set V)
      (centers ∪ reserved) (2 * radius) w).2
      ⟨y, Finset.mem_union_right _ hyprotected, p.reverse, hrev,
        by
          calc
            p.reverse.length = p.length := by simp
            _ ≤ radius := hplen
            _ ≤ 2 * radius := by omega⟩
  · have hzdeleted : z ∉ deleted := by
      intro hzd
      exact Finset.disjoint_left.1 havailable (hpacking.1 hzcenter) hzd
    have hwz : w ∈ ballAvoiding G (deleted : Set V) z (radius + radius) :=
      mem_ballAvoiding_of_not_disjoint_singleton_balls G deleted
        hwdeleted hzdeleted hmeet
    obtain ⟨p, hp, hplen⟩ :=
      (mem_ballAvoiding G (deleted : Set V) z (radius + radius) w).1 hwz
    exact (mem_ballAvoidingFrom G (deleted : Set V)
      (centers ∪ reserved) (2 * radius) w).2
      ⟨z, Finset.mem_union_left _ hzcenter, p, hp, by simpa [two_mul] using hplen⟩

/-- A purely numerical maximal-packing criterion.  If every undeleted
vertex has degree at most `Delta`, then the crude Moore bound forces a capped
packing to attain its cap as soon as even the doubled-radius ball from all
possible centres and reserved vertices is smaller than the available set. -/
theorem exists_full_cappedBallPacking [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted available reserved : Finset V) (radius target Delta : ℕ)
    (havailable : Disjoint available deleted)
    (hreserved : Disjoint reserved deleted)
    (hdegree : ∀ v ∉ deleted, G.degree v ≤ Delta)
    (hnumeric : (target + reserved.card) * (Delta + 1) ^ (2 * radius) <
      available.card) :
    ∃ centers : Finset V,
      IsCappedBallPacking G deleted available reserved radius target centers ∧
      centers.card = target := by
  classical
  obtain ⟨centers, hpacking, hmax⟩ :=
    exists_max_card_cappedBallPacking G deleted available reserved radius target
  refine ⟨centers, hpacking, ?_⟩
  apply Nat.le_antisymm hpacking.2.1
  by_contra hnot
  have hshort : centers.card < target := Nat.lt_of_not_ge hnot
  have hcover := available_subset_doubled_ball_of_maximal_packing
    G deleted available reserved centers radius target havailable hreserved
      hpacking hmax hshort
  have hcentersDeleted : Disjoint centers deleted := by
    rw [Finset.disjoint_left]
    intro z hzcenter hzdeleted
    exact Finset.disjoint_left.1 havailable (hpacking.1 hzcenter) hzdeleted
  have hseedDeleted : Disjoint (centers ∪ reserved) deleted :=
    Finset.disjoint_union_left.2 ⟨hcentersDeleted, hreserved⟩
  have hball := card_ballAvoidingFrom_le_of_degree_bound G
    (centers ∪ reserved) deleted Delta (2 * radius) hseedDeleted hdegree
  have hseedCard : (centers ∪ reserved).card ≤ target + reserved.card := by
    exact (Finset.card_union_le centers reserved).trans (Nat.add_le_add_right
      hpacking.2.1 reserved.card)
  have hballSmall :
      (ballAvoidingFrom G (deleted : Set V) (centers ∪ reserved)
        (2 * radius)).card < available.card := by
    calc
      (ballAvoidingFrom G (deleted : Set V) (centers ∪ reserved)
          (2 * radius)).card
          ≤ (centers ∪ reserved).card * (Delta + 1) ^ (2 * radius) := hball
      _ ≤ (target + reserved.card) * (Delta + 1) ^ (2 * radius) :=
        Nat.mul_le_mul_right _ hseedCard
      _ < available.card := hnumeric
  have havailableCard := Finset.card_le_card hcover
  omega

/-! ## One protected expansion -/

/-! The comparison curve used in the paper is multiplicative rather than
linear.  The next four lemmas isolate the exact induction: at step `i` the
expander pays the vertices of the external neighbourhood which lie in the
deleted set, and spends the remaining expansion on the prescribed increment.
This is the quantitative core of Lemma 3.2. -/

/-- A capped avoiding-ball induction with an arbitrary comparison sequence,
arbitrary increment at each radius, and arbitrary bound for the blocked
external neighbourhood. -/
theorem min_growth_le_card_ballAvoidingFrom_of_lmExpander
    [Fintype V] (G : SimpleGraph V) (epsilon k : ℝ)
    (hexp : IsLMExpander G epsilon k) (X : Set V) (A : Finset V)
    (radius : ℕ) (growth step loss : ℕ → ℕ)
    (hstart : growth 0 ≤ A.card)
    (hnext : ∀ i : ℕ, i < radius →
      growth (i + 1) ≤ growth i + step i)
    (hblocked : ∀ i : ℕ, i < radius →
      (blockedExternalNeighborhood G X
        (ballAvoidingFrom G X A i)).card ≤ loss i)
    (hlower : ∀ i : ℕ, i < radius →
      k / 2 ≤ ((growth i : ℕ) : ℝ))
    (hrate : ∀ i : ℕ, i < radius → ∀ s : ℕ,
      growth i ≤ s → s ≤ Fintype.card V / 2 →
      (((step i + loss i : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ))) :
    min (growth radius) (Fintype.card V / 2 + 1) ≤
      (ballAvoidingFrom G X A radius).card := by
  have hmain : ∀ i : ℕ, i ≤ radius →
      min (growth i) (Fintype.card V / 2 + 1) ≤
        (ballAvoidingFrom G X A i).card := by
    intro i hi
    induction i with
    | zero =>
        simpa using
          (min_le_left (growth 0) (Fintype.card V / 2 + 1)).trans hstart
    | succ i ih =>
        let current := ballAvoidingFrom G X A i
        let cap := Fintype.card V / 2 + 1
        have hiradius : i < radius := by omega
        have ih' : min (growth i) cap ≤ current.card := ih (by omega)
        by_cases hcap : cap ≤ current.card
        · have hmono : current.card ≤
              (ballAvoidingFrom G X A (i + 1)).card :=
            Finset.card_le_card
              (ballAvoidingFrom_radius_mono G X A (Nat.le_succ i))
          exact (min_le_right (growth (i + 1)) cap).trans (hcap.trans hmono)
        · have hcurrentUpper : current.card ≤ Fintype.card V / 2 := by
            dsimp [cap] at hcap
            omega
          have hgrowthCurrent : growth i ≤ current.card := by
            by_cases hgcap : cap ≤ growth i
            · have : cap ≤ current.card := by
                simpa [min_eq_right hgcap] using ih'
              exact (hcap this).elim
            · have hgrowthLeCap : growth i ≤ cap :=
                Nat.le_of_lt (lt_of_not_ge hgcap)
              simpa [min_eq_left hgrowthLeCap] using ih'
          have hcurrentLower : k / 2 ≤ (current.card : ℝ) :=
            (hlower i hiradius).trans (by exact_mod_cast hgrowthCurrent)
          have hcurrentUpperReal : (current.card : ℝ) ≤
              (Fintype.card V : ℝ) / 2 := by
            calc
              (current.card : ℝ) ≤ ((Fintype.card V / 2 : ℕ) : ℝ) := by
                exact_mod_cast hcurrentUpper
              _ ≤ (Fintype.card V : ℝ) / 2 := by
                simpa using (Nat.cast_div_le (α := ℝ)
                  (m := Fintype.card V) (n := 2))
          have hbudget : (((step i +
              (blockedExternalNeighborhood G X current).card : ℕ) : ℝ) ≤
                expansionEpsilon epsilon k current.card *
                  (current.card : ℝ)) := by
            have hnat : step i +
                (blockedExternalNeighborhood G X current).card ≤
                  step i + loss i :=
              Nat.add_le_add_left (hblocked i hiradius) (step i)
            have hcast : (((step i +
                (blockedExternalNeighborhood G X current).card : ℕ) : ℝ) ≤
                  ((step i + loss i : ℕ) : ℝ)) := by
              exact_mod_cast hnat
            exact hcast.trans
              (hrate i hiradius current.card hgrowthCurrent hcurrentUpper)
          have hstep : current.card + step i ≤
              (ballAvoidingFrom G X A (i + 1)).card :=
            hexp.card_ballAvoidingFrom_add_le_succ X A i (step i)
              hcurrentLower hcurrentUpperReal hbudget
          exact (min_le_left (growth (i + 1)) cap).trans <|
            (hnext i hiradius).trans <|
              (Nat.add_le_add_right hgrowthCurrent (step i)).trans hstep
  exact hmain radius le_rfl

/-- Limited contact specializes the arbitrary loss in the variable-growth
induction to `contact * (i + 1)`. -/
theorem min_growth_le_card_ballAvoidingFrom_of_lmExpander_limitedContact
    [Fintype V] (G : SimpleGraph V) (epsilon k : ℝ)
    (hexp : IsLMExpander G epsilon k) (X : Set V) (A : Finset V)
    (contact radius : ℕ) (growth step : ℕ → ℕ)
    (hcontact : HasLimitedContact G A X contact)
    (hstart : growth 0 ≤ A.card)
    (hnext : ∀ i : ℕ, i < radius →
      growth (i + 1) ≤ growth i + step i)
    (hlower : ∀ i : ℕ, i < radius →
      k / 2 ≤ ((growth i : ℕ) : ℝ))
    (hrate : ∀ i : ℕ, i < radius → ∀ s : ℕ,
      growth i ≤ s → s ≤ Fintype.card V / 2 →
      (((step i + contact * (i + 1) : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ))) :
    min (growth radius) (Fintype.card V / 2 + 1) ≤
      (ballAvoidingFrom G X A radius).card := by
  apply min_growth_le_card_ballAvoidingFrom_of_lmExpander
    G epsilon k hexp X A radius growth step
      (fun i ↦ contact * (i + 1)) hstart hnext
  · intro i _
    exact hcontact i
  · exact hlower
  · exact hrate

/-- Monotone comparison curves can use their consecutive differences as the
variable increment. -/
theorem min_growth_le_card_ballAvoidingFrom_of_lmExpander_limitedContact_diff
    [Fintype V] (G : SimpleGraph V) (epsilon k : ℝ)
    (hexp : IsLMExpander G epsilon k) (X : Set V) (A : Finset V)
    (contact radius : ℕ) (growth : ℕ → ℕ)
    (hcontact : HasLimitedContact G A X contact)
    (hstart : growth 0 ≤ A.card) (hgrowth : Monotone growth)
    (hlower : ∀ i : ℕ, i < radius →
      k / 2 ≤ ((growth i : ℕ) : ℝ))
    (hrate : ∀ i : ℕ, i < radius → ∀ s : ℕ,
      growth i ≤ s → s ≤ Fintype.card V / 2 →
      (((growth (i + 1) - growth i + contact * (i + 1) : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ))) :
    min (growth radius) (Fintype.card V / 2 + 1) ≤
      (ballAvoidingFrom G X A radius).card := by
  apply min_growth_le_card_ballAvoidingFrom_of_lmExpander_limitedContact
    G epsilon k hexp X A contact radius growth
      (fun i ↦ growth (i + 1) - growth i) hcontact hstart
  · intro i _
    have hmono : growth i ≤ growth (i + 1) := hgrowth (Nat.le_succ i)
    omega
  · exact hlower
  · exact hrate

/-- A multiplicative specialization with a variable natural factor. -/
theorem min_growth_le_card_ballAvoidingFrom_of_lmExpander_limitedContact_mul
    [Fintype V] (G : SimpleGraph V) (epsilon k : ℝ)
    (hexp : IsLMExpander G epsilon k) (X : Set V) (A : Finset V)
    (contact radius : ℕ) (growth factor : ℕ → ℕ)
    (hcontact : HasLimitedContact G A X contact)
    (hstart : growth 0 ≤ A.card)
    (hfactor : ∀ i : ℕ, i < radius → 1 ≤ factor i)
    (hnext : ∀ i : ℕ, i < radius →
      growth (i + 1) ≤ factor i * growth i)
    (hlower : ∀ i : ℕ, i < radius →
      k / 2 ≤ ((growth i : ℕ) : ℝ))
    (hrate : ∀ i : ℕ, i < radius → ∀ s : ℕ,
      growth i ≤ s → s ≤ Fintype.card V / 2 →
      (((((factor i - 1) * growth i + contact * (i + 1)) : ℕ) : ℝ) ≤
        expansionEpsilon epsilon k s * (s : ℝ))) :
    min (growth radius) (Fintype.card V / 2 + 1) ≤
      (ballAvoidingFrom G X A radius).card := by
  apply min_growth_le_card_ballAvoidingFrom_of_lmExpander_limitedContact
    G epsilon k hexp X A contact radius growth
      (fun i ↦ (factor i - 1) * growth i) hcontact hstart
  · intro i hi
    have hfac := hfactor i hi
    have hfactorEq : 1 + (factor i - 1) = factor i := by omega
    calc
      growth (i + 1) ≤ factor i * growth i := hnext i hi
      _ = (1 + (factor i - 1)) * growth i := by rw [hfactorEq]
      _ = growth i + (factor i - 1) * growth i := by
        simp [Nat.add_mul]
  · exact hlower
  · exact hrate

/-- Passing from a root to its radius-one avoiding ball doubles a
limited-contact constant. -/
theorem oneBall_hasLimitedContact [Fintype V]
    (G : SimpleGraph V) (forbidden : Set V) (x : V) (contact : ℕ)
    (hx : x ∉ forbidden)
    (hcontact : HasLimitedContact G ({x} : Finset V) forbidden contact) :
    HasLimitedContact G (ballAvoiding G forbidden x 1) forbidden
      (2 * contact) := by
  classical
  intro radius
  let A := ballAvoiding G forbidden x 1
  have hsingleton :
      ballAvoidingFrom G forbidden ({x} : Finset V) 1 = A := by
    ext y
    simp [A, ballAvoidingFrom]
  have hsemigroup := ballAvoidingFrom_ballAvoidingFrom_subset
    G forbidden ({x} : Finset V) 1 radius (by simpa using hx)
  have hballs : ballAvoidingFrom G forbidden A radius ⊆
      ballAvoidingFrom G forbidden ({x} : Finset V) (radius + 1) := by
    rw [← hsingleton]
    simpa [Nat.add_comm] using hsemigroup
  have hlargeAvoids : ∀ y ∈
      ballAvoidingFrom G forbidden ({x} : Finset V) (radius + 1),
      y ∉ forbidden := by
    apply ballAvoidingFrom_avoids_forbidden
    simpa using hx
  have hblocked := blockedExternalNeighborhood_subset_of_subset_of_avoids
    G forbidden hballs hlargeAvoids
  have hcard := Finset.card_le_card hblocked
  have hsource := hcontact (radius + 1)
  calc
    (blockedExternalNeighborhood G forbidden
        (ballAvoidingFrom G forbidden A radius)).card
        ≤ (blockedExternalNeighborhood G forbidden
          (ballAvoidingFrom G forbidden ({x} : Finset V)
            (radius + 1))).card := hcard
    _ ≤ contact * ((radius + 1) + 1) := hsource
    _ ≤ contact * (2 * (radius + 1)) :=
      Nat.mul_le_mul_left contact (by omega)
    _ = (2 * contact) * (radius + 1) := by ac_rfl

/-- One prescribed rooted expansion, constructed from the exact expander
inequality after paying a uniform deletion budget. -/
theorem exists_protected_vertexExpansion [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (d m q radius budget D : ℕ) (W : Finset V) (root : V)
    (hmin : d - 1 ≤ G.degree root)
    (hW : W.card ≤ budget)
    (hseed : kappa / 2 ≤ ((d - 1 - budget : ℕ) : ℝ))
    (hrate : ∀ s : ℕ, d - 1 - budget ≤ s →
      s ≤ Fintype.card V / 2 →
      (((budget + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ)))
    (htargetGrowth : D ≤ d - 1 - budget + radius * q)
    (htargetHalf : D ≤ Fintype.card V / 2 + 1)
    (hradius : radius + 1 ≤ m) (hD : 0 < D) :
    ∃ E : VertexExpansion G root D m,
      E.verts ⊆ ballAvoiding G (W : Set V) root (radius + 1) := by
  classical
  let A := ballAvoiding G (W : Set V) root 1
  have hAseed : d - 1 - budget ≤ A.card := by
    exact card_ballAvoiding_one_lower_of_minDegree G W root d budget hmin hW
  have hAlower : kappa / 2 ≤ (A.card : ℝ) :=
    hseed.trans (by exact_mod_cast hAseed)
  have hArate : ∀ s : ℕ, A.card ≤ s → s ≤ Fintype.card V / 2 →
      (((W.card + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ)) := by
    intro s hAs hs
    have hbudgetRate := hrate s (hAseed.trans hAs) hs
    have hWq : (((W.card + q : ℕ) : ℝ)) ≤ (((budget + q : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_le_add_right hW q
    exact hWq.trans hbudgetRate
  have hgrowth := min_card_ballAvoidingFrom_of_lmExpander_growth
    G epsilon kappa hexp W A q radius hAlower hArate
  have hDleft : D ≤ A.card + radius * q := by omega
  have hDmin : D ≤ min (A.card + radius * q) (Fintype.card V / 2 + 1) :=
    (le_min_iff).2 ⟨hDleft, htargetHalf⟩
  have hDfrom : D ≤
      (ballAvoidingFrom G (W : Set V) A radius).card := hDmin.trans hgrowth
  have hfromSubset : ballAvoidingFrom G (W : Set V) A radius ⊆
      ballAvoiding G (W : Set V) root (radius + 1) := by
    simpa [A] using ballAvoidingFrom_ballAvoiding_one_subset G W root radius
  have hDball : D ≤ (ballAvoiding G (W : Set V) root (radius + 1)).card :=
    hDfrom.trans (Finset.card_le_card hfromSubset)
  let Efull := VertexExpansion.ofBallAvoiding G (W : Set V) root (radius + 1)
  obtain ⟨Esmall, hsmall⟩ :=
    Efull.proposition3_10 hD hDball
  let E : VertexExpansion G root D m := Esmall.radiusMono hradius
  refine ⟨E, ?_⟩
  intro z hz
  exact hsmall (by simpa [E] using hz)

/-! ## Simultaneous expansions -/

/-- The exact matrix-indexed conclusion of Liu--Montgomery Lemma 3.11.  The
two indices allow several expansions at each prescribed (distinct) root;
pairwise disjointness is imposed only after removing the shared roots. -/
structure LM311ExpansionFamily (G : SimpleGraph V) {k : ℕ}
    (root : Fin k ↪ V) (order : Fin k → Fin k → ℕ)
    (radius : ℕ) (reserved : Finset V) where
  expansion : ∀ i j : Fin k,
    VertexExpansion G (root i) (order i j) radius
  avoids_protected : ∀ i j : Fin k,
    Disjoint ((expansion i j).verts \ {root i}) reserved
  pairwise_disjoint : ∀ a b : Fin k × Fin k, a ≠ b →
    Disjoint
      ((expansion a.1 a.2).verts \ {root a.1})
      ((expansion b.1 b.2).verts \ {root b.1})

/-- Forget part of the reserved set in a simultaneous expansion family. -/
def LM311ExpansionFamily.mono_reserved {k : ℕ}
    {root : Fin k ↪ V} {order : Fin k → Fin k → ℕ} {radius : ℕ}
    {large small : Finset V}
    (F : LM311ExpansionFamily G root order radius large)
    (hsmall : small ⊆ large) :
    LM311ExpansionFamily G root order radius small where
  expansion := F.expansion
  avoids_protected := fun i j ↦ (F.avoids_protected i j).mono_right hsmall
  pairwise_disjoint := F.pairwise_disjoint

/-! ### Source numerical certificate -/

/-- The explicit Moore bound used for the shortest cycle throughout the
source proof. -/
def lm311GirthBudget (N : ℕ) : ℕ := 2 * (Nat.log 2 N + 2)

/-- Fixed vertices in the high-degree routing barrier: the protected set,
the prescribed roots, and `2k²` selected hubs. -/
def lm311HighFixedBudget (k protectedCard : ℕ) : ℕ :=
  protectedCard + k + 2 * k ^ 2

/-- Radius-one seed retained at a deficient prescribed root in Case I. -/
def lm311HighRootSeed (d k protectedCard : ℕ) : ℕ :=
  d - 1 - (lm311HighFixedBudget k protectedCard + 3 + 2 * k ^ 2)

/-- The complete carrier paid by a high-degree hub ball. -/
def lm311HighCarrierBudget (N k protectedCard routeBound : ℕ) : ℕ :=
  lm311HighFixedBudget k protectedCard + lm311GirthBudget N +
    k ^ 2 * routeBound

/-- The high-hub connector uses its full minimum-degree neighborhood.  The
polylogarithmic high-degree cutoff is needed only for the final petals. -/
def lm311HighHubSeed (N d Delta k protectedCard routeBound : ℕ) : ℕ :=
  max (d - 1) Delta - lm311HighCarrierBudget N k protectedCard routeBound

/-- Radius-one seed retained at a packed low-degree centre in Case II. -/
def lm311ReservoirSeed (d k protectedCard : ℕ) : ℕ :=
  d - 1 - (2 * k ^ 2 + protectedCard + k + 3)

/-- Radius-one seed retained at a deficient low root. -/
def lm311LowRootSeed (d k protectedCard : ℕ) : ℕ :=
  d - 1 - (4 * k ^ 2 + 2 * protectedCard + 2 * k + 3)

/-- High-degree vertices which are genuinely free for Case-I routing. -/
noncomputable def lm311HighCandidates [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Delta : ℕ) (protectedSet cycle roots : Finset V) :
    Finset V :=
  (Finset.univ.filter fun v ↦ Delta ≤ G.degree v) \
    (protectedSet ∪ cycle ∪ roots)

/-- Purely numerical data used by the two cases in the proof of
Liu--Montgomery Lemma 3.11.  Every field is an equality or inequality between
natural or real numbers; in particular this record contains no graph,
packing, path, expansion, or availability predicate. -/
structure LM311Numerics (epsilon kappa : ℝ)
    (N k d D Delta ell₀ m protectedCard : ℕ) where
  k_pos : 0 < k
  four_le_d : 4 ≤ d
  D_pos : 0 < D
  ell₀_pos : 0 < ell₀
  m_pos : 0 < m
  Delta_eq : Delta = D ^ 2

  highRounds : ℕ
  highRootGrowth : ℕ → ℕ
  highRootGain : ℕ → ℕ
  highHubGrowth : ℕ → ℕ
  highHubGain : ℕ → ℕ
  high_root_start : highRootGrowth 0 ≤
    lm311HighRootSeed d k protectedCard
  high_hub_start : highHubGrowth 0 ≤
    lm311HighHubSeed N d Delta k protectedCard (3 * m + 1)
  high_root_next : ∀ i < highRounds,
    highRootGrowth (i + 1) ≤ highRootGrowth i + highRootGain i
  high_hub_next : ∀ i < highRounds,
    highHubGrowth (i + 1) ≤ highHubGrowth i + highHubGain i
  high_root_lower : ∀ i < highRounds,
    kappa / 2 ≤ (highRootGrowth i : ℝ)
  high_hub_lower : ∀ i < highRounds,
    kappa / 2 ≤ (highHubGrowth i : ℝ)
  high_root_rate : ∀ i < highRounds, ∀ s : ℕ,
    highRootGrowth i ≤ s →
    s ≤ N / 2 →
    ((((highRootGain i + lm311HighFixedBudget k protectedCard +
      (2 * (i + 2) + 1) + k ^ 2 * (i + 3) : ℕ) : ℝ)) ≤
      expansionEpsilon epsilon kappa s * (s : ℝ))
  high_hub_rate : ∀ i < highRounds, ∀ s : ℕ,
    highHubGrowth i ≤ s →
    s ≤ N / 2 →
    ((((highHubGain i + lm311HighCarrierBudget N k protectedCard
      (3 * m + 1) : ℕ) : ℝ)) ≤
      expansionEpsilon epsilon kappa s * (s : ℝ))
  high_root_half : N / 2 + 1 ≤ highRootGrowth highRounds
  high_hub_half : N / 2 + 1 ≤ highHubGrowth highRounds
  high_connector : 2 * (highRounds + 1) < 3 * m + 1
  high_star_budget :
    D + protectedCard + lm311GirthBudget N + k +
      k ^ 2 * (3 * m + 1) + k ^ 2 * D ≤ Delta

  packing :
    (k ^ 2 + (k + lm311GirthBudget N + protectedCard)) *
        (Delta + 1) ^ (10 * ell₀) <
      N - (2 * k ^ 2 + lm311GirthBudget N + protectedCard + k)

  reservoirRounds : ℕ
  reservoirGrowth : ℕ → ℕ
  reservoirGain : ℕ → ℕ
  reservoir_radius : reservoirRounds + 1 ≤ ell₀
  reservoir_start : reservoirGrowth 0 ≤
    lm311ReservoirSeed d k protectedCard
  reservoir_next : ∀ i < reservoirRounds,
    reservoirGrowth (i + 1) ≤ reservoirGrowth i + reservoirGain i
  reservoir_seed_lower : ∀ i < reservoirRounds,
    kappa / 2 ≤ (reservoirGrowth i : ℝ)
  reservoir_rate : ∀ i < reservoirRounds, ∀ s : ℕ,
    reservoirGrowth i ≤ s →
    s ≤ N / 2 →
    ((((reservoirGain i + 2 * k ^ 2 + protectedCard + k +
      (2 * (i + 2) + 1) : ℕ) : ℝ)) ≤
      expansionEpsilon epsilon kappa s * (s : ℝ))
  reservoir_target : Delta ≤ reservoirGrowth reservoirRounds
  reservoir_half : Delta ≤ N / 2 + 1

  connectRounds : ℕ
  lowRootGrowth : ℕ → ℕ
  lowRootGain : ℕ → ℕ
  lowReservoirGrowth : ℕ → ℕ
  lowReservoirGain : ℕ → ℕ
  low_root_start : lowRootGrowth 0 ≤
    lm311LowRootSeed d k protectedCard
  low_reservoir_start : lowReservoirGrowth 0 ≤ Delta
  low_root_next : ∀ i < connectRounds,
    lowRootGrowth (i + 1) ≤ lowRootGrowth i + lowRootGain i
  low_reservoir_next : d - 1 ≤ Delta → ∀ i < connectRounds,
    lowReservoirGrowth (i + 1) ≤
      lowReservoirGrowth i + lowReservoirGain i
  low_root_lower : ∀ i < connectRounds,
    kappa / 2 ≤ (lowRootGrowth i : ℝ)
  low_reservoir_lower : d - 1 ≤ Delta → ∀ i < connectRounds,
    kappa / 2 ≤ (lowReservoirGrowth i : ℝ)
  low_root_rate : ∀ i < connectRounds, ∀ s : ℕ,
    lowRootGrowth i ≤ s →
    s ≤ N / 2 →
    ((((lowRootGain i + 4 * k ^ 2 + 2 * protectedCard + 2 * k +
      (2 * (i + 2) + 1) + k ^ 2 * (i + 3) +
      (if i < ell₀ then 0 else k ^ 2 * Delta) : ℕ) : ℝ)) ≤
      expansionEpsilon epsilon kappa s * (s : ℝ))
  low_reservoir_rate : d - 1 ≤ Delta → ∀ i < connectRounds, ∀ s : ℕ,
    lowReservoirGrowth i ≤ s → s ≤ N / 2 →
    ((((lowReservoirGain i + 2 * protectedCard + 2 * k ^ 2 + 2 * k +
      lm311GirthBudget N + k ^ 2 * (3 * m + 1) +
      (if i < ell₀ then 0 else k ^ 2 * Delta) : ℕ) : ℝ)) ≤
      expansionEpsilon epsilon kappa s * (s : ℝ))
  low_root_half : N / 2 + 1 ≤ lowRootGrowth connectRounds
  low_reservoir_half : d - 1 ≤ Delta →
    N / 2 + 1 ≤ lowReservoirGrowth connectRounds
  low_connector : 2 * connectRounds + 1 < 3 * m + 1
  attach_radius : 3 * m + 2 * ell₀ ≤ 5 * m
  low_star_budget :
    D + protectedCard + lm311GirthBudget N + k + k ^ 2 * D ≤ Delta

/-! ### Attaching paths to reservoir expansions -/

/-- Re-root a bounded expansion at one of its vertices, paying a factor two
in the radius. -/
noncomputable def VertexExpansion.reroot {root y : V} {D r : ℕ}
    (E : VertexExpansion G root D r) (hy : y ∈ E.verts) :
    VertexExpansion G y D (2 * r) where
  vertices := E.verts
  root_mem := hy
  card_vertices := E.card_verts
  path_to := by
    intro z hz
    obtain ⟨py, hpy, hpylen, hpysupp⟩ := E.exists_path hy
    obtain ⟨pz, hpz, hpzlen, hpzsupp⟩ := E.exists_path hz
    let w : G.Walk y z := py.reverse.append pz
    refine ⟨w.bypass, w.bypass_isPath, ?_, ?_⟩
    · calc
        w.bypass.length ≤ w.length := w.length_bypass_le_length
        _ = py.length + pz.length := by simp [w]
        _ ≤ 2 * r := by omega
    · intro a ha
      have ha' := w.support_bypass_subset_support ha
      change a ∈ (py.reverse.append pz).support at ha'
      rw [Walk.mem_support_append_iff] at ha'
      rcases ha' with ha' | ha'
      · exact hpysupp a (by simpa [py.support_reverse] using ha')
      · exact hpzsupp a ha'

@[simp] theorem VertexExpansion.verts_reroot {root y : V} {D r : ℕ}
    (E : VertexExpansion G root D r) (hy : y ∈ E.verts) :
    (E.reroot hy).verts = E.verts := rfl

/-- Attach a rooted path to an expansion and retain the old order.  Loop
erasure means no disjointness assumption between the pieces is needed. -/
theorem exists_attached_vertexExpansion {x y : V} {D rp rE R : ℕ}
    (p : G.Walk x y) (hp : p.IsPath) (hplen : p.length ≤ rp)
    (E : VertexExpansion G y D rE) (hR : rp + rE ≤ R) :
    ∃ F : VertexExpansion G x D R,
      F.verts ⊆ p.support.toFinset ∪ E.verts := by
  classical
  let S : Finset V := p.support.toFinset ∪ E.verts
  have hxS : x ∈ S := Finset.mem_union_left _ (by simp)
  let Ffull : VertexExpansion G x S.card (rp + rE) :=
    { vertices := S
      root_mem := hxS
      card_vertices := rfl
      path_to := by
        intro z hz
        rw [Finset.mem_union] at hz
        rcases hz with hzp | hzE
        · have hzp' : z ∈ p.support := by simpa using hzp
          let q := p.takeUntil z hzp'
          exact ⟨q, hp.takeUntil hzp',
            ((p.length_takeUntil_le_length hzp').trans hplen).trans
              (Nat.le_add_right rp rE),
            fun w hw ↦ Finset.mem_union_left _ <| by
              simp only [List.mem_toFinset]
              exact p.support_takeUntil_subset_support hzp' hw⟩
        · obtain ⟨q, hq, hqlen, hqsupp⟩ := E.exists_path hzE
          let w : G.Walk x z := p.append q
          refine ⟨w.bypass, w.bypass_isPath, ?_, ?_⟩
          · calc
              w.bypass.length ≤ w.length := w.length_bypass_le_length
              _ = p.length + q.length := by simp [w]
              _ ≤ rp + rE := Nat.add_le_add hplen hqlen
          · intro a ha
            have ha' := w.support_bypass_subset_support ha
            change a ∈ (p.append q).support at ha'
            rw [Walk.mem_support_append_iff] at ha'
            rcases ha' with ha' | ha'
            · exact Finset.mem_union_left _ (by simpa using ha')
            · exact Finset.mem_union_right _ (hqsupp a ha') }
  have hDcard : D ≤ S.card := by
    rw [← E.card_verts]
    exact Finset.card_le_card Finset.subset_union_right
  obtain ⟨Fsmall, hsmall⟩ :=
    Ffull.proposition3_10 E.size_pos hDcard
  let F : VertexExpansion G x D R := Fsmall.radiusMono hR
  exact ⟨F, by simpa [F] using hsmall⟩

/-- The prefix ending at the first vertex of a prescribed finite set.  This
is the path-trimming operation used when an augmenting connector first enters
an unused hub or reservoir. -/
theorem exists_first_entry_prefix {x y : V} (p : G.Walk x y)
    (hp : p.IsPath) (S : Finset V) (hy : y ∈ S) :
    ∃ z ∈ S, ∃ q : G.Walk x z,
      q.IsPath ∧ q.length ≤ p.length ∧
        q.support ⊆ p.support ∧
        (∀ w : V, w ∈ q.support → w ∈ S → w = z) := by
  classical
  let P : ℕ → Prop := fun i ↦ i ≤ p.length ∧ p.getVert i ∈ S
  have hP : ∃ i, P i := by
    refine ⟨p.length, le_rfl, ?_⟩
    simpa using hy
  let i := Nat.find hP
  have hi : i ≤ p.length ∧ p.getVert i ∈ S := Nat.find_spec hP
  let z := p.getVert i
  let q : G.Walk x z := p.take i
  have hqlen : q.length = i := by
    simp [q, Walk.take_length, Nat.min_eq_left hi.1]
  refine ⟨z, hi.2, q, hp.take i, by omega, ?_, ?_⟩
  · intro w hw
    rw [Walk.support_take] at hw
    exact (List.take_prefix (i + 1) p.support).subset hw
  · intro w hwq hwS
    obtain ⟨j, hjw, hjle⟩ :=
      (Walk.mem_support_iff_exists_getVert (p := q)).1 hwq
    have hji : j ≤ i := by simpa [hqlen] using hjle
    have hqget : q.getVert j = p.getVert j := by
      simp [q, Walk.take_getVert, Nat.min_eq_right hji]
    have hjP : P j := by
      refine ⟨hji.trans hi.1, ?_⟩
      simpa [← hjw, hqget] using hwS
    have hij : i ≤ j := Nat.find_min' hP hjP
    have hjiEq : j = i := Nat.le_antisymm hji hij
    rw [← hjw, hqget, hjiEq]

/-! ### Finite extremal path families

The proof of Lemma 3.11 chooses a family with as many root-to-reservoir paths
as possible and, subject to that, with minimum total length.  Encoding this
lexicographic choice explicitly keeps the subsequent switching argument
constructive. -/

/-- A simple path of length strictly below `bound`, starting in `roots` and
ending in `targets`. -/
abbrev BoundedRootTargetPath [DecidableEq V] (G : SimpleGraph V)
    (roots targets : Finset V) (bound : ℕ) :=
  Σ r : {v : V // v ∈ roots},
    Σ z : {v : V // v ∈ targets},
      {p : G.Walk r.1 z.1 // p.IsPath ∧ p.length < bound}

noncomputable instance [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (roots targets : Finset V) (bound : ℕ) :
    Fintype (BoundedRootTargetPath G roots targets bound) := by
  letI : LocallyFinite G := fun (_ : V) ↦ Fintype.ofFinite _
  dsimp [BoundedRootTargetPath]
  infer_instance

namespace BoundedRootTargetPath

variable [DecidableEq V] {roots targets : Finset V} {bound : ℕ}

abbrev root (p : BoundedRootTargetPath G roots targets bound) : V := p.1.1

abbrev target (p : BoundedRootTargetPath G roots targets bound) : V :=
  p.2.1.1

abbrev walk (p : BoundedRootTargetPath G roots targets bound) :
    G.Walk p.root p.target := p.2.2.1

def supportFinset (p : BoundedRootTargetPath G roots targets bound) : Finset V :=
  p.walk.support.toFinset

abbrev length (p : BoundedRootTargetPath G roots targets bound) : ℕ :=
  p.walk.length

lemma root_mem (p : BoundedRootTargetPath G roots targets bound) :
    p.root ∈ roots := p.1.2

lemma target_mem (p : BoundedRootTargetPath G roots targets bound) :
    p.target ∈ targets := p.2.1.2

lemma isPath (p : BoundedRootTargetPath G roots targets bound) :
    p.walk.IsPath := p.2.2.2.1

lemma length_lt (p : BoundedRootTargetPath G roots targets bound) :
    p.length < bound := p.2.2.2.2

end BoundedRootTargetPath

/-- Source-eligible path families.  Every internal vertex avoids the common
barrier, different paths are disjoint away from the complete root set,
different paths use different target reservoirs (as recorded by `label`),
and no root starts more than `multiplicity` paths. -/
def IsAdmissiblePathFamily [DecidableEq V] {J : Type v} [DecidableEq J]
    {G : SimpleGraph V} (roots targets barrier : Finset V) (label : V → J)
    (bound multiplicity : ℕ)
    (family : Finset (BoundedRootTargetPath G roots targets bound)) : Prop :=
  (∀ p : BoundedRootTargetPath G roots targets bound, p ∈ family →
      p.walk.Avoids (barrier : Set V) ({p.root, p.target} : Set V)) ∧
  Set.InjOn
    (fun (p : BoundedRootTargetPath G roots targets bound) ↦ label p.target)
    family ∧
  (∀ p ∈ family, ∀ q ∈ family, p ≠ q →
      Disjoint (p.supportFinset \ roots) (q.supportFinset \ roots)) ∧
    ∀ r ∈ roots,
      (family.filter fun p ↦ p.root = r).card ≤ multiplicity

/-- Total number of edges in all paths of a finite family. -/
def pathFamilyTotalLength [DecidableEq V] {G : SimpleGraph V}
    {roots targets : Finset V} {bound : ℕ}
    (family : Finset (BoundedRootTargetPath G roots targets bound)) : ℕ :=
  ∑ p ∈ family, p.length

/-- An admissible bounded path family can be chosen lexicographically
extremal: maximum cardinality, then minimum total length. -/
theorem exists_cardMax_lengthMin_pathFamily [Fintype V] [DecidableEq V]
    {J : Type v} [DecidableEq J]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (roots targets barrier : Finset V) (label : V → J)
    (bound multiplicity : ℕ) :
    ∃ family : Finset (BoundedRootTargetPath G roots targets bound),
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family ∧
      (∀ other : Finset (BoundedRootTargetPath G roots targets bound),
        IsAdmissiblePathFamily roots targets barrier label bound multiplicity other →
        other.card ≤ family.card) ∧
      (∀ other : Finset (BoundedRootTargetPath G roots targets bound),
        IsAdmissiblePathFamily roots targets barrier label bound multiplicity other →
        other.card = family.card →
        pathFamilyTotalLength family ≤ pathFamilyTotalLength other) := by
  let originalDecEq : DecidableEq V := inferInstance
  let originalDecRel : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableEq V := originalDecEq
  letI : DecidableRel G.Adj := originalDecRel
  let good : Finset (Finset (BoundedRootTargetPath G roots targets bound)) :=
    Finset.univ.powerset.filter
      (IsAdmissiblePathFamily roots targets barrier label bound multiplicity)
  have hempty :
      (∅ : Finset (BoundedRootTargetPath G roots targets bound)) ∈ good := by
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_powerset.2 (Finset.empty_subset _), ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      have : False := by simpa using hp
      exact this.elim
    · intro p hp
      have : False := by simpa using hp
      exact this.elim
    · intro p hp
      have : False := by simpa using hp
      exact this.elim
    · simp
  have hgood : good.Nonempty := ⟨∅, hempty⟩
  obtain ⟨cardMax, hcardMaxGood, hcardMax⟩ :=
    good.exists_max_image Finset.card hgood
  let bestCard : Finset
      (Finset (BoundedRootTargetPath G roots targets bound)) :=
    good.filter fun family ↦ family.card = cardMax.card
  have hcardMaxBest : cardMax ∈ bestCard :=
    Finset.mem_filter.2 ⟨hcardMaxGood, rfl⟩
  have hbestCard : bestCard.Nonempty := ⟨cardMax, hcardMaxBest⟩
  obtain ⟨family, hfamilyBest, hlengthMin⟩ :=
    bestCard.exists_min_image pathFamilyTotalLength hbestCard
  have hfamilyGood : family ∈ good :=
    (Finset.mem_filter.1 hfamilyBest).1
  have hfamilyCard : family.card = cardMax.card :=
    (Finset.mem_filter.1 hfamilyBest).2
  have hfamilyAdmissible :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family :=
    (Finset.mem_filter.1 hfamilyGood).2
  refine ⟨family, hfamilyAdmissible, ?_, ?_⟩
  · intro other hother
    have hotherGood : other ∈ good := by
      apply Finset.mem_filter.2
      exact ⟨Finset.mem_powerset.2 (Finset.subset_univ other), hother⟩
    exact (hcardMax other hotherGood).trans_eq hfamilyCard.symm
  · intro other hother hotherCard
    apply hlengthMin other
    apply Finset.mem_filter.2
    refine ⟨?_, ?_⟩
    · apply Finset.mem_filter.2
      exact ⟨Finset.mem_powerset.2 (Finset.subset_univ other), hother⟩
    · rw [hotherCard, hfamilyCard]

namespace BoundedRootTargetPath

variable [Fintype V]
variable {J : Type v} [DecidableEq J]
variable {roots targets barrier : Finset V} {label : V → J}
variable {bound multiplicity : ℕ}

/-- The canonical label of a vertex known to lie in a nonempty finite target
set.  Values outside the target set are irrelevant to admissible routes. -/
noncomputable def targetLabel (default : {v : V // v ∈ targets}) (v : V) :
    {v : V // v ∈ targets} :=
  if h : v ∈ targets then ⟨v, h⟩ else default

@[simp] theorem targetLabel_of_mem (default : {v : V // v ∈ targets})
    {v : V} (hv : v ∈ targets) :
    targetLabel (targets := targets) default v = ⟨v, hv⟩ := by
  simp [targetLabel, hv]

theorem targetLabel_injective_on (default : {v : V // v ∈ targets}) :
    Set.InjOn (targetLabel (targets := targets) default) (targets : Set V) := by
  intro x hx y hy hxy
  have hxval : (targetLabel (targets := targets) default x).1 = x :=
    congrArg Subtype.val (targetLabel_of_mem default hx)
  have hyval : (targetLabel (targets := targets) default y).1 = y :=
    congrArg Subtype.val (targetLabel_of_mem default hy)
  exact hxval.symm.trans ((congrArg Subtype.val hxy).trans hyval)

/-- The reservoir-label injection bounds an admissible family by the number
of available labelled reservoirs. -/
theorem IsAdmissiblePathFamily.card_le_labels [Fintype J]
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family) :
    family.card ≤ Fintype.card J := by
  apply Finset.card_le_card_of_injOn
      (fun p : BoundedRootTargetPath G roots targets bound ↦ label p.target)
  · intro p hp
    exact Finset.mem_univ _
  · exact hfamily.2.1

/-- The per-root multiplicity condition gives the complementary global
bound on the number of routes. -/
theorem IsAdmissiblePathFamily.card_le_roots_mul
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family) :
    family.card ≤ roots.card * multiplicity := by
  by_contra hnot
  have hlt : roots.card * multiplicity < family.card := Nat.lt_of_not_ge hnot
  obtain ⟨r, hr, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := family) (t := roots) (f := fun p ↦ p.root)
      (fun p hp ↦ p.root_mem) hlt
  exact (Nat.not_lt_of_ge (hfamily.2.2.2 r hr)) hfiber

/-- A genuinely deficient root makes the global route bound strict. -/
theorem IsAdmissiblePathFamily.card_lt_roots_mul_of_fiber_lt
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family)
    {x : V} (hx : x ∈ roots)
    (hdef : (family.filter fun p ↦ p.root = x).card < multiplicity) :
    family.card < roots.card * multiplicity := by
  rw [Finset.card_eq_sum_card_fiberwise
    (s := family) (t := roots) (f := fun p ↦ p.root)
    (fun p hp ↦ p.root_mem)]
  calc
    (∑ r ∈ roots, (family.filter fun p ↦ p.root = r).card)
        < ∑ _r ∈ roots, multiplicity := by
      apply Finset.sum_lt_sum
      · intro r hr
        exact hfamily.2.2.2 r hr
      · exact ⟨x, hx, hdef⟩
    _ = roots.card * multiplicity := by simp

/-- If an admissible family has not filled all labels, one reservoir label is
unused. -/
theorem IsAdmissiblePathFamily.exists_unused_label [Fintype J]
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family)
    (hshort : family.card < Fintype.card J) :
    ∃ j : J, ∀ p ∈ family, label p.target ≠ j := by
  classical
  by_contra hnone
  push_neg at hnone
  have huniv : (Finset.univ : Finset J) ⊆
      family.image (fun p ↦ label p.target) := by
    intro j hj
    obtain ⟨p, hp, hpj⟩ := hnone j
    exact Finset.mem_image.2 ⟨p, hp, hpj⟩
  have himage :
      (family.image (fun p ↦ label p.target)).card = family.card :=
    Finset.card_image_of_injOn hfamily.2.1
  have hcard := Finset.card_le_card huniv
  have hle : Fintype.card J ≤ family.card := by simpa [himage] using hcard
  exact (not_le_of_gt hshort) hle

/-- Maximality forces a root fibre to attain its allowed multiplicity once
every deficient fibre admits one compatible extra route. -/
theorem filter_card_eq_multiplicity_of_augment
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family)
    (hmaximum : ∀ other : Finset (BoundedRootTargetPath G roots targets bound),
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity other →
      other.card ≤ family.card)
    {x : V} (hx : x ∈ roots)
    (haugment :
      (family.filter fun p ↦ p.root = x).card < multiplicity →
      ∃ p : BoundedRootTargetPath G roots targets bound,
        p ∉ family ∧ p.root = x ∧
          IsAdmissiblePathFamily roots targets barrier label bound multiplicity
            (insert p family)) :
    (family.filter fun p ↦ p.root = x).card = multiplicity := by
  apply Nat.le_antisymm (hfamily.2.2.2 x hx)
  by_contra hnot
  have hdeficient :
      (family.filter fun p ↦ p.root = x).card < multiplicity :=
    Nat.lt_of_not_ge hnot
  obtain ⟨p, hpnot, -, hpinsert⟩ := haugment hdeficient
  have hcard := hmaximum (insert p family) hpinsert
  simp [hpnot] at hcard

/-- Reindex a full fibre over each embedded root by the second matrix
coordinate.  The resulting matrix of routes is injective. -/
theorem exists_routeMatrix_of_fullFibres {k m : ℕ}
    (root : Fin k ↪ V)
    (family : Finset
      (BoundedRootTargetPath G roots targets (3 * m + 1)))
    (hfull : ∀ i : Fin k,
      (family.filter fun p ↦ p.root = root i).card = k) :
    ∃ route : Fin k → Fin k →
        BoundedRootTargetPath G roots targets (3 * m + 1),
      (∀ i j, route i j ∈ family ∧ (route i j).root = root i) ∧
      Function.Injective (Function.uncurry route) := by
  classical
  let fiber (i : Fin k) := family.filter fun p ↦ p.root = root i
  let enumerate (i : Fin k) : Fin k ≃ {p // p ∈ fiber i} :=
    (finCongr (by
      rw [Fintype.card_coe]
      simpa [fiber] using hfull i)).symm.trans
      (Fintype.equivFin {p // p ∈ fiber i}).symm
  let route : Fin k → Fin k →
      BoundedRootTargetPath G roots targets (3 * m + 1) :=
    fun i j ↦ (enumerate i j).1
  refine ⟨route, ?_, ?_⟩
  · intro i j
    have hmem : (enumerate i j).1 ∈ fiber i := (enumerate i j).2
    change (enumerate i j).1 ∈
      family.filter (fun p ↦ p.root = root i) at hmem
    have hparts := Finset.mem_filter.1 hmem
    exact ⟨hparts.1, hparts.2⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hroute
    have hi : i = i' := by
      apply root.injective
      have hrootsEq := congrArg
        (fun p : BoundedRootTargetPath G roots targets (3 * m + 1) ↦ p.root)
        hroute
      have hri : (enumerate i j).1.root = root i := by
        have hm : (enumerate i j).1 ∈ fiber i := (enumerate i j).2
        change (enumerate i j).1 ∈
          family.filter (fun p ↦ p.root = root i) at hm
        exact (Finset.mem_filter.1 hm).2
      have hri' : (enumerate i' j').1.root = root i' := by
        have hm : (enumerate i' j').1 ∈ fiber i' := (enumerate i' j').2
        change (enumerate i' j').1 ∈
          family.filter (fun p ↦ p.root = root i') at hm
        exact (Finset.mem_filter.1 hm).2
      simpa [route, hri, hri'] using hrootsEq
    subst i'
    have hj : j = j' := by
      apply (enumerate i).injective
      change (enumerate i j).1 = (enumerate i j').1 at hroute
      exact Subtype.ext hroute
    subst j'
    rfl

/-- Reindex one full root fibre.  This is the dependent form needed when
only the low-degree prescribed roots are routed in Case II. -/
theorem exists_routeFiber_of_full {k m : ℕ} {x : V}
    (family : Finset
      (BoundedRootTargetPath G roots targets (3 * m + 1)))
    (hfull : (family.filter fun p ↦ p.root = x).card = k) :
    ∃ route : Fin k → BoundedRootTargetPath G roots targets (3 * m + 1),
      (∀ j, route j ∈ family ∧ (route j).root = x) ∧
      Function.Injective route := by
  classical
  let fiber := family.filter fun p ↦ p.root = x
  let enumerate : Fin k ≃ {p // p ∈ fiber} :=
    (finCongr (by
      rw [Fintype.card_coe]
      simpa [fiber] using hfull)).symm.trans
      (Fintype.equivFin {p // p ∈ fiber}).symm
  let route : Fin k → BoundedRootTargetPath G roots targets (3 * m + 1) :=
    fun j ↦ (enumerate j).1
  refine ⟨route, ?_, ?_⟩
  · intro j
    have hm : (enumerate j).1 ∈ fiber := (enumerate j).2
    change (enumerate j).1 ∈ family.filter (fun p ↦ p.root = x) at hm
    exact Finset.mem_filter.1 hm
  · intro a b hab
    apply enumerate.injective
    change (enumerate a).1 = (enumerate b).1 at hab
    exact Subtype.ext hab

noncomputable def familySupport
    (family : Finset (BoundedRootTargetPath G roots targets bound)) : Finset V :=
  family.biUnion supportFinset

/-- A bounded path has fewer than `bound + 1` support vertices, so the whole
extremal carrier has the corresponding union bound. -/
theorem card_familySupport_le
    (family : Finset (BoundedRootTargetPath G roots targets bound)) :
    (familySupport family).card ≤ family.card * bound := by
  classical
  calc
    (familySupport family).card ≤
        ∑ p ∈ family, p.supportFinset.card := by
      simpa [familySupport] using
        (Finset.card_biUnion_le
          (s := family) (t := fun p ↦ p.supportFinset))
    _ ≤ ∑ _p ∈ family, bound := by
      apply Finset.sum_le_sum
      intro p hp
      rw [supportFinset, List.toFinset_card_of_nodup p.isPath.support_nodup,
        p.walk.length_support]
      exact p.length_lt
    _ = family.card * bound := by simp

/-- Attach a full matrix of admissible routes to pairwise fresh endpoint
stars, then shrink each resulting expansion to its requested order. -/
noncomputable def expansionFamilyOfRoutesAndStars
    {k m D endpointRadius R : ℕ}
    (root : Fin k ↪ V) (order : Fin k → Fin k → ℕ)
    (protectedSet base : Finset V)
    (family : Finset
      (BoundedRootTargetPath G roots targets (3 * m + 1)))
    (hfamily : IsAdmissiblePathFamily roots targets barrier label
      (3 * m + 1) k family)
    (hrootsBarrier : roots ⊆ barrier)
    (htargetsBarrier : targets ⊆ barrier)
    (hrootTarget : Disjoint roots targets)
    (hprotectedBarrier : protectedSet ⊆ barrier)
    (htargetProtected : Disjoint targets protectedSet)
    (hfamilyBase : familySupport family ⊆ base)
    (hrootsBase : roots ⊆ base)
    (hprotectedBase : protectedSet ⊆ base)
    (route : Fin k → Fin k →
      BoundedRootTargetPath G roots targets (3 * m + 1))
    (hroute : ∀ i j, route i j ∈ family ∧ (route i j).root = root i)
    (hrouteInj : Function.Injective (Function.uncurry route))
    (star : ∀ i j : Fin k,
      VertexExpansion G (route i j).target D endpointRadius)
    (hstarBase : ∀ i j,
      Disjoint ((star i j).verts \ {(route i j).target}) base)
    (hstarPair : ∀ a b : Fin k × Fin k, a ≠ b →
      Disjoint (star a.1 a.2).verts (star b.1 b.2).verts)
    (hattach : 3 * m + endpointRadius ≤ R)
    (hm : 0 < m) (horderPos : ∀ i j, 0 < order i j)
    (horderLe : ∀ i j, order i j ≤ D) :
    LM311ExpansionFamily G root order R protectedSet := by
  classical
  have castRoot_verts {a b : V} (h : a = b)
      (F : VertexExpansion G a D R) :
      ((h ▸ F : VertexExpansion G b D R)).verts = F.verts := by
    cases h
    rfl
  have hattached (i j : Fin k) :
      ∃ E : VertexExpansion G (root i) D R,
        E.verts ⊆ (route i j).supportFinset ∪ (star i j).verts := by
    obtain ⟨E, hE⟩ := exists_attached_vertexExpansion
      (rp := 3 * m) (R := R)
      (route i j).walk (route i j).isPath
      (Nat.le_of_lt_succ (by simpa using (route i j).length_lt))
      (star i j) hattach
    have hrouteRoot := (hroute i j).2
    let E' : VertexExpansion G (root i) D R := hrouteRoot ▸ E
    refine ⟨E', ?_⟩
    rw [show E'.verts = E.verts from castRoot_verts hrouteRoot E]
    exact hE
  let full (i j : Fin k) : VertexExpansion G (root i) D R :=
    Classical.choose (hattached i j)
  have hfull (i j : Fin k) :
      (full i j).verts ⊆
        (route i j).supportFinset ∪ (star i j).verts :=
    Classical.choose_spec (hattached i j)
  have hsmall (i j : Fin k) :
      ∃ E : VertexExpansion G (root i) (order i j) R,
        E.verts ⊆ (route i j).supportFinset ∪ (star i j).verts := by
    obtain ⟨E, hE⟩ := (full i j).proposition3_10
      (horderPos i j) (horderLe i j)
    exact ⟨E, hE.trans (hfull i j)⟩
  let expansion (i j : Fin k) :
      VertexExpansion G (root i) (order i j) R :=
    Classical.choose (hsmall i j)
  have hexpansion (i j : Fin k) :
      (expansion i j).verts ⊆
        (route i j).supportFinset ∪ (star i j).verts :=
    Classical.choose_spec (hsmall i j)
  have route_not_root_of_mem_trim {i j : Fin k} {z : V}
      (hz : z ∈ (expansion i j).verts \ {root i}) : z ∉ roots := by
    intro hzRoots
    have hzCarrier := hexpansion i j (Finset.mem_sdiff.1 hz).1
    rcases Finset.mem_union.1 hzCarrier with hzPath | hzStar
    · have hzBarrier := hrootsBarrier hzRoots
      have hzPathWalk : z ∈ (route i j).walk.support := by
        simpa only [supportFinset, List.mem_toFinset] using hzPath
      have hzEnds := hfamily.1 (route i j) (hroute i j).1 z hzPathWalk hzBarrier
      have hzEnds' : z = (route i j).root ∨ z = (route i j).target := by
        simpa using hzEnds
      rcases hzEnds' with hzRoot | hzTarget
      · exact (Finset.mem_sdiff.1 hz).2 (by simpa [hroute i j |>.2] using hzRoot)
      · have hzTargets : z ∈ targets := by
          simpa [hzTarget] using (route i j).target_mem
        exact Finset.disjoint_left.1 hrootTarget hzRoots hzTargets
    · by_cases hzCenter : z = (route i j).target
      · have hzTargets : z ∈ targets := by
          simpa [hzCenter] using (route i j).target_mem
        exact Finset.disjoint_left.1 hrootTarget hzRoots hzTargets
      · have hzArm : z ∈ (star i j).verts \ {(route i j).target} :=
          Finset.mem_sdiff.2 ⟨hzStar, by simpa using hzCenter⟩
        have hzBase := Finset.disjoint_left.1 (hstarBase i j) hzArm
          (hrootsBase hzRoots)
        exact hzBase.elim
  have hrouteTargetNe {a b : Fin k × Fin k} (hab : a ≠ b) :
      (route a.1 a.2).target ≠ (route b.1 b.2).target := by
    intro htarget
    have hlabelEq : label (route a.1 a.2).target =
        label (route b.1 b.2).target := congrArg label htarget
    have hrouteEq := hfamily.2.1 (hroute a.1 a.2).1
      (hroute b.1 b.2).1 hlabelEq
    exact hab (hrouteInj hrouteEq)
  let F : LM311ExpansionFamily G root order R protectedSet :=
    { expansion := expansion
      avoids_protected := by
        intro i j
        rw [Finset.disjoint_left]
        intro z hz hzProtected
        have hzCarrier := hexpansion i j (Finset.mem_sdiff.1 hz).1
        rcases Finset.mem_union.1 hzCarrier with hzPath | hzStar
        · have hzPathWalk : z ∈ (route i j).walk.support := by
            simpa only [supportFinset, List.mem_toFinset] using hzPath
          have hzEnds := hfamily.1 (route i j) (hroute i j).1 z hzPathWalk
            (hprotectedBarrier hzProtected)
          rcases (by simpa using hzEnds :
              z = (route i j).root ∨ z = (route i j).target) with hzR | hzT
          · exact (Finset.mem_sdiff.1 hz).2
              (by simpa [hroute i j |>.2] using hzR)
          · have hzTargets : z ∈ targets := by
              simpa [hzT] using (route i j).target_mem
            exact Finset.disjoint_left.1 htargetProtected hzTargets hzProtected
        · by_cases hzT : z = (route i j).target
          · have hzTargets : z ∈ targets := by
              simpa [hzT] using (route i j).target_mem
            exact Finset.disjoint_left.1 htargetProtected hzTargets hzProtected
          · exact (Finset.disjoint_left.1 (hstarBase i j)
              (Finset.mem_sdiff.2 ⟨hzStar, by simpa using hzT⟩)
              (hprotectedBase hzProtected)).elim
      pairwise_disjoint := by
        intro a b hab
        rw [Finset.disjoint_left]
        intro z hzA hzB
        have hzACarrier := hexpansion a.1 a.2 (Finset.mem_sdiff.1 hzA).1
        have hzBCarrier := hexpansion b.1 b.2 (Finset.mem_sdiff.1 hzB).1
        rcases Finset.mem_union.1 hzACarrier with hzAPath | hzAStar <;>
          rcases Finset.mem_union.1 hzBCarrier with hzBPath | hzBStar
        · have hzNotRoots := route_not_root_of_mem_trim hzA
          exact (Finset.disjoint_left.1
            (hfamily.2.2.1 (route a.1 a.2) (hroute a.1 a.2).1
              (route b.1 b.2) (hroute b.1 b.2).1
              (fun h ↦ hab (hrouteInj h)))
            (Finset.mem_sdiff.2 ⟨hzAPath, hzNotRoots⟩)
            (Finset.mem_sdiff.2 ⟨hzBPath, hzNotRoots⟩)).elim
        · by_cases hzCenter : z = (route b.1 b.2).target
          · subst z
            have hzBarrier := htargetsBarrier (route b.1 b.2).target_mem
            have hzAPathWalk : (route b.1 b.2).target ∈
                (route a.1 a.2).walk.support := by
              simpa only [supportFinset, List.mem_toFinset] using hzAPath
            have hzEnds := hfamily.1 (route a.1 a.2) (hroute a.1 a.2).1 _
              hzAPathWalk hzBarrier
            rcases (by simpa using hzEnds :
                (route b.1 b.2).target = (route a.1 a.2).root ∨
                (route b.1 b.2).target = (route a.1 a.2).target) with hR | hT
            · have htRoot : (route b.1 b.2).target ∈ roots := by
                rw [hR]
                exact (route a.1 a.2).root_mem
              exact (Finset.disjoint_left.1 hrootTarget htRoot
                (route b.1 b.2).target_mem).elim
            · exact (hrouteTargetNe hab) hT.symm
          · exact (Finset.disjoint_left.1 (hstarBase b.1 b.2)
              (Finset.mem_sdiff.2 ⟨hzBStar, by simpa using hzCenter⟩)
              (hfamilyBase (Finset.mem_biUnion.2
                ⟨route a.1 a.2, (hroute a.1 a.2).1, hzAPath⟩))).elim
        · by_cases hzCenter : z = (route a.1 a.2).target
          · subst z
            have hzBarrier := htargetsBarrier (route a.1 a.2).target_mem
            have hzBPathWalk : (route a.1 a.2).target ∈
                (route b.1 b.2).walk.support := by
              simpa only [supportFinset, List.mem_toFinset] using hzBPath
            have hzEnds := hfamily.1 (route b.1 b.2) (hroute b.1 b.2).1 _
              hzBPathWalk hzBarrier
            rcases (by simpa using hzEnds :
                (route a.1 a.2).target = (route b.1 b.2).root ∨
                (route a.1 a.2).target = (route b.1 b.2).target) with hR | hT
            · have htRoot : (route a.1 a.2).target ∈ roots := by
                rw [hR]
                exact (route b.1 b.2).root_mem
              exact (Finset.disjoint_left.1 hrootTarget htRoot
                (route a.1 a.2).target_mem).elim
            · exact (hrouteTargetNe hab) hT
          · exact (Finset.disjoint_left.1 (hstarBase a.1 a.2)
              (Finset.mem_sdiff.2 ⟨hzAStar, by simpa using hzCenter⟩)
              (hfamilyBase (Finset.mem_biUnion.2
                ⟨route b.1 b.2, (hroute b.1 b.2).1, hzBPath⟩))).elim
        · exact (Finset.disjoint_left.1 (hstarPair a b hab)
            hzAStar hzBStar).elim }
  exact F

/-- Deleted set used for switching from a deficient root. -/
noncomputable def switchingBarrier
    (barrier : Finset V)
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (x : V) : Finset V :=
  (barrier ∪ familySupport family) \ {x}

noncomputable def switchingContact
    (barrier : Finset V)
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (x : V) (old : BoundedRootTargetPath G roots targets bound)
    (ell : ℕ) : Finset V :=
  externalNeighborhood G
      (ballAvoiding G (switchingBarrier barrier family x : Set V) x ell) ∩
    old.supportFinset

/-- A short path from a deficient root to an unused labelled target augments
the path family whenever it avoids the switching barrier away from its two
endpoints. -/
theorem exists_admissible_insert_of_switching_path
    (hrootsBarrier : roots ⊆ barrier)
    (htargetsBarrier : targets ⊆ barrier)
    (hrootTarget : Disjoint roots targets)
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family)
    {x y : V} (hx : x ∈ roots) (hy : y ∈ targets)
    (hdeficient : (family.filter fun q ↦ q.root = x).card < multiplicity)
    (hyunused : ∀ q ∈ family, label q.target ≠ label y)
    (p : G.Walk x y) (hp : p.IsPath) (hplen : p.length < bound)
    (hpavoid : p.IsAvoidingPath
      ((switchingBarrier barrier family x \ {y} : Finset V) : Set V)
      ({x, y} : Set V)) :
    ∃ new : BoundedRootTargetPath G roots targets bound,
      new ∉ family ∧ new.root = x ∧
        IsAdmissiblePathFamily roots targets barrier label bound multiplicity
          (insert new family) := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  letI : DecidableEq V := originalDecEq
  let new : BoundedRootTargetPath G roots targets bound :=
    ⟨⟨x, hx⟩, ⟨⟨y, hy⟩, ⟨p, hp, hplen⟩⟩⟩
  have hnewRoot : new.root = x := rfl
  have hnewTarget : new.target = y := rfl
  have hnewNot : new ∉ family := by
    intro hnew
    exact hyunused new hnew (by rfl)
  refine ⟨new, hnewNot, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · intro z hz hzBarrier
      by_cases hzx : z = x
      · exact Or.inl (hzx.trans hnewRoot.symm)
      by_cases hzy : z = y
      · exact Or.inr (hzy.trans hnewTarget.symm)
      have hzSwitch : z ∈ switchingBarrier barrier family x := by
        exact Finset.mem_sdiff.2
          ⟨Finset.mem_union_left _ hzBarrier, by simpa using hzx⟩
      have hzDeleted : z ∈ switchingBarrier barrier family x \ {y} :=
        Finset.mem_sdiff.2 ⟨hzSwitch, by simpa using hzy⟩
      have hzEnds := hpavoid.2 z (by simpa [new] using hz) (by simpa using hzDeleted)
      exact (by simpa [hzx, hzy] using hzEnds)
    · exact hfamily.1 q hq
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact (hyunused b hb hab.symm).elim
    · exact (hyunused a ha hab).elim
    · exact hfamily.2.1 ha hb hab
  · intro a ha b hb hab
    have hnewOld (old : BoundedRootTargetPath G roots targets bound)
        (hold : old ∈ family) :
        Disjoint (new.supportFinset \ roots) (old.supportFinset \ roots) := by
      rw [Finset.disjoint_left]
      intro z hzNew hzOld
      obtain ⟨hzP, hzNotRoots⟩ := Finset.mem_sdiff.1 hzNew
      obtain ⟨hzOldSupport, -⟩ := Finset.mem_sdiff.1 hzOld
      have hzx : z ≠ x := fun h ↦ hzNotRoots (h ▸ hx)
      have hzy : z ≠ y := by
        intro hzy
        subst z
        have hyOldWalk : y ∈ old.walk.support := by
          simpa only [supportFinset, List.mem_toFinset] using hzOldSupport
        have hyEnds := hfamily.1 old hold y hyOldWalk (htargetsBarrier hy)
        rcases (by simpa using hyEnds : y = old.root ∨ y = old.target) with hyr | hyt
        · have hyroot : y ∈ roots := by simpa [hyr] using old.root_mem
          exact Finset.disjoint_left.1 hrootTarget hyroot hy
        · exact hyunused old hold (congrArg label hyt).symm
      have hzFamily : z ∈ familySupport family := by
        apply Finset.mem_biUnion.2
        exact ⟨old, hold, hzOldSupport⟩
      have hzSwitch : z ∈ switchingBarrier barrier family x :=
        Finset.mem_sdiff.2
          ⟨Finset.mem_union_right _ hzFamily, by simpa using hzx⟩
      have hzDeleted : z ∈ switchingBarrier barrier family x \ {y} :=
        Finset.mem_sdiff.2 ⟨hzSwitch, by simpa using hzy⟩
      have hzPWalk : z ∈ p.support := by
        simpa only [new, supportFinset, List.mem_toFinset] using hzP
      have hzEnds := hpavoid.2 z hzPWalk (by simpa using hzDeleted)
      exact (by simpa [hzx, hzy] using hzEnds)
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact (hab rfl).elim
    · exact hnewOld b hb
    · exact (hnewOld a ha).symm
    · exact hfamily.2.2.1 a ha b hb hab
  · intro r hr
    by_cases hrx : r = x
    · subst r
      have hfilter :
          ((insert new family).filter fun q ↦ q.root = x) =
            insert new (family.filter fun q ↦ q.root = x) := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hq | hq, hroot⟩
          · exact Or.inl hq
          · exact Or.inr ⟨hq, hroot⟩
        · rintro (hq | ⟨hq, hroot⟩)
          · subst q
            exact ⟨Or.inl rfl, hnewRoot⟩
          · exact ⟨Or.inr hq, hroot⟩
      rw [hfilter]
      simp [hnewNot]
      omega
    · have hfilter :
          ((insert new family).filter fun q ↦ q.root = r) =
            family.filter fun q ↦ q.root = r := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hq | hq, hroot⟩
          · subst q
            exact (hrx (hroot.symm.trans hnewRoot)).elim
          · exact ⟨hq, hroot⟩
        · rintro ⟨hq, hroot⟩
          exact ⟨Or.inr hq, hroot⟩
      rw [hfilter]
      exact hfamily.2.2.2 r hr

/-- A proper suffix of a simple path does not contain its old root. -/
lemma root_not_mem_support_dropUntil
    (p : BoundedRootTargetPath G roots targets bound)
    {w : V} (hw : w ∈ p.walk.support) (hwr : w ≠ p.root) :
    p.root ∉ (p.walk.dropUntil w hw).support := by
  intro hr
  have hsuffix := p.walk.support_dropUntil_suffix_support hw
  have heq : (p.walk.dropUntil w hw).support = p.walk.support :=
    List.Nodup.eq_of_head_mem_of_suffix hsuffix
      (hne := p.walk.support_ne_nil) (by simpa using hr)
      p.isPath.support_nodup
  have hconsOld : p.root :: p.walk.support.tail = p.walk.support :=
    p.walk.cons_tail_support
  have hconsNew : w :: (p.walk.dropUntil w hw).support.tail =
      (p.walk.dropUntil w hw).support :=
    (p.walk.dropUntil w hw).cons_tail_support
  have hconsEq : p.root :: p.walk.support.tail =
      w :: (p.walk.dropUntil w hw).support.tail :=
    hconsOld.trans (heq.symm.trans hconsNew.symm)
  have hrootEq : p.root = w := (List.cons.inj hconsEq).1
  exact hwr hrootEq.symm

/-- Source switching inequality: minimum total length forces each old route
to have at most `ell+2` contacts with the deficient-root ball. -/
theorem switchingContact_card_le_of_lengthMin
    (hrootsBarrier : roots ⊆ barrier)
    (htargetsBarrier : targets ⊆ barrier)
    (hrootTarget : Disjoint roots targets)
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family)
    (hminimum : ∀ other : Finset (BoundedRootTargetPath G roots targets bound),
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity other →
      other.card = family.card →
      pathFamilyTotalLength family ≤ pathFamilyTotalLength other)
    {x : V} (hxroots : x ∈ roots)
    (hxdeficient :
      (family.filter fun p ↦ p.root = x).card < multiplicity)
    {old : BoundedRootTargetPath G roots targets bound} (hold : old ∈ family)
    (ell : ℕ) :
    (switchingContact barrier family x old ell).card ≤ ell + 2 := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  letI : DecidableEq V := originalDecEq
  by_contra hcontactBound
  have hcontactLarge : ell + 2 <
      (switchingContact barrier family x old ell).card :=
    Nat.lt_of_not_ge hcontactBound
  let pref : Finset V := (old.walk.support.take (ell + 2)).toFinset
  have hprefCard : pref.card ≤ ell + 2 := by
    calc
      pref.card ≤ (old.walk.support.take (ell + 2)).length :=
        List.toFinset_card_le _
      _ ≤ ell + 2 := List.length_take_le _ _
  have hnotSubset : ¬ switchingContact barrier family x old ell ⊆ pref := by
    intro hsubset
    have hcard := (Finset.card_le_card hsubset).trans hprefCard
    exact (Nat.not_lt_of_ge hcard) hcontactLarge
  obtain ⟨w, hwContact, hwPrefix⟩ := Finset.not_subset.1 hnotSubset
  have hwOldFin : w ∈ old.supportFinset :=
    (Finset.mem_inter.1 hwContact).2
  have hwOld : w ∈ old.walk.support := List.mem_toFinset.1 hwOldFin
  have hidx : ell + 2 ≤ old.walk.support.idxOf w := by
    have hnotTake : w ∉ old.walk.support.take (ell + 2) := by
      simpa [pref] using hwPrefix
    exact Nat.le_of_not_gt (fun hlt ↦
      hnotTake ((List.mem_take_iff_idxOf_lt hwOld).2 hlt))
  have hwRoot : w ≠ old.root := by
    intro hwr
    subst w
    have hidxRoot : old.walk.support.idxOf old.root = 0 := by
      calc
        old.walk.support.idxOf old.root =
            (old.root :: old.walk.support.tail).idxOf old.root := by
          rw [old.walk.cons_tail_support]
        _ = 0 := List.idxOf_cons_self
    omega
  let ball := ballAvoiding G (switchingBarrier barrier family x : Set V) x ell
  have hwExternal : w ∈ externalNeighborhood G ball :=
    (Finset.mem_inter.1 hwContact).1
  obtain ⟨hwBall, y, hyBall, hyw⟩ :=
    (mem_externalNeighborhood G ball w).1 hwExternal
  obtain ⟨p, hp, hplen⟩ :=
    (mem_ballAvoiding G (switchingBarrier barrier family x : Set V) x ell y).1
      (by simpa [ball] using hyBall)
  have hwNotP : w ∉ p.support := by
    intro hwp
    have hwInBall : w ∈ ballAvoiding G
        (switchingBarrier barrier family x : Set V) x ell :=
      support_subset_ballAvoiding hp hplen w hwp
    exact hwBall (by simpa [ball] using hwInBall)
  let entrance : G.Walk x w := p.concat hyw
  have hentrancePath : entrance.IsPath := hp.1.concat hwNotP hyw
  have hentranceLength : entrance.length ≤ ell + 1 := by
    simpa [entrance] using Nat.add_le_add_right hplen 1
  let suffix : G.Walk w old.target := old.walk.dropUntil w hwOld
  have hsuffixRoot : old.root ∉ suffix.support := by
    simpa [suffix] using root_not_mem_support_dropUntil old hwOld hwRoot
  let raw : G.Walk x old.target := entrance.append suffix
  let newWalk : G.Walk x old.target := raw.bypass
  have hnewPath : newWalk.IsPath := raw.bypass_isPath
  have hidxOldLength : old.walk.support.idxOf w ≤ old.length := by
    have h := List.idxOf_lt_length_of_mem hwOld
    rw [old.walk.length_support] at h
    exact Nat.le_of_lt_succ h
  have hsuffixLength : suffix.length =
      old.length - old.walk.support.idxOf w := by
    simpa [suffix] using old.walk.length_dropUntil hwOld
  have hrawShort : raw.length < old.length := by
    have hrawLength : raw.length = entrance.length + suffix.length := by
      simp [raw]
    have hentranceLt : entrance.length < old.walk.support.idxOf w := by omega
    calc
      raw.length = entrance.length + suffix.length := hrawLength
      _ = entrance.length +
          (old.length - old.walk.support.idxOf w) := by rw [hsuffixLength]
      _ < old.walk.support.idxOf w +
          (old.length - old.walk.support.idxOf w) :=
        Nat.add_lt_add_right hentranceLt _
      _ = old.length := Nat.add_sub_of_le hidxOldLength
  have hnewShort : newWalk.length < old.length :=
    raw.length_bypass_le_length.trans_lt hrawShort
  have hnewBound : newWalk.length < bound := hnewShort.trans old.length_lt
  have hwNotRootSet : w ∉ roots := by
    intro hwRoots
    have hwBarrier : w ∈ barrier := hrootsBarrier hwRoots
    have hwAllowed := hfamily.1 old hold w hwOld hwBarrier
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwAllowed
    rcases hwAllowed with hwo | hwt
    · exact hwRoot hwo
    · have hwtMem : w ∈ targets := hwt.symm ▸ old.target_mem
      exact Finset.disjoint_left.1 hrootTarget hwRoots hwtMem
  have hballAvoids : ∀ z ∈ ball,
      z = x ∨ z ∉ switchingBarrier barrier family x := by
    intro z hz
    have hzReach := (mem_ballAvoiding G
      (switchingBarrier barrier family x : Set V) x ell z).1
        (by simpa [ball] using hz)
    exact hzReach.eq_root_or_not_mem
  have hnewAvoids :
      newWalk.Avoids (barrier : Set V) ({x, old.target} : Set V) := by
    have hrawAvoids :
        raw.Avoids (barrier : Set V) ({x, old.target} : Set V) := by
      intro z hzRaw hzBarrier
      change z ∈ (entrance.append suffix).support at hzRaw
      rw [Walk.mem_support_append_iff] at hzRaw
      rcases hzRaw with hzEntrance | hzSuffix
      · change z ∈ (p.concat hyw).support at hzEntrance
        rw [Walk.support_concat] at hzEntrance
        rcases List.mem_append.1 hzEntrance with hzp | hzw
        · have hzBall : z ∈ ball := by
            have hz' := support_subset_ballAvoiding hp hplen z hzp
            simpa [ball] using hz'
          rcases hballAvoids z hzBall with rfl | hzNotBlocked
          · simp
          · by_cases hzx : z = x
            · simp [hzx]
            · exfalso
              apply hzNotBlocked
              exact Finset.mem_sdiff.2
                ⟨Finset.mem_union_left _ hzBarrier, by simpa [hzx]⟩
        · have hzw' : z = w := by simpa using hzw
          subst z
          have hwAllowed := hfamily.1 old hold w hwOld hzBarrier
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwAllowed
          rcases hwAllowed with hwo | hwt
          · exact (hwRoot hwo).elim
          · simp [hwt]
      · have hzOld : z ∈ old.walk.support :=
          old.walk.support_dropUntil_subset_support hwOld
            (by simpa [suffix] using hzSuffix)
        have hzAllowed := hfamily.1 old hold z hzOld hzBarrier
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzAllowed
        rcases hzAllowed with hzr | hzt
        · exact (hsuffixRoot (by simpa [hzr, suffix] using hzSuffix)).elim
        · simp [hzt]
    exact hrawAvoids.of_support_subset raw.support_bypass_subset_support
  let new : BoundedRootTargetPath G roots targets bound :=
    ⟨⟨x, hxroots⟩, ⟨old.2.1, ⟨newWalk, hnewPath, hnewBound⟩⟩⟩
  have hnewLength : new.length < old.length := hnewShort
  have hnewAvoids' :
      new.walk.Avoids (barrier : Set V) ({new.root, new.target} : Set V) := by
    simpa [new] using hnewAvoids
  let other := insert new (family.erase old)
  have hnewNotErase : new ∉ family.erase old := by
    intro hnewErase
    have hnewFamily : new ∈ family := Finset.mem_of_mem_erase hnewErase
    have hlabelEq : label new.target = label old.target := by simp [new]
    have hnewEqOld := hfamily.2.1 hnewFamily hold hlabelEq
    have hfalse := hnewLength
    rw [hnewEqOld] at hfalse
    exact (Nat.lt_irrefl old.length) hfalse
  have hotherCard : other.card = family.card := by
    change (insert new (family.erase old)).card = family.card
    rw [Finset.card_insert_of_notMem hnewNotErase,
      Finset.card_erase_of_mem hold]
    have hpos : 0 < family.card := Finset.card_pos.2 ⟨old, hold⟩
    omega
  have hnewTraceSubset : new.supportFinset \ roots ⊆
      (old.supportFinset \ roots) ∪ ball := by
    intro z hz
    have hzParts := Finset.mem_sdiff.1 hz
    have hzNew : z ∈ newWalk.support := by
      have hzNewFin : z ∈ new.supportFinset := hzParts.1
      have hzNewWalk : z ∈ new.walk.support := List.mem_toFinset.1 hzNewFin
      simpa [new] using hzNewWalk
    have hzRaw : z ∈ raw.support := raw.support_bypass_subset_support hzNew
    change z ∈ (entrance.append suffix).support at hzRaw
    rw [Walk.mem_support_append_iff] at hzRaw
    rcases hzRaw with hzEntrance | hzSuffix
    · change z ∈ (p.concat hyw).support at hzEntrance
      rw [Walk.support_concat] at hzEntrance
      rcases List.mem_append.1 hzEntrance with hzp | hzw
      · exact Finset.mem_union_right _ (by
          have hz' := support_subset_ballAvoiding hp hplen z hzp
          simpa [ball] using hz')
      · have hzw' : z = w := by simpa using hzw
        subst z
        exact Finset.mem_union_left _
          (Finset.mem_sdiff.2 ⟨hwOldFin, hwNotRootSet⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.2
        ⟨List.mem_toFinset.2
          (old.walk.support_dropUntil_subset_support hwOld
            (by simpa [suffix] using hzSuffix)), hzParts.2⟩
  have hballDisjointRemaining : ∀ q ∈ family.erase old,
      Disjoint ball (q.supportFinset \ roots) := by
    intro q hq
    rw [Finset.disjoint_left]
    intro z hzBall hzQ
    have hzQParts := Finset.mem_sdiff.1 hzQ
    have hzNotX : z ≠ x := by
      intro hzx
      subst z
      exact hzQParts.2 hxroots
    rcases hballAvoids z hzBall with hzx | hzNotBlocked
    · exact (hzNotX hzx).elim
    · exfalso
      apply hzNotBlocked
      apply Finset.mem_sdiff.2
      refine ⟨?_, ?_⟩
      · apply Finset.mem_union_right
        change z ∈ family.biUnion supportFinset
        rw [Finset.mem_biUnion]
        exact ⟨q, Finset.mem_of_mem_erase hq, hzQParts.1⟩
      · simpa [hzNotX]
  have hnewDisjointRemaining : ∀ q ∈ family.erase old,
      Disjoint (new.supportFinset \ roots) (q.supportFinset \ roots) := by
    intro q hq
    apply Finset.disjoint_left.2
    intro z hzNew hzQ
    rcases Finset.mem_union.1 (hnewTraceSubset hzNew) with hzOld | hzBall
    · have hqFamily := Finset.mem_of_mem_erase hq
      have hqNeOld : old ≠ q := by
        intro h
        subst q
        simpa using hq
      exact Finset.disjoint_left.1
        (hfamily.2.2.1 old hold q hqFamily hqNeOld) hzOld hzQ
    · exact Finset.disjoint_left.1 (hballDisjointRemaining q hq) hzBall hzQ
  have hotherAdmissible :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity other := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq
      rw [show other = insert new (family.erase old) by rfl,
        Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact hnewAvoids'
      · exact hfamily.1 q (Finset.mem_of_mem_erase hq)
    · intro a ha b hb hab
      change a ∈ other at ha
      change b ∈ other at hb
      simp only [other, Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · have hnewFamilyLabel : label new.target = label old.target := rfl
        have hbFamily := Finset.mem_of_mem_erase hb
        have hlabel := hfamily.2.1 hold hbFamily
        have : old = b := hlabel (hnewFamilyLabel.symm.trans hab)
        subst b
        have : old ∉ family.erase old := by simp
        exact (this hb).elim
      · have haFamily := Finset.mem_of_mem_erase ha
        have hlabel := hfamily.2.1 haFamily hold
        have : a = old := hlabel
          (hab.trans (show label new.target = label old.target by rfl))
        subst a
        have : old ∉ family.erase old := by simp
        exact (this ha).elim
      · exact hfamily.2.1 (Finset.mem_of_mem_erase ha)
          (Finset.mem_of_mem_erase hb) hab
    · intro a ha b hb hab
      rw [show other = insert new (family.erase old) by rfl,
        Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact hnewDisjointRemaining b hb
      · exact (hnewDisjointRemaining a ha).symm
      · exact hfamily.2.2.1 a (Finset.mem_of_mem_erase ha)
          b (Finset.mem_of_mem_erase hb) hab
    · intro r hr
      by_cases hrx : r = x
      · subst r
        have hfilterSubset :
            (other.filter fun p ↦ p.root = x) ⊆
              insert new (family.filter fun p ↦ p.root = x) := by
          intro q hq
          obtain ⟨hqOther, hqRoot⟩ := Finset.mem_filter.1 hq
          rw [show other = insert new (family.erase old) by rfl,
            Finset.mem_insert] at hqOther
          rcases hqOther with rfl | hqOther
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.2
              ⟨Finset.mem_of_mem_erase hqOther, hqRoot⟩)
        have hcard := Finset.card_le_card hfilterSubset
        have hinsert := Finset.card_insert_le new
          (family.filter fun p ↦ p.root = x)
        omega
      · have hfilterSubset :
            (other.filter fun p ↦ p.root = r) ⊆
              family.filter fun p ↦ p.root = r := by
          intro q hq
          obtain ⟨hqOther, hqRoot⟩ := Finset.mem_filter.1 hq
          rw [show other = insert new (family.erase old) by rfl,
            Finset.mem_insert] at hqOther
          rcases hqOther with rfl | hqOther
          · exact (hrx hqRoot.symm).elim
          · exact Finset.mem_filter.2
              ⟨Finset.mem_of_mem_erase hqOther, hqRoot⟩
        exact (Finset.card_le_card hfilterSubset).trans
          (hfamily.2.2.2 r hr)
  have hminimumApplied := hminimum other hotherAdmissible hotherCard
  have hsumErase :
      pathFamilyTotalLength (family.erase old) + old.length =
        pathFamilyTotalLength family := by
    simp only [pathFamilyTotalLength]
    rw [Finset.sum_erase_add _ _ hold]
  have hsumInsert :
      pathFamilyTotalLength other =
        new.length + pathFamilyTotalLength (family.erase old) := by
    simp [other, pathFamilyTotalLength, hnewNotErase]
  have hotherShorter :
      pathFamilyTotalLength other < pathFamilyTotalLength family := by
    rw [hsumInsert, ← hsumErase]
    omega
  exact (not_lt_of_ge hminimumApplied) hotherShorter

/-- Summing the switching inequality over an optimal family bounds all path
contacts at once. -/
theorem card_external_inter_familySupport_le
    (hrootsBarrier : roots ⊆ barrier)
    (htargetsBarrier : targets ⊆ barrier)
    (hrootTarget : Disjoint roots targets)
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family)
    (hminimum : ∀ other : Finset (BoundedRootTargetPath G roots targets bound),
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity other →
      other.card = family.card →
      pathFamilyTotalLength family ≤ pathFamilyTotalLength other)
    {x : V} (hxroots : x ∈ roots)
    (hxdeficient :
      (family.filter fun p ↦ p.root = x).card < multiplicity)
    (ell : ℕ) :
    (externalNeighborhood G
        (ballAvoiding G (switchingBarrier barrier family x : Set V) x ell) ∩
      familySupport family).card ≤ family.card * (ell + 2) := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  letI : DecidableEq V := originalDecEq
  have hsub : externalNeighborhood G
      (ballAvoiding G (switchingBarrier barrier family x : Set V) x ell) ∩
        familySupport family ⊆
      family.biUnion (fun p ↦ switchingContact barrier family x p ell) := by
    intro z hz
    obtain ⟨hzN, hzFamily⟩ := Finset.mem_inter.1 hz
    obtain ⟨p, hp, hzP⟩ := Finset.mem_biUnion.1 hzFamily
    exact Finset.mem_biUnion.2
      ⟨p, hp, Finset.mem_inter.2 ⟨hzN, hzP⟩⟩
  calc
    (externalNeighborhood G
        (ballAvoiding G (switchingBarrier barrier family x : Set V) x ell) ∩
      familySupport family).card
        ≤ (family.biUnion
          (fun p ↦ switchingContact barrier family x p ell)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ p ∈ family, (switchingContact barrier family x p ell).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ family, (ell + 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact switchingContact_card_le_of_lengthMin
        hrootsBarrier htargetsBarrier hrootTarget family hfamily hminimum
        hxroots hxdeficient hp ell
    _ = family.card * (ell + 2) := by simp

/-- Complete blocked-loss bound for a deficient-root ball: fixed deleted
vertices are paid once, the shortest cycle contributes `2(ell+1)+1`, and
the optimal route family contributes `|family|(ell+2)`. -/
theorem card_blocked_switchingBarrier_le
    {c : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (fixed : Finset V)
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    {x : V}
    (hcover : switchingBarrier barrier family x ⊆
      fixed ∪ C.support.toFinset ∪ familySupport family)
    (hrootsBarrier : roots ⊆ barrier)
    (htargetsBarrier : targets ⊆ barrier)
    (hrootTarget : Disjoint roots targets)
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family)
    (hminimum : ∀ other : Finset (BoundedRootTargetPath G roots targets bound),
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity other →
      other.card = family.card →
      pathFamilyTotalLength family ≤ pathFamilyTotalLength other)
    (hxroots : x ∈ roots)
    (hxdeficient :
      (family.filter fun p ↦ p.root = x).card < multiplicity)
    (ell : ℕ) :
    (blockedExternalNeighborhood G (switchingBarrier barrier family x : Set V)
      (ballAvoiding G (switchingBarrier barrier family x : Set V) x ell)).card ≤
      fixed.card + (2 * (ell + 1) + 1) + family.card * (ell + 2) := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  letI : DecidableEq V := originalDecEq
  let ball := ballAvoiding G (switchingBarrier barrier family x : Set V) x ell
  have hsub : blockedExternalNeighborhood G
      (switchingBarrier barrier family x : Set V)
      ball ⊆ (fixed ∪ C.support.toFinset) ∪
        (externalNeighborhood G ball ∩ familySupport family) := by
    intro z hz
    obtain ⟨hzN, hzBlocked⟩ :=
      (mem_blockedExternalNeighborhood G
        (switchingBarrier barrier family x : Set V) ball z).1 hz
    have hzBlockedFin : z ∈ switchingBarrier barrier family x := by
      simpa using hzBlocked
    have hzCover := hcover hzBlockedFin
    simp only [Finset.mem_union] at hzCover
    rcases hzCover with (hzFixed | hzCycle) | hzFamily
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzFixed)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hzCycle)
    · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hzN, hzFamily⟩)
  have hcycle :
      (C.support.toFinset ∩ externalNeighborhood G ball).card ≤
        2 * (ell + 1) + 1 := by
    apply (Finset.card_le_card ?_).trans
      (hC.card_support_inter_ballAvoiding_le (v := x) (ell + 1))
    intro z hz
    obtain ⟨hzC, hzN⟩ := Finset.mem_inter.1 hz
    exact Finset.mem_inter.2 ⟨hzC,
      externalNeighborhood_ballAvoidingFrom_singleton_subset_ball
        G (switchingBarrier barrier family x : Set V) x ell (by
          simpa [ballAvoidingFrom, ball] using hzN)⟩
  have hpath := card_external_inter_familySupport_le
    hrootsBarrier htargetsBarrier hrootTarget family hfamily hminimum
    hxroots hxdeficient ell
  -- Replace the whole cycle by the cycle vertices actually in the external
  -- neighborhood before counting.
  have hrefined : blockedExternalNeighborhood G
      (switchingBarrier barrier family x : Set V) ball ⊆
      fixed ∪ (C.support.toFinset ∩ externalNeighborhood G ball) ∪
        (externalNeighborhood G ball ∩ familySupport family) := by
    intro z hz
    obtain ⟨hzN, hzBlocked⟩ :=
      (mem_blockedExternalNeighborhood G
        (switchingBarrier barrier family x : Set V) ball z).1 hz
    have hzBlockedFin : z ∈ switchingBarrier barrier family x := by
      simpa using hzBlocked
    have hzCover := hcover hzBlockedFin
    simp only [Finset.mem_union] at hzCover ⊢
    rcases hzCover with (hzFixed | hzCycle) | hzFamily
    · exact Or.inl (Or.inl hzFixed)
    · exact Or.inl (Or.inr (Finset.mem_inter.2 ⟨hzCycle, hzN⟩))
    · exact Or.inr (Finset.mem_inter.2 ⟨hzN, hzFamily⟩)
  have hrefinedCard := Finset.card_le_card hrefined
  have hu₁ := Finset.card_union_le fixed
    (C.support.toFinset ∩ externalNeighborhood G ball)
  have hu₂ := Finset.card_union_le
    (fixed ∪ (C.support.toFinset ∩ externalNeighborhood G ball))
    (externalNeighborhood G ball ∩ familySupport family)
  calc
    (blockedExternalNeighborhood G
        (switchingBarrier barrier family x : Set V) ball).card
        ≤ (fixed ∪ (C.support.toFinset ∩ externalNeighborhood G ball) ∪
          (externalNeighborhood G ball ∩ familySupport family)).card :=
      hrefinedCard
    _ ≤ (fixed ∪ (C.support.toFinset ∩ externalNeighborhood G ball)).card +
          (externalNeighborhood G ball ∩ familySupport family).card := hu₂
    _ ≤ (fixed.card +
          (C.support.toFinset ∩ externalNeighborhood G ball).card) +
          (externalNeighborhood G ball ∩ familySupport family).card :=
      Nat.add_le_add_right hu₁ _
    _ ≤ fixed.card + (2 * (ell + 1) + 1) + family.card * (ell + 2) := by
      dsimp [ball] at hcycle hpath
      exact Nat.add_le_add (Nat.add_le_add_left hcycle fixed.card) hpath

/-- Switching-barrier bookkeeping which charges only the vertices of an
additional reservoir union that are actually contacted at the current
radius.  This is the early/late split used in the low-degree branch of
Lemma 3.11. -/
theorem card_blocked_switchingBarrier_with_extra_le
    {c : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (fixed extra : Finset V)
    (family : Finset (BoundedRootTargetPath G roots targets bound))
    {x : V}
    (hcover : switchingBarrier barrier family x ⊆
      fixed ∪ C.support.toFinset ∪ familySupport family ∪ extra)
    (hrootsBarrier : roots ⊆ barrier)
    (htargetsBarrier : targets ⊆ barrier)
    (hrootTarget : Disjoint roots targets)
    (hfamily :
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity family)
    (hminimum : ∀ other : Finset (BoundedRootTargetPath G roots targets bound),
      IsAdmissiblePathFamily roots targets barrier label bound multiplicity other →
      other.card = family.card →
      pathFamilyTotalLength family ≤ pathFamilyTotalLength other)
    (hxroots : x ∈ roots)
    (hxdeficient :
      (family.filter fun p ↦ p.root = x).card < multiplicity)
    (ell extraLoss : ℕ)
    (hextra :
      (externalNeighborhood G
          (ballAvoiding G (switchingBarrier barrier family x : Set V) x ell) ∩
        extra).card ≤ extraLoss) :
    (blockedExternalNeighborhood G (switchingBarrier barrier family x : Set V)
      (ballAvoiding G (switchingBarrier barrier family x : Set V) x ell)).card ≤
      fixed.card + (2 * (ell + 1) + 1) +
        family.card * (ell + 2) + extraLoss := by
  let ball := ballAvoiding G (switchingBarrier barrier family x : Set V) x ell
  have hcycle :
      (C.support.toFinset ∩ externalNeighborhood G ball).card ≤
        2 * (ell + 1) + 1 := by
    apply (Finset.card_le_card ?_).trans
      (hC.card_support_inter_ballAvoiding_le (v := x) (ell + 1))
    intro z hz
    obtain ⟨hzC, hzN⟩ := Finset.mem_inter.1 hz
    exact Finset.mem_inter.2 ⟨hzC,
      externalNeighborhood_ballAvoidingFrom_singleton_subset_ball
        G (switchingBarrier barrier family x : Set V) x ell (by
          simpa [ballAvoidingFrom, ball] using hzN)⟩
  have hpaths := card_external_inter_familySupport_le
    hrootsBarrier htargetsBarrier hrootTarget family hfamily hminimum
    hxroots hxdeficient ell
  let N := externalNeighborhood G ball
  have hrefined : blockedExternalNeighborhood G
      (switchingBarrier barrier family x : Set V) ball ⊆
      ((fixed ∪ (C.support.toFinset ∩ N)) ∪
        (N ∩ familySupport family)) ∪ (N ∩ extra) := by
    intro z hz
    obtain ⟨hzN, hzBlocked⟩ :=
      (mem_blockedExternalNeighborhood G
        (switchingBarrier barrier family x : Set V) ball z).1 hz
    have hzBlockedFin : z ∈ switchingBarrier barrier family x := by
      simpa using hzBlocked
    have hzCover := hcover hzBlockedFin
    simp only [Finset.mem_union] at hzCover ⊢
    rcases hzCover with ((hzFixed | hzCycle) | hzFamily) | hzExtra
    · exact Or.inl (Or.inl (Or.inl hzFixed))
    · exact Or.inl (Or.inl (Or.inr (Finset.mem_inter.2 ⟨hzCycle, hzN⟩)))
    · exact Or.inl (Or.inr (Finset.mem_inter.2 ⟨hzN, hzFamily⟩))
    · exact Or.inr (Finset.mem_inter.2 ⟨hzN, hzExtra⟩)
  have hcard := Finset.card_le_card hrefined
  have hu1 := Finset.card_union_le fixed (C.support.toFinset ∩ N)
  have hu2 := Finset.card_union_le
    (fixed ∪ (C.support.toFinset ∩ N)) (N ∩ familySupport family)
  have hu3 := Finset.card_union_le
    ((fixed ∪ (C.support.toFinset ∩ N)) ∪
      (N ∩ familySupport family)) (N ∩ extra)
  dsimp [N, ball] at hcycle hpaths hextra
  calc
    (blockedExternalNeighborhood G
        (switchingBarrier barrier family x : Set V) ball).card
        ≤ (((fixed ∪ (C.support.toFinset ∩ N)) ∪
            (N ∩ familySupport family)) ∪ (N ∩ extra)).card := hcard
    _ ≤ ((fixed ∪ (C.support.toFinset ∩ N)) ∪
          (N ∩ familySupport family)).card + (N ∩ extra).card := hu3
    _ ≤ ((fixed ∪ (C.support.toFinset ∩ N)).card +
          (N ∩ familySupport family).card) + (N ∩ extra).card :=
      Nat.add_le_add_right hu2 _
    _ ≤ ((fixed.card + (C.support.toFinset ∩ N).card) +
          (N ∩ familySupport family).card) + (N ∩ extra).card :=
      Nat.add_le_add_right (Nat.add_le_add_right hu1 _) _
    _ ≤ fixed.card + (2 * (ell + 1) + 1) +
          family.card * (ell + 2) + extraLoss := by
      dsimp [N, ball]
      omega

end BoundedRootTargetPath

/-! ## The two source branches -/

/-- If the deleted set is a fixed finite set together with a shortest cycle,
then a radius-`r` root ball loses at most the whole fixed set and `2(r+1)+1`
cycle vertices at its next boundary. -/
theorem card_blocked_fixed_union_shortestCycle_le [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {c v : V} {C : G.Walk c c} (hC : IsShortestCycle C)
    (fixed : Finset V) (r : ℕ) :
    (blockedExternalNeighborhood G
      (((fixed : Set V) ∪ (C.support.toFinset : Set V)))
      (ballAvoiding G ((fixed ∪ C.support.toFinset : Finset V) : Set V)
        v r)).card ≤ fixed.card + (2 * (r + 1) + 1) := by
  let ball := ballAvoiding G
    ((fixed ∪ C.support.toFinset : Finset V) : Set V) v r
  let N := externalNeighborhood G ball
  have hsub : blockedExternalNeighborhood G
      (((fixed : Set V) ∪ (C.support.toFinset : Set V))) ball ⊆
      fixed ∪ (C.support.toFinset ∩ N) := by
    intro z hz
    obtain ⟨hzN, hzDeleted⟩ :=
      (mem_blockedExternalNeighborhood G
        ((fixed : Set V) ∪ (C.support.toFinset : Set V)) ball z).1 hz
    rcases hzDeleted with hzFixed | hzCycle
    · exact Finset.mem_union_left _ hzFixed
    · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hzCycle, hzN⟩)
  have hcycle : (C.support.toFinset ∩ N).card ≤ 2 * (r + 1) + 1 := by
    apply (Finset.card_le_card ?_).trans
      (hC.card_support_inter_ballAvoiding_le (v := v) (r + 1))
    intro z hz
    obtain ⟨hzC, hzN⟩ := Finset.mem_inter.1 hz
    exact Finset.mem_inter.2 ⟨hzC,
      externalNeighborhood_ballAvoidingFrom_singleton_subset_ball
        G (((fixed ∪ C.support.toFinset : Finset V) : Set V)) v r (by
          simpa [ballAvoidingFrom, ball, N] using hzN)⟩
  exact (Finset.card_le_card hsub).trans <|
    (Finset.card_union_le fixed (C.support.toFinset ∩ N)).trans <|
      Nat.add_le_add_left hcycle fixed.card

/-- Turn two large avoiding balls into a short path from a prescribed root
to a prescribed target.  The first seed is contained in the radius-one ball
of the root and the second seed consists of neighbours of the target.  Loop
erasure removes any accidental overlap between the three pieces. -/
theorem exists_short_root_target_path_of_large_balls [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A B : Finset V) {x y : V} (rounds : ℕ)
    (hA : A ⊆ ballAvoiding G (U : Set V) x 1)
    (hB : B ⊆ G.neighborFinset y)
    (hAavoid : ∀ a ∈ A, a ∉ (U : Set V))
    (hBavoid : ∀ b ∈ B, b ∉ (U : Set V))
    (hlarge : Fintype.card V <
      (ballAvoidingFrom G (U : Set V) A rounds).card +
        (ballAvoidingFrom G (U : Set V) B rounds).card) :
    ∃ q : G.Walk x y, q.IsPath ∧ q.length ≤ 2 * (rounds + 1) ∧
      q.IsAvoidingPath (((U \ {y} : Finset V) : Set V))
        ({x, y} : Set V) := by
  classical
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_path_between_avoiding_of_large_balls G (U : Set V) A B
      rounds rounds hAavoid hBavoid hlarge
  obtain ⟨px, hpx, hpxlen⟩ :=
    (mem_ballAvoiding G (U : Set V) x 1 a).1 (hA ha)
  have hby : G.Adj b y := by
    exact (G.mem_neighborFinset y b).1 (hB hb) |>.symm
  let edge : G.Walk b y := Walk.cons hby Walk.nil
  let w : G.Walk x y := (px.append p).append edge
  let q : G.Walk x y := w.bypass
  refine ⟨q, w.bypass_isPath, ?_, ?_⟩
  · calc
      q.length ≤ w.length := w.length_bypass_le_length
      _ = px.length + p.length + 1 := by simp [w, edge]
      _ ≤ 1 + (rounds + rounds) + 1 := by omega
      _ = 2 * (rounds + 1) := by omega
  · refine ⟨w.bypass_isPath, ?_⟩
    intro z hzq hzU
    have hzW : z ∈ w.support := w.support_bypass_subset_support hzq
    have hzParts : (z ∈ px.support ∨ z ∈ p.support) ∨ z ∈ edge.support := by
      simpa only [w, Walk.mem_support_append_iff] using hzW
    have hzU' : z ∈ (U : Set V) := by
      have hzUParts : z ∈ U ∧ z ≠ y := by
        simpa [Finset.mem_singleton] using hzU
      exact hzUParts.1
    rcases hzParts with (hzpx | hzp) | hzedge
    · have hzx : z = x := by simpa using hpx.2 z hzpx hzU'
      exact by simp [hzx]
    · exact (hp.2 z hzp hzU').elim
    · have hzEnds : z = b ∨ z = y := by simpa [edge] using hzedge
      rcases hzEnds with hzb | hzy
      · subst z
        exact (hBavoid b hb hzU').elim
      · exact by simp [hzy]

/-- Variant of the large-ball connector whose second endpoint may be any
vertex of a prescribed reservoir seed. -/
theorem exists_short_root_set_path_of_large_balls [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U A B : Finset V) {x : V} (rounds : ℕ)
    (hA : A ⊆ ballAvoiding G (U : Set V) x 1)
    (hAavoid : ∀ a ∈ A, a ∉ (U : Set V))
    (hBavoid : ∀ b ∈ B, b ∉ (U : Set V))
    (hlarge : Fintype.card V <
      (ballAvoidingFrom G (U : Set V) A rounds).card +
        (ballAvoidingFrom G (U : Set V) B rounds).card) :
    ∃ y ∈ B, ∃ q : G.Walk x y,
      q.IsPath ∧ q.length ≤ 2 * rounds + 1 ∧
        q.IsAvoidingPath (U : Set V) ({x, y} : Set V) := by
  classical
  obtain ⟨a, ha, y, hy, p, hp, hplen⟩ :=
    exists_path_between_avoiding_of_large_balls G (U : Set V) A B
      rounds rounds hAavoid hBavoid hlarge
  obtain ⟨px, hpx, hpxlen⟩ :=
    (mem_ballAvoiding G (U : Set V) x 1 a).1 (hA ha)
  let raw : G.Walk x y := px.append p
  let q : G.Walk x y := raw.bypass
  refine ⟨y, hy, q, raw.bypass_isPath, ?_, ?_⟩
  · calc
      q.length ≤ raw.length := raw.length_bypass_le_length
      _ = px.length + p.length := by simp [raw]
      _ ≤ 1 + (rounds + rounds) := by omega
      _ = 2 * rounds + 1 := by omega
  · refine ⟨raw.bypass_isPath, ?_⟩
    intro z hzq hzU
    have hzRaw : z ∈ raw.support := raw.support_bypass_subset_support hzq
    have hzParts : z ∈ px.support ∨ z ∈ p.support := by
      simpa only [raw, Walk.mem_support_append_iff] using hzRaw
    rcases hzParts with hzpx | hzp
    · have hzx : z = x := by simpa using hpx.2 z hzpx hzU
      exact by simp [hzx]
    · exact (hp.2 z hzp hzU).elim

/-- Grow one of the separated low-degree centres into a `Delta`-vertex
reservoir.  The fixed deleted vertices are paid globally, while the shortest
cycle is paid only through its local `2r+1` contact bound. -/
theorem exists_lowReservoirExpansion [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (k d D Delta ell₀ m protectedCard : ℕ)
    (num : LM311Numerics epsilon kappa (Fintype.card V)
      k d D Delta ell₀ m protectedCard)
    {c v : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (fixed : Finset V)
    (hfixed : fixed.card ≤ 2 * k ^ 2 + protectedCard + k)
    (hv : v ∉ fixed ∪ C.support.toFinset)
    (hmin : d - 1 ≤ G.degree v) :
    ∃ E : VertexExpansion G v Delta ell₀,
      E.verts ⊆ ballAvoiding G
        (((fixed ∪ C.support.toFinset : Finset V) : Set V)) v ell₀ := by
  let deleted : Finset V := fixed ∪ C.support.toFinset
  have hvDeleted : v ∉ deleted := by simpa [deleted] using hv
  have hblocked (r : ℕ) :
      (blockedExternalNeighborhood G (deleted : Set V)
        (ballAvoiding G (deleted : Set V) v r)).card ≤
        (2 * k ^ 2 + protectedCard + k) + (2 * (r + 1) + 1) := by
    have h := card_blocked_fixed_union_shortestCycle_le G (v := v) hC fixed r
    simpa [deleted, Nat.add_assoc] using
      h.trans (Nat.add_le_add_right hfixed (2 * (r + 1) + 1))
  let A := ballAvoiding G (deleted : Set V) v 1
  have hAstart : lm311ReservoirSeed d k protectedCard ≤ A.card := by
    have h := card_ballAvoiding_one_lower_of_blocked G deleted v d
      ((2 * k ^ 2 + protectedCard + k) + 3) hvDeleted hmin (by
        simpa [two_mul, Nat.mul_comm, Nat.add_assoc] using hblocked 0)
    simpa [A, lm311ReservoirSeed, Nat.add_assoc] using h
  let growth : ℕ → ℕ := num.reservoirGrowth
  let loss : ℕ → ℕ := fun r ↦
    (2 * k ^ 2 + protectedCard + k) + (2 * (r + 2) + 1)
  have hgrowth := min_growth_le_card_ballAvoidingFrom_of_lmExpander
    G epsilon kappa hexp (deleted : Set V) A num.reservoirRounds
      growth num.reservoirGain loss
      (by simpa [growth] using num.reservoir_start.trans hAstart)
      (by intro r hr; simpa [growth] using num.reservoir_next r hr)
      (by
        intro r hr
        have hsub : ballAvoidingFrom G (deleted : Set V) A r ⊆
            ballAvoiding G (deleted : Set V) v (r + 1) := by
          simpa [A] using
            ballAvoidingFrom_ballAvoiding_one_subset G deleted v r
        have hav : ∀ z ∈ ballAvoiding G (deleted : Set V) v (r + 1),
            z ∉ (deleted : Set V) := by
          intro z hz
          have hzReach :=
            (mem_ballAvoiding G (deleted : Set V) v (r + 1) z).1 hz
          rcases hzReach.eq_root_or_not_mem with hzv | hzD
          · simpa [hzv] using hvDeleted
          · exact hzD
        have hb := blockedExternalNeighborhood_subset_of_subset_of_avoids
          G (deleted : Set V) hsub hav
        exact (Finset.card_le_card hb).trans (by
          simpa [loss] using hblocked (r + 1)))
      (by
        intro r hr
        simpa [growth] using num.reservoir_seed_lower r hr)
      (by
        intro r hr s hgs hs
        simpa [growth, loss, Nat.add_assoc] using
          num.reservoir_rate r hr s hgs hs)
  have hDelta : Delta ≤
      (ballAvoidingFrom G (deleted : Set V) A num.reservoirRounds).card := by
    have htarget : Delta ≤ growth num.reservoirRounds := by
      simpa [growth] using num.reservoir_target
    have hcap : Delta ≤ Fintype.card V / 2 + 1 := num.reservoir_half
    exact (le_min htarget hcap).trans hgrowth
  have hsub : ballAvoidingFrom G (deleted : Set V) A num.reservoirRounds ⊆
      ballAvoiding G (deleted : Set V) v (num.reservoirRounds + 1) := by
    simpa [A] using ballAvoidingFrom_ballAvoiding_one_subset
      G deleted v num.reservoirRounds
  have hball : Delta ≤
      (ballAvoiding G (deleted : Set V) v (num.reservoirRounds + 1)).card :=
    hDelta.trans (Finset.card_le_card hsub)
  let Efull := VertexExpansion.ofBallAvoiding G (deleted : Set V) v
    (num.reservoirRounds + 1)
  have hDeltaPos : 0 < Delta := by
    rw [num.Delta_eq]
    exact pow_pos num.D_pos 2
  obtain ⟨Esmall, hEsmall⟩ := Efull.proposition3_10 hDeltaPos hball
  let E : VertexExpansion G v Delta ell₀ :=
    Esmall.radiusMono num.reservoir_radius
  refine ⟨E, ?_⟩
  intro z hz
  have hzsmall : z ∈ Esmall.verts := by simpa [E] using hz
  have hzball : z ∈ ballAvoiding G (deleted : Set V) v
      (num.reservoirRounds + 1) := hEsmall hzsmall
  exact ballAvoiding_radius_mono G (deleted : Set V) v
    num.reservoir_radius hzball

/-- Failure of the high-degree alternative supplies `k²` separated
low-degree centres.  All exceptional high-degree vertices, the prescribed
reserved set, the shortest cycle, and the prescribed roots are placed in the
deleted set, so the crude bounded-degree ball estimate applies literally. -/
theorem exists_lowCappedPacking [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (k d D Delta ell₀ m protectedCard : ℕ)
    (reservedSet : Finset V) (hreserved : reservedSet.card ≤ protectedCard)
    {c : V} (C : G.Walk c c)
    (hCcard : C.support.toFinset.card ≤ lm311GirthBudget (Fintype.card V))
    (root : Fin k ↪ V)
    (num : LM311Numerics epsilon kappa (Fintype.card V)
      k d D Delta ell₀ m protectedCard)
    (hlow : (lm311HighCandidates G Delta reservedSet C.support.toFinset
      (Finset.univ.image root)).card < 2 * k ^ 2) :
    let roots : Finset V := Finset.univ.image root
    let high := lm311HighCandidates G Delta reservedSet C.support.toFinset roots
    let fixed := high ∪ reservedSet ∪ roots
    let deleted := fixed ∪ C.support.toFinset
    ∃ centers : Finset V,
      IsCappedBallPacking G deleted (Finset.univ \ deleted) ∅
        (5 * ell₀) (k ^ 2) centers ∧
      centers.card = k ^ 2 ∧
      fixed.card ≤ 2 * k ^ 2 + protectedCard + k := by
  classical
  dsimp only
  let roots : Finset V := Finset.univ.image root
  let high := lm311HighCandidates G Delta reservedSet C.support.toFinset roots
  let fixed := high ∪ reservedSet ∪ roots
  let deleted := fixed ∪ C.support.toFinset
  let available : Finset V := Finset.univ \ deleted
  have hrootsCard : roots.card = k := by
    simpa [roots] using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin k))
        root.injective)
  have hhighCard : high.card ≤ 2 * k ^ 2 := by
    change (lm311HighCandidates G Delta reservedSet C.support.toFinset
      (Finset.univ.image root)).card ≤ 2 * k ^ 2
    exact hlow.le
  have hfixedCard : fixed.card ≤ 2 * k ^ 2 + protectedCard + k := by
    have hu1 := Finset.card_union_le high reservedSet
    have hu2 := Finset.card_union_le (high ∪ reservedSet) roots
    dsimp [fixed]
    calc
      (high ∪ reservedSet ∪ roots).card ≤
          (high ∪ reservedSet).card + roots.card := hu2
      _ ≤ (high.card + reservedSet.card) + roots.card :=
        Nat.add_le_add_right hu1 roots.card
      _ ≤ 2 * k ^ 2 + protectedCard + k :=
        Nat.add_le_add (Nat.add_le_add hhighCard hreserved) hrootsCard.le
  have hdeletedCard : deleted.card ≤
      2 * k ^ 2 + lm311GirthBudget (Fintype.card V) + protectedCard + k := by
    have hu := Finset.card_union_le fixed C.support.toFinset
    dsimp [deleted]
    exact hu.trans (by omega)
  have hdegree : ∀ v ∉ deleted, G.degree v ≤ Delta := by
    intro v hv
    by_contra hnot
    have hvDelta : Delta ≤ G.degree v := Nat.le_of_not_ge hnot
    have hvNotFixed : v ∉ fixed := fun h ↦ hv (Finset.mem_union_left _ h)
    have hvNotCycle : v ∉ C.support.toFinset := fun h ↦
      hv (Finset.mem_union_right _ h)
    have hvNotHigh : v ∉ high := fun h ↦ hvNotFixed
      (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hvNotReserved : v ∉ reservedSet := fun h ↦ hvNotFixed
      (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvNotRoots : v ∉ roots := fun h ↦ hvNotFixed
      (Finset.mem_union_right _ h)
    apply hvNotHigh
    dsimp [high, lm311HighCandidates]
    exact Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hvDelta⟩,
      by simpa [Finset.union_assoc] using
        (show v ∉ (reservedSet ∪ C.support.toFinset) ∪ roots from by
          simp [hvNotReserved, hvNotCycle, hvNotRoots])⟩
  have havailable : Disjoint available deleted := by
    exact Finset.sdiff_disjoint
  have hreservedEmpty : Disjoint (∅ : Finset V) deleted := by simp
  have havailableCard : Fintype.card V -
      (2 * k ^ 2 + lm311GirthBudget (Fintype.card V) + protectedCard + k) ≤
      available.card := by
    dsimp [available]
    rw [Finset.card_sdiff, Finset.card_univ]
    have hinter : (deleted ∩ (Finset.univ : Finset V)).card = deleted.card := by
      simp
    rw [hinter]
    exact Nat.sub_le_sub_left hdeletedCard (Fintype.card V)
  have hnumeric :
      (k ^ 2 + (∅ : Finset V).card) * (Delta + 1) ^ (2 * (5 * ell₀)) <
        available.card := by
    calc
      (k ^ 2 + (∅ : Finset V).card) * (Delta + 1) ^ (2 * (5 * ell₀)) ≤
          (k ^ 2 + (k + lm311GirthBudget (Fintype.card V) + protectedCard)) *
            (Delta + 1) ^ (10 * ell₀) := by
        simp only [Finset.card_empty, add_zero]
        rw [show 2 * (5 * ell₀) = 10 * ell₀ by omega]
        apply Nat.mul_le_mul_right
        omega
      _ < Fintype.card V -
          (2 * k ^ 2 + lm311GirthBudget (Fintype.card V) + protectedCard + k) :=
        num.packing
      _ ≤ available.card := havailableCard
  obtain ⟨centers, hpacking, hcard⟩ := exists_full_cappedBallPacking G
    deleted available ∅ (5 * ell₀) (k ^ 2) Delta havailable
      hreservedEmpty hdegree hnumeric
  exact ⟨centers, hpacking, hcard, hfixedCard⟩

/-- Reindex the capped packing and grow every centre into a pairwise-disjoint
`Delta`-vertex reservoir. -/
theorem exists_lowReservoirSystem [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (k d D Delta ell₀ m protectedCard : ℕ)
    (reservedSet : Finset V) (hreserved : reservedSet.card ≤ protectedCard)
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (root : Fin k ↪ V) (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (num : LM311Numerics epsilon kappa (Fintype.card V)
      k d D Delta ell₀ m protectedCard)
    (hlow : (lm311HighCandidates G Delta reservedSet C.support.toFinset
      (Finset.univ.image root)).card < 2 * k ^ 2) :
    let roots : Finset V := Finset.univ.image root
    let high := lm311HighCandidates G Delta reservedSet C.support.toFinset roots
    let fixed := high ∪ reservedSet ∪ roots
    let deleted := fixed ∪ C.support.toFinset
    ∃ center : Fin (k ^ 2) ↪ V,
      ∃ reservoir : ∀ s : Fin (k ^ 2),
        VertexExpansion G (center s) Delta ell₀,
        (∀ s, Disjoint (reservoir s).verts deleted) ∧
        (∀ s t, s ≠ t →
          Disjoint (reservoir s).verts (reservoir t).verts) := by
  classical
  dsimp only
  let roots : Finset V := Finset.univ.image root
  let high := lm311HighCandidates G Delta reservedSet C.support.toFinset roots
  let fixed := high ∪ reservedSet ∪ roots
  let deleted := fixed ∪ C.support.toFinset
  have hdegreeThree : ∀ v : V, 3 ≤ G.degree v := by
    intro v
    have hv := hmin v
    have hd := num.four_le_d
    omega
  have hCcard : C.support.toFinset.card ≤
      lm311GirthBudget (Fintype.card V) := by
    rw [cycle_support_toFinset_card_eq_length C hC.1]
    simpa [lm311GirthBudget] using
      hC.length_le_two_mul_log_add_two G hdegreeThree
  obtain ⟨centers, hpacking, hcentersCard, hfixedCard⟩ :=
    exists_lowCappedPacking G epsilon kappa k d D Delta ell₀ m protectedCard
      reservedSet hreserved C hCcard root num hlow
  let enumerate : Fin (k ^ 2) ≃ {v : V // v ∈ centers} :=
    (finCongr (by simpa using hcentersCard)).symm.trans
      (Fintype.equivFin {v : V // v ∈ centers}).symm
  let center : Fin (k ^ 2) ↪ V :=
    ⟨fun s ↦ (enumerate s).1, fun _ _ h ↦ enumerate.injective (Subtype.ext h)⟩
  have hcenterMem (s : Fin (k ^ 2)) : center s ∈ centers := (enumerate s).2
  have hcenterDeleted (s : Fin (k ^ 2)) : center s ∉ deleted := by
    exact Finset.disjoint_left.1 (Finset.sdiff_disjoint :
      Disjoint (Finset.univ \ deleted) deleted) (hpacking.1 (hcenterMem s))
  have hexists (s : Fin (k ^ 2)) :
      ∃ E : VertexExpansion G (center s) Delta ell₀,
        E.verts ⊆ ballAvoiding G (deleted : Set V) (center s) ell₀ := by
    apply exists_lowReservoirExpansion G epsilon kappa hexp
      k d D Delta ell₀ m protectedCard num C hC fixed hfixedCard
    · simpa [deleted] using hcenterDeleted s
    · exact hmin (center s)
  let reservoir (s : Fin (k ^ 2)) :
      VertexExpansion G (center s) Delta ell₀ := Classical.choose (hexists s)
  have hreservoirBall (s : Fin (k ^ 2)) :
      (reservoir s).verts ⊆
        ballAvoiding G (deleted : Set V) (center s) ell₀ :=
    Classical.choose_spec (hexists s)
  refine ⟨center, reservoir, ?_, ?_⟩
  · intro s
    rw [Finset.disjoint_left]
    intro z hzE hzD
    have hzBall := hreservoirBall s hzE
    have hzAvoid := ballAvoidingFrom_avoids_forbidden G (deleted : Set V)
      ({center s} : Finset V) ell₀ (by simpa using hcenterDeleted s)
    exact (hzAvoid z (by simpa [ballAvoidingFrom] using hzBall) hzD).elim
  · intro s t hst
    apply (hpacking.2.2.1 (hcenterMem s) (hcenterMem t)
      (fun h ↦ hst (center.injective h))).mono
    · intro z hz
      exact ballAvoiding_radius_mono G (deleted : Set V) (center s) (by omega)
        (hreservoirBall s hz)
    · intro z hz
      exact ballAvoiding_radius_mono G (deleted : Set V) (center t) (by omega)
        (hreservoirBall t hz)

/-- The union of a finite indexed family of reservoir carriers. -/
noncomputable def reservoirUnion {n Delta radius : ℕ}
    {center : Fin n → V}
    (reservoir : ∀ s : Fin n, VertexExpansion G (center s) Delta radius) :
    Finset V :=
  Finset.univ.biUnion fun s ↦ (reservoir s).verts

/-- Canonical reservoir label of a vertex.  The default is used only outside
the reservoir union. -/
noncomputable def reservoirLabel {n Delta radius : ℕ}
    {center : Fin n → V}
    (default : Fin n)
    (reservoir : ∀ s : Fin n, VertexExpansion G (center s) Delta radius)
    (v : V) : Fin n :=
  if h : ∃ s : Fin n, v ∈ (reservoir s).verts then Classical.choose h
  else default

theorem reservoir_mem_union {n Delta radius : ℕ}
    {center : Fin n → V}
    (reservoir : ∀ s : Fin n, VertexExpansion G (center s) Delta radius)
    (s : Fin n) {v : V} (hv : v ∈ (reservoir s).verts) :
    v ∈ reservoirUnion reservoir := by
  classical
  exact Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _, hv⟩

theorem reservoirLabel_eq_of_mem {n Delta radius : ℕ}
    {center : Fin n → V}
    (default : Fin n)
    (reservoir : ∀ s : Fin n, VertexExpansion G (center s) Delta radius)
    (hpair : ∀ s t, s ≠ t →
      Disjoint (reservoir s).verts (reservoir t).verts)
    (s : Fin n) {v : V} (hv : v ∈ (reservoir s).verts) :
    reservoirLabel default reservoir v = s := by
  classical
  let hex : ∃ t : Fin n, v ∈ (reservoir t).verts := ⟨s, hv⟩
  rw [reservoirLabel, dif_pos hex]
  let t : Fin n := Classical.choose hex
  have hvt : v ∈ (reservoir t).verts := Classical.choose_spec hex
  change t = s
  by_contra hne
  exact (Finset.disjoint_left.1 (hpair t s hne) hvt hv).elim

/-- Source-exact Case-II reservoirs.  The high-degree set `L` is the deleted
set for packing, while prescribed roots, the protected set, and the part of
the shortest cycle outside `L` are protected as genuinely distant seeds. -/
theorem exists_sourceLowReservoirSystem [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (k d D Delta ell₀ m protectedCard : ℕ)
    (reservedSet : Finset V) (hreserved : reservedSet.card ≤ protectedCard)
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (root : Fin k ↪ V) (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (num : LM311Numerics epsilon kappa (Fintype.card V)
      k d D Delta ell₀ m protectedCard)
    (hlow : (lm311HighCandidates G Delta reservedSet C.support.toFinset
      (Finset.univ.image root)).card < 2 * k ^ 2) :
    let roots : Finset V := Finset.univ.image root
    let L : Finset V := Finset.univ.filter fun v ↦ Delta ≤ G.degree v
    let lowRoots := roots \ L
    let protectedSet := (reservedSet ∪ C.support.toFinset) ∪ roots
    ∃ center : Fin (k ^ 2) ↪ V,
      ∃ reservoir : ∀ s : Fin (k ^ 2),
        VertexExpansion G (center s) Delta ell₀,
        (∀ s, center s ∉ L) ∧
        (∀ s, Disjoint (reservoir s).verts protectedSet) ∧
        (∀ s t, s ≠ t →
          Disjoint (reservoir s).verts (reservoir t).verts) ∧
        (∀ s, (reservoir s).verts ⊆
          ballAvoiding G (L : Set V) (center s) ell₀) ∧
        (∀ s t, s ≠ t → Disjoint
          (ballAvoiding G (L : Set V) (center s) (5 * ell₀))
          (ballAvoiding G (L : Set V) (center t) (5 * ell₀))) ∧
        (∀ s, Disjoint
          (ballAvoiding G (L : Set V) (center s) (5 * ell₀)) lowRoots) := by
  classical
  dsimp only
  let roots : Finset V := Finset.univ.image root
  let L : Finset V := Finset.univ.filter fun v ↦ Delta ≤ G.degree v
  let lowRoots := roots \ L
  let protectedSet := (reservedSet ∪ C.support.toFinset) ∪ roots
  let fixed : Finset V := L \ C.support.toFinset
  let guard : Finset V := protectedSet \ L
  let available : Finset V := Finset.univ \ L
  have hrootsCard : roots.card = k := by
    simpa [roots] using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin k))
        root.injective)
  have hfixedSub : fixed ⊆
      lm311HighCandidates G Delta reservedSet C.support.toFinset roots ∪
        reservedSet ∪ roots := by
    intro v hv
    obtain ⟨hvL, hvC⟩ := Finset.mem_sdiff.1 hv
    by_cases hvR : v ∈ reservedSet
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvR)
    by_cases hvX : v ∈ roots
    · exact Finset.mem_union_right _ hvX
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    change v ∈ (Finset.univ.filter fun w ↦ Delta ≤ G.degree w) \
      (reservedSet ∪ C.support.toFinset ∪ roots)
    exact Finset.mem_sdiff.2 ⟨hvL, by
      intro hvUnion
      rcases Finset.mem_union.1 hvUnion with hvRC | hvRoots
      · rcases Finset.mem_union.1 hvRC with hvReserved | hvCycle
        · exact hvR hvReserved
        · exact hvC hvCycle
      · exact hvX hvRoots⟩
  have hfixedCard : fixed.card ≤ 2 * k ^ 2 + protectedCard + k := by
    have hc := Finset.card_le_card hfixedSub
    have hu1 := Finset.card_union_le
      (lm311HighCandidates G Delta reservedSet C.support.toFinset roots)
      reservedSet
    have hu2 := Finset.card_union_le
      (lm311HighCandidates G Delta reservedSet C.support.toFinset roots ∪
        reservedSet) roots
    have hhc : (lm311HighCandidates G Delta reservedSet C.support.toFinset
      roots).card ≤ 2 * k ^ 2 := by
      change (lm311HighCandidates G Delta reservedSet C.support.toFinset
        (Finset.univ.image root)).card ≤ 2 * k ^ 2
      exact hlow.le
    calc
      fixed.card ≤
          (lm311HighCandidates G Delta reservedSet C.support.toFinset roots ∪
            reservedSet ∪ roots).card := hc
      _ ≤ (lm311HighCandidates G Delta reservedSet C.support.toFinset roots ∪
            reservedSet).card + roots.card := hu2
      _ ≤ ((lm311HighCandidates G Delta reservedSet C.support.toFinset roots).card +
            reservedSet.card) + roots.card := Nat.add_le_add_right hu1 roots.card
      _ ≤ 2 * k ^ 2 + protectedCard + k :=
        Nat.add_le_add (Nat.add_le_add hhc hreserved) hrootsCard.le
  have hdegree : ∀ v ∉ L, G.degree v ≤ Delta := by
    intro v hv
    have hlt : G.degree v < Delta := by
      by_contra hnot
      have hvDelta : Delta ≤ G.degree v := Nat.le_of_not_gt hnot
      exact hv (Finset.mem_filter.2 ⟨Finset.mem_univ _, hvDelta⟩)
    exact hlt.le
  have hguardL : Disjoint guard L := Finset.sdiff_disjoint
  have havailableL : Disjoint available L := Finset.sdiff_disjoint
  have hdegreeThree : ∀ v : V, 3 ≤ G.degree v := by
    intro v
    have hv := hmin v
    have hd := num.four_le_d
    omega
  have hCcard : C.support.toFinset.card ≤
      lm311GirthBudget (Fintype.card V) := by
    rw [cycle_support_toFinset_card_eq_length C hC.1]
    simpa [lm311GirthBudget] using
      hC.length_le_two_mul_log_add_two G hdegreeThree
  have hLcard : L.card ≤
      2 * k ^ 2 + protectedCard + k +
        lm311GirthBudget (Fintype.card V) := by
    have hLsub : L ⊆ fixed ∪ C.support.toFinset := by
      intro v hv
      by_cases hvC : v ∈ C.support.toFinset
      · exact Finset.mem_union_right _ hvC
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hv, hvC⟩)
    exact (Finset.card_le_card hLsub).trans <|
      (Finset.card_union_le fixed C.support.toFinset).trans (by omega)
  have havailableCard : Fintype.card V -
      (2 * k ^ 2 + lm311GirthBudget (Fintype.card V) + protectedCard + k) ≤
      available.card := by
    dsimp [available]
    rw [Finset.card_sdiff, Finset.card_univ]
    have hinter : (L ∩ (Finset.univ : Finset V)).card = L.card := by simp
    rw [hinter]
    apply Nat.sub_le_sub_left
    omega
  have hguardCard : guard.card ≤
      k + lm311GirthBudget (Fintype.card V) + protectedCard := by
    have hpC := Finset.card_union_le reservedSet C.support.toFinset
    have hpCR := Finset.card_union_le (reservedSet ∪ C.support.toFinset) roots
    exact (Finset.card_le_card Finset.sdiff_subset).trans <|
      hpCR.trans (by omega)
  have hnumeric : (k ^ 2 + guard.card) *
      (Delta + 1) ^ (2 * (5 * ell₀)) < available.card := by
    calc
      (k ^ 2 + guard.card) * (Delta + 1) ^ (2 * (5 * ell₀)) ≤
          (k ^ 2 + (k + lm311GirthBudget (Fintype.card V) + protectedCard)) *
            (Delta + 1) ^ (10 * ell₀) := by
        rw [show 2 * (5 * ell₀) = 10 * ell₀ by omega]
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_left hguardCard (k ^ 2))
      _ < Fintype.card V -
          (2 * k ^ 2 + lm311GirthBudget (Fintype.card V) + protectedCard + k) :=
        num.packing
      _ ≤ available.card := havailableCard
  obtain ⟨centers, hpacking, hcentersCard⟩ := exists_full_cappedBallPacking G
    L available guard (5 * ell₀) (k ^ 2) Delta havailableL hguardL
      hdegree hnumeric
  let enumerate : Fin (k ^ 2) ≃ {v : V // v ∈ centers} :=
    (finCongr (by simpa using hcentersCard)).symm.trans
      (Fintype.equivFin {v : V // v ∈ centers}).symm
  let center : Fin (k ^ 2) ↪ V :=
    ⟨fun s ↦ (enumerate s).1, fun _ _ h ↦ enumerate.injective (Subtype.ext h)⟩
  have hcenterMem (s : Fin (k ^ 2)) : center s ∈ centers := (enumerate s).2
  have hcenterL (s : Fin (k ^ 2)) : center s ∉ L := by
    exact Finset.disjoint_left.1 havailableL (hpacking.1 (hcenterMem s))
  have hcenterCycle (s : Fin (k ^ 2)) : center s ∉ C.support.toFinset := by
    intro hsC
    by_cases hsL : center s ∈ L
    · exact hcenterL s hsL
    · have hsGuard : center s ∈ guard := by
        exact Finset.mem_sdiff.2 ⟨Finset.mem_union_left _
          (Finset.mem_union_right _ hsC), hsL⟩
      have hsBall : center s ∈ ballAvoiding G (L : Set V) (center s)
          (5 * ell₀) := by simp
      exact (Finset.disjoint_left.1 (hpacking.2.2.2 _ (hcenterMem s))
        hsBall hsGuard).elim
  have hexists (s : Fin (k ^ 2)) :
      ∃ E : VertexExpansion G (center s) Delta ell₀,
        E.verts ⊆ ballAvoiding G (((fixed ∪ C.support.toFinset : Finset V) : Set V))
          (center s) ell₀ := by
    apply exists_lowReservoirExpansion G epsilon kappa hexp
      k d D Delta ell₀ m protectedCard num C hC fixed hfixedCard
    · intro hsUnion
      rcases Finset.mem_union.1 hsUnion with hsFixed | hsCycle
      · exact hcenterL s (Finset.mem_sdiff.1 hsFixed).1
      · exact hcenterCycle s hsCycle
    · exact hmin (center s)
  let reservoir (s : Fin (k ^ 2)) :
      VertexExpansion G (center s) Delta ell₀ := Classical.choose (hexists s)
  have hreservoirSmallBall (s : Fin (k ^ 2)) :
      (reservoir s).verts ⊆
        ballAvoiding G (((fixed ∪ C.support.toFinset : Finset V) : Set V))
          (center s) ell₀ := Classical.choose_spec (hexists s)
  have hreservoirLBall (s : Fin (k ^ 2)) :
      (reservoir s).verts ⊆ ballAvoiding G (L : Set V) (center s) ell₀ := by
    intro z hz
    obtain ⟨p, hp, hplen⟩ :=
      (mem_ballAvoiding G (((fixed ∪ C.support.toFinset : Finset V) : Set V))
        (center s) ell₀ z).1 (hreservoirSmallBall s hz)
    rw [mem_ballAvoiding]
    refine ⟨p, ⟨hp.1, ?_⟩, hplen⟩
    intro w hw hwL
    have hwDeleted : w ∈ ((fixed ∪ C.support.toFinset : Finset V) : Set V) := by
      by_cases hwC : w ∈ C.support.toFinset
      · exact Finset.mem_union_right _ hwC
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hwL, hwC⟩)
    exact hp.2 w hw hwDeleted
  have hreservoirProtected (s : Fin (k ^ 2)) :
      Disjoint (reservoir s).verts protectedSet := by
    rw [Finset.disjoint_left]
    intro z hzE hzP
    by_cases hzL : z ∈ L
    · have hzBall := hreservoirLBall s hzE
      have hzAvoid := ballAvoidingFrom_avoids_forbidden G (L : Set V)
        ({center s} : Finset V) ell₀ (by simpa using hcenterL s)
      exact (hzAvoid z (by simpa [ballAvoidingFrom] using hzBall) hzL).elim
    · have hzGuard : z ∈ guard := Finset.mem_sdiff.2 ⟨hzP, hzL⟩
      have hzBig := ballAvoiding_radius_mono G (L : Set V) (center s)
        (Nat.le_mul_of_pos_left ell₀ (by omega : 0 < 5))
        (hreservoirLBall s hzE)
      exact (Finset.disjoint_left.1 (hpacking.2.2.2 _ (hcenterMem s))
        hzBig hzGuard).elim
  have hreservoirPair : ∀ s t, s ≠ t →
      Disjoint (reservoir s).verts (reservoir t).verts := by
    intro s t hst
    apply (hpacking.2.2.1 (hcenterMem s) (hcenterMem t)
      (fun h ↦ hst (center.injective h))).mono
    · intro z hz
      exact ballAvoiding_radius_mono G (L : Set V) (center s)
        (by have hell := num.ell₀_pos; omega)
        (hreservoirLBall s hz)
    · intro z hz
      exact ballAvoiding_radius_mono G (L : Set V) (center t)
        (by have hell := num.ell₀_pos; omega)
        (hreservoirLBall t hz)
  refine ⟨center, reservoir, hcenterL, hreservoirProtected, hreservoirPair,
    hreservoirLBall, ?_, ?_⟩
  · intro s t hst
    exact hpacking.2.2.1 (hcenterMem s) (hcenterMem t)
      (fun h ↦ hst (center.injective h))
  intro s
  apply (hpacking.2.2.2 _ (hcenterMem s)).mono_right
  intro z hzLow
  exact Finset.mem_sdiff.2 ⟨
    Finset.mem_union_right _ (Finset.mem_sdiff.1 hzLow).1,
    (Finset.mem_sdiff.1 hzLow).2⟩

/-- Before the first packed scale, a ball from a low prescribed root cannot
touch a reservoir lying in a far packed ball.  This is the zero-loss half of
the early/late reservoir accounting in Case II. -/
theorem externalNeighborhood_ball_disjoint_reservoir_of_far [Fintype V]
    (G : SimpleGraph V) (L U lowRoots reservoir : Finset V)
    (center x : V) (ell₀ r : ℕ)
    (hcenterL : center ∉ L) (hxLow : x ∈ lowRoots)
    (hUL : L ⊆ U) (hxU : x ∉ U) (hell : 0 < ell₀) (hr : r ≤ ell₀)
    (hreservoir : reservoir ⊆
      ballAvoiding G (L : Set V) center ell₀)
    (hfar : Disjoint
      (ballAvoiding G (L : Set V) center (5 * ell₀)) lowRoots) :
    Disjoint
      (externalNeighborhood G (ballAvoiding G (U : Set V) x r))
      reservoir := by
  classical
  rw [Finset.disjoint_left]
  intro z hzN hzReservoir
  obtain ⟨hzOutside, w, hwBall, hwz⟩ :=
    (mem_externalNeighborhood G (ballAvoiding G (U : Set V) x r) z).1 hzN
  obtain ⟨p, hp, hplen⟩ :=
    (mem_ballAvoiding G (L : Set V) center ell₀ z).1
      (hreservoir hzReservoir)
  obtain ⟨q, hq, hqlen⟩ :=
    (mem_ballAvoiding G (U : Set V) x r w).1 hwBall
  have hzL : z ∉ L := by
    have hav := ballAvoidingFrom_avoids_forbidden G (L : Set V)
      ({center} : Finset V) ell₀ (by simpa using hcenterL)
    exact hav z (by simpa [ballAvoidingFrom] using hreservoir hzReservoir)
  have hwU : w ∉ U := by
    have hav := ballAvoidingFrom_avoids_forbidden G (U : Set V)
      ({x} : Finset V) r (by simpa using hxU)
    exact hav w (by simpa [ballAvoidingFrom] using hwBall)
  have hwL : w ∉ L := fun hw ↦ hwU (hUL hw)
  let edge : G.Walk z w := Walk.cons hwz.symm Walk.nil
  let raw : G.Walk center x := (p.append edge).append q.reverse
  let path : G.Walk center x := raw.bypass
  have hpathAvoids : path.Avoids (L : Set V) ({center} : Set V) := by
    apply (show raw.Avoids (L : Set V) ({center} : Set V) from ?_).of_support_subset
      raw.support_bypass_subset_support
    intro a ha haL
    have haParts : (a ∈ p.support ∨ a ∈ edge.support) ∨
        a ∈ q.reverse.support := by
      simpa only [raw, Walk.mem_support_append_iff] using ha
    rcases haParts with (hap | hae) | haq
    · exact hp.2 a hap haL
    · have haEnds : a = z ∨ a = w := by simpa [edge] using hae
      rcases haEnds with rfl | rfl
      · exact (hzL haL).elim
      · exact (hwL haL).elim
    · have haq' : a ∈ q.support := by
        simpa [q.support_reverse] using haq
      have hax : a = x := by simpa using hq.2 a haq' (hUL haL)
      subst a
      have hxNotL : x ∉ L := by
        intro hxL
        exact hxU (hUL hxL)
      exact (hxNotL haL).elim
  have hxBig : x ∈ ballAvoiding G (L : Set V) center (5 * ell₀) := by
    rw [mem_ballAvoiding]
    refine ⟨path, ⟨raw.bypass_isPath, hpathAvoids⟩, ?_⟩
    calc
      path.length ≤ raw.length := raw.length_bypass_le_length
      _ = p.length + 1 + q.length := by simp [raw, edge]
      _ ≤ ell₀ + 1 + r := by omega
      _ ≤ 5 * ell₀ := by omega
  exact (Finset.disjoint_left.1 hfar hxBig hxLow).elim

/-- Avoiding balls are monotone in their finite seed set. -/
theorem ballAvoidingFrom_seed_mono [Fintype V]
    (G : SimpleGraph V) (X : Set V) {A B : Finset V} (hAB : A ⊆ B)
    (r : ℕ) :
    ballAvoidingFrom G X A r ⊆ ballAvoidingFrom G X B r := by
  intro y hy
  obtain ⟨a, ha, p, hp, hplen⟩ :=
    (mem_ballAvoidingFrom G X A r y).1 hy
  exact (mem_ballAvoidingFrom G X B r y).2
    ⟨a, hAB ha, p, hp, hplen⟩

/-- A ball grown from one packed reservoir has no boundary contact with a
different reservoir before the packing scale. -/
theorem externalNeighborhood_ballFrom_reservoir_disjoint_of_far [Fintype V]
    (G : SimpleGraph V) (L W reservoirS reservoirT : Finset V)
    (centerS centerT : V) (ell₀ r : ℕ)
    (hcenterSL : centerS ∉ L) (hcenterTL : centerT ∉ L)
    (hLW : L ⊆ W) (hell : 0 < ell₀) (hr : r < ell₀)
    (hreservoirS : reservoirS ⊆
      ballAvoiding G (L : Set V) centerS ell₀)
    (hreservoirT : reservoirT ⊆
      ballAvoiding G (L : Set V) centerT ell₀)
    (hfar : Disjoint
      (ballAvoiding G (L : Set V) centerS (5 * ell₀))
      (ballAvoiding G (L : Set V) centerT (5 * ell₀))) :
    Disjoint
      (externalNeighborhood G
        (ballAvoidingFrom G (W : Set V) reservoirS r))
      reservoirT := by
  classical
  rw [Finset.disjoint_left]
  intro z hzN hzT
  have hzTL : z ∉ L := by
    have hav := ballAvoidingFrom_avoids_forbidden G (L : Set V)
      ({centerT} : Finset V) ell₀ (by simpa using hcenterTL)
    exact hav z (by simpa [ballAvoidingFrom] using hreservoirT hzT)
  have hsmallLarge : ballAvoidingFrom G (W : Set V) reservoirS r ⊆
      ballAvoidingFrom G (L : Set V) reservoirS r :=
    ballAvoidingFrom_forbidden_anti G hLW reservoirS r
  have hzStep : z ∈ ballAvoidingFrom G (L : Set V) reservoirS (r + 1) := by
    have hzParts := externalNeighborhood_subset_union_of_subset G hsmallLarge hzN
    rcases Finset.mem_union.1 hzParts with hzBall | hzBoundary
    · exact ballAvoidingFrom_radius_mono G (L : Set V) reservoirS
        (Nat.le_succ r) hzBall
    · apply availableExternalNeighborhood_subset_ballAvoidingFrom_succ
      exact (mem_availableExternalNeighborhood G (L : Set V) _ z).2
        ⟨hzBoundary, hzTL⟩
  have hseed : reservoirS ⊆
      ballAvoidingFrom G (L : Set V) ({centerS} : Finset V) ell₀ := by
    simpa [ballAvoidingFrom] using hreservoirS
  have hzSeeded : z ∈ ballAvoidingFrom G (L : Set V)
      (ballAvoidingFrom G (L : Set V) ({centerS} : Finset V) ell₀)
      (r + 1) :=
    ballAvoidingFrom_seed_mono G (L : Set V) hseed (r + 1) hzStep
  have hzSRadius : z ∈ ballAvoidingFrom G (L : Set V)
      ({centerS} : Finset V) (ell₀ + (r + 1)) :=
    ballAvoidingFrom_ballAvoidingFrom_subset G (L : Set V)
      ({centerS} : Finset V) ell₀ (r + 1) (by simpa using hcenterSL) hzSeeded
  have hzSBig : z ∈ ballAvoiding G (L : Set V) centerS (5 * ell₀) := by
    have hz := ballAvoidingFrom_radius_mono G (L : Set V)
      ({centerS} : Finset V)
      (show ell₀ + (r + 1) ≤ 5 * ell₀ by omega) hzSRadius
    simpa [ballAvoidingFrom] using hz
  have hzTBig : z ∈ ballAvoiding G (L : Set V) centerT (5 * ell₀) :=
    ballAvoiding_radius_mono G (L : Set V) centerT
      (show ell₀ ≤ 5 * ell₀ by omega) (hreservoirT hzT)
  exact (Finset.disjoint_left.1 hfar hzSBig hzTBig).elim

/-- The total carrier of `n` order-`Delta` reservoirs has size at most
`n * Delta`. -/
theorem card_reservoirUnion_le {n Delta radius : ℕ}
    {center : Fin n → V}
    (reservoir : ∀ s : Fin n, VertexExpansion G (center s) Delta radius) :
    (reservoirUnion reservoir).card ≤ n * Delta := by
  classical
  calc
    (reservoirUnion reservoir).card ≤
        ∑ s : Fin n, (reservoir s).verts.card := by
      simpa [reservoirUnion] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin n)))
          (t := fun s ↦ (reservoir s).verts))
    _ = n * Delta := by simp [VertexExpansion.card_verts]

/-- Disjointness from each reservoir is equivalent to disjointness from
their finite union. -/
theorem disjoint_reservoirUnion_of_forall {n Delta radius : ℕ}
    {center : Fin n → V}
    (reservoir : ∀ s : Fin n, VertexExpansion G (center s) Delta radius)
    (S : Finset V) (hS : ∀ s, Disjoint S (reservoir s).verts) :
    Disjoint S (reservoirUnion reservoir) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzS hzUnion
  obtain ⟨s, -, hzs⟩ := Finset.mem_biUnion.1 hzUnion
  exact (Finset.disjoint_left.1 (hS s) hzS hzs).elim

/-- The labelled maximal routing argument in the low-degree branch.  Every
low prescribed root receives `k` internally disjoint routes to distinct
packed reservoirs. -/
theorem exists_sourceLowFullPathFamily [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (k d D Delta ell₀ m protectedCard : ℕ)
    (reservedSet roots L lowRoots protectedSet fixed : Finset V)
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (center : Fin (k ^ 2) ↪ V)
    (reservoir : ∀ s : Fin (k ^ 2),
      VertexExpansion G (center s) Delta ell₀)
    (hcenterL : ∀ s, center s ∉ L)
    (hreservoirProtected : ∀ s,
      Disjoint (reservoir s).verts protectedSet)
    (hreservoirPair : ∀ s t, s ≠ t →
      Disjoint (reservoir s).verts (reservoir t).verts)
    (hreservoirLBall : ∀ s, (reservoir s).verts ⊆
      ballAvoiding G (L : Set V) (center s) ell₀)
    (hfarPair : ∀ s t, s ≠ t → Disjoint
      (ballAvoiding G (L : Set V) (center s) (5 * ell₀))
      (ballAvoiding G (L : Set V) (center t) (5 * ell₀)))
    (hfarRoots : ∀ s, Disjoint
      (ballAvoiding G (L : Set V) (center s) (5 * ell₀)) lowRoots)
    (hrootsCard : roots.card = k)
    (hlowRoots : lowRoots = roots \ L)
    (hprotected : reservedSet.card ≤ protectedCard)
    (hprotectedDef : protectedSet =
      (reservedSet ∪ C.support.toFinset) ∪ roots)
    (hfixedCard : fixed.card ≤ 2 * k ^ 2 + 2 * protectedCard + 2 * k)
    (hLcover : L ⊆ fixed ∪ C.support.toFinset)
    (hrootsFixed : roots ⊆ fixed)
    (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (hdDelta : d - 1 ≤ Delta)
    (num : LM311Numerics epsilon kappa (Fintype.card V)
      k d D Delta ell₀ m protectedCard) :
    let targets := reservoirUnion reservoir
    let default : Fin (k ^ 2) := ⟨0, pow_pos num.k_pos 2⟩
    let label := reservoirLabel default reservoir
    let barrier := (fixed ∪ C.support.toFinset) ∪ targets
    ∃ family : Finset
        (BoundedRootTargetPath G lowRoots targets (3 * m + 1)),
      IsAdmissiblePathFamily lowRoots targets barrier label
        (3 * m + 1) k family ∧
      (∀ other : Finset
          (BoundedRootTargetPath G lowRoots targets (3 * m + 1)),
        IsAdmissiblePathFamily lowRoots targets barrier label
          (3 * m + 1) k other → other.card ≤ family.card) ∧
      (∀ other : Finset
          (BoundedRootTargetPath G lowRoots targets (3 * m + 1)),
        IsAdmissiblePathFamily lowRoots targets barrier label
          (3 * m + 1) k other → other.card = family.card →
        pathFamilyTotalLength family ≤ pathFamilyTotalLength other) ∧
      ∀ x ∈ lowRoots,
        (family.filter fun p ↦ p.root = x).card = k := by
  classical
  dsimp only
  let targets := reservoirUnion reservoir
  let default : Fin (k ^ 2) := ⟨0, pow_pos num.k_pos 2⟩
  let label := reservoirLabel default reservoir
  let barrier := (fixed ∪ C.support.toFinset) ∪ targets
  have htargetProtected : Disjoint targets protectedSet := by
    exact (disjoint_reservoirUnion_of_forall reservoir protectedSet
      (fun s ↦ (hreservoirProtected s).symm)).symm
  have hrootTarget : Disjoint lowRoots targets := by
    rw [Finset.disjoint_left]
    intro z hzRoot hzTarget
    have hzRoots : z ∈ roots := by
      rw [hlowRoots] at hzRoot
      exact (Finset.mem_sdiff.1 hzRoot).1
    have hzProtected : z ∈ protectedSet := by
      rw [hprotectedDef]
      exact Finset.mem_union_right _ hzRoots
    exact (Finset.disjoint_left.1 htargetProtected hzTarget hzProtected).elim
  have hrootsBarrier : lowRoots ⊆ barrier := by
    intro z hz
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply hrootsFixed
    rw [hlowRoots] at hz
    exact (Finset.mem_sdiff.1 hz).1
  have htargetsBarrier : targets ⊆ barrier := Finset.subset_union_right
  obtain ⟨family, hfamily, hmaximum, hminimum⟩ :=
    exists_cardMax_lengthMin_pathFamily G lowRoots targets barrier label
      (3 * m + 1) k
  have hlowRootsCard : lowRoots.card ≤ k := by
    rw [hlowRoots]
    exact (Finset.card_le_card Finset.sdiff_subset).trans hrootsCard.le
  have hfamilyCard : family.card ≤ k ^ 2 := by
    have h := BoundedRootTargetPath.IsAdmissiblePathFamily.card_le_roots_mul
      family hfamily
    calc
      family.card ≤ lowRoots.card * k := h
      _ ≤ k * k := Nat.mul_le_mul_right k hlowRootsCard
      _ = k ^ 2 := by simp [pow_two]
  have htargetCard : targets.card ≤ k ^ 2 * Delta := by
    exact card_reservoirUnion_le reservoir
  have hcover (x : V) :
      BoundedRootTargetPath.switchingBarrier barrier family x ⊆
        fixed ∪ C.support.toFinset ∪
          BoundedRootTargetPath.familySupport family ∪ targets := by
    intro z hz
    have hz' := (Finset.mem_sdiff.1 hz).1
    simpa [barrier, Finset.union_assoc, Finset.union_left_comm,
      Finset.union_comm] using hz'
  refine ⟨family, hfamily, hmaximum, hminimum, ?_⟩
  intro x hxLow
  apply BoundedRootTargetPath.filter_card_eq_multiplicity_of_augment
    family hfamily hmaximum hxLow
  intro hdeficient
  have hshortRoots :=
    BoundedRootTargetPath.IsAdmissiblePathFamily.card_lt_roots_mul_of_fiber_lt
      family hfamily hxLow hdeficient
  have hshort : family.card < Fintype.card (Fin (k ^ 2)) := by
    rw [Fintype.card_fin]
    exact hshortRoots.trans_le <|
      calc
        lowRoots.card * k ≤ k * k := Nat.mul_le_mul_right k hlowRootsCard
        _ = k ^ 2 := by simp [pow_two]
  obtain ⟨unused, hunused⟩ :=
    BoundedRootTargetPath.IsAdmissiblePathFamily.exists_unused_label
      family hfamily hshort
  let B : Finset V := (reservoir unused).verts
  let U : Finset V :=
    BoundedRootTargetPath.switchingBarrier barrier family x
  have hxNotL : x ∉ L := by
    rw [hlowRoots] at hxLow
    exact (Finset.mem_sdiff.1 hxLow).2
  have hxU : x ∉ U := by
    simp [U, BoundedRootTargetPath.switchingBarrier]
  have hLU : L ⊆ U := by
    intro z hzL
    apply Finset.mem_sdiff.2
    refine ⟨?_, ?_⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact hLcover hzL
    · intro hzx
      have hzx' : z = x := by simpa using hzx
      subst z
      exact hxNotL hzL
  have hblockedRoot (r : ℕ) :
      (blockedExternalNeighborhood G (U : Set V)
        (ballAvoiding G (U : Set V) x r)).card ≤
        (2 * k ^ 2 + 2 * protectedCard + 2 * k) +
          (2 * (r + 1) + 1) + k ^ 2 * (r + 2) +
          (if r ≤ ell₀ then 0 else k ^ 2 * Delta) := by
    let extraLoss := if r ≤ ell₀ then 0 else k ^ 2 * Delta
    have hextra :
        (externalNeighborhood G (ballAvoiding G (U : Set V) x r) ∩
          targets).card ≤ extraLoss := by
      by_cases hr : r ≤ ell₀
      · have hdisjoint : Disjoint
            (externalNeighborhood G (ballAvoiding G (U : Set V) x r))
            targets := by
          apply disjoint_reservoirUnion_of_forall reservoir
          intro s
          exact externalNeighborhood_ball_disjoint_reservoir_of_far
            G L U lowRoots (reservoir s).verts (center s) x ell₀ r
              (hcenterL s) hxLow hLU hxU num.ell₀_pos hr
              (hreservoirLBall s) (hfarRoots s)
        have hinter : externalNeighborhood G
            (ballAvoiding G (U : Set V) x r) ∩ targets = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.1 hdisjoint
        simp [extraLoss, hr, hinter]
      · have hinter :
            (externalNeighborhood G (ballAvoiding G (U : Set V) x r) ∩
              targets).card ≤ targets.card :=
          Finset.card_le_card Finset.inter_subset_right
        exact hinter.trans (by simpa [extraLoss, hr] using htargetCard)
    have h :=
      BoundedRootTargetPath.card_blocked_switchingBarrier_with_extra_le
        hC fixed targets family (hcover x) hrootsBarrier htargetsBarrier
          hrootTarget hfamily hminimum hxLow hdeficient r extraLoss hextra
    have hfixedWeak : fixed.card ≤
        2 * k ^ 2 + 2 * protectedCard + 2 * k := by omega
    exact h.trans <| by
      dsimp [extraLoss]
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add hfixedWeak le_rfl)
          (Nat.mul_le_mul_right (r + 2) hfamilyCard)) le_rfl
  let A := ballAvoiding G (U : Set V) x 1
  have hAstart : lm311LowRootSeed d k protectedCard ≤ A.card := by
    have hzero := hblockedRoot 0
    have hcontact :
        (blockedExternalNeighborhood G (U : Set V) ({x} : Finset V)).card ≤
          4 * k ^ 2 + 2 * protectedCard + 2 * k + 3 := by
      have hzero' :
          (blockedExternalNeighborhood G (U : Set V)
            ({x} : Finset V)).card ≤
            (2 * k ^ 2 + 2 * protectedCard + 2 * k) + (2 * 1 + 1) +
              k ^ 2 * 2 := by
        simpa only [ballAvoiding_zero, if_pos (Nat.zero_le ell₀),
          zero_add, Nat.mul_zero, Nat.add_zero] using hzero
      omega
    have h := card_ballAvoiding_one_lower_of_blocked G U x d
      (4 * k ^ 2 + 2 * protectedCard + 2 * k + 3)
      hxU (hmin x) hcontact
    simpa [A, lm311LowRootSeed, Nat.add_assoc] using h
  let growthRoot : ℕ → ℕ := num.lowRootGrowth
  let lossRoot : ℕ → ℕ := fun r ↦
    (4 * k ^ 2 + 2 * protectedCard + 2 * k) +
      (2 * (r + 2) + 1) + k ^ 2 * (r + 3) +
      (if r < ell₀ then 0 else k ^ 2 * Delta)
  have hrootGrowth := min_growth_le_card_ballAvoidingFrom_of_lmExpander
    G epsilon kappa hexp (U : Set V) A num.connectRounds
      growthRoot num.lowRootGain lossRoot
      (by simpa [growthRoot] using num.low_root_start.trans hAstart)
      (by intro r hr; simpa [growthRoot] using num.low_root_next r hr)
      (by
        intro r hr
        have hsub : ballAvoidingFrom G (U : Set V) A r ⊆
            ballAvoiding G (U : Set V) x (r + 1) := by
          simpa [A] using ballAvoidingFrom_ballAvoiding_one_subset G U x r
        have hav : ∀ z ∈ ballAvoiding G (U : Set V) x (r + 1),
            z ∉ (U : Set V) := by
          intro z hz
          have hzReach :=
            (mem_ballAvoiding G (U : Set V) x (r + 1) z).1 hz
          rcases hzReach.eq_root_or_not_mem with hzx | hzU
          · simpa [hzx] using hxU
          · exact hzU
        have hb := blockedExternalNeighborhood_subset_of_subset_of_avoids
          G (U : Set V) hsub hav
        have hbound :
            (blockedExternalNeighborhood G (U : Set V)
              (ballAvoiding G (U : Set V) x (r + 1))).card ≤
                lossRoot r := by
          have hblocked := hblockedRoot (r + 1)
          have hbase :
              2 * k ^ 2 + 2 * protectedCard + 2 * k ≤
                4 * k ^ 2 + 2 * protectedCard + 2 * k := by
            omega
          by_cases hir : r < ell₀
          · have hs : r + 1 ≤ ell₀ := by omega
            refine hblocked.trans ?_
            simp only [lossRoot, if_pos hir, if_pos hs]
            rw [show r + 1 + 1 = r + 2 by omega,
              show r + 1 + 2 = r + 3 by omega]
            exact Nat.add_le_add
              (Nat.add_le_add (Nat.add_le_add hbase le_rfl) le_rfl) le_rfl
          · have hs : ¬ r + 1 ≤ ell₀ := by omega
            refine hblocked.trans ?_
            simp only [lossRoot, if_neg hir, if_neg hs]
            rw [show r + 1 + 1 = r + 2 by omega,
              show r + 1 + 2 = r + 3 by omega]
            exact Nat.add_le_add
              (Nat.add_le_add (Nat.add_le_add hbase le_rfl) le_rfl) le_rfl
        exact (Finset.card_le_card hb).trans hbound)
      (by
        intro r hr
        simpa [growthRoot] using num.low_root_lower r hr)
      (by
        intro r hr s hgs hs
        simpa [growthRoot, lossRoot, Nat.add_assoc] using
          num.low_root_rate r hr s hgs hs)
  have hrootHalf : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (U : Set V) A num.connectRounds).card := by
    have hreaches : Fintype.card V / 2 + 1 ≤
        growthRoot num.connectRounds := by
      simpa [growthRoot] using num.low_root_half
    simpa [min_eq_right hreaches] using hrootGrowth
  let W : Finset V := U \ B
  have hLW : L ⊆ W := by
    intro z hzL
    apply Finset.mem_sdiff.2
    refine ⟨hLU hzL, ?_⟩
    intro hzB
    have hzBall := hreservoirLBall unused hzB
    have hav := ballAvoidingFrom_avoids_forbidden G (L : Set V)
      ({center unused} : Finset V) ell₀ (by simpa using hcenterL unused)
    exact hav z (by simpa [ballAvoidingFrom] using hzBall) hzL
  have hBavoid : ∀ b ∈ B, b ∉ (W : Set V) := by
    intro b hb hbw
    exact (Finset.mem_sdiff.1 hbw).2 hb
  have hbaseCard :
      (fixed ∪ C.support.toFinset ∪
        BoundedRootTargetPath.familySupport family).card ≤
        2 * protectedCard + 2 * k ^ 2 + 2 * k +
          lm311GirthBudget (Fintype.card V) + k ^ 2 * (3 * m + 1) := by
    have hdegreeThree : ∀ v : V, 3 ≤ G.degree v := by
      intro v
      have hv := hmin v
      have hd := num.four_le_d
      omega
    have hCcard : C.support.toFinset.card ≤
        lm311GirthBudget (Fintype.card V) := by
      rw [cycle_support_toFinset_card_eq_length C hC.1]
      simpa [lm311GirthBudget] using
        hC.length_le_two_mul_log_add_two G hdegreeThree
    have hsupp := BoundedRootTargetPath.card_familySupport_le family
    have hsupp' : (BoundedRootTargetPath.familySupport family).card ≤
        k ^ 2 * (3 * m + 1) :=
      hsupp.trans (Nat.mul_le_mul_right (3 * m + 1) hfamilyCard)
    have hu1 := Finset.card_union_le fixed C.support.toFinset
    have hu2 := Finset.card_union_le (fixed ∪ C.support.toFinset)
      (BoundedRootTargetPath.familySupport family)
    calc
      (fixed ∪ C.support.toFinset ∪
          BoundedRootTargetPath.familySupport family).card ≤
          (fixed ∪ C.support.toFinset).card +
            (BoundedRootTargetPath.familySupport family).card := hu2
      _ ≤ (fixed.card + C.support.toFinset.card) +
            (BoundedRootTargetPath.familySupport family).card :=
        Nat.add_le_add_right hu1 _
      _ ≤ 2 * protectedCard + 2 * k ^ 2 + 2 * k +
          lm311GirthBudget (Fintype.card V) + k ^ 2 * (3 * m + 1) := by
        omega
  let base : Finset V := fixed ∪ C.support.toFinset ∪
    BoundedRootTargetPath.familySupport family
  let otherTargets : Finset V := targets \ B
  have hWcover : W ⊆ base ∪ otherTargets := by
    intro z hzW
    have hzU := (Finset.mem_sdiff.1 hzW).1
    have hzCover := hcover x hzU
    rcases Finset.mem_union.1 hzCover with hzBase | hzTarget
    · exact Finset.mem_union_left _ (by
        simpa [base, Finset.union_assoc] using hzBase)
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.2 ⟨hzTarget, (Finset.mem_sdiff.1 hzW).2⟩)
  have hblockedReservoir (r : ℕ) :
      (blockedExternalNeighborhood G (W : Set V)
        (ballAvoidingFrom G (W : Set V) B r)).card ≤
        (2 * protectedCard + 2 * k ^ 2 + 2 * k +
          lm311GirthBudget (Fintype.card V) + k ^ 2 * (3 * m + 1)) +
          (if r < ell₀ then 0 else k ^ 2 * Delta) := by
    let extraLoss := if r < ell₀ then 0 else k ^ 2 * Delta
    have hextra :
        (externalNeighborhood G (ballAvoidingFrom G (W : Set V) B r) ∩
          otherTargets).card ≤ extraLoss := by
      by_cases hr : r < ell₀
      · have hdisjoint : Disjoint
            (externalNeighborhood G (ballAvoidingFrom G (W : Set V) B r))
            otherTargets := by
          rw [Finset.disjoint_left]
          intro z hzN hzOther
          have hzTargets := (Finset.mem_sdiff.1 hzOther).1
          obtain ⟨t, -, hzt⟩ := Finset.mem_biUnion.1 hzTargets
          by_cases htu : t = unused
          · subst t
            exact (Finset.mem_sdiff.1 hzOther).2 hzt
          · exact Finset.disjoint_left.1
              (externalNeighborhood_ballFrom_reservoir_disjoint_of_far
                G L W B (reservoir t).verts (center unused) (center t)
                  ell₀ r (hcenterL unused) (hcenterL t) hLW
                  num.ell₀_pos hr (hreservoirLBall unused)
                  (hreservoirLBall t)
                  (hfarPair unused t (fun h ↦ htu h.symm))) hzN hzt
        have hinter : externalNeighborhood G
            (ballAvoidingFrom G (W : Set V) B r) ∩ otherTargets = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.1 hdisjoint
        simp [extraLoss, hr, hinter]
      · have hc :
            (externalNeighborhood G (ballAvoidingFrom G (W : Set V) B r) ∩
              otherTargets).card ≤ otherTargets.card :=
          Finset.card_le_card Finset.inter_subset_right
        have hot : otherTargets.card ≤ k ^ 2 * Delta :=
          (Finset.card_le_card Finset.sdiff_subset).trans htargetCard
        exact hc.trans (by simpa [extraLoss, hr] using hot)
    have hsub : blockedExternalNeighborhood G (W : Set V)
        (ballAvoidingFrom G (W : Set V) B r) ⊆
        base ∪ (externalNeighborhood G
          (ballAvoidingFrom G (W : Set V) B r) ∩ otherTargets) := by
      intro z hz
      obtain ⟨hzN, hzW⟩ :=
        (mem_blockedExternalNeighborhood G (W : Set V) _ z).1 hz
      have hzCover := hWcover hzW
      rcases Finset.mem_union.1 hzCover with hzBase | hzOther
      · exact Finset.mem_union_left _ hzBase
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hzN, hzOther⟩)
    have hc := Finset.card_le_card hsub
    have hu := Finset.card_union_le base
      (externalNeighborhood G (ballAvoidingFrom G (W : Set V) B r) ∩
        otherTargets)
    calc
      (blockedExternalNeighborhood G (W : Set V)
          (ballAvoidingFrom G (W : Set V) B r)).card ≤
          (base ∪ (externalNeighborhood G
            (ballAvoidingFrom G (W : Set V) B r) ∩ otherTargets)).card := hc
      _ ≤ base.card + (externalNeighborhood G
            (ballAvoidingFrom G (W : Set V) B r) ∩ otherTargets).card := hu
      _ ≤ (2 * protectedCard + 2 * k ^ 2 + 2 * k +
          lm311GirthBudget (Fintype.card V) + k ^ 2 * (3 * m + 1)) +
          extraLoss := Nat.add_le_add (by simpa [base] using hbaseCard) hextra
      _ = _ := rfl
  let growthReservoir : ℕ → ℕ := num.lowReservoirGrowth
  let lossReservoir : ℕ → ℕ := fun r ↦
    (2 * protectedCard + 2 * k ^ 2 + 2 * k +
      lm311GirthBudget (Fintype.card V) + k ^ 2 * (3 * m + 1)) +
      (if r < ell₀ then 0 else k ^ 2 * Delta)
  have hreservoirGrowth :=
    min_growth_le_card_ballAvoidingFrom_of_lmExpander
      G epsilon kappa hexp (W : Set V) B num.connectRounds
        growthReservoir num.lowReservoirGain lossReservoir
        (by
          have hseed : num.lowReservoirGrowth 0 ≤ B.card :=
            num.low_reservoir_start.trans (by
              simpa [B] using (reservoir unused).card_verts.ge)
          simpa [growthReservoir] using hseed)
        (by intro r hr; simpa [growthReservoir] using
          num.low_reservoir_next hdDelta r hr)
        (by intro r hr; simpa [lossReservoir] using hblockedReservoir r)
        (by
          intro r hr
          simpa [growthReservoir] using
            num.low_reservoir_lower hdDelta r hr)
        (by
          intro r hr s hgs hs
          simpa [growthReservoir, lossReservoir, Nat.add_assoc] using
            num.low_reservoir_rate hdDelta r hr s hgs hs)
  have hreservoirHalf : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) B num.connectRounds).card := by
    have hreaches : Fintype.card V / 2 + 1 ≤
        growthReservoir num.connectRounds := by
      simpa [growthReservoir] using num.low_reservoir_half hdDelta
    simpa [min_eq_right hreaches] using hreservoirGrowth
  have hrootHalfW : Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) A num.connectRounds).card := by
    apply hrootHalf.trans
    apply Finset.card_le_card
    exact ballAvoidingFrom_forbidden_anti G Finset.sdiff_subset A
      num.connectRounds
  have hAavoid : ∀ a ∈ A, a ∉ (W : Set V) := by
    intro a ha haW
    have haU : a ∉ (U : Set V) := by
      have hav := ballAvoidingFrom_avoids_forbidden G (U : Set V)
        ({x} : Finset V) 1 (by simpa using hxU)
      exact hav a (by simpa [A, ballAvoidingFrom] using ha)
    exact haU (Finset.sdiff_subset haW)
  have hlarge : Fintype.card V <
      (ballAvoidingFrom G (W : Set V) A num.connectRounds).card +
        (ballAvoidingFrom G (W : Set V) B num.connectRounds).card := by
    omega
  obtain ⟨y, hyB, q, hqPath, hqLength, hqAvoid⟩ :=
    exists_short_root_set_path_of_large_balls (x := x)
      G W A B num.connectRounds
      (by
        intro z hz
        exact ballAvoiding_forbidden_anti G Finset.sdiff_subset x 1
          (by simpa [A] using hz))
      hAavoid hBavoid hlarge
  have hyTargets : y ∈ targets := reservoir_mem_union reservoir unused hyB
  obtain ⟨z, hzTargets, q', hq'Path, hq'Length, hq'Support,
      hq'First⟩ := exists_first_entry_prefix q hqPath targets hyTargets
  have htargetsU : targets ⊆ U := by
    intro a ha
    apply Finset.mem_sdiff.2
    refine ⟨Finset.mem_union_left _ (Finset.mem_union_right _ ha), ?_⟩
    intro hax
    have hax' : a = x := by simpa using hax
    subst a
    exact Finset.disjoint_left.1 hrootTarget hxLow ha
  have hzB : z ∈ B := by
    have hzQ : z ∈ q.support := hq'Support (by simp)
    have hzU := htargetsU hzTargets
    by_cases hzW : z ∈ W
    · have hzEnds := hqAvoid.2 z hzQ hzW
      rcases (by simpa using hzEnds : z = x ∨ z = y) with hzx | hzy
      · subst z
        exact (Finset.disjoint_left.1 hrootTarget hxLow hzTargets).elim
      · simpa [hzy] using hyB
    · by_contra hzNotB
      exact hzW (Finset.mem_sdiff.2 ⟨hzU, hzNotB⟩)
  have hq'AvoidU : q'.IsAvoidingPath (U : Set V) ({x, z} : Set V) := by
    refine ⟨hq'Path, ?_⟩
    intro a haQ haU
    have haInQ : a ∈ q.support := hq'Support haQ
    by_cases haW : a ∈ W
    · have haEnds := hqAvoid.2 a haInQ haW
      rcases (by simpa using haEnds : a = x ∨ a = y) with hax | hay
      · simp [hax]
      · have hayTarget : a ∈ targets := by simpa [hay] using hyTargets
        have haz := hq'First a haQ hayTarget
        simp [haz]
    · have haB : a ∈ B := by
        by_contra haNotB
        exact haW (Finset.mem_sdiff.2 ⟨haU, haNotB⟩)
      have haTarget : a ∈ targets := reservoir_mem_union reservoir unused haB
      have haz := hq'First a haQ haTarget
      simp [haz]
  have hzLabel : label z = unused := by
    dsimp [label]
    exact reservoirLabel_eq_of_mem default reservoir hreservoirPair unused hzB
  have hzUnused : ∀ old ∈ family, label old.target ≠ label z := by
    intro old hold heq
    exact hunused old hold (heq.trans hzLabel)
  obtain ⟨new, hnewNot, hnewRoot, hnewFamily⟩ :=
    BoundedRootTargetPath.exists_admissible_insert_of_switching_path
      hrootsBarrier htargetsBarrier hrootTarget family hfamily hxLow hzTargets
        hdeficient hzUnused q' hq'Path
        (lt_of_le_of_lt hq'Length (by
          have hc := num.low_connector
          omega))
        (hq'AvoidU.mono_forbidden (by
          intro a ha
          exact (Finset.mem_sdiff.1 ha).1))
  exact ⟨new, hnewNot, hnewRoot, hnewFamily⟩

/-- High-degree branch of Liu--Montgomery Lemma 3.11. -/
theorem liuMontgomery_lemma3_11_caseHigh [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (k d D Delta ell₀ m protectedCard : ℕ)
    (reservedSet : Finset V) (hprotected : reservedSet.card ≤ protectedCard)
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (root : Fin k ↪ V) (order : Fin k → Fin k → ℕ)
    (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (horderPos : ∀ i j, 0 < order i j)
    (horderLe : ∀ i j, order i j ≤ D)
    (num : LM311Numerics epsilon kappa (Fintype.card V)
      k d D Delta ell₀ m protectedCard)
    (hhigh : 2 * k ^ 2 ≤
      (lm311HighCandidates G Delta reservedSet C.support.toFinset
        (Finset.univ.image root)).card) :
    Nonempty (LM311ExpansionFamily G root order (5 * m)
      ((reservedSet ∪ C.support.toFinset) ∪ Finset.univ.image root)) := by
  classical
  let roots : Finset V := Finset.univ.image root
  have hrootsCard : roots.card = k := by
    simpa [roots] using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin k))
        root.injective)
  have hdegreeThree : ∀ v : V, 3 ≤ G.degree v := by
    intro v
    have hv := hmin v
    have hd := num.four_le_d
    omega
  have hCcard : C.support.toFinset.card ≤
      lm311GirthBudget (Fintype.card V) := by
    rw [cycle_support_toFinset_card_eq_length C hC.1]
    simpa [lm311GirthBudget] using
      hC.length_le_two_mul_log_add_two G hdegreeThree
  obtain ⟨hubs, hhubsSub, hhubsCard⟩ :=
    Finset.exists_subset_card_eq hhigh
  have hhubsNonempty : hubs.Nonempty := by
    apply Finset.card_pos.mp
    rw [hhubsCard]
    have hk2 : 0 < k ^ 2 := pow_pos num.k_pos 2
    omega
  let defaultHub : {v : V // v ∈ hubs} :=
    ⟨Classical.choose hhubsNonempty, Classical.choose_spec hhubsNonempty⟩
  let label : V → {v : V // v ∈ hubs} :=
    BoundedRootTargetPath.targetLabel defaultHub
  let fixed : Finset V := reservedSet ∪ roots ∪ hubs
  let barrier : Finset V := fixed ∪ C.support.toFinset
  have hhubsRoots : Disjoint hubs roots := by
    rw [Finset.disjoint_left]
    intro z hzH hzR
    have hzCand := hhubsSub hzH
    exact (Finset.mem_sdiff.1 hzCand).2 (by
      apply Finset.mem_union_right
      exact hzR)
  have hrootTarget : Disjoint roots hubs := hhubsRoots.symm
  have hrootsBarrier : roots ⊆ barrier := by
    intro z hz
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hz))
  have hhubsBarrier : hubs ⊆ barrier := by
    intro z hz
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  have hfixedCard : fixed.card ≤ lm311HighFixedBudget k protectedCard := by
    have h₁ := Finset.card_union_le reservedSet roots
    have h₂ := Finset.card_union_le (reservedSet ∪ roots) hubs
    calc
      fixed.card ≤ (reservedSet ∪ roots).card + hubs.card := by
        simpa [fixed] using h₂
      _ ≤ (reservedSet.card + roots.card) + hubs.card :=
        Nat.add_le_add_right h₁ hubs.card
      _ ≤ lm311HighFixedBudget k protectedCard := by
        dsimp [lm311HighFixedBudget]
        rw [hrootsCard, hhubsCard]
        omega
  obtain ⟨family, hfamily, hmaximum, hminimum⟩ :=
    exists_cardMax_lengthMin_pathFamily G roots hubs barrier label
      (3 * m + 1) k
  have hfamilyCard : family.card ≤ k ^ 2 := by
    have h := BoundedRootTargetPath.IsAdmissiblePathFamily.card_le_roots_mul
      family hfamily
    rw [hrootsCard] at h
    simpa [pow_two] using h
  have hcover (x : V) :
      BoundedRootTargetPath.switchingBarrier barrier family x ⊆
        fixed ∪ C.support.toFinset ∪
          BoundedRootTargetPath.familySupport family := by
    intro z hz
    have hz' := (Finset.mem_sdiff.1 hz).1
    simpa [barrier, Finset.union_assoc] using hz'
  have hfull : ∀ i : Fin k,
      (family.filter fun p ↦ p.root = root i).card = k := by
    intro i
    apply BoundedRootTargetPath.filter_card_eq_multiplicity_of_augment
      family hfamily hmaximum (by simpa [roots])
    intro hdeficient
    have hlabelsCard : Fintype.card {v : V // v ∈ hubs} = 2 * k ^ 2 := by
      simpa [hhubsCard]
    have hshort : family.card < Fintype.card {v : V // v ∈ hubs} := by
      rw [hlabelsCard]
      have hk2 : 0 < k ^ 2 := pow_pos num.k_pos 2
      omega
    obtain ⟨unused, hunused⟩ :=
      BoundedRootTargetPath.IsAdmissiblePathFamily.exists_unused_label
        family hfamily hshort
    let x : V := root i
    let y : V := unused.1
    let U : Finset V :=
      BoundedRootTargetPath.switchingBarrier barrier family x
    have hxRoots : x ∈ roots := by simp [x, roots]
    have hyHubs : y ∈ hubs := unused.2
    have hxU : x ∉ U := by simp [U, BoundedRootTargetPath.switchingBarrier]
    have hblockedRoot (r : ℕ) :
        (blockedExternalNeighborhood G (U : Set V)
          (ballAvoiding G (U : Set V) x r)).card ≤
          lm311HighFixedBudget k protectedCard +
            (2 * (r + 1) + 1) + k ^ 2 * (r + 2) := by
      have h := BoundedRootTargetPath.card_blocked_switchingBarrier_le
        hC fixed family (hcover x) hrootsBarrier hhubsBarrier hrootTarget
          hfamily hminimum hxRoots (by simpa [x] using hdeficient) r
      exact h.trans <| Nat.add_le_add
        (Nat.add_le_add hfixedCard le_rfl)
        (Nat.mul_le_mul_right (r + 2) hfamilyCard)
    let A := ballAvoiding G (U : Set V) x 1
    have hAstart : lm311HighRootSeed d k protectedCard ≤ A.card := by
      have h := card_ballAvoiding_one_lower_of_blocked G U x d
        (lm311HighFixedBudget k protectedCard + 3 + 2 * k ^ 2)
        hxU (hmin x) (by
          simpa [U, x, two_mul, Nat.mul_comm, Nat.add_assoc] using
            hblockedRoot 0)
      simpa [A, lm311HighRootSeed] using h
    let growthRoot : ℕ → ℕ := num.highRootGrowth
    let lossRoot : ℕ → ℕ := fun r ↦
      lm311HighFixedBudget k protectedCard +
        (2 * (r + 2) + 1) + k ^ 2 * (r + 3)
    have hrootGrowth :=
      min_growth_le_card_ballAvoidingFrom_of_lmExpander
        G epsilon kappa hexp (U : Set V) A num.highRounds
          growthRoot num.highRootGain lossRoot
          (by simpa [growthRoot] using num.high_root_start.trans hAstart)
          (by intro r hr; simpa [growthRoot] using num.high_root_next r hr)
          (by
            intro r hr
            have hsub : ballAvoidingFrom G (U : Set V) A r ⊆
                ballAvoiding G (U : Set V) x (r + 1) := by
              simpa [A] using ballAvoidingFrom_ballAvoiding_one_subset G U x r
            have hav : ∀ z ∈ ballAvoiding G (U : Set V) x (r + 1),
                z ∉ (U : Set V) := by
              intro z hz
              have hzReach :=
                (mem_ballAvoiding G (U : Set V) x (r + 1) z).1 hz
              rcases hzReach.eq_root_or_not_mem with hzx | hzU
              · simpa [hzx] using hxU
              · exact hzU
            have hb := blockedExternalNeighborhood_subset_of_subset_of_avoids
              G (U : Set V) hsub hav
            exact (Finset.card_le_card hb).trans (by
              simpa [lossRoot] using hblockedRoot (r + 1)))
          (by
            intro r hr
            simpa [growthRoot] using num.high_root_lower r hr)
          (by
            intro r hr s hgs hs
            simpa [growthRoot, lossRoot, Nat.add_assoc] using
              num.high_root_rate r hr s hgs hs)
    have hrootHalf : Fintype.card V / 2 + 1 ≤
        (ballAvoidingFrom G (U : Set V) A num.highRounds).card := by
      have hreaches : Fintype.card V / 2 + 1 ≤
          growthRoot num.highRounds := by
        simpa [growthRoot] using num.high_root_half
      simpa [min_eq_right hreaches] using hrootGrowth
    have hsupportCard :
        (BoundedRootTargetPath.familySupport family).card ≤
          k ^ 2 * (3 * m + 1) := by
      exact (BoundedRootTargetPath.card_familySupport_le family).trans
        (Nat.mul_le_mul_right (3 * m + 1) hfamilyCard)
    have hUcard : U.card ≤
        lm311HighCarrierBudget (Fintype.card V) k protectedCard
          (3 * m + 1) := by
      have hUcover := Finset.card_le_card (hcover x)
      have hu1 := Finset.card_union_le fixed C.support.toFinset
      have hu2 := Finset.card_union_le (fixed ∪ C.support.toFinset)
        (BoundedRootTargetPath.familySupport family)
      calc
        U.card ≤ ((fixed ∪ C.support.toFinset) ∪
            BoundedRootTargetPath.familySupport family).card := hUcover
        _ ≤ (fixed ∪ C.support.toFinset).card +
            (BoundedRootTargetPath.familySupport family).card := hu2
        _ ≤ (fixed.card + C.support.toFinset.card) +
            (BoundedRootTargetPath.familySupport family).card :=
          Nat.add_le_add_right hu1 _
        _ ≤ lm311HighCarrierBudget (Fintype.card V) k protectedCard
            (3 * m + 1) := by
          dsimp [lm311HighCarrierBudget]
          omega
    have hyDelta : Delta ≤ G.degree y := by
      have hyCandidate := hhubsSub hyHubs
      exact (Finset.mem_filter.1 (Finset.mem_sdiff.1 hyCandidate).1).2
    have hyDegree : max (d - 1) Delta ≤ G.degree y :=
      max_le (hmin y) hyDelta
    let B : Finset V := G.neighborFinset y \ U
    have hBstart : lm311HighHubSeed (Fintype.card V) d Delta k
        protectedCard (3 * m + 1) ≤ B.card := by
      have hinter : (U ∩ G.neighborFinset y).card ≤ U.card :=
        Finset.card_le_card Finset.inter_subset_left
      have hraw : max (d - 1) Delta - U.card ≤ B.card := by
        calc
          max (d - 1) Delta - U.card ≤ G.degree y - U.card :=
            Nat.sub_le_sub_right hyDegree U.card
          _ ≤ G.degree y - (U ∩ G.neighborFinset y).card :=
            Nat.sub_le_sub_left hinter (G.degree y)
          _ = B.card := by
            dsimp [B]
            rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree]
      dsimp [lm311HighHubSeed]
      exact (Nat.sub_le_sub_left hUcard _).trans hraw
    let growthHub : ℕ → ℕ := num.highHubGrowth
    let lossHub : ℕ → ℕ := fun _ ↦
      lm311HighCarrierBudget (Fintype.card V) k protectedCard (3 * m + 1)
    have hhubGrowth :=
      min_growth_le_card_ballAvoidingFrom_of_lmExpander
        G epsilon kappa hexp (U : Set V) B num.highRounds
          growthHub num.highHubGain lossHub
          (by simpa [growthHub] using num.high_hub_start.trans hBstart)
          (by intro r hr; simpa [growthHub] using num.high_hub_next r hr)
          (by
            intro r hr
            calc
              (blockedExternalNeighborhood G (U : Set V)
                  (ballAvoidingFrom G (U : Set V) B r)).card ≤ U.card := by
                apply Finset.card_le_card
                intro z hz
                exact (mem_blockedExternalNeighborhood G (U : Set V) _ z).1 hz |>.2
              _ ≤ lossHub r := by simpa [lossHub] using hUcard)
          (by
            intro r hr
            simpa [growthHub] using num.high_hub_lower r hr)
          (by
            intro r hr s hgs hs
            simpa [growthHub, lossHub, Nat.add_assoc] using
              num.high_hub_rate r hr s hgs hs)
    have hhubHalf : Fintype.card V / 2 + 1 ≤
        (ballAvoidingFrom G (U : Set V) B num.highRounds).card := by
      have hreaches : Fintype.card V / 2 + 1 ≤
          growthHub num.highRounds := by
        simpa [growthHub] using num.high_hub_half
      simpa [min_eq_right hreaches] using hhubGrowth
    have hAavoid : ∀ a ∈ A, a ∉ (U : Set V) := by
      simpa [A, ballAvoidingFrom] using
        (ballAvoidingFrom_avoids_forbidden G (U : Set V) ({x} : Finset V) 1
          (by simpa using hxU))
    have hBavoid : ∀ b ∈ B, b ∉ (U : Set V) := by
      intro b hb
      exact (Finset.mem_sdiff.1 hb).2
    have hlarge : Fintype.card V <
        (ballAvoidingFrom G (U : Set V) A num.highRounds).card +
          (ballAvoidingFrom G (U : Set V) B num.highRounds).card := by
      omega
    obtain ⟨q, hqPath, hqLength, hqAvoid⟩ :=
      exists_short_root_target_path_of_large_balls G U A B num.highRounds
        (by intro z hz; exact hz) (by
          intro z hz
          exact (Finset.mem_sdiff.1 hz).1) hAavoid hBavoid hlarge
    have hyLabel : label y = unused := by
      dsimp [label, y]
      simpa using
        (BoundedRootTargetPath.targetLabel_of_mem defaultHub hyHubs)
    have hyunused' : ∀ q ∈ family, label q.target ≠ label y := by
      intro old hold heq
      exact hunused old hold (heq.trans hyLabel)
    obtain ⟨new, hnewNot, hnewRoot, hnewFamily⟩ :=
      BoundedRootTargetPath.exists_admissible_insert_of_switching_path
        hrootsBarrier hhubsBarrier hrootTarget family hfamily hxRoots hyHubs
          (by simpa [x] using hdeficient) hyunused' q hqPath
          (hqLength.trans_lt num.high_connector) (by simpa [U, y] using hqAvoid)
    exact ⟨new, hnewNot, hnewRoot, hnewFamily⟩
  obtain ⟨route, hroute, hrouteInj⟩ :=
    BoundedRootTargetPath.exists_routeMatrix_of_fullFibres root family hfull
  let protectedSet : Finset V :=
    (reservedSet ∪ C.support.toFinset) ∪ roots
  let base : Finset V :=
    protectedSet ∪ BoundedRootTargetPath.familySupport family
  have hbaseCard : base.card ≤
      protectedCard + lm311GirthBudget (Fintype.card V) + k +
        k ^ 2 * (3 * m + 1) := by
    have hpC := Finset.card_union_le reservedSet C.support.toFinset
    have hpCR := Finset.card_union_le (reservedSet ∪ C.support.toFinset) roots
    have hall := Finset.card_union_le protectedSet
      (BoundedRootTargetPath.familySupport family)
    have hsupport := BoundedRootTargetPath.card_familySupport_le family
    have hsupport' :
        (BoundedRootTargetPath.familySupport family).card ≤
          k ^ 2 * (3 * m + 1) :=
      hsupport.trans (Nat.mul_le_mul_right (3 * m + 1) hfamilyCard)
    calc
      base.card ≤ protectedSet.card +
          (BoundedRootTargetPath.familySupport family).card := hall
      _ ≤ ((reservedSet ∪ C.support.toFinset).card + roots.card) +
          (BoundedRootTargetPath.familySupport family).card :=
        Nat.add_le_add_right hpCR _
      _ ≤ ((reservedSet.card + C.support.toFinset.card) + roots.card) +
          (BoundedRootTargetPath.familySupport family).card :=
        Nat.add_le_add_right (Nat.add_le_add_right hpC roots.card) _
      _ ≤ protectedCard + lm311GirthBudget (Fintype.card V) + k +
          k ^ 2 * (3 * m + 1) := by
        exact Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hprotected hCcard) hrootsCard.le)
          hsupport'
  let center : (Fin k × Fin k) ↪ V :=
    ⟨fun a ↦ (route a.1 a.2).target, by
      intro a b hab
      have hlabelEq : label (route a.1 a.2).target =
          label (route b.1 b.2).target := congrArg label hab
      have hrouteEq := hfamily.2.1 (hroute a.1 a.2).1
        (hroute b.1 b.2).1 hlabelEq
      exact hrouteInj hrouteEq⟩
  have hcenterBase : ∀ a, center a ∈ base := by
    intro a
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.2
    exact ⟨route a.1 a.2, (hroute a.1 a.2).1, by
      change (route a.1 a.2).target ∈ (route a.1 a.2).walk.support.toFinset
      exact List.mem_toFinset.2 (route a.1 a.2).walk.end_mem_support⟩
  have hcenterDegree : ∀ a,
      D + base.card + Fintype.card (Fin k × Fin k) * D ≤
        G.degree (center a) := by
    intro a
    have htargetHub : (route a.1 a.2).target ∈ hubs :=
      (route a.1 a.2).target_mem
    have hdeg : Delta ≤ G.degree (center a) := by
      have hcand := hhubsSub htargetHub
      change Delta ≤ G.degree ((route a.1 a.2).target)
      exact (Finset.mem_filter.1 (Finset.mem_sdiff.1 hcand).1).2
    have hcardPair : Fintype.card (Fin k × Fin k) = k ^ 2 := by
      simp [pow_two]
    rw [hcardPair]
    have hbudget := num.high_star_budget
    have hpre : D + base.card + k ^ 2 * D ≤
        D + (protectedCard + lm311GirthBudget (Fintype.card V) + k +
          k ^ 2 * (3 * m + 1)) + k ^ 2 * D :=
      Nat.add_le_add_right (Nat.add_le_add_left hbaseCard D) (k ^ 2 * D)
    exact hpre.trans (by omega)
  obtain ⟨starPair, hstarBase, hstarPair⟩ :=
    exists_pairwise_starExpansion_avoiding_finite G center base num.D_pos
      hcenterBase hcenterDegree
  let star (i j : Fin k) :
      VertexExpansion G (route i j).target D 1 := starPair (i, j)
  refine ⟨?_⟩
  apply BoundedRootTargetPath.expansionFamilyOfRoutesAndStars
    (roots := roots) (targets := hubs) (barrier := barrier) (label := label)
    (root := root) (order := order) (protectedSet := protectedSet)
    (base := base) (family := family) (route := route) (star := star)
    (endpointRadius := 1) (R := 5 * m) (hattach := by
      have hm := num.m_pos
      omega)
    hfamily hrootsBarrier hhubsBarrier hrootTarget
  · intro z hz
    rcases Finset.mem_union.1 hz with hzPC | hzR
    · rcases Finset.mem_union.1 hzPC with hzP | hzC
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ hzP))
      · exact Finset.mem_union_right _ hzC
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ hzR))
  · rw [Finset.disjoint_left]
    intro z hzH hzProtected
    have hcand := hhubsSub hzH
    exact (Finset.mem_sdiff.1 hcand).2 (by
      simpa [protectedSet, roots, Finset.union_assoc] using hzProtected)
  · exact Finset.subset_union_right
  · intro z hz
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  · exact Finset.subset_union_left
  · exact hroute
  · exact hrouteInj
  · intro i j
    change Disjoint ((starPair (i, j)).verts \ {center (i, j)}) base
    exact hstarBase (i, j)
  · intro a b hab
    simpa [star] using hstarPair a b hab
  · exact num.m_pos
  · exact horderPos
  · exact horderLe

/-- Low-degree branch of Liu--Montgomery Lemma 3.11.  Low prescribed roots
are routed to the separated reservoirs; high prescribed roots are handled
afterwards by repeated-centre stars. -/
theorem liuMontgomery_lemma3_11_caseLow [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (k d D Delta ell₀ m protectedCard : ℕ)
    (reservedSet : Finset V) (hprotected : reservedSet.card ≤ protectedCard)
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (root : Fin k ↪ V) (order : Fin k → Fin k → ℕ)
    (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (horderPos : ∀ i j, 0 < order i j)
    (horderLe : ∀ i j, order i j ≤ D)
    (num : LM311Numerics epsilon kappa (Fintype.card V)
      k d D Delta ell₀ m protectedCard)
    (hlow : (lm311HighCandidates G Delta reservedSet C.support.toFinset
      (Finset.univ.image root)).card < 2 * k ^ 2) :
    Nonempty (LM311ExpansionFamily G root order (5 * m)
      ((reservedSet ∪ C.support.toFinset) ∪ Finset.univ.image root)) := by
  classical
  let roots : Finset V := Finset.univ.image root
  let L : Finset V := Finset.univ.filter fun v ↦ Delta ≤ G.degree v
  let lowRoots : Finset V := roots \ L
  let protectedSet : Finset V := (reservedSet ∪ C.support.toFinset) ∪ roots
  let fixed0 : Finset V := L \ C.support.toFinset
  let fixed : Finset V := fixed0 ∪ reservedSet ∪ roots
  have hrootsCard : roots.card = k := by
    simpa [roots] using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin k))
        root.injective)
  have hfixed0Sub : fixed0 ⊆
      lm311HighCandidates G Delta reservedSet C.support.toFinset roots ∪
        reservedSet ∪ roots := by
    intro v hv
    obtain ⟨hvL, hvC⟩ := Finset.mem_sdiff.1 hv
    by_cases hvR : v ∈ reservedSet
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvR)
    by_cases hvX : v ∈ roots
    · exact Finset.mem_union_right _ hvX
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    change v ∈ (Finset.univ.filter fun w ↦ Delta ≤ G.degree w) \
      (reservedSet ∪ C.support.toFinset ∪ roots)
    exact Finset.mem_sdiff.2 ⟨hvL, by
      intro hvUnion
      rcases Finset.mem_union.1 hvUnion with hvRC | hvRoots
      · rcases Finset.mem_union.1 hvRC with hvReserved | hvCycle
        · exact hvR hvReserved
        · exact hvC hvCycle
      · exact hvX hvRoots⟩
  have hfixed0Card : fixed0.card ≤ 2 * k ^ 2 + protectedCard + k := by
    have hc := Finset.card_le_card hfixed0Sub
    have hu1 := Finset.card_union_le
      (lm311HighCandidates G Delta reservedSet C.support.toFinset roots)
      reservedSet
    have hu2 := Finset.card_union_le
      (lm311HighCandidates G Delta reservedSet C.support.toFinset roots ∪
        reservedSet) roots
    have hh : (lm311HighCandidates G Delta reservedSet C.support.toFinset
        roots).card ≤ 2 * k ^ 2 := by
      change (lm311HighCandidates G Delta reservedSet C.support.toFinset
        (Finset.univ.image root)).card ≤ 2 * k ^ 2
      exact hlow.le
    calc
      fixed0.card ≤
          (lm311HighCandidates G Delta reservedSet C.support.toFinset roots ∪
            reservedSet ∪ roots).card := hc
      _ ≤ (lm311HighCandidates G Delta reservedSet C.support.toFinset roots ∪
            reservedSet).card + roots.card := hu2
      _ ≤ ((lm311HighCandidates G Delta reservedSet C.support.toFinset
            roots).card + reservedSet.card) + roots.card :=
        Nat.add_le_add_right hu1 roots.card
      _ ≤ 2 * k ^ 2 + protectedCard + k :=
        Nat.add_le_add (Nat.add_le_add hh hprotected) hrootsCard.le
  have hfixedCard : fixed.card ≤
      2 * k ^ 2 + 2 * protectedCard + 2 * k := by
    have hu1 := Finset.card_union_le fixed0 reservedSet
    have hu2 := Finset.card_union_le (fixed0 ∪ reservedSet) roots
    exact hu2.trans <| (Nat.add_le_add_right hu1 roots.card).trans (by omega)
  have hLcover : L ⊆ fixed ∪ C.support.toFinset := by
    intro v hv
    by_cases hvC : v ∈ C.support.toFinset
    · exact Finset.mem_union_right _ hvC
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hv, hvC⟩)))
  have hrootsFixed : roots ⊆ fixed := by
    exact fun _ hz ↦ Finset.mem_union_right _ hz
  obtain ⟨center, reservoir, hcenterL, hreservoirProtected,
      hreservoirPair, hreservoirLBall, hfarPair, hfarRoots⟩ :=
    exists_sourceLowReservoirSystem G epsilon kappa hexp
      k d D Delta ell₀ m protectedCard reservedSet hprotected C hC root hmin
        num hlow
  let defaultCenter : Fin (k ^ 2) := ⟨0, pow_pos num.k_pos 2⟩
  have hdDelta : d - 1 ≤ Delta := by
    have hnotHigh : ¬ Delta ≤ G.degree (center defaultCenter) := by
      intro hhighDegree
      apply hcenterL defaultCenter
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hhighDegree⟩
    exact (hmin (center defaultCenter)).trans (Nat.le_of_lt
      (Nat.lt_of_not_ge hnotHigh))
  let targets := reservoirUnion reservoir
  let default : Fin (k ^ 2) := ⟨0, pow_pos num.k_pos 2⟩
  let label := reservoirLabel default reservoir
  let barrier := (fixed ∪ C.support.toFinset) ∪ targets
  obtain ⟨family, hfamily, hmaximum, hminimum, hfull⟩ :=
    exists_sourceLowFullPathFamily G epsilon kappa hexp
      k d D Delta ell₀ m protectedCard reservedSet roots L lowRoots
        protectedSet fixed C hC center reservoir hcenterL hreservoirProtected
        hreservoirPair hreservoirLBall hfarPair hfarRoots hrootsCard rfl
        hprotected rfl hfixedCard hLcover hrootsFixed hmin hdDelta num
  let lowIndices : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ root i ∉ L
  let highIndices : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ root i ∈ L
  have hrouteExists (i : {i // i ∈ lowIndices}) :
      ∃ route : Fin k →
          BoundedRootTargetPath G lowRoots targets (3 * m + 1),
        (∀ j, route j ∈ family ∧ (route j).root = root i.1) ∧
        Function.Injective route := by
    apply BoundedRootTargetPath.exists_routeFiber_of_full family
    apply hfull
    exact Finset.mem_sdiff.2 ⟨by simp [roots], by
      have hi := Finset.mem_filter.1 i.2
      exact hi.2⟩
  let route (i : {i // i ∈ lowIndices}) (j : Fin k) :
      BoundedRootTargetPath G lowRoots targets (3 * m + 1) :=
    Classical.choose (hrouteExists i) j
  have hroute (i : {i // i ∈ lowIndices}) (j : Fin k) :
      route i j ∈ family ∧ (route i j).root = root i.1 :=
    (Classical.choose_spec (hrouteExists i)).1 j
  have hrouteInj (i : {i // i ∈ lowIndices}) :
      Function.Injective (route i) :=
    (Classical.choose_spec (hrouteExists i)).2
  have htargetInReservoir
      (p : BoundedRootTargetPath G lowRoots targets (3 * m + 1))
      (hp : p ∈ family) :
      p.target ∈ (reservoir (label p.target)).verts := by
    have hpTarget : p.target ∈ targets := p.target_mem
    obtain ⟨s, -, hps⟩ := Finset.mem_biUnion.1 hpTarget
    have hlabel : label p.target = s := by
      dsimp [label]
      exact reservoirLabel_eq_of_mem default reservoir hreservoirPair s hps
    rw [hlabel]
    exact hps
  have castRoot_verts {a b : V} {n r : ℕ} (h : a = b)
      (E : VertexExpansion G a n r) :
      ((h ▸ E : VertexExpansion G b n r)).verts = E.verts := by
    cases h
    rfl
  have hlowExists (a : {i // i ∈ lowIndices} × Fin k) :
      ∃ E : VertexExpansion G (root a.1.1) (order a.1.1 a.2) (5 * m),
        E.verts ⊆ (route a.1 a.2).supportFinset ∪
          (reservoir (label (route a.1 a.2).target)).verts := by
    let p := route a.1 a.2
    have hyp : p.target ∈ (reservoir (label p.target)).verts :=
      htargetInReservoir p (hroute a.1 a.2).1
    let endpoint : VertexExpansion G p.target Delta (2 * ell₀) :=
      (reservoir (label p.target)).reroot hyp
    obtain ⟨full, hfullCarrier⟩ := exists_attached_vertexExpansion
      (rp := 3 * m) (rE := 2 * ell₀) (R := 5 * m)
      p.walk p.isPath (Nat.le_of_lt_succ (by simpa [p] using p.length_lt))
      endpoint num.attach_radius
    have hpRoot : p.root = root a.1.1 := by
      simpa [p] using (hroute a.1 a.2).2
    let full' : VertexExpansion G (root a.1.1) Delta (5 * m) :=
      hpRoot ▸ full
    have hDDelta : D ≤ Delta := by
      rw [num.Delta_eq]
      nlinarith [num.D_pos]
    obtain ⟨small, hsmall⟩ := full'.proposition3_10
      (horderPos a.1.1 a.2) ((horderLe a.1.1 a.2).trans hDDelta)
    refine ⟨small, hsmall.trans ?_⟩
    intro z hz
    have hzFull : z ∈ full.verts := by
      rw [← castRoot_verts hpRoot full]
      exact hz
    have hzCarrier := hfullCarrier hzFull
    rcases Finset.mem_union.1 hzCarrier with hzPath | hzEndpoint
    · exact Finset.mem_union_left _ (by
        simpa [p, BoundedRootTargetPath.supportFinset] using hzPath)
    · exact Finset.mem_union_right _ (by
        simpa [p, endpoint] using hzEndpoint)
  let lowExpansion (a : {i // i ∈ lowIndices} × Fin k) :
      VertexExpansion G (root a.1.1) (order a.1.1 a.2) (5 * m) :=
    Classical.choose (hlowExists a)
  have hlowCarrier (a : {i // i ∈ lowIndices} × Fin k) :
      (lowExpansion a).verts ⊆ (route a.1 a.2).supportFinset ∪
        (reservoir (label (route a.1 a.2).target)).verts :=
    Classical.choose_spec (hlowExists a)
  have htargetProtected : Disjoint targets protectedSet := by
    exact (disjoint_reservoirUnion_of_forall reservoir protectedSet
      (fun s ↦ (hreservoirProtected s).symm)).symm
  have hrootTarget : Disjoint lowRoots targets := by
    rw [Finset.disjoint_left]
    intro z hzLow hzTarget
    have hzRoot : z ∈ roots := (Finset.mem_sdiff.1 hzLow).1
    have hzProtected : z ∈ protectedSet := by
      exact Finset.mem_union_right _ hzRoot
    exact (Finset.disjoint_left.1 htargetProtected hzTarget hzProtected).elim
  have hrootsBarrier : lowRoots ⊆ barrier := by
    intro z hz
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply hrootsFixed
    exact (Finset.mem_sdiff.1 hz).1
  have htargetsBarrier : targets ⊆ barrier := Finset.subset_union_right
  have hprotectedBarrier : protectedSet ⊆ barrier := by
    intro z hz
    rcases Finset.mem_union.1 hz with hzPC | hzRoots
    · rcases Finset.mem_union.1 hzPC with hzReserved | hzCycle
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _ hzReserved)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hzCycle)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (hrootsFixed hzRoots))
  have hrouteDistinct : ∀
      (a b : {i // i ∈ lowIndices} × Fin k), a ≠ b →
      route a.1 a.2 ≠ route b.1 b.2 := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hab hrouteEq
    have hiVal : i.1 = i'.1 := by
      apply root.injective
      calc
        root i.1 = (route i j).root := (hroute i j).2.symm
        _ = (route i' j').root := congrArg
          (fun p : BoundedRootTargetPath G lowRoots targets (3 * m + 1) ↦
            p.root) hrouteEq
        _ = root i'.1 := (hroute i' j').2
    have hi : i = i' := Subtype.ext hiVal
    subst i'
    have hj : j = j' := hrouteInj i hrouteEq
    subst j'
    exact hab rfl
  have hlabelNe : ∀ (a b : {i // i ∈ lowIndices} × Fin k),
      a ≠ b → label (route a.1 a.2).target ≠
        label (route b.1 b.2).target := by
    intro a b hab hlabelEq
    exact hrouteDistinct a b hab <|
      hfamily.2.1 (hroute a.1 a.2).1 (hroute b.1 b.2).1 hlabelEq
  have htrimNotLow (a : {i // i ∈ lowIndices} × Fin k) {z : V}
      (hz : z ∈ (lowExpansion a).verts \ {root a.1.1}) : z ∉ lowRoots := by
    intro hzLow
    have hzCarrier := hlowCarrier a (Finset.mem_sdiff.1 hz).1
    rcases Finset.mem_union.1 hzCarrier with hzPath | hzReservoir
    · have hzWalk : z ∈ (route a.1 a.2).walk.support := by
        simpa only [BoundedRootTargetPath.supportFinset, List.mem_toFinset] using
          hzPath
      have hzEnds := hfamily.1 (route a.1 a.2) (hroute a.1 a.2).1 z
        hzWalk (hrootsBarrier hzLow)
      rcases (by simpa using hzEnds :
          z = (route a.1 a.2).root ∨ z = (route a.1 a.2).target) with
        hzRoot | hzTarget
      · exact (Finset.mem_sdiff.1 hz).2 (by
          simpa [hroute a.1 a.2 |>.2] using hzRoot)
      · have hzT : z ∈ targets := by
          simpa [hzTarget] using (route a.1 a.2).target_mem
        exact Finset.disjoint_left.1 hrootTarget hzLow hzT
    · have hzT : z ∈ targets :=
        reservoir_mem_union reservoir _ hzReservoir
      exact Finset.disjoint_left.1 hrootTarget hzLow hzT
  have hlowAvoids (a : {i // i ∈ lowIndices} × Fin k) :
      Disjoint ((lowExpansion a).verts \ {root a.1.1}) protectedSet := by
    rw [Finset.disjoint_left]
    intro z hz hzProtected
    have hzCarrier := hlowCarrier a (Finset.mem_sdiff.1 hz).1
    rcases Finset.mem_union.1 hzCarrier with hzPath | hzReservoir
    · have hzWalk : z ∈ (route a.1 a.2).walk.support := by
        simpa only [BoundedRootTargetPath.supportFinset, List.mem_toFinset] using
          hzPath
      have hzEnds := hfamily.1 (route a.1 a.2) (hroute a.1 a.2).1 z
        hzWalk (hprotectedBarrier hzProtected)
      rcases (by simpa using hzEnds :
          z = (route a.1 a.2).root ∨ z = (route a.1 a.2).target) with
        hzRoot | hzTarget
      · exact (Finset.mem_sdiff.1 hz).2 (by
          simpa [hroute a.1 a.2 |>.2] using hzRoot)
      · have hzT : z ∈ targets := by
          simpa [hzTarget] using (route a.1 a.2).target_mem
        exact Finset.disjoint_left.1 htargetProtected hzT hzProtected
    · exact Finset.disjoint_left.1 (hreservoirProtected _)
        hzReservoir hzProtected
  have hlowPair : ∀ (a b : {i // i ∈ lowIndices} × Fin k), a ≠ b →
      Disjoint ((lowExpansion a).verts \ {root a.1.1})
        ((lowExpansion b).verts \ {root b.1.1}) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro z hzA hzB
    have hzACarrier := hlowCarrier a (Finset.mem_sdiff.1 hzA).1
    have hzBCarrier := hlowCarrier b (Finset.mem_sdiff.1 hzB).1
    rcases Finset.mem_union.1 hzACarrier with hzAPath | hzARes <;>
      rcases Finset.mem_union.1 hzBCarrier with hzBPath | hzBRes
    · have hzAPath' : z ∈ (route a.1 a.2).supportFinset \ lowRoots :=
        Finset.mem_sdiff.2 ⟨hzAPath, htrimNotLow a hzA⟩
      have hzBPath' : z ∈ (route b.1 b.2).supportFinset \ lowRoots :=
        Finset.mem_sdiff.2 ⟨hzBPath, htrimNotLow b hzB⟩
      exact Finset.disjoint_left.1
        (hfamily.2.2.1 (route a.1 a.2) (hroute a.1 a.2).1
          (route b.1 b.2) (hroute b.1 b.2).1
          (hrouteDistinct a b hab)) hzAPath' hzBPath'
    · have hzWalk : z ∈ (route a.1 a.2).walk.support := by
        simpa only [BoundedRootTargetPath.supportFinset, List.mem_toFinset] using
          hzAPath
      have hzEnds := hfamily.1 (route a.1 a.2) (hroute a.1 a.2).1 z
        hzWalk (htargetsBarrier (reservoir_mem_union reservoir _ hzBRes))
      rcases (by simpa using hzEnds :
          z = (route a.1 a.2).root ∨ z = (route a.1 a.2).target) with
        hzRoot | hzTarget
      · have hzLow : z ∈ lowRoots := by
          simpa [hzRoot] using (route a.1 a.2).root_mem
        exact htrimNotLow b hzB hzLow
      · have hown := htargetInReservoir (route a.1 a.2)
          (hroute a.1 a.2).1
        have hzOwn : z ∈
            (reservoir (label (route a.1 a.2).target)).verts := by
          simpa [hzTarget] using hown
        exact Finset.disjoint_left.1
          (hreservoirPair _ _ (hlabelNe a b hab)) hzOwn hzBRes
    · have hzWalk : z ∈ (route b.1 b.2).walk.support := by
        simpa only [BoundedRootTargetPath.supportFinset, List.mem_toFinset] using
          hzBPath
      have hzEnds := hfamily.1 (route b.1 b.2) (hroute b.1 b.2).1 z
        hzWalk (htargetsBarrier (reservoir_mem_union reservoir _ hzARes))
      rcases (by simpa using hzEnds :
          z = (route b.1 b.2).root ∨ z = (route b.1 b.2).target) with
        hzRoot | hzTarget
      · have hzLow : z ∈ lowRoots := by
          simpa [hzRoot] using (route b.1 b.2).root_mem
        exact htrimNotLow a hzA hzLow
      · have hown := htargetInReservoir (route b.1 b.2)
          (hroute b.1 b.2).1
        have hzOwn : z ∈
            (reservoir (label (route b.1 b.2).target)).verts := by
          simpa [hzTarget] using hown
        exact Finset.disjoint_left.1
          (hreservoirPair _ _ (hlabelNe a b hab)) hzARes hzOwn
    · exact Finset.disjoint_left.1
        (hreservoirPair _ _ (hlabelNe a b hab)) hzARes hzBRes
  let lowUnion : Finset V :=
    Finset.univ.biUnion fun a : {i // i ∈ lowIndices} × Fin k ↦
      (lowExpansion a).verts
  let base : Finset V := protectedSet ∪ lowUnion
  have hdegreeThree : ∀ v : V, 3 ≤ G.degree v := by
    intro v
    have hv := hmin v
    have hd := num.four_le_d
    omega
  have hCcard : C.support.toFinset.card ≤
      lm311GirthBudget (Fintype.card V) := by
    rw [cycle_support_toFinset_card_eq_length C hC.1]
    simpa [lm311GirthBudget] using
      hC.length_le_two_mul_log_add_two G hdegreeThree
  have hprotectedCard : protectedSet.card ≤
      protectedCard + lm311GirthBudget (Fintype.card V) + k := by
    have hu1 := Finset.card_union_le reservedSet C.support.toFinset
    have hu2 := Finset.card_union_le (reservedSet ∪ C.support.toFinset) roots
    exact hu2.trans <| (Nat.add_le_add_right hu1 roots.card).trans (by omega)
  have hlowUnionCard : lowUnion.card ≤
      Fintype.card ({i // i ∈ lowIndices} × Fin k) * D := by
    calc
      lowUnion.card ≤ ∑ a ∈
          (Finset.univ : Finset ({i // i ∈ lowIndices} × Fin k)),
          (lowExpansion a).verts.card := by
        simpa [lowUnion] using
          (Finset.card_biUnion_le
            (s := (Finset.univ :
              Finset ({i // i ∈ lowIndices} × Fin k)))
            (t := fun a ↦ (lowExpansion a).verts))
      _ ≤ ∑ _a ∈
          (Finset.univ : Finset ({i // i ∈ lowIndices} × Fin k)), D := by
        apply Finset.sum_le_sum
        intro a ha
        rw [(lowExpansion a).card_verts]
        exact horderLe a.1.1 a.2
      _ = Fintype.card ({i // i ∈ lowIndices} × Fin k) * D := by simp
  have hbaseCard : base.card ≤
      protectedCard + lm311GirthBudget (Fintype.card V) + k +
        Fintype.card ({i // i ∈ lowIndices} × Fin k) * D := by
    exact (Finset.card_union_le protectedSet lowUnion).trans
      (Nat.add_le_add hprotectedCard hlowUnionCard)
  have hindexCount : lowIndices.card + highIndices.card = k := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k))) (fun i ↦ root i ∉ L)
    simpa [lowIndices, highIndices] using hsplit
  have hslotCount :
      Fintype.card ({i // i ∈ lowIndices} × Fin k) +
        Fintype.card ({i // i ∈ highIndices} × Fin k) = k ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    nlinarith [hindexCount]
  let highCenter : {i // i ∈ highIndices} × Fin k → V :=
    fun a ↦ root a.1.1
  have hhighCenterBase : ∀ a, highCenter a ∈ base := by
    intro a
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.2 ⟨a.1.1, Finset.mem_univ _, rfl⟩
  have hhighDegree : ∀ a,
      D + base.card +
        Fintype.card ({i // i ∈ highIndices} × Fin k) * D ≤
          G.degree (highCenter a) := by
    intro a
    have haHigh : root a.1.1 ∈ L := (Finset.mem_filter.1 a.1.2).2
    have hDelta : Delta ≤ G.degree (root a.1.1) :=
      (Finset.mem_filter.1 haHigh).2
    have hbudget := num.low_star_budget
    have hpre : D + base.card +
        Fintype.card ({i // i ∈ highIndices} × Fin k) * D ≤
        D + (protectedCard + lm311GirthBudget (Fintype.card V) + k +
          Fintype.card ({i // i ∈ lowIndices} × Fin k) * D) +
          Fintype.card ({i // i ∈ highIndices} × Fin k) * D :=
      Nat.add_le_add_right (Nat.add_le_add_left hbaseCard D) _
    exact hpre.trans (by nlinarith [hslotCount, hbudget, hDelta])
  obtain ⟨highStar, hhighStarBase, hhighStarPair⟩ :=
    exists_pairwise_trimmed_starExpansion_avoiding_finite G highCenter base
      num.D_pos hhighCenterBase hhighDegree
  have hhighExists (a : {i // i ∈ highIndices} × Fin k) :
      ∃ E : VertexExpansion G (root a.1.1) (order a.1.1 a.2) (5 * m),
        E.verts ⊆ (highStar a).verts := by
    obtain ⟨small, hsmall⟩ := (highStar a).proposition3_10
      (horderPos a.1.1 a.2) (horderLe a.1.1 a.2)
    have hradius : 1 ≤ 5 * m := by
      have hm := num.m_pos
      omega
    exact ⟨small.radiusMono hradius, by simpa using hsmall⟩
  let highExpansion (a : {i // i ∈ highIndices} × Fin k) :
      VertexExpansion G (root a.1.1) (order a.1.1 a.2) (5 * m) :=
    Classical.choose (hhighExists a)
  have hhighCarrier (a : {i // i ∈ highIndices} × Fin k) :
      (highExpansion a).verts ⊆ (highStar a).verts :=
    Classical.choose_spec (hhighExists a)
  have hhighAvoids (a : {i // i ∈ highIndices} × Fin k) :
      Disjoint ((highExpansion a).verts \ {root a.1.1}) protectedSet := by
    apply (hhighStarBase a).mono
    · intro z hz
      exact Finset.mem_sdiff.2 ⟨hhighCarrier a (Finset.mem_sdiff.1 hz).1,
        (Finset.mem_sdiff.1 hz).2⟩
    · exact Finset.subset_union_left
  have hhighPair : ∀
      (a b : {i // i ∈ highIndices} × Fin k), a ≠ b →
      Disjoint ((highExpansion a).verts \ {root a.1.1})
        ((highExpansion b).verts \ {root b.1.1}) := by
    intro a b hab
    apply (hhighStarPair a b hab).mono
    · intro z hz
      exact Finset.mem_sdiff.2 ⟨hhighCarrier a (Finset.mem_sdiff.1 hz).1,
        (Finset.mem_sdiff.1 hz).2⟩
    · intro z hz
      exact Finset.mem_sdiff.2 ⟨hhighCarrier b (Finset.mem_sdiff.1 hz).1,
        (Finset.mem_sdiff.1 hz).2⟩
  let expansion (i j : Fin k) :
      VertexExpansion G (root i) (order i j) (5 * m) :=
    if hi : i ∈ lowIndices then lowExpansion (⟨i, hi⟩, j)
    else highExpansion (⟨i, by
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      have hi' : ¬ root i ∉ L := by
        intro hnot
        exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩)
      simpa using hi'⟩, j)
  refine ⟨{
    expansion := expansion
    avoids_protected := ?_
    pairwise_disjoint := ?_ }⟩
  · intro i j
    by_cases hi : i ∈ lowIndices
    · change Disjoint ((expansion i j).verts \ {root i}) protectedSet
      simpa only [expansion, dif_pos hi] using
        hlowAvoids ((⟨i, hi⟩ : {i // i ∈ lowIndices}), j)
    · have hiHigh : i ∈ highIndices := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, ?_⟩
        have : ¬ root i ∉ L := by
          intro hnot
          exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩)
        simpa using this
      change Disjoint ((expansion i j).verts \ {root i}) protectedSet
      simpa only [expansion, dif_neg hi] using
        hhighAvoids ((⟨i, hiHigh⟩ : {i // i ∈ highIndices}), j)
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hab
    by_cases hi : i ∈ lowIndices <;> by_cases hi' : i' ∈ lowIndices
    · have hne :
          ((⟨i, hi⟩ : {i // i ∈ lowIndices}), j) ≠
          ((⟨i', hi'⟩ : {i // i ∈ lowIndices}), j') := by
        intro h
        apply hab
        exact Prod.ext (congrArg (fun a ↦ a.1.1) h)
          (congrArg (fun a ↦ a.2) h)
      simpa [expansion, hi, hi'] using
        hlowPair (⟨i, hi⟩, j) (⟨i', hi'⟩, j') hne
    · have hiHigh : i' ∈ highIndices := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, ?_⟩
        have : ¬ root i' ∉ L := by
          intro hnot
          exact hi' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩)
        simpa using this
      rw [Finset.disjoint_left]
      intro z hzLow hzHigh
      have hzLow' : z ∈
          (lowExpansion ((⟨i, hi⟩ : {i // i ∈ lowIndices}), j)).verts \
            {root i} := by
        simpa only [expansion, dif_pos hi] using hzLow
      have hzLowFull : z ∈
          (lowExpansion ((⟨i, hi⟩ : {i // i ∈ lowIndices}), j)).verts :=
        (Finset.mem_sdiff.1 hzLow').1
      have hzHighArm : z ∈ (highStar (⟨i', hiHigh⟩, j')).verts \
          {root i'} := by
        have hz' : z ∈ (highExpansion (⟨i', hiHigh⟩, j')).verts \
            {root i'} := by simpa [expansion, hi, hi'] using hzHigh
        exact Finset.mem_sdiff.2 ⟨hhighCarrier _ (Finset.mem_sdiff.1 hz').1,
          (Finset.mem_sdiff.1 hz').2⟩
      exact (Finset.disjoint_left.1 (hhighStarBase (⟨i', hiHigh⟩, j'))
        hzHighArm (by
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.2
          exact ⟨(⟨i, hi⟩, j), Finset.mem_univ _, hzLowFull⟩)).elim
    · have hiHigh : i ∈ highIndices := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, ?_⟩
        have : ¬ root i ∉ L := by
          intro hnot
          exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩)
        simpa using this
      exact (by
        have h := (show Disjoint
            ((lowExpansion (⟨i', hi'⟩, j')).verts \ {root i'})
            ((highExpansion (⟨i, hiHigh⟩, j)).verts \ {root i}) from by
          rw [Finset.disjoint_left]
          intro z hzLow hzHigh
          have hzLowFull := (Finset.mem_sdiff.1 hzLow).1
          have hzHighArm : z ∈ (highStar (⟨i, hiHigh⟩, j)).verts \
              {root i} := Finset.mem_sdiff.2
            ⟨hhighCarrier _ (Finset.mem_sdiff.1 hzHigh).1,
              (Finset.mem_sdiff.1 hzHigh).2⟩
          exact (Finset.disjoint_left.1 (hhighStarBase (⟨i, hiHigh⟩, j))
            hzHighArm (by
              apply Finset.mem_union_right
              apply Finset.mem_biUnion.2
              exact ⟨(⟨i', hi'⟩, j'), Finset.mem_univ _, hzLowFull⟩)).elim)
        simpa [expansion, hi, hi'] using h.symm)
    · have hiHigh : i ∈ highIndices := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, by
          have : ¬ root i ∉ L := by
            intro hnot
            exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩)
          simpa using this⟩
      have hiHigh' : i' ∈ highIndices := by
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ _, by
          have : ¬ root i' ∉ L := by
            intro hnot
            exact hi' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩)
          simpa using this⟩
      have hne :
          ((⟨i, hiHigh⟩ : {i // i ∈ highIndices}), j) ≠
          ((⟨i', hiHigh'⟩ : {i // i ∈ highIndices}), j') := by
        intro h
        apply hab
        exact Prod.ext (congrArg (fun a ↦ a.1.1) h)
          (congrArg (fun a ↦ a.2) h)
      simpa [expansion, hi, hi'] using
        hhighPair (⟨i, hiHigh⟩, j) (⟨i', hiHigh'⟩, j') hne

/-- Source-faithful Liu--Montgomery Lemma 3.11.  The graph-theoretic
high/low dichotomy is internal; the hypotheses exposed here are precisely
the expander, bipartite, minimum-degree, shortest-cycle, order, and scalar
numerical assumptions used downstream. -/
theorem liuMontgomery_lemma3_11_source [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Bipartition G)
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (k d D Delta ell₀ m protectedCard : ℕ)
    (reservedSet : Finset V) (hprotected : reservedSet.card ≤ protectedCard)
    {c : V} (C : G.Walk c c) (hC : IsShortestCycle C)
    (root : Fin k ↪ V) (order : Fin k → Fin k → ℕ)
    (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (horderPos : ∀ i j, 0 < order i j)
    (horderLe : ∀ i j, order i j ≤ D)
    (num : LM311Numerics epsilon kappa (Fintype.card V)
      k d D Delta ell₀ m protectedCard) :
    Nonempty (LM311ExpansionFamily G root order (5 * m)
      ((reservedSet ∪ C.support.toFinset) ∪ Finset.univ.image root)) := by
  have _ := B
  by_cases hhigh : 2 * k ^ 2 ≤
      (lm311HighCandidates G Delta reservedSet C.support.toFinset
        (Finset.univ.image root)).card
  · exact liuMontgomery_lemma3_11_caseHigh G epsilon kappa hexp
      k d D Delta ell₀ m protectedCard reservedSet hprotected C hC root order
        hmin horderPos horderLe num hhigh
  · exact liuMontgomery_lemma3_11_caseLow G epsilon kappa hexp
      k d D Delta ell₀ m protectedCard reservedSet hprotected C hC root order
        hmin horderPos horderLe num (Nat.lt_of_not_ge hhigh)

/-- A coarse protected-set constructor used only when a global deletion
budget is genuinely available.  This is not the source Lemma 3.11: its
sequential budget includes the total order of earlier expansions. -/
theorem liuMontgomery_lemma3_11_protected [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (d t m q radius budget : ℕ)
    (reserved : Finset V) (root : Fin t → V) (order : Fin t → ℕ)
    (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (hbudget : reserved.card + t + ∑ i : Fin t, order i ≤ budget)
    (hseed : kappa / 2 ≤ ((d - 1 - budget : ℕ) : ℝ))
    (hrate : ∀ s : ℕ, d - 1 - budget ≤ s →
      s ≤ Fintype.card V / 2 →
      (((budget + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ)))
    (htargetGrowth : ∀ i : Fin t,
      order i ≤ d - 1 - budget + radius * q)
    (htargetHalf : ∀ i : Fin t,
      order i ≤ Fintype.card V / 2 + 1)
    (hradius : radius + 1 ≤ m)
    (hpositive : ∀ i : Fin t, 0 < order i) :
    ∃ E : ∀ i : Fin t, VertexExpansion G (root i) (order i) m,
      (∀ i : Fin t, Disjoint ((E i).verts \ {root i}) reserved) ∧
      (∀ i : Fin t,
        Disjoint ((E i).verts \ {root i})
          (Finset.univ.image root)) ∧
      (∀ i j : Fin t, i ≠ j →
        Disjoint ((E i).verts \ {root i}) ((E j).verts \ {root j})) := by
  classical
  induction t generalizing reserved with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · exact fun i ↦ Fin.elim0 i
      · exact fun i ↦ Fin.elim0 i
  | succ t ih =>
      let last : Fin (t + 1) := Fin.last t
      let rootOld : Fin t → V := fun i ↦ root i.castSucc
      let orderOld : Fin t → ℕ := fun i ↦ order i.castSucc
      let protectedOld : Finset V := insert (root last) reserved
      have hbudgetOld :
          protectedOld.card + t + ∑ i : Fin t, orderOld i ≤ budget := by
        have hpcard : protectedOld.card ≤ reserved.card + 1 := by
          simp [protectedOld, Finset.card_insert_le]
        have hsum : (∑ i : Fin t, orderOld i) + order last =
            ∑ i : Fin (t + 1), order i := by
          simpa [orderOld, last] using (Fin.sum_univ_castSucc order).symm
        omega
      obtain ⟨Eold, hEoldProtected, hEoldRoots, hEoldPair⟩ :=
        ih protectedOld rootOld orderOld hbudgetOld
          (fun i ↦ htargetGrowth i.castSucc)
          (fun i ↦ htargetHalf i.castSucc)
          (fun i ↦ hpositive i.castSucc)
      let roots : Finset V := Finset.univ.image root
      let oldVerts : Finset V := Finset.univ.biUnion fun i : Fin t ↦ (Eold i).verts
      let W : Finset V := reserved ∪ roots ∪ oldVerts
      have hrootsCard : roots.card ≤ t + 1 := by
        simpa [roots] using
          (Finset.card_image_le
            (s := (Finset.univ : Finset (Fin (t + 1)))) (f := root))
      have holdVertsCard : oldVerts.card ≤ ∑ i : Fin t, orderOld i := by
        calc
          oldVerts.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)), (Eold i).verts.card := by
            simpa [oldVerts] using
              (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin t)))
                (t := fun i ↦ (Eold i).verts))
          _ = ∑ i : Fin t, orderOld i := by simp [VertexExpansion.card_verts]
      have hW : W.card ≤ budget := by
        have hunion₁ := Finset.card_union_le reserved roots
        have hunion₂ := Finset.card_union_le (reserved ∪ roots) oldVerts
        have hsum : (∑ i : Fin t, orderOld i) + order last =
            ∑ i : Fin (t + 1), order i := by
          simpa [orderOld, last] using (Fin.sum_univ_castSucc order).symm
        dsimp [W]
        omega
      obtain ⟨Elast, hElastBall⟩ := exists_protected_vertexExpansion
        G epsilon kappa hexp d m q radius budget (order last) W (root last)
          (hmin (root last)) hW hseed hrate (htargetGrowth last)
          (htargetHalf last) hradius (hpositive last)
      have hElastOutside : ∀ z ∈ Elast.verts \ {root last}, z ∉ W := by
        intro z hz hzW
        have hzParts := Finset.mem_sdiff.1 hz
        have hzball := hElastBall hzParts.1
        have hzcarrier :=
          ballAvoiding_subset_insert_compl G (W : Set V) (root last) (radius + 1)
            hzball
        rcases hzcarrier with hzroot | hznot
        · exact hzParts.2 (by simpa using hzroot)
        · exact hznot hzW
      let E : ∀ i : Fin (t + 1), VertexExpansion G (root i) (order i) m :=
        fun i ↦ Fin.lastCases Elast (fun j ↦ Eold j) i
      refine ⟨E, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · rw [Finset.disjoint_left]
          intro z hzE hzP
          exact hElastOutside z (by simpa [E, last] using hzE)
            (by simp [W, hzP])
        · have h := hEoldProtected j
          simpa [E] using h.mono_right (Finset.subset_insert _ _)
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · rw [Finset.disjoint_left]
          intro z hzE hzRoots
          exact hElastOutside z (by simpa [E, last] using hzE)
            (by simp [W, roots, hzRoots])
        · rw [Finset.disjoint_left]
          intro z hzE hzRoots
          have htrimOld : z ∈ (Eold j).verts \ {rootOld j} := by
            simpa [E, rootOld] using hzE
          have hzOldRoots := Finset.disjoint_left.1 (hEoldRoots j) htrimOld
          have : z ∈ Finset.univ.image rootOld := by
            rcases Finset.mem_image.1 hzRoots with ⟨i, -, rfl⟩
            by_cases hilast : i = last
            · subst i
              have hzlast : root last ∈ protectedOld := by simp [protectedOld]
              exact (Finset.disjoint_left.1 (hEoldProtected j)
                htrimOld hzlast).elim
            · obtain ⟨i', rfl⟩ := (Fin.exists_castSucc_eq).2 hilast
              exact Finset.mem_image.2 ⟨i', by simp, rfl⟩
          exact hzOldRoots this
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
            induction j using Fin.lastCases with
            | last => exact (hij rfl).elim
            | cast j' =>
                rw [Finset.disjoint_left]
                intro z hzLast hzOld
                exact hElastOutside z (by simpa [E, last] using hzLast) (by
                  apply Finset.mem_union_right
                  change z ∈ Finset.univ.biUnion (fun i : Fin t ↦ (Eold i).verts)
                  rw [Finset.mem_biUnion]
                  exact ⟨j', by simp,
                    by simpa [E] using (Finset.mem_sdiff.1 hzOld).1⟩)
        | cast i' =>
            induction j using Fin.lastCases with
            | last =>
                rw [Finset.disjoint_left]
                intro z hzOld hzLast
                exact hElastOutside z (by simpa [E, last] using hzLast) (by
                  apply Finset.mem_union_right
                  change z ∈ Finset.univ.biUnion (fun i : Fin t ↦ (Eold i).verts)
                  rw [Finset.mem_biUnion]
                  exact ⟨i', by simp,
                    by simpa [E] using (Finset.mem_sdiff.1 hzOld).1⟩)
            | cast j' =>
                simpa only [E, Fin.lastCases_castSucc, rootOld, orderOld] using
                  hEoldPair i' j'
                    (fun h ↦ hij (congrArg Fin.castSucc h))

/-! ## Source-facing shortest-cycle wrapper -/

/-- Compatibility wrapper for the coarse global-budget constructor. -/
theorem liuMontgomery_lemma3_11 [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Bipartition G) (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (d t m q radius budget : ℕ)
    (forbidden : Finset V) {c : V} (C : G.Walk c c)
    (hC : IsShortestCycle C)
    (root : Fin t → V) (order : Fin t → ℕ)
    (hmin : ∀ v : V, d - 1 ≤ G.degree v)
    (hfree : ¬ oneSubdivisionClique (d / 2) ⊑ G)
    (hbudget : (forbidden ∪ C.support.toFinset).card + t +
      ∑ i : Fin t, order i ≤ budget)
    (hseed : kappa / 2 ≤ ((d - 1 - budget : ℕ) : ℝ))
    (hrate : ∀ s : ℕ, d - 1 - budget ≤ s →
      s ≤ Fintype.card V / 2 →
      (((budget + q : ℕ) : ℝ) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ)))
    (htargetGrowth : ∀ i : Fin t,
      order i ≤ d - 1 - budget + radius * q)
    (htargetHalf : ∀ i : Fin t,
      order i ≤ Fintype.card V / 2 + 1)
    (hradius : radius + 1 ≤ m)
    (hpositive : ∀ i : Fin t, 0 < order i) :
    ∃ E : ∀ i : Fin t, VertexExpansion G (root i) (order i) m,
      (∀ i : Fin t, Disjoint ((E i).verts \ {root i}) forbidden) ∧
      (∀ i : Fin t, Disjoint ((E i).verts \ {root i}) C.support.toFinset) ∧
      (∀ i : Fin t,
        Disjoint ((E i).verts \ {root i}) (Finset.univ.image root)) ∧
      (∀ i j : Fin t, i ≠ j →
        Disjoint ((E i).verts \ {root i}) ((E j).verts \ {root j})) := by
  classical
  have _ := B
  have _ := hC
  have _ := hfree
  obtain ⟨E, hprotected, hroots, hpair⟩ :=
    liuMontgomery_lemma3_11_protected G epsilon kappa hexp
      d t m q radius budget (forbidden ∪ C.support.toFinset)
      root order hmin hbudget hseed hrate htargetGrowth htargetHalf
      hradius hpositive
  refine ⟨E, ?_, ?_, hroots, hpair⟩
  · intro i
    exact (hprotected i).mono_right Finset.subset_union_left
  · intro i
    rw [Finset.disjoint_left]
    intro z hzE hzC
    exact Finset.disjoint_left.1 (hprotected i) hzE
      (Finset.mem_union_right _ hzC)

end Erdos63
