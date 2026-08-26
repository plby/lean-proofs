/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.Nat.Find
import Mathlib.Tactic
import ErdosProblems.Erdos58.Bipartite
import ErdosProblems.Erdos1105.PathCycleSplice

/-!
# Voss's two-chord theorem

This file develops the structural part of Voss's proof that a finite
two-connected non-bipartite graph of minimum degree at least three contains
an odd cycle with two chords, apart from the complete graph on four vertices
and the triangular prism.

The cycle predicate below records two *distinct* chords directly.  The main
Erdős 1091 file converts it to the equivalent lower bound on its finite chord
count.
-/

open SimpleGraph

namespace Erdos1091.Voss

universe u

/-- An odd simple cycle with two specified distinct chords. -/
def HasOddCycleWithTwoChords {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (z : V) (C : G.Walk z z), C.IsCycle ∧ Odd C.length ∧
    ∃ e f : Sym2 V, e ≠ f ∧ C.IsChord e ∧ C.IsChord f

/-- A cycle is shortest among the odd cycles of its ambient graph. -/
def IsShortestOddCycle {V : Type u} {G : SimpleGraph V} {z : V}
    (C : G.Walk z z) : Prop :=
  C.IsCycle ∧ Odd C.length ∧
    ∀ (z' : V) (D : G.Walk z' z'), D.IsCycle → Odd D.length → C.length ≤ D.length

/-- Every supplied odd cycle has a shortest odd cycle no longer than it. -/
theorem exists_shortestOddCycle_of_oddCycle {V : Type u} {G : SimpleGraph V}
    {z₀ : V} (C₀ : G.Walk z₀ z₀) (hC₀ : C₀.IsCycle) (hodd₀ : Odd C₀.length) :
    ∃ (z : V) (C : G.Walk z z),
      IsShortestOddCycle C ∧ C.length ≤ C₀.length := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ (z : V) (C : G.Walk z z), C.IsCycle ∧ Odd C.length ∧ C.length = n
  have hP : ∃ n, P n := ⟨C₀.length, z₀, C₀, hC₀, hodd₀, rfl⟩
  obtain ⟨z, C, hcycle, hodd, hlength⟩ := Nat.find_spec hP
  have hminimal (z' : V) (D : G.Walk z' z')
      (hD : D.IsCycle) (hDodd : Odd D.length) : Nat.find hP ≤ D.length :=
    Nat.find_min' hP ⟨z', D, hD, hDodd, rfl⟩
  refine ⟨z, C, ⟨hcycle, hodd, ?_⟩, ?_⟩
  · intro z' D hD hDodd
    rw [hlength]
    exact hminimal z' D hD hDodd
  · rw [hlength]
    exact hminimal z₀ C₀ hC₀ hodd₀

/-- A graph which is not two-colorable contains a shortest odd cycle. -/
theorem exists_shortestOddCycle_of_not_colorable_two {V : Type u}
    {G : SimpleGraph V} (hncol : ¬ G.Colorable 2) :
    ∃ (z : V) (C : G.Walk z z), IsShortestOddCycle C := by
  classical
  have hsome : ∃ (z : V) (C : G.Walk z z), C.IsCycle ∧ Odd C.length := by
    by_contra hnone
    apply hncol
    apply Erdos58.colorable_two_of_no_odd_isCycle
    intro z C hC hodd
    exact hnone ⟨z, C, hC, hodd⟩
  obtain ⟨z₀, C₀, hC₀, hodd₀⟩ := hsome
  obtain ⟨z, C, hC, -⟩ :=
    exists_shortestOddCycle_of_oddCycle C₀ hC₀ hodd₀
  exact ⟨z, C, hC⟩

/-- A shortest odd cycle is chordless. -/
theorem IsShortestOddCycle.isChordless {V : Type u} {G : SimpleGraph V}
    {z : V} {C : G.Walk z z} (hC : IsShortestOddCycle C) : C.IsChordless := by
  classical
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro a b ha hb hab
  by_contra habEdge
  let R : G.Walk a a := C.rotate a ha
  have hbR : b ∈ R.support := by simpa [R] using hb
  let p : G.Walk a b := R.takeUntil b hbR
  let q : G.Walk a b := (R.dropUntil b hbR).reverse
  let e : G.Walk a b := hab.toWalk
  have hR : R.IsCycle := hC.1.rotate ha
  have hp : p.IsPath := hR.isPath_takeUntil hbR
  have hpnonempty : ¬p.Nil := by
    dsimp [p]
    rw [Walk.nil_takeUntil]
    exact G.ne_of_adj hab
  have hwhole : ((R.takeUntil b hbR).append (R.dropUntil b hbR)).IsCycle := by
    simpa using hR
  have hdrop : (R.dropUntil b hbR).IsPath :=
    hwhole.isPath_of_append_right hpnonempty
  have hq : q.IsPath := hdrop.reverse
  have he : e.IsPath := hab.isPath_toWalk
  have hchordR : s(a, b) ∉ R.edges := by
    change s(a, b) ∉ (C.rotate a ha).edges
    rw [(C.rotate_edges a ha).mem_iff]
    exact habEdge
  have hep : e ≠ p := by
    intro hep
    apply hchordR
    apply R.edges_takeUntil_subset_edges hbR
    have : s(a, b) ∈ e.edges := by simp [e, hab.edges_toWalk]
    simpa [hep] using this
  have heq : e ≠ q := by
    intro heq
    apply hchordR
    apply R.edges_dropUntil_subset_edges hbR
    have heEdge : s(a, b) ∈ e.edges := by simp [e, hab.edges_toWalk]
    have hqEdge : s(a, b) ∈ q.edges := by simpa [heq] using heEdge
    simpa [q, Walk.edges_reverse] using hqEdge
  have hpNotOne : p.length ≠ 1 := by
    intro hlen
    apply hchordR
    apply R.edges_takeUntil_subset_edges hbR
    rw [p.mk_mem_edges_iff_exists]
    refine ⟨0, by omega, ?_⟩
    rw [Walk.getVert_zero, Nat.zero_add, ← hlen, Walk.getVert_length]
  have hqNotOne : q.length ≠ 1 := by
    intro hlen
    apply hchordR
    apply R.edges_dropUntil_subset_edges hbR
    have hqedge : s(a, b) ∈ q.edges := by
      rw [q.mk_mem_edges_iff_exists]
      refine ⟨0, by omega, ?_⟩
      rw [Walk.getVert_zero, Nat.zero_add, ← hlen, Walk.getVert_length]
    simpa [q, Walk.edges_reverse] using hqedge
  let P : G.Walk a a := p.append e.reverse
  let Q : G.Walk a a := e.append q.reverse
  have hPcycle : P.IsCycle := by
    apply hp.isCycle_append he.reverse
    · intro x hx
      have hna : a ∉ p.support.tail := by
        have hn : (a :: p.support.tail).Nodup := by
          rw [p.cons_tail_support]
          exact hp.support_nodup
        exact (List.nodup_cons.mp hn).1
      intro hx'
      have hxa : x = a := by simpa [e] using hx'
      exact hna (hxa ▸ hx)
    · left
      have hpNotNil : ¬p.Nil := hpnonempty
      have hpLen : 0 < p.length := Walk.not_nil_iff_lt_length.mp hpNotNil
      omega
  have hQcycle : Q.IsCycle := by
    apply he.isCycle_append hq.reverse
    · intro x hx hx'
      have hxb : x = b := by simpa [e] using hx
      subst x
      have hn := hq.reverse.support_nodup
      rw [← q.reverse.cons_tail_support] at hn
      exact (List.nodup_cons.mp hn).1 hx'
    · right
      have hqNotNil : ¬q.Nil := by
        rw [hq.nil_iff_eq]
        exact G.ne_of_adj hab
      have hqLen : 0 < q.length := Walk.not_nil_iff_lt_length.mp hqNotNil
      simpa using (show 1 < q.length by omega)
  have hsplit : C.length = p.length + q.length := by
    calc
      C.length = R.length := by simp [R]
      _ = (R.takeUntil b hbR).length + (R.dropUntil b hbR).length := by
        rw [← Walk.length_append, R.take_spec]
      _ = p.length + q.length := by simp [p, q]
  have hparity : Odd P.length ∨ Odd Q.length := by
    have hodd : Odd (p.length + q.length) := by simpa [hsplit] using hC.2.1
    have : Odd (p.length + 1) ∨ Odd (q.length + 1) := by
      rcases Nat.even_or_odd p.length with hpEven | hpOdd
      · left
        rw [Nat.odd_add_one]
        exact Nat.not_odd_iff_even.mpr hpEven
      · right
        rw [Nat.odd_add_one]
        have hqEven : Even q.length := by
          rcases hpOdd with ⟨i, hi⟩
          rcases hodd with ⟨k, hk⟩
          refine ⟨k - i, ?_⟩
          omega
        exact Nat.not_odd_iff_even.mpr hqEven
    simpa [P, Q, Walk.length_append, e] using this
  rcases hparity with hPodd | hQodd
  · have hle := hC.2.2 a P hPcycle hPodd
    have hqpos : 0 < q.length := by
      rw [← Walk.not_nil_iff_lt_length]
      rw [hq.nil_iff_eq]
      exact G.ne_of_adj hab
    have hqTwo : 2 ≤ q.length := by omega
    simp only [P, Walk.length_append, Walk.length_reverse, e, hab.length_toWalk] at hle
    omega
  · have hle := hC.2.2 a Q hQcycle hQodd
    have hppos : 0 < p.length := Walk.not_nil_iff_lt_length.mp hpnonempty
    have hpTwo : 2 ≤ p.length := by omega
    simp only [Q, Walk.length_append, Walk.length_reverse, e, hab.length_toWalk] at hle
    omega

/-! ## Attachment paths and their maximum length

For the application the attachment set is the vertex set of a shortest odd
cycle.  It is enough to maximize over all attachment paths at once: each
such path lies in a single component of the complement of the attachment
set, so this is the maximum of the bridge-wise maxima in Voss's notation.
-/

/-- A path whose first vertex, and no other vertex, belongs to `S`. -/
structure AttachmentPath {V : Type u} (G : SimpleGraph V) (S : Set V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  start_mem : start ∈ S
  finish_notMem : finish ∉ S
  only_start : ∀ x ∈ walk.support, x ∈ S → x = start

/-- An open ear with respect to `S`: a simple path with distinct endpoints
in `S` and all internal vertices outside `S`. -/
structure Ear {V : Type u} (G : SimpleGraph V) (S : Set V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  start_mem : start ∈ S
  finish_mem : finish ∈ S
  endpoints_ne : start ≠ finish
  only_ends : ∀ x ∈ walk.support, x ∈ S → x = start ∨ x = finish

namespace AttachmentPath

variable {V : Type u} {G : SimpleGraph V} {S : Set V}

theorem endpoints_ne (P : AttachmentPath G S) : P.start ≠ P.finish := by
  intro h
  exact P.finish_notMem (h ▸ P.start_mem)

theorem length_pos (P : AttachmentPath G S) : 0 < P.walk.length := by
  rw [← Walk.not_nil_iff_lt_length, P.isPath.nil_iff_eq]
  exact P.endpoints_ne

/-- An unused neighbor outside the attachment set extends the path. -/
def extend (P : AttachmentPath G S) {v : V} (h : G.Adj P.finish v)
    (hv : v ∉ P.walk.support) (hvS : v ∉ S) : AttachmentPath G S where
  start := P.start
  finish := v
  walk := P.walk.concat h
  isPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_concat, List.nodup_append']
    refine ⟨P.isPath.support_nodup, by simp, ?_⟩
    intro x hx hxv
    have hxeq : x = v := List.mem_singleton.mp hxv
    exact hv (hxeq ▸ hx)
  start_mem := P.start_mem
  finish_notMem := hvS
  only_start := by
    intro x hx hxS
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact P.only_start x hx hxS
    · exact (hvS hxS).elim

/-- An unused neighbor in the attachment set closes the attachment path to
an open ear. -/
def close (P : AttachmentPath G S) {v : V} (h : G.Adj P.finish v)
    (hv : v ∉ P.walk.support) (hvS : v ∈ S) : Ear G S where
  start := P.start
  finish := v
  walk := P.walk.concat h
  isPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_concat, List.nodup_append']
    refine ⟨P.isPath.support_nodup, by simp, ?_⟩
    intro x hx hxv
    have hxeq : x = v := List.mem_singleton.mp hxv
    exact hv (hxeq ▸ hx)
  start_mem := P.start_mem
  finish_mem := hvS
  endpoints_ne := by
    intro h
    exact hv (h ▸ P.walk.start_mem_support)
  only_ends := by
    intro x hx hxS
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl (P.only_start x hx hxS)
    · exact Or.inr rfl

/-- Finiteness gives a longest attachment path whenever one exists. -/
theorem exists_longest [Fintype V] (P₀ : AttachmentPath G S) :
    ∃ P : AttachmentPath G S,
      ∀ Q : AttachmentPath G S, Q.walk.length ≤ P.walk.length := by
  let lengths : Set ℕ := {n | ∃ P : AttachmentPath G S, P.walk.length = n}
  have hfinite : lengths.Finite :=
    (Set.finite_le_nat (Fintype.card V)).subset (by
      rintro n ⟨P, rfl⟩
      exact P.isPath.length_lt.le)
  obtain ⟨n, ⟨⟨P, rfl⟩, hmax⟩⟩ :=
    hfinite.exists_maximal ⟨P₀.walk.length, P₀, rfl⟩
  refine ⟨P, fun Q ↦ ?_⟩
  by_cases hle : Q.walk.length ≤ P.walk.length
  · exact hle
  · exact hmax ⟨Q, rfl⟩ (Nat.le_of_lt (Nat.lt_of_not_ge hle))

/-- Voss's maximum-path lemma: the terminal vertex of a longest attachment
path has no neighbor outside the path and the attachment set. -/
theorem neighbor_mem_of_longest (P : AttachmentPath G S)
    (hmax : ∀ Q : AttachmentPath G S, Q.walk.length ≤ P.walk.length)
    {v : V} (h : G.Adj P.finish v) : v ∈ P.walk.support ∨ v ∈ S := by
  classical
  by_contra hnone
  have hv : v ∉ P.walk.support := fun hv ↦ hnone (Or.inl hv)
  have hvS : v ∉ S := fun hv ↦ hnone (Or.inr hv)
  have hle := hmax (P.extend h hv hvS)
  simp only [extend, Walk.length_concat] at hle
  omega

/-- Under the negation of the long-ear conclusion, every terminal neighbor
of a longest attachment path is already on that path. -/
theorem neighbor_mem_of_longest_of_no_long_ear (P : AttachmentPath G S)
    (hmax : ∀ Q : AttachmentPath G S, Q.walk.length ≤ P.walk.length)
    (hno : ∀ Q : Ear G S, Q.walk.length ≠ P.walk.length + 1)
    {v : V} (h : G.Adj P.finish v) : v ∈ P.walk.support := by
  rcases P.neighbor_mem_of_longest hmax h with hv | hvS
  · exact hv
  · by_contra hv
    exact hno (P.close h hv hvS) (by simp [close])

end AttachmentPath

namespace Ear

variable {V : Type u} {G : SimpleGraph V} {S : Set V}

/-- Joining an ear of length at least two to a path in the attachment set
produces a simple cycle. -/
theorem isCycle_append (E : Ear G S) (hlen : 2 ≤ E.walk.length)
    (q : G.Walk E.finish E.start) (hq : q.IsPath)
    (hqS : ∀ x ∈ q.support, x ∈ S) : (E.walk.append q).IsCycle := by
  apply E.isPath.isCycle_append hq
  · intro x hxE hxq
    have hxE' : x ∈ E.walk.support := List.tail_subset _ hxE
    have hxq' : x ∈ q.support := List.tail_subset _ hxq
    rcases E.only_ends x hxE' (hqS x hxq') with hx | hx
    · subst x
      have hn := E.isPath.support_nodup
      rw [← E.walk.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 hxE
    · subst x
      have hn := hq.support_nodup
      rw [← q.cons_tail_support, List.nodup_cons] at hn
      exact hn.1 hxq
  · exact Or.inl (by omega)

/-- An ear chord other than the edge between its endpoints remains a chord
after the ear is closed by any path inside the attachment set. -/
theorem isChord_append (E : Ear G S) (q : G.Walk E.finish E.start)
    (hqS : ∀ x ∈ q.support, x ∈ S) {e : Sym2 V}
    (he : E.walk.IsChord e) (hne : e ≠ s(E.start, E.finish)) :
    (E.walk.append q).IsChord e := by
  induction e using Sym2.ind with
  | _ x y =>
    rcases he with ⟨hxy, hnot, hx, hy⟩
    refine ⟨hxy, ?_, ?_, ?_⟩
    · simp only [Walk.edges_append, List.mem_append, not_or]
      refine ⟨hnot, ?_⟩
      intro hqedge
      have hxS := hqS x (q.fst_mem_support_of_mem_edges hqedge)
      have hyS := hqS y (q.snd_mem_support_of_mem_edges hqedge)
      rcases E.only_ends x hx hxS with rfl | rfl <;>
        rcases E.only_ends y hy hyS with rfl | rfl
      · exact G.irrefl hxy
      · exact hne rfl
      · exact hne Sym2.eq_swap
      · exact G.irrefl hxy
    · rw [Walk.support_append]
      exact List.mem_append_left _ hx
    · rw [Walk.support_append]
      exact List.mem_append_left _ hy

/-- The parity step behind Voss's observation about attachment paths. -/
theorem hasOddCycleWithTwoChords_of_two_chords
    {z : V} (C : G.Walk z z) (hC : C.IsCycle) (hodd : Odd C.length)
    (E : Ear G {x | x ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    {e f : Sym2 V} (hef : e ≠ f)
    (he : E.walk.IsChord e) (hf : E.walk.IsChord f)
    (heEnds : e ≠ s(E.start, E.finish)) (hfEnds : f ≠ s(E.start, E.finish)) :
    HasOddCycleWithTwoChords G := by
  classical
  let R : G.Walk E.start E.start := C.rotate E.start E.start_mem
  have hR : R.IsCycle := hC.rotate E.start_mem
  have hb : E.finish ∈ R.support := by
    simpa [R] using E.finish_mem
  let p : G.Walk E.start E.finish := R.takeUntil E.finish hb
  let q : G.Walk E.finish E.start := R.dropUntil E.finish hb
  have hp : p.IsPath := hR.isPath_takeUntil hb
  have hpnil : ¬p.Nil := by
    rw [hp.nil_iff_eq]
    exact E.endpoints_ne
  have hwhole : (p.append q).IsCycle := by
    simpa [p, q] using hR
  have hq : q.IsPath := hwhole.isPath_of_append_right hpnil
  have hpS : ∀ x ∈ p.reverse.support, x ∈ C.support := by
    intro x hx
    have hx' : x ∈ p.support := by simpa using hx
    have hxR := R.support_takeUntil_subset_support hb hx'
    simpa [R] using hxR
  have hqS : ∀ x ∈ q.support, x ∈ C.support := by
    intro x hx
    have hxR := R.support_dropUntil_subset_support hb hx
    simpa [R] using hxR
  have hsplit : p.reverse.length + q.length = C.length := by
    simp only [Walk.length_reverse]
    calc
      p.length + q.length = (p.append q).length := (Walk.length_append _ _).symm
      _ = R.length := by simp [p, q]
      _ = C.length := by simp [R]
  have hparity : Odd (E.walk.append p.reverse).length ∨
      Odd (E.walk.append q).length := by
    simp only [Walk.length_append, Nat.odd_iff] at hodd ⊢
    omega
  rcases hparity with h₁ | h₂
  · exact ⟨E.start, E.walk.append p.reverse,
      E.isCycle_append hlen p.reverse hp.reverse hpS, h₁,
      e, f, hef, E.isChord_append p.reverse hpS he heEnds,
      E.isChord_append p.reverse hpS hf hfEnds⟩
  · exact ⟨E.start, E.walk.append q,
      E.isCycle_append hlen q hq hqS, h₂,
      e, f, hef, E.isChord_append q hqS he heEnds,
      E.isChord_append q hqS hf hfEnds⟩

/-- In a graph with no odd doubly-chorded cycle, an ear of an odd cycle has
at most one chord other than the possible edge between its endpoints. -/
theorem chords_eq_of_no_odd_two_chords
    {z : V} (C : G.Walk z z) (hC : C.IsCycle) (hodd : Odd C.length)
    (hno : ¬ HasOddCycleWithTwoChords G)
    (E : Ear G {x | x ∈ C.support}) (hlen : 2 ≤ E.walk.length)
    {e f : Sym2 V} (he : E.walk.IsChord e) (hf : E.walk.IsChord f)
    (heEnds : e ≠ s(E.start, E.finish)) (hfEnds : f ≠ s(E.start, E.finish)) :
    e = f := by
  by_contra hef
  exact hno (hasOddCycleWithTwoChords_of_two_chords C hC hodd E hlen
    hef he hf heEnds hfEnds)

end Ear

/-! ## Lassos

A lasso consists of a stem and a cycle which meets the stem only at its
terminal vertex.  Only the initial vertex of the stem may belong to the
attachment set.  We allow a zero-length stem, so a cycle meeting the
attachment set once is a lasso as well.  This includes the case of a closing
edge back to the initial attachment vertex in the maximality argument.
-/

structure AttachmentStem {V : Type u} (G : SimpleGraph V) (S : Set V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  start_mem : start ∈ S
  only_start : ∀ x ∈ walk.support, x ∈ S → x = start

structure AttachmentLasso {V : Type u} (G : SimpleGraph V) (S : Set V) where
  stem : AttachmentStem G S
  cycle : G.Walk stem.finish stem.finish
  isCycle : cycle.IsCycle
  cycle_only_start : ∀ x ∈ cycle.support, x ∈ S → x = stem.start
  intersection : ∀ x ∈ stem.walk.support, x ∈ cycle.support → x = stem.finish

namespace AttachmentLasso

variable {V : Type u} {G : SimpleGraph V} {S : Set V}

def length (L : AttachmentLasso G S) : ℕ := L.stem.walk.length + L.cycle.length

/-- Delete the last cycle edge to open a lasso into an attachment path. -/
def openPath (L : AttachmentLasso G S) : AttachmentPath G S where
  start := L.stem.start
  finish := L.cycle.penultimate
  walk := L.stem.walk.append L.cycle.dropLast
  isPath := Erdos1105.isPath_append_of_inter_eq_end L.stem.isPath
    L.isCycle.isPath_dropLast (by
      intro x hxstem hxcycle
      apply L.intersection x hxstem
      rw [Walk.support_dropLast L.isCycle.not_nil] at hxcycle
      exact List.dropLast_subset _ hxcycle)
  start_mem := L.stem.start_mem
  finish_notMem := by
    intro hvS
    have hv := L.cycle.getVert_mem_support (L.cycle.length - 1)
    have hvroot := L.cycle_only_start L.cycle.penultimate hv hvS
    have hrootcycle : L.stem.start ∈ L.cycle.support := hvroot ▸ hv
    have hrootbranch := L.intersection L.stem.start L.stem.walk.start_mem_support hrootcycle
    exact (Walk.adj_penultimate L.isCycle.not_nil).ne (hvroot.trans hrootbranch)
  only_start := by
    intro x hx hxS
    rw [Walk.support_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact L.stem.only_start x hx hxS
    · have hx' : x ∈ L.cycle.dropLast.support := List.tail_subset _ hx
      rw [Walk.support_dropLast L.isCycle.not_nil] at hx'
      exact L.cycle_only_start x (List.dropLast_subset _ hx') hxS

theorem openPath_length_add_one (L : AttachmentLasso G S) :
    L.openPath.walk.length + 1 = L.length := by
  have h := Walk.length_dropLast_add_one L.isCycle.not_nil
  simp only [openPath, Walk.length_append, length]
  omega

/-- Opening a lasso retains all of its vertices. -/
theorem openPath_support (L : AttachmentLasso G S) (x : V) :
    x ∈ L.openPath.walk.support ↔ x ∈ L.stem.walk.support ∨ x ∈ L.cycle.support := by
  have hcycle : x ∈ L.cycle.support ↔ x ∈ L.cycle.dropLast.support := by
    rw [← Walk.support_dropLast_concat L.isCycle.not_nil]
    simp only [List.mem_append, List.mem_singleton]
    exact or_iff_left_of_imp (fun h ↦ h.symm ▸ L.cycle.dropLast.start_mem_support)
  constructor
  · intro hx
    change x ∈ (L.stem.walk.append L.cycle.dropLast).support at hx
    rw [Walk.support_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hcycle.mpr (List.tail_subset _ hx))
  · rintro (hx | hx)
    · change x ∈ (L.stem.walk.append L.cycle.dropLast).support
      rw [Walk.support_append]
      exact List.mem_append_left _ hx
    · have hx' := hcycle.mp hx
      rcases L.cycle.dropLast.mem_support_iff.mp hx' with hxstart | hxtail
      · change x ∈ (L.stem.walk.append L.cycle.dropLast).support
        rw [Walk.support_append]
        exact List.mem_append_left _ (hxstart.symm ▸ L.stem.walk.end_mem_support)
      · change x ∈ (L.stem.walk.append L.cycle.dropLast).support
        rw [Walk.support_append]
        exact List.mem_append_right _ hxtail

/-- Reversing the cycle preserves the stem and the length of a lasso. -/
def reverseCycle (L : AttachmentLasso G S) : AttachmentLasso G S where
  stem := L.stem
  cycle := L.cycle.reverse
  isCycle := L.isCycle.reverse
  cycle_only_start := by simpa using L.cycle_only_start
  intersection := by simpa using L.intersection

@[simp] theorem reverseCycle_length (L : AttachmentLasso G S) :
    L.reverseCycle.length = L.length := by simp [reverseCycle, length]

/-- The lasso length is bounded by one more than the longest attachment
path length, since opening it deletes exactly one edge. -/
theorem length_le_of_longest (L : AttachmentLasso G S) (P : AttachmentPath G S)
    (hmax : ∀ Q : AttachmentPath G S, Q.walk.length ≤ P.walk.length) :
    L.length ≤ P.walk.length + 1 := by
  have hle := hmax L.openPath
  have heq := L.openPath_length_add_one
  omega

end AttachmentLasso

namespace AttachmentPath

variable {V : Type u} {G : SimpleGraph V} {S : Set V}

/-- A chord from the terminal vertex to an internal vertex turns an
attachment path into a lasso, without losing any vertex. -/
noncomputable def toLasso [DecidableEq V] (P : AttachmentPath G S) {r : V}
    (hr : r ∈ P.walk.support)
    (hfr : G.Adj P.finish r) (hedge : s(P.finish, r) ∉ P.walk.edges) :
    AttachmentLasso G S := by
  let p := P.walk.takeUntil r hr
  let q := P.walk.dropUntil r hr
  have hsplit : (p.append q).IsPath := by simpa [p, q] using P.isPath
  have hmeet : ∀ x ∈ p.support, x ∈ q.support → x = r := by
    intro x hxp hxq
    rcases q.mem_support_iff.mp hxq with hx | hx
    · exact hx
    · have hn := hsplit.support_nodup
      rw [Walk.support_append, List.nodup_append'] at hn
      exact (hn.2.2 hxp hx).elim
  let B : AttachmentStem G S :=
    { start := P.start
      finish := r
      walk := p
      isPath := P.isPath.takeUntil hr
      start_mem := P.start_mem
      only_start := fun x hx hxS ↦
        P.only_start x (P.walk.support_takeUntil_subset_support hr hx) hxS }
  let C : G.Walk r r := Walk.cons hfr.symm q.reverse
  have hC : C.IsCycle := by
    apply (Walk.cons_isCycle_iff q.reverse hfr.symm).mpr
    refine ⟨(P.isPath.dropUntil hr).reverse, ?_⟩
    intro he
    apply hedge
    apply P.walk.edges_dropUntil_subset_edges hr
    simpa [q, Walk.edges_reverse, Sym2.eq_swap] using he
  have hCmem (x : V) : x ∈ C.support ↔ x ∈ q.support := by
    simp only [C, Walk.support_cons, List.mem_cons, Walk.support_reverse, List.mem_reverse]
    exact or_iff_right_of_imp (fun h ↦ h.symm ▸ q.start_mem_support)
  refine ⟨B, C, hC, ?_, ?_⟩
  · intro x hx hxS
    have hxq := (hCmem x).mp hx
    have hxP := P.walk.support_dropUntil_subset_support hr hxq
    exact P.only_start x hxP hxS
  · intro x hxp hxC
    exact hmeet x hxp ((hCmem x).mp hxC)

theorem toLasso_length [DecidableEq V] (P : AttachmentPath G S) {r : V}
    (hr : r ∈ P.walk.support)
    (hfr : G.Adj P.finish r) (hedge : s(P.finish, r) ∉ P.walk.edges) :
    (P.toLasso hr hfr hedge).length = P.walk.length + 1 := by
  change (P.walk.takeUntil r hr).length +
    (Walk.cons hfr.symm (P.walk.dropUntil r hr).reverse).length = _
  have h := congrArg Walk.length (P.walk.take_spec hr)
  simp only [Walk.length_append] at h
  simp only [Walk.length_cons, Walk.length_reverse]
  omega

theorem toLasso_cycle_length [DecidableEq V] (P : AttachmentPath G S) {r : V}
    (hr : r ∈ P.walk.support)
    (hfr : G.Adj P.finish r) (hedge : s(P.finish, r) ∉ P.walk.edges) :
    (P.toLasso hr hfr hedge).cycle.length =
      (P.walk.dropUntil r hr).length + 1 := by
  change (Walk.cons hfr.symm (P.walk.dropUntil r hr).reverse).length = _
  simp

/-- If no ear realizes the desired length, a longest attachment path whose
terminal degree is at least three extends to a lasso of length `d+1`.
The extra closing edge is chosen away from the start and the preceding
vertex, so the lasso cycle does not contain the attachment vertex. -/
theorem exists_lasso_of_no_long_ear [Fintype V] [DecidableRel G.Adj]
    (P : AttachmentPath G S)
    (hmax : ∀ Q : AttachmentPath G S, Q.walk.length ≤ P.walk.length)
    (hno : ∀ Q : Ear G S, Q.walk.length ≠ P.walk.length + 1)
    (hdegree : 3 ≤ G.degree P.finish) :
    ∃ L : AttachmentLasso G S, L.length = P.walk.length + 1 := by
  classical
  have hsmall : ({P.start, P.walk.penultimate} : Finset V).card <
      (G.neighborFinset P.finish).card := by
    have hpair : ({P.start, P.walk.penultimate} : Finset V).card ≤ 2 := by
      simpa using Finset.card_insert_le P.start ({P.walk.penultimate} : Finset V)
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨r, hrN, hravoid⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hfr : G.Adj P.finish r := by simpa using hrN
  have hrstart : r ≠ P.start := by
    intro hr
    exact hravoid (by simp [hr])
  have hrprev : r ≠ P.walk.penultimate := by
    intro hr
    exact hravoid (by simp [hr])
  have hr := P.neighbor_mem_of_longest_of_no_long_ear hmax hno hfr
  have hedge : s(P.finish, r) ∉ P.walk.edges := by
    intro he
    exact hrprev (P.isPath.eq_penultimate_of_mem_edges he)
  exact ⟨P.toLasso hr hfr hedge, P.toLasso_length hr hfr hedge⟩

end AttachmentPath

namespace AttachmentLasso

variable {V : Type u} {G : SimpleGraph V} {S : Set V}

/-- Among lassos of a fixed total length, a finite graph has one with a
longest cycle.  This is Voss's second maximality choice. -/
theorem exists_maximum_cycle (L₀ : AttachmentLasso G S) :
    ∃ L : AttachmentLasso G S, L.length = L₀.length ∧
      ∀ K : AttachmentLasso G S, K.length = L₀.length →
        K.cycle.length ≤ L.cycle.length := by
  let lengths : Set ℕ := {n | ∃ L : AttachmentLasso G S,
    L.length = L₀.length ∧ L.cycle.length = n}
  have hfinite : lengths.Finite :=
    (Set.finite_le_nat L₀.length).subset (by
      rintro n ⟨L, htotal, rfl⟩
      change L.cycle.length ≤ L₀.length
      rw [← htotal]
      exact Nat.le_add_left _ _)
  obtain ⟨n, ⟨⟨L, hL, rfl⟩, hmax⟩⟩ :=
    hfinite.exists_maximal ⟨L₀.cycle.length, L₀, rfl, rfl⟩
  refine ⟨L, hL, fun K hK ↦ ?_⟩
  by_cases hle : K.cycle.length ≤ L.cycle.length
  · exact hle
  · exact hmax ⟨K, hK, rfl⟩ (Nat.le_of_lt (Nat.lt_of_not_ge hle))

/-- At the terminal vertex of an opened maximal lasso, every neighbor lies
on the lasso cycle.  A neighbor earlier on the stem would close a longer
cycle without changing the total length of the lasso. -/
theorem neighbor_mem_cycle_of_maximal (L : AttachmentLasso G S)
    (hmaxPath : ∀ Q : AttachmentPath G S, Q.walk.length ≤ L.openPath.walk.length)
    (hnoEar : ∀ E : Ear G S, E.walk.length ≠ L.length)
    (hmaxCycle : ∀ K : AttachmentLasso G S, K.length = L.length →
      K.cycle.length ≤ L.cycle.length)
    {v : V} (hadj : G.Adj L.cycle.penultimate v) : v ∈ L.cycle.support := by
  classical
  let P := L.openPath
  have hPlen : P.walk.length + 1 = L.length := L.openPath_length_add_one
  have hvP : v ∈ P.walk.support :=
    P.neighbor_mem_of_longest_of_no_long_ear hmaxPath (by
      intro E hE
      apply hnoEar E
      exact hE.trans hPlen) hadj
  by_contra hvC
  have hvStem : v ∈ L.stem.walk.support :=
    ((L.openPath_support v).mp hvP).resolve_right hvC
  have hvBranch : v ≠ L.stem.finish := by
    intro h
    exact hvC (h.symm ▸ L.cycle.start_mem_support)
  have hfinishC : P.finish ∈ L.cycle.support := L.cycle.getVert_mem_support _
  have hfinishStem : P.finish ∉ L.stem.walk.support := by
    intro h
    have heq := L.intersection P.finish h hfinishC
    exact (Walk.adj_penultimate L.isCycle.not_nil).ne heq
  have hedge : s(P.finish, v) ∉ P.walk.edges := by
    intro he
    change s(P.finish, v) ∈ (L.stem.walk.append L.cycle.dropLast).edges at he
    rw [Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact hfinishStem (L.stem.walk.fst_mem_support_of_mem_edges he)
    · have hv := L.cycle.dropLast.snd_mem_support_of_mem_edges he
      rw [Walk.support_dropLast L.isCycle.not_nil] at hv
      exact hvC (List.dropLast_subset _ hv)
  let K := P.toLasso hvP hadj hedge
  have hKlen : K.length = L.length :=
    (P.toLasso_length hvP hadj hedge).trans hPlen
  have hKmax : K.cycle.length ≤ L.cycle.length := hmaxCycle K hKlen
  have hKcycle : K.cycle.length = (P.walk.dropUntil v hvP).length + 1 :=
    P.toLasso_cycle_length hvP hadj hedge
  have htake : (P.walk.takeUntil v hvP).length =
      (L.stem.walk.takeUntil v hvStem).length := by
    change ((L.stem.walk.append L.cycle.dropLast).takeUntil v hvP).length = _
    rw [Walk.takeUntil_append_of_mem_left L.stem.walk L.cycle.dropLast hvStem]
  have htakeLt : (L.stem.walk.takeUntil v hvStem).length < L.stem.walk.length :=
    L.stem.walk.length_takeUntil_lt_length hvStem hvBranch
  have hsplit := congrArg Walk.length (P.walk.take_spec hvP)
  simp only [Walk.length_append] at hsplit
  have hlenDef : L.length = L.stem.walk.length + L.cycle.length := rfl
  omega

end AttachmentLasso

namespace PathRotation

variable {V : Type u} {G : SimpleGraph V} {a b : V}

/-- Rotate a path through an edge from an earlier vertex to its terminal
vertex: keep the prefix, use that edge, and traverse the remaining suffix
backwards. -/
def rotate (p : G.Walk a b) (j : ℕ) (h : G.Adj (p.getVert j) b) :
    G.Walk a (p.getVert (j + 1)) :=
  (p.take j).append (Walk.cons h (p.drop (j + 1)).reverse)

theorem isPath (p : G.Walk a b) (hp : p.IsPath) (j : ℕ)
    (hj : j < p.length) (h : G.Adj (p.getVert j) b) : (rotate p j h).IsPath := by
  have hdisj := Erdos1105.path_prefix_suffix_disjoint p hp
    (Nat.lt_succ_self j) (show j + 1 ≤ p.length by omega)
  apply Walk.IsPath.mk'
  simp only [rotate, Walk.support_append, Walk.support_cons, List.tail_cons]
  rw [List.nodup_append']
  refine ⟨(hp.take j).support_nodup, (hp.drop (j + 1)).reverse.support_nodup, ?_⟩
  simpa only [Walk.support_reverse, List.disjoint_reverse_right] using hdisj

theorem length_eq (p : G.Walk a b) (j : ℕ) (hj : j < p.length)
    (h : G.Adj (p.getVert j) b) : (rotate p j h).length = p.length := by
  simp only [rotate, Walk.length_append, Walk.length_cons, Walk.length_reverse,
    Walk.take_length, Walk.drop_length]
  omega

theorem mem_support_iff (p : G.Walk a b) (j : ℕ) (hj : j < p.length)
    (h : G.Adj (p.getVert j) b) (x : V) :
    x ∈ (rotate p j h).support ↔ x ∈ p.support := by
  simp only [rotate, Walk.support_append, Walk.support_cons, List.tail_cons,
    List.mem_append, Walk.support_reverse, List.mem_reverse,
    Walk.support_take, Walk.drop_support_eq_support_drop_min]
  rw [Nat.min_eq_left (show j + 1 ≤ p.length by omega)]
  rw [← List.mem_append, List.take_append_drop]

end PathRotation

namespace AttachmentLasso

variable {V : Type u} {G : SimpleGraph V} {S : Set V}

/-- A simple traversal of all cycle vertices, beginning at the branch
vertex.  It can use a cycle chord as a path edge. -/
structure Traversal (L : AttachmentLasso G S) where
  finish : V
  walk : G.Walk L.stem.finish finish
  isPath : walk.IsPath
  support_iff : ∀ x, x ∈ walk.support ↔ x ∈ L.cycle.support
  length_add_one : walk.length + 1 = L.cycle.length

namespace Traversal

variable {L : AttachmentLasso G S}

theorem finish_ne_branch (T : Traversal L) : T.finish ≠ L.stem.finish := by
  intro h
  have hn : T.walk.Nil := T.isPath.nil_iff_eq.mpr h.symm
  have hz : T.walk.length = 0 := Walk.length_eq_zero_iff.mpr hn
  have hthree := L.isCycle.three_le_length
  have hlen := T.length_add_one
  omega

/-- Prepending the lasso stem to a cycle traversal gives an attachment
path. -/
def toPath (T : Traversal L) : AttachmentPath G S where
  start := L.stem.start
  finish := T.finish
  walk := L.stem.walk.append T.walk
  isPath := Erdos1105.isPath_append_of_inter_eq_end L.stem.isPath T.isPath
    (fun x hx hxT ↦ L.intersection x hx ((T.support_iff x).mp hxT))
  start_mem := L.stem.start_mem
  finish_notMem := by
    intro hfS
    have hfC : T.finish ∈ L.cycle.support := (T.support_iff _).mp T.walk.end_mem_support
    have hfroot := L.cycle_only_start T.finish hfC hfS
    have hrootC : L.stem.start ∈ L.cycle.support := hfroot ▸ hfC
    have hrootbranch := L.intersection L.stem.start L.stem.walk.start_mem_support hrootC
    exact T.finish_ne_branch (hfroot.trans hrootbranch)
  only_start := by
    intro x hx hxS
    rw [Walk.support_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact L.stem.only_start x hx hxS
    · exact L.cycle_only_start x ((T.support_iff x).mp (List.tail_subset _ hx)) hxS

theorem toPath_length_add_one (T : Traversal L) :
    T.toPath.walk.length + 1 = L.length := by
  have h := T.length_add_one
  simp only [toPath, Walk.length_append, length]
  omega

theorem toPath_support (T : Traversal L) (x : V) :
    x ∈ T.toPath.walk.support ↔ x ∈ L.stem.walk.support ∨ x ∈ L.cycle.support := by
  change x ∈ (L.stem.walk.append T.walk).support ↔ _
  rw [Walk.support_append, List.mem_append]
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr ((T.support_iff x).mp (List.tail_subset _ hx))
  · rintro (hx | hx)
    · exact Or.inl hx
    · rcases T.walk.mem_support_iff.mp ((T.support_iff x).mpr hx) with hx | hx
      · exact Or.inl (hx.symm ▸ L.stem.walk.end_mem_support)
      · exact Or.inr hx

/-- The predecessor obtained by opening a cycle is a traversal. -/
def dropLast (L : AttachmentLasso G S) : Traversal L where
  finish := L.cycle.penultimate
  walk := L.cycle.dropLast
  isPath := L.isCycle.isPath_dropLast
  support_iff := by
    intro x
    rw [← Walk.support_dropLast_concat L.isCycle.not_nil]
    simp only [List.mem_append, List.mem_singleton]
    exact (or_iff_left_of_imp
      (fun h ↦ h.symm ▸ L.cycle.dropLast.start_mem_support)).symm
  length_add_one := Walk.length_dropLast_add_one L.isCycle.not_nil

/-- Rotate a traversal through an edge from its terminal vertex. -/
def rotate (T : Traversal L) (j : ℕ) (hj : j < T.walk.length)
    (h : G.Adj (T.walk.getVert j) T.finish) : Traversal L where
  finish := T.walk.getVert (j + 1)
  walk := PathRotation.rotate T.walk j h
  isPath := PathRotation.isPath T.walk T.isPath j hj h
  support_iff := fun x ↦ (PathRotation.mem_support_iff T.walk j hj h x).trans (T.support_iff x)
  length_add_one := by
    rw [PathRotation.length_eq T.walk j hj h]
    exact T.length_add_one

/-- The maximal-cycle argument applies to every traversal, including a
traversal obtained by a chord rotation. -/
theorem neighbor_mem_cycle_of_maximal (T : Traversal L)
    (hmaxPath : ∀ Q : AttachmentPath G S, Q.walk.length ≤ T.toPath.walk.length)
    (hnoEar : ∀ E : Ear G S, E.walk.length ≠ L.length)
    (hmaxCycle : ∀ K : AttachmentLasso G S, K.length = L.length →
      K.cycle.length ≤ L.cycle.length)
    {v : V} (hadj : G.Adj T.finish v) : v ∈ L.cycle.support := by
  classical
  let P := T.toPath
  have hPlen : P.walk.length + 1 = L.length := T.toPath_length_add_one
  have hvP : v ∈ P.walk.support :=
    P.neighbor_mem_of_longest_of_no_long_ear hmaxPath (by
      intro E hE
      exact hnoEar E (hE.trans hPlen)) hadj
  by_contra hvC
  have hvStem : v ∈ L.stem.walk.support :=
    ((T.toPath_support v).mp hvP).resolve_right hvC
  have hvBranch : v ≠ L.stem.finish := by
    intro h
    exact hvC (h.symm ▸ L.cycle.start_mem_support)
  have hfinishC : P.finish ∈ L.cycle.support := (T.support_iff _).mp T.walk.end_mem_support
  have hfinishStem : P.finish ∉ L.stem.walk.support := by
    intro h
    exact T.finish_ne_branch (L.intersection P.finish h hfinishC)
  have hedge : s(P.finish, v) ∉ P.walk.edges := by
    intro he
    change s(P.finish, v) ∈ (L.stem.walk.append T.walk).edges at he
    rw [Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact hfinishStem (L.stem.walk.fst_mem_support_of_mem_edges he)
    · exact hvC ((T.support_iff v).mp (T.walk.snd_mem_support_of_mem_edges he))
  let K := P.toLasso hvP hadj hedge
  have hKlen : K.length = L.length :=
    (P.toLasso_length hvP hadj hedge).trans hPlen
  have hKmax : K.cycle.length ≤ L.cycle.length := hmaxCycle K hKlen
  have hKcycle : K.cycle.length = (P.walk.dropUntil v hvP).length + 1 :=
    P.toLasso_cycle_length hvP hadj hedge
  have htake : (P.walk.takeUntil v hvP).length =
      (L.stem.walk.takeUntil v hvStem).length := by
    change ((L.stem.walk.append T.walk).takeUntil v hvP).length = _
    rw [Walk.takeUntil_append_of_mem_left L.stem.walk T.walk hvStem]
  have htakeLt : (L.stem.walk.takeUntil v hvStem).length < L.stem.walk.length :=
    L.stem.walk.length_takeUntil_lt_length hvStem hvBranch
  have hsplit := congrArg Walk.length (P.walk.take_spec hvP)
  simp only [Walk.length_append] at hsplit
  have hlenDef : L.length = L.stem.walk.length + L.cycle.length := rfl
  omega

end Traversal

end AttachmentLasso

/-! ## Extracting a cycle chord from a third neighbor -/

theorem cycle_edge_at_base {V : Type u} {G : SimpleGraph V} {z w : V}
    (C : G.Walk z z) (hC : C.IsCycle) (he : s(z, w) ∈ C.edges) :
    w = C.snd ∨ w = C.penultimate := by
  have htail : ¬C.tail.Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_tail]
    have hlen := hC.three_le_length
    omega
  have hpen : C.penultimate = C.tail.penultimate := by
    calc
      C.penultimate = (Walk.cons (C.adj_snd hC.not_nil) C.tail).penultimate := by
        rw [C.cons_tail_eq hC.not_nil]
      _ = C.tail.penultimate := Walk.penultimate_cons_of_not_nil _ _ htail
  rw [← C.cons_tail_eq hC.not_nil, Walk.edges_cons, List.mem_cons] at he
  rcases he with he | he
  · exact Or.inl ((Sym2.mkEmbedding z).injective he)
  · exact Or.inr ((hC.isPath_tail.eq_penultimate_of_mem_edges he).trans hpen.symm)

/-- If a cycle vertex has at least three neighbors and all of them lie on
the cycle, one of its incident edges is a cycle chord. -/
theorem exists_chord_at_of_three_le_degree {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {z v : V}
    (C : G.Walk z z) (hC : C.IsCycle) (hv : v ∈ C.support)
    (hdegree : 3 ≤ G.degree v)
    (hneighbors : ∀ w, G.Adj v w → w ∈ C.support) :
    ∃ w : V, C.IsChord s(v, w) := by
  classical
  let R := C.rotate v hv
  have hR : R.IsCycle := hC.rotate hv
  have hsmall : ({R.snd, R.penultimate} : Finset V).card <
      (G.neighborFinset v).card := by
    have hpair : ({R.snd, R.penultimate} : Finset V).card ≤ 2 := by
      simpa using Finset.card_insert_le R.snd ({R.penultimate} : Finset V)
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w, hwN, hwavoid⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hvw : G.Adj v w := by simpa using hwN
  refine ⟨w, hvw, ?_, hv, hneighbors w hvw⟩
  intro he
  have heR : s(v, w) ∈ R.edges := (C.rotate_edges v hv).mem_iff.mpr he
  rcases cycle_edge_at_base R hR heR with hw | hw
  · exact hwavoid (by simp [hw])
  · exact hwavoid (by simp [hw])

namespace AttachmentLasso.Traversal

variable {V : Type u} {G : SimpleGraph V} {S : Set V} {L : AttachmentLasso G S}

/-- Open the cycle in the other direction, keeping the original lasso as
the ambient object. -/
def reverseDropLast (L : AttachmentLasso G S) : Traversal L where
  finish := L.cycle.reverse.penultimate
  walk := L.cycle.reverse.dropLast
  isPath := L.isCycle.reverse.isPath_dropLast
  support_iff := by
    intro x
    have h := (dropLast L.reverseCycle).support_iff x
    simpa [dropLast, AttachmentLasso.reverseCycle] using h
  length_add_one := by
    simpa using Walk.length_dropLast_add_one L.isCycle.reverse.not_nil

/-- In a longest lasso with a longest possible cycle, the endpoint of any
cycle traversal has a chord on the original cycle. -/
theorem exists_chord_at_finish [Fintype V] [DecidableRel G.Adj]
    (T : Traversal L)
    (hdegree : ∀ v ∉ S, 3 ≤ G.degree v)
    (hmaxPath : ∀ Q : AttachmentPath G S, Q.walk.length + 1 ≤ L.length)
    (hnoEar : ∀ E : Ear G S, E.walk.length ≠ L.length)
    (hmaxCycle : ∀ K : AttachmentLasso G S, K.length = L.length →
      K.cycle.length ≤ L.cycle.length) :
    ∃ w : V, L.cycle.IsChord s(T.finish, w) := by
  apply exists_chord_at_of_three_le_degree L.cycle L.isCycle
    ((T.support_iff T.finish).mp T.walk.end_mem_support)
    (hdegree T.finish T.toPath.finish_notMem)
  intro w hw
  apply T.neighbor_mem_cycle_of_maximal ?_ hnoEar hmaxCycle hw
  intro Q
  have hQ := hmaxPath Q
  have hT := T.toPath_length_add_one
  omega

end AttachmentLasso.Traversal

namespace AttachmentLasso

variable {V : Type u} {G : SimpleGraph V} {S : Set V}

/-- The three-chord configuration in Voss's lasso argument, indexed along
the cycle opened at its branch vertex.  The first chord joins the last
vertex to position `j`; the third is incident with position `j+1`. -/
theorem exists_three_chord_configuration [Fintype V] [DecidableRel G.Adj]
    (L : AttachmentLasso G S)
    (hdegree : ∀ v ∉ S, 3 ≤ G.degree v)
    (hmaxPath : ∀ Q : AttachmentPath G S, Q.walk.length + 1 ≤ L.length)
    (hnoEar : ∀ E : Ear G S, E.walk.length ≠ L.length)
    (hmaxCycle : ∀ K : AttachmentLasso G S, K.length = L.length →
      K.cycle.length ≤ L.cycle.length) :
    ∃ j k l : ℕ, 1 ≤ j ∧ j + 1 < L.cycle.dropLast.length ∧
      k ≤ L.cycle.dropLast.length ∧ l ≤ L.cycle.dropLast.length ∧
      L.cycle.IsChord s(L.cycle.penultimate, L.cycle.dropLast.getVert j) ∧
      L.cycle.IsChord s(L.cycle.snd, L.cycle.dropLast.getVert k) ∧
      L.cycle.IsChord s(L.cycle.dropLast.getVert (j + 1), L.cycle.dropLast.getVert l) := by
  classical
  let T := Traversal.dropLast L
  let p := L.cycle.dropLast
  obtain ⟨ybar, hy⟩ := T.exists_chord_at_finish hdegree hmaxPath hnoEar hmaxCycle
  change L.cycle.IsChord s(L.cycle.penultimate, ybar) at hy
  obtain ⟨hyadj, hyedge, _, hymem⟩ := Walk.isChord_sym2Mk.mp hy
  have hyP : ybar ∈ p.support := (T.support_iff ybar).mpr hymem
  obtain ⟨j, hjget, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp hyP
  have hjpos : 1 ≤ j := by
    by_contra h
    have hj0 : j = 0 := by omega
    have hyroot : ybar = L.stem.finish := by
      simpa [p, hj0] using hjget.symm
    apply hyedge
    rw [hyroot]
    exact L.cycle.mk_penultimate_end_mem_edges L.isCycle.not_nil
  have hjlt : j < p.length := by
    by_contra h
    have hjend : j = p.length := by omega
    have hyend : ybar = L.cycle.penultimate := by
      simpa [hjend] using hjget.symm
    exact hyadj.ne hyend.symm
  have hjgap : j + 1 < p.length := by
    by_contra h
    have hjend : j + 1 = p.length := by omega
    have heP : s(L.cycle.penultimate, ybar) ∈ p.edges := by
      rw [p.mk_mem_edges_iff_exists]
      refine ⟨j, hjlt, ?_⟩
      rw [hjget, hjend, Walk.getVert_length]
      exact Sym2.eq_swap
    apply hyedge
    change s(L.cycle.penultimate, ybar) ∈ (L.cycle.take (L.cycle.length - 1)).edges at heP
    rw [Walk.edges_take] at heP
    exact List.mem_of_mem_take heP
  have hrotate : G.Adj (T.walk.getVert j) T.finish := by
    change G.Adj (p.getVert j) L.cycle.penultimate
    rw [hjget]
    exact hyadj.symm
  let T' := T.rotate j hjlt hrotate
  obtain ⟨vbar, hv⟩ := T'.exists_chord_at_finish hdegree hmaxPath hnoEar hmaxCycle
  change L.cycle.IsChord s(p.getVert (j + 1), vbar) at hv
  have hvP : vbar ∈ p.support := (T.support_iff vbar).mpr hv.2.2.2
  obtain ⟨l, hlget, hlle⟩ := Walk.mem_support_iff_exists_getVert.mp hvP
  obtain ⟨zbar, hz⟩ := (Traversal.reverseDropLast L).exists_chord_at_finish
    hdegree hmaxPath hnoEar hmaxCycle
  have hz' : L.cycle.IsChord s(L.cycle.snd, zbar) := by
    simpa [Traversal.reverseDropLast] using hz
  have hzP : zbar ∈ p.support := (T.support_iff zbar).mpr hz'.2.2.2
  obtain ⟨k, hkget, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hzP
  refine ⟨j, k, l, hjpos, hjgap, hkle, hlle, ?_, ?_, ?_⟩
  · simpa [← hjget] using hy
  · simpa [← hkget] using hz'
  · simpa [← hlget] using hv

end AttachmentLasso

end Erdos1091.Voss
