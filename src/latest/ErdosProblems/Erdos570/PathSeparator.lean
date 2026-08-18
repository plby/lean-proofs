/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos79.Core
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# DFS separators in path-free graphs

The proof of Häggkvist's path--complete-bipartite Ramsey bound is a depth-first
search invariant.  This file develops the finite path-stack portion of that
argument independently of Ramsey coding.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The canonical coded path on `k` vertices. -/
def pathCode (k : ℕ) : GraphCode := ⟨k, SimpleGraph.pathGraph k⟩

@[simp] theorem pathCode_vertexCount (k : ℕ) :
    (pathCode k).vertexCount = k := rfl

@[simp] theorem pathCode_graph (k : ℕ) :
    (pathCode k).graph = SimpleGraph.pathGraph k := rfl

/-- A canonical finite-ordinal code for the complete bipartite graph with
part sizes `a` and `b`. -/
def completeBipartiteCode (a b : ℕ) : GraphCode :=
  ⟨a + b,
    (completeBipartiteGraph (Fin a) (Fin b)).map
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).toEmbedding⟩

@[simp] theorem completeBipartiteCode_vertexCount (a b : ℕ) :
    (completeBipartiteCode a b).vertexCount = a + b := rfl

/-- A nonempty DFS stack, stored as a simple walk whose first vertex is the
top of the stack. -/
structure PathStack {V : Type*} (G : SimpleGraph V) where
  first : V
  last : V
  walk : G.Walk first last
  isPath : walk.IsPath

namespace PathStack

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- The finite set of vertices currently on a path stack. -/
def verts (S : PathStack G) : Finset V := S.walk.support.toFinset

@[simp] theorem card_verts (S : PathStack G) :
    S.verts.card = S.walk.length + 1 := by
  rw [verts, List.toFinset_card_of_nodup S.isPath.support_nodup,
    S.walk.length_support]

@[simp] theorem first_mem_verts (S : PathStack G) : S.first ∈ S.verts := by
  simp [verts]

/-- A singleton path stack. -/
def singleton (v : V) : PathStack G where
  first := v
  last := v
  walk := .nil
  isPath := .nil

@[simp] theorem verts_singleton (v : V) :
    (singleton (G := G) v).verts = {v} := by
  simp [singleton, verts]

/-- Push a fresh neighbor onto the top of a path stack. -/
def push (S : PathStack G) (v : V) (h : G.Adj S.first v)
    (hv : v ∉ S.verts) : PathStack G where
  first := v
  last := S.last
  walk := S.walk.cons h.symm
  isPath := S.isPath.cons (by simpa [verts] using hv)

@[simp] theorem verts_push (S : PathStack G) (v : V) (h : G.Adj S.first v)
    (hv : v ∉ S.verts) :
    (S.push v h hv).verts = insert v S.verts := by
  simp [push, verts, SimpleGraph.Walk.support_cons]

@[simp] theorem card_verts_push (S : PathStack G) (v : V)
    (h : G.Adj S.first v) (hv : v ∉ S.verts) :
    (S.push v h hv).verts.card = S.verts.card + 1 := by
  rw [verts_push, Finset.card_insert_of_notMem hv]

/-- If `G` contains no `P_k`, every path stack has at most `k-1` vertices. -/
theorem card_verts_le_of_pathGraph_not_isContained {k : ℕ} (hk : 1 ≤ k)
    (S : PathStack G) (hfree : ¬SimpleGraph.pathGraph k ⊑ G) :
    S.verts.card ≤ k - 1 := by
  by_contra h
  have hlen : k - 1 ≤ S.walk.length := by
    rw [card_verts] at h
    omega
  let q := S.walk.take (k - 1)
  have hq : q.IsPath := S.isPath.take (k - 1)
  have hqLen : q.length = k - 1 := by
    change (S.walk.take (k - 1)).length = k - 1
    rw [SimpleGraph.Walk.take_length, min_eq_left hlen]
  apply hfree
  have hc := hq.isContained_pathGraph
  rw [hqLen, Nat.sub_add_cancel hk] at hc
  exact hc

/-- A path stack is either a singleton or can be popped, with its old top
removed from the vertex set. -/
theorem singleton_or_exists_pop (S : PathStack G) :
    S.verts = {S.first} ∨
      ∃ T : PathStack G,
        S.verts = insert S.first T.verts ∧ S.first ∉ T.verts := by
  rcases S with ⟨first, last, walk, hpath⟩
  cases walk with
  | nil =>
      left
      simp [verts]
  | @cons _ next last h p =>
      right
      let T : PathStack G :=
        { first := next
          last := last
          walk := p
          isPath := hpath.of_cons }
      refine ⟨T, ?_, ?_⟩
      · simp [verts, T, SimpleGraph.Walk.support_cons]
      · simpa [verts, T] using
          (SimpleGraph.Walk.cons_isPath_iff h p).mp hpath |>.2

end PathStack

/-- The vertices in an optional path stack. -/
def pathStackVerts {V : Type*} {G : SimpleGraph V} [DecidableEq V] :
    Option (PathStack G) → Finset V
  | none => ∅
  | some S => S.verts

@[simp] theorem pathStackVerts_none {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] : pathStackVerts (G := G) none = ∅ := rfl

@[simp] theorem pathStackVerts_some {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] (S : PathStack G) : pathStackVerts (some S) = S.verts := rfl

/-- The invariants of the processed/unseen/path-stack partition in depth-first
search. -/
structure DFSInvariant {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (S : Option (PathStack G)) : Prop where
  disjointAB : Disjoint A B
  disjointAS : Disjoint A (pathStackVerts S)
  disjointBS : Disjoint B (pathStackVerts S)
  noEdgeAB : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b
  card_eq : A.card + B.card + (pathStackVerts S).card = Fintype.card V

private theorem dfsSeparatorAux
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k n m : ℕ) (hk : 2 ≤ k)
    (hfree : ¬SimpleGraph.pathGraph k ⊑ G)
    (htotal : n + m + k - 2 ≤ Fintype.card V)
    (A B : Finset V) (S : Option (PathStack G))
    (hinv : DFSInvariant G A B S) (hAn : A.card ≤ n)
    (hstop : A.card < n ∨ (pathStackVerts S).card ≤ k - 2) :
    ∃ A' B' : Finset V, A'.card = n ∧ m ≤ B'.card ∧
      Disjoint A' B' ∧ ∀ a ∈ A', ∀ b ∈ B', ¬G.Adj a b := by
  have htotal' : n + m + (k - 2) ≤ Fintype.card V := by omega
  by_cases hdone : A.card = n
  · have hScard : (pathStackVerts S).card ≤ k - 2 :=
      hstop.resolve_left (by omega)
    refine ⟨A, B, hdone, ?_, hinv.disjointAB, hinv.noEdgeAB⟩
    have hc := hinv.card_eq
    omega
  have hAlt : A.card < n := Nat.lt_of_le_of_ne hAn hdone
  cases S with
  | none =>
      have hBne : B.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hB
        subst B
        have hc := hinv.card_eq
        simp only [pathStackVerts_none, Finset.card_empty, add_zero] at hc
        omega
      obtain ⟨v, hvB⟩ := hBne
      let B' := B.erase v
      let S' : Option (PathStack G) := some (PathStack.singleton (G := G) v)
      have hvA : v ∉ A := by
        exact fun hv ↦ Finset.disjoint_left.mp hinv.disjointAB hv hvB
      have hinv' : DFSInvariant G A B' S' := by
        constructor
        · exact hinv.disjointAB.mono_right (Finset.erase_subset _ _)
        · rw [Finset.disjoint_left]
          intro a ha hav
          simp only [S', pathStackVerts_some, PathStack.verts_singleton,
            Finset.mem_singleton] at hav
          exact hvA (hav ▸ ha)
        · rw [Finset.disjoint_left]
          intro b hb hbv
          simp only [S', pathStackVerts_some, PathStack.verts_singleton,
            Finset.mem_singleton] at hbv
          subst b
          exact Finset.notMem_erase v B hb
        · intro a ha b hb
          exact hinv.noEdgeAB a ha b (Finset.mem_of_mem_erase hb)
        · have hcard := Finset.card_erase_of_mem hvB
          have hc := hinv.card_eq
          simp only [pathStackVerts_none, Finset.card_empty, add_zero] at hc
          simp only [B', S', pathStackVerts_some, PathStack.verts_singleton,
            Finset.card_singleton]
          omega
      exact dfsSeparatorAux G k n m hk hfree htotal A B' S' hinv' hAn (.inl hAlt)
  | some T =>
      by_cases hext : ∃ v, v ∈ B ∧ G.Adj T.first v
      · obtain ⟨v, hvB, hvadj⟩ := hext
        have hvT : v ∉ T.verts := by
          exact fun hv ↦ Finset.disjoint_left.mp hinv.disjointBS hvB hv
        have hvA : v ∉ A := by
          exact fun hv ↦ Finset.disjoint_left.mp hinv.disjointAB hv hvB
        let B' := B.erase v
        let T' := T.push v hvadj hvT
        let S' : Option (PathStack G) := some T'
        have hinv' : DFSInvariant G A B' S' := by
          constructor
          · exact hinv.disjointAB.mono_right (Finset.erase_subset _ _)
          · rw [Finset.disjoint_left]
            intro a ha hav
            simp only [S', pathStackVerts_some, T', PathStack.verts_push,
              Finset.mem_insert] at hav
            rcases hav with rfl | hav
            · exact hvA ha
            · exact Finset.disjoint_left.mp hinv.disjointAS ha hav
          · rw [Finset.disjoint_left]
            intro b hb hbS
            simp only [S', pathStackVerts_some, T', PathStack.verts_push,
              Finset.mem_insert] at hbS
            rcases hbS with hbS | hbS
            · exact (Finset.mem_erase.mp hb).1 hbS
            · exact Finset.disjoint_left.mp hinv.disjointBS
                (Finset.mem_of_mem_erase hb) hbS
          · intro a ha b hb
            exact hinv.noEdgeAB a ha b (Finset.mem_of_mem_erase hb)
          · have hBerase := Finset.card_erase_of_mem hvB
            have hTpush := PathStack.card_verts_push T v hvadj hvT
            have hc := hinv.card_eq
            simp only [pathStackVerts_some] at hc
            change A.card + (B.erase v).card +
              (T.push v hvadj hvT).verts.card = Fintype.card V
            rw [hBerase, hTpush]
            have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨v, hvB⟩
            omega
        exact dfsSeparatorAux G k n m hk hfree htotal A B' S' hinv' hAn (.inl hAlt)
      · rcases T.singleton_or_exists_pop with hsingle | ⟨T', hpop, hfirst⟩
        · let A' := insert T.first A
          have hfirstA : T.first ∉ A := by
            intro h
            exact Finset.disjoint_left.mp hinv.disjointAS h
              (by simpa [hsingle] using T.first_mem_verts)
          have hfirstB : T.first ∉ B := by
            intro h
            exact Finset.disjoint_left.mp hinv.disjointBS h T.first_mem_verts
          have hinv' : DFSInvariant G A' B none := by
            constructor
            · rw [Finset.disjoint_left]
              intro a ha hb
              simp only [A', Finset.mem_insert] at ha
              rcases ha with rfl | ha
              · exact hfirstB hb
              · exact Finset.disjoint_left.mp hinv.disjointAB ha hb
            · simp
            · simp
            · intro a ha b hb
              simp only [A', Finset.mem_insert] at ha
              rcases ha with rfl | ha
              · exact fun hadj ↦ hext ⟨b, hb, hadj⟩
              · exact hinv.noEdgeAB a ha b hb
            · have hAinsert := Finset.card_insert_of_notMem hfirstA
              have hTcard : T.verts.card = 1 := by rw [hsingle, Finset.card_singleton]
              simp only [A', pathStackVerts_none, Finset.card_empty, add_zero]
              have hc := hinv.card_eq
              change A.card + B.card + T.verts.card = Fintype.card V at hc
              omega
          have hA'n : A'.card ≤ n := by
            rw [Finset.card_insert_of_notMem hfirstA]
            omega
          have hstop' : A'.card < n ∨ (pathStackVerts (none : Option (PathStack G))).card ≤ k - 2 := by
            by_cases h : A'.card < n
            · exact .inl h
            · exact .inr (by simp)
          exact dfsSeparatorAux G k n m hk hfree htotal A' B none hinv' hA'n hstop'
        · let A' := insert T.first A
          have hfirstA : T.first ∉ A := by
            intro h
            exact Finset.disjoint_left.mp hinv.disjointAS h T.first_mem_verts
          have hfirstB : T.first ∉ B := by
            intro h
            exact Finset.disjoint_left.mp hinv.disjointBS h T.first_mem_verts
          have hAT' : Disjoint A T'.verts := by
            apply hinv.disjointAS.mono_right
            intro z hz
            simp only [pathStackVerts_some]
            rw [hpop]
            exact Finset.mem_insert_of_mem hz
          have hBT' : Disjoint B T'.verts := by
            apply hinv.disjointBS.mono_right
            intro z hz
            simp only [pathStackVerts_some]
            rw [hpop]
            exact Finset.mem_insert_of_mem hz
          have hinv' : DFSInvariant G A' B (some T') := by
            constructor
            · rw [Finset.disjoint_left]
              intro a ha hb
              simp only [A', Finset.mem_insert] at ha
              rcases ha with rfl | ha
              · exact hfirstB hb
              · exact Finset.disjoint_left.mp hinv.disjointAB ha hb
            · rw [Finset.disjoint_left]
              intro a ha hz
              simp only [A', Finset.mem_insert] at ha
              rcases ha with rfl | ha
              · exact hfirst hz
              · exact Finset.disjoint_left.mp hAT' ha hz
            · exact hBT'
            · intro a ha b hb
              simp only [A', Finset.mem_insert] at ha
              rcases ha with rfl | ha
              · exact fun hadj ↦ hext ⟨b, hb, hadj⟩
              · exact hinv.noEdgeAB a ha b hb
            · have hAinsert := Finset.card_insert_of_notMem hfirstA
              have hTcard : T.verts.card = T'.verts.card + 1 := by
                rw [hpop, Finset.card_insert_of_notMem hfirst]
              change A'.card + B.card + T'.verts.card = Fintype.card V
              have hc := hinv.card_eq
              change A.card + B.card + T.verts.card = Fintype.card V at hc
              have hAcard : A'.card = A.card + 1 := by
                change (insert T.first A).card = A.card + 1
                rw [Finset.card_insert_of_notMem hfirstA]
              omega
          have hA'n : A'.card ≤ n := by
            change (insert T.first A).card ≤ n
            rw [Finset.card_insert_of_notMem hfirstA]
            omega
          have hTbound := T.card_verts_le_of_pathGraph_not_isContained
            (show 1 ≤ k by omega) hfree
          have hT'card : T'.verts.card + 1 = T.verts.card := by
            rw [hpop, Finset.card_insert_of_notMem hfirst]
          have hstop' : A'.card < n ∨
              (pathStackVerts (some T')).card ≤ k - 2 := by
            by_cases h : A'.card < n
            · exact .inl h
            · right
              simp only [pathStackVerts_some]
              omega
          exact dfsSeparatorAux G k n m hk hfree htotal A' B (some T')
            hinv' hA'n hstop'
termination_by 2 * B.card + (pathStackVerts S).card
decreasing_by
  · have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨v, hvB⟩
    simp_all only [pathStackVerts_some, PathStack.verts_singleton,
      Finset.card_singleton, pathStackVerts_none, Finset.card_empty,
      Finset.card_erase_of_mem]
    omega
  · have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨v, hvB⟩
    simp_all only [pathStackVerts_some, pathStackVerts_none,
      Finset.card_erase_of_mem, PathStack.card_verts_push]
    omega
  · simp_all only [pathStackVerts_none, Finset.card_empty,
      pathStackVerts_some, Finset.card_singleton]
    omega
  · simp_all only [pathStackVerts_some, pathStackVerts_none]
    omega

/-- DFS separation theorem.  A `P_k`-free graph on at least
`n + m + k - 2` vertices has disjoint `n`- and `m`-sets with no edge between
them. -/
theorem exists_anticomplete_finsets_of_pathGraph_not_isContained
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {k n m : ℕ} (hk : 2 ≤ k)
    (hcard : n + m + k - 2 ≤ Fintype.card V)
    (hfree : ¬SimpleGraph.pathGraph k ⊑ G) :
    ∃ A B : Finset V, A.card = n ∧ B.card = m ∧ Disjoint A B ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b := by
  let A₀ : Finset V := ∅
  let B₀ : Finset V := Finset.univ
  have hinv₀ : DFSInvariant G A₀ B₀ none := by
    constructor <;> simp [A₀, B₀]
  have hA₀ : A₀.card ≤ n := by simp [A₀]
  have hstop₀ : A₀.card < n ∨
      (pathStackVerts (none : Option (PathStack G))).card ≤ k - 2 := by
    by_cases hn : n = 0
    · right; simp
    · left; simp [A₀, Nat.pos_of_ne_zero hn]
  obtain ⟨A, B, hA, hmB, hAB, hno⟩ :=
    dfsSeparatorAux G k n m hk hfree hcard A₀ B₀ none hinv₀ hA₀ hstop₀
  obtain ⟨B', hB'B, hB'card⟩ := Finset.exists_subset_card_eq hmB
  refine ⟨A, B', hA, hB'card, hAB.mono_right hB'B, ?_⟩
  intro a ha b hb
  exact hno a ha b (hB'B hb)

/-- Häggkvist's path--complete-bipartite Ramsey bound, in exact-order
`RamseyAt` form. -/
theorem ramseyAt_path_completeBipartite {k a b : ℕ} (hk : 2 ≤ k) :
    RamseyAt (pathCode k) (completeBipartiteCode a b) (a + b + k - 2) := by
  classical
  intro C
  by_cases hpath : SimpleGraph.pathGraph k ⊑ C
  · exact .inl (by simpa [pathCode] using hpath)
  · right
    obtain ⟨A, B, hA, hB, hAB, hno⟩ :=
      exists_anticomplete_finsets_of_pathGraph_not_isContained C hk
        (n := a) (m := b) (by simp) hpath
    have hcomplete : completeBipartiteGraph (Fin a) (Fin b) ⊑ Cᶜ := by
      rw [SimpleGraph.completeBipartiteGraph_isContained_iff]
      refine ⟨A, B, by simpa using hA, by simpa using hB, ?_⟩
      intro x hx y hy
      rw [SimpleGraph.compl_adj]
      refine ⟨?_, hno x hx y hy⟩
      intro hxy
      exact Finset.disjoint_left.mp hAB hx (hxy ▸ hy)
    let e := SimpleGraph.Iso.map
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))
      (completeBipartiteGraph (Fin a) (Fin b))
    exact ⟨hcomplete.some.comp e.symm.toCopy⟩

theorem graphRamseyNumber_path_completeBipartite_le {k a b : ℕ} (hk : 2 ≤ k) :
    graphRamseyNumber (pathCode k) (completeBipartiteCode a b) ≤
      a + b + k - 2 :=
  graphRamseyNumber_le_of_ramseyAt (ramseyAt_path_completeBipartite hk)

end Erdos570
