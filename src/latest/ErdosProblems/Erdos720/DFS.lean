import ErdosProblems.Erdos720.Foundation
import Mathlib.Combinatorics.SimpleGraph.Hasse

open Finset
open scoped SimpleGraph

noncomputable section

namespace Erdos720

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The invariant of the usual depth-first-search stack. -/
def DFSInvariant (G : SimpleGraph V) (U : Finset V) (s : List V) (D : Finset V) : Prop :=
  s.Nodup ∧
  s.IsChain G.Adj ∧
  Disjoint U s.toFinset ∧
  Disjoint U D ∧
  Disjoint s.toFinset D ∧
  U ∪ s.toFinset ∪ D = univ ∧
  ∀ d ∈ D, ∀ u ∈ U, ¬ G.Adj d u

lemma dfsInvariant_initial (G : SimpleGraph V) :
    DFSInvariant G univ [] ∅ := by
  simp [DFSInvariant]

lemma dfsInvariant_push {G : SimpleGraph V} {U : Finset V} {s : List V} {D : Finset V}
    (h : DFSInvariant G U s D) {v : V} (hvU : v ∈ U)
    (hvchain : ∀ a, s.head? = some a → G.Adj v a) :
    DFSInvariant G (U.erase v) (v :: s) D := by
  rcases h with ⟨hsnodup, hschain, hUs, hUD, hsD, hcover, hno⟩
  have hvnotS : v ∉ s.toFinset := fun hvS ↦ Finset.disjoint_left.mp hUs hvU hvS
  have hvnotD : v ∉ D := fun hvD ↦ Finset.disjoint_left.mp hUD hvU hvD
  refine ⟨hsnodup.cons (by simpa using hvnotS), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases s with
    | nil => simp
    | cons a s =>
        simpa using ⟨hvchain a rfl, hschain⟩
  · rw [List.toFinset_cons]
    exact Finset.disjoint_left.mpr fun x hxU hxS ↦ by
      have hxne : x ≠ v := (Finset.mem_erase.mp hxU).1
      rcases Finset.mem_insert.mp hxS with rfl | hxS
      · exact hxne rfl
      · exact Finset.disjoint_left.mp hUs (Finset.mem_of_mem_erase hxU) hxS
  · exact hUD.mono_left (Finset.erase_subset _ _)
  · rw [List.toFinset_cons]
    exact Finset.disjoint_insert_left.mpr ⟨hvnotD, hsD⟩
  · rw [Finset.ext_iff] at hcover ⊢
    intro x
    specialize hcover x
    simp only [List.toFinset_cons, mem_union, mem_erase, mem_insert, mem_univ,
      iff_true] at hcover ⊢
    tauto
  · intro d hd u hu
    exact hno d hd u (Finset.mem_of_mem_erase hu)

lemma dfsInvariant_pop {G : SimpleGraph V} {U : Finset V} {a : V} {s : List V}
    {D : Finset V} (h : DFSInvariant G U (a :: s) D)
    (haU : ∀ u ∈ U, ¬ G.Adj a u) :
    DFSInvariant G U s (insert a D) := by
  rcases h with ⟨hasnodup, hchain, hUs, hUD, hsD, hcover, hno⟩
  have haD : a ∉ D := by
    have haS : a ∈ (a :: s).toFinset := by simp
    exact fun haD ↦ Finset.disjoint_left.mp hsD haS haD
  have haU' : a ∉ U := by
    have haS : a ∈ (a :: s).toFinset := by simp
    exact fun haUmem ↦ Finset.disjoint_left.mp hUs haUmem haS
  have haS : a ∉ s.toFinset := by
    simpa using (List.nodup_cons.mp hasnodup).1
  refine ⟨hasnodup.of_cons, hchain.of_cons, ?_, ?_, ?_, ?_, ?_⟩
  · exact hUs.mono_right (by simp)
  · exact Finset.disjoint_insert_right.mpr ⟨haU', hUD⟩
  · exact Finset.disjoint_insert_right.mpr ⟨haS,
      hsD.mono_left (by simp)⟩
  · rw [Finset.ext_iff] at hcover ⊢
    intro x
    specialize hcover x
    simp only [mem_union, List.toFinset_cons, mem_insert, mem_univ, iff_true]
      at hcover ⊢
    tauto
  · intro d hd u hu
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact haU u hu
    · exact hno d hd u hu

lemma dfsInvariant_card {G : SimpleGraph V} {U : Finset V} {s : List V} {D : Finset V}
    (h : DFSInvariant G U s D) :
    U.card + s.length + D.card = Fintype.card V := by
  rcases h with ⟨hsnodup, -, hUs, hUD, hsD, hcover, -⟩
  calc
    U.card + s.length + D.card = U.card + s.toFinset.card + D.card := by
      rw [List.toFinset_card_of_nodup hsnodup]
    _ = (U ∪ s.toFinset ∪ D).card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hUD, hsD⟩),
        Finset.card_union_of_disjoint hUs]
    _ = Fintype.card V := by simp [hcover]

lemma pathGraph_isContained_of_list {G : SimpleGraph V} {l : List V} {k : ℕ}
    (hk : 0 < k) (hl : k ≤ l.length) (hnodup : l.Nodup) (hchain : l.IsChain G.Adj) :
    pathGraph k ⊑ G := by
  let t := l.take k
  have htlen : t.length = k := by simp [t, hl]
  have htne : t ≠ [] := by
    intro h
    have : t.length = 0 := by simp [h]
    omega
  have htchain : t.IsChain G.Adj := hchain.take k
  let p := SimpleGraph.Walk.ofSupport t htne htchain
  have hp : p.IsPath := by
    have htnd : t.Nodup := by
      exact hnodup.take
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p] using htnd
  have hcontain := hp.isContained_pathGraph
  have hplen : p.length + 1 = k := by
    dsimp [p]
    rw [SimpleGraph.Walk.length_ofSupport, htlen]
    omega
  rw [hplen] at hcontain
  exact hcontain

lemma dfs_exists_finished_card (G : SimpleGraph V) (t : ℕ)
    (htV : t ≤ Fintype.card V) :
    ∃ U s D, DFSInvariant G U s D ∧ D.card = t := by
  classical
  let score (D : Finset V) (s : List V) := D.card * (Fintype.card V + 1) + s.length
  let bound := Fintype.card V * (Fintype.card V + 1) + Fintype.card V
  let Q : Finset ℕ := (Finset.range (bound + 1)).filter fun q ↦
    ∃ U s D, DFSInvariant G U s D ∧ D.card ≤ t ∧ q = score D s
  have hzeroQ : 0 ∈ Q := by
    simp only [Q, Finset.mem_filter, Finset.mem_range]
    refine ⟨by simp [bound], univ, [], ∅, dfsInvariant_initial G, by simp, ?_⟩
    simp [score]
  have hQne : Q.Nonempty := ⟨0, hzeroQ⟩
  let q := Q.max' hQne
  have hqQ : q ∈ Q := Finset.max'_mem Q hQne
  obtain ⟨U, s, D, hinv, hDt, hqscore⟩ := (Finset.mem_filter.mp hqQ).2
  refine ⟨U, s, D, hinv, ?_⟩
  apply le_antisymm hDt
  by_contra hnot
  have hDlt : D.card < t := by omega
  have hscore_le_bound (U' : Finset V) (s' : List V) (D' : Finset V)
      (hinv' : DFSInvariant G U' s' D') : score D' s' ≤ bound := by
    have hDcard : D'.card ≤ Fintype.card V := Finset.card_le_univ D'
    have hscard : s'.length ≤ Fintype.card V :=
      (List.Nodup.length_le_card hinv'.1).trans_eq (Finset.card_univ)
    dsimp [score, bound]
    exact (Nat.add_le_add
      (Nat.mul_le_mul_right (Fintype.card V + 1) hDcard) hscard)
  have hmax (q' : ℕ) (hq' : q' ∈ Q) : q' ≤ q := Finset.le_max' Q q' hq'
  cases hs : s with
  | nil =>
      have hUne : U.Nonempty := by
        by_contra hUempty
        have hUeq : U = ∅ := not_nonempty_iff_eq_empty.mp hUempty
        have hcard := dfsInvariant_card hinv
        simp [hs, hUeq] at hcard
        omega
      obtain ⟨v, hvU⟩ := hUne
      have hinv' : DFSInvariant G (U.erase v) [v] D := by
        simpa [hs] using dfsInvariant_push hinv hvU (by simp [hs])
      let q' := score D [v]
      have hq'Q : q' ∈ Q := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hscore_le_bound _ _ _ hinv')),
          U.erase v, [v], D, hinv', hDt, rfl⟩
      have hlt : q < q' := by simp [q', score, hs, hqscore]
      exact (not_lt_of_ge (hmax q' hq'Q)) hlt
  | cons a s' =>
      by_cases hex : ∃ v ∈ U, G.Adj a v
      · obtain ⟨v, hvU, hav⟩ := hex
        have hinv' : DFSInvariant G (U.erase v) (v :: a :: s') D := by
          simpa [hs] using dfsInvariant_push hinv hvU (by
            intro b hb
            have hab : a = b := by simpa [hs] using hb
            subst b
            exact hav.symm)
        let q' := score D (v :: a :: s')
        have hq'Q : q' ∈ Q := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hscore_le_bound _ _ _ hinv')),
            U.erase v, v :: a :: s', D, hinv', hDt, rfl⟩
        have hlt : q < q' := by simp [q', score, hs, hqscore]
        exact (not_lt_of_ge (hmax q' hq'Q)) hlt
      · have haU : ∀ u ∈ U, ¬ G.Adj a u := by
          intro u hu hau
          exact hex ⟨u, hu, hau⟩
        have hinv' : DFSInvariant G U s' (insert a D) := by
          simpa [hs] using dfsInvariant_pop (G := G) (U := U) (a := a) (s := s')
            (D := D) (by simpa [hs] using hinv) haU
        have haD : a ∉ D := by
          have hdisj := hinv.2.2.2.2.1
          exact fun ha ↦ Finset.disjoint_left.mp hdisj (by simp [hs]) ha
        have hcardD' : (insert a D).card ≤ t := by
          rw [Finset.card_insert_of_notMem haD]
          omega
        let q' := score (insert a D) s'
        have hq'Q : q' ∈ Q := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hscore_le_bound _ _ _ hinv')),
            U, s', insert a D, hinv', hcardD', rfl⟩
        have hVpos : 0 < Fintype.card V := lt_of_lt_of_le (by omega) htV
        have hlt : q < q' := by
          have hq_eq : q = D.card * (Fintype.card V + 1) + (s'.length + 1) := by
            simpa [hs, score] using hqscore
          dsimp [q', score]
          rw [Finset.card_insert_of_notMem haD]
          rw [hq_eq]
          simp only [Nat.add_mul, one_mul]
          omega
        exact (not_lt_of_ge (hmax q' hq'Q)) hlt

/-- A graph without a `k`-vertex path has two prescribed large anticomplete sets. -/
lemma exists_anticomplete_sets_of_path_free (G : SimpleGraph V) (t k : ℕ) (hk : 0 < k)
    (hsize : 2 * t + k ≤ Fintype.card V + 1)
    (hno : ¬ pathGraph k ⊑ G) :
    ∃ A B : Finset V, A.card = t ∧ B.card = t ∧ Disjoint A B ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
  classical
  have htV : t ≤ Fintype.card V := by omega
  obtain ⟨U, s, D, hinv, hDcard⟩ := dfs_exists_finished_card G t htV
  have hslt : s.length < k := by
    by_contra h
    exact hno (pathGraph_isContained_of_list hk (not_lt.mp h) hinv.1 hinv.2.1)
  have hcard := dfsInvariant_card hinv
  have htU : t ≤ U.card := by omega
  obtain ⟨B, hBU, hBcard⟩ := Finset.exists_subset_card_eq (s := U) htU
  refine ⟨D, B, hDcard, hBcard, ?_, ?_⟩
  · exact hinv.2.2.2.1.symm.mono_right hBU
  · intro a ha b hb
    exact hinv.2.2.2.2.2.2 a ha b (hBU hb)

end Erdos720
