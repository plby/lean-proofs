/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite linkedness lemmas used in the proof of Erdős Problem 717.

This file formalizes the elementary dense-graph linkage lemma from
Thomas--Wollan, European J. Combin. 26 (2005), Lemma 3.1.
-/

import ErdosProblems.Erdos718.Erdos718Core
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fintype

open Function Set
open SimpleGraph

namespace Erdos717
namespace ThomasWollan

universe u v

variable {V : Type u} {ι : Type v} [Fintype V] [DecidableEq V]

/-- Vertices which can serve as the middle of a length-two path between the
two terminals indexed by `i`, while avoiding the distinguished terminal set
`X`. -/
def availableMiddle (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (terminal : Sum ι ι ↪ V) (i : ι) : Finset V :=
  (G.neighborFinset (terminal (.inl i)) ∩
      G.neighborFinset (terminal (.inr i))) \ X

private lemma terminal_left_ne_right (terminal : Sum ι ι ↪ V) (i : ι) :
    terminal (.inl i) ≠ terminal (.inr i) := by
  intro h
  have h' : (Sum.inl i : Sum ι ι) = Sum.inr i := terminal.injective h
  cases h'

/-- The numerical common-neighbour estimate behind Thomas--Wollan's
length-two linkage lemma. -/
lemma card_availableMiddle_ge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k δ : ℕ) (X : Finset V) (terminal : Sum ι ι ↪ V) (i : ι)
    (hleftX : terminal (.inl i) ∈ X)
    (hrightX : terminal (.inr i) ∈ X)
    (hX : X.card ≤ 2 * k)
    (hdegree : ∀ v, δ ≤ G.degree v)
    (hsize : Fintype.card V + 3 * k ≤ 2 * δ + 4)
    (hnonadj : ¬G.Adj (terminal (.inl i)) (terminal (.inr i))) :
    k ≤ (availableMiddle G X terminal i).card := by
  classical
  by_cases hk : k = 0
  · simp [hk]
  let a := terminal (.inl i)
  let b := terminal (.inr i)
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  have hab : a ≠ b := terminal_left_ne_right terminal i
  have haA : a ∉ A := by simp [A]
  have hbB : b ∉ B := by simp [B]
  have haB : a ∉ B := by
    intro h
    exact hnonadj (G.mem_neighborFinset b a |>.mp h).symm
  have hbA : b ∉ A := by
    intro h
    exact hnonadj (G.mem_neighborFinset a b |>.mp h)
  have haU : a ∉ A ∪ B := by simp [haA, haB]
  have hbU : b ∉ A ∪ B := by simp [hbA, hbB]
  have hunion : (A ∪ B).card + 2 ≤ Fintype.card V := by
    have hsub : insert a (insert b (A ∪ B)) ⊆ (Finset.univ : Finset V) :=
      Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_univ] at hcard
    have haIns : a ∉ insert b (A ∪ B) := by simp [hab, haU]
    rw [Finset.card_insert_of_notMem haIns,
      Finset.card_insert_of_notMem hbU] at hcard
    omega
  have hinter_eq := Finset.card_union_add_card_inter A B
  have hA : δ ≤ A.card := by simpa [A] using hdegree a
  have hB : δ ≤ B.card := by simpa [B] using hdegree b
  have hinter : 3 * k - 2 ≤ (A ∩ B).card := by
    have hsum : 2 * δ ≤ A.card + B.card := by omega
    omega
  have haI : a ∉ X ∩ (A ∩ B) := by simp [haA]
  have hbI : b ∉ X ∩ (A ∩ B) := by simp [hbB]
  have hsmall : (X ∩ (A ∩ B)).card + 2 ≤ X.card := by
    have hsub : insert a (insert b (X ∩ (A ∩ B))) ⊆ X := by
      intro v hv
      simp only [Finset.mem_insert] at hv
      rcases hv with rfl | rfl | hv
      · exact hleftX
      · exact hrightX
      · exact (Finset.mem_inter.mp hv).1
    have hcard := Finset.card_le_card hsub
    have haIns : a ∉ insert b (X ∩ (A ∩ B)) := by simp [hab, haI]
    rw [Finset.card_insert_of_notMem haIns,
      Finset.card_insert_of_notMem hbI] at hcard
    omega
  unfold availableMiddle
  rw [Finset.card_sdiff]
  change k ≤ (A ∩ B).card - (X ∩ (A ∩ B)).card
  omega

/-- Thomas--Wollan's Lemma 3.1: the degree/cardinality inequality forces
enough distinct common neighbours to route every prescribed pairing by paths
of length at most two. -/
theorem isKLinked_of_minDegree_card
    (G : SimpleGraph V) [DecidableRel G.Adj] (k δ : ℕ)
    (hdegree : ∀ v, δ ≤ G.degree v)
    (hsize : Fintype.card V + 3 * k ≤ 2 * δ + 4) :
    Erdos718.IsKLinked G k := by
  classical
  intro X hXfinite hXcard
  intro J _ terminal hrange
  let XF : Finset V := hXfinite.toFinset
  have htermX (z : Sum J J) : terminal z ∈ X :=
    hrange ⟨z, rfl⟩
  have htermXF (z : Sum J J) : terminal z ∈ XF := by
    simpa [XF] using htermX z
  let terminalInX : Sum J J ↪ X :=
    { toFun := fun z => ⟨terminal z, htermX z⟩
      inj' := fun _ _ h => terminal.injective (congrArg Subtype.val h) }
  have hJcard : Fintype.card J ≤ k := by
    letI : Fintype X := hXfinite.fintype
    have hc := Fintype.card_le_of_injective terminalInX terminalInX.injective
    have hXcard' : Fintype.card X = X.ncard := Set.fintypeCard_eq_ncard X
    rw [Fintype.card_sum, hXcard'] at hc
    omega
  let Missing := {i : J // ¬G.Adj (terminal (.inl i)) (terminal (.inr i))}
  let candidate (i : Missing) : Finset V :=
    availableMiddle G XF terminal i.1
  have hcandidate (i : Missing) : k ≤ (candidate i).card := by
    apply card_availableMiddle_ge G k δ XF terminal i.1
    · exact htermXF (.inl i.1)
    · exact htermXF (.inr i.1)
    · simpa [XF, Set.ncard_eq_toFinset_card' X] using hXcard
    · exact hdegree
    · exact hsize
    · exact i.2
  have hMissingCard : Fintype.card Missing ≤ k := by
    exact (Fintype.card_subtype_le (fun i : J =>
      ¬G.Adj (terminal (.inl i)) (terminal (.inr i)))).trans hJcard
  have hHall (s : Finset Missing) :
      s.card ≤ (s.biUnion candidate).card := by
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      calc
        s.card ≤ Fintype.card Missing := Finset.card_le_univ s
        _ ≤ k := hMissingCard
        _ ≤ (candidate i).card := hcandidate i
        _ ≤ (s.biUnion candidate).card := by
          apply Finset.card_le_card
          intro v hv
          exact Finset.mem_biUnion.mpr ⟨i, hi, hv⟩
    · simp only [Finset.not_nonempty_iff_eq_empty] at hs
      simp [hs]
  obtain ⟨middle, hmiddle_inj, hmiddle_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' candidate).mp hHall
  have hmiddle_left (i : Missing) :
      G.Adj (terminal (.inl i.1)) (middle i) := by
    have h := (Finset.mem_sdiff.mp (hmiddle_mem i)).1
    exact G.mem_neighborFinset _ _ |>.mp (Finset.mem_inter.mp h).1
  have hmiddle_right (i : Missing) :
      G.Adj (middle i) (terminal (.inr i.1)) := by
    have h := (Finset.mem_sdiff.mp (hmiddle_mem i)).1
    exact (G.mem_neighborFinset _ _ |>.mp (Finset.mem_inter.mp h).2).symm
  have hmiddle_not_X (i : Missing) : middle i ∉ X := by
    have h := (Finset.mem_sdiff.mp (hmiddle_mem i)).2
    simpa [XF] using h
  let linkagePath (i : J) :
      G.Walk (terminal (.inl i)) (terminal (.inr i)) :=
    if h : G.Adj (terminal (.inl i)) (terminal (.inr i)) then
      h.toWalk
    else
      (hmiddle_left (⟨i, h⟩ : Missing)).toWalk.concat
        (hmiddle_right (⟨i, h⟩ : Missing))
  have linkagePath_isPath (i : J) : (linkagePath i).IsPath := by
    by_cases h : G.Adj (terminal (.inl i)) (terminal (.inr i))
    · simpa [linkagePath, h] using h.isPath_toWalk
    · let mi : Missing := ⟨i, h⟩
      have hleft := hmiddle_left mi
      have hright := hmiddle_right mi
      have hnot : terminal (.inr i) ∉ hleft.toWalk.support := by
        rw [hleft.support_toWalk]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(terminal_left_ne_right terminal i).symm, hright.ne.symm⟩
      simpa [linkagePath, h, mi] using
        hleft.isPath_toWalk.concat hnot hright
  have linkagePath_avoids (i : J) :
      Disjoint (Erdos718.walkInteriorSet (linkagePath i)) X := by
    rw [Set.disjoint_left]
    intro v hv hvX
    by_cases h : G.Adj (terminal (.inl i)) (terminal (.inr i))
    · rw [show linkagePath i = h.toWalk by simp [linkagePath, h]] at hv
      have hs : v = terminal (.inl i) ∨ v = terminal (.inr i) := by
        simpa [Erdos718.walkInteriorSet, h.support_toWalk] using hv.1
      exact hs.elim hv.2.1 hv.2.2
    · let mi : Missing := ⟨i, h⟩
      have hp : linkagePath i =
          (hmiddle_left mi).toWalk.concat (hmiddle_right mi) := by
        simp [linkagePath, h, mi]
      have hs : v = terminal (.inl i) ∨ v = middle mi ∨
          v = terminal (.inr i) := by
        simpa [hp, SimpleGraph.Walk.support_concat,
          SimpleGraph.Adj.support_toWalk] using hv.1
      have hvmid : v = middle mi := by
        rcases hs with hs | hs | hs
        · exact (hv.2.1 hs).elim
        · exact hs
        · exact (hv.2.2 hs).elim
      exact hmiddle_not_X mi (hvmid ▸ hvX)
  have linkagePath_disjoint : Pairwise fun i j : J =>
      Disjoint {v | v ∈ (linkagePath i).support}
        {v | v ∈ (linkagePath j).support} := by
    intro i j hij
    rw [Set.disjoint_left]
    intro v hvi hvj
    by_cases hi : G.Adj (terminal (.inl i)) (terminal (.inr i))
    · have hpi : linkagePath i = hi.toWalk := by simp [linkagePath, hi]
      rw [hpi, hi.support_toWalk] at hvi
      simp at hvi
      by_cases hj : G.Adj (terminal (.inl j)) (terminal (.inr j))
      · have hpj : linkagePath j = hj.toWalk := by simp [linkagePath, hj]
        rw [hpj, hj.support_toWalk] at hvj
        simp at hvj
        rcases hvi with rfl | rfl <;> rcases hvj with h | h
        all_goals
          have hz := terminal.injective h
          simp_all
      · let mj : Missing := ⟨j, hj⟩
        have hpj : linkagePath j =
            (hmiddle_left mj).toWalk.concat (hmiddle_right mj) := by
          simp [linkagePath, hj, mj]
        rw [hpj] at hvj
        simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.support_concat,
          SimpleGraph.Adj.support_toWalk, List.mem_append, List.mem_cons] at hvj
        simp at hvj
        rcases hvi with rfl | rfl
        all_goals
          rcases hvj with (h | h) | h
          · have hz := terminal.injective h
            simp_all
          · exact hmiddle_not_X mj (h ▸ htermX _)
          · have hz := terminal.injective h
            simp_all
    · let mi : Missing := ⟨i, hi⟩
      have hpi : linkagePath i =
          (hmiddle_left mi).toWalk.concat (hmiddle_right mi) := by
        simp [linkagePath, hi, mi]
      rw [hpi] at hvi
      simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.support_concat,
        SimpleGraph.Adj.support_toWalk, List.mem_append, List.mem_cons] at hvi
      simp at hvi
      by_cases hj : G.Adj (terminal (.inl j)) (terminal (.inr j))
      · have hpj : linkagePath j = hj.toWalk := by simp [linkagePath, hj]
        rw [hpj, hj.support_toWalk] at hvj
        simp at hvj
        rcases hvj with rfl | rfl
        all_goals
          rcases hvi with (h | h) | h
          · have hz := terminal.injective h
            simp_all
          · exact hmiddle_not_X mi (h ▸ htermX _)
          · have hz := terminal.injective h
            simp_all
      · let mj : Missing := ⟨j, hj⟩
        have hpj : linkagePath j =
            (hmiddle_left mj).toWalk.concat (hmiddle_right mj) := by
          simp [linkagePath, hj, mj]
        rw [hpj] at hvj
        simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.support_concat,
          SimpleGraph.Adj.support_toWalk, List.mem_append, List.mem_cons] at hvj
        simp at hvj
        rcases hvi with (hvi | hvi) | hvi
        · rcases hvj with (hvj | hvj) | hvj
          · have hz := terminal.injective (hvi.symm.trans hvj)
            simp_all
          · exact hmiddle_not_X mj ((hvi.symm.trans hvj) ▸ htermX _)
          · have hz := terminal.injective (hvi.symm.trans hvj)
            simp_all
        · rcases hvj with (hvj | hvj) | hvj
          · exact hmiddle_not_X mi ((hvi.symm.trans hvj).symm ▸ htermX _)
          · apply hij
            exact congrArg Subtype.val
              (hmiddle_inj (hvi.symm.trans hvj))
          · exact hmiddle_not_X mi ((hvi.symm.trans hvj).symm ▸ htermX _)
        · rcases hvj with (hvj | hvj) | hvj
          · have hz := terminal.injective (hvi.symm.trans hvj)
            simp_all
          · exact hmiddle_not_X mj ((hvi.symm.trans hvj) ▸ htermX _)
          · have hz := terminal.injective (hvi.symm.trans hvj)
            simp_all
  exact ⟨{
    path := linkagePath
    isPath := linkagePath_isPath
    avoids := linkagePath_avoids
    disjoint := linkagePath_disjoint
  }⟩

/-! ### Short partial linkages -/

/-- A vertex-disjoint collection of paths of length at most seven which
resolves a selected subset of a prescribed pairing. -/
structure ShortPartialLinkage (G : SimpleGraph V) (X : Set V)
    (terminal : Sum ι ι ↪ V) where
  active : Finset ι
  path : ∀ i : active,
    G.Walk (terminal (.inl i.1)) (terminal (.inr i.1))
  isPath : ∀ i, (path i).IsPath
  length_le : ∀ i, (path i).length ≤ 7
  avoids : ∀ i, Disjoint (Erdos718.walkInteriorSet (path i)) X
  disjoint : Pairwise fun i j : active =>
    Disjoint {v | v ∈ (path i).support} {v | v ∈ (path j).support}

namespace ShortPartialLinkage

variable [Fintype ι] {G : SimpleGraph V} {X : Set V}
  {terminal : Sum ι ι ↪ V}

def empty (G : SimpleGraph V) (X : Set V) (terminal : Sum ι ι ↪ V) :
    ShortPartialLinkage G X terminal where
  active := Finset.univ.filter fun _ => False
  path i := ((Finset.mem_filter.mp i.2).2).elim
  isPath i := ((Finset.mem_filter.mp i.2).2).elim
  length_le i := ((Finset.mem_filter.mp i.2).2).elim
  avoids i := ((Finset.mem_filter.mp i.2).2).elim
  disjoint i := ((Finset.mem_filter.mp i.2).2).elim

def totalLength (P : ShortPartialLinkage G X terminal) : ℕ :=
  ∑ i : P.active, (P.path i).length

/-- A partial linkage resolving every index is a linkage. -/
def toPairLinkage (P : ShortPartialLinkage G X terminal)
    (hfull : P.active = Finset.univ) : Erdos718.PairLinkage G X terminal where
  path i := P.path ⟨i, by rw [hfull]; exact Finset.mem_univ i⟩
  isPath i := P.isPath ⟨i, by rw [hfull]; exact Finset.mem_univ i⟩
  avoids i := P.avoids ⟨i, by rw [hfull]; exact Finset.mem_univ i⟩
  disjoint := by
    intro i j hij
    exact P.disjoint (fun h => hij (congrArg Subtype.val h))

lemma active_card_lt_of_no_linkage
    (P : ShortPartialLinkage G X terminal)
    (hno : ¬Nonempty (Erdos718.PairLinkage G X terminal)) :
    P.active.card < Fintype.card ι := by
  have hle := Finset.card_le_univ P.active
  by_contra hnot
  have heqcard : P.active.card = (Finset.univ : Finset ι).card := by
    simpa using Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  have hfull := Finset.eq_univ_of_card P.active (by simpa using heqcard)
  exact hno ⟨P.toPairLinkage hfull⟩

/-- Choose a partial linkage which first maximizes the number of resolved
pairs and then minimizes the sum of its path lengths. -/
theorem exists_lexicographically_optimal
    (G : SimpleGraph V) (X : Set V) (terminal : Sum ι ι ↪ V) :
    ∃ P : ShortPartialLinkage G X terminal,
      (∀ Q : ShortPartialLinkage G X terminal,
        Q.active.card ≤ P.active.card) ∧
      (∀ Q : ShortPartialLinkage G X terminal,
        Q.active.card = P.active.card → P.totalLength ≤ Q.totalLength) := by
  classical
  let ExistsSize (m : ℕ) : Prop :=
    ∃ P : ShortPartialLinkage G X terminal, P.active.card = m
  have hzero : ExistsSize 0 := by
    exact ⟨empty G X terminal, by simp [empty]⟩
  let m := Nat.findGreatest ExistsSize (Fintype.card ι)
  have hm : ExistsSize m := by
    exact Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hzero
  let ExistsTotal (n : ℕ) : Prop :=
    ∃ P : ShortPartialLinkage G X terminal,
      P.active.card = m ∧ P.totalLength = n
  have htotal : ∃ n, ExistsTotal n := by
    obtain ⟨P, hP⟩ := hm
    exact ⟨P.totalLength, P, hP, rfl⟩
  let n := Nat.find htotal
  obtain ⟨P, hPsize, hPlength⟩ := Nat.find_spec htotal
  refine ⟨P, ?_, ?_⟩
  · intro Q
    rw [hPsize]
    apply Nat.le_findGreatest (Finset.card_le_univ Q.active)
    exact ⟨Q, rfl⟩
  · intro Q hQ
    rw [hPlength]
    apply Nat.find_min' htotal
    exact ⟨Q, hQ.trans hPsize, rfl⟩

/-- The internal vertices of one selected short path. -/
def interiorFinset (P : ShortPartialLinkage G X terminal) (i : P.active) :
    Finset V :=
  ((P.path i).support.toFinset.erase (terminal (.inl i.1))).erase
    (terminal (.inr i.1))

lemma card_interiorFinset_le_six
    (P : ShortPartialLinkage G X terminal) (i : P.active) :
    (P.interiorFinset i).card ≤ 6 := by
  classical
  let p := P.path i
  let a := terminal (.inl i.1)
  let b := terminal (.inr i.1)
  have hab : a ≠ b := terminal_left_ne_right terminal i.1
  have ha : a ∈ p.support.toFinset := by
    exact List.mem_toFinset.mpr p.start_mem_support
  have hb : b ∈ p.support.toFinset := by
    exact List.mem_toFinset.mpr p.end_mem_support
  have hb' : b ∈ p.support.toFinset.erase a := by
    exact Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hcardSupport : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup (P.isPath i).support_nodup,
      p.length_support]
  unfold interiorFinset
  change ((p.support.toFinset.erase a).erase b).card ≤ 6
  rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
  rw [hcardSupport]
  have hlen := P.length_le i
  change p.length ≤ 7 at hlen
  omega

/-- The distinguished set together with all internal vertices used by a
partial linkage. -/
def usedVertices (P : ShortPartialLinkage G X terminal) (XF : Finset V) :
    Finset V :=
  XF ∪ P.active.attach.biUnion P.interiorFinset

def selectedSupports (P : ShortPartialLinkage G X terminal) : Finset V :=
  P.active.attach.biUnion fun i => (P.path i).support.toFinset

noncomputable def inactiveTerminals
    (P : ShortPartialLinkage G X terminal) : Finset V := by
  classical
  exact (Finset.univ.filter fun i => i ∉ P.active).biUnion fun i =>
    {terminal (.inl i), terminal (.inr i)}

def terminalFinset (terminal : Sum ι ι ↪ V) : Finset V :=
  Finset.univ.map terminal

@[simp] lemma card_terminalFinset (terminal : Sum ι ι ↪ V) :
    (terminalFinset terminal).card = 2 * Fintype.card ι := by
  simp [terminalFinset, Fintype.card_sum]
  omega

lemma mem_terminalFinset (terminal : Sum ι ι ↪ V) (z : Sum ι ι) :
    terminal z ∈ terminalFinset terminal := by
  simp [terminalFinset]

lemma usedVertices_subset_selectedSupports_union_inactiveTerminals
    (P : ShortPartialLinkage G X terminal) :
    P.usedVertices (terminalFinset terminal) ⊆
      P.selectedSupports ∪ P.inactiveTerminals := by
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with hvterm | hvinterior
  · obtain ⟨z, _hz, rfl⟩ := Finset.mem_map.mp hvterm
    cases z with
    | inl i =>
        by_cases hi : i ∈ P.active
        · apply Finset.mem_union_left
          apply Finset.mem_biUnion.mpr
          let j : P.active := ⟨i, hi⟩
          refine ⟨j, Finset.mem_attach _ _, ?_⟩
          exact List.mem_toFinset.mpr (P.path j).start_mem_support
        · apply Finset.mem_union_right
          unfold inactiveTerminals
          apply Finset.mem_biUnion.mpr
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
          show terminal (.inl i) ∈
            ({terminal (.inl i), terminal (.inr i)} : Finset V)
          simp
    | inr i =>
        by_cases hi : i ∈ P.active
        · apply Finset.mem_union_left
          apply Finset.mem_biUnion.mpr
          let j : P.active := ⟨i, hi⟩
          refine ⟨j, Finset.mem_attach _ _, ?_⟩
          exact List.mem_toFinset.mpr (P.path j).end_mem_support
        · apply Finset.mem_union_right
          unfold inactiveTerminals
          apply Finset.mem_biUnion.mpr
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
          show terminal (.inr i) ∈
            ({terminal (.inl i), terminal (.inr i)} : Finset V)
          simp
  · apply Finset.mem_union_left
    obtain ⟨i, hi, hvint⟩ := Finset.mem_biUnion.mp hvinterior
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    unfold interiorFinset at hvint
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hvint)

lemma card_usedVertices_le
    (P : ShortPartialLinkage G X terminal) (XF : Finset V) :
    (P.usedVertices XF).card ≤ XF.card + 6 * P.active.card := by
  classical
  calc
    (P.usedVertices XF).card ≤ XF.card +
        (P.active.attach.biUnion P.interiorFinset).card :=
      Finset.card_union_le _ _
    _ ≤ XF.card + ∑ i ∈ P.active.attach, (P.interiorFinset i).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ ≤ XF.card + ∑ _i ∈ P.active.attach, 6 := by
      gcongr with i hi
      exact P.card_interiorFinset_le_six i
    _ = XF.card + 6 * P.active.card := by simp [Nat.mul_comm]

lemma support_subset_usedVertices
    (P : ShortPartialLinkage G X terminal) (XF : Finset V)
    (hterminal : ∀ z, terminal z ∈ XF) (i : P.active) :
    (P.path i).support.toFinset ⊆ P.usedVertices XF := by
  classical
  intro v hv
  by_cases hva : v = terminal (.inl i.1)
  · subst v
    exact Finset.mem_union_left _ (hterminal _)
  by_cases hvb : v = terminal (.inr i.1)
  · subst v
    exact Finset.mem_union_left _ (hterminal _)
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_attach _ _, ?_⟩
  exact Finset.mem_erase.mpr ⟨hvb,
    Finset.mem_erase.mpr ⟨hva, hv⟩⟩

/-- Add one new short path at an index not already resolved. -/
noncomputable def insert
    (P : ShortPartialLinkage G X terminal) (i : ι) (hi : i ∉ P.active)
    (p : G.Walk (terminal (.inl i)) (terminal (.inr i)))
    (hp : p.IsPath) (hlen : p.length ≤ 7)
    (havoid : Disjoint (Erdos718.walkInteriorSet p) X)
    (hdisj : ∀ j : P.active,
      Disjoint {v | v ∈ p.support} {v | v ∈ (P.path j).support}) :
    ShortPartialLinkage G X terminal := by
  classical
  let newActive := P.active.cons i hi
  let oldIndex (j : newActive) (hji : j.1 ≠ i) : P.active :=
    ⟨j.1, (Finset.mem_cons.mp j.2).resolve_left hji⟩
  let newPath (j : newActive) :
      G.Walk (terminal (.inl j.1)) (terminal (.inr j.1)) :=
    if hji : j.1 = i then
      p.copy
        (congrArg (fun x => terminal (.inl x)) hji.symm)
        (congrArg (fun x => terminal (.inr x)) hji.symm)
    else
      P.path (oldIndex j hji)
  refine {
    active := newActive
    path := newPath
    isPath := ?_
    length_le := ?_
    avoids := ?_
    disjoint := ?_
  }
  · intro j
    by_cases hji : j.1 = i
    · simp only [newPath, hji, ↓reduceDIte]
      simpa only [SimpleGraph.Walk.isPath_def,
        SimpleGraph.Walk.support_copy] using hp
    · simp only [newPath, hji, ↓reduceDIte]
      exact P.isPath (oldIndex j hji)
  · intro j
    by_cases hji : j.1 = i
    · simp only [newPath, hji, ↓reduceDIte,
        SimpleGraph.Walk.length_copy]
      exact hlen
    · simp only [newPath, hji, ↓reduceDIte]
      exact P.length_le (oldIndex j hji)
  · intro j
    by_cases hji : j.1 = i
    · simp only [newPath, hji, ↓reduceDIte,
        Erdos718.walkInteriorSet, SimpleGraph.Walk.support_copy]
      exact havoid
    · simp only [newPath, hji, ↓reduceDIte]
      exact P.avoids (oldIndex j hji)
  · intro j l hjl
    by_cases hji : j.1 = i
    · by_cases hli : l.1 = i
      · exact (hjl (Subtype.ext (hji.trans hli.symm))).elim
      · simpa only [newPath, hji, hli, ↓reduceDIte,
          Set.mem_ofPred_eq, SimpleGraph.Walk.support_copy] using
          hdisj (oldIndex l hli)
    · by_cases hli : l.1 = i
      · have h := (hdisj (oldIndex j hji)).symm
        simpa only [newPath, hji, hli, ↓reduceDIte,
          Set.mem_ofPred_eq, SimpleGraph.Walk.support_copy] using h
      · simpa only [newPath, hji, hli, ↓reduceDIte] using
          P.disjoint (by
            intro h
            apply hjl
            apply Subtype.ext
            exact congrArg (fun x : P.active => x.1) h)

@[simp] lemma active_insert
    (P : ShortPartialLinkage G X terminal) (i : ι) (hi : i ∉ P.active)
    (p : G.Walk (terminal (.inl i)) (terminal (.inr i)))
    (hp : p.IsPath) (hlen : p.length ≤ 7)
    (havoid : Disjoint (Erdos718.walkInteriorSet p) X)
    (hdisj : ∀ j : P.active,
      Disjoint {v | v ∈ p.support} {v | v ∈ (P.path j).support}) :
    (P.insert i hi p hp hlen havoid hdisj).active =
      P.active.cons i hi := rfl

/-- Replace one selected path, preserving the active index set. -/
noncomputable def replace
    (P : ShortPartialLinkage G X terminal) (i : P.active)
    (p : G.Walk (terminal (.inl i.1)) (terminal (.inr i.1)))
    (hp : p.IsPath) (hlen : p.length ≤ 7)
    (havoid : Disjoint (Erdos718.walkInteriorSet p) X)
    (hdisj : ∀ j : P.active, j ≠ i →
      Disjoint {v | v ∈ p.support} {v | v ∈ (P.path j).support}) :
    ShortPartialLinkage G X terminal := by
  classical
  let newPath (j : P.active) :
      G.Walk (terminal (.inl j.1)) (terminal (.inr j.1)) :=
    if hji : j = i then
      p.copy
        (congrArg (fun x : P.active => terminal (.inl x.1)) hji.symm)
        (congrArg (fun x : P.active => terminal (.inr x.1)) hji.symm)
    else
      P.path j
  refine {
    active := P.active
    path := newPath
    isPath := ?_
    length_le := ?_
    avoids := ?_
    disjoint := ?_
  }
  · intro j
    by_cases hji : j = i
    · simp only [newPath, hji, ↓reduceDIte]
      simpa only [SimpleGraph.Walk.isPath_def,
        SimpleGraph.Walk.support_copy] using hp
    · simp only [newPath, hji, ↓reduceDIte]
      exact P.isPath j
  · intro j
    by_cases hji : j = i
    · simp only [newPath, hji, ↓reduceDIte,
        SimpleGraph.Walk.length_copy]
      exact hlen
    · simp only [newPath, hji, ↓reduceDIte]
      exact P.length_le j
  · intro j
    by_cases hji : j = i
    · simp only [newPath, hji, ↓reduceDIte,
        Erdos718.walkInteriorSet, SimpleGraph.Walk.support_copy]
      exact havoid
    · simp only [newPath, hji, ↓reduceDIte]
      exact P.avoids j
  · intro j l hjl
    by_cases hji : j = i
    · by_cases hli : l = i
      · exact (hjl (hji.trans hli.symm)).elim
      · simpa only [newPath, hji, hli, ↓reduceDIte,
          Set.mem_ofPred_eq, SimpleGraph.Walk.support_copy] using hdisj l hli
    · by_cases hli : l = i
      · have h := (hdisj j hji).symm
        simpa only [newPath, hji, hli, ↓reduceDIte,
          Set.mem_ofPred_eq, SimpleGraph.Walk.support_copy] using h
      · simpa only [newPath, hji, hli, ↓reduceDIte] using P.disjoint hjl

@[simp] lemma active_replace
    (P : ShortPartialLinkage G X terminal) (i : P.active)
    (p : G.Walk (terminal (.inl i.1)) (terminal (.inr i.1)))
    (hp : p.IsPath) (hlen : p.length ≤ 7)
    (havoid : Disjoint (Erdos718.walkInteriorSet p) X)
    (hdisj : ∀ j : P.active, j ≠ i →
      Disjoint {v | v ∈ p.support} {v | v ∈ (P.path j).support}) :
    (P.replace i p hp hlen havoid hdisj).active = P.active := rfl

lemma totalLength_replace_lt
    (P : ShortPartialLinkage G X terminal) (i : P.active)
    (p : G.Walk (terminal (.inl i.1)) (terminal (.inr i.1)))
    (hp : p.IsPath) (hlen : p.length ≤ 7)
    (havoid : Disjoint (Erdos718.walkInteriorSet p) X)
    (hdisj : ∀ j : P.active, j ≠ i →
      Disjoint {v | v ∈ p.support} {v | v ∈ (P.path j).support})
    (hshort : p.length < (P.path i).length) :
    (P.replace i p hp hlen havoid hdisj).totalLength < P.totalLength := by
  classical
  unfold totalLength
  apply Finset.sum_lt_sum
  · intro j hj
    change ((P.replace i p hp hlen havoid hdisj).path j).length ≤
      (P.path j).length
    by_cases hji : j = i
    · subst j
      simpa [replace, SimpleGraph.Walk.length_copy] using hshort.le
    · simp only [replace]
      split
      · rename_i h
        exact (hji h).elim
      · exact le_rfl
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    change ((P.replace i p hp hlen havoid hdisj).path i).length <
      (P.path i).length
    simpa [replace, SimpleGraph.Walk.length_copy] using hshort

/-! ### The shortening move -/

/-- Four neighbours of an outside vertex on a path include two whose
positions differ by at least three. -/
lemma exists_far_apart_neighbors_on_path
    [DecidableRel G.Adj] {a b v : V} {p : G.Walk a b} (hp : p.IsPath)
    (hv : v ∉ p.support)
    (hfour : 4 ≤ (G.neighborFinset v ∩ p.support.toFinset).card) :
    ∃ x y : V,
      x ∈ p.support ∧ y ∈ p.support ∧ G.Adj x v ∧ G.Adj v y ∧
        p.support.idxOf x + 3 ≤ p.support.idxOf y := by
  classical
  let N := G.neighborFinset v ∩ p.support.toFinset
  obtain ⟨B, hBN, hBcard⟩ := Finset.exists_subset_card_eq hfour
  let position (x : V) := p.support.idxOf x
  have hpos_inj : Set.InjOn position B := by
    intro x hx y hy hxy
    have hxN := Finset.mem_inter.mp (hBN hx)
    exact (List.idxOf_inj (List.mem_toFinset.mp hxN.2)).mp hxy
  let I := B.image position
  have hIcard : I.card = 4 := by
    rw [Finset.card_image_iff.mpr hpos_inj, hBcard]
  let order := I.orderEmbOfFin hIcard
  let z0 := order (0 : Fin 4)
  let z3 := order (3 : Fin 4)
  have hz0I : z0 ∈ I := I.orderEmbOfFin_mem hIcard (0 : Fin 4)
  have hz3I : z3 ∈ I := I.orderEmbOfFin_mem hIcard (3 : Fin 4)
  obtain ⟨x, hxB, hxpos⟩ := Finset.mem_image.mp hz0I
  obtain ⟨y, hyB, hypos⟩ := Finset.mem_image.mp hz3I
  have hgap : z0 + 3 ≤ z3 := by
    have h01 : order (0 : Fin 4) < order (1 : Fin 4) :=
      order.strictMono (by decide)
    have h12 : order (1 : Fin 4) < order (2 : Fin 4) :=
      order.strictMono (by decide)
    have h23 : order (2 : Fin 4) < order (3 : Fin 4) :=
      order.strictMono (by decide)
    omega
  have hxN := Finset.mem_inter.mp (hBN hxB)
  have hyN := Finset.mem_inter.mp (hBN hyB)
  refine ⟨x, y, List.mem_toFinset.mp hxN.2,
    List.mem_toFinset.mp hyN.2, ?_, ?_, ?_⟩
  · exact (G.mem_neighborFinset v x |>.mp hxN.1).symm
  · exact G.mem_neighborFinset v y |>.mp hyN.1
  · simpa only [position, hxpos, hypos] using hgap

/-- Replacing the segment between two far-apart neighbours by a two-edge
detour through an outside vertex produces a strictly shorter path. -/
lemma exists_shorter_path_via
    [DecidableRel G.Adj] {a b v : V} {p : G.Walk a b} (hp : p.IsPath)
    (hv : v ∉ p.support)
    (hfour : 4 ≤ (G.neighborFinset v ∩ p.support.toFinset).card) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length < p.length ∧
      q.support.toFinset ⊆ ({v} : Finset V) ∪ p.support.toFinset := by
  classical
  obtain ⟨x, y, hx, hy, hxv, hvy, hgap⟩ :=
    exists_far_apart_neighbors_on_path hp hv hfour
  let left := p.takeUntil x hx
  let right := p.dropUntil y hy
  let middle : G.Walk x y := hxv.toWalk.concat hvy
  let shortcut : G.Walk a b := (left.append middle).append right
  let q : G.Walk a b := shortcut.bypass
  have hyidx : p.support.idxOf y ≤ p.length := by
    have := List.idxOf_lt_length_of_mem hy
    rw [p.length_support] at this
    omega
  have hshortcut : shortcut.length < p.length := by
    simp only [shortcut, left, right, middle, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_takeUntil, SimpleGraph.Walk.length_dropUntil,
      SimpleGraph.Walk.length_concat, SimpleGraph.Adj.length_toWalk]
    omega
  refine ⟨q, SimpleGraph.Walk.bypass_isPath _, ?_, ?_⟩
  · exact (shortcut.length_bypass_le_length).trans_lt hshortcut
  · intro z hz
    have hz' : z ∈ shortcut.support :=
      shortcut.support_bypass_subset_support (List.mem_toFinset.mp hz)
    simp only [shortcut, SimpleGraph.Walk.mem_support_append_iff] at hz'
    rcases hz' with (hzleft | hzmiddle) | hzright
    · exact Finset.mem_union_right _
        (List.mem_toFinset.mpr (p.support_takeUntil_subset_support hx hzleft))
    · simp only [middle, SimpleGraph.Walk.support_concat,
        SimpleGraph.Adj.support_toWalk, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hzmiddle
      rcases hzmiddle with (hzx | hzv) | hzy
      · rw [hzx]
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hx)
      · rw [hzv]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      · rw [hzy]
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr hy)
    · exact Finset.mem_union_right _
        (List.mem_toFinset.mpr (p.support_dropUntil_subset_support hy hzright))

/-- In a lexicographically optimal short partial linkage, an unused vertex
has at most three neighbours on each selected path. -/
lemma card_neighbors_on_path_le_three_of_optimal
    [DecidableRel G.Adj]
    (P : ShortPartialLinkage G X terminal) (XF : Finset V)
    (hX : X = (XF : Set V)) (hterminal : ∀ z, terminal z ∈ XF)
    (hminimal : ∀ Q : ShortPartialLinkage G X terminal,
      Q.active.card = P.active.card → P.totalLength ≤ Q.totalLength)
    {v : V} (hv : v ∉ P.usedVertices XF) (i : P.active) :
    (G.neighborFinset v ∩ (P.path i).support.toFinset).card ≤ 3 := by
  classical
  by_contra hnot
  have hfour : 4 ≤
      (G.neighborFinset v ∩ (P.path i).support.toFinset).card := by omega
  have hvpath : v ∉ (P.path i).support := by
    intro hvp
    exact hv (P.support_subset_usedVertices XF hterminal i
      (List.mem_toFinset.mpr hvp))
  obtain ⟨q, hqpath, hqlt, hqsub⟩ :=
    exists_shorter_path_via (P.isPath i) hvpath hfour
  have hqlen : q.length ≤ 7 := hqlt.le.trans (P.length_le i)
  have hvXF : v ∉ XF := by
    intro hvF
    exact hv (Finset.mem_union_left _ hvF)
  have hqavoid : Disjoint (Erdos718.walkInteriorSet q) X := by
    rw [Set.disjoint_left]
    intro z hzq hzX
    have hzXF : z ∈ XF := by
      change z ∈ (XF : Set V)
      rw [← hX]
      exact hzX
    have hzq' := hqsub (List.mem_toFinset.mpr hzq.1)
    rcases Finset.mem_union.mp hzq' with hzv | hzp
    · have : z = v := Finset.mem_singleton.mp hzv
      exact hvXF (this ▸ hzXF)
    · have hzint : z ∈ Erdos718.walkInteriorSet (P.path i) := by
        refine ⟨List.mem_toFinset.mp hzp, ?_, ?_⟩
        · intro hzleft
          exact hzq.2.1 hzleft
        · intro hzright
          exact hzq.2.2 hzright
      exact (Set.disjoint_left.mp (P.avoids i)) hzint hzX
  have hqdisj : ∀ j : P.active, j ≠ i →
      Disjoint {z | z ∈ q.support} {z | z ∈ (P.path j).support} := by
    intro j hji
    rw [Set.disjoint_left]
    intro z hzq hzj
    have hzq' := hqsub (List.mem_toFinset.mpr hzq)
    rcases Finset.mem_union.mp hzq' with hzv | hzi
    · have hzv' : z = v := Finset.mem_singleton.mp hzv
      subst z
      exact hv (P.support_subset_usedVertices XF hterminal j
        (List.mem_toFinset.mpr hzj))
    · exact (Set.disjoint_left.mp (P.disjoint hji.symm))
        (List.mem_toFinset.mp hzi) hzj
  let Q := P.replace i q hqpath hqlen hqavoid hqdisj
  have hsame : Q.active.card = P.active.card := by
    simp only [Q, active_replace]
  have hmin := hminimal Q hsame
  have hshort : Q.totalLength < P.totalLength := by
    exact P.totalLength_replace_lt i q hqpath hqlen hqavoid hqdisj hqlt
  omega

lemma terminal_not_mem_selected_path
    (P : ShortPartialLinkage G X terminal)
    (hterminalX : ∀ z, terminal z ∈ X) (z : Sum ι ι) (j : P.active)
    (hzleft : z ≠ .inl j.1) (hzright : z ≠ .inr j.1) :
    terminal z ∉ (P.path j).support := by
  intro hz
  by_cases hs : terminal z = terminal (.inl j.1)
  · exact hzleft (terminal.injective hs)
  by_cases ht : terminal z = terminal (.inr j.1)
  · exact hzright (terminal.injective ht)
  have hzint : terminal z ∈ Erdos718.walkInteriorSet (P.path j) :=
    ⟨hz, hs, ht⟩
  exact (Set.disjoint_left.mp (P.avoids j)) hzint (hterminalX z)

/-- An unused vertex cannot be adjacent to both endpoints of an unresolved
pair, or that two-edge path could be added to the partial linkage. -/
lemma not_both_adj_inactive_of_optimal
    [DecidableRel G.Adj]
    (P : ShortPartialLinkage G X terminal) (XF : Finset V)
    (hX : X = (XF : Set V)) (hterminal : ∀ z, terminal z ∈ XF)
    (hmaximal : ∀ Q : ShortPartialLinkage G X terminal,
      Q.active.card ≤ P.active.card)
    {v : V} (hv : v ∉ P.usedVertices XF) {i : ι} (hi : i ∉ P.active) :
    ¬(G.Adj (terminal (.inl i)) v ∧ G.Adj v (terminal (.inr i))) := by
  classical
  rintro ⟨hleft, hright⟩
  let p : G.Walk (terminal (.inl i)) (terminal (.inr i)) :=
    hleft.toWalk.concat hright
  have hterminalX (z : Sum ι ι) : terminal z ∈ X := by
    rw [hX]
    exact hterminal z
  have hvXF : v ∉ XF := by
    intro hvF
    exact hv (Finset.mem_union_left _ hvF)
  have hvleft : v ≠ terminal (.inl i) := by
    exact hleft.ne.symm
  have hvright : v ≠ terminal (.inr i) := by
    exact hright.ne
  have hpath : p.IsPath := by
    apply hleft.isPath_toWalk.concat
    rw [hleft.support_toWalk]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(terminal_left_ne_right terminal i).symm, hvright.symm⟩
  have hlen : p.length ≤ 7 := by simp [p]
  have havoid : Disjoint (Erdos718.walkInteriorSet p) X := by
    rw [Set.disjoint_left]
    intro z hz hzX
    have hzsupp : z = terminal (.inl i) ∨ z = v ∨
        z = terminal (.inr i) := by
      simpa [p, SimpleGraph.Walk.support_concat,
        SimpleGraph.Adj.support_toWalk] using hz.1
    rcases hzsupp with hzl | hzv | hzr
    · exact hz.2.1 hzl
    · subst z
      apply hvXF
      change v ∈ (XF : Set V)
      rw [← hX]
      exact hzX
    · exact hz.2.2 hzr
  have hdisj : ∀ j : P.active,
      Disjoint {z | z ∈ p.support} {z | z ∈ (P.path j).support} := by
    intro j
    rw [Set.disjoint_left]
    intro z hzp hzj
    have hzsupp : z = terminal (.inl i) ∨ z = v ∨
        z = terminal (.inr i) := by
      simpa [p, SimpleGraph.Walk.support_concat,
        SimpleGraph.Adj.support_toWalk] using hzp
    rcases hzsupp with hzl | hzv | hzr
    · subst z
      apply P.terminal_not_mem_selected_path hterminalX (.inl i) j
      · intro hz
        have hij : i = j.1 := Sum.inl_injective hz
        exact hi (hij ▸ j.2)
      · intro hz
        cases hz
      · exact hzj
    · subst z
      exact hv (P.support_subset_usedVertices XF hterminal j
        (List.mem_toFinset.mpr hzj))
    · subst z
      apply P.terminal_not_mem_selected_path hterminalX (.inr i) j
      · intro hz
        cases hz
      · intro hz
        have hij : i = j.1 := Sum.inr_injective hz
        exact hi (hij ▸ j.2)
      · exact hzj
  let Q := P.insert i hi p hpath hlen havoid hdisj
  have hQcard : Q.active.card = P.active.card + 1 := by
    simp only [Q, active_insert, Finset.card_cons]
  have := hmaximal Q
  omega

lemma card_neighbors_inactive_pair_le_one
    [DecidableRel G.Adj]
    (P : ShortPartialLinkage G X terminal) (XF : Finset V)
    (hX : X = (XF : Set V)) (hterminal : ∀ z, terminal z ∈ XF)
    (hmaximal : ∀ Q : ShortPartialLinkage G X terminal,
      Q.active.card ≤ P.active.card)
    {v : V} (hv : v ∉ P.usedVertices XF) {i : ι} (hi : i ∉ P.active) :
    (G.neighborFinset v ∩
      ({terminal (.inl i), terminal (.inr i)} : Finset V)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  rcases Finset.mem_inter.mp hx with ⟨hxN, hxpair⟩
  rcases Finset.mem_inter.mp hy with ⟨hyN, hypair⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair hypair
  rcases hxpair with hxl | hxr <;> rcases hypair with hyl | hyr
  · exact hxl.trans hyl.symm
  · exfalso
    subst x
    subst y
    apply P.not_both_adj_inactive_of_optimal XF hX hterminal hmaximal hv hi
    constructor
    · exact (G.mem_neighborFinset v (terminal (.inl i)) |>.mp hxN).symm
    · exact G.mem_neighborFinset v (terminal (.inr i)) |>.mp hyN
  · exfalso
    subst x
    subst y
    apply P.not_both_adj_inactive_of_optimal XF hX hterminal hmaximal hv hi
    constructor
    · exact (G.mem_neighborFinset v (terminal (.inl i)) |>.mp hyN).symm
    · exact G.mem_neighborFinset v (terminal (.inr i)) |>.mp hxN
  · exact hxr.trans hyr.symm

/-- The central `3k` count in the proof of Thomas--Wollan's Theorem 1.5. -/
lemma card_neighbors_usedVertices_le_three_mul
    [DecidableRel G.Adj]
    (P : ShortPartialLinkage G X terminal)
    (hXrange : X = Set.range terminal)
    (hoptimal :
      (∀ Q : ShortPartialLinkage G X terminal,
        Q.active.card ≤ P.active.card) ∧
      (∀ Q : ShortPartialLinkage G X terminal,
        Q.active.card = P.active.card → P.totalLength ≤ Q.totalLength))
    {v : V} (hv : v ∉ P.usedVertices (terminalFinset terminal)) :
    (G.neighborFinset v ∩ P.usedVertices (terminalFinset terminal)).card ≤
      3 * Fintype.card ι := by
  classical
  let N := G.neighborFinset v
  let XF := terminalFinset terminal
  have hrangeXF : Set.range terminal = (XF : Set V) := by
    ext z
    simp [XF, terminalFinset]
  have hX : X = (XF : Set V) := hXrange.trans hrangeXF
  have hterminal (z : Sum ι ι) : terminal z ∈ XF :=
    mem_terminalFinset terminal z
  have hselected :
      (N ∩ P.selectedSupports).card ≤ 3 * P.active.card := by
    rw [selectedSupports, Finset.inter_biUnion]
    calc
      (P.active.attach.biUnion fun i =>
          N ∩ (P.path i).support.toFinset).card ≤
          ∑ i ∈ P.active.attach,
            (N ∩ (P.path i).support.toFinset).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ P.active.attach, 3 := by
        gcongr with i hi
        exact P.card_neighbors_on_path_le_three_of_optimal XF hX hterminal
          hoptimal.2 hv i
      _ = 3 * P.active.card := by simp [Nat.mul_comm]
  have hinactive :
      (N ∩ P.inactiveTerminals).card ≤
        Fintype.card ι - P.active.card := by
    unfold inactiveTerminals
    rw [Finset.inter_biUnion]
    calc
      ((Finset.univ.filter fun i => i ∉ P.active).biUnion fun i =>
          N ∩ ({terminal (.inl i), terminal (.inr i)} : Finset V)).card ≤
          ∑ i ∈ (Finset.univ.filter fun i => i ∉ P.active),
            (N ∩ ({terminal (.inl i), terminal (.inr i)} : Finset V)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ.filter fun i => i ∉ P.active), 1 := by
        gcongr with i hi
        have hi' : i ∉ P.active := (Finset.mem_filter.mp hi).2
        exact P.card_neighbors_inactive_pair_le_one XF hX hterminal
          hoptimal.1 hv hi'
      _ = Fintype.card ι - P.active.card := by
        have hfilter :
            (Finset.univ.filter fun i : ι => i ∉ P.active).card =
              Fintype.card ι - P.active.card := by
          rw [show (Finset.univ.filter fun i : ι => i ∉ P.active) =
              Finset.univ \ P.active by ext i; simp]
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
            Finset.card_univ]
        simp [hfilter]
  have hcover := P.usedVertices_subset_selectedSupports_union_inactiveTerminals
  have htotal :
      (N ∩ P.usedVertices XF).card ≤
        (N ∩ P.selectedSupports).card +
          (N ∩ P.inactiveTerminals).card := by
    calc
      (N ∩ P.usedVertices XF).card ≤
          (N ∩ (P.selectedSupports ∪ P.inactiveTerminals)).card := by
        apply Finset.card_le_card
        intro z hz
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
          hcover (Finset.mem_inter.mp hz).2⟩
      _ = ((N ∩ P.selectedSupports) ∪
          (N ∩ P.inactiveTerminals)).card := by
        congr 1
        exact Finset.inter_union_distrib_left N _ _
      _ ≤ (N ∩ P.selectedSupports).card +
          (N ∩ P.inactiveTerminals).card := Finset.card_union_le _ _
  have hactive : P.active.card ≤ Fintype.card ι := Finset.card_le_univ _
  change (N ∩ P.usedVertices XF).card ≤ 3 * Fintype.card ι
  omega

/-- Maximality forbids a short route for an inactive pair whose nonterminal
vertices all lie outside the used set. -/
lemma no_short_external_walk_of_optimal
    (P : ShortPartialLinkage G (Set.range terminal) terminal)
    (hmaximal : ∀ Q : ShortPartialLinkage G (Set.range terminal) terminal,
      Q.active.card ≤ P.active.card)
    {i : ι} (hi : i ∉ P.active) :
    ¬∃ p : G.Walk (terminal (.inl i)) (terminal (.inr i)),
      p.length ≤ 7 ∧
      ∀ z ∈ p.support,
        z ≠ terminal (.inl i) → z ≠ terminal (.inr i) →
          z ∉ P.usedVertices (terminalFinset terminal) := by
  classical
  rintro ⟨p, hplen, hexternal⟩
  let q : G.Walk (terminal (.inl i)) (terminal (.inr i)) := p.bypass
  have hqpath : q.IsPath := SimpleGraph.Walk.bypass_isPath _
  have hqlen : q.length ≤ 7 := p.length_bypass_le_length.trans hplen
  have hqsub : q.support ⊆ p.support := p.support_bypass_subset_support
  have havoid : Disjoint (Erdos718.walkInteriorSet q) (Set.range terminal) := by
    rw [Set.disjoint_left]
    intro z hzq hzterm
    have hzused : z ∈ P.usedVertices (terminalFinset terminal) := by
      apply Finset.mem_union_left
      obtain ⟨w, rfl⟩ := hzterm
      exact mem_terminalFinset terminal w
    exact hexternal z (hqsub hzq.1) hzq.2.1 hzq.2.2 hzused
  have hterminalRange (z : Sum ι ι) : terminal z ∈ Set.range terminal :=
    ⟨z, rfl⟩
  have hdisj : ∀ j : P.active,
      Disjoint {z | z ∈ q.support} {z | z ∈ (P.path j).support} := by
    intro j
    rw [Set.disjoint_left]
    intro z hzq hzj
    by_cases hzl : z = terminal (.inl i)
    · subst z
      apply P.terminal_not_mem_selected_path hterminalRange (.inl i) j
      · intro h
        exact hi (Sum.inl_injective h ▸ j.2)
      · intro h
        cases h
      · exact hzj
    by_cases hzr : z = terminal (.inr i)
    · subst z
      apply P.terminal_not_mem_selected_path hterminalRange (.inr i) j
      · intro h
        cases h
      · intro h
        exact hi (Sum.inr_injective h ▸ j.2)
      · exact hzj
    exact hexternal z (hqsub hzq) hzl hzr
      (P.support_subset_usedVertices (terminalFinset terminal)
        (mem_terminalFinset terminal) j (List.mem_toFinset.mpr hzj))
  let Q := P.insert i hi q hqpath hqlen havoid hdisj
  have hQcard : Q.active.card = P.active.card + 1 := by
    simp only [Q, active_insert, Finset.card_cons]
  have := hmaximal Q
  omega

/-- Vertices outside `L` reachable from `s` by a walk of length at most
three which leaves `L` immediately. -/
noncomputable def shortReach (G : SimpleGraph V) (L : Finset V) (s : V) :
    Finset V := by
  classical
  exact Finset.univ.filter fun z =>
    z ∉ L ∧ ∃ p : G.Walk s z, p.length ≤ 3 ∧
      ∀ w ∈ p.support, w ≠ s → w ∉ L

lemma mem_shortReach_iff (G : SimpleGraph V) (L : Finset V) (s z : V) :
    z ∈ shortReach G L s ↔
      z ∉ L ∧ ∃ p : G.Walk s z, p.length ≤ 3 ∧
        ∀ w ∈ p.support, w ≠ s → w ∉ L := by
  classical
  simp [shortReach]

lemma neighbor_mem_shortReach [DecidableRel G.Adj]
    (L : Finset V) {s x : V} (hsx : G.Adj s x) (hx : x ∉ L) :
    x ∈ shortReach G L s := by
  rw [mem_shortReach_iff]
  refine ⟨hx, hsx.toWalk, by simp, ?_⟩
  intro w hw hws
  rw [hsx.support_toWalk] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  exact hw.resolve_left hws ▸ hx

lemma shortReach_disjoint_of_no_short_external
    (P : ShortPartialLinkage G (Set.range terminal) terminal)
    (hmaximal : ∀ Q : ShortPartialLinkage G (Set.range terminal) terminal,
      Q.active.card ≤ P.active.card)
    {i : ι} (hi : i ∉ P.active) :
    Disjoint
      (shortReach G (P.usedVertices (terminalFinset terminal))
        (terminal (.inl i)))
      (shortReach G (P.usedVertices (terminalFinset terminal))
        (terminal (.inr i))) := by
  classical
  let L := P.usedVertices (terminalFinset terminal)
  rw [Finset.disjoint_left]
  intro z hzS hzT
  rw [mem_shortReach_iff] at hzS hzT
  obtain ⟨hzL, p, hpLen, hpExt⟩ := hzS
  obtain ⟨_hzL', q, hqLen, hqExt⟩ := hzT
  apply P.no_short_external_walk_of_optimal hmaximal hi
  refine ⟨p.append q.reverse, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse]
    omega
  · intro w hw hws hwt
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hw
    rcases hw with hwp | hwq
    · exact hpExt w hwp hws
    · exact hqExt w (List.mem_reverse.mp hwq) hwt

lemma shortReach_noCross_of_no_short_external
    (P : ShortPartialLinkage G (Set.range terminal) terminal)
    (hmaximal : ∀ Q : ShortPartialLinkage G (Set.range terminal) terminal,
      Q.active.card ≤ P.active.card)
    {i : ι} (hi : i ∉ P.active) {z w : V}
    (hz : z ∈ shortReach G (P.usedVertices (terminalFinset terminal))
      (terminal (.inl i)))
    (hw : w ∈ shortReach G (P.usedVertices (terminalFinset terminal))
      (terminal (.inr i))) :
    ¬G.Adj z w := by
  classical
  intro hzw
  let L := P.usedVertices (terminalFinset terminal)
  rw [mem_shortReach_iff] at hz hw
  obtain ⟨hzL, p, hpLen, hpExt⟩ := hz
  obtain ⟨hwL, q, hqLen, hqExt⟩ := hw
  apply P.no_short_external_walk_of_optimal hmaximal hi
  refine ⟨(p.concat hzw).append q.reverse, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse]
    omega
  · intro u hu hus hut
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hu
    rcases hu with hup | huq
    · rw [SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton] at hup
      rcases hup with hup | rfl
      · exact hpExt u hup hus
      · exact hwL
    · exact hqExt u (List.mem_reverse.mp huq) hut

def outsideNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Finset V) (v : V) : Finset V :=
  (G.neighborFinset v).filter fun w => w ∉ L

lemma mem_outsideNeighbors_iff [DecidableRel G.Adj]
    (L : Finset V) (v w : V) :
    w ∈ outsideNeighbors G L v ↔ G.Adj v w ∧ w ∉ L := by
  simp [outsideNeighbors]

lemma card_outsideNeighbors_ge
    [DecidableRel G.Adj]
    (P : ShortPartialLinkage G (Set.range terminal) terminal)
    (hoptimal :
      (∀ Q : ShortPartialLinkage G (Set.range terminal) terminal,
        Q.active.card ≤ P.active.card) ∧
      (∀ Q : ShortPartialLinkage G (Set.range terminal) terminal,
        Q.active.card = P.active.card → P.totalLength ≤ Q.totalLength))
    (k : ℕ) (hcardι : Fintype.card ι = k)
    (hdegree : ∀ v, 8 * k ≤ G.degree v)
    {v : V} (hv : v ∉ P.usedVertices (terminalFinset terminal)) :
    5 * k ≤ (outsideNeighbors G
      (P.usedVertices (terminalFinset terminal)) v).card := by
  classical
  let L := P.usedVertices (terminalFinset terminal)
  let N := G.neighborFinset v
  have hinside : (N.filter fun w => w ∈ L).card ≤ 3 * k := by
    have h := P.card_neighbors_usedVertices_le_three_mul rfl hoptimal hv
    rw [hcardι] at h
    have heq : (N.filter fun w => w ∈ L) = N ∩ L := by
      ext w
      simp
    rw [heq]
    exact h
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := N) (p := fun w => w ∈ L)
  have hdeg : 8 * k ≤ N.card := by
    simpa [N] using hdegree v
  unfold outsideNeighbors
  change 5 * k ≤ (N.filter fun w => w ∉ L).card
  have houtEq : (N.filter fun w => w ∉ L) =
      N.filter fun w => ¬w ∈ L := by rfl
  rw [houtEq]
  omega

lemma one_step_mem_shortReach [DecidableRel G.Adj]
    (L : Finset V) {s x u : V} (hsx : G.Adj s x) (hxL : x ∉ L)
    (hxu : G.Adj x u) (huL : u ∉ L) :
    u ∈ shortReach G L s := by
  rw [mem_shortReach_iff]
  refine ⟨huL, hsx.toWalk.concat hxu, by simp, ?_⟩
  intro w hw hws
  simp only [SimpleGraph.Walk.support_concat,
    SimpleGraph.Adj.support_toWalk, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with (hws' | hwx) | hwu
  · exact (hws hws').elim
  · exact hwx ▸ hxL
  · exact hwu ▸ huL

lemma two_step_mem_shortReach [DecidableRel G.Adj]
    (L : Finset V) {s x u w : V} (hsx : G.Adj s x) (hxL : x ∉ L)
    (hxu : G.Adj x u) (huL : u ∉ L)
    (huw : G.Adj u w) (hwL : w ∉ L) :
    w ∈ shortReach G L s := by
  rw [mem_shortReach_iff]
  refine ⟨hwL, (hsx.toWalk.concat hxu).concat huw, by simp, ?_⟩
  intro z hz hzs
  simp only [SimpleGraph.Walk.support_concat,
    SimpleGraph.Adj.support_toWalk, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz with ((hzs' | hzx) | hzu) | hzw
  · exact (hzs hzs').elim
  · exact hzx ▸ hxL
  · exact hzu ▸ huL
  · exact hzw ▸ hwL

end ShortPartialLinkage

/-! ### Thomas--Wollan's small dense linked subgraph -/

structure KLinkedSubgraph (G : SimpleGraph V) (k : ℕ) where
  W : Type u
  fintypeW : Fintype W
  H : SimpleGraph W
  inclusion : H ↪g G
  enough_vertices : 2 * k ≤ Fintype.card W
  linked : Erdos718.IsKLinked H k

attribute [instance] KLinkedSubgraph.fintypeW

/-- Complete graphs are linked: use the prescribed terminal edges themselves.
This elementary form is useful for the `k = 1` endpoint of the dense
subgraph theorem. -/
theorem completeGraph_isKLinked (α : Type*) (k : ℕ) :
    Erdos718.IsKLinked (SimpleGraph.completeGraph α) k := by
  classical
  intro X hX hXcard ι _ terminal hterminal
  let p (i : ι) : (SimpleGraph.completeGraph α).Walk
      (terminal (.inl i)) (terminal (.inr i)) :=
    (show (SimpleGraph.completeGraph α).Adj
      (terminal (.inl i)) (terminal (.inr i)) by
        simp [terminal.injective.ne Sum.inl_ne_inr]).toWalk
  have hp (i : ι) : (p i).IsPath := SimpleGraph.Adj.isPath_toWalk _
  refine ⟨{
    path := p
    isPath := hp
    avoids := fun i => ?_
    disjoint := fun i j hij => ?_
  }⟩
  · rw [Set.disjoint_left]
    intro z hz hXz
    simp only [p, Erdos718.walkInteriorSet,
      SimpleGraph.Adj.support_toWalk, List.mem_cons,
      List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hz
    rcases hz.1 with hz' | hz'
    · exact hz.2.1 hz'
    · exact hz.2.2 hz'
  · change Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}
    rw [Set.disjoint_left]
    intro z hzi hzj
    simp only [p, SimpleGraph.Adj.support_toWalk, List.mem_cons,
      List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hzi hzj
    rcases hzi with hzi | hzi <;> rcases hzj with hzj | hzj
    · apply hij
      exact Sum.inl.inj (terminal.injective (hzi.symm.trans hzj))
    · exact terminal.injective.ne Sum.inl_ne_inr (hzi.symm.trans hzj)
    · exact terminal.injective.ne Sum.inr_ne_inl (hzi.symm.trans hzj)
    · apply hij
      exact Sum.inr.inj (terminal.injective (hzi.symm.trans hzj))

/-- The two endpoints of an edge induce a `1`-linked subgraph. -/
theorem exists_oneLinkedSubgraph_of_adj (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    Nonempty (KLinkedSubgraph G 1) := by
  classical
  let S : Set V := {u, v}
  have hcomplete : G.induce S = SimpleGraph.completeGraph S := by
    ext a b
    change G.Adj (a : V) (b : V) ↔ a ≠ b
    constructor
    · intro h hab
      exact h.ne (congrArg Subtype.val hab)
    · intro hab
      have ha : (a : V) ∈ ({u, v} : Set V) := a.property
      have hb : (b : V) ∈ ({u, v} : Set V) := b.property
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (hab (Subtype.ext (ha.trans hb.symm))).elim
      · simpa [ha, hb] using huv
      · simpa [ha, hb] using huv.symm
      · exact (hab (Subtype.ext (ha.trans hb.symm))).elim
  refine ⟨{
    W := S
    fintypeW := inferInstance
    H := G.induce S
    inclusion := SimpleGraph.Embedding.induce S
    enough_vertices := ?_
    linked := ?_
  }⟩
  · simp [S, huv.ne]
  · rw [hcomplete]
    exact completeGraph_isKLinked S 1

/-- Thomas--Wollan, Theorem 1.5, in the exact-terminal form used in its
proof.  The argument has one vertex of harmless slack: a graph of order at
most `16k + 1` and minimum degree at least `8k`
which fails one prescribed `k`-pair linkage contains a genuine `k`-linked
subgraph. -/
theorem exists_kLinkedSubgraph_of_unlinked_exact
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 2 ≤ k)
    (hcard : Fintype.card V ≤ 16 * k + 1)
    (hdegree : ∀ v, 8 * k ≤ G.degree v)
    (terminal : Sum (Fin k) (Fin k) ↪ V)
    (hno : ¬Nonempty
      (Erdos718.PairLinkage G (Set.range terminal) terminal)) :
    Nonempty (KLinkedSubgraph G k) := by
  classical
  obtain ⟨P, hPmax, hPmin⟩ :=
    ShortPartialLinkage.exists_lexicographically_optimal
      G (Set.range terminal) terminal
  have hPcard : P.active.card < k := by
    simpa using P.active_card_lt_of_no_linkage hno
  obtain ⟨i, hi⟩ : ∃ i : Fin k, i ∉ P.active := by
    by_contra h
    push_neg at h
    have hfull : P.active = Finset.univ := Finset.eq_univ_of_forall h
    have : P.active.card = k := by simp [hfull]
    omega
  let XF := ShortPartialLinkage.terminalFinset terminal
  let L := P.usedVertices XF
  have hterminal (z : Sum (Fin k) (Fin k)) : terminal z ∈ XF :=
    ShortPartialLinkage.mem_terminalFinset terminal z
  have hLcard : L.card ≤ 8 * k - 6 := by
    dsimp [L]
    have h := P.card_usedVertices_le XF
    have hXFcard : XF.card = 2 * k := by
      simpa [XF] using ShortPartialLinkage.card_terminalFinset terminal
    omega
  have endpoint_has_outside_neighbor (s : V) :
      ∃ x : V, G.Adj s x ∧ x ∉ L := by
    by_contra hn
    push_neg at hn
    have hsub : G.neighborFinset s ⊆ L := by
      intro x hx
      exact hn x (G.mem_neighborFinset s x |>.mp hx)
    have hdegCard : 8 * k ≤ (G.neighborFinset s).card := by
      simpa using hdegree s
    have := Finset.card_le_card hsub
    omega
  obtain ⟨x, hsx, hxL⟩ := endpoint_has_outside_neighbor (terminal (.inl i))
  obtain ⟨y, hty, hyL⟩ := endpoint_has_outside_neighbor (terminal (.inr i))
  have hyt : G.Adj y (terminal (.inr i)) := hty.symm
  let S := ShortPartialLinkage.shortReach G L (terminal (.inl i))
  let T := ShortPartialLinkage.shortReach G L (terminal (.inr i))
  letI fintypeS : Fintype (S : Set V) := FinsetCoe.fintype S
  letI fintypeT : Fintype (T : Set V) := FinsetCoe.fintype T
  have hxS : x ∈ S := by
    exact ShortPartialLinkage.neighbor_mem_shortReach L hsx hxL
  have hyT : y ∈ T := by
    exact ShortPartialLinkage.neighbor_mem_shortReach L hty hyL
  have hST : Disjoint S T := by
    exact P.shortReach_disjoint_of_no_short_external hPmax hi
  have hNoCross : ∀ z ∈ S, ∀ w ∈ T, ¬G.Adj z w := by
    intro z hz w hw
    exact P.shortReach_noCross_of_no_short_external hPmax hi hz hw
  let W := Finset.univ.filter fun v => v ∉ L
  have hScardW : S ⊆ W := by
    intro z hz
    have hz' : z ∈ ShortPartialLinkage.shortReach G L (terminal (.inl i)) := by
      simpa [S] using hz
    have hz'' := (ShortPartialLinkage.mem_shortReach_iff
      (G := G) (L := L) (s := terminal (.inl i)) (z := z)).mp hz'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz''.1⟩
  have hTcardW : T ⊆ W := by
    intro z hz
    have hz' : z ∈ ShortPartialLinkage.shortReach G L (terminal (.inr i)) := by
      simpa [T] using hz
    have hz'' := (ShortPartialLinkage.mem_shortReach_iff
      (G := G) (L := L) (s := terminal (.inr i)) (z := z)).mp hz'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz''.1⟩
  have hWcard : W.card ≤ 14 * k + 1 := by
    have htermSub : XF ⊆ L := Finset.subset_union_left
    have hLlower : 2 * k ≤ L.card := by
      have := Finset.card_le_card htermSub
      have hXFcard : XF.card = 2 * k := by
        simpa [XF] using ShortPartialLinkage.card_terminalFinset terminal
      omega
    have hWeq : W.card = Fintype.card V - L.card := by
      rw [show W = Finset.univ \ L by ext z; simp [W]]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  have houtside (v : V) (hv : v ∉ L) :
      5 * k ≤ (ShortPartialLinkage.outsideNeighbors G L v).card := by
    exact P.card_outsideNeighbors_ge ⟨hPmax, hPmin⟩ k (by simp) hdegree hv
  have hcover (v : V) (hv : v ∈ W) : v ∈ S ∨ v ∈ T := by
    have hvL : v ∉ L := (Finset.mem_filter.mp hv).2
    by_contra hnot
    push_neg at hnot
    let A := ShortPartialLinkage.outsideNeighbors G L x
    let B := ShortPartialLinkage.outsideNeighbors G L y
    let C := ShortPartialLinkage.outsideNeighbors G L v
    have hAcard : 5 * k ≤ A.card := houtside x hxL
    have hBcard : 5 * k ≤ B.card := houtside y hyL
    have hCcard : 5 * k ≤ C.card := houtside v hvL
    have hAW : A ⊆ W := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (ShortPartialLinkage.mem_outsideNeighbors_iff L x u).mp hu |>.2⟩
    have hBW : B ⊆ W := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (ShortPartialLinkage.mem_outsideNeighbors_iff L y u).mp hu |>.2⟩
    have hCW : C ⊆ W := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (ShortPartialLinkage.mem_outsideNeighbors_iff L v u).mp hu |>.2⟩
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro u huA huB
      have huA' := (ShortPartialLinkage.mem_outsideNeighbors_iff L x u).mp huA
      have huB' := (ShortPartialLinkage.mem_outsideNeighbors_iff L y u).mp huB
      exact (Finset.disjoint_left.mp hST)
        (ShortPartialLinkage.one_step_mem_shortReach L hsx hxL huA'.1 huA'.2)
        (ShortPartialLinkage.one_step_mem_shortReach L hty hyL huB'.1 huB'.2)
    have hAC : Disjoint A C := by
      rw [Finset.disjoint_left]
      intro u huA huC
      have huA' := (ShortPartialLinkage.mem_outsideNeighbors_iff L x u).mp huA
      have huC' := (ShortPartialLinkage.mem_outsideNeighbors_iff L v u).mp huC
      exact hnot.1 (ShortPartialLinkage.two_step_mem_shortReach L hsx hxL
        huA'.1 huA'.2 huC'.1.symm hvL)
    have hBC : Disjoint B C := by
      rw [Finset.disjoint_left]
      intro u huB huC
      have huB' := (ShortPartialLinkage.mem_outsideNeighbors_iff L y u).mp huB
      have huC' := (ShortPartialLinkage.mem_outsideNeighbors_iff L v u).mp huC
      exact hnot.2 (ShortPartialLinkage.two_step_mem_shortReach L hty hyL
        huB'.1 huB'.2 huC'.1.symm hvL)
    have hABCsub : (A ∪ B) ∪ C ⊆ W := by
      intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · rcases Finset.mem_union.mp hu with hu | hu
        · exact hAW hu
        · exact hBW hu
      · exact hCW hu
    have hABCcard : A.card + B.card + C.card = ((A ∪ B) ∪ C).card := by
      calc
        A.card + B.card + C.card = (A ∪ B).card + C.card := by
          rw [Finset.card_union_of_disjoint hAB]
        _ = ((A ∪ B) ∪ C).card := by
          rw [Finset.card_union_of_disjoint
            (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩)]
    have hle := Finset.card_le_card hABCsub
    omega
  have hSTeqW : S ∪ T = W := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hScardW hTcardW
    · intro v hv
      exact Finset.mem_union.mpr (hcover v hv)
  have hsumST : S.card + T.card = W.card := by
    rw [← Finset.card_union_of_disjoint hST, hSTeqW]
  have hdegreeS : ∀ z : (S : Set V),
      5 * k ≤ (G.induce (S : Set V)).degree z := by
    intro z
    have hzL : (z : V) ∉ L := (Finset.mem_filter.mp (hScardW z.2)).2
    have hout := houtside z hzL
    have hsub : ShortPartialLinkage.outsideNeighbors G L z ⊆
        G.neighborFinset z ∩ S := by
      intro u hu
      have hu' := (ShortPartialLinkage.mem_outsideNeighbors_iff L z u).mp hu
      have huW : u ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'.2⟩
      have huST := hcover u huW
      have huS : u ∈ S := huST.resolve_right fun huT =>
        hNoCross z z.2 u huT hu'.1
      exact Finset.mem_inter.mpr ⟨by simpa using hu'.1, huS⟩
    have hc := Finset.card_le_card hsub
    have heq : ((G.induce (S : Set V)).neighborFinset z).map
        (Function.Embedding.subtype _) = G.neighborFinset z ∩ S := by
      ext u
      simp
    have hm := congrArg Finset.card heq
    simp only [Finset.card_map] at hm
    calc
      5 * k ≤ (ShortPartialLinkage.outsideNeighbors G L z).card := hout
      _ ≤ (G.neighborFinset z ∩ S).card := hc
      _ = ((G.induce (S : Set V)).neighborFinset z).card := by
        simpa using hm.symm
      _ = (G.induce (S : Set V)).degree z :=
        (G.induce (S : Set V)).card_neighborFinset_eq_degree z
  have hdegreeT : ∀ z : (T : Set V),
      5 * k ≤ (G.induce (T : Set V)).degree z := by
    intro z
    have hzL : (z : V) ∉ L := (Finset.mem_filter.mp (hTcardW z.2)).2
    have hout := houtside z hzL
    have hsub : ShortPartialLinkage.outsideNeighbors G L z ⊆
        G.neighborFinset z ∩ T := by
      intro u hu
      have hu' := (ShortPartialLinkage.mem_outsideNeighbors_iff L z u).mp hu
      have huW : u ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'.2⟩
      have huST := hcover u huW
      have huT : u ∈ T := huST.resolve_left fun huS =>
        hNoCross u huS z z.2 hu'.1.symm
      exact Finset.mem_inter.mpr ⟨by simpa using hu'.1, huT⟩
    have hc := Finset.card_le_card hsub
    have heq : ((G.induce (T : Set V)).neighborFinset z).map
        (Function.Embedding.subtype _) = G.neighborFinset z ∩ T := by
      ext u
      simp
    have hm := congrArg Finset.card heq
    simp only [Finset.card_map] at hm
    calc
      5 * k ≤ (ShortPartialLinkage.outsideNeighbors G L z).card := hout
      _ ≤ (G.neighborFinset z ∩ T).card := hc
      _ = ((G.induce (T : Set V)).neighborFinset z).card := by
        simpa using hm.symm
      _ = (G.induce (T : Set V)).degree z :=
        (G.induce (T : Set V)).card_neighborFinset_eq_degree z
  by_cases hsmall : S.card ≤ T.card
  · have hScard : S.card ≤ 7 * k := by omega
    have hlinked : Erdos718.IsKLinked (G.induce (S : Set V)) k := by
      apply isKLinked_of_minDegree_card (G.induce (S : Set V)) k (5 * k)
      · exact hdegreeS
      · simpa using (show S.card + 3 * k ≤ 2 * (5 * k) + 4 by omega)
    have henough : 2 * k ≤ Fintype.card (S : Set V) := by
      have hxdeg := hdegreeS ⟨x, hxS⟩
      have hxlt := (G.induce (S : Set V)).degree_lt_card_verts ⟨x, hxS⟩
      have hcardS : Fintype.card (S : Set V) = S.card := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
          Set.ncard_coe_finset]
      rw [hcardS]
      omega
    exact ⟨{
      W := (S : Set V)
      fintypeW := inferInstance
      H := G.induce (S : Set V)
      inclusion := SimpleGraph.Embedding.induce (S : Set V)
      enough_vertices := henough
      linked := hlinked
    }⟩
  · have hTcard : T.card ≤ 7 * k := by omega
    have hlinked : Erdos718.IsKLinked (G.induce (T : Set V)) k := by
      apply isKLinked_of_minDegree_card (G.induce (T : Set V)) k (5 * k)
      · exact hdegreeT
      · simpa using (show T.card + 3 * k ≤ 2 * (5 * k) + 4 by omega)
    have henough : 2 * k ≤ Fintype.card (T : Set V) := by
      have hydeg := hdegreeT ⟨y, hyT⟩
      have hylt := (G.induce (T : Set V)).degree_lt_card_verts ⟨y, hyT⟩
      have hcardT : Fintype.card (T : Set V) = T.card := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
          Set.ncard_coe_finset]
      rw [hcardT]
      omega
    exact ⟨{
      W := (T : Set V)
      fintypeW := inferInstance
      H := G.induce (T : Set V)
      inclusion := SimpleGraph.Embedding.induce (T : Set V)
      enough_vertices := henough
      linked := hlinked
    }⟩

/-- A failed linkage involving at most `2k` distinguished vertices can be
padded to a failed linkage of exactly `k` pairs.  The padding retains all of
the distinguished vertices among the new terminals, so a linkage for the
padded problem would restrict to one for the original problem. -/
lemma exists_full_unlinked_terminal_of_not_isKLinked
    (G : SimpleGraph V) (k : ℕ)
    (henough : 2 * k ≤ Fintype.card V)
    (hnot : ¬Erdos718.IsKLinked G k) :
    ∃ terminal : Sum (Fin k) (Fin k) ↪ V,
      ¬Nonempty (Erdos718.PairLinkage G (Set.range terminal) terminal) := by
  classical
  rw [Erdos718.IsKLinked] at hnot
  push Not at hnot
  obtain ⟨X, hXfinite, hXcard, hnot⟩ := hnot
  rw [Erdos718.IsLinkedSet] at hnot
  push Not at hnot
  obtain ⟨ι, instι, terminal, hrange, hno⟩ := hnot
  letI : Fintype ι := instι
  letI : Fintype X := hXfinite.fintype
  let terminalX : Sum ι ι ↪ X :=
    ⟨fun z => ⟨terminal z, hrange ⟨z, rfl⟩⟩,
      fun a b hab => terminal.injective (Subtype.ext_iff.mp hab)⟩
  have hιcard : Fintype.card ι ≤ k := by
    have hsum := Fintype.card_le_of_embedding terminalX
    have hcardX : Fintype.card X = X.ncard := Set.fintypeCard_eq_ncard X
    rw [hcardX] at hsum
    simp only [Fintype.card_sum] at hsum
    omega
  let base : ι ↪ Fin k :=
    (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hιcard)
  let sumBase : Sum ι ι ↪ Sum (Fin k) (Fin k) :=
    Function.Embedding.sumMap base base
  obtain ⟨xpos₀⟩ : Nonempty (X ↪ Sum (Fin k) (Fin k)) := by
    apply Function.Embedding.nonempty_of_card_le
    have hcardX : Fintype.card X = X.ncard := Set.fintypeCard_eq_ncard X
    rw [hcardX]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair
    (terminalX.trans xpos₀) sumBase
    (terminalX.trans xpos₀).injective sumBase.injective
  let xpos : X ↪ Sum (Fin k) (Fin k) := xpos₀.trans τ.toEmbedding
  have hxpos (z : Sum ι ι) : xpos (terminalX z) = sumBase z := hτ z
  obtain ⟨full₀⟩ : Nonempty (Sum (Fin k) (Fin k) ↪ V) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (xpos.trans full₀) (Function.Embedding.subtype fun z => z ∈ X)
    (xpos.trans full₀).injective
    (Function.Embedding.subtype fun z => z ∈ X).injective
  let full : Sum (Fin k) (Fin k) ↪ V := full₀.trans σ.toEmbedding
  have hfullX (z : X) : full (xpos z) = (z : V) := hσ z
  have hfullOriginal (z : Sum ι ι) : full (sumBase z) = terminal z := by
    calc
      full (sumBase z) = full (xpos (terminalX z)) := by rw [hxpos]
      _ = (terminalX z : V) := hfullX (terminalX z)
      _ = terminal z := rfl
  refine ⟨full, ?_⟩
  rintro ⟨L⟩
  let smallTerminal : Sum ι ι ↪ V := sumBase.trans full
  have hsmallTerminal : smallTerminal = terminal := by
    ext z
    exact hfullOriginal z
  have hXsub : X ⊆ Set.range full := by
    intro z hz
    exact ⟨xpos ⟨z, hz⟩, hfullX ⟨z, hz⟩⟩
  have Lsmall : Erdos718.PairLinkage G X smallTerminal := {
    path := fun i => L.path (base i)
    isPath := fun i => L.isPath (base i)
    avoids := fun i => (L.avoids (base i)).mono_right hXsub
    disjoint := fun i j hij => L.disjoint (base.injective.ne hij)
  }
  rw [hsmallTerminal] at Lsmall
  exact hno.false Lsmall

/-- Thomas--Wollan, Theorem 1.5, with the one-vertex slack present in its
proof: a nonempty graph of order at most `16k + 1` and minimum degree at
least `8k` contains a `k`-linked subgraph. -/
theorem exists_kLinkedSubgraph_of_minDegree_card
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hV : Nonempty V)
    (hcard : Fintype.card V ≤ 16 * k + 1)
    (hdegree : ∀ v, 8 * k ≤ G.degree v) :
    Nonempty (KLinkedSubgraph G k) := by
  classical
  by_cases hkone : k = 1
  · subst k
    let v := Classical.choice hV
    have hvpos : 0 < G.degree v := by
      have := hdegree v
      omega
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hvpos
    exact exists_oneLinkedSubgraph_of_adj G hvw
  have hktwo : 2 ≤ k := by omega
  have henough : 2 * k ≤ Fintype.card V := by
    let v := Classical.choice hV
    have hvdeg := hdegree v
    have hvlt := G.degree_lt_card_verts v
    omega
  by_cases hlinked : Erdos718.IsKLinked G k
  · exact ⟨{
      W := V
      fintypeW := inferInstance
      H := G
      inclusion := SimpleGraph.Embedding.refl
      enough_vertices := henough
      linked := hlinked
    }⟩
  · obtain ⟨terminal, hterminal⟩ :=
      exists_full_unlinked_terminal_of_not_isKLinked G k henough hlinked
    exact exists_kLinkedSubgraph_of_unlinked_exact
      G k hktwo hcard hdegree terminal hterminal

end ThomasWollan
end Erdos717
