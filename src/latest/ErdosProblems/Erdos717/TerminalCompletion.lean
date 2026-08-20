/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Completing all harmless edges among a prescribed set of paired terminals.

An added terminal--terminal edge cannot occur in a linkage whose interiors
avoid the terminal set, unless it directly joins one of the prescribed
pairs.  The completion deliberately omits precisely those pair edges.
-/

import ErdosProblems.Erdos717.ThomasWollanMassed

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

universe u v

variable {V : Type u} {ι : Type v}

/-- The finset image of a finite terminal embedding. -/
noncomputable def terminalFinset [Fintype ι]
    (terminal : Sum ι ι ↪ V) : Finset V := by
  classical
  exact Finset.univ.map terminal

@[simp] lemma mem_terminalFinset [Fintype ι] {terminal : Sum ι ι ↪ V}
    {x : V} :
    x ∈ terminalFinset terminal ↔ x ∈ Set.range terminal := by
  classical
  simp [terminalFinset]

lemma card_terminalFinset [Fintype ι] (terminal : Sum ι ι ↪ V) :
    (terminalFinset terminal).card = 2 * Fintype.card ι := by
  classical
  simp [terminalFinset, Fintype.card_sum]
  omega

/-- The symmetric relation saying that two vertices are one of the
prescribed terminal pairs. -/
def ArePaired (terminal : Sum ι ι ↪ V) (u v : V) : Prop :=
  ∃ i, (u = terminal (.inl i) ∧ v = terminal (.inr i)) ∨
    (u = terminal (.inr i) ∧ v = terminal (.inl i))

lemma arePaired_symm {terminal : Sum ι ι ↪ V} {u v : V} :
    ArePaired terminal u v ↔ ArePaired terminal v u := by
  constructor <;> rintro ⟨i, h | h⟩
  · exact ⟨i, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨i, Or.inl ⟨h.2, h.1⟩⟩
  · exact ⟨i, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨i, Or.inl ⟨h.2, h.1⟩⟩

lemma arePaired_prescribed (terminal : Sum ι ι ↪ V) (i : ι) :
    ArePaired terminal (terminal (.inl i)) (terminal (.inr i)) :=
  ⟨i, Or.inl ⟨rfl, rfl⟩⟩

/-- A vertex has at most one partner in a prescribed pairing. -/
lemma arePaired_left_unique {terminal : Sum ι ι ↪ V} {a x y : V}
    (hax : ArePaired terminal a x) (hay : ArePaired terminal a y) :
    x = y := by
  rcases hax with ⟨i, hi | hi⟩ <;>
    rcases hay with ⟨j, hj | hj⟩
  · have hij : i = j := by
      apply Sum.inl_injective
      apply terminal.injective
      exact hi.1.symm.trans hj.1
    subst j
    exact hi.2.trans hj.2.symm
  · have : (Sum.inl i : Sum ι ι) = Sum.inr j := by
      apply terminal.injective
      exact hi.1.symm.trans hj.1
    exact (Sum.inl_ne_inr this).elim
  · have : (Sum.inr i : Sum ι ι) = Sum.inl j := by
      apply terminal.injective
      exact hi.1.symm.trans hj.1
    exact (Sum.inr_ne_inl this).elim
  · have hij : i = j := by
      apply Sum.inr_injective
      apply terminal.injective
      exact hi.1.symm.trans hj.1
    subst j
    exact hi.2.trans hj.2.symm

/-- The graph of all terminal--terminal edges except the prescribed pair
edges.  `fromRel` supplies symmetry and removes loops. -/
def harmlessTerminalGraph (terminal : Sum ι ι ↪ V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v =>
    u ∈ Set.range terminal ∧ v ∈ Set.range terminal ∧
      ¬ ArePaired terminal u v

/-- Add every harmless edge inside the terminal set. -/
def terminalCompletion (G : SimpleGraph V) (terminal : Sum ι ι ↪ V) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∨ (harmlessTerminalGraph terminal).Adj u v
  symm.symm _ _ := Or.imp G.adj_symm (harmlessTerminalGraph terminal).adj_symm

lemma le_terminalCompletion (G : SimpleGraph V) (terminal : Sum ι ι ↪ V) :
    G ≤ terminalCompletion G terminal :=
  fun _ _ h => Or.inl h

lemma harmlessTerminalGraph_adj_iff {terminal : Sum ι ι ↪ V} {u v : V} :
    (harmlessTerminalGraph terminal).Adj u v ↔
      u ≠ v ∧ u ∈ Set.range terminal ∧ v ∈ Set.range terminal ∧
        ¬ ArePaired terminal u v := by
  rw [harmlessTerminalGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, h.2.1, h.1, fun hp => h.2.2 (arePaired_symm.mpr hp)⟩
  · rintro ⟨hne, hu, hv, hp⟩
    exact ⟨hne, Or.inl ⟨hu, hv, hp⟩⟩

lemma terminalCompletion_adj_iff {G : SimpleGraph V}
    {terminal : Sum ι ι ↪ V} {u v : V} :
    (terminalCompletion G terminal).Adj u v ↔
      G.Adj u v ∨
        (u ≠ v ∧ u ∈ Set.range terminal ∧ v ∈ Set.range terminal ∧
          ¬ ArePaired terminal u v) := by
  change (G.Adj u v ∨ (harmlessTerminalGraph terminal).Adj u v) ↔ _
  rw [harmlessTerminalGraph_adj_iff]

/-- On a walk whose interior avoids all terminals, every terminal in its
support is one of its endpoints. -/
lemma terminal_mem_support_eq_endpoint {G : SimpleGraph V}
    {terminal : Sum ι ι ↪ V} {a b z : V} (p : G.Walk a b)
    (havoid : Disjoint (Erdos718.walkInteriorSet p) (Set.range terminal))
    (hzsupport : z ∈ p.support) (hzterminal : z ∈ Set.range terminal) :
    z = a ∨ z = b := by
  by_contra h
  push_neg at h
  exact (Set.disjoint_left.mp havoid) ⟨hzsupport, h.1, h.2⟩ hzterminal

/-- Every edge of one path in a completed linkage was already present in
the original graph. -/
lemma pairLinkage_edge_mem_original [Fintype ι]
    {G : SimpleGraph V} {terminal : Sum ι ι ↪ V}
    (L : Erdos718.PairLinkage (terminalCompletion G terminal)
      (Set.range terminal) terminal) (i : ι) (e : Sym2 V)
    (he : e ∈ (L.path i).edges) : e ∈ G.edgeSet := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj := (L.path i).adj_of_mem_edges he
      rw [terminalCompletion_adj_iff] at hadj
      rcases hadj with hG | hadd
      · exact hG
      · have huSupport := (L.path i).fst_mem_support_of_mem_edges he
        have hvSupport := (L.path i).snd_mem_support_of_mem_edges he
        have huEnd := terminal_mem_support_eq_endpoint (L.path i)
          (L.avoids i) huSupport hadd.2.1
        have hvEnd := terminal_mem_support_eq_endpoint (L.path i)
          (L.avoids i) hvSupport hadd.2.2.1
        exfalso
        apply hadd.2.2.2
        rcases huEnd with hu | hu <;> rcases hvEnd with hv | hv
        · exact (hadd.1 (hu.trans hv.symm)).elim
        · exact ⟨i, Or.inl ⟨hu, hv⟩⟩
        · exact ⟨i, Or.inr ⟨hu, hv⟩⟩
        · exact (hadd.1 (hu.trans hv.symm)).elim

/-- The preceding edge-transfer fact with a larger forbidden terminal set. -/
lemma pairLinkage_edge_mem_original_of_subset [Fintype ι]
    {G : SimpleGraph V} {X : Set V} {terminal : Sum ι ι ↪ V}
    (L : Erdos718.PairLinkage (terminalCompletion G terminal) X terminal)
    (hterminal : Set.range terminal ⊆ X) (i : ι) (e : Sym2 V)
    (he : e ∈ (L.path i).edges) : e ∈ G.edgeSet := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj := (L.path i).adj_of_mem_edges he
      rw [terminalCompletion_adj_iff] at hadj
      rcases hadj with hG | hadd
      · exact hG
      · have havoidsRange : Disjoint
            (Erdos718.walkInteriorSet (L.path i)) (Set.range terminal) :=
          Set.disjoint_of_subset_right hterminal (L.avoids i)
        have huSupport := (L.path i).fst_mem_support_of_mem_edges he
        have hvSupport := (L.path i).snd_mem_support_of_mem_edges he
        have huEnd := terminal_mem_support_eq_endpoint (L.path i)
          havoidsRange huSupport hadd.2.1
        have hvEnd := terminal_mem_support_eq_endpoint (L.path i)
          havoidsRange hvSupport hadd.2.2.1
        exfalso
        apply hadd.2.2.2
        rcases huEnd with hu | hu <;> rcases hvEnd with hv | hv
        · exact (hadd.1 (hu.trans hv.symm)).elim
        · exact ⟨i, Or.inl ⟨hu, hv⟩⟩
        · exact ⟨i, Or.inr ⟨hu, hv⟩⟩
        · exact (hadd.1 (hu.trans hv.symm)).elim

/-- A linkage in the terminal completion transfers back to the original
graph, with exactly the same supports. -/
noncomputable def Erdos718.PairLinkage.ofTerminalCompletion [Fintype ι]
    {G : SimpleGraph V} {terminal : Sum ι ι ↪ V}
    (L : Erdos718.PairLinkage (terminalCompletion G terminal)
      (Set.range terminal) terminal) :
    Erdos718.PairLinkage G (Set.range terminal) terminal where
  path i := (L.path i).transfer G (pairLinkage_edge_mem_original L i)
  isPath i := (L.isPath i).transfer _
  avoids i := by
    simpa only [Erdos718.walkInteriorSet, Set.mem_setOf_eq,
      Walk.support_transfer] using L.avoids i
  disjoint i j hij := by simpa using L.disjoint hij

/-- Transfer a completed linkage back while retaining an arbitrary larger
forbidden set containing all terminals. -/
noncomputable def Erdos718.PairLinkage.ofTerminalCompletionOfSubset
    [Fintype ι] {G : SimpleGraph V} {X : Set V}
    {terminal : Sum ι ι ↪ V}
    (L : Erdos718.PairLinkage (terminalCompletion G terminal) X terminal)
    (hterminal : Set.range terminal ⊆ X) :
    Erdos718.PairLinkage G X terminal where
  path i := (L.path i).transfer G
    (pairLinkage_edge_mem_original_of_subset L hterminal i)
  isPath i := (L.isPath i).transfer _
  avoids i := by
    simpa only [Erdos718.walkInteriorSet, Set.mem_ofPred_eq,
      Walk.support_transfer] using L.avoids i
  disjoint i j hij := by simpa using L.disjoint hij

theorem nonempty_pairLinkage_terminalCompletion_iff [Fintype ι]
    {G : SimpleGraph V} {terminal : Sum ι ι ↪ V} :
    Nonempty (Erdos718.PairLinkage (terminalCompletion G terminal)
      (Set.range terminal) terminal) ↔
    Nonempty (Erdos718.PairLinkage G (Set.range terminal) terminal) := by
  constructor
  · exact Nonempty.map Erdos718.PairLinkage.ofTerminalCompletion
  · exact Nonempty.map (fun L => L.mapLe (le_terminalCompletion G terminal))

/-- Completing terminal edges changes no edge incident with a finset
disjoint from the terminals. -/
lemma incidentEdges_terminalCompletion [Fintype ι] [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (terminal : Sum ι ι ↪ V)
    [DecidableRel G.Adj]
    [DecidableRel (terminalCompletion G terminal).Adj]
    (S : Finset V) (hdisj : Disjoint S (terminalFinset terminal)) :
    incidentEdges (terminalCompletion G terminal) S = incidentEdges G S := by
  classical
  unfold incidentEdges
  congr 1
  ext e
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨he, hinc⟩
    refine ⟨?_, hinc⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
        change (terminalCompletion G terminal).Adj u v at he
        change G.Adj u v
        rw [terminalCompletion_adj_iff] at he
        rcases he with he | hadd
        · exact he
        · exfalso
          apply hinc
          intro z hz
          rw [Sym2.toFinset_mk_eq] at hz
          have hzterm : z ∈ terminalFinset terminal := by
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact mem_terminalFinset.mpr hadd.2.1
            · have hzv : z = v := Finset.mem_singleton.mp hz
              subst z
              exact mem_terminalFinset.mpr hadd.2.2.1
          have hznotS : z ∉ S := by
            intro hzS
            exact Finset.disjoint_left.mp hdisj hzS hzterm
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact hznotS
  · rintro ⟨he, hinc⟩
    refine ⟨?_, hinc⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
        change G.Adj u v at he
        change (terminalCompletion G terminal).Adj u v
        exact le_terminalCompletion G terminal he

/-- The mass conditions are invariant under harmless terminal completion. -/
lemma isEightKMassed_terminalCompletion [Fintype ι] [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (terminal : Sum ι ι ↪ V) (k : ℕ)
    [DecidableRel G.Adj]
    [DecidableRel (terminalCompletion G terminal).Adj]
    (hmassed : IsEightKMassed G (terminalFinset terminal) k) :
    IsEightKMassed (terminalCompletion G terminal)
      (terminalFinset terminal) k := by
  classical
  constructor
  · have houtside : Disjoint
        (Finset.univ \ terminalFinset terminal) (terminalFinset terminal) := by
      exact Finset.sdiff_disjoint
    rw [incidentEdges_terminalCompletion G terminal _ houtside]
    exact hmassed.1
  · intro s hXleft horder
    have hdisj : Disjoint (s.right \ s.left) (terminalFinset terminal) := by
      exact Finset.disjoint_left.mpr fun _ hzRight hzX =>
        (Finset.mem_sdiff.mp hzRight).2 (hXleft hzX)
    let t : Erdos718.Separation G := {
      left := s.left
      right := s.right
      cover := s.cover
      not_adj := by
        intro u v huL huR hvR hvL huv
        exact s.not_adj huL huR hvR hvL
          (le_terminalCompletion G terminal huv)
    }
    rw [incidentEdges_terminalCompletion G terminal _ hdisj]
    simpa [t] using hmassed.2 t hXleft horder

/-- The same invariance for a distinguished finset which merely contains
all the terminals. -/
lemma isEightKMassed_terminalCompletion_of_subset [Fintype ι] [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (terminal : Sum ι ι ↪ V)
    (X : Finset V) (k : ℕ)
    [DecidableRel G.Adj]
    [DecidableRel (terminalCompletion G terminal).Adj]
    (hterminal : terminalFinset terminal ⊆ X)
    (hmassed : IsEightKMassed G X k) :
    IsEightKMassed (terminalCompletion G terminal) X k := by
  constructor
  · have hdisj : Disjoint (Finset.univ \ X) (terminalFinset terminal) :=
      Finset.sdiff_disjoint.mono_right hterminal
    rw [incidentEdges_terminalCompletion G terminal _ hdisj]
    exact hmassed.1
  · intro s hXleft horder
    have hdisj : Disjoint (s.right \ s.left) (terminalFinset terminal) := by
      exact Finset.disjoint_left.mpr fun _ hzRight hzTerminal =>
        (Finset.mem_sdiff.mp hzRight).2
          (hXleft (hterminal hzTerminal))
    let t : Erdos718.Separation G := {
      left := s.left
      right := s.right
      cover := s.cover
      not_adj := by
        intro u v huL huR hvR hvL huv
        exact s.not_adj huL huR hvR hvL
          (le_terminalCompletion G terminal huv)
    }
    rw [incidentEdges_terminalCompletion G terminal _ hdisj]
    simpa [t] using hmassed.2 t hXleft horder

/-- Adding a genuinely new harmless terminal edge strictly increases the
number of edges induced by any finset containing the terminals. -/
lemma edgesOn_lt_terminalCompletion [Fintype ι] [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (terminal : Sum ι ι ↪ V)
    (X : Finset V)
    [DecidableRel G.Adj]
    [DecidableRel (terminalCompletion G terminal).Adj]
    {u v : V} (hu : u ∈ terminalFinset terminal)
    (hv : v ∈ terminalFinset terminal) (hne : u ≠ v)
    (hnotPaired : ¬ArePaired terminal u v) (hnotAdj : ¬G.Adj u v)
    (hterminal : terminalFinset terminal ⊆ X) :
    Erdos718.MaderPrototype.edgesOn G X <
      Erdos718.MaderPrototype.edgesOn (terminalCompletion G terminal) X := by
  unfold Erdos718.MaderPrototype.edgesOn
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he ⊢
    have hedge : e ∈ G.edgeSet := he.1
    have hcomp : e ∈ (terminalCompletion G terminal).edgeSet := by
      induction e using Sym2.inductionOn with
      | _ a b =>
          change G.Adj a b at hedge
          change (terminalCompletion G terminal).Adj a b
          exact le_terminalCompletion G terminal hedge
    exact ⟨hcomp, he.2⟩
  · intro heq
    have hnew : s(u, v) ∈
        ((terminalCompletion G terminal).edgeFinset.filter fun e =>
          e.toFinset ⊆ X) := by
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      refine ⟨?_, hterminal hu, hterminal hv⟩
      change (terminalCompletion G terminal).Adj u v
      rw [terminalCompletion_adj_iff]
      exact Or.inr ⟨hne, mem_terminalFinset.mp hu,
        mem_terminalFinset.mp hv, hnotPaired⟩
    rw [← heq] at hnew
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at hnew
    exact hnotAdj hnew.1

/-! ### Completion of a larger distinguished set -/

/-- Add every edge inside `X` except the prescribed terminal-pair edges. -/
def harmlessSetGraph (X : Set V) (terminal : Sum ι ι ↪ V) :
    SimpleGraph V :=
  SimpleGraph.fromRel fun u v => u ∈ X ∧ v ∈ X ∧
    ¬ArePaired terminal u v

def setCompletion (G : SimpleGraph V) (X : Set V)
    (terminal : Sum ι ι ↪ V) : SimpleGraph V where
  Adj u v := G.Adj u v ∨ (harmlessSetGraph X terminal).Adj u v
  symm.symm _ _ := Or.imp G.adj_symm (harmlessSetGraph X terminal).adj_symm

lemma le_setCompletion (G : SimpleGraph V) (X : Set V)
    (terminal : Sum ι ι ↪ V) : G ≤ setCompletion G X terminal :=
  fun _ _ h => Or.inl h

lemma harmlessSetGraph_adj_iff {X : Set V}
    {terminal : Sum ι ι ↪ V} {u v : V} :
    (harmlessSetGraph X terminal).Adj u v ↔
      u ≠ v ∧ u ∈ X ∧ v ∈ X ∧ ¬ArePaired terminal u v := by
  rw [harmlessSetGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, h.2.1, h.1, fun hp => h.2.2 (arePaired_symm.mpr hp)⟩
  · rintro ⟨hne, hu, hv, hp⟩
    exact ⟨hne, Or.inl ⟨hu, hv, hp⟩⟩

lemma setCompletion_adj_iff {G : SimpleGraph V} {X : Set V}
    {terminal : Sum ι ι ↪ V} {u v : V} :
    (setCompletion G X terminal).Adj u v ↔
      G.Adj u v ∨ (u ≠ v ∧ u ∈ X ∧ v ∈ X ∧
        ¬ArePaired terminal u v) := by
  change (G.Adj u v ∨ (harmlessSetGraph X terminal).Adj u v) ↔ _
  rw [harmlessSetGraph_adj_iff]

lemma pairLinkage_edge_mem_setCompletion [Fintype ι]
    {G : SimpleGraph V} {X : Set V} {terminal : Sum ι ι ↪ V}
    (L : Erdos718.PairLinkage (setCompletion G X terminal) X terminal)
    (i : ι) (e : Sym2 V) (he : e ∈ (L.path i).edges) :
    e ∈ G.edgeSet := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hadj := (L.path i).adj_of_mem_edges he
      rw [setCompletion_adj_iff] at hadj
      rcases hadj with hG | hadd
      · exact hG
      · have huSupport := (L.path i).fst_mem_support_of_mem_edges he
        have hvSupport := (L.path i).snd_mem_support_of_mem_edges he
        have huEnd : u = terminal (.inl i) ∨ u = terminal (.inr i) := by
          by_contra h
          push Not at h
          exact (Set.disjoint_left.mp (L.avoids i))
            ⟨huSupport, h.1, h.2⟩ hadd.2.1
        have hvEnd : v = terminal (.inl i) ∨ v = terminal (.inr i) := by
          by_contra h
          push Not at h
          exact (Set.disjoint_left.mp (L.avoids i))
            ⟨hvSupport, h.1, h.2⟩ hadd.2.2.1
        exfalso
        apply hadd.2.2.2
        rcases huEnd with hu | hu <;> rcases hvEnd with hv | hv
        · exact (hadd.1 (hu.trans hv.symm)).elim
        · exact ⟨i, Or.inl ⟨hu, hv⟩⟩
        · exact ⟨i, Or.inr ⟨hu, hv⟩⟩
        · exact (hadd.1 (hu.trans hv.symm)).elim

noncomputable def Erdos718.PairLinkage.ofSetCompletion [Fintype ι]
    {G : SimpleGraph V} {X : Set V} {terminal : Sum ι ι ↪ V}
    (L : Erdos718.PairLinkage (setCompletion G X terminal) X terminal) :
    Erdos718.PairLinkage G X terminal where
  path i := (L.path i).transfer G (pairLinkage_edge_mem_setCompletion L i)
  isPath i := (L.isPath i).transfer _
  avoids i := by
    simpa only [Erdos718.walkInteriorSet, Set.mem_ofPred_eq,
      Walk.support_transfer] using L.avoids i
  disjoint i j hij := by simpa using L.disjoint hij

lemma incidentEdges_setCompletion [Fintype ι] [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (X S : Finset V)
    (terminal : Sum ι ι ↪ V)
    [DecidableRel G.Adj]
    [DecidableRel (setCompletion G (X : Set V) terminal).Adj]
    (hdisj : Disjoint S X) :
    incidentEdges (setCompletion G (X : Set V) terminal) S =
      incidentEdges G S := by
  unfold incidentEdges
  congr 1
  ext e
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨he, hinc⟩
    refine ⟨?_, hinc⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
        change (setCompletion G (X : Set V) terminal).Adj u v at he
        change G.Adj u v
        rw [setCompletion_adj_iff] at he
        rcases he with he | hadd
        · exact he
        · exfalso
          apply hinc
          intro z hz
          rw [Sym2.toFinset_mk_eq] at hz
          have hzX : z ∈ X := by
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact hadd.2.1
            · have hzv : z = v := Finset.mem_singleton.mp hz
              subst z
              exact hadd.2.2.1
          have hznotS : z ∉ S := fun hzS =>
            Finset.disjoint_left.mp hdisj hzS hzX
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact hznotS
  · rintro ⟨he, hinc⟩
    refine ⟨?_, hinc⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
        change G.Adj u v at he
        change (setCompletion G (X : Set V) terminal).Adj u v
        exact le_setCompletion G (X : Set V) terminal he

lemma isEightKMassed_setCompletion [Fintype ι] [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (X : Finset V)
    (terminal : Sum ι ι ↪ V) (k : ℕ)
    [DecidableRel G.Adj]
    [DecidableRel (setCompletion G (X : Set V) terminal).Adj]
    (hmassed : IsEightKMassed G X k) :
    IsEightKMassed (setCompletion G (X : Set V) terminal) X k := by
  constructor
  · rw [incidentEdges_setCompletion G X (Finset.univ \ X) terminal
      Finset.sdiff_disjoint]
    exact hmassed.1
  · intro s hXleft horder
    have hdisj : Disjoint (s.right \ s.left) X := by
      exact Finset.disjoint_left.mpr fun _ hzRight hzX =>
        (Finset.mem_sdiff.mp hzRight).2 (hXleft hzX)
    let t : Erdos718.Separation G := {
      left := s.left
      right := s.right
      cover := s.cover
      not_adj := by
        intro u v huL huR hvR hvL huv
        exact s.not_adj huL huR hvR hvL
          (le_setCompletion G (X : Set V) terminal huv)
    }
    rw [incidentEdges_setCompletion G X _ terminal hdisj]
    simpa [t] using hmassed.2 t hXleft horder

lemma edgesOn_lt_setCompletion [Fintype ι] [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (X : Finset V)
    (terminal : Sum ι ι ↪ V)
    [DecidableRel G.Adj]
    [DecidableRel (setCompletion G (X : Set V) terminal).Adj]
    {u v : V} (hu : u ∈ X) (hv : v ∈ X) (hne : u ≠ v)
    (hnotPaired : ¬ArePaired terminal u v) (hnotAdj : ¬G.Adj u v) :
    Erdos718.MaderPrototype.edgesOn G X <
      Erdos718.MaderPrototype.edgesOn
        (setCompletion G (X : Set V) terminal) X := by
  unfold Erdos718.MaderPrototype.edgesOn
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he ⊢
    have hedge : e ∈ G.edgeSet := he.1
    have hcomp : e ∈ (setCompletion G (X : Set V) terminal).edgeSet := by
      induction e using Sym2.inductionOn with
      | _ a b =>
          change G.Adj a b at hedge
          change (setCompletion G (X : Set V) terminal).Adj a b
          exact le_setCompletion G (X : Set V) terminal hedge
    exact ⟨hcomp, he.2⟩
  · intro heq
    have hnew : s(u, v) ∈
        ((setCompletion G (X : Set V) terminal).edgeFinset.filter fun e =>
          e.toFinset ⊆ X) := by
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      refine ⟨?_, hu, hv⟩
      change (setCompletion G (X : Set V) terminal).Adj u v
      rw [setCompletion_adj_iff]
      exact Or.inr ⟨hne, hu, hv, hnotPaired⟩
    rw [← heq] at hnew
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at hnew
    exact hnotAdj hnew.1

end ThomasWollanMassed
end Erdos717
