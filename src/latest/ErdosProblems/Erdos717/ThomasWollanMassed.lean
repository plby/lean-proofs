/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The terminal-aware "massed" formulation used for the easy (constant eight)
Thomas--Wollan linkage theorem.
-/

import ErdosProblems.Erdos717.ContractLinkage

open Function Set
open SimpleGraph
open scoped Sym2

namespace Erdos717
namespace ThomasWollanMassed

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Number of edges with at least one endpoint in `S`. -/
def incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => ¬ e.toFinset ⊆ Finset.univ \ S).card

lemma incidentEdges_univ_sdiff (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) :
    incidentEdges G (Finset.univ \ X) =
      G.edgeFinset.card - Erdos718.MaderPrototype.edgesOn G X := by
  classical
  unfold incidentEdges Erdos718.MaderPrototype.edgesOn
  have hset : Finset.univ \ (Finset.univ \ X) = X := by ext x; simp
  rw [hset]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := G.edgeFinset) (fun e => e.toFinset ⊆ X)
  omega

lemma incidentEdges_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    incidentEdges G ∅ = 0 := by
  unfold incidentEdges
  simp

lemma edgesOn_le_choose (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) :
    Erdos718.MaderPrototype.edgesOn G X ≤ X.card.choose 2 := by
  rw [Erdos718.MaderPrototype.edgesOn_eq_induce]
  have h := (G.induce (X : Set V)).card_edgeFinset_le_card_choose_two
  simpa using h

/-- Thomas--Wollan's mass condition with the integer parameter specialized
to `8k`.  `X` is the distinguished terminal set. -/
def IsEightKMassed (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (k : ℕ) : Prop :=
  8 * k * (Fintype.card V - X.card) <
      incidentEdges G (Finset.univ \ X) ∧
    ∀ s : Erdos718.Separation G,
      X ⊆ s.left → s.separator.card < X.card →
      incidentEdges G (s.right \ s.left) ≤
        8 * k * (s.right \ s.left).card

/-- In a `2k`-connected graph, any separation of order below `2k` whose
left side contains `2k` distinguished vertices has empty strict right side. -/
lemma strictRight_empty_of_connected
    {G : SimpleGraph V} {X : Finset V} {k : ℕ}
    (hconn : Erdos718.IsKConnected G (2 * k))
    (hXcard : X.card = 2 * k)
    (s : Erdos718.Separation G)
    (hXleft : X ⊆ s.left) (horder : s.separator.card < X.card) :
    s.right \ s.left = ∅ := by
  by_contra hne
  have hright : (s.right \ s.left).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hleft : (s.left \ s.right).Nonempty := by
    by_contra hleftEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hleftEmpty
    have hXright : X ⊆ s.right := by
      intro x hx
      have hxL := hXleft hx
      by_contra hxR
      have : x ∈ s.left \ s.right := Finset.mem_sdiff.mpr ⟨hxL, hxR⟩
      rw [hleftEmpty] at this
      exact Finset.notMem_empty x this
    have hXsep : X ⊆ s.separator := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hXleft hx, hXright hx⟩
    have hcard := Finset.card_le_card hXsep
    omega
  have hproper : s.Proper := ⟨hleft, hright⟩
  have hlarge := hconn.2 s hproper
  unfold Erdos718.Separation.order at hlarge
  rw [hXcard] at horder
  omega

/-- The hypotheses of the density corollary imply the mass conditions for
every exact `k`-pair terminal set. -/
lemma isEightKMassed_of_connected_edges
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (hconn : Erdos718.IsKConnected G (2 * k))
    (hE : 8 * k * Fintype.card V ≤ G.edgeFinset.card)
    (X : Finset V) (hXcard : X.card = 2 * k) :
    IsEightKMassed G X k := by
  constructor
  · rw [incidentEdges_univ_sdiff]
    have hinside := edgesOn_le_choose G X
    have hchoose : X.card.choose 2 < 8 * k * X.card := by
      calc
        X.card.choose 2 ≤ X.card ^ 2 := Nat.choose_le_pow _ _
        _ < 8 * k * X.card := by rw [hXcard]; nlinarith
    have hinsidelt : Erdos718.MaderPrototype.edgesOn G X <
        8 * k * X.card := hinside.trans_lt hchoose
    have hinsideEdge : Erdos718.MaderPrototype.edgesOn G X ≤
        G.edgeFinset.card := by
      unfold Erdos718.MaderPrototype.edgesOn
      exact Finset.card_le_card (Finset.filter_subset _ _)
    rw [Nat.lt_sub_iff_add_lt]
    have hsplit : 8 * k * Fintype.card V =
        8 * k * (Fintype.card V - X.card) +
          8 * k * X.card := by
      have hXle : X.card ≤ Fintype.card V := Finset.card_le_univ X
      conv_lhs => rw [show Fintype.card V =
          (Fintype.card V - X.card) + X.card by omega]
      rw [mul_add]
    calc
      8 * k * (Fintype.card V - X.card) +
          Erdos718.MaderPrototype.edgesOn G X <
        8 * k * (Fintype.card V - X.card) + 8 * k * X.card :=
          Nat.add_lt_add_left hinsidelt _
      _ = 8 * k * Fintype.card V := hsplit.symm
      _ ≤ G.edgeFinset.card := hE
  · intro s hXleft horder
    have hempty := strictRight_empty_of_connected hconn hXcard s hXleft horder
    rw [hempty, incidentEdges_empty G]
    simp

end ThomasWollanMassed
end Erdos717
