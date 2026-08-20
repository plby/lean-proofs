import ErdosProblems.Erdos746.Model
import ErdosProblems.Erdos746.Posa
import ErdosProblems.Erdos746.LocalLYM
import Mathlib.Tactic

/-!
# Monotonicity in the exact uniform random-graph model

An upward-closed family occupies a nondecreasing proportion of the levels of
the Boolean lattice.  We derive the adjacent-level statement from the local
LYM double count in `Erdos543.Model`, iterate it, and then specialize to
Hamiltonicity and two-expansion of graphs.
-/

namespace Erdos746

open Filter

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The proportion of the `m`th level of the Boolean lattice on `U` which
satisfies `P`.  This is set to zero when the level is empty. -/
def layerProbability {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (m : ℕ) : ℝ :=
  ((LocalLYM.goodSets U P m).card : ℝ) / U.card.choose m

/-- Local LYM in normalized form: the density of an upward-closed family
does not decrease from a valid level to the next level. -/
theorem layerProbability_mono_succ {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (m : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    (hm : m < U.card) :
    layerProbability U P m ≤ layerProbability U P (m + 1) := by
  have hcount := LocalLYM.extension_count_le_marked_count U P m hP
  have hchoose : U.card.choose (m + 1) * (m + 1) =
      U.card.choose m * (U.card - m) := Nat.choose_succ_right_eq _ _
  have hm1 : 0 < (m + 1 : ℝ) := by positivity
  have hdenm : 0 < (U.card.choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hm)
  have hdenm1 : 0 < (U.card.choose (m + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos hm
  rw [layerProbability, layerProbability, div_le_div_iff₀ hdenm hdenm1]
  norm_cast at hcount hchoose ⊢
  nlinarith

/-- The density monotonicity between any two valid levels. -/
theorem layerProbability_mono {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    {m k : ℕ} (hmk : m ≤ k) (hk : k ≤ U.card) :
    layerProbability U P m ≤ layerProbability U P k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
  clear hmk
  revert hk
  induction d with
  | zero =>
      intro _
      exact le_rfl
  | succ d ih =>
      intro hk
      have hprev : m + d ≤ U.card := by omega
      have hstep : m + d < U.card := by omega
      exact (ih hprev).trans (layerProbability_mono_succ U P (m + d) hP hstep)

/-- Restricting a `Set.powersetCard` sample by an event is equivalent to
restricting the corresponding finite Boolean-lattice layer. -/
noncomputable def powersetCardEventEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α → Prop) (m : ℕ) :
    {s : Set.powersetCard α m // P s.1} ≃
      {s : Finset α // s ∈ (Finset.univ.powersetCard m).filter P} where
  toFun s := ⟨s.1.1, by
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, s.1.2⟩, s.2⟩⟩
  invFun s := ⟨⟨s.1, by
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp s.2).1).2⟩,
    (Finset.mem_filter.mp s.2).2⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

/-- On a finite ambient type, `layerProbability` is exactly the uniform
probability on `Set.powersetCard`. -/
theorem layerProbability_univ_eq_uniformProbability
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : Finset α → Prop) (m : ℕ) :
    layerProbability (Finset.univ : Finset α) P m =
      uniformProbability (fun s : Set.powersetCard α m ↦ P s.1) := by
  have hcard : Fintype.card (Set.powersetCard α m) =
      (Fintype.card α).choose m := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card,
      ← Fintype.card_eq_nat_card]
  rw [layerProbability, uniformProbability, LocalLYM.goodSets,
    Finset.card_univ, hcard]
  congr 1
  have hc : (Finset.univ.powersetCard m |>.filter P).card =
      Fintype.card {s : Set.powersetCard α m // P s.1} := by
    simpa only [Fintype.card_coe] using
      (Fintype.card_congr (powersetCardEventEquiv P m)).symm
  rw [← Fintype.card_subtype]
  exact_mod_cast hc

/-- Uniform probability, at a fixed edge count, of an arbitrary graph
property. -/
def graphPropertyProbability (n m : ℕ)
    (Q : SimpleGraph (Fin n) → Prop) : ℝ :=
  uniformProbability (fun G : FixedEdgeGraph n m ↦ Q (FixedEdgeGraph.graph G))

theorem graphPropertyProbability_eq_layerProbability (n m : ℕ)
    (Q : SimpleGraph (Fin n) → Prop) :
    graphPropertyProbability n m Q =
      layerProbability (Finset.univ : Finset (Edge n))
        (fun s ↦ Q (graphOfEdges s)) m := by
  rw [layerProbability_univ_eq_uniformProbability]
  rfl

/-- Every edge-monotone graph property has nondecreasing probability in the
uniform fixed-edge model. -/
theorem graphPropertyProbability_mono {n m k : ℕ}
    (Q : SimpleGraph (Fin n) → Prop)
    (hQ : ∀ ⦃G H : SimpleGraph (Fin n)⦄, G ≤ H → Q G → Q H)
    (hmk : m ≤ k) (hk : k ≤ edgeCount n) :
    graphPropertyProbability n m Q ≤ graphPropertyProbability n k Q := by
  rw [graphPropertyProbability_eq_layerProbability,
    graphPropertyProbability_eq_layerProbability]
  apply layerProbability_mono _ _ (fun _ _ hst hs ↦
    hQ (graphOfEdges_mono hst) hs) hmk
  rw [Finset.card_univ, card_edge]
  exact hk

/-- The finite-set description of the Hamiltonicity event. -/
def IsHamiltonianEdgeSet (n : ℕ) (s : Finset (Edge n)) : Prop :=
  (graphOfEdges s).IsHamiltonian

theorem isHamiltonianEdgeSet_mono {n : ℕ} {s t : Finset (Edge n)}
    (hst : s ⊆ t) (hs : IsHamiltonianEdgeSet n s) :
    IsHamiltonianEdgeSet n t :=
  hs.mono (graphOfEdges_mono hst)

theorem hamiltonianProbability_eq_layerProbability (n m : ℕ) :
    hamiltonianProbability n m =
      layerProbability (Finset.univ : Finset (Edge n))
        (IsHamiltonianEdgeSet n) m := by
  rw [layerProbability_univ_eq_uniformProbability]
  rfl

/-- Hamiltonicity probability in the exact uniform model is nondecreasing
with the number of edges. -/
theorem hamiltonianProbability_mono {n m k : ℕ}
    (hmk : m ≤ k) (hk : k ≤ edgeCount n) :
    hamiltonianProbability n m ≤ hamiltonianProbability n k := by
  simpa only [hamiltonianProbability, graphPropertyProbability] using
    graphPropertyProbability_mono
      (fun G : SimpleGraph (Fin n) ↦ G.IsHamiltonian)
      (fun _ _ hGH hG ↦ hG.mono hGH) hmk hk

/-- External neighborhoods can only grow when edges are added. -/
theorem outerNeighborFinset_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (hGH : G ≤ H) (S : Finset V) :
    G.outerNeighborFinset S ⊆ H.outerNeighborFinset S := by
  intro v hv
  rw [SimpleGraph.mem_outerNeighborFinset] at hv ⊢
  exact ⟨hv.1, hv.2.imp fun u hu ↦ ⟨hu.1, hGH hu.2⟩⟩

/-- Two-expansion up to a fixed size is an edge-monotone graph property. -/
theorem isTwoExpanderUpTo_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} (hGH : G ≤ H) {r : ℕ}
    (hG : G.IsTwoExpanderUpTo r) : H.IsTwoExpanderUpTo r := by
  intro S hSr
  exact (hG S hSr).trans
    (Finset.card_le_card (outerNeighborFinset_mono hGH S))

/-- Exact fixed-edge probability of two-expansion up to `r`. -/
def twoExpanderProbability (n m r : ℕ) : ℝ :=
  graphPropertyProbability n m (fun G ↦ G.IsTwoExpanderUpTo r)

/-- The exact two-expansion probability is nondecreasing with edge count. -/
theorem twoExpanderProbability_mono {n m k r : ℕ}
    (hmk : m ≤ k) (hk : k ≤ edgeCount n) :
    twoExpanderProbability n m r ≤ twoExpanderProbability n k r := by
  exact graphPropertyProbability_mono
    (fun G : SimpleGraph (Fin n) ↦ G.IsTwoExpanderUpTo r)
    (fun _ _ hGH hG ↦ isTwoExpanderUpTo_mono hGH hG) hmk hk

end

end Erdos746
