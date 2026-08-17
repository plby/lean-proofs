import ErdosProblems.Erdos113.AnchoredLifts
import ErdosProblems.Erdos113.FourCycles

open scoped SimpleGraph

namespace Erdos113AnchorConstruction

noncomputable section

open Erdos113ManyLifts Erdos113Incidence Erdos113AnchoredLifts
  Erdos113FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NeighborVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :=
  ↑(G.neighborFinset v)

def neighborEmbed {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    NeighborVertex G v → V := fun x ↦ x.1

lemma neighborEmbed_injective {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    Function.Injective (neighborEmbed (G := G) (v := v)) :=
  Subtype.val_injective

def selectedMiddle (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (a b : NeighborVertex G v) : Finset V :=
  ((commonNeighborFinset G a.1 b.1).erase v).filter fun y ↦ P a.1 y b.1

@[simp] lemma mem_selectedMiddle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    {a b : NeighborVertex G v} {y : V} :
    y ∈ selectedMiddle G v P a b ↔
      G.Adj a.1 y ∧ G.Adj b.1 y ∧ y ≠ v ∧ P a.1 y b.1 := by
  simp [selectedMiddle, mem_commonNeighborFinset, and_assoc, and_left_comm]

lemma selectedMiddle_comm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (a b : NeighborVertex G v) :
    selectedMiddle G v P a b = selectedMiddle G v P b a := by
  ext y
  simp only [mem_selectedMiddle]
  rw [hP]
  aesop

def selectedPairGraph
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (lower : ℕ) : SimpleGraph (NeighborVertex G v) :=
  SimpleGraph.fromRel fun a b ↦
    lower ≤ (selectedMiddle G v P a b).card ∧
      (selectedMiddle G v P a b).card ≤ 2 * lower

noncomputable instance selectedPairGraph_decidableRel
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (lower : ℕ) : DecidableRel (selectedPairGraph G v P lower).Adj :=
  Classical.decRel _

lemma selectedPairGraph_bounds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (lower : ℕ) {a b : NeighborVertex G v}
    (hab : (selectedPairGraph G v P lower).Adj a b) :
    lower ≤ (selectedMiddle G v P a b).card ∧
      (selectedMiddle G v P a b).card ≤ 2 * lower := by
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, h | h⟩
  · exact h
  · simpa [selectedMiddle_comm G v P hP a b] using h

noncomputable def selectedLiftSystem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (lower : ℕ) (hlower : 0 < lower) :
    LiftSystem (selectedPairGraph G v P lower) G where
  embed := neighborEmbed
  embed_injective := neighborEmbed_injective
  middle := selectedMiddle G v P
  lower := lower
  lower_pos := hlower
  lower_card := fun h ↦ (selectedPairGraph_bounds G v P hP lower h).1
  upper_card := fun h ↦ (selectedPairGraph_bounds G v P hP lower h).2
  adj_left := fun h ↦ (mem_selectedMiddle G v P).mp h |>.1
  adj_right := fun h ↦ (mem_selectedMiddle G v P).mp h |>.2.1 |>.symm
  middle_disjoint := by
    intro a b y hy t hyt
    have hydata := (mem_selectedMiddle G v P).mp hy
    have hav : G.Adj v a.1 := (G.mem_neighborFinset v a.1).mp a.2
    have htv : G.Adj v t.1 := (G.mem_neighborFinset v t.1).mp t.2
    have hya := hcross hydata.1
    have hva := hcross hav
    have hvt := hcross htv
    have hside : side y = side v := by
      rw [hya, hva]
      cases side v <;> rfl
    have hsidemap : side y = side t.1 := by
      simpa [neighborEmbed] using congrArg side hyt
    rw [hside, hvt] at hsidemap
    exact (Bool.eq_not_self (side v)).mp hsidemap

theorem anchorNeighbors_card_le_codegree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (lower : ℕ) (hlower : 0 < lower) (y : V) :
    (anchorNeighbors (selectedLiftSystem G side hcross v P hP lower hlower) v y).card ≤
      codegree G v y := by
  let S := anchorNeighbors
    (selectedLiftSystem G side hcross v P hP lower hlower) v y
  calc
    S.card = (S.image neighborEmbed).card :=
      (Finset.card_image_of_injective S neighborEmbed_injective).symm
    _ ≤ codegree G v y := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
      change t ∈ anchorNeighbors
        (selectedLiftSystem G side hcross v P hP lower hlower) v y at ht
      rw [mem_anchorNeighbors] at ht
      rw [mem_commonNeighborFinset]
      exact ⟨ht.1, ht.2.symm⟩

/-- Package the selected-middle construction as an anchored lift system.
The only remaining inputs are the two incidence estimates produced by the
dyadic four-cycle selection. -/
noncomputable def selectedAnchoredLiftSystem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool)
    (hcross : ∀ ⦃x y⦄, G.Adj x y → side y = !side x)
    (v : V) (P : V → V → V → Prop) [∀ x y z, Decidable (P x y z)]
    (hP : ∀ x y z, P x y z ↔ P z y x)
    (lower : ℕ) (hlower : 0 < lower)
    (leftCap rightCap : ℕ)
    (hcodegree : ∀ y,
      IsMiddleVertex (selectedLiftSystem G side hcross v P hP lower hlower) y →
        codegree G v y ≤ rightCap)
    (hleft : ∀ t,
      (leftPartners
        (selectedLiftSystem G side hcross v P hP lower hlower) t).card ≤ leftCap) :
    AnchoredLiftSystem (selectedPairGraph G v P lower) G where
  toLiftSystem := selectedLiftSystem G side hcross v P hP lower hlower
  anchor := v
  leftCap := leftCap
  rightCap := rightCap
  anchor_adj := fun t ↦ (G.mem_neighborFinset v t.1).mp t.2
  anchor_cap := by
    intro y hy
    exact (anchorNeighbors_card_le_codegree
      G side hcross v P hP lower hlower y).trans (hcodegree y hy)
  left_cap := hleft

end

end Erdos113AnchorConstruction
