/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.EC2
import Mathlib.Tactic

/-!
# Literal host graphs realizing truncated root rows

Only edges from one specified root to a specified bad-target union are
deleted. This is an ordinary spanning subgraph, with exact root-neighbor
and target-degree identities.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoSourceRootTruncation

open Finset SimpleGraph
open Erdos547EC2

variable {V : Type*} [DecidableEq V]

def truncateRoot (H : SimpleGraph V) (z : V) (D : Finset V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ (u ≠ z ∨ v ∉ D) ∧ (v ≠ z ∨ u ∉ D)
  symm := ⟨fun _ _ huv => ⟨huv.1.symm, huv.2.2, huv.2.1⟩⟩
  loopless := ⟨fun u huu => (H.ne_of_adj huu.1) rfl⟩

instance (H : SimpleGraph V) [DecidableRel H.Adj] (z : V) (D : Finset V) :
    DecidableRel (truncateRoot H z D).Adj := by
  unfold truncateRoot
  infer_instance

theorem truncateRoot_le (H : SimpleGraph V) (z : V) (D : Finset V) :
    truncateRoot H z D ≤ H := fun _ _ h => h.1

theorem adj_root_iff (H : SimpleGraph V) (z v : V) (D : Finset V) :
    (truncateRoot H z D).Adj z v ↔ H.Adj z v ∧ v ∉ D := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1.resolve_left (by simp)⟩
  · intro h
    exact ⟨h.1, Or.inr h.2, Or.inl h.1.ne.symm⟩

theorem adj_away_iff (H : SimpleGraph V) (z u v : V) (D : Finset V)
    (hu : u ≠ z) (hv : v ≠ z) :
    (truncateRoot H z D).Adj u v ↔ H.Adj u v := by
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl hu, Or.inl hv⟩⟩

theorem adj_other_root_iff (H : SimpleGraph V) (z u v : V) (D : Finset V)
    (hu : u ≠ z) (huD : u ∉ D) :
    (truncateRoot H z D).Adj u v ↔ H.Adj u v := by
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl hu, Or.inr huD⟩⟩

theorem neighborFinset_root [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (z : V) (D : Finset V) :
    (truncateRoot H z D).neighborFinset z = H.neighborFinset z \ D := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff, adj_root_iff]

theorem degree_root_loss [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (z : V) (D : Finset V) :
    H.degree z ≤ (truncateRoot H z D).degree z + D.card := by
  have hsplit := Finset.card_sdiff_add_card_inter (H.neighborFinset z) D
  have hsub : (H.neighborFinset z ∩ D).card ≤ D.card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [← H.card_neighborFinset_eq_degree z,
    ← (truncateRoot H z D).card_neighborFinset_eq_degree z, neighborFinset_root]
  omega

theorem degree_away_loss [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (z u : V) (D : Finset V)
    (hu : u ≠ z) :
    H.degree u ≤ (truncateRoot H z D).degree u + 1 := by
  have hsub : H.neighborFinset u ⊆
      (truncateRoot H z D).neighborFinset u ∪ {z} := by
    intro v hv
    by_cases hvz : v = z
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hvz)
    · exact Finset.mem_union_left _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr
        ((adj_away_iff H z u v D hu hvz).mpr
          ((SimpleGraph.mem_neighborFinset _ _ _).mp hv)))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree] using hcard

theorem degree_other_root_eq [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (z u : V) (D : Finset V)
    (hu : u ≠ z) (huD : u ∉ D) :
    (truncateRoot H z D).degree u = H.degree u := by
  have hneighbors : (truncateRoot H z D).neighborFinset u = H.neighborFinset u := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, adj_other_root_iff H z u v D hu huD]
  exact congrArg Finset.card hneighbors

theorem degreeInto_root_eq_zero [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (z : V) (D Y : Finset V)
    (hY : Y ⊆ D) : degreeInto (truncateRoot H z D) z Y = 0 := by
  unfold degreeInto
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvY, hvAdj⟩ := Finset.mem_filter.mp hv
  exact ((adj_root_iff H z v D).mp hvAdj).2 (hY hvY)

theorem degreeInto_root_eq_of_disjoint [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (z : V) (D Y : Finset V)
    (hY : Disjoint Y D) : degreeInto (truncateRoot H z D) z Y = degreeInto H z Y := by
  unfold degreeInto
  congr 1
  ext v
  by_cases hv : v ∈ Y
  · have hvD : v ∉ D := fun hvD => (Finset.disjoint_left.mp hY) hv hvD
    simp only [Finset.mem_filter, hv, true_and, adj_root_iff, hvD, not_false_eq_true,
      and_true]
  · simp only [Finset.mem_filter, hv, false_and]

theorem degreeInto_other_root_eq [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (z u : V) (D Y : Finset V)
    (hu : u ≠ z) (huD : u ∉ D) :
    degreeInto (truncateRoot H z D) u Y = degreeInto H u Y := by
  unfold degreeInto
  congr 1
  ext v
  simp only [Finset.mem_filter, adj_other_root_iff H z u v D hu huD]

/-- Simultaneous truncation of two root rows has a uniform degree-loss
bound. At a selected root only its own bad-target set matters; every
other vertex loses at most two incident edges. -/
theorem twoRoot_degree_loss [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (zA zB : V) (DA DB : Finset V)
    (hne : zA ≠ zB) (hA : zA ∉ DB) (hB : zB ∉ DA) (u : V) :
    H.degree u ≤ (truncateRoot (truncateRoot H zA DA) zB DB).degree u +
      (max DA.card DB.card + 2) := by
  have hDA : DA.card ≤ max DA.card DB.card := Nat.le_max_left _ _
  have hDB : DB.card ≤ max DA.card DB.card := Nat.le_max_right _ _
  by_cases huA : u = zA
  · subst u
    rw [degree_other_root_eq (truncateRoot H zA DA) zB zA DB hne hA]
    have h := degree_root_loss H zA DA
    omega
  · by_cases huB : u = zB
    · subst u
      have hfirst := degree_other_root_eq H zA zB DA hne.symm hB
      have hsecond := degree_root_loss (truncateRoot H zA DA) zB DB
      omega
    · have hfirst := degree_away_loss H zA u DA huA
      have hsecond := degree_away_loss (truncateRoot H zA DA) zB u DB huB
      omega

end Erdos547b.ZhaoSourceRootTruncation

#print axioms Erdos547b.ZhaoSourceRootTruncation.truncateRoot_le
#print axioms Erdos547b.ZhaoSourceRootTruncation.neighborFinset_root
#print axioms Erdos547b.ZhaoSourceRootTruncation.degree_root_loss
#print axioms Erdos547b.ZhaoSourceRootTruncation.degree_away_loss
#print axioms Erdos547b.ZhaoSourceRootTruncation.degree_other_root_eq
#print axioms Erdos547b.ZhaoSourceRootTruncation.degreeInto_root_eq_zero
#print axioms Erdos547b.ZhaoSourceRootTruncation.degreeInto_root_eq_of_disjoint
#print axioms Erdos547b.ZhaoSourceRootTruncation.degreeInto_other_root_eq
#print axioms Erdos547b.ZhaoSourceRootTruncation.twoRoot_degree_loss
