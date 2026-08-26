import ErdosProblems.Erdos547.ShrubHostFree
import ErdosProblems.Erdos547.ReservoirCandidates

/-!
# Available primary and secondary roots in a shrub host
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

theorem secondary_for_state (E : H.State) (F : Finset ↥P.shrubs) (S : ↥P.shrubs) (v : V)
    (hused : ((H.reservoir (H.head S) ∩ E.occupied).card : ℝ) ≤ 4 * H.ε * H.m) :
    ∃ R : Finset V, R ⊆ H.secondaryPool S ∧
      Disjoint R (E.occupied ∪ H.reserved F) ∧
      Disjoint R (H.free E F (H.head S)) ∧ v ∉ R ∧ 2 * H.ε * H.m ≤ (R.card : ℝ) := by
  have hroom : 2 * H.ε * H.m + ((H.reservoir (H.head S) ∩ E.occupied).card : ℝ) + 1 ≤
      (H.secondaryPool S).card := by
    nlinarith only [hused, H.secondary_card S, H.ε_volume]
  obtain ⟨R, hR, hRu, hRA, hvR, hsize⟩ := secondary_reservoir_pool
    (H.reservoir (H.head S)) (H.secondaryPool S) E.occupied (H.free E F (H.head S)) v
    (2 * H.ε * H.m) (H.secondary_sub S)
    (H.free_avoid_reservoir E F (H.head S) (H.head S)).symm hroom
  have hres : Disjoint R (H.reserved F) :=
    (H.reserved_avoid_reservoir F (H.head S)).symm.mono_left (hR.trans (H.secondary_sub S))
  exact ⟨R, hR, Finset.disjoint_union_right.mpr ⟨hRu, hres⟩, hRA, hvR, hsize⟩

theorem primary_for_state (E : H.State) (F : Finset ↥P.shrubs)
    (hEF : Disjoint E.placed F) (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (S : ↥P.shrubs) (j : I) (hj : H.IsTarget E S j)
    (hused : ((H.reservoir (H.head S) ∩ E.occupied).card : ℝ) ≤ 4 * H.ε * H.m) :
    ∃ v ∈ H.primaryPool S, v ∉ E.occupied ∧
      2 * H.ε * H.m ≤ (degreeIn G (H.free E F j) v : ℝ) := by
  have hroom : ((H.clusters (H.head S)).card : ℝ) * H.ε +
      (H.reservoir (H.head S) ∩ E.occupied).card < (H.primaryPool S).card := by
    rw [H.cluster_card]
    nlinarith only [hused, H.primary_card S, H.ε_volume]
  have hfree := H.target_free_room E F hEF hcap S j hj
  exact exists_typical_unused_reservoir_vertex G (H.target_regular E S j hj).1
    (H.free_sub E F j) (by simpa only [H.cluster_card] using hfree.1)
    (H.reservoir_sub (H.head S)) (H.primary_sub S) hroom hfree.2

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.secondary_for_state
#print axioms Erdos547.ShrubHostSetup.primary_for_state
