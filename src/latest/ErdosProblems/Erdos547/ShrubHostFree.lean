import ErdosProblems.Erdos547.ShrubHostSetup
import ErdosProblems.Erdos547.RootedRegularMargins

/-!
# Free sets and target pairs in an explicit shrub host setup
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph
open scoped BigOperators

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

abbrev State := ShrubState P G H.clusters H.head H.seed

def reserved (F : Finset ↥P.shrubs) : Finset V := F.biUnion H.privateSet

noncomputable def free (E : H.State) (F : Finset ↥P.shrubs) (i : I) : Finset V :=
  H.clusters i \ (H.reservoir i ∪ E.occupied ∪ H.reserved F)

theorem free_sub (E : H.State) (F : Finset ↥P.shrubs) (i : I) :
    H.free E F i ⊆ H.clusters i := Finset.sdiff_subset

theorem free_avoid_used_reserved (E : H.State) (F : Finset ↥P.shrubs) (i : I) :
    Disjoint (H.free E F i) (E.occupied ∪ H.reserved F) := by
  apply Finset.disjoint_left.mpr
  intro v hv hbad
  have hh := (Finset.mem_sdiff.mp hv).2
  rcases Finset.mem_union.mp hbad with hused | hres
  · exact hh (Finset.mem_union_left _ (Finset.mem_union_right _ hused))
  · exact hh (Finset.mem_union_right _ hres)

theorem free_avoid_reservoir (E : H.State) (F : Finset ↥P.shrubs) (i j : I) :
    Disjoint (H.free E F i) (H.reservoir j) := by
  apply Finset.disjoint_left.mpr
  intro v hv hq
  by_cases hij : i = j
  · subst j
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_union_left _ (Finset.mem_union_left _ hq))
  · exact Finset.disjoint_left.mp (H.cluster_disjoint i j hij)
      (H.free_sub E F i hv) (H.reservoir_sub j hq)

theorem reserved_avoid_reservoir (F : Finset ↥P.shrubs) (i : I) :
    Disjoint (H.reserved F) (H.reservoir i) := by
  apply Finset.disjoint_left.mpr
  intro v hv hq
  obtain ⟨S, _, hvS⟩ := Finset.mem_biUnion.mp hv
  exact Finset.disjoint_left.mp (H.private_reservoir S i) hvS hq

theorem free_size (E : H.State) (F : Finset ↥P.shrubs)
    (hEF : Disjoint E.placed F)
    (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i) (i : I) :
    H.η * H.m ≤ ((H.free E F i).card : ℝ) := by
  apply H.buffer_margin.trans
  exact E.available_from_capacities H.cluster_disjoint H.capacity hcap F hEF H.privateSet
    (fun S _ ↦ H.private_sub S) (fun S _ ↦ (H.private_card S).le)
    i (H.reservoir i) H.m H.mainSize H.q (H.cluster_card i) (H.reservoir_card i)
    H.volume H.seed_buffer (H.cluster_budget i)

def IsTarget (E : H.State) (S : ↥P.shrubs) (j : I) : Prop :=
  H.targetFloor ≤ H.capacity (ShrubState.shrubGroup P H.head S) j ∧
    (E.farLoad (ShrubState.shrubGroup P H.head S) j : ℝ) <
      (1 - H.slack / 2) * H.capacity (ShrubState.shrubGroup P H.head S) j

theorem exists_target (E : H.State) (S : ↥P.shrubs) : ∃ j, H.IsTarget E S j :=
  E.exists_target (ShrubState.shrubGroup P H.head S) H.capacity H.slack H.targetFloor
    H.slack_pos H.slack_le_one H.targetFloor_pos.le (H.group_positive S)
    (H.group_demand _) (H.group_target_margin S)

theorem target_regular (E : H.State) (S : ↥P.shrubs) (j : I) (hj : H.IsTarget E S j) :
    G.IsUniform H.ε (H.clusters (H.head S)) (H.clusters j) ∧
    Disjoint (H.clusters (H.head S)) (H.clusters j) ∧
    H.d ≤ (G.edgeDensity (H.clusters (H.head S)) (H.clusters j) : ℝ) :=
  H.capacity_regular _ j (H.targetFloor_pos.trans_le hj.1)

theorem target_free_room (E : H.State) (F : Finset ↥P.shrubs)
    (hEF : Disjoint E.placed F) (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (S : ↥P.shrubs) (j : I) (hj : H.IsTarget E S j) :
    H.m * H.ε ≤ ((H.free E F j).card : ℝ) ∧
    2 * H.ε * H.m ≤ ((G.edgeDensity (H.clusters (H.head S)) (H.clusters j) : ℝ) - H.ε) *
      (H.free E F j).card := by
  have hd := (H.target_regular E S j hj).2.2
  have hd1 : H.d ≤ 1 := hd.trans
    (by exact_mod_cast G.edgeDensity_le_one (H.clusters (H.head S)) (H.clusters j))
  have hd0 : 0 ≤ H.d := (mul_nonneg (by norm_num) H.ε_pos.le).trans H.degree_margin
  have hweak : 4 * H.ε ≤ H.d * H.η := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hd0 hd1) H.η_nonneg
    nlinarith only [hh, H.embedding_margin, H.ε_pos.le]
  have hroom := regular_pair_room H.ε H.d
    (G.edgeDensity (H.clusters (H.head S)) (H.clusters j) : ℝ) H.η H.m (H.ε * H.m)
    (H.free E F j).card H.ε_pos.le hd hd1 H.η_nonneg (Nat.cast_nonneg _)
    H.degree_margin hweak (H.free_size E F hEF hcap j) le_rfl
  constructor
  · simpa only [mul_comm H.ε] using hroom.1
  · linarith only [hroom.2]

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.free_size
#print axioms Erdos547.ShrubHostSetup.target_free_room
