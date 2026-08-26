import ErdosProblems.Erdos547.ShrubRootBudget
import ErdosProblems.Erdos547.ShrubPostponement
import ErdosProblems.Erdos547.ShrubStateEndpoints

/-!
# Initialization and the private-root phase step
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

theorem exists_initial_state : ∃ E : H.State, E.placed = ∅ ∧
    (∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i) ∧ H.ReservoirBound E ∅ ∧
    Disjoint E.occupied (H.reserved Finset.univ) := by
  classical
  obtain ⟨E, hplaced, hused⟩ := @ShrubState.exists_initial U V I _ _ _ T _ r ℓ col P G
    H.clusters H.head H.seed
  have hcard : E.occupied.card = P.seeds.card := by
    rw [hused]
    have hi : Function.Injective (fun v : ↥P.seeds ↦ H.seed v) := H.seed.injective
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_coe]
  refine ⟨E, hplaced, ?_, ?_, ?_⟩
  · intro a i
    simpa only [ShrubState.farLoad, routedLoad, hplaced, Finset.sum_empty, Nat.cast_zero]
      using H.capacity_nonneg a i
  · intro i
    have hc := Finset.card_le_card (show H.reservoir i ∩ E.occupied ⊆ E.occupied from
      Finset.inter_subset_right)
    rw [hcard] at hc
    exact hc.trans (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))
  · rw [hused]
    apply Finset.disjoint_left.mpr
    intro v hv hres
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨S, _, hvS⟩ := Finset.mem_biUnion.mp hres
    exact H.private_seed S z hvS

theorem private_step_or_failure (hT : T.IsTree) (E : H.State) (F : Finset ↥P.shrubs)
    (hEF : Disjoint E.placed F)
    (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (hbound : H.ReservoirBound E ∅) (hreserved : Disjoint E.occupied (H.reserved F))
    (S : ↥P.shrubs) (hSF : S ∈ F) :
    H.FailedAt E F S ∨ ∃ E' : H.State, ∃ j : I,
      E'.placed = insert S E.placed ∧ E'.tail = Function.update E.tail S j ∧
      E.occupied ⊆ E'.occupied ∧ Disjoint E'.occupied (H.reserved (F.erase S)) ∧
      (∀ a i, (E'.farLoad a i : ℝ) ≤ H.capacity a i) ∧ H.ReservoirBound E' ∅ := by
  classical
  by_cases hfailed : H.FailedAt E F S
  · exact Or.inl hfailed
  · right
    have hex : ∃ j, H.IsTarget E S j ∧ ∃ v ∈ H.privateSet S,
        2 * H.ε * H.m ≤ (degreeIn G (H.free E F j) v : ℝ) := by
      by_contra hn
      apply hfailed
      intro j hj v hv
      exact lt_of_not_ge fun hd ↦ hn ⟨j, hj, v, hv, hd⟩
    obtain ⟨j, hj, v, hv, hroot⟩ := hex
    have hS : S ∉ E.placed := fun hh ↦ Finset.disjoint_left.mp hEF hh hSF
    have hempty : ∀ i : I,
        (((∅ : Finset ↥P.shrubs).filter (fun A ↦ H.head A = i)).card : ℝ) ≤ 2 * H.ε * H.m := by
      intro i
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) H.ε_pos.le) (Nat.cast_nonneg _)
    have hused := H.reservoirBound_small hT E ∅ hbound hempty (H.head S)
    have hresSub := H.reserved_mono (Finset.erase_subset S F)
    have hvbad : v ∉ E.occupied ∪ H.reserved (F.erase S) := by
      intro hh
      rcases Finset.mem_union.mp hh with hu | hr
      · exact Finset.disjoint_left.mp hreserved hu (Finset.mem_biUnion.mpr ⟨S, hSF, hv⟩)
      · exact Finset.disjoint_left.mp (H.private_avoid_remainder F S) hv hr
    have hp : v ∈ H.reservoir (H.head S) → False :=
      fun hq ↦ Finset.disjoint_left.mp (H.private_reservoir S (H.head S)) hv hq
    obtain ⟨E', hplaced, htail, hmono, hreserved', hcap', hcount⟩ := H.step_from_root
      E F (F.erase S) (Finset.erase_subset S F) hEF hcap (hreserved.mono_right hresSub)
      S hS j hj hused v (H.private_sub S hv) hvbad (H.private_adj S v hv) hroot False hp
    have hcount' : ∀ i, (H.reservoir i ∩ E'.occupied).card ≤ (H.reservoir i ∩ E.occupied).card +
        (if H.head S = i ∧ S ∈ (∅ : Finset ↥P.shrubs) then 1 else 0) +
        (if (H.roots S).second.isSome then 1 else 0) := by
      intro i
      simpa only [Finset.notMem_empty] using hcount i
    exact ⟨E', j, hplaced, htail, hmono, hreserved', hcap',
      H.reservoirBound_insert E E' ∅ S hS hplaced hbound hcount'⟩

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.exists_initial_state
#print axioms Erdos547.ShrubHostSetup.private_step_or_failure
