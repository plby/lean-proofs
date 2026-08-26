import ErdosProblems.Erdos547.ShrubRootBudget
import ErdosProblems.Erdos547.ShrubStateEndpoints

/-!
# Completing the postponed shrubs using reservoirs only for roots
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

theorem reservoir_step (hT : T.IsTree) (E : H.State) (B : Finset ↥P.shrubs)
    (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (hbound : H.ReservoirBound E B)
    (hB : ∀ i, ((B.filter (fun S ↦ H.head S = i)).card : ℝ) ≤ 2 * H.ε * H.m)
    (S : ↥P.shrubs) (hSB : S ∈ B) (hS : S ∉ E.placed) :
    ∃ E' : H.State, E'.placed = insert S E.placed ∧
      (∀ a i, (E'.farLoad a i : ℝ) ≤ H.capacity a i) ∧ H.ReservoirBound E' B := by
  classical
  obtain ⟨j, hj⟩ := H.exists_target E S
  have hused := H.reservoirBound_small hT E B hbound hB (H.head S)
  obtain ⟨v, hv, hvused, hroot⟩ := H.primary_for_state E ∅ (Finset.disjoint_empty_right _)
    hcap S j hj hused
  have hvX := H.reservoir_sub (H.head S) (H.primary_sub S hv)
  have hvbad : v ∉ E.occupied ∪ H.reserved ∅ := by
    simpa only [reserved, Finset.biUnion_empty, Finset.union_empty] using hvused
  have hres : Disjoint E.occupied (H.reserved ∅) := by simp [reserved]
  obtain ⟨E', hplaced, _, _, _, hcap', hcount⟩ := H.step_from_root E ∅ ∅ (Finset.Subset.refl _)
    (Finset.disjoint_empty_right _) hcap hres S hS j hj hused v hvX hvbad
    (H.primary_adj S v hv) hroot (S ∈ B) (fun _ ↦ hSB)
  exact ⟨E', hplaced, hcap', H.reservoirBound_insert E E' B S hS hplaced hbound hcount⟩

theorem place_reservoir_shrubs (hT : T.IsTree) (B : Finset ↥P.shrubs)
    (hB : ∀ i, ((B.filter (fun S ↦ H.head S = i)).card : ℝ) ≤ 2 * H.ε * H.m)
    (F : Finset ↥P.shrubs) (hFB : F ⊆ B) (E : H.State)
    (hEF : Disjoint E.placed F)
    (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (hbound : H.ReservoirBound E B) :
    ∃ E' : H.State, E'.placed = E.placed ∪ F ∧
      (∀ a i, (E'.farLoad a i : ℝ) ≤ H.capacity a i) ∧ H.ReservoirBound E' B := by
  classical
  induction F using Finset.induction_on generalizing E with
  | empty =>
      exact ⟨E, (Finset.union_empty _).symm, hcap, hbound⟩
  | @insert S F hSF ih =>
      have hS : S ∉ E.placed := fun h ↦
        Finset.disjoint_left.mp hEF h (Finset.mem_insert_self _ _)
      obtain ⟨E₁, hplaced₁, hcap₁, hbound₁⟩ := H.reservoir_step hT E B hcap hbound hB
        S (hFB (Finset.mem_insert_self _ _)) hS
      have hE₁F : Disjoint E₁.placed F := by
        rw [hplaced₁]
        apply Finset.disjoint_insert_left.mpr
        exact ⟨hSF, hEF.mono_right (Finset.subset_insert _ _)⟩
      obtain ⟨E₂, hplaced₂, hcap₂, hbound₂⟩ := ih
        ((Finset.subset_insert S F).trans hFB) E₁ hE₁F hcap₁ hbound₁
      refine ⟨E₂, ?_, hcap₂, hbound₂⟩
      rw [hplaced₂, hplaced₁]
      ext A
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto

theorem complete_reservoir_phase (hT : T.IsTree) (E : H.State) (B : Finset ↥P.shrubs)
    (hEB : Disjoint E.placed B) (hcover : E.placed ∪ B = Finset.univ)
    (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (hbound : H.ReservoirBound E B)
    (hB : ∀ i, ((B.filter (fun S ↦ H.head S = i)).card : ℝ) ≤ 2 * H.ε * H.m) : T ⊑ G := by
  obtain ⟨E', hplaced, _, _⟩ := H.place_reservoir_shrubs hT B hB B (Finset.Subset.refl _)
    E hEB hcap hbound
  exact E'.isContained_of_all_placed (hplaced.trans hcover)

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.complete_reservoir_phase
