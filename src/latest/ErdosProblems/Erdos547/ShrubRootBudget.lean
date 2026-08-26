import ErdosProblems.Erdos547.ShrubHostStep

/-!
# A reservoir budget that is preserved in both embedding phases
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

noncomputable def secondaryCount (E : Finset ↥P.shrubs) : ℕ :=
  E.filter (fun S ↦ (H.roots S).second.isSome) |>.card

noncomputable def primaryCount (E B : Finset ↥P.shrubs) (i : I) : ℕ :=
  E.filter (fun S ↦ S ∈ B ∧ H.head S = i) |>.card

def ReservoirBound (E : H.State) (B : Finset ↥P.shrubs) : Prop :=
  ∀ i, (H.reservoir i ∩ E.occupied).card ≤
    P.seeds.card + H.secondaryCount E.placed + H.primaryCount E.placed B i

theorem secondaryCount_le_seeds (hT : T.IsTree) (E : Finset ↥P.shrubs) :
    H.secondaryCount E ≤ P.seeds.card := by
  classical
  have hh := P.second_roots_add_one_le_seeds hT H.roots
  have hc : H.secondaryCount E ≤
      ((Finset.univ : Finset ↥P.shrubs).filter (fun S ↦ (H.roots S).second.isSome)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ E))
  omega

theorem primaryCount_le_postponed (E B : Finset ↥P.shrubs) (i : I) :
    H.primaryCount E B i ≤ (B.filter (fun S ↦ H.head S = i)).card := by
  classical
  apply Finset.card_le_card
  intro S hS
  exact Finset.mem_filter.mpr (Finset.mem_filter.mp hS).2

theorem reservoirBound_small (hT : T.IsTree) (E : H.State) (B : Finset ↥P.shrubs)
    (hbound : H.ReservoirBound E B)
    (hB : ∀ i, ((B.filter (fun S ↦ H.head S = i)).card : ℝ) ≤ 2 * H.ε * H.m) (i : I) :
    ((H.reservoir i ∩ E.occupied).card : ℝ) ≤ 4 * H.ε * H.m := by
  have hb : ((H.reservoir i ∩ E.occupied).card : ℝ) ≤ (P.seeds.card : ℝ) +
      (H.secondaryCount E.placed : ℝ) + (H.primaryCount E.placed B i : ℝ) := by
    exact_mod_cast hbound i
  have hs : (H.secondaryCount E.placed : ℝ) ≤ P.seeds.card := by
    exact_mod_cast H.secondaryCount_le_seeds hT E.placed
  have hp : (H.primaryCount E.placed B i : ℝ) ≤ (B.filter (fun S ↦ H.head S = i)).card := by
    exact_mod_cast H.primaryCount_le_postponed E.placed B i
  nlinarith only [hb, hs, hp, hB i, H.seed_small]

theorem reservoirBound_insert (E E' : H.State) (B : Finset ↥P.shrubs)
    (S : ↥P.shrubs) (hS : S ∉ E.placed) (hplaced : E'.placed = insert S E.placed)
    (hbound : H.ReservoirBound E B)
    (hstep : ∀ i, (H.reservoir i ∩ E'.occupied).card ≤ (H.reservoir i ∩ E.occupied).card +
      (if H.head S = i ∧ S ∈ B then 1 else 0) + (if (H.roots S).second.isSome then 1 else 0)) :
    H.ReservoirBound E' B := by
  classical
  intro i
  have hs : H.secondaryCount E'.placed = H.secondaryCount E.placed +
      (if (H.roots S).second.isSome then 1 else 0) := by
    rw [hplaced]
    by_cases hp : (H.roots S).second.isSome
    · simp [secondaryCount, Finset.filter_insert, hp, hS, Nat.add_comm]
    · simp [secondaryCount, Finset.filter_insert, hp]
  have hp : H.primaryCount E'.placed B i = H.primaryCount E.placed B i +
      (if H.head S = i ∧ S ∈ B then 1 else 0) := by
    rw [hplaced]
    by_cases hb : S ∈ B ∧ H.head S = i
    · simp [primaryCount, Finset.filter_insert, hb.1, hb.2, hS, Nat.add_comm]
    · have hb' : ¬(H.head S = i ∧ S ∈ B) := fun h ↦ hb ⟨h.2, h.1⟩
      simp [primaryCount, Finset.filter_insert, hb, hb']
  have h1 := hbound i
  have h2 := hstep i
  rw [hs, hp]
  omega

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.reservoirBound_small
#print axioms Erdos547.ShrubHostSetup.reservoirBound_insert
