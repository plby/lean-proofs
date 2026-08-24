import ErdosProblems.Erdos587.BoundedRemoval
import ErdosProblems.Erdos587.LatticeIndexBound

/-! Stability of generated subgroups from uniform bounds on their indices. -/

open scoped BigOperators

namespace Erdos587.CFP

def generatedSubgroup {α G : Type*} [AddGroup G] (φ : α → G) (A : Finset α) :
    AddSubgroup G := AddSubgroup.closure (φ '' (A : Set α))

theorem generatedSubgroup_mono {α G : Type*} [AddGroup G] (φ : α → G)
    {A B : Finset α} (hAB : A ⊆ B) : generatedSubgroup φ A ≤ generatedSubgroup φ B :=
  AddSubgroup.closure_mono (Set.image_mono hAB)

variable {α ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, AddGroup (G i)]

def HasStableGeneratedSubgroups (φ : ∀ i, α → G i) (B : Finset α) (r : ℕ) : Prop :=
  ∀ D ⊆ B, B.card ≤ D.card + r → ∀ i, generatedSubgroup (φ i) D = generatedSubgroup (φ i) B

noncomputable def subgroupIndexPotential (φ : ∀ i, α → G i) (B : Finset α) : ℕ :=
  ∑ i, (generatedSubgroup (φ i) B).index

theorem subgroupIndexPotential_le {φ : ∀ i, α → G i} {B : Finset α} {L : ℕ}
    (hindex : ∀ i, (generatedSubgroup (φ i) B).index ≤ L) :
    subgroupIndexPotential φ B ≤ Fintype.card ι * L := by
  calc
    subgroupIndexPotential φ B = ∑ i, (generatedSubgroup (φ i) B).index := rfl
    _ ≤ ∑ _i : ι, L := Finset.sum_le_sum (fun i _hi => hindex i)
    _ = Fintype.card ι * L := by simp

theorem subgroupIndexPotential_lt_of_strict {φ : ∀ i, α → G i} {D B : Finset α}
    (hDB : D ⊆ B) (hfinite : ∀ i, (generatedSubgroup (φ i) D).FiniteIndex)
    (hstrict : ∃ i, generatedSubgroup (φ i) D ≠ generatedSubgroup (φ i) B) :
    subgroupIndexPotential φ B < subgroupIndexPotential φ D := by
  have hmono (i : ι) : (generatedSubgroup (φ i) B).index ≤
      (generatedSubgroup (φ i) D).index := by
    letI := hfinite i
    exact AddSubgroup.index_antitone (generatedSubgroup_mono (φ i) hDB)
  obtain ⟨i, hi⟩ := hstrict
  have hlt : (generatedSubgroup (φ i) B).index < (generatedSubgroup (φ i) D).index := by
    letI := hfinite i
    exact AddSubgroup.index_strictAnti (lt_of_le_of_ne (generatedSubgroup_mono (φ i) hDB) hi)
  exact Finset.sum_lt_sum (fun j _hj => hmono j) ⟨i, Finset.mem_univ i, hlt⟩

/-- Removing at most `r` elements per strict subgroup decrease terminates with
uniform deletion loss, since the sum of the indices is bounded. -/
theorem exists_subset_with_stable_generatedSubgroups (φ : ∀ i, α → G i)
    (A : Finset α) (r L : ℕ)
    (hindex : ∀ D ⊆ A, A.card ≤ D.card + (Fintype.card ι * L + 1) * r →
      ∀ i, (generatedSubgroup (φ i) D).FiniteIndex ∧ (generatedSubgroup (φ i) D).index ≤ L) :
    ∃ B ⊆ A, A.card ≤ B.card + (Fintype.card ι * L) * r ∧
      HasStableGeneratedSubgroups φ B r := by
  classical
  apply exists_good_subset_of_bounded_potential
    (potential := subgroupIndexPotential φ) (K := Fintype.card ι * L)
  · intro D hDA hcost
    exact subgroupIndexPotential_le (fun i => (hindex D hDA hcost i).2)
  · intro B hBA hcost hnot
    simp only [HasStableGeneratedSubgroups] at hnot
    push Not at hnot
    obtain ⟨D, hDB, hremove, i, hne⟩ := hnot
    have hDA : D ⊆ A := hDB.trans hBA
    have hDcost : A.card ≤ D.card + (Fintype.card ι * L + 1) * r := by
      calc
        A.card ≤ B.card + (Fintype.card ι * L) * r := hcost
        _ ≤ (D.card + r) + (Fintype.card ι * L) * r := Nat.add_le_add_right hremove _
        _ = D.card + (Fintype.card ι * L + 1) * r := by ring
    refine ⟨D, hDB, hremove, ?_⟩
    exact subgroupIndexPotential_lt_of_strict hDB
      (fun j => (hindex D hDA hDcost j).1) ⟨i, hne⟩

end Erdos587.CFP
