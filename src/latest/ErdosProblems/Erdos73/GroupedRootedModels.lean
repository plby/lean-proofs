/- Grouping connected blocks of a left-rooted minor model. -/
import ErdosProblems.Erdos73.RootedPartition
import ErdosProblems.Erdos73.MinorPathLifting

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {T : SimpleGraph I}
variable {A B : Finset V}

namespace LeftRootedModel

def groupBranch (M : LeftRootedModel T G A B) (S : Finset I) : Finset V :=
  S.biUnion M.branch

def groupRoots (M : LeftRootedModel T G A B) (S : Finset I) : Finset V :=
  S.image M.root

theorem mem_groupBranch (M : LeftRootedModel T G A B) (S : Finset I) (v : V) :
    v ∈ M.groupBranch S ↔ ∃ i ∈ S, v ∈ M.branch i := Finset.mem_biUnion

theorem groupBranch_connected (M : LeftRootedModel T G A B) (S : Finset I)
    (hS : (T.induce (S : Set I)).Connected) :
    (G.induce (M.groupBranch S : Set V)).Connected :=
  M.toMinorModel.connected_induce_branchUnion S hS

theorem groupBranch_nonempty (M : LeftRootedModel T G A B) (S : Finset I)
    (hS : S.Nonempty) : (M.groupBranch S).Nonempty := by
  obtain ⟨i, hi⟩ := hS
  exact ⟨M.root i, (M.mem_groupBranch S _).mpr ⟨i, hi, M.root_mem i⟩⟩

theorem groupBranch_subset_left (M : LeftRootedModel T G A B) (S : Finset I) :
    M.groupBranch S ⊆ A := by
  intro v hv
  obtain ⟨i, _, hi⟩ := (M.mem_groupBranch S v).mp hv
  exact M.subset_left i hi

theorem groupBranch_disjoint (M : LeftRootedModel T G A B) {S U : Finset I}
    (hSU : Disjoint S U) : Disjoint (M.groupBranch S) (M.groupBranch U) := by
  rw [Finset.disjoint_left]
  intro v hvS hvU
  obtain ⟨i, hi, hvi⟩ := (M.mem_groupBranch S v).mp hvS
  obtain ⟨j, hj, hvj⟩ := (M.mem_groupBranch U v).mp hvU
  have hij : i ≠ j := fun h => Finset.disjoint_left.mp hSU hi (h ▸ hj)
  exact Finset.disjoint_left.mp (M.disjoint hij) hvi hvj

theorem groupBranch_inter_right (M : LeftRootedModel T G A B) (S : Finset I) :
    M.groupBranch S ∩ B = M.groupRoots S := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvS, hvB⟩ := Finset.mem_inter.mp hv
    obtain ⟨i, hi, hvi⟩ := (M.mem_groupBranch S v).mp hvS
    exact Finset.mem_image.mpr ⟨i, hi, (M.eq_root_of_mem_branch_of_mem_right hvi hvB).symm⟩
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_inter.mpr
      ⟨(M.mem_groupBranch S _).mpr ⟨i, hi, M.root_mem i⟩,
        (Finset.mem_inter.mp (M.root_mem_separator i)).2⟩

theorem groupRoots_subset_separator (M : LeftRootedModel T G A B) (S : Finset I) :
    M.groupRoots S ⊆ A ∩ B := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact M.root_mem_separator i

theorem groupRoots_subset_branch (M : LeftRootedModel T G A B) (S : Finset I) :
    M.groupRoots S ⊆ M.groupBranch S := by
  rw [← M.groupBranch_inter_right S]
  exact Finset.inter_subset_left

theorem groupRoots_card (M : LeftRootedModel T G A B) (S : Finset I) :
    (M.groupRoots S).card = S.card := Finset.card_image_of_injective _ M.root_injective

end LeftRootedModel
end
end Erdos73
