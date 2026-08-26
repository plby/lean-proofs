/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePrivatePairGeometry

/-!
# Disjoint whole supports of the actual private groups
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePrivatePairGeometry

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)

def Geometry.pairs (x : {c // c ∈ C}) :=
  privatePairUnion W (fun i => P.X (x, i)) (fun i => P.Y (x, i))

def Geometry.support (x : {c // c ∈ C}) := whole W (P.center x) ∪ P.pairs W Q S O x

theorem Geometry.center_disjoint_pairs (x y : {c // c ∈ C}) :
    Disjoint (whole W (P.center x)) (P.pairs W Q S O y) := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvP
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hvP
  exact Finset.disjoint_left.mp (P.center_pair_disjoint x (y, i)) hvC hi

theorem Geometry.pair_groups_disjoint (x y : {c // c ∈ C}) (hxy : x ≠ y) :
    Disjoint (P.pairs W Q S O x) (P.pairs W Q S O y) := by
  apply Finset.disjoint_left.mpr
  intro v hvX hvY
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hvX
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hvY
  exact Finset.disjoint_left.mp (P.pairs_disjoint (x, i) (y, j)
    (fun h => hxy (congrArg Prod.fst h))) hi hj

theorem Geometry.supports_disjoint (x y : {c // c ∈ C}) (hxy : x ≠ y) :
    Disjoint (P.support W Q S O x) (P.support W Q S O y) := by
  apply Finset.disjoint_union_left.mpr
  constructor <;> apply Finset.disjoint_union_right.mpr
  · exact ⟨P.centers_disjoint W Q S O x y hxy, P.center_disjoint_pairs W Q S O x y⟩
  · exact ⟨(P.center_disjoint_pairs W Q S O y x).symm, P.pair_groups_disjoint W Q S O x y hxy⟩

theorem Geometry.three_sets_subset_support (x : {c // c ∈ C}) (i : Fin 4) :
    whole W (P.center x) ∪ whole W (P.X (x, i)) ∪ whole W (P.Y (x, i)) ⊆
      P.support W Q S O x := by
  intro v hv
  have hp : whole W (P.X (x, i)) ∪ whole W (P.Y (x, i)) ⊆ P.pairs W Q S O x :=
    Finset.subset_biUnion_of_mem (fun j => whole W (P.X (x, j)) ∪ whole W (P.Y (x, j)))
      (Finset.mem_univ i)
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases Finset.mem_union.mp hv with hc | hx
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ (hp (Finset.mem_union_left _ hx))
  · exact Finset.mem_union_right _ (hp (Finset.mem_union_right _ hv))

end Erdos547b.ZhaoSourcePrivatePairGeometry

#print axioms Erdos547b.ZhaoSourcePrivatePairGeometry.Geometry.supports_disjoint
#print axioms Erdos547b.ZhaoSourcePrivatePairGeometry.Geometry.three_sets_subset_support
