/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedBranchPlacement

/-!
# Constructing the next literal marked partial placement

The history theorem supplies the actual fresh graph copy; appendBranch
stores it while preserving all previous copies and their group assignments.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedPlacementAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceMarkedBranchPlacement Erdos547b.ZhaoSourceMarkedHistoryStep
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b : ℕ} (F : OrderedRootedForest b) (marks : ∀ i, Finset (Fin (F.size i)))
variable {selected : Finset (Fin b)} {parent : Fin b → Fin hostN}

theorem exists_placementAdvance (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hC : 0 < C.card)
    (E : Placement W Q S O P F marks selected parent)
    (base : Finset (Fin hostN)) (hbase : ∀ x, Disjoint base (P.support W Q S O x))
    (hsize : ∀ j ∈ selected, 3 ≤ F.size j)
    (hmarks : (∑ j : {i // i ∈ selected}, ((marks j.1).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize)
    (htotal : (∑ j : {i // i ∈ selected}, (F.size j.1 : ℝ)) ≤
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize)
    (i : Fin b) (hi : i ∉ selected) (bad : Finset {c // c ∈ C}) (hbad : 16 * bad.card ≤ C.card)
    (hparent : ∀ x, x ∉ bad → (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
      (((whole W (P.center x)).filter ((embeddingHost W).Adj (parent i))).card : ℝ))
    (hcolor : ∀ a ∈ marks i, (F.isTree i).coloringTwoOfVert (F.root i) a = 0)
    (hsmall : F.size i ≤ freshBranchBound α W.clusterSize) :
    ∃ E' : Placement W Q S O P F marks (insert i selected) parent,
      (∀ j (hj : j ∈ selected), E'.forestCopy.componentCopy j (Finset.mem_insert_of_mem hj) =
        E.forestCopy.componentCopy j hj) ∧
      (∀ j (hj : j ∈ selected), E'.group ⟨j, Finset.mem_insert_of_mem hj⟩ = E.group ⟨j, hj⟩) ∧
      (∀ a, E'.forestCopy.componentCopy i (Finset.mem_insert_self _ _) a ∉ base) := by
  let copies := fun j : {i // i ∈ selected} => E.forestCopy.componentCopy j.1 j.2
  have hroot (j : {i // i ∈ selected}) : copies j (F.root j.1) ∈ whole W (P.center (E.group j)) :=
    (E.marked j.1 j.2 _ (Finset.mem_insert_self _ _)).1
  have hmark (j : {i // i ∈ selected}) (a) (ha : a ∈ marks j.1) :
      copies j a ∈ whole W (P.center (E.group j)) :=
    (E.marked j.1 j.2 a (Finset.mem_insert_of_mem ha)).1
  obtain ⟨x, slot, f, _, hfattach, hfresh, hfmarked, hfother, _, _⟩ :=
    exists_historyStep W Q S O P (fun j : {i // i ∈ selected} => Fin (F.size j.1))
      (fun j => F.tree j.1) (fun j => F.root j.1) (fun j => marks j.1) copies E.group
      hα hα1 hC base hbase hroot hmark (fun j => E.other j.1 j.2)
      (fun j => by simpa only [Fintype.card_fin] using hsize j.1 j.2) hmarks
      (by simpa only [Fintype.card_fin] using htotal) (parent i) bad hbad hparent
      (F.tree i) (F.isTree i) (F.root i) (marks i) hcolor
      (by simpa only [Fintype.card_fin] using hsmall)
  have hfresh' : ∀ a, f a ∉ E.used W Q S O P F marks := by
    intro a ha
    apply hfresh a
    exact Finset.mem_union_right _ ha
  have hfbase : ∀ a, f a ∉ base := by
    intro a ha
    exact hfresh a (Finset.mem_union_left _ ha)
  have hfpairs : ∀ a, a ≠ F.root i → a ∉ marks i → f a ∈ P.pairs W Q S O x := by
    intro a har ham
    have h := hfother a har ham
    have hpair : f a ∈ whole W (P.X (x, slot)) ∪ whole W (P.Y (x, slot)) := by
      split_ifs at h
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ h
    exact Finset.mem_biUnion.mpr ⟨slot, Finset.mem_univ _, hpair⟩
  let E' := E.appendBranch W Q S O P F marks i hi x f hfattach hfresh' hfmarked hfpairs
  refine ⟨E', ?_, ?_, ?_⟩
  · exact E.appendBranch_preserves_copy W Q S O P F marks i hi x f hfattach hfresh' hfmarked hfpairs
  · exact E.appendBranch_preserves_group W Q S O P F marks i hi x f hfattach hfresh' hfmarked hfpairs
  · intro a
    have heq := E.appendBranch_new_copy W Q S O P F marks i hi x f hfattach hfresh' hfmarked hfpairs
    change E'.forestCopy.componentCopy i (Finset.mem_insert_self _ _) a ∉ base
    change E'.forestCopy.componentCopy i (Finset.mem_insert_self _ _) = f at heq
    rw [heq]
    exact hfbase a

end Erdos547b.ZhaoSourceMarkedPlacementAdvance

#print axioms Erdos547b.ZhaoSourceMarkedPlacementAdvance.exists_placementAdvance
