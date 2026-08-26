/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedPlacementAdvance

/-!
# Finite owner-batch extension of a literal marked placement

All intermediate mass and mark budgets follow by restriction from the
fixed old-plus-batch set. Previously chosen graph images are preserved.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedBatchAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceMarkedBranchPlacement Erdos547b.ZhaoSourceMarkedPlacementAdvance
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b : ℕ} (F : OrderedRootedForest b) (marks : ∀ i, Finset (Fin (F.size i)))
variable {selected : Finset (Fin b)} {parent : Fin b → Fin hostN}

private def castPlacement {s t : Finset (Fin b)} (h : s = t)
    (E : Placement W Q S O P F marks s parent) : Placement W Q S O P F marks t parent := h ▸ E

private theorem castPlacement_copy {s t : Finset (Fin b)} (h : s = t)
    (E : Placement W Q S O P F marks s parent) (j : Fin b) (hj : j ∈ t) :
    (castPlacement W Q S O P F marks h E).forestCopy.componentCopy j hj =
      E.forestCopy.componentCopy j (h.symm ▸ hj) := by
  subst t
  rfl

private theorem castPlacement_group {s t : Finset (Fin b)} (h : s = t)
    (E : Placement W Q S O P F marks s parent) (j : Fin b) (hj : j ∈ t) :
    (castPlacement W Q S O P F marks h E).group ⟨j, hj⟩ = E.group ⟨j, h.symm ▸ hj⟩ := by
  subst t
  rfl

theorem exists_batchAdvance (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hC : 0 < C.card)
    (E : Placement W Q S O P F marks selected parent)
    (base : Finset (Fin hostN)) (hbase : ∀ x, Disjoint base (P.support W Q S O x))
    (bad : Fin b → Finset {c // c ∈ C}) (batch : Finset (Fin b)) :
    Disjoint selected batch →
    (∀ j ∈ selected ∪ batch, 3 ≤ F.size j) →
    (∑ j ∈ selected ∪ batch, ((marks j).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize →
    (∑ j ∈ selected ∪ batch, (F.size j : ℝ)) ≤
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize →
    (∀ i ∈ batch, ∀ a ∈ marks i, (F.isTree i).coloringTwoOfVert (F.root i) a = 0) →
    (∀ i ∈ batch, F.size i ≤ freshBranchBound α W.clusterSize) →
    (∀ i ∈ batch, 16 * (bad i).card ≤ C.card) →
    (∀ i ∈ batch, ∀ x, x ∉ bad i →
      (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
        (((whole W (P.center x)).filter ((embeddingHost W).Adj (parent i))).card : ℝ)) →
    ∃ E' : Placement W Q S O P F marks (selected ∪ batch) parent,
      (∀ j (hj : j ∈ selected), E'.forestCopy.componentCopy j (Finset.mem_union_left _ hj) =
        E.forestCopy.componentCopy j hj) ∧
      (∀ j (hj : j ∈ selected), E'.group ⟨j, Finset.mem_union_left _ hj⟩ = E.group ⟨j, hj⟩) := by
  induction batch using Finset.induction_on with
  | empty =>
      intro _ _ _ _ _ _ _ _
      let h : selected = selected ∪ ∅ := (Finset.union_empty selected).symm
      exact ⟨castPlacement W Q S O P F marks h E,
        fun j hj => castPlacement_copy W Q S O P F marks h E j _,
        fun j hj => castPlacement_group W Q S O P F marks h E j _⟩
  | @insert i batch hi ih =>
      intro hdisjoint hsize hmarks htotal hcolor hsmall hbad hparent
      have hsub : selected ∪ batch ⊆ selected ∪ insert i batch :=
        Finset.union_subset_union (Finset.Subset.refl _) (Finset.subset_insert _ _)
      have hdisjoint' : Disjoint selected batch :=
        hdisjoint.mono_right (Finset.subset_insert _ _)
      have hmarks' : (∑ j ∈ selected ∪ batch, ((marks j).card : ℝ)) ≤
          (epsilon α : ℝ) * W.clusterSize :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans hmarks
      have htotal' : (∑ j ∈ selected ∪ batch, (F.size j : ℝ)) ≤
          (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans htotal
      obtain ⟨E₁, hcopies₁, hgroups₁⟩ := ih hdisjoint' (fun j hj => hsize j (hsub hj)) hmarks' htotal'
        (fun j hj => hcolor j (Finset.mem_insert_of_mem hj))
        (fun j hj => hsmall j (Finset.mem_insert_of_mem hj))
        (fun j hj => hbad j (Finset.mem_insert_of_mem hj))
        (fun j hj => hparent j (Finset.mem_insert_of_mem hj))
      have hin : i ∈ insert i batch := Finset.mem_insert_self _ _
      have hiSelected : i ∉ selected := fun hs => Finset.disjoint_left.mp hdisjoint hs hin
      have hiOld : i ∉ selected ∪ batch := by simpa only [Finset.mem_union, not_or] using And.intro hiSelected hi
      obtain ⟨E₂, hcopies₂, hgroups₂, _⟩ := exists_placementAdvance W Q S O P F marks hα hα1 hC
        E₁ base hbase (fun j hj => hsize j (hsub hj))
        (by rw [Finset.sum_coe_sort (selected ∪ batch) (fun j => ((marks j).card : ℝ))]; exact hmarks')
        (by rw [Finset.sum_coe_sort (selected ∪ batch) (fun j => (F.size j : ℝ))]; exact htotal')
        i hiOld (bad i) (hbad i hin) (hparent i hin) (hcolor i hin) (hsmall i hin)
      have hdom : selected ∪ insert i batch = insert i (selected ∪ batch) := by
        ext j
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      refine ⟨castPlacement W Q S O P F marks hdom.symm E₂, ?_, ?_⟩
      · intro j hj
        rw [castPlacement_copy]
        exact (hcopies₂ j (Finset.mem_union_left _ hj)).trans (hcopies₁ j hj)
      · intro j hj
        rw [castPlacement_group]
        exact (hgroups₂ j (Finset.mem_union_left _ hj)).trans (hgroups₁ j hj)

end Erdos547b.ZhaoSourceMarkedBatchAdvance

#print axioms Erdos547b.ZhaoSourceMarkedBatchAdvance.exists_batchAdvance
