/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedBatchAdvance

/-!
# Advancing marked branches at one actual owner root

The root map is updated only at the current owner. Old attachments, copies
and groups are preserved; one root's good-group bound serves its whole batch.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedOwnerAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceMarkedBranchPlacement Erdos547b.ZhaoSourceMarkedBatchAdvance
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b r : ℕ} (F : OrderedRootedForest b) (marks : ∀ i, Finset (Fin (F.size i)))
variable (selected : Finset (Fin b)) (owner : Fin b → Fin r)

theorem ownerPrefix_mono {n m : ℕ} (hnm : n ≤ m) :
    ownerPrefix selected owner n ⊆ ownerPrefix selected owner m := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2.trans_le hnm⟩

private def castPlacement {s t : Finset (Fin b)} {parent : Fin b → Fin hostN} (h : s = t)
    (E : Placement W Q S O P F marks s parent) : Placement W Q S O P F marks t parent := h ▸ E

private theorem castPlacement_copy {s t : Finset (Fin b)} {parent : Fin b → Fin hostN} (h : s = t)
    (E : Placement W Q S O P F marks s parent) (j : Fin b) (hj : j ∈ t) :
    (castPlacement W Q S O P F marks h E).forestCopy.componentCopy j hj =
      E.forestCopy.componentCopy j (h.symm ▸ hj) := by
  subst t
  rfl

private theorem castPlacement_group {s t : Finset (Fin b)} {parent : Fin b → Fin hostN} (h : s = t)
    (E : Placement W Q S O P F marks s parent) (j : Fin b) (hj : j ∈ t) :
    (castPlacement W Q S O P F marks h E).group ⟨j, hj⟩ = E.group ⟨j, h.symm ▸ hj⟩ := by
  subst t
  rfl

theorem exists_ownerAdvance (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hC : 0 < C.card)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (E : Placement W Q S O P F marks (ownerPrefix selected owner n.val) (fun i => rootImage (owner i)))
    (base : Finset (Fin hostN)) (hbase : ∀ x, Disjoint base (P.support W Q S O x))
    (hsize : ∀ j ∈ selected, 3 ≤ F.size j)
    (hmarks : (∑ j ∈ selected, ((marks j).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize)
    (htotal : (∑ j ∈ selected, (F.size j : ℝ)) ≤
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize)
    (hcolor : ∀ i ∈ selected, ∀ a ∈ marks i, (F.isTree i).coloringTwoOfVert (F.root i) a = 0)
    (hsmall : ∀ i ∈ selected, F.size i ≤ freshBranchBound α W.clusterSize)
    (z : Fin hostN) (bad : Finset {c // c ∈ C}) (hbad : 16 * bad.card ≤ C.card)
    (hgood : ∀ x, x ∉ bad → (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
      (((whole W (P.center x)).filter ((embeddingHost W).Adj z)).card : ℝ)) :
    ∃ E' : Placement W Q S O P F marks (ownerPrefix selected owner (n.val + 1))
        (fun i => Function.update rootImage n z (owner i)),
      (∀ j (hj : j ∈ ownerPrefix selected owner n.val), E'.forestCopy.componentCopy j
        (ownerPrefix_mono selected owner (Nat.le_succ n.val) hj) = E.forestCopy.componentCopy j hj) ∧
      (∀ j (hj : j ∈ ownerPrefix selected owner n.val), E'.group
        ⟨j, ownerPrefix_mono selected owner (Nat.le_succ n.val) hj⟩ = E.group ⟨j, hj⟩) := by
  let parent' := fun i => Function.update rootImage n z (owner i)
  have hagrees : ∀ i ∈ ownerPrefix selected owner n.val, parent' i = rootImage (owner i) := by
    intro i hi
    have hbefore := (Finset.mem_filter.mp hi).2
    have hne : owner i ≠ n := fun h => (Nat.ne_of_lt hbefore) (congrArg Fin.val h)
    exact Function.update_of_ne hne z rootImage
  let E₀ := E.reparent W Q S O P F marks parent' hagrees
  have hsub : ownerPrefix selected owner n.val ∪ ownerBatch selected owner n ⊆ selected :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hmarkSubset : (∑ j ∈ ownerPrefix selected owner n.val ∪ ownerBatch selected owner n,
      ((marks j).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans hmarks
  have hmassSubset : (∑ j ∈ ownerPrefix selected owner n.val ∪ ownerBatch selected owner n,
      (F.size j : ℝ)) ≤ (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans htotal
  obtain ⟨E₁, hcopies, hgroups⟩ := exists_batchAdvance W Q S O P F marks hα hα1 hC E₀
    base hbase (fun _ => bad) (ownerBatch selected owner n)
    (ownerPrefix_disjoint_ownerBatch selected owner n.val n.isLt)
    (fun j hj => hsize j (hsub hj)) hmarkSubset hmassSubset
    (fun i hi => hcolor i (Finset.mem_filter.mp hi).1)
    (fun i hi => hsmall i (Finset.mem_filter.mp hi).1)
    (fun _ _ => hbad) (by
      intro i hi x hx
      have ho := (Finset.mem_filter.mp hi).2
      simpa only [parent', ho, Function.update_self] using hgood x hx)
  let hdom := ownerPrefix_succ selected owner n.val n.isLt
  refine ⟨castPlacement W Q S O P F marks hdom E₁, ?_, ?_⟩
  · intro j hj
    rw [castPlacement_copy]
    exact hcopies j hj
  · intro j hj
    rw [castPlacement_group]
    exact hgroups j hj

theorem exists_ownerSkip (rootImage : Fin r → Fin hostN) (n : Fin r)
    (E : Placement W Q S O P F marks (ownerPrefix selected owner n.val) (fun i => rootImage (owner i)))
    (z : Fin hostN) (hno : ∀ i ∈ selected, owner i ≠ n) :
    ∃ E' : Placement W Q S O P F marks (ownerPrefix selected owner (n.val + 1))
        (fun i => Function.update rootImage n z (owner i)),
      (∀ j (hj : j ∈ ownerPrefix selected owner n.val), E'.forestCopy.componentCopy j
        (ownerPrefix_mono selected owner (Nat.le_succ n.val) hj) = E.forestCopy.componentCopy j hj) ∧
      (∀ j (hj : j ∈ ownerPrefix selected owner n.val), E'.group
        ⟨j, ownerPrefix_mono selected owner (Nat.le_succ n.val) hj⟩ = E.group ⟨j, hj⟩) := by
  have hdom : ownerPrefix selected owner (n.val + 1) = ownerPrefix selected owner n.val := by
    ext i
    simp only [ownerPrefix, Finset.mem_filter]
    constructor
    · intro hi
      have hne : (owner i).val ≠ n.val := fun h => hno i hi.1 (Fin.ext h)
      exact ⟨hi.1, by omega⟩
    · intro hi
      exact ⟨hi.1, Nat.lt_succ_of_lt hi.2⟩
  let parent' := fun i => Function.update rootImage n z (owner i)
  have hagrees : ∀ i ∈ ownerPrefix selected owner n.val, parent' i = rootImage (owner i) := by
    intro i hi
    exact Function.update_of_ne (hno i (Finset.mem_filter.mp hi).1) z rootImage
  let E₀ := E.reparent W Q S O P F marks parent' hagrees
  refine ⟨castPlacement W Q S O P F marks hdom.symm E₀, ?_, ?_⟩
  · intro j hj
    rw [castPlacement_copy]
    rfl
  · intro j hj
    rw [castPlacement_group]
    rfl

end Erdos547b.ZhaoSourceMarkedOwnerAdvance

#print axioms Erdos547b.ZhaoSourceMarkedOwnerAdvance.exists_ownerAdvance
#print axioms Erdos547b.ZhaoSourceMarkedOwnerAdvance.exists_ownerSkip
