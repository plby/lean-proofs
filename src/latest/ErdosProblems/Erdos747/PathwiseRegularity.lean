import ErdosProblems.Erdos747.AggregateBaseBridges

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Checkpoint control of a deletion path -/

/-- The recursively exposed prefix at time `t` of a terminal history at
time `T`, when `k` further deletion choices separate the two times.  Keeping
the equality `t + k = T` explicit avoids making the construction depend on
a proof of truncated subtraction. -/
def deletionHistoryCheckpointPrefix {n : ℕ} (H : Finset (Edge n))
    (T : ℕ) (e : DeletionHistory H T) (t k : ℕ) (h : t + k = T) :
    DeletionHistory H t :=
  deletionHistoryAncestor H t k (castDeletionHistory H h.symm e)

/-- A recursively exposed checkpoint prefix of a uniform terminal deletion
history is uniform. -/
lemma finsetProbability_deletionHistoryCheckpointPrefix {n : ℕ}
    (H : Finset (Edge n)) (T t k : ℕ) (h : t + k = T)
    (hT : T ≤ H.card) (P : DeletionHistory H t → Prop) :
    finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (fun e ↦ P (deletionHistoryCheckpointPrefix H T e t k h)) =
      finsetProbability (Finset.univ : Finset (DeletionHistory H t)) P := by
  subst T
  change finsetProbability
      (Finset.univ : Finset (DeletionHistory H (t + k)))
      (fun e ↦ P (deletionHistoryAncestor H t k e)) =
    finsetProbability (Finset.univ : Finset (DeletionHistory H t)) P
  calc
    finsetProbability (Finset.univ : Finset (DeletionHistory H (t + k)))
        (fun e ↦ P (deletionHistoryAncestor H t k e)) =
      @finsetProbability _ Finset.univ
        (fun e : DeletionHistory H (t + k) ↦
          P (deletionHistoryAncestor H t k e)) (Classical.decPred _) :=
      finsetProbability_decidable_irrel Finset.univ _ _ _
    _ = @finsetProbability _ Finset.univ P (Classical.decPred _) := by
      calc
        @finsetProbability _ Finset.univ
            (fun e : DeletionHistory H (t + k) ↦
              P (deletionHistoryAncestor H t k e)) (Classical.decPred _) =
          finsetProbability
            (Finset.univ : Finset (DeletionHistory H (t + k)))
            (fun e ↦ P (deletionHistoryAncestor H t k e)) :=
          finsetProbability_decidable_irrel Finset.univ _ _ _
        _ = finsetProbability
            (Finset.univ : Finset (DeletionHistory H t)) P :=
          finsetProbability_deletionHistoryAncestor H t k hT P
        _ = @finsetProbability _ Finset.univ P (Classical.decPred _) :=
          finsetProbability_decidable_irrel Finset.univ _ _ _
    _ = finsetProbability (Finset.univ : Finset (DeletionHistory H t)) P :=
      finsetProbability_decidable_irrel Finset.univ _ _ _

/-- A heterogeneous family of checkpoint marginals controls any terminal
event which deterministically produces a failed checkpoint. -/
lemma finsetProbability_le_checkpoint_sum
    {α ι : Type*} (s : Finset α) (I : Finset ι)
    (β : ι → Type*) [∀ i, Fintype (β i)]
    (proj : (i : ι) → α → β i)
    (P : (i : ι) → β i → Prop) (Bad : α → Prop)
    (hcover : ∀ x ∈ s, Bad x → ∃ i ∈ I, P i (proj i x))
    (hmarginal : ∀ i ∈ I,
      finsetProbability s (fun x ↦ P i (proj i x)) ≤
        finsetProbability (Finset.univ : Finset (β i)) (P i)) :
    finsetProbability s Bad ≤
      ∑ i ∈ I,
        finsetProbability (Finset.univ : Finset (β i)) (P i) := by
  calc
    finsetProbability s Bad ≤
        finsetProbability s (fun x ↦ ∃ i ∈ I, P i (proj i x)) := by
      apply finsetProbability_mono_event
      intro x hx hbad
      exact hcover x hx hbad
    _ ≤ ∑ i ∈ I, finsetProbability s (fun x ↦ P i (proj i x)) :=
      finsetProbability_bexists_le_sum s I (fun i x ↦ P i (proj i x))
    _ ≤ ∑ i ∈ I,
        finsetProbability (Finset.univ : Finset (β i)) (P i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmarginal i hi

/-- Deletion-specific checkpoint union bound.  The caller only has to show
that a bad path yields a bad checkpoint; uniform-prefix marginals and the
finite union bound are handled here. -/
lemma finsetProbability_deletionPath_le_checkpoint_sum {n : ℕ}
    (H : Finset (Edge n)) (T : ℕ) (hT : T ≤ H.card)
    (I : Finset ℕ) (gap : ℕ → ℕ)
    (hgap : ∀ t ∈ I, t + gap t = T)
    (P : (t : ℕ) → DeletionHistory H t → Prop)
    (Bad : DeletionHistory H T → Prop)
    (hcover : ∀ e : DeletionHistory H T, Bad e →
      ∃ (i : ↥I),
        P i.1 (deletionHistoryCheckpointPrefix H T e i.1 (gap i.1)
          (hgap i.1 i.2))) :
    finsetProbability (Finset.univ : Finset (DeletionHistory H T)) Bad ≤
      ∑ t ∈ I,
        finsetProbability (Finset.univ : Finset (DeletionHistory H t))
          (P t) := by
  let proj : (i : ↥I) →
      DeletionHistory H T → DeletionHistory H i.1 :=
    fun i e ↦ deletionHistoryCheckpointPrefix H T e i.1 (gap i.1)
      (hgap i.1 i.2)
  let PI : (i : ↥I) → DeletionHistory H i.1 → Prop :=
    fun i ↦ P i.1
  have hbound := finsetProbability_le_checkpoint_sum
      (Finset.univ : Finset (DeletionHistory H T))
      (Finset.univ : Finset ↥I) (fun i ↦ DeletionHistory H i.1)
      proj PI Bad
      (by
        intro e he hbad
        obtain ⟨i, hi⟩ := hcover e hbad
        exact ⟨i, Finset.mem_univ i, hi⟩)
      (by
        intro i hi
        dsimp only [proj, PI]
        exact (finsetProbability_deletionHistoryCheckpointPrefix H T i.1
          (gap i.1) (hgap i.1 i.2) hT (P i.1)).le)
  exact hbound.trans_eq
    (Finset.sum_subtype I (fun _ ↦ Iff.rfl)
      (fun t ↦ finsetProbability
        (Finset.univ : Finset (DeletionHistory H t)) (P t))).symm

end

end Erdos747
