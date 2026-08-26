/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalOnlineCandidates

/-!
# Hierarchical assembly from a concrete online step

The hierarchy assembly argument only needs an `OnlineStep` at each stage.
This module factors that recursion out of the older uniform-capacity
constructor, allowing different source classes to use different genuine
local embedding theorems while retaining one global injective copy.

The callback is an internal construction interface: public applications must
build it from graph and numeric hypotheses, rather than assume a copy.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalOnlineFromStep

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s : ℕ} {B : Type u}

section Construction

variable [Fintype B] [DecidableEq B]
  (F : HierarchicalSegmentForest r s)
  (G : SimpleGraph B) [DecidableRel G.Adj]
  (originalImage : Fin r → B)
  (rootCandidate : Fin s → Finset B)
  (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
  (step : ∀ i
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j),
    OnlineStep F G originalImage rootCandidate interiorCandidate i prior)

/-- The well-founded run of an arbitrary concrete hierarchy step. -/
noncomputable def segmentFromStep (i : Fin s) :
    SegmentRealization F G rootCandidate interiorCandidate i :=
  (step i (fun j _ => segmentFromStep j)).data
termination_by i.val

theorem segmentFromStep_fresh (i j : Fin s) (hj : j.val < i.val)
    (a : Fin (F.segments.size i)) (b : Fin (F.segments.size j)) :
    (segmentFromStep F G originalImage rootCandidate interiorCandidate step i).copy a ≠
      (segmentFromStep F G originalImage rootCandidate interiorCandidate step j).copy b := by
  rw [segmentFromStep.eq_def]
  exact (step i (fun j _ => segmentFromStep F G originalImage rootCandidate
    interiorCandidate step j)).fresh j hj a b

theorem segmentFromStep_parent_adj_original (i : Fin s) (q : Fin r)
    (hp : F.parent i = Sum.inl q) :
    G.Adj (originalImage q)
      (segmentFromStep F G originalImage rootCandidate interiorCandidate
        step i).rootImage := by
  rw [segmentFromStep.eq_def]
  exact (step i (fun j _ => segmentFromStep F G originalImage rootCandidate
    interiorCandidate step j)).parent_adj_original q hp

theorem segmentFromStep_parent_adj_segment (i j : Fin s)
    (a : Fin (F.segments.size j)) (hp : F.parent i = Sum.inr ⟨j, a⟩) :
    G.Adj
      ((segmentFromStep F G originalImage rootCandidate interiorCandidate
        step j).copy a)
      (segmentFromStep F G originalImage rootCandidate interiorCandidate
        step i).rootImage := by
  conv_rhs => rw [segmentFromStep.eq_def]
  exact (step i (fun j _ => segmentFromStep F G originalImage rootCandidate
    interiorCandidate step j)).parent_adj_segment j a hp

include step in
/-- Assemble a full hierarchy copy from locally constructed online steps. -/
theorem exists_hierarchicalCandidateEmbedding_fromStep
    (horiginalInj : Function.Injective originalImage)
    (horiginalOutsideRoot : ∀ q i, originalImage q ∉ rootCandidate i)
    (horiginalOutsideInterior : ∀ q i a,
      originalImage q ∉ interiorCandidate i a) :
    Nonempty (HierarchicalCandidateEmbedding F G originalImage
      rootCandidate interiorCandidate) := by
  classical
  let D : ∀ i, SegmentRealization F G rootCandidate interiorCandidate i :=
    fun i => segmentFromStep F G originalImage rootCandidate interiorCandidate
      step i
  let E : F.segments.Embedding G :=
    { copy := fun i => (D i).copy
      injective := by
        rintro ⟨i, a⟩ ⟨j, b⟩ hab
        by_cases hij : i = j
        · subst j
          have hab' : a = b := (D i).copy.injective hab
          subst b
          rfl
        · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
          rcases lt_or_gt_of_ne hv with hji | hij'
          · exact False.elim
              ((segmentFromStep_fresh F G originalImage rootCandidate
                interiorCandidate step j i hji b a) hab.symm)
          · exact False.elim
              ((segmentFromStep_fresh F G originalImage rootCandidate
                interiorCandidate step i j hij' a b) hab) }
  have hrootOutside : ∀ q i a, originalImage q ≠ E.copy i a := by
    intro q i a heq
    by_cases ha : a = F.segments.root i
    · apply horiginalOutsideRoot q i
      have hEqRoot : originalImage q = (D i).rootImage := by
        calc
          originalImage q = E.copy i a := heq
          _ = (D i).copy a := rfl
          _ = (D i).copy (F.segments.root i) := congrArg (D i).copy ha
          _ = (D i).rootImage := (D i).map_root
      rw [hEqRoot]
      exact (D i).root_mem
    · apply horiginalOutsideInterior q i a
      rw [heq]
      exact (D i).map_nonroot a ha
  have hparentAdj : ∀ i,
      G.Adj
        (F.assembledMap originalImage (fun j a => E.copy j a) (F.parent i))
        (E.copy i (F.segments.root i)) := by
    intro i
    cases hp : F.parent i with
    | inl q =>
        change G.Adj (originalImage q) ((D i).copy (F.segments.root i))
        rw [(D i).map_root]
        exact segmentFromStep_parent_adj_original F G originalImage
          rootCandidate interiorCandidate step i q hp
    | inr z =>
        rcases z with ⟨j, a⟩
        change G.Adj ((D j).copy a) ((D i).copy (F.segments.root i))
        rw [(D i).map_root]
        exact segmentFromStep_parent_adj_segment F G originalImage
          rootCandidate interiorCandidate step i j a hp
  let fullCopy := F.copyOfSegmentEmbedding G originalImage E horiginalInj
    hrootOutside hparentAdj
  exact ⟨
    { segmentEmbedding := E
      rootImage := fun i => (D i).rootImage
      map_root := fun i => (D i).map_root
      map_nonroot := fun i a ha => (D i).map_nonroot a ha
      root_mem := fun i => (D i).root_mem
      parent_adj := hparentAdj
      fullCopy := fullCopy
      fullCopy_root := fun _ => rfl
      fullCopy_segment := fun _ _ => rfl }⟩

end Construction

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalOnlineFromStep

#print axioms Erdos547b.ZhaoLemma59HierarchicalOnlineFromStep.HierarchicalSegmentForest.exists_hierarchicalCandidateEmbedding_fromStep
