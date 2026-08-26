/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalCoordinatePools

/-!
# Online hierarchical realization with coordinate-sensitive pools

This is the side-sensitive counterpart of `HierarchicalUnifiedPools`.
Matching-edge interiors alternate between endpoint clusters, so every
coordinate carries its own physical pool.  At an online step we delete only
earlier images from the target coordinate's pool.  The degree certificate is
the exact side load plus one small-component carry.

All hierarchy parent edges are built during the recursion.  In particular,
the result realizes the original cross-component cut edges when partition
parents are included among the hierarchy marks.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalCoordinateOnline

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s : ℕ} {B : Type u} {Pool : Type*} [DecidableEq Pool]

section Construction

variable [Fintype B] [DecidableEq B]
  (F : HierarchicalSegmentForest r s)
  (G : SimpleGraph B) [DecidableRel G.Adj]
  (originalImage : Fin r → B)
  (small : ℕ)
  (rootPool : Fin s → Pool)
  (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
  (rootCandidate : Fin s → Finset B)
  (interiorCandidate : (i : Fin s) →
    Fin (F.segments.size i) → Finset B)
  (hsmall : ∀ i, F.segments.size i ≤ small)
  (horiginalInj : Function.Injective originalImage)
  (horiginalOutsideRoot : ∀ q i, originalImage q ∉ rootCandidate i)
  (horiginalOutsideInterior : ∀ q i a,
    originalImage q ∉ interiorCandidate i a)
  (hrootDisjoint : ∀ i j, rootPool i ≠ rootPool j →
    Disjoint (rootCandidate i) (rootCandidate j))
  (hinteriorDisjoint : ∀ i a j b, interiorPool i a ≠ interiorPool j b →
    Disjoint (interiorCandidate i a) (interiorCandidate j b))
  (hrootInteriorDisjoint : ∀ i j a, rootPool i ≠ interiorPool j a →
    Disjoint (rootCandidate i) (interiorCandidate j a))
  (hattachOriginal : ∀ i q, F.parent i = Sum.inl q →
    coordinatePoolLoad F rootPool interiorPool (rootPool i) + small + 1 ≤
      #((rootCandidate i).filter (G.Adj (originalImage q))))
  (hattachSegment : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    ∀ z, z ∈ sourceCandidate F rootCandidate interiorCandidate j a →
      coordinatePoolLoad F rootPool interiorPool (rootPool i) + small + 1 ≤
        #((rootCandidate i).filter (G.Adj z)))
  (hinternal : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    ∀ z, z ∈ sourceCandidate F rootCandidate interiorCandidate i a →
      coordinatePoolLoad F rootPool interiorPool (interiorPool i b) +
          small + 1 ≤
        #((interiorCandidate i b).filter (G.Adj z)))

/-- One topological step with coordinate-sensitive deletion. -/
noncomputable def coordinateOnlineStep (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) :
    OnlineStep F G originalImage rootCandidate interiorCandidate i prior := by
  classical
  let parentWitness : ∃ z : B,
      coordinatePoolLoad F rootPool interiorPool (rootPool i) + small + 1 ≤
          #((rootCandidate i).filter (G.Adj z)) ∧
        ((∃ q, F.parent i = Sum.inl q ∧ z = originalImage q) ∨
          ∃ w : Σ j : Fin s, {a : Fin (F.segments.size j) // j.val < i.val},
            F.parent i = Sum.inr ⟨w.1, w.2.1⟩ ∧
              z = (prior w.1 w.2.2).copy w.2.1) := by
    cases hp : F.parent i with
    | inl q =>
        exact ⟨originalImage q, hattachOriginal i q hp,
          Or.inl ⟨q, rfl, rfl⟩⟩
    | inr x =>
        rcases x with ⟨j, a⟩
        let R := prior j (F.parent_earlier i j a hp)
        have hmem : R.copy a ∈
            sourceCandidate F rootCandidate interiorCandidate j a := by
          by_cases ha : a = F.segments.root j
          · simpa [sourceCandidate, ha, R.map_root] using R.root_mem
          · simpa [sourceCandidate, ha] using R.map_nonroot a ha
        exact ⟨R.copy a, hattachSegment i j a hp _ hmem,
          Or.inr ⟨⟨j, ⟨a, F.parent_earlier i j a hp⟩⟩, rfl, rfl⟩⟩
  let parentImage := Classical.choose parentWitness
  have hparentDegree :
      coordinatePoolLoad F rootPool interiorPool (rootPool i) + small + 1 ≤
        #((rootCandidate i).filter (G.Adj parentImage)) := by
    simpa [parentImage] using (Classical.choose_spec parentWitness).1
  have hparentSource := (Classical.choose_spec parentWitness).2
  let neighborRoot := (rootCandidate i).filter (G.Adj parentImage)
  let rootUsed := coordinateUsedPool F G rootPool interiorPool rootCandidate
    interiorCandidate i (rootPool i) prior
  have hrootUsed : #rootUsed ≤
      coordinatePoolLoad F rootPool interiorPool (rootPool i) := by
    simpa [rootUsed] using
      card_coordinateUsedPool_le_load F G rootPool interiorPool rootCandidate
        interiorCandidate i (rootPool i) prior
  let rootChoices := neighborRoot \ rootUsed
  have hchoiceCard : 0 < #rootChoices := by
    have hcard := Finset.card_sdiff_add_card_inter neighborRoot rootUsed
    have hinter : #(neighborRoot ∩ rootUsed) ≤ #rootUsed :=
      Finset.card_le_card Finset.inter_subset_right
    have hdeg : #rootUsed + 1 ≤ #neighborRoot := by
      have := hparentDegree
      dsimp only [neighborRoot]
      omega
    change 0 < #(neighborRoot \ rootUsed)
    omega
  let hnonempty : rootChoices.Nonempty := Finset.card_pos.mp hchoiceCard
  let z : B := Classical.choose hnonempty
  have hz : z ∈ rootChoices := Classical.choose_spec hnonempty
  have hzRoot : z ∈ rootCandidate i :=
    (Finset.mem_filter.mp (by
      simpa [neighborRoot] using (Finset.mem_sdiff.mp hz).1)).1
  have hzParent : G.Adj parentImage z :=
    (Finset.mem_filter.mp (by
      simpa [neighborRoot] using (Finset.mem_sdiff.mp hz).1)).2
  have hzUnused : z ∉ rootUsed := (Finset.mem_sdiff.mp hz).2
  let used : (a : Fin (F.segments.size i)) → Finset B := fun a ↦
    coordinateUsedPool F G rootPool interiorPool rootCandidate
      interiorCandidate i (interiorPool i a) prior
  let candidateNow : Fin (F.segments.size i) → Finset B := fun a ↦
    if a = F.segments.root i then ∅ else interiorCandidate i a \ used a
  have hcurrent (a : Fin (F.segments.size i)) :
      F.segments.size i + #(used a) ≤
        coordinatePoolLoad F rootPool interiorPool (interiorPool i a) +
          small := by
    have h := card_coordinateUsedPool_add_size_le_load_add_small F G rootPool
      interiorPool rootCandidate interiorCandidate small hsmall i
      (interiorPool i a) prior
    simpa [used, Nat.add_comm] using h
  have hrootCross : ∀ a,
      (F.segments.tree i).Adj (F.segments.root i) a →
      F.segments.size i ≤ #(candidateNow a |>.filter (G.Adj z)) := by
    intro a hadj
    have ha : a ≠ F.segments.root i := hadj.ne'
    have hdeg := hinternal i (F.segments.root i) a hadj ha z (by
      simpa [sourceCandidate] using hzRoot)
    simpa [candidateNow, ha] using
      card_neighbors_cleaned_ge G (interiorCandidate i a) (used a) z
        (F.segments.size i) ((hcurrent a).trans (by omega :
          coordinatePoolLoad F rootPool interiorPool (interiorPool i a) +
              small ≤
            coordinatePoolLoad F rootPool interiorPool (interiorPool i a) +
              small + 1) |>.trans hdeg)
  have hcross : ∀ a b, (F.segments.tree i).Adj a b →
      b ≠ F.segments.root i → ∀ v ∈ candidateNow a,
      F.segments.size i ≤ #(candidateNow b |>.filter (G.Adj v)) := by
    intro a b hab hb v hv
    by_cases ha : a = F.segments.root i
    · subst a
      simp [candidateNow] at hv
    have hvOrig : v ∈ interiorCandidate i a :=
      (Finset.mem_sdiff.mp (by simpa [candidateNow, ha] using hv)).1
    have hdeg := hinternal i a b hab hb v (by
      simpa [sourceCandidate, ha] using hvOrig)
    simpa [candidateNow, hb] using
      card_neighbors_cleaned_ge G (interiorCandidate i b) (used b) v
        (F.segments.size i) ((hcurrent b).trans (by omega :
          coordinatePoolLoad F rootPool interiorPool (interiorPool i b) +
              small ≤
            coordinatePoolLoad F rootPool interiorPool (interiorPool i b) +
              small + 1) |>.trans hdeg)
  let hcopyEx := exists_rooted_candidate_copy (F.segments.tree i) G
    (F.segments.isTree i) (F.segments.root i) candidateNow z
    (by simpa only [Fintype.card_fin] using hrootCross)
    (by simpa only [Fintype.card_fin] using hcross)
  let copy := Classical.choose hcopyEx
  have hcopyRoot := (Classical.choose_spec hcopyEx).1
  have hcopyMem := (Classical.choose_spec hcopyEx).2
  let data : SegmentRealization F G rootCandidate interiorCandidate i :=
    { rootImage := z
      root_mem := hzRoot
      copy := copy
      map_root := hcopyRoot
      map_nonroot := by
        intro a ha
        exact (Finset.mem_sdiff.mp (by
          simpa [candidateNow, ha] using hcopyMem a ha)).1 }
  refine
    { data := data
      fresh := ?_
      parent_adj_original := ?_
      parent_adj_segment := ?_ }
  · intro j hj a b heq
    by_cases ha : a = F.segments.root i
    · subst a
      by_cases hb : b = F.segments.root j
      · subst b
        have heq' : z = (prior j hj).rootImage :=
          hcopyRoot.symm.trans (heq.trans (prior j hj).map_root)
        by_cases hp : rootPool j = rootPool i
        · apply hzUnused
          rw [heq']
          exact root_mem_coordinateUsedPool F G rootPool interiorPool
            rootCandidate interiorCandidate i j hj (rootPool i) hp prior
        · apply Finset.disjoint_left.mp (hrootDisjoint i j (Ne.symm hp))
            hzRoot
          rw [heq']
          exact (prior j hj).root_mem
      · have hprior := (prior j hj).map_nonroot b hb
        have heq' : z = (prior j hj).copy b := hcopyRoot.symm.trans heq
        by_cases hp : interiorPool j b = rootPool i
        · apply hzUnused
          rw [heq']
          exact coordinate_mem_coordinateUsedPool F G rootPool interiorPool
            rootCandidate interiorCandidate i j hj b hb (rootPool i) hp prior
        · apply Finset.disjoint_left.mp
            (hrootInteriorDisjoint i j b (Ne.symm hp)) hzRoot
          rw [heq']
          exact hprior
    · have hcur : copy a ∈ interiorCandidate i a :=
        (Finset.mem_sdiff.mp (by
          simpa [candidateNow, ha] using hcopyMem a ha)).1
      have hcurUnused : copy a ∉ used a :=
        (Finset.mem_sdiff.mp (by
          simpa [candidateNow, ha] using hcopyMem a ha)).2
      by_cases hb : b = F.segments.root j
      · subst b
        by_cases hp : rootPool j = interiorPool i a
        · apply hcurUnused
          rw [heq, (prior j hj).map_root]
          exact root_mem_coordinateUsedPool F G rootPool interiorPool
            rootCandidate interiorCandidate i j hj (interiorPool i a) hp prior
        · apply Finset.disjoint_left.mp
            (hrootInteriorDisjoint j i a hp) (prior j hj).root_mem
          rw [← (prior j hj).map_root, ← heq]
          exact hcur
      · have hprior := (prior j hj).map_nonroot b hb
        by_cases hp : interiorPool j b = interiorPool i a
        · apply hcurUnused
          rw [heq]
          exact coordinate_mem_coordinateUsedPool F G rootPool interiorPool
            rootCandidate interiorCandidate i j hj b hb (interiorPool i a)
            hp prior
        · apply Finset.disjoint_left.mp
            (hinteriorDisjoint i a j b (Ne.symm hp)) hcur
          rw [heq]
          exact hprior
  · intro q hp
    rcases hparentSource with ⟨q', hp', hEq⟩ | ⟨w, hp', hEq⟩
    · have hqq : q' = q := Sum.inl.inj (hp'.symm.trans hp)
      subst q'
      change G.Adj (originalImage q) z
      rw [← hEq]
      exact hzParent
    · cases hp'.symm.trans hp
  · intro j a hp
    rcases hparentSource with ⟨q, hp', hEq⟩ | ⟨w, hp', hEq⟩
    · cases hp'.symm.trans hp
    · rcases w with ⟨j', ⟨a', hj'⟩⟩
      have hja : (⟨j', a'⟩ : Σ j, Fin (F.segments.size j)) = ⟨j, a⟩ :=
        Sum.inr.inj (hp'.symm.trans hp)
      cases hja
      change G.Adj ((prior j (F.parent_earlier i j a hp)).copy a) z
      rw [← hEq]
      exact hzParent

noncomputable def coordinateOnlineSegment (i : Fin s) :
    SegmentRealization F G rootCandidate interiorCandidate i :=
  (coordinateOnlineStep F G originalImage small rootPool interiorPool
    rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
    hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i
    (fun j _ ↦ coordinateOnlineSegment j)).data
termination_by i.val

theorem coordinateOnlineSegment_fresh (i j : Fin s) (hj : j.val < i.val)
    (a : Fin (F.segments.size i)) (b : Fin (F.segments.size j)) :
    (coordinateOnlineSegment F G originalImage small rootPool interiorPool
      rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
      hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i).copy a ≠
    (coordinateOnlineSegment F G originalImage small rootPool interiorPool
      rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
      hrootInteriorDisjoint hattachOriginal hattachSegment hinternal j).copy b := by
  rw [coordinateOnlineSegment.eq_def]
  exact (coordinateOnlineStep F G originalImage small rootPool interiorPool
    rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
    hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i
    (fun j _ ↦ coordinateOnlineSegment F G originalImage small rootPool
      interiorPool rootCandidate interiorCandidate hsmall hrootDisjoint
      hinteriorDisjoint hrootInteriorDisjoint hattachOriginal hattachSegment
      hinternal j)).fresh j hj a b

theorem coordinateOnlineSegment_parent_adj_original (i : Fin s) (q : Fin r)
    (hp : F.parent i = Sum.inl q) :
    G.Adj (originalImage q)
      (coordinateOnlineSegment F G originalImage small rootPool interiorPool
        rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
        hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i).rootImage := by
  rw [coordinateOnlineSegment.eq_def]
  exact (coordinateOnlineStep F G originalImage small rootPool interiorPool
    rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
    hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i
    (fun j _ ↦ coordinateOnlineSegment F G originalImage small rootPool
      interiorPool rootCandidate interiorCandidate hsmall hrootDisjoint
      hinteriorDisjoint hrootInteriorDisjoint hattachOriginal hattachSegment
      hinternal j)).parent_adj_original q hp

theorem coordinateOnlineSegment_parent_adj_segment (i j : Fin s)
    (a : Fin (F.segments.size j)) (hp : F.parent i = Sum.inr ⟨j, a⟩) :
    G.Adj
      ((coordinateOnlineSegment F G originalImage small rootPool interiorPool
        rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
        hrootInteriorDisjoint hattachOriginal hattachSegment hinternal j).copy a)
      (coordinateOnlineSegment F G originalImage small rootPool interiorPool
        rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
        hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i).rootImage := by
  conv_rhs => rw [coordinateOnlineSegment.eq_def]
  exact (coordinateOnlineStep F G originalImage small rootPool interiorPool
    rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
    hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i
    (fun j _ ↦ coordinateOnlineSegment F G originalImage small rootPool
      interiorPool rootCandidate interiorCandidate hsmall hrootDisjoint
      hinteriorDisjoint hrootInteriorDisjoint hattachOriginal hattachSegment
      hinternal j)).parent_adj_segment j a hp

include small rootPool interiorPool hsmall horiginalInj horiginalOutsideRoot
  horiginalOutsideInterior hrootDisjoint hinteriorDisjoint
  hrootInteriorDisjoint hattachOriginal hattachSegment hinternal in
/-- Full cut-aware hierarchy embedding from coordinate-side load bounds. -/
theorem exists_hierarchicalCandidateEmbedding_coordinatePools :
    Nonempty (HierarchicalCandidateEmbedding F G originalImage
      rootCandidate interiorCandidate) := by
  classical
  let D : ∀ i, SegmentRealization F G rootCandidate interiorCandidate i :=
    fun i ↦ coordinateOnlineSegment F G originalImage small rootPool interiorPool
      rootCandidate interiorCandidate hsmall hrootDisjoint hinteriorDisjoint
      hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i
  let E : F.segments.Embedding G :=
    { copy := fun i ↦ (D i).copy
      injective := by
        rintro ⟨i, a⟩ ⟨j, b⟩ hab
        by_cases hij : i = j
        · subst j
          have hab' : a = b := (D i).copy.injective hab
          subst b
          rfl
        · have hv : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
          rcases lt_or_gt_of_ne hv with hji | hij'
          · exact False.elim
              ((coordinateOnlineSegment_fresh F G originalImage small rootPool
                interiorPool rootCandidate interiorCandidate hsmall
                hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
                hattachOriginal hattachSegment hinternal j i hji b a) hab.symm)
          · exact False.elim
              ((coordinateOnlineSegment_fresh F G originalImage small rootPool
                interiorPool rootCandidate interiorCandidate hsmall
                hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
                hattachOriginal hattachSegment hinternal i j hij' a b) hab) }
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
      G.Adj (F.assembledMap originalImage (fun j a ↦ E.copy j a) (F.parent i))
        (E.copy i (F.segments.root i)) := by
    intro i
    cases hp : F.parent i with
    | inl q =>
        change G.Adj (originalImage q) ((D i).copy (F.segments.root i))
        rw [(D i).map_root]
        exact coordinateOnlineSegment_parent_adj_original F G originalImage
          small rootPool interiorPool rootCandidate interiorCandidate hsmall
          hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint hattachOriginal
          hattachSegment hinternal i q hp
    | inr x =>
        rcases x with ⟨j, a⟩
        change G.Adj ((D j).copy a) ((D i).copy (F.segments.root i))
        rw [(D i).map_root]
        exact coordinateOnlineSegment_parent_adj_segment F G originalImage
          small rootPool interiorPool rootCandidate interiorCandidate hsmall
          hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint hattachOriginal
          hattachSegment hinternal i j a hp
  let fullCopy := F.copyOfSegmentEmbedding G originalImage E horiginalInj
    hrootOutside hparentAdj
  exact ⟨
    { segmentEmbedding := E
      rootImage := fun i ↦ (D i).rootImage
      map_root := fun i ↦ (D i).map_root
      map_nonroot := fun i a ha ↦ (D i).map_nonroot a ha
      root_mem := fun i ↦ (D i).root_mem
      parent_adj := hparentAdj
      fullCopy := fullCopy
      fullCopy_root := fun _ ↦ rfl
      fullCopy_segment := fun _ _ ↦ rfl }⟩

end Construction

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalCoordinateOnline

#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinateOnline.HierarchicalSegmentForest.exists_hierarchicalCandidateEmbedding_coordinatePools
