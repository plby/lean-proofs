/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalOnlineCandidates

/-!
# Hierarchical online realization with unified physical pools

The first hierarchical backend separated every segment-root reservoir from
every interior reservoir.  That is correct for Zhao's exceptional `F₀`, but
too strong for the residual arrows: the root of an `F₁`/`F_b` segment lies
in one side of its assigned matching edge and later vertices may return to
that side.

Here `rootPool` and `interiorPool` name the physical occupancy pool charged
by the two kinds of coordinates.  They may coincide.  Every root is chosen
after deleting all earlier images charged to its pool, and every segment is
then embedded after the same deletion.  Thus the conclusion is still an
actual full graph copy, but no false root/interior disjointness premise is
needed.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalUnified

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s : ℕ} {B : Type u} {Pool : Type*} [DecidableEq Pool]

/-- Occupancy charged by one segment to one physical pool. -/
def poolWeight (F : HierarchicalSegmentForest r s)
    (rootPool interiorPool : Fin s → Pool) (i : Fin s) (e : Pool) : ℕ :=
  (if rootPool i = e then 1 else 0) +
    (if interiorPool i = e then F.segments.size i - 1 else 0)

/-- Total root-plus-interior occupancy of a physical pool. -/
def poolLoad (F : HierarchicalSegmentForest r s)
    (rootPool interiorPool : Fin s → Pool) (e : Pool) : ℕ :=
  ∑ i, poolWeight F rootPool interiorPool i e

section Construction

variable [Fintype B] [DecidableEq B]
  (F : HierarchicalSegmentForest r s)
  (G : SimpleGraph B) [DecidableRel G.Adj]
  (originalImage : Fin r → B)
  (rootPool interiorPool : Fin s → Pool)
  (rootCandidate : Fin s → Finset B)
  (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
  (horiginalInj : Function.Injective originalImage)
  (horiginalOutsideRoot : ∀ q i, originalImage q ∉ rootCandidate i)
  (horiginalOutsideInterior : ∀ q i a, originalImage q ∉ interiorCandidate i a)
  (hrootDisjoint : ∀ i j, rootPool i ≠ rootPool j →
    Disjoint (rootCandidate i) (rootCandidate j))
  (hinteriorDisjoint : ∀ i a j b, interiorPool i ≠ interiorPool j →
    Disjoint (interiorCandidate i a) (interiorCandidate j b))
  (hrootInteriorDisjoint : ∀ i j a, rootPool i ≠ interiorPool j →
    Disjoint (rootCandidate i) (interiorCandidate j a))
  (hattachOriginal : ∀ i q, F.parent i = Sum.inl q →
    poolLoad F rootPool interiorPool (rootPool i) + 1 ≤
      #((rootCandidate i).filter (G.Adj (originalImage q))))
  (hattachSegment : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    ∀ z, z ∈ sourceCandidate F rootCandidate interiorCandidate j a →
      poolLoad F rootPool interiorPool (rootPool i) + 1 ≤
        #((rootCandidate i).filter (G.Adj z)))
  (hinternal : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    ∀ z, z ∈ sourceCandidate F rootCandidate interiorCandidate i a →
      poolLoad F rootPool interiorPool (interiorPool i) + 1 ≤
        #((interiorCandidate i b).filter (G.Adj z)))

/-- Images of one earlier segment charged to `e`. -/
def usedPiece (j : Fin s) (e : Pool)
    (R : SegmentRealization F G rootCandidate interiorCandidate j) : Finset B :=
  (if rootPool j = e then {R.rootImage} else ∅) ∪
    (if interiorPool j = e then
      (Finset.univ.erase (F.segments.root j)).image R.copy else ∅)

/-- Every earlier image charged to the physical pool `e`. -/
def usedPool (i : Fin s) (e : Pool)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) : Finset B :=
  (Finset.Iio i).attach.biUnion fun j ↦
    usedPiece F G rootPool interiorPool rootCandidate interiorCandidate j.1 e
      (prior j.1 (Fin.mk_lt_mk.mp (Finset.mem_Iio.mp j.2)))

theorem card_usedPiece_le_weight (j : Fin s) (e : Pool)
    (R : SegmentRealization F G rootCandidate interiorCandidate j) :
    #(usedPiece F G rootPool interiorPool rootCandidate interiorCandidate j e R) ≤
      poolWeight F rootPool interiorPool j e := by
  classical
  rw [usedPiece, poolWeight]
  calc
    #((if rootPool j = e then {R.rootImage} else ∅) ∪
        (if interiorPool j = e then
          (Finset.univ.erase (F.segments.root j)).image R.copy else ∅)) ≤
      #(if rootPool j = e then {R.rootImage} else ∅) +
        #(if interiorPool j = e then
          (Finset.univ.erase (F.segments.root j)).image R.copy else ∅) :=
        by exact Finset.card_union_le _ _
    _ ≤ (if rootPool j = e then 1 else 0) +
        (if interiorPool j = e then F.segments.size j - 1 else 0) := by
      gcongr
      · split <;> simp
      · split
        · exact Finset.card_image_le.trans_eq (by simp)
        · simp

theorem card_usedPool_add_weight_le_load (i : Fin s) (e : Pool)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) :
    #(usedPool F G rootPool interiorPool rootCandidate interiorCandidate i e prior) +
        poolWeight F rootPool interiorPool i e ≤
      poolLoad F rootPool interiorPool e := by
  classical
  have hused : #(usedPool F G rootPool interiorPool rootCandidate
      interiorCandidate i e prior) ≤
      ∑ j ∈ Finset.Iio i, poolWeight F rootPool interiorPool j e := by
    calc
      #(usedPool F G rootPool interiorPool rootCandidate
          interiorCandidate i e prior) ≤
          ∑ j ∈ (Finset.Iio i).attach,
            #(usedPiece F G rootPool interiorPool rootCandidate
              interiorCandidate j.1 e
              (prior j.1 (Fin.mk_lt_mk.mp (Finset.mem_Iio.mp j.2)))) :=
        Finset.card_biUnion_le
      _ ≤ ∑ j ∈ (Finset.Iio i).attach,
          poolWeight F rootPool interiorPool j.1 e := by
        exact Finset.sum_le_sum fun j _ ↦
          card_usedPiece_le_weight F G rootPool interiorPool rootCandidate
            interiorCandidate j.1 e _
      _ = ∑ j ∈ Finset.Iio i,
          poolWeight F rootPool interiorPool j e :=
        Finset.sum_attach (Finset.Iio i)
          (fun j ↦ poolWeight F rootPool interiorPool j e)
  have hsubset : Finset.Iio i ⊆ Finset.univ.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨by
      intro hji
      subst j
      simpa using Finset.mem_Iio.mp hj, Finset.mem_univ _⟩
  calc
    #(usedPool F G rootPool interiorPool rootCandidate interiorCandidate
        i e prior) + poolWeight F rootPool interiorPool i e ≤
      (∑ j ∈ Finset.Iio i, poolWeight F rootPool interiorPool j e) +
        poolWeight F rootPool interiorPool i e := Nat.add_le_add_right hused _
    _ ≤ (∑ j ∈ Finset.univ.erase i,
        poolWeight F rootPool interiorPool j e) +
          poolWeight F rootPool interiorPool i e := by
      exact Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsubset) _
    _ = poolLoad F rootPool interiorPool e := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rfl

theorem root_mem_usedPool (i j : Fin s) (hj : j.val < i.val)
    (e : Pool) (he : rootPool j = e)
    (prior : ∀ t : Fin s, t.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate t) :
    (prior j hj).rootImage ∈
      usedPool F G rootPool interiorPool rootCandidate interiorCandidate i e prior := by
  classical
  apply Finset.mem_biUnion.mpr
  let jm : {j // j ∈ Finset.Iio i} := ⟨j, by simpa using hj⟩
  refine ⟨jm, Finset.mem_attach _ _, ?_⟩
  rw [usedPiece, if_pos he]
  exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

theorem nonroot_mem_usedPool (i j : Fin s) (hj : j.val < i.val)
    (e : Pool) (he : interiorPool j = e)
    (b : Fin (F.segments.size j)) (hb : b ≠ F.segments.root j)
    (prior : ∀ t : Fin s, t.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate t) :
    (prior j hj).copy b ∈
      usedPool F G rootPool interiorPool rootCandidate interiorCandidate i e prior := by
  classical
  apply Finset.mem_biUnion.mpr
  let jm : {j // j ∈ Finset.Iio i} := ⟨j, by simpa using hj⟩
  refine ⟨jm, Finset.mem_attach _ _, ?_⟩
  rw [usedPiece, if_pos he]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩, rfl⟩)

/-- One online step with unified root/interior occupancy. -/
noncomputable def unifiedOnlineStep (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) :
    OnlineStep F G originalImage rootCandidate interiorCandidate i prior := by
  classical
  let parentWitness : ∃ z : B,
      poolLoad F rootPool interiorPool (rootPool i) + 1 ≤
          #((rootCandidate i).filter (G.Adj z)) ∧
        ((∃ q, F.parent i = Sum.inl q ∧ z = originalImage q) ∨
          ∃ w : Σ j : Fin s, {a : Fin (F.segments.size j) // j.val < i.val},
            F.parent i = Sum.inr ⟨w.1, w.2.1⟩ ∧
              z = (prior w.1 w.2.2).copy w.2.1) := by
    cases hp : F.parent i with
    | inl q => exact ⟨originalImage q, hattachOriginal i q hp,
        Or.inl ⟨q, rfl, rfl⟩⟩
    | inr x =>
        rcases x with ⟨j, a⟩
        let R := prior j (F.parent_earlier i j a hp)
        have hmem : R.copy a ∈ sourceCandidate F rootCandidate
            interiorCandidate j a := by
          by_cases ha : a = F.segments.root j
          · simpa [sourceCandidate, ha, R.map_root] using R.root_mem
          · simpa [sourceCandidate, ha] using R.map_nonroot a ha
        exact ⟨R.copy a, hattachSegment i j a hp _ hmem,
          Or.inr ⟨⟨j, ⟨a, F.parent_earlier i j a hp⟩⟩, rfl, rfl⟩⟩
  let parentImage := Classical.choose parentWitness
  have hparentDegree : poolLoad F rootPool interiorPool (rootPool i) + 1 ≤
      #((rootCandidate i).filter (G.Adj parentImage)) := by
    simpa [parentImage] using (Classical.choose_spec parentWitness).1
  have hparentSource :
      ((∃ q, F.parent i = Sum.inl q ∧ parentImage = originalImage q) ∨
        ∃ w : Σ j : Fin s, {a : Fin (F.segments.size j) // j.val < i.val},
          F.parent i = Sum.inr ⟨w.1, w.2.1⟩ ∧
            parentImage = (prior w.1 w.2.2).copy w.2.1) := by
    simpa [parentImage] using (Classical.choose_spec parentWitness).2
  let neighborRoot := (rootCandidate i).filter (G.Adj parentImage)
  let rootUsed := usedPool F G rootPool interiorPool rootCandidate
    interiorCandidate i (rootPool i) prior
  have husedRoot : #rootUsed + 1 ≤
      poolLoad F rootPool interiorPool (rootPool i) := by
    have h := card_usedPool_add_weight_le_load F G rootPool interiorPool
      rootCandidate interiorCandidate i (rootPool i) prior
    have h' : #rootUsed + poolWeight F rootPool interiorPool i (rootPool i) ≤
        poolLoad F rootPool interiorPool (rootPool i) := by
      simpa [rootUsed] using h
    have hw : 1 ≤ poolWeight F rootPool interiorPool i (rootPool i) := by
      simp [poolWeight]
    omega
  let rootChoices := neighborRoot \ rootUsed
  have hchoiceCard : 0 < #rootChoices := by
    have hcard := Finset.card_sdiff_add_card_inter neighborRoot rootUsed
    have hinter : #(neighborRoot ∩ rootUsed) ≤ #rootUsed :=
      Finset.card_le_card Finset.inter_subset_right
    have hdeg : poolLoad F rootPool interiorPool (rootPool i) + 1 ≤
        #neighborRoot := by simpa [neighborRoot] using hparentDegree
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
  let used := usedPool F G rootPool interiorPool rootCandidate
    interiorCandidate i (interiorPool i) prior
  let candidateNow : Fin (F.segments.size i) → Finset B := fun a ↦
    if a = F.segments.root i then ∅ else interiorCandidate i a \ used
  have hcurrent : F.segments.size i + #used ≤
      poolLoad F rootPool interiorPool (interiorPool i) + 1 := by
    have h := card_usedPool_add_weight_le_load F G rootPool interiorPool
      rootCandidate interiorCandidate i (interiorPool i) prior
    have h' : #used +
        poolWeight F rootPool interiorPool i (interiorPool i) ≤
          poolLoad F rootPool interiorPool (interiorPool i) := by
      simpa [used] using h
    have hw : F.segments.size i - 1 ≤
        poolWeight F rootPool interiorPool i (interiorPool i) := by
      simp [poolWeight]
    have hpos : 0 < F.segments.size i :=
      lt_of_le_of_lt (Nat.zero_le _) (F.segments.root i).isLt
    omega
  have hrootCross : ∀ a,
      (F.segments.tree i).Adj (F.segments.root i) a →
      F.segments.size i ≤ #(candidateNow a |>.filter (G.Adj z)) := by
    intro a hadj
    have ha := hadj.ne'
    have hdeg := hinternal i (F.segments.root i) a hadj ha z (by
      simpa [sourceCandidate] using hzRoot)
    simpa [candidateNow, ha] using
      Erdos547b.RegularPair.card_neighbors_cleaned_ge G
        (interiorCandidate i a) used z
        (F.segments.size i) (hcurrent.trans hdeg)
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
      Erdos547b.RegularPair.card_neighbors_cleaned_ge G
        (interiorCandidate i b) used v
        (F.segments.size i) (hcurrent.trans hdeg)
  let hcopyEx := exists_rooted_candidate_copy (F.segments.tree i) G
    (F.segments.isTree i) (F.segments.root i) candidateNow z
    (by simpa only [Fintype.card_fin] using hrootCross)
    (by simpa only [Fintype.card_fin] using hcross)
  let copy := Classical.choose hcopyEx
  have hcopyRoot := (Classical.choose_spec hcopyEx).1
  have hcopyMem := (Classical.choose_spec hcopyEx).2
  let data : SegmentRealization F G rootCandidate interiorCandidate i := {
    rootImage := z
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
        by_cases hg : rootPool j = rootPool i
        · apply hzUnused
          rw [heq']
          exact root_mem_usedPool F G rootPool interiorPool rootCandidate
            interiorCandidate i j hj (rootPool i) hg prior
        · apply Finset.disjoint_left.mp (hrootDisjoint i j (Ne.symm hg)) hzRoot
          rw [heq']
          exact (prior j hj).root_mem
      · have hprior := (prior j hj).map_nonroot b hb
        have heq' : z = (prior j hj).copy b := hcopyRoot.symm.trans heq
        by_cases hg : interiorPool j = rootPool i
        · apply hzUnused
          rw [heq']
          exact nonroot_mem_usedPool F G rootPool interiorPool rootCandidate
            interiorCandidate i j hj (rootPool i) hg b hb prior
        · apply Finset.disjoint_left.mp
            (hrootInteriorDisjoint i j b (Ne.symm hg)) hzRoot
          rw [heq']
          exact hprior
    · have hcur : copy a ∈ interiorCandidate i a :=
        (Finset.mem_sdiff.mp (by
          simpa [candidateNow, ha] using hcopyMem a ha)).1
      have hcurUnused : copy a ∉ used :=
        (Finset.mem_sdiff.mp (by
          simpa [candidateNow, ha] using hcopyMem a ha)).2
      by_cases hb : b = F.segments.root j
      · subst b
        by_cases hg : rootPool j = interiorPool i
        · apply hcurUnused
          rw [heq]
          rw [(prior j hj).map_root]
          exact root_mem_usedPool F G rootPool interiorPool rootCandidate
            interiorCandidate i j hj (interiorPool i) hg prior
        · apply Finset.disjoint_left.mp
            (hrootInteriorDisjoint j i a hg) (prior j hj).root_mem
          rw [← (prior j hj).map_root, ← heq]
          exact hcur
      · have hprior := (prior j hj).map_nonroot b hb
        by_cases hg : interiorPool j = interiorPool i
        · apply hcurUnused
          rw [heq]
          exact nonroot_mem_usedPool F G rootPool interiorPool rootCandidate
            interiorCandidate i j hj (interiorPool i) hg b hb prior
        · apply Finset.disjoint_left.mp
            (hinteriorDisjoint i a j b (Ne.symm hg)) hcur
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

noncomputable def unifiedOnlineSegment (i : Fin s) :
    SegmentRealization F G rootCandidate interiorCandidate i :=
  (unifiedOnlineStep F G originalImage rootPool interiorPool rootCandidate
    interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
    hattachOriginal hattachSegment hinternal i
    (fun j _ ↦ unifiedOnlineSegment j)).data
termination_by i.val

theorem unifiedOnlineSegment_fresh (i j : Fin s) (hj : j.val < i.val)
    (a : Fin (F.segments.size i)) (b : Fin (F.segments.size j)) :
    (unifiedOnlineSegment F G originalImage rootPool interiorPool rootCandidate
      interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
      hattachOriginal hattachSegment hinternal i).copy a ≠
    (unifiedOnlineSegment F G originalImage rootPool interiorPool rootCandidate
      interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
      hattachOriginal hattachSegment hinternal j).copy b := by
  rw [unifiedOnlineSegment.eq_def]
  exact (unifiedOnlineStep F G originalImage rootPool interiorPool rootCandidate
    interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
    hattachOriginal hattachSegment hinternal i
    (fun j _ ↦ unifiedOnlineSegment F G originalImage rootPool interiorPool
      rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
      hrootInteriorDisjoint hattachOriginal hattachSegment hinternal j)).fresh
      j hj a b

theorem unifiedOnlineSegment_parent_adj_original (i : Fin s) (q : Fin r)
    (hp : F.parent i = Sum.inl q) :
    G.Adj (originalImage q)
      (unifiedOnlineSegment F G originalImage rootPool interiorPool rootCandidate
        interiorCandidate hrootDisjoint hinteriorDisjoint
        hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i).rootImage := by
  rw [unifiedOnlineSegment.eq_def]
  exact (unifiedOnlineStep F G originalImage rootPool interiorPool rootCandidate
    interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
    hattachOriginal hattachSegment hinternal i
    (fun j _ ↦ unifiedOnlineSegment F G originalImage rootPool interiorPool
      rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
      hrootInteriorDisjoint hattachOriginal hattachSegment hinternal j)).parent_adj_original q hp

theorem unifiedOnlineSegment_parent_adj_segment (i j : Fin s)
    (a : Fin (F.segments.size j)) (hp : F.parent i = Sum.inr ⟨j, a⟩) :
    G.Adj
      ((unifiedOnlineSegment F G originalImage rootPool interiorPool rootCandidate
        interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
        hattachOriginal hattachSegment hinternal j).copy a)
      (unifiedOnlineSegment F G originalImage rootPool interiorPool rootCandidate
        interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
        hattachOriginal hattachSegment hinternal i).rootImage := by
  conv_rhs => rw [unifiedOnlineSegment.eq_def]
  exact (unifiedOnlineStep F G originalImage rootPool interiorPool rootCandidate
    interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
    hattachOriginal hattachSegment hinternal i
    (fun j _ ↦ unifiedOnlineSegment F G originalImage rootPool interiorPool
      rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
      hrootInteriorDisjoint hattachOriginal hattachSegment hinternal j)).parent_adj_segment j a hp

include rootPool interiorPool horiginalInj horiginalOutsideRoot
  horiginalOutsideInterior hrootDisjoint hinteriorDisjoint
  hrootInteriorDisjoint hattachOriginal hattachSegment hinternal in
/-- Copy-valued arbitrary-special endpoint with unified physical occupancy.
Every hierarchy parent edge is constructed online. -/
theorem exists_hierarchicalCandidateEmbedding_unifiedPools :
    Nonempty (HierarchicalCandidateEmbedding F G originalImage
      rootCandidate interiorCandidate) := by
  classical
  let D : ∀ i, SegmentRealization F G rootCandidate interiorCandidate i :=
    fun i ↦ unifiedOnlineSegment F G originalImage rootPool interiorPool
      rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
      hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i
  let E : F.segments.Embedding G := {
    copy := fun i ↦ (D i).copy
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
            ((unifiedOnlineSegment_fresh F G originalImage rootPool interiorPool
              rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
              hrootInteriorDisjoint hattachOriginal hattachSegment hinternal
              j i hji b a) hab.symm)
        · exact False.elim
            ((unifiedOnlineSegment_fresh F G originalImage rootPool interiorPool
              rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
              hrootInteriorDisjoint hattachOriginal hattachSegment hinternal
              i j hij' a b) hab) }
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
        exact unifiedOnlineSegment_parent_adj_original F G originalImage
          rootPool interiorPool rootCandidate interiorCandidate hrootDisjoint
          hinteriorDisjoint hrootInteriorDisjoint hattachOriginal
          hattachSegment hinternal i q hp
    | inr x =>
        rcases x with ⟨j, a⟩
        change G.Adj ((D j).copy a) ((D i).copy (F.segments.root i))
        rw [(D i).map_root]
        exact unifiedOnlineSegment_parent_adj_segment F G originalImage
          rootPool interiorPool rootCandidate interiorCandidate hrootDisjoint
          hinteriorDisjoint hrootInteriorDisjoint hattachOriginal
          hattachSegment hinternal i j a hp
  let fullCopy := F.copyOfSegmentEmbedding G originalImage E horiginalInj
    hrootOutside hparentAdj
  exact ⟨{
    segmentEmbedding := E
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

end Erdos547b.ZhaoLemma59HierarchicalUnified

#print axioms Erdos547b.ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest.exists_hierarchicalCandidateEmbedding_unifiedPools
