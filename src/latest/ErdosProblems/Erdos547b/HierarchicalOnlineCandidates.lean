/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalSegmentForest
import ErdosProblems.Erdos547b.Lemma59

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalOnline

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59
open Erdos547b.ZhaoLemma59Hierarchical

universe u

namespace HierarchicalSegmentForest

variable {r s c k : ℕ} {B : Type u}

/-- Number of cluster-layer roots assigned to one cluster block. -/
def rootLoad (rootGroup : Fin s → Fin c) (C : Fin c) : ℕ :=
  #{i : Fin s | rootGroup i = C}

/-- Total matching-layer demand assigned to one matching block. -/
def interiorLoad (F : HierarchicalSegmentForest r s)
    (group : Fin s → Fin k) (e : Fin k) : ℕ :=
  ∑ i, if group i = e then F.segments.size i - 1 else 0

/-- Candidate block used by one coordinate of one segment. -/
def sourceCandidate [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (rootCandidate : Fin s → Finset B)
    (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  if a = F.segments.root i then rootCandidate i else interiorCandidate i a

/-- Concrete output of one embedded hierarchical segment. -/
structure SegmentRealization [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s) (G : SimpleGraph B)
    (rootCandidate : Fin s → Finset B)
    (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) where
  rootImage : B
  root_mem : rootImage ∈ rootCandidate i
  copy : (F.segments.tree i).Copy G
  map_root : copy (F.segments.root i) = rootImage
  map_nonroot : ∀ a, a ≠ F.segments.root i → copy a ∈ interiorCandidate i a

section Construction

variable [Fintype B] [DecidableEq B]
  (F : HierarchicalSegmentForest r s)
  (G : SimpleGraph B) [DecidableRel G.Adj]
  (originalImage : Fin r → B)
  (rootGroup : Fin s → Fin c) (group : Fin s → Fin k)
  (rootCandidate : Fin s → Finset B)
  (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
  (horiginalInj : Function.Injective originalImage)
  (horiginalOutsideRoot : ∀ q i, originalImage q ∉ rootCandidate i)
  (horiginalOutsideInterior : ∀ q i a, originalImage q ∉ interiorCandidate i a)
  (hrootDisjoint : ∀ i j, rootGroup i ≠ rootGroup j →
    Disjoint (rootCandidate i) (rootCandidate j))
  (hinteriorDisjoint : ∀ i a j b, group i ≠ group j →
    Disjoint (interiorCandidate i a) (interiorCandidate j b))
  (hrootInteriorDisjoint : ∀ i j a,
    Disjoint (rootCandidate i) (interiorCandidate j a))
  (hattachOriginal : ∀ i q, F.parent i = Sum.inl q →
    rootLoad rootGroup (rootGroup i) + 1 ≤
      #((rootCandidate i).filter (G.Adj (originalImage q))))
  (hattachSegment : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    ∀ z, z ∈ sourceCandidate F rootCandidate interiorCandidate j a →
      rootLoad rootGroup (rootGroup i) + 1 ≤
        #((rootCandidate i).filter (G.Adj z)))
  (hinternal : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    ∀ z, z ∈ sourceCandidate F rootCandidate interiorCandidate i a →
      interiorLoad F group (group i) + 1 ≤
        #((interiorCandidate i b).filter (G.Adj z)))

/-- Matching-layer images already occupied in the matching group of `i`. -/
def usedInterior (group : Fin s → Fin k) (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) : Finset B :=
  ((Finset.Iio i).filter fun j ↦ group j = group i).attach.biUnion fun j ↦
    let R := prior j.1 (Fin.mk_lt_mk.mp
      (Finset.mem_Iio.mp (Finset.mem_filter.mp j.2).1))
    (Finset.univ.erase (F.segments.root j.1)).image R.copy

/-- Cluster-layer roots already occupied in the root group of `i`. -/
def usedRoots (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) : Finset B :=
  ((Finset.Iio i).filter fun j ↦ rootGroup j = rootGroup i).attach.image fun j ↦
    (prior j.1 (Fin.mk_lt_mk.mp
      (Finset.mem_Iio.mp (Finset.mem_filter.mp j.2).1))).rootImage

theorem card_usedRoots_lt_load (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) :
    #(usedRoots F G rootGroup rootCandidate interiorCandidate i prior) <
      rootLoad rootGroup (rootGroup i) := by
  classical
  let earlierSame := (Finset.Iio i).filter fun j ↦ rootGroup j = rootGroup i
  have hcardImage :
      #(usedRoots F G rootGroup rootCandidate interiorCandidate i prior) ≤
        #earlierSame := by
    calc
      #(usedRoots F G rootGroup rootCandidate interiorCandidate i prior) ≤
          #earlierSame.attach := Finset.card_image_le
      _ = #earlierSame := Finset.card_attach
  have hproper : earlierSame ⊂
      (Finset.univ.filter fun j : Fin s ↦ rootGroup j = rootGroup i) := by
    constructor
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    · intro hsub
      have hiEarlier : i ∈ Finset.Iio i :=
        (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, rfl⟩))).1
      simpa using hiEarlier
  exact hcardImage.trans_lt (by
    simpa [earlierSame, rootLoad] using Finset.card_lt_card hproper)

theorem card_usedInterior_add_current_le_load (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) :
    #(usedInterior (F := F) (G := G) (rootCandidate := rootCandidate)
      (interiorCandidate := interiorCandidate) group i prior) +
        (F.segments.size i - 1) ≤ interiorLoad F group (group i) := by
  classical
  let earlier := (Finset.Iio i).filter fun j ↦ group j = group i
  have hused : #(usedInterior (F := F) (G := G)
      (rootCandidate := rootCandidate) (interiorCandidate := interiorCandidate)
      group i prior) ≤ ∑ j ∈ earlier, (F.segments.size j - 1) := by
    calc
      #(usedInterior (F := F) (G := G) (rootCandidate := rootCandidate)
          (interiorCandidate := interiorCandidate) group i prior) ≤
          ∑ j ∈ earlier.attach,
            #((Finset.univ.erase (F.segments.root j.1)).image
              (prior j.1 (Fin.mk_lt_mk.mp
                (Finset.mem_Iio.mp (Finset.mem_filter.mp j.2).1))).copy) :=
        Finset.card_biUnion_le
      _ ≤ ∑ j ∈ earlier.attach, (F.segments.size j.1 - 1) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          #((Finset.univ.erase (F.segments.root j.1)).image
              (prior j.1 (Fin.mk_lt_mk.mp
                (Finset.mem_Iio.mp (Finset.mem_filter.mp j.2).1))).copy) ≤
              #(Finset.univ.erase (F.segments.root j.1)) := Finset.card_image_le
          _ = F.segments.size j.1 - 1 := by simp
      _ = ∑ j ∈ earlier, (F.segments.size j - 1) :=
        Finset.sum_attach earlier (fun j ↦ F.segments.size j - 1)
  have hsub : earlier ⊆
      (Finset.univ.filter fun j ↦ group j = group i).erase i := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact Finset.mem_erase.mpr ⟨by
      intro hji
      subst j
      simpa using hj'.1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.2⟩⟩
  have hsum :
      (∑ j ∈ earlier, (F.segments.size j - 1)) +
          (F.segments.size i - 1) ≤
        ∑ j, if group j = group i then F.segments.size j - 1 else 0 := by
    let same := Finset.univ.filter fun j ↦ group j = group i
    calc
      (∑ j ∈ earlier, (F.segments.size j - 1)) +
            (F.segments.size i - 1) ≤
          (∑ j ∈ same.erase i, (F.segments.size j - 1)) +
            (F.segments.size i - 1) :=
        Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsub) _
      _ = ∑ j ∈ same, (F.segments.size j - 1) :=
        Finset.sum_erase_add same (fun j ↦ F.segments.size j - 1) (by simp [same])
      _ = ∑ j, if group j = group i then F.segments.size j - 1 else 0 := by
        change (∑ j ∈ (Finset.univ.filter fun j ↦ group j = group i),
            (F.segments.size j - 1)) =
          ∑ j ∈ Finset.univ,
            if group j = group i then F.segments.size j - 1 else 0
        exact Finset.sum_filter (fun j ↦ group j = group i)
          (fun j ↦ F.segments.size j - 1)
  exact (Nat.add_le_add_right hused _).trans (by
    simpa [interiorLoad] using hsum)

/-- One online step and the invariants needed for global assembly. -/
structure OnlineStep (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) where
  data : SegmentRealization F G rootCandidate interiorCandidate i
  fresh : ∀ j (hj : j.val < i.val) a b,
    data.copy a ≠ (prior j hj).copy b
  parent_adj_original : ∀ q, F.parent i = Sum.inl q →
    G.Adj (originalImage q) data.rootImage
  parent_adj_segment : ∀ j a (hp : F.parent i = Sum.inr ⟨j, a⟩),
    G.Adj ((prior j (F.parent_earlier i j a hp)).copy a) data.rootImage

/-- One topological online step. Every image and parent edge is constructed. -/
noncomputable def onlineStep (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) :
    OnlineStep F G originalImage rootCandidate interiorCandidate i prior := by
  classical
  let parentWitness : ∃ z : B,
      rootLoad rootGroup (rootGroup i) + 1 ≤
          #((rootCandidate i).filter (G.Adj z)) ∧
        ((∃ q, F.parent i = Sum.inl q ∧ z = originalImage q) ∨
          ∃ w : Σ j : Fin s, {a : Fin (F.segments.size j) // j.val < i.val},
            F.parent i = Sum.inr ⟨w.1, w.2.1⟩ ∧
              z = (prior w.1 w.2.2).copy w.2.1) := by
    cases hp : F.parent i with
    | inl q =>
        exact ⟨originalImage q, hattachOriginal i q hp,
          Or.inl ⟨q, rfl, rfl⟩⟩
    | inr z =>
        rcases z with ⟨j, a⟩
        let R := prior j (F.parent_earlier i j a hp)
        have hmem : R.copy a ∈
            sourceCandidate F rootCandidate interiorCandidate j a := by
          by_cases ha : a = F.segments.root j
          · simpa [sourceCandidate, ha, R.map_root] using R.root_mem
          · simpa [sourceCandidate, ha] using R.map_nonroot a ha
        exact ⟨R.copy a, hattachSegment i j a hp (R.copy a) hmem,
          Or.inr ⟨⟨j, ⟨a, F.parent_earlier i j a hp⟩⟩, rfl, rfl⟩⟩
  let parentImage : B := Classical.choose parentWitness
  have hparentDegree : rootLoad rootGroup (rootGroup i) + 1 ≤
      #((rootCandidate i).filter (G.Adj parentImage)) :=
    (Classical.choose_spec parentWitness).1
  have hparentSource := (Classical.choose_spec parentWitness).2
  let neighborRoot := (rootCandidate i).filter (G.Adj parentImage)
  let rootUsed := usedRoots F G rootGroup rootCandidate interiorCandidate i prior
  let rootChoices := neighborRoot \ rootUsed
  have hrootUnused : #rootUsed < rootLoad rootGroup (rootGroup i) :=
    card_usedRoots_lt_load F G rootGroup rootCandidate interiorCandidate i prior
  have hchoiceCard : 0 < #rootChoices := by
    have hcard := Finset.card_sdiff_add_card_inter neighborRoot rootUsed
    have hinter : #(neighborRoot ∩ rootUsed) ≤ #rootUsed :=
      Finset.card_le_card Finset.inter_subset_right
    have hdeg : rootLoad rootGroup (rootGroup i) + 1 ≤ #neighborRoot := by
      simpa [neighborRoot] using hparentDegree
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
  let used := usedInterior (F := F) (G := G) (rootCandidate := rootCandidate)
    (interiorCandidate := interiorCandidate) group i prior
  let candidateNow : Fin (F.segments.size i) → Finset B := fun a ↦
    if a = F.segments.root i then ∅ else interiorCandidate i a \ used
  have hcurrent : F.segments.size i + #used ≤
      interiorLoad F group (group i) + 1 := by
    have hu := card_usedInterior_add_current_le_load F G group
      rootCandidate interiorCandidate i prior
    have hu' : #used + (F.segments.size i - 1) ≤
        interiorLoad F group (group i) := by simpa [used] using hu
    have hpos : 0 < F.segments.size i :=
      lt_of_le_of_lt (Nat.zero_le _) (F.segments.root i).isLt
    omega
  have hrootCross : ∀ a,
      (F.segments.tree i).Adj (F.segments.root i) a →
      F.segments.size i ≤ #(candidateNow a |>.filter (G.Adj z)) := by
    intro a hadj
    have ha : a ≠ F.segments.root i := hadj.ne'
    have hdeg := hinternal i (F.segments.root i) a hadj ha z (by
      simpa [sourceCandidate] using hzRoot)
    simpa [candidateNow, ha] using
      card_neighbors_cleaned_ge G (interiorCandidate i a) used z
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
      card_neighbors_cleaned_ge G (interiorCandidate i b) used v
        (F.segments.size i) (hcurrent.trans hdeg)
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
  have hrootUsedMem (j : Fin s) (hj : j.val < i.val)
      (hgroup : rootGroup j = rootGroup i) :
      (prior j hj).rootImage ∈ rootUsed := by
    apply Finset.mem_image.mpr
    let jm : {j // j ∈ (Finset.Iio i).filter fun j ↦
        rootGroup j = rootGroup i} := ⟨j, Finset.mem_filter.mpr ⟨by
          simpa using hj, hgroup⟩⟩
    exact ⟨jm, Finset.mem_attach _ _, rfl⟩
  have hinteriorUsedMem (j : Fin s) (hj : j.val < i.val)
      (hgroup : group j = group i) (b : Fin (F.segments.size j))
      (hb : b ≠ F.segments.root j) : (prior j hj).copy b ∈ used := by
    apply Finset.mem_biUnion.mpr
    let jm : {j // j ∈ (Finset.Iio i).filter fun j ↦
        group j = group i} := ⟨j, Finset.mem_filter.mpr ⟨by
          simpa using hj, hgroup⟩⟩
    refine ⟨jm, Finset.mem_attach _ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨b, ?_, rfl⟩
    change b ∈ Finset.univ.erase (F.segments.root j)
    exact Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩
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
        have heq' : z = (prior j hj).rootImage := by
          calc
            z = copy (F.segments.root i) := hcopyRoot.symm
            _ = (prior j hj).copy (F.segments.root j) := heq
            _ = (prior j hj).rootImage := (prior j hj).map_root
        by_cases hg : rootGroup j = rootGroup i
        · apply hzUnused
          rw [heq']
          exact hrootUsedMem j hj hg
        · apply (Finset.disjoint_left.mp
              (hrootDisjoint i j (Ne.symm hg))) hzRoot
          rw [heq']
          exact (prior j hj).root_mem
      · have hprior := (prior j hj).map_nonroot b hb
        have heq' : z = (prior j hj).copy b := hcopyRoot.symm.trans heq
        apply (Finset.disjoint_left.mp
            (hrootInteriorDisjoint i j b)) hzRoot
        rw [heq']
        exact hprior
    · have hcur : copy a ∈ interiorCandidate i a :=
          (Finset.mem_sdiff.mp (by
            simpa [candidateNow, ha] using hcopyMem a ha)).1
      by_cases hb : b = F.segments.root j
      · subst b
        apply (Finset.disjoint_left.mp
            (hrootInteriorDisjoint j i a)) (prior j hj).root_mem
        rw [← (prior j hj).map_root, ← heq]
        exact hcur
      · have hprior := (prior j hj).map_nonroot b hb
        by_cases hg : group j = group i
        · have hnot : copy a ∉ used :=
            (Finset.mem_sdiff.mp (by
              simpa [candidateNow, ha] using hcopyMem a ha)).2
          apply hnot
          rw [heq]
          exact hinteriorUsedMem j hj hg b hb
        · apply (Finset.disjoint_left.mp
              (hinteriorDisjoint i a j b (Ne.symm hg))) hcur
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

/-- The well-founded online run through every hierarchical segment. -/
noncomputable def onlineSegment (i : Fin s) :
    SegmentRealization F G rootCandidate interiorCandidate i :=
  (onlineStep F G originalImage rootGroup group rootCandidate interiorCandidate
    hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint hattachOriginal
    hattachSegment hinternal i (fun j _hj ↦ onlineSegment j)).data
termination_by i.val

theorem onlineSegment_fresh (i j : Fin s) (hj : j.val < i.val)
    (a : Fin (F.segments.size i)) (b : Fin (F.segments.size j)) :
    (onlineSegment F G originalImage rootGroup group rootCandidate
      interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
      hattachOriginal hattachSegment hinternal i).copy a ≠
    (onlineSegment F G originalImage rootGroup group rootCandidate
      interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
      hattachOriginal hattachSegment hinternal j).copy b := by
  rw [onlineSegment.eq_def]
  exact (onlineStep F G originalImage rootGroup group rootCandidate
    interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
    hattachOriginal hattachSegment hinternal i
      (fun j _hj ↦ onlineSegment F G originalImage rootGroup group
        rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
        hrootInteriorDisjoint hattachOriginal hattachSegment hinternal j)).fresh
      j hj a b

theorem onlineSegment_parent_adj_original (i : Fin s) (q : Fin r)
    (hp : F.parent i = Sum.inl q) :
    G.Adj (originalImage q)
      (onlineSegment F G originalImage rootGroup group rootCandidate
        interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
        hattachOriginal hattachSegment hinternal i).rootImage := by
  rw [onlineSegment.eq_def]
  exact (onlineStep F G originalImage rootGroup group rootCandidate
    interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
    hattachOriginal hattachSegment hinternal i
      (fun j _hj ↦ onlineSegment F G originalImage rootGroup group
        rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
        hrootInteriorDisjoint hattachOriginal hattachSegment hinternal j)).parent_adj_original
      q hp

theorem onlineSegment_parent_adj_segment (i j : Fin s)
    (a : Fin (F.segments.size j)) (hp : F.parent i = Sum.inr ⟨j, a⟩) :
    G.Adj
      ((onlineSegment F G originalImage rootGroup group rootCandidate
        interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
        hattachOriginal hattachSegment hinternal j).copy a)
      (onlineSegment F G originalImage rootGroup group rootCandidate
        interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
        hattachOriginal hattachSegment hinternal i).rootImage := by
  conv_rhs => rw [onlineSegment.eq_def]
  exact (onlineStep F G originalImage rootGroup group rootCandidate
    interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
    hattachOriginal hattachSegment hinternal i
      (fun j _hj ↦ onlineSegment F G originalImage rootGroup group
        rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
        hrootInteriorDisjoint hattachOriginal hattachSegment hinternal j)).parent_adj_segment
      j a hp

/-- Copy-valued result of the hierarchical realization. `fullCopy` contains
all internal edges and every restored hierarchical parent edge. -/
structure HierarchicalCandidateEmbedding where
  segmentEmbedding : F.segments.Embedding G
  rootImage : Fin s → B
  map_root : ∀ i, segmentEmbedding.copy i (F.segments.root i) = rootImage i
  map_nonroot : ∀ i a, a ≠ F.segments.root i →
    segmentEmbedding.copy i a ∈ interiorCandidate i a
  root_mem : ∀ i, rootImage i ∈ rootCandidate i
  parent_adj : ∀ i,
    G.Adj
      (F.assembledMap originalImage
        (fun j a ↦ segmentEmbedding.copy j a) (F.parent i))
      (segmentEmbedding.copy i (F.segments.root i))
  fullCopy : F.graph.Copy G
  fullCopy_root : ∀ q, fullCopy (Sum.inl q) = originalImage q
  fullCopy_segment : ∀ i a,
    fullCopy (Sum.inr ⟨i, a⟩) = segmentEmbedding.copy i a

include rootGroup group horiginalInj horiginalOutsideRoot
  horiginalOutsideInterior hrootDisjoint hinteriorDisjoint
  hrootInteriorDisjoint hattachOriginal hattachSegment hinternal in
theorem exists_hierarchicalCandidateEmbedding :
    Nonempty (HierarchicalCandidateEmbedding F G originalImage
      rootCandidate interiorCandidate) := by
  classical
  let D : ∀ i, SegmentRealization F G rootCandidate interiorCandidate i :=
    fun i ↦ onlineSegment F G originalImage rootGroup group rootCandidate
      interiorCandidate hrootDisjoint hinteriorDisjoint hrootInteriorDisjoint
      hattachOriginal hattachSegment hinternal i
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
              ((onlineSegment_fresh F G originalImage rootGroup group
                rootCandidate interiorCandidate hrootDisjoint
                hinteriorDisjoint hrootInteriorDisjoint hattachOriginal
                hattachSegment hinternal j i hji b a) hab.symm)
          · exact False.elim
              ((onlineSegment_fresh F G originalImage rootGroup group
                rootCandidate interiorCandidate hrootDisjoint
                hinteriorDisjoint hrootInteriorDisjoint hattachOriginal
                hattachSegment hinternal i j hij' a b) hab) }
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
        (F.assembledMap originalImage (fun j a ↦ E.copy j a) (F.parent i))
        (E.copy i (F.segments.root i)) := by
    intro i
    cases hp : F.parent i with
    | inl q =>
        change G.Adj (originalImage q) ((D i).copy (F.segments.root i))
        rw [(D i).map_root]
        exact onlineSegment_parent_adj_original F G originalImage rootGroup group
          rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
          hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i q hp
    | inr z =>
        rcases z with ⟨j, a⟩
        change G.Adj ((D j).copy a) ((D i).copy (F.segments.root i))
        rw [(D i).map_root]
        exact onlineSegment_parent_adj_segment F G originalImage rootGroup group
          rootCandidate interiorCandidate hrootDisjoint hinteriorDisjoint
          hrootInteriorDisjoint hattachOriginal hattachSegment hinternal i j a hp
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

end Erdos547b.ZhaoLemma59HierarchicalOnline

#print axioms Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.exists_hierarchicalCandidateEmbedding
