/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59
import ErdosProblems.Erdos547b.ForestCapacity
import ErdosProblems.Erdos547b.Proposition57

open scoped SimpleGraph

noncomputable section

namespace Erdos547b

open Finset Fintype SimpleGraph

namespace RegularPair.OrderedRootedForest

variable {m : ℕ}

/-!
The theorem below is the prescribed-root, vertex-dependent version of the
greedy core in `ZhaoLemma59`.  Components are embedded in their given order.
After the head component has been embedded, its complete image is deleted
from every candidate set for the tail.  Thus the induction produces one
global injection; no disjointness assumption on the original candidate sets
is needed.
-/

/-- Embed an ordered rooted forest with prescribed roots and a separate
candidate set for every source vertex.  The total forest order in the two
degree hypotheses is exactly the reserve which pays for deleting all images
of earlier components. -/
theorem exists_embedding_in_vertex_candidates
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin m → B)
    (candidate : (Σ i, Fin (F.size i)) → Finset B)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i k a, a ≠ F.root k →
      rootImage i ∉ candidate ⟨k, a⟩)
    (hrootDegree : ∀ i ⦃a⦄, (F.tree i).Adj (F.root i) a →
      F.order ≤ #{w ∈ candidate ⟨i, a⟩ | G.Adj (rootImage i) w})
    (hcross : ∀ i ⦃a b⦄, (F.tree i).Adj a b → b ≠ F.root i →
      ∀ v ∈ candidate ⟨i, a⟩,
        F.order ≤ #{w ∈ candidate ⟨i, b⟩ | G.Adj v w}) :
    ∃ E : F.Embedding G,
      (∀ i, E.copy i (F.root i) = rootImage i) ∧
      ∀ i a, a ≠ F.root i → E.copy i a ∈ candidate ⟨i, a⟩ := by
  classical
  induction m with
  | zero =>
      let copies : ∀ i : Fin 0, (F.tree i).Copy G := fun i ↦ Fin.elim0 i
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
        rintro ⟨i, a⟩
        exact Fin.elim0 i
      let E : F.Embedding G := ⟨copies, hinjective⟩
      refine ⟨E, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      let Ftail : OrderedRootedForest m := F.tail
      let rootImageTail : Fin m → B := fun i ↦ rootImage i.succ
      have hhead_le : F.size 0 ≤ F.order := by
        rw [← F.order_tail_add_head]
        omega
      obtain ⟨fhead, hfheadRoot, hfheadMem⟩ :=
        ZhaoLemma59.exists_rooted_candidate_copy
          (F.tree 0) G (F.isTree 0) (F.root 0)
          (fun a ↦ candidate ⟨0, a⟩) (rootImage 0) (by
            intro a ha
            simpa using hhead_le.trans (hrootDegree 0 ha)) (by
            intro a b hab hb v hv
            simpa using hhead_le.trans (hcross 0 hab hb v hv))
      let used : Finset B := Finset.univ.image fhead
      have husedCard : #used = F.size 0 := by
        rw [show #used = Fintype.card (Fin (F.size 0)) by
          exact card_image_iff.mpr fun _ _ _ _ h ↦ fhead.injective h]
        simp
      have htail_add_used : Ftail.order + #used = F.order := by
        rw [husedCard]
        simpa [Ftail, add_comm] using F.order_tail_add_head
      let candidateTail : (Σ i, Fin (Ftail.size i)) → Finset B :=
        fun z ↦ candidate ⟨z.1.succ, z.2⟩ \ used
      have htailRootInjective : Function.Injective rootImageTail := by
        intro i k h
        exact Fin.succ_inj.mp (hrootInjective h)
      have htailRootOutside : ∀ i k a, a ≠ Ftail.root k →
          rootImageTail i ∉ candidateTail ⟨k, a⟩ := by
        intro i k a ha hmem
        exact hrootOutside i.succ k.succ a ha (mem_sdiff.mp hmem).1
      have htailRootDegree : ∀ i ⦃a⦄,
          (Ftail.tree i).Adj (Ftail.root i) a →
          Ftail.order ≤
            #{w ∈ candidateTail ⟨i, a⟩ | G.Adj (rootImageTail i) w} := by
        intro i a ha
        apply RegularPair.card_neighbors_cleaned_ge G
          (candidate ⟨i.succ, a⟩) used (rootImageTail i) Ftail.order
        rw [htail_add_used]
        exact hrootDegree i.succ ha
      have htailCross : ∀ i ⦃a b⦄,
          (Ftail.tree i).Adj a b → b ≠ Ftail.root i →
          ∀ v ∈ candidateTail ⟨i, a⟩,
            Ftail.order ≤
              #{w ∈ candidateTail ⟨i, b⟩ | G.Adj v w} := by
        intro i a b hab hb v hv
        apply RegularPair.card_neighbors_cleaned_ge G
          (candidate ⟨i.succ, b⟩) used v Ftail.order
        rw [htail_add_used]
        exact hcross i.succ hab hb v (mem_sdiff.mp hv).1
      obtain ⟨Etail, hEtailRoot, hEtailMem⟩ :=
        ih Ftail rootImageTail candidateTail htailRootInjective
          htailRootOutside htailRootDegree htailCross
      have hheadTailDisjoint : ∀ a i b, fhead a ≠ Etail.copy i b := by
        intro a i b hab
        by_cases hbroot : b = Ftail.root i
        · by_cases haroot : a = F.root 0
          · have htailRoot : Etail.copy i b = rootImage i.succ := by
              rw [hbroot]
              simpa [Ftail, rootImageTail] using hEtailRoot i
            have himage : rootImage 0 = rootImage i.succ := by
              rw [← hfheadRoot, ← haroot, ← htailRoot]
              exact hab
            have hindex : (0 : Fin (m + 1)) = i.succ := hrootInjective himage
            have hval := congrArg Fin.val hindex
            simp at hval
          · have hamem := hfheadMem a haroot
            apply hrootOutside i.succ 0 a haroot
            have htailRoot : Etail.copy i b = rootImage i.succ := by
              rw [hbroot]
              simpa [Ftail, rootImageTail] using hEtailRoot i
            rw [← htailRoot, ← hab]
            exact hamem
        · have hbmem := hEtailMem i b hbroot
          have hbunused : Etail.copy i b ∉ used := (mem_sdiff.mp hbmem).2
          apply hbunused
          exact mem_image.mpr ⟨a, mem_univ a, hab⟩
      let copies : ∀ i, (F.tree i).Copy G :=
        Fin.cases fhead (fun i ↦ Etail.copy i)
      have hinjective : Function.Injective
          (fun z : Σ i, Fin (F.size i) ↦ copies z.1 z.2) := by
        rintro ⟨i, a⟩ ⟨k, b⟩ hab
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · change fhead a = fhead b at hab
            have : a = b := fhead.injective hab
            subst b
            rfl
          · change fhead a = Etail.copy k b at hab
            exact False.elim (hheadTailDisjoint a k b hab)
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
          · change Etail.copy i a = fhead b at hab
            exact False.elim (hheadTailDisjoint b i a hab.symm)
          · have htail :
                (⟨i, a⟩ : Σ i, Fin (Ftail.size i)) = ⟨k, b⟩ := by
              apply Etail.injective
              change Etail.copy i a = Etail.copy k b at hab
              exact hab
            cases htail
            rfl
      let E : F.Embedding G := ⟨copies, hinjective⟩
      refine ⟨E, ?_, ?_⟩
      · intro i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · change fhead (F.root 0) = rootImage 0
          exact hfheadRoot
        · change Etail.copy i (F.root i.succ) = rootImage i.succ
          have hi := hEtailRoot i
          change Etail.copy i (F.root i.succ) = rootImage i.succ at hi
          exact hi
      · intro i a ha
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · change fhead a ∈ candidate ⟨0, a⟩
          exact hfheadMem a ha
        · have ha' : a ≠ Ftail.root i := by
            change a ≠ F.root i.succ
            exact ha
          have hm := hEtailMem i a ha'
          exact (mem_sdiff.mp hm).1

end RegularPair.OrderedRootedForest

namespace ZhaoProp57

open RegularPair
open RegularPair.OrderedRootedForest

variable {m : ℕ}

/-- The literal root vertices of an ordered rooted forest. -/
def orderedRoots (F : OrderedRootedForest m) :
    Finset (Σ i, Fin (F.size i)) :=
  Finset.univ.image fun i ↦ ⟨i, F.root i⟩

/-- The union of all vertex-dependent candidate sets. -/
def vertexCandidateTarget {B : Type*} [DecidableEq B]
    (F : OrderedRootedForest m)
    (candidate : (Σ i, Fin (F.size i)) → Finset B) : Finset B :=
  Finset.univ.biUnion candidate

/-- Candidate-set construction of Zhao's online arrow for an ordered rooted
forest.  `bad` is the online exceptional set for each possible root.  Every
injective root assignment in `rootCluster` avoiding those sets is realized by
a genuine globally injective copy.  No embedding assertion is assumed: the
copy is built component-by-component by
`exists_embedding_in_vertex_candidates`.
-/
theorem flexibleEmbedding_of_vertex_candidates
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCluster : Finset B)
    (candidate : (Σ i, Fin (F.size i)) → Finset B)
    (bad : (Σ i, Fin (F.size i)) → Finset B) (slack : ℕ)
    (hbadSubset : ∀ x, bad x ⊆ rootCluster)
    (hbadCard : ∀ i, #(bad ⟨i, F.root i⟩) ≤ slack)
    (hrootOutside : ∀ z ∈ rootCluster, ∀ i a, a ≠ F.root i →
      z ∉ candidate ⟨i, a⟩)
    (hrootDegree : ∀ i z, z ∈ rootCluster →
      z ∉ bad ⟨i, F.root i⟩ →
      ∀ ⦃a⦄, (F.tree i).Adj (F.root i) a →
        F.order ≤ #{w ∈ candidate ⟨i, a⟩ | G.Adj z w})
    (hcross : ∀ i ⦃a b⦄, (F.tree i).Adj a b → b ≠ F.root i →
      ∀ v ∈ candidate ⟨i, a⟩,
        F.order ≤ #{w ∈ candidate ⟨i, b⟩ | G.Adj v w}) :
    Nonempty (FlexibleEmbedding F.graph G (orderedRoots F) rootCluster
      (vertexCandidateTarget F candidate) slack) := by
  classical
  refine ⟨
    { bad := bad
      bad_subset := hbadSubset
      card_bad := ?_
      realize := ?_ }⟩
  · intro r hr
    obtain ⟨i, -, hir⟩ := Finset.mem_image.mp hr
    subst r
    exact hbadCard i
  · intro rootMap hrootMapInj hrootMapMem hrootMapGood
    let rootImage : Fin m → B := fun i ↦ rootMap ⟨i, F.root i⟩
    have hriInj : Function.Injective rootImage := by
      intro i j hij
      have hsigma : (⟨i, F.root i⟩ : Σ i, Fin (F.size i)) =
          ⟨j, F.root j⟩ := by
        apply hrootMapInj
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · exact hij
      exact Sigma.mk.inj_iff.mp hsigma |>.1
    have hriMem (i : Fin m) : rootImage i ∈ rootCluster := by
      apply hrootMapMem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hriGood (i : Fin m) : rootImage i ∉ bad ⟨i, F.root i⟩ := by
      apply hrootMapGood
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨E, hEroot, hEmem⟩ :=
      F.exists_embedding_in_vertex_candidates G rootImage candidate hriInj (by
        intro i k a ha
        exact hrootOutside (rootImage i) (hriMem i) k a ha) (by
        intro i a ha
        exact hrootDegree i (rootImage i) (hriMem i) (hriGood i) ha) hcross
    refine ⟨
      { copy := E.toGraphCopy
        map_root := ?_
        map_nonroot := ?_ }⟩
    · intro r hr
      obtain ⟨i, -, hir⟩ := Finset.mem_image.mp hr
      subst r
      change E.copy i (F.root i) = rootMap ⟨i, F.root i⟩
      exact hEroot i
    · rintro ⟨i, a⟩ hnotroot
      have ha : a ≠ F.root i := by
        intro ha
        apply hnotroot
        subst a
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨i, a⟩, Finset.mem_univ _, hEmem i a ha⟩

/-- The canonical online bad set for one component root: these are precisely
the points of `rootCluster` which fail the required candidate degree for at
least one child of that root. -/
def rootDegreeBad
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCluster : Finset B)
    (candidate : (Σ i, Fin (F.size i)) → Finset B) (i : Fin m) : Finset B := by
  classical
  exact rootCluster.filter fun z ↦
    ∃ a, (F.tree i).Adj (F.root i) a ∧
      #{w ∈ candidate ⟨i, a⟩ | G.Adj z w} < F.order

/-- Fully canonical form of the prescribed-root online embedding theorem.
Only a cardinality estimate for the explicitly defined degree-failure set is
assumed.  Avoiding that set supplies the root-degree hypothesis needed by the
sequential construction. -/
theorem flexibleEmbedding_of_vertex_candidates_of_bad_card
    {B : Type*} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest m) (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCluster : Finset B)
    (candidate : (Σ i, Fin (F.size i)) → Finset B) (slack : ℕ)
    (hbadCard : ∀ i, #(rootDegreeBad F G rootCluster candidate i) ≤ slack)
    (hrootOutside : ∀ z ∈ rootCluster, ∀ i a, a ≠ F.root i →
      z ∉ candidate ⟨i, a⟩)
    (hcross : ∀ i ⦃a b⦄, (F.tree i).Adj a b → b ≠ F.root i →
      ∀ v ∈ candidate ⟨i, a⟩,
        F.order ≤ #{w ∈ candidate ⟨i, b⟩ | G.Adj v w}) :
    Nonempty (FlexibleEmbedding F.graph G (orderedRoots F) rootCluster
      (vertexCandidateTarget F candidate) slack) := by
  classical
  let bad : (Σ i, Fin (F.size i)) → Finset B :=
    fun x ↦ rootDegreeBad F G rootCluster candidate x.1
  apply flexibleEmbedding_of_vertex_candidates F G rootCluster candidate bad slack
  · intro x z hz
    exact (Finset.mem_filter.mp hz).1
  · intro i
    exact hbadCard i
  · exact hrootOutside
  · intro i z hz hzgood a ha
    apply Nat.le_of_not_gt
    intro hlt
    apply hzgood
    exact Finset.mem_filter.mpr ⟨hz, ⟨a, ha, hlt⟩⟩
  · exact hcross

end ZhaoProp57

end Erdos547b

#print axioms Erdos547b.RegularPair.OrderedRootedForest.exists_embedding_in_vertex_candidates
#print axioms Erdos547b.ZhaoProp57.flexibleEmbedding_of_vertex_candidates
#print axioms Erdos547b.ZhaoProp57.flexibleEmbedding_of_vertex_candidates_of_bad_card
