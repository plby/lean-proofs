/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalCoordinatePools
import ErdosProblems.Erdos547b.Lemma51DynamicRegularPair

/-!
# Dynamic cut-aware hierarchical realization

This is the cut-aware analogue of Zhao's Lemma 5.8 online step.  Each
hierarchy segment is embedded by the dynamic one-tree regular-pair theorem
inside the literal residual endpoint sets.  Thus earlier images may occupy
almost an entire endpoint; no false `load ≤ pair-density * N` hypothesis is
introduced.  The topological recursion still restores every hierarchy
parent edge, including the original cross-component cut edges.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalCoordinateDynamicOnline

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma51DynamicRegularPair
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
  (rootPool : Fin s → Pool)
  (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
  (pairPool : Fin s → Fin 2 → Pool)
  (whole raw : Pool → Finset B)
  (rho density : ℝ)

/-- Candidate reservoirs associated to the literal coordinate pools. -/
def dynamicRootCandidate (i : Fin s) : Finset B := raw (rootPool i)

def dynamicInteriorCandidate (i : Fin s)
    (a : Fin (F.segments.size i)) : Finset B := raw (interiorPool i a)

/-- The physical pool occupied by one coordinate, treating the segment root
through its root slot. -/
def dynamicVertexPool (i : Fin s) (a : Fin (F.segments.size i)) : Pool :=
  if a = F.segments.root i then rootPool i else interiorPool i a

/-- Images in one physical pool which were created before segment `i`. -/
def dynamicUsedPool (i : Fin s) (p : Pool)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (dynamicRootCandidate rootPool raw)
        (dynamicInteriorCandidate F interiorPool raw) j) : Finset B :=
  coordinateUsedPool F G rootPool interiorPool
    (dynamicRootCandidate rootPool raw)
    (dynamicInteriorCandidate F interiorPool raw) i p prior

/-- Literal live endpoint of the current regular pair. -/
def dynamicAvailable (i : Fin s) (c : Fin 2)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (dynamicRootCandidate rootPool raw)
        (dynamicInteriorCandidate F interiorPool raw) j) : Finset B :=
  raw (pairPool i c) \ dynamicUsedPool F G rootPool interiorPool raw i
    (pairPool i c) prior

/-- Image of the already embedded hierarchy parent. -/
def dynamicParentImage (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (dynamicRootCandidate rootPool raw)
        (dynamicInteriorCandidate F interiorPool raw) j) : B :=
  match hp : F.parent i with
  | Sum.inl q => originalImage q
  | Sum.inr z =>
      (prior z.1 (F.parent_earlier i z.1 z.2 hp)).copy z.2

variable
  (hpairRoot : ∀ i, rootPool i = pairPool i 0)
  (hpairInterior : ∀ i a,
    interiorPool i a = pairPool i
      ((F.segments.isTree i).coloringTwoOfVert (F.segments.root i) a))
  (hrawSubset : ∀ p, raw p ⊆ whole p)
  (hrawDisjoint : ∀ p q, p ≠ q → Disjoint (raw p) (raw q))
  (horiginalInj : Function.Injective originalImage)
  (horiginalOutsideRoot : ∀ q i,
    originalImage q ∉ dynamicRootCandidate rootPool raw i)
  (horiginalOutsideInterior : ∀ q i a,
    originalImage q ∉ dynamicInteriorCandidate F interiorPool raw i a)
  (huniform : ∀ i,
    G.IsUniform rho (whole (pairPool i 0)) (whole (pairPool i 1)))
  (hwholeDisjoint : ∀ i,
    Disjoint (whole (pairPool i 0)) (whole (pairPool i 1)))
  (hdensity : ∀ i,
    density ≤ G.edgeDensity (whole (pairPool i 0)) (whole (pairPool i 1)))
  (havailableLarge : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (dynamicRootCandidate rootPool raw)
          (dynamicInteriorCandidate F interiorPool raw) j) c,
    rho * (#(whole (pairPool i c)) : ℝ) ≤
      (#(dynamicAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ))
  (hparent : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (dynamicRootCandidate rootPool raw)
          (dynamicInteriorCandidate F interiorPool raw) j),
    1 + rho * (#(whole (pairPool i 0)) : ℝ) ≤
      (#((dynamicAvailable F G rootPool interiorPool pairPool raw i 0 prior).filter
        (G.Adj (dynamicParentImage F G originalImage rootPool interiorPool raw i
          prior))) : ℝ))
  (hmargin : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (dynamicRootCandidate rootPool raw)
          (dynamicInteriorCandidate F interiorPool raw) j) c,
    (F.segments.size i : ℝ) + rho * (#(whole (pairPool i c)) : ℝ) + 1 ≤
      (density - rho) *
        (#(dynamicAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ))

/-- One topological step, realized by the dynamic regular-pair primitive. -/
noncomputable def dynamicCoordinateOnlineStep (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (dynamicRootCandidate rootPool raw)
        (dynamicInteriorCandidate F interiorPool raw) j) :
    OnlineStep F G originalImage (dynamicRootCandidate rootPool raw)
      (dynamicInteriorCandidate F interiorPool raw) i prior := by
  classical
  let wholeLocal : Fin 2 → Finset B := fun c ↦ whole (pairPool i c)
  let availableLocal : Fin 2 → Finset B := fun c ↦
    dynamicAvailable F G rootPool interiorPool pairPool raw i c prior
  have havailableSubset : ∀ c, availableLocal c ⊆ wholeLocal c := by
    intro c
    exact Finset.sdiff_subset.trans (hrawSubset (pairPool i c))
  let hex :=
    exists_dynamic_rooted_tree_copy_of_uniform
      (F.segments.tree i) (F.segments.isTree i) (F.segments.root i) G
      (dynamicParentImage F G originalImage rootPool interiorPool raw i prior)
      (Equiv.refl (Fin 2)) wholeLocal availableLocal rho density
      (huniform i) havailableSubset (havailableLarge i prior) (hdensity i)
      (hwholeDisjoint i) (by
        simpa [wholeLocal, availableLocal] using (hparent i prior)) (by
          intro c
          simpa [wholeLocal, availableLocal] using hmargin i prior c)
  let copy := Classical.choose hex
  have hcopySpec := Classical.choose_spec hex
  have hattach : G.Adj
      (dynamicParentImage F G originalImage rootPool interiorPool raw i prior)
      (copy (F.segments.root i)) := by
    simpa [copy] using hcopySpec.1
  have hcopyMem : ∀ a, copy a ∈ availableLocal
      ((Equiv.refl (Fin 2))
        ((F.segments.isTree i).coloringTwoOfVert (F.segments.root i) a)) := by
    simpa [copy] using hcopySpec.2
  have hcopyPool (a : Fin (F.segments.size i)) :
      copy a ∈ raw (dynamicVertexPool F rootPool interiorPool i a) := by
    have hm := hcopyMem a
    by_cases ha : a = F.segments.root i
    · subst a
      have hm' : copy (F.segments.root i) ∈ raw (pairPool i 0) \
          dynamicUsedPool F G rootPool interiorPool raw i (pairPool i 0) prior := by
        simpa [availableLocal, dynamicAvailable] using hm
      simpa [dynamicVertexPool, hpairRoot] using (Finset.mem_sdiff.mp hm').1
    · have hp := hpairInterior i a
      have hm' : copy a ∈ raw (pairPool i
          ((F.segments.isTree i).coloringTwoOfVert (F.segments.root i) a)) \
          dynamicUsedPool F G rootPool interiorPool raw i
            (pairPool i ((F.segments.isTree i).coloringTwoOfVert
              (F.segments.root i) a)) prior := by
        simpa [availableLocal, dynamicAvailable] using hm
      simpa [dynamicVertexPool, ha, hp] using (Finset.mem_sdiff.mp hm').1
  have hcopyUnused (a : Fin (F.segments.size i)) :
      copy a ∉ dynamicUsedPool F G rootPool interiorPool raw i
        (dynamicVertexPool F rootPool interiorPool i a) prior := by
    have hm := hcopyMem a
    by_cases ha : a = F.segments.root i
    · subst a
      have hm' : copy (F.segments.root i) ∈ raw (pairPool i 0) \
          dynamicUsedPool F G rootPool interiorPool raw i (pairPool i 0) prior := by
        simpa [availableLocal, dynamicAvailable] using hm
      simpa [dynamicVertexPool, hpairRoot] using (Finset.mem_sdiff.mp hm').2
    · have hp := hpairInterior i a
      have hm' : copy a ∈ raw (pairPool i
          ((F.segments.isTree i).coloringTwoOfVert (F.segments.root i) a)) \
          dynamicUsedPool F G rootPool interiorPool raw i
            (pairPool i ((F.segments.isTree i).coloringTwoOfVert
              (F.segments.root i) a)) prior := by
        simpa [availableLocal, dynamicAvailable] using hm
      simpa [dynamicVertexPool, ha, hp] using (Finset.mem_sdiff.mp hm').2
  let data : SegmentRealization F G (dynamicRootCandidate rootPool raw)
      (dynamicInteriorCandidate F interiorPool raw) i :=
    { rootImage := copy (F.segments.root i)
      root_mem := by
        simpa [dynamicRootCandidate, dynamicVertexPool] using
          hcopyPool (F.segments.root i)
      copy := copy
      map_root := rfl
      map_nonroot := by
        intro a ha
        simpa [dynamicInteriorCandidate, dynamicVertexPool, ha] using
          hcopyPool a }
  refine
    { data := data
      fresh := ?_
      parent_adj_original := ?_
      parent_adj_segment := ?_ }
  · intro j hj a b heq
    let R := prior j hj
    have hpriorPool : R.copy b ∈
        raw (dynamicVertexPool F rootPool interiorPool j b) := by
      by_cases hb : b = F.segments.root j
      · subst b
        simpa [dynamicVertexPool, dynamicRootCandidate, R.map_root] using
          R.root_mem
      · simpa [dynamicVertexPool, dynamicInteriorCandidate, hb] using
          R.map_nonroot b hb
    by_cases hp : dynamicVertexPool F rootPool interiorPool j b =
        dynamicVertexPool F rootPool interiorPool i a
    · apply hcopyUnused a
      rw [← hp, heq]
      by_cases hb : b = F.segments.root j
      · subst b
        simpa [dynamicUsedPool, (prior j hj).map_root] using
          root_mem_coordinateUsedPool F G rootPool interiorPool
          (dynamicRootCandidate rootPool raw)
          (dynamicInteriorCandidate F interiorPool raw) i j hj
          (dynamicVertexPool F rootPool interiorPool j (F.segments.root j))
          (by simp [dynamicVertexPool]) prior
      · exact coordinate_mem_coordinateUsedPool F G rootPool interiorPool
          (dynamicRootCandidate rootPool raw)
          (dynamicInteriorCandidate F interiorPool raw) i j hj b hb
          (dynamicVertexPool F rootPool interiorPool j b)
          (by simp [dynamicVertexPool, hb]) prior
    · exact (Finset.disjoint_left.mp
        (hrawDisjoint _ _ (Ne.symm hp)) (hcopyPool a) (heq ▸ hpriorPool)).elim
  · intro q hp
    change G.Adj (originalImage q) (copy (F.segments.root i))
    have hparentEq :
        dynamicParentImage F G originalImage rootPool interiorPool raw i prior =
          originalImage q := by
      unfold dynamicParentImage
      split
      next q' hq' =>
        have hqq' : q' = q := Sum.inl.inj (hq'.symm.trans hp)
        subst q'
        rfl
      next z hz =>
        have hfalse : False := by simpa using hz.symm.trans hp
        exact hfalse.elim
    have hedge := congrArg
      (fun z ↦ s(z, copy (F.segments.root i))) hparentEq
    exact (G.adj_congr_of_sym2 hedge).mp hattach
  · intro j a hp
    change G.Adj ((prior j (F.parent_earlier i j a hp)).copy a)
      (copy (F.segments.root i))
    have hparentEq :
        dynamicParentImage F G originalImage rootPool interiorPool raw i prior =
          (prior j (F.parent_earlier i j a hp)).copy a := by
      unfold dynamicParentImage
      split
      next q hq =>
        have hfalse : False := by simpa using hq.symm.trans hp
        exact hfalse.elim
      next z hz =>
        have hzz : z = ⟨j, a⟩ := Sum.inr.inj (hz.symm.trans hp)
        subst z
        rfl
    have hedge := congrArg
      (fun z ↦ s(z, copy (F.segments.root i))) hparentEq
    exact (G.adj_congr_of_sym2 hedge).mp hattach

noncomputable def dynamicCoordinateOnlineSegment (i : Fin s) :
    SegmentRealization F G (dynamicRootCandidate rootPool raw)
      (dynamicInteriorCandidate F interiorPool raw) i :=
  (dynamicCoordinateOnlineStep F G originalImage rootPool interiorPool pairPool
    whole raw rho density hpairRoot hpairInterior hrawSubset hrawDisjoint
    huniform hwholeDisjoint hdensity havailableLarge hparent hmargin i
    (fun j _ ↦ dynamicCoordinateOnlineSegment j)).data
termination_by i.val

theorem dynamicCoordinateOnlineSegment_fresh (i j : Fin s)
    (hj : j.val < i.val) (a : Fin (F.segments.size i))
    (b : Fin (F.segments.size j)) :
    (dynamicCoordinateOnlineSegment F G originalImage rootPool interiorPool
      pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
      hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
      hmargin i).copy a ≠
    (dynamicCoordinateOnlineSegment F G originalImage rootPool interiorPool
      pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
      hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
      hmargin j).copy b := by
  rw [dynamicCoordinateOnlineSegment.eq_def]
  exact (dynamicCoordinateOnlineStep F G originalImage rootPool interiorPool
    pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
    hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
    hmargin i (fun j _ ↦ dynamicCoordinateOnlineSegment F G originalImage
      rootPool interiorPool pairPool whole raw rho density hpairRoot
      hpairInterior hrawSubset hrawDisjoint huniform hwholeDisjoint hdensity
      havailableLarge hparent hmargin j)).fresh j hj a b

theorem dynamicCoordinateOnlineSegment_parent_adj_original (i : Fin s)
    (q : Fin r) (hp : F.parent i = Sum.inl q) :
    G.Adj (originalImage q)
      (dynamicCoordinateOnlineSegment F G originalImage rootPool interiorPool
        pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
        hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
        hmargin i).rootImage := by
  rw [dynamicCoordinateOnlineSegment.eq_def]
  exact (dynamicCoordinateOnlineStep F G originalImage rootPool interiorPool
    pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
    hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
    hmargin i (fun j _ ↦ dynamicCoordinateOnlineSegment F G originalImage
      rootPool interiorPool pairPool whole raw rho density hpairRoot
      hpairInterior hrawSubset hrawDisjoint huniform hwholeDisjoint hdensity
      havailableLarge hparent hmargin j)).parent_adj_original q hp

theorem dynamicCoordinateOnlineSegment_parent_adj_segment (i j : Fin s)
    (a : Fin (F.segments.size j)) (hp : F.parent i = Sum.inr ⟨j, a⟩) :
    G.Adj
      ((dynamicCoordinateOnlineSegment F G originalImage rootPool interiorPool
        pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
        hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
        hmargin j).copy a)
      (dynamicCoordinateOnlineSegment F G originalImage rootPool interiorPool
        pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
        hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
        hmargin i).rootImage := by
  conv_rhs => rw [dynamicCoordinateOnlineSegment.eq_def]
  exact (dynamicCoordinateOnlineStep F G originalImage rootPool interiorPool
    pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
    hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
    hmargin i (fun j _ ↦ dynamicCoordinateOnlineSegment F G originalImage
      rootPool interiorPool pairPool whole raw rho density hpairRoot
      hpairInterior hrawSubset hrawDisjoint huniform hwholeDisjoint hdensity
      havailableLarge hparent hmargin j)).parent_adj_segment j a hp

include pairPool whole rho density hpairRoot hpairInterior hrawSubset
  hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent hmargin
  horiginalInj horiginalOutsideRoot horiginalOutsideInterior in
/-- Full hierarchy copy from dynamic per-segment regular-pair steps. -/
theorem exists_hierarchicalCandidateEmbedding_dynamicCoordinatePools :
    Nonempty (HierarchicalCandidateEmbedding F G originalImage
      (dynamicRootCandidate rootPool raw)
      (dynamicInteriorCandidate F interiorPool raw)) := by
  classical
  let D : ∀ i, SegmentRealization F G (dynamicRootCandidate rootPool raw)
      (dynamicInteriorCandidate F interiorPool raw) i := fun i ↦
    dynamicCoordinateOnlineSegment F G originalImage rootPool interiorPool
      pairPool whole raw rho density hpairRoot hpairInterior hrawSubset
      hrawDisjoint huniform hwholeDisjoint hdensity havailableLarge hparent
      hmargin i
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
              ((dynamicCoordinateOnlineSegment_fresh F G originalImage
                rootPool interiorPool pairPool whole raw rho density hpairRoot
                hpairInterior hrawSubset hrawDisjoint huniform hwholeDisjoint
                hdensity havailableLarge hparent hmargin j i hji b a) hab.symm)
          · exact False.elim
              ((dynamicCoordinateOnlineSegment_fresh F G originalImage
                rootPool interiorPool pairPool whole raw rho density hpairRoot
                hpairInterior hrawSubset hrawDisjoint huniform hwholeDisjoint
                hdensity havailableLarge hparent hmargin i j hij' a b) hab) }
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
        exact dynamicCoordinateOnlineSegment_parent_adj_original F G
          originalImage rootPool interiorPool pairPool whole raw rho density
          hpairRoot hpairInterior hrawSubset hrawDisjoint huniform
          hwholeDisjoint hdensity havailableLarge hparent hmargin i q hp
    | inr z =>
        rcases z with ⟨j, a⟩
        change G.Adj ((D j).copy a) ((D i).copy (F.segments.root i))
        rw [(D i).map_root]
        exact dynamicCoordinateOnlineSegment_parent_adj_segment F G
          originalImage rootPool interiorPool pairPool whole raw rho density
          hpairRoot hpairInterior hrawSubset hrawDisjoint huniform
          hwholeDisjoint hdensity havailableLarge hparent hmargin i j a hp
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
    fullCopy_segment := fun _ _ ↦ rfl
  }⟩

end Construction

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalCoordinateDynamicOnline

#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinateDynamicOnline.HierarchicalSegmentForest.exists_hierarchicalCandidateEmbedding_dynamicCoordinatePools
