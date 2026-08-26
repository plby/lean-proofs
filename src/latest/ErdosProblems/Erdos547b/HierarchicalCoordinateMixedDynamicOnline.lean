/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalOnlineFromStep
import ErdosProblems.Erdos547b.HierarchicalCoordinatePools
import ErdosProblems.Erdos547b.Lemma51DynamicRegularPair
import ErdosProblems.Erdos547b.Lemma59DynamicSelectedBranch

/-!
# Mixed dynamic coordinate hierarchy

This is the cut-aware online hierarchy constructor needed for Claim 6.16.
Selected segments have a root in an external cluster and descendants in a
matching pair, so they use the genuine two-pair Lemma 5.9 step. All other
segments have their root and descendants in one matching pair and use the
dynamic Lemma 5.8 step. The common `OnlineStep` interface then assembles one
injective copy and restores every hierarchy parent edge.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma51DynamicRegularPair
open Erdos547b.ZhaoLemma59DynamicSelectedBranch
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalOnlineFromStep
open Erdos547b.ZhaoLemma59HierarchicalOnlineFromStep.HierarchicalSegmentForest
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
  (rootOnly : Fin s → Prop) [DecidablePred rootOnly]
  (selected : Fin s → Prop) [DecidablePred selected]
  (rootPool : Fin s → Pool)
  (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
  (pairPool : Fin s → Fin 2 → Pool)
  (orient : Fin s → Equiv (Fin 2) (Fin 2))
  (whole raw : Pool → Finset B)
  (rho : ℝ) (rootDensity pairDensity : Fin s → ℝ)

/-- Literal candidates used by the assembled hierarchy. -/
def mixedRootCandidate (i : Fin s) : Finset B := raw (rootPool i)

def mixedInteriorCandidate (i : Fin s)
    (a : Fin (F.segments.size i)) : Finset B := raw (interiorPool i a)

/-- Earlier images occupying one literal coordinate pool. -/
def mixedUsedPool (i : Fin s) (p : Pool)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j) : Finset B :=
  coordinateUsedPool F G rootPool interiorPool
    (mixedRootCandidate rootPool raw)
    (mixedInteriorCandidate F interiorPool raw) i p prior

/-- Current residual of one matching endpoint. -/
def mixedAvailable (i : Fin s) (c : Fin 2)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j) : Finset B :=
  raw (pairPool i c) \ mixedUsedPool F G rootPool interiorPool raw i
    (pairPool i c) prior

/-- Image of the already embedded hierarchy parent. -/
def mixedParentImage (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j) : B :=
  match hp : F.parent i with
  | Sum.inl q => originalImage q
  | Sum.inr z =>
      (prior z.1 (F.parent_earlier i z.1 z.2 hp)).copy z.2

/-- Live selected-root reservoir, already restricted to neighbors of the
embedded hierarchy parent. -/
def mixedSelectedRootAvailable (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j) : Finset B :=
  (raw (rootPool i) \ mixedUsedPool F G rootPool interiorPool raw i
      (rootPool i) prior).filter
    (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw i prior))

variable
  (hrootPair : ∀ i, ¬ rootOnly i → ¬ selected i →
    rootPool i = pairPool i (orient i 0))
  (hinteriorPair : ∀ i a,
    interiorPool i a = pairPool i
      (orient i ((F.segments.isTree i).coloringTwoOfVert
        (F.segments.root i) a)))
  (hrawSubset : ∀ p, raw p ⊆ whole p)
  (relevant : Pool → Prop)
  (hrootRelevant : ∀ i, relevant (rootPool i))
  (hinteriorRelevant : ∀ i a, relevant (interiorPool i a))
  (hrawDisjoint : ∀ p q, relevant p → relevant q → p ≠ q →
    Disjoint (raw p) (raw q))
  (horiginalInj : Function.Injective originalImage)
  (horiginalOutsideRoot : ∀ q i,
    originalImage q ∉ mixedRootCandidate rootPool raw i)
  (horiginalOutsideInterior : ∀ q i a,
    originalImage q ∉ mixedInteriorCandidate F interiorPool raw i a)
  (huniformPair : ∀ i, ¬ rootOnly i →
    G.IsUniform rho (whole (pairPool i 0)) (whole (pairPool i 1)))
  (hwholeDisjoint : ∀ i, ¬ rootOnly i →
    Disjoint (whole (pairPool i 0)) (whole (pairPool i 1)))
  (hpairDensity : ∀ i, ¬ rootOnly i →
    pairDensity i ≤ G.edgeDensity
      (whole (pairPool i 0)) (whole (pairPool i 1)))
  (huniformSelectedRoot : ∀ i, ¬ rootOnly i → selected i →
    G.IsUniform rho (whole (rootPool i))
      (whole (pairPool i (orient i 1))))
  (hselectedRootDensity : ∀ i, ¬ rootOnly i → selected i →
    rootDensity i ≤ G.edgeDensity (whole (rootPool i))
      (whole (pairPool i (orient i 1))))
  (hrootOnlySize : ∀ i, rootOnly i → F.segments.size i = 1)
  (hrootOnlyNonempty : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j),
    rootOnly i →
    (mixedSelectedRootAvailable F G originalImage rootPool interiorPool raw i
      prior).Nonempty)
  (havailableLarge : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j) c,
    ¬ rootOnly i →
    rho * (#(whole (pairPool i c)) : ℝ) ≤
      (#(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ))
  (hselectedRootLarge : ∀ i
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → selected i →
    rho * (#(whole (rootPool i)) : ℝ) <
      (#(mixedSelectedRootAvailable F G originalImage rootPool interiorPool
        raw i prior) : ℝ))
  (hselectedRootMargin : ∀ i
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → selected i →
    (F.segments.size i : ℝ) +
        rho * (#(whole (pairPool i (orient i 1))) : ℝ) ≤
      (rootDensity i - rho) *
        (#(mixedAvailable F G rootPool interiorPool pairPool raw i
          (orient i 1) prior) : ℝ))
  (hparent : ∀ i
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j),
    ¬ rootOnly i → ¬ selected i →
    1 + rho * (#(whole (pairPool i (orient i 0))) : ℝ) ≤
      (#((mixedAvailable F G rootPool interiorPool pairPool raw i
        (orient i 0) prior).filter
          (G.Adj (mixedParentImage F G originalImage rootPool interiorPool raw
            i prior))) : ℝ))
  (hpairMargin : ∀ i
      (prior : ∀ j : Fin s, j.val < i.val →
        SegmentRealization F G (mixedRootCandidate rootPool raw)
          (mixedInteriorCandidate F interiorPool raw) j) c,
    ¬ rootOnly i →
    (F.segments.size i : ℝ) + rho * (#(whole (pairPool i c)) : ℝ) + 1 ≤
      (pairDensity i - rho) *
        (#(mixedAvailable F G rootPool interiorPool pairPool raw i c prior) : ℝ))

/-- One mixed selected/nonselected dynamic hierarchy step. -/
noncomputable def mixedDynamicOnlineStep (i : Fin s)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G (mixedRootCandidate rootPool raw)
        (mixedInteriorCandidate F interiorPool raw) j) :
    OnlineStep F G originalImage (mixedRootCandidate rootPool raw)
      (mixedInteriorCandidate F interiorPool raw) i prior := by
  classical
  let wholeLocal : Fin 2 → Finset B := fun c => whole (pairPool i c)
  let availableLocal : Fin 2 → Finset B := fun c =>
    mixedAvailable F G rootPool interiorPool pairPool raw i c prior
  have havailableSubset : ∀ c, availableLocal c ⊆ wholeLocal c := by
    intro c
    exact Finset.sdiff_subset.trans (hrawSubset (pairPool i c))
  have hex : ∃ copy : (F.segments.tree i).Copy G,
      G.Adj
        (mixedParentImage F G originalImage rootPool interiorPool raw i prior)
        (copy (F.segments.root i)) ∧
      copy (F.segments.root i) ∈
        raw (rootPool i) \
          mixedUsedPool F G rootPool interiorPool raw i (rootPool i) prior ∧
      ∀ a, a ≠ F.segments.root i →
        copy a ∈ raw (interiorPool i a) \
          mixedUsedPool F G rootPool interiorPool raw i (interiorPool i a) prior := by
    by_cases hr : rootOnly i
    · let rootAvailable := mixedSelectedRootAvailable F G originalImage
        rootPool interiorPool raw i prior
      let w := Classical.choose (hrootOnlyNonempty i prior hr)
      have hw : w ∈ rootAvailable :=
        Classical.choose_spec (hrootOnlyNonempty i prior hr)
      have hsub : Subsingleton (Fin (F.segments.size i)) :=
        Fintype.card_le_one_iff_subsingleton.mp (by
          rw [Fintype.card_fin, hrootOnlySize i hr])
      let copy : (F.segments.tree i).Copy G :=
        ⟨⟨(fun _ => w), fun {a b} hab =>
          False.elim ((F.segments.tree i).ne_of_adj hab (hsub.elim a b))⟩,
          fun a b _ => hsub.elim a b⟩
      refine ⟨copy, ?_, ?_, ?_⟩
      · exact (Finset.mem_filter.mp hw).2
      · exact (Finset.mem_filter.mp hw).1
      · intro a ha
        exact False.elim (ha (hsub.elim a (F.segments.root i)))
    · by_cases hs : selected i
      · obtain ⟨copy, hattach, hroot, hnonroot⟩ :=
        exists_dynamic_selected_rooted_tree_copy
          (F.segments.tree i) (F.segments.isTree i) (F.segments.root i) G
          (mixedParentImage F G originalImage rootPool interiorPool raw i prior)
          (orient i) (whole (rootPool i))
          (mixedSelectedRootAvailable F G originalImage rootPool interiorPool
            raw i prior)
          wholeLocal availableLocal rho (rootDensity i) (pairDensity i)
          (by simpa [wholeLocal] using huniformSelectedRoot i hr hs)
          (by simpa [wholeLocal] using huniformPair i hr)
          (by
            intro x hx
            exact (hrawSubset (rootPool i))
              (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1)
          havailableSubset (by
            simpa using hselectedRootLarge i prior hr hs)
          (by
            intro c
            simpa [wholeLocal, availableLocal] using havailableLarge i prior c hr)
          (by simpa [wholeLocal] using hselectedRootDensity i hr hs)
          (by simpa [wholeLocal] using hpairDensity i hr)
          (by
            simpa [wholeLocal, availableLocal] using
              hselectedRootMargin i prior hr hs)
          (by
            intro c
            have hm := hpairMargin i prior c hr
            have hm' : (F.segments.size i : ℝ) +
                rho * (#(whole (pairPool i c)) : ℝ) ≤
              (pairDensity i - rho) *
                (#(mixedAvailable F G rootPool interiorPool pairPool raw i c
                  prior) : ℝ) := by linarith
            simpa [wholeLocal, availableLocal] using hm')
          (by
            intro w hw
            exact (Finset.mem_filter.mp hw).2)
        refine ⟨copy, hattach, ?_, ?_⟩
        · exact (Finset.mem_filter.mp hroot).1
        · intro a ha
          have hm := hnonroot a ha
          rw [hinteriorPair i a]
          simpa [availableLocal, mixedAvailable] using hm
      · obtain ⟨copy, hattach, hmem⟩ :=
        exists_dynamic_rooted_tree_copy_of_uniform
          (F.segments.tree i) (F.segments.isTree i) (F.segments.root i) G
          (mixedParentImage F G originalImage rootPool interiorPool raw i prior)
          (orient i) wholeLocal availableLocal rho (pairDensity i)
          (by simpa [wholeLocal] using huniformPair i hr)
          havailableSubset
          (by
            intro c
            simpa [wholeLocal, availableLocal] using havailableLarge i prior c hr)
          (by simpa [wholeLocal] using hpairDensity i hr)
          (by simpa [wholeLocal] using hwholeDisjoint i hr)
          (by simpa [wholeLocal, availableLocal] using hparent i prior hr hs)
          (by
            intro c
            simpa [wholeLocal, availableLocal] using hpairMargin i prior c hr)
        refine ⟨copy, hattach, ?_, ?_⟩
        · have hm := hmem (F.segments.root i)
          rw [hrootPair i hr hs]
          simpa [availableLocal, mixedAvailable] using hm
        · intro a ha
          have hm := hmem a
          rw [hinteriorPair i a]
          simpa [availableLocal, mixedAvailable] using hm
  let copy := Classical.choose hex
  have hcopySpec := Classical.choose_spec hex
  have hattach := hcopySpec.1
  have hrootMem := hcopySpec.2.1
  have hnonrootMem := hcopySpec.2.2
  let data : SegmentRealization F G (mixedRootCandidate rootPool raw)
      (mixedInteriorCandidate F interiorPool raw) i :=
    { rootImage := copy (F.segments.root i)
      root_mem := by
        exact (Finset.mem_sdiff.mp hrootMem).1
      copy := copy
      map_root := rfl
      map_nonroot := by
        intro a ha
        exact (Finset.mem_sdiff.mp (hnonrootMem a ha)).1 }
  refine
    { data := data
      fresh := ?_
      parent_adj_original := ?_
      parent_adj_segment := ?_ }
  · intro j hj a b heq
    let R := prior j hj
    have hpriorPool : R.copy b ∈
        raw (if b = F.segments.root j then rootPool j else interiorPool j b) := by
      by_cases hb : b = F.segments.root j
      · subst b
        simp only [if_pos rfl]
        rw [R.map_root]
        exact R.root_mem
      · simp only [if_neg hb]
        exact R.map_nonroot b hb
    by_cases ha : a = F.segments.root i
    · subst a
      have hcurUnused := (Finset.mem_sdiff.mp hrootMem).2
      let curPool := rootPool i
      let priorPool := if b = F.segments.root j then rootPool j else interiorPool j b
      have hcurRelevant : relevant curPool := hrootRelevant i
      have hpriorRelevant : relevant priorPool := by
        by_cases hb : b = F.segments.root j
        · simp only [priorPool, hb, if_true]
          exact hrootRelevant j
        · simp only [priorPool, hb, if_false]
          exact hinteriorRelevant j b
      by_cases hp : priorPool = curPool
      · have hp' : priorPool = rootPool i := by simpa [curPool] using hp
        have hpriorUsed : R.copy b ∈
            mixedUsedPool F G rootPool interiorPool raw i (rootPool i) prior := by
          by_cases hb : b = F.segments.root j
          · subst b
            rw [R.map_root]
            exact root_mem_coordinateUsedPool F G rootPool interiorPool
              (mixedRootCandidate rootPool raw)
              (mixedInteriorCandidate F interiorPool raw) i j hj (rootPool i)
              (by simpa [priorPool, curPool] using hp) prior
          · exact coordinate_mem_coordinateUsedPool F G rootPool interiorPool
              (mixedRootCandidate rootPool raw)
              (mixedInteriorCandidate F interiorPool raw) i j hj b hb
              (rootPool i) (by simpa [priorPool, curPool, hb] using hp) prior
        apply hcurUnused
        rw [heq]
        exact hpriorUsed
      · exact (Finset.disjoint_left.mp
          (hrawDisjoint curPool priorPool hcurRelevant hpriorRelevant
            (Ne.symm hp))
          (Finset.mem_sdiff.mp hrootMem).1 (heq ▸ hpriorPool)).elim
    · have hcur := hnonrootMem a ha
      have hcurUnused := (Finset.mem_sdiff.mp hcur).2
      let curPool := interiorPool i a
      let priorPool := if b = F.segments.root j then rootPool j else interiorPool j b
      have hcurRelevant : relevant curPool := hinteriorRelevant i a
      have hpriorRelevant : relevant priorPool := by
        by_cases hb : b = F.segments.root j
        · simp only [priorPool, hb, if_true]
          exact hrootRelevant j
        · simp only [priorPool, hb, if_false]
          exact hinteriorRelevant j b
      by_cases hp : priorPool = curPool
      · have hp' : priorPool = interiorPool i a := by simpa [curPool] using hp
        have hpriorUsed : R.copy b ∈ mixedUsedPool F G rootPool interiorPool raw i
            (interiorPool i a) prior := by
          by_cases hb : b = F.segments.root j
          · subst b
            rw [R.map_root]
            exact root_mem_coordinateUsedPool F G rootPool interiorPool
              (mixedRootCandidate rootPool raw)
              (mixedInteriorCandidate F interiorPool raw) i j hj
              (interiorPool i a)
              (by simpa [priorPool, curPool] using hp) prior
          · exact coordinate_mem_coordinateUsedPool F G rootPool interiorPool
              (mixedRootCandidate rootPool raw)
              (mixedInteriorCandidate F interiorPool raw) i j hj b hb
              (interiorPool i a)
              (by simpa [priorPool, curPool, hb] using hp) prior
        apply hcurUnused
        rw [heq]
        exact hpriorUsed
      · exact (Finset.disjoint_left.mp
          (hrawDisjoint curPool priorPool hcurRelevant hpriorRelevant
            (Ne.symm hp))
          (Finset.mem_sdiff.mp hcur).1 (heq ▸ hpriorPool)).elim
  · intro q hp
    change G.Adj (originalImage q) (copy (F.segments.root i))
    have hparentEq :
        mixedParentImage F G originalImage rootPool interiorPool raw i prior =
          originalImage q := by
      unfold mixedParentImage
      split
      next q' hq' =>
        have hqq' : q' = q := Sum.inl.inj (hq'.symm.trans hp)
        subst q'
        rfl
      next z hz =>
        have hfalse : False := by simpa using hz.symm.trans hp
        exact hfalse.elim
    have hedge := congrArg (fun x => s(x, copy (F.segments.root i))) hparentEq
    exact (G.adj_congr_of_sym2 hedge).mp hattach
  · intro j a hp
    change G.Adj ((prior j (F.parent_earlier i j a hp)).copy a)
      (copy (F.segments.root i))
    have hparentEq :
        mixedParentImage F G originalImage rootPool interiorPool raw i prior =
          (prior j (F.parent_earlier i j a hp)).copy a := by
      unfold mixedParentImage
      split
      next q hq =>
        have hfalse : False := by simpa using hq.symm.trans hp
        exact hfalse.elim
      next z hz =>
        have hzz : z = ⟨j, a⟩ := Sum.inr.inj (hz.symm.trans hp)
        subst z
        rfl
    have hedge := congrArg (fun x => s(x, copy (F.segments.root i))) hparentEq
    exact (G.adj_congr_of_sym2 hedge).mp hattach

include rootOnly selected rootPool interiorPool pairPool orient whole rho rootDensity
  pairDensity hrootPair hinteriorPair hrawSubset relevant hrootRelevant
  hinteriorRelevant hrawDisjoint huniformPair
  hwholeDisjoint hpairDensity huniformSelectedRoot hselectedRootDensity
  hrootOnlySize hrootOnlyNonempty havailableLarge hselectedRootLarge
  hselectedRootMargin hparent hpairMargin
  horiginalInj horiginalOutsideRoot horiginalOutsideInterior in
/-- Full cut-aware hierarchy embedding using the genuine selected and
matching-pair dynamic local steps. -/
theorem exists_hierarchicalCandidateEmbedding_mixedDynamic :
    Nonempty (HierarchicalCandidateEmbedding F G originalImage
      (mixedRootCandidate rootPool raw)
      (mixedInteriorCandidate F interiorPool raw)) := by
  let step := mixedDynamicOnlineStep F G originalImage rootOnly selected rootPool
    interiorPool pairPool orient whole raw rho rootDensity pairDensity hrootPair
    hinteriorPair hrawSubset relevant hrootRelevant hinteriorRelevant
    hrawDisjoint huniformPair hwholeDisjoint
    hpairDensity huniformSelectedRoot hselectedRootDensity hrootOnlySize
    hrootOnlyNonempty havailableLarge hselectedRootLarge hselectedRootMargin
    hparent hpairMargin
  exact exists_hierarchicalCandidateEmbedding_fromStep F G originalImage
    (mixedRootCandidate rootPool raw) (mixedInteriorCandidate F interiorPool raw)
    step horiginalInj horiginalOutsideRoot horiginalOutsideInterior

end Construction

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline

#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicOnline.HierarchicalSegmentForest.exists_hierarchicalCandidateEmbedding_mixedDynamic
