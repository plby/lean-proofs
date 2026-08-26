/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59FullOnline

/-!
# Online selection of the Zhao component-root skeleton

Only deleted cut edges whose parent is itself a component root constrain two
root images.  The other deleted edges end at an internal branch vertex and
are handled by the owner-specific Lemma-5.8 cleaning certificate.  This file
therefore extracts the small root-only online selection hidden inside the
full Lemma-5.9 construction.

At stage `i`, the eligible root set is the whole root candidate unless the
recorded cut parent is the earlier component root.  In that latter case it
is the neighbourhood of the already chosen parent-root image.  A cardinal
lower bound by `numParts` leaves room to avoid every earlier root image.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58RootSkeleton

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition

universe u v

variable {V : Type u} {B : Type v}
variable [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- One stage of the root-only online recursion. -/
structure RootSkeletonStep [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (candidate : Fin P.numParts → Finset B)
    (i : Fin P.numParts)
    (prior : ∀ k : Fin P.numParts, k.val < i.val → B) where
  rootImage : B
  root_mem : rootImage ∈ candidate i
  fresh : ∀ k (hk : k.val < i.val), rootImage ≠ prior k hk
  parent_adj : ∀ (hi : i.val ≠ 0)
      (hroot : P.parent i hi = P.roots (P.parentPart i hi)),
    G.Adj (prior (P.parentPart i hi) (P.parent_earlier i hi)) rootImage

section Construction

variable [Fintype B] [DecidableEq B]
  (P : ZhaoForestPartition T globalRoot small)
  (G : SimpleGraph B) [DecidableRel G.Adj]
  (candidate : Fin P.numParts → Finset B)
  (hcandidate : ∀ i, P.numParts ≤ #(candidate i))
  (hlink : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj))
      z, z ∈ candidate (P.parentPart j hj) →
      P.numParts ≤ #((candidate j).filter (G.Adj z)))

/-- Execute one root-selection stage against all previously chosen roots. -/
noncomputable def rootSkeletonStep (i : Fin P.numParts)
    (prior : ∀ k : Fin P.numParts, k.val < i.val → B)
    (hpriorMem : ∀ k (hk : k.val < i.val), prior k hk ∈ candidate k) :
    RootSkeletonStep P G candidate i prior := by
  classical
  let eligible : Finset B := if hi : i.val = 0 then candidate i
    else if hroot : P.parent i hi = P.roots (P.parentPart i hi) then
      (candidate i).filter
        (G.Adj (prior (P.parentPart i hi) (P.parent_earlier i hi)))
    else candidate i
  have heligible : P.numParts ≤ #eligible := by
    by_cases hi : i.val = 0
    · simpa [eligible, hi] using hcandidate i
    · by_cases hroot : P.parent i hi = P.roots (P.parentPart i hi)
      · simpa [eligible, hi, hroot] using hlink i hi hroot
          (prior (P.parentPart i hi) (P.parent_earlier i hi))
          (hpriorMem (P.parentPart i hi) (P.parent_earlier i hi))
      · simpa [eligible, hi, hroot] using hcandidate i
  let earlier : Finset (Fin P.numParts) := Finset.Iio i
  let used : Finset B := earlier.attach.image fun k ↦
    prior k.1 (by
      have hkIio : k.1 ∈ Finset.Iio i := k.2
      exact Fin.mk_lt_mk.mp (Finset.mem_Iio.mp hkIio))
  have hused : #used ≤ i.val := by
    calc
      #used ≤ #earlier.attach := Finset.card_image_le
      _ = #earlier := Finset.card_attach
      _ = i.val := by simp [earlier]
  have hused_lt : #used < #eligible :=
    lt_of_le_of_lt hused (lt_of_lt_of_le i.isLt heligible)
  let hex : ∃ z ∈ eligible, z ∉ used :=
    Finset.exists_mem_notMem_of_card_lt_card hused_lt
  let z : B := Classical.choose hex
  have hzEligible : z ∈ eligible := (Classical.choose_spec hex).1
  have hzUnused : z ∉ used := (Classical.choose_spec hex).2
  have hzCandidate : z ∈ candidate i := by
    by_cases hi : i.val = 0
    · simpa [eligible, hi] using hzEligible
    · by_cases hroot : P.parent i hi = P.roots (P.parentPart i hi)
      · exact (Finset.mem_filter.mp (by
          simpa [eligible, hi, hroot] using hzEligible)).1
      · simpa [eligible, hi, hroot] using hzEligible
  exact {
    rootImage := z
    root_mem := hzCandidate
    fresh := by
      intro k hk heq
      apply hzUnused
      apply Finset.mem_image.mpr
      refine ⟨⟨k, by simpa [earlier] using hk⟩, Finset.mem_attach _ _, ?_⟩
      exact heq.symm
    parent_adj := by
      intro hi hroot
      have hzAdj : G.Adj
          (prior (P.parentPart i hi) (P.parent_earlier i hi)) z :=
        (Finset.mem_filter.mp (by
          simpa [eligible, hi, hroot] using hzEligible)).2
      exact hzAdj
  }

/-- The recursively selected root, retaining its candidate-membership proof
inside the recursive datum. -/
noncomputable def rootSkeletonData (i : Fin P.numParts) :
    {z // z ∈ candidate i} :=
  let step := rootSkeletonStep P G candidate hcandidate hlink i
    (fun k _hk ↦ (rootSkeletonData k).1)
    (fun k _hk ↦ (rootSkeletonData k).2)
  ⟨step.rootImage, step.root_mem⟩
termination_by i.val

/-- The recursively selected root at one literal partition index. -/
noncomputable def rootSkeletonImage (i : Fin P.numParts) : B :=
  (rootSkeletonData P G candidate hcandidate hlink i).1

theorem rootSkeletonImage_mem (i : Fin P.numParts) :
    rootSkeletonImage P G candidate hcandidate hlink i ∈ candidate i := by
  exact (rootSkeletonData P G candidate hcandidate hlink i).2

theorem rootSkeletonImage_fresh (i k : Fin P.numParts)
    (hk : k.val < i.val) :
    rootSkeletonImage P G candidate hcandidate hlink i ≠
      rootSkeletonImage P G candidate hcandidate hlink k := by
  rw [rootSkeletonImage, rootSkeletonData.eq_def]
  exact (rootSkeletonStep P G candidate hcandidate hlink i
    (fun k _hk ↦ (rootSkeletonData P G candidate hcandidate hlink k).1)
    (fun k _hk ↦ (rootSkeletonData P G candidate hcandidate hlink k).2)).fresh
      k hk

theorem rootSkeletonImage_parent_adj
    (j : Fin P.numParts) (hj : j.val ≠ 0)
    (hroot : P.parent j hj = P.roots (P.parentPart j hj)) :
    G.Adj
      (rootSkeletonImage P G candidate hcandidate hlink
        (P.parentPart j hj))
      (rootSkeletonImage P G candidate hcandidate hlink j) := by
  let step := rootSkeletonStep P G candidate hcandidate hlink j
    (fun k _hk ↦ (rootSkeletonData P G candidate hcandidate hlink k).1)
    (fun k _hk ↦ (rootSkeletonData P G candidate hcandidate hlink k).2)
  have hjdef : rootSkeletonImage P G candidate hcandidate hlink j =
      step.rootImage := by
    rw [rootSkeletonImage, rootSkeletonData.eq_def]
  rw [hjdef]
  exact step.parent_adj hj hroot

end Construction

/-- Concrete root-skeleton output used by the cut-aware Lemma-5.8 wrapper. -/
structure RootSkeletonEmbedding [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (candidate : Fin P.numParts → Finset B) where
  rootImage : Fin P.numParts → B
  injective : Function.Injective rootImage
  mem_candidate : ∀ i, rootImage i ∈ candidate i
  cut_root_adj : ∀ j (hj : j.val ≠ 0),
    P.parent j hj = P.roots (P.parentPart j hj) →
    G.Adj (rootImage j) (rootImage (P.parentPart j hj))

/-- Select all component roots online. -/
theorem exists_rootSkeletonEmbedding
    [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (candidate : Fin P.numParts → Finset B)
    (hcandidate : ∀ i, P.numParts ≤ #(candidate i))
    (hlink : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj))
      z, z ∈ candidate (P.parentPart j hj) →
      P.numParts ≤ #((candidate j).filter (G.Adj z))) :
    Nonempty (RootSkeletonEmbedding P G candidate) := by
  let rootImage := rootSkeletonImage P G candidate hcandidate hlink
  refine ⟨{
    rootImage := rootImage
    injective := ?_
    mem_candidate := rootSkeletonImage_mem P G candidate hcandidate hlink
    cut_root_adj := ?_
  }⟩
  · intro i j hij
    by_cases hijVal : i.val < j.val
    · exact False.elim ((rootSkeletonImage_fresh P G candidate hcandidate
        hlink j i hijVal) hij.symm)
    · by_cases hjiVal : j.val < i.val
      · exact False.elim ((rootSkeletonImage_fresh P G candidate hcandidate
          hlink i j hjiVal) hij)
      · apply Fin.ext
        omega
  · intro j hj hroot
    exact (rootSkeletonImage_parent_adj P G candidate hcandidate hlink
      j hj hroot).symm

end Erdos547b.ZhaoLemma58RootSkeleton

#print axioms Erdos547b.ZhaoLemma58RootSkeleton.exists_rootSkeletonEmbedding
