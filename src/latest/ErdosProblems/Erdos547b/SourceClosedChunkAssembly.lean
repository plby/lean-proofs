/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceResidualRootPacking

/-!
# Simultaneous assembly of the closed matching chunks

The actual local copies chosen for different closed chunks have disjoint
images. This proves global injectivity of the entire closed family, while
retaining all attachments to its prescribed outer root and all permanent
endpoint-cleaning constraints. The pending chunk is deliberately absent.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClosedChunkAssembly

open Finset SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

private theorem closed_bin_injective {Bin Item : Type*} {bins : List Bin} {items : List Item}
    {weight : Item → ℝ} {capacity : Bin → ℝ} {slack : ℝ}
    (P : SaturatedPacking bins items weight capacity slack) :
    Function.Injective (fun j : Fin P.closed.length => (P.closed[j.val]).1) := by
  intro j k h
  have hj : P.closed[j.val] ∈ P.closed ++ P.pending.toList :=
    List.mem_append_left _ (List.getElem_mem j.isLt)
  have hk : P.closed[k.val] ∈ P.closed ++ P.pending.toList :=
    List.mem_append_left _ (List.getElem_mem k.isLt)
  have hpair : P.closed[j.val] = P.closed[k.val] := List.inj_on_of_nodup_map P.bins_nodup hj hk h
  have hn : P.closed.Nodup := by
    have hnAll := P.bins_nodup.of_map Prod.fst
    exact (List.nodup_append.mp hnAll).1
  exact hn.injective_get hpair

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b : ℕ} (F : OrderedRootedForest b) (items : List (Fin b))
variable (bins : List (MatchingEdge Q.claim67.M))
variable (P : SaturatedPacking bins items (fun i => (F.size i : ℝ))
  (partOneCapacity W Q S C) (freshBranchBound α W.clusterSize))

abbrev closedChunk (j : Fin P.closed.length) := P.closed[j.val]

abbrev closedForest (j : Fin P.closed.length) := listForest F (closedChunk W Q S C F items bins P j).2

theorem closedEdge_injective :
    Function.Injective (fun j : Fin P.closed.length => (closedChunk W Q S C F items bins P j).1) := by
  exact closed_bin_injective P

structure ClosedAssembly (z : Fin hostN) where
  orient : ∀ j : Fin P.closed.length,
    Fin (closedChunk W Q S C F items bins P j).2.length → Fin 2 ≃ Fin 2
  copies : ∀ j : Fin P.closed.length,
    DynamicAttachedForestEmbedding (closedForest W Q S C F items bins P j) (embeddingHost W)
      (fun _ => z) (orient j)
      (residualSide (edgeWhole W Q (closedChunk W Q S C F items bins P j).1)
        (deleted W Q (closedChunk W Q S C F items bins P j).1))
  injective : Function.Injective
    (fun x : Σ j : Fin P.closed.length,
      Σ i : Fin (closedChunk W Q S C F items bins P j).2.length,
        Fin ((closedForest W Q S C F items bins P j).size i) =>
      (copies x.1).embedding.copy x.2.1 x.2.2)

/-- Choose the actual local copies once and assemble their global
injectivity using the actual matching's endpoint disjointness. -/
theorem exists_closedAssembly (z : Fin hostN)
    (R : RealizedPacking W Q S C F items bins P z) :
    Nonempty (ClosedAssembly W Q S C F items bins P z) := by
  have hlocal (j : Fin P.closed.length) := R.closed (P.closed[j.val]) (List.getElem_mem j.isLt)
  choose orient hcopies using hlocal
  let copies := fun j => Classical.choice (hcopies j)
  refine ⟨⟨orient, copies, ?_⟩⟩
  rintro ⟨j, i, a⟩ ⟨k, l, d⟩ h
  change (copies j).embedding.copy i a = (copies k).embedding.copy l d at h
  by_cases hjk : j = k
  · subst k
    have hinner : (⟨i, a⟩ : Σ i, Fin ((closedForest W Q S C F items bins P j).size i)) = ⟨l, d⟩ :=
      (copies j).embedding.injective h
    exact congrArg (Sigma.mk j) hinner
  · have he : (closedChunk W Q S C F items bins P j).1 ≠
        (closedChunk W Q S C F items bins P k).1 :=
      fun he => hjk (closedEdge_injective W Q S C F items bins P he)
    have ha := (Finset.mem_sdiff.mp ((copies j).map_side i a)).1
    have hd := (Finset.mem_sdiff.mp ((copies k).map_side l d)).1
    have hdisj := edgeWhole_cross_disjoint W Q _ _ he
      (orient j i (((closedForest W Q S C F items bins P j).isTree i).coloringTwoOfVert
        ((closedForest W Q S C F items bins P j).root i) a))
      (orient k l (((closedForest W Q S C F items bins P k).isTree l).coloringTwoOfVert
        ((closedForest W Q S C F items bins P k).root l) d))
    exact False.elim (Finset.disjoint_left.mp hdisj ha (h.symm ▸ hd))

end Erdos547b.ZhaoSourceClosedChunkAssembly

#print axioms Erdos547b.ZhaoSourceClosedChunkAssembly.closedEdge_injective
#print axioms Erdos547b.ZhaoSourceClosedChunkAssembly.exists_closedAssembly
