/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClosedChunkAssembly

/-!
# Literal original-index placement of closed branches

Each placed original branch retains an actual matching edge, orientation,
copy, attachment, and cleaned-side membership. The transport uses the
already proved global injectivity of the chosen chunk copies; it does not
choose new images for branches or rely on a default edge outside the domain.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceOriginalBranchPlacement

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ForestMatching

universe u v w

/-- A literal partial branch embedding, with an adaptive edge assignment
defined only on the branches that have actually been placed. -/
structure BranchPlacement {b : ℕ} {V : Type u} {K : Type v}
    (F : OrderedRootedForest b) (G : SimpleGraph V) (selected : Finset (Fin b))
    (parent : Fin b → V) (endpoint : K → Fin 2 → Finset V) where
  edge : {i // i ∈ selected} → K
  orient : {i // i ∈ selected} → Fin 2 ≃ Fin 2
  forestCopy : OrderedForestCopy selected (fun i => Fin (F.size i)) F.tree G
  attach : ∀ i hi, G.Adj (parent i) (forestCopy.componentCopy i hi (F.root i))
  map_side : ∀ i hi a, forestCopy.componentCopy i hi a ∈
    endpoint (edge ⟨i, hi⟩) (orient ⟨i, hi⟩ ((F.isTree i).coloringTwoOfVert (F.root i) a))

private def transportCopy {b : ℕ} {V : Type u} (F : OrderedRootedForest b)
    (G : SimpleGraph V) {i j : Fin b} (h : i = j) (f : (F.tree i).Copy G) :
    (F.tree j).Copy G := h ▸ f

private theorem transportCopy_apply {b : ℕ} {V : Type u} (F : OrderedRootedForest b)
    (G : SimpleGraph V) {i j : Fin b} (h : i = j) (f : (F.tree i).Copy G)
    (a : Fin (F.size j)) :
    transportCopy F G h f a = f (Fin.cast (congrArg F.size h.symm) a) := by
  subst j
  rfl

private theorem root_cast {b : ℕ} (F : OrderedRootedForest b) {i j : Fin b} (h : i = j) :
    Fin.cast (congrArg F.size h.symm) (F.root j) = F.root i := by
  subst j
  rfl

private theorem color_cast {b : ℕ} (F : OrderedRootedForest b) {i j : Fin b} (h : i = j)
    (a : Fin (F.size j)) :
    (F.isTree i).coloringTwoOfVert (F.root i) (Fin.cast (congrArg F.size h.symm) a) =
      (F.isTree j).coloringTwoOfVert (F.root j) a := by
  subst j
  rfl

/-- Pull a simultaneous indexed family back to the original branches.
All graph images, attachment edges and physical-side assignments are
inherited from the given family, not reconstructed by a second embedding. -/
theorem exists_branchPlacement_with_positions_of_indexedCopies
    {b : ℕ} {V : Type u} {K : Type v} {I : Type w}
    (F : OrderedRootedForest b) (G : SimpleGraph V) (selected : Finset (Fin b))
    (parent : Fin b → V) (endpoint : K → Fin 2 → Finset V)
    (index : I → Fin b) (hcover : ∀ i ∈ selected, ∃ t, index t = i)
    (edge : I → K) (orient : I → Fin 2 ≃ Fin 2)
    (copies : ∀ t, (F.tree (index t)).Copy G)
    (hinj : Function.Injective (fun x : Σ t, Fin (F.size (index t)) => copies x.1 x.2))
    (hattach : ∀ t, G.Adj (parent (index t)) (copies t (F.root (index t))))
    (hside : ∀ t a, copies t a ∈ endpoint (edge t)
      (orient t ((F.isTree (index t)).coloringTwoOfVert (F.root (index t)) a))) :
    ∃ E : BranchPlacement F G selected parent endpoint,
      ∀ i, ∃ t, index t = i.1 ∧ E.edge i = edge t := by
  let pick : {i // i ∈ selected} → I := fun i => Classical.choose (hcover i.1 i.2)
  have hindex (i : {i // i ∈ selected}) : index (pick i) = i.1 := Classical.choose_spec (hcover i.1 i.2)
  let f := fun i hi => transportCopy F G (hindex ⟨i, hi⟩) (copies (pick ⟨i, hi⟩))
  refine ⟨{
    edge := fun i => edge (pick i)
    orient := fun i => orient (pick i)
    forestCopy := {
      componentCopy := f
      disjoint_ranges := ?_ }
    attach := ?_
    map_side := ?_ }, ?_⟩
  · intro i hi j hj hij
    rw [Set.disjoint_left]
    rintro x ⟨a, rfl⟩ ⟨d, heq⟩
    change transportCopy F G (hindex ⟨j, hj⟩) (copies (pick ⟨j, hj⟩)) d =
      transportCopy F G (hindex ⟨i, hi⟩) (copies (pick ⟨i, hi⟩)) a at heq
    rw [transportCopy_apply, transportCopy_apply] at heq
    have heq' :
        (⟨pick ⟨j, hj⟩, Fin.cast (congrArg F.size (hindex ⟨j, hj⟩).symm) d⟩ :
          Σ t, Fin (F.size (index t))) =
        ⟨pick ⟨i, hi⟩, Fin.cast (congrArg F.size (hindex ⟨i, hi⟩).symm) a⟩ := hinj heq
    have hpick : pick ⟨j, hj⟩ = pick ⟨i, hi⟩ := congrArg Sigma.fst heq'
    exact hij ((hindex ⟨i, hi⟩).symm.trans ((congrArg index hpick.symm).trans (hindex ⟨j, hj⟩)))
  · intro i hi
    change G.Adj (parent i) (transportCopy F G (hindex ⟨i, hi⟩) (copies (pick ⟨i, hi⟩)) (F.root i))
    rw [transportCopy_apply, root_cast F (hindex ⟨i, hi⟩)]
    simpa only [hindex] using hattach (pick ⟨i, hi⟩)
  · intro i hi a
    change transportCopy F G (hindex ⟨i, hi⟩) (copies (pick ⟨i, hi⟩)) a ∈ _
    rw [transportCopy_apply]
    have hs := hside (pick ⟨i, hi⟩) (Fin.cast (congrArg F.size (hindex ⟨i, hi⟩).symm) a)
    rw [color_cast F (hindex ⟨i, hi⟩)] at hs
    exact hs
  · intro i
    exact ⟨pick i, hindex i, rfl⟩

theorem exists_branchPlacement_of_indexedCopies
    {b : ℕ} {V : Type u} {K : Type v} {I : Type w}
    (F : OrderedRootedForest b) (G : SimpleGraph V) (selected : Finset (Fin b))
    (parent : Fin b → V) (endpoint : K → Fin 2 → Finset V)
    (index : I → Fin b) (hcover : ∀ i ∈ selected, ∃ t, index t = i)
    (edge : I → K) (orient : I → Fin 2 ≃ Fin 2)
    (copies : ∀ t, (F.tree (index t)).Copy G)
    (hinj : Function.Injective (fun x : Σ t, Fin (F.size (index t)) => copies x.1 x.2))
    (hattach : ∀ t, G.Adj (parent (index t)) (copies t (F.root (index t))))
    (hside : ∀ t a, copies t a ∈ endpoint (edge t)
      (orient t ((F.isTree (index t)).coloringTwoOfVert (F.root (index t)) a))) :
    Nonempty (BranchPlacement F G selected parent endpoint) := by
  obtain ⟨E, _⟩ := exists_branchPlacement_with_positions_of_indexedCopies F G selected parent endpoint
    index hcover edge orient copies hinj hattach hside
  exact ⟨E⟩

private theorem flatMap_index_cover {K I : Type*} (chunks : List (K × List I))
    (i : I) (hi : i ∈ chunks.flatMap Prod.snd) :
    ∃ j : Fin chunks.length, ∃ k : Fin chunks[j.val].2.length, chunks[j.val].2[k.val] = i := by
  obtain ⟨p, hp, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
  subst p
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hi
  exact ⟨j, k, hk⟩

open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceOnlineMatchingRoot
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceClosedChunkAssembly Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b : ℕ} (F : OrderedRootedForest b) (items : List (Fin b))
variable (bins : List (MatchingEdge Q.claim67.M))
variable (P : SaturatedPacking bins items (fun i => (F.size i : ℝ))
  (partOneCapacity W Q S C) (freshBranchBound α W.clusterSize))

def closedSelected : Finset (Fin b) := (P.closed.flatMap Prod.snd).toFinset

abbrev ClosedPosition := Σ j : Fin P.closed.length,
  Fin (closedChunk W Q S C F items bins P j).2.length

abbrev originalIndex (x : ClosedPosition W Q S C F items bins P) : Fin b :=
  (closedChunk W Q S C F items bins P x.1).2[x.2.val]

/-- Transport the actual simultaneously chosen copies to a literal
original-index branch placement, preserving their attachments and clean
matching-side membership. Empty closed families require no special edge. -/
theorem exists_original_closed_placement_with_closed_edges (z : Fin hostN)
    (E : ClosedAssembly W Q S C F items bins P z) :
    ∃ D : BranchPlacement F (embeddingHost W) (closedSelected W Q S C F items bins P)
        (fun _ => z) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)),
      ∀ i, D.edge i ∈ (P.closed.map Prod.fst).toFinset := by
  have htransport :
      ∃ D : BranchPlacement F (embeddingHost W) (closedSelected W Q S C F items bins P)
          (fun _ => z) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)),
        ∀ i, ∃ x : ClosedPosition W Q S C F items bins P,
          originalIndex W Q S C F items bins P x = i.1 ∧
            D.edge i = (closedChunk W Q S C F items bins P x.1).1 := by
    refine exists_branchPlacement_with_positions_of_indexedCopies F (embeddingHost W)
      (closedSelected W Q S C F items bins P) (fun _ => z)
      (fun e => residualSide (edgeWhole W Q e) (deleted W Q e))
      (originalIndex W Q S C F items bins P) ?_
      (fun x => (closedChunk W Q S C F items bins P x.1).1)
      (fun x => E.orient x.1 x.2) (fun x => (E.copies x.1).embedding.copy x.2) ?_ ?_ ?_
    · intro i hi
      obtain ⟨j, k, hk⟩ := flatMap_index_cover P.closed i (List.mem_toFinset.mp hi)
      exact ⟨⟨j, k⟩, hk⟩
    · rintro ⟨⟨j, i⟩, a⟩ ⟨⟨k, l⟩, d⟩ h
      have h' :
          (⟨j, ⟨i, a⟩⟩ : Σ j : Fin P.closed.length,
            Σ i : Fin (closedChunk W Q S C F items bins P j).2.length,
              Fin ((closedForest W Q S C F items bins P j).size i)) = ⟨k, ⟨l, d⟩⟩ := E.injective h
      exact congrArg (Equiv.sigmaAssoc _).symm h'
    · intro x
      exact (E.copies x.1).attach x.2
    · intro x a
      exact (E.copies x.1).map_side x.2 a
  obtain ⟨D, hpositions⟩ := htransport
  refine ⟨D, ?_⟩
  intro i
  obtain ⟨x, _, hx⟩ := hpositions i
  rw [hx]
  exact List.mem_toFinset.mpr (List.mem_map.mpr
    ⟨closedChunk W Q S C F items bins P x.1, List.getElem_mem x.1.isLt, rfl⟩)

theorem exists_original_closed_placement_in_bins (z : Fin hostN)
    (E : ClosedAssembly W Q S C F items bins P z) :
    ∃ D : BranchPlacement F (embeddingHost W) (closedSelected W Q S C F items bins P)
        (fun _ => z) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)),
      ∀ i, D.edge i ∈ bins := by
  obtain ⟨D, hclosed⟩ := exists_original_closed_placement_with_closed_edges W Q S C F items bins P z E
  refine ⟨D, ?_⟩
  intro i
  obtain ⟨p, hp, hpi⟩ := List.mem_map.mp (List.mem_toFinset.mp (hclosed i))
  rw [← hpi]
  exact P.bins_mem p (List.mem_append_left _ hp)

theorem exists_original_closed_placement (z : Fin hostN)
    (E : ClosedAssembly W Q S C F items bins P z) :
    Nonempty (BranchPlacement F (embeddingHost W) (closedSelected W Q S C F items bins P)
      (fun _ => z) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e))) := by
  obtain ⟨D, _⟩ := exists_original_closed_placement_in_bins W Q S C F items bins P z E
  exact ⟨D⟩

/-- The finite residual constructor's graph data produce literal
original-branch copies with all permanent endpoint constraints intact. -/
theorem exists_original_closed_placement_of_realized (z : Fin hostN)
    (R : RealizedPacking W Q S C F items bins P z) :
    Nonempty (BranchPlacement F (embeddingHost W) (closedSelected W Q S C F items bins P)
      (fun _ => z) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e))) := by
  obtain ⟨E⟩ := exists_closedAssembly W Q S C F items bins P z R
  exact exists_original_closed_placement W Q S C F items bins P z E

end Erdos547b.ZhaoSourceOriginalBranchPlacement

#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.exists_branchPlacement_of_indexedCopies
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.exists_branchPlacement_with_positions_of_indexedCopies
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.exists_original_closed_placement_in_bins
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.exists_original_closed_placement_with_closed_edges
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.exists_original_closed_placement
#print axioms Erdos547b.ZhaoSourceOriginalBranchPlacement.exists_original_closed_placement_of_realized
