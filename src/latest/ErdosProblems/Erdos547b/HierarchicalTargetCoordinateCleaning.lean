/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalTargetCleaning
import ErdosProblems.Erdos547b.HierarchicalCoordinateRegularEmbedding

/-!
# Target-relative cleaning for coordinate-sensitive hierarchy pools

The low-degree exceptional sets are unchanged from the canonical target
cleaner.  Only occupancy accounting changes: each interior coordinate uses
its actual endpoint pool, and every one-tree step carries one `small` reserve.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateCleaning

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinateRegular
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinateRegular.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s : ℕ} {B : Type u} {RootGroup Pool : Type*}
variable [DecidableEq Pool]

/-- Canonical target cleaning with an endpoint pool at every coordinate. -/
noncomputable def targetCoordinateCleanedRegularSystem
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (originalImage : Fin r → B) (small : ℕ)
    (rootGroup : Fin s → RootGroup)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (hreserved : Finset.univ.image originalImage ⊆ reserved)
    (hsegmentSmall : ∀ i, F.segments.size i ≤ small)
    (hattachOriginalCapacity : ∀ i q, F.parent i = Sum.inl q →
      (coordinatePoolLoad F rootPool interiorPool (rootPool i) + small + 1 : ℝ) +
          #(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i (F.segments.root i) ∪ reserved) ≤
        (#((rootRaw (rootGroup i)).filter (G.Adj (originalImage q))) : ℝ))
    (hattachCapacity : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
      (coordinatePoolLoad F rootPool interiorPool (rootPool i) + small + 1 : ℝ) +
          #(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i (F.segments.root i) ∪ reserved) ≤
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole j a)
          (rootWhole (rootGroup i)) - rho) * #(rootRaw (rootGroup i)))
    (hinternalCapacity : ∀ i a b, (F.segments.tree i).Adj a b →
      b ≠ F.segments.root i →
      (coordinatePoolLoad F rootPool interiorPool (interiorPool i b) +
          small + 1 : ℝ) +
          #(targetInteriorRemoved F G rho rootGroup rootWhole rootRaw
            interiorWhole interiorRaw reserved i b) ≤
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole i a)
          (interiorWhole i b) - rho) * #(interiorRaw i b))
    (horiginalInjective : Function.Injective originalImage)
    (hrootRawDisjoint : ∀ i j, rootPool i ≠ rootPool j →
      Disjoint (rootRaw (rootGroup i)) (rootRaw (rootGroup j)))
    (hinteriorRawDisjoint : ∀ i a j b,
      interiorPool i a ≠ interiorPool j b →
      Disjoint (interiorRaw i a) (interiorRaw j b))
    (hrootInteriorRawDisjoint : ∀ i j a,
      rootPool i ≠ interiorPool j a →
      Disjoint (rootRaw (rootGroup i)) (interiorRaw j a)) :
    CoordinateCleanedRegularSystem F G originalImage small rootPool
      interiorPool
      (targetRootCandidate F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw reserved)
      (targetInteriorCandidate F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw reserved) := by
  refine {
    rootRaw := fun i ↦ rootRaw (rootGroup i)
    interiorRaw := interiorRaw
    rootRemoved := fun i ↦ targetCoordinateRemoved F G rho rootGroup
      rootWhole rootRaw interiorWhole interiorRaw i (F.segments.root i) ∪ reserved
    interiorRemoved := targetInteriorRemoved F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved
    rootCandidate_eq := ?_
    interiorCandidate_eq := ?_
    segment_small := hsegmentSmall
    attach_original_capacity := hattachOriginalCapacity
    attach_source_degree := ?_
    internal_source_degree := ?_
    original_injective := horiginalInjective
    original_outside_root := ?_
    original_outside_interior := ?_
    root_disjoint := ?_
    interior_disjoint := ?_
    root_interior_disjoint := ?_
  }
  · intro i
    ext z
    simp [targetRootCandidate, targetCoordinateCandidate,
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
  · intro i a
    rfl
  · intro i j a hp z hz
    rw [sourceCandidate_target_eq] at hz
    have hzRaw := (Finset.mem_sdiff.mp hz).1
    have hzGood := targetCandidate_not_lowDegree_child F G rho rootGroup
      rootWhole rootRaw interiorWhole interiorRaw reserved i j a hp z hz
    exact (hattachCapacity i j a hp).trans
      (target_degree_ge_of_not_mem_lowDegree G rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole j a)
        (rootWhole (rootGroup i))
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw j a)
        (rootRaw (rootGroup i)) z hzRaw hzGood)
  · intro i a b hab hb z hz
    rw [sourceCandidate_target_eq] at hz
    have hzRaw := (Finset.mem_sdiff.mp hz).1
    have hzGood := targetCandidate_not_lowDegree_internal F G rho rootGroup
      rootWhole rootRaw interiorWhole interiorRaw reserved i a b hab hb z hz
    exact (hinternalCapacity i a b hab hb).trans
      (target_degree_ge_of_not_mem_lowDegree G rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)
        (interiorWhole i b)
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw i a)
        (interiorRaw i b) z hzRaw hzGood)
  · intro q i hz
    have hz' : originalImage q ∈
        ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootRaw interiorRaw i (F.segments.root i) \
          (targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i (F.segments.root i) ∪ reserved) := by
      simpa only [targetRootCandidate, targetCoordinateCandidate] using hz
    exact (Finset.mem_sdiff.mp hz').2
      (Finset.mem_union_right _
        (hreserved (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩)))
  · intro q i a hz
    by_cases ha : a = F.segments.root i
    · subst a
      simpa [targetInteriorCandidate, targetInteriorRemoved] using hz
    · apply (Finset.mem_sdiff.mp hz).2
      rw [targetInteriorRemoved, if_neg ha]
      exact Finset.mem_union_right _
        (hreserved (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩))
  · intro i j hij
    exact (hrootRawDisjoint i j hij).mono
      (by
        intro z hz
        have hz' := Finset.sdiff_subset hz
        simpa [targetRootCandidate, targetCoordinateCandidate,
          ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
          using hz')
      (by
        intro z hz
        have hz' := Finset.sdiff_subset hz
        simpa [targetRootCandidate, targetCoordinateCandidate,
          ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
          using hz')
  · intro i a j b hij
    exact (hinteriorRawDisjoint i a j b hij).mono
      Finset.sdiff_subset Finset.sdiff_subset
  · intro i j a hij
    exact (hrootInteriorRawDisjoint i j a hij).mono
      (by
        intro z hz
        have hz' := Finset.sdiff_subset hz
        simpa [targetRootCandidate, targetCoordinateCandidate,
          ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
          using hz')
      Finset.sdiff_subset

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateCleaning

#print axioms Erdos547b.ZhaoLemma59HierarchicalTargetCoordinateCleaning.HierarchicalSegmentForest.targetCoordinateCleanedRegularSystem
