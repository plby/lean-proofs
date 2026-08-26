/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalCanonicalCleaning
import ErdosProblems.Erdos547b.HierarchicalUnifiedRegularEmbedding

/-!
# Hierarchical cleaning toward large target reservoirs

Uniformity belongs to the whole cluster pair `C--D`, whereas Zhao's actual
root candidates can be high-degree subreservoirs `S ⊆ C`, `T ⊆ D`.  This
module cleans the actual source `S` by the low-degree exceptional set for
the whole pair and the actual target `T`.  It never asserts that the sliced
pair `S--T` is uniform.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalTargetCleaning

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalCanonical
open Erdos547b.ZhaoLemma59HierarchicalUnified
open Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s c k : ℕ} {B : Type u} {RootGroup : Type*}

/-- All target-relative low-degree sets which can obstruct a future edge
out of one hierarchy coordinate. -/
noncomputable def targetCoordinateRemoved
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B := by
  let sourceWhole :=
    ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
      F rootGroup rootWhole interiorWhole i a
  let sourceRaw :=
    ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
      F rootGroup rootRaw interiorRaw i a
  exact
    ((childSegments F i a).biUnion fun t ↦
      targetLowDegreeVertices G rho sourceWhole (rootWhole (rootGroup t))
        sourceRaw (rootRaw (rootGroup t))) ∪
    ((internalTargets F i a).biUnion fun b ↦
      targetLowDegreeVertices G rho sourceWhole (interiorWhole i b)
        sourceRaw (interiorRaw i b))

/-- The actual coordinate reservoir after target-relative cleaning and a
fixed reservation (normally the prescribed original-root images). -/
noncomputable def targetCoordinateCandidate
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
      F rootGroup rootRaw interiorRaw i a \
    (targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw i a ∪ reserved)

noncomputable def targetRootCandidate
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B) (i : Fin s) : Finset B :=
  targetCoordinateCandidate F G rho rootGroup rootWhole rootRaw
    interiorWhole interiorRaw reserved i (F.segments.root i)

noncomputable def targetInteriorRemoved
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  if a = F.segments.root i then interiorRaw i a
  else targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
    interiorWhole interiorRaw i a ∪ reserved

noncomputable def targetInteriorCandidate
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  interiorRaw i a \
    targetInteriorRemoved F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved i a

theorem sourceCandidate_target_eq
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) :
    ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.sourceCandidate F
      (targetRootCandidate F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw reserved)
      (targetInteriorCandidate F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw reserved) i a =
    targetCoordinateCandidate F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved i a := by
  by_cases ha : a = F.segments.root i
  · subst a
    simp [ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.sourceCandidate,
      targetRootCandidate]
  · ext z
    simp [ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.sourceCandidate,
      targetInteriorCandidate, targetInteriorRemoved,
      targetCoordinateCandidate,
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate,
      ha, and_assoc]

theorem targetCandidate_not_lowDegree_child
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (t i : Fin s) (a : Fin (F.segments.size i))
    (hp : F.parent t = Sum.inr ⟨i, a⟩) (z : B)
    (hz : z ∈ targetCoordinateCandidate F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved i a) :
    z ∉ targetLowDegreeVertices G rho
      (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootGroup rootWhole interiorWhole i a)
      (rootWhole (rootGroup t))
      (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootGroup rootRaw interiorRaw i a)
      (rootRaw (rootGroup t)) := by
  intro hzlow
  have hznot := (Finset.mem_sdiff.mp hz).2
  apply hznot
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  refine ⟨t, ?_, hzlow⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

theorem targetCandidate_not_lowDegree_internal
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a b : Fin (F.segments.size i))
    (hab : (F.segments.tree i).Adj a b)
    (hb : b ≠ F.segments.root i) (z : B)
    (hz : z ∈ targetCoordinateCandidate F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved i a) :
    z ∉ targetLowDegreeVertices G rho
      (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootGroup rootWhole interiorWhole i a)
      (interiorWhole i b)
      (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
        F rootGroup rootRaw interiorRaw i a)
      (interiorRaw i b) := by
  letI : DecidableRel (F.segments.tree i).Adj := Classical.decRel _
  intro hzlow
  have hznot := (Finset.mem_sdiff.mp hz).2
  apply hznot
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨b, ?_, hzlow⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hb⟩

/-- Canonical cleaned system for actual subreservoirs of whole regular-pair
sides.  Uniformity is used upstream only to bound the explicit exceptional
sets; the degree proof here follows definitionally from having removed those
sets. -/
noncomputable def targetCleanedRegularSystem
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (originalImage : Fin r → B)
    (rootGroup : Fin s → Fin c) (group : Fin s → Fin k)
    (rootWhole rootRaw : Fin c → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (hreserved : Finset.univ.image originalImage ⊆ reserved)
    (hattachOriginalCapacity : ∀ i q, F.parent i = Sum.inl q →
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.rootLoad
          rootGroup (rootGroup i) + 1 : ℝ) +
          #(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i (F.segments.root i) ∪ reserved) ≤
        (#((rootRaw (rootGroup i)).filter (G.Adj (originalImage q))) : ℝ))
    (hattachCapacity : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.rootLoad
          rootGroup (rootGroup i) + 1 : ℝ) +
          #(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i (F.segments.root i) ∪ reserved) ≤
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole j a)
          (rootWhole (rootGroup i)) - rho) * #(rootRaw (rootGroup i)))
    (hinternalCapacity : ∀ i a b, (F.segments.tree i).Adj a b →
      b ≠ F.segments.root i →
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.interiorLoad
          F group (group i) + 1 : ℝ) +
          #(targetInteriorRemoved F G rho rootGroup rootWhole rootRaw
            interiorWhole interiorRaw reserved i b) ≤
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole i a)
          (interiorWhole i b) - rho) * #(interiorRaw i b))
    (hrootSubset : ∀ C, rootRaw C ⊆ rootWhole C)
    (hinteriorSubset : ∀ i a, interiorRaw i a ⊆ interiorWhole i a)
    (horiginalInjective : Function.Injective originalImage)
    (hrootRawDisjoint : ∀ C D, C ≠ D →
      Disjoint (rootRaw C) (rootRaw D))
    (hinteriorRawDisjoint : ∀ i a j b, group i ≠ group j →
      Disjoint (interiorRaw i a) (interiorRaw j b))
    (hrootInteriorRawDisjoint : ∀ C i a,
      Disjoint (rootRaw C) (interiorRaw i a)) :
    ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.CleanedRegularSystem
      F G rho originalImage rootGroup group
      (targetRootCandidate F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw reserved)
      (targetInteriorCandidate F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw reserved) := by
  refine {
    rootRaw := rootRaw
    interiorRaw := interiorRaw
    rootRemoved := fun i ↦ targetCoordinateRemoved F G rho rootGroup
      rootWhole rootRaw interiorWhole interiorRaw i (F.segments.root i) ∪ reserved
    interiorRemoved := targetInteriorRemoved F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved
    rootCandidate_eq := ?_
    interiorCandidate_eq := ?_
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
        (hreserved (show originalImage q ∈
            (Finset.univ.image originalImage : Finset B) from
          Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩)))
  · intro q i a hz
    by_cases ha : a = F.segments.root i
    · subst a
      simpa [targetInteriorCandidate, targetInteriorRemoved] using hz
    · apply (Finset.mem_sdiff.mp hz).2
      rw [targetInteriorRemoved, if_neg ha]
      exact Finset.mem_union_right _
        (hreserved (show originalImage q ∈
            (Finset.univ.image originalImage : Finset B) from
          Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩))
  · intro i j hij
    exact (hrootRawDisjoint (rootGroup i) (rootGroup j) hij).mono
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
  · intro i j a
    exact (hrootInteriorRawDisjoint (rootGroup i) j a).mono
      (by
        intro z hz
        have hz' := Finset.sdiff_subset hz
        simpa [targetRootCandidate, targetCoordinateCandidate,
          ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
          using hz')
      Finset.sdiff_subset

/-- Unified-pool version of `targetCleanedRegularSystem`.  It is the actual
backend used by Lemma 6.14(2): `F₀` gives its C-root and M₂-interior layers
different physical tags, whereas an `F₁`/`F_b` segment gives its root and
interior layers the same matching-edge tag. -/
noncomputable def targetUnifiedCleanedRegularSystem
    [Fintype B] [DecidableEq B]
    {Pool : Type*} [DecidableEq Pool]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (originalImage : Fin r → B)
    (rootGroup : Fin s → RootGroup)
    (rootPool interiorPool : Fin s → Pool)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (hreserved : Finset.univ.image originalImage ⊆ reserved)
    (hattachOriginalCapacity : ∀ i q, F.parent i = Sum.inl q →
      (ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest.poolLoad
          F rootPool interiorPool (rootPool i) + 1 : ℝ) +
          #(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i (F.segments.root i) ∪ reserved) ≤
        (#((rootRaw (rootGroup i)).filter (G.Adj (originalImage q))) : ℝ))
    (hattachCapacity : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
      (ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest.poolLoad
          F rootPool interiorPool (rootPool i) + 1 : ℝ) +
          #(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i (F.segments.root i) ∪ reserved) ≤
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole j a)
          (rootWhole (rootGroup i)) - rho) * #(rootRaw (rootGroup i)))
    (hinternalCapacity : ∀ i a b, (F.segments.tree i).Adj a b →
      b ≠ F.segments.root i →
      (ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest.poolLoad
          F rootPool interiorPool (interiorPool i) + 1 : ℝ) +
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
      interiorPool i ≠ interiorPool j →
      Disjoint (interiorRaw i a) (interiorRaw j b))
    (hrootInteriorRawDisjoint : ∀ i j a,
      rootPool i ≠ interiorPool j →
      Disjoint (rootRaw (rootGroup i)) (interiorRaw j a)) :
    ZhaoLemma59HierarchicalUnifiedRegular.HierarchicalSegmentForest.UnifiedCleanedRegularSystem
      F G originalImage rootPool interiorPool
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
        (hreserved (show originalImage q ∈
            (Finset.univ.image originalImage : Finset B) from
          Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩)))
  · intro q i a hz
    by_cases ha : a = F.segments.root i
    · subst a
      simpa [targetInteriorCandidate, targetInteriorRemoved] using hz
    · apply (Finset.mem_sdiff.mp hz).2
      rw [targetInteriorRemoved, if_neg ha]
      exact Finset.mem_union_right _
        (hreserved (show originalImage q ∈
            (Finset.univ.image originalImage : Finset B) from
          Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩))
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

end Erdos547b.ZhaoLemma59HierarchicalTargetCleaning

#print axioms Erdos547b.ZhaoLemma59HierarchicalTargetCleaning.HierarchicalSegmentForest.targetCleanedRegularSystem
#print axioms Erdos547b.ZhaoLemma59HierarchicalTargetCleaning.HierarchicalSegmentForest.targetUnifiedCleanedRegularSystem
