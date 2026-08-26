/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalRegularEmbedding

/-!
# Canonical cleaning for hierarchical regular-pair systems

Every already embedded coordinate may later have to attach several child
segments, and every internal tree edge must be available in its forward
direction.  This module removes the union of the corresponding regular-pair
atypical sets once and for all.  Consequently callers provide actual
uniform pairs and aggregate capacity inequalities, but no pointwise
candidate-degree or cleaned-membership oracle.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalCanonical

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalRegular

universe u

namespace HierarchicalSegmentForest

variable {r s c k : ℕ} {B : Type u} {RootGroup : Type*}

/-- Later hierarchy segments attached to one already embedded coordinate. -/
noncomputable def childSegments
    (F : HierarchicalSegmentForest r s)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter fun t ↦ F.parent t = Sum.inr ⟨i, a⟩

/-- Non-root internal targets reached from one source coordinate. -/
noncomputable def internalTargets
    (F : HierarchicalSegmentForest r s)
    (i : Fin s) (a : Fin (F.segments.size i)) :
    Finset (Fin (F.segments.size i)) := by
  classical
  exact Finset.univ.filter fun b ↦
    (F.segments.tree i).Adj a b ∧ b ≠ F.segments.root i

/-- Bad vertices of a one-root host layer for all hierarchy segments attached
directly to that original root. -/
noncomputable def oneRootBad
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A : Finset B)
    (rootGroup : Fin s → RootGroup) (rootRaw : RootGroup → Finset B) : Finset B := by
  exact (Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0).biUnion fun i ↦
    atypicalVertices G rho A (rootRaw (rootGroup i))

/-- The initial bad union has exactly the standard regularity loss: one
`rho * |A|` term per segment attached to the original root. -/
theorem card_oneRootBad_le
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A : Finset B)
    (rootGroup : Fin s → RootGroup) (rootRaw : RootGroup → Finset B)
    (huniform : ∀ i, F.parent i = Sum.inl 0 →
      G.IsUniform rho A (rootRaw (rootGroup i)))
    (hrho : rho ≤ 1) :
    (#(oneRootBad F G rho A rootGroup rootRaw) : ℝ) ≤
      (#(Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0) : ℝ) *
        (rho * #A) := by
  let I := Finset.univ.filter fun i ↦ F.parent i = Sum.inl 0
  have hcardNat : #(oneRootBad F G rho A rootGroup rootRaw) ≤
      ∑ i ∈ I, #(atypicalVertices G rho A (rootRaw (rootGroup i))) := by
    unfold oneRootBad
    change #((I.biUnion fun i ↦
      atypicalVertices G rho A (rootRaw (rootGroup i)))) ≤
        ∑ i ∈ I, #(atypicalVertices G rho A (rootRaw (rootGroup i)))
    exact Finset.card_biUnion_le
  calc
    (#(oneRootBad F G rho A rootGroup rootRaw) : ℝ) ≤
        ∑ i ∈ I,
          (#(atypicalVertices G rho A (rootRaw (rootGroup i))) : ℝ) := by
      exact_mod_cast hcardNat
    _ ≤ ∑ _i ∈ I, rho * #A := by
      apply Finset.sum_le_sum
      intro i hi
      exact card_atypicalVertices_le G
        (huniform i (Finset.mem_filter.mp hi).2) hrho
    _ = (#I : ℝ) * (rho * #A) := by simp
    _ = _ := by rfl

/-- Choose the original-root image outside every required atypical set. -/
theorem exists_oneRootImage_of_bad_card
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest 1 s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (A : Finset B)
    (rootGroup : Fin s → RootGroup) (rootRaw : RootGroup → Finset B)
    (hbad : #(oneRootBad F G rho A rootGroup rootRaw) < #A) :
    ∃ z ∈ A, ∀ i, F.parent i = Sum.inl 0 →
      z ∈ cleanedSide G rho A (rootRaw (rootGroup i)) := by
  have hpos : 0 < #(A \ oneRootBad F G rho A rootGroup rootRaw) := by
    exact Finset.card_pos.mpr
      (Finset.sdiff_nonempty_of_card_lt_card hbad)
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  refine ⟨z, (Finset.mem_sdiff.mp hz).1, ?_⟩
  intro i hp
  rw [cleanedSide]
  refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz).1, ?_⟩
  intro hzbad
  apply (Finset.mem_sdiff.mp hz).2
  apply Finset.mem_biUnion.mpr
  refine ⟨i, ?_, hzbad⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

/-! ## Cleaning toward a large target subreservoir -/

/-- Vertices of the actual source reservoir `S ⊆ C` which have too few
neighbors in the actual target reservoir `T ⊆ D`, measured against the
density of the *whole* regular pair `C--D`.  This is the form needed for
Zhao's high-degree reservoirs `A₀,B₀`: no uniformity of the sliced pair
`S--T` is asserted. -/
noncomputable def targetLowDegreeVertices
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (C D S T : Finset B) : Finset B :=
  {x ∈ S | (#(T.filter (G.Adj x)) : ℝ) <
    (G.edgeDensity C D - rho) * #T}

/-- Whole-pair uniformity controls the exceptional vertices relative to a
large target subreservoir.  This is exactly `card_lowDegreeVertices_le`,
packaged under the public target-cleaning name. -/
theorem card_targetLowDegreeVertices_le
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    {rho : ℝ} {C D S T : Finset B}
    (huniform : G.IsUniform rho C D)
    (hSC : S ⊆ C) (hTD : T ⊆ D)
    (hSlarge : rho * #C ≤ #S) (hTlarge : rho * #D ≤ #T) :
    (#(targetLowDegreeVertices G rho C D S T) : ℝ) ≤ rho * #C := by
  simpa [targetLowDegreeVertices] using
    card_lowDegreeVertices_le G huniform hSC hTD hSlarge hTlarge

/-- Membership outside the target-relative bad set gives the real degree
certificate consumed by `CleanedRegularSystem`. -/
theorem target_degree_ge_of_not_mem_lowDegree
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (C D S T : Finset B) (z : B)
    (hzS : z ∈ S)
    (hzGood : z ∉ targetLowDegreeVertices G rho C D S T) :
    (G.edgeDensity C D - rho) * #T ≤
      (#(T.filter (G.Adj z)) : ℝ) := by
  apply le_of_not_gt
  intro hlt
  exact hzGood (by simpa [targetLowDegreeVertices, hzS, hlt])

/-- Union of all atypical sets which can obstruct an outgoing attachment
from one hierarchy coordinate. -/
noncomputable def coordinateRemoved
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B := by
  let X := ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
    F rootGroup rootRaw interiorRaw i a
  exact
    ((childSegments F i a).biUnion fun t ↦
      atypicalVertices G rho X (rootRaw (rootGroup t))) ∪
    ((internalTargets F i a).biUnion fun b ↦
      atypicalVertices G rho X (interiorRaw i b))

/-- The single cleaned candidate used by a source coordinate. -/
noncomputable def coordinateCandidate
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
      F rootGroup rootRaw interiorRaw i a \ 
    coordinateRemoved F G rho rootGroup rootRaw interiorRaw i a

/-- Also reserve a fixed finite set, in particular the already prescribed
original-root images. -/
noncomputable def reservedCoordinateCandidate
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  coordinateCandidate F G rho rootGroup rootRaw interiorRaw i a \ reserved

noncomputable def canonicalRootCandidate
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) : Finset B :=
  reservedCoordinateCandidate F G rho rootGroup rootRaw interiorRaw reserved i
    (F.segments.root i)

/-- The interior candidate at a segment root is deliberately empty: that
coordinate is represented by `canonicalRootCandidate`. -/
noncomputable def canonicalInteriorRemoved
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  if a = F.segments.root i then interiorRaw i a
  else coordinateRemoved F G rho rootGroup rootRaw interiorRaw i a ∪ reserved

noncomputable def canonicalInteriorCandidate
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) : Finset B :=
  interiorRaw i a \
    canonicalInteriorRemoved F G rho rootGroup rootRaw interiorRaw reserved i a

theorem sourceCandidate_canonical_eq_coordinateCandidate
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i)) :
    ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.sourceCandidate F
      (canonicalRootCandidate F G rho rootGroup rootRaw interiorRaw reserved)
      (canonicalInteriorCandidate F G rho rootGroup rootRaw interiorRaw reserved) i a =
    reservedCoordinateCandidate F G rho rootGroup rootRaw interiorRaw
      reserved i a := by
  by_cases ha : a = F.segments.root i
  · subst a
    simp [ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.sourceCandidate,
      canonicalRootCandidate]
  · ext z
    simp [ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.sourceCandidate,
      canonicalInteriorCandidate, canonicalInteriorRemoved,
      reservedCoordinateCandidate, coordinateCandidate,
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate,
      ha, and_assoc]

theorem coordinateCandidate_subset_child_cleaned
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (t i : Fin s) (a : Fin (F.segments.size i))
    (hp : F.parent t = Sum.inr ⟨i, a⟩) :
    coordinateCandidate F G rho rootGroup rootRaw interiorRaw i a ⊆
      cleanedSide G rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw i a)
        (rootRaw (rootGroup t)) := by
  intro z hz
  rw [cleanedSide]
  refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz).1, ?_⟩
  intro hzbad
  apply (Finset.mem_sdiff.mp hz).2
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  refine ⟨t, ?_, hzbad⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

theorem coordinateCandidate_subset_internal_cleaned
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a b : Fin (F.segments.size i))
    (hab : (F.segments.tree i).Adj a b)
    (hb : b ≠ F.segments.root i) :
    coordinateCandidate F G rho rootGroup rootRaw interiorRaw i a ⊆
      cleanedSide G rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw i a)
        (interiorRaw i b) := by
  letI : DecidableRel (F.segments.tree i).Adj := Classical.decRel _
  intro z hz
  rw [cleanedSide]
  refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz).1, ?_⟩
  intro hzbad
  apply (Finset.mem_sdiff.mp hz).2
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨b, ?_, hzbad⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hb⟩

/-- Construct the complete cleaned regular system canonically.  The caller
supplies actual uniform pairs, raw-set separation and aggregate numerical
capacities only. -/
noncomputable def canonicalCleanedRegularSystem
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (originalImage : Fin r → B)
    (rootGroup : Fin s → Fin c) (group : Fin s → Fin k)
    (rootRaw : Fin c → Finset B)
    (interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (hattachOriginalCapacity : ∀ i q, F.parent i = Sum.inl q →
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.rootLoad
          rootGroup (rootGroup i) + 1 : ℝ) +
          #(coordinateRemoved F G rho rootGroup rootRaw interiorRaw i
            (F.segments.root i) ∪ Finset.univ.image originalImage) ≤
        (#((rootRaw (rootGroup i)).filter (G.Adj (originalImage q))) : ℝ))
    (hattachUniform : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
      G.IsUniform rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw j a)
        (rootRaw (rootGroup i)))
    (hattachCapacity : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.rootLoad
          rootGroup (rootGroup i) + 1 : ℝ) +
          #(coordinateRemoved F G rho rootGroup rootRaw interiorRaw i
            (F.segments.root i) ∪ Finset.univ.image originalImage) ≤
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootRaw interiorRaw j a)
          (rootRaw (rootGroup i)) - rho) * #(rootRaw (rootGroup i)))
    (hinternalUniform : ∀ i a b, (F.segments.tree i).Adj a b →
      b ≠ F.segments.root i →
      G.IsUniform rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw i a)
        (interiorRaw i b))
    (hinternalCapacity : ∀ i a b, (F.segments.tree i).Adj a b →
      b ≠ F.segments.root i →
      (ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest.interiorLoad
          F group (group i) + 1 : ℝ) +
          #(canonicalInteriorRemoved F G rho rootGroup rootRaw interiorRaw
            (Finset.univ.image originalImage) i b) ≤
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootRaw interiorRaw i a)
          (interiorRaw i b) - rho) * #(interiorRaw i b))
    (horiginalInjective : Function.Injective originalImage)
    (hrootRawDisjoint : ∀ C D, C ≠ D →
      Disjoint (rootRaw C) (rootRaw D))
    (hinteriorRawDisjoint : ∀ i a j b, group i ≠ group j →
      Disjoint (interiorRaw i a) (interiorRaw j b))
    (hrootInteriorRawDisjoint : ∀ C i a,
      Disjoint (rootRaw C) (interiorRaw i a)) :
    ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.CleanedRegularSystem
      F G rho originalImage rootGroup group
      (canonicalRootCandidate F G rho rootGroup rootRaw interiorRaw
        (Finset.univ.image originalImage))
      (canonicalInteriorCandidate F G rho rootGroup rootRaw interiorRaw
        (Finset.univ.image originalImage)) := by
  refine
    { rootRaw := rootRaw
      interiorRaw := interiorRaw
      rootRemoved := fun i ↦ coordinateRemoved F G rho rootGroup rootRaw
        interiorRaw i (F.segments.root i) ∪ Finset.univ.image originalImage
      interiorRemoved := canonicalInteriorRemoved F G rho rootGroup rootRaw
        interiorRaw (Finset.univ.image originalImage)
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
      root_interior_disjoint := ?_ }
  · intro i
    ext z
    simp [canonicalRootCandidate, reservedCoordinateCandidate,
      coordinateCandidate,
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate,
      and_assoc]
  · intro i a
    rfl
  · intro i j a hp z hz
    have hzClean : z ∈ cleanedSide G rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw j a)
        (rootRaw (rootGroup i)) := by
      rw [sourceCandidate_canonical_eq_coordinateCandidate] at hz
      exact (coordinateCandidate_subset_child_cleaned F G rho rootGroup rootRaw
        interiorRaw i j a hp) (Finset.sdiff_subset hz)
    have hz' : z ∈
        ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootRaw interiorRaw j a \
          atypicalVertices G rho
            (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
              F rootGroup rootRaw interiorRaw j a)
            (rootRaw (rootGroup i)) := by
      simpa [cleanedSide] using hzClean
    have hzDeg :
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootRaw interiorRaw j a)
          (rootRaw (rootGroup i)) - rho) * #(rootRaw (rootGroup i)) ≤
          (#((rootRaw (rootGroup i)).filter (G.Adj z)) : ℝ) := by
      apply le_of_not_gt
      intro hlt
      exact (Finset.mem_sdiff.mp hz').2 (by
        simpa [atypicalVertices, (Finset.mem_sdiff.mp hz').1, hlt])
    exact (hattachCapacity i j a hp).trans hzDeg
  · intro i a b hab hb z hz
    have hzClean : z ∈ cleanedSide G rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw i a)
        (interiorRaw i b) := by
      rw [sourceCandidate_canonical_eq_coordinateCandidate] at hz
      exact (coordinateCandidate_subset_internal_cleaned F G rho rootGroup rootRaw
        interiorRaw i a b hab hb) (Finset.sdiff_subset hz)
    have hz' : z ∈
        ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootRaw interiorRaw i a \
          atypicalVertices G rho
            (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
              F rootGroup rootRaw interiorRaw i a)
            (interiorRaw i b) := by
      simpa [cleanedSide] using hzClean
    have hzDeg :
        (G.edgeDensity
          (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootRaw interiorRaw i a)
          (interiorRaw i b) - rho) * #(interiorRaw i b) ≤
          (#((interiorRaw i b).filter (G.Adj z)) : ℝ) := by
      apply le_of_not_gt
      intro hlt
      exact (Finset.mem_sdiff.mp hz').2 (by
        simpa [atypicalVertices, (Finset.mem_sdiff.mp hz').1, hlt])
    exact (hinternalCapacity i a b hab hb).trans hzDeg
  · intro q i hmem
    have hmem' : originalImage q ∈
        coordinateCandidate F G rho rootGroup rootRaw interiorRaw i
            (F.segments.root i) \
          Finset.univ.image originalImage := by
      simpa only [canonicalRootCandidate, reservedCoordinateCandidate] using hmem
    exact (Finset.mem_sdiff.mp hmem').2
      (show originalImage q ∈
          (Finset.univ.image originalImage : Finset B) from
        Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩)
  · intro q i a hmem
    by_cases ha : a = F.segments.root i
    · exfalso
      apply (Finset.mem_sdiff.mp hmem).2
      simpa [canonicalInteriorRemoved, ha] using (Finset.mem_sdiff.mp hmem).1
    · apply (Finset.mem_sdiff.mp hmem).2
      simp [canonicalInteriorRemoved, ha]
  · intro i j hij
    exact (hrootRawDisjoint (rootGroup i) (rootGroup j) hij).mono
      (by
        intro z hz
        have hz' := Finset.sdiff_subset (Finset.sdiff_subset hz)
        simpa [canonicalRootCandidate, reservedCoordinateCandidate,
          coordinateCandidate,
          ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
          using hz')
      (by
        intro z hz
        have hz' := Finset.sdiff_subset (Finset.sdiff_subset hz)
        simpa [canonicalRootCandidate, reservedCoordinateCandidate,
          coordinateCandidate,
          ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
          using hz')
  · intro i a j b hij
    exact (hinteriorRawDisjoint i a j b hij).mono
      (Finset.sdiff_subset)
      (Finset.sdiff_subset)
  · intro i j a
    exact (hrootInteriorRawDisjoint (rootGroup i) j a).mono
      (by
        intro z hz
        have hz' := Finset.sdiff_subset (Finset.sdiff_subset hz)
        simpa [canonicalRootCandidate, reservedCoordinateCandidate,
          coordinateCandidate,
          ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
          using hz')
      (Finset.sdiff_subset)

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalCanonical

#print axioms Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest.canonicalCleanedRegularSystem
