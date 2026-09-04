/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberRootAvailability

/-!
# Bounded root incidence in the cycle-cover absorber

Although the full cycle-cover bank contains all edge-faithful quotients, a
private vertex is tagged by one particular copy.  A root adjacent to that
vertex therefore lies in the image of the copy's template, of size at most
`12`.  This is the constant-degree fact needed on the small vortex layer.
-/

namespace Erdos207

open Finset

noncomputable section

lemma target_mem_of_mem_transformerSourceSide
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    (phi : EdgeBijectiveHom G H)
    (heven : ∀ x, Even (G.degree x))
    {T : TripleOn (TransformerVertex G W)} {y : W}
    (hT : T ∈ transformerSourceSide phi heven)
    (hy : TransformerVertex.target y ∈ T.1) :
    ∃ x : V, y = phi.hom x := by
  rcases mem_union.mp hT with hEdge | hMatching
  · obtain ⟨e, rfl⟩ := mem_transformerSourceEdgeTriples_iff.mp hEdge
    exact (target_not_mem_sourceEdgeTriple e y hy).elim
  · obtain ⟨x, p, rfl⟩ :=
      (mem_transformerTargetMatchingTriples_iff phi heven).mp hMatching
    exact ⟨x, (target_mem_targetMatchingTriple_iff phi heven x p y).mp hy⟩

lemma target_mem_of_mem_c4c5LocalOut
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : C4C5QuotientMap Y)
    {T : TripleOn (C4C5LocalVertex Y)} {y : Y}
    (hT : T ∈ c4c5LocalOut f)
    (hy : Sum.inl (TransformerVertex.target y) ∈ T.1) :
    ∃ x : Fin 9, y = f.1 x := by
  rcases mem_union.mp hT with hAbs | hSource
  · obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hAbs
    obtain ⟨a, ha, hay⟩ := Finset.mem_map.mp hy
    have : c4c5LocalAbsorberEmbedding a ≠
        Sum.inl (TransformerVertex.target y) := by
      rw [← (finSumFinEquiv (m := 9) (n := 6)).apply_symm_apply a]
      rcases (finSumFinEquiv (m := 9) (n := 6)).symm a with a | a <;>
        simp [c4c5LocalAbsorberEmbedding, transformerSourceEmbedding]
    exact (this hay).elim
  · obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hSource
    obtain ⟨a, ha, hay⟩ := Finset.mem_map.mp hy
    have haTarget : a = TransformerVertex.target y := by
      apply c4c5LocalTransformerEmbedding.injective
      simpa [c4c5LocalTransformerEmbedding] using hay
    subst a
    exact target_mem_of_mem_transformerSourceSide
      (c4c5QuotientHom f) c4c5Template_even_degree hS ha

lemma target_mem_of_mem_threeC4LocalOut
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : ThreeC4QuotientMap Y)
    {T : TripleOn (ThreeC4LocalVertex Y)} {y : Y}
    (hT : T ∈ threeC4LocalOut f)
    (hy : Sum.inl (TransformerVertex.target y) ∈ T.1) :
    ∃ x : Fin 12, y = f.1 x := by
  rcases mem_union.mp hT with hAbs | hSource
  · obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hAbs
    obtain ⟨a, ha, hay⟩ := Finset.mem_map.mp hy
    have : threeC4LocalAbsorberEmbedding a ≠
        Sum.inl (TransformerVertex.target y) := by
      rw [← (finSumFinEquiv (m := 12) (n := 6)).apply_symm_apply a]
      rcases (finSumFinEquiv (m := 12) (n := 6)).symm a with a | a <;>
        simp [threeC4LocalAbsorberEmbedding, transformerSourceEmbedding]
    exact (this hay).elim
  · obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hSource
    obtain ⟨a, ha, hay⟩ := Finset.mem_map.mp hy
    have haTarget : a = TransformerVertex.target y := by
      apply threeC4LocalTransformerEmbedding.injective
      simpa [threeC4LocalTransformerEmbedding] using hay
    subst a
    exact target_mem_of_mem_transformerSourceSide
      (threeC4QuotientHom f) threeC4Template_even_degree hS ha

/-- Roots in the base type which can meet one fixed vertex of the universal
cycle-cover bank. -/
def fullCycleCoverRootCandidates
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    FullCycleCoverVertex Y → Finset Y
  | Sum.inl _ => ∅
  | Sum.inr p => match p.1 with
    | .triangle _ => ∅
    | .c4c5 f => univ.image f.1
    | .threeC4 f => univ.image f.1

lemma card_fullCycleCoverRootCandidates_le_twelve
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (v : FullCycleCoverVertex Y) :
    (fullCycleCoverRootCandidates v).card ≤ 12 := by
  rcases v with y | p
  · simp [fullCycleCoverRootCandidates]
  · rcases p with ⟨i, z⟩
    cases i with
    | triangle f => simp [fullCycleCoverRootCandidates]
    | c4c5 f =>
        calc
          (fullCycleCoverRootCandidates
              (Sum.inr ⟨FullCycleCoverCopy.c4c5 f, z⟩)).card
              ≤ (univ : Finset (Fin 9)).card := by
                simpa [fullCycleCoverRootCandidates] using
                  (card_image_le :
                    ((univ : Finset (Fin 9)).image f.1).card ≤
                      (univ : Finset (Fin 9)).card)
          _ = 9 := by simp
          _ ≤ 12 := by omega
    | threeC4 f =>
        calc
          (fullCycleCoverRootCandidates
              (Sum.inr ⟨FullCycleCoverCopy.threeC4 f, z⟩)).card
              ≤ (univ : Finset (Fin 12)).card := by
                simpa [fullCycleCoverRootCandidates] using
                  (card_image_le :
                    ((univ : Finset (Fin 12)).image f.1).card ≤
                      (univ : Finset (Fin 12)).card)
          _ = 12 := by simp

lemma root_mem_fullCycleCoverRootCandidates_of_copy_adj
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) {y : Y} {v : FullCycleCoverVertex Y}
    (hyv : (coveredGraph (fullCycleCoverOut i)).Adj (Sum.inl y) v) :
    y ∈ fullCycleCoverRootCandidates v := by
  cases i with
  | triangle f =>
      simp [fullCycleCoverOut, coveredGraph] at hyv
  | c4c5 f =>
      rw [fullCycleCoverOut, coveredGraph_mapTripleSystem,
        SimpleGraph.map_adj] at hyv
      obtain ⟨a, b, hab, ha, hb⟩ := hyv
      have haTarget : a = Sum.inl (TransformerVertex.target y) := by
        apply (c4c5FullAttachmentEmbedding f).injective
        simpa using ha
      subst a
      have hbPrivate : IsC4C5LocalPrivate b := by
        rcases c4c5LocalOut_edge_has_private f hab with ha | hb
        · exact (show False by
            simpa [IsC4C5LocalPrivate, IsTransformerNonTarget] using ha).elim
        · exact hb
      obtain ⟨T, hT, hyT, hbT, hyb⟩ := hab
      obtain ⟨x, hyx⟩ := target_mem_of_mem_c4c5LocalOut f hT hyT
      have hyImage : y ∈ (univ : Finset (Fin 9)).image f.1 :=
        mem_image.mpr ⟨x, mem_univ x, hyx.symm⟩
      rw [← hb]
      rcases b with b | k
      · cases b with
        | source z =>
            simp [fullCycleCoverRootCandidates,
              c4c5FullAttachmentEmbedding, c4c5LocalSplitEquiv]
            exact hyImage
        | target z => exact hbPrivate.elim
        | edge e =>
            simp [fullCycleCoverRootCandidates,
              c4c5FullAttachmentEmbedding, c4c5LocalSplitEquiv]
            exact hyImage
      · simp [fullCycleCoverRootCandidates,
          c4c5FullAttachmentEmbedding, c4c5LocalSplitEquiv]
        exact hyImage
  | threeC4 f =>
      rw [fullCycleCoverOut, coveredGraph_mapTripleSystem,
        SimpleGraph.map_adj] at hyv
      obtain ⟨a, b, hab, ha, hb⟩ := hyv
      have haTarget : a = Sum.inl (TransformerVertex.target y) := by
        apply (threeC4FullAttachmentEmbedding f).injective
        simpa using ha
      subst a
      have hbPrivate : IsThreeC4LocalPrivate b := by
        rcases threeC4LocalOut_edge_has_private f hab with ha | hb
        · exact (show False by
            simpa [IsThreeC4LocalPrivate, IsTransformerNonTarget] using ha).elim
        · exact hb
      obtain ⟨T, hT, hyT, hbT, hyb⟩ := hab
      obtain ⟨x, hyx⟩ := target_mem_of_mem_threeC4LocalOut f hT hyT
      have hyImage : y ∈ (univ : Finset (Fin 12)).image f.1 :=
        mem_image.mpr ⟨x, mem_univ x, hyx.symm⟩
      rw [← hb]
      rcases b with b | k
      · cases b with
        | source z =>
            simp [fullCycleCoverRootCandidates,
              threeC4FullAttachmentEmbedding, threeC4LocalSplitEquiv]
            exact hyImage
        | target z => exact hbPrivate.elim
        | edge e =>
            simp [fullCycleCoverRootCandidates,
              threeC4FullAttachmentEmbedding, threeC4LocalSplitEquiv]
            exact hyImage
      · simp [fullCycleCoverRootCandidates,
          threeC4FullAttachmentEmbedding, threeC4LocalSplitEquiv]
        exact hyImage

lemma root_mem_fullCycleCoverRootCandidates_of_outGraph_adj
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {y : Y} {v : FullCycleCoverVertex Y}
    (hyv : (graphSup (univ : Finset (FullCycleCoverCopy Y))
      (fun i ↦ coveredGraph (fullCycleCoverOut i))).Adj (Sum.inl y) v) :
    y ∈ fullCycleCoverRootCandidates v := by
  have aux : ∀ s : Finset (FullCycleCoverCopy Y),
      (graphSup s (fun i ↦ coveredGraph (fullCycleCoverOut i))).Adj
          (Sum.inl y) v →
        y ∈ fullCycleCoverRootCandidates v := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [graphSup_insert, SimpleGraph.sup_adj]
        intro h
        exact h.elim
          (root_mem_fullCycleCoverRootCandidates_of_copy_adj i)
          ih
  exact aux univ hyv

/-- Original path-cover roots adjacent to a fixed path-cover vertex. -/
def pathCoverOriginalRootCandidates
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} :
    PathCoverVertex V k → Finset V
  | .root _ => ∅
  | .middle e _ => {e.1.out.1, e.1.out.2}

lemma card_pathCoverOriginalRootCandidates_le_two
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (v : PathCoverVertex V k) :
    (pathCoverOriginalRootCandidates v).card ≤ 2 := by
  cases v with
  | root x => simp [pathCoverOriginalRootCandidates]
  | middle e i =>
      have h := card_insert_le e.1.out.1 {e.1.out.2}
      simp only [card_singleton] at h
      simpa only [pathCoverOriginalRootCandidates] using h

lemma root_mem_pathCoverOriginalRootCandidates_of_adj
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    {x : V} {v : PathCoverVertex V k}
    (hxv : (pathCoverGraph V k).Adj (.root x) v) :
    x ∈ pathCoverOriginalRootCandidates v := by
  cases v with
  | root y => exact (pathCoverGraph_not_adj_root_root x y hxv).elim
  | middle e i =>
      rw [pathCoverGraph_adj_root_middle] at hxv
      simp only [pathCoverOriginalRootCandidates, mem_insert, mem_singleton]
      rw [← e.1.out_eq, Sym2.mem_iff] at hxv
      exact hxv

/-- Pull back the at most twelve base-root candidates of the full-cycle bank
to original roots, and add the two possible path-cover neighbors. -/
def cycleCoverCoreRootCandidates
    (V : Type*) [Fintype V] [DecidableEq V]
    (v : CycleCoverAbsorberVertex V) : Finset V :=
  (univ.filter fun x ↦
      (PathCoverVertex.root x : CycleCoverPathVertex V) ∈
        fullCycleCoverRootCandidates v) ∪
    match v with
    | Sum.inl w => pathCoverOriginalRootCandidates w
    | Sum.inr _ => ∅

lemma card_cycleCoverCoreRootCandidates_le_fourteen
    (V : Type*) [Fintype V] [DecidableEq V]
    (v : CycleCoverAbsorberVertex V) :
    (cycleCoverCoreRootCandidates V v).card ≤ 14 := by
  let A : Finset V := univ.filter fun x ↦
    (PathCoverVertex.root x : CycleCoverPathVertex V) ∈
      fullCycleCoverRootCandidates v
  have hmapSubset : A.map (pathCoverRootEmbedding
      (X := V) (k := 6 * (Fintype.card V) ^ 2)) ⊆
      fullCycleCoverRootCandidates v := by
    intro y hy
    obtain ⟨x, hxA, rfl⟩ := Finset.mem_map.mp hy
    exact (mem_filter.mp hxA).2
  have hA : A.card ≤ 12 := by
    rw [← card_map (pathCoverRootEmbedding
      (X := V) (k := 6 * (Fintype.card V) ^ 2))]
    exact (card_le_card hmapSubset).trans
      (card_fullCycleCoverRootCandidates_le_twelve v)
  rcases v with w | p
  · change (A ∪ pathCoverOriginalRootCandidates w).card ≤ 14
    exact (card_union_le _ _).trans <| by
      have hB := card_pathCoverOriginalRootCandidates_le_two
        (k := 6 * (Fintype.card V) ^ 2) w
      omega
  · change (A ∪ ∅).card ≤ 14
    simp only [union_empty]
    omega

lemma root_mem_cycleCoverCoreRootCandidates_of_adj
    (V : Type*) [Fintype V] [DecidableEq V]
    {x : V} {v : CycleCoverAbsorberVertex V}
    (hxv : (cycleCoverAbsorberGraph V).Adj
      (cycleCoverRootEmbedding V x) v) :
    x ∈ cycleCoverCoreRootCandidates V v := by
  rw [cycleCoverAbsorberGraph, SimpleGraph.sup_adj] at hxv
  rcases hxv with hxv | hxv
  · apply mem_union_left
    exact mem_filter.mpr ⟨mem_univ x,
      root_mem_fullCycleCoverRootCandidates_of_outGraph_adj hxv⟩
  · rw [embeddedPathCoverGraph, SimpleGraph.map_adj] at hxv
    obtain ⟨a, b, hab, ha, hb⟩ := hxv
    have haRoot : a = PathCoverVertex.root x := by
      change a = PathCoverVertex.root x
      apply (fullCycleCoverBaseEmbedding (CycleCoverPathVertex V)).injective
      exact ha
    subst a
    have hbBase : v = Sum.inl b := hb.symm
    subst v
    apply mem_union_right
    exact root_mem_pathCoverOriginalRootCandidates_of_adj hab

/-- Original flexible roots which can meet one fixed vertex after the sphere
transform.  A root vertex uses the fourteen core candidates; an interior
vertex uses the at most three original roots whose core images index its
sphere fiber. -/
def highGirthOriginalRootCandidates
    (V : Type*) [Fintype V] [DecidableEq V] {q : ℕ} :
    HighGirthCycleCoverVertex V q → Finset V
  | .root b => cycleCoverCoreRootCandidates V b
  | .interior T _ =>
      univ.filter fun x ↦ cycleCoverRootEmbedding V x ∈ T.1

lemma card_highGirthOriginalRootCandidates_le_fourteen
    (V : Type*) [Fintype V] [DecidableEq V] {q : ℕ}
    (v : HighGirthCycleCoverVertex V q) :
    (highGirthOriginalRootCandidates V v).card ≤ 14 := by
  cases v with
  | root b =>
      exact card_cycleCoverCoreRootCandidates_le_fourteen V b
  | interior T z =>
      let A : Finset V := univ.filter fun x ↦
        cycleCoverRootEmbedding V x ∈ T.1
      have hmapSubset : A.map (cycleCoverRootEmbedding V) ⊆ T.1 := by
        intro y hy
        obtain ⟨x, hxA, rfl⟩ := Finset.mem_map.mp hy
        exact (mem_filter.mp hxA).2
      have hA : A.card ≤ 3 := by
        rw [← card_map (cycleCoverRootEmbedding V)]
        exact (card_le_card hmapSubset).trans_eq T.2
      change A.card ≤ 14
      omega

lemma core_root_mem_fiber_of_sphereOut_adj
    {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q) {a : V} {R : TripleOn V}
    {z : SphereInterior q}
    (haz : (sphereTransformOutGraph V hq).Adj
      (SphereExpansionVertex.root a)
      (SphereExpansionVertex.interior R z)) :
    a ∈ R.1 := by
  change (coveredGraph (sphereTransform hq
    (∅ : TripleSystemOn V))).Adj _ _ at haz
  obtain ⟨T, A, hAfam, haA, hzA, hazne⟩ :=
    (coveredGraph_sphereTransform_adj_iff hq
      (∅ : TripleSystemOn V) _ _).mp haz
  obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hAfam
  have hRT : R = T :=
    (interior_mem_attachSphereTriple_iff hq T R z S).mp hzA |>.1
  subst R
  exact root_mem_of_mem_attachSphereTriple hq T S a haA

lemma root_mem_highGirthOriginalRootCandidates_of_adj
    (V : Type*) [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) {x : V}
    {v : HighGirthCycleCoverVertex V q}
    (hxv : (highGirthCycleCoverGraph V hq).Adj
      (highGirthCycleCoverRootEmbedding V q x) v) :
    x ∈ highGirthOriginalRootCandidates V v := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  change ((sphereTransformOutGraph (CycleCoverAbsorberVertex V) hq ⊔
      (cycleCoverAbsorberGraph V).map
        (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q))).Adj
    (SphereExpansionVertex.root (cycleCoverRootEmbedding V x)) v at hxv
  rw [SimpleGraph.sup_adj] at hxv
  rcases hxv with hxv | hxv
  · cases v with
    | root b =>
        exact (sphereTransformOutGraph_not_adj_root_root hq _ _ hxv).elim
    | interior T z =>
        exact mem_filter.mpr ⟨mem_univ x,
          core_root_mem_fiber_of_sphereOut_adj hq hxv⟩
  · rw [SimpleGraph.map_adj] at hxv
    obtain ⟨a, b, hab, ha, hb⟩ := hxv
    have haRoot : a = cycleCoverRootEmbedding V x := by
      apply (sphereExpansionRootEmbedding
        (CycleCoverAbsorberVertex V) q).injective
      exact ha
    subst a
    cases v with
    | root c =>
        have hbRoot : b = c :=
          SphereExpansionVertex.root.inj hb
        subst b
        exact root_mem_cycleCoverCoreRootCandidates_of_adj V hab
    | interior T z => cases hb

/-- Transport the high-girth root candidates through a padding embedding.
Vertices outside the padded absorber have no candidates. -/
noncomputable def mappedHighGirthOriginalRootCandidates
    {V W : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq W] {q : ℕ}
    (f : HighGirthCycleCoverVertex V q ↪ W) (y : W) : Finset V := by
  classical
  exact if hy : ∃ z, f z = y then
    highGirthOriginalRootCandidates V (Classical.choose hy)
  else ∅

lemma mappedHighGirthOriginalRootCandidates_apply
    {V W : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq W] {q : ℕ}
    (f : HighGirthCycleCoverVertex V q ↪ W)
    (z : HighGirthCycleCoverVertex V q) :
    mappedHighGirthOriginalRootCandidates f (f z) =
      highGirthOriginalRootCandidates V z := by
  rw [mappedHighGirthOriginalRootCandidates, dif_pos ⟨z, rfl⟩]
  have hz : Classical.choose
      (show ∃ w, f w = f z from ⟨z, rfl⟩) = z := by
    apply f.injective
    exact Classical.choose_spec
      (show ∃ w, f w = f z from ⟨z, rfl⟩)
  rw [hz]

lemma card_mappedHighGirthOriginalRootCandidates_le_fourteen
    {V W : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq W] {q : ℕ}
    (f : HighGirthCycleCoverVertex V q ↪ W) (y : W) :
    (mappedHighGirthOriginalRootCandidates f y).card ≤ 14 := by
  rw [mappedHighGirthOriginalRootCandidates]
  split_ifs with hy
  · exact card_highGirthOriginalRootCandidates_le_fourteen V _
  · simp

lemma root_mem_mappedHighGirthCandidates_of_map_adj
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {q : ℕ} (hq : 2 ≤ q)
    (f : HighGirthCycleCoverVertex V q ↪ W)
    {x : V} {y : W}
    (hxy : ((highGirthCycleCoverGraph V hq).map f).Adj
      (f (highGirthCycleCoverRootEmbedding V q x)) y) :
    x ∈ mappedHighGirthOriginalRootCandidates f y := by
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨a, b, hab, ha, hb⟩ := hxy
  have haRoot : a = highGirthCycleCoverRootEmbedding V q x :=
    f.injective ha
  subst a
  rw [← hb, mappedHighGirthOriginalRootCandidates_apply]
  exact root_mem_highGirthOriginalRootCandidates_of_adj V hq hab

/-- Pull the two endpoint sphere-fiber candidate sets back to original
cycle-cover roots. -/
noncomputable def mappedHighGirthPairOriginalRootCandidates
    {V W : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq W] {q : ℕ}
    (f : HighGirthCycleCoverVertex V q ↪ W) (u v : W) : Finset V := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  letI : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  exact univ.filter fun x ↦ cycleCoverRootEmbedding V x ∈
    mappedSpherePairRootCandidates f u v

lemma card_mappedHighGirthPairOriginalRootCandidates_le_six
    {V W : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq W] {q : ℕ}
    (f : HighGirthCycleCoverVertex V q ↪ W) (u v : W) :
    (mappedHighGirthPairOriginalRootCandidates f u v).card ≤ 6 := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  let A := mappedHighGirthPairOriginalRootCandidates f u v
  have hmapSubset : A.map (cycleCoverRootEmbedding V) ⊆
      mappedSpherePairRootCandidates f u v := by
    intro y hy
    obtain ⟨x, hxA, rfl⟩ := Finset.mem_map.mp hy
    exact (mem_filter.mp hxA).2
  rw [← card_map (cycleCoverRootEmbedding V)]
  exact (card_le_card hmapSubset).trans
    (card_mappedSpherePairRootCandidates_le_six f u v)

lemma root_mem_mappedHighGirthPairCandidates_of_bank
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {q : ℕ} (hq : 2 ≤ q)
    (f : HighGirthCycleCoverVertex V q ↪ W)
    {u v : W} (huv : u ≠ v) (w : ThirdVertex u v) (x : V)
    (hw : w.1 = f (highGirthCycleCoverRootEmbedding V q x))
    (hbank : thirdVertexTriple huv w ∈
      mapTripleSystem f
        (highGirthCycleCoverBank V hq)) :
    x ∈ mappedHighGirthPairOriginalRootCandidates f u v := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  apply mem_filter.mpr
  refine ⟨mem_univ x, ?_⟩
  exact root_mem_pairCandidates_of_thirdVertexTriple_mem_bank
    hq f huv w (cycleCoverRootEmbedding V x) hw hbank

lemma root_mem_mappedHighGirthPairCandidates_of_forbidden
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {q q₀ : ℕ}
    (hq : 2 ≤ q) (hq₀q : q₀ ≤ q)
    (f : HighGirthCycleCoverVertex V q ↪ W)
    {B : TripleSystemOn W}
    (hB : B ⊆ mapTripleSystem f (highGirthCycleCoverBank V hq))
    {u v : W} (huv : u ≠ v) (w : ThirdVertex u v) (x : V)
    (hw : w.1 = f (highGirthCycleCoverRootEmbedding V q x))
    (hcomplete : CompletesForbidden
      (absorberErdosForbiddenConfigurationsOn q₀ B) ∅
      (thirdVertexTriple huv w)) :
    x ∈ mappedHighGirthPairOriginalRootCandidates f u v := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  apply mem_filter.mpr
  refine ⟨mem_univ x, ?_⟩
  exact root_mem_pairCandidates_of_thirdVertexTriple_forbidden
    hq hq₀q f hB huv w (cycleCoverRootEmbedding V x) hw hcomplete

end

end Erdos207
