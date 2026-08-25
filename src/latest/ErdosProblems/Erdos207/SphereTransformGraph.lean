/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Data.Fintype.Order
import ErdosProblems.Erdos207.CycleCoverAbsorber
import ErdosProblems.Erdos207.SphereExpansion

/-!
# The graph covered by the simultaneous sphere transform

This file identifies the graph covered by the simultaneous high-girth sphere
transform.  Its out-part is fixed, and changing a root triple from the out-side
to the in-side adds exactly the three edges of that root triple.
-/

namespace Erdos207

open Finset

noncomputable section

def sphereExpansionRootEmbedding (V : Type*) (q : ℕ) :
    V ↪ SphereExpansionVertex V q where
  toFun := SphereExpansionVertex.root
  inj' _ _ h := SphereExpansionVertex.root.inj h

lemma coveredGraph_sphereTransform_adj_iff
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (C : TripleSystemOn V) (x y : SphereExpansionVertex V q) :
    (coveredGraph (sphereTransform hq C)).Adj x y ↔
      ∃ T : TripleOn V,
        (coveredGraph (attachSphereFamily hq T
          (sphereDecomposition hq (decide (T ∈ C))))).Adj x y := by
  constructor
  · rintro ⟨U, hU, hxU, hyU, hxy⟩
    obtain ⟨T, hUT⟩ := (mem_sphereTransform_iff hq C U).mp hU
    exact ⟨T, U, hUT, hxU, hyU, hxy⟩
  · rintro ⟨T, U, hUT, hxU, hyU, hxy⟩
    exact ⟨U, (mem_sphereTransform_iff hq C U).mpr ⟨T, hUT⟩,
      hxU, hyU, hxy⟩

lemma coveredGraph_attachedSphere_interior_left
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) (inward : Bool) (R : TripleOn V)
    (z : SphereInterior q) (y : SphereExpansionVertex V q) :
    (coveredGraph (attachSphereFamily hq T
      (sphereDecomposition hq inward))).Adj
        (SphereExpansionVertex.interior R z) y ↔
      (coveredGraph (attachSphereFamily hq T
        (sphereDecomposition hq false))).Adj
          (SphereExpansionVertex.interior R z) y := by
  change
    (coveredGraph (mapTripleSystem (attachSphereEmbedding hq T)
      (sphereDecomposition hq inward))).Adj
        (SphereExpansionVertex.interior R z) y ↔
    (coveredGraph (mapTripleSystem (attachSphereEmbedding hq T)
      (sphereDecomposition hq false))).Adj
        (SphereExpansionVertex.interior R z) y
  rw [coveredGraph_mapTripleSystem, coveredGraph_mapTripleSystem]
  cases inward with
  | false => rfl
  | true =>
      rw [sphere_switch_coveredGraph_eq hq,
        SimpleGraph.map_sup_embedding, SimpleGraph.sup_adj]
      constructor
      · rintro (hout | hroot)
        · exact hout
        · rw [SimpleGraph.map_adj] at hroot
          obtain ⟨a, b, hab, ha, hb⟩ := hroot
          obtain ⟨U, hU, haU, hbU, habne⟩ := hab
          simp only [mem_singleton] at hU
          subst U
          have haCases :
              a = SphereVertex.pole true ∨
              a = SphereVertex.cycle ⟨0, by omega⟩ ∨
              a = SphereVertex.cycle ⟨1, by omega⟩ := by
            simpa [sphereRootTriple] using haU
          rcases haCases with rfl | rfl | rfl <;>
            simp [attachSphereEmbedding, attachSphereVertex] at ha
      · exact Or.inl

lemma coveredGraph_attachedSphere_interior_right
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) (inward : Bool) (x : SphereExpansionVertex V q)
    (R : TripleOn V) (z : SphereInterior q) :
    (coveredGraph (attachSphereFamily hq T
      (sphereDecomposition hq inward))).Adj x
        (SphereExpansionVertex.interior R z) ↔
      (coveredGraph (attachSphereFamily hq T
        (sphereDecomposition hq false))).Adj x
          (SphereExpansionVertex.interior R z) := by
  simpa only [SimpleGraph.adj_comm] using
    coveredGraph_attachedSphere_interior_left hq T inward R z x

/-- The graph covered by the all-out simultaneous transform. -/
def sphereTransformOutGraph
    (V : Type*) [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q) :
    SimpleGraph (SphereExpansionVertex V q) :=
  coveredGraph (sphereTransform hq (∅ : TripleSystemOn V))

/-- The simultaneous sphere transform covers its fixed all-out graph together
with exactly the graph covered by the selected root triples. -/
theorem coveredGraph_sphereTransform_eq
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (C : TripleSystemOn V) :
    coveredGraph (sphereTransform hq C) =
      sphereTransformOutGraph V hq ⊔
        (coveredGraph C).map (sphereExpansionRootEmbedding V q) := by
  ext x y
  cases x with
  | interior R z =>
      simp only [SimpleGraph.sup_adj]
      rw [coveredGraph_sphereTransform_adj_iff]
      constructor
      · rintro ⟨T, hT⟩
        left
        change (coveredGraph (sphereTransform hq
          (∅ : TripleSystemOn V))).Adj _ _
        rw [coveredGraph_sphereTransform_adj_iff]
        refine ⟨T, ?_⟩
        simpa using
          (coveredGraph_attachedSphere_interior_left hq T
            (decide (T ∈ C)) R z y).mp hT
      · rintro (hout | hroot)
        · change (coveredGraph (sphereTransform hq
              (∅ : TripleSystemOn V))).Adj _ _ at hout
          rw [coveredGraph_sphereTransform_adj_iff] at hout
          obtain ⟨T, hT⟩ := hout
          refine ⟨T, ?_⟩
          have hTfalse :
              (coveredGraph (attachSphereFamily hq T
                (sphereDecomposition hq false))).Adj
                  (SphereExpansionVertex.interior R z) y := by
            simpa using hT
          exact (coveredGraph_attachedSphere_interior_left hq T
            (decide (T ∈ C)) R z y).mpr hTfalse
        · rw [SimpleGraph.map_adj] at hroot
          obtain ⟨a, b, hab, ha, hb⟩ := hroot
          cases ha
  | root a =>
      cases y with
      | interior R z =>
          simp only [SimpleGraph.sup_adj]
          rw [coveredGraph_sphereTransform_adj_iff]
          constructor
          · rintro ⟨T, hT⟩
            left
            change (coveredGraph (sphereTransform hq
              (∅ : TripleSystemOn V))).Adj _ _
            rw [coveredGraph_sphereTransform_adj_iff]
            refine ⟨T, ?_⟩
            exact (coveredGraph_attachedSphere_interior_right hq T
              (decide (T ∈ C)) (SphereExpansionVertex.root a) R z).mp hT
          · rintro (hout | hroot)
            · change (coveredGraph (sphereTransform hq
                  (∅ : TripleSystemOn V))).Adj _ _ at hout
              rw [coveredGraph_sphereTransform_adj_iff] at hout
              obtain ⟨T, hT⟩ := hout
              refine ⟨T, ?_⟩
              have hTfalse :
                  (coveredGraph (attachSphereFamily hq T
                    (sphereDecomposition hq false))).Adj
                      (SphereExpansionVertex.root a)
                        (SphereExpansionVertex.interior R z) := by
                simpa using hT
              exact (coveredGraph_attachedSphere_interior_right hq T
                (decide (T ∈ C)) (SphereExpansionVertex.root a) R z).mpr hTfalse
            · rw [SimpleGraph.map_adj] at hroot
              obtain ⟨u, v, huv, hu, hv⟩ := hroot
              cases hv
      | root b =>
          simp only [SimpleGraph.sup_adj]
          rw [coveredGraph_sphereTransform_adj_iff]
          constructor
          · rintro ⟨T, hT⟩
            have hdata :=
              (attachedSphere_root_adj_iff hq T
                (decide (T ∈ C)) a b).mp hT
            right
            rw [SimpleGraph.map_adj]
            refine ⟨a, b, ?_, rfl, rfl⟩
            exact ⟨T, by simpa using hdata.1, hdata.2.1,
              hdata.2.2.1, hdata.2.2.2⟩
          · rintro (hout | hroot)
            · change (coveredGraph (sphereTransform hq
                  (∅ : TripleSystemOn V))).Adj _ _ at hout
              rw [coveredGraph_sphereTransform_adj_iff] at hout
              obtain ⟨T, hT⟩ := hout
              have hfalse :=
                (attachedSphere_root_adj_iff hq T false a b).mp hT
              simp at hfalse
            · rw [SimpleGraph.map_adj] at hroot
              obtain ⟨u, v, huv, hu, hv⟩ := hroot
              have hua : u = a := SphereExpansionVertex.root.inj hu
              have hvb : v = b := SphereExpansionVertex.root.inj hv
              subst u
              subst v
              obtain ⟨T, hTC, haT, hbT, hab⟩ := huv
              refine ⟨T, ?_⟩
              exact (attachedSphere_root_adj_iff hq T
                (decide (T ∈ C)) a b).mpr
                  ⟨by simpa using hTC, haT, hbT, hab⟩

abbrev HighGirthCycleCoverVertex
    (V : Type*) [Fintype V] (q : ℕ) :=
  SphereExpansionVertex (CycleCoverAbsorberVertex V) q

def highGirthCycleCoverRootEmbedding
    (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    V ↪ HighGirthCycleCoverVertex V q :=
  (cycleCoverRootEmbedding V).trans
    (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q)

/-- The fixed high-girth absorber graph obtained by applying the sphere
transform to the path/full-cycle-cover absorber. -/
noncomputable def highGirthCycleCoverGraph
    (V : Type*) [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) :
    SimpleGraph (HighGirthCycleCoverVertex V q) := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  letI : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  exact
    sphereTransformOutGraph (CycleCoverAbsorberVertex V) hq ⊔
      (cycleCoverAbsorberGraph V).map
        (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q)

/-- Every triangle-divisible graph on the root type is absorbed by the fixed
graph, and the resulting triangle decomposition has girth greater than `q`. -/
theorem highGirthCycleCover_absorbs
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : TriangleDivisible G) :
    ∃ C : TripleSystemOn (HighGirthCycleCoverVertex V q),
      IsHighGirthTriangleDecomposition q
        (highGirthCycleCoverGraph V hq ⊔
          G.map (highGirthCycleCoverRootEmbedding V q)) C := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  letI : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  obtain ⟨C₀, hC₀⟩ := cycleCoverAbsorber_absorbs hV G hG
  let C := sphereTransform hq C₀
  have hpacking : IsPackingOn C :=
    sphereTransform_isPacking hq hC₀.isPackingOn
  refine ⟨C, ?_, sphereTransform_girthGreater hq hC₀.isPackingOn⟩
  have hcover := coveredGraph_sphereTransform_eq hq C₀
  have hC₀cover : coveredGraph C₀ =
      cycleCoverAbsorberGraph V ⊔
        G.map (cycleCoverRootEmbedding V) := hC₀.coveredGraph_eq
  rw [hC₀cover, SimpleGraph.map_sup_embedding,
    SimpleGraph.map_map] at hcover
  change IsTriangleDecomposition
    ((sphereTransformOutGraph (CycleCoverAbsorberVertex V) hq ⊔
        (cycleCoverAbsorberGraph V).map
          (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q)) ⊔
      G.map ((cycleCoverRootEmbedding V).trans
        (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q))) C
  have hrootMap :
      G.map ((cycleCoverRootEmbedding V).trans
        (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q)) =
      G.map ((sphereExpansionRootEmbedding
        (CycleCoverAbsorberVertex V) q :
          CycleCoverAbsorberVertex V →
            HighGirthCycleCoverVertex V q) ∘
        (cycleCoverRootEmbedding V : V → CycleCoverAbsorberVertex V)) := by
    rfl
  have hgraph :
      ((sphereTransformOutGraph (CycleCoverAbsorberVertex V) hq ⊔
          (cycleCoverAbsorberGraph V).map
            (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q)) ⊔
        G.map ((cycleCoverRootEmbedding V).trans
          (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q))) =
        coveredGraph C := by
    rw [hrootMap, hcover]
    ac_rfl
  rw [hgraph]
  exact hpacking.isTriangleDecomposition

end

end Erdos207
