/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.CardEmbedding
import ErdosProblems.Erdos207.SphereTransformGraph

/-!
# The efficient high-girth absorber interface

This file packages the explicit path-cover, bounded cycle-cover, and sphere
constructions into the two properties used by the KSSS iteration: exact
high-girth absorption and localization of the finite absorber bank.
-/

namespace Erdos207

open Finset

noncomputable section

noncomputable instance sphereInteriorFintype (q : ℕ) :
    Fintype (SphereInterior q) := Fintype.ofFinite _

lemma fullCycleCoverOutGraph_not_adj_base_base
    {V : Type*} [Fintype V] [DecidableEq V]
    (a b : CycleCoverPathVertex V) :
    ¬(fullCycleCoverOutGraph V).Adj (Sum.inl a) (Sum.inl b) := by
  have hnone : ∀ s : Finset (FullCycleCoverCopy (CycleCoverPathVertex V)),
      ¬(graphSup s (fun i ↦ coveredGraph (fullCycleCoverOut i))).Adj
        (Sum.inl a) (Sum.inl b) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [graphSup_insert, SimpleGraph.sup_adj]
        push Not
        refine ⟨?_, ih⟩
        intro hi
        have hstructure := fullCycleCoverOut_edge_structure i hi
        simpa [IsPrivateForFullCycleCoverCopy] using hstructure.2.2
  exact hnone univ

lemma embeddedPathCoverGraph_not_adj_root_root
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V) :
    ¬(embeddedPathCoverGraph V).Adj
      (cycleCoverRootEmbedding V a) (cycleCoverRootEmbedding V b) := by
  intro hab
  rw [embeddedPathCoverGraph, SimpleGraph.map_adj] at hab
  obtain ⟨x, y, hxy, hx, hy⟩ := hab
  have hx' : x = PathCoverVertex.root a := by
    exact (fullCycleCoverBaseEmbedding
      (CycleCoverPathVertex V)).injective hx
  have hy' : y = PathCoverVertex.root b := by
    exact (fullCycleCoverBaseEmbedding
      (CycleCoverPathVertex V)).injective hy
  subst x
  subst y
  exact pathCoverGraph_not_adj_root_root a b hxy

lemma cycleCoverAbsorberGraph_not_adj_root_root
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V) :
    ¬(cycleCoverAbsorberGraph V).Adj
      (cycleCoverRootEmbedding V a) (cycleCoverRootEmbedding V b) := by
  rw [cycleCoverAbsorberGraph, SimpleGraph.sup_adj]
  push_neg
  constructor
  · exact fullCycleCoverOutGraph_not_adj_base_base
      (PathCoverVertex.root a) (PathCoverVertex.root b)
  · exact embeddedPathCoverGraph_not_adj_root_root a b

/-- The finite union of the two sides of every sphere attached to a triple. -/
def sphereTransformBank
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q) :
    TripleSystemOn (SphereExpansionVertex V q) :=
  (univ : Finset (TripleOn V)).biUnion fun T ↦
    attachSphereFamily hq T (sphereBank hq)

lemma sphereTransform_subset_bank
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (C : TripleSystemOn V) :
    sphereTransform hq C ⊆ sphereTransformBank hq := by
  intro U hU
  obtain ⟨T, hUT⟩ := (mem_sphereTransform_iff hq C U).mp hU
  simp only [sphereTransformBank, mem_biUnion]
  obtain ⟨S, hSselected, rfl⟩ := Finset.mem_map.mp hUT
  refine ⟨T, mem_univ T, Finset.mem_map.mpr ⟨S, ?_, rfl⟩⟩
  exact sphereDecomposition_subset_bank hq _ hSselected

lemma sphereTransformOutGraph_not_adj_root_root
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (a b : V) :
    ¬(sphereTransformOutGraph V hq).Adj
      (SphereExpansionVertex.root a) (SphereExpansionVertex.root b) := by
  intro hab
  change (coveredGraph (sphereTransform hq
    (∅ : TripleSystemOn V))).Adj _ _ at hab
  obtain ⟨T, hT⟩ :=
    (coveredGraph_sphereTransform_adj_iff hq
      (∅ : TripleSystemOn V) _ _).mp hab
  have hfalse := (attachedSphere_root_adj_iff hq T
    (decide (T ∈ (∅ : TripleSystemOn V))) a b).mp hT
  simpa using hfalse.1

def highGirthCycleCoverRoots
    (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Finset (HighGirthCycleCoverVertex V q) :=
  univ.map (highGirthCycleCoverRootEmbedding V q)

lemma highGirthCycleCoverGraph_not_adj_root_root
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) (a b : V) :
    ¬(highGirthCycleCoverGraph V hq).Adj
      (highGirthCycleCoverRootEmbedding V q a)
      (highGirthCycleCoverRootEmbedding V q b) := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  change ¬((sphereTransformOutGraph (CycleCoverAbsorberVertex V) hq ⊔
      (cycleCoverAbsorberGraph V).map
        (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q))).Adj
    (SphereExpansionVertex.root (cycleCoverRootEmbedding V a))
    (SphereExpansionVertex.root (cycleCoverRootEmbedding V b))
  rw [SimpleGraph.sup_adj]
  push_neg
  exact ⟨sphereTransformOutGraph_not_adj_root_root hq _ _, by
    change ¬((cycleCoverAbsorberGraph V).map
      (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q)).Adj
        (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q
          (cycleCoverRootEmbedding V a))
        (sphereExpansionRootEmbedding (CycleCoverAbsorberVertex V) q
          (cycleCoverRootEmbedding V b))
    rw [SimpleGraph.map_adj_apply]
    exact cycleCoverAbsorberGraph_not_adj_root_root a b⟩

lemma highGirthCycleCoverRoots_card
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) :
    (highGirthCycleCoverRoots V q).card = Fintype.card V := by
  simp [highGirthCycleCoverRoots]

lemma SimpleGraph.map_comap_eq_of_supportedOn_range
    {A W : Type*} [DecidableEq A] [DecidableEq W]
    (f : A ↪ W) (G : SimpleGraph W)
    (hG : GraphSupportedOn G (Set.range f)) :
    (G.comap f).map f = G := by
  apply le_antisymm (SimpleGraph.map_comap_le f G)
  intro x y hxy
  obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hG hxy
  exact SimpleGraph.map_adj_apply.mpr hxy

lemma TriangleDivisible.of_map
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    (G : SimpleGraph A) [DecidableRel G.Adj] (f : A ↪ W)
    (hG : TriangleDivisible (G.map f)) : TriangleDivisible G := by
  constructor
  · intro v
    have hv := hG.1 (f v)
    have hneighbors :
        (G.map f).neighborFinset (f v) = (G.neighborFinset v).map f := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, mem_map]
      constructor
      · intro hw
        rw [SimpleGraph.map_adj] at hw
        obtain ⟨a, b, hab, ha, hb⟩ := hw
        have hav : a = v := f.injective ha
        subst a
        exact ⟨b, hab, hb⟩
      · rintro ⟨b, hb, rfl⟩
        exact SimpleGraph.map_adj_apply.mpr hb
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      hneighbors, card_map,
      SimpleGraph.card_neighborFinset_eq_degree] at hv
    exact hv
  · simpa [SimpleGraph.card_edgeFinset_map] using hG.2

/-- The concrete construction already satisfies the exact high-girth
absorption property before it is transported to an initial segment `Fin N`. -/
theorem highGirthCycleCover_hasAbsorptionProperty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V) :
    HasHighGirthAbsorptionProperty q
      (highGirthCycleCoverGraph V hq)
      (highGirthCycleCoverRoots V q) := by
  constructor
  · intro u hu v hv huv
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_map.mp hv
    exact highGirthCycleCoverGraph_not_adj_root_root hq a b
  · intro L _ hLsupported hLdiv
    let f := highGirthCycleCoverRootEmbedding V q
    let G := L.comap f
    have hsuppRange : GraphSupportedOn L (Set.range f) := by
      intro u v huv
      obtain ⟨hu, hv⟩ := hLsupported huv
      constructor
      · obtain ⟨a, _ha, hau⟩ := Finset.mem_map.mp hu
        exact ⟨a, hau⟩
      · obtain ⟨b, _hb, hbv⟩ := Finset.mem_map.mp hv
        exact ⟨b, hbv⟩
    have hmap : G.map f = L :=
      SimpleGraph.map_comap_eq_of_supportedOn_range f L hsuppRange
    have hGdiv : TriangleDivisible G := by
      apply TriangleDivisible.of_map G f
      simpa only [hmap] using hLdiv
    obtain ⟨C, hC⟩ := highGirthCycleCover_absorbs hq hV G hGdiv
    refine ⟨C, ?_⟩
    have hrootMap :
        G.map (highGirthCycleCoverRootEmbedding V q) = L := by
      simpa only [f] using hmap
    simpa only [hrootMap] using hC

lemma sphereBank_card_le {q : ℕ} (hq : 2 ≤ q) :
    (sphereBank hq).card ≤ 4 * q := by
  calc
    (sphereBank hq).card ≤
        (univ : Finset (ConcreteSphereTag q)).card := by
      exact card_image_le
    _ = Fintype.card (ConcreteSphereTag q) := card_univ
    _ ≤ Fintype.card (Fin (2 * q) × Bool) := Fintype.card_subtype_le _
    _ = 4 * q := by simp; omega

lemma attachSphereFamily_bank_card_le
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) :
    (attachSphereFamily hq T (sphereBank hq)).card ≤ 4 * q := by
  rw [attachSphereFamily_card]
  exact sphereBank_card_le hq

def sphereVertexLocalBank
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q) :
    SphereExpansionVertex V q →
      TripleSystemOn (SphereExpansionVertex V q)
  | .root _ => ∅
  | .interior T _ => attachSphereFamily hq T (sphereBank hq)

/-- All sphere fibers whose private vertices are touched by `R`.  Writing it
as a union over the vertices of `R` gives the sharp elementary size bound. -/
def sphereLocalFamily
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (R : TripleSystemOn (SphereExpansionVertex V q)) :
    TripleSystemOn (SphereExpansionVertex V q) :=
  R.biUnion fun U ↦ U.1.biUnion (sphereVertexLocalBank hq)

lemma sphereVertexLocalBank_card_le
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (x : SphereExpansionVertex V q) :
    (sphereVertexLocalBank hq x).card ≤ 4 * q := by
  cases x with
  | root a => simp [sphereVertexLocalBank]
  | interior T z =>
      exact attachSphereFamily_bank_card_le hq T

lemma sphereLocalFamily_card_le
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (R : TripleSystemOn (SphereExpansionVertex V q))
    (hRq : R.card ≤ q) :
    (sphereLocalFamily hq R).card ≤ 12 * q ^ 2 := by
  calc
    (sphereLocalFamily hq R).card ≤
        ∑ U ∈ R, (U.1.biUnion (sphereVertexLocalBank hq)).card :=
      card_biUnion_le
    _ ≤ ∑ U ∈ R, ∑ x ∈ U.1, (4 * q) := by
      apply Finset.sum_le_sum
      intro U hUR
      exact card_biUnion_le.trans
        (Finset.sum_le_sum fun x _ ↦ sphereVertexLocalBank_card_le hq x)
    _ = ∑ _U ∈ R, 3 * (4 * q) := by
      apply Finset.sum_congr rfl
      intro U hUR
      simp [U.2]
    _ = R.card * (3 * (4 * q)) := by simp
    _ ≤ q * (3 * (4 * q)) := Nat.mul_le_mul_right _ hRq
    _ = 12 * q ^ 2 := by ring

lemma sphereFiber_subset_localFamily_of_interior_mem
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    {R : TripleSystemOn (SphereExpansionVertex V q)}
    (T : TripleOn V) (z : SphereInterior q)
    (hz : SphereExpansionVertex.interior T z ∈ verticesOn R) :
    attachSphereFamily hq T (sphereBank hq) ⊆ sphereLocalFamily hq R := by
  obtain ⟨U, hUR, hzU⟩ := mem_biUnion.mp hz
  intro A hA
  simp only [sphereLocalFamily, mem_biUnion]
  refine ⟨U, hUR, SphereExpansionVertex.interior T z, hzU, ?_⟩
  simpa [sphereVertexLocalBank] using hA

lemma sphereBank_mem_decomposition
    {q : ℕ} (hq : 2 ≤ q) {S : TripleOn (SphereVertex q)}
    (hS : S ∈ sphereBank hq) :
    S ∈ sphereDecomposition hq true ∨
      S ∈ sphereDecomposition hq false := by
  obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hS
  by_cases hphase : t.1.2 = spherePhase t.1.1
  · left
    exact (mem_sphereDecomposition_iff hq).mpr
      ⟨t, (sphereTagSelected_true_iff t).mpr hphase, rfl⟩
  · right
    have hnot : t.1.2 = !spherePhase t.1.1 := by
      cases ht : t.1.2 <;> cases hp : spherePhase t.1.1 <;>
        simp_all
    exact (mem_sphereDecomposition_iff hq).mpr
      ⟨t, (sphereTagSelected_false_iff t).mpr hnot, rfl⟩

lemma sphereBank_interior_edge_in_outGraph
    {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q) (T : TripleOn V)
    {A : TripleOn (SphereExpansionVertex V q)}
    (hA : A ∈ attachSphereFamily hq T (sphereBank hq))
    {z : SphereInterior q}
    (hzA : SphereExpansionVertex.interior T z ∈ A.1)
    {y : SphereExpansionVertex V q} (hyA : y ∈ A.1)
    (hzy : SphereExpansionVertex.interior T z ≠ y) :
    (sphereTransformOutGraph V hq).Adj
      (SphereExpansionVertex.interior T z) y := by
  obtain ⟨S, hSbank, rfl⟩ := Finset.mem_map.mp hA
  rcases sphereBank_mem_decomposition hq hSbank with hSin | hSout
  · have hin :
        (coveredGraph (attachSphereFamily hq T
          (sphereDecomposition hq true))).Adj
            (SphereExpansionVertex.interior T z) y :=
      ⟨attachSphereTriple hq T S,
        (mem_mapTripleSystem_iff (attachSphereEmbedding hq T) _ S).mpr hSin,
        hzA, hyA, hzy⟩
    have hout := (coveredGraph_attachedSphere_interior_left
      hq T true T z y).mp hin
    change (coveredGraph (sphereTransform hq
      (∅ : TripleSystemOn V))).Adj _ _
    exact (coveredGraph_sphereTransform_adj_iff hq
      (∅ : TripleSystemOn V) _ _).mpr ⟨T, by simpa using hout⟩
  · have hout :
        (coveredGraph (attachSphereFamily hq T
          (sphereDecomposition hq false))).Adj
            (SphereExpansionVertex.interior T z) y :=
      ⟨attachSphereTriple hq T S,
        (mem_mapTripleSystem_iff (attachSphereEmbedding hq T) _ S).mpr hSout,
        hzA, hyA, hzy⟩
    change (coveredGraph (sphereTransform hq
      (∅ : TripleSystemOn V))).Adj _ _
    exact (coveredGraph_sphereTransform_adj_iff hq
      (∅ : TripleSystemOn V) _ _).mpr ⟨T, by simpa using hout⟩

lemma IsErdosConfig.isPackingOn
    {W : Type*} [DecidableEq W] {r : ℕ}
    {E : TripleSystemOn W} (hE : IsErdosConfigOn r E) (hr : 5 ≤ r) :
    IsPackingOn E := by
  intro u v huv T hTE huT hvT U hUE huU hvU
  by_contra hTU
  apply hE.2 4 (by omega) (by omega)
  refine ⟨{T, U}, ?_, ?_⟩
  · intro A hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl <;> assumption
  · constructor
    · simp [hTU]
    · have hinter' : 1 < (T.1 ∩ U.1).card :=
        Finset.one_lt_card.mpr
          ⟨u, Finset.mem_inter.mpr ⟨huT, huU⟩,
            v, Finset.mem_inter.mpr ⟨hvT, hvU⟩, huv⟩
      have hinter : 2 ≤ (T.1 ∩ U.1).card := by omega
      have hunion := Finset.card_union_add_card_inter T.1 U.1
      have hvertices :
          verticesOn ({T, U} : TripleSystemOn W) = T.1 ∪ U.1 := by
        simp [verticesOn]
      rw [hvertices]
      rw [T.2, U.2] at hunion
      omega

lemma sphereTransformBank_interior_fiber
    {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q)
    {A : TripleOn (SphereExpansionVertex V q)}
    (hA : A ∈ sphereTransformBank hq)
    (T : TripleOn V) (z : SphereInterior q)
    (hzA : SphereExpansionVertex.interior T z ∈ A.1) :
    A ∈ attachSphereFamily hq T (sphereBank hq) := by
  obtain ⟨R, _hR, hAR⟩ := mem_biUnion.mp hA
  obtain ⟨S, hSbank, rfl⟩ := Finset.mem_map.mp hAR
  have hRT :=
    (interior_mem_attachSphereTriple_iff hq R T z S).mp hzA |>.1
  subst R
  exact (mem_mapTripleSystem_iff (attachSphereEmbedding hq T)
    (sphereBank hq) S).mpr hSbank

/-- Fiber-locality of the universal sphere bank.  This is the complete (A2)
argument: a nonlocal bank triangle supplies a private interior leaf; unless a
new non-bank triangle uses that leaf, minimality of an Erdős configuration is
contradicted. -/
theorem sphereTransformBank_hasLocalization
    {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q)
    (H : SimpleGraph (SphereExpansionVertex V q))
    (hOut : sphereTransformOutGraph V hq ≤ H)
    (X : Finset (SphereExpansionVertex V q))
    (hXroots : ∀ x ∈ X, ∃ a : V, x = SphereExpansionVertex.root a) :
    HasAbsorberLocalization q (12 * q ^ 2) H X
      (sphereTransformBank hq) := by
  intro K hHK R hRq hRtri
  let L_R := sphereLocalFamily hq R
  have hLRB : L_R ⊆ sphereTransformBank hq := by
    intro A hA
    obtain ⟨U, hUR, x, hxU, hAx⟩ := by
      simpa only [L_R, sphereLocalFamily, mem_biUnion] using hA
    cases x with
    | root a => simp [sphereVertexLocalBank] at hAx
    | interior T z =>
        simp only [sphereVertexLocalBank] at hAx
        simp only [sphereTransformBank, mem_biUnion]
        exact ⟨T, mem_univ T, hAx⟩
  refine ⟨L_R, hLRB, sphereLocalFamily_card_le hq R hRq, ?_⟩
  intro r hr5 hrq E hE hRE
  by_cases hlocal : E ∩ sphereTransformBank hq ⊆ L_R
  · exact Or.inl hlocal
  · right
    rw [not_subset] at hlocal
    obtain ⟨A, hAEB, hAnotLocal⟩ := hlocal
    have hAE : A ∈ E := (mem_inter.mp hAEB).1
    have hAB : A ∈ sphereTransformBank hq := (mem_inter.mp hAEB).2
    obtain ⟨T, _hTuniv, hAfiber⟩ := by
      simpa only [sphereTransformBank, mem_biUnion] using hAB
    let D : TripleSystemOn (SphereExpansionVertex V q) :=
      E.filter fun S ↦ S ∈ attachSphereFamily hq T (sphereBank hq)
    have hDfiber : D ⊆ attachSphereFamily hq T (sphereBank hq) := by
      intro S hSD
      exact (mem_filter.mp hSD).2
    have hDE : D ⊆ E := filter_subset _ _
    have hAinD : A ∈ D := mem_filter.mpr ⟨hAE, hAfiber⟩
    have hDne : D.Nonempty := ⟨A, hAinD⟩
    have hDcard : D.card ≤ q := by
      calc
        D.card ≤ E.card := card_le_card hDE
        _ = r - 2 := hE.1.1
        _ ≤ q := by omega
    have hDpacking : IsPackingOn D :=
      (IsErdosConfig.isPackingOn hE hr5).mono hDE
    obtain ⟨z, hzD, hzone⟩ :=
      attachSphereFamily_short_interior_leaf hq T hDfiber hDpacking hDne hDcard
    let x : SphereExpansionVertex V q := SphereExpansionVertex.interior T z
    have hxD : x ∈ verticesOn D := hzD
    have hxnotR : x ∉ verticesOn R := by
      intro hxR
      have hfiberLocal := sphereFiber_subset_localFamily_of_interior_mem
        hq T z hxR hAfiber
      exact hAnotLocal hfiberLocal
    have hexternal : ∃ S : TripleOn (SphereExpansionVertex V q),
        S ∈ E ∧ x ∈ S.1 ∧ S ∉ sphereTransformBank hq := by
      by_contra hnone
      push Not at hnone
      have hthrough : triplesThrough E x = triplesThrough D x := by
        ext S
        simp only [triplesThrough, D, mem_filter]
        constructor
        · rintro ⟨hSE, hxS⟩
          have hSB : S ∈ sphereTransformBank hq := by
            exact hnone S hSE hxS
          have hSfiber := sphereTransformBank_interior_fiber
            hq hSB T z hxS
          exact ⟨⟨hSE, hSfiber⟩, hxS⟩
        · rintro ⟨⟨hSE, hSfiber⟩, hxS⟩
          exact ⟨hSE, hxS⟩
      have hxtwo := IsErdosConfig.two_le_card_triplesThrough hE hr5
        (verticesOn_mono hDE hxD)
      rw [hthrough, hzone] at hxtwo
      omega
    obtain ⟨S, hSE, hxS, hSnotB⟩ := hexternal
    have hSnotR : S ∉ R := by
      intro hSR
      apply hxnotR
      exact mem_biUnion.mpr ⟨S, hSR, hxS⟩
    refine ⟨S, hSE, ?_, x, hxS, ?_, ?_⟩
    · simp [hSnotR, hSnotB]
    · obtain ⟨A₀, hA₀D, hxA₀⟩ := mem_biUnion.mp hxD
      have hA₀fiber :
          A₀ ∈ attachSphereFamily hq T (sphereBank hq) :=
        (mem_filter.mp hA₀D).2
      obtain ⟨y, hyA₀, hyx⟩ := Finset.exists_mem_ne
        (by rw [A₀.2]; omega) x
      exact ⟨y, hOut (sphereBank_interior_edge_in_outGraph
        hq T hA₀fiber hxA₀ hyA₀ hyx.symm)⟩
    · intro hxX
      obtain ⟨a, ha⟩ := hXroots x hxX
      change SphereExpansionVertex.interior T z =
        SphereExpansionVertex.root a at ha
      cases ha

/-- The actual fixed bank used by the high-girth cycle-cover absorber. -/
noncomputable def highGirthCycleCoverBank
    (V : Type*) [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) :
    TripleSystemOn (HighGirthCycleCoverVertex V q) := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  letI : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  exact sphereTransformBank hq

theorem highGirthCycleCover_hasLocalization
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) :
    HasAbsorberLocalization q (12 * q ^ 2)
      (highGirthCycleCoverGraph V hq)
      (highGirthCycleCoverRoots V q)
      (highGirthCycleCoverBank V hq) := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  apply sphereTransformBank_hasLocalization hq
  · intro x y hxy
    exact Or.inl hxy
  · intro x hx
    obtain ⟨a, _ha, hax⟩ := Finset.mem_map.mp hx
    exact ⟨cycleCoverRootEmbedding V a, hax.symm⟩

theorem highGirthCycleCover_absorbs_in_bank
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : TriangleDivisible G) :
    ∃ C : TripleSystemOn (HighGirthCycleCoverVertex V q),
      C ⊆ highGirthCycleCoverBank V hq ∧
      IsHighGirthTriangleDecomposition q
        (highGirthCycleCoverGraph V hq ⊔
          G.map (highGirthCycleCoverRootEmbedding V q)) C := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  obtain ⟨C₀, hC₀⟩ := cycleCoverAbsorber_absorbs hV G hG
  let C := sphereTransform hq C₀
  have hpacking : IsPackingOn C :=
    sphereTransform_isPacking hq hC₀.isPackingOn
  refine ⟨C, sphereTransform_subset_bank hq C₀, ?_,
    sphereTransform_girthGreater hq hC₀.isPackingOn⟩
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

theorem highGirthCycleCover_hasAbsorptionBank
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V) :
    HasHighGirthAbsorptionBank q
      (highGirthCycleCoverGraph V hq)
      (highGirthCycleCoverRoots V q)
      (highGirthCycleCoverBank V hq) := by
  constructor
  · intro u hu v hv huv
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_map.mp hv
    exact highGirthCycleCoverGraph_not_adj_root_root hq a b
  · intro L _ hLsupported hLdiv
    let f := highGirthCycleCoverRootEmbedding V q
    let G := L.comap f
    have hsuppRange : GraphSupportedOn L (Set.range f) := by
      intro u v huv
      obtain ⟨hu, hv⟩ := hLsupported huv
      constructor
      · obtain ⟨a, _ha, hau⟩ := Finset.mem_map.mp hu
        exact ⟨a, hau⟩
      · obtain ⟨b, _hb, hbv⟩ := Finset.mem_map.mp hv
        exact ⟨b, hbv⟩
    have hmap : G.map f = L :=
      SimpleGraph.map_comap_eq_of_supportedOn_range f L hsuppRange
    have hGdiv : TriangleDivisible G := by
      apply TriangleDivisible.of_map G f
      simpa only [hmap] using hLdiv
    obtain ⟨C, hCB, hC⟩ :=
      highGirthCycleCover_absorbs_in_bank hq hV G hGdiv
    refine ⟨C, hCB, ?_⟩
    have hrootMap :
        G.map (highGirthCycleCoverRootEmbedding V q) = L := by
      simpa only [f] using hmap
    simpa only [hrootMap] using hC

def fullCycleCoverLocalConstant : ℕ :=
  Fintype.card (Fin 9) +
    Fintype.card c4c5TemplateGraph.edgeSet + 6 +
  (Fintype.card (Fin 12) +
    Fintype.card threeC4TemplateGraph.edgeSet + 6)

lemma transformerVertex_card
    {A Y : Type*} [Fintype A] [Fintype Y]
    (G : SimpleGraph A) [DecidableRel G.Adj] :
    Fintype.card (TransformerVertex G Y) =
      Fintype.card A + Fintype.card Y + Fintype.card G.edgeSet := by
  rw [← Fintype.card_congr (transformerVertexEquiv G)]
  simp [add_assoc]

lemma fullCycleCoverLocalUniversal_card
    {Y : Type*} [Fintype Y] :
    Fintype.card (C4C5LocalVertex Y ⊕ ThreeC4LocalVertex Y) =
      2 * Fintype.card Y + fullCycleCoverLocalConstant := by
  simp only [Fintype.card_sum, C4C5LocalVertex, ThreeC4LocalVertex,
    transformerVertex_card, Fintype.card_fin]
  simp [fullCycleCoverLocalConstant]
  omega

def fullCycleCoverPrivateToUniversal
    {Y : Type*} (i : FullCycleCoverCopy Y) :
    FullCycleCoverPrivate i ↪ (C4C5LocalVertex Y ⊕ ThreeC4LocalVertex Y) :=
  match i with
  | .triangle f =>
      { toFun := PEmpty.elim
        inj' := by
          intro x
          exact PEmpty.elim x }
  | .c4c5 f =>
      (Function.Embedding.subtype IsC4C5LocalPrivate).trans
        Function.Embedding.inl
  | .threeC4 f =>
      (Function.Embedding.subtype IsThreeC4LocalPrivate).trans
        Function.Embedding.inr

lemma fullCycleCoverPrivate_card_le
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (i : FullCycleCoverCopy Y) :
    Fintype.card (FullCycleCoverPrivate i) ≤
      2 * Fintype.card Y + fullCycleCoverLocalConstant := by
  rw [← fullCycleCoverLocalUniversal_card]
  exact Fintype.card_le_of_embedding (fullCycleCoverPrivateToUniversal i)

lemma c4c5QuotientMap_card_le
    {Y : Type*} [Fintype Y] :
    Fintype.card (C4C5QuotientMap Y) ≤ Fintype.card Y ^ 9 := by
  calc
    Fintype.card (C4C5QuotientMap Y) ≤
        Fintype.card (Fin 9 → Y) := Fintype.card_subtype_le _
    _ = Fintype.card Y ^ 9 := by simp

lemma threeC4QuotientMap_card_le
    {Y : Type*} [Fintype Y] :
    Fintype.card (ThreeC4QuotientMap Y) ≤ Fintype.card Y ^ 12 := by
  calc
    Fintype.card (ThreeC4QuotientMap Y) ≤
        Fintype.card (Fin 12 → Y) := Fintype.card_subtype_le _
    _ = Fintype.card Y ^ 12 := by simp

lemma embedding_fin_three_card_le
    {Y : Type*} [Fintype Y] :
    Fintype.card (Fin 3 ↪ Y) ≤ Fintype.card Y ^ 3 := by
  rw [Fintype.card_embedding_eq]
  simpa using Nat.descFactorial_le_pow (Fintype.card Y) 3

lemma fullCycleCoverCopy_card_le
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    Fintype.card (FullCycleCoverCopy Y) ≤
      Fintype.card Y ^ 3 + Fintype.card Y ^ 9 +
        Fintype.card Y ^ 12 := by
  rw [← Fintype.card_congr (fullCycleCoverCopyEquiv Y)]
  simp only [Fintype.card_sum]
  have h3 := embedding_fin_three_card_le (Y := Y)
  have h9 := c4c5QuotientMap_card_le (Y := Y)
  have h12 := threeC4QuotientMap_card_le (Y := Y)
  omega

def fullCycleCoverVertexBoundEmbedding
    {Y : Type*} :
    FullCycleCoverVertex Y ↪
      Y ⊕ (FullCycleCoverCopy Y ×
        (C4C5LocalVertex Y ⊕ ThreeC4LocalVertex Y)) where
  toFun
    | Sum.inl y => Sum.inl y
    | Sum.inr p => Sum.inr (p.1, fullCycleCoverPrivateToUniversal p.1 p.2)
  inj' := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Sum.inl.inj hxy)
        | inr y => cases hxy
    | inr x =>
        rcases x with ⟨i, xi⟩
        cases y with
        | inl y => cases hxy
        | inr y =>
            rcases y with ⟨j, yj⟩
            have hprod :
                (i, fullCycleCoverPrivateToUniversal i xi) =
                  (j, fullCycleCoverPrivateToUniversal j yj) :=
              Sum.inr.inj hxy
            have hij : i = j := congrArg Prod.fst hprod
            subst j
            have hprivate :
                fullCycleCoverPrivateToUniversal i xi =
                  fullCycleCoverPrivateToUniversal i yj := by
              exact congrArg Prod.snd hprod
            have hxyPrivate :=
              (fullCycleCoverPrivateToUniversal i).injective hprivate
            subst yj
            rfl

lemma fullCycleCoverVertex_card_le
    {Y : Type*} [Fintype Y] [DecidableEq Y] :
    Fintype.card (FullCycleCoverVertex Y) ≤
      Fintype.card Y +
        (Fintype.card Y ^ 3 + Fintype.card Y ^ 9 +
          Fintype.card Y ^ 12) *
            (2 * Fintype.card Y + fullCycleCoverLocalConstant) := by
  calc
    Fintype.card (FullCycleCoverVertex Y) ≤
        Fintype.card
          (Y ⊕ (FullCycleCoverCopy Y ×
            (C4C5LocalVertex Y ⊕ ThreeC4LocalVertex Y))) :=
      Fintype.card_le_of_embedding fullCycleCoverVertexBoundEmbedding
    _ = Fintype.card Y +
        Fintype.card (FullCycleCoverCopy Y) *
          (2 * Fintype.card Y + fullCycleCoverLocalConstant) := by
      rw [Fintype.card_sum, Fintype.card_prod,
        fullCycleCoverLocalUniversal_card]
    _ ≤ _ := by
      gcongr
      exact fullCycleCoverCopy_card_le

lemma cycleCoverPathVertex_card_le
    (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (CycleCoverPathVertex (Fin m)) ≤ 7 * m ^ 4 := by
  rw [pathCoverVertex_card]
  simp only [Fintype.card_fin]
  have hchoose : m.choose 2 ≤ m ^ 2 := Nat.choose_le_pow m 2
  have hmpow : m ≤ m ^ 4 := by
    simpa only [pow_one] using
      (pow_le_pow_right' hm (by omega : 1 ≤ 4))
  calc
    m + m.choose 2 * (6 * m ^ 2) ≤
        m ^ 4 + m ^ 2 * (6 * m ^ 2) := by gcongr
    _ = 7 * m ^ 4 := by ring

def cycleCoverCardConstant : ℕ :=
  (1 + 3 * (2 + fullCycleCoverLocalConstant)) * 7 ^ 13

lemma cycleCoverAbsorberVertex_card_le
    (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (CycleCoverAbsorberVertex (Fin m)) ≤
      cycleCoverCardConstant * m ^ 52 := by
  let y := Fintype.card (CycleCoverPathVertex (Fin m))
  have hy : 1 ≤ y := by
    have hycard : y = m + m.choose 2 * (6 * m ^ 2) := by
      dsimp [y]
      rw [pathCoverVertex_card]
      simp
    omega
  have hyBound : y ≤ 7 * m ^ 4 := cycleCoverPathVertex_card_le m hm
  have hy3 : y ^ 3 ≤ y ^ 12 := pow_le_pow_right' hy (by omega)
  have hy9 : y ^ 9 ≤ y ^ 12 := pow_le_pow_right' hy (by omega)
  have hy13 : y ≤ y ^ 13 := by
    simpa only [pow_one] using pow_le_pow_right' hy (by omega : 1 ≤ 13)
  have hlinear :
      2 * y + fullCycleCoverLocalConstant ≤
        (2 + fullCycleCoverLocalConstant) * y := by
    nlinarith [Nat.mul_le_mul_left fullCycleCoverLocalConstant hy]
  have hraw := fullCycleCoverVertex_card_le
    (Y := CycleCoverPathVertex (Fin m))
  change Fintype.card (CycleCoverAbsorberVertex (Fin m)) ≤
      y + (y ^ 3 + y ^ 9 + y ^ 12) *
        (2 * y + fullCycleCoverLocalConstant) at hraw
  calc
    Fintype.card (CycleCoverAbsorberVertex (Fin m)) ≤
        y + (y ^ 3 + y ^ 9 + y ^ 12) *
          (2 * y + fullCycleCoverLocalConstant) := hraw
    _ ≤ y ^ 13 + (3 * y ^ 12) *
          ((2 + fullCycleCoverLocalConstant) * y) := by
      gcongr
      omega
    _ = (1 + 3 * (2 + fullCycleCoverLocalConstant)) * y ^ 13 := by
      ring
    _ ≤ (1 + 3 * (2 + fullCycleCoverLocalConstant)) *
          (7 * m ^ 4) ^ 13 := by gcongr
    _ = cycleCoverCardConstant * m ^ 52 := by
      unfold cycleCoverCardConstant
      rw [mul_pow, ← pow_mul]
      norm_num
      ring

def tripleFunctionEmbedding
    {Z : Type*} [LinearOrder Z] : TripleOn Z ↪ (Fin 3 → Z) where
  toFun := tripleVertex
  inj' := by
    intro T U hTU
    apply Subtype.ext
    ext x
    constructor
    · intro hxT
      let i : Fin 3 := (T.1.orderIsoOfFin T.2).symm ⟨x, hxT⟩
      have hxi : tripleVertex T i = x := by
        change ((T.1.orderIsoOfFin T.2 i).1) = x
        simp [i]
      have := tripleVertex_mem U i
      rwa [← hTU, hxi] at this
    · intro hxU
      let i : Fin 3 := (U.1.orderIsoOfFin U.2).symm ⟨x, hxU⟩
      have hxi : tripleVertex U i = x := by
        change ((U.1.orderIsoOfFin U.2 i).1) = x
        simp [i]
      have := tripleVertex_mem T i
      rwa [hTU, hxi] at this

lemma tripleOn_card_le_cube
    {Z : Type*} [Fintype Z] [LinearOrder Z] :
    Fintype.card (TripleOn Z) ≤ Fintype.card Z ^ 3 := by
  calc
    Fintype.card (TripleOn Z) ≤ Fintype.card (Fin 3 → Z) :=
      Fintype.card_le_of_embedding tripleFunctionEmbedding
    _ = Fintype.card Z ^ 3 := by simp

def sphereVertexEquivSum (q : ℕ) :
    SphereVertex q ≃ (Fin (2 * q) ⊕ Bool) where
  toFun
    | .cycle i => Sum.inl i
    | .pole b => Sum.inr b
  invFun
    | Sum.inl i => .cycle i
    | Sum.inr b => .pole b
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

lemma sphereInterior_card_le (q : ℕ) :
    Fintype.card (SphereInterior q) ≤ 2 * q + 2 := by
  calc
    Fintype.card (SphereInterior q) ≤ Fintype.card (SphereVertex q) :=
      Fintype.card_subtype_le _
    _ = Fintype.card (Fin (2 * q) ⊕ Bool) :=
      Fintype.card_congr (sphereVertexEquivSum q)
    _ = 2 * q + 2 := by simp

lemma sphereExpansionVertex_card_le
    {Z : Type*} [Fintype Z] [LinearOrder Z]
    (q : ℕ) (hZ : 1 ≤ Fintype.card Z) :
    Fintype.card (SphereExpansionVertex Z q) ≤
      (2 * q + 3) * Fintype.card Z ^ 3 := by
  calc
    Fintype.card (SphereExpansionVertex Z q) ≤
        Fintype.card (Z ⊕ (TripleOn Z × SphereInterior q)) :=
      Fintype.card_le_of_embedding sphereExpansionVertexEquiv.toEmbedding
    _ = Fintype.card Z + Fintype.card (TripleOn Z) *
        Fintype.card (SphereInterior q) := by simp
    _ ≤ Fintype.card Z ^ 3 +
        Fintype.card Z ^ 3 * (2 * q + 2) := by
        gcongr
        · simpa only [pow_one] using
            pow_le_pow_right' hZ (by omega : 1 ≤ 3)
        · exact tripleOn_card_le_cube
        · exact sphereInterior_card_le q
    _ = (2 * q + 3) * Fintype.card Z ^ 3 := by ring

def highGirthAbsorberCardCoefficient (q : ℕ) : ℕ :=
  (2 * q + 3) * cycleCoverCardConstant ^ 3

lemma highGirthCycleCoverVertex_card_le
    (q m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (HighGirthCycleCoverVertex (Fin m) q) ≤
      highGirthAbsorberCardCoefficient q * m ^ 156 := by
  let coreDecidableEq :
      DecidableEq (CycleCoverAbsorberVertex (Fin m)) := inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex (Fin m)) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex (Fin m))) _
        coreDecidableEq
  have hcorePos : 1 ≤
      Fintype.card (CycleCoverAbsorberVertex (Fin m)) := by
    have hroot : m ≤ Fintype.card (CycleCoverAbsorberVertex (Fin m)) :=
      by simpa using
        Fintype.card_le_of_embedding (cycleCoverRootEmbedding (Fin m))
    exact hm.trans hroot
  calc
    Fintype.card (HighGirthCycleCoverVertex (Fin m) q) ≤
        (2 * q + 3) *
          Fintype.card (CycleCoverAbsorberVertex (Fin m)) ^ 3 :=
      sphereExpansionVertex_card_le q hcorePos
    _ ≤ (2 * q + 3) *
          (cycleCoverCardConstant * m ^ 52) ^ 3 := by
      gcongr
      exact cycleCoverAbsorberVertex_card_le m hm
    _ = highGirthAbsorberCardCoefficient q * m ^ 156 := by
      unfold highGirthAbsorberCardCoefficient
      rw [mul_pow, ← pow_mul]
      norm_num
      ring

lemma mapTriple_comp
    {A W Z : Type*} [DecidableEq A] [DecidableEq W] [DecidableEq Z]
    (f : A ↪ W) (g : W ↪ Z) (T : TripleOn A) :
    mapTriple (f.trans g) T = mapTriple g (mapTriple f T) := by
  apply Subtype.ext
  exact (Finset.map_map f g T.1).symm

lemma mapTripleSystem_comp
    {A W Z : Type*} [DecidableEq A] [DecidableEq W] [DecidableEq Z]
    (f : A ↪ W) (g : W ↪ Z) (C : TripleSystemOn A) :
    mapTripleSystem (f.trans g) C =
      mapTripleSystem g (mapTripleSystem f C) := by
  unfold mapTripleSystem
  rw [Finset.map_map]
  apply congrArg (fun e : TripleOn A ↪ TripleOn Z ↦ C.map e)
  apply Function.Embedding.ext
  intro T
  exact mapTriple_comp f g T

@[simp]
lemma mapTripleSystem_refl
    {A : Type*} [DecidableEq A] (C : TripleSystemOn A) :
    mapTripleSystem (Function.Embedding.refl A) C = C := by
  ext T
  simp [mapTripleSystem, mapTripleEmbedding, mapTriple]

@[simp]
lemma mapTripleSystem_equiv_symm_apply
    {A W : Type*} [DecidableEq A] [DecidableEq W]
    (e : A ≃ W) (C : TripleSystemOn A) :
    mapTripleSystem e.symm.toEmbedding
      (mapTripleSystem e.toEmbedding C) = C := by
  rw [← mapTripleSystem_comp]
  simpa using mapTripleSystem_refl C

@[simp]
lemma mapTripleSystem_equiv_apply_symm
    {A W : Type*} [DecidableEq A] [DecidableEq W]
    (e : A ≃ W) (C : TripleSystemOn W) :
    mapTripleSystem e.toEmbedding
      (mapTripleSystem e.symm.toEmbedding C) = C := by
  rw [← mapTripleSystem_comp]
  simpa using mapTripleSystem_refl C

lemma mapTripleSystem_mono
    {A W : Type*} [DecidableEq A] [DecidableEq W]
    (f : A ↪ W) {C D : TripleSystemOn A} (hCD : C ⊆ D) :
    mapTripleSystem f C ⊆ mapTripleSystem f D := by
  intro U hU
  obtain ⟨T, hTC, rfl⟩ := Finset.mem_map.mp hU
  exact (mem_mapTripleSystem_iff f D T).mpr (hCD hTC)

lemma verticesOn_mapTripleSystem
    {A W : Type*} [DecidableEq A] [DecidableEq W]
    (f : A ↪ W) (C : TripleSystemOn A) :
    verticesOn (mapTripleSystem f C) = (verticesOn C).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨U, hU, hyU⟩ := mem_biUnion.mp hy
    obtain ⟨T, hTC, rfl⟩ := Finset.mem_map.mp hU
    obtain ⟨x, hxT, rfl⟩ := Finset.mem_map.mp hyU
    exact Finset.mem_map.mpr ⟨x, mem_biUnion.mpr ⟨T, hTC, hxT⟩, rfl⟩
  · intro hy
    obtain ⟨x, hxC, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨T, hTC, hxT⟩ := mem_biUnion.mp hxC
    exact mem_biUnion.mpr
      ⟨mapTriple f T, (mem_mapTripleSystem_iff f C T).mpr hTC,
        (mem_mapTriple_apply_iff f T x).mpr hxT⟩

lemma IsTriangleDecomposition.map
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {G : SimpleGraph A} {C : TripleSystemOn A}
    (hC : IsTriangleDecomposition G C) (f : A ↪ W) :
    IsTriangleDecomposition (G.map f) (mapTripleSystem f C) := by
  rw [← hC.coveredGraph_eq, ← coveredGraph_mapTripleSystem]
  exact hC.isPackingOn.map f |>.isTriangleDecomposition

lemma GirthGreaterOn.map
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {q : ℕ} {C : TripleSystemOn A}
    (hC : GirthGreaterOn q C) (f : A ↪ W) :
    GirthGreaterOn q (mapTripleSystem f C) := by
  intro r hr4 hrq
  rintro ⟨D, hDmap, hDcard, hDvertices⟩
  let D₀ : TripleSystemOn A :=
    C.filter fun T ↦ mapTriple f T ∈ D
  have hD₀C : D₀ ⊆ C := filter_subset _ _
  have hmapD₀ : mapTripleSystem f D₀ = D := by
    ext U
    constructor
    · intro hU
      obtain ⟨T, hTD₀, rfl⟩ := Finset.mem_map.mp hU
      exact (mem_filter.mp hTD₀).2
    · intro hUD
      have hUmap := hDmap hUD
      obtain ⟨T, hTC, hTU⟩ := Finset.mem_map.mp hUmap
      subst U
      exact (mem_mapTripleSystem_iff f D₀ T).mpr
        (mem_filter.mpr ⟨hTC, hUD⟩)
  apply hC r hr4 hrq
  refine ⟨D₀, hD₀C, ?_, ?_⟩
  · rw [← card_mapTripleSystem f D₀, hmapD₀]
    exact hDcard
  · rw [← hmapD₀, verticesOn_mapTripleSystem, card_map] at hDvertices
    exact hDvertices

lemma IsHighGirthTriangleDecomposition.map
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {q : ℕ} {G : SimpleGraph A} {C : TripleSystemOn A}
    (hC : IsHighGirthTriangleDecomposition q G C) (f : A ↪ W) :
    IsHighGirthTriangleDecomposition q (G.map f) (mapTripleSystem f C) :=
  ⟨hC.1.map f, hC.2.map f⟩

lemma IsConfigOn.map
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {v k : ℕ} {C : TripleSystemOn A}
    (hC : IsConfigOn v k C) (f : A ↪ W) :
    IsConfigOn v k (mapTripleSystem f C) := by
  constructor
  · rw [card_mapTripleSystem]
    exact hC.1
  · rw [verticesOn_mapTripleSystem, card_map]
    exact hC.2

lemma IsErdosConfig.map
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {r : ℕ} {C : TripleSystemOn A}
    (hC : IsErdosConfigOn r C) (f : A ↪ W) :
    IsErdosConfigOn r (mapTripleSystem f C) :=
  ⟨hC.1.map f, hC.2.map f⟩

lemma ConsistsOfTriangles.map
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {G : SimpleGraph A} {C : TripleSystemOn A}
    (hC : ConsistsOfTriangles G C) (f : A ↪ W) :
    ConsistsOfTriangles (G.map f) (mapTripleSystem f C) := by
  intro U hUC x hxU y hyU hxy
  obtain ⟨T, hTC, rfl⟩ := Finset.mem_map.mp hUC
  obtain ⟨a, haT, rfl⟩ := Finset.mem_map.mp hxU
  obtain ⟨b, hbT, rfl⟩ := Finset.mem_map.mp hyU
  exact SimpleGraph.map_adj_apply.mpr
    (hC T hTC a haT b hbT (f.injective.ne_iff.mp hxy))

lemma GirthGreaterOn.mono
    {A : Type*} [DecidableEq A] {q q' : ℕ}
    {C : TripleSystemOn A} (hC : GirthGreaterOn q C)
    (hqq' : q' ≤ q) : GirthGreaterOn q' C := by
  intro r hr4 hrq'
  exact hC r hr4 (hrq'.trans hqq')

lemma HasHighGirthAbsorptionBank.cutoff_mono
    {A : Type*} [Fintype A] [DecidableEq A]
    {q q' : ℕ} {H : SimpleGraph A} {X : Finset A}
    {B : TripleSystemOn A}
    (h : HasHighGirthAbsorptionBank q H X B) (hqq' : q' ≤ q) :
    HasHighGirthAbsorptionBank q' H X B := by
  refine ⟨h.1, ?_⟩
  intro L _ hLsupport hLdiv
  obtain ⟨C, hCB, hC⟩ := h.2 L hLsupport hLdiv
  exact ⟨C, hCB, hC.1, hC.2.mono hqq'⟩

lemma HasHighGirthAbsorptionBank.mono_roots
    {A : Type*} [Fintype A] [DecidableEq A]
    {q : ℕ} {H : SimpleGraph A} {X X' : Finset A}
    {B : TripleSystemOn A}
    (h : HasHighGirthAbsorptionBank q H X B) (hXX : X' ⊆ X) :
    HasHighGirthAbsorptionBank q H X' B := by
  constructor
  · intro u hu v hv huv
    exact h.1 u (hXX hu) v (hXX hv) huv
  · intro L _ hLsupport hLdiv
    apply h.2 L
    · intro u v huv
      exact ⟨hXX (hLsupport huv).1, hXX (hLsupport huv).2⟩
    · exact hLdiv

lemma HasAbsorberLocalization.cutoff_mono
    {A : Type*} [Fintype A] [DecidableEq A]
    {q q' M : ℕ} {H : SimpleGraph A} {X : Finset A}
    {B : TripleSystemOn A}
    (h : HasAbsorberLocalization q M H X B) (hqq' : q' ≤ q) :
    HasAbsorberLocalization q' M H X B := by
  intro K hHK R hRq' hRtri
  obtain ⟨L, hLB, hLM, hL⟩ := h K hHK R (hRq'.trans hqq') hRtri
  refine ⟨L, hLB, hLM, ?_⟩
  intro r hr5 hrq' E hE hRE
  exact hL r hr5 (hrq'.trans hqq') E hE hRE

lemma HasAbsorberLocalization.mono_roots
    {A : Type*} [Fintype A] [DecidableEq A]
    {q M : ℕ} {H : SimpleGraph A} {X X' : Finset A}
    {B : TripleSystemOn A}
    (h : HasAbsorberLocalization q M H X B) (hXX : X' ⊆ X) :
    HasAbsorberLocalization q M H X' B := by
  intro K hHK R hRq hRtri
  obtain ⟨L, hLB, hLM, hL⟩ := h K hHK R hRq hRtri
  refine ⟨L, hLB, hLM, ?_⟩
  intro r hr5 hrq E hE hRE
  rcases hL r hr5 hrq E hE hRE with hlocal | ⟨T, hTE, hTfree,
      v, hvT, hvH, hvX⟩
  · exact Or.inl hlocal
  · exact Or.inr ⟨T, hTE, hTfree, v, hvT, hvH,
      fun hvX' ↦ hvX (hXX hvX')⟩

lemma HasAbsorberLocalization.bound_mono
    {A : Type*} [Fintype A] [DecidableEq A]
    {q M M' : ℕ} {H : SimpleGraph A} {X : Finset A}
    {B : TripleSystemOn A}
    (h : HasAbsorberLocalization q M H X B) (hMM : M ≤ M') :
    HasAbsorberLocalization q M' H X B := by
  intro K hHK R hRq hRtri
  obtain ⟨L, hLB, hLM, hL⟩ := h K hHK R hRq hRtri
  exact ⟨L, hLB, hLM.trans hMM, hL⟩

theorem HasHighGirthAbsorptionBank.mapEquiv
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {q : ℕ} {H : SimpleGraph A} {X : Finset A}
    {B : TripleSystemOn A}
    (h : HasHighGirthAbsorptionBank q H X B) (e : A ≃ W) :
    HasHighGirthAbsorptionBank q (H.map e.toEmbedding) (X.map e.toEmbedding)
      (mapTripleSystem e.toEmbedding B) := by
  constructor
  · intro u hu v hv huv
    obtain ⟨a, haX, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hbX, rfl⟩ := Finset.mem_map.mp hv
    rw [SimpleGraph.map_adj_apply]
    exact h.1 a haX b hbX (e.injective.ne_iff.mp huv)
  · intro L _ hLsupport hLdiv
    let G : SimpleGraph A := L.comap e.toEmbedding
    have hmap : G.map e.toEmbedding = L := by
      change (L.comap e.toEmbedding).map e.toEmbedding = L
      rw [← SimpleGraph.map_symm L e, SimpleGraph.map_map]
      have hfun :
          (e.toEmbedding : A → W) ∘ (e.symm.toEmbedding : W → A) = id := by
        funext x
        exact e.apply_symm_apply x
      rw [hfun, SimpleGraph.map_id]
    have hGsupport : GraphSupportedOn G (X : Set A) := by
      intro a b hab
      obtain ⟨ha, hb⟩ := hLsupport hab
      obtain ⟨a', ha'X, haa'⟩ := Finset.mem_map.mp ha
      obtain ⟨b', hb'X, hbb'⟩ := Finset.mem_map.mp hb
      have ha'eq : a' = a := e.injective haa'
      have hb'eq : b' = b := e.injective hbb'
      subst a'
      subst b'
      change a ∈ X ∧ b ∈ X
      exact ⟨ha'X, hb'X⟩
    have hGdiv : TriangleDivisible G := by
      apply TriangleDivisible.of_map G e.toEmbedding
      simpa only [hmap] using hLdiv
    obtain ⟨C, hCB, hC⟩ := h.2 G hGsupport hGdiv
    refine ⟨mapTripleSystem e.toEmbedding C,
      mapTripleSystem_mono e.toEmbedding hCB, ?_⟩
    have hCmap := hC.map e.toEmbedding
    rw [SimpleGraph.map_sup_embedding, hmap] at hCmap
    exact hCmap

@[simp]
lemma mapTriple_equiv_symm_apply
    {A W : Type*} [DecidableEq A] [DecidableEq W]
    (e : A ≃ W) (T : TripleOn A) :
    mapTriple e.symm.toEmbedding (mapTriple e.toEmbedding T) = T := by
  apply Subtype.ext
  ext x
  simp [mapTriple]

@[simp]
lemma mapTriple_equiv_apply_symm
    {A W : Type*} [DecidableEq A] [DecidableEq W]
    (e : A ≃ W) (T : TripleOn W) :
    mapTriple e.toEmbedding (mapTriple e.symm.toEmbedding T) = T := by
  apply Subtype.ext
  ext x
  simp [mapTriple]

lemma mapTripleSystem_inter_equiv
    {A W : Type*} [DecidableEq A] [DecidableEq W]
    (e : A ≃ W) (C D : TripleSystemOn A) :
    mapTripleSystem e.toEmbedding (C ∩ D) =
      mapTripleSystem e.toEmbedding C ∩ mapTripleSystem e.toEmbedding D := by
  ext U
  constructor
  · intro hU
    obtain ⟨T, hTCD, rfl⟩ := Finset.mem_map.mp hU
    exact mem_inter.mpr ⟨
      (mem_mapTripleSystem_iff e.toEmbedding C T).mpr (mem_inter.mp hTCD).1,
      (mem_mapTripleSystem_iff e.toEmbedding D T).mpr (mem_inter.mp hTCD).2⟩
  · intro hU
    have hUC := (mem_inter.mp hU).1
    have hUD := (mem_inter.mp hU).2
    obtain ⟨T, hTC, hTU⟩ := Finset.mem_map.mp hUC
    obtain ⟨S, hSD, hSU⟩ := Finset.mem_map.mp hUD
    have hTS : T = S := mapTriple_injective e.toEmbedding (hTU.trans hSU.symm)
    subst S
    exact Finset.mem_map.mpr ⟨T, mem_inter.mpr ⟨hTC, hSD⟩, hTU⟩

theorem HasAbsorberLocalization.mapEquiv
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {q M : ℕ} {H : SimpleGraph A} {X : Finset A}
    {B : TripleSystemOn A}
    (h : HasAbsorberLocalization q M H X B) (e : A ≃ W) :
    HasAbsorberLocalization q M (H.map e.toEmbedding) (X.map e.toEmbedding)
      (mapTripleSystem e.toEmbedding B) := by
  intro K hHK R hRq hRtri
  let K₀ : SimpleGraph A := K.comap e.toEmbedding
  let R₀ : TripleSystemOn A := mapTripleSystem e.symm.toEmbedding R
  have hHK₀ : H ≤ K₀ := by
    exact (SimpleGraph.map_le_iff_le_comap e.toEmbedding H K).mp hHK
  have hR₀q : R₀.card ≤ q := by
    simpa only [R₀, card_mapTripleSystem] using hRq
  have hR₀tri : ConsistsOfTriangles K₀ R₀ := by
    have hmap := hRtri.map e.symm.toEmbedding
    rw [SimpleGraph.map_symm K e] at hmap
    exact hmap
  obtain ⟨L₀, hL₀B, hL₀M, hL₀⟩ := h K₀ hHK₀ R₀ hR₀q hR₀tri
  let L := mapTripleSystem e.toEmbedding L₀
  refine ⟨L, mapTripleSystem_mono e.toEmbedding hL₀B, ?_, ?_⟩
  · simpa only [L, card_mapTripleSystem] using hL₀M
  · intro r hr5 hrq E hE hRE
    let E₀ : TripleSystemOn A := mapTripleSystem e.symm.toEmbedding E
    have hE₀ : IsErdosConfigOn r E₀ :=
      IsErdosConfig.map hE e.symm.toEmbedding
    have hR₀E₀ : R₀ ⊆ E₀ :=
      mapTripleSystem_mono e.symm.toEmbedding hRE
    rcases hL₀ r hr5 hrq E₀ hE₀ hR₀E₀ with hlocal |
        ⟨T₀, hT₀E, hT₀free, v₀, hv₀T, hv₀H, hv₀X⟩
    · left
      have hmapped := mapTripleSystem_mono e.toEmbedding hlocal
      rw [mapTripleSystem_inter_equiv,
        mapTripleSystem_equiv_apply_symm] at hmapped
      exact hmapped
    · right
      let T := mapTriple e.toEmbedding T₀
      have hTE : T ∈ E := by
        have hm : T ∈ mapTripleSystem e.toEmbedding E₀ :=
          (mem_mapTripleSystem_iff e.toEmbedding E₀ T₀).mpr hT₀E
        simpa only [E₀, mapTripleSystem_equiv_apply_symm] using hm
      have hTfree : T ∉ R ∪ mapTripleSystem e.toEmbedding B := by
        intro hTin
        apply hT₀free
        rw [mem_union] at hTin ⊢
        rcases hTin with hTR | hTB
        · left
          have hm := (mem_mapTripleSystem_iff e.symm.toEmbedding R T).mpr hTR
          simpa only [T, mapTriple_equiv_symm_apply] using hm
        · right
          have hm := (mem_mapTripleSystem_iff e.symm.toEmbedding
            (mapTripleSystem e.toEmbedding B) T).mpr hTB
          simpa only [T, R₀, mapTriple_equiv_symm_apply,
            mapTripleSystem_equiv_symm_apply] using hm
      refine ⟨T, hTE, hTfree, e v₀, ?_, ?_, ?_⟩
      · exact (mem_mapTriple_apply_iff e.toEmbedding T₀ v₀).mpr hv₀T
      · obtain ⟨w₀, hvw⟩ := hv₀H
        exact ⟨e w₀, SimpleGraph.map_adj_apply.mpr hvw⟩
      · intro hvX
        obtain ⟨v, hv, hvEq⟩ := Finset.mem_map.mp hvX
        exact hv₀X (by simpa only [e.injective hvEq] using hv)

/-- One coefficient simultaneously dominates the vertex count and the
localization-bank bound after reserving twice as many concrete roots as are
eventually exposed in the flexible set. -/
def efficientHighGirthAbsorberCoefficient (q : ℕ) : ℕ :=
  max (highGirthAbsorberCardCoefficient (q + 2) * 2 ^ 156)
    (12 * (q + 2) ^ 2)

/-- The explicit absorber developed above supplies KSSS's efficient
high-girth absorber hypothesis, with absolute exponent `156`. -/
theorem efficientHighGirthAbsorbers : EfficientHighGirthAbsorbers := by
  refine ⟨156, ?_⟩
  intro q
  refine ⟨efficientHighGirthAbsorberCoefficient q, ?_⟩
  intro m hm
  let q' := q + 2
  have hq' : 2 ≤ q' := by simp [q']
  let V := Fin (2 * m)
  have hV : 2 ≤ Fintype.card V := by
    simp only [V, Fintype.card_fin]
    omega
  let W := HighGirthCycleCoverVertex V q'
  let N := Fintype.card W
  let e : W ≃ Fin N := Fintype.equivFin W
  let i : Fin m ↪ V := Fin.castLEEmb (by
    change m ≤ 2 * m
    omega)
  let j : Fin m ↪ W :=
    i.trans (highGirthCycleCoverRootEmbedding V q')
  let X₀ : Finset W := (univ : Finset (Fin m)).map j
  let H₀ : SimpleGraph W := highGirthCycleCoverGraph V hq'
  let B₀ : TripleSystemOn W := highGirthCycleCoverBank V hq'
  let H : SimpleGraph (Fin N) := H₀.map e.toEmbedding
  let X : Finset (Fin N) := X₀.map e.toEmbedding
  let B : TripleSystemOn (Fin N) := mapTripleSystem e.toEmbedding B₀
  refine ⟨N, H, X, B, ?_, ?_, ?_, ?_⟩
  · have hcard := highGirthCycleCoverVertex_card_le q' (2 * m) (by omega)
    calc
      N ≤ highGirthAbsorberCardCoefficient q' * (2 * m) ^ 156 := by
        change Fintype.card W ≤
          highGirthAbsorberCardCoefficient q' * (2 * m) ^ 156
        exact hcard
      _ = (highGirthAbsorberCardCoefficient q' * 2 ^ 156) * m ^ 156 := by
        rw [mul_pow]
        ring
      _ ≤ efficientHighGirthAbsorberCoefficient q * m ^ 156 := by
        apply Nat.mul_le_mul_right
        unfold efficientHighGirthAbsorberCoefficient
        simpa only [q'] using (le_max_left
          (highGirthAbsorberCardCoefficient (q + 2) * 2 ^ 156)
          (12 * (q + 2) ^ 2))
  · simp only [X, X₀, card_map, card_univ, Fintype.card_fin]
  · have hX₀ : X₀ ⊆ highGirthCycleCoverRoots V q' := by
      intro x hx
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_map.mpr ⟨i a, mem_univ _, rfl⟩
    have hA := (highGirthCycleCover_hasAbsorptionBank hq' hV).mono_roots hX₀
    have hAq : HasHighGirthAbsorptionBank q
        (highGirthCycleCoverGraph V hq') X₀
        (highGirthCycleCoverBank V hq') :=
      hA.cutoff_mono (by simp only [q']; omega)
    simpa only [H, X, B, H₀, B₀] using hAq.mapEquiv e
  · have hX₀ : X₀ ⊆ highGirthCycleCoverRoots V q' := by
      intro x hx
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_map.mpr ⟨i a, mem_univ _, rfl⟩
    have hA := (highGirthCycleCover_hasLocalization hq').mono_roots hX₀
    have hAq : HasAbsorberLocalization q (12 * q' ^ 2)
        (highGirthCycleCoverGraph V hq') X₀
        (highGirthCycleCoverBank V hq') :=
      hA.cutoff_mono (by simp only [q']; omega)
    have hAmap := hAq.mapEquiv e
    simpa only [H, X, B, H₀, B₀, q',
      efficientHighGirthAbsorberCoefficient] using
      hAmap.bound_mono (le_max_right
        (highGirthAbsorberCardCoefficient (q + 2) * 2 ^ 156)
        (12 * (q + 2) ^ 2))

end

end Erdos207
