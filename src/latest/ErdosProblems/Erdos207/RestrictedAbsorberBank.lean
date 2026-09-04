/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberPadding
import ErdosProblems.Erdos207.AbsorberWellSpread

/-!
# The realizable absorber bank

The simultaneous sphere transform uses the out-side of every sphere, but it
uses an in-side only when the underlying cycle-cover decomposition contains
the corresponding core triangle.  Thus the bank needed by absorption is the
union of all out-sides and only the realizable in-sides.  Keeping this
distinction is essential: the full symmetric sphere bank contains root pairs
which can never occur in an absorber switch and would create spurious
order-four forbidden configurations.
-/

namespace Erdos207

open Finset

noncomputable section

open scoped Classical

/-- Shrinking the bank preserves absorber localization. -/
theorem HasAbsorberLocalization.mono_bank
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B B' : TripleSystemOn V}
    (h : HasAbsorberLocalization q M H X B) (hB'B : B' ⊆ B) :
    HasAbsorberLocalization q M H X B' := by
  intro K hHK R hRq hRtri
  obtain ⟨L, hLB, hLM, hL⟩ := h K hHK R hRq hRtri
  let L' := L ∩ B'
  refine ⟨L', ?_, ?_, ?_⟩
  · exact inter_subset_right
  · exact (card_le_card inter_subset_left).trans hLM
  · intro r hr5 hrq E hE hRE
    rcases hL r hr5 hrq E hE hRE with hlocal | hbad
    · left
      intro T hT
      have hTB' : T ∈ B' := (mem_inter.mp hT).2
      exact mem_inter.mpr ⟨hlocal (mem_inter.mpr
        ⟨(mem_inter.mp hT).1, hB'B hTB'⟩), hTB'⟩
    · right
      obtain ⟨T, hTE, hTfree, v, hvT, hvH, hvX⟩ := hbad
      refine ⟨T, hTE, ?_, v, hvT, hvH, hvX⟩
      intro hTRB'
      apply hTfree
      rcases mem_union.mp hTRB' with hTR | hTB'
      · exact mem_union.mpr (Or.inl hTR)
      · exact mem_union.mpr (Or.inr (hB'B hTB'))

/-- Core decompositions which can arise while absorbing a graph on the
original roots. -/
noncomputable def realizableCycleCoverDecompositions
    (V : Type*) [Fintype V] [DecidableEq V] (Y : Finset V) :
    Finset (TripleSystemOn (CycleCoverAbsorberVertex V)) := by
  classical
  exact (univ : Finset (TripleSystemOn (CycleCoverAbsorberVertex V))).filter
    fun C ↦ ∃ G : SimpleGraph V,
      GraphSupportedOn G (Y : Set V) ∧ IsTriangleDecomposition
        (cycleCoverAbsorberGraph V ⊔
          G.map (cycleCoverRootEmbedding V)) C

@[simp]
lemma mem_realizableCycleCoverDecompositions_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {Y : Finset V}
    {C : TripleSystemOn (CycleCoverAbsorberVertex V)} :
    C ∈ realizableCycleCoverDecompositions V Y ↔
      ∃ G : SimpleGraph V,
        GraphSupportedOn G (Y : Set V) ∧ IsTriangleDecomposition
          (cycleCoverAbsorberGraph V ⊔
            G.map (cycleCoverRootEmbedding V)) C := by
  classical
  simp [realizableCycleCoverDecompositions]

/-- The union of every realizable core decomposition. -/
noncomputable def realizableCycleCoverBank
    (V : Type*) [Fintype V] [DecidableEq V] (Y : Finset V) :
    TripleSystemOn (CycleCoverAbsorberVertex V) :=
  (realizableCycleCoverDecompositions V Y).biUnion id

lemma subset_realizableCycleCoverBank_of_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    {Y : Finset V}
    {G : SimpleGraph V}
    {C : TripleSystemOn (CycleCoverAbsorberVertex V)}
    (hGsupport : GraphSupportedOn G (Y : Set V))
    (hC : IsTriangleDecomposition
      (cycleCoverAbsorberGraph V ⊔
        G.map (cycleCoverRootEmbedding V)) C) :
    C ⊆ realizableCycleCoverBank V Y := by
  intro T hTC
  exact mem_biUnion.mpr
    ⟨C, mem_realizableCycleCoverDecompositions_iff.mpr
      ⟨G, hGsupport, hC⟩, hTC⟩

/-- All pairs in a realizable core-bank triangle are either fixed absorber
pairs or pairs of original roots. -/
lemma realizableCycleCoverBank_pair_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {Y : Finset V}
    {T : TripleOn (CycleCoverAbsorberVertex V)}
    (hT : T ∈ realizableCycleCoverBank V Y)
    {x y : CycleCoverAbsorberVertex V}
    (hx : x ∈ T.1) (hy : y ∈ T.1) (hxy : x ≠ y) :
    (cycleCoverAbsorberGraph V).Adj x y ∨
      (x ∈ Y.map (cycleCoverRootEmbedding V) ∧
        y ∈ Y.map (cycleCoverRootEmbedding V)) := by
  obtain ⟨C, hCreal, hTC⟩ := mem_biUnion.mp hT
  obtain ⟨G, hGsupport, hC⟩ :=
    mem_realizableCycleCoverDecompositions_iff.mp hCreal
  have hadj :
      (cycleCoverAbsorberGraph V ⊔
        G.map (cycleCoverRootEmbedding V)).Adj x y :=
    hC.1 T hTC x hx y hy hxy
  rw [SimpleGraph.sup_adj] at hadj
  rcases hadj with hfixed | hroot
  · exact Or.inl hfixed
  · right
    rw [SimpleGraph.map_adj] at hroot
    obtain ⟨a, b, _hab, rfl, rfl⟩ := hroot
    obtain ⟨haY, hbY⟩ := hGsupport _hab
    exact ⟨mem_map.mpr ⟨a, haY, rfl⟩,
      mem_map.mpr ⟨b, hbY, rfl⟩⟩

/-- All out-sides, together with the in-side of precisely the realizable
core triangles. -/
noncomputable def restrictedSphereTransformBank
    {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q) (C : TripleSystemOn V) :
    TripleSystemOn (SphereExpansionVertex V q) :=
  sphereTransform hq ∅ ∪
    C.biUnion fun T ↦
      attachSphereFamily hq T (sphereDecomposition hq true)

lemma restrictedSphereTransformBank_subset
    {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q) (C : TripleSystemOn V) :
    restrictedSphereTransformBank hq C ⊆ sphereTransformBank hq := by
  intro U hU
  rcases mem_union.mp hU with hout | hin
  · exact sphereTransform_subset_bank hq ∅ hout
  · obtain ⟨T, _hTC, hUin⟩ := mem_biUnion.mp hin
    simp only [sphereTransformBank, mem_biUnion]
    exact ⟨T, mem_univ T,
      mapTripleSystem_mono (attachSphereEmbedding hq T)
        (sphereDecomposition_subset_bank hq true) hUin⟩

/-- The transform of a realizable core decomposition lies in the restricted
bank. -/
lemma sphereTransform_subset_restrictedBank
    {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q)
    {C D : TripleSystemOn V} (hDC : D ⊆ C) :
    sphereTransform hq D ⊆ restrictedSphereTransformBank hq C := by
  intro U hU
  obtain ⟨T, hUT⟩ := (mem_sphereTransform_iff hq D U).mp hU
  by_cases hTD : T ∈ D
  · apply mem_union.mpr
    right
    exact mem_biUnion.mpr ⟨T, hDC hTD, by simpa [hTD] using hUT⟩
  · apply mem_union.mpr
    left
    apply (mem_sphereTransform_iff hq ∅ U).mpr
    exact ⟨T, by simpa [hTD] using hUT⟩

/-- The high-girth bank obtained by restricting in-sides to realizable core
decompositions. -/
noncomputable def realizableHighGirthCycleCoverBank
    (V : Type*) [Fintype V] [DecidableEq V]
    (Y : Finset V) {q : ℕ} (hq : 2 ≤ q) :
    TripleSystemOn (HighGirthCycleCoverVertex V q) := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  letI : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  exact restrictedSphereTransformBank hq (realizableCycleCoverBank V Y)

lemma realizableHighGirthCycleCoverBank_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {Y : Finset V}
    {q : ℕ} (hq : 2 ≤ q) :
    realizableHighGirthCycleCoverBank V Y hq ⊆
      highGirthCycleCoverBank V hq := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  exact restrictedSphereTransformBank_subset hq _

theorem realizableHighGirthCycleCover_hasLocalization
    {V : Type*} [Fintype V] [DecidableEq V]
    {Y : Finset V}
    {q : ℕ} (hq : 2 ≤ q) :
    HasAbsorberLocalization q (12 * q ^ 2)
      (highGirthCycleCoverGraph V hq)
      (Y.map (highGirthCycleCoverRootEmbedding V q))
      (realizableHighGirthCycleCoverBank V Y hq) :=
  ((highGirthCycleCover_hasLocalization hq).mono_roots (by
    intro x hx
    obtain ⟨y, hyY, rfl⟩ := mem_map.mp hx
    exact mem_map.mpr ⟨y, mem_univ y, rfl⟩)).mono_bank
      (realizableHighGirthCycleCoverBank_subset hq)

/-- Every triangle-divisible root graph has a high-girth switch contained in
the realizable bank. -/
theorem highGirthCycleCover_absorbs_in_realizableBank
    {V : Type*} [Fintype V] [DecidableEq V]
    {Y : Finset V}
    {q : ℕ} (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGsupport : GraphSupportedOn G (Y : Set V))
    (hG : TriangleDivisible G) :
    ∃ C : TripleSystemOn (HighGirthCycleCoverVertex V q),
      C ⊆ realizableHighGirthCycleCoverBank V Y hq ∧
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
  have hC₀bank : C₀ ⊆ realizableCycleCoverBank V Y :=
    subset_realizableCycleCoverBank_of_decomposition hGsupport hC₀
  have hpacking : IsPackingOn C :=
    sphereTransform_isPacking hq hC₀.isPackingOn
  refine ⟨C, sphereTransform_subset_restrictedBank hq hC₀bank,
    ?_, sphereTransform_girthGreater hq hC₀.isPackingOn⟩
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

theorem realizableHighGirthCycleCover_hasAbsorptionBank
    {V : Type*} [Fintype V] [DecidableEq V]
    {Y : Finset V}
    {q : ℕ} (hq : 2 ≤ q) (hV : 2 ≤ Fintype.card V) :
    HasHighGirthAbsorptionBank q
      (highGirthCycleCoverGraph V hq)
      (Y.map (highGirthCycleCoverRootEmbedding V q))
      (realizableHighGirthCycleCoverBank V Y hq) := by
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
    have hGsupport : GraphSupportedOn G (Y : Set V) := by
      intro a b hab
      have hmapped : L.Adj (f a) (f b) := by
        rw [← hmap, SimpleGraph.map_adj_apply]
        exact hab
      obtain ⟨ha, hb⟩ := hLsupported hmapped
      obtain ⟨a', ha'Y, ha'eq⟩ := mem_map.mp ha
      obtain ⟨b', hb'Y, hb'eq⟩ := mem_map.mp hb
      have haa' : a = a' := f.injective ha'eq.symm
      have hbb' : b = b' := f.injective hb'eq.symm
      exact ⟨haa' ▸ ha'Y, hbb' ▸ hb'Y⟩
    obtain ⟨C, hCB, hC⟩ :=
      highGirthCycleCover_absorbs_in_realizableBank
        hq hV G hGsupport hGdiv
    refine ⟨C, hCB, ?_⟩
    have hrootMap :
        G.map (highGirthCycleCoverRootEmbedding V q) = L := by
      simpa only [f] using hmap
    simpa only [hrootMap] using hC

/-- Every pair appearing in a bank triangle is either an absorber edge or
has both endpoints in the flexible root set. -/
def BankPairsSupported
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (B : TripleSystemOn V) : Prop :=
  ∀ T ∈ B, ∀ u ∈ T.1, ∀ v ∈ T.1, u ≠ v →
    H.Adj u v ∨ (u ∈ X ∧ v ∈ X)

/-- The realizable high-girth bank has no spurious pairs. -/
theorem realizableHighGirthCycleCover_bankPairsSupported
    {V : Type*} [Fintype V] [DecidableEq V]
    {Y : Finset V}
    {q : ℕ} (hq : 2 ≤ q) :
    BankPairsSupported
      (highGirthCycleCoverGraph V hq)
      (Y.map (highGirthCycleCoverRootEmbedding V q))
      (realizableHighGirthCycleCoverBank V Y hq) := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  intro U hUB x hxU y hyU hxy
  change U ∈ restrictedSphereTransformBank hq
      (realizableCycleCoverBank V Y) at hUB
  rcases mem_union.mp hUB with hout | hin
  · left
    apply Or.inl
    exact ⟨U, hout, hxU, hyU, hxy⟩
  · obtain ⟨T, hTcore, hUin⟩ := mem_biUnion.mp hin
    have hadjIn :
        (coveredGraph (attachSphereFamily hq T
          (sphereDecomposition hq true))).Adj x y :=
      ⟨U, hUin, hxU, hyU, hxy⟩
    cases x with
    | interior R z =>
        left
        apply Or.inl
        apply (coveredGraph_sphereTransform_adj_iff hq ∅ _ _).mpr
        exact ⟨T,
          (coveredGraph_attachedSphere_interior_left hq T true R z y).mp
            hadjIn⟩
    | root a =>
      cases y with
      | interior R z =>
          left
          apply Or.inl
          apply (coveredGraph_sphereTransform_adj_iff hq ∅ _ _).mpr
          exact ⟨T,
            (coveredGraph_attachedSphere_interior_right hq T true
              (SphereExpansionVertex.root a) R z).mp hadjIn⟩
      | root b =>
          have hroot := (attachedSphere_root_adj_iff hq T true a b).mp hadjIn
          rcases realizableCycleCoverBank_pair_supported hTcore
              hroot.2.1 hroot.2.2.1 hroot.2.2.2 with hfixed | hroots
          · left
            exact Or.inr (SimpleGraph.map_adj_apply.mpr hfixed)
          · right
            constructor
            · obtain ⟨r, _hr, rfl⟩ := mem_map.mp hroots.1
              exact mem_map.mpr ⟨r, _hr, rfl⟩
            · obtain ⟨r, _hr, rfl⟩ := mem_map.mp hroots.2
              exact mem_map.mpr ⟨r, _hr, rfl⟩

theorem BankPairsSupported.mapEmbedding
    {A W : Type*} [Fintype A] [DecidableEq A]
    [Fintype W] [DecidableEq W]
    {H : SimpleGraph A} {X : Finset A} {B : TripleSystemOn A}
    (h : BankPairsSupported H X B) (f : A ↪ W) :
    BankPairsSupported (H.map f) (X.map f) (mapTripleSystem f B) := by
  intro U hUB x hxU y hyU hxy
  obtain ⟨T, hTB, rfl⟩ := mem_map.mp hUB
  obtain ⟨a, haT, rfl⟩ := mem_map.mp hxU
  obtain ⟨b, hbT, rfl⟩ := mem_map.mp hyU
  have hab : a ≠ b := f.injective.ne_iff.mp hxy
  rcases h T hTB a haT b hbT hab with hH | hX
  · exact Or.inl (SimpleGraph.map_adj_apply.mpr hH)
  · exact Or.inr ⟨mem_map.mpr ⟨a, hX.1, rfl⟩,
      mem_map.mpr ⟨b, hX.2, rfl⟩⟩

/-- The realizable absorber padded into `Fin n`, with all crude numerical
bounds and the bank-pair support property retained. -/
theorem exists_paddedRealizableAbsorber
    {q m n : ℕ} (hm : 1 ≤ m)
    (hfit : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * m) ^ 156 ≤ n) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n),
        X.card = m ∧ HasHighGirthAbsorptionBank q H X B ∧
          HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
          BankPairsSupported H X B ∧
          (verticesOn B).card ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ∧
          (graphSupportFinset H).card ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ∧
          (∀ v, H.degree v ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156) ∧
          B.card ≤
            (highGirthAbsorberCardCoefficient (q + 2) *
              (2 * m) ^ 156) ^ 3 := by
  let q' := q + 2
  have hq' : 2 ≤ q' := by simp [q']
  let V := Fin (2 * m)
  have hV : 2 ≤ Fintype.card V := by
    simp only [V, Fintype.card_fin]
    omega
  let W := HighGirthCycleCoverVertex V q'
  have hWbound : Fintype.card W ≤
      highGirthAbsorberCardCoefficient q' * (2 * m) ^ 156 :=
    highGirthCycleCoverVertex_card_le q' (2 * m) (by omega)
  have hWcard : Fintype.card W ≤ n := by
    exact hWbound.trans (by simpa only [q'] using hfit)
  let f : W ↪ Fin n :=
    (Fintype.equivFin W).toEmbedding.trans (Fin.castLEEmb hWcard)
  let i : Fin m ↪ V := Fin.castLEEmb (by
    change m ≤ 2 * m
    omega)
  let Y : Finset V := (univ : Finset (Fin m)).map i
  let j : Fin m ↪ W :=
    i.trans (highGirthCycleCoverRootEmbedding V q')
  let X₀ : Finset W := (univ : Finset (Fin m)).map j
  let H : SimpleGraph (Fin n) :=
    (highGirthCycleCoverGraph V hq').map f
  let X : Finset (Fin n) := X₀.map f
  let B₀ : TripleSystemOn W :=
    realizableHighGirthCycleCoverBank V Y hq'
  let B : TripleSystemOn (Fin n) := mapTripleSystem f B₀
  refine ⟨H, X, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [X, X₀, card_map, card_univ, Fintype.card_fin]
  · have hYX : Y.map (highGirthCycleCoverRootEmbedding V q') = X₀ := by
      simp only [Y, X₀, j, map_map]
    have hA := realizableHighGirthCycleCover_hasAbsorptionBank
      (Y := Y) hq' hV
    have hAq : HasHighGirthAbsorptionBank q
        (highGirthCycleCoverGraph V hq') X₀ B₀ :=
      (hYX ▸ hA).cutoff_mono (by simp only [q']; omega)
    simpa only [H, X, B] using hAq.mapEmbedding f
  · have hX : X ⊆ (highGirthCycleCoverRoots V q').map f := by
      intro x hx
      obtain ⟨y, hyX₀, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hyX₀
      exact Finset.mem_map.mpr
        ⟨j a, Finset.mem_map.mpr ⟨i a, mem_univ _, rfl⟩, rfl⟩
    have hAfull :=
      (highGirthCycleCover_hasLocalization_mapEmbedding hq' f).mono_roots hX
    have hAmap := hAfull.mono_bank
      (mapTripleSystem_mono f (realizableHighGirthCycleCoverBank_subset
        (Y := Y) hq'))
    have hAq : HasAbsorberLocalization q (12 * q' ^ 2) H X B := by
      exact hAmap.cutoff_mono (by simp only [q']; omega)
    simpa only [q'] using hAq
  · have hbank :=
      (realizableHighGirthCycleCover_bankPairsSupported
        (Y := Y) hq').mapEmbedding f
    simpa only [H, X, B, X₀, Y, j, map_map] using hbank
  · rw [verticesOn_mapTripleSystem, card_map]
    exact (card_le_card (show verticesOn B₀ ⊆ (univ : Finset W) from
      subset_univ _)).trans (by
        simpa only [card_univ, q'] using hWbound)
  · have hsub : graphSupportFinset H ⊆
        (univ : Finset W).map f := by
      intro v hv
      obtain ⟨w, hvw⟩ := mem_graphSupportFinset_iff.mp hv
      change ((highGirthCycleCoverGraph V hq').map f).Adj v w at hvw
      obtain ⟨u, _z, _huz, hu, _hw⟩ :=
        (SimpleGraph.map_adj f
          (highGirthCycleCoverGraph V hq') v w).mp hvw
      exact mem_map.mpr ⟨u, mem_univ u, hu⟩
    exact (card_le_card hsub).trans
      (by simpa only [card_map, card_univ, q'] using hWbound)
  · intro v
    let : DecidableRel H.Adj := Classical.decRel H.Adj
    have hsub : H.neighborFinset v ⊆
        (univ : Finset W).map f := by
      intro y hy
      have hadj : H.Adj v y := by
        simpa only [SimpleGraph.mem_neighborFinset] using hy
      change ((highGirthCycleCoverGraph V hq').map f).Adj v y at hadj
      obtain ⟨u, w, _huw, _hu, hw⟩ :=
        (SimpleGraph.map_adj f (highGirthCycleCoverGraph V hq') v y).mp hadj
      exact mem_map.mpr ⟨w, mem_univ w, hw⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact (card_le_card hsub).trans
      (by simpa only [card_map, card_univ, q'] using hWbound)
  · change (mapTripleSystem f B₀).card ≤ _
    rw [card_mapTripleSystem]
    calc
      B₀.card ≤ Fintype.card (TripleOn W) := by
        simpa only [card_univ] using
          (card_le_card (show B₀ ⊆
            (univ : Finset (TripleOn W)) from subset_univ _))
      _ = Nat.choose (Fintype.card W) 3 := by
        simpa only [TripleOn] using (Fintype.card_finset_len (α := W) 3)
      _ ≤ Fintype.card W ^ 3 := Nat.choose_le_pow _ _
      _ ≤ (highGirthAbsorberCardCoefficient q' * (2 * m) ^ 156) ^ 3 :=
        pow_le_pow_left₀ zero_le hWbound 3
      _ = (highGirthAbsorberCardCoefficient (q + 2) *
          (2 * m) ^ 156) ^ 3 := by rfl

end

end Erdos207
