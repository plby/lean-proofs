/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.HighGirthAbsorber

/-!
# Padding a high-girth absorber

The concrete sphere-transform absorber is first constructed on a polynomially
small auxiliary type and is then embedded into the final vertex set.  This
file proves that the absorption property survives that padding and develops
the fiber-local family used to retain absorber localization in the larger
ambient type.
-/

namespace Erdos207

open Finset

noncomputable section

open scoped Classical

/-- Every vertex of a graph embedded from `V` has degree at most `|V|` in
the image graph. -/
theorem SimpleGraph.degree_map_le_card
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (f : V ↪ W) (w : W) :
    (G.map f).degree w ≤ Fintype.card V := by
  have hsub : (G.map f).neighborFinset w ⊆
      (univ : Finset V).map f := by
    intro y hy
    have hadj : (G.map f).Adj w y := by
      simpa only [SimpleGraph.mem_neighborFinset] using hy
    obtain ⟨u, v, huv, hu, hv⟩ :=
      (SimpleGraph.map_adj f G w y).mp hadj
    exact mem_map.mpr ⟨v, mem_univ v, hv⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact (card_le_card hsub).trans_eq (by simp)

/-- There are at most `|V|³` triples on a finite type. -/
theorem card_tripleOn_le_cube (V : Type*) [Fintype V] [DecidableEq V] :
    Fintype.card (TripleOn V) ≤ Fintype.card V ^ 3 := by
  calc
    Fintype.card (TripleOn V) = Nat.choose (Fintype.card V) 3 := by
      simpa only [TripleOn] using (Fintype.card_finset_len (α := V) 3)
    _ ≤ Fintype.card V ^ 3 := Nat.choose_le_pow _ _

/-- The absorption-bank property is preserved when isolated vertices are
added to the ambient type. -/
theorem HasHighGirthAbsorptionBank.mapEmbedding
    {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    {q : ℕ} {H : SimpleGraph A} {X : Finset A}
    {B : TripleSystemOn A}
    (h : HasHighGirthAbsorptionBank q H X B) (f : A ↪ W) :
    HasHighGirthAbsorptionBank q (H.map f) (X.map f)
      (mapTripleSystem f B) := by
  constructor
  · intro u hu v hv huv
    obtain ⟨a, haX, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b, hbX, rfl⟩ := Finset.mem_map.mp hv
    rw [SimpleGraph.map_adj_apply]
    exact h.1 a haX b hbX (f.injective.ne_iff.mp huv)
  · intro L _ hLsupport hLdiv
    let G : SimpleGraph A := L.comap f
    have hsuppRange : GraphSupportedOn L (Set.range f) := by
      intro u v huv
      obtain ⟨hu, hv⟩ := hLsupport huv
      constructor
      · obtain ⟨a, _haX, hau⟩ := Finset.mem_map.mp hu
        exact ⟨a, hau⟩
      · obtain ⟨b, _hbX, hbv⟩ := Finset.mem_map.mp hv
        exact ⟨b, hbv⟩
    have hmap : G.map f = L :=
      SimpleGraph.map_comap_eq_of_supportedOn_range f L hsuppRange
    have hGsupport : GraphSupportedOn G (X : Set A) := by
      intro a b hab
      have hmapped : L.Adj (f a) (f b) := by
        rw [← hmap, SimpleGraph.map_adj_apply]
        exact hab
      obtain ⟨ha, hb⟩ := hLsupport hmapped
      obtain ⟨a', ha'X, ha'eq⟩ := Finset.mem_map.mp ha
      obtain ⟨b', hb'X, hb'eq⟩ := Finset.mem_map.mp hb
      have haa' : a = a' := f.injective ha'eq.symm
      have hbb' : b = b' := f.injective hb'eq.symm
      simpa [haa', hbb'] using And.intro ha'X hb'X
    have hGdiv : TriangleDivisible G := by
      apply TriangleDivisible.of_map G f
      simpa only [hmap] using hLdiv
    obtain ⟨C, hCB, hC⟩ := h.2 G hGsupport hGdiv
    refine ⟨mapTripleSystem f C, mapTripleSystem_mono f hCB, ?_⟩
    have hCmap := hC.map f
    rw [SimpleGraph.map_sup_embedding, hmap] at hCmap
    exact hCmap

lemma sphereVertexLocalBank_subset_bank
    {V : Type*} [Fintype V] [LinearOrder V]
    {q : ℕ} (hq : 2 ≤ q) (x : SphereExpansionVertex V q) :
    sphereVertexLocalBank hq x ⊆ sphereTransformBank hq := by
  cases x with
  | root a => simp [sphereVertexLocalBank]
  | interior T z =>
      intro A hA
      simp only [sphereTransformBank, mem_biUnion]
      exact ⟨T, mem_univ T, hA⟩

/-- The image of the source sphere fiber containing `x`, and the empty
family when `x` is outside the padded absorber. -/
noncomputable def mappedSphereVertexLocalBank
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ} (f : SphereExpansionVertex V q ↪ W)
    (hq : 2 ≤ q) (x : W) : TripleSystemOn W :=
  if hx : ∃ a, f a = x then
    mapTripleSystem f (sphereVertexLocalBank hq (Classical.choose hx))
  else ∅

lemma mappedSphereVertexLocalBank_apply
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ} (f : SphereExpansionVertex V q ↪ W)
    (hq : 2 ≤ q) (a : SphereExpansionVertex V q) :
    mappedSphereVertexLocalBank f hq (f a) =
      mapTripleSystem f (sphereVertexLocalBank hq a) := by
  rw [mappedSphereVertexLocalBank, dif_pos ⟨a, rfl⟩]
  have ha : Classical.choose (show ∃ b, f b = f a from ⟨a, rfl⟩) = a := by
    apply f.injective
    exact Classical.choose_spec
      (show ∃ b, f b = f a from ⟨a, rfl⟩)
  rw [ha]

lemma mappedSphereVertexLocalBank_card_le
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ} (f : SphereExpansionVertex V q ↪ W)
    (hq : 2 ≤ q) (x : W) :
    (mappedSphereVertexLocalBank f hq x).card ≤ 4 * q := by
  rw [mappedSphereVertexLocalBank]
  split_ifs with hx
  · rw [card_mapTripleSystem]
    exact sphereVertexLocalBank_card_le hq _
  · simp

/-- The padded local family is the union of the embedded sphere fibers met by
the prescribed ambient triangles. -/
noncomputable def mappedSphereLocalFamily
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ} (f : SphereExpansionVertex V q ↪ W)
    (hq : 2 ≤ q) (R : TripleSystemOn W) : TripleSystemOn W :=
  R.biUnion fun U ↦ U.1.biUnion (mappedSphereVertexLocalBank f hq)

lemma mappedSphereLocalFamily_card_le
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ} (f : SphereExpansionVertex V q ↪ W)
    (hq : 2 ≤ q) (R : TripleSystemOn W) (hRq : R.card ≤ q) :
    (mappedSphereLocalFamily f hq R).card ≤ 12 * q ^ 2 := by
  calc
    (mappedSphereLocalFamily f hq R).card ≤
        ∑ U ∈ R,
          (U.1.biUnion (mappedSphereVertexLocalBank f hq)).card :=
      card_biUnion_le
    _ ≤ ∑ U ∈ R, ∑ x ∈ U.1, (4 * q) := by
      apply Finset.sum_le_sum
      intro U hUR
      exact card_biUnion_le.trans
        (Finset.sum_le_sum fun x _ ↦
          mappedSphereVertexLocalBank_card_le f hq x)
    _ = ∑ _U ∈ R, 3 * (4 * q) := by
      apply Finset.sum_congr rfl
      intro U hUR
      simp [U.2]
    _ = R.card * (3 * (4 * q)) := by simp
    _ ≤ q * (3 * (4 * q)) := Nat.mul_le_mul_right _ hRq
    _ = 12 * q ^ 2 := by ring

lemma mappedSphereFiber_subset_localFamily_of_interior_mem
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ} (f : SphereExpansionVertex V q ↪ W)
    (hq : 2 ≤ q) {R : TripleSystemOn W}
    (T : TripleOn V) (z : SphereInterior q)
    (hz : f (SphereExpansionVertex.interior T z) ∈ verticesOn R) :
    mapTripleSystem f (attachSphereFamily hq T (sphereBank hq)) ⊆
      mappedSphereLocalFamily f hq R := by
  obtain ⟨U, hUR, hzU⟩ := mem_biUnion.mp hz
  intro A hA
  simp only [mappedSphereLocalFamily, mem_biUnion]
  refine ⟨U, hUR, f (SphereExpansionVertex.interior T z), hzU, ?_⟩
  rw [mappedSphereVertexLocalBank_apply]
  exact mapTripleSystem_mono f (by
    intro S hS
    simpa [sphereVertexLocalBank] using hS) hA

/-- The sphere-transform localization axiom survives embedding the absorber
into a larger ambient vertex type.  Ambient configuration triangles outside
the image are handled by the private-interior-leaf argument itself. -/
theorem mappedSphereTransformBank_hasLocalization
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [DecidableEq W]
    {q : ℕ} (hq : 2 ≤ q)
    (f : SphereExpansionVertex V q ↪ W)
    (H : SimpleGraph W)
    (hOut : (sphereTransformOutGraph V hq).map f ≤ H)
    (X : Finset W)
    (hXroots : ∀ x ∈ X, ∃ a : V,
      x = f (SphereExpansionVertex.root a)) :
    HasAbsorberLocalization q (12 * q ^ 2) H X
      (mapTripleSystem f (sphereTransformBank hq)) := by
  intro K hHK R hRq hRtri
  let L_R := mappedSphereLocalFamily f hq R
  have hLRB : L_R ⊆ mapTripleSystem f (sphereTransformBank hq) := by
    intro A hA
    obtain ⟨U, hUR, x, hxU, hAx⟩ := by
      simpa only [L_R, mappedSphereLocalFamily, mem_biUnion] using hA
    rw [mappedSphereVertexLocalBank] at hAx
    split_ifs at hAx with hx
    · exact mapTripleSystem_mono f
        (sphereVertexLocalBank_subset_bank hq _) hAx
    · simp at hAx
  refine ⟨L_R, hLRB, mappedSphereLocalFamily_card_le f hq R hRq, ?_⟩
  intro r hr5 hrq E hE hRE
  by_cases hlocal :
      E ∩ mapTripleSystem f (sphereTransformBank hq) ⊆ L_R
  · exact Or.inl hlocal
  · right
    rw [not_subset] at hlocal
    obtain ⟨A, hAEB, hAnotLocal⟩ := hlocal
    have hAE : A ∈ E := (mem_inter.mp hAEB).1
    have hAB : A ∈ mapTripleSystem f (sphereTransformBank hq) :=
      (mem_inter.mp hAEB).2
    obtain ⟨A₀, hA₀B, rfl⟩ := Finset.mem_map.mp hAB
    obtain ⟨T, _hTuniv, hA₀fiber⟩ := by
      simpa only [sphereTransformBank, mem_biUnion] using hA₀B
    let D₀ : TripleSystemOn (SphereExpansionVertex V q) :=
      (attachSphereFamily hq T (sphereBank hq)).filter fun S ↦
        mapTriple f S ∈ E
    have hD₀fiber : D₀ ⊆ attachSphereFamily hq T (sphereBank hq) :=
      filter_subset _ _
    have hmapD₀E : mapTripleSystem f D₀ ⊆ E := by
      intro U hU
      obtain ⟨S, hSD₀, rfl⟩ := Finset.mem_map.mp hU
      exact (mem_filter.mp hSD₀).2
    have hA₀D₀ : A₀ ∈ D₀ :=
      mem_filter.mpr ⟨hA₀fiber, hAE⟩
    have hD₀ne : D₀.Nonempty := ⟨A₀, hA₀D₀⟩
    have hD₀card : D₀.card ≤ q := by
      calc
        D₀.card = (mapTripleSystem f D₀).card :=
          (card_mapTripleSystem f D₀).symm
        _ ≤ E.card := card_le_card hmapD₀E
        _ = r - 2 := hE.1.1
        _ ≤ q := by omega
    have hD₀packing : IsPackingOn D₀ := by
      apply IsPackingOn.of_map (f := f)
      exact (IsErdosConfig.isPackingOn hE hr5).mono hmapD₀E
    obtain ⟨z, hzD₀, hzone⟩ :=
      attachSphereFamily_short_interior_leaf hq T hD₀fiber hD₀packing
        hD₀ne hD₀card
    let x₀ : SphereExpansionVertex V q :=
      SphereExpansionVertex.interior T z
    let x : W := f x₀
    have hxD₀ : x₀ ∈ verticesOn D₀ := hzD₀
    have hxnotR : x ∉ verticesOn R := by
      intro hxR
      have hfiberLocal :=
        mappedSphereFiber_subset_localFamily_of_interior_mem
          f hq T z hxR
      apply hAnotLocal
      apply hfiberLocal
      exact (mem_mapTripleSystem_iff f _ A₀).mpr hA₀fiber
    have hexternal : ∃ S : TripleOn W,
        S ∈ E ∧ x ∈ S.1 ∧
          S ∉ mapTripleSystem f (sphereTransformBank hq) := by
      by_contra hnone
      push Not at hnone
      have hthrough :
          triplesThrough E x = triplesThrough (mapTripleSystem f D₀) x := by
        ext S
        simp only [triplesThrough, mem_filter]
        constructor
        · rintro ⟨hSE, hxS⟩
          have hSB : S ∈ mapTripleSystem f (sphereTransformBank hq) :=
            hnone S hSE hxS
          obtain ⟨S₀, hS₀B, rfl⟩ := Finset.mem_map.mp hSB
          have hxS₀ : x₀ ∈ S₀.1 := by
            exact (mem_mapTriple_apply_iff f S₀ x₀).mp hxS
          have hS₀fiber := sphereTransformBank_interior_fiber
            hq hS₀B T z hxS₀
          exact ⟨(mem_mapTripleSystem_iff f D₀ S₀).mpr
            (mem_filter.mpr ⟨hS₀fiber, hSE⟩), hxS⟩
        · rintro ⟨hSD, hxS⟩
          exact ⟨hmapD₀E hSD, hxS⟩
      have hxmap : x ∈ verticesOn (mapTripleSystem f D₀) := by
        rw [verticesOn_mapTripleSystem]
        exact Finset.mem_map.mpr ⟨x₀, hxD₀, rfl⟩
      have hxtwo := IsErdosConfig.two_le_card_triplesThrough
        (x := x) hE hr5 (verticesOn_mono hmapD₀E hxmap)
      rw [hthrough, triplesThrough_map_apply, card_mapTripleSystem,
        hzone] at hxtwo
      omega
    obtain ⟨S, hSE, hxS, hSnotB⟩ := hexternal
    have hSnotR : S ∉ R := by
      intro hSR
      apply hxnotR
      exact mem_biUnion.mpr ⟨S, hSR, hxS⟩
    refine ⟨S, hSE, ?_, x, hxS, ?_, ?_⟩
    · simp [hSnotR, hSnotB]
    · obtain ⟨A₁, hA₁D₀, hxA₁⟩ := mem_biUnion.mp hxD₀
      have hA₁fiber :
          A₁ ∈ attachSphereFamily hq T (sphereBank hq) :=
        hD₀fiber hA₁D₀
      obtain ⟨y₀, hyA₁, hyx⟩ := Finset.exists_mem_ne
        (by rw [A₁.2]; omega) x₀
      refine ⟨f y₀, hOut ?_⟩
      rw [SimpleGraph.map_adj_apply]
      exact sphereBank_interior_edge_in_outGraph
        hq T hA₁fiber hxA₁ hyA₁ hyx.symm
    · intro hxX
      obtain ⟨a, ha⟩ := hXroots x hxX
      have hsource : x₀ = SphereExpansionVertex.root a :=
        f.injective (by simpa [x] using ha)
      change SphereExpansionVertex.interior T z =
        SphereExpansionVertex.root a at hsource
      cases hsource

/-- The concrete high-girth cycle-cover absorber retains localization after
it is padded into any finite ambient type. -/
theorem highGirthCycleCover_hasLocalization_mapEmbedding
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {q : ℕ} (hq : 2 ≤ q)
    (f : HighGirthCycleCoverVertex V q ↪ W) :
    HasAbsorberLocalization q (12 * q ^ 2)
      ((highGirthCycleCoverGraph V hq).map f)
      ((highGirthCycleCoverRoots V q).map f)
      (mapTripleSystem f (highGirthCycleCoverBank V hq)) := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  apply mappedSphereTransformBank_hasLocalization hq f
  · apply SimpleGraph.map_monotone f
    intro x y hxy
    exact Or.inl hxy
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hy
    exact ⟨cycleCoverRootEmbedding V a, rfl⟩

/-- A concrete absorber on exactly `n` ambient vertices.  The only numerical
hypothesis says that the polynomial-size sphere construction fits inside
`Fin n`; all remaining vertices are isolated in the absorber graph. -/
theorem exists_paddedEfficientAbsorber
    {q m n : ℕ} (hm : 1 ≤ m)
    (hfit : highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156 ≤ n) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n),
        X.card = m ∧ HasHighGirthAbsorptionBank q H X B ∧
          HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
          (∀ v, H.degree v ≤
            highGirthAbsorberCardCoefficient (q + 2) * (2 * m) ^ 156) ∧
          B.card ≤
            (highGirthAbsorberCardCoefficient (q + 2) *
              (2 * m) ^ 156) ^ 3 ∧
          ∃ (f : HighGirthCycleCoverVertex (Fin (2 * m)) (q + 2) ↪ Fin n)
              (i : Fin m ↪ Fin (2 * m)),
            H = (highGirthCycleCoverGraph (Fin (2 * m))
                (show 2 ≤ q + 2 by omega)).map f ∧
            X = ((univ : Finset (Fin m)).map
                (i.trans (highGirthCycleCoverRootEmbedding
                  (Fin (2 * m)) (q + 2)))).map f ∧
            B = mapTripleSystem f
              (highGirthCycleCoverBank (Fin (2 * m))
                (show 2 ≤ q + 2 by omega)) := by
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
  let j : Fin m ↪ W :=
    i.trans (highGirthCycleCoverRootEmbedding V q')
  let X₀ : Finset W := (univ : Finset (Fin m)).map j
  let H : SimpleGraph (Fin n) :=
    (highGirthCycleCoverGraph V hq').map f
  let X : Finset (Fin n) := X₀.map f
  let B : TripleSystemOn (Fin n) :=
    mapTripleSystem f (highGirthCycleCoverBank V hq')
  refine ⟨H, X, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [X, X₀, card_map, card_univ, Fintype.card_fin]
  · have hX₀ : X₀ ⊆ highGirthCycleCoverRoots V q' := by
      intro x hx
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_map.mpr ⟨i a, mem_univ _, rfl⟩
    have hA :=
      (highGirthCycleCover_hasAbsorptionBank hq' hV).mono_roots hX₀
    have hAq : HasHighGirthAbsorptionBank q
        (highGirthCycleCoverGraph V hq') X₀
        (highGirthCycleCoverBank V hq') :=
      hA.cutoff_mono (by simp only [q']; omega)
    simpa only [H, X, B] using hAq.mapEmbedding f
  · have hX : X ⊆ (highGirthCycleCoverRoots V q').map f := by
      intro x hx
      obtain ⟨y, hyX₀, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hyX₀
      exact Finset.mem_map.mpr
        ⟨j a, Finset.mem_map.mpr ⟨i a, mem_univ _, rfl⟩, rfl⟩
    have hA :=
      (highGirthCycleCover_hasLocalization_mapEmbedding hq' f).mono_roots hX
    have hAq : HasAbsorberLocalization q (12 * q' ^ 2) H X B :=
      hA.cutoff_mono (by simp only [q']; omega)
    simpa only [q'] using hAq
  · intro v
    let : DecidableRel H.Adj := Classical.decRel H.Adj
    have hsub : H.neighborFinset v ⊆
        (univ : Finset W).map f := by
      intro y hy
      have hadj : H.Adj v y := by
        simpa only [SimpleGraph.mem_neighborFinset] using hy
      change ((highGirthCycleCoverGraph V hq').map f).Adj v y at hadj
      obtain ⟨u, w, huw, hu, hw⟩ :=
        (SimpleGraph.map_adj f (highGirthCycleCoverGraph V hq') v y).mp hadj
      exact mem_map.mpr ⟨w, mem_univ w, hw⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact (card_le_card hsub).trans
      (by simpa only [card_map, card_univ, q'] using hWbound)
  · change (mapTripleSystem f
      (highGirthCycleCoverBank V hq')).card ≤ _
    rw [card_mapTripleSystem]
    calc
      (highGirthCycleCoverBank V hq').card ≤
          Fintype.card (TripleOn W) := by
        simpa only [card_univ] using
          (card_le_card (show highGirthCycleCoverBank V hq' ⊆
            (univ : Finset (TripleOn W)) from subset_univ _))
      _ ≤ Fintype.card W ^ 3 := card_tripleOn_le_cube W
      _ ≤ (highGirthAbsorberCardCoefficient q' * (2 * m) ^ 156) ^ 3 :=
        pow_le_pow_left₀ zero_le hWbound 3
      _ = (highGirthAbsorberCardCoefficient (q + 2) *
          (2 * m) ^ 156) ^ 3 := by rfl
  · refine ⟨f, i, ?_, ?_, ?_⟩ <;> rfl

end

end Erdos207
