/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberRootTriples
import ErdosProblems.Erdos207.InitialPairAvailability

/-!
# Root candidates in the sphere absorber

Every non-root vertex of the sphere expansion belongs to one attached
sphere.  Hence it can interact with at most the three roots of that sphere.
The small candidate set below makes this bounded-root-incidence statement
available to the initial typicality argument.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Roots of the unique attached sphere containing an expansion vertex.
Root vertices themselves have no local sphere fiber. -/
def sphereExpansionRootCandidates
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} :
    SphereExpansionVertex V q → Finset V
  | .root _ => ∅
  | .interior T _ => T.1

@[simp]
lemma sphereExpansionRootCandidates_root
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (a : V) :
    sphereExpansionRootCandidates (q := q)
      (SphereExpansionVertex.root a) = ∅ := rfl

@[simp]
lemma sphereExpansionRootCandidates_interior
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ}
    (T : TripleOn V) (z : SphereInterior q) :
    sphereExpansionRootCandidates
      (SphereExpansionVertex.interior T z) = T.1 := rfl

lemma card_sphereExpansionRootCandidates_le_three
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ}
    (x : SphereExpansionVertex V q) :
    (sphereExpansionRootCandidates x).card ≤ 3 := by
  cases x with
  | root a => simp
  | interior T z => simp [T.2]

/-- If an attached triangle contains a root, that root belongs to the base
triple indexing the attached sphere. -/
lemma root_mem_of_mem_attachSphereTriple
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (R : TripleOn V) (S : TripleOn (SphereVertex q)) (a : V)
    (ha : SphereExpansionVertex.root a ∈
      (attachSphereTriple hq R S).1) :
    a ∈ R.1 := by
  obtain ⟨y, hyS, hy⟩ := Finset.mem_map.mp ha
  obtain ⟨i, _hyi, hia⟩ :=
    exists_rootIndex_of_attach_eq_root hq R hy
  rw [← hia]
  exact tripleVertex_mem R i

/-- An interior vertex in an attached triangle identifies its fiber, so any
root in the same triangle is one of that fiber's three roots. -/
lemma root_mem_candidates_of_bank_interior
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    {U : TripleOn (SphereExpansionVertex V q)}
    (hU : U ∈ sphereTransformBank hq) {a : V}
    (haU : SphereExpansionVertex.root a ∈ U.1)
    (R : TripleOn V) (z : SphereInterior q)
    (hzU : SphereExpansionVertex.interior R z ∈ U.1) :
    a ∈ sphereExpansionRootCandidates
      (SphereExpansionVertex.interior R z) := by
  have hUfiber := sphereTransformBank_interior_fiber hq hU R z hzU
  obtain ⟨S, _hSbank, hSU⟩ := Finset.mem_map.mp hUfiber
  rw [← hSU] at haU
  exact root_mem_of_mem_attachSphereTriple hq R S a haU

/-- Every universal-bank triangle contains a private sphere-interior vertex. -/
lemma exists_interior_mem_sphereTransformBank
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    {U : TripleOn (SphereExpansionVertex V q)}
    (hU : U ∈ sphereTransformBank hq) :
    ∃ R : TripleOn V, ∃ z : SphereInterior q,
      SphereExpansionVertex.interior R z ∈ U.1 := by
  obtain ⟨R, _hRuniv, hUR⟩ := by
    simpa only [sphereTransformBank, mem_biUnion] using hU
  obtain ⟨S, hSbank, rfl⟩ := Finset.mem_map.mp hUR
  obtain ⟨t, _htuniv, rfl⟩ := Finset.mem_image.mp hSbank
  obtain ⟨z, hz⟩ := exists_interior_mem_sphereTriangle hq t
  refine ⟨R, z, ?_⟩
  rw [← attachSphereVertex_interior R z]
  exact Finset.mem_map.mpr ⟨z.1, hz, rfl⟩

/-- If every triangle of an Erdős configuration outside the mapped
universal bank is already prescribed by `R`, then its entire bank part lies
in the explicit union of sphere fibers touched by `R`.  This is the local
half of absorber localization with the actual local family exposed. -/
theorem inter_mappedSphereBank_subset_localFamily_of_outside_subset
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [DecidableEq W]
    {q r : ℕ} (hq : 2 ≤ q)
    (f : SphereExpansionVertex V q ↪ W)
    {R E : TripleSystemOn W}
    (hr5 : 5 ≤ r) (hrq : r ≤ q) (hE : IsErdosConfigOn r E)
    (houtside : E \ mapTripleSystem f (sphereTransformBank hq) ⊆ R) :
    E ∩ mapTripleSystem f (sphereTransformBank hq) ⊆
      mappedSphereLocalFamily f hq R := by
  intro A hA
  by_contra hAnotLocal
  have hAE : A ∈ E := (mem_inter.mp hA).1
  have hAB : A ∈ mapTripleSystem f (sphereTransformBank hq) :=
    (mem_inter.mp hA).2
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
  have hA₀D₀ : A₀ ∈ D₀ := mem_filter.mpr ⟨hA₀fiber, hAE⟩
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
      mappedSphereFiber_subset_localFamily_of_interior_mem f hq T z hxR
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
        have hxS₀ : x₀ ∈ S₀.1 :=
          (mem_mapTriple_apply_iff f S₀ x₀).mp hxS
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
  have hSR : S ∈ R :=
    houtside (mem_sdiff.mpr ⟨hSE, hSnotB⟩)
  exact hxnotR (mem_biUnion.mpr ⟨S, hSR, hxS⟩)

/-- Root candidates after embedding a sphere expansion in a larger ambient
type.  Vertices outside the embedded absorber have no candidates. -/
noncomputable def mappedSphereRootCandidates
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ}
    (f : SphereExpansionVertex V q ↪ W) (y : W) : Finset V := by
  classical
  exact if hy : ∃ x, f x = y then
    sphereExpansionRootCandidates (Classical.choose hy)
  else ∅

lemma mappedSphereRootCandidates_apply
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ}
    (f : SphereExpansionVertex V q ↪ W)
    (x : SphereExpansionVertex V q) :
    mappedSphereRootCandidates f (f x) =
      sphereExpansionRootCandidates x := by
  rw [mappedSphereRootCandidates, dif_pos ⟨x, rfl⟩]
  have hx : Classical.choose
      (show ∃ y, f y = f x from ⟨x, rfl⟩) = x := by
    apply f.injective
    exact Classical.choose_spec
      (show ∃ y, f y = f x from ⟨x, rfl⟩)
  rw [hx]

lemma card_mappedSphereRootCandidates_le_three
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ}
    (f : SphereExpansionVertex V q ↪ W) (y : W) :
    (mappedSphereRootCandidates f y).card ≤ 3 := by
  rw [mappedSphereRootCandidates]
  split_ifs with hy
  · exact card_sphereExpansionRootCandidates_le_three _
  · simp

/-- A mapped local-fiber triangle containing a mapped root charges that root
to the candidate set of the vertex which selected the fiber. -/
lemma root_mem_mappedCandidates_of_mem_mappedVertexLocalBank
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ} (hq : 2 ≤ q)
    (f : SphereExpansionVertex V q ↪ W)
    {y : W} {A : TripleOn W} {a : V}
    (hA : A ∈ mappedSphereVertexLocalBank f hq y)
    (haA : f (SphereExpansionVertex.root a) ∈ A.1) :
    a ∈ mappedSphereRootCandidates f y := by
  rw [mappedSphereVertexLocalBank] at hA
  rw [mappedSphereRootCandidates]
  split_ifs at hA ⊢ with hy
  · let x := Classical.choose hy
    have hxy : f x = y := Classical.choose_spec hy
    obtain ⟨A₀, hA₀, hAmap⟩ := Finset.mem_map.mp hA
    have haA₀ : SphereExpansionVertex.root a ∈ A₀.1 := by
      have haAmap : f (SphereExpansionVertex.root a) ∈
          (mapTriple f A₀).1 := by
        rw [show mapTriple f A₀ = A by exact hAmap]
        exact haA
      exact (mem_mapTriple_apply_iff f A₀
        (SphereExpansionVertex.root a)).mp haAmap
    change A₀ ∈ sphereVertexLocalBank hq x at hA₀
    change a ∈ sphereExpansionRootCandidates x
    cases hx : x with
    | root b =>
        rw [hx] at hA₀
        simp [sphereVertexLocalBank] at hA₀
    | interior R z =>
        rw [sphereExpansionRootCandidates_interior]
        have hA₀fiber : A₀ ∈ attachSphereFamily hq R (sphereBank hq) := by
          rw [hx] at hA₀
          simpa [sphereVertexLocalBank] using hA₀
        obtain ⟨S, _hSbank, hSmap⟩ := Finset.mem_map.mp hA₀fiber
        rw [← hSmap] at haA₀
        exact root_mem_of_mem_attachSphereTriple hq R S a haA₀
  · simp at hA

/-- Membership in the explicit local family of a singleton triangle charges
every mapped root of a local bank triangle to one of the three vertices of
that singleton. -/
lemma exists_vertex_root_mem_mappedCandidates_of_local_singleton
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ} (hq : 2 ≤ q)
    (f : SphereExpansionVertex V q ↪ W)
    {T A : TripleOn W} {a : V}
    (hA : A ∈ mappedSphereLocalFamily f hq ({T} : TripleSystemOn W))
    (haA : f (SphereExpansionVertex.root a) ∈ A.1) :
    ∃ y ∈ T.1, a ∈ mappedSphereRootCandidates f y := by
  simp only [mappedSphereLocalFamily, mem_biUnion] at hA
  obtain ⟨U, hUT, y, hyU, hAy⟩ := hA
  have hU : U = T := by simpa using hUT
  subst U
  exact ⟨y, hyU,
    root_mem_mappedCandidates_of_mem_mappedVertexLocalBank hq f hAy haA⟩

/-- A singleton forbidden completion through a mapped root is charged to a
root candidate of one of its three vertices.  The order-four case is ruled
out by packinghood; at order at least five the private-interior-leaf argument
forces the bank part into the explicit local family. -/
theorem exists_vertex_root_mem_mappedCandidates_of_singleton_forbidden
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [DecidableEq W]
    {q q₀ : ℕ} (hq : 2 ≤ q) (hq₀q : q₀ ≤ q)
    (f : SphereExpansionVertex V q ↪ W)
    {B : TripleSystemOn W} (hB : B ⊆
      mapTripleSystem f (sphereTransformBank hq))
    {T : TripleOn W} {a : V}
    (haT : f (SphereExpansionVertex.root a) ∈ T.1)
    (hcomplete : CompletesForbidden
      (absorberErdosForbiddenConfigurationsOn q₀ B) ∅ T) :
    ∃ y ∈ T.1, a ∈ mappedSphereRootCandidates f y := by
  obtain ⟨S, hSF, hTS, hSerase⟩ := hcomplete
  have hS : S = {T} := by
    ext U
    constructor
    · intro hUS
      by_cases hUT : U = T
      · simpa [hUT]
      · have hUerase : U ∈ S.erase T := mem_erase.mpr ⟨hUT, hUS⟩
        have : U ∈ (∅ : TripleSystemOn W) := hSerase hUerase
        simp at this
    · intro hU
      have hUT : U = T := by simpa only [mem_singleton] using hU
      subst U
      exact hTS
  subst S
  obtain ⟨_hne, r, hr4, hrq₀, E, hE, hEpacking, hEout⟩ :=
    mem_absorberErdosForbiddenConfigurationsOn_iff.mp hSF
  have hTE : T ∈ E := by
    have hTdiff : T ∈ E \ B := by simpa only [hEout]
    exact (mem_sdiff.mp hTdiff).1
  by_cases hr5 : 5 ≤ r
  · have houtside :
        E \ mapTripleSystem f (sphereTransformBank hq) ⊆
          ({T} : TripleSystemOn W) := by
      intro U hU
      have hUnotB : U ∉ B := fun hUB ↦ (mem_sdiff.mp hU).2 (hB hUB)
      have hUdiff : U ∈ E \ B := mem_sdiff.mpr ⟨(mem_sdiff.mp hU).1, hUnotB⟩
      simpa only [hEout] using hUdiff
    have hlocal :=
      inter_mappedSphereBank_subset_localFamily_of_outside_subset
        hq f hr5 (hrq₀.trans hq₀q) hE houtside
    have haroot : f (SphereExpansionVertex.root a) ∈ verticesOn E :=
      mem_biUnion.mpr ⟨T, hTE, haT⟩
    have hthrough := IsErdosConfig.two_le_card_triplesThrough hE hr5 haroot
    have hTthrough : T ∈ triplesThrough E
        (f (SphereExpansionVertex.root a)) :=
      mem_filter.mpr ⟨hTE, haT⟩
    obtain ⟨A, hAthrough, hAT⟩ :=
      Finset.exists_mem_ne (s := triplesThrough E
        (f (SphereExpansionVertex.root a))) (by omega) T
    have hAE : A ∈ E := (mem_filter.mp hAthrough).1
    have haA : f (SphereExpansionVertex.root a) ∈ A.1 :=
      (mem_filter.mp hAthrough).2
    have hAfull : A ∈ mapTripleSystem f (sphereTransformBank hq) := by
      by_contra hAnotFull
      have hAnotB : A ∉ B := fun hAB ↦ hAnotFull (hB hAB)
      have hAdiff : A ∈ E \ B := mem_sdiff.mpr ⟨hAE, hAnotB⟩
      have : A = T := by simpa only [hEout, mem_singleton] using hAdiff
      exact hAT this
    have hAlocal : A ∈
        mappedSphereLocalFamily f hq ({T} : TripleSystemOn W) :=
      hlocal (mem_inter.mpr ⟨hAE, hAfull⟩)
    exact exists_vertex_root_mem_mappedCandidates_of_local_singleton
      hq f hAlocal haA
  · have hr : r = 4 := by omega
    have hconfig4 : IsConfigOn 4 2 E := by
      simpa [hr] using hE.1
    exact (hEpacking.no_four_config ⟨E, Subset.rfl, hconfig4⟩).elim

/-- Candidate roots contributed by the two fixed endpoints of a pair. -/
def mappedSpherePairRootCandidates
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ}
    (f : SphereExpansionVertex V q ↪ W) (u v : W) : Finset V :=
  mappedSphereRootCandidates f u ∪ mappedSphereRootCandidates f v

lemma card_mappedSpherePairRootCandidates_le_six
    {V W : Type*} [Fintype V] [LinearOrder V]
    [DecidableEq W] {q : ℕ}
    (f : SphereExpansionVertex V q ↪ W) (u v : W) :
    (mappedSpherePairRootCandidates f u v).card ≤ 6 := by
  exact (card_union_le _ _).trans (by
    have hu := card_mappedSphereRootCandidates_le_three f u
    have hv := card_mappedSphereRootCandidates_le_three f v
    omega)

/-- A universal-bank triangle through a fixed pair and a mapped root charges
the root to one of the endpoint candidate sets. -/
lemma root_mem_pairCandidates_of_thirdVertexTriple_mem_bank
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [DecidableEq W]
    {q : ℕ} (hq : 2 ≤ q)
    (f : SphereExpansionVertex V q ↪ W)
    {u v : W} (huv : u ≠ v) (w : ThirdVertex u v) (a : V)
    (hw : w.1 = f (SphereExpansionVertex.root a))
    (hbank : thirdVertexTriple huv w ∈
      mapTripleSystem f (sphereTransformBank hq)) :
    a ∈ mappedSpherePairRootCandidates f u v := by
  obtain ⟨U, hUbank, hUmap⟩ := Finset.mem_map.mp hbank
  have hrootU : SphereExpansionVertex.root a ∈ U.1 := by
    apply (mem_mapTriple_apply_iff f U
      (SphereExpansionVertex.root a)).mp
    have hrootMap : f (SphereExpansionVertex.root a) ∈
        (mapTriple f U).1 := by
      rw [show mapTriple f U = thirdVertexTriple huv w by exact hUmap,
        ← hw]
      exact third_mem_thirdVertexTriple huv w
    exact hrootMap
  obtain ⟨R, z, hzU⟩ := exists_interior_mem_sphereTransformBank hq hUbank
  have hzin : f (SphereExpansionVertex.interior R z) ∈
      (thirdVertexTriple huv w).1 := by
    rw [← hUmap]
    exact Finset.mem_map.mpr
      ⟨SphereExpansionVertex.interior R z, hzU, rfl⟩
  have haroot : a ∈ sphereExpansionRootCandidates
      (SphereExpansionVertex.interior R z) :=
    root_mem_candidates_of_bank_interior hq hUbank hrootU R z hzU
  simp only [thirdVertexTriple, tripleOfThree, mem_insert,
    mem_singleton] at hzin
  rcases hzin with hzu | hzv | hzw
  · apply mem_union.mpr
    left
    rw [← hzu, mappedSphereRootCandidates_apply]
    exact haroot
  · apply mem_union.mpr
    right
    rw [← hzv, mappedSphereRootCandidates_apply]
    exact haroot
  · have hcontra : SphereExpansionVertex.interior R z =
        SphereExpansionVertex.root a := by
      apply f.injective
      rw [hzw, hw]
    cases hcontra

/-- The same endpoint charge for a singleton forbidden completion. -/
lemma root_mem_pairCandidates_of_thirdVertexTriple_forbidden
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [DecidableEq W]
    {q q₀ : ℕ} (hq : 2 ≤ q) (hq₀q : q₀ ≤ q)
    (f : SphereExpansionVertex V q ↪ W)
    {B : TripleSystemOn W} (hB : B ⊆
      mapTripleSystem f (sphereTransformBank hq))
    {u v : W} (huv : u ≠ v) (w : ThirdVertex u v) (a : V)
    (hw : w.1 = f (SphereExpansionVertex.root a))
    (hcomplete : CompletesForbidden
      (absorberErdosForbiddenConfigurationsOn q₀ B) ∅
      (thirdVertexTriple huv w)) :
    a ∈ mappedSpherePairRootCandidates f u v := by
  have hroot : f (SphereExpansionVertex.root a) ∈
      (thirdVertexTriple huv w).1 := by
    rw [← hw]
    exact third_mem_thirdVertexTriple huv w
  obtain ⟨y, hyT, hay⟩ :=
    exists_vertex_root_mem_mappedCandidates_of_singleton_forbidden
      hq hq₀q f hB hroot hcomplete
  simp only [thirdVertexTriple, tripleOfThree, mem_insert,
    mem_singleton] at hyT
  rcases hyT with rfl | rfl | hyw
  · exact mem_union.mpr (Or.inl hay)
  · exact mem_union.mpr (Or.inr hay)
  · rw [hw] at hyw
    have hempty : mappedSphereRootCandidates f y = ∅ := by
      rw [hyw, mappedSphereRootCandidates_apply]
      rfl
    rw [hempty] at hay
    simp at hay

end

end Erdos207
