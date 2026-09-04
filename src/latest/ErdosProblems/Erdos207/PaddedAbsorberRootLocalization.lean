/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCoreRootCandidates

/-!
# Root localization for the padded absorber

The six-point bound for singleton completions is the zero-dimensional end of
a stronger fact.  If a forbidden outside family contains a designated
triangle through a flexible root, then either that root already occurs in a
different outside triangle, or it is one of the boundedly many absorber roots
charged to a vertex of the other outside triangles or to a different vertex
of the designated triangle.  This is the bank-independent rooted estimate
needed at the small end of the vortex.
-/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

/-- Abstract form of the extra root-locality supplied by the explicit padded
absorber. -/
def HasPaddedAbsorberRootLocalization
    {W : Type*} [Fintype W] [DecidableEq W]
    (q : ℕ) (X : Finset W) (B : TripleSystemOn W) : Prop :=
  ∃ candidates : W → Finset W,
    (∀ y, (candidates y).card ≤ 14) ∧
    ∀ S ∈ absorberErdosForbiddenConfigurationsOn q B,
      ∀ T ∈ S, ∀ x ∈ X, x ∈ T.1 →
        x ∈ verticesOn (S.erase T) ∨
          ∃ y ∈ verticesOn (S.erase T) ∪ T.1.erase x,
            x ∈ candidates y

/-- General form of the sphere-fiber root charge.  The singleton statement
used for the six-point endpoint is recovered when `S.erase T` is empty. -/
lemma sphereRoot_localized_of_forbidden
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [DecidableEq W]
    {q q₀ : ℕ} (hq : 2 ≤ q) (hq₀q : q₀ ≤ q)
    (f : SphereExpansionVertex V q ↪ W)
    {B : TripleSystemOn W}
    (hB : B ⊆ mapTripleSystem f (sphereTransformBank hq))
    {S : TripleSystemOn W} {T : TripleOn W} {a : V}
    (hSF : S ∈ absorberErdosForbiddenConfigurationsOn q₀ B)
    (hTS : T ∈ S)
    (haT : f (SphereExpansionVertex.root a) ∈ T.1) :
    f (SphereExpansionVertex.root a) ∈ verticesOn (S.erase T) ∨
      ∃ y ∈ verticesOn (S.erase T) ∪
          T.1.erase (f (SphereExpansionVertex.root a)),
        a ∈ mappedSphereRootCandidates f y := by
  obtain ⟨_hne, r, hr4, hrq₀, E, hE, hEpacking, hEout⟩ :=
    mem_absorberErdosForbiddenConfigurationsOn_iff.mp hSF
  have hr5 : 5 ≤ r := by
    by_contra hr5
    have hr : r = 4 := by omega
    have hconfig4 : IsConfigOn 4 2 E := by
      simpa [hr] using hE.1
    exact (hEpacking.no_four_config ⟨E, Subset.rfl, hconfig4⟩).elim
  have hTE : T ∈ E := by
    have hTdiff : T ∈ E \ B := by
      rw [hEout]
      exact hTS
    exact (mem_sdiff.mp hTdiff).1
  have houtside :
      E \ mapTripleSystem f (sphereTransformBank hq) ⊆ S := by
    intro U hU
    have hUnotB : U ∉ B := fun hUB ↦ (mem_sdiff.mp hU).2 (hB hUB)
    have hUdiff : U ∈ E \ B :=
      mem_sdiff.mpr ⟨(mem_sdiff.mp hU).1, hUnotB⟩
    rw [hEout] at hUdiff
    exact hUdiff
  have hlocal : E ∩ mapTripleSystem f (sphereTransformBank hq) ⊆
      mappedSphereLocalFamily f hq S :=
    inter_mappedSphereBank_subset_localFamily_of_outside_subset
      hq f hr5 (hrq₀.trans hq₀q) hE houtside
  let x : W := f (SphereExpansionVertex.root a)
  have hxE : x ∈ verticesOn E :=
    mem_biUnion.mpr ⟨T, hTE, haT⟩
  have htwo := IsErdosConfig.two_le_card_triplesThrough hE hr5 hxE
  have hTthrough : T ∈ triplesThrough E x :=
    mem_filter.mpr ⟨hTE, haT⟩
  obtain ⟨A, hAthrough, hAT⟩ :=
    Finset.exists_mem_ne (s := triplesThrough E x) (by omega) T
  have hAE : A ∈ E := (mem_filter.mp hAthrough).1
  have hxA : x ∈ A.1 := (mem_filter.mp hAthrough).2
  by_cases hAfull : A ∈ mapTripleSystem f (sphereTransformBank hq)
  · have hAlocal : A ∈ mappedSphereLocalFamily f hq S :=
      hlocal (mem_inter.mpr ⟨hAE, hAfull⟩)
    obtain ⟨U, hUS, y, hyU, hAy⟩ := by
      simpa only [mappedSphereLocalFamily, mem_biUnion] using hAlocal
    have hay : a ∈ mappedSphereRootCandidates f y :=
      root_mem_mappedCandidates_of_mem_mappedVertexLocalBank hq f hAy hxA
    have hyx : y ≠ x := by
      intro hyx
      subst y
      have hempty : mappedSphereRootCandidates f x = ∅ := by
        change mappedSphereRootCandidates f
            (f (SphereExpansionVertex.root a)) = ∅
        rw [mappedSphereRootCandidates_apply]
        rfl
      rw [hempty] at hay
      simpa using hay
    refine Or.inr ⟨y, ?_, hay⟩
    by_cases hUT : U = T
    · subst U
      exact mem_union_right _ (mem_erase.mpr ⟨hyx, hyU⟩)
    · apply mem_union_left
      exact mem_biUnion.mpr ⟨U, mem_erase.mpr ⟨hUT, hUS⟩, hyU⟩
  · apply Or.inl
    apply mem_biUnion.mpr
    refine ⟨A, mem_erase.mpr ⟨hAT, ?_⟩, hxA⟩
    have hAnotB : A ∉ B := fun hAB ↦ hAfull (hB hAB)
    have hAdiff : A ∈ E \ B := mem_sdiff.mpr ⟨hAE, hAnotB⟩
    rw [hEout] at hAdiff
    exact hAdiff

/-- The nested cycle-cover construction inherits the preceding charge, with
the fourteen-element original-root candidate sets. -/
lemma highGirthRoot_localized_of_forbidden
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {q q₀ : ℕ} (hq : 2 ≤ q) (hq₀q : q₀ ≤ q)
    (f : HighGirthCycleCoverVertex V q ↪ W)
    {B : TripleSystemOn W}
    (hB : B ⊆ mapTripleSystem f (highGirthCycleCoverBank V hq))
    {S : TripleSystemOn W} {T : TripleOn W} {a : V}
    (hSF : S ∈ absorberErdosForbiddenConfigurationsOn q₀ B)
    (hTS : T ∈ S)
    (haT : f (highGirthCycleCoverRootEmbedding V q a) ∈ T.1) :
    f (highGirthCycleCoverRootEmbedding V q a) ∈
        verticesOn (S.erase T) ∨
      ∃ y ∈ verticesOn (S.erase T) ∪
          T.1.erase (f (highGirthCycleCoverRootEmbedding V q a)),
        a ∈ mappedHighGirthOriginalRootCandidates f y := by
  let coreDecidableEq : DecidableEq (CycleCoverAbsorberVertex V) :=
    inferInstance
  let : LinearOrder (CycleCoverAbsorberVertex V) :=
    @Equiv.linearOrder _ _
      (Fintype.equivFin (CycleCoverAbsorberVertex V)) _ coreDecidableEq
  have hraw := sphereRoot_localized_of_forbidden
    (V := CycleCoverAbsorberVertex V) hq hq₀q f hB hSF hTS haT
  rcases hraw with hrem | ⟨y, hy, hcandidate⟩
  · exact Or.inl hrem
  · refine Or.inr ⟨y, hy, ?_⟩
    rw [mappedSphereRootCandidates] at hcandidate
    split_ifs at hcandidate with hyf
    · let z := Classical.choose hyf
      have hzy : f z = y := Classical.choose_spec hyf
      rw [← hzy, mappedHighGirthOriginalRootCandidates_apply]
      change cycleCoverRootEmbedding V a ∈
        sphereExpansionRootCandidates z at hcandidate
      cases hz : z with
      | root b =>
          rw [hz, sphereExpansionRootCandidates_root] at hcandidate
          simp at hcandidate
      | interior R w =>
          rw [hz, sphereExpansionRootCandidates_interior] at hcandidate
          exact mem_filter.mpr ⟨mem_univ a, hcandidate⟩
    · simp at hcandidate

/-- The explicit padded absorber admits uniformly bounded root-localization
candidates. -/
theorem paddedConstruction_hasRootLocalization
    {q m n : ℕ}
    {X : Finset (Fin n)} {B : TripleSystemOn (Fin n)}
    (f : HighGirthCycleCoverVertex (Fin (2 * m)) (q + 2) ↪ Fin n)
    (i : Fin m ↪ Fin (2 * m))
    (hX : X = ((univ : Finset (Fin m)).map
      (i.trans (highGirthCycleCoverRootEmbedding
        (Fin (2 * m)) (q + 2)))).map f)
    (hB : B = mapTripleSystem f
      (highGirthCycleCoverBank (Fin (2 * m))
        (show 2 ≤ q + 2 by omega))) :
    HasPaddedAbsorberRootLocalization q X B := by
  let root : Fin (2 * m) ↪
      HighGirthCycleCoverVertex (Fin (2 * m)) (q + 2) :=
    highGirthCycleCoverRootEmbedding (Fin (2 * m)) (q + 2)
  let candidates : Fin n → Finset (Fin n) := fun y ↦
    (mappedHighGirthOriginalRootCandidates f y).map (root.trans f)
  refine ⟨candidates, ?_, ?_⟩
  · intro y
    rw [card_map]
    exact card_mappedHighGirthOriginalRootCandidates_le_fourteen f y
  · intro S hSF T hTS x hxX hxT
    subst B
    subst X
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hxX
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hz
    have hloc := highGirthRoot_localized_of_forbidden
      (q := q + 2) (q₀ := q) (by omega) (by omega) f
      (Subset.rfl) hSF hTS hxT
    rcases hloc with hrem | ⟨y, hy, hay⟩
    · exact Or.inl hrem
    · refine Or.inr ⟨y, hy, ?_⟩
      exact Finset.mem_map.mpr ⟨i a, hay, rfl⟩

end

end Erdos207
