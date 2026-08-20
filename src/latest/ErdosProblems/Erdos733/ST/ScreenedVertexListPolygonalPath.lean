import ErdosProblems.Erdos733.ST.PolygonalPath
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.PolygonalPathInGeneralPosition
import Mathlib.Data.Set.Finite.Lattice

open Classical
noncomputable section

-- [TABLET NODE: ScreenedVertexListPolygonalPath]
lemma ScreenedVertexListPolygonalPath (K : FinitePolygonalSet)
    (xs : List (EuclideanSpace ℝ (Fin 2)))
    (source target : EuclideanSpace ℝ (Fin 2))
    (hxs : xs ≠ [])
    (hsource : xs.head? = some source)
    (htarget : xs.getLast? = some target)
    (hsourceK : source ∉ K.carrier)
    (htargetK : target ∉ K.carrier)
    (hvertices : ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ xs → v ∉ K.carrier)
    (hpoints : ∀ (i : ℕ) (hi : i + 1 < xs.length)
      (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ K.points → p ∉ segment ℝ xs[i] xs[i + 1])
    (hoverlap : ∀ (i : ℕ) (hi : i + 1 < xs.length)
      (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      s ∈ K.segments →
        ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
          segment ℝ p q ⊆ segment ℝ xs[i] xs[i + 1] ∩ segment ℝ s.1 s.2)
    (htransverse : ∀ (i : ℕ) (hi : i + 1 < xs.length)
      (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
      (_hs : s ∈ K.segments) (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ openSegment ℝ xs[i] xs[i + 1] →
        p ∈ openSegment ℝ s.1 s.2 →
          ¬ ∃ c : ℝ, s.2 - s.1 = c • (xs[i + 1] - xs[i])) :
    ∃ γ : PolygonalPath,
      γ.vertices = xs ∧
        γ.source = source ∧
          γ.target = target ∧
            γ.carrier =
              ({source, target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                {p | ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
                  p ∈ segment ℝ xs[i] xs[i + 1]} ∧
              PolygonalPathInGeneralPosition γ K := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  let carrier : Set E :=
    ({source, target} : Set E) ∪
      {p | ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
        p ∈ segment ℝ xs[i] xs[i + 1]}
  let γ : PolygonalPath :=
    { vertices := xs
      vertices_nonempty := hxs
      source := source
      target := target
      source_eq_head := hsource
      target_eq_last := htarget
      carrier := carrier
      carrier_eq := rfl }
  refine ⟨γ, rfl, rfl, rfl, rfl, ?_⟩
  dsimp [PolygonalPathInGeneralPosition, γ]
  constructor
  · intro v hv
    exact hvertices v hv
  constructor
  · intro p hpK hpγ
    have hpKcarrier : p ∈ K.carrier := by
      rw [K.carrier_eq]
      exact Or.inl hpK
    simp only [carrier, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hpγ
    rcases hpγ with hp_end | hp_seg
    · rcases hp_end with rfl | rfl
      · exact hsourceK hpKcarrier
      · exact htargetK hpKcarrier
    · rcases hp_seg with ⟨i, hi, hpseg⟩
      exact hpoints i hi p hpK hpseg
  constructor
  · exact hoverlap
  constructor
  · exact htransverse
  · have hpair_finite :
        ∀ (i : ℕ) (hi : i + 1 < xs.length)
          (s : E × E), s ∈ K.segments →
            Set.Finite (segment ℝ xs[i] xs[i + 1] ∩ segment ℝ s.1 s.2) := by
      intro i hi s hs
      apply Set.Subsingleton.finite
      intro p hp q hq
      by_contra hpq
      exact hoverlap i hi s hs ⟨p, q, hpq, by
        intro z hz
        constructor
        · exact (convex_segment xs[i] xs[i + 1]).segment_subset hp.1 hq.1 hz
        · exact (convex_segment s.1 s.2).segment_subset hp.2 hq.2 hz⟩
    let idxSet : Set ℕ := {i | i + 1 < xs.length}
    let pairUnion : Set E :=
      ⋃ i : {i : ℕ // i + 1 < xs.length},
        ⋃ s : {s : E × E // s ∈ K.segments},
          segment ℝ xs[i.1] xs[i.1 + 1] ∩ segment ℝ s.1.1 s.1.2
    have hidx_finite : Set.Finite idxSet := by
      refine (Set.finite_lt_nat xs.length).subset ?_
      intro i hi
      exact Nat.lt_of_succ_lt hi
    have hsegset_finite : Set.Finite (K.segments : Set (E × E)) :=
      K.segments.finite_toSet
    have hpairUnion_finite : Set.Finite pairUnion := by
      haveI : Finite {i : ℕ // i + 1 < xs.length} := hidx_finite
      haveI : Finite {s : E × E // s ∈ K.segments} := hsegset_finite
      apply Set.finite_iUnion
      intro i
      apply Set.finite_iUnion
      intro s
      exact hpair_finite i.1 i.2 s.1 s.2
    have hcover_finite :
        Set.Finite (({source, target} : Set E) ∪ (K.points : Set E) ∪ pairUnion) := by
      exact (((Set.finite_singleton target).insert source).union
        K.points.finite_toSet).union hpairUnion_finite
    refine hcover_finite.subset ?_
    intro p hp
    rcases hp with ⟨hpγ, hpK⟩
    simp only [carrier, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hpγ
    rw [K.carrier_eq] at hpK
    simp only [Set.mem_union, Set.mem_iUnion] at hpK
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_iUnion, pairUnion]
    rcases hpγ with hp_end | hpseg
    · left
      left
      exact hp_end
    · rcases hpK with hp_point | hpKseg
      · left
        right
        exact hp_point
      · right
        rcases hpseg with ⟨i, hi, hpseg⟩
        rcases hpKseg with ⟨s, hpKseg⟩
        exact ⟨⟨i, hi⟩, s, ⟨hpseg, hpKseg⟩⟩
