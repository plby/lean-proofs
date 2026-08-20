import ErdosProblems.Erdos733.ST.FiniteElementarySegmentCutParameterList
import ErdosProblems.Erdos733.ST.FiniteSortedRealCutListCoversUnitInterval
import ErdosProblems.Erdos733.ST.PolygonalPath
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathSegmentSubdivisionDataExists]
lemma PolygonalPathSegmentSubdivisionDataExists
    (γ : PolygonalPath)
    (cutVertices : Finset (EuclideanSpace ℝ (Fin 2)))
    (hcut_original :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ cutVertices)
    (i : ℕ) (hi : i + 1 < γ.vertices.length)
    (hseg :
      γ.vertices[i]'(Nat.lt_of_succ_lt hi) ≠ γ.vertices[i + 1]'hi) :
    ∃ L : List ℝ,
      L.Nodup ∧
        L.SortedLT ∧
          (∀ t : ℝ, t ∈ L ↔
            t = 0 ∨ t = 1 ∨
              (0 ≤ t ∧ t ≤ 1 ∧
                AffineMap.lineMap
                  (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                  (γ.vertices[i + 1]'hi) t ∈ cutVertices)) ∧
            (0 : ℝ) ∈ L ∧
              (1 : ℝ) ∈ L ∧
                (∀ t : ℝ, t ∈ L → 0 ≤ t ∧ t ≤ 1) ∧
                  (∀ k (hk : k + 1 < L.length), L[k] < L[k + 1]) ∧
                    (∀ k (hk : k + 1 < L.length) t,
                      0 ≤ t → t ≤ 1 →
                        AffineMap.lineMap
                          (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                          (γ.vertices[i + 1]'hi) t ∈ cutVertices →
                          ¬ (L[k] < t ∧ t < L[k + 1])) ∧
                      (∀ k (hk : k + 1 < L.length),
                        AffineMap.lineMap
                            (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                            (γ.vertices[i + 1]'hi)
                            (L[k]'(Nat.lt_of_succ_lt hk)) ∈ cutVertices ∧
                          AffineMap.lineMap
                            (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                            (γ.vertices[i + 1]'hi)
                            (L[k + 1]'hk) ∈ cutVertices ∧
                            AffineMap.lineMap
                                (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                (γ.vertices[i + 1]'hi)
                                (L[k]'(Nat.lt_of_succ_lt hk)) ≠
                              AffineMap.lineMap
                                (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                (γ.vertices[i + 1]'hi)
                                (L[k + 1]'hk) ∧
                              segment ℝ
                                  (AffineMap.lineMap
                                    (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                    (γ.vertices[i + 1]'hi)
                                    (L[k]'(Nat.lt_of_succ_lt hk)))
                                  (AffineMap.lineMap
                                    (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                    (γ.vertices[i + 1]'hi)
                                    (L[k + 1]'hk)) ⊆
                                segment ℝ
                                  (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                  (γ.vertices[i + 1]'hi) ∧
                                segment ℝ
                                    (AffineMap.lineMap
                                      (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                      (γ.vertices[i + 1]'hi)
                                      (L[k]'(Nat.lt_of_succ_lt hk)))
                                    (AffineMap.lineMap
                                      (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                      (γ.vertices[i + 1]'hi)
                                      (L[k + 1]'hk)) ⊆
                                  γ.carrier ∧
                                  ∀ v : EuclideanSpace ℝ (Fin 2),
                                    v ∈ cutVertices →
                                      v ∉ openSegment ℝ
                                        (AffineMap.lineMap
                                          (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                          (γ.vertices[i + 1]'hi)
                                          (L[k]'(Nat.lt_of_succ_lt hk)))
                                        (AffineMap.lineMap
                                          (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                          (γ.vertices[i + 1]'hi)
                                          (L[k + 1]'hk))) ∧
                        segment ℝ
                            (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                            (γ.vertices[i + 1]'hi) ⊆
                          ⋃ k : {k : ℕ // k + 1 < L.length},
                            segment ℝ
                              (AffineMap.lineMap
                                (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                (γ.vertices[i + 1]'hi)
                                (L[k.1]'(Nat.lt_of_succ_lt k.2)))
                              (AffineMap.lineMap
                                (γ.vertices[i]'(Nat.lt_of_succ_lt hi))
                                (γ.vertices[i + 1]'hi)
                                (L[k.1 + 1]'k.2)) := by
-- BODY
  classical
  let A : EuclideanSpace ℝ (Fin 2) := γ.vertices[i]'(Nat.lt_of_succ_lt hi)
  let B : EuclideanSpace ℝ (Fin 2) := γ.vertices[i + 1]'hi
  have hAcut : A ∈ cutVertices :=
    hcut_original A (List.getElem_mem (l := γ.vertices) (n := i) (Nat.lt_of_succ_lt hi))
  have hBcut : B ∈ cutVertices :=
    hcut_original B (List.getElem_mem (l := γ.vertices) (n := i + 1) hi)
  rcases FiniteElementarySegmentCutParameterList A B hseg cutVertices with
    ⟨L, hnodup, hsorted, hmem, hzero, hone, hbounds, hlt, hparam_gap⟩
  have endpoint_mem :
      ∀ k (hk : k < L.length),
        AffineMap.lineMap A B (L[k]'hk) ∈ cutVertices := by
    intro k hk
    have hLmem : L[k]'hk ∈ L := List.getElem_mem (l := L) (n := k) hk
    rcases (hmem (L[k]'hk)).1 hLmem with h0 | h1 | hmid
    · rw [h0, AffineMap.lineMap_apply_zero]
      exact hAcut
    · rw [h1, AffineMap.lineMap_apply_one]
      exact hBcut
    · exact hmid.2.2
  have point_on_original :
      ∀ k (hk : k < L.length),
        AffineMap.lineMap A B (L[k]'hk) ∈ segment ℝ A B := by
    intro k hk
    have hLmem : L[k]'hk ∈ L := List.getElem_mem (l := L) (n := k) hk
    rw [segment_eq_image_lineMap]
    exact ⟨L[k]'hk, hbounds (L[k]'hk) hLmem, rfl⟩
  have consecutive_subset_original :
      ∀ k (hk : k + 1 < L.length),
        segment ℝ
            (AffineMap.lineMap A B (L[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap A B (L[k + 1]'hk)) ⊆
          segment ℝ A B := by
    intro k hk
    exact (convex_segment A B).segment_subset
      (point_on_original k (Nat.lt_of_succ_lt hk))
      (point_on_original (k + 1) hk)
  have consecutive_subset_carrier :
      ∀ k (hk : k + 1 < L.length),
        segment ℝ
            (AffineMap.lineMap A B (L[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap A B (L[k + 1]'hk)) ⊆
          γ.carrier := by
    intro k hk x hx
    have hx_original := consecutive_subset_original k hk hx
    rw [γ.carrier_eq]
    exact Or.inr ⟨i, hi, by simpa [A, B] using hx_original⟩
  have no_cut_open :
      ∀ k (hk : k + 1 < L.length) (v : EuclideanSpace ℝ (Fin 2)),
        v ∈ cutVertices →
          v ∉ openSegment ℝ
            (AffineMap.lineMap A B (L[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap A B (L[k + 1]'hk)) := by
    intro k hk v hvcut hvopen
    rw [openSegment_eq_image_lineMap] at hvopen
    rcases hvopen with ⟨θ, hθ, hθv⟩
    let u : ℝ := L[k]'(Nat.lt_of_succ_lt hk)
    let w : ℝ := L[k + 1]'hk
    let t : ℝ := (1 - θ) * u + θ * w
    have huw : u < w := by
      simpa [u, w] using hlt k hk
    have ht_between : u < t ∧ t < w := by
      constructor <;> dsimp [t] <;> nlinarith [hθ.1, hθ.2, huw]
    have hu_mem : u ∈ L := by
      dsimp [u]
      exact List.getElem_mem (l := L) (n := k) (Nat.lt_of_succ_lt hk)
    have hw_mem : w ∈ L := by
      dsimp [w]
      exact List.getElem_mem (l := L) (n := k + 1) hk
    have hu_bounds : 0 ≤ u ∧ u ≤ 1 := hbounds u hu_mem
    have hw_bounds : 0 ≤ w ∧ w ≤ 1 := hbounds w hw_mem
    have ht0 : 0 ≤ t := by
      dsimp [t]
      nlinarith [hθ.1, hθ.2, hu_bounds.1, hw_bounds.1]
    have ht1 : t ≤ 1 := by
      dsimp [t]
      nlinarith [hθ.1, hθ.2, hu_bounds.2, hw_bounds.2]
    have hline :
        AffineMap.lineMap A B t =
          AffineMap.lineMap
            (AffineMap.lineMap A B u) (AffineMap.lineMap A B w) θ := by
      ext j
      simp [t, AffineMap.lineMap_apply_module]
      ring
    have htCut : AffineMap.lineMap A B t ∈ cutVertices := by
      rw [hline, hθv]
      exact hvcut
    exact hparam_gap k hk t ht0 ht1 htCut (by
      simpa [u, w] using ht_between)
  have coverage :
      segment ℝ A B ⊆
        ⋃ k : {k : ℕ // k + 1 < L.length},
          segment ℝ
            (AffineMap.lineMap A B (L[k.1]'(Nat.lt_of_succ_lt k.2)))
            (AffineMap.lineMap A B (L[k.1 + 1]'k.2)) := by
    intro x hx
    rw [segment_eq_image_lineMap] at hx
    rcases hx with ⟨t, htIcc, rfl⟩
    rcases
      FiniteSortedRealCutListCoversUnitInterval L hsorted hzero hone hbounds t htIcc with
      ⟨k, hk, htseg⟩
    have hxedge :
        AffineMap.lineMap A B t ∈
          segment ℝ
            (AffineMap.lineMap A B (L[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap A B (L[k + 1]'hk)) := by
      rw [← image_segment ℝ (AffineMap.lineMap A B)
        (L[k]'(Nat.lt_of_succ_lt hk)) (L[k + 1]'hk)]
      exact ⟨t, htseg, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hxedge⟩
  refine ⟨L, hnodup, hsorted, ?_, hzero, hone, hbounds, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa [A, B] using hmem t
  · intro k hk
    exact hlt k hk
  · intro k hk t ht0 ht1 htcut
    exact hparam_gap k hk t ht0 ht1 (by simpa [A, B] using htcut)
  · intro k hk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact endpoint_mem k (Nat.lt_of_succ_lt hk)
    · exact endpoint_mem (k + 1) hk
    · intro heq
      have hparam_eq :
          L[k]'(Nat.lt_of_succ_lt hk) = L[k + 1]'hk :=
        AffineMap.lineMap_injective ℝ hseg heq
      exact (ne_of_lt (hlt k hk)) hparam_eq
    · exact consecutive_subset_original k hk
    · exact consecutive_subset_carrier k hk
    · intro v hv
      exact no_cut_open k hk v hv
  · simpa [A, B] using coverage

