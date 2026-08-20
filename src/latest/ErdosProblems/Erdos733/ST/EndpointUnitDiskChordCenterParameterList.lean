import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Data.Finset.Sort

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskChordCenterParameterList]
lemma EndpointUnitDiskChordCenterParameterList
    (A B : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B)
    (T : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ L : List ℝ,
      L.Nodup ∧
        L.SortedLT ∧
          (∀ t : ℝ,
            t ∈ L ↔
              0 < t ∧ t < 1 ∧ AffineMap.lineMap A B t ∈ T) ∧
            (∀ t ∈ L,
              AffineMap.lineMap A B t ∈ openSegment ℝ A B) := by
-- BODY
  let τ : EuclideanSpace ℝ (Fin 2) → ℝ := fun z =>
    if hz : z ∈ openSegment ℝ A B then
      Classical.choose (by
        have hz' : z ∈ AffineMap.lineMap A B '' Set.Ioo (0 : ℝ) 1 := by
          simpa [openSegment_eq_image_lineMap] using hz
        exact hz')
    else
      0
  have τ_spec :
      ∀ {z : EuclideanSpace ℝ (Fin 2)}, z ∈ openSegment ℝ A B →
        0 < τ z ∧ τ z < 1 ∧ z = AffineMap.lineMap A B (τ z) := by
    intro z hz
    dsimp [τ]
    rw [dif_pos hz]
    let hchoose :=
      Classical.choose_spec (by
        have hz' : z ∈ AffineMap.lineMap A B '' Set.Ioo (0 : ℝ) 1 := by
          simpa [openSegment_eq_image_lineMap] using hz
        exact hz')
    rcases hchoose with ⟨ht, htz⟩
    exact ⟨ht.1, ht.2, htz.symm⟩
  let centers : Finset (EuclideanSpace ℝ (Fin 2)) :=
    T.filter (fun z => z ∈ openSegment ℝ A B)
  let params : Finset ℝ := centers.image τ
  have hmem : ∀ t : ℝ,
      t ∈ params.sort ↔
        0 < t ∧ t < 1 ∧ AffineMap.lineMap A B t ∈ T := by
    intro t
    constructor
    · intro ht
      have htparams : t ∈ params := by
        simpa [params] using (Finset.mem_sort (s := params) (r := (· ≤ ·))).1 ht
      rcases (Finset.mem_image.mp htparams) with ⟨z, hzcenters, hzt⟩
      have hzT : z ∈ T := by
        simpa [centers] using (Finset.mem_filter.mp hzcenters).1
      have hzopen : z ∈ openSegment ℝ A B := by
        simpa [centers] using (Finset.mem_filter.mp hzcenters).2
      have hτ := τ_spec hzopen
      constructor
      · simpa [← hzt] using hτ.1
      constructor
      · simpa [← hzt] using hτ.2.1
      · have hzline : z = AffineMap.lineMap A B t := by
          simpa [hzt] using hτ.2.2
        simpa [← hzline] using hzT
    · rintro ⟨ht0, ht1, htT⟩
      have hopen : AffineMap.lineMap A B t ∈ openSegment ℝ A B :=
        lineMap_mem_openSegment (𝕜 := ℝ) A B ⟨ht0, ht1⟩
      have hτ := τ_spec hopen
      have hτ_eq : τ (AffineMap.lineMap A B t) = t := by
        have hinj := AffineMap.lineMap_injective (k := ℝ) hAB
        apply hinj
        exact hτ.2.2.symm
      have hcenters :
          AffineMap.lineMap A B t ∈ centers := by
        change AffineMap.lineMap A B t ∈
          T.filter (fun z => z ∈ openSegment ℝ A B)
        exact Finset.mem_filter.mpr ⟨htT, hopen⟩
      have htparams : t ∈ params := by
        refine Finset.mem_image.mpr ?_
        exact ⟨AffineMap.lineMap A B t, hcenters, hτ_eq⟩
      simpa [params] using (Finset.mem_sort (s := params) (r := (· ≤ ·))).2 htparams
  refine ⟨params.sort, Finset.sort_nodup _ _, Finset.sortedLT_sort _, hmem, ?_⟩
  intro t ht
  have htprops := (hmem t).1 ht
  exact lineMap_mem_openSegment (𝕜 := ℝ) A B ⟨htprops.1, htprops.2.1⟩

