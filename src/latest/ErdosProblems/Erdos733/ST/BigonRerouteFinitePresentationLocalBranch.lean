import ErdosProblems.Erdos733.ST.FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: BigonRerouteFinitePresentationLocalBranch]
lemma BigonRerouteFinitePresentationLocalBranch
    (K : FinitePolygonalSet)
    (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
    (hs : s ∈ K.segments)
    (z : EuclideanSpace ℝ (Fin 2))
    (hznotpoints : z ∉ (K.points : Set (EuclideanSpace ℝ (Fin 2))))
    (hzs : z ∈ openSegment ℝ s.1 s.2) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball z r ∩ K.carrier =
        Metric.ball z r ∩ segment ℝ s.1 s.2 := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  let forbidden : Set E :=
    (K.points : Set E) ∪
      ⋃ t : {t : E × E // t ∈ K.segments},
        if t.1 = s then (∅ : Set E) else segment ℝ t.1.1 t.1.2
  have hforbiddenClosed : IsClosed forbidden := by
    apply (K.points.finite_toSet.isClosed).union
    exact isClosed_iUnion_of_finite fun t => by
      by_cases hts : t.1 = s
      · simp [hts]
      · rw [if_neg hts, ← convexHull_pair]
        exact (by
          simp : ({t.1.1, t.1.2} : Set E).Finite).isClosed_convexHull ℝ
  have hznotforbidden : z ∉ forbidden := by
    intro hz
    rcases hz with hzPoint | hzSegment
    · exact hznotpoints hzPoint
    · rcases Set.mem_iUnion.mp hzSegment with ⟨t, hzt⟩
      by_cases hts : t.1 = s
      · simp [hts] at hzt
      · rw [if_neg hts] at hzt
        exact hznotpoints
          (K.segment_intersections_listed s t.1 hs t.2 (Ne.symm hts) z
            (openSegment_subset_segment ℝ s.1 s.2 hzs) hzt)
  have hopen : IsOpen forbiddenᶜ := hforbiddenClosed.isOpen_compl
  rcases Metric.isOpen_iff.mp hopen z hznotforbidden with
    ⟨r, hr, hball⟩
  refine ⟨r, hr, Set.ext ?_⟩
  intro w
  constructor
  · rintro ⟨hwball, hwK⟩
    refine ⟨hwball, ?_⟩
    rw [K.carrier_eq] at hwK
    rcases hwK with hwPoint | hwSegment
    · exact ((hball hwball) (Or.inl hwPoint)).elim
    · rcases Set.mem_iUnion.mp hwSegment with ⟨t, hwt⟩
      by_cases hts : t.1 = s
      · simpa [hts] using hwt
      · exact ((hball hwball)
          (Or.inr (Set.mem_iUnion.mpr ⟨t, by simpa [hts] using hwt⟩))).elim
  · rintro ⟨hwball, hws⟩
    refine ⟨hwball, ?_⟩
    rw [K.carrier_eq]
    right
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hws⟩
