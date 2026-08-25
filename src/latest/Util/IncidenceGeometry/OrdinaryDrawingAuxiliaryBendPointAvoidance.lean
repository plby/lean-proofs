import Util.IncidenceGeometry.FinitePointLineAvoidance

open Classical
noncomputable section

lemma OrdinaryDrawingAuxiliaryBendPointAvoidance
    (a b : EuclideanSpace ℝ (Fin 2))
    (points : Finset (EuclideanSpace ℝ (Fin 2)))
    (segments : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (lines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hab : a ≠ b)
    (hseg : ∀ s ∈ segments, s.1 ≠ s.2)
    (hline : ∀ ℓ ∈ lines,
      (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧
        Module.finrank ℝ ℓ.direction = 1) :
    ∃ z : EuclideanSpace ℝ (Fin 2),
      z ∉ (points : Set (EuclideanSpace ℝ (Fin 2))) ∧
        (∀ ℓ ∈ lines, z ∉ (ℓ : Set (EuclideanSpace ℝ (Fin 2)))) ∧
          (∀ s ∈ segments,
            z ∉ (affineSpan ℝ ({s.1, s.2} :
              Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)))) ∧
            (∀ s ∈ segments,
              z ∉ (affineSpan ℝ ({a, a + (s.2 - s.1)} :
                Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)))) ∧
              (∀ s ∈ segments,
                z ∉ (affineSpan ℝ ({b, b + (s.2 - s.1)} :
                  Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)))) ∧
                a ≠ z ∧
                  ¬ ∃ c : ℝ, b - a = c • (z - a) := by
  let E := EuclideanSpace ℝ (Fin 2)
  have line_dim_test :
      ∀ (u v : E), u ≠ v →
        ((affineSpan ℝ ({u, v} : Set E) : Set E).Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ ({u, v} : Set E)).direction = 1) := by
    intro u v huv
    constructor
    · exact ⟨u, left_mem_affineSpan_pair ℝ u v⟩
    · rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (sub_ne_zero.mpr huv)
  have smul_parallel_mem_endpointLine :
      ∀ {z : E}, (∃ c : ℝ, b - a = c • (z - a)) →
        z ∈ (affineSpan ℝ ({a, b} : Set E) : Set E) := by
    intro z hc
    rcases hc with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hzero : b - a = 0 := by simpa [hc0] using hc
      exact hab ((sub_eq_zero.mp hzero).symm)
    have hz_sub : z - a = c⁻¹ • (b - a) := by
      calc
        z - a = c⁻¹ • (c • (z - a)) := by simp [hc_ne]
        _ = c⁻¹ • (b - a) := by rw [hc]
    have hz_eq : z = a + c⁻¹ • (b - a) := by
      calc
        z = a + (z - a) := by abel
        _ = a + c⁻¹ • (b - a) := by rw [hz_sub]
    rw [hz_eq]
    have h := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ)
      (p₁ := a) (p₂ := b) (c⁻¹)
    simpa [vsub_eq_sub, add_comm, add_left_comm, add_assoc] using h
  let endpointLine : AffineSubspace ℝ E := affineSpan ℝ ({a, b} : Set E)
  let supportLine : E × E → AffineSubspace ℝ E :=
    fun s => affineSpan ℝ ({s.1, s.2} : Set E)
  let parallelLineA : E × E → AffineSubspace ℝ E :=
    fun s => affineSpan ℝ ({a, a + (s.2 - s.1)} : Set E)
  let parallelLineB : E × E → AffineSubspace ℝ E :=
    fun s => affineSpan ℝ ({b, b + (s.2 - s.1)} : Set E)
  let allLines : Finset (AffineSubspace ℝ E) :=
    insert endpointLine
      (lines ∪
        ((segments.image supportLine) ∪
          ((segments.image parallelLineA) ∪ (segments.image parallelLineB))))
  have hline_all :
      ∀ ℓ ∈ allLines, (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    simp only [allLines, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hℓ
    rcases hℓ with rfl | hrest
    · exact line_dim_test a b hab
    rcases hrest with hℓorig | hrest
    · exact hline ℓ hℓorig
    rcases hrest with hsupport | hrest
    · rcases hsupport with ⟨s, hs, rfl⟩
      exact line_dim_test s.1 s.2 (hseg s hs)
    rcases hrest with hparallelA | hparallelB
    · rcases hparallelA with ⟨s, hs, rfl⟩
      have hsne : s.2 - s.1 ≠ 0 := sub_ne_zero.mpr (hseg s hs).symm
      have hane : a ≠ a + (s.2 - s.1) := by
        intro h
        have hzero : s.2 - s.1 = 0 := by
          calc
            s.2 - s.1 = (a + (s.2 - s.1)) - a := by abel
            _ = a - a := by rw [← h]
            _ = 0 := by abel
        exact hsne hzero
      exact line_dim_test a (a + (s.2 - s.1)) hane
    · rcases hparallelB with ⟨s, hs, rfl⟩
      have hsne : s.2 - s.1 ≠ 0 := sub_ne_zero.mpr (hseg s hs).symm
      have hbne : b ≠ b + (s.2 - s.1) := by
        intro h
        have hzero : s.2 - s.1 = 0 := by
          calc
            s.2 - s.1 = (b + (s.2 - s.1)) - b := by abel
            _ = b - b := by rw [← h]
            _ = 0 := by abel
        exact hsne hzero
      exact line_dim_test b (b + (s.2 - s.1)) hbne
  have hWnonempty : (Set.univ : Set E).Nonempty := ⟨a, trivial⟩
  obtain ⟨z, _hzW, hzpoints, hzlines⟩ :=
    FinitePointLineAvoidance (Set.univ : Set E) points allLines isOpen_univ hWnonempty
      hline_all
  refine ⟨z, hzpoints, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ hℓ hzℓ
    exact hzlines ℓ (by simp [allLines, hℓ]) hzℓ
  · intro s hs hzsupport
    have hmem : supportLine s ∈ allLines := by
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    exact hzlines (supportLine s) hmem hzsupport
  · intro s hs hzparallel
    have hmem : parallelLineA s ∈ allLines := by
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    exact hzlines (parallelLineA s) hmem hzparallel
  · intro s hs hzparallel
    have hmem : parallelLineB s ∈ allLines := by
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    exact hzlines (parallelLineB s) hmem hzparallel
  · intro haz
    exact hzlines endpointLine (by simp [allLines]) (by
      simpa [endpointLine, haz] using left_mem_affineSpan_pair ℝ a b)
  · intro hcol
    exact hzlines endpointLine (by simp [allLines]) (smul_parallel_mem_endpointLine hcol)
