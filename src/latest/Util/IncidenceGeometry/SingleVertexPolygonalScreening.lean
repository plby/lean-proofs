import Util.IncidenceGeometry.FinitePointLineAvoidance
import Util.IncidenceGeometry.FinitePolygonalSet

open Classical
noncomputable section

lemma SingleVertexPolygonalScreening
    (K : FinitePolygonalSet) (a : EuclideanSpace ℝ (Fin 2))
    (W : Set (EuclideanSpace ℝ (Fin 2)))
    (ha : a ∉ K.carrier) (hWopen : IsOpen W) (hWnonempty : W.Nonempty) :
    ∃ x ∈ W, x ∉ K.carrier ∧
      (∀ p : EuclideanSpace ℝ (Fin 2), p ∈ K.points → p ∉ segment ℝ a x) ∧
      (∀ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2), s ∈ K.segments →
          ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
            segment ℝ p q ⊆ segment ℝ a x ∩ segment ℝ s.1 s.2) ∧
      (∀ (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), s ∈ K.segments →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ openSegment ℝ a x → p ∈ openSegment ℝ s.1 s.2 →
            ¬ ∃ c : ℝ, s.2 - s.1 = c • (x - a)) := by
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
  have segment_subset_line :
      ∀ (u v : E), segment ℝ u v ⊆ (affineSpan ℝ ({u, v} : Set E) : Set E) := by
    intro u v z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, _ht, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair t u v
  have point_mem_line_of_mem_segment :
      ∀ {a x p : E}, p ≠ a → p ∈ segment ℝ a x →
        x ∈ (affineSpan ℝ ({a, p} : Set E) : Set E) := by
    intro a x p hpa hpseg
    have hp_line_ax : p ∈ (affineSpan ℝ ({a, x} : Set E) : Set E) :=
      segment_subset_line a x hpseg
    have hline_eq : affineSpan ℝ ({a, p} : Set E) = affineSpan ℝ ({a, x} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (left_mem_affineSpan_pair ℝ a x) hp_line_ax hpa.symm
    rw [hline_eq]
    exact right_mem_affineSpan_pair ℝ a x
  have smul_parallel_mem_line :
      ∀ {a x u v : E}, (∃ c : ℝ, v - u = c • (x - a)) → u ≠ v →
        x ∈ (affineSpan ℝ ({a, a + (v - u)} : Set E) : Set E) := by
    intro a x u v hc huv
    rcases hc with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hzero : v - u = 0 := by simpa [hc0] using hc
      exact huv ((sub_eq_zero.mp hzero).symm)
    have hx_sub : x - a = c⁻¹ • (v - u) := by
      calc
        x - a = c⁻¹ • (c • (x - a)) := by simp [hc_ne]
        _ = c⁻¹ • (v - u) := by rw [hc]
    have hx_eq : x = a + c⁻¹ • (v - u) := by
      calc
        x = a + (x - a) := by abel
        _ = a + c⁻¹ • (v - u) := by rw [hx_sub]
    rw [hx_eq]
    have h := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ)
      (p₁ := a) (p₂ := a + (v - u)) (c⁻¹)
    simpa [vsub_eq_sub, add_comm, add_left_comm, add_assoc] using h
  let pointLine : E → AffineSubspace ℝ E := fun p => affineSpan ℝ ({a, p} : Set E)
  let supportLine : E × E → AffineSubspace ℝ E := fun s => affineSpan ℝ ({s.1, s.2} : Set E)
  let parallelLine : E × E → AffineSubspace ℝ E :=
    fun s => affineSpan ℝ ({a, a + (s.2 - s.1)} : Set E)
  let lines : Finset (AffineSubspace ℝ E) :=
    (K.points.image pointLine) ∪
      ((K.segments.image supportLine) ∪ (K.segments.image parallelLine))
  have hline : ∀ ℓ ∈ lines, (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    simp only [lines, Finset.mem_union, Finset.mem_image] at hℓ
    rcases hℓ with hpoint | hrest
    · rcases hpoint with ⟨p, hpK, rfl⟩
      have hp_carrier : p ∈ K.carrier := by
        rw [K.carrier_eq]
        exact Or.inl hpK
      exact line_dim_test a p (by intro hap; exact ha (hap ▸ hp_carrier))
    · rcases hrest with hsupport | hparallel
      · rcases hsupport with ⟨s, hsK, rfl⟩
        exact line_dim_test s.1 s.2 (K.segment_nondegenerate s hsK)
      · rcases hparallel with ⟨s, hsK, rfl⟩
        have hsne : s.2 - s.1 ≠ 0 := sub_ne_zero.mpr (K.segment_nondegenerate s hsK).symm
        have hane : a ≠ a + (s.2 - s.1) := by
          intro h
          have : s.2 - s.1 = 0 := by
            calc
              s.2 - s.1 = (a + (s.2 - s.1)) - a := by abel
              _ = a - a := by rw [← h]
              _ = 0 := by abel
          exact hsne this
        exact line_dim_test a (a + (s.2 - s.1)) hane
  obtain ⟨x, hxW, hxpoints, hxlines⟩ :=
    FinitePointLineAvoidance W K.points lines hWopen hWnonempty hline
  refine ⟨x, hxW, ?_, ?_, ?_, ?_⟩
  · intro hxK
    rw [K.carrier_eq] at hxK
    rcases hxK with hxpt | hxseg
    · exact hxpoints hxpt
    · simp only [Set.mem_iUnion] at hxseg
      rcases hxseg with ⟨s, hxs⟩
      have hx_support : x ∈ (supportLine s.1 : Set E) :=
        segment_subset_line s.1.1 s.1.2 hxs
      have hsupport_mem : supportLine s.1 ∈ lines := by
        simp only [lines, Finset.mem_union, Finset.mem_image]
        right; left
        exact ⟨s.1, s.2, rfl⟩
      exact hxlines (supportLine s.1) hsupport_mem hx_support
  · intro p hpK hpseg
    have hp_carrier : p ∈ K.carrier := by
      rw [K.carrier_eq]
      exact Or.inl hpK
    have hpa : p ≠ a := by intro h; exact ha (h ▸ hp_carrier)
    have hx_point_line : x ∈ (pointLine p : Set E) :=
      point_mem_line_of_mem_segment hpa hpseg
    have hpoint_mem : pointLine p ∈ lines := by
      simp only [lines, Finset.mem_union, Finset.mem_image]
      left
      exact ⟨p, hpK, rfl⟩
    exact hxlines (pointLine p) hpoint_mem hx_point_line
  · intro s hsK hoverlap
    rcases hoverlap with ⟨p, q, hpq, hsubset⟩
    have hp_ax : p ∈ segment ℝ a x := (hsubset (left_mem_segment ℝ p q)).1
    have hq_ax : q ∈ segment ℝ a x := (hsubset (right_mem_segment ℝ p q)).1
    have hp_s : p ∈ segment ℝ s.1 s.2 := (hsubset (left_mem_segment ℝ p q)).2
    have hq_s : q ∈ segment ℝ s.1 s.2 := (hsubset (right_mem_segment ℝ p q)).2
    have hp_ax_line : p ∈ (affineSpan ℝ ({a, x} : Set E) : Set E) :=
      segment_subset_line a x hp_ax
    have hq_ax_line : q ∈ (affineSpan ℝ ({a, x} : Set E) : Set E) :=
      segment_subset_line a x hq_ax
    have hp_s_line : p ∈ (supportLine s : Set E) :=
      segment_subset_line s.1 s.2 hp_s
    have hq_s_line : q ∈ (supportLine s : Set E) :=
      segment_subset_line s.1 s.2 hq_s
    have hline_eq_ax : affineSpan ℝ ({p, q} : Set E) = affineSpan ℝ ({a, x} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_ax_line hq_ax_line hpq
    have hline_eq_s : affineSpan ℝ ({p, q} : Set E) = supportLine s :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_s_line hq_s_line hpq
    have hx_support : x ∈ (supportLine s : Set E) := by
      rw [← hline_eq_s, hline_eq_ax]
      exact right_mem_affineSpan_pair ℝ a x
    have hsupport_mem : supportLine s ∈ lines := by
      simp only [lines, Finset.mem_union, Finset.mem_image]
      right; left
      exact ⟨s, hsK, rfl⟩
    exact hxlines (supportLine s) hsupport_mem hx_support
  · intro s hsK p _hpopen _hpsopen hparallel
    have hx_parallel : x ∈ (parallelLine s : Set E) :=
      smul_parallel_mem_line hparallel (K.segment_nondegenerate s hsK)
    have hparallel_mem : parallelLine s ∈ lines := by
      simp only [lines, Finset.mem_union, Finset.mem_image]
      right; right
      exact ⟨s, hsK, rfl⟩
    exact hxlines (parallelLine s) hparallel_mem hx_parallel
