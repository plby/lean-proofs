import ErdosProblems.Erdos733.ST.CyclicPresentationRetainedSideFanBridge
import ErdosProblems.Erdos733.ST.CyclicPresentationTriangleGeneralPosition
import ErdosProblems.Erdos733.ST.FinitePointLineAvoidance
import ErdosProblems.Erdos733.ST.PolygonalPathInGeneralPosition
import ErdosProblems.Erdos733.ST.TriangleSegmentNoOverlapIntersectionSubsingleton
import Mathlib.Data.Set.Finite.Lattice

open Classical
noncomputable section


-- [TABLET NODE: CyclicPresentationRetainedApexBasicAvoidance]
lemma CyclicPresentationRetainedApexBasicAvoidance
    (γ : PolygonalPath) {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (hgp : PolygonalPathInGeneralPosition γ K)
    (R : CyclicCurvePresentation J K) :
    let retained : Finset ℕ :=
      ((Finset.range γ.vertices.length).filter fun i =>
        if hi : i + 1 < γ.vertices.length then
          γ.vertices[i] ≠ γ.vertices[i + 1]
        else
          False)
    let start : retained → EuclideanSpace ℝ (Fin 2) := fun i =>
      γ.vertices[i.1]'(by
        have h := i.2
        simp [retained] at h
        exact h.1)
    let stop : retained → EuclideanSpace ℝ (Fin 2) := fun i =>
      γ.vertices[i.1 + 1]'(by
        have h := i.2
        simp [retained] at h
        exact h.2.choose)
    ∀ (σ : Equiv.Perm retained),
      (∀ i : retained, start (σ i) = stop i) →
        ∃ z : EuclideanSpace ℝ (Fin 2),
          z ∉ J.carrier ∧
            (∀ i : retained, z ≠ start i) ∧
              (∀ i : retained, start (σ i) ≠ z) ∧
                (∀ i : retained, start i ≠ start (σ i)) ∧
                  (∀ i : retained,
                    ¬ ∃ c : ℝ, start (σ i) - start i = c • (z - start i)) ∧
                    (∀ i : retained,
                      CyclicPresentationTriangleGeneralPosition R z (start i) (start (σ i))) := by
-- BODY
  intro retained start stop σ hσ
  let E := EuclideanSpace ℝ (Fin 2)
  rcases hgp with ⟨hγ_vertices, hKpoints_off, hγ_noOverlap, hγ_transverse, _hγ_finite⟩
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
    intro u v x hx
    rw [segment_eq_image_lineMap] at hx
    rcases hx with ⟨t, _ht, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair t u v
  have smul_parallel_mem_line :
      ∀ {a x b : E}, (∃ c : ℝ, b - a = c • (x - a)) → a ≠ b →
        x ∈ (affineSpan ℝ ({a, b} : Set E) : Set E) := by
    intro a x b hc hab
    rcases hc with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hzero : b - a = 0 := by simpa [hc0] using hc
      exact hab ((sub_eq_zero.mp hzero).symm)
    have hx_sub : x - a = c⁻¹ • (b - a) := by
      calc
        x - a = c⁻¹ • (c • (x - a)) := by simp [hc_ne]
        _ = c⁻¹ • (b - a) := by rw [hc]
    have hx_eq : x = a + c⁻¹ • (b - a) := by
      calc
        x = a + (x - a) := by abel
        _ = a + c⁻¹ • (b - a) := by rw [hx_sub]
    rw [hx_eq]
    have h := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ)
      (p₁ := a) (p₂ := b) (c⁻¹)
    simpa [vsub_eq_sub, add_comm, add_left_comm, add_assoc] using h
  have point_mem_line_of_mem_segment_left :
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
  have point_mem_line_of_mem_segment_right :
      ∀ {x a p : E}, p ≠ a → p ∈ segment ℝ x a →
        x ∈ (affineSpan ℝ ({a, p} : Set E) : Set E) := by
    intro x a p hpa hpseg
    have hp_line_xa : p ∈ (affineSpan ℝ ({x, a} : Set E) : Set E) :=
      segment_subset_line x a hpseg
    have hline_eq : affineSpan ℝ ({a, p} : Set E) = affineSpan ℝ ({x, a} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (right_mem_affineSpan_pair ℝ x a) hp_line_xa hpa.symm
    rw [hline_eq]
    exact left_mem_affineSpan_pair ℝ x a
  have smul_direction_mem_parallelLine_left :
      ∀ {a x u v : E}, (∃ c : ℝ, x - a = c • (v - u)) →
        x ∈ (affineSpan ℝ ({a, a + (v - u)} : Set E) : Set E) := by
    intro a x u v hc
    rcases hc with ⟨c, hc⟩
    have hx_eq : x = a + c • (v - u) := by
      calc
        x = a + (x - a) := by abel
        _ = a + c • (v - u) := by rw [hc]
    rw [hx_eq]
    have h := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ)
      (p₁ := a) (p₂ := a + (v - u)) c
    simpa [vsub_eq_sub, add_comm, add_left_comm, add_assoc] using h
  have hside : ∀ i : retained, start i ≠ start (σ i) := by
    intro i hbad
    have hi := i.2
    simp [retained] at hi
    rcases hi.2 with ⟨_hi_succ, hne⟩
    have hstart_stop : start i ≠ stop i := by
      simpa [start, stop] using hne
    exact hstart_stop (hbad.trans (hσ i))
  let supportLine : {p : E // p ∈ R.vertices} → AffineSubspace ℝ E := fun p =>
    affineSpan ℝ ({p.1, (R.successor p).1} : Set E)
  let sideLine : retained → AffineSubspace ℝ E := fun i =>
    affineSpan ℝ ({start i, start (σ i)} : Set E)
  let vertexLine : retained × {p : E // p ∈ R.vertices} → AffineSubspace ℝ E := fun ip =>
    affineSpan ℝ ({start ip.1, ip.2.1} : Set E)
  let radialParallelLine :
      retained × {p : E // p ∈ R.vertices} → AffineSubspace ℝ E := fun ip =>
    affineSpan ℝ ({start ip.1,
      start ip.1 + ((R.successor ip.2).1 - ip.2.1)} : Set E)
  let apexPoints : Finset E := Finset.univ.image start
  let lines : Finset (AffineSubspace ℝ E) :=
    (R.vertices.attach.image supportLine) ∪
      ((Finset.univ.image sideLine) ∪
        ((Finset.univ.product R.vertices.attach).image vertexLine ∪
          ((Finset.univ.product R.vertices.attach).image radialParallelLine)))
  have hline : ∀ ℓ ∈ lines, (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    simp only [lines, Finset.mem_union, Finset.mem_image] at hℓ
    rcases hℓ with hsupport | hrest
    · rcases hsupport with ⟨p, _hp, rfl⟩
      exact line_dim_test p.1 (R.successor p).1 (R.successor_nondegenerate p)
    rcases hrest with hsideLine | hrest
    · rcases hsideLine with ⟨i, _hi, rfl⟩
      exact line_dim_test (start i) (start (σ i)) (hside i)
    rcases hrest with hvertexLine | hparallelLine
    · rcases hvertexLine with ⟨ip, _hip, rfl⟩
      have hpK : ip.2.1 ∈ K.points := by
        have hpR : ip.2.1 ∈ (R.vertices : Set E) := ip.2.2
        have hpKset : ip.2.1 ∈ (K.points : Set E) := by
          rw [← R.vertices_eq_points]
          exact hpR
        exact hpKset
      have hpCarrier : ip.2.1 ∈ K.carrier := by
        rw [K.carrier_eq]
        exact Or.inl hpK
      have hstart_mem : start ip.1 ∈ γ.vertices := by
        dsimp [start]
        exact List.getElem_mem _
      have hne : start ip.1 ≠ ip.2.1 := by
        intro h
        exact hγ_vertices (start ip.1) hstart_mem (h ▸ hpCarrier)
      exact line_dim_test (start ip.1) ip.2.1 hne
    · rcases hparallelLine with ⟨ip, _hip, rfl⟩
      have hdir_ne :
          (R.successor ip.2).1 - ip.2.1 ≠ 0 :=
        sub_ne_zero.mpr (R.successor_nondegenerate ip.2).symm
      have hne : start ip.1 ≠ start ip.1 + ((R.successor ip.2).1 - ip.2.1) := by
        intro h
        have : (R.successor ip.2).1 - ip.2.1 = 0 := by
          calc
            (R.successor ip.2).1 - ip.2.1 =
                (start ip.1 + ((R.successor ip.2).1 - ip.2.1)) - start ip.1 := by abel
            _ = start ip.1 - start ip.1 := by rw [← h]
            _ = 0 := by abel
        exact hdir_ne this
      exact line_dim_test (start ip.1)
        (start ip.1 + ((R.successor ip.2).1 - ip.2.1)) hne
  have hWnonempty : (Set.univ : Set E).Nonempty := ⟨0, trivial⟩
  obtain ⟨z, _hzW, hzpoints, hzlines⟩ :=
    FinitePointLineAvoidance (Set.univ : Set E) apexPoints lines isOpen_univ hWnonempty hline
  have hzJ : z ∉ J.carrier := by
    intro hzJ
    rw [R.cyclic_carrier_eq] at hzJ
    simp only [Set.mem_iUnion] at hzJ
    rcases hzJ with ⟨p, hzseg⟩
    have hz_support : z ∈ (supportLine p : Set E) :=
      segment_subset_line p.1 (R.successor p).1 hzseg
    have hsupport_mem : supportLine p ∈ lines := by
      simp only [lines, Finset.mem_union, Finset.mem_image]
      left
      exact ⟨p, by simp, rfl⟩
    exact hzlines (supportLine p) hsupport_mem hz_support
  have hza : ∀ i : retained, z ≠ start i := by
    intro i hzi
    apply hzpoints
    change z ∈ (apexPoints : Set E)
    rw [hzi]
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  have hbz : ∀ i : retained, start (σ i) ≠ z := by
    intro i h
    exact (hza (σ i)) h.symm
  have hncol :
      ∀ i : retained, ¬ ∃ c : ℝ, start (σ i) - start i = c • (z - start i) := by
    intro i hparallel
    have hz_side : z ∈ (sideLine i : Set E) :=
      smul_parallel_mem_line hparallel (hside i)
    have hside_mem : sideLine i ∈ lines := by
      simp only [lines, Finset.mem_union, Finset.mem_image]
      right; left
      exact ⟨i, by simp, rfl⟩
    exact hzlines (sideLine i) hside_mem hz_side
  have hvertexLine_mem :
      ∀ (i : retained) (p : {p : E // p ∈ R.vertices}), vertexLine (i, p) ∈ lines := by
    intro i p
    simp only [lines, Finset.mem_union, Finset.mem_image]
    right; right; left
    exact ⟨(i, p), by simp, rfl⟩
  have hradialParallelLine_mem :
      ∀ (i : retained) (p : {p : E // p ∈ R.vertices}),
        radialParallelLine (i, p) ∈ lines := by
    intro i p
    simp only [lines, Finset.mem_union, Finset.mem_image]
    right; right; right
    exact ⟨(i, p), by simp, rfl⟩
  have cyclic_vertex_mem_Kpoints :
      ∀ p : {p : E // p ∈ R.vertices}, p.1 ∈ K.points := by
    intro p
    have hpR : p.1 ∈ (R.vertices : Set E) := p.2
    have hpKset : p.1 ∈ (K.points : Set E) := by
      rw [← R.vertices_eq_points]
      exact hpR
    exact hpKset
  have cyclic_vertex_mem_Kcarrier :
      ∀ p : {p : E // p ∈ R.vertices}, p.1 ∈ K.carrier := by
    intro p
    rw [K.carrier_eq]
    exact Or.inl (cyclic_vertex_mem_Kpoints p)
  have retained_succ : ∀ i : retained, i.1 + 1 < γ.vertices.length := by
    intro i
    have hi := i.2
    simp [retained] at hi
    exact hi.2.choose
  have start_mem_vertices : ∀ i : retained, start i ∈ γ.vertices := by
    intro i
    dsimp [start]
    exact List.getElem_mem _
  have start_not_Kcarrier : ∀ i : retained, start i ∉ K.carrier := by
    intro i
    exact hγ_vertices (start i) (start_mem_vertices i)
  have start_not_Jcarrier : ∀ i : retained, start i ∉ J.carrier := by
    intro i hiJ
    exact start_not_Kcarrier i (by
      rw [R.finite_set_carrier_eq]
      exact hiJ)
  have openSegment_of_segment_subset :
      ∀ {u v s t x : EuclideanSpace ℝ (Fin 2)}, u ≠ v →
        segment ℝ u v ⊆ segment ℝ s t →
          x ∈ openSegment ℝ u v → x ∈ openSegment ℝ s t := by
    intro u v s t x huv hsub hx
    rw [openSegment_eq_image_lineMap] at hx ⊢
    rcases hx with ⟨r, hr, rfl⟩
    have hu : u ∈ segment ℝ s t := hsub (left_mem_segment ℝ u v)
    have hv : v ∈ segment ℝ s t := hsub (right_mem_segment ℝ u v)
    rw [segment_eq_image_lineMap] at hu hv
    rcases hu with ⟨a, ha, hu_eq⟩
    rcases hv with ⟨b, hb, hv_eq⟩
    have hab : a ≠ b := by
      intro hab
      apply huv
      calc
        u = AffineMap.lineMap s t a := hu_eq.symm
        _ = AffineMap.lineMap s t b := by rw [hab]
        _ = v := hv_eq
    refine ⟨(1 - r) * a + r * b, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hab with hablt | hblt
      · constructor <;> nlinarith [hr.1, hr.2, ha.1, ha.2, hb.1, hb.2, hablt]
      · constructor <;> nlinarith [hr.1, hr.2, ha.1, ha.2, hb.1, hb.2, hblt]
    · rw [← hu_eq, ← hv_eq]
      ext j
      simp [AffineMap.lineMap_apply_module]
      ring_nf
  have subsegment_direction :
      ∀ {u v s t : EuclideanSpace ℝ (Fin 2)}, segment ℝ u v ⊆ segment ℝ s t →
        ∃ d : ℝ, v - u = d • (t - s) := by
    intro u v s t hsub
    have hu : u ∈ segment ℝ s t := hsub (left_mem_segment ℝ u v)
    have hv : v ∈ segment ℝ s t := hsub (right_mem_segment ℝ u v)
    rw [segment_eq_image_lineMap] at hu hv
    rcases hu with ⟨a, _ha, hu_eq⟩
    rcases hv with ⟨b, _hb, hv_eq⟩
    refine ⟨b - a, ?_⟩
    rw [← hu_eq, ← hv_eq]
    ext j
    simp [AffineMap.lineMap_apply_module]
    ring_nf
  have hVertexOffZStart :
      ∀ (i : retained) (p : {p : E // p ∈ R.vertices}),
        p.1 ∉ segment ℝ z (start i) := by
    intro i p hpseg
    have hp_ne_start : p.1 ≠ start i := by
      intro hp_eq
      exact start_not_Kcarrier i (by
        simpa [hp_eq] using cyclic_vertex_mem_Kcarrier p)
    have hz_line : z ∈ (vertexLine (i, p) : Set E) :=
      point_mem_line_of_mem_segment_right hp_ne_start hpseg
    exact hzlines (vertexLine (i, p)) (hvertexLine_mem i p) hz_line
  have hVertexOffStartZ :
      ∀ (i : retained) (p : {p : E // p ∈ R.vertices}),
        p.1 ∉ segment ℝ (start i) z := by
    intro i p hpseg
    have hp_ne_start : p.1 ≠ start i := by
      intro hp_eq
      exact start_not_Kcarrier i (by
        simpa [hp_eq] using cyclic_vertex_mem_Kcarrier p)
    have hz_line : z ∈ (vertexLine (i, p) : Set E) :=
      point_mem_line_of_mem_segment_left hp_ne_start hpseg
    exact hzlines (vertexLine (i, p)) (hvertexLine_mem i p) hz_line
  have hNoOverlapZStart :
      ∀ (i : retained) (p : {p : E // p ∈ R.vertices}),
        ¬ ∃ u v : E, u ≠ v ∧
          segment ℝ u v ⊆
            segment ℝ p.1 (R.successor p).1 ∩ segment ℝ z (start i) := by
    intro i p hoverlap
    rcases hoverlap with ⟨u, v, huv, hsubset⟩
    have hu_zs : u ∈ segment ℝ z (start i) := (hsubset (left_mem_segment ℝ u v)).2
    have hv_zs : v ∈ segment ℝ z (start i) := (hsubset (right_mem_segment ℝ u v)).2
    have hu_R : u ∈ segment ℝ p.1 (R.successor p).1 := (hsubset (left_mem_segment ℝ u v)).1
    have hv_R : v ∈ segment ℝ p.1 (R.successor p).1 := (hsubset (right_mem_segment ℝ u v)).1
    have hu_zs_line : u ∈ (affineSpan ℝ ({z, start i} : Set E) : Set E) :=
      segment_subset_line z (start i) hu_zs
    have hv_zs_line : v ∈ (affineSpan ℝ ({z, start i} : Set E) : Set E) :=
      segment_subset_line z (start i) hv_zs
    have hu_R_line : u ∈ (supportLine p : Set E) :=
      segment_subset_line p.1 (R.successor p).1 hu_R
    have hv_R_line : v ∈ (supportLine p : Set E) :=
      segment_subset_line p.1 (R.successor p).1 hv_R
    have hline_eq_zs : affineSpan ℝ ({u, v} : Set E) =
        affineSpan ℝ ({z, start i} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hu_zs_line hv_zs_line huv
    have hline_eq_R : affineSpan ℝ ({u, v} : Set E) = supportLine p :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hu_R_line hv_R_line huv
    have hz_support : z ∈ (supportLine p : Set E) := by
      rw [← hline_eq_R, hline_eq_zs]
      exact left_mem_affineSpan_pair ℝ z (start i)
    have hsupport_mem : supportLine p ∈ lines := by
      simp only [lines, Finset.mem_union, Finset.mem_image]
      left
      exact ⟨p, by simp, rfl⟩
    exact hzlines (supportLine p) hsupport_mem hz_support
  have hNoOverlapStartZ :
      ∀ (i : retained) (p : {p : E // p ∈ R.vertices}),
        ¬ ∃ u v : E, u ≠ v ∧
          segment ℝ u v ⊆
            segment ℝ p.1 (R.successor p).1 ∩ segment ℝ (start i) z := by
    intro i p hoverlap
    rcases hoverlap with ⟨u, v, huv, hsubset⟩
    have hu_sz : u ∈ segment ℝ (start i) z := (hsubset (left_mem_segment ℝ u v)).2
    have hv_sz : v ∈ segment ℝ (start i) z := (hsubset (right_mem_segment ℝ u v)).2
    have hu_R : u ∈ segment ℝ p.1 (R.successor p).1 := (hsubset (left_mem_segment ℝ u v)).1
    have hv_R : v ∈ segment ℝ p.1 (R.successor p).1 := (hsubset (right_mem_segment ℝ u v)).1
    have hu_sz_line : u ∈ (affineSpan ℝ ({start i, z} : Set E) : Set E) :=
      segment_subset_line (start i) z hu_sz
    have hv_sz_line : v ∈ (affineSpan ℝ ({start i, z} : Set E) : Set E) :=
      segment_subset_line (start i) z hv_sz
    have hu_R_line : u ∈ (supportLine p : Set E) :=
      segment_subset_line p.1 (R.successor p).1 hu_R
    have hv_R_line : v ∈ (supportLine p : Set E) :=
      segment_subset_line p.1 (R.successor p).1 hv_R
    have hline_eq_sz : affineSpan ℝ ({u, v} : Set E) =
        affineSpan ℝ ({start i, z} : Set E) :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hu_sz_line hv_sz_line huv
    have hline_eq_R : affineSpan ℝ ({u, v} : Set E) = supportLine p :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hu_R_line hv_R_line huv
    have hz_support : z ∈ (supportLine p : Set E) := by
      rw [← hline_eq_R, hline_eq_sz]
      exact right_mem_affineSpan_pair ℝ (start i) z
    have hsupport_mem : supportLine p ∈ lines := by
      simp only [lines, Finset.mem_union, Finset.mem_image]
      left
      exact ⟨p, by simp, rfl⟩
    exact hzlines (supportLine p) hsupport_mem hz_support
  have hTransZStart :
      ∀ (i : retained) (p : {p : E // p ∈ R.vertices}) (x : E),
        x ∈ openSegment ℝ p.1 (R.successor p).1 →
          x ∈ openSegment ℝ z (start i) →
            ¬ ∃ c : ℝ, start i - z = c • ((R.successor p).1 - p.1) := by
    intro i p x _hxR _hxrad hparallel
    have hz_parallel : z ∈ (radialParallelLine (i, p) : Set E) := by
      apply smul_direction_mem_parallelLine_left
      rcases hparallel with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      calc
        z - start i = -(start i - z) := by abel
        _ = (-c) • ((R.successor p).1 - p.1) := by
          rw [hc]
          simp
    exact hzlines (radialParallelLine (i, p)) (hradialParallelLine_mem i p) hz_parallel
  have hTransStartZ :
      ∀ (i : retained) (p : {p : E // p ∈ R.vertices}) (x : E),
        x ∈ openSegment ℝ p.1 (R.successor p).1 →
          x ∈ openSegment ℝ (start i) z →
            ¬ ∃ c : ℝ, z - start i = c • ((R.successor p).1 - p.1) := by
    intro i p x _hxR _hxrad hparallel
    have hz_parallel : z ∈ (radialParallelLine (i, p) : Set E) :=
      smul_direction_mem_parallelLine_left hparallel
    exact hzlines (radialParallelLine (i, p)) (hradialParallelLine_mem i p) hz_parallel
  have htri : ∀ i : retained,
      CyclicPresentationTriangleGeneralPosition R z (start i) (start (σ i)) := by
    intro i
    have hi_succ : i.1 + 1 < γ.vertices.length := retained_succ i
    have h_b_eq : start (σ i) = γ.vertices[i.1 + 1] := by
      simpa [stop] using hσ i
    have hmid_seg :
        segment ℝ (start i) (start (σ i)) =
          segment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1] := by
      rw [h_b_eq]
    have hmid_open :
        openSegment ℝ (start i) (start (σ i)) =
          openSegment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1] := by
      rw [h_b_eq]
    have hpath_dir :
        γ.vertices[i.1 + 1] - γ.vertices[i.1] = start (σ i) - start i := by
      rw [h_b_eq]
    have hNoOverlapAB :
        ∀ p : {p : E // p ∈ R.vertices},
          ¬ ∃ u v : E, u ≠ v ∧
            segment ℝ u v ⊆
              segment ℝ p.1 (R.successor p).1 ∩ segment ℝ (start i) (start (σ i)) := by
      intro p hoverlap
      rcases R.cyclic_piece_refines_segment p with ⟨s, hsK, hsubR⟩
      apply hγ_noOverlap i.1 hi_succ s hsK
      rcases hoverlap with ⟨u, v, huv, hsubset⟩
      refine ⟨u, v, huv, ?_⟩
      intro x hxuv
      have hx := hsubset hxuv
      constructor
      · simpa [hmid_seg] using hx.2
      · exact hsubR hx.1
    have hTransAB :
        ∀ (p : {p : E // p ∈ R.vertices}) (x : E),
          x ∈ openSegment ℝ p.1 (R.successor p).1 →
            x ∈ openSegment ℝ (start i) (start (σ i)) →
              ¬ ∃ c : ℝ,
                start (σ i) - start i = c • ((R.successor p).1 - p.1) := by
      intro p x hxR hxmid hparallel
      rcases R.cyclic_piece_refines_segment p with ⟨s, hsK, hsubR⟩
      have hxKopen : x ∈ openSegment ℝ s.1 s.2 :=
        openSegment_of_segment_subset (R.successor_nondegenerate p) hsubR hxR
      have hxmid_path : x ∈ openSegment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1] := by
        simpa [hmid_open] using hxmid
      apply hγ_transverse i.1 hi_succ s hsK x hxmid_path hxKopen
      rcases hparallel with ⟨c, hc⟩
      rcases subsegment_direction hsubR with ⟨d, hd⟩
      have hmid_ne_zero : start (σ i) - start i ≠ 0 :=
        sub_ne_zero.mpr (hside i).symm
      have hmid_as_s : start (σ i) - start i = (c * d) • (s.2 - s.1) := by
        calc
          start (σ i) - start i = c • ((R.successor p).1 - p.1) := hc
          _ = c • (d • (s.2 - s.1)) := by rw [hd]
          _ = (c * d) • (s.2 - s.1) := by rw [mul_smul]
      have hcd_ne : c * d ≠ 0 := by
        intro hcd
        have hzero : start (σ i) - start i = 0 := by
          simpa [hcd] using hmid_as_s
        exact hmid_ne_zero hzero
      refine ⟨(c * d)⁻¹, ?_⟩
      calc
        s.2 - s.1 = (c * d)⁻¹ • ((c * d) • (s.2 - s.1)) := by
          rw [inv_smul_smul₀ hcd_ne]
        _ = (c * d)⁻¹ • (start (σ i) - start i) := by rw [← hmid_as_s]
        _ = (c * d)⁻¹ • (γ.vertices[i.1 + 1] - γ.vertices[i.1]) := by
          rw [hpath_dir]
    have hboundaryFinite :
        Set.Finite
          (J.carrier ∩
            (segment ℝ z (start i) ∪
              segment ℝ (start i) (start (σ i)) ∪ segment ℝ (start (σ i)) z)) := by
      let triSides : Set E :=
        segment ℝ z (start i) ∪
          segment ℝ (start i) (start (σ i)) ∪ segment ℝ (start (σ i)) z
      have hfiniteZA :
          ∀ p : {p : E // p ∈ R.vertices},
            Set.Finite
              (segment ℝ p.1 (R.successor p).1 ∩ segment ℝ z (start i) : Set E) := by
        intro p
        exact (TriangleSegmentNoOverlapIntersectionSubsingleton p.1 (R.successor p).1
          z (start i) (hNoOverlapZStart i p)).1.finite
      have hfiniteAB :
          ∀ p : {p : E // p ∈ R.vertices},
            Set.Finite
              (segment ℝ p.1 (R.successor p).1 ∩
                segment ℝ (start i) (start (σ i)) : Set E) := by
        intro p
        exact (TriangleSegmentNoOverlapIntersectionSubsingleton p.1 (R.successor p).1
          (start i) (start (σ i)) (hNoOverlapAB p)).1.finite
      have hfiniteBZ :
          ∀ p : {p : E // p ∈ R.vertices},
            Set.Finite
              (segment ℝ p.1 (R.successor p).1 ∩ segment ℝ (start (σ i)) z : Set E) := by
        intro p
        exact (TriangleSegmentNoOverlapIntersectionSubsingleton p.1 (R.successor p).1
          (start (σ i)) z (hNoOverlapStartZ (σ i) p)).1.finite
      have hfinitePiece :
          ∀ p : {p : E // p ∈ R.vertices},
            Set.Finite (segment ℝ p.1 (R.successor p).1 ∩ triSides : Set E) := by
        intro p
        refine (((hfiniteZA p).union (hfiniteAB p)).union (hfiniteBZ p)).subset ?_
        intro x hx
        rcases hx with ⟨hxseg, hxtri⟩
        dsimp [triSides] at hxtri
        rcases hxtri with hleft | hbz
        · rcases hleft with hza | hab
          · exact Or.inl (Or.inl ⟨hxseg, hza⟩)
          · exact Or.inl (Or.inr ⟨hxseg, hab⟩)
        · exact Or.inr ⟨hxseg, hbz⟩
      let pieceUnion : Set E :=
        ⋃ p : {p : E // p ∈ R.vertices},
          segment ℝ p.1 (R.successor p).1 ∩ triSides
      have hVfinite : Set.Finite (R.vertices : Set E) := R.vertices.finite_toSet
      haveI : Finite {p : E // p ∈ R.vertices} := hVfinite
      have hpieceUnionFinite : Set.Finite pieceUnion := by
        apply Set.finite_iUnion
        intro p
        exact hfinitePiece p
      refine hpieceUnionFinite.subset ?_
      intro x hx
      rcases hx with ⟨hxJ, hxtri⟩
      have hxJ' := hxJ
      rw [R.cyclic_carrier_eq] at hxJ'
      simp only [Set.mem_iUnion] at hxJ'
      rcases hxJ' with ⟨p, hxseg⟩
      exact Set.mem_iUnion.2 ⟨p, ⟨hxseg, by simpa [triSides] using hxtri⟩⟩
    dsimp [CyclicPresentationTriangleGeneralPosition]
    refine ⟨?_, hzJ, start_not_Jcarrier i, start_not_Jcarrier (σ i),
      hNoOverlapZStart i, hNoOverlapAB, hNoOverlapStartZ (σ i),
      hTransZStart i, hTransAB, hTransStartZ (σ i), hboundaryFinite⟩
    intro p
    refine ⟨hVertexOffZStart i p, ?_, hVertexOffStartZ (σ i) p⟩
    intro hpseg
    have hpγ : p.1 ∈ γ.carrier := by
      rw [γ.carrier_eq]
      right
      exact ⟨i.1, hi_succ, by simpa [hmid_seg] using hpseg⟩
    exact hKpoints_off p.1 (cyclic_vertex_mem_Kpoints p) hpγ
  exact ⟨z, hzJ, hza, hbz, hside, hncol, htri⟩
