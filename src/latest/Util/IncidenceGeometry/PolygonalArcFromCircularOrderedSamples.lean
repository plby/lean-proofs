import Util.IncidenceGeometry.CircularOrderedSamplesBasicChordControls
import Util.IncidenceGeometry.CircularOrderedSamplesNonadjacentChordInteriors

open Classical
noncomputable section

noncomputable def PolygonalArcFromCircularOrderedSamples
    {m : ℕ} (hm : 0 < m)
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hγ_cont : Continuous γ)
    (hγ_inj : Function.Injective γ)
    (hγ_circle : ∀ t, dist (γ t) c = r)
    (params : Fin (m + 1) → Set.Icc (0 : ℝ) 1)
    (hparams_strict :
      ∀ ⦃i j : Fin (m + 1)⦄, i < j → params i < params j) :
    PolygonalArc :=
  let vertices : List (EuclideanSpace ℝ (Fin 2)) :=
    List.ofFn (fun k : Fin (m + 1) => γ (params k))
  { vertices := vertices
    length_ge_two := by
      dsimp [vertices]
      simp
      omega
    source := γ (params ⟨0, by omega⟩)
    target := γ (params ⟨m, by omega⟩)
    source_eq_head := by
      dsimp [vertices]
      simp
    target_eq_last := by
      dsimp [vertices]
      rw [List.getLast?_eq_getLast_of_ne_nil]
      · rw [List.getLast_ofFn_succ]
        rfl
      · simp
    carrier :=
      {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
        p ∈ segment ℝ vertices[i] vertices[i + 1]}
    relativeInterior :=
      {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
        p ∈ segment ℝ vertices[i] vertices[i + 1]} \
        ({γ (params ⟨0, by omega⟩), γ (params ⟨m, by omega⟩)} :
          Set (EuclideanSpace ℝ (Fin 2)))
    carrier_eq := by rfl
    relativeInterior_eq := by rfl
    simple_vertices := by
      have hbasic :=
        CircularOrderedSamplesBasicChordControls
          (m := m) (c := c) (r := r) (γ := γ)
          hγ_inj hγ_circle params hparams_strict
      simpa [vertices] using hbasic.1
    segment_intersections := by
      have hbasic :=
        CircularOrderedSamplesBasicChordControls
          (m := m) (c := c) (r := r) (γ := γ)
          hγ_inj hγ_circle params hparams_strict
      have hnonadj :=
        CircularOrderedSamplesNonadjacentChordInteriors
          (m := m) (c := c) (r := r) (γ := γ)
          hγ_cont hγ_inj hγ_circle params hparams_strict
      have hvertices_length : vertices.length = m + 1 := by
        dsimp [vertices]
        simp
      have hnodup : vertices.Nodup := by
        simpa [vertices] using hbasic.1
      have hadjacent :
          ∀ i
            (hi : (i + 1) + 1 < vertices.length),
            (segment ℝ vertices[i] vertices[i + 1] ∩
                segment ℝ vertices[i + 1] vertices[(i + 1) + 1]) =
              {vertices[i + 1]} := by
        simpa [vertices] using hbasic.2.1
      have havoid :
          ∀ ⦃i k : ℕ⦄,
            (hi : i + 1 < vertices.length) →
            (hk : k < vertices.length) →
            k ≠ i →
            k ≠ i + 1 →
            vertices[k] ∉ openSegment ℝ vertices[i] vertices[i + 1] := by
        simpa [vertices] using hbasic.2.2
      have hopen_disjoint :
          ∀ ⦃i j : ℕ⦄,
            (hi : i + 1 < vertices.length) →
            (hj : j + 1 < vertices.length) →
            i + 1 < j →
            Disjoint (openSegment ℝ vertices[i] vertices[i + 1])
              (openSegment ℝ vertices[j] vertices[j + 1]) := by
        simpa [vertices] using hnonadj
      have vertex_ne_of_ne :
          ∀ {a b : ℕ} (ha : a < vertices.length) (hb : b < vertices.length),
            a ≠ b → vertices[a] ≠ vertices[b] := by
        intro a b ha hb hne heq
        exact hne
          ((hnodup.getElem_inj_iff (i := a) (j := b) (hi := ha) (hj := hb)).1 heq)
      intro i j hi hj hij
      by_cases hsucc : j = i + 1
      · subst j
        simp [hadjacent i hj]
      · have hgap : i + 1 < j := by omega
        have hempty :
            (segment ℝ vertices[i] vertices[i + 1] ∩
                segment ℝ vertices[j] vertices[j + 1]) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro p hp
          have hi_len : i < vertices.length := by omega
          have hi1_len : i + 1 < vertices.length := hi
          have hj_len : j < vertices.length := by omega
          have hj1_len : j + 1 < vertices.length := hj
          by_cases hp_i : p = vertices[i]
          · have hp_seg_j : vertices[i] ∈ segment ℝ vertices[j] vertices[j + 1] := by
              simpa [hp_i] using hp.2
            have hopen_j : vertices[i] ∈ openSegment ℝ vertices[j] vertices[j + 1] :=
              mem_openSegment_of_ne_left_right
                (vertex_ne_of_ne hj_len hi_len (by omega))
                (vertex_ne_of_ne hj1_len hi_len (by omega))
                hp_seg_j
            exact havoid (i := j) (k := i) hj hi_len (by omega) (by omega) hopen_j
          · by_cases hp_i1 : p = vertices[i + 1]
            · have hp_seg_j : vertices[i + 1] ∈ segment ℝ vertices[j] vertices[j + 1] := by
                simpa [hp_i1] using hp.2
              have hopen_j : vertices[i + 1] ∈ openSegment ℝ vertices[j] vertices[j + 1] :=
                mem_openSegment_of_ne_left_right
                  (vertex_ne_of_ne hj_len hi1_len (by omega))
                  (vertex_ne_of_ne hj1_len hi1_len (by omega))
                  hp_seg_j
              exact havoid (i := j) (k := i + 1) hj hi1_len (by omega) (by omega) hopen_j
            · by_cases hp_j : p = vertices[j]
              · have hp_seg_i : vertices[j] ∈ segment ℝ vertices[i] vertices[i + 1] := by
                  simpa [hp_j] using hp.1
                have hopen_i : vertices[j] ∈ openSegment ℝ vertices[i] vertices[i + 1] :=
                  mem_openSegment_of_ne_left_right
                    (vertex_ne_of_ne hi_len hj_len (by omega))
                    (vertex_ne_of_ne hi1_len hj_len (by omega))
                    hp_seg_i
                exact havoid (i := i) (k := j) hi hj_len (by omega) (by omega) hopen_i
              · by_cases hp_j1 : p = vertices[j + 1]
                · have hp_seg_i : vertices[j + 1] ∈ segment ℝ vertices[i] vertices[i + 1] := by
                    simpa [hp_j1] using hp.1
                  have hopen_i :
                      vertices[j + 1] ∈ openSegment ℝ vertices[i] vertices[i + 1] :=
                    mem_openSegment_of_ne_left_right
                      (vertex_ne_of_ne hi_len hj1_len (by omega))
                      (vertex_ne_of_ne hi1_len hj1_len (by omega))
                      hp_seg_i
                  exact havoid (i := i) (k := j + 1) hi hj1_len (by omega) (by omega) hopen_i
                · have hopen_i :
                      p ∈ openSegment ℝ vertices[i] vertices[i + 1] :=
                    mem_openSegment_of_ne_left_right
                      (by intro h; exact hp_i h.symm)
                      (by intro h; exact hp_i1 h.symm)
                      hp.1
                  have hopen_j :
                      p ∈ openSegment ℝ vertices[j] vertices[j + 1] :=
                    mem_openSegment_of_ne_left_right
                      (by intro h; exact hp_j h.symm)
                      (by intro h; exact hp_j1 h.symm)
                      hp.2
                  exact (Set.disjoint_left.mp (hopen_disjoint hi hj hgap) hopen_i) hopen_j
        simp [hsucc, hempty]
    vertices_avoid_nonincident_interiors := by
      have hbasic :=
        CircularOrderedSamplesBasicChordControls
          (m := m) (c := c) (r := r) (γ := γ)
          hγ_inj hγ_circle params hparams_strict
      simpa [vertices] using hbasic.2.2 }
