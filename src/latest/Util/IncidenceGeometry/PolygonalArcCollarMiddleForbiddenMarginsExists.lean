import Util.IncidenceGeometry.PolygonalArcCollarMiddleForbiddenMargins
import Util.IncidenceGeometry.PositiveSeparation
import Mathlib.Analysis.Normed.Module.Convex

open Classical
noncomputable section

lemma PolygonalArcCollarMiddleForbiddenMarginsExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii) :
    Nonempty (PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) := by
  let E := EuclideanSpace ℝ (Fin 2)
  let n := γ.vertices.length
  have hlen_pos : 0 < n := by
    have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
    dsimp [n]
    omega
  letI : Nonempty (Fin n) := ⟨⟨0, hlen_pos⟩⟩
  have segment_nonempty :
      ∀ (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (segment ℝ γ.vertices[k] γ.vertices[k + 1]).Nonempty := by
    intro k hk
    exact ⟨γ.vertices[k], by simp [left_mem_segment]⟩
  have segment_compact :
      ∀ (k : ℕ) (hk : k + 1 < γ.vertices.length),
        IsCompact (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
    intro k hk
    rw [segment_eq_image' ℝ γ.vertices[k] γ.vertices[k + 1]]
    exact isCompact_Icc.image
      (by fun_prop :
        Continuous (fun θ : ℝ =>
          γ.vertices[k] + θ • (γ.vertices[k + 1] - γ.vertices[k])))
  have middle_segment_pair_separation :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            ∃ δ : ℝ, 0 < δ ∧
              ∀ z, z ∈ middleSegments.middle j hj →
                ∀ q, q ∈ segment ℝ γ.vertices[k] γ.vertices[k + 1] →
                  δ ≤ dist z q := by
    intro j hj k hk hgap
    have hdisj :
        Disjoint (middleSegments.middle j hj)
          (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
      rw [Set.disjoint_left]
      intro x hxM hxSeg
      have hxSegj :
          x ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] :=
        middleSegments.middle_subset_segment j hj hxM
      cases hgap with
      | inl hlt =>
          have hjk : j < k := by omega
          have hnot : k ≠ j + 1 := by omega
          have hinter :=
            γ.segment_intersections (i := j) (j := k) hj hk hjk
          have hxInter :
              x ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] ∩
                segment ℝ γ.vertices[k] γ.vertices[k + 1] :=
            ⟨hxSegj, hxSeg⟩
          have hxEmpty : x ∈ (∅ : Set E) := by
            simpa [hnot, E] using show
              x ∈ (if k = j + 1 then {γ.vertices[k]} else
                    (∅ : Set E)) by
                simpa [hinter, E] using hxInter
          simpa using hxEmpty
      | inr hlt =>
          have hkj : k < j := by omega
          have hnot : j ≠ k + 1 := by omega
          have hinter :=
            γ.segment_intersections (i := k) (j := j) hk hj hkj
          have hxInter :
              x ∈ segment ℝ γ.vertices[k] γ.vertices[k + 1] ∩
                segment ℝ γ.vertices[j] γ.vertices[j + 1] :=
            ⟨hxSeg, hxSegj⟩
          have hxEmpty : x ∈ (∅ : Set E) := by
            simpa [hnot, E] using show
              x ∈ (if j = k + 1 then {γ.vertices[j]} else
                    (∅ : Set E)) by
                simpa [hinter, E] using hxInter
          simpa using hxEmpty
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation (middleSegments.middle_nonempty j hj)
        (segment_nonempty k hk) (middleSegments.middle_compact j hj)
        (segment_compact k hk) hdisj
    exact ⟨δ, hδpos, hδ⟩
  have middle_disk_pair_separation :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (i : Fin γ.vertices.length), i.1 ≠ j → i.1 ≠ j + 1 →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ z, z ∈ middleSegments.middle j hj →
              ∀ q, q ∈ Metric.closedBall γ.vertices[i.1] (controlRadii.radius i) →
                δ ≤ dist z q := by
    intro j hj i hij hijs
    have hball_nonempty :
        (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)).Nonempty := by
      exact ⟨γ.vertices[i.1], by
        rw [Metric.mem_closedBall]
        simpa using (controlRadii.radius_pos i).le⟩
    have hball_compact :
        IsCompact (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)) :=
      isCompact_closedBall γ.vertices[i.1] (controlRadii.radius i)
    have hdisj :
        Disjoint (middleSegments.middle j hj)
          (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)) := by
      rw [Set.disjoint_left]
      intro x hxM hxBall
      have hxSeg :
          x ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] :=
        middleSegments.middle_subset_segment j hj hxM
      have hcontrol :=
        controlRadii.nonincident_segment_disjoint (i := i) (j := j) hj hij hijs
      exact (Set.disjoint_left.mp hcontrol hxBall) hxSeg
    obtain ⟨δ, hδpos, hδ⟩ :=
      PositiveSeparation (middleSegments.middle_nonempty j hj) hball_nonempty
        (middleSegments.middle_compact j hj) hball_compact hdisj
    exact ⟨δ, hδpos, hδ⟩
  let segmentTerm : (j : ℕ) → (hj : j + 1 < γ.vertices.length) → Fin n → ℝ :=
    fun j hj k =>
      if h : k.1 + 1 < γ.vertices.length ∧
          (j + 1 < k.1 ∨ k.1 + 1 < j) then
        Classical.choose
          (middle_segment_pair_separation j hj k.1 h.1 h.2)
      else
        (1 : ℝ)
  let segmentBound : (j : ℕ) → (hj : j + 1 < γ.vertices.length) → ℝ :=
    fun j hj =>
      (Finset.univ : Finset (Fin n)).inf' Finset.univ_nonempty
        (segmentTerm j hj)
  have segmentTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (k : Fin n),
        0 < segmentTerm j hj k := by
    intro j hj k
    dsimp [segmentTerm]
    by_cases h : k.1 + 1 < γ.vertices.length ∧
        (j + 1 < k.1 ∨ k.1 + 1 < j)
    · simpa [h] using
        (Classical.choose_spec
          (middle_segment_pair_separation j hj k.1 h.1 h.2)).1
    · simp [h]
  have segmentBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < segmentBound j hj := by
    intro j hj
    dsimp [segmentBound]
    exact (Finset.lt_inf'_iff _).2 (by
      intro k _hk
      exact segmentTerm_pos j hj k)
  let diskTerm : (j : ℕ) → (hj : j + 1 < γ.vertices.length) → Fin n → ℝ :=
    fun j hj i =>
      if h : i.1 ≠ j ∧ i.1 ≠ j + 1 then
        Classical.choose
          (middle_disk_pair_separation j hj ⟨i.1, by simpa [n] using i.2⟩
            h.1 h.2)
      else
        (1 : ℝ)
  let diskBound : (j : ℕ) → (hj : j + 1 < γ.vertices.length) → ℝ :=
    fun j hj =>
      (Finset.univ : Finset (Fin n)).inf' Finset.univ_nonempty
        (diskTerm j hj)
  have diskTerm_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (i : Fin n),
        0 < diskTerm j hj i := by
    intro j hj i
    dsimp [diskTerm]
    by_cases h : i.1 ≠ j ∧ i.1 ≠ j + 1
    · simpa [h] using
        (Classical.choose_spec
          (middle_disk_pair_separation j hj
            ⟨i.1, by simpa [n] using i.2⟩ h.1 h.2)).1
    · simp [h]
  have diskBound_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < diskBound j hj := by
    intro j hj
    dsimp [diskBound]
    exact (Finset.lt_inf'_iff _).2 (by
      intro i _hi
      exact diskTerm_pos j hj i)
  let margin : (j : ℕ) → j + 1 < γ.vertices.length → ℝ :=
    fun j hj => min (segmentBound j hj) (diskBound j hj)
  have margin_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < margin j hj := by
    intro j hj
    dsimp [margin]
    exact lt_min (segmentBound_pos j hj) (diskBound_pos j hj)
  have margin_le_segment_pair :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (hgap : j + 1 < k ∨ k + 1 < j) →
            margin j hj ≤
              Classical.choose
                (middle_segment_pair_separation j hj k hk hgap) := by
    intro j hj k hk hgap
    let kf : Fin n := ⟨k, by
      dsimp [n]
      exact Nat.lt_of_succ_lt hk⟩
    have hcond : kf.1 + 1 < γ.vertices.length ∧
        (j + 1 < kf.1 ∨ kf.1 + 1 < j) := by
      exact ⟨hk, by simpa [kf] using hgap⟩
    have hbound :
        segmentBound j hj ≤
          Classical.choose
            (middle_segment_pair_separation j hj k hk hgap) := by
      have hentry : segmentBound j hj ≤ segmentTerm j hj kf := by
        dsimp [segmentBound]
        exact Finset.inf'_le (segmentTerm j hj) (Finset.mem_univ kf)
      simpa [segmentTerm, hcond, kf] using hentry
    exact le_trans (min_le_left _ _) hbound
  have margin_le_disk_pair :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (i : Fin γ.vertices.length), (hij : i.1 ≠ j) → (hijs : i.1 ≠ j + 1) →
          margin j hj ≤
            Classical.choose
              (middle_disk_pair_separation j hj i hij hijs) := by
    intro j hj i hij hijs
    let iF : Fin n := ⟨i.1, by
      dsimp [n]
      exact i.2⟩
    have hcond : iF.1 ≠ j ∧ iF.1 ≠ j + 1 := by
      exact ⟨by simpa [iF] using hij, by simpa [iF] using hijs⟩
    have hbound :
        diskBound j hj ≤
          Classical.choose
            (middle_disk_pair_separation j hj i hij hijs) := by
      have hentry : diskBound j hj ≤ diskTerm j hj iF := by
        dsimp [diskBound]
        exact Finset.inf'_le (diskTerm j hj) (Finset.mem_univ iF)
      simpa [diskTerm, hcond, iF] using hentry
    exact le_trans (min_le_right _ _) hbound
  refine ⟨
    { margin := margin
      margin_pos := margin_pos
      middle_segment_separation := ?_
      middle_control_disk_separation := ?_
      middle_core_separation := ?_ }⟩
  · intro j hj k hk hgap z hz q hq
    exact le_trans (margin_le_segment_pair j hj k hk hgap)
      ((Classical.choose_spec
        (middle_segment_pair_separation j hj k hk hgap)).2 z hz q hq)
  · intro j hj i hij hijs z hz q hq
    exact le_trans (margin_le_disk_pair j hj i hij hijs)
      ((Classical.choose_spec
        (middle_disk_pair_separation j hj i hij hijs)).2 z hz q hq)
  · intro j hj k hk hgap z hz q hq
    exact le_trans (margin_le_segment_pair j hj k hk hgap)
      ((Classical.choose_spec
        (middle_segment_pair_separation j hj k hk hgap)).2 z hz q
          (middleSegments.middle_subset_segment k hk hq))
