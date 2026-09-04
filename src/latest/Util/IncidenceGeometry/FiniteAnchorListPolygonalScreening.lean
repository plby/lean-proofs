import Util.IncidenceGeometry.SingleVertexPolygonalScreening
import Util.IncidenceGeometry.FinalVertexPolygonalScreening

open Classical
noncomputable section

lemma FiniteAnchorListPolygonalScreening
    (K : FinitePolygonalSet) (a target : EuclideanSpace ℝ (Fin 2))
    (anchors : List (EuclideanSpace ℝ (Fin 2))) (ρ : ℝ) :
    0 < ρ →
      a ∉ K.carrier →
        target ∉ K.carrier →
          (∀ _h : 0 < anchors.length, dist a anchors[0] < ρ) →
            anchors.getLast? = some target →
              3 ≤ anchors.length →
                ∃ xs : List (EuclideanSpace ℝ (Fin 2)),
                  xs.length = anchors.length ∧
                    xs.head? = some a ∧
                      xs.getLast? = some target ∧
                        (∀ (i : ℕ) (hxi : i < xs.length) (hai : i < anchors.length),
                          dist xs[i] anchors[i] < ρ) ∧
                          (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ xs → v ∉ K.carrier) ∧
                            (∀ (i : ℕ) (hi : i + 1 < xs.length)
                                (p : EuclideanSpace ℝ (Fin 2)),
                                p ∈ K.points → p ∉ segment ℝ xs[i] xs[i + 1]) ∧
                              (∀ (i : ℕ) (hi : i + 1 < xs.length)
                                  (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
                                  s ∈ K.segments →
                                    ¬ ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q ∧
                                      segment ℝ p q ⊆
                                        segment ℝ xs[i] xs[i + 1] ∩ segment ℝ s.1 s.2) ∧
                                (∀ (i : ℕ) (hi : i + 1 < xs.length)
                                    (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
                                    (_hs : s ∈ K.segments)
                                    (p : EuclideanSpace ℝ (Fin 2)),
                                    p ∈ openSegment ℝ xs[i] xs[i + 1] →
                                      p ∈ openSegment ℝ s.1 s.2 →
                                        ¬ ∃ c : ℝ,
                                          s.2 - s.1 = c • (xs[i + 1] - xs[i])) := by
  revert a target ρ
  induction anchors with
  | nil =>
      intro a target ρ hρ haK htargetK hclose0 hlast hlen
      simp at hlen
  | cons anchor0 rest ih =>
      intro a target ρ hρ haK htargetK hclose0 hlast hlen
      cases rest with
      | nil =>
          simp at hlen
      | cons anchor1 rest' =>
          cases rest' with
          | nil =>
              simp at hlen
          | cons anchor2 tail =>
              cases tail with
              | nil =>
                  have hlast_eq : anchor2 = target := by
                    simpa using hlast
                  subst anchor2
                  have hball_nonempty :
                      (Metric.ball anchor1 ρ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
                    refine ⟨anchor1, ?_⟩
                    rw [Metric.mem_ball, dist_self]
                    exact hρ
                  obtain ⟨x, hxball, hxK, hpoints_left, hoverlap_left, htrans_left,
                      hpoints_right, hoverlap_right, htrans_right⟩ :=
                    FinalVertexPolygonalScreening K a target (Metric.ball anchor1 ρ)
                      haK htargetK Metric.isOpen_ball hball_nonempty
                  refine ⟨[a, x, target], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simp
                  · simp
                  · simp
                  · intro i hxi _hai
                    have hi3 : i < 3 := by simpa using hxi
                    interval_cases i
                    · simpa using hclose0 (by simp)
                    · simpa [Metric.mem_ball] using hxball
                    · change dist target target < ρ
                      rw [dist_self]
                      exact hρ
                  · intro v hv
                    simp only [List.mem_cons, List.not_mem_nil] at hv
                    rcases hv with rfl | rfl | hvtarget
                    · exact haK
                    · exact hxK
                    · rcases hvtarget with rfl | hvnil
                      · exact htargetK
                      · cases hvnil
                  · intro i hi p hpK hpseg
                    have hi2 : i < 2 := by
                      have hi3 : i + 1 < 3 := by simpa using hi
                      omega
                    interval_cases i
                    · exact hpoints_left p hpK (by simpa using hpseg)
                    · exact hpoints_right p hpK (by simpa using hpseg)
                  · intro i hi s hsK hover
                    have hi2 : i < 2 := by
                      have hi3 : i + 1 < 3 := by simpa using hi
                      omega
                    interval_cases i
                    · exact hoverlap_left s hsK (by simpa using hover)
                    · exact hoverlap_right s hsK (by simpa using hover)
                  · intro i hi s hsK p hpopen hpsopen
                    have hi2 : i < 2 := by
                      have hi3 : i + 1 < 3 := by simpa using hi
                      omega
                    interval_cases i
                    · exact htrans_left s hsK p (by simpa using hpopen) hpsopen
                    · exact htrans_right s hsK p (by simpa using hpopen) hpsopen
              | cons anchor3 tail' =>
                  have hball_nonempty :
                      (Metric.ball anchor1 ρ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
                    refine ⟨anchor1, ?_⟩
                    rw [Metric.mem_ball, dist_self]
                    exact hρ
                  obtain ⟨x, hxball, hxK, hpoints_first, hoverlap_first,
                      htrans_first⟩ :=
                    SingleVertexPolygonalScreening K a (Metric.ball anchor1 ρ)
                      haK Metric.isOpen_ball hball_nonempty
                  have hclose_tail :
                      ∀ _h : 0 < (anchor1 :: anchor2 :: anchor3 :: tail').length,
                        dist x (anchor1 :: anchor2 :: anchor3 :: tail')[0] < ρ := by
                    intro _h
                    simpa [Metric.mem_ball] using hxball
                  have hlast_tail :
                      (anchor1 :: anchor2 :: anchor3 :: tail').getLast? = some target := by
                    simpa using hlast
                  have hlen_tail : 3 ≤ (anchor1 :: anchor2 :: anchor3 :: tail').length := by
                    simp
                  obtain ⟨ys, hys_len, hys_head, hys_last, hys_close, hys_vertices,
                      hys_points, hys_overlap, hys_trans⟩ :=
                    ih x target ρ hρ hxK htargetK hclose_tail hlast_tail hlen_tail
                  have hys0 : ys[0] = x := by
                    cases ys with
                    | nil =>
                        simp at hys_head
                    | cons y ys' =>
                        simp only [List.getElem_cons_zero] at hys_head ⊢
                        simpa using hys_head
                  refine ⟨a :: ys, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simp [hys_len]
                  · simp
                  · cases ys with
                    | nil =>
                        simp at hys_len
                    | cons y ys' =>
                        simp only [List.getLast?_cons_cons] at hys_last ⊢
                        exact hys_last
                  · intro i hxi hai
                    cases i with
                    | zero =>
                        have hclose_anchor0 := hclose0 (by simp)
                        change dist a anchor0 < ρ at hclose_anchor0
                        exact hclose_anchor0
                    | succ j =>
                        have hxi' : j < ys.length := by
                          simp at hxi
                          omega
                        have hai' : j < (anchor1 :: anchor2 :: anchor3 :: tail').length := by
                          simp at hai
                          omega
                        simpa using hys_close j hxi' hai'
                  · intro v hv
                    simp only [List.mem_cons] at hv
                    rcases hv with rfl | hvys
                    · exact haK
                    · exact hys_vertices v hvys
                  · intro i hi p hpK hpseg
                    cases i with
                    | zero =>
                        exact hpoints_first p hpK (by simpa [hys0] using hpseg)
                    | succ j =>
                        have hiy : j + 1 < ys.length := by
                          simp at hi
                          omega
                        exact hys_points j hiy p hpK (by simpa using hpseg)
                  · intro i hi s hsK hover
                    cases i with
                    | zero =>
                        exact hoverlap_first s hsK (by simpa [hys0] using hover)
                    | succ j =>
                        have hiy : j + 1 < ys.length := by
                          simp at hi
                          omega
                        exact hys_overlap j hiy s hsK (by simpa using hover)
                  · intro i hi s hsK p hpopen hpsopen
                    cases i with
                    | zero =>
                        simpa [hys0] using
                          htrans_first s hsK p (by simpa [hys0] using hpopen) hpsopen
                    | succ j =>
                        have hiy : j + 1 < ys.length := by
                          simp at hi
                          omega
                        exact hys_trans j hiy s hsK p (by simpa using hpopen) hpsopen
