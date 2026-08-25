import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingSegmentOrderedWindowParameters
    (α : PolygonalPath) (i : ℕ) (hi : i + 1 < α.vertices.length)
    (cutBefore cutAfter :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (params : List ℝ) :
    (∀ n (hn : n < params.length),
      ∃ b a : ℝ,
        0 < b ∧ b < params[n] ∧ params[n] < a ∧ a < 1 ∧
          AffineMap.lineMap α.vertices[i] α.vertices[i + 1] b =
            cutBefore (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]) ∧
            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] a =
              cutAfter (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])) →
      (∀ n (hn : n + 1 < params.length), params[n] < params[n + 1]) →
        (∀ n (hn : n + 1 < params.length),
          Disjoint
            (segment ℝ
              (cutBefore (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]))
              (cutAfter (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])))
            (segment ℝ
              (cutBefore
                (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n + 1]))
              (cutAfter
                (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n + 1])))) →
          ∃ left right : (n : ℕ) → n < params.length → ℝ,
            (∀ n (hn : n < params.length),
              0 < left n hn ∧ left n hn < params[n] ∧
                params[n] < right n hn ∧ right n hn < 1 ∧
                  AffineMap.lineMap α.vertices[i] α.vertices[i + 1] (left n hn) =
                    cutBefore
                      (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]) ∧
                    AffineMap.lineMap α.vertices[i] α.vertices[i + 1] (right n hn) =
                      cutAfter
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])) ∧
              (∀ n (hn : n + 1 < params.length),
                right n (Nat.lt_of_succ_lt hn) < left (n + 1) hn) := by
  intro hwindow hparam_order hdisjoint
  let left : (n : ℕ) → n < params.length → ℝ :=
    fun n hn => Classical.choose (hwindow n hn)
  let right : (n : ℕ) → n < params.length → ℝ :=
    fun n hn => Classical.choose (Classical.choose_spec (hwindow n hn))
  have hspec :
      ∀ n (hn : n < params.length),
        0 < left n hn ∧ left n hn < params[n] ∧
          params[n] < right n hn ∧ right n hn < 1 ∧
            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] (left n hn) =
              cutBefore (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]) ∧
              AffineMap.lineMap α.vertices[i] α.vertices[i + 1] (right n hn) =
                cutAfter (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]) := by
    intro n hn
    dsimp [left, right]
    exact Classical.choose_spec (Classical.choose_spec (hwindow n hn))
  refine ⟨left, right, hspec, ?_⟩
  intro n hn
  have hn0 : n < params.length := Nat.lt_of_succ_lt hn
  have hn1 : n + 1 < params.length := hn
  have hs0 := hspec n hn0
  have hs1 := hspec (n + 1) hn1
  have lineMap_mem_segment_of_between :
      ∀ {alpha beta s : ℝ}, alpha < beta → alpha ≤ s → s ≤ beta →
        AffineMap.lineMap α.vertices[i] α.vertices[i + 1] s ∈
          segment ℝ
            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] alpha)
            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] beta) := by
    intro alpha beta s halpha_beta halpha_s hs_beta
    rw [segment_eq_image_lineMap]
    let theta : ℝ := (s - alpha) / (beta - alpha)
    refine ⟨theta, ?_, ?_⟩
    · constructor
      · dsimp [theta]
        exact div_nonneg (sub_nonneg.mpr halpha_s) (sub_nonneg.mpr halpha_beta.le)
      · dsimp [theta]
        rw [div_le_one (sub_pos.mpr halpha_beta)]
        linarith
    · ext k
      simp [theta, AffineMap.lineMap_apply_module]
      field_simp [sub_ne_zero.mpr halpha_beta.ne']
      ring
  by_contra hnot
  have hleft_next_le_right : left (n + 1) hn1 ≤ right n hn0 := le_of_not_gt hnot
  let s : ℝ := max (left n hn0) (left (n + 1) hn1)
  have hleft_right0 : left n hn0 < right n hn0 := hs0.2.1.trans hs0.2.2.1
  have hleft_right1 : left (n + 1) hn1 < right (n + 1) hn1 :=
    hs1.2.1.trans hs1.2.2.1
  have hs_left0 : left n hn0 ≤ s := le_max_left _ _
  have hs_left1 : left (n + 1) hn1 ≤ s := le_max_right _ _
  have hleft0_le_right1 : left n hn0 ≤ right (n + 1) hn1 := by
    linarith [hparam_order n hn, hs0.2.1, hs1.2.2.1]
  have hs_right0 : s ≤ right n hn0 :=
    max_le (le_of_lt hleft_right0) hleft_next_le_right
  have hs_right1 : s ≤ right (n + 1) hn1 :=
    max_le hleft0_le_right1 (le_of_lt hleft_right1)
  have hp0seg :
      AffineMap.lineMap α.vertices[i] α.vertices[i + 1] s ∈
        segment ℝ
          (cutBefore (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n]))
          (cutAfter (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n])) := by
    simpa [hs0.2.2.2.2.1, hs0.2.2.2.2.2] using
      lineMap_mem_segment_of_between hleft_right0 hs_left0 hs_right0
  have hp1seg :
      AffineMap.lineMap α.vertices[i] α.vertices[i + 1] s ∈
        segment ℝ
          (cutBefore
            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n + 1]))
          (cutAfter
            (AffineMap.lineMap α.vertices[i] α.vertices[i + 1] params[n + 1])) := by
    simpa [hs1.2.2.2.2.1, hs1.2.2.2.2.2] using
      lineMap_mem_segment_of_between hleft_right1 hs_left1 hs_right1
  exact (Set.disjoint_left.mp (hdisjoint n hn)) hp0seg hp1seg
