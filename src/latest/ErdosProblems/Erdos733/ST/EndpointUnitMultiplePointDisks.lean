import ErdosProblems.Erdos733.ST.EndpointUnitChordMultiplePointControl

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitMultiplePointDisks]
lemma EndpointUnitMultiplePointDisks {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (ha : ∀ i, dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hb : ∀ i, dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hdistinct : Function.Injective (fun x : ι ⊕ ι => Sum.elim a b x)) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin 2)),
      ∃ r : EuclideanSpace ℝ (Fin 2) → ℝ,
        (∀ z, z ∈ T ↔
          z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
            ∃ i j k : ι,
              i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
                z ∈ openSegment ℝ (a i) (b i) ∧
                  z ∈ openSegment ℝ (a j) (b j) ∧
                    z ∈ openSegment ℝ (a k) (b k)) ∧
          (∀ z ∈ T, 0 < r z) ∧
            (∀ z ∈ T,
              Metric.closedBall z (r z) ⊆
                Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
              (∀ ⦃z w : EuclideanSpace ℝ (Fin 2)⦄,
                z ∈ T → w ∈ T → z ≠ w →
                  Disjoint (Metric.closedBall z (r z)) (Metric.closedBall w (r w))) ∧
                (∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
                  z ∈ T → ∀ i,
                    z ∉ segment ℝ (a i) (b i) →
                      Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i))) ∧
                  (∀ ⦃z y : EuclideanSpace ℝ (Fin 2)⦄,
                    z ∈ T →
                      y ∈ Metric.closedBall z (r z) →
                        (∃ i j : ι,
                          i ≠ j ∧
                            y ∈ segment ℝ (a i) (b i) ∧
                              y ∈ segment ℝ (a j) (b j)) →
                          y = z) ∧
                    (∀ ⦃z : EuclideanSpace ℝ (Fin 2)⦄,
                      z ∈ T → ∀ i,
                        z ∈ openSegment ℝ (a i) (b i) →
                          ∃ u v : EuclideanSpace ℝ (Fin 2),
                            u ∈ Metric.sphere z (r z) ∧
                              v ∈ Metric.sphere z (r z) ∧
                                u ∈ segment ℝ (a i) (b i) ∧
                                  v ∈ segment ℝ (a i) (b i) ∧
                                    z ∈ openSegment ℝ u v ∧
                                      Metric.closedBall z (r z) ∩
                                          segment ℝ (a i) (b i) =
                                        segment ℝ u v) := by
-- BODY
  let triplePoints : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      ∃ i j k : ι,
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
          p ∈ openSegment ℝ (a i) (b i) ∧
            p ∈ openSegment ℝ (a j) (b j) ∧
              p ∈ openSegment ℝ (a k) (b k)}
  have hcontrol :
      triplePoints.Finite ∧
        (∀ i, a i ≠ b i) ∧
          (∀ ⦃i j : ι⦄,
            i ≠ j →
              ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (a i) (b i) ∩ segment ℝ (a j) (b j)) ∧
            (∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
              i ≠ j →
                p ∈ openSegment ℝ (a i) (b i) →
                  p ∈ openSegment ℝ (a j) (b j) →
                    q ∈ openSegment ℝ (a i) (b i) →
                      q ∈ openSegment ℝ (a j) (b j) →
                        p = q) ∧
              (∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
                i ≠ j →
                  p ∈ openSegment ℝ (a i) (b i) →
                    p ∈ openSegment ℝ (a j) (b j) →
                      ¬ ∃ t : ℝ, b j - a j = t • (b i - a i)) := by
    simpa [triplePoints] using EndpointUnitChordMultiplePointControl a b ha hb hdistinct
  rcases hcontrol with
    ⟨hfinite, hendpoint_ne, hno_shared_segment, hopen_inter_unique,
      hnonscalar_direction⟩
  let T : Finset (EuclideanSpace ℝ (Fin 2)) := hfinite.toFinset
  have hT_mem : ∀ z : EuclideanSpace ℝ (Fin 2), z ∈ T ↔ z ∈ triplePoints := by
    intro z
    simp [T]
  have radius_exists :
      ∀ z : EuclideanSpace ℝ (Fin 2), z ∈ T →
        ∃ R : ℝ,
          0 < R ∧
            Metric.closedBall z R ⊆
              Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
              (∀ ⦃w : EuclideanSpace ℝ (Fin 2)⦄,
                w ∈ T → z ≠ w → R < dist z w / 2) ∧
                (∀ i,
                  z ∉ segment ℝ (a i) (b i) →
                    Disjoint (Metric.closedBall z R) (segment ℝ (a i) (b i))) ∧
                  (∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
                    y ∈ Metric.closedBall z R →
                      (∃ i j : ι,
                        i ≠ j ∧
                          y ∈ segment ℝ (a i) (b i) ∧
                            y ∈ segment ℝ (a j) (b j)) →
                        y = z) ∧
                    (∀ i,
                      z ∈ openSegment ℝ (a i) (b i) →
                        ∃ u v : EuclideanSpace ℝ (Fin 2),
                          u ∈ Metric.sphere z R ∧
                            v ∈ Metric.sphere z R ∧
                              u ∈ segment ℝ (a i) (b i) ∧
                                v ∈ segment ℝ (a i) (b i) ∧
                                  z ∈ openSegment ℝ u v ∧
                                    Metric.closedBall z R ∩
                                        segment ℝ (a i) (b i) =
                                      segment ℝ u v) := by
    intro z hz
    have hz_triple : z ∈ triplePoints := (hT_mem z).mp hz
    have hz_ball : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := hz_triple.1
    rcases hz_triple.2 with
      ⟨i0, _j0, _k0, _hij0, _hik0, _hjk0, _hzi0, _hzj0, _hzk0⟩
    letI : Nonempty ι := ⟨i0⟩
    letI : Nonempty {w : EuclideanSpace ℝ (Fin 2) // w ∈ T} := ⟨⟨z, hz⟩⟩
    have segment_closed :
        ∀ i, IsClosed (segment ℝ (a i) (b i)) := by
      intro i
      rw [← convexHull_pair (𝕜 := ℝ) (a i) (b i)]
      exact (by
        simp : ({a i, b i} : Set (EuclideanSpace ℝ (Fin 2))).Finite).isClosed_convexHull ℝ
    have hz_dist_lt_one : dist z (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
      simpa [Metric.mem_ball] using hz_ball
    have z_ne_a : ∀ i, z ≠ a i := by
      intro i h
      have hdist : dist z (0 : EuclideanSpace ℝ (Fin 2)) = 1 := by
        simpa [h] using ha i
      linarith
    have z_ne_b : ∀ i, z ≠ b i := by
      intro i h
      have hdist : dist z (0 : EuclideanSpace ℝ (Fin 2)) = 1 := by
        simpa [h] using hb i
      linarith
    have seg_gap :
        ∀ i, z ∉ segment ℝ (a i) (b i) →
          ∃ ε : ℝ, 0 < ε ∧
            Metric.closedBall z ε ⊆
              (segment ℝ (a i) (b i))ᶜ := by
      intro i hnot
      have hopen : IsOpen ((segment ℝ (a i) (b i))ᶜ) :=
        (segment_closed i).isOpen_compl
      have hzcomp : z ∈ (segment ℝ (a i) (b i))ᶜ := hnot
      rcases Metric.isOpen_iff.mp hopen z hzcomp with ⟨ε, hεpos, hεsub⟩
      refine ⟨ε / 2, half_pos hεpos, ?_⟩
      intro y hy
      exact hεsub (Metric.closedBall_subset_ball (half_lt_self hεpos) hy)
    let epsSeg : ι → ℝ := fun i =>
      if h : z ∈ segment ℝ (a i) (b i) then
        1
      else
        Classical.choose (seg_gap i h)
    have epsSeg_pos : ∀ i, 0 < epsSeg i := by
      intro i
      dsimp [epsSeg]
      split_ifs with h
      · exact (zero_lt_one : (0 : ℝ) < 1)
      · exact (Classical.choose_spec (seg_gap i h)).1
    have epsSeg_sub :
        ∀ i, z ∉ segment ℝ (a i) (b i) →
          Metric.closedBall z (epsSeg i) ⊆
            (segment ℝ (a i) (b i))ᶜ := by
      intro i hnot
      have hspec := (Classical.choose_spec (seg_gap i hnot)).2
      simpa [epsSeg, hnot] using hspec
    have epsSeg_disjoint :
        ∀ i, ∀ {ρ : ℝ}, ρ ≤ epsSeg i →
          z ∉ segment ℝ (a i) (b i) →
            Disjoint (Metric.closedBall z ρ) (segment ℝ (a i) (b i)) := by
      intro i ρ hρ hnot
      rw [Set.disjoint_left]
      intro y hy hseg
      exact (epsSeg_sub i hnot (Metric.closedBall_subset_closedBall hρ hy)) hseg
    let fT : {w // w ∈ T} → ℝ := fun w =>
      if z = (w : EuclideanSpace ℝ (Fin 2)) then
        1
      else
        dist z (w : EuclideanSpace ℝ (Fin 2)) / 2
    have fT_pos : ∀ w : {w // w ∈ T}, 0 < fT w := by
      intro w
      dsimp [fT]
      split_ifs with h
      · exact (zero_lt_one : (0 : ℝ) < 1)
      · exact half_pos (dist_pos.mpr h)
    let mT : ℝ := Finset.univ.inf' Finset.univ_nonempty fT
    have hmT_pos : 0 < mT := by
      dsimp [mT]
      exact (Finset.lt_inf'_iff _).2 (by intro w _; exact fT_pos w)
    let ρT : ℝ := mT / 2
    have hρT_pos : 0 < ρT := by
      dsimp [ρT]
      exact half_pos hmT_pos
    have hρT_lt : ∀ w : {w // w ∈ T}, ρT < fT w := by
      intro w
      exact (half_lt_self hmT_pos).trans_le (by
        dsimp [ρT, mT]
        exact Finset.inf'_le _ (Finset.mem_univ w))
    let mSeg : ℝ := Finset.univ.inf' Finset.univ_nonempty epsSeg
    have hmSeg_pos : 0 < mSeg := by
      dsimp [mSeg]
      exact (Finset.lt_inf'_iff _).2 (by intro i _; exact epsSeg_pos i)
    let ρSeg : ℝ := mSeg / 2
    have hρSeg_pos : 0 < ρSeg := by
      dsimp [ρSeg]
      exact half_pos hmSeg_pos
    have hρSeg_lt : ∀ i, ρSeg < epsSeg i := by
      intro i
      exact (half_lt_self hmSeg_pos).trans_le (by
        dsimp [ρSeg, mSeg]
        exact Finset.inf'_le _ (Finset.mem_univ i))
    let fA : ι → ℝ := fun i => dist z (a i)
    have fA_pos : ∀ i, 0 < fA i := by
      intro i
      exact dist_pos.mpr (z_ne_a i)
    let mA : ℝ := Finset.univ.inf' Finset.univ_nonempty fA
    have hmA_pos : 0 < mA := by
      dsimp [mA]
      exact (Finset.lt_inf'_iff _).2 (by intro i _; exact fA_pos i)
    let ρA : ℝ := mA / 2
    have hρA_pos : 0 < ρA := by
      dsimp [ρA]
      exact half_pos hmA_pos
    have hρA_lt : ∀ i, ρA < fA i := by
      intro i
      exact (half_lt_self hmA_pos).trans_le (by
        dsimp [ρA, mA]
        exact Finset.inf'_le _ (Finset.mem_univ i))
    let fB : ι → ℝ := fun i => dist z (b i)
    have fB_pos : ∀ i, 0 < fB i := by
      intro i
      exact dist_pos.mpr (z_ne_b i)
    let mB : ℝ := Finset.univ.inf' Finset.univ_nonempty fB
    have hmB_pos : 0 < mB := by
      dsimp [mB]
      exact (Finset.lt_inf'_iff _).2 (by intro i _; exact fB_pos i)
    let ρB : ℝ := mB / 2
    have hρB_pos : 0 < ρB := by
      dsimp [ρB]
      exact half_pos hmB_pos
    have hρB_lt : ∀ i, ρB < fB i := by
      intro i
      exact (half_lt_self hmB_pos).trans_le (by
        dsimp [ρB, mB]
        exact Finset.inf'_le _ (Finset.mem_univ i))
    let δ : ℝ := 1 - dist z (0 : EuclideanSpace ℝ (Fin 2))
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      linarith
    let M : ℝ := min δ (min ρT (min ρSeg (min ρA ρB)))
    have hM_pos : 0 < M := by
      dsimp [M]
      exact lt_min hδ_pos
        (lt_min hρT_pos (lt_min hρSeg_pos (lt_min hρA_pos hρB_pos)))
    let R : ℝ := M / 2
    have hR_pos : 0 < R := half_pos hM_pos
    have hR_lt_M : R < M := half_lt_self hM_pos
    have hM_le_δ : M ≤ δ := by
      dsimp [M]
      exact min_le_left _ _
    have hM_le_ρT : M ≤ ρT := by
      dsimp [M]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hM_le_ρSeg : M ≤ ρSeg := by
      dsimp [M]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    have hM_le_ρA : M ≤ ρA := by
      dsimp [M]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
    have hM_le_ρB : M ≤ ρB := by
      dsimp [M]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))
    have hR_lt_δ : R < δ := hR_lt_M.trans_le hM_le_δ
    have hR_lt_ρT : R < ρT := hR_lt_M.trans_le hM_le_ρT
    have hR_lt_ρSeg : R < ρSeg := hR_lt_M.trans_le hM_le_ρSeg
    have hR_lt_ρA : R < ρA := hR_lt_M.trans_le hM_le_ρA
    have hR_lt_ρB : R < ρB := hR_lt_M.trans_le hM_le_ρB
    have hball_sub :
        Metric.closedBall z R ⊆
          Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      intro y hy
      have hyz : dist y z ≤ R := by
        simpa [Metric.mem_closedBall] using hy
      have htri : dist y (0 : EuclideanSpace ℝ (Fin 2)) ≤
          dist y z + dist z (0 : EuclideanSpace ℝ (Fin 2)) :=
        dist_triangle y z (0 : EuclideanSpace ℝ (Fin 2))
      have hlt : dist y z + dist z (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        dsimp [δ] at hR_lt_δ
        linarith
      exact lt_of_le_of_lt htri hlt
    have hT_half :
        ∀ ⦃w : EuclideanSpace ℝ (Fin 2)⦄,
          w ∈ T → z ≠ w → R < dist z w / 2 := by
      intro w hw hzw
      have hlt := hρT_lt ⟨w, hw⟩
      exact hR_lt_ρT.trans (by
        simpa [fT, hzw] using hlt)
    have hnonincident :
        ∀ i,
          z ∉ segment ℝ (a i) (b i) →
            Disjoint (Metric.closedBall z R) (segment ℝ (a i) (b i)) := by
      intro i hnot
      exact epsSeg_disjoint i (le_of_lt (hR_lt_ρSeg.trans (hρSeg_lt i))) hnot
    have point_in_open_of_ball_segment :
        ∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
          y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
            ∀ i, y ∈ segment ℝ (a i) (b i) →
              y ∈ openSegment ℝ (a i) (b i) := by
      intro y hyball i hyseg
      have hydist : dist y (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
        simpa [Metric.mem_ball] using hyball
      refine mem_openSegment_of_ne_left_right ?_ ?_ hyseg
      · intro h
        have hdist : dist y (0 : EuclideanSpace ℝ (Fin 2)) = 1 := by
          simpa [h] using ha i
        linarith
      · intro h
        have hdist : dist y (0 : EuclideanSpace ℝ (Fin 2)) = 1 := by
          simpa [h] using hb i
        linarith
    have hpair_unique :
        ∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
          y ∈ Metric.closedBall z R →
            (∃ i j : ι,
              i ≠ j ∧
                y ∈ segment ℝ (a i) (b i) ∧
                  y ∈ segment ℝ (a j) (b j)) →
              y = z := by
      intro y hy htwo
      rcases htwo with ⟨i, j, hij, hyi_seg, hyj_seg⟩
      have hy_ball : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
        hball_sub hy
      have hyi_open := point_in_open_of_ball_segment hy_ball i hyi_seg
      have hyj_open := point_in_open_of_ball_segment hy_ball j hyj_seg
      have hzi_seg : z ∈ segment ℝ (a i) (b i) := by
        by_contra hnot
        have hdis := hnonincident i hnot
        rw [Set.disjoint_left] at hdis
        exact hdis hy hyi_seg
      have hzj_seg : z ∈ segment ℝ (a j) (b j) := by
        by_contra hnot
        have hdis := hnonincident j hnot
        rw [Set.disjoint_left] at hdis
        exact hdis hy hyj_seg
      have hzi_open := point_in_open_of_ball_segment hz_ball i hzi_seg
      have hzj_open := point_in_open_of_ball_segment hz_ball j hzj_seg
      exact hopen_inter_unique hij hyi_open hyj_open hzi_open hzj_open
    have segment_diameter :
        ∀ {A B z : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ},
          A ≠ B →
            z ∈ openSegment ℝ A B →
              0 < ρ →
                ρ < dist z A →
                  ρ < dist z B →
                    ∃ u v : EuclideanSpace ℝ (Fin 2),
                      u ∈ Metric.sphere z ρ ∧
                        v ∈ Metric.sphere z ρ ∧
                          u ∈ segment ℝ A B ∧
                            v ∈ segment ℝ A B ∧
                              z ∈ openSegment ℝ u v ∧
                                Metric.closedBall z ρ ∩ segment ℝ A B =
                                  segment ℝ u v := by
      intro A B z ρ hAB hzopen hρpos hρA hρB
      rw [openSegment_eq_image_lineMap] at hzopen
      rcases hzopen with ⟨t, ht, hzt⟩
      subst z
      have dist_lineMap_lineMap_local :
          ∀ c₁ c₂ : ℝ,
            dist (AffineMap.lineMap A B c₁) (AffineMap.lineMap A B c₂) =
              dist c₁ c₂ * dist A B := by
        intro c₁ c₂
        rw [dist_eq_norm, Real.dist_eq, dist_eq_norm]
        have hvec :
            AffineMap.lineMap A B c₁ - AffineMap.lineMap A B c₂ =
              (c₁ - c₂) • (B - A) := by
          apply PiLp.ext
          intro k
          simp [AffineMap.lineMap_apply_module]
          ring
        rw [hvec, norm_smul, Real.norm_eq_abs]
        have hnorm : ‖B - A‖ = ‖A - B‖ := by
          have hneg : B - A = -(A - B) := by
            abel
          rw [hneg, norm_neg]
        rw [hnorm]
      let d : ℝ := dist A B
      have hd_pos : 0 < d := by
        dsimp [d]
        exact dist_pos.mpr hAB
      let ε : ℝ := ρ / d
      have hεpos : 0 < ε := div_pos hρpos hd_pos
      have hε_lt_t : ε < t := by
        dsimp [ε]
        rw [div_lt_iff₀ hd_pos]
        have hdist : dist (AffineMap.lineMap A B t) A = t * dist A B := by
          simpa [Real.dist_eq, abs_of_pos ht.1, mul_comm] using
            dist_lineMap_lineMap_local t 0
        simpa [d, hdist] using hρA
      have hε_lt_one_sub : ε < 1 - t := by
        dsimp [ε]
        rw [div_lt_iff₀ hd_pos]
        have hdist : dist (AffineMap.lineMap A B t) B = (1 - t) * dist A B := by
          calc
            dist (AffineMap.lineMap A B t) B =
                dist (AffineMap.lineMap A B t) (AffineMap.lineMap A B (1 : ℝ)) := by
              rw [AffineMap.lineMap_apply_one]
            _ = (1 - t) * dist A B := by
              rw [dist_lineMap_lineMap_local, Real.dist_eq]
              have habs : |t - 1| = 1 - t := by
                rw [abs_of_neg (sub_neg.mpr ht.2)]
                ring
              rw [habs]
        simpa [d, hdist] using hρB
      let u : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B (t - ε)
      let v : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B (t + ε)
      have hε_mul_d : ε * d = ρ := by
        dsimp [ε, d]
        exact div_mul_cancel₀ ρ hd_pos.ne'
      have hdist_left_param : dist (t - ε) t = ε := by
        rw [Real.dist_eq]
        have hneg : t - ε - t = -ε := by ring
        rw [hneg, abs_neg, abs_of_pos hεpos]
      have hdist_right_param : dist (t + ε) t = ε := by
        rw [Real.dist_eq]
        ring_nf
        exact abs_of_pos hεpos
      have hu_sphere : u ∈ Metric.sphere (AffineMap.lineMap A B t) ρ := by
        rw [Metric.mem_sphere]
        dsimp [u]
        rw [dist_lineMap_lineMap_local, hdist_left_param, hε_mul_d]
      have hv_sphere : v ∈ Metric.sphere (AffineMap.lineMap A B t) ρ := by
        rw [Metric.mem_sphere]
        dsimp [v]
        rw [dist_lineMap_lineMap_local, hdist_right_param, hε_mul_d]
      have hu_seg : u ∈ segment ℝ A B := by
        rw [segment_eq_image_lineMap]
        refine ⟨t - ε, ?_, rfl⟩
        exact ⟨by linarith, by linarith [ht.2, hεpos]⟩
      have hv_seg : v ∈ segment ℝ A B := by
        rw [segment_eq_image_lineMap]
        refine ⟨t + ε, ?_, rfl⟩
        exact ⟨by linarith [ht.1, hεpos], by linarith⟩
      have hz_open_uv : AffineMap.lineMap A B t ∈ openSegment ℝ u v := by
        rw [openSegment_eq_image_lineMap]
        refine ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩
        apply PiLp.ext
        intro k
        simp [u, v, AffineMap.lineMap_apply_module]
        ring
      have hball_u : u ∈ Metric.closedBall (AffineMap.lineMap A B t) ρ := by
        rw [Metric.mem_closedBall]
        exact le_of_eq (Metric.mem_sphere.mp hu_sphere)
      have hball_v : v ∈ Metric.closedBall (AffineMap.lineMap A B t) ρ := by
        rw [Metric.mem_closedBall]
        exact le_of_eq (Metric.mem_sphere.mp hv_sphere)
      have hsub_uv_ball :
          segment ℝ u v ⊆ Metric.closedBall (AffineMap.lineMap A B t) ρ :=
        (convex_closedBall (AffineMap.lineMap A B t) ρ).segment_subset hball_u hball_v
      have hsub_uv_seg : segment ℝ u v ⊆ segment ℝ A B :=
        (convex_segment A B).segment_subset hu_seg hv_seg
      have hinter :
          Metric.closedBall (AffineMap.lineMap A B t) ρ ∩ segment ℝ A B =
            segment ℝ u v := by
        apply Set.Subset.antisymm
        · rintro y ⟨hyball, hyseg⟩
          rw [segment_eq_image_lineMap] at hyseg
          rcases hyseg with ⟨s, hs, rfl⟩
          rw [segment_eq_image_lineMap]
          have hdist_le : dist s t ≤ ε := by
            rw [le_div_iff₀ hd_pos]
            have h := hyball
            rw [Metric.mem_closedBall, dist_lineMap_lineMap_local] at h
            simpa [ε, d, mul_comm] using h
          have habs : |s - t| ≤ ε := by
            simpa [Real.dist_eq] using hdist_le
          have hbounds := abs_sub_le_iff.mp habs
          have hs_lower : t - ε ≤ s := by linarith
          have hs_upper : s ≤ t + ε := by linarith
          let lam : ℝ := (s - (t - ε)) / (2 * ε)
          refine ⟨lam, ?_, ?_⟩
          · have hden_pos : 0 < 2 * ε := by positivity
            constructor
            · exact div_nonneg (sub_nonneg.mpr hs_lower) hden_pos.le
            · rw [div_le_iff₀ hden_pos]
              linarith
          · apply PiLp.ext
            intro k
            simp [lam, u, v, AffineMap.lineMap_apply_module]
            field_simp [hεpos.ne']
            ring
        · intro y hy
          exact ⟨hsub_uv_ball hy, hsub_uv_seg hy⟩
      exact ⟨u, v, hu_sphere, hv_sphere, hu_seg, hv_seg, hz_open_uv, hinter⟩
    have hdiameter :
        ∀ i,
          z ∈ openSegment ℝ (a i) (b i) →
            ∃ u v : EuclideanSpace ℝ (Fin 2),
              u ∈ Metric.sphere z R ∧
                v ∈ Metric.sphere z R ∧
                  u ∈ segment ℝ (a i) (b i) ∧
                    v ∈ segment ℝ (a i) (b i) ∧
                      z ∈ openSegment ℝ u v ∧
                        Metric.closedBall z R ∩
                            segment ℝ (a i) (b i) =
                          segment ℝ u v := by
      intro i hzi
      exact segment_diameter (hendpoint_ne i) hzi hR_pos
        (hR_lt_ρA.trans (hρA_lt i)) (hR_lt_ρB.trans (hρB_lt i))
    exact ⟨R, hR_pos, hball_sub, hT_half, hnonincident, hpair_unique, hdiameter⟩
  let r : EuclideanSpace ℝ (Fin 2) → ℝ := fun z =>
    if hz : z ∈ T then Classical.choose (radius_exists z hz) else 1
  have r_spec :
      ∀ z : EuclideanSpace ℝ (Fin 2), ∀ hz : z ∈ T,
        0 < r z ∧
          Metric.closedBall z (r z) ⊆
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
            (∀ ⦃w : EuclideanSpace ℝ (Fin 2)⦄,
              w ∈ T → z ≠ w → r z < dist z w / 2) ∧
              (∀ i,
                z ∉ segment ℝ (a i) (b i) →
                  Disjoint (Metric.closedBall z (r z)) (segment ℝ (a i) (b i))) ∧
                (∀ ⦃y : EuclideanSpace ℝ (Fin 2)⦄,
                  y ∈ Metric.closedBall z (r z) →
                    (∃ i j : ι,
                      i ≠ j ∧
                        y ∈ segment ℝ (a i) (b i) ∧
                          y ∈ segment ℝ (a j) (b j)) →
                      y = z) ∧
                  (∀ i,
                    z ∈ openSegment ℝ (a i) (b i) →
                      ∃ u v : EuclideanSpace ℝ (Fin 2),
                        u ∈ Metric.sphere z (r z) ∧
                          v ∈ Metric.sphere z (r z) ∧
                            u ∈ segment ℝ (a i) (b i) ∧
                              v ∈ segment ℝ (a i) (b i) ∧
                                z ∈ openSegment ℝ u v ∧
                                  Metric.closedBall z (r z) ∩
                                      segment ℝ (a i) (b i) =
                                    segment ℝ u v) := by
    intro z hz
    dsimp [r]
    simpa [hz] using Classical.choose_spec (radius_exists z hz)
  refine ⟨T, r, ?_⟩
  constructor
  · intro z
    exact hT_mem z
  constructor
  · intro z hz
    exact (r_spec z hz).1
  constructor
  · intro z hz
    exact (r_spec z hz).2.1
  constructor
  · intro z w hz hw hzw
    rw [Set.disjoint_left]
    intro y hyz hyw
    have hz_spec := r_spec z hz
    have hw_spec := r_spec w hw
    have hz_lt : r z < dist z w / 2 := hz_spec.2.2.1 hw hzw
    have hw_lt : r w < dist w z / 2 := hw_spec.2.2.1 hz hzw.symm
    have hyz_dist : dist z y ≤ r z := by
      simpa [Metric.mem_closedBall, dist_comm] using hyz
    have hyw_dist : dist y w ≤ r w := by
      simpa [Metric.mem_closedBall] using hyw
    have htri : dist z w ≤ dist z y + dist y w := dist_triangle z y w
    have hsum_lt : dist z y + dist y w < dist z w := by
      calc
        dist z y + dist y w ≤ r z + r w := add_le_add hyz_dist hyw_dist
        _ < dist z w / 2 + dist w z / 2 := add_lt_add hz_lt hw_lt
        _ = dist z w := by
          rw [dist_comm w z]
          ring
    exact (not_lt_of_ge htri) hsum_lt
  constructor
  · intro z hz i hzi
    exact (r_spec z hz).2.2.2.1 i hzi
  constructor
  · intro z y hz hy htwo
    exact (r_spec z hz).2.2.2.2.1 hy htwo
  · intro z hz i hzi
    exact (r_spec z hz).2.2.2.2.2 i hzi
