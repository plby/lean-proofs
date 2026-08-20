import ErdosProblems.Erdos733.ST.StraightSegmentPolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitChordMultiplePointControl]
lemma EndpointUnitChordMultiplePointControl {ι : Type*} [Fintype ι]
    (a b : ι → EuclideanSpace ℝ (Fin 2))
    (ha : ∀ i, dist (a i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hb : ∀ i, dist (b i) (0 : EuclideanSpace ℝ (Fin 2)) = 1)
    (hdistinct : Function.Injective (fun x : ι ⊕ ι => Sum.elim a b x)) :
    let triplePoints : Set (EuclideanSpace ℝ (Fin 2)) :=
      {p | p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        ∃ i j k : ι,
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            p ∈ openSegment ℝ (a i) (b i) ∧
              p ∈ openSegment ℝ (a j) (b j) ∧
                p ∈ openSegment ℝ (a k) (b k)}
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
-- BODY
  let triplePoints : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      ∃ i j k : ι,
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
          p ∈ openSegment ℝ (a i) (b i) ∧
            p ∈ openSegment ℝ (a j) (b j) ∧
              p ∈ openSegment ℝ (a k) (b k)}
  change triplePoints.Finite ∧
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
                    ¬ ∃ t : ℝ, b j - a j = t • (b i - a i))
  have endpoint_ne : ∀ i, a i ≠ b i := by
    intro i h
    have hsum : (Sum.inl i : ι ⊕ ι) = Sum.inr i :=
      hdistinct (by simpa [Sum.elim] using h)
    cases hsum
  have a_ne_a : ∀ ⦃i j : ι⦄, i ≠ j → a i ≠ a j := by
    intro i j hij h
    have hsum : (Sum.inl i : ι ⊕ ι) = Sum.inl j :=
      hdistinct (by simpa [Sum.elim] using h)
    exact hij (Sum.inl.inj hsum)
  have a_ne_b : ∀ i j : ι, a i ≠ b j := by
    intro i j h
    have hsum : (Sum.inl i : ι ⊕ ι) = Sum.inr j :=
      hdistinct (by simpa [Sum.elim] using h)
    cases hsum
  have b_ne_a : ∀ ⦃i j : ι⦄, i ≠ j → b i ≠ a j := by
    intro i j _ h
    exact a_ne_b j i h.symm
  have circle_sq_origin :
      ∀ {z : EuclideanSpace ℝ (Fin 2)},
        dist z (0 : EuclideanSpace ℝ (Fin 2)) = 1 →
          z 0 ^ 2 + z 1 ^ 2 = 1 := by
    intro z hz
    have hsq : dist z (0 : EuclideanSpace ℝ (Fin 2)) ^ 2 = (1 : ℝ) ^ 2 := by
      rw [hz]
    rw [dist_eq_norm] at hsq
    change ‖z - 0‖ ^ 2 = (1 : ℝ) ^ 2 at hsq
    have hnorm := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (z - 0)
    rw [hnorm] at hsq
    norm_num at hsq
    simpa [EuclideanSpace, Fin.sum_univ_two, sub_eq_add_neg, sq] using hsq
  have quadratic_no_three :
      ∀ {A B C t₁ t₂ t₃ : ℝ}, A ≠ 0 →
        A * t₁ ^ 2 + B * t₁ + C = 0 →
        A * t₂ ^ 2 + B * t₂ + C = 0 →
        A * t₃ ^ 2 + B * t₃ + C = 0 →
        t₁ ≠ t₂ → t₁ ≠ t₃ → t₂ ≠ t₃ → False := by
    intro A B C t₁ t₂ t₃ hA h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
    have hf₁₂ : (t₁ - t₂) * (A * (t₁ + t₂) + B) = 0 := by
      nlinarith
    have hlin₁₂ : A * (t₁ + t₂) + B = 0 :=
      (mul_eq_zero.mp hf₁₂).resolve_left (sub_ne_zero.mpr h₁₂)
    have hf₁₃ : (t₁ - t₃) * (A * (t₁ + t₃) + B) = 0 := by
      nlinarith
    have hlin₁₃ : A * (t₁ + t₃) + B = 0 :=
      (mul_eq_zero.mp hf₁₃).resolve_left (sub_ne_zero.mpr h₁₃)
    have hzero : A * (t₂ - t₃) = 0 := by
      nlinarith
    exact h₂₃ (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hA))
  have unit_line_no_three :
      ∀ {x y u v w : EuclideanSpace ℝ (Fin 2)}, x ≠ y →
        u ∈ line[ℝ, x, y] → v ∈ line[ℝ, x, y] → w ∈ line[ℝ, x, y] →
        dist u (0 : EuclideanSpace ℝ (Fin 2)) = 1 →
        dist v (0 : EuclideanSpace ℝ (Fin 2)) = 1 →
        dist w (0 : EuclideanSpace ℝ (Fin 2)) = 1 →
        u ≠ v → u ≠ w → v ≠ w → False := by
    intro x y u v w hxy hu hv hw hdu hdv hdw huv huw hvw
    let d0 : ℝ := y 0 - x 0
    let d1 : ℝ := y 1 - x 1
    let A : ℝ := d0 ^ 2 + d1 ^ 2
    let B : ℝ := 2 * (x 0 * d0 + x 1 * d1)
    let C : ℝ := x 0 ^ 2 + x 1 ^ 2 - 1
    have hA : A ≠ 0 := by
      have hd : d0 ≠ 0 ∨ d1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hxy
        apply PiLp.ext
        intro i
        fin_cases i
        · dsimp [d0] at h ⊢
          linarith
        · dsimp [d1] at h ⊢
          linarith
      rcases hd with hd | hd
      · have hpos : 0 < A := by
          dsimp [A]
          exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd) (sq_nonneg d1)
        exact ne_of_gt hpos
      · have hpos : 0 < A := by
          dsimp [A]
          exact add_pos_of_nonneg_of_pos (sq_nonneg d0) (sq_pos_of_ne_zero hd)
        exact ne_of_gt hpos
    have root_of_line :
        ∀ {z : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
          z = AffineMap.lineMap x y t →
          dist z (0 : EuclideanSpace ℝ (Fin 2)) = 1 →
            A * t ^ 2 + B * t + C = 0 := by
      intro z t hzline hdist
      have hsq := circle_sq_origin hdist
      subst z
      dsimp [A, B, C, d0, d1]
      simp [AffineMap.lineMap_apply_module] at hsq ⊢
      ring_nf at hsq ⊢
      nlinarith
    rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := u)
        (p₁ := x) (p₂ := y)).mp hu with ⟨tu, htu⟩
    rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := v)
        (p₁ := x) (p₂ := y)).mp hv with ⟨tv, htv⟩
    rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := w)
        (p₁ := x) (p₂ := y)).mp hw with ⟨tw, htw⟩
    have htu_root := root_of_line htu.symm hdu
    have htv_root := root_of_line htv.symm hdv
    have htw_root := root_of_line htw.symm hdw
    have htu_ne_tv : tu ≠ tv := by
      intro ht
      apply huv
      rw [← htu, ← htv, ht]
    have htu_ne_tw : tu ≠ tw := by
      intro ht
      apply huw
      rw [← htu, ← htw, ht]
    have htv_ne_tw : tv ≠ tw := by
      intro ht
      apply hvw
      rw [← htv, ← htw, ht]
    exact quadratic_no_three hA htu_root htv_root htw_root htu_ne_tv htu_ne_tw htv_ne_tw
  have segment_subset_line :
      ∀ x y : EuclideanSpace ℝ (Fin 2), segment ℝ x y ⊆ line[ℝ, x, y] := by
    intro x y z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, _ht, hzt⟩
    rw [← hzt]
    exact AffineMap.lineMap_mem_affineSpan_pair t x y
  have openSegment_subset_line :
      ∀ x y : EuclideanSpace ℝ (Fin 2), openSegment ℝ x y ⊆ line[ℝ, x, y] := by
    intro x y z hz
    exact segment_subset_line x y (openSegment_subset_segment ℝ x y hz)
  have no_shared_segment :
      ∀ ⦃i j : ι⦄,
        i ≠ j →
          ¬ ∃ p q : EuclideanSpace ℝ (Fin 2),
            p ≠ q ∧
              segment ℝ p q ⊆
                segment ℝ (a i) (b i) ∩ segment ℝ (a j) (b j) := by
    intro i j hij hbad
    rcases hbad with ⟨p, q, hpq, hsub⟩
    have hp_i_seg : p ∈ segment ℝ (a i) (b i) := (hsub (left_mem_segment ℝ p q)).1
    have hq_i_seg : q ∈ segment ℝ (a i) (b i) := (hsub (right_mem_segment ℝ p q)).1
    have hp_j_seg : p ∈ segment ℝ (a j) (b j) := (hsub (left_mem_segment ℝ p q)).2
    have hq_j_seg : q ∈ segment ℝ (a j) (b j) := (hsub (right_mem_segment ℝ p q)).2
    have hp_i_line : p ∈ line[ℝ, a i, b i] := segment_subset_line (a i) (b i) hp_i_seg
    have hq_i_line : q ∈ line[ℝ, a i, b i] := segment_subset_line (a i) (b i) hq_i_seg
    have hp_j_line : p ∈ line[ℝ, a j, b j] := segment_subset_line (a j) (b j) hp_j_seg
    have hq_j_line : q ∈ line[ℝ, a j, b j] := segment_subset_line (a j) (b j) hq_j_seg
    have hline_i : line[ℝ, p, q] = line[ℝ, a i, b i] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_i_line hq_i_line hpq
    have hline_j : line[ℝ, p, q] = line[ℝ, a j, b j] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hp_j_line hq_j_line hpq
    have hai_line : a i ∈ line[ℝ, p, q] := by
      rw [hline_i]
      exact left_mem_affineSpan_pair ℝ (a i) (b i)
    have hbi_line : b i ∈ line[ℝ, p, q] := by
      rw [hline_i]
      exact right_mem_affineSpan_pair ℝ (a i) (b i)
    have haj_line : a j ∈ line[ℝ, p, q] := by
      rw [hline_j]
      exact left_mem_affineSpan_pair ℝ (a j) (b j)
    exact unit_line_no_three hpq hai_line hbi_line haj_line (ha i) (hb i) (ha j)
      (endpoint_ne i) (a_ne_a hij) (b_ne_a hij)
  have open_inter_unique :
      ∀ ⦃i j : ι⦄ ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ openSegment ℝ (a i) (b i) →
            p ∈ openSegment ℝ (a j) (b j) →
              q ∈ openSegment ℝ (a i) (b i) →
                q ∈ openSegment ℝ (a j) (b j) →
                  p = q := by
    intro i j p q hij hp_i hp_j hq_i hq_j
    by_cases hpq : p = q
    · exact hpq
    · exfalso
      have hp_i_line : p ∈ line[ℝ, a i, b i] := openSegment_subset_line (a i) (b i) hp_i
      have hq_i_line : q ∈ line[ℝ, a i, b i] := openSegment_subset_line (a i) (b i) hq_i
      have hp_j_line : p ∈ line[ℝ, a j, b j] := openSegment_subset_line (a j) (b j) hp_j
      have hq_j_line : q ∈ line[ℝ, a j, b j] := openSegment_subset_line (a j) (b j) hq_j
      have hline_i : line[ℝ, p, q] = line[ℝ, a i, b i] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne hp_i_line hq_i_line hpq
      have hline_j : line[ℝ, p, q] = line[ℝ, a j, b j] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne hp_j_line hq_j_line hpq
      have hai_line : a i ∈ line[ℝ, p, q] := by
        rw [hline_i]
        exact left_mem_affineSpan_pair ℝ (a i) (b i)
      have hbi_line : b i ∈ line[ℝ, p, q] := by
        rw [hline_i]
        exact right_mem_affineSpan_pair ℝ (a i) (b i)
      have haj_line : a j ∈ line[ℝ, p, q] := by
        rw [hline_j]
        exact left_mem_affineSpan_pair ℝ (a j) (b j)
      exact unit_line_no_three hpq hai_line hbi_line haj_line (ha i) (hb i) (ha j)
        (endpoint_ne i) (a_ne_a hij) (b_ne_a hij)
  have nonscalar_direction :
      ∀ ⦃i j : ι⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        i ≠ j →
          p ∈ openSegment ℝ (a i) (b i) →
            p ∈ openSegment ℝ (a j) (b j) →
              ¬ ∃ t : ℝ, b j - a j = t • (b i - a i) := by
    intro i j p hij hp_i hp_j hparallel
    rcases hparallel with ⟨t, hdir⟩
    have hp_i_line : p ∈ line[ℝ, a i, b i] := openSegment_subset_line (a i) (b i) hp_i
    have hp_j_line : p ∈ line[ℝ, a j, b j] := openSegment_subset_line (a j) (b j) hp_j
    rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := p)
        (p₁ := a i) (p₂ := b i)).mp hp_i_line with ⟨r, hr⟩
    rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := p)
        (p₁ := a j) (p₂ := b j)).mp hp_j_line with ⟨s, hs⟩
    have haj_line : a j ∈ line[ℝ, a i, b i] := by
      refine (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := a j)
        (p₁ := a i) (p₂ := b i)).mpr ?_
      refine ⟨r - s * t, ?_⟩
      apply PiLp.ext
      intro k
      have hrk := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z k) hr
      have hsk := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z k) hs
      have hdirk := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z k) hdir
      simp [AffineMap.lineMap_apply_module] at hrk hsk ⊢
      simp at hdirk
      have hpcoord :
          (1 - r) * (a i) k + r * (b i) k =
            (1 - s) * (a j) k + s * (b j) k := by
        rw [hrk, hsk]
      calc
        (1 - (r - s * t)) * (a i) k + (r - s * t) * (b i) k =
            ((1 - r) * (a i) k + r * (b i) k) -
              s * (t * ((b i) k - (a i) k)) := by
          ring
        _ = ((1 - r) * (a i) k + r * (b i) k) -
              s * ((b j) k - (a j) k) := by
          rw [← hdirk]
        _ = ((1 - s) * (a j) k + s * (b j) k) -
              s * ((b j) k - (a j) k) := by
          rw [hpcoord]
        _ = (a j) k := by
          ring
    exact unit_line_no_three (endpoint_ne i)
      (left_mem_affineSpan_pair ℝ (a i) (b i))
      (right_mem_affineSpan_pair ℝ (a i) (b i))
      haj_line (ha i) (hb i) (ha j)
      (endpoint_ne i) (a_ne_a hij) (b_ne_a hij)
  have pair_inter_finite :
      ∀ ⦃i j : ι⦄, i ≠ j →
        (openSegment ℝ (a i) (b i) ∩ openSegment ℝ (a j) (b j) :
          Set (EuclideanSpace ℝ (Fin 2))).Finite := by
    intro i j hij
    have hsubsingleton :
        (openSegment ℝ (a i) (b i) ∩ openSegment ℝ (a j) (b j) :
          Set (EuclideanSpace ℝ (Fin 2))).Subsingleton := by
      intro p hp q hq
      exact open_inter_unique hij hp.1 hp.2 hq.1 hq.2
    exact hsubsingleton.finite
  let tripleFor : ι × ι × ι → Set (EuclideanSpace ℝ (Fin 2)) := fun ijk =>
    {p | p ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2 ∧
        p ∈ openSegment ℝ (a ijk.1) (b ijk.1) ∧
          p ∈ openSegment ℝ (a ijk.2.1) (b ijk.2.1) ∧
            p ∈ openSegment ℝ (a ijk.2.2) (b ijk.2.2)}
  have tripleFor_finite : ∀ ijk, (tripleFor ijk).Finite := by
    intro ijk
    by_cases hij : ijk.1 = ijk.2.1
    · have hempty : tripleFor ijk = ∅ := by
        ext p
        simp [tripleFor, hij]
      rw [hempty]
      exact Set.finite_empty
    · have hsub :
          tripleFor ijk ⊆
            (openSegment ℝ (a ijk.1) (b ijk.1) ∩
              openSegment ℝ (a ijk.2.1) (b ijk.2.1) :
                Set (EuclideanSpace ℝ (Fin 2))) := by
        rintro p ⟨_, _, _, _, hpi, hpj, _⟩
        exact ⟨hpi, hpj⟩
      exact (pair_inter_finite hij).subset hsub
  have triple_union_finite : (⋃ ijk, tripleFor ijk).Finite :=
    Set.finite_iUnion tripleFor_finite
  have triple_subset_union : triplePoints ⊆ ⋃ ijk, tripleFor ijk := by
    intro p hp
    rcases hp with ⟨hpball, i, j, k, hij, hik, hjk, hpi, hpj, hpk⟩
    refine Set.mem_iUnion.mpr ⟨(i, j, k), ?_⟩
    exact ⟨hpball, hij, hik, hjk, hpi, hpj, hpk⟩
  have triple_finite : triplePoints.Finite :=
    triple_union_finite.subset triple_subset_union
  exact ⟨triple_finite, endpoint_ne, no_shared_segment, open_inter_unique, nonscalar_direction⟩
