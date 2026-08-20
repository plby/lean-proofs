import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementCircleOutsideNearSupportingCoordinate]
lemma PolygonalReplacementCircleOutsideNearSupportingCoordinate
    {R k : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ},
        R * x + (x ^ 2 + y ^ 2) = 2 * k * y →
          0 ≤ 2 * R * x + (x ^ 2 + y ^ 2) →
            x ^ 2 + y ^ 2 < δ ^ 2 →
              0 ≤ x := by
-- BODY
  classical
  have coordinate_bound :
      ∀ {x y : ℝ},
        R * x + (x ^ 2 + y ^ 2) = 2 * k * y →
          0 ≤ 2 * R * x + (x ^ 2 + y ^ 2) →
            x ^ 2 + y ^ 2 <
              4 * R ^ 2 * k ^ 2 / (R ^ 2 + k ^ 2) →
              0 ≤ x := by
    intro x y howner hout hnear
    by_cases hk : k = 0
    · subst k
      nlinarith
    · by_contra hxnot
      have hx : x < 0 := lt_of_not_ge hxnot
      let N : ℝ := x ^ 2 + y ^ 2
      have hNpos : 0 < N := by
        dsimp [N]
        nlinarith [sq_nonneg x, sq_nonneg y, hx]
      have hA_nonneg : 0 ≤ -R * x := by nlinarith
      have hA_le : 2 * (-R * x) ≤ N := by
        dsimp [N]
        nlinarith
      have hA_sq_le : (-R * x) ^ 2 ≤ N ^ 2 / 4 := by
        have hN_nonneg : 0 ≤ N := le_of_lt hNpos
        nlinarith
      have hB_eq : 2 * k * y = N - (-R * x) := by
        dsimp [N] at howner ⊢
        linarith
      have hB_nonneg : 0 ≤ N - (-R * x) := by
        nlinarith
      have hB_le : N - (-R * x) ≤ N := by
        nlinarith
      have hB_sq_le : (2 * k * y) ^ 2 ≤ N ^ 2 := by
        rw [hB_eq]
        nlinarith
      have hN_eq :
          N = (-R * x) ^ 2 / R ^ 2 + (2 * k * y) ^ 2 / (4 * k ^ 2) := by
        dsimp [N]
        field_simp [ne_of_gt hR, hk]
        ring_nf
      have hmain :
          4 * R ^ 2 * k ^ 2 ≤ N * (R ^ 2 + k ^ 2) := by
        have hR2pos : 0 < R ^ 2 := sq_pos_of_pos hR
        have hk2pos : 0 < k ^ 2 := sq_pos_of_ne_zero hk
        nlinarith [hN_eq, hA_sq_le, hB_sq_le, hR2pos, hk2pos]
      have hden_pos : 0 < R ^ 2 + k ^ 2 := by positivity
      have hnear' : N * (R ^ 2 + k ^ 2) < 4 * R ^ 2 * k ^ 2 := by
        have := mul_lt_mul_of_pos_right hnear hden_pos
        field_simp [hden_pos.ne'] at this
        simpa [N, mul_assoc, mul_left_comm, mul_comm] using this
      nlinarith
  by_cases hk : k = 0
  · refine ⟨R, hR, ?_⟩
    intro x y howner hout _hnear
    subst k
    nlinarith
  · let δ : ℝ := min R |k|
    have hδpos : 0 < δ := lt_min hR (abs_pos.mpr hk)
    refine ⟨δ, hδpos, ?_⟩
    intro x y howner hout hnear
    have hthreshold :
        δ ^ 2 ≤ 4 * R ^ 2 * k ^ 2 / (R ^ 2 + k ^ 2) := by
      have hR2pos : 0 < R ^ 2 := sq_pos_of_pos hR
      have hk2pos : 0 < k ^ 2 := sq_pos_of_ne_zero hk
      have hdenpos : 0 < R ^ 2 + k ^ 2 := by positivity
      have hδ_le_R : δ ≤ R := min_le_left _ _
      have hδ_le_abs : δ ≤ |k| := min_le_right _ _
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδpos
      have hδ2_le_R2 : δ ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ hδ_nonneg hδ_le_R 2
      have hδ2_le_k2 : δ ^ 2 ≤ k ^ 2 := by
        have := pow_le_pow_left₀ hδ_nonneg hδ_le_abs 2
        simpa [sq_abs] using this
      have hmul' :
          δ ^ 2 * (R ^ 2 + k ^ 2) ≤ 4 * R ^ 2 * k ^ 2 := by
        nlinarith [mul_pos hR2pos hk2pos]
      exact (le_div_iff₀ hdenpos).2 hmul'
    exact coordinate_bound howner hout (lt_of_lt_of_le hnear hthreshold)
