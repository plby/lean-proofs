import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma PlanarRot90ScalarSameSideConesDisjoint (A B : ℝ)
    (hnot : ¬ (0 < A ∧ B = 0)) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
        |b| < κ * a → |r| < κ * c →
        ¬ (a = c * A - r * B ∧ b = c * B + r * A) := by
  by_cases hB : B = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro a c b r ha hc hbr hb hr hEq
    have hA_nonpos : A ≤ 0 := by
      by_contra hApos'
      exact hnot ⟨lt_of_not_ge hApos', hB⟩
    have hb_eq : b = r * A := by
      simpa [hB] using hEq.2
    have hbr_nonpos : b * r ≤ 0 := by
      rw [hb_eq]
      have hr_sq_nonneg : 0 ≤ r * r := mul_self_nonneg r
      nlinarith
    nlinarith
  · let κ : ℝ := min (1 / 2) (|B| / (8 * (|A| + |B| + 1)))
    have hκpos : 0 < κ := by
      have hBpos : 0 < |B| := abs_pos.mpr hB
      have hden : 0 < 8 * (|A| + |B| + 1) := by positivity
      exact lt_min (by norm_num) (div_pos hBpos hden)
    refine ⟨κ, hκpos, ?_⟩
    intro a c b r ha hc hbr hb_lt hr_lt hEq
    have hκ_le_half : κ ≤ 1 / 2 := by
      dsimp [κ]
      exact min_le_left _ _
    have hκ_le_big : κ ≤ |B| / (8 * (|A| + |B| + 1)) := by
      dsimp [κ]
      exact min_le_right _ _
    have hBpos : 0 < |B| := abs_pos.mpr hB
    have hc_absB_lt : c * |B| < κ * a + κ * c * |A| := by
      have hb_sub : c * B = b - r * A := by
        linarith [hEq.2]
      have htri : |c * B| ≤ |b| + |r * A| := by
        calc
          |c * B| = |b - r * A| := by rw [hb_sub]
          _ ≤ |b| + |r * A| := by
            simpa [sub_eq_add_neg, abs_neg] using abs_add_le b (-(r * A))
      have hrA_le : |r * A| ≤ κ * c * |A| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (le_of_lt hr_lt) (abs_nonneg A)
      calc
        c * |B| = |c * B| := by rw [abs_mul, abs_of_pos hc]
        _ ≤ |b| + |r * A| := htri
        _ < κ * a + κ * c * |A| := add_lt_add_of_lt_of_le hb_lt hrA_le
    have ha_le : a ≤ c * |A| + |r| * |B| := by
      have ha_eq : a = c * A - r * B := hEq.1
      calc
        a = |a| := by rw [abs_of_pos ha]
        _ = |c * A - r * B| := by rw [ha_eq]
        _ ≤ |c * A| + |r * B| := by
          simpa [sub_eq_add_neg, abs_neg] using abs_add_le (c * A) (-(r * B))
        _ = c * |A| + |r| * |B| := by
          rw [abs_mul, abs_mul, abs_of_pos hc]
    have ha_lt : a < c * |A| + κ * c * |B| := by
      calc
        a ≤ c * |A| + |r| * |B| := ha_le
        _ < c * |A| + (κ * c) * |B| := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_lt_add_left (mul_lt_mul_of_pos_right hr_lt hBpos) (c * |A|)
        _ = c * |A| + κ * c * |B| := by ring
    have hB_lt : |B| < κ * (2 * |A| + κ * |B|) := by
      have hmain : c * |B| < κ * (c * |A| + κ * c * |B|) + κ * c * |A| := by
        calc
          c * |B| < κ * a + κ * c * |A| := hc_absB_lt
          _ < κ * (c * |A| + κ * c * |B|) + κ * c * |A| := by
            nlinarith [mul_lt_mul_of_pos_left ha_lt hκpos]
      have hdiv : |B| < κ * (|A| + κ * |B|) + κ * |A| := by
        ring_nf at hmain ⊢
        nlinarith [hmain, hc]
      nlinarith
    have hupper : κ * (2 * |A| + κ * |B|) < |B| := by
      have hterm : κ * (2 * |A| + κ * |B|) ≤ |B| / 4 := by
        have hinside_le : 2 * |A| + κ * |B| ≤ 2 * (|A| + |B| + 1) := by
          have hκB_le : κ * |B| ≤ |B| := by
            have hκ_le_one : κ ≤ 1 := by nlinarith [hκ_le_half]
            simpa using mul_le_mul_of_nonneg_right hκ_le_one (abs_nonneg B)
          nlinarith [hκB_le, abs_nonneg B]
        have hmul :
            κ * (2 * |A| + κ * |B|) ≤
              (|B| / (8 * (|A| + |B| + 1))) *
                (2 * (|A| + |B| + 1)) := by
          have hleft :
              κ * (2 * |A| + κ * |B|) ≤
                κ * (2 * (|A| + |B| + 1)) :=
            mul_le_mul_of_nonneg_left hinside_le (le_of_lt hκpos)
          have hright :
              κ * (2 * (|A| + |B| + 1)) ≤
                (|B| / (8 * (|A| + |B| + 1))) *
                  (2 * (|A| + |B| + 1)) :=
            mul_le_mul_of_nonneg_right hκ_le_big (by positivity)
          exact le_trans hleft hright
        have hscaled :
            (|B| / (8 * (|A| + |B| + 1))) *
                (2 * (|A| + |B| + 1)) = |B| / 4 := by
          have hpos : |A| + |B| + 1 ≠ 0 := by positivity
          field_simp [hpos]
          ring
        simpa [hscaled] using hmul
      calc
        κ * (2 * |A| + κ * |B|) ≤ |B| / 4 := hterm
        _ < |B| := by nlinarith
    exact not_lt_of_ge (le_of_lt hupper) hB_lt
