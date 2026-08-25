import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic
import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma AffineInterpolationInteriorZeroParity
    (u v : ℝ) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    Odd
        (Set.ncard
          {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ (1 - t) * u + t * v = 0}) ↔
      decide (0 < u) ≠ decide (0 < v) := by
  by_cases huv_eq : u = v
  · subst v
    have hset :
        {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ (1 - t) * u + t * u = 0} = ∅ := by
      ext t
      constructor
      · rintro ⟨-, hzero⟩
        have : u = 0 := by linarith
        exact (hu0 this).elim
      · intro h
        exact False.elim h
    rw [hset]
    simp
  · have huv : u ≠ v := huv_eq
    have hzero_iff :
        ∀ t : ℝ, (1 - t) * u + t * v = 0 ↔ t = u / (u - v) := by
      intro t
      constructor
      · intro h
        have hden : u - v ≠ 0 := sub_ne_zero.mpr huv
        field_simp [hden] at h ⊢
        ring_nf at h ⊢
        linarith
      · intro ht
        subst ht
        have hden : u - v ≠ 0 := sub_ne_zero.mpr huv
        field_simp [hden]
        ring
    have hroot_mem :
        u / (u - v) ∈ Set.Ioo (0 : ℝ) 1 ↔
          (u < 0 ∧ 0 < v) ∨ (0 < u ∧ v < 0) := by
      constructor
      · intro h
        have hden : u - v ≠ 0 := sub_ne_zero.mpr huv
        by_cases hdenpos : 0 < u - v
        · have hu_pos : 0 < u := (div_pos_iff_of_pos_right hdenpos).1 h.1
          have hlt : u < u - v := (div_lt_one hdenpos).1 h.2
          right
          exact ⟨hu_pos, by linarith⟩
        · have hdenneg : u - v < 0 := lt_of_le_of_ne (le_of_not_gt hdenpos) hden
          have hu_neg : u < 0 := by
            by_contra hnot
            have hu_nonneg : 0 ≤ u := le_of_not_gt hnot
            have hquot_nonpos : u / (u - v) ≤ 0 :=
              div_nonpos_of_nonneg_of_nonpos hu_nonneg hdenneg.le
            exact (not_lt_of_ge hquot_nonpos) h.1
          have hlt : u - v < u := by
            have hmul := (div_lt_iff_of_neg hdenneg).1 h.2
            linarith
          left
          exact ⟨hu_neg, by linarith⟩
      · rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
        · have hdenneg : u - v < 0 := by linarith
          constructor
          · exact div_pos_of_neg_of_neg hu hdenneg
          · exact (div_lt_iff_of_neg hdenneg).2 (by linarith)
        · have hdenpos : 0 < u - v := by linarith
          constructor
          · exact (div_pos_iff_of_pos_right hdenpos).2 hu
          · exact (div_lt_one hdenpos).2 (by linarith)
    have hset :
        {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ (1 - t) * u + t * v = 0} =
          if (u < 0 ∧ 0 < v) ∨ (0 < u ∧ v < 0) then
            {u / (u - v)}
          else
            ∅ := by
      ext t
      by_cases hsign : (u < 0 ∧ 0 < v) ∨ (0 < u ∧ v < 0)
      · simp only [hsign, if_true, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · exact fun ht => (hzero_iff t).1 ht.2
        · intro ht
          exact ⟨by simpa [ht] using hroot_mem.2 hsign, (hzero_iff t).2 ht⟩
      · simp only [hsign, if_false, Set.mem_setOf_eq, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨htI, htzero⟩
          exact hsign (hroot_mem.1 (by simpa [(hzero_iff t).1 htzero] using htI))
        · intro hfalse
          exact False.elim hfalse
    have hncard :
        Set.ncard
            {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ (1 - t) * u + t * v = 0} =
          if (u < 0 ∧ 0 < v) ∨ (0 < u ∧ v < 0) then 1 else 0 := by
      rw [hset]
      split_ifs <;> simp
    rw [hncard]
    by_cases hsign : (u < 0 ∧ 0 < v) ∨ (0 < u ∧ v < 0)
    · rw [if_pos hsign]
      rcases hsign with ⟨hu_neg, hv_pos⟩ | ⟨hu_pos, hv_neg⟩
      · have hu_not : ¬ 0 < u := by linarith
        simp [hu_not, hv_pos]
      · have hv_not : ¬ 0 < v := by linarith
        simp [hu_pos, hv_not]
    · rw [if_neg hsign]
      by_cases hu_pos : 0 < u
      · by_cases hv_pos : 0 < v
        · simp [hu_pos, hv_pos]
        · have hv_neg : v < 0 := lt_of_le_of_ne (le_of_not_gt hv_pos) hv0
          exact False.elim (hsign (Or.inr ⟨hu_pos, hv_neg⟩))
      · have hu_neg : u < 0 := lt_of_le_of_ne (le_of_not_gt hu_pos) hu0
        by_cases hv_pos : 0 < v
        · exact False.elim (hsign (Or.inl ⟨hu_neg, hv_pos⟩))
        · simp [hu_pos, hv_pos]
