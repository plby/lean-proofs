import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90ClockwiseWedgeSignCriterion]
lemma PlanarRot90ClockwiseWedgeSignCriterion (A N : ℝ)
    (hA0 : 0 < A) (hA2 : A < 2 * Real.pi)
    (hN0 : 0 < N) (hN2 : N < 2 * Real.pi) :
    (if 0 < Real.sin N then
      A < Real.pi ∧ 0 < Real.sin (N - A)
     else if Real.sin N < 0 then
      A < Real.pi ∨ 0 < Real.sin (N - A)
     else
      A < Real.pi) ↔ A < N := by
-- BODY
  have hsin_pos_iff {x : ℝ} (hx0 : 0 < x) (hx2 : x < 2 * Real.pi) :
      0 < Real.sin x ↔ x < Real.pi := by
    constructor
    · intro hsin
      by_contra hnot
      have hpi_le : Real.pi ≤ x := le_of_not_gt hnot
      rcases eq_or_lt_of_le hpi_le with hpi | hpi_lt
      · rw [← hpi, Real.sin_pi] at hsin
        linarith
      · have hxsub_neg : x - 2 * Real.pi < 0 := by linarith
        have hxsub_gt : -Real.pi < x - 2 * Real.pi := by linarith
        have hneg : Real.sin (x - 2 * Real.pi) < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt hxsub_neg hxsub_gt
        rw [Real.sin_sub_two_pi] at hneg
        linarith
    · intro hxpi
      exact Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hsin_neg_iff {x : ℝ} (hx0 : 0 < x) (hx2 : x < 2 * Real.pi) :
      Real.sin x < 0 ↔ Real.pi < x := by
    constructor
    · intro hsin
      by_contra hnot
      have hxpi : x ≤ Real.pi := le_of_not_gt hnot
      have hnonneg : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hx0) hxpi
      linarith
    · intro hpi_lt
      have hxsub_neg : x - 2 * Real.pi < 0 := by linarith
      have hxsub_gt : -Real.pi < x - 2 * Real.pi := by linarith
      have hneg : Real.sin (x - 2 * Real.pi) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt hxsub_neg hxsub_gt
      rwa [Real.sin_sub_two_pi] at hneg
  have hsin_pos_iff_neg_pi_pi {x : ℝ} (hxneg : -Real.pi < x) (hxpi : x < Real.pi) :
      0 < Real.sin x ↔ 0 < x := by
    constructor
    · intro hsin
      by_contra hnot
      have hxle : x ≤ 0 := le_of_not_gt hnot
      rcases eq_or_lt_of_le hxle with hx0eq | hxlt0
      · rw [hx0eq, Real.sin_zero] at hsin
        linarith
      · have hneg : Real.sin x < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hxlt0 hxneg
        linarith
    · intro hx0
      exact Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  by_cases hNpi_lt : N < Real.pi
  · have hsinN : 0 < Real.sin N := (hsin_pos_iff hN0 hN2).2 hNpi_lt
    simp [hsinN]
    constructor
    · rintro ⟨_hApi, hsin⟩
      have hdiff_negpi : -Real.pi < N - A := by linarith
      have hdiff_pi : N - A < Real.pi := by linarith
      have hdiff_pos : 0 < N - A :=
        (hsin_pos_iff_neg_pi_pi hdiff_negpi hdiff_pi).1 hsin
      linarith
    · intro hAN
      constructor
      · linarith
      · have hdiff_pos : 0 < N - A := by linarith
        have hdiff_pi : N - A < Real.pi := by linarith
        exact Real.sin_pos_of_pos_of_lt_pi hdiff_pos hdiff_pi
  · have hNpi_le : Real.pi ≤ N := le_of_not_gt hNpi_lt
    rcases eq_or_lt_of_le hNpi_le with hNpi_eq | hpiN
    · have hsinN_not_pos : ¬ 0 < Real.sin N := by
        rw [← hNpi_eq, Real.sin_pi]
        linarith
      have hsinN_not_neg : ¬ Real.sin N < 0 := by
        rw [← hNpi_eq, Real.sin_pi]
        linarith
      simp [hsinN_not_pos, hsinN_not_neg, hNpi_eq]
    · have hsinN_neg : Real.sin N < 0 := (hsin_neg_iff hN0 hN2).2 hpiN
      have hsinN_not_pos : ¬ 0 < Real.sin N := by linarith
      simp [hsinN_not_pos, hsinN_neg]
      constructor
      · intro h
        rcases h with hApi | hsin
        · linarith
        · have hdiff_negpi : -Real.pi < N - A := by linarith
          by_cases hApi : A < Real.pi
          · linarith
          · have hApi_le : Real.pi ≤ A := le_of_not_gt hApi
            have hdiff_pi : N - A < Real.pi := by linarith
            have hdiff_pos : 0 < N - A :=
              (hsin_pos_iff_neg_pi_pi hdiff_negpi hdiff_pi).1 hsin
            linarith
      · intro hAN
        by_cases hApi : A < Real.pi
        · exact Or.inl hApi
        · right
          have hApi_le : Real.pi ≤ A := le_of_not_gt hApi
          have hdiff_pos : 0 < N - A := by linarith
          have hdiff_pi : N - A < Real.pi := by linarith
          exact Real.sin_pos_of_pos_of_lt_pi hdiff_pos hdiff_pi
