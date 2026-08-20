import ErdosProblems.Erdos733.ST.CrossingLemma
import ErdosProblems.Erdos733.ST.UnitDistanceArcGraph

open scoped Real

-- [TABLET NODE: unit_distance_upper_bound]
theorem unit_distance_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        (unitDist P : ℝ) ≤ C * (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
-- BODY
  refine ⟨5 + (200 : ℝ) ^ ((1 : ℝ) / 3), by positivity, ?_⟩
  intro P
  by_cases hP0 : P.card = 0
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hP0
    simp [unitDist, hPempty]
  · have hn_nat : 1 ≤ P.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hP0)
    have hn : (1 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hn_nat
    have hn_nonneg : 0 ≤ (P.card : ℝ) := by positivity
    have hn_pow : (P.card : ℝ) ≤ (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
      exact Real.self_le_rpow_of_one_le hn (by norm_num)
    have hpow_nonneg : 0 ≤ (P.card : ℝ) ^ ((4 : ℝ) / 3) :=
      Real.rpow_nonneg hn_nonneg _
    have hroot_nonneg : 0 ≤ (200 : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) _
    have hC_ge_five : (5 : ℝ) ≤ 5 + (200 : ℝ) ^ ((1 : ℝ) / 3) := by
      nlinarith
    rcases UnitDistanceArcGraph P with ⟨G, hGfin, h_edges, h_cross⟩
    letI : Fintype G.edgeSet := hGfin
    let e : ℝ := (G.edgeFinset.card : ℝ)
    have hu_le : (unitDist P : ℝ) ≤ e + (P.card : ℝ) := by
      dsimp [e]
      nlinarith [h_edges]
    by_cases hsmall : G.edgeFinset.card < 4 * P.card
    · have hsmallR : e < 4 * (P.card : ℝ) := by
        dsimp [e]
        exact_mod_cast hsmall
      have hu_lt : (unitDist P : ℝ) < 5 * (P.card : ℝ) := by
        nlinarith
      have hfive_n_le :
          5 * (P.card : ℝ) ≤ 5 * (P.card : ℝ) ^ ((4 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hn_pow (by norm_num)
      have hfive_pow_le :
          5 * (P.card : ℝ) ^ ((4 : ℝ) / 3) ≤
            (5 + (200 : ℝ) ^ ((1 : ℝ) / 3)) *
              (P.card : ℝ) ^ ((4 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right hC_ge_five hpow_nonneg
      exact (le_of_lt hu_lt).trans (hfive_n_le.trans hfive_pow_le)
    · have hlarge_nat : 4 * P.card ≤ G.edgeFinset.card := le_of_not_gt hsmall
      have hnV : 1 ≤ Fintype.card P := by
        simpa [Fintype.card_coe] using hn_nat
      have hlargeV : 4 * Fintype.card P ≤ G.edgeFinset.card := by
        simpa [Fintype.card_coe] using hlarge_nat
      have hcross_lower := CrossingLemma G hnV hlargeV
      have hcross_lower' :
          e ^ 3 / (100 * (P.card : ℝ) ^ 2) ≤ (CrossingNumber G : ℝ) := by
        dsimp [e]
        simpa [Fintype.card_coe] using hcross_lower
      have hbound :
          e ^ 3 / (100 * (P.card : ℝ) ^ 2) ≤ 2 * (P.card : ℝ) ^ 2 :=
        hcross_lower'.trans h_cross
      have hden_pos : 0 < 100 * (P.card : ℝ) ^ 2 := by
        positivity
      have hcube_le : e ^ 3 ≤ 200 * (P.card : ℝ) ^ 4 := by
        have hmul := (div_le_iff₀ hden_pos).mp hbound
        nlinarith [hmul]
      have he_nonneg : 0 ≤ e := by
        dsimp [e]
        positivity
      have htarget_nonneg : 0 ≤ 200 * (P.card : ℝ) ^ 4 := by
        positivity
      have he_root_inv : e ≤ (200 * (P.card : ℝ) ^ 4) ^ ((3 : ℝ)⁻¹) := by
        rw [Real.le_rpow_inv_iff_of_pos he_nonneg htarget_nonneg
          (by norm_num : (0 : ℝ) < 3)]
        simpa [Real.rpow_natCast] using hcube_le
      have hroot_factor :
          (200 * (P.card : ℝ) ^ 4) ^ ((1 : ℝ) / 3) =
            (200 : ℝ) ^ ((1 : ℝ) / 3) *
              (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 200) (pow_nonneg hn_nonneg 4)]
        rw [← Real.rpow_natCast_mul hn_nonneg 4 ((1 : ℝ) / 3)]
        congr 1
        norm_num
      have hroot_factor_inv :
          (200 * (P.card : ℝ) ^ 4) ^ ((3 : ℝ)⁻¹) =
            (200 : ℝ) ^ ((1 : ℝ) / 3) *
              (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
        simpa [one_div] using hroot_factor
      have he_le :
          e ≤ (200 : ℝ) ^ ((1 : ℝ) / 3) *
            (P.card : ℝ) ^ ((4 : ℝ) / 3) :=
        he_root_inv.trans_eq hroot_factor_inv
      have hsum_le :
          e + (P.card : ℝ) ≤
            (200 : ℝ) ^ ((1 : ℝ) / 3) *
                (P.card : ℝ) ^ ((4 : ℝ) / 3) +
              (P.card : ℝ) ^ ((4 : ℝ) / 3) :=
        add_le_add he_le hn_pow
      have hone_pow_le :
          (1 : ℝ) * (P.card : ℝ) ^ ((4 : ℝ) / 3) ≤
            5 * (P.card : ℝ) ^ ((4 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 5) hpow_nonneg
      have hsum_le_C :
          (200 : ℝ) ^ ((1 : ℝ) / 3) *
                (P.card : ℝ) ^ ((4 : ℝ) / 3) +
              (P.card : ℝ) ^ ((4 : ℝ) / 3) ≤
            (5 + (200 : ℝ) ^ ((1 : ℝ) / 3)) *
              (P.card : ℝ) ^ ((4 : ℝ) / 3) := by
        nlinarith [hone_pow_le]
      exact hu_le.trans (hsum_le.trans hsum_le_C)
