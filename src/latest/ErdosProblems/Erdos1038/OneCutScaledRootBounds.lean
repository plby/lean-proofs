import ErdosProblems.Erdos1038.OneCutScaledDerivative

/-!
# Root enclosures from stable residual signs

These lemmas are the semantic bridge used by each rational interval box.  A
checker only has to prove strict signs of the resolved scaled residual at its
rational endpoints; the actual nontrivial inner and outer roots are then
enclosed by the displayed interval.
-/

open Set

namespace Erdos1038

noncomputable section

theorem scaledInnerResidual_eq_exteriorFunction_div {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hqz : q < z) (hz1 : z < 1) :
    scaledInnerResidual (q, z) = exteriorFunction q (z / q) := by
  have hu0 : 0 < z / q := div_pos (hq.trans hqz) hq
  have hqu : q < z / q := by
    rw [lt_div_iff₀ hq]
    nlinarith
  have hpole : q * (z / q) ≠ 1 := by
    rw [mul_div_cancel₀ _ hq.ne']
    exact hz1.ne
  rw [scaledInnerResidual_eq_scaledResidual hz1]
  convert! scaledResidual_mul_eq_exteriorFunction hq hq1 hu0 hqu hpole using 1
  field_simp [hq.ne']

theorem scaledOuterResidual_eq_exteriorFunction_div {q z : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hz1 : 1 < z) :
    scaledOuterResidual (q, z) = exteriorFunction q (z / q) := by
  have hu0 : 0 < z / q := div_pos (by linarith) hq
  have hqu : q < z / q := by
    rw [lt_div_iff₀ hq]
    nlinarith
  have hpole : q * (z / q) ≠ 1 := by
    rw [mul_div_cancel₀ _ hq.ne']
    exact hz1.ne'
  rw [scaledOuterResidual_eq_scaledResidual hz1]
  convert! scaledResidual_mul_eq_exteriorFunction hq hq1 hu0 hqu hpole using 1
  field_simp [hq.ne']

theorem exteriorFunction_inner_neg_before_uPlus {q u : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) (hu1 : 1 < u)
    (huq : u < q⁻¹) (huplus : u < uPlus q) :
    exteriorFunction q u < 0 := by
  have hroot : exteriorFunction q (uPlus q) = 0 :=
    exteriorEquation_iff_exteriorFunction_eq_zero.1 (uPlus_spec hq hqs).2.2
  rcases le_total u (innerCritical q) with huc | hcu
  · have hanti := exteriorFunction_strictAntiOn_one_critical hq hqs
      ⟨le_rfl, (innerCritical_gt_one hq hqs).le⟩ ⟨hu1.le, huc⟩ hu1
    rw [exteriorFunction_one (q_lt_one_of_pos_le_qSoft hq hqs.le)] at hanti
    exact hanti
  · have hmono := exteriorFunction_strictMonoOn_after_critical hq hqs
      ⟨hcu, huq⟩
      ⟨(innerCritical_lt_uPlus hq hqs).le, (uPlus_spec hq hqs).2.1⟩ huplus
    rwa [hroot] at hmono

theorem exteriorFunction_inner_pos_after_uPlus {q u : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) (huq : u < q⁻¹)
    (hplusu : uPlus q < u) :
    0 < exteriorFunction q u := by
  have hroot : exteriorFunction q (uPlus q) = 0 :=
    exteriorEquation_iff_exteriorFunction_eq_zero.1 (uPlus_spec hq hqs).2.2
  have hmono := exteriorFunction_strictMonoOn_after_critical hq hqs
    ⟨(innerCritical_lt_uPlus hq hqs).le, (uPlus_spec hq hqs).2.1⟩
    ⟨(innerCritical_lt_uPlus hq hqs).trans hplusu |>.le, huq⟩ hplusu
  rwa [hroot] at hmono

theorem scaledInnerResidual_neg_imp_lt_zPlus {q a : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) (hqa : q < a) (ha1 : a < 1)
    (hneg : scaledInnerResidual (q, a) < 0) :
    a < zPlus q := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hu1 : 1 < a / q := (lt_div_iff₀ hq).2 (by simpa using! hqa)
  have huq : a / q < q⁻¹ := by
    rw [← one_div, div_lt_div_iff_of_pos_right hq]
    exact ha1
  by_contra hn
  have hle : zPlus q ≤ a := le_of_not_gt hn
  have huple : uPlus q ≤ a / q := by
    rw [zPlus] at hle
    exact (le_div_iff₀ hq).2 (by simpa [mul_comm] using! hle)
  rcases huple.eq_or_lt with heq | hlt
  · have hzero : exteriorFunction q (a / q) = 0 := by
      rw [← heq]
      exact exteriorEquation_iff_exteriorFunction_eq_zero.1
        (uPlus_spec hq hqs).2.2
    rw [scaledInnerResidual_eq_exteriorFunction_div hq hq1 hqa ha1,
      hzero] at hneg
    exact lt_irrefl 0 hneg
  · have hpos := exteriorFunction_inner_pos_after_uPlus hq hqs huq hlt
    rw [scaledInnerResidual_eq_exteriorFunction_div hq hq1 hqa ha1] at hneg
    linarith

theorem scaledInnerResidual_pos_imp_zPlus_lt {q b : ℝ}
    (hq : 0 < q) (hqs : q < qSoft) (hqb : q < b) (hb1 : b < 1)
    (hpos : 0 < scaledInnerResidual (q, b)) :
    zPlus q < b := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs.le
  have hu1 : 1 < b / q := (lt_div_iff₀ hq).2 (by simpa using! hqb)
  have huq : b / q < q⁻¹ := by
    rw [← one_div, div_lt_div_iff_of_pos_right hq]
    exact hb1
  by_contra hn
  have hle : b ≤ zPlus q := le_of_not_gt hn
  have hule : b / q ≤ uPlus q := by
    rw [zPlus] at hle
    exact (div_le_iff₀ hq).2 (by simpa [mul_comm] using! hle)
  rcases hule.eq_or_lt with heq | hlt
  · have hzero : exteriorFunction q (b / q) = 0 := by
      rw [heq]
      exact exteriorEquation_iff_exteriorFunction_eq_zero.1
        (uPlus_spec hq hqs).2.2
    rw [scaledInnerResidual_eq_exteriorFunction_div hq hq1 hqb hb1,
      hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hneg := exteriorFunction_inner_neg_before_uPlus hq hqs hu1 huq hlt
    rw [scaledInnerResidual_eq_exteriorFunction_div hq hq1 hqb hb1] at hpos
    linarith

theorem scaledOuterResidual_pos_imp_lt_zMinus {q a : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) (ha1 : 1 < a)
    (hpos : 0 < scaledOuterResidual (q, a)) :
    a < zMinus q := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs
  have huq : q⁻¹ < a / q := by
    rw [← one_div, div_lt_div_iff_of_pos_right hq]
    exact ha1
  by_contra hn
  have hle : zMinus q ≤ a := le_of_not_gt hn
  have humle : uMinus q ≤ a / q := by
    rw [zMinus] at hle
    exact (le_div_iff₀ hq).2 (by simpa [mul_comm] using! hle)
  rcases humle.eq_or_lt with heq | hlt
  · have hzero : exteriorFunction q (a / q) = 0 := by
      rw [← heq]
      exact exteriorEquation_iff_exteriorFunction_eq_zero.1
        (uMinus_spec hq hqs).2
    rw [scaledOuterResidual_eq_exteriorFunction_div hq hq1 ha1, hzero] at hpos
    exact lt_irrefl 0 hpos
  · have hanti := exteriorFunction_strictAntiOn_outer hq hqs
      (uMinus_spec hq hqs).1 huq hlt
    have hzero := exteriorEquation_iff_exteriorFunction_eq_zero.1
      (uMinus_spec hq hqs).2
    rw [hzero] at hanti
    rw [scaledOuterResidual_eq_exteriorFunction_div hq hq1 ha1] at hpos
    linarith

theorem scaledOuterResidual_neg_imp_zMinus_lt {q b : ℝ}
    (hq : 0 < q) (hqs : q ≤ qSoft) (hb1 : 1 < b)
    (hneg : scaledOuterResidual (q, b) < 0) :
    zMinus q < b := by
  have hq1 := q_lt_one_of_pos_le_qSoft hq hqs
  have huq : q⁻¹ < b / q := by
    rw [← one_div, div_lt_div_iff_of_pos_right hq]
    exact hb1
  by_contra hn
  have hle : b ≤ zMinus q := le_of_not_gt hn
  have hule : b / q ≤ uMinus q := by
    rw [zMinus] at hle
    exact (div_le_iff₀ hq).2 (by simpa [mul_comm] using! hle)
  rcases hule.eq_or_lt with heq | hlt
  · have hzero : exteriorFunction q (b / q) = 0 := by
      rw [heq]
      exact exteriorEquation_iff_exteriorFunction_eq_zero.1
        (uMinus_spec hq hqs).2
    rw [scaledOuterResidual_eq_exteriorFunction_div hq hq1 hb1, hzero] at hneg
    exact lt_irrefl 0 hneg
  · have hanti := exteriorFunction_strictAntiOn_outer hq hqs huq
      (uMinus_spec hq hqs).1 hlt
    have hzero := exteriorEquation_iff_exteriorFunction_eq_zero.1
      (uMinus_spec hq hqs).2
    rw [hzero] at hanti
    rw [scaledOuterResidual_eq_exteriorFunction_div hq hq1 hb1] at hneg
    linarith

/-- A four-sign endpoint certificate encloses both scaled roots. -/
theorem scaledRoots_mem_Ioo_of_endpoint_signs {q ap bp am bm : ℝ}
    (hq : 0 < q) (hqs : q < qSoft)
    (hqap : q < ap) (hapbp : ap < bp) (hbp1 : bp < 1)
    (h1am : 1 < am) (hambm : am < bm)
    (hpLo : scaledInnerResidual (q, ap) < 0)
    (hpHi : 0 < scaledInnerResidual (q, bp))
    (hmLo : 0 < scaledOuterResidual (q, am))
    (hmHi : scaledOuterResidual (q, bm) < 0) :
    zPlus q ∈ Ioo ap bp ∧ zMinus q ∈ Ioo am bm := by
  exact ⟨⟨scaledInnerResidual_neg_imp_lt_zPlus hq hqs hqap
      (hapbp.trans hbp1) hpLo,
    scaledInnerResidual_pos_imp_zPlus_lt hq hqs (hqap.trans hapbp) hbp1 hpHi⟩,
    ⟨scaledOuterResidual_pos_imp_lt_zMinus hq hqs.le h1am hmLo,
      scaledOuterResidual_neg_imp_zMinus_lt hq hqs.le
        (h1am.trans hambm) hmHi⟩⟩

end

end Erdos1038
