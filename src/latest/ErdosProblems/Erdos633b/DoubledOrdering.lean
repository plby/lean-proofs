import ErdosProblems.Erdos633b.DoubledTiling
import ErdosProblems.Erdos633b.DoubledOuterMetric
import ErdosProblems.Erdos633b.Arithmetic

/-! Both strict parameter orders give the same geometric doubled-triangle family. -/

namespace Erdos633b.DoubledCoordinates

open Sixty DoubledDimensions

theorem groupTwo_parameters_ne (a b c : ℕ) (ha : 0 < a)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) : a ≠ b := by
  intro heq
  subst b
  have hnat : c ^ 2 = 3 * a ^ 2 := by nlinarith
  have hrat : (c : ℚ) ^ 2 = 3 * (a : ℚ) ^ 2 := by exact_mod_cast hnat
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hs : IsSquare (3 : ℚ) := by
    refine ⟨(c : ℚ) / a, ?_⟩
    field_simp
    nlinarith only [hrat]
  have hs' : IsSquare (3 : ℕ) := Rat.isSquare_ofNat_iff.mp hs
  obtain ⟨k, hk⟩ := hs'
  by_cases hk1 : k ≤ 1
  · obtain rfl | rfl := (show k = 0 ∨ k = 1 by omega)
    all_goals norm_num at hk
  · have hk2 : 2 ≤ k := by omega
    nlinarith

theorem doubled_patch_exists (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ∃ m : ℕ, ∃ hm : 0 < m,
      Nonempty (Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
        (outer d hd a b c m (by exact_mod_cast ha) (by exact_mod_cast hb)
          (by exact_mod_cast hc) (by exact_mod_cast hm)).support
        (m ^ 2 * (a + 2 * b) * (2 * a + b))) := by
  obtain hab | hba := lt_or_gt_of_ne (groupTwo_parameters_ne a b c ha hrel)
  · exact ⟨outerScale a b c, outerScale_pos a b c hb hc,
      ⟨doubled_integer_patch d hd he a b c ha hab hc hrel⟩⟩
  · have har : (0 : ℝ) < a := by exact_mod_cast ha
    have hbr : (0 : ℝ) < b := by exact_mod_cast hb
    have hcr : (0 : ℝ) < c := by exact_mod_cast hc
    have hrel' : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by nlinarith
    have hrelr : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + (a : ℝ) * b + (b : ℝ) ^ 2 := by
      exact_mod_cast hrel
    have hrelr' : (c : ℝ) ^ 2 = (b : ℝ) ^ 2 + (b : ℝ) * a + (a : ℝ) ^ 2 := by
      exact_mod_cast hrel'
    let m := outerScale b a c
    have hm : 0 < m := outerScale_pos b a c ha hc
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    let R := groupTwoReference d hd a b har hbr
    let R0 := groupTwoReference d hd b a hbr har
    let R' : Triangle := R.reindex (Equiv.swap 1 2)
    let S0 := outer d hd b a c m hbr har hcr hmr
    let S : Triangle := S0.reindex (Equiv.swap 0 1)
    let T := outer d hd a b c m har hbr hcr hmr
    have hsides (i : Fin 3) : S.side i = T.side i := by
      rw [Triangle.side_reindex, outer_sides d hd he b a c m hbr har hcr hmr hrelr',
        outer_sides d hd he a b c m har hbr hcr hmr hrelr]
      fin_cases i
      · change (m : ℝ) * b * ((b : ℝ) + 2 * a) = (m : ℝ) * b * (2 * (a : ℝ) + b)
        ring
      · change (m : ℝ) * a * (2 * (b : ℝ) + a) = (m : ℝ) * a * ((a : ℝ) + 2 * b)
        ring
      · rfl
    have hreference (i : Fin 3) : R'.side i = R0.side i := by
      rw [Triangle.side_reindex, reference_sides d hd he a b c har hbr hcr hrelr,
        reference_sides d hd he b a c hbr har hcr hrelr']
      fin_cases i <;> rfl
    have d0 : Patch R0 S.support (m ^ 2 * (b + 2 * a) * (2 * b + a)) := by
      simpa only [S, Triangle.support_reindex] using
        doubled_integer_patch d hd he b a c hb hba hc hrel'
    have result := ((d0.transportSides T hsides).changeTileBySides R' hreference).changeTile
      (R.support_reindex (Equiv.swap 1 2))
    have hn : m ^ 2 * (b + 2 * a) * (2 * b + a) = m ^ 2 * (a + 2 * b) * (2 * a + b) := by ring
    rw [hn] at result
    exact ⟨m, hm, ⟨result⟩⟩

end Erdos633b.DoubledCoordinates
