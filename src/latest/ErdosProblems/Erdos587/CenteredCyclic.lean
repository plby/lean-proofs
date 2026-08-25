import ErdosProblems.Erdos587.FullPeriodDensity
import ErdosProblems.Erdos587.RootMargin

/-!
# Centered cyclic frequencies

The discrete rectangle count is compared to the centered interval means
without dropping the complete Gauss mean at any frequency.
-/

open scoped BigOperators

namespace Erdos587

open Erdos438.QuadraticWeyl

lemma exactQuadraticInterval_neg (q : ℕ) (a s : ℤ) (L : ℕ) :
    exactQuadraticInterval q (-a) s L = starRingEnd ℂ (exactQuadraticInterval q a s L) := by
  unfold exactQuadraticInterval quadraticResiduePhase
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← phase_neg]
  congr 1
  push_cast
  ring

lemma completeQuadraticGaussSum_neg_zero {q : ℕ} (hq : 0 < q) (a : ℤ) :
    completeQuadraticGaussSum q (-a) 0 = starRingEnd ℂ (completeQuadraticGaussSum q a 0) := by
  rw [← exactQuadraticInterval_period hq (-a) 0, ← exactQuadraticInterval_period hq a 0]
  exact exactQuadraticInterval_neg q a 0 q

lemma centeredQuadraticInterval_neg {q : ℕ} (hq : 0 < q) (a s : ℤ) (L : ℕ) :
    centeredQuadraticInterval q (-a) s L = starRingEnd ℂ (centeredQuadraticInterval q a s L) := by
  rw [centeredQuadraticInterval, centeredQuadraticInterval,
    exactQuadraticInterval_neg, completeQuadraticGaussSum_neg_zero hq,
    map_sub, map_mul, map_div₀, map_natCast, map_natCast]

lemma norm_centeredQuadraticInterval_neg {q : ℕ} (hq : 0 < q) (a s : ℤ) (L : ℕ) :
    ‖centeredQuadraticInterval q (-a) s L‖ = ‖centeredQuadraticInterval q a s L‖ := by
  rw [centeredQuadraticInterval_neg hq]
  exact norm_star _

lemma nvQuadraticIntervalSum_pure_factor
    (q A C X Z L : ℕ) [NeZero q] (s : ℤ) :
    nvQuadraticIntervalSum q A 0 C X Z L (s : ZMod q) =
      phase (((s * ((C : ℤ) - X) : ℤ) : ℝ) / q) *
        exactQuadraticInterval q (s * A) Z L := by
  unfold nvQuadraticIntervalSum exactQuadraticInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcast : (s : ZMod q) *
        ((A * (Z + j) ^ 2 + 0 * (Z + j) + C : ℕ) : ZMod q) -
      (s : ZMod q) * (X : ZMod q) =
      ((s * (((A * (Z + j) ^ 2 + C : ℕ) : ℤ) - X) : ℤ) : ZMod q) := by
    push_cast
    ring
  rw [hcast, stdAddChar_int_eq_phase, quadraticResiduePhase, ← phase_add]
  congr 1
  push_cast
  ring

lemma nvCenteredQuadraticIntervalSum_pure_factor
    (q A C X Z L : ℕ) [NeZero q] (s : ℤ) :
    nvCenteredQuadraticIntervalSum q A 0 C X Z L (s : ZMod q) =
      phase (((s * ((C : ℤ) - X) : ℤ) : ℝ) / q) *
        centeredQuadraticInterval q (s * A) Z L := by
  rw [nvCenteredQuadraticIntervalSum, nvQuadraticIntervalSum_pure_factor,
    nvQuadraticIntervalSum_pure_factor, exactQuadraticInterval_period (NeZero.pos q)]
  rw [centeredQuadraticInterval]
  ring

lemma norm_nvCenteredQuadraticIntervalSum_pure_int
    (q A C X Z L : ℕ) [NeZero q] (s : ℤ) :
    ‖nvCenteredQuadraticIntervalSum q A 0 C X Z L (s : ZMod q)‖ =
      ‖centeredQuadraticInterval q (s * A) Z L‖ := by
  rw [nvCenteredQuadraticIntervalSum_pure_factor, norm_mul, norm_phase, one_mul]

lemma norm_nvCenteredQuadraticIntervalSum_pure
    (q A C X Z L : ℕ) [NeZero q] (h : ZMod q) :
    ‖nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖ =
      ‖centeredQuadraticInterval q ((A * h.valMinAbs.natAbs : ℕ) : ℤ) Z L‖ := by
  let s : ℤ := h.valMinAbs
  let d : ℕ := h.valMinAbs.natAbs
  have hh : h = (s : ZMod q) := (ZMod.coe_valMinAbs h).symm
  have hd : (d : ℤ) = |s| := by simp [d, s]
  conv_lhs => rw [hh, norm_nvCenteredQuadraticIntervalSum_pure_int]
  change ‖centeredQuadraticInterval q (s * A) Z L‖ =
    ‖centeredQuadraticInterval q ((A * d : ℕ) : ℤ) Z L‖
  rcases le_total 0 s with hs | hs
  · have hsd : s = d := by rw [← abs_of_nonneg hs, ← hd]
    rw [hsd]
    have hcoef : (d : ℤ) * A = ((A * d : ℕ) : ℤ) := by push_cast; ring
    rw [hcoef]
  · have hsd : s = -(d : ℤ) := by
      have habs := abs_of_nonpos hs
      rw [← hd] at habs
      omega
    rw [hsd]
    have hcoef : -(d : ℤ) * A = -((A * d : ℕ) : ℤ) := by push_cast; ring
    rw [hcoef, norm_centeredQuadraticInterval_neg (NeZero.pos q)]

lemma card_leastResidueFiber_le_two_all (q d : ℕ) [NeZero q] :
    (Waring.Analytic.leastResidueFiber q d).card ≤ 2 := by
  classical
  by_cases hne : (Waring.Analytic.leastResidueFiber q d).Nonempty
  · obtain ⟨h, hh⟩ := hne
    have hd : h.valMinAbs.natAbs = d := by
      simpa only [Waring.Analytic.leastResidueFiber, Finset.mem_filter,
        Finset.mem_univ, true_and] using hh
    apply Waring.Analytic.card_leastResidueFiber_le_two
    rw [← hd]
    exact ZMod.natAbs_valMinAbs_le h
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

lemma sum_low_norm_le_two_nat_norm (q M : ℕ) [NeZero q]
    (f : ZMod q → ℂ) (g : ℕ → ℂ)
    (hnorm : ∀ h, ‖f h‖ = ‖g h.valMinAbs.natAbs‖) :
    (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter (fun h => h.valMinAbs.natAbs ≤ M), ‖f h‖) ≤
      2 * ∑ d ∈ Finset.Icc 1 M, ‖g d‖ := by
  classical
  let low := (Finset.univ.erase (0 : ZMod q)).filter (fun h => h.valMinAbs.natAbs ≤ M)
  let ds := Finset.Icc 1 M
  let b : ZMod q → ℕ := fun h => h.valMinAbs.natAbs
  have hmaps : (low : Set (ZMod q)).MapsTo b ds := by
    intro h hh
    have hh' := Finset.mem_filter.mp hh
    have hh0 := (Finset.mem_erase.mp hh'.1).1
    have hdpos : 1 ≤ h.valMinAbs.natAbs := by
      have hne : h.valMinAbs ≠ 0 := fun hz => hh0 ((ZMod.valMinAbs_eq_zero h).mp hz)
      omega
    exact Finset.mem_Icc.mpr ⟨hdpos, hh'.2⟩
  have hfiber (d : ℕ) : ((low.filter fun h => b h = d).card : ℝ) ≤ 2 := by
    have hsub : low.filter (fun h => b h = d) ⊆ Waring.Analytic.leastResidueFiber q d := by
      intro h hh
      have hhd := (Finset.mem_filter.mp hh).2
      simpa only [b, Waring.Analytic.leastResidueFiber, Finset.mem_filter,
        Finset.mem_univ, true_and] using hhd
    exact_mod_cast (Finset.card_le_card hsub).trans (card_leastResidueFiber_le_two_all q d)
  have hterm (d : ℕ) : (∑ h ∈ low with b h = d, ‖f h‖) ≤ 2 * ‖g d‖ := by
    calc
      _ = ∑ _h ∈ low.filter (fun h => b h = d), ‖g d‖ := by
        apply Finset.sum_congr rfl
        intro h hh
        have hhd : h.valMinAbs.natAbs = d := (Finset.mem_filter.mp hh).2
        rw [hnorm, hhd]
      _ = ((low.filter fun h => b h = d).card : ℝ) * ‖g d‖ := by simp
      _ ≤ 2 * ‖g d‖ := mul_le_mul_of_nonneg_right (hfiber d) (norm_nonneg _)
  change (∑ h ∈ low, ‖f h‖) ≤ _
  calc
    _ = ∑ d ∈ ds, ∑ h ∈ low with b h = d, ‖f h‖ :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ d ∈ ds, 2 * ‖g d‖ := Finset.sum_le_sum (fun d hd => hterm d)
    _ = _ := by rw [Finset.mul_sum]

lemma sum_low_norm_nvCenteredQuadraticIntervalSum_le
    (q A C X Z L M : ℕ) [NeZero q] :
    (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter (fun h => h.valMinAbs.natAbs ≤ M),
      ‖nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖) ≤
      2 * ∑ d ∈ Finset.Icc 1 M,
        ‖centeredQuadraticInterval q ((A * d : ℕ) : ℤ) Z L‖ := by
  exact sum_low_norm_le_two_nat_norm q M _ _ (norm_nvCenteredQuadraticIntervalSum_pure q A C X Z L)

theorem exists_centered_cyclic_low_mean_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q A C X Z L M : ℕ) [NeZero q], A.Coprime q →
        0 < 2 * M * L → 3 ≤ (((2 * M * L : ℕ) : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ)) →
        (q : ℝ) ≤ (((2 * M * L : ℕ) : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ)) →
        (∑ h ∈ (Finset.univ.erase (0 : ZMod q)).filter (fun h => h.valMinAbs.natAbs ≤ M),
          ‖nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖) ≤
          K * M * Real.sqrt L * Real.log ((2 * M * L : ℕ) : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hmean⟩ := exists_centered_quadratic_first_mean_of_power_margin j
  refine ⟨2 * K, by positivity, O, hO, ?_⟩
  intro q A C X Z L M hq ha hsize hroot hmargin
  have hm := hmean A q M L ha (NeZero.pos q) hsize hroot hmargin
    (fun _ => (Z : ℤ)) (fun _ => L) (fun _ _ => le_rfl)
  calc
    _ ≤ 2 * ∑ d ∈ Finset.Icc 1 M,
        ‖centeredQuadraticInterval q ((A * d : ℕ) : ℤ) Z L‖ :=
      sum_low_norm_nvCenteredQuadraticIntervalSum_le q A C X Z L M
    _ ≤ 2 * (K * M * Real.sqrt L * Real.log ((2 * M * L : ℕ) : ℝ) ^ O) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

end Erdos587
