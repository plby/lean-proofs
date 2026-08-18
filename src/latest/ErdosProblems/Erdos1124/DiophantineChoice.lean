/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0 license. -/
import ErdosProblems.Erdos1124.OneDimensionalDiscrepancy
import ErdosProblems.Erdos1124.TorusAction
import ErdosProblems.Erdos1124.FreeTuple
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# A simultaneous Diophantine choice of circle generators

The fixed negative-half-moment estimates from
`OneDimensionalDiscrepancy` imply, by a summable Markov bound and the first
Borel--Cantelli lemma, that almost every tuple eventually satisfies the
polynomial product lower bound needed in the discrepancy argument.  Removing
the null sets on which an integer multiple of a coordinate vanishes turns
that eventual estimate into a uniform estimate.
-/

open scoped BigOperators ENNReal NNReal Topology
open Finset Function MeasureTheory Set Filter

namespace Erdos1124.DiophantineChoice

noncomputable section


abbrev Circle := OneDimensionalDiscrepancy.Circle
abbrev tupleHaar (d : ℕ) := OneDimensionalDiscrepancy.tupleHaar d

/-- Product of the distances to the nearest integer at frequency `h`. -/
def distanceProduct {d : ℕ} (h : ℤ) (u : Fin d → Circle) : ℝ :=
  ∏ i, OneDimensionalDiscrepancy.integerDistance (h • u i)

lemma distanceProduct_nonneg {d : ℕ} (h : ℤ) (u : Fin d → Circle) :
    0 ≤ distanceProduct h u := by
  exact Finset.prod_nonneg fun i _ ↦ OneDimensionalDiscrepancy.integerDistance_nonneg _

@[simp] lemma distanceProduct_neg {d : ℕ} (h : ℤ) (u : Fin d → Circle) :
    distanceProduct (-h) u = distanceProduct h u := by
  simp [distanceProduct, neg_smul]

lemma tupleMomentAt_eq_rpow_distanceProduct {d : ℕ} (h : ℤ) (u : Fin d → Circle) :
    OneDimensionalDiscrepancy.tupleNegativeHalfMomentAt h u =
      distanceProduct h u ^ (-(1 / 2 : ℝ)) := by
  exact OneDimensionalDiscrepancy.tupleNegativeHalfMoment_eq_rpow_prod (fun i ↦ h • u i)

private def frequency (n : ℕ) : ℤ := (n + 1 : ℕ)

private def momentThreshold (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ (3 / 2 : ℝ)

private def largeMoment {d : ℕ} (n : ℕ) : Set (Fin d → Circle) :=
  {u | momentThreshold n ≤ OneDimensionalDiscrepancy.tupleNegativeHalfMomentAt (frequency n) u}

private lemma frequency_ne_zero (n : ℕ) : frequency n ≠ 0 := by
  change ((n + 1 : ℕ) : ℤ) ≠ 0
  exact_mod_cast Nat.succ_ne_zero n

private lemma momentThreshold_pos (n : ℕ) : 0 < momentThreshold n := by
  exact Real.rpow_pos_of_pos (by positivity) _

private lemma integral_tupleMoment_nonneg (d : ℕ) :
    0 ≤ ∫ u, OneDimensionalDiscrepancy.tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d) :=
  integral_nonneg fun u ↦ OneDimensionalDiscrepancy.tupleNegativeHalfMoment_nonneg u

private lemma measureReal_largeMoment_le (d n : ℕ) :
    (tupleHaar d).real (largeMoment (d := d) n) ≤
      (∫ u, OneDimensionalDiscrepancy.tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) /
        momentThreshold n := by
  apply (le_div_iff₀ (momentThreshold_pos n)).2
  simpa [largeMoment, mul_comm] using
    OneDimensionalDiscrepancy.mul_measureReal_tupleMoment_ge_le_integral d (frequency_ne_zero n)
      (momentThreshold n)

private lemma summable_moment_majorant (d : ℕ) :
    Summable (fun n : ℕ ↦
      (∫ u, OneDimensionalDiscrepancy.tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) /
        momentThreshold n) := by
  have hs0 : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hs : Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-(3 / 2 : ℝ))) := by
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hs0
  have hmul := hs.mul_left
    (∫ u, OneDimensionalDiscrepancy.tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d))
  apply hmul.congr
  intro n
  rw [momentThreshold, div_eq_mul_inv, Real.rpow_neg
    (by positivity : 0 ≤ (n + 1 : ℝ))]
  rfl

private lemma tsum_measure_largeMoment_ne_top (d : ℕ) :
    ∑' n, tupleHaar d (largeMoment (d := d) n) ≠ ∞ := by
  have hs := summable_moment_majorant d
  have htop : ∑' n : ℕ, ENNReal.ofReal
      ((∫ u, OneDimensionalDiscrepancy.tupleNegativeHalfMoment (d := d) u ∂(tupleHaar d)) /
        momentThreshold n) ≠ ∞ := hs.tsum_ofReal_ne_top
  apply ne_top_of_le_ne_top htop
  apply ENNReal.tsum_le_tsum
  intro n
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_largeMoment_le d n)

/-- Almost every tuple has only finitely many frequencies at which its
negative half moment is as large as the critical `n^(3/2)` threshold. -/
theorem ae_eventually_not_largeMoment (d : ℕ) :
    ∀ᵐ u ∂(tupleHaar d), ∀ᶠ n in atTop, u ∉ largeMoment (d := d) n :=
  ae_eventually_notMem (tsum_measure_largeMoment_ne_top d)

private lemma measure_coordinate_integerMultiple_eq_zero {d : ℕ}
    (h : ℤ) (hh : h ≠ 0) (i : Fin d) :
    tupleHaar d {u | h • u i = 0} = 0 := by
  have heval : MeasurePreserving (fun u : Fin d → Circle ↦ u i)
      (tupleHaar d) OneDimensionalDiscrepancy.circleHaar := by
    exact measurePreserving_eval (fun _ : Fin d ↦ OneDimensionalDiscrepancy.circleHaar) i
  have hmul := (OneDimensionalDiscrepancy.measurePreserving_integerMultiple h hh).comp heval
  have hpre := hmul.measure_preimage
    (measurableSet_singleton (0 : Circle)).nullMeasurableSet
  change tupleHaar d {u | h • u i = 0} =
    OneDimensionalDiscrepancy.circleHaar ({0} : Set Circle) at hpre
  have hz : OneDimensionalDiscrepancy.circleHaar ({0} : Set Circle) = 0 :=
    by
      have hv : (volume : Measure Circle) = OneDimensionalDiscrepancy.circleHaar := by
        simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
      rw [← hv]
      exact FreeTuple.volume_singleton_circle 0
  exact hpre.trans hz

/-- No nonzero integer frequency kills any coordinate, almost everywhere. -/
theorem ae_forall_integerMultiple_ne_zero (d : ℕ) :
    ∀ᵐ u ∂(tupleHaar d), ∀ h : ℤ, h ≠ 0 → ∀ i, h • u i ≠ 0 := by
  rw [ae_all_iff]
  intro h
  by_cases hh : h = 0
  · subst h
    simp
  · have hi : ∀ i : Fin d, ∀ᵐ u ∂(tupleHaar d), h • u i ≠ 0 := by
      intro i
      rw [ae_iff]
      simpa only [not_ne_iff] using measure_coordinate_integerMultiple_eq_zero h hh i
    filter_upwards [ae_all_iff.mpr hi] with u hu
    exact fun _ i ↦ hu i

private lemma distanceProduct_pos_of_coordinates {d : ℕ} {h : ℤ}
    {u : Fin d → Circle} (hu : ∀ i, h • u i ≠ 0) :
    0 < distanceProduct h u := by
  apply Finset.prod_pos
  intro i _
  simpa [OneDimensionalDiscrepancy.integerDistance, norm_pos_iff] using hu i

private lemma eventual_distanceProduct_lower {d : ℕ} {u : Fin d → Circle}
    (hlarge : ∀ᶠ n in atTop, u ∉ largeMoment (d := d) n)
    (hnz : ∀ h : ℤ, h ≠ 0 → ∀ i, h • u i ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      (n + 1 : ℝ) ^ (-(3 : ℝ)) ≤ distanceProduct (frequency n) u := by
  filter_upwards [hlarge] with n hn
  have hp : 0 < distanceProduct (frequency n) u :=
    distanceProduct_pos_of_coordinates (hnz _ (frequency_ne_zero n))
  have hm : OneDimensionalDiscrepancy.tupleNegativeHalfMomentAt (frequency n) u < momentThreshold n := by
    simpa [largeMoment] using hn
  rw [tupleMomentAt_eq_rpow_distanceProduct] at hm
  have hsqrt : distanceProduct (frequency n) u ^ (1 / 2 : ℝ) >
      (momentThreshold n)⁻¹ := by
    rw [Real.rpow_neg hp.le] at hm
    have hi := (inv_lt_inv₀ (momentThreshold_pos n)
      (inv_pos.mpr (Real.rpow_pos_of_pos hp _))).2 hm
    simpa using hi
  have hsquare := Real.rpow_lt_rpow (inv_nonneg.mpr (momentThreshold_pos n).le)
    hsqrt (by norm_num : (0 : ℝ) < 2)
  rw [← Real.rpow_mul hp.le] at hsquare
  have hpident : distanceProduct (frequency n) u ^ ((1 / 2 : ℝ) * 2) =
      distanceProduct (frequency n) u := by norm_num
  rw [hpident] at hsquare
  have hth : ((momentThreshold n)⁻¹) ^ ((2 : ℝ)) =
      (n + 1 : ℝ) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_mul (momentThreshold_pos n).le,
      momentThreshold, ← Real.rpow_mul (by positivity : 0 ≤ (n + 1 : ℝ))]
    norm_num
  rw [hth] at hsquare
  exact hsquare.le

private lemma exists_positive_uniform_factor (f : ℕ → ℝ) (hf : ∀ n, 0 < f n)
    (hevent : ∀ᶠ n in atTop, 1 ≤ f n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ f n := by
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  have hfinite_aux : ∀ N : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n < N, c ≤ f n := by
    intro M
    induction M with
    | zero => exact ⟨1, zero_lt_one, by simp⟩
    | succ M ih =>
        obtain ⟨c, hc, hcle⟩ := ih
        refine ⟨min c (f M), lt_min hc (hf M), ?_⟩
        intro n hn
        rw [Nat.lt_succ_iff] at hn
        rcases hn.lt_or_eq with hlt | rfl
        · exact (min_le_left _ _).trans (hcle n hlt)
        · exact min_le_right _ _
  obtain ⟨c, hc, hcle⟩ := hfinite_aux N
  refine ⟨min c 1, lt_min hc zero_lt_one, fun n ↦ ?_⟩
  by_cases hn : n < N
  · exact (min_le_left _ _).trans (hcle n hn)
  · exact (min_le_right _ _).trans (hN n (Nat.le_of_not_gt hn))

/-- For almost every tuple there is a positive constant giving a uniform
`h⁻³` lower bound at all positive integer frequencies. -/
theorem ae_exists_uniform_nat_product_lower (d : ℕ) :
    ∀ᵐ u ∂(tupleHaar d), ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c * (n + 1 : ℝ) ^ (-(3 : ℝ)) ≤ distanceProduct (frequency n) u := by
  filter_upwards [ae_eventually_not_largeMoment d,
    ae_forall_integerMultiple_ne_zero d] with u hlarge hnz
  have hevent := eventual_distanceProduct_lower hlarge hnz
  let f : ℕ → ℝ := fun n ↦
    distanceProduct (frequency n) u / (n + 1 : ℝ) ^ (-(3 : ℝ))
  have hf : ∀ n, 0 < f n := by
    intro n
    exact div_pos (distanceProduct_pos_of_coordinates (hnz _ (frequency_ne_zero n)))
      (Real.rpow_pos_of_pos (by positivity) _)
  have hevent' : ∀ᶠ n in atTop, 1 ≤ f n := by
    filter_upwards [hevent] with n hn
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < (n + 1 : ℝ)) _)).2
      (by simpa [f, mul_comm] using hn)
  obtain ⟨c, hc, hcu⟩ := exists_positive_uniform_factor f hf hevent'
  refine ⟨c, hc, fun n ↦ ?_⟩
  exact (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < (n + 1 : ℝ)) _)).mp
    (hcu n)

/-- A tuple of 32 generators with a uniform cubic product bound at every
nonzero integer frequency. -/
theorem exists_generators32_product_lower :
    ∃ (u : Fin 32 → Circle) (c : ℝ), 0 < c ∧
      ∀ h : ℤ, h ≠ 0 →
        c * (|h| : ℝ) ^ (-(3 : ℝ)) ≤ distanceProduct h u := by
  obtain ⟨u, c, hc, hu⟩ :=
    (ae_exists_uniform_nat_product_lower 32).exists
  refine ⟨u, c, hc, fun h hh ↦ ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg h
  · have hm : m ≠ 0 := by simpa using hh
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simpa [frequency, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)] using hu n
  · have hm : m ≠ 0 := by simpa using hh
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [distanceProduct_neg]
    convert hu n using 1
    rw [Int.cast_neg, Int.cast_natCast, Nat.cast_succ,
      abs_of_nonpos (by have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
    · simp
    · simp [frequency]

private lemma tupleHaar_eq_volume (d : ℕ) :
    tupleHaar d = (volume : Measure (Fin d → Circle)) := by
  rw [MeasureTheory.volume_pi]
  unfold tupleHaar OneDimensionalDiscrepancy.tupleHaar
  congr 1
  funext i
  symm
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

/-- Freeness holds almost everywhere for the same product Haar measure used
in the moment argument. -/
theorem ae_circleFree (d : ℕ) :
    ∀ᵐ u ∂(tupleHaar d), FreeTuple.CircleFree u := by
  rw [tupleHaar_eq_volume]
  exact FreeTuple.ae_free d

/-- A free tuple of 32 circle generators satisfying the uniform cubic
product lower bound at every nonzero integer frequency. -/
theorem exists_generators32_free_product_lower :
    ∃ (u : Fin 32 → Circle) (c : ℝ),
      FreeTuple.CircleFree u ∧ 0 < c ∧
      ∀ h : ℤ, h ≠ 0 →
        c * (|h| : ℝ) ^ (-(3 : ℝ)) ≤ distanceProduct h u := by
  have hae : ∀ᵐ u ∂(tupleHaar 32),
      FreeTuple.CircleFree u ∧
        ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
          c * (n + 1 : ℝ) ^ (-(3 : ℝ)) ≤ distanceProduct (frequency n) u :=
    (ae_circleFree 32).and (ae_exists_uniform_nat_product_lower 32)
  obtain ⟨u, hfree, c, hc, hu⟩ := hae.exists
  refine ⟨u, c, hfree, hc, fun h hh ↦ ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg h
  · have hm : m ≠ 0 := by simpa using hh
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simpa [frequency, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)] using hu n
  · have hm : m ≠ 0 := by simpa using hh
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [distanceProduct_neg]
    convert hu n using 1
    rw [Int.cast_neg, Int.cast_natCast, Nat.cast_succ,
      abs_of_nonpos (by have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
    · simp
    · simp [frequency]

/-- Two independent coordinate families, each free and each satisfying the
uniform cubic product bound.  This is the direct input used to build a
two-dimensional torus action. -/
theorem exists_two_generators32_free_product_lower :
    ∃ (u v : Fin 32 → Circle) (cu cv : ℝ),
      FreeTuple.CircleFree u ∧ FreeTuple.CircleFree v ∧
      0 < cu ∧ 0 < cv ∧
      (∀ h : ℤ, h ≠ 0 →
        cu * (|h| : ℝ) ^ (-(3 : ℝ)) ≤ distanceProduct h u) ∧
      (∀ h : ℤ, h ≠ 0 →
        cv * (|h| : ℝ) ^ (-(3 : ℝ)) ≤ distanceProduct h v) := by
  obtain ⟨u, cu, hufree, hcu, hu⟩ := exists_generators32_free_product_lower
  obtain ⟨v, cv, hvfree, hcv, hv⟩ := exists_generators32_free_product_lower
  exact ⟨u, v, cu, cv, hufree, hvfree, hcu, hcv, hu, hv⟩

end

end Erdos1124.DiophantineChoice
