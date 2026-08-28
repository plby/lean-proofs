/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file has been modified. Its copyright notice is retained below.

Copyright 2026 The Lean-Proofs Authors.
-/
import Wikipedia.VinogradovsTheorem.MajorArcApproximation
import Wikipedia.VinogradovsTheorem.SingularSeries
import Wikipedia.VinogradovsTheorem.VaughanMinorArc

/-!
# Qualitative major and minor arcs for Erdős Problem 471

This file proves the large-odd, quadratically positive von Mangoldt triple
estimate from the proved Bombieri--Vinogradov theorem and the proved
q-sensitive Vaughan estimate.
-/

namespace VinogradovsTheorem.Analytic

open scoped BigOperators Topology ArithmeticFunction.vonMangoldt
open Filter MeasureTheory

/-- Integer logarithmic scale.  Its use avoids rounding issues in all later
cutoffs while remaining comparable with the natural logarithm. -/
def logScale (n : ℕ) : ℕ := Erdos387.binaryLogScale n

/-- Polylogarithmic major-arc denominator cutoff. -/
def majorDenominatorCutoff (n : ℕ) : ℕ := logScale n ^ 20

/-- Dirichlet approximation cutoff.  The deliberately generous exponent
leaves ample room both for the major-arc AP error and for the truncated
singular-integral tail. -/
def dirichletCutoff (n : ℕ) : ℕ := n / logScale n ^ 100

theorem tendsto_logScale : Tendsto logScale atTop atTop := by
  have hlogb : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor := (tendsto_nat_floor_atTop (α := ℝ)).comp hlogb
  have hlog : Tendsto (fun n : ℕ ↦ Nat.log 2 n) atTop atTop := by
    convert hfloor using 1
    funext n
    change Nat.log 2 n = ⌊Real.logb 2 (n : ℝ)⌋₊
    simpa using (Real.natFloor_logb_natCast 2 n).symm
  change Tendsto (fun n : ℕ ↦ Nat.log 2 n + 1) atTop atTop
  simpa [Function.comp_def] using (tendsto_add_atTop_nat 1).comp hlog

theorem tendsto_majorDenominatorCutoff :
    Tendsto majorDenominatorCutoff atTop atTop := by
  exact (Filter.tendsto_pow_atTop (by norm_num : 20 ≠ 0)).comp tendsto_logScale

theorem eventually_four_logScale_pow_120_le :
    ∀ᶠ n : ℕ in atTop, 4 * logScale n ^ 120 ≤ n := by
  filter_upwards [Erdos387.eventually_binaryLogScale_pow_le_half 121,
    tendsto_logScale.eventually_ge_atTop 2] with n hn hL
  change logScale n ^ 121 ≤ n / 2 at hn
  have htwo : 2 * logScale n ^ 120 ≤ logScale n ^ 121 := by
    calc
      2 * logScale n ^ 120 ≤ logScale n * logScale n ^ 120 :=
        Nat.mul_le_mul_right _ hL
      _ = logScale n ^ 120 * logScale n := Nat.mul_comm _ _
      _ = logScale n ^ (120 + 1) := (pow_succ _ _).symm
      _ = logScale n ^ 121 := rfl
  have hhalf : 2 * logScale n ^ 120 ≤ n / 2 := htwo.trans hn
  calc
    4 * logScale n ^ 120 = 2 * (2 * logScale n ^ 120) := by
      rw [← Nat.mul_assoc]
    _ ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 hhalf
    _ = (n / 2) * 2 := by omega
    _ ≤ n := Nat.div_mul_le_self n 2

theorem eventually_n_le_two_dirichletCutoff_mul_logScale_pow_100 :
    ∀ᶠ n : ℕ in atTop,
      n ≤ 2 * dirichletCutoff n * logScale n ^ 100 := by
  filter_upwards [Erdos387.eventually_binaryLogScale_pow_le_half 100]
    with n hn
  let K := logScale n ^ 100
  have hKpos : 0 < K := pow_pos (Erdos387.binaryLogScale_pos n) _
  have hKn : K ≤ n := by
    change K ≤ n / 2 at hn
    exact hn.trans (Nat.div_le_self n 2)
  have hDpos : 0 < n / K := Nat.div_pos hKn hKpos
  have hdecomp := Nat.div_add_mod n K
  have hmod := Nat.mod_lt n hKpos
  have hKle : K ≤ K * (n / K) := Nat.le_mul_of_pos_right _ hDpos
  have hmain : n < 2 * (K * (n / K)) := by omega
  change n ≤ 2 * (n / K) * K
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmain.le

theorem dirichletCutoff_le (n : ℕ) : dirichletCutoff n ≤ n := by
  exact Nat.div_le_self _ _

theorem singularTerm_partial_sums_tendstoUniformly :
    TendstoUniformly
      (fun K : ℕ => fun n : ℕ =>
        ∑ q ∈ Finset.range K, singularTerm q n)
      (fun n : ℕ => ∑' q : ℕ, singularTerm q n) atTop := by
  exact tendstoUniformly_tsum_nat summable_uniform_singularMajorant
    (fun q n => norm_singularTerm_le_zero_frequency q n)

theorem eventually_uniform_singularTerm_tail {P : ℕ → ℕ}
    (hP : Tendsto P atTop atTop) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      ‖(∑ q ∈ Finset.range (P n), singularTerm q n) -
        (∑' q : ℕ, singularTerm q n)‖ < eps := by
  have h := (Metric.tendstoUniformly_iff.mp
    singularTerm_partial_sums_tendstoUniformly) eps heps
  filter_upwards [hP.eventually h] with n hn
  simpa [dist_eq_norm, norm_sub_rev] using hn n

/-- The circle-method integrand at target `n`. -/
noncomputable def integrand (n : ℕ) (α : ℝ) : ℂ :=
  (Vinogradov.vonMangoldtExpSum α n) ^ 3 * Vinogradov.negAddChar α n

/-- The linear-model integrand in the translated variable. -/
noncomputable def betaIntegrand (n : ℕ) (β : ℝ) : ℂ :=
  (Vinogradov.linearExpSum n β) ^ 3 * Vinogradov.negAddChar β n

/-- Symmetric local singular integral with arc scale `D`, separate from the
target `n`. -/
noncomputable def localBetaIntegral (D q n : ℕ) : ℂ :=
  ∫ β in Set.Ioo (-(1 / ((q : ℝ) * (D : ℝ)))) (1 / ((q : ℝ) * (D : ℝ))),
    betaIntegrand n β

/-- The model for `S_Λ(α,n)^3 e(-nα)` on the arc about `a/q`, with the
geometric arc scale `D` independent of the target `n`. -/
noncomputable def localMainIntegrand (n a q : ℕ) (α : ℝ) : ℂ :=
  (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
      (Nat.totient q : ℝ) : ℂ) *
        Vinogradov.linearExpSum n (α - Vinogradov.rationalCenter a q)) ^ 3) *
    Vinogradov.negAddChar α n

/-- The right-hand copy of the endpoint arc around `0 = 1` on the circle. -/
noncomputable def rightEndpointArc (D : ℕ) : Set ℝ :=
  Set.Ioc (1 - 1 / (D : ℝ)) 1

/-- The reduced rational centers form a finite set. -/
theorem majorArcCenters_finite (P : ℕ) :
    (Vinogradov.majorArcCenters P).Finite := by
  refine Set.Finite.subset
    ((Set.finite_Iic (P + 1)).prod (Set.finite_Iic (P + 1))) ?_
  rintro ⟨a, q⟩ ⟨hq, _, ha, _⟩
  exact ⟨(lt_of_lt_of_le ha hq).le.trans (Nat.le_succ _),
    hq.trans (Nat.le_succ _)⟩

/-- The endpoint center `(0,1)` has two pieces on the circle; every internal
center uses the usual clipped local major arc. -/
noncomputable def torusLocalArc (D : ℕ) (aq : ℕ × ℕ) : Set ℝ :=
  if aq = (0, 1) then
    Vinogradov.localMajorArcExplicit D 0 1 ∪ rightEndpointArc D
  else
    Vinogradov.localMajorArcExplicit D aq.1 aq.2

/-- Union of all major arcs, with the endpoint arc wrapped across `1`. -/
noncomputable def torusMajorArcs (D P : ℕ) : Set ℝ :=
  ⋃ aq ∈ (majorArcCenters_finite P).toFinset,
    torusLocalArc D aq

/-- Complementary minor arcs in the closed fundamental interval. -/
noncomputable def torusMinorArcs (D P : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 \ torusMajorArcs D P

theorem integrand_continuous (n : ℕ) : Continuous (integrand n) := by
  unfold integrand Vinogradov.vonMangoldtExpSum Vinogradov.addChar
    Vinogradov.negAddChar
  fun_prop

theorem betaIntegrand_periodic (n : ℕ) :
    Function.Periodic (betaIntegrand n) 1 := by
  intro β
  simp [betaIntegrand, Vinogradov.linearExpSum,
    Vinogradov.addChar_periodic, Vinogradov.negAddChar_periodic]

theorem betaIntegrand_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (betaIntegrand n) volume a b := by
  apply Continuous.intervalIntegrable
  unfold betaIntegrand Vinogradov.linearExpSum Vinogradov.addChar
    Vinogradov.negAddChar
  fun_prop

private lemma reduced_nat_fraction_eq_of_cross_mul_eq {a q b r : ℕ}
    (_hq : 0 < q) (hr : 0 < r)
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime b r)
    (h : a * r = b * q) :
    (a, q) = (b, r) := by
  have hq_dvd_r : q ∣ r := by
    apply hcop.symm.dvd_of_dvd_mul_left
    rw [h]
    exact Nat.dvd_mul_left q b
  have hr_dvd_q : r ∣ q := by
    apply hcop'.symm.dvd_of_dvd_mul_left
    rw [← h]
    exact Nat.dvd_mul_left r a
  have hqr : q = r := Nat.dvd_antisymm hq_dvd_r hr_dvd_q
  have ha : a = b := by
    apply Nat.eq_of_mul_eq_mul_right hr
    simpa [hqr] using h
  exact Prod.ext ha hqr

private lemma one_le_abs_cross_sub_of_reduced_ne {a q b r : ℕ}
    (hq : 0 < q) (hr : 0 < r)
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime b r)
    (hne : (a, q) ≠ (b, r)) :
    (1 : ℝ) ≤ |(a : ℝ) * (r : ℝ) - (b : ℝ) * (q : ℝ)| := by
  let z : ℤ := (a : ℤ) * (r : ℤ) - (b : ℤ) * (q : ℤ)
  have hz : z ≠ 0 := by
    intro hz0
    apply hne
    have hz0' : (a : ℤ) * (r : ℤ) = (b : ℤ) * (q : ℤ) := by
      simpa [z] using sub_eq_zero.mp hz0
    exact reduced_nat_fraction_eq_of_cross_mul_eq hq hr hcop hcop' (by
      exact_mod_cast hz0')
  have hge : (1 : ℤ) ≤ |z| := by
    have : (0 : ℤ) < |z| := abs_pos.mpr hz
    omega
  have hreal : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast hge
  simpa [z] using hreal

private lemma farey_distinct_centers_separation {a q b r : ℕ}
    (hq : 0 < q) (hr : 0 < r)
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime b r)
    (hne : (a, q) ≠ (b, r)) :
    (1 : ℝ) / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hnum := one_le_abs_cross_sub_of_reduced_ne hq hr hcop hcop' hne
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : (0 : ℝ) < (q : ℝ) * r := mul_pos hqR hrR
  calc
    (1 : ℝ) / ((q : ℝ) * r) ≤
        |(a : ℝ) * (r : ℝ) - (b : ℝ) * (q : ℝ)| / ((q : ℝ) * r) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = |((a : ℝ) * (r : ℝ) - (b : ℝ) * (q : ℝ)) /
          ((q : ℝ) * r)| := by rw [abs_div, abs_of_pos hden]
    _ = |(a : ℝ) / q - (b : ℝ) / r| := by
      congr 1
      rw [div_sub_div (a := (a : ℝ)) (b := (q : ℝ))
        (c := (b : ℝ)) (d := (r : ℝ))]
      ring
      · exact_mod_cast Nat.ne_of_gt hq
      · exact_mod_cast Nat.ne_of_gt hr

private lemma local_radius_sum_le_farey_bound {D q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqrD : q + r ≤ D) :
    (1 : ℝ) / ((q : ℝ) * D) + 1 / ((r : ℝ) * D) ≤
      1 / ((q : ℝ) * r) := by
  have hqD : q < D := lt_of_lt_of_le (Nat.lt_add_of_pos_right hr) hqrD
  have hD : 0 < D := lt_trans hq hqD
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hqrDR : (q : ℝ) + (r : ℝ) ≤ (D : ℝ) := by exact_mod_cast hqrD
  field_simp [hqR.ne', hrR.ne', hDR.ne', mul_ne_zero]
  nlinarith [hqR, hrR, hDR, hqrDR]

/-- Ordinary clipped local arcs are pairwise disjoint at Farey scale. -/
theorem localMajorArcExplicit_pairwise_disjoint
    {D P : ℕ} (hPD : 2 * P ≤ D) :
    Set.Pairwise (Vinogradov.majorArcCenters P)
      (Function.onFun Disjoint fun aq =>
        Vinogradov.localMajorArcExplicit D aq.1 aq.2) := by
  intro aq haq bq hbq hne
  rcases aq with ⟨a, q⟩
  rcases bq with ⟨b, r⟩
  change Disjoint (Vinogradov.localMajorArcExplicit D a q)
    (Vinogradov.localMajorArcExplicit D b r)
  rw [Set.disjoint_left]
  intro α hα hβ
  have hq := Vinogradov.majorArcCenters_q_pos haq
  have hr := Vinogradov.majorArcCenters_q_pos hbq
  have hqrD : q + r ≤ D := by
    have hqP := Vinogradov.majorArcCenters_q_le haq
    have hrP := Vinogradov.majorArcCenters_q_le hbq
    omega
  have hsep :
      (1 : ℝ) / ((q : ℝ) * r) ≤
        dist ((a : ℝ) / q) ((b : ℝ) / r) := by
    simpa [Real.dist_eq] using farey_distinct_centers_separation hq hr
      (Vinogradov.majorArcCenters_coprime haq)
      (Vinogradov.majorArcCenters_coprime hbq) hne
  have hαa : dist ((a : ℝ) / q) α < 1 / ((q : ℝ) * D) := by
    simpa [Real.dist_eq, abs_sub_comm] using hα.2
  have hαb : dist α ((b : ℝ) / r) < 1 / ((r : ℝ) * D) := by
    simpa [Real.dist_eq] using hβ.2
  have hdist : dist ((a : ℝ) / q) ((b : ℝ) / r) <
      1 / ((q : ℝ) * D) + 1 / ((r : ℝ) * D) :=
    lt_of_le_of_lt (dist_triangle _ α _) (add_lt_add hαa hαb)
  exact (not_lt_of_ge hsep)
    (hdist.trans_le (local_radius_sum_le_farey_bound hq hr hqrD))

private lemma zero_numerator_center_eq_endpoint {P q : ℕ}
    (h : (0, q) ∈ Vinogradov.majorArcCenters P) : q = 1 := by
  exact (Nat.coprime_zero_left q).mp (Vinogradov.majorArcCenters_coprime h)

/-- The wrapped right endpoint is disjoint from every internal local arc. -/
theorem rightEndpointArc_disjoint_localMajorArc
    {D P a q : ℕ} (hP : 1 ≤ P) (hDP : 2 * P ≤ D)
    (hcenter : (a, q) ∈ Vinogradov.majorArcCenters P)
    (hne : (a, q) ≠ (0, 1)) :
    Disjoint (rightEndpointArc D)
      (Vinogradov.localMajorArcExplicit D a q) := by
  rw [Set.disjoint_left]
  intro α hright hlocal
  have hq : 0 < q := Vinogradov.majorArcCenters_q_pos hcenter
  have hqP : q ≤ P := Vinogradov.majorArcCenters_q_le hcenter
  have haPos : 0 < a := by
    by_contra ha
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    have hq1 := zero_numerator_center_eq_endpoint hcenter
    exact hne (by simp [hq1])
  have haq : a < q := Vinogradov.majorArcCenters_a_lt_q hcenter
  have hD : 0 < D := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have haqR0 : (a : ℝ) < (q : ℝ) := by exact_mod_cast haq
  have haqR : (a : ℝ) ≤ (q : ℝ) - 1 := by
    have : a ≤ q - 1 := by omega
    have hcast : (a : ℝ) ≤ (q - 1 : ℕ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega : 1 ≤ q)] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hqD : q + 1 ≤ D := by omega
  have hlower : 1 - 1 / (D : ℝ) < α := hright.1
  have habs : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * D) := hlocal.2
  have hupp : α < (a : ℝ) / q + 1 / ((q : ℝ) * D) := by
    have := (abs_lt.mp habs).2
    linarith
  have hcenterUpper :
      (a : ℝ) / q + 1 / ((q : ℝ) * D) ≤ 1 - 1 / (D : ℝ) := by
    field_simp [hqR.ne', hDR.ne', mul_ne_zero]
    nlinarith [show (q : ℝ) + 1 ≤ D by exact_mod_cast hqD]
  linarith

theorem endpointPieces_disjoint {D : ℕ} (hD : 2 ≤ D) :
    Disjoint (Vinogradov.localMajorArcExplicit D 0 1)
      (rightEndpointArc D) := by
  rw [Set.disjoint_left]
  intro α hleft hright
  have hDR : (0 : ℝ) < D := by positivity
  have hlower : 1 - 1 / (D : ℝ) < α := hright.1
  have hupper : α < 1 / (D : ℝ) := by
    have habs : |α| < 1 / (D : ℝ) := by
      simpa [Vinogradov.localMajorArcExplicit] using hleft.2
    exact (abs_lt.mp habs).2
  have hhalf : 2 ≤ (D : ℝ) := by exact_mod_cast hD
  have hinv : 2 * (1 / (D : ℝ)) ≤ 1 := by
    simpa [one_div] using
      ((mul_inv_le_iff₀ hDR).2 (by simpa using hhalf) :
        (2 : ℝ) * (D : ℝ)⁻¹ ≤ 1)
  linarith

/-- The wrapped local arcs are pairwise disjoint. -/
theorem torusLocalArc_pairwise_disjoint
    {D P : ℕ} (hP : 1 ≤ P) (hPD : 2 * P ≤ D) :
    Set.Pairwise (Vinogradov.majorArcCenters P)
      (Function.onFun Disjoint (torusLocalArc D)) := by
  intro aq haq bq hbq hne
  have hplain := localMajorArcExplicit_pairwise_disjoint hPD haq hbq hne
  by_cases haq0 : aq = (0, 1)
  · subst aq
    have hbq0 : bq ≠ (0, 1) := by
      intro h
      exact hne h.symm
    rcases bq with ⟨b, r⟩
    change Disjoint (torusLocalArc D (0, 1)) (torusLocalArc D (b, r))
    rw [torusLocalArc, if_pos rfl, torusLocalArc, if_neg hbq0]
    exact Disjoint.union_left hplain
      (rightEndpointArc_disjoint_localMajorArc hP hPD hbq hbq0).symm.symm
  · by_cases hbq0 : bq = (0, 1)
    · subst bq
      rcases aq with ⟨a, q⟩
      change Disjoint (torusLocalArc D (a, q)) (torusLocalArc D (0, 1))
      rw [torusLocalArc, if_neg haq0, torusLocalArc, if_pos rfl]
      exact Disjoint.union_right hplain
        (rightEndpointArc_disjoint_localMajorArc hP hPD haq haq0).symm
    · rcases aq with ⟨a, q⟩
      rcases bq with ⟨b, r⟩
      change Disjoint (torusLocalArc D (a, q)) (torusLocalArc D (b, r))
      simpa [torusLocalArc, haq0, hbq0] using hplain

theorem rightEndpointArc_measurableSet (D : ℕ) :
    MeasurableSet (rightEndpointArc D) := measurableSet_Ioc

theorem torusLocalArc_measurableSet (D : ℕ) (aq : ℕ × ℕ) :
    MeasurableSet (torusLocalArc D aq) := by
  by_cases h : aq = (0, 1)
  · subst aq
    simp only [torusLocalArc, if_pos rfl]
    exact (Vinogradov.localMajorArcExplicit_measurableSet D 0 1).union
      (rightEndpointArc_measurableSet D)
  · simp only [torusLocalArc, if_neg h]
    exact Vinogradov.localMajorArcExplicit_measurableSet D aq.1 aq.2

theorem rightEndpointArc_subset_Icc (D : ℕ) :
    rightEndpointArc D ⊆ Set.Icc (0 : ℝ) 1 := by
  intro α hα
  refine ⟨?_, hα.2⟩
  by_cases hD : D = 0
  · subst D
    simp [rightEndpointArc] at hα
  · have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hD
    have hDpos : (0 : ℝ) < D := by exact_mod_cast (Nat.pos_of_ne_zero hD)
    have hinv : 1 / (D : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hDpos).2
      norm_num
      exact_mod_cast hD1
    have hlo : 1 - 1 / (D : ℝ) < α := by
      exact hα.1
    linarith

theorem torusLocalArc_subset_Icc (D : ℕ) (aq : ℕ × ℕ) :
    torusLocalArc D aq ⊆ Set.Icc (0 : ℝ) 1 := by
  by_cases h : aq = (0, 1)
  · subst aq
    simp only [torusLocalArc, if_pos rfl]
    exact Set.union_subset
      (Vinogradov.localMajorArcExplicit_subset_Icc D 0 1)
      (rightEndpointArc_subset_Icc D)
  · simpa [torusLocalArc, h] using
      (Vinogradov.localMajorArcExplicit_subset_Icc D aq.1 aq.2)

/-- Rational-window description used by Dirichlet approximation.  Allowing
`a = q` is precisely what represents the wrapped endpoint near `1`. -/
def InWrappedMajorArc (D P : ℕ) (α : ℝ) : Prop :=
  ∃ a q : ℕ, 0 < q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
    |α - (a : ℝ) / q| < 1 / ((q : ℝ) * D)

theorem mem_torusMajorArcs_of_inWrappedMajor
    {D P : ℕ} {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (h : InWrappedMajorArc D P α) :
    α ∈ torusMajorArcs D P := by
  classical
  rcases h with ⟨a, q, hq, hqP, haq, hcop, hdist⟩
  by_cases halt : a < q
  · have hc : (a, q) ∈ Vinogradov.majorArcCenters P :=
      ⟨hqP, hq.ne', halt, hcop⟩
    rw [torusMajorArcs]
    simp only [Set.mem_iUnion]
    refine ⟨(a, q), ?_, ?_⟩
    · exact (Set.Finite.mem_toFinset (majorArcCenters_finite P)).2 hc
    · by_cases he : (a, q) = (0, 1)
      · have ha0 : a = 0 := congrArg Prod.fst he
        have hq1 : q = 1 := congrArg Prod.snd he
        subst a
        subst q
        simp only [torusLocalArc, if_pos rfl, Set.mem_union]
        exact Or.inl ⟨hα, by simpa using hdist⟩
      · simp only [torusLocalArc, if_neg he]
        exact ⟨hα, hdist⟩
  · have haeq : a = q := by omega
    subst a
    have hq1 : q = 1 := by
      simpa using hcop
    subst q
    have hc : (0, 1) ∈ Vinogradov.majorArcCenters P := by
      exact Vinogradov.zero_one_mem_majorArcCenters (by omega)
    rw [torusMajorArcs]
    simp only [Set.mem_iUnion]
    refine ⟨(0, 1),
      (Set.Finite.mem_toFinset (majorArcCenters_finite P)).2 hc, ?_⟩
    simp only [torusLocalArc, if_pos rfl, Set.mem_union]
    right
    refine ⟨?_, hα.2⟩
    have := (abs_lt.mp hdist).1
    simp only [Nat.cast_one, one_mul] at this
    linarith

/-- Outside the wrapped major arcs, Dirichlet approximation supplies a
reduced fraction whose denominator lies strictly above the major cutoff. -/
theorem exists_reduced_approximant_of_mem_torusMinor
    {D P : ℕ} (hD : 0 < D) (hP : 1 ≤ P) {α : ℝ}
    (hα : α ∈ torusMinorArcs D P) :
    ∃ a q : ℕ, 2 ≤ q ∧ P < q ∧ q ≤ D ∧ a < q ∧ a.Coprime q ∧
      |α - (a : ℝ) / q| < 1 / ((q : ℝ) * D) := by
  have hminor : ¬ InWrappedMajorArc D P α := by
    intro h
    exact hα.2 (mem_torusMajorArcs_of_inWrappedMajor hα.1 h)
  obtain ⟨c, hcdist, hcden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hD
  set q : ℕ := c.den with hqdef
  set x : ℤ := c.num with hxdef
  have hq0 : 0 < q := c.pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hcast : (c : ℝ) = (x : ℝ) / (q : ℝ) := by
    rw [hxdef, hqdef, Rat.cast_def]
  have hwin : |α - (x : ℝ) / (q : ℝ)| ≤
      1 / (((D : ℝ) + 1) * q) := by
    rw [← hcast]
    exact_mod_cast hcdist
  have hcop : x.natAbs.Coprime q := c.reduced
  have hqD : q ≤ D := hcden
  have hstrict : 1 / (((D : ℝ) + 1) * q) <
      1 / ((q : ℝ) * D) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [hqR, hDR]
  have hsmall : 1 / (((D : ℝ) + 1) * q) < 1 / (q : ℝ) := by
    apply one_div_lt_one_div_of_lt hqR
    nlinarith [hqR, hDR]
  have hx0 : 0 ≤ x := by
    by_contra hxneg
    push Not at hxneg
    have hx1 : (x : ℝ) ≤ -1 := by exact_mod_cast (by omega : x ≤ -1)
    have hgap : 1 / (q : ℝ) ≤ α - (x : ℝ) / q := by
      have hkey : (1 + (x : ℝ)) / q ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hqR.le
      have : 1 / (q : ℝ) + (x : ℝ) / q ≤ α := by
        calc
          _ = (1 + (x : ℝ)) / q := by ring
          _ ≤ 0 := hkey
          _ ≤ α := hα.1.1
      linarith
    have : 1 / (q : ℝ) ≤ |α - (x : ℝ) / q| :=
      hgap.trans (le_abs_self _)
    linarith
  have hxq : x ≤ (q : ℤ) := by
    by_contra hxgt
    push Not at hxgt
    have hx1 : (q : ℝ) + 1 ≤ (x : ℝ) := by
      exact_mod_cast (by omega : (q : ℤ) + 1 ≤ x)
    have hgap : 1 / (q : ℝ) ≤ (x : ℝ) / q - α := by
      have hxy : 1 + 1 / (q : ℝ) ≤ (x : ℝ) / q := by
        rw [le_div_iff₀ hqR]
        field_simp
        linarith
      linarith [hα.1.2]
    have : 1 / (q : ℝ) ≤ |α - (x : ℝ) / q| := by
      rw [abs_sub_comm]
      exact hgap.trans (le_abs_self _)
    linarith
  set a : ℕ := x.toNat with hadef
  have haR : (a : ℝ) = (x : ℝ) := by
    rw [hadef]
    exact_mod_cast Int.toNat_of_nonneg hx0
  have haq : a ≤ q := by omega
  have hacop : a.Coprime q := by
    have haabs : a = x.natAbs := by omega
    simpa [haabs] using hcop
  have hdist : |α - (a : ℝ) / q| < 1 / ((q : ℝ) * D) := by
    rw [haR]
    exact hwin.trans_lt hstrict
  have hqP : P < q := by
    by_contra h
    push Not at h
    exact hminor ⟨a, q, hq0, h, haq, hacop, hdist⟩
  have hq2 : 2 ≤ q := by omega
  have halt : a < q := by
    by_contra h
    have haeq : a = q := by omega
    have hq1 : q = 1 := by
      rw [haeq, Nat.coprime_self] at hacop
      exact hacop
    omega
  exact ⟨a, q, hq2, hqP, hqD, halt, hacop, hdist⟩

lemma star_vonMangoldtExpSum_eq_negAddChar_sum (α : ℝ) (N : ℕ) :
    starRingEnd ℂ (Vinogradov.vonMangoldtExpSum α N) =
      ∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℂ) * Vinogradov.negAddChar α n := by
  unfold Vinogradov.vonMangoldtExpSum
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_mul, Complex.conj_ofReal, Vinogradov.conj_addChar_eq_negAddChar]

lemma norm_sq_vonMangoldtExpSum_eq_complex (α : ℝ) (N : ℕ) :
    (((‖Vinogradov.vonMangoldtExpSum α N‖ : ℝ) ^ 2 : ℝ) : ℂ) =
      Vinogradov.vonMangoldtExpSum α N *
        ∑ n ∈ Finset.range (N + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) * Vinogradov.negAddChar α n := by
  rw [← star_vonMangoldtExpSum_eq_negAddChar_sum]
  rw [mul_comm _ (starRingEnd ℂ _)]
  rw [← Complex.normSq_eq_conj_mul_self]
  norm_cast
  rw [Complex.normSq_eq_norm_sq]

/-- Exact Parseval identity for the hard-cutoff von Mangoldt sum. -/
theorem integral_norm_vonMangoldtExpSum_sq (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
        ‖Vinogradov.vonMangoldtExpSum α N‖ ^ 2) =
      ∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 := by
  have hkernel := Vinogradov.integral_vonMangoldtExpSum_mul_neg_kernel N
  have hlhs_eq :
      (∫ α in Set.Icc (0 : ℝ) 1,
          Vinogradov.vonMangoldtExpSum α N *
            ∑ n ∈ Finset.range (N + 1),
              (ArithmeticFunction.vonMangoldt n : ℂ) *
                Vinogradov.negAddChar α n) =
      ∫ α in Set.Icc (0 : ℝ) 1,
          (((‖Vinogradov.vonMangoldtExpSum α N‖ : ℝ) ^ 2 : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun α _ => ?_)
    rw [norm_sq_vonMangoldtExpSum_eq_complex]
  have hrhs_eq :
      (∑ n ∈ Finset.range (N + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (ArithmeticFunction.vonMangoldt n : ℂ)) =
      ((∑ n ∈ Finset.range (N + 1),
          (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [sq]
  rw [hlhs_eq, hrhs_eq] at hkernel
  rw [show (∫ α in Set.Icc (0 : ℝ) 1,
        (((‖Vinogradov.vonMangoldtExpSum α N‖ : ℝ) ^ 2 : ℝ) : ℂ)) =
        (((∫ α in Set.Icc (0 : ℝ) 1,
            ((‖Vinogradov.vonMangoldtExpSum α N‖ : ℝ) ^ 2)) : ℝ) : ℂ) from
      integral_complex_ofReal] at hkernel
  exact_mod_cast hkernel

theorem sum_vonMangoldt_sq_le (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2) ≤
      (N + 1 : ℕ) * Real.log (N + 1 : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ _n ∈ Finset.range (N + 1), Real.log (N + 1 : ℝ) ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hnle : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hnonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hlelogn : (ArithmeticFunction.vonMangoldt n : ℝ) ≤
          Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_le_log
      have hlogmono : Real.log (n : ℝ) ≤ Real.log (N + 1 : ℝ) := by
        by_cases hn0 : n = 0
        · subst n
          simp
          exact Real.log_nonneg (by norm_num)
        · exact Real.log_le_log (by positivity)
            (by exact_mod_cast (show n ≤ N + 1 by omega))
      nlinarith [sq_nonneg ((ArithmeticFunction.vonMangoldt n : ℝ)),
        sq_nonneg (Real.log (N + 1 : ℝ))]
    _ = _ := by simp [nsmul_eq_mul]

theorem vonMangoldtExpSum_eq_lambdaSubLog_add_log (n : ℕ) (α : ℝ) :
    Vinogradov.vonMangoldtExpSum α n =
      Vinogradov.arithmeticExpSum
          (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α +
        Vinogradov.arithmeticExpSum ArithmeticFunction.log n α := by
  unfold Vinogradov.vonMangoldtExpSum Vinogradov.arithmeticExpSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [MathExtras.Helfgott.arithmeticFunction_sub_apply]
  push_cast
  ring

/-- A point on the minor arcs has a Vaughan denominator in the saving range,
and hence an explicit uniform bound depending only on the two cutoffs. -/
theorem norm_vonMangoldtExpSum_minor_le
    {n D P : ℕ} {α : ℝ}
    (hn32 : 32 ≤ n) (hD : 0 < D) (hP : 1 ≤ P) (hDn : D ≤ n)
    (hD35 : 4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (D : ℝ))
    (hV : 2 * (MathExtras.Helfgott.vaughanCutoff n *
        MathExtras.Helfgott.vaughanCutoff n) ≤ D)
    (hα : α ∈ torusMinorArcs D P) :
    ‖Vinogradov.vonMangoldtExpSum α n‖ ≤
      2304 * (((n : ℝ) / Real.sqrt (P : ℝ) +
          (n : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((D : ℝ) * n)) * Real.log (n : ℝ) ^ 4) +
        2 * (D : ℝ) * Real.log (n : ℝ) := by
  obtain ⟨a, q, hq2, hPq, hqD, haq, hcop, hdist⟩ :=
    exists_reduced_approximant_of_mem_torusMinor hD hP hα
  have hsub := MathExtras.Helfgott.lambdaSubLog_envelope_at
    n a q D α hn32 hq2 hqD hDn haq hcop hdist hD35 hV
  have hlog := MathExtras.Helfgott.norm_log_expSum_le_of_center_at
    n a q D α hq2 (by omega) hcop hdist
  rw [vonMangoldtExpSum_eq_lambdaSubLog_add_log]
  calc
    ‖Vinogradov.arithmeticExpSum
          (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α +
        Vinogradov.arithmeticExpSum ArithmeticFunction.log n α‖ ≤
        ‖Vinogradov.arithmeticExpSum
          (ArithmeticFunction.vonMangoldt - ArithmeticFunction.log) n α‖ +
        ‖Vinogradov.arithmeticExpSum ArithmeticFunction.log n α‖ :=
      norm_add_le _ _
    _ ≤ 2304 * MathExtras.Helfgott.hardCutoffVaughanTypeIIVinogradovEnvelope n q +
        2 * (q : ℝ) * Real.log (n : ℝ) := add_le_add hsub hlog
    _ ≤ 2304 * (((n : ℝ) / Real.sqrt (P : ℝ) +
          (n : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt ((D : ℝ) * n)) * Real.log (n : ℝ) ^ 4) +
        2 * (D : ℝ) * Real.log (n : ℝ) := by
      unfold MathExtras.Helfgott.hardCutoffVaughanTypeIIVinogradovEnvelope
      have hPpos : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
      have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      have hPqR : (P : ℝ) ≤ q := by exact_mod_cast (Nat.le_of_lt hPq)
      have hqDR : (q : ℝ) ≤ D := by exact_mod_cast hqD
      have hsqrtP : Real.sqrt (P : ℝ) ≤ Real.sqrt (q : ℝ) :=
        Real.sqrt_le_sqrt hPqR
      have hfirst : (n : ℝ) / Real.sqrt (q : ℝ) ≤
          (n : ℝ) / Real.sqrt (P : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity)
          (Real.sqrt_pos.mpr hPpos) hsqrtP
      have hlast : Real.sqrt ((q : ℝ) * n) ≤ Real.sqrt ((D : ℝ) * n) := by
        exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hqDR (by positivity))
      have hlog0 : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      have henv0 : 0 ≤ Real.log (n : ℝ) ^ 4 := by positivity
      have henv :
          ((n : ℝ) / Real.sqrt (q : ℝ) + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((q : ℝ) * n)) * Real.log (n : ℝ) ^ 4 ≤
            ((n : ℝ) / Real.sqrt (P : ℝ) + (n : ℝ) ^ ((4 : ℝ) / 5) +
              Real.sqrt ((D : ℝ) * n)) * Real.log (n : ℝ) ^ 4 := by
        gcongr
      have hlogterm : 2 * (q : ℝ) * Real.log (n : ℝ) ≤
          2 * (D : ℝ) * Real.log (n : ℝ) := by
        gcongr
      gcongr

/-- The shifted beta window corresponding to a clipped local arc. -/
noncomputable def localBetaWindow (D a q : ℕ) : Set ℝ :=
  {β | Vinogradov.rationalCenter a q + β ∈ Set.Icc (0 : ℝ) 1 ∧
    |β| < Vinogradov.majorArcRadius D q}

theorem localBetaWindow_measurableSet (D a q : ℕ) :
    MeasurableSet (localBetaWindow D a q) := by
  unfold localBetaWindow
  exact (measurableSet_Icc.preimage
      ((continuous_const.add continuous_id).measurable)).inter
    ((isOpen_lt continuous_abs continuous_const).measurableSet)

theorem localBetaWindow_eq_Ioo_of_internal_center
    {D a q : ℕ} (ha : 0 < a) (haq : a < q) (hD : 1 ≤ D) :
    localBetaWindow D a q =
      Set.Ioo (-(Vinogradov.majorArcRadius D q))
        (Vinogradov.majorArcRadius D q) := by
  ext β
  constructor
  · intro hβ
    exact abs_lt.mp hβ.2
  · intro hβ
    rcases hβ with ⟨hβleft, hβright⟩
    refine ⟨?_, abs_lt.mpr ⟨hβleft, hβright⟩⟩
    have hq : 0 < q := lt_of_lt_of_le ha haq.le
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hDR : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hleft : Vinogradov.majorArcRadius D q ≤
        Vinogradov.rationalCenter a q := by
      unfold Vinogradov.majorArcRadius Vinogradov.rationalCenter
      field_simp [hqR.ne', hDR.ne']
      nlinarith
    have haq1 : a + 1 ≤ q := by omega
    have hright : Vinogradov.rationalCenter a q +
        Vinogradov.majorArcRadius D q ≤ 1 := by
      unfold Vinogradov.majorArcRadius Vinogradov.rationalCenter
      have haqR : (a : ℝ) + 1 ≤ q := by exact_mod_cast haq1
      field_simp [hqR.ne', hDR.ne']
      nlinarith
    constructor
    · linarith
    · linarith

theorem localMajorArcExplicit_eq_image_localBetaWindow (D a q : ℕ) :
    Vinogradov.localMajorArcExplicit D a q =
      (fun β : ℝ => Vinogradov.rationalCenter a q + β) ''
        localBetaWindow D a q := by
  ext α
  constructor
  · intro hα
    refine ⟨α - Vinogradov.rationalCenter a q, ?_, by ring⟩
    refine ⟨by simpa [localBetaWindow] using hα.1, ?_⟩
    have hclose : |α - Vinogradov.rationalCenter a q| <
        Vinogradov.majorArcRadius D q := by
      simpa [Vinogradov.rationalCenter, Vinogradov.majorArcRadius] using hα.2
    simpa [localBetaWindow] using hclose
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨hβ.1, ?_⟩
    have hsub : Vinogradov.rationalCenter a q + β -
        (a : ℝ) / (q : ℝ) = β := by simp [Vinogradov.rationalCenter]
    simpa [Vinogradov.majorArcRadius, hsub] using hβ.2

theorem integral_localMajorArcExplicit_eq_shifted_betaWindow
    (D a q : ℕ) (f : ℝ → ℂ) :
    (∫ α in Vinogradov.localMajorArcExplicit D a q, f α) =
      ∫ β in localBetaWindow D a q,
        f (Vinogradov.rationalCenter a q + β) := by
  rw [localMajorArcExplicit_eq_image_localBetaWindow]
  exact MeasurePreserving.setIntegral_image_emb
    (measurePreserving_add_left volume (Vinogradov.rationalCenter a q))
    ((Homeomorph.addLeft
      (Vinogradov.rationalCenter a q)).isClosedEmbedding.measurableEmbedding)
    f (localBetaWindow D a q)

theorem negAddChar_add (x y : ℝ) (n : ℕ) :
    Vinogradov.negAddChar (x + y) n =
      Vinogradov.negAddChar x n * Vinogradov.negAddChar y n := by
  unfold Vinogradov.negAddChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Arithmetic coefficient attached to one reduced center. -/
noncomputable def localMainCenterCoeff (n : ℕ) (aq : ℕ × ℕ) : ℂ :=
  (((((ArithmeticFunction.moebius aq.2 : ℤ) : ℝ) ^ 3) /
      (Nat.totient aq.2 : ℝ) ^ 3 : ℝ) : ℂ) *
    Vinogradov.negAddChar
      (Vinogradov.rationalCenter aq.1 aq.2) n

theorem localMainIntegrand_shifted_eq
    (n a q : ℕ) (β : ℝ) :
    localMainIntegrand n a q (Vinogradov.rationalCenter a q + β) =
      localMainCenterCoeff n (a, q) * betaIntegrand n β := by
  unfold localMainIntegrand localMainCenterCoeff betaIntegrand
  rw [negAddChar_add]
  have hsub : Vinogradov.rationalCenter a q + β -
      Vinogradov.rationalCenter a q = β := by ring
  rw [hsub]
  have hcoeff :
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
        (Nat.totient q : ℝ) : ℂ)) ^ 3) =
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 3) /
        (Nat.totient q : ℝ) ^ 3 : ℝ) : ℂ) := by
    ring_nf
    norm_num
  rw [mul_pow, hcoeff]
  ring

theorem localMainIntegral_internal
    {D n a q : ℕ} (ha : 0 < a) (haq : a < q) (hD : 1 ≤ D) :
    (∫ α in Vinogradov.localMajorArcExplicit D a q,
        localMainIntegrand n a q α) =
      localMainCenterCoeff n (a, q) * localBetaIntegral D q n := by
  rw [integral_localMajorArcExplicit_eq_shifted_betaWindow]
  rw [setIntegral_congr_fun (localBetaWindow_measurableSet D a q)
    (fun β _ => localMainIntegrand_shifted_eq n a q β)]
  rw [integral_const_mul]
  rw [localBetaWindow_eq_Ioo_of_internal_center ha haq hD]
  simp only [localBetaIntegral, Vinogradov.majorArcRadius]

theorem localMainIntegrand_zero_one_eq (n : ℕ) (α : ℝ) :
    localMainIntegrand n 0 1 α = betaIntegrand n α := by
  unfold localMainIntegrand betaIntegrand
  simp [Vinogradov.rationalCenter]

theorem localMainIntegrand_continuous (n a q : ℕ) :
    Continuous (localMainIntegrand n a q) := by
  unfold localMainIntegrand Vinogradov.linearExpSum Vinogradov.addChar
    Vinogradov.negAddChar
  fun_prop

theorem localBetaIntegral_eq_interval
    {D q n : ℕ} (hD : 0 < D) (hq : 0 < q) :
    localBetaIntegral D q n =
      ∫ β in (-(1 / ((q : ℝ) * (D : ℝ))))..
        (1 / ((q : ℝ) * (D : ℝ))), betaIntegrand n β := by
  have hr : 0 ≤ 1 / ((q : ℝ) * (D : ℝ)) := by positivity
  unfold localBetaIntegral
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]

theorem localMainIntegral_left_endpoint_eq_interval
    {D n : ℕ} (hD : 1 ≤ D) :
    (∫ α in Vinogradov.localMajorArcExplicit D 0 1,
        localMainIntegrand n 0 1 α) =
      ∫ α in (0 : ℝ)..(1 / (D : ℝ)), betaIntegrand n α := by
  let r : ℝ := 1 / (D : ℝ)
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : 0 < (D : ℝ) := zero_lt_one.trans_le hDR
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrle : r ≤ 1 := by
    simpa [r] using one_div_le_one_div_of_le zero_lt_one hDR
  have hset : Vinogradov.localMajorArcExplicit D 0 1 =
      Set.Ico (0 : ℝ) r := by
    ext α
    constructor
    · rintro ⟨⟨hα0, _⟩, hclose⟩
      have hc : |α| < r := by
        simpa [Vinogradov.rationalCenter, r] using hclose
      rw [abs_of_nonneg hα0] at hc
      exact ⟨hα0, hc⟩
    · rintro ⟨hα0, hαr⟩
      refine ⟨⟨hα0, (le_of_lt hαr).trans hrle⟩, ?_⟩
      have hc : |α| < r := by rwa [abs_of_nonneg hα0]
      simpa [Vinogradov.rationalCenter, r] using hc
  calc
    (∫ α in Vinogradov.localMajorArcExplicit D 0 1,
        localMainIntegrand n 0 1 α) =
        ∫ α in Set.Ico (0 : ℝ) r, betaIntegrand n α := by
      rw [hset]
      exact setIntegral_congr_fun measurableSet_Ico
        (fun α _ => localMainIntegrand_zero_one_eq n α)
    _ = ∫ α in Set.Ioo (0 : ℝ) r, betaIntegrand n α := by
      rw [integral_Ico_eq_integral_Ioo]
    _ = ∫ α in (0 : ℝ)..r, betaIntegrand n α := by
      rw [intervalIntegral.integral_of_le hrpos.le, integral_Ioc_eq_integral_Ioo]
    _ = ∫ α in (0 : ℝ)..(1 / (D : ℝ)), betaIntegrand n α := by rfl

theorem localMainIntegral_right_endpoint_eq_interval
    {D n : ℕ} (hD : 1 ≤ D) :
    (∫ α in rightEndpointArc D, localMainIntegrand n 0 1 α) =
      ∫ β in (-(1 / (D : ℝ)))..(0 : ℝ), betaIntegrand n β := by
  let r : ℝ := 1 / (D : ℝ)
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hset : rightEndpointArc D = Set.Ioc (1 - r) 1 := by rfl
  have hright :
      (∫ α in rightEndpointArc D, localMainIntegrand n 0 1 α) =
        ∫ α in (1 - r)..1, betaIntegrand n α := by
    rw [hset]
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun α _ => localMainIntegrand_zero_one_eq n α)]
    rw [intervalIntegral.integral_of_le (by linarith)]
  have hshift :
      (∫ β in (-r)..(0 : ℝ), betaIntegrand n β) =
        ∫ α in (1 - r)..1, betaIntegrand n α := by
    calc
      (∫ β in (-r)..(0 : ℝ), betaIntegrand n β) =
          ∫ β in (-r)..(0 : ℝ), betaIntegrand n (β + 1) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with β _hβ
        exact (betaIntegrand_periodic n β).symm
      _ = ∫ α in (-r) + 1..(0 : ℝ) + 1, betaIntegrand n α := by
        rw [intervalIntegral.integral_comp_add_right]
      _ = ∫ α in (1 - r)..1, betaIntegrand n α := by
        congr 1 <;> ring
  rw [hright, hshift]

/-- The two endpoint pieces together supply the full symmetric `q=1`
beta window. -/
theorem localMainIntegral_endpoint
    {D n : ℕ} (hD : 2 ≤ D) :
    (∫ α in torusLocalArc D (0, 1), localMainIntegrand n 0 1 α) =
      localBetaIntegral D 1 n := by
  have hD1 : 1 ≤ D := by omega
  have hcont := localMainIntegrand_continuous n 0 1
  have hleftInt : IntegrableOn (localMainIntegrand n 0 1)
      (Vinogradov.localMajorArcExplicit D 0 1) :=
    (hcont.integrableOn_Icc).mono_set
      (Vinogradov.localMajorArcExplicit_subset_Icc D 0 1)
  have hrightInt : IntegrableOn (localMainIntegrand n 0 1)
      (rightEndpointArc D) :=
    (hcont.integrableOn_Icc).mono_set (rightEndpointArc_subset_Icc D)
  have hsplit :
      (∫ β in (-(1 / (D : ℝ)))..(1 / (D : ℝ)), betaIntegrand n β) =
        (∫ β in (-(1 / (D : ℝ)))..(0 : ℝ), betaIntegrand n β) +
          ∫ β in (0 : ℝ)..(1 / (D : ℝ)), betaIntegrand n β := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (betaIntegrand_intervalIntegrable n (-(1 / (D : ℝ))) 0)
      (betaIntegrand_intervalIntegrable n 0 (1 / (D : ℝ)))]
  rw [torusLocalArc, if_pos rfl]
  rw [setIntegral_union (endpointPieces_disjoint hD)
    (rightEndpointArc_measurableSet D) hleftInt hrightInt]
  rw [localMainIntegral_left_endpoint_eq_interval hD1,
    localMainIntegral_right_endpoint_eq_interval hD1]
  rw [add_comm, ← hsplit]
  simpa using (localBetaIntegral_eq_interval (n := n) (q := 1)
    (D := D) (by omega) (by omega)).symm

/-- For a fixed denominator, summing over centers is summing over the reduced
residue classes modulo that denominator. -/
theorem sum_majorArcCenters_fixed_denominator {P q : ℕ}
    (F : ℕ → ℂ) :
    ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        F aq.1 =
      if q ≤ P ∧ q ≠ 0 then
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F a
      else 0 := by
  classical
  by_cases hq : q ≤ P ∧ q ≠ 0
  · rw [if_pos hq]
    apply Finset.sum_bij (fun aq _haq => aq.1)
    · intro aq haq
      simp only [Finset.mem_filter, Finset.mem_range]
      simp only [Finset.mem_filter] at haq
      have hmem : aq ∈ Vinogradov.majorArcCenters P :=
        (Set.Finite.mem_toFinset (majorArcCenters_finite P)).mp haq.1
      exact ⟨by simpa [haq.2] using Vinogradov.majorArcCenters_a_lt_q hmem,
        by simpa [haq.2] using Vinogradov.majorArcCenters_coprime hmem⟩
    · intro aq₁ haq₁ aq₂ haq₂ hfst
      cases aq₁ with
      | mk a₁ q₁ =>
        cases aq₂ with
        | mk a₂ q₂ =>
          simp only at hfst
          simp only [Finset.mem_filter] at haq₁ haq₂
          simp [hfst, haq₁.2, haq₂.2]
    · intro a ha
      refine ⟨(a, q), ?_, rfl⟩
      simp only [Finset.mem_filter]
      refine ⟨?_, trivial⟩
      rw [Set.Finite.mem_toFinset (majorArcCenters_finite P)]
      exact ⟨hq.1, hq.2, Finset.mem_range.mp (Finset.mem_filter.mp ha).1,
        (Finset.mem_filter.mp ha).2⟩
    · intro aq haq
      rfl
  · simp only [hq, if_false]
    apply Finset.sum_eq_zero
    intro aq haq
    simp only [Finset.mem_filter] at haq
    have hmem : aq ∈ Vinogradov.majorArcCenters P :=
      (Set.Finite.mem_toFinset (majorArcCenters_finite P)).mp haq.1
    exact (hq ⟨by simpa [haq.2] using Vinogradov.majorArcCenters_q_le hmem,
      by simpa [haq.2] using Vinogradov.majorArcCenters_q_ne_zero hmem⟩).elim

private theorem negAddChar_rationalCenter_eq_addChar_complement {a q n : ℕ}
    (hq : 0 < q) (haq : a ≤ q) :
    Vinogradov.negAddChar (Vinogradov.rationalCenter a q) n =
      Vinogradov.addChar ((n : ℝ) / (q : ℝ)) (q - a) := by
  unfold Vinogradov.negAddChar Vinogradov.addChar Vinogradov.rationalCenter
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hsubc : ((q - a : ℕ) : ℂ) = (q : ℂ) - (a : ℂ) := Nat.cast_sub haq
  have harg :
      2 * Real.pi * Complex.I * ((q - a : ℕ) : ℂ) *
          ((((n : ℝ) / (q : ℝ) : ℝ) : ℂ)) =
        -2 * Real.pi * Complex.I * ((((a : ℝ) / (q : ℝ) : ℝ) : ℂ)) * (n : ℂ) +
          (n : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hsubc]
    push_cast
    field_simp [hqc]
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I]
  ring

private theorem coprime_filter_pos_of_two_le {a q : ℕ} (hq : 2 ≤ q)
    (ha : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q)) :
    0 < a := by
  have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
  by_contra hapos
  have haz : a = 0 := Nat.eq_zero_of_not_pos hapos
  have hq1 : q = 1 := (Nat.coprime_zero_left q).mp (by simpa [haz] using hcop)
  omega

theorem sum_negAddChar_reduced_eq_ramanujanSum (q n : ℕ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Vinogradov.negAddChar (Vinogradov.rationalCenter a q) n) =
      Vinogradov.ramanujanSum q n := by
  classical
  rcases lt_or_ge q 2 with hq_small | hq
  · interval_cases q <;> simp [Vinogradov.ramanujanSum, Vinogradov.rationalCenter]
  · unfold Vinogradov.ramanujanSum
    let s : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)
    change (∑ a ∈ s, Vinogradov.negAddChar (Vinogradov.rationalCenter a q) n) =
      ∑ a ∈ s, Vinogradov.addChar ((n : ℝ) / (q : ℝ)) a
    refine Finset.sum_bij (fun a _ha => q - a) ?_ ?_ ?_ ?_
    · intro a ha
      have haf : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
        simpa [s] using ha
      have ha' := Finset.mem_filter.mp haf
      have halt : a < q := Finset.mem_range.mp ha'.1
      have hapos : 0 < a := coprime_filter_pos_of_two_le hq haf
      have hmem : q - a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (Nat.sub_lt (by omega) hapos),
          (Nat.coprime_self_sub_left halt.le).mpr ha'.2⟩
      simpa [s] using hmem
    · intro a₁ ha₁ a₂ ha₂ hsub
      change q - a₁ = q - a₂ at hsub
      have ha₁f : a₁ ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
        simpa [s] using ha₁
      have ha₂f : a₂ ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
        simpa [s] using ha₂
      have ha₁lt : a₁ < q := Finset.mem_range.mp (Finset.mem_filter.mp ha₁f).1
      have ha₂lt : a₂ < q := Finset.mem_range.mp (Finset.mem_filter.mp ha₂f).1
      omega
    · intro b hb
      have hbf : b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
        simpa [s] using hb
      have hb' := Finset.mem_filter.mp hbf
      have hblt : b < q := Finset.mem_range.mp hb'.1
      have hbpos : 0 < b := coprime_filter_pos_of_two_le hq hbf
      refine ⟨q - b, ?_, ?_⟩
      · have hmem : q - b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr (Nat.sub_lt (by omega) hbpos),
            (Nat.coprime_self_sub_left hblt.le).mpr hb'.2⟩
        simpa [s] using hmem
      · change q - (q - b) = b
        omega
    · intro a ha
      have haf : a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) := by
        simpa [s] using ha
      have halt : a < q := Finset.mem_range.mp (Finset.mem_filter.mp haf).1
      exact negAddChar_rationalCenter_eq_addChar_complement (n := n) (by omega) halt.le

theorem sum_majorArcCenters_fixed_denominator_negAddChar {P q n : ℕ}
    (hP : q ≤ P) (hq : q ≠ 0) :
    ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        Vinogradov.negAddChar (Vinogradov.rationalCenter aq.1 aq.2) n =
      Vinogradov.ramanujanSum q n := by
  have h := sum_majorArcCenters_fixed_denominator (P := P) (q := q)
    (fun a => Vinogradov.negAddChar (Vinogradov.rationalCenter a q) n)
  rw [if_pos ⟨hP, hq⟩] at h
  calc
    ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        Vinogradov.negAddChar (Vinogradov.rationalCenter aq.1 aq.2) n =
      ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        Vinogradov.negAddChar (Vinogradov.rationalCenter aq.1 q) n := by
          refine Finset.sum_congr rfl ?_
          intro aq haq
          simp only [Finset.mem_filter] at haq
          simp [haq.2]
    _ = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Vinogradov.negAddChar (Vinogradov.rationalCenter a q) n := by simpa using h
    _ = Vinogradov.ramanujanSum q n :=
      sum_negAddChar_reduced_eq_ramanujanSum q n

/-- Integral of the local main model over the wrapped arc at one center. -/
noncomputable def localModelIntegral (D n : ℕ) (aq : ℕ × ℕ) : ℂ :=
  ∫ α in torusLocalArc D aq,
    localMainIntegrand n aq.1 aq.2 α

theorem localModelIntegral_eq
    {D P n : ℕ} (hD : 2 ≤ D) {aq : ℕ × ℕ}
    (haq : aq ∈ Vinogradov.majorArcCenters P) :
    localModelIntegral D n aq =
      localMainCenterCoeff n aq * localBetaIntegral D aq.2 n := by
  by_cases hzero : aq = (0, 1)
  · subst aq
    rw [localModelIntegral, localMainIntegral_endpoint hD]
    simp [localMainCenterCoeff, Vinogradov.rationalCenter]
  · have ha : 0 < aq.1 := by
      have hqpos := Vinogradov.majorArcCenters_q_pos haq
      have hcop := Vinogradov.majorArcCenters_coprime haq
      by_contra hapos
      have haz : aq.1 = 0 := Nat.eq_zero_of_not_pos hapos
      have hq1 : aq.2 = 1 :=
        (Nat.coprime_zero_left aq.2).mp (by simpa [haz] using hcop)
      exact hzero (Prod.ext haz hq1)
    have halt := Vinogradov.majorArcCenters_a_lt_q haq
    rw [localModelIntegral, torusLocalArc, if_neg hzero]
    exact localMainIntegral_internal ha halt (by omega)

theorem sum_majorArcCenters_fixed_denominator_localModel
    {D P q n : ℕ} (hD : 2 ≤ D) (hP : q ≤ P) (hq : q ≠ 0) :
    ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        localModelIntegral D n aq =
      singularTerm q n * localBetaIntegral D q n := by
  let coeff : ℂ :=
    (((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 3) /
      (Nat.totient q : ℝ) ^ 3 : ℝ) : ℂ)
  have hphase := sum_majorArcCenters_fixed_denominator_negAddChar
    (P := P) (q := q) (n := n) hP hq
  calc
    ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        localModelIntegral D n aq =
      ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        localMainCenterCoeff n aq * localBetaIntegral D q n := by
          refine Finset.sum_congr rfl ?_
          intro aq haq
          simp only [Finset.mem_filter] at haq
          have hcenter : aq ∈ Vinogradov.majorArcCenters P :=
            (Set.Finite.mem_toFinset (majorArcCenters_finite P)).mp haq.1
          rw [localModelIntegral_eq hD hcenter, haq.2]
    _ = ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        coeff * Vinogradov.negAddChar
          (Vinogradov.rationalCenter aq.1 aq.2) n * localBetaIntegral D q n := by
          refine Finset.sum_congr rfl ?_
          intro aq haq
          simp only [Finset.mem_filter] at haq
          simp [localMainCenterCoeff, coeff, haq.2, mul_assoc]
    _ = (coeff *
        ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
          Vinogradov.negAddChar
            (Vinogradov.rationalCenter aq.1 aq.2) n) * localBetaIntegral D q n := by
          simp [Finset.mul_sum, mul_left_comm, mul_comm]
    _ = coeff * Vinogradov.ramanujanSum q n * localBetaIntegral D q n := by
      rw [hphase]
    _ = singularTerm q n * localBetaIntegral D q n := by
      simp [singularTerm, coeff, mul_assoc]

/-- Regrouping the finite wrapped local model by denominator gives precisely
the finite singular-series/singular-integral model. -/
theorem sum_localModelIntegral_eq_denominator_sum (D P n : ℕ)
    (hD : 2 ≤ D) :
    ∑ aq ∈ (majorArcCenters_finite P).toFinset,
        localModelIntegral D n aq =
      ∑ q ∈ Finset.Icc 1 P,
        singularTerm q n * localBetaIntegral D q n := by
  classical
  let t : Finset (ℕ × ℕ) := (majorArcCenters_finite P).toFinset
  let F : ℕ × ℕ → ℂ := fun aq => localModelIntegral D n aq
  have hmap : ∀ aq ∈ t, aq.2 ∈ Finset.Icc 1 P := by
    intro aq haq
    have hcenter : aq ∈ Vinogradov.majorArcCenters P :=
      (Set.Finite.mem_toFinset (majorArcCenters_finite P)).mp (by simpa [t] using haq)
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_of_lt (Vinogradov.majorArcCenters_q_pos hcenter),
        Vinogradov.majorArcCenters_q_le hcenter⟩
  have hfiber :
      ∑ q ∈ Finset.Icc 1 P, ∑ aq ∈ t with aq.2 = q, F aq =
        ∑ aq ∈ t, F aq :=
    Finset.sum_fiberwise_of_maps_to (s := t) (t := Finset.Icc 1 P)
      (g := fun aq : ℕ × ℕ => aq.2) hmap F
  rw [← hfiber]
  refine Finset.sum_congr rfl ?_
  intro q hqmem
  have hqIcc := Finset.mem_Icc.mp hqmem
  have hq_ne : q ≠ 0 := by omega
  calc
    ∑ aq ∈ t with aq.2 = q, F aq =
      ∑ aq ∈ ((majorArcCenters_finite P).toFinset.filter fun aq => aq.2 = q),
        localModelIntegral D n aq := by
          refine Finset.sum_congr ?_ ?_
          · simp [t]
          · intro aq _haq
            rfl
    _ = singularTerm q n * localBetaIntegral D q n :=
      sum_majorArcCenters_fixed_denominator_localModel hD hqIcc.2 hq_ne

/-- The complementary middle interval left after wrapping the negative half
of the local beta window to the right endpoint. -/
noncomputable def localBetaIntegralTail (D q n : ℕ) : ℂ :=
  ∫ β in (1 / ((q : ℝ) * (D : ℝ)))..
      (1 - 1 / ((q : ℝ) * (D : ℝ))), betaIntegrand n β

theorem singularIntegral_eq_localBetaIntegral_add_tail
    {D q n : ℕ} (hprod : 2 ≤ q * D) :
    Vinogradov.singularIntegral n n =
      localBetaIntegral D q n + localBetaIntegralTail D q n := by
  let r : ℝ := 1 / ((q : ℝ) * (D : ℝ))
  have hprodpos : 0 < q * D := lt_of_lt_of_le (by norm_num) hprod
  have hdenpos : 0 < (q : ℝ) * (D : ℝ) := by exact_mod_cast hprodpos
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrhalf : r ≤ (1 : ℝ) / 2 := by
    have hden2 : (2 : ℝ) ≤ (q : ℝ) * (D : ℝ) := by exact_mod_cast hprod
    exact (one_div_le_one_div hdenpos (by norm_num : (0 : ℝ) < 2)).2 hden2
  have hfull : Vinogradov.singularIntegral n n =
      ∫ β in (0 : ℝ)..1, betaIntegrand n β := by
    unfold Vinogradov.singularIntegral betaIntegrand
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [integral_Icc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  have hlocal : localBetaIntegral D q n =
      ∫ β in (-r)..r, betaIntegrand n β := by
    unfold localBetaIntegral r
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  rw [hfull, hlocal, localBetaIntegralTail]
  change (∫ β in (0 : ℝ)..1, betaIntegrand n β) =
    (∫ β in (-r)..r, betaIntegrand n β) +
      ∫ β in r..(1 - r), betaIntegrand n β
  have hshift : (∫ β in (-r)..0, betaIntegrand n β) =
      ∫ β in (1 - r)..1, betaIntegrand n β := by
    calc
      (∫ β in (-r)..0, betaIntegrand n β) =
          ∫ β in (-r)..0, betaIntegrand n (β + 1) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with β _hβ
            exact (betaIntegrand_periodic n β).symm
      _ = ∫ β in (-r) + 1..(0 : ℝ) + 1, betaIntegrand n β := by
            rw [intervalIntegral.integral_comp_add_right]
      _ = ∫ β in (1 - r)..1, betaIntegrand n β := by
            congr 1 <;> ring
  have hsplitLocal : (∫ β in (-r)..r, betaIntegrand n β) =
      (∫ β in (-r)..0, betaIntegrand n β) +
        ∫ β in (0 : ℝ)..r, betaIntegrand n β := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (betaIntegrand_intervalIntegrable n (-r) 0)
      (betaIntegrand_intervalIntegrable n 0 r)]
  have hsplitFull₁ : (∫ β in (0 : ℝ)..1, betaIntegrand n β) =
      (∫ β in (0 : ℝ)..r, betaIntegrand n β) +
        ∫ β in r..1, betaIntegrand n β := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (betaIntegrand_intervalIntegrable n 0 r)
      (betaIntegrand_intervalIntegrable n r 1)]
  have hsplitFull₂ : (∫ β in r..1, betaIntegrand n β) =
      (∫ β in r..(1-r), betaIntegrand n β) +
        ∫ β in (1-r)..1, betaIntegrand n β := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (betaIntegrand_intervalIntegrable n r (1-r))
      (betaIntegrand_intervalIntegrable n (1-r) 1)]
  rw [hsplitFull₁, hsplitFull₂, hsplitLocal, hshift]
  abel

private theorem two_mul_le_abs_sin_pi_mul_of_mem_Icc_zero_half
    {β : ℝ} (hβ0 : 0 ≤ β) (hβhalf : β ≤ 1 / 2) :
    2 * β ≤ |Real.sin (Real.pi * β)| := by
  have hpiabs : |Real.pi * β| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hβ0]
    nlinarith [Real.pi_pos, hβhalf]
  have h := Real.mul_abs_le_abs_sin hpiabs
  rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hβ0] at h
  have hleft : 2 / Real.pi * (Real.pi * β) = 2 * β := by
    field_simp [Real.pi_ne_zero]
  simpa [hleft] using h

private theorem two_mul_one_sub_le_abs_sin_pi_mul_of_mem_Icc_half_one
    {β : ℝ} (hβhalf : 1 / 2 ≤ β) (hβ1 : β ≤ 1) :
    2 * (1 - β) ≤ |Real.sin (Real.pi * β)| := by
  let γ : ℝ := 1 - β
  have hγ0 : 0 ≤ γ := by dsimp [γ]; linarith
  have hγhalf : γ ≤ 1 / 2 := by dsimp [γ]; linarith
  have hγ := two_mul_le_abs_sin_pi_mul_of_mem_Icc_zero_half hγ0 hγhalf
  have hsineq : |Real.sin (Real.pi * γ)| = |Real.sin (Real.pi * β)| := by
    have harg : Real.pi * γ = Real.pi - Real.pi * β := by dsimp [γ]; ring
    rw [harg, Real.sin_pi_sub]
  simpa [γ, hsineq] using hγ

private theorem norm_betaIntegrand_le_left_cube
    (n : ℕ) {β : ℝ} (hβpos : 0 < β) (hβhalf : β ≤ 1 / 2) :
    ‖betaIntegrand n β‖ ≤ (1 / (2 * β)) ^ 3 := by
  have hβlt1 : β < 1 := by nlinarith
  have hnotint : ¬ ∃ k : ℤ, (k : ℝ) = β := by
    rintro ⟨k, hk⟩
    have hkpos : (0 : ℤ) < k := by
      exact_mod_cast (show (0 : ℝ) < (k : ℝ) by simpa [hk] using hβpos)
    have hklt : k < 1 := by
      exact_mod_cast (show (k : ℝ) < 1 by simpa [hk] using hβlt1)
    omega
  have hsin : 2 * β ≤ |Real.sin (Real.pi * β)| :=
    two_mul_le_abs_sin_pi_mul_of_mem_Icc_zero_half hβpos.le hβhalf
  have hinv : 1 / |Real.sin (Real.pi * β)| ≤ 1 / (2 * β) :=
    one_div_le_one_div_of_le (by positivity) hsin
  unfold betaIntegrand
  rw [norm_mul, norm_pow, Vinogradov.norm_negAddChar, mul_one]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (Vinogradov.norm_linearExpSum_le_oscillation_sin n hnotint) 3).trans
      (pow_le_pow_left₀ (by positivity) hinv 3)

private theorem norm_betaIntegrand_le_right_cube
    (n : ℕ) {β : ℝ} (hβhalf : 1 / 2 ≤ β) (hβlt1 : β < 1) :
    ‖betaIntegrand n β‖ ≤ (1 / (2 * (1 - β))) ^ 3 := by
  have hnotint : ¬ ∃ k : ℤ, (k : ℝ) = β := by
    rintro ⟨k, hk⟩
    have hkpos : (0 : ℤ) < k := by
      exact_mod_cast (show (0 : ℝ) < (k : ℝ) by nlinarith [hβhalf, hk])
    have hklt : k < 1 := by
      exact_mod_cast (show (k : ℝ) < 1 by simpa [hk] using hβlt1)
    omega
  have hsin : 2 * (1 - β) ≤ |Real.sin (Real.pi * β)| :=
    two_mul_one_sub_le_abs_sin_pi_mul_of_mem_Icc_half_one hβhalf hβlt1.le
  have hinv : 1 / |Real.sin (Real.pi * β)| ≤ 1 / (2 * (1 - β)) :=
    one_div_le_one_div_of_le (by positivity) hsin
  unfold betaIntegrand
  rw [norm_mul, norm_pow, Vinogradov.norm_negAddChar, mul_one]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (Vinogradov.norm_linearExpSum_le_oscillation_sin n hnotint) 3).trans
      (pow_le_pow_left₀ (by positivity) hinv 3)

private theorem intervalIntegrable_left_beta_kernel {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (fun β : ℝ => (1 / (2 * β)) ^ 3) volume
      a (1 / 2) := by
  have h0not : (0 : ℝ) ∉ Set.uIcc a (1 / 2 : ℝ) :=
    Set.notMem_uIcc_of_lt ha (by norm_num)
  have hz : IntervalIntegrable (fun β : ℝ => β ^ (-3 : ℤ)) volume
      a (1 / 2) :=
    intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := (-3 : ℤ))
      (Or.inr h0not)
  have hc := hz.const_mul (1 / 8 : ℝ)
  convert hc using 1
  funext β
  by_cases hβ : β = 0
  · simp [hβ]
  · field_simp [hβ]
    ring

private theorem intervalIntegrable_right_beta_kernel {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (fun β : ℝ => (1 / (2 * (1 - β))) ^ 3) volume
      (1 / 2) (1 - a) := by
  have hleft := intervalIntegrable_left_beta_kernel ha
  convert (hleft.comp_sub_left (1 : ℝ)).symm using 1
  norm_num

private theorem integral_left_beta_kernel {a : ℝ} (ha : 0 < a) :
    ∫ β in a..(1 / 2 : ℝ), (1 / (2 * β)) ^ 3 =
      (1 / 16) * (a ^ (-2 : ℤ) - 4) := by
  have h0not : (0 : ℝ) ∉ Set.uIcc a (1 / 2 : ℝ) :=
    Set.notMem_uIcc_of_lt ha (by norm_num)
  rw [show (fun β : ℝ => (1 / (2 * β)) ^ 3) =
      fun β : ℝ => (1 / 8 : ℝ) * β ^ (-3 : ℤ) by
    funext β
    by_cases hβ : β = 0
    · simp [hβ]
    · field_simp [hβ]
      ring]
  rw [intervalIntegral.integral_const_mul, integral_zpow]
  · norm_num
    field_simp [ha.ne']
    ring
  · right
    exact ⟨by norm_num, h0not⟩

private theorem integral_right_beta_kernel {a : ℝ} (ha : 0 < a) :
    ∫ β in (1 / 2 : ℝ)..(1 - a), (1 / (2 * (1 - β))) ^ 3 =
      (1 / 16) * (a ^ (-2 : ℤ) - 4) := by
  have h := integral_left_beta_kernel ha
  rw [← h]
  rw [intervalIntegral.integral_comp_sub_left
    (f := fun t : ℝ => (1 / (2 * t)) ^ 3) (d := 1)]
  norm_num

/-- Oscillation of the linear exponential sum makes the discarded middle
beta interval only quadratic in the reciprocal radius. -/
theorem norm_localBetaIntegralTail_le {D q n : ℕ} (hprod : 2 ≤ q * D) :
    ‖localBetaIntegralTail D q n‖ ≤
      (((q : ℝ) * (D : ℝ)) ^ 2) / 8 := by
  let r : ℝ := 1 / ((q : ℝ) * (D : ℝ))
  have hprodpos : 0 < q * D := lt_of_lt_of_le (by norm_num) hprod
  have hxpos : 0 < (q : ℝ) * (D : ℝ) := by exact_mod_cast hprodpos
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrhalf : r ≤ (1 : ℝ) / 2 := by
    have hx2 : (2 : ℝ) ≤ (q : ℝ) * (D : ℝ) := by exact_mod_cast hprod
    exact (one_div_le_one_div hxpos (by norm_num : (0 : ℝ) < 2)).2 hx2
  have hleft :
      ‖∫ β in r..(1 / 2 : ℝ), betaIntegrand n β‖ ≤
        ∫ β in r..(1 / 2 : ℝ), (1 / (2 * β)) ^ 3 := by
    apply intervalIntegral.norm_integral_le_of_norm_le hrhalf
    · filter_upwards [] with β hβ
      exact norm_betaIntegrand_le_left_cube n
        (hrpos.trans hβ.1) hβ.2
    · exact intervalIntegrable_left_beta_kernel hrpos
  have hright :
      ‖∫ β in (1 / 2 : ℝ)..(1 - r), betaIntegrand n β‖ ≤
        ∫ β in (1 / 2 : ℝ)..(1 - r),
          (1 / (2 * (1 - β))) ^ 3 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · filter_upwards [] with β hβ
      exact norm_betaIntegrand_le_right_cube n hβ.1.le
        (hβ.2.trans_lt (sub_lt_self 1 hrpos))
    · exact intervalIntegrable_right_beta_kernel hrpos
  have hsplit : localBetaIntegralTail D q n =
      (∫ β in r..(1 / 2 : ℝ), betaIntegrand n β) +
        ∫ β in (1 / 2 : ℝ)..(1-r), betaIntegrand n β := by
    unfold localBetaIntegralTail r
    rw [intervalIntegral.integral_add_adjacent_intervals
      (betaIntegrand_intervalIntegrable n r (1/2))
      (betaIntegrand_intervalIntegrable n (1/2) (1-r))]
  have hrpow : r ^ (-2 : ℤ) = ((q : ℝ) * (D : ℝ)) ^ 2 := by
    dsimp [r]
    rw [zpow_neg]
    norm_num
    field_simp [hxpos.ne']
  rw [hsplit]
  calc
    ‖(∫ β in r..(1 / 2 : ℝ), betaIntegrand n β) +
        ∫ β in (1 / 2 : ℝ)..(1-r), betaIntegrand n β‖ ≤
      ‖∫ β in r..(1 / 2 : ℝ), betaIntegrand n β‖ +
        ‖∫ β in (1 / 2 : ℝ)..(1-r), betaIntegrand n β‖ := norm_add_le _ _
    _ ≤ (∫ β in r..(1 / 2 : ℝ), (1 / (2 * β)) ^ 3) +
        ∫ β in (1 / 2 : ℝ)..(1-r), (1 / (2 * (1-β))) ^ 3 :=
      add_le_add hleft hright
    _ = (1 / 16) * (r ^ (-2 : ℤ) - 4) +
        (1 / 16) * (r ^ (-2 : ℤ) - 4) := by
      rw [integral_left_beta_kernel hrpos, integral_right_beta_kernel hrpos]
    _ ≤ (((q : ℝ) * (D : ℝ)) ^ 2) / 8 := by
      rw [hrpow]
      ring_nf
      norm_num

/-- The full singular integral counts at most one third coordinate for every
choice of the first two. -/
theorem norm_singularIntegral_self_le (n : ℕ) :
    ‖Vinogradov.singularIntegral n n‖ ≤ ((n : ℝ) + 1) ^ 2 := by
  let T := ((Finset.range (n + 1) ×ˢ
      (Finset.range (n + 1) ×ˢ Finset.range (n + 1))).filter
        (fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2 = n))
  let U := Finset.range (n + 1) ×ˢ Finset.range (n + 1)
  let f : {x // x ∈ T} → {ab // ab ∈ U} := fun x =>
    ⟨(x.val.1, x.val.2.1), by
      have hx := (Finset.mem_filter.mp x.property).1
      have hx' : x.val.1 ∈ Finset.range (n + 1) ∧
          x.val.2.1 ∈ Finset.range (n + 1) ∧
            x.val.2.2 ∈ Finset.range (n + 1) := by
        simpa only [Finset.mem_product] using hx
      simpa only [U, Finset.mem_product] using And.intro hx'.1 hx'.2.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hfirst : x.val.1 = y.val.1 :=
      congrArg (fun z : {ab // ab ∈ U} => z.val.1) hxy
    have hsecond : x.val.2.1 = y.val.2.1 :=
      congrArg (fun z : {ab // ab ∈ U} => z.val.2) hxy
    have hxsum := (Finset.mem_filter.mp x.property).2
    have hysum := (Finset.mem_filter.mp y.property).2
    apply Prod.ext hfirst
    apply Prod.ext hsecond
    omega
  have hcard : T.card ≤ U.card := by
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  rw [Vinogradov.singularIntegral_self_eq_choose]
  change ‖(T.card : ℂ)‖ ≤ ((n : ℝ) + 1) ^ 2
  rw [Complex.norm_natCast]
  have hU : U.card = (n + 1) ^ 2 := by simp [U, pow_two]
  rw [hU] at hcard
  norm_cast at hcard ⊢

/-- Total mass of the target-independent denominator majorant. -/
noncomputable def singularMajorantTotal : ℝ :=
  ∑' q : ℕ, ‖singularTerm q 0‖

theorem singularMajorantTotal_nonneg : 0 ≤ singularMajorantTotal := by
  exact tsum_nonneg fun _ => norm_nonneg _

theorem sum_norm_singularTerm_le_majorant (s : Finset ℕ) (n : ℕ) :
    ∑ q ∈ s, ‖singularTerm q n‖ ≤ singularMajorantTotal := by
  calc
    ∑ q ∈ s, ‖singularTerm q n‖ ≤
        ∑ q ∈ s, ‖singularTerm q 0‖ := by
      exact Finset.sum_le_sum fun q _ => norm_singularTerm_le_zero_frequency q n
    _ ≤ ∑' q : ℕ, ‖singularTerm q 0‖ :=
      summable_uniform_singularMajorant.sum_le_tsum s (fun _ _ => norm_nonneg _)
    _ = singularMajorantTotal := rfl

theorem sum_Icc_singularTerm_eq_sum_range_succ (P n : ℕ) :
    ∑ q ∈ Finset.Icc 1 P, singularTerm q n =
      ∑ q ∈ Finset.range (P + 1), singularTerm q n := by
  classical
  have hset : Finset.range (P + 1) = insert 0 (Finset.Icc 1 P) := by
    ext q
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset]
  simp [singularTerm_zero]

/-- Quantitative comparison of the finite local beta model with the same
finite denominator sum multiplied by the full singular integral. -/
theorem norm_denominator_model_sub_full_le
    {D P n : ℕ} (hD : 2 ≤ D) :
    ‖(∑ q ∈ Finset.Icc 1 P,
          singularTerm q n * localBetaIntegral D q n) -
        (∑ q ∈ Finset.Icc 1 P, singularTerm q n) *
          Vinogradov.singularIntegral n n‖ ≤
      singularMajorantTotal * (((P : ℝ) * (D : ℝ)) ^ 2 / 8) := by
  have hpoint : ∀ q ∈ Finset.Icc 1 P,
      ‖singularTerm q n * localBetaIntegral D q n -
          singularTerm q n * Vinogradov.singularIntegral n n‖ ≤
        ‖singularTerm q n‖ * (((P : ℝ) * (D : ℝ)) ^ 2 / 8) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    have hprod : 2 ≤ q * D := by nlinarith
    have hsplit := singularIntegral_eq_localBetaIntegral_add_tail
      (n := n) hprod
    have htail := norm_localBetaIntegralTail_le (n := n) hprod
    have hqP : (q : ℝ) ≤ P := by exact_mod_cast hqIcc.2
    have hD0 : (0 : ℝ) ≤ D := by positivity
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hP0 : (0 : ℝ) ≤ P := by positivity
    have hsq : ((q : ℝ) * (D : ℝ)) ^ 2 ≤
        ((P : ℝ) * (D : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hqP hD0) 2
    calc
      ‖singularTerm q n * localBetaIntegral D q n -
          singularTerm q n * Vinogradov.singularIntegral n n‖ =
        ‖singularTerm q n * localBetaIntegralTail D q n‖ := by
          have heq : singularTerm q n * localBetaIntegral D q n -
              singularTerm q n * Vinogradov.singularIntegral n n =
            -(singularTerm q n * localBetaIntegralTail D q n) := by
              rw [hsplit]
              ring
          rw [heq, norm_neg]
      _ ≤ ‖singularTerm q n‖ * ‖localBetaIntegralTail D q n‖ := norm_mul_le _ _
      _ ≤ ‖singularTerm q n‖ *
          (((q : ℝ) * (D : ℝ)) ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left htail (norm_nonneg _)
      _ ≤ ‖singularTerm q n‖ *
          (((P : ℝ) * (D : ℝ)) ^ 2 / 8) := by gcongr
  calc
    ‖(∑ q ∈ Finset.Icc 1 P, singularTerm q n * localBetaIntegral D q n) -
        (∑ q ∈ Finset.Icc 1 P, singularTerm q n) *
          Vinogradov.singularIntegral n n‖ =
      ‖∑ q ∈ Finset.Icc 1 P,
        (singularTerm q n * localBetaIntegral D q n -
          singularTerm q n * Vinogradov.singularIntegral n n)‖ := by
            rw [Finset.sum_mul]
            simp only [Finset.sum_sub_distrib]
    _ ≤ ∑ q ∈ Finset.Icc 1 P,
        ‖singularTerm q n * localBetaIntegral D q n -
          singularTerm q n * Vinogradov.singularIntegral n n‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 P,
        ‖singularTerm q n‖ * (((P : ℝ) * (D : ℝ)) ^ 2 / 8) :=
      Finset.sum_le_sum hpoint
    _ = (∑ q ∈ Finset.Icc 1 P, ‖singularTerm q n‖) *
        (((P : ℝ) * (D : ℝ)) ^ 2 / 8) := by rw [Finset.sum_mul]
    _ ≤ singularMajorantTotal * (((P : ℝ) * (D : ℝ)) ^ 2 / 8) := by
      gcongr
      exact sum_norm_singularTerm_le_majorant _ _

theorem eventually_localBeta_tail_error_le_mul {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      singularMajorantTotal *
          (((majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ)) ^ 2 / 8) ≤
        ε * (n : ℝ) ^ 2 := by
  have hLpow : Tendsto (fun n : ℕ => logScale n ^ 160) atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : 160 ≠ 0)).comp tendsto_logScale
  have hcast : Tendsto (fun n : ℕ => ((logScale n ^ 160 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hLpow
  have hlarge := hcast.eventually_ge_atTop (singularMajorantTotal / (8 * ε))
  filter_upwards [hlarge] with n hn
  have hnat : majorDenominatorCutoff n * dirichletCutoff n *
      logScale n ^ 80 ≤ n := by
    calc
      majorDenominatorCutoff n * dirichletCutoff n * logScale n ^ 80 =
          dirichletCutoff n * logScale n ^ 100 := by
        simp only [majorDenominatorCutoff]
        rw [show logScale n ^ 100 = logScale n ^ 20 * logScale n ^ 80 by
          rw [← pow_add]]
        ring
      _ = (n / logScale n ^ 100) * logScale n ^ 100 := rfl
      _ ≤ n := Nat.div_mul_le_self _ _
  have hreal : (majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ) *
      (logScale n : ℝ) ^ 80 ≤ (n : ℝ) := by exact_mod_cast hnat
  have hbase : (0 : ℝ) ≤
      (majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ) *
        (logScale n : ℝ) ^ 80 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  have hsquare := pow_le_pow_left₀ hbase hreal 2
  have hpow : ((logScale n : ℝ) ^ 80) ^ 2 =
      (logScale n : ℝ) ^ 160 := by
    rw [show (160 : ℕ) = 80 * 2 by norm_num, pow_mul]
  have hsquare' :
      ((majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ)) ^ 2 *
          (logScale n : ℝ) ^ 160 ≤ (n : ℝ) ^ 2 := by
    rw [← hpow, ← mul_pow]
    exact hsquare
  have hn' : singularMajorantTotal / (8 * ε) ≤
      (logScale n : ℝ) ^ 160 := by simpa only [Nat.cast_pow] using hn
  have hden : 0 < 8 * ε := mul_pos (by norm_num) hε
  have hC : singularMajorantTotal ≤
      (logScale n : ℝ) ^ 160 * (8 * ε) :=
    (div_le_iff₀ hden).mp hn'
  have hpdnonneg : 0 ≤
      ((majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ)) ^ 2 :=
    sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hC hpdnonneg
  calc
    singularMajorantTotal *
        (((majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ)) ^ 2 / 8) =
      (((majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ)) ^ 2 *
        singularMajorantTotal) / 8 := by ring
    _ ≤ (((majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ)) ^ 2 *
        ((logScale n : ℝ) ^ 160 * (8 * ε))) / 8 := by gcongr
    _ = ε * (((majorDenominatorCutoff n : ℝ) * (dirichletCutoff n : ℝ)) ^ 2 *
        (logScale n : ℝ) ^ 160) := by ring
    _ ≤ ε * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsquare' hε.le

theorem eventually_denominator_truncation_error_le_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖((∑ q ∈ Finset.Icc 1 (majorDenominatorCutoff n), singularTerm q n) -
          (∑' q : ℕ, singularTerm q n)) *
          Vinogradov.singularIntegral n n‖ ≤ ε * (n : ℝ) ^ 2 := by
  let Pplus : ℕ → ℕ := fun n => majorDenominatorCutoff n + 1
  have hPplus : Tendsto Pplus atTop atTop := by
    exact (tendsto_add_atTop_nat 1).comp tendsto_majorDenominatorCutoff
  have hepsTail : 0 < ε / 4 := by positivity
  have htail := eventually_uniform_singularTerm_tail hPplus hepsTail
  filter_upwards [htail, eventually_ge_atTop (1 : ℕ)] with n hnTail hn
  have hJ := norm_singularIntegral_self_le n
  have hnquad : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  rw [norm_mul]
  rw [sum_Icc_singularTerm_eq_sum_range_succ]
  have htail' :
      ‖(∑ q ∈ Finset.range (majorDenominatorCutoff n + 1), singularTerm q n) -
          (∑' q : ℕ, singularTerm q n)‖ < ε / 4 := by
    simpa [Pplus] using hnTail
  calc
    ‖(∑ q ∈ Finset.range (majorDenominatorCutoff n + 1), singularTerm q n) -
        ∑' q : ℕ, singularTerm q n‖ * ‖Vinogradov.singularIntegral n n‖ ≤
      (ε / 4) * (((n : ℝ) + 1) ^ 2) :=
        mul_le_mul htail'.le hJ (norm_nonneg _) (by positivity)
    _ ≤ (ε / 4) * (4 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hnquad (by positivity)
    _ = ε * (n : ℝ) ^ 2 := by ring

theorem eventually_four_majorDenominatorCutoff_le_dirichletCutoff :
    ∀ᶠ n : ℕ in atTop,
      4 * majorDenominatorCutoff n ≤ dirichletCutoff n := by
  filter_upwards [eventually_four_logScale_pow_120_le] with n hn
  have hKpos : 0 < logScale n ^ 100 :=
    pow_pos (Erdos387.binaryLogScale_pos n) _
  apply (Nat.le_div_iff_mul_le hKpos).2
  calc
    4 * majorDenominatorCutoff n * logScale n ^ 100 =
        4 * logScale n ^ 120 := by
      simp only [majorDenominatorCutoff]
      rw [show logScale n ^ 120 = logScale n ^ 20 * logScale n ^ 100 by
        rw [← pow_add]]
      ring
    _ ≤ n := hn

/-- The fully aggregated finite local model has a positive quadratic real
part on every sufficiently large odd target. -/
theorem eventually_denominator_model_re_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      Odd n →
        c * (n : ℝ) ^ 2 ≤
          (∑ q ∈ Finset.Icc 1 (majorDenominatorCutoff n),
            singularTerm q n *
              localBetaIntegral (dirichletCutoff n) q n).re := by
  obtain ⟨N₀, K, hK, hsing⟩ := Vinogradov.singularIntegral_lower_bound
  have hε : 0 < K / 4 := by positivity
  have hlocal := eventually_localBeta_tail_error_le_mul hε
  have htrunc := eventually_denominator_truncation_error_le_mul hε
  have hscale := eventually_four_majorDenominatorCutoff_le_dirichletCutoff
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop N₀
  refine ⟨K / 2, by positivity, ?_⟩
  filter_upwards [hlocal, htrunc, hscale, hN] with n hnLocal hnTrunc hnScale hnN
  intro hodd
  let model : ℂ := ∑ q ∈ Finset.Icc 1 (majorDenominatorCutoff n),
    singularTerm q n * localBetaIntegral (dirichletCutoff n) q n
  let finiteCoeff : ℂ :=
    ∑ q ∈ Finset.Icc 1 (majorDenominatorCutoff n), singularTerm q n
  let J : ℂ := Vinogradov.singularIntegral n n
  let fullCoeff : ℂ := ∑' q : ℕ, singularTerm q n
  have hPpos : 0 < majorDenominatorCutoff n :=
    pow_pos (Erdos387.binaryLogScale_pos n) _
  have hD : 2 ≤ dirichletCutoff n := by omega
  have hModel : ‖model - finiteCoeff * J‖ ≤ (K / 4) * (n : ℝ) ^ 2 := by
    exact (norm_denominator_model_sub_full_le hD).trans hnLocal
  have hFinite : ‖(finiteCoeff - fullCoeff) * J‖ ≤
      (K / 4) * (n : ℝ) ^ 2 := by
    simpa [finiteCoeff, fullCoeff, J] using hnTrunc
  have hJ : K * (n : ℝ) ^ 2 ≤ J.re := by
    simpa [J] using hsing n hnN
  have hSeries : (1 : ℝ) ≤ 2 * singularSeries n := by
    calc
      (1 : ℝ) = 2 * (1 / 2) := by norm_num
      _ ≤ 2 * singularSeries n :=
        mul_le_mul_of_nonneg_left (singularSeries_lower_half_of_odd n hodd)
          (by norm_num)
  have hJnonneg : 0 ≤ J.re := by
    have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    exact (mul_nonneg hK.le hn2).trans hJ
  have hFullEq : (fullCoeff * J).re =
      (2 * singularSeries n) * J.re := by
    rw [show fullCoeff = 2 * (singularSeries n : ℂ) by
      exact tsum_singularTerm_eq_two_singularSeries hodd]
    simp
  have hFull : K * (n : ℝ) ^ 2 ≤ (fullCoeff * J).re := by
    rw [hFullEq]
    exact hJ.trans (le_mul_of_one_le_left hJnonneg hSeries)
  have hReModel : |model.re - (finiteCoeff * J).re| ≤
      (K / 4) * (n : ℝ) ^ 2 := by
    calc
      |model.re - (finiteCoeff * J).re| = |(model - finiteCoeff * J).re| := by
        simp
      _ ≤ ‖model - finiteCoeff * J‖ := Complex.abs_re_le_norm _
      _ ≤ (K / 4) * (n : ℝ) ^ 2 := hModel
  have hReFinite : |(finiteCoeff * J).re - (fullCoeff * J).re| ≤
      (K / 4) * (n : ℝ) ^ 2 := by
    calc
      |(finiteCoeff * J).re - (fullCoeff * J).re| =
          |((finiteCoeff - fullCoeff) * J).re| := by
            congr 1
            simp
            ring
      _ ≤ ‖(finiteCoeff - fullCoeff) * J‖ := Complex.abs_re_le_norm _
      _ ≤ (K / 4) * (n : ℝ) ^ 2 := hFinite
  have h₁ := (neg_le_abs (model.re - (finiteCoeff * J).re)).trans hReModel
  have h₂ := (neg_le_abs ((finiteCoeff * J).re - (fullCoeff * J).re)).trans hReFinite
  linarith only [h₁, h₂, hFull]

/-- Exact splitting of a wrapped major-arc integral into its disjoint local
pieces. -/
theorem integral_torusMajorArcs_eq_sum
    {D P n : ℕ} (hP : 1 ≤ P) (hPD : 2 * P ≤ D) :
    (∫ α in torusMajorArcs D P, integrand n α) =
      ∑ aq ∈ (majorArcCenters_finite P).toFinset,
        ∫ α in torusLocalArc D aq, integrand n α := by
  rw [torusMajorArcs]
  apply MeasureTheory.integral_biUnion_finset
  · intro aq _haq
    exact torusLocalArc_measurableSet D aq
  · simpa using torusLocalArc_pairwise_disjoint hP hPD
  · intro aq _haq
    exact (integrand_continuous n).integrableOn_Icc.mono_set
      (torusLocalArc_subset_Icc D aq)

theorem norm_mu_phi_linearExpSum_le (N q : ℕ) (β : ℝ) :
    ‖(((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
        (Nat.totient q : ℝ) : ℂ) * Vinogradov.linearExpSum N β))‖ ≤
      (N : ℝ) + 1 := by
  let coeff : ℂ :=
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ)
  change ‖coeff * Vinogradov.linearExpSum N β‖ ≤ (N : ℝ) + 1
  have hcoeff : ‖coeff‖ ≤ (1 : ℝ) := by
    simpa [coeff, RCLike.norm_ofReal, RCLike.ofReal_div, abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ (Nat.totient q : ℝ) by positivity)] using
      Vinogradov.mu_phi_quotient_bound q
  calc
    ‖coeff * Vinogradov.linearExpSum N β‖ =
        ‖coeff‖ * ‖Vinogradov.linearExpSum N β‖ := norm_mul _ _
    _ ≤ 1 * ((N : ℝ) + 1) :=
      mul_le_mul hcoeff (Vinogradov.norm_linearExpSum_le N β)
        (norm_nonneg _) (by norm_num)
    _ = (N : ℝ) + 1 := one_mul _

theorem norm_cube_sub_cube_le (x y : ℂ) :
    ‖x ^ 3 - y ^ 3‖ ≤
      ‖x - y‖ * (‖x‖ ^ 2 + ‖x‖ * ‖y‖ + ‖y‖ ^ 2) := by
  rw [show x ^ 3 - y ^ 3 = (x-y) * (x^2 + x*y + y^2) by ring]
  rw [norm_mul]
  gcongr
  calc
    ‖x ^ 2 + x * y + y ^ 2‖ ≤ ‖x ^ 2‖ + ‖x * y‖ + ‖y ^ 2‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖x‖ ^ 2 + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by
      rw [norm_pow, norm_mul, norm_pow]

/-- The discrepancy estimate also includes the modulus `1`; the shared Erdős
387 interface only states its immediate corollary for moduli at least `2`. -/
theorem eventually_weightedProgressionDiscrepancy_le_polylog_positive (C : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ Q a y : ℕ,
      1 ≤ Q → Q ≤ logScale X ^ C → a.Coprime Q →
      2 ≤ y → y ≤ 2 * X →
      BoundedGaps.Maynard.weightedProgressionDiscrepancy y Q a ≤
        (X : ℝ) / (16 * (logScale X ^ C : ℕ)) := by
  filter_upwards [Erdos387.eventually_weightedBV_sum_le_polylog C,
    Erdos387.eventually_binaryLogScale_pow_le_quarterCutoff C,
    eventually_ge_atTop 2] with X hsum hcut hX
  intro Q a y hQ hQscale ha hy hyX
  let Qmax := BoundedGaps.Maynard.modulusCutoff (1 / 4 : ℝ) (2 * X)
  have hQmem : Q ∈ Finset.Icc 1 Qmax :=
    Finset.mem_Icc.2 ⟨hQ, hQscale.trans (by simpa [Qmax, logScale] using hcut)⟩
  have hmaxNonneg (q : ℕ) :
      0 ≤ BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo
        (2 * X) q := by
    rw [← BoundedGaps.BombieriVinogradov.maxWeightedProgressionDiscrepancyUpTo_eq_maynard]
    exact BoundedGaps.BombieriVinogradov.maxWeightedProgressionDiscrepancyUpTo_nonneg
      (2 * X) q
  have hmaxLe :
      BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo (2 * X) Q ≤
        ∑ q ∈ Finset.Icc 1 Qmax,
          BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo
            (2 * X) q := by
    exact Finset.single_le_sum (fun q hq => hmaxNonneg q) hQmem
  exact (Erdos387.weightedProgressionDiscrepancy_le_maxUpTo
    (by omega) hy hyX (by omega) ha).trans
      (hmaxLe.trans (by simpa [Qmax, logScale] using hsum))

/-- The proved uniform progression estimate, including the harmless endpoints
`m=0,1`, in the range needed by the major arcs. -/
theorem eventually_majorArc_progression_estimate :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ,
      0 < q → q ≤ logScale N ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ N →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (N : ℝ) / (16 * (logScale N ^ 1000 : ℕ)) + 1 := by
  filter_upwards
    [eventually_weightedProgressionDiscrepancy_le_polylog_positive 1000]
      with N hdisc
  intro q hq hqL r hr hcop m hm
  by_cases hm2 : 2 ≤ m
  · have hLpow : logScale N ^ 20 ≤ logScale N ^ 1000 :=
      Nat.pow_le_pow_right (by simpa [logScale] using Erdos387.binaryLogScale_pos N)
        (by omega)
    have h := hdisc q r m (by omega) (hqL.trans hLpow) hcop hm2 (by omega)
    unfold BoundedGaps.Maynard.weightedProgressionDiscrepancy at h
    exact h.trans (le_add_of_nonneg_right zero_le_one)
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · have hpsi : psiAP 0 q r = 0 := by
        rw [psiAP, BoundedGaps.Maynard.chebyshevProgressionSum]
        simp
      rw [hpsi]
      norm_num only [Nat.cast_zero, zero_div, sub_zero, abs_zero]
      exact add_nonneg
        (div_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))) zero_le_one
    · have hphiNat : 0 < Nat.totient q := Nat.totient_pos.mpr hq
      have hphi : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast hphiNat
      have hpsi : psiAP 1 q r = 0 := by
        classical
        rw [psiAP_eq_range_filter, Finset.sum_filter]
        norm_num [Finset.sum_range_succ, ArithmeticFunction.map_zero,
          ArithmeticFunction.vonMangoldt_apply_one]
      have hfrac : (1 : ℝ) / (Nat.totient q : ℝ) ≤ 1 :=
        (div_le_one (by positivity)).2 hphi
      have hfrac0 : 0 ≤ (1 : ℝ) / (Nat.totient q : ℝ) := by positivity
      have hNterm : 0 ≤ (N : ℝ) / (16 * (logScale N ^ 1000 : ℕ)) :=
        div_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      rw [hpsi]
      norm_num only [Nat.cast_one, zero_sub, abs_neg, abs_of_nonneg hfrac0]
      exact hfrac.trans (by linarith)

/- The first major-arc aggregation draft is retained temporarily below while
the verified, lower-complexity version is integrated after it.

/-- A convenient real envelope for the local major-arc approximation error. -/
noncomputable def majorApproxError (n : ℕ) : ℝ :=
  40 * ((n : ℝ) / (logScale n : ℝ) ^ 880 +
    (logScale n : ℝ) ^ 120 +
    (logScale n : ℝ) ^ 20 * Real.sqrt ((n : ℝ) + 1))

lemma majorApprox_algebra {n : ℕ} {L : ℝ} (hLpos : 0 < L) :
    L ^ 20 * (((n : ℝ) / (16 * L ^ 1000) + 2) * (17 * L ^ 100)) ≤
      40 * ((n : ℝ) / L ^ 880 + L ^ 120) := by
  have hLne : L ≠ 0 := hLpos.ne'
  have h1000 : L ^ 1000 = L ^ 880 * L ^ 120 := by rw [← pow_add]
  have h120 : L ^ 120 = L ^ 20 * L ^ 100 := by rw [← pow_add]
  rw [h1000, h120]
  field_simp [hLne]
  nlinarith [Nat.cast_nonneg (α := ℝ) n, pow_pos hLpos 880,
    pow_pos hLpos 120]

Superseded monolithic proof, replaced below by split default-limit helpers.
theorem norm_local_sum_sub_model_le_majorApproxError
    {n D a q : ℕ} {β : ℝ}
    (hn : 1 ≤ n) (hq : 0 < q) (hqP : q ≤ majorDenominatorCutoff n)
    (haq : a.Coprime q)
    (hβ : |β| < 1 / ((q : ℝ) * (D : ℝ)))
    (hnD : (n : ℝ) ≤
      2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
      |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
        (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1) :
    ‖Vinogradov.vonMangoldtExpSum
        (Vinogradov.rationalCenter a q + β) n -
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
          (Nat.totient q : ℝ) : ℝ) : ℂ) *
        Vinogradov.linearExpSum n β)‖ ≤ majorApproxError n := by
  have hDpos : 0 < D := by
    by_contra hDz
    have : D = 0 := Nat.eq_zero_of_not_pos hDz
    subst D
    simp only [Nat.cast_zero, mul_zero, div_zero] at hβ
    exact (not_lt_of_ge (abs_nonneg β)) hβ
  let L : ℝ := logScale n
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hqP' : (q : ℝ) ≤ L ^ 20 := by
    change (q : ℝ) ≤ (logScale n : ℝ) ^ 20
    have hqPcast : (q : ℝ) ≤ ((logScale n ^ 20 : ℕ) : ℝ) := by
      exact_mod_cast hqP
    rw [Nat.cast_pow] at hqPcast
    exact hqPcast
  have hbetaN : |β| * (n : ℝ) ≤ 2 * L ^ 100 := by
    calc
      |β| * (n : ℝ) ≤ (1 / ((q : ℝ) * (D : ℝ))) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hβ.le (Nat.cast_nonneg _)
      _ ≤ (1 / (D : ℝ)) * (n : ℝ) := by
        gcongr
        exact one_le_cast.mpr (Nat.succ_le_iff.mpr hq)
      _ = (n : ℝ) / (D : ℝ) := by ring
      _ ≤ 2 * L ^ 100 := by
        rw [div_le_iff₀ hDR]
        simpa [L, mul_assoc] using hnD
  have hfactor : 1 + 2 * Real.pi * |β| * (n : ℝ) ≤ 17 * L ^ 100 := by
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hLone : (1 : ℝ) ≤ L := by
      exact_mod_cast Erdos387.binaryLogScale_pos n
    have hLpow : 1 ≤ L ^ 100 := one_le_pow₀ hLone
    nlinarith [mul_le_mul_of_nonneg_left hbetaN (mul_nonneg (by positivity) hpi),
      Real.pi_pos]
  have hphi : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hinv : ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hphi)
  have hE : 0 ≤ (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 := by
    exact add_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))) zero_le_one
  have happrox := vonMangoldtExpSum_local_approximation
    (N := n) (a := a) (q := q) (β := β)
    (E := (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    hq haq hE hAP
  have hcardNat : q.primeFactors.card ≤ q + 1 := by
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_range]
    have hpdvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    exact Nat.lt_succ_of_le (Nat.le_of_dvd hq hpdvd)
  have hcard : (q.primeFactors.card : ℝ) ≤ 2 * (q : ℝ) := by
    have hq1 : 1 ≤ q := Nat.succ_le_iff.mpr hq
    exact_mod_cast hcardNat.trans (by omega : q + 1 ≤ 2 * q)
  have hlog : Real.log ((n : ℝ) + 1) ≤
      2 * Real.sqrt ((n : ℝ) + 1) := by
    have h := Real.log_le_rpow_div
      (x := (n : ℝ) + 1) (by positivity) (ε := (1 : ℝ) / 2) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith
  have hfirst :
      (q : ℝ) *
          (((n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 +
              ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖) *
            (1 + 2 * Real.pi * |β| * (n : ℝ))) ≤
        40 * ((n : ℝ) / L ^ 880 + L ^ 120) := by
    calc
      (q : ℝ) *
          (((n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 +
              ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖) *
            (1 + 2 * Real.pi * |β| * (n : ℝ))) ≤
        L ^ 20 * (((n : ℝ) / (16 * L ^ 1000) + 2) *
          (17 * L ^ 100)) := by
            gcongr
            simpa [L] using hinv
      _ ≤ 40 * ((n : ℝ) / L ^ 880 + L ^ 120) := by
        have hLne : L ≠ 0 := hLpos.ne'
        have h1000 : L ^ 1000 = L ^ 880 * L ^ 120 := by
          rw [← pow_add]
        have h120 : L ^ 120 = L ^ 20 * L ^ 100 := by
          rw [← pow_add]
        rw [h1000, h120]
        field_simp [hLne]
        nlinarith [Nat.cast_nonneg (α := ℝ) n, pow_pos hLpos 880,
          pow_pos hLpos 120]
  have hsecond :
      (q.primeFactors.card : ℝ) * Real.log ((n : ℝ) + 1) ≤
        40 * (L ^ 20 * Real.sqrt ((n : ℝ) + 1)) := by
    calc
      (q.primeFactors.card : ℝ) * Real.log ((n : ℝ) + 1) ≤
          (2 * (q : ℝ)) * (2 * Real.sqrt ((n : ℝ) + 1)) := by
        exact mul_le_mul hcard hlog (Real.log_nonneg (by nlinarith)) (by positivity)
      _ ≤ 40 * (L ^ 20 * Real.sqrt ((n : ℝ) + 1)) := by
        have hsqrt : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right hqP' hsqrt]
  exact happrox.trans (by
    unfold majorApproxError
    dsimp [L] at hfirst hsecond ⊢
    linarith)

theorem norm_vonMangoldtExpSum_le_eight_succ (n : ℕ) (α : ℝ) :
    ‖Vinogradov.vonMangoldtExpSum α n‖ ≤ 8 * ((n : ℝ) + 1) := by
  have hψ := Vinogradov.norm_vonMangoldtExpSum_le_psi α n
  have hcheb := Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (Nat.cast_nonneg _)
  have hlog : Real.log 4 + 4 ≤ 8 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  calc
    ‖Vinogradov.vonMangoldtExpSum α n‖ ≤ Chebyshev.psi n := hψ
    _ ≤ (Real.log 4 + 4) * (n : ℝ) := hcheb
    _ ≤ 8 * ((n : ℝ) + 1) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith

theorem norm_integrand_sub_localMainIntegrand_le
    {n a q : ℕ} {α R : ℝ} (hR : 0 ≤ R)
    (hsum :
      ‖Vinogradov.vonMangoldtExpSum α n -
        (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
            (Nat.totient q : ℝ) : ℝ) : ℂ) *
          Vinogradov.linearExpSum n
            (α - Vinogradov.rationalCenter a q))‖ ≤ R) :
    ‖integrand n α - localMainIntegrand n a q α‖ ≤
      100 * R * ((n : ℝ) + 1) ^ 2 := by
  let S : ℂ := Vinogradov.vonMangoldtExpSum α n
  let M : ℂ := (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
      (Nat.totient q : ℝ) : ℝ) : ℂ) *
    Vinogradov.linearExpSum n (α - Vinogradov.rationalCenter a q))
  have hS : ‖S‖ ≤ 8 * ((n : ℝ) + 1) :=
    norm_vonMangoldtExpSum_le_eight_succ n α
  have hM : ‖M‖ ≤ (n : ℝ) + 1 :=
    by
      dsimp [M]
      exact norm_mu_phi_linearExpSum_le n q
        (α - Vinogradov.rationalCenter a q)
  have hn1 : 0 ≤ (n : ℝ) + 1 := by positivity
  have hquad : ‖S‖ ^ 2 + ‖S‖ * ‖M‖ + ‖M‖ ^ 2 ≤
      100 * ((n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (‖S‖ - 8 * ((n : ℝ) + 1)),
      sq_nonneg (‖M‖ - ((n : ℝ) + 1)), norm_nonneg S, norm_nonneg M]
  have hrearrange : integrand n α - localMainIntegrand n a q α =
      (S ^ 3 - M ^ 3) * Vinogradov.negAddChar α n := by
    dsimp [integrand, localMainIntegrand, S, M]
    ring
  rw [hrearrange, norm_mul, Vinogradov.norm_negAddChar, mul_one]
  calc
    ‖S ^ 3 - M ^ 3‖ ≤
        ‖S - M‖ * (‖S‖ ^ 2 + ‖S‖ * ‖M‖ + ‖M‖ ^ 2) :=
      norm_cube_sub_cube_le S M
    _ ≤ R * (100 * ((n : ℝ) + 1) ^ 2) :=
      mul_le_mul hsum hquad (by positivity) hR
    _ = 100 * R * ((n : ℝ) + 1) ^ 2 := by ring

Superseded combined wrapped-arc proof; split helpers below stay under the
default per-declaration heartbeat limit.
theorem norm_integrand_sub_localMain_on_torusLocalArc
    {n D P : ℕ} (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    {aq : ℕ × ℕ} (haq : aq ∈ Vinogradov.majorArcCenters P)
    {α : ℝ} (hα : α ∈ torusLocalArc D aq) :
    ‖integrand n α - localMainIntegrand n aq.1 aq.2 α‖ ≤
      100 * majorApproxError n * ((n : ℝ) + 1) ^ 2 := by
  have hR : 0 ≤ majorApproxError n := by
    unfold majorApproxError
    positivity
  apply norm_integrand_sub_localMainIntegrand_le hR
  by_cases hend : aq = (0, 1)
  · subst aq
    simp only [torusLocalArc, if_pos rfl, Set.mem_union] at hα
    have hone : 1 ≤ logScale n ^ 20 :=
      pow_pos (Erdos387.binaryLogScale_pos n) _
    rcases hα with hleft | hright
    · have hsum := norm_local_sum_sub_model_le_majorApproxError
        (n := n) (D := D) (a := 0) (q := 1) (β := α)
        hn (by norm_num) (by simpa [majorDenominatorCutoff] using
          Vinogradov.majorArcCenters_q_le haq) (by simp)
        (by simpa [Vinogradov.rationalCenter] using hleft.2) hnD
        (hAP 1 (by norm_num) (by simpa [majorDenominatorCutoff] using
          Vinogradov.majorArcCenters_q_le haq))
      simpa [Vinogradov.rationalCenter] using hsum
    · have hDpos : 0 < D := by
        by_contra hDz
        have : D = 0 := Nat.eq_zero_of_not_pos hDz
        subst D
        simp [rightEndpointArc] at hright
      have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
      have hdist : |α - 1| < 1 / (D : ℝ) := by
        rw [abs_lt]
        constructor
        · have := hright.1
          dsimp [rightEndpointArc] at this
          linarith
        · have hinv : 0 < 1 / (D : ℝ) := by positivity
          linarith [hright.2]
      have hlinear : Vinogradov.linearExpSum n (α - 1) =
          Vinogradov.linearExpSum n α := by
        unfold Vinogradov.linearExpSum
        refine Finset.sum_congr rfl ?_
        intro m _hm
        exact Vinogradov.addChar_sub_one α m
      have hsum := norm_local_sum_sub_model_le_majorApproxError
        (n := n) (D := D) (a := 1) (q := 1) (β := α - 1)
        hn (by norm_num) (by simpa [majorDenominatorCutoff] using
          Vinogradov.majorArcCenters_q_le haq) (by simp)
        (by simpa using hdist) hnD
        (hAP 1 (by norm_num) (by simpa [majorDenominatorCutoff] using
          Vinogradov.majorArcCenters_q_le haq))
      simpa [Vinogradov.rationalCenter, hlinear] using hsum
  · have hq := Vinogradov.majorArcCenters_q_pos haq
    have hqP := Vinogradov.majorArcCenters_q_le haq
    have hcop := Vinogradov.majorArcCenters_coprime haq
    have hplain : α ∈ Vinogradov.localMajorArcExplicit D aq.1 aq.2 := by
      simpa [torusLocalArc, hend] using hα
    have hsum := norm_local_sum_sub_model_le_majorApproxError
      (n := n) (D := D) (a := aq.1) (q := aq.2)
      (β := α - Vinogradov.rationalCenter aq.1 aq.2)
      hn hq hqP hcop hplain.2 hnD
      (hAP aq.2 hq (by simpa [majorDenominatorCutoff] using hqP))
    simpa using hsum

theorem localMajorArcExplicit_volume_real_le
    (D a q : ℕ) (hD : 0 < D) (hq : 0 < q) :
    (volume : Measure ℝ).real (Vinogradov.localMajorArcExplicit D a q) ≤
      2 / ((q : ℝ) * (D : ℝ)) := by
  let center : ℝ := (a : ℝ) / (q : ℝ)
  let r : ℝ := 1 / ((q : ℝ) * (D : ℝ))
  let t : Set ℝ := Set.Ioo (center - r) (center + r)
  have hsubset : Vinogradov.localMajorArcExplicit D a q ⊆ t := by
    intro α hα
    have hclose : |α - center| < r := by
      simpa [Vinogradov.localMajorArcExplicit, center, r] using hα.2
    rcases abs_lt.mp hclose with ⟨hleft, hright⟩
    constructor <;> linarith
  have hmeasure : (volume : Measure ℝ)
      (Vinogradov.localMajorArcExplicit D a q) ≤ volume t := measure_mono hsubset
  have ht : volume t = ENNReal.ofReal (2 / ((q : ℝ) * (D : ℝ))) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  have ht_ne : volume t ≠ ⊤ := by rw [ht]; exact ENNReal.ofReal_ne_top
  have hs_ne : (volume : Measure ℝ)
      (Vinogradov.localMajorArcExplicit D a q) ≠ ⊤ :=
    ne_top_of_le_ne_top ht_ne hmeasure
  have hle := (ENNReal.toReal_le_toReal hs_ne ht_ne).mpr hmeasure
  have hnonneg : 0 ≤ 2 / ((q : ℝ) * (D : ℝ)) := by positivity
  have htwo :
      (D : ℝ)⁻¹ * (q : ℝ)⁻¹ + (D : ℝ)⁻¹ * (q : ℝ)⁻¹ =
        2 / ((q : ℝ) * (D : ℝ)) := by ring
  simpa [Measure.real_def, ht, ENNReal.toReal_ofReal hnonneg, t, center, r, htwo]
    using hle

theorem torusLocalArc_volume_real_le
    {D P : ℕ} (hD : 2 ≤ D) {aq : ℕ × ℕ}
    (haq : aq ∈ Vinogradov.majorArcCenters P) :
    (volume : Measure ℝ).real (torusLocalArc D aq) ≤ 3 / (D : ℝ) := by
  have hDpos : 0 < D := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hq := Vinogradov.majorArcCenters_q_pos haq
  by_cases hend : aq = (0, 1)
  · subst aq
    rw [torusLocalArc, if_pos rfl]
    have hleft_ne : (volume : Measure ℝ)
        (Vinogradov.localMajorArcExplicit D 0 1) ≠ ⊤ := by
      exact ne_top_of_le_ne_top (by simp)
        (Vinogradov.localMajorArcExplicit_volume_le_one D 0 1)
    have hright_ne : (volume : Measure ℝ) (rightEndpointArc D) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤)
      simpa [Real.volume_Icc] using
        (measure_mono (rightEndpointArc_subset_Icc D) :
          (volume : Measure ℝ) (rightEndpointArc D) ≤ volume (Set.Icc (0 : ℝ) 1))
    have hu : (volume : Measure ℝ)
        (Vinogradov.localMajorArcExplicit D 0 1 ∪ rightEndpointArc D) ≤
      volume (Vinogradov.localMajorArcExplicit D 0 1) +
        volume (rightEndpointArc D) := measure_union_le _ _
    have hreal := (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hleft_ne, hright_ne⟩) hu)
      (ENNReal.add_ne_top.mpr ⟨hleft_ne, hright_ne⟩)).mpr hu
    rw [ENNReal.toReal_add hleft_ne hright_ne] at hreal
    have hright : (volume : Measure ℝ).real (rightEndpointArc D) =
        1 / (D : ℝ) := by
      rw [Measure.real_def, rightEndpointArc, Real.volume_Ioc]
      have hnonneg : 0 ≤ (1 : ℝ) - (1 - 1 / (D : ℝ)) := by
        have : 0 ≤ 1 / (D : ℝ) := by positivity
        linarith
      rw [ENNReal.toReal_ofReal hnonneg]
      ring
    calc
      (volume : Measure ℝ).real
          (Vinogradov.localMajorArcExplicit D 0 1 ∪ rightEndpointArc D) ≤
        (volume : Measure ℝ).real (Vinogradov.localMajorArcExplicit D 0 1) +
          (volume : Measure ℝ).real (rightEndpointArc D) := by
            simpa [Measure.real_def] using hreal
      _ ≤ 2 / ((1 : ℝ) * D) + 1 / (D : ℝ) := by
        have hleft : (volume : Measure ℝ).real
            (Vinogradov.localMajorArcExplicit D 0 1) ≤
              2 / ((1 : ℝ) * (D : ℝ)) := by
          simpa only [Nat.cast_one] using
            localMajorArcExplicit_volume_real_le D 0 1 hDpos one_pos
        exact add_le_add hleft (le_of_eq hright)
      _ = 3 / (D : ℝ) := by ring
  · rw [torusLocalArc, if_neg hend]
    calc
      (volume : Measure ℝ).real
          (Vinogradov.localMajorArcExplicit D aq.1 aq.2) ≤
        2 / ((aq.2 : ℝ) * (D : ℝ)) :=
          localMajorArcExplicit_volume_real_le D aq.1 aq.2 hDpos hq
      _ ≤ 3 / (D : ℝ) := by
        have hqR : (1 : ℝ) ≤ aq.2 := by exact_mod_cast hq
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hi : ((aq.2 : ℝ) * (D : ℝ))⁻¹ ≤ ((D : ℝ))⁻¹ := by
          exact inv_anti₀ (by positivity) (by nlinarith)
        nlinarith [inv_pos.mpr hDR]

theorem majorArcCenters_card_le (P : ℕ) :
    (majorArcCenters_finite P).toFinset.card ≤ (P + 1) ^ 2 := by
  have hsub : (majorArcCenters_finite P).toFinset ⊆
      Finset.range (P + 1) ×ˢ Finset.range (P + 1) := by
    intro aq haq
    have hc : aq ∈ Vinogradov.majorArcCenters P :=
      (Set.Finite.mem_toFinset (majorArcCenters_finite P)).mp haq
    have ha := Vinogradov.majorArcCenters_a_lt_q hc
    have hqP := Vinogradov.majorArcCenters_q_le hc
    rw [Finset.mem_product]
    exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  calc
    (majorArcCenters_finite P).toFinset.card ≤
        (Finset.range (P + 1) ×ˢ Finset.range (P + 1)).card :=
      Finset.card_le_card hsub
    _ = (P + 1) ^ 2 := by simp [pow_two]

theorem norm_local_integral_sub_model_le
    {n D P : ℕ} (hD : 2 ≤ D) (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    {aq : ℕ × ℕ} (haq : aq ∈ Vinogradov.majorArcCenters P) :
    ‖(∫ α in torusLocalArc D aq, integrand n α) -
        localModelIntegral D n aq‖ ≤
      (100 * majorApproxError n * ((n : ℝ) + 1) ^ 2) *
        (3 / (D : ℝ)) := by
  have hcont : Continuous (fun α : ℝ =>
      integrand n α - localMainIntegrand n aq.1 aq.2 α) :=
    (integrand_continuous n).sub (localMainIntegrand_continuous n aq.1 aq.2)
  have hfinite : volume (torusLocalArc D aq) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (torusLocalArc_subset_Icc D aq)) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hbound := norm_setIntegral_le_of_norm_le_const hfinite
    (fun α hα => norm_integrand_sub_localMain_on_torusLocalArc hn hnD hAP haq hα)
  rw [localModelIntegral]
  rw [← MeasureTheory.integral_sub
    ((integrand_continuous n).integrableOn_Icc.mono_set
      (torusLocalArc_subset_Icc D aq))
    ((localMainIntegrand_continuous n aq.1 aq.2).integrableOn_Icc.mono_set
      (torusLocalArc_subset_Icc D aq))]
  have hconst0 : 0 ≤ 100 * majorApproxError n * ((n : ℝ) + 1) ^ 2 := by
    unfold majorApproxError
    positivity
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (torusLocalArc_volume_real_le hD haq) hconst0)

theorem norm_major_integral_sub_denominator_model_le
    {n D P : ℕ} (hP : 1 ≤ P) (hPD : 2 * P ≤ D) (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1) :
    ‖(∫ α in torusMajorArcs D P, integrand n α) -
        ∑ q ∈ Finset.Icc 1 P,
          singularTerm q n * localBetaIntegral D q n‖ ≤
      ((P + 1 : ℕ) : ℝ) ^ 2 *
        ((100 * majorApproxError n * ((n : ℝ) + 1) ^ 2) *
          (3 / (D : ℝ))) := by
  have hD : 2 ≤ D := by omega
  rw [integral_torusMajorArcs_eq_sum hP hPD,
    ← sum_localModelIntegral_eq_denominator_sum D P n hD]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ aq ∈ (majorArcCenters_finite P).toFinset,
        ((∫ α in torusLocalArc D aq, integrand n α) -
          localModelIntegral D n aq)‖ ≤
      ∑ aq ∈ (majorArcCenters_finite P).toFinset,
        ‖(∫ α in torusLocalArc D aq, integrand n α) -
          localModelIntegral D n aq‖ := norm_sum_le _ _
    _ ≤ ∑ _aq ∈ (majorArcCenters_finite P).toFinset,
        ((100 * majorApproxError n * ((n : ℝ) + 1) ^ 2) *
          (3 / (D : ℝ))) := by
      refine Finset.sum_le_sum fun aq haq => ?_
      exact norm_local_integral_sub_model_le hD hn hnD hAP
        ((Set.Finite.mem_toFinset (majorArcCenters_finite P)).mp haq)
    _ = ((majorArcCenters_finite P).toFinset.card : ℝ) *
        ((100 * majorApproxError n * ((n : ℝ) + 1) ^ 2) *
          (3 / (D : ℝ))) := by simp
    _ ≤ ((P + 1 : ℕ) : ℝ) ^ 2 *
        ((100 * majorApproxError n * ((n : ℝ) + 1) ^ 2) *
          (3 / (D : ℝ))) := by
      have hcard := majorArcCenters_card_le P
      have hcardR : ((majorArcCenters_finite P).toFinset.card : ℝ) ≤
          ((P + 1 : ℕ) : ℝ) ^ 2 := by
        norm_num only [Nat.cast_pow]
        exact_mod_cast hcard
      have hfactor0 : 0 ≤
          (100 * majorApproxError n * ((n : ℝ) + 1) ^ 2) *
            (3 / (D : ℝ)) := by
        unfold majorApproxError
        positivity
      exact mul_le_mul_of_nonneg_right hcardR hfactor0

theorem major_integral_error_envelope_le
    {n D : ℕ} (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100) :
    (((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ^ 2 *
        ((100 * majorApproxError n * ((n : ℝ) + 1) ^ 2) *
          (3 / (D : ℝ)))) ≤
      384000 * ((n : ℝ) ^ 2 / (logScale n : ℝ) ^ 740 +
        (n : ℝ) * (logScale n : ℝ) ^ 260 +
        (n : ℝ) * (logScale n : ℝ) ^ 160 *
          Real.sqrt ((n : ℝ) + 1)) := by
  let L : ℝ := logScale n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hDpos : 0 < D := by
    by_contra hDz
    have : D = 0 := Nat.eq_zero_of_not_pos hDz
    subst D
    norm_num at hnD
    linarith
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hP : ((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ≤ 2 * L ^ 20 := by
    have hLone : (1 : ℝ) ≤ L := by
      dsimp [L]
      exact_mod_cast Erdos387.binaryLogScale_pos n
    have hpow : (1 : ℝ) ≤ L ^ 20 := one_le_pow₀ hLone
    simp only [Nat.cast_add, Nat.cast_one, majorDenominatorCutoff, Nat.cast_pow]
    dsimp [L] at hpow ⊢
    linarith
  have hn1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ 2*n)
  have hinvD : 3 / (D : ℝ) ≤ 6 * L ^ 100 / (n : ℝ) := by
    rw [div_le_div_iff₀ hDR hnR]
    dsimp [L] at hnD ⊢
    nlinarith
  calc
    (((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ^ 2 *
        ((100 * majorApproxError n * ((n : ℝ) + 1) ^ 2) *
          (3 / (D : ℝ)))) ≤
      (2 * L ^ 20) ^ 2 *
        ((100 * majorApproxError n * (2 * (n : ℝ)) ^ 2) *
          (6 * L ^ 100 / (n : ℝ))) := by
      gcongr
    _ = 384000 * ((n : ℝ) ^ 2 / L ^ 740 +
        (n : ℝ) * L ^ 260 +
        (n : ℝ) * L ^ 160 * Real.sqrt ((n : ℝ) + 1)) := by
      unfold majorApproxError
      dsimp [L]
      field_simp [hnR.ne', hLpos.ne']
      ring

theorem eventually_major_integral_error_envelope_le_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      184320 * ((n : ℝ) ^ 2 / (logScale n : ℝ) ^ 738 +
        (n : ℝ) * (logScale n : ℝ) ^ 262 +
        (n : ℝ) * (logScale n : ℝ) ^ 162 *
          Real.sqrt ((n : ℝ) + 1)) ≤ ε * (n : ℝ) ^ 2 := by
  let C : ℝ := 552960 / ε
  have hC : 0 < C := by dsimp [C]; positivity
  have hLreal : Tendsto (fun n : ℕ => (logScale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_logScale
  have hLlarge := hLreal.eventually_ge_atTop C
  have hL738Nat : Tendsto (fun n : ℕ => logScale n ^ 738) atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : 738 ≠ 0)).comp tendsto_logScale
  have hL738 : Tendsto (fun n : ℕ => ((logScale n ^ 738 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hL738Nat
  have hL738large := hL738.eventually_ge_atTop C
  filter_upwards [hLlarge, hL738large,
    Erdos387.eventually_binaryLogScale_pow_le_half 263,
    Erdos387.eventually_binaryLogScale_pow_le_half 326,
    eventually_ge_atTop (1 : ℕ)] with n hnL hn738 hn263 hn326 hn
  let L : ℝ := logScale n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hnL' : C ≤ L := by simpa [L] using hnL
  have hn738' : C ≤ L ^ 738 := by
    simpa only [L, Nat.cast_pow] using hn738
  have hn263' : L ^ 263 ≤ (n : ℝ) / 2 := by
    have hcast : (((logScale n ^ 263 : ℕ) : ℝ)) ≤
        (((n / 2 : ℕ) : ℝ)) := by exact_mod_cast hn263
    calc
      L ^ 263 = ((logScale n ^ 263 : ℕ) : ℝ) := by rw [Nat.cast_pow]
      _ ≤ ((n / 2 : ℕ) : ℝ) := hcast
      _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hn326' : L ^ 326 ≤ (n : ℝ) / 2 := by
    have hcast : (((logScale n ^ 326 : ℕ) : ℝ)) ≤
        (((n / 2 : ℕ) : ℝ)) := by exact_mod_cast hn326
    calc
      L ^ 326 = ((logScale n ^ 326 : ℕ) : ℝ) := by rw [Nat.cast_pow]
      _ ≤ ((n / 2 : ℕ) : ℝ) := hcast
      _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hA : 184320 * ((n : ℝ) ^ 2 / L ^ 738) ≤
      (ε / 3) * (n : ℝ) ^ 2 := by
    have hden : 552960 ≤ ε * L ^ 738 := by
      have := (div_le_iff₀ hε).mp (by simpa [C] using hn738')
      nlinarith
    have hLpowpos : 0 < L ^ 738 := pow_pos hLpos _
    have hratio : 184320 / L ^ 738 ≤ ε / 3 := by
      rw [div_le_iff₀ hLpowpos]
      nlinarith
    calc
      184320 * ((n : ℝ) ^ 2 / L ^ 738) =
          (184320 / L ^ 738) * (n : ℝ) ^ 2 := by ring
      _ ≤ (ε / 3) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
  have hCL262 : C * L ^ 262 ≤ L ^ 263 := by
    calc
      C * L ^ 262 ≤ L * L ^ 262 :=
        mul_le_mul_of_nonneg_right hnL' (pow_nonneg hLpos.le _)
      _ = L ^ 263 := by ring
  have hB : 184320 * ((n : ℝ) * L ^ 262) ≤
      (ε / 3) * (n : ℝ) ^ 2 := by
    have hmain : C * L ^ 262 ≤ (n : ℝ) / 2 := hCL262.trans hn263'
    have hscaled := mul_le_mul_of_nonneg_left hmain hε.le
    dsimp [C] at hscaled
    field_simp [hε.ne'] at hscaled
    nlinarith [Nat.cast_nonneg (α := ℝ) n, pow_nonneg hLpos.le 262]
  have hCL162 : C * L ^ 162 ≤ L ^ 163 := by
    calc
      C * L ^ 162 ≤ L * L ^ 162 :=
        mul_le_mul_of_nonneg_right hnL' (pow_nonneg hLpos.le _)
      _ = L ^ 163 := by ring
  have hroot : L ^ 163 * Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) := by
    have hleft0 : 0 ≤ L ^ 163 * Real.sqrt ((n : ℝ) + 1) :=
      mul_nonneg (pow_nonneg hLpos.le _) (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ hleft0 hnR.le).mp
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (show 0 ≤ n + 1 by omega))]
    have hpow : (L ^ 163) ^ 2 = L ^ 326 := by
      rw [show (326 : ℕ) = 163 * 2 by norm_num, pow_mul]
    rw [hpow]
    have hprod := mul_le_mul_of_nonneg_right hn326'
      (show 0 ≤ (n : ℝ) + 1 by positivity)
    calc
      L ^ 326 * ((n : ℝ) + 1) ≤ ((n : ℝ) / 2) * ((n : ℝ) + 1) := hprod
      _ ≤ (n : ℝ) ^ 2 := by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
  have hCroot : C * L ^ 162 * Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hCL162 (Real.sqrt_nonneg _)).trans hroot
  have hCterm : 184320 * ((n : ℝ) * L ^ 162 *
      Real.sqrt ((n : ℝ) + 1)) ≤ (ε / 3) * (n : ℝ) ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hCroot hε.le
    dsimp [C] at hscaled
    field_simp [hε.ne'] at hscaled
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  dsimp [L] at hA hB hCterm ⊢
  linarith

theorem eventually_major_integral_error_envelope_le_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      384000 * ((n : ℝ) ^ 2 / (logScale n : ℝ) ^ 740 +
        (n : ℝ) * (logScale n : ℝ) ^ 260 +
        (n : ℝ) * (logScale n : ℝ) ^ 160 *
          Real.sqrt ((n : ℝ) + 1)) ≤ ε * (n : ℝ) ^ 2 := by
  let C : ℝ := 1152000 / ε
  have hC : 0 < C := by dsimp [C]; positivity
  have hLreal : Tendsto (fun n : ℕ => (logScale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_logScale
  have hLlarge := hLreal.eventually_ge_atTop C
  have hL740Nat : Tendsto (fun n : ℕ => logScale n ^ 740) atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : 740 ≠ 0)).comp tendsto_logScale
  have hL740 : Tendsto (fun n : ℕ => ((logScale n ^ 740 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hL740Nat
  have hL740large := hL740.eventually_ge_atTop C
  filter_upwards [hLlarge, hL740large,
    Erdos387.eventually_binaryLogScale_pow_le_half 261,
    Erdos387.eventually_binaryLogScale_pow_le_half 322,
    eventually_ge_atTop (1 : ℕ)] with n hnL hn740 hn261 hn322 hn
  let L : ℝ := logScale n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hnL' : C ≤ L := by simpa [L] using hnL
  have hn740' : C ≤ L ^ 740 := by
    simpa only [L, Nat.cast_pow] using hn740
  have hn261' : L ^ 261 ≤ (n : ℝ) / 2 := by
    have hcast : (((logScale n ^ 261 : ℕ) : ℝ)) ≤
        (((n / 2 : ℕ) : ℝ)) := by exact_mod_cast hn261
    calc
      L ^ 261 = ((logScale n ^ 261 : ℕ) : ℝ) := by
        simp [L, Nat.cast_pow]
      _ ≤ ((n / 2 : ℕ) : ℝ) := hcast
      _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hn322' : L ^ 322 ≤ (n : ℝ) / 2 := by
    have hcast : (((logScale n ^ 322 : ℕ) : ℝ)) ≤
        (((n / 2 : ℕ) : ℝ)) := by exact_mod_cast hn322
    calc
      L ^ 322 = ((logScale n ^ 322 : ℕ) : ℝ) := by
        simp [L, Nat.cast_pow]
      _ ≤ ((n / 2 : ℕ) : ℝ) := hcast
      _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hA : 384000 * ((n : ℝ) ^ 2 / L ^ 740) ≤
      (ε / 3) * (n : ℝ) ^ 2 := by
    have hden : 1152000 ≤ ε * L ^ 740 := by
      have := (div_le_iff₀ hε).mp (by simpa [C] using hn740')
      nlinarith
    have hLpowpos : 0 < L ^ 740 := pow_pos hLpos _
    rw [div_eq_mul_inv]
    have hratio : 384000 * (L ^ 740)⁻¹ ≤ ε / 3 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
      apply (mul_inv_le_iff₀ hLpowpos).2
      nlinarith
    nlinarith [sq_nonneg (n : ℝ)]
  have hCL260 : C * L ^ 260 ≤ L ^ 261 := by
    calc
      C * L ^ 260 ≤ L * L ^ 260 :=
        mul_le_mul_of_nonneg_right hnL' (pow_nonneg hLpos.le _)
      _ = L ^ 261 := by ring
  have hB : 384000 * ((n : ℝ) * L ^ 260) ≤
      (ε / 3) * (n : ℝ) ^ 2 := by
    have hmain : C * L ^ 260 ≤ (n : ℝ) / 2 := hCL260.trans hn261'
    have hscaled : 1152000 * L ^ 260 ≤ ε * ((n : ℝ) / 2) := by
      have := mul_le_mul_of_nonneg_left hmain hε.le
      dsimp [C] at this
      field_simp [hε.ne'] at this
      nlinarith
    nlinarith [Nat.cast_nonneg (α := ℝ) n, pow_nonneg hLpos.le 260]
  have hCL160 : C * L ^ 160 ≤ L ^ 161 := by
    calc
      C * L ^ 160 ≤ L * L ^ 160 :=
        mul_le_mul_of_nonneg_right hnL' (pow_nonneg hLpos.le _)
      _ = L ^ 161 := by ring
  have hroot : L ^ 161 * Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) := by
    have hsqrt0 : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
    have hleft0 : 0 ≤ L ^ 161 * Real.sqrt ((n : ℝ) + 1) := by positivity
    apply (sq_le_sq₀ hleft0 hnR.le).mp
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hpow : (L ^ 161) ^ 2 = L ^ 322 := by
      rw [show (322 : ℕ) = 161 * 2 by norm_num, pow_mul]
    rw [hpow]
    have hprod := mul_le_mul_of_nonneg_right hn322'
      (show 0 ≤ (n : ℝ) + 1 by positivity)
    calc
      L ^ 322 * ((n : ℝ) + 1) ≤ ((n : ℝ) / 2) * ((n : ℝ) + 1) := hprod
      _ ≤ (n : ℝ) ^ 2 := by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
  have hCroot : C * L ^ 160 * Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hCL160 (Real.sqrt_nonneg _)).trans hroot
  have hC : 384000 * ((n : ℝ) * L ^ 160 *
      Real.sqrt ((n : ℝ) + 1)) ≤ (ε / 3) * (n : ℝ) ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hCroot hε.le
    dsimp [C] at hscaled
    field_simp [hε.ne'] at hscaled
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  dsimp [L] at hA hB hC ⊢
  linarith

theorem eventually_norm_major_integral_sub_model_le_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ α in torusMajorArcs (dirichletCutoff n)
            (majorDenominatorCutoff n), integrand n α) -
          ∑ q ∈ Finset.Icc 1 (majorDenominatorCutoff n),
            singularTerm q n * localBetaIntegral (dirichletCutoff n) q n‖ ≤
        ε * (n : ℝ) ^ 2 := by
  have henv := eventually_major_integral_error_envelope_le_mul hε
  filter_upwards [henv, eventually_four_majorDenominatorCutoff_le_dirichletCutoff,
    eventually_n_le_two_dirichletCutoff_mul_logScale_pow_100,
    eventually_majorArc_progression_estimate,
    eventually_ge_atTop (1 : ℕ)] with n hnEnv hnScale hnD hAP hn
  have hP : 1 ≤ majorDenominatorCutoff n :=
    pow_pos (Erdos387.binaryLogScale_pos n) _
  have hPD : 2 * majorDenominatorCutoff n ≤ dirichletCutoff n := by omega
  have hnDreal : (n : ℝ) ≤
      2 * (dirichletCutoff n : ℝ) * (logScale n : ℝ) ^ 100 := by
    exact_mod_cast hnD
  exact (norm_major_integral_sub_denominator_model_le hP hPD hn hnDreal
    (by simpa [majorDenominatorCutoff] using hAP)).trans
      ((major_integral_error_envelope_le hn hnDreal).trans hnEnv)

theorem eventually_dirichletCutoff_vaughan_conditions :
    ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (dirichletCutoff n : ℝ) ∧
      2 * (MathExtras.Helfgott.vaughanCutoff n *
        MathExtras.Helfgott.vaughanCutoff n) ≤ dirichletCutoff n := by
  let δ : ℝ := 1 / (8 * (3 : ℝ) ^ 100)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmallReal :=
    isLittleO_log_rpow_rpow_atTop (100 : ℝ)
      (show (0 : ℝ) < (1 : ℝ) / 5 by norm_num)
  have hsmallNat := hsmallReal.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hsmallNat.bound hδ
  filter_upwards [hsmall, eventually_ge_atTop (4 : ℕ),
    eventually_n_le_two_dirichletCutoff_mul_logScale_pow_100]
      with n hnsmall hn4 hnD
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hrpow0 : 0 ≤ (n : ℝ) ^ ((5 : ℝ)⁻¹) := Real.rpow_nonneg hnR.le _
  have hnsmall' : Real.log (n : ℝ) ^ (100 : ℝ) ≤
      δ * (n : ℝ) ^ ((1 : ℝ) / 5) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hrpow0,
      one_div] using hnsmall
  have hlogNat : Real.log (n : ℝ) ^ (100 : ℝ) =
      Real.log (n : ℝ) ^ (100 : ℕ) := by norm_num
  rw [hlogNat] at hnsmall'
  have hLlog : (logScale n : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    simpa [logScale] using Erdos387.binaryLogScale_cast_le_three_mul_log hn4
  have hL100 : (logScale n : ℝ) ^ 100 ≤
      (3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100 := by
    calc
      (logScale n : ℝ) ^ 100 ≤ (3 * Real.log (n : ℝ)) ^ 100 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hLlog 100
      _ = (3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100 := by rw [mul_pow]
  have hscale : 8 * (logScale n : ℝ) ^ 100 ≤
      (n : ℝ) ^ ((1 : ℝ) / 5) := by
    have hmul := mul_le_mul_of_nonneg_left hnsmall'
      (show 0 ≤ 8 * (3 : ℝ) ^ 100 by positivity)
    dsimp [δ] at hmul
    have hcancel : 8 * (3 : ℝ) ^ 100 *
        (1 / (8 * (3 : ℝ) ^ 100) * (n : ℝ) ^ ((1 : ℝ) / 5)) =
      (n : ℝ) ^ ((1 : ℝ) / 5) := by field_simp
    calc
      8 * (logScale n : ℝ) ^ 100 ≤
          8 * ((3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100) := by gcongr
      _ = (8 * (3 : ℝ) ^ 100) * Real.log (n : ℝ) ^ 100 := by ring
      _ ≤ (8 * (3 : ℝ) ^ 100) *
          (1 / (8 * (3 : ℝ) ^ 100) * (n : ℝ) ^ ((1 : ℝ) / 5)) := hmul
      _ = (n : ℝ) ^ ((1 : ℝ) / 5) := hcancel
  have hLpos : 0 < (logScale n : ℝ) ^ 100 := by
    positivity
  have hnDreal : (n : ℝ) ≤
      2 * (dirichletCutoff n : ℝ) * (logScale n : ℝ) ^ 100 := by
    exact_mod_cast hnD
  have hpow65 : (n : ℝ) ^ ((3 : ℝ) / 5) *
      (n : ℝ) ^ ((1 : ℝ) / 5) ≤ (n : ℝ) := by
    rw [← Real.rpow_add hnR.le]
    have hpow : (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (n : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega))
        (by norm_num)
    simpa using hpow
  have hD35 : 4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤
      (dirichletCutoff n : ℝ) := by
    apply (mul_le_mul_right (mul_pos (by norm_num) hLpos)).mp
    calc
      (4 * (n : ℝ) ^ ((3 : ℝ) / 5)) *
          (2 * (logScale n : ℝ) ^ 100) =
        (n : ℝ) ^ ((3 : ℝ) / 5) *
          (8 * (logScale n : ℝ) ^ 100) := by ring
      _ ≤ (n : ℝ) ^ ((3 : ℝ) / 5) *
          (n : ℝ) ^ ((1 : ℝ) / 5) := by gcongr
      _ ≤ (n : ℝ) := hpow65
      _ ≤ 2 * (dirichletCutoff n : ℝ) * (logScale n : ℝ) ^ 100 := hnDreal
      _ = (dirichletCutoff n : ℝ) *
          (2 * (logScale n : ℝ) ^ 100) := by ring
  have hpow85 : (n : ℝ) ^ ((4 : ℝ) / 5) *
      (n : ℝ) ^ ((1 : ℝ) / 5) = (n : ℝ) := by
    rw [← Real.rpow_add hnR.le]
    norm_num
  have hD45 : 2 * (n : ℝ) ^ ((4 : ℝ) / 5) ≤
      (dirichletCutoff n : ℝ) := by
    apply (mul_le_mul_right (mul_pos (by norm_num) hLpos)).mp
    calc
      (2 * (n : ℝ) ^ ((4 : ℝ) / 5)) *
          (2 * (logScale n : ℝ) ^ 100) =
        (n : ℝ) ^ ((4 : ℝ) / 5) *
          (4 * (logScale n : ℝ) ^ 100) := by ring
      _ ≤ (n : ℝ) ^ ((4 : ℝ) / 5) *
          (n : ℝ) ^ ((1 : ℝ) / 5) := by
        gcongr
        linarith [hscale]
      _ = (n : ℝ) := hpow85
      _ ≤ 2 * (dirichletCutoff n : ℝ) * (logScale n : ℝ) ^ 100 := hnDreal
      _ = (dirichletCutoff n : ℝ) *
          (2 * (logScale n : ℝ) ^ 100) := by ring
  have hVreal : 2 *
      ((MathExtras.Helfgott.vaughanCutoff n : ℝ) *
        (MathExtras.Helfgott.vaughanCutoff n : ℝ)) ≤
      (dirichletCutoff n : ℝ) :=
    (mul_le_mul_of_nonneg_left
      (MathExtras.Helfgott.vaughanCutoff_sq_le_rpow45 n) (by norm_num)).trans hD45
  refine ⟨hD35, ?_⟩
  exact_mod_cast hVreal

theorem norm_minor_integral_le
    {n D P : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hpoint : ∀ α ∈ torusMinorArcs D P,
      ‖Vinogradov.vonMangoldtExpSum α n‖ ≤ B) :
    ‖∫ α in torusMinorArcs D P, integrand n α‖ ≤
      B * ((n + 1 : ℕ) * Real.log (n + 1 : ℝ) ^ 2) := by
  have hmajor_meas : MeasurableSet (torusMajorArcs D P) := by
    unfold torusMajorArcs
    exact Finset.measurableSet_biUnion _ fun aq _ =>
      torusLocalArc_measurableSet D aq
  have hminor_meas : MeasurableSet (torusMinorArcs D P) := by
    exact measurableSet_Icc.diff hmajor_meas
  have hminor_subset : torusMinorArcs D P ⊆ Set.Icc (0 : ℝ) 1 :=
    fun _ h => h.1
  have hsq_cont : Continuous (fun α : ℝ =>
      ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2) := by
    unfold Vinogradov.vonMangoldtExpSum Vinogradov.addChar
    fun_prop
  have hsq_int : IntegrableOn
      (fun α : ℝ => ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) := hsq_cont.integrableOn_Icc
  calc
    ‖∫ α in torusMinorArcs D P, integrand n α‖ ≤
        ∫ α in torusMinorArcs D P, ‖integrand n α‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ α in torusMinorArcs D P,
        B * ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2 := by
      apply setIntegral_mono_on
      · exact (integrand_continuous n).norm.integrableOn_Icc.mono_set hminor_subset
      · exact (hsq_cont.const_mul B).integrableOn_Icc.mono_set hminor_subset
      · exact hminor_meas
      · intro α hα
        unfold integrand
        rw [norm_mul, norm_pow, Vinogradov.norm_negAddChar]
        have hnorm0 : 0 ≤ ‖Vinogradov.vonMangoldtExpSum α n‖ := norm_nonneg _
        nlinarith [hpoint α hα]
    _ = B * ∫ α in torusMinorArcs D P,
        ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ B * ∫ α in Set.Icc (0 : ℝ) 1,
        ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2 := by
      gcongr
      filter_upwards [] with α
      positivity
    _ = B * ∑ m ∈ Finset.range (n + 1),
        (ArithmeticFunction.vonMangoldt m : ℝ) ^ 2 := by
      rw [integral_norm_vonMangoldtExpSum_sq]
    _ ≤ B * ((n + 1 : ℕ) * Real.log (n + 1 : ℝ) ^ 2) := by
      gcongr
      exact sum_vonMangoldt_sq_le n

-/

theorem localMajorArcExplicit_volume_real_le
    (D a q : ℕ) (hD : 0 < D) (hq : 0 < q) :
    (volume : Measure ℝ).real (Vinogradov.localMajorArcExplicit D a q) ≤
      2 / ((q : ℝ) * (D : ℝ)) := by
  let center : ℝ := (a : ℝ) / (q : ℝ)
  let r : ℝ := 1 / ((q : ℝ) * (D : ℝ))
  let t : Set ℝ := Set.Ioo (center - r) (center + r)
  have hsubset : Vinogradov.localMajorArcExplicit D a q ⊆ t := by
    intro α hα
    have hclose : |α - center| < r := by
      simpa [Vinogradov.localMajorArcExplicit, center, r] using hα.2
    rcases abs_lt.mp hclose with ⟨hleft, hright⟩
    constructor <;> linarith
  have hmeasure : (volume : Measure ℝ)
      (Vinogradov.localMajorArcExplicit D a q) ≤ volume t := measure_mono hsubset
  have ht : volume t = ENNReal.ofReal (2 / ((q : ℝ) * (D : ℝ))) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  have ht_ne : volume t ≠ ⊤ := by rw [ht]; exact ENNReal.ofReal_ne_top
  have hs_ne : (volume : Measure ℝ)
      (Vinogradov.localMajorArcExplicit D a q) ≠ ⊤ :=
    ne_top_of_le_ne_top ht_ne hmeasure
  have hle := (ENNReal.toReal_le_toReal hs_ne ht_ne).mpr hmeasure
  have hnonneg : 0 ≤ 2 / ((q : ℝ) * (D : ℝ)) := by positivity
  have htwo :
      (D : ℝ)⁻¹ * (q : ℝ)⁻¹ + (D : ℝ)⁻¹ * (q : ℝ)⁻¹ =
        2 / ((q : ℝ) * (D : ℝ)) := by ring
  simpa [Measure.real_def, ht, ENNReal.toReal_ofReal hnonneg, t, center, r, htwo]
    using hle

theorem rightEndpointArc_volume_real (D : ℕ) (hD : 0 < D) :
    (volume : Measure ℝ).real (rightEndpointArc D) = 1 / (D : ℝ) := by
  rw [Measure.real_def, rightEndpointArc, Real.volume_Ioc]
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hnonneg : 0 ≤ (1 : ℝ) - (1 - 1 / (D : ℝ)) := by
    have : 0 ≤ 1 / (D : ℝ) := by positivity
    linarith
  rw [ENNReal.toReal_ofReal hnonneg]
  ring

theorem torusLocalArc_volume_real_le
    {D P : ℕ} (hD : 0 < D) {aq : ℕ × ℕ}
    (haq : aq ∈ Vinogradov.majorArcCenters P) :
    (volume : Measure ℝ).real (torusLocalArc D aq) ≤ 3 / (D : ℝ) := by
  have hq := Vinogradov.majorArcCenters_q_pos haq
  by_cases hz : aq = (0, 1)
  · subst aq
    rw [torusLocalArc, if_pos rfl]
    have hleft_ne : (volume : Measure ℝ)
        (Vinogradov.localMajorArcExplicit D 0 1) ≠ ⊤ := by
      exact ne_top_of_le_ne_top (by simp)
        (Vinogradov.localMajorArcExplicit_volume_le_one D 0 1)
    have hright_ne : (volume : Measure ℝ) (rightEndpointArc D) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤)
      simpa [Real.volume_Icc] using
        (measure_mono (rightEndpointArc_subset_Icc D) :
          (volume : Measure ℝ) (rightEndpointArc D) ≤ volume (Set.Icc (0 : ℝ) 1))
    have hu : (volume : Measure ℝ)
        (Vinogradov.localMajorArcExplicit D 0 1 ∪ rightEndpointArc D) ≤
      volume (Vinogradov.localMajorArcExplicit D 0 1) +
        volume (rightEndpointArc D) := measure_union_le _ _
    have hreal := (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hleft_ne, hright_ne⟩) hu)
      (ENNReal.add_ne_top.mpr ⟨hleft_ne, hright_ne⟩)).mpr hu
    rw [ENNReal.toReal_add hleft_ne hright_ne] at hreal
    calc
      (volume : Measure ℝ).real
          (Vinogradov.localMajorArcExplicit D 0 1 ∪ rightEndpointArc D) ≤
        (volume : Measure ℝ).real (Vinogradov.localMajorArcExplicit D 0 1) +
          (volume : Measure ℝ).real (rightEndpointArc D) := by
            simpa [Measure.real_def] using hreal
      _ ≤ 2 / ((1 : ℝ) * D) + 1 / (D : ℝ) := by
        have hleft : (volume : Measure ℝ).real
            (Vinogradov.localMajorArcExplicit D 0 1) ≤
              2 / ((1 : ℝ) * (D : ℝ)) := by
          simpa only [Nat.cast_one] using
            localMajorArcExplicit_volume_real_le D 0 1 hD one_pos
        exact add_le_add hleft (le_of_eq (rightEndpointArc_volume_real D hD))
      _ = 3 / (D : ℝ) := by ring
  · rw [torusLocalArc, if_neg hz]
    calc
      (volume : Measure ℝ).real
          (Vinogradov.localMajorArcExplicit D aq.1 aq.2) ≤
        2 / ((aq.2 : ℝ) * (D : ℝ)) :=
          localMajorArcExplicit_volume_real_le D aq.1 aq.2 hD hq
      _ ≤ 3 / (D : ℝ) := by
        have hqR : (1 : ℝ) ≤ aq.2 := by exact_mod_cast hq
        have hDR : (0 : ℝ) < D := by exact_mod_cast hD
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hi : ((aq.2 : ℝ) * (D : ℝ))⁻¹ ≤ ((D : ℝ))⁻¹ := by
          exact inv_anti₀ (by positivity) (by nlinarith)
        nlinarith [inv_pos.mpr hDR]

theorem majorArcCenters_card_le (P : ℕ) :
    (majorArcCenters_finite P).toFinset.card ≤ (P + 1) ^ 2 := by
  have hsub : (majorArcCenters_finite P).toFinset ⊆
      Finset.range (P + 1) ×ˢ Finset.range (P + 1) := by
    intro aq haq
    have hc : aq ∈ Vinogradov.majorArcCenters P :=
      (Set.Finite.mem_toFinset (majorArcCenters_finite P)).mp haq
    have ha := Vinogradov.majorArcCenters_a_lt_q hc
    have hqP := Vinogradov.majorArcCenters_q_le hc
    rw [Finset.mem_product]
    exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  calc
    (majorArcCenters_finite P).toFinset.card ≤
        (Finset.range (P + 1) ×ˢ Finset.range (P + 1)).card :=
      Finset.card_le_card hsub
    _ = (P + 1) ^ 2 := by simp [pow_two]

theorem norm_major_integral_sub_model_le
    {D P n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hD : 0 < D) (hP : 1 ≤ P) (hPD : 2 * P ≤ D)
    (hpoint : ∀ aq ∈ Vinogradov.majorArcCenters P,
      ∀ α ∈ torusLocalArc D aq,
        ‖integrand n α - localMainIntegrand n aq.1 aq.2 α‖ ≤ B) :
    ‖(∫ α in torusMajorArcs D P, integrand n α) -
        ∑ aq ∈ (majorArcCenters_finite P).toFinset,
          localModelIntegral D n aq‖ ≤
      ((P + 1 : ℕ) : ℝ) ^ 2 * (B * (3 / (D : ℝ))) := by
  rw [integral_torusMajorArcs_eq_sum hP hPD]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ aq ∈ (majorArcCenters_finite P).toFinset,
        ((∫ α in torusLocalArc D aq, integrand n α) -
          localModelIntegral D n aq)‖ ≤
      ∑ aq ∈ (majorArcCenters_finite P).toFinset,
        ‖(∫ α in torusLocalArc D aq, integrand n α) -
          localModelIntegral D n aq‖ := norm_sum_le _ _
    _ ≤ ∑ _aq ∈ (majorArcCenters_finite P).toFinset,
        B * (3 / (D : ℝ)) := by
      apply Finset.sum_le_sum
      intro aq haq
      have hc : aq ∈ Vinogradov.majorArcCenters P :=
        (Set.Finite.mem_toFinset (majorArcCenters_finite P)).mp haq
      have hf : IntegrableOn (integrand n) (torusLocalArc D aq) :=
        (integrand_continuous n).integrableOn_Icc.mono_set
          (torusLocalArc_subset_Icc D aq)
      have hg : IntegrableOn (localMainIntegrand n aq.1 aq.2)
          (torusLocalArc D aq) :=
        (localMainIntegrand_continuous n aq.1 aq.2).integrableOn_Icc.mono_set
          (torusLocalArc_subset_Icc D aq)
      have hfin : (volume : Measure ℝ) (torusLocalArc D aq) < ⊤ := by
        refine lt_of_le_of_lt (measure_mono (torusLocalArc_subset_Icc D aq)) ?_
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_lt_top
      rw [localModelIntegral]
      rw [← MeasureTheory.integral_sub hf hg]
      exact (norm_setIntegral_le_of_norm_le_const hfin (hpoint aq hc)).trans
        (mul_le_mul_of_nonneg_left (torusLocalArc_volume_real_le hD hc) hB)
    _ = ((majorArcCenters_finite P).toFinset.card : ℝ) *
        (B * (3 / (D : ℝ))) := by simp
    _ ≤ ((P + 1 : ℕ) : ℝ) ^ 2 * (B * (3 / (D : ℝ))) := by
      gcongr
      exact_mod_cast majorArcCenters_card_le P

theorem norm_major_integral_sub_finite_model_le
    {D P n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hD : 2 ≤ D) (hP : 1 ≤ P) (hPD : 2 * P ≤ D)
    (hpoint : ∀ aq ∈ Vinogradov.majorArcCenters P,
      ∀ α ∈ torusLocalArc D aq,
        ‖integrand n α - localMainIntegrand n aq.1 aq.2 α‖ ≤ B) :
    ‖(∫ α in torusMajorArcs D P, integrand n α) -
        ∑ q ∈ Finset.Icc 1 P,
          singularTerm q n * localBetaIntegral D q n‖ ≤
      ((P + 1 : ℕ) : ℝ) ^ 2 * (B * (3 / (D : ℝ))) := by
  rw [← sum_localModelIntegral_eq_denominator_sum D P n hD]
  exact norm_major_integral_sub_model_le hB (by omega) hP hPD hpoint

theorem primeFactors_card_le_succ (q : ℕ) : q.primeFactors.card ≤ q + 1 := by
  calc
    q.primeFactors.card ≤ (Finset.range (q + 1)).card := by
      apply Finset.card_le_card
      intro p hp
      have hp' := Nat.mem_primeFactors.mp hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.le_of_dvd (by omega) hp'.2.1))
    _ = q + 1 := Finset.card_range _

theorem norm_inv_totient_le_one {q : ℕ} (hq : 0 < q) :
    ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
  have hphi : (1 : ℝ) ≤ Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hq
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).2 hphi

theorem norm_local_sum_sub_main_le
    {n a q P : ℕ} {β E R : ℝ}
    (hq : 0 < q) (haq : a.Coprime q) (hqP : q ≤ P)
    (hE : 0 ≤ E) (hβ : |β| * (n : ℝ) ≤ R)
    (hlog : 0 ≤ Real.log ((n : ℝ) + 1))
    (hAP : ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
      |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤ E) :
    ‖Vinogradov.vonMangoldtExpSum
        (Vinogradov.rationalCenter a q + β) n -
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
          (Nat.totient q : ℝ) : ℝ) : ℂ) *
        Vinogradov.linearExpSum n β)‖ ≤
      (P : ℝ) * ((E + 1) * (1 + 2 * Real.pi * R)) +
        (P + 1 : ℕ) * Real.log ((n : ℝ) + 1) := by
  have hbase := vonMangoldtExpSum_local_approximation
    (β := β) (E := E) hq haq hE hAP
  have hqR : (q : ℝ) ≤ P := by exact_mod_cast hqP
  have hpfNat : q.primeFactors.card ≤ P + 1 :=
    (primeFactors_card_le_succ q).trans (Nat.add_le_add_right hqP 1)
  have hpf : (q.primeFactors.card : ℝ) ≤ (P + 1 : ℕ) := by
    exact_mod_cast hpfNat
  have hfirstFactor :
      E + ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖ ≤ E + 1 := by
    linarith [norm_inv_totient_le_one hq]
  have hsecondFactor :
      1 + 2 * Real.pi * |β| * (n : ℝ) ≤ 1 + 2 * Real.pi * R := by
    nlinarith [mul_le_mul_of_nonneg_left hβ
      (show 0 ≤ 2 * Real.pi by positivity)]
  have hA :
      (E + ‖((1 / (Nat.totient q : ℝ) : ℝ) : ℂ)‖) *
          (1 + 2 * Real.pi * |β| * (n : ℝ)) ≤
        (E + 1) * (1 + 2 * Real.pi * R) := by
    exact mul_le_mul hfirstFactor hsecondFactor (by positivity) (by positivity)
  exact hbase.trans (add_le_add
    (mul_le_mul hqR hA (by positivity) (by positivity))
    (mul_le_mul_of_nonneg_right hpf hlog))

/-- A uniform real envelope for the local major-arc approximation error. -/
noncomputable def majorApproxError (n : ℕ) : ℝ :=
  40 * ((n : ℝ) / (logScale n : ℝ) ^ 880 +
    (logScale n : ℝ) ^ 120 +
    (logScale n : ℝ) ^ 20 * Real.sqrt ((n : ℝ) + 1))

lemma majorApprox_algebra_active {n : ℕ} {L : ℝ} (hLpos : 0 < L) :
    L ^ 20 * (((n : ℝ) / (16 * L ^ 1000) + 2) * (17 * L ^ 100)) ≤
      40 * ((n : ℝ) / L ^ 880 + L ^ 120) := by
  have hLne : L ≠ 0 := hLpos.ne'
  have h1000 : L ^ 1000 = L ^ 880 * L ^ 120 := by rw [← pow_add]
  have h120 : L ^ 120 = L ^ 20 * L ^ 100 := by rw [← pow_add]
  rw [h1000, h120]
  field_simp [hLne]
  nlinarith [Nat.cast_nonneg (α := ℝ) n, pow_pos hLpos 880,
    pow_pos hLpos 120]

/- Superseded monolithic proof, replaced below by split default-limit helpers.
theorem norm_local_sum_sub_model_le_majorApproxError
    {n a q : ℕ} {β : ℝ}
    (hn : 1 ≤ n) (hq : 0 < q) (hqP : q ≤ majorDenominatorCutoff n)
    (haq : a.Coprime q)
    (hβn : |β| * (n : ℝ) ≤ 2 * (logScale n : ℝ) ^ 100)
    (hAP : ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
      |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
        (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1) :
    ‖Vinogradov.vonMangoldtExpSum
        (Vinogradov.rationalCenter a q + β) n -
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
          (Nat.totient q : ℝ) : ℝ) : ℂ) *
        Vinogradov.linearExpSum n β)‖ ≤ majorApproxError n := by
  let L : ℝ := logScale n
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hLone : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hE : 0 ≤ (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 := by
    exact add_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))) zero_le_one
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact this)
  have happrox := norm_local_sum_sub_main_le
    (P := majorDenominatorCutoff n)
    (R := 2 * (logScale n : ℝ) ^ 100)
    (E := (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    hq haq hqP hE hβn hlog0 hAP
  have hfactor : 1 + 2 * Real.pi * (2 * L ^ 100) ≤ 17 * L ^ 100 := by
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hLpow : 1 ≤ L ^ 100 := one_le_pow₀ hLone
    have hmult := mul_le_mul_of_nonneg_right hpi
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pow_nonneg hLpos.le 100))
    have hpiTerm : 2 * Real.pi * (2 * L ^ 100) ≤ 16 * L ^ 100 := by
      calc
        2 * Real.pi * (2 * L ^ 100) = Real.pi * (4 * L ^ 100) := by ring
        _ ≤ 4 * (4 * L ^ 100) := hmult
        _ = 16 * L ^ 100 := by ring
    linarith
  have hP : (majorDenominatorCutoff n : ℝ) = L ^ 20 := by
    unfold majorDenominatorCutoff
    rw [Nat.cast_pow]
  have hfirst :
      (majorDenominatorCutoff n : ℝ) *
          (((n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 + 1) *
            (1 + 2 * Real.pi * (2 * (logScale n : ℝ) ^ 100))) ≤
        40 * ((n : ℝ) / L ^ 880 + L ^ 120) := by
    have hcast1000 : ((logScale n ^ 1000 : ℕ) : ℝ) = L ^ 1000 := by
      rw [Nat.cast_pow]
    rw [hP]
    rw [hcast1000]
    calc
      L ^ 20 * (((n : ℝ) / (16 * L ^ 1000) + 1 + 1) *
          (1 + 2 * Real.pi * (2 * (logScale n : ℝ) ^ 100))) ≤
          L ^ 20 * (((n : ℝ) / (16 * L ^ 1000) + 2) *
            (17 * L ^ 100)) := by
        have hA0 : 0 ≤ (n : ℝ) / (16 * L ^ 1000) + 2 := by
          exact add_nonneg (div_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (by norm_num) (pow_nonneg hLpos.le 1000))) (by norm_num)
        have hf := mul_le_mul_of_nonneg_left hfactor hA0
        have hf' := mul_le_mul_of_nonneg_left hf (pow_nonneg hLpos.le 20)
        convert hf' using 1 <;> dsimp [L] <;> ring
      _ ≤ 40 * ((n : ℝ) / L ^ 880 + L ^ 120) :=
        majorApprox_algebra hLpos
  have hlog : Real.log ((n : ℝ) + 1) ≤
      2 * Real.sqrt ((n : ℝ) + 1) := by
    have h := Real.log_le_rpow_div
      (x := (n : ℝ) + 1) (by positivity) (ε := (1 : ℝ) / 2) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith
  have hPplus : ((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ≤ 2 * L ^ 20 := by
    rw [Nat.cast_add, Nat.cast_one, hP]
    nlinarith [one_le_pow₀ hLone 20]
  have hsecond :
      ((majorDenominatorCutoff n + 1 : ℕ) : ℝ) *
          Real.log ((n : ℝ) + 1) ≤
        40 * (L ^ 20 * Real.sqrt ((n : ℝ) + 1)) := by
    calc
      _ ≤ (2 * L ^ 20) * (2 * Real.sqrt ((n : ℝ) + 1)) :=
        mul_le_mul hPplus hlog hlog0 (by positivity)
      _ ≤ 40 * (L ^ 20 * Real.sqrt ((n : ℝ) + 1)) := by
        positivity
  exact happrox.trans (by
    unfold majorApproxError
    dsimp [L] at hfirst hsecond ⊢
    linarith)

-/

theorem majorApprox_factor (n : ℕ) :
    1 + 2 * Real.pi * (2 * (logScale n : ℝ) ^ 100) ≤
      17 * (logScale n : ℝ) ^ 100 := by
  let L : ℝ := logScale n
  have hLone : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hLpow : 1 ≤ L ^ 100 := one_le_pow₀ hLone
  have hmul := mul_le_mul_of_nonneg_left hpi
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (le_trans zero_le_one hLpow))
  dsimp [L] at hmul hLpow ⊢
  calc
    1 + 2 * Real.pi * (2 * (logScale n : ℝ) ^ 100) =
        1 + (4 * (logScale n : ℝ) ^ 100) * Real.pi := by ring
    _ ≤ 1 + (4 * (logScale n : ℝ) ^ 100) * 4 := by linarith
    _ ≤ 17 * (logScale n : ℝ) ^ 100 := by linarith

theorem majorApprox_first_envelope (n : ℕ) :
    (majorDenominatorCutoff n : ℝ) *
        (((n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 + 1) *
          (1 + 2 * Real.pi * (2 * (logScale n : ℝ) ^ 100))) ≤
      40 * ((n : ℝ) / (logScale n : ℝ) ^ 880 +
        (logScale n : ℝ) ^ 120) := by
  let L : ℝ := logScale n
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hP : (majorDenominatorCutoff n : ℝ) = L ^ 20 := by
    change (((logScale n) ^ 20 : ℕ) : ℝ) = (logScale n : ℝ) ^ 20
    exact Nat.cast_pow _ _
  rw [hP]
  have hcast : ((logScale n ^ 1000 : ℕ) : ℝ) = L ^ 1000 := by
    dsimp [L]
    exact Nat.cast_pow _ _
  have hscalar :
      (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 + 1 =
        (n : ℝ) / (16 * L ^ 1000) + 2 := by
    rw [hcast]
    ring
  have hf := majorApprox_factor n
  have hA0 : 0 ≤ (n : ℝ) / (16 * L ^ 1000) + 2 := by
    exact add_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (pow_nonneg hLpos.le _))) (by norm_num)
  have hinner :
      ((n : ℝ) / (16 * L ^ 1000) + 2) *
          (1 + 2 * Real.pi * (2 * L ^ 100)) ≤
        ((n : ℝ) / (16 * L ^ 1000) + 2) * (17 * L ^ 100) :=
    mul_le_mul_of_nonneg_left hf hA0
  calc
    L ^ 20 * (((n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 + 1) *
        (1 + 2 * Real.pi * (2 * (logScale n : ℝ) ^ 100))) ≤
        L ^ 20 * (((n : ℝ) / (16 * L ^ 1000) + 2) *
          (17 * L ^ 100)) := by
      rw [hscalar]
      exact mul_le_mul_of_nonneg_left hinner (pow_nonneg hLpos.le _)
    _ ≤ 40 * ((n : ℝ) / L ^ 880 + L ^ 120) := by
      exact majorApprox_algebra_active hLpos

theorem log_succ_le_two_sqrt (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
  have h := Real.log_le_rpow_div
    (x := (n : ℝ) + 1) (by positivity) (ε := (1 : ℝ) / 2) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at h
  nlinarith

theorem majorApprox_second_envelope (n : ℕ) :
    ((majorDenominatorCutoff n + 1 : ℕ) : ℝ) *
        Real.log ((n : ℝ) + 1) ≤
      40 * ((logScale n : ℝ) ^ 20 * Real.sqrt ((n : ℝ) + 1)) := by
  let L : ℝ := logScale n
  have hLone : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact this)
  have hlog := log_succ_le_two_sqrt n
  have hP : (majorDenominatorCutoff n : ℝ) = L ^ 20 := by
    change (((logScale n) ^ 20 : ℕ) : ℝ) = (logScale n : ℝ) ^ 20
    exact Nat.cast_pow _ _
  have hPplus : ((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ≤ 2 * L ^ 20 := by
    rw [Nat.cast_add, Nat.cast_one, hP]
    have hpow : 1 ≤ L ^ 20 := one_le_pow₀ hLone
    nlinarith
  dsimp [L] at hPplus ⊢
  calc
    _ ≤ (2 * (logScale n : ℝ) ^ 20) *
        (2 * Real.sqrt ((n : ℝ) + 1)) :=
      mul_le_mul hPplus hlog hlog0 (by positivity)
    _ ≤ 40 * ((logScale n : ℝ) ^ 20 *
        Real.sqrt ((n : ℝ) + 1)) := by
      have hnonneg : 0 ≤ (logScale n : ℝ) ^ 20 *
          Real.sqrt ((n : ℝ) + 1) :=
        mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          (Real.sqrt_nonneg _)
      nlinarith

theorem norm_local_sum_sub_model_le_majorApproxError
    {n a q : ℕ} {β : ℝ}
    (hn : 1 ≤ n) (hq : 0 < q) (hqP : q ≤ majorDenominatorCutoff n)
    (haq : a.Coprime q)
    (hβn : |β| * (n : ℝ) ≤ 2 * (logScale n : ℝ) ^ 100)
    (hAP : ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
      |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
        (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1) :
    ‖Vinogradov.vonMangoldtExpSum
        (Vinogradov.rationalCenter a q + β) n -
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
          (Nat.totient q : ℝ) : ℝ) : ℂ) *
        Vinogradov.linearExpSum n β)‖ ≤ majorApproxError n := by
  have hE : 0 ≤ (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1 := by
    exact add_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))) zero_le_one
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact this)
  have happrox := norm_local_sum_sub_main_le
    (P := majorDenominatorCutoff n)
    (R := 2 * (logScale n : ℝ) ^ 100)
    (E := (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    hq haq hqP hE hβn hlog0 hAP
  have hfirst := majorApprox_first_envelope n
  have hsecond := majorApprox_second_envelope n
  exact happrox.trans (by
    unfold majorApproxError
    linarith)

theorem norm_vonMangoldtExpSum_le_log (n : ℕ) (α : ℝ) :
    ‖Vinogradov.vonMangoldtExpSum α n‖ ≤
      ((n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) := by
  refine (Vinogradov.norm_vonMangoldtExpSum_le_sum α n).trans ?_
  calc
    (∑ m ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt m) ≤
        ∑ _m ∈ Finset.range (n + 1), Real.log ((n : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (by
          by_cases hm0 : m = 0
          · subst m
            have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
            simpa only [Nat.cast_zero, Real.log_zero] using Real.log_nonneg hone
          · exact Real.log_le_log (by positivity)
              (by exact_mod_cast (show m ≤ n + 1 by omega)))
    _ = ((n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) := by simp

theorem norm_integrand_sub_localMain_le
    {n a q : ℕ} {α delta : ℝ} (hdelta : 0 ≤ delta)
    (hsum : ‖Vinogradov.vonMangoldtExpSum α n -
      (((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
        (Nat.totient q : ℝ) : ℝ) : ℂ) *
          Vinogradov.linearExpSum n
            (α - Vinogradov.rationalCenter a q))‖ ≤ delta) :
    ‖integrand n α - localMainIntegrand n a q α‖ ≤
      delta * (3 * ((((n + 1 : ℕ) : ℝ) *
        (Real.log ((n : ℝ) + 1) + 1)) ^ 2)) := by
  let x := Vinogradov.vonMangoldtExpSum α n
  let y := ((((ArithmeticFunction.moebius q : ℤ) : ℝ) /
    (Nat.totient q : ℝ) : ℂ) * Vinogradov.linearExpSum n
      (α - Vinogradov.rationalCenter a q))
  let H : ℝ := ((n + 1 : ℕ) : ℝ) * (Real.log ((n : ℝ) + 1) + 1)
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact this)
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hsum' : ‖x - y‖ ≤ delta := by
    simpa [x, y, RCLike.ofReal_div] using hsum
  have hx : ‖x‖ ≤ H := by
    dsimp [x, H]
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) :=
        norm_vonMangoldtExpSum_le_log n α
      _ ≤ ((n + 1 : ℕ) : ℝ) * (Real.log ((n : ℝ) + 1) + 1) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
          (by positivity)
  have hy : ‖y‖ ≤ H := by
    dsimp [y, H]
    calc
      _ ≤ (n : ℝ) + 1 := norm_mu_phi_linearExpSum_le n q
        (α - Vinogradov.rationalCenter a q)
      _ ≤ ((n + 1 : ℕ) : ℝ) * (Real.log ((n : ℝ) + 1) + 1) := by
        rw [Nat.cast_add, Nat.cast_one]
        nlinarith
  change ‖x ^ 3 * Vinogradov.negAddChar α n -
    y ^ 3 * Vinogradov.negAddChar α n‖ ≤ delta * (3 * H ^ 2)
  rw [← sub_mul]
  rw [norm_mul, Vinogradov.norm_negAddChar, mul_one]
  refine (norm_cube_sub_cube_le x y).trans ?_
  have hquad : ‖x‖ ^ 2 + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 ≤ 3 * H ^ 2 := by
    have hxx : ‖x‖ ^ 2 ≤ H ^ 2 := by
      simpa [pow_two] using mul_le_mul hx hx (norm_nonneg x) hH0
    have hxy : ‖x‖ * ‖y‖ ≤ H ^ 2 := by
      simpa [pow_two] using mul_le_mul hx hy (norm_nonneg y) hH0
    have hyy : ‖y‖ ^ 2 ≤ H ^ 2 := by
      simpa [pow_two] using mul_le_mul hy hy (norm_nonneg y) hH0
    linarith
  exact mul_le_mul hsum' hquad (by positivity) hdelta

noncomputable def majorIntegrandError (n : ℕ) : ℝ :=
  majorApproxError n *
    (3 * ((((n + 1 : ℕ) : ℝ) * (Real.log ((n : ℝ) + 1) + 1)) ^ 2))

lemma localBeta_mul_n_le
    {n D q : ℕ} {beta : ℝ} (hn : 1 ≤ n) (hq : 0 < q)
    (hbeta : |beta| < 1 / ((q : ℝ) * (D : ℝ)))
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100) :
    |beta| * (n : ℝ) ≤ 2 * (logScale n : ℝ) ^ 100 := by
  have hDpos : 0 < D := by
    by_contra hDz
    have hD0 : D = 0 := Nat.eq_zero_of_not_pos hDz
    subst D
    norm_num at hnD
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  calc
    |beta| * (n : ℝ) ≤
        (1 / ((q : ℝ) * (D : ℝ))) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hbeta.le (Nat.cast_nonneg _)
    _ ≤ (1 / (D : ℝ)) * (n : ℝ) := by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hinv : ((q : ℝ) * (D : ℝ))⁻¹ ≤ ((D : ℝ))⁻¹ := by
        exact inv_anti₀ (by positivity) (by nlinarith)
      simpa [one_div] using mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg n)
    _ = (n : ℝ) / (D : ℝ) := by ring
    _ ≤ 2 * (logScale n : ℝ) ^ 100 := by
      rw [div_le_iff₀ hDR]
      calc
        (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100 := hnD
        _ = (2 * (logScale n : ℝ) ^ 100) * (D : ℝ) := by ring

/- Superseded combined wrapped-arc proof; split helpers below stay under the
default per-declaration heartbeat limit.
theorem norm_integrand_sub_localMain_on_torusLocalArc
    {n D : ℕ} (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    {aq : ℕ × ℕ} (haq :
      aq ∈ Vinogradov.majorArcCenters (majorDenominatorCutoff n))
    {α : ℝ} (hα : α ∈ torusLocalArc D aq) :
    ‖integrand n α - localMainIntegrand n aq.1 aq.2 α‖ ≤
      majorIntegrandError n := by
  have hErr : 0 ≤ majorApproxError n := by
    unfold majorApproxError
    positivity
  apply norm_integrand_sub_localMain_le hErr
  by_cases hend : aq = (0, 1)
  · subst aq
    simp only [torusLocalArc, if_pos rfl, Set.mem_union] at hα
    have hone : 1 ≤ logScale n ^ 20 :=
      pow_pos (Erdos387.binaryLogScale_pos n) _
    rcases hα with hleft | hright
    · have hbeta : |α| * (n : ℝ) ≤ 2 * (logScale n : ℝ) ^ 100 := by
        apply localBeta_mul_n_le (D := D) hn (q := 1) (by norm_num) _ hnD
        simpa [Vinogradov.rationalCenter] using hleft.2
      have hsum := norm_local_sum_sub_model_le_majorApproxError
        (n := n) (a := 0) (q := 1) (β := α) hn (by norm_num)
        (by simpa [majorDenominatorCutoff] using hone) (by simp) hbeta
        (hAP 1 (by norm_num) hone)
      simpa [Vinogradov.rationalCenter] using hsum
    · have hDpos : 0 < D := by
        by_contra hDz
        have hD0 : D = 0 := Nat.eq_zero_of_not_pos hDz
        subst D
        simp [rightEndpointArc] at hright
      have hdist : |α - 1| < 1 / ((1 : ℝ) * (D : ℝ)) := by
        have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
        change 1 - 1 / (D : ℝ) < α ∧ α ≤ 1 at hright
        rw [one_mul, abs_lt]
        constructor
        · have := hright.1
          linarith
        · have hinv : 0 < 1 / (D : ℝ) := by positivity
          linarith [hright.2]
      have hbeta : |α - 1| * (n : ℝ) ≤
          2 * (logScale n : ℝ) ^ 100 := by
        have hdist' : |α - 1| <
            1 / (((1 : ℕ) : ℝ) * (D : ℝ)) := by simpa using hdist
        exact localBeta_mul_n_le (D := D) hn (q := 1)
          (by norm_num) hdist' hnD
      have hlinear : Vinogradov.linearExpSum n (α - 1) =
          Vinogradov.linearExpSum n α := by
        unfold Vinogradov.linearExpSum
        refine Finset.sum_congr rfl ?_
        intro m _hm
        exact Vinogradov.addChar_sub_one α m
      have hsum := norm_local_sum_sub_model_le_majorApproxError
        (n := n) (a := 1) (q := 1) (β := α - 1) hn (by norm_num)
        (by simpa [majorDenominatorCutoff] using hone) (by simp) hbeta
        (hAP 1 (by norm_num) hone)
      simpa [Vinogradov.rationalCenter, hlinear,
        RCLike.ofReal_div] using hsum
  · have hq := Vinogradov.majorArcCenters_q_pos haq
    have hqP : aq.2 ≤ majorDenominatorCutoff n :=
      Vinogradov.majorArcCenters_q_le haq
    have hcop := Vinogradov.majorArcCenters_coprime haq
    have hplain : α ∈ Vinogradov.localMajorArcExplicit D aq.1 aq.2 := by
      simpa [torusLocalArc, hend] using hα
    have hbeta := localBeta_mul_n_le hn hq hplain.2 hnD
    have hsum := norm_local_sum_sub_model_le_majorApproxError
      (n := n) (a := aq.1) (q := aq.2)
      (β := α - Vinogradov.rationalCenter aq.1 aq.2)
      hn hq hqP hcop hbeta
      (hAP aq.2 hq (by simpa [majorDenominatorCutoff] using hqP))
    simpa [majorIntegrandError] using hsum

-/

lemma majorApproxError_nonneg (n : ℕ) : 0 ≤ majorApproxError n := by
  unfold majorApproxError
  positivity

theorem norm_integrand_sub_localMain_leftEndpoint
    {n D : ℕ} {α : ℝ} (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    (hα : α ∈ Vinogradov.localMajorArcExplicit D 0 1) :
    ‖integrand n α - localMainIntegrand n 0 1 α‖ ≤
      majorIntegrandError n := by
  apply norm_integrand_sub_localMain_le (majorApproxError_nonneg n)
  have hbeta : |α| * (n : ℝ) ≤ 2 * (logScale n : ℝ) ^ 100 := by
    apply localBeta_mul_n_le (D := D) hn (q := 1) (by norm_num) _ hnD
    simpa [Vinogradov.rationalCenter] using hα.2
  have hone : 1 ≤ logScale n ^ 20 :=
    pow_pos (Erdos387.binaryLogScale_pos n) _
  have hsum := norm_local_sum_sub_model_le_majorApproxError
    (n := n) (a := 0) (q := 1) (β := α) hn (by norm_num)
    (by simpa [majorDenominatorCutoff] using hone) (by simp) hbeta
    (hAP 1 (by norm_num) hone)
  simpa [Vinogradov.rationalCenter] using hsum

theorem norm_integrand_sub_localMain_rightEndpoint
    {n D : ℕ} {α : ℝ} (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    (hα : α ∈ rightEndpointArc D) :
    ‖integrand n α - localMainIntegrand n 0 1 α‖ ≤
      majorIntegrandError n := by
  apply norm_integrand_sub_localMain_le (majorApproxError_nonneg n)
  have hDpos : 0 < D := by
    by_contra hDz
    have hD0 : D = 0 := Nat.eq_zero_of_not_pos hDz
    subst D
    simp [rightEndpointArc] at hα
  have hdist : |α - 1| < 1 / (((1 : ℕ) : ℝ) * (D : ℝ)) := by
    have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
    change 1 - 1 / (D : ℝ) < α ∧ α ≤ 1 at hα
    rw [Nat.cast_one, one_mul, abs_lt]
    constructor
    · linarith [hα.1]
    · have hinv : 0 < 1 / (D : ℝ) := by positivity
      linarith [hα.2]
  have hbeta : |α - 1| * (n : ℝ) ≤
      2 * (logScale n : ℝ) ^ 100 :=
    localBeta_mul_n_le (D := D) hn (q := 1) (by norm_num) hdist hnD
  have hlinear : Vinogradov.linearExpSum n (α - 1) =
      Vinogradov.linearExpSum n α := by
    unfold Vinogradov.linearExpSum
    refine Finset.sum_congr rfl ?_
    intro m _hm
    exact Vinogradov.addChar_sub_one α m
  have hone : 1 ≤ logScale n ^ 20 :=
    pow_pos (Erdos387.binaryLogScale_pos n) _
  have hsum := norm_local_sum_sub_model_le_majorApproxError
    (n := n) (a := 1) (q := 1) (β := α - 1) hn (by norm_num)
    (by simpa [majorDenominatorCutoff] using hone) (by simp) hbeta
    (hAP 1 (by norm_num) hone)
  simpa [Vinogradov.rationalCenter, hlinear, RCLike.ofReal_div] using hsum

theorem norm_integrand_sub_localMain_internal
    {n D : ℕ} (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    {aq : ℕ × ℕ} (haq :
      aq ∈ Vinogradov.majorArcCenters (majorDenominatorCutoff n))
    {α : ℝ} (hα : α ∈ Vinogradov.localMajorArcExplicit D aq.1 aq.2) :
    ‖integrand n α - localMainIntegrand n aq.1 aq.2 α‖ ≤
      majorIntegrandError n := by
  apply norm_integrand_sub_localMain_le (majorApproxError_nonneg n)
  have hq := Vinogradov.majorArcCenters_q_pos haq
  have hqP : aq.2 ≤ majorDenominatorCutoff n :=
    Vinogradov.majorArcCenters_q_le haq
  have hcop := Vinogradov.majorArcCenters_coprime haq
  have hbeta := localBeta_mul_n_le hn hq hα.2 hnD
  have hsum := norm_local_sum_sub_model_le_majorApproxError
    (n := n) (a := aq.1) (q := aq.2)
    (β := α - Vinogradov.rationalCenter aq.1 aq.2)
    hn hq hqP hcop hbeta
    (hAP aq.2 hq (by simpa [majorDenominatorCutoff] using hqP))
  have hcenter : Vinogradov.rationalCenter aq.1 aq.2 +
      (α - Vinogradov.rationalCenter aq.1 aq.2) = α := by ring
  rw [hcenter] at hsum
  exact hsum

theorem norm_integrand_sub_localMain_on_torusLocalArc
    {n D : ℕ} (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1)
    {aq : ℕ × ℕ} (haq :
      aq ∈ Vinogradov.majorArcCenters (majorDenominatorCutoff n))
    {α : ℝ} (hα : α ∈ torusLocalArc D aq) :
    ‖integrand n α - localMainIntegrand n aq.1 aq.2 α‖ ≤
      majorIntegrandError n := by
  by_cases hend : aq = (0, 1)
  · subst aq
    simp only [torusLocalArc, if_pos rfl, Set.mem_union] at hα
    rcases hα with hleft | hright
    · exact norm_integrand_sub_localMain_leftEndpoint hn hnD hAP hleft
    · exact norm_integrand_sub_localMain_rightEndpoint hn hnD hAP hright
  · apply norm_integrand_sub_localMain_internal hn hnD hAP haq
    simpa [torusLocalArc, hend] using hα

theorem log_succ_add_one_le_four_logScale {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) + 1 ≤ 4 * (logScale n : ℝ) := by
  have hLoneNat : 1 ≤ logScale n := Erdos387.binaryLogScale_pos n
  have hLone : (1 : ℝ) ≤ logScale n := by exact_mod_cast hLoneNat
  have hnpos : 0 < n := by omega
  have hltNat : n < 2 ^ logScale n := by
    simpa [logScale, Erdos387.binaryLogScale, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n)
  have hltR : (n : ℝ) < (2 : ℝ) ^ logScale n := by
    exact_mod_cast hltNat
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogn : Real.log (n : ℝ) ≤ (logScale n : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ logScale n) :=
        (Real.log_lt_log (by exact_mod_cast hnpos) hltR).le
      _ = (logScale n : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ (logScale n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ = (logScale n : ℝ) := mul_one _
  have hsuccNat : n + 1 ≤ 2 * n := by omega
  have hsuccR : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by exact_mod_cast hsuccNat
  have hlogsucc : Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by positivity) hsuccR
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by exact_mod_cast hnpos.ne')] at hlogsucc
  linarith

lemma majorIntegrandError_nonneg (n : ℕ) : 0 ≤ majorIntegrandError n := by
  unfold majorIntegrandError
  exact mul_nonneg (majorApproxError_nonneg n) (by positivity)

theorem norm_major_integral_sub_denominator_model_le
    {n D : ℕ} (hn : 1 ≤ n) (hD : 2 ≤ D)
    (hPD : 2 * majorDenominatorCutoff n ≤ D)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100)
    (hAP : ∀ q : ℕ, 0 < q → q ≤ logScale n ^ 20 →
      ∀ r : ℕ, r < q → r.Coprime q → ∀ m : ℕ, m ≤ n →
        |psiAP m q r - (m : ℝ) / (Nat.totient q : ℝ)| ≤
          (n : ℝ) / (16 * (logScale n ^ 1000 : ℕ)) + 1) :
    ‖(∫ α in torusMajorArcs D (majorDenominatorCutoff n), integrand n α) -
        ∑ q ∈ Finset.Icc 1 (majorDenominatorCutoff n),
          singularTerm q n * localBetaIntegral D q n‖ ≤
      (((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ^ 2) *
        (majorIntegrandError n * (3 / (D : ℝ))) := by
  apply norm_major_integral_sub_finite_model_le
  · exact majorIntegrandError_nonneg n
  · exact hD
  · exact pow_pos (Erdos387.binaryLogScale_pos n) _
  · exact hPD
  · intro aq haq α hα
    exact norm_integrand_sub_localMain_on_torusLocalArc hn hnD hAP haq hα

theorem major_integral_error_envelope_le
    {n D : ℕ} (hn : 1 ≤ n)
    (hnD : (n : ℝ) ≤ 2 * (D : ℝ) * (logScale n : ℝ) ^ 100) :
    (((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ^ 2 *
      (majorIntegrandError n * (3 / (D : ℝ)))) ≤
      184320 * ((n : ℝ) ^ 2 / (logScale n : ℝ) ^ 738 +
        (n : ℝ) * (logScale n : ℝ) ^ 262 +
        (n : ℝ) * (logScale n : ℝ) ^ 162 *
          Real.sqrt ((n : ℝ) + 1)) := by
  let L : ℝ := logScale n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hDpos : 0 < D := by
    by_contra hDz
    have hD0 : D = 0 := Nat.eq_zero_of_not_pos hDz
    subst D
    norm_num at hnD
    linarith
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hP : ((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ≤ 2 * L ^ 20 := by
    have hLone : (1 : ℝ) ≤ L := by
      dsimp [L]
      exact_mod_cast Erdos387.binaryLogScale_pos n
    have hpow : (1 : ℝ) ≤ L ^ 20 := one_le_pow₀ hLone
    change (((logScale n ^ 20 + 1 : ℕ) : ℝ)) ≤ 2 * L ^ 20
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
    dsimp [L] at hpow ⊢
    linarith
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (by omega : n + 1 ≤ 2 * n)
  have hlog := log_succ_add_one_le_four_logScale hn
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) + 1 := by
    have : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
    linarith
  have hinvD : 3 / (D : ℝ) ≤ 6 * L ^ 100 / (n : ℝ) := by
    rw [div_le_div_iff₀ hDR hnR]
    dsimp [L] at hnD ⊢
    nlinarith
  have hH : (((n + 1 : ℕ) : ℝ) *
        (Real.log ((n : ℝ) + 1) + 1)) ^ 2 ≤
      (2 * (n : ℝ) * (4 * L)) ^ 2 := by
    apply pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg _) hlog0) _ 2
    exact mul_le_mul hn1 hlog hlog0 (by positivity)
  have hMI : majorIntegrandError n ≤
      majorApproxError n * (3 * ((2 * (n : ℝ) * (4 * L)) ^ 2)) := by
    unfold majorIntegrandError
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hH (by norm_num)) (majorApproxError_nonneg n)
  have hquot0 : 0 ≤ 3 / (D : ℝ) := by positivity
  have hupperQuot0 : 0 ≤ 6 * L ^ 100 / (n : ℝ) := by positivity
  have hupperMI0 : 0 ≤
      majorApproxError n * (3 * ((2 * (n : ℝ) * (4 * L)) ^ 2)) :=
    mul_nonneg (majorApproxError_nonneg n) (by positivity)
  have hinner : majorIntegrandError n * (3 / (D : ℝ)) ≤
      (majorApproxError n * (3 * ((2 * (n : ℝ) * (4 * L)) ^ 2))) *
        (6 * L ^ 100 / (n : ℝ)) :=
    mul_le_mul hMI hinvD hquot0 hupperMI0
  have hP2 : (((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ^ 2) ≤
      (2 * L ^ 20) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hP 2
  have hleftInner0 : 0 ≤ majorIntegrandError n * (3 / (D : ℝ)) :=
    mul_nonneg (majorIntegrandError_nonneg n) hquot0
  calc
    (((majorDenominatorCutoff n + 1 : ℕ) : ℝ) ^ 2 *
      (majorIntegrandError n * (3 / (D : ℝ)))) ≤
      (2 * L ^ 20) ^ 2 *
        (majorApproxError n *
          (3 * ((2 * (n : ℝ) * (4 * L)) ^ 2)) *
            (6 * L ^ 100 / (n : ℝ))) := by
      exact mul_le_mul hP2 hinner hleftInner0 (sq_nonneg _)
    _ = 184320 * ((n : ℝ) ^ 2 / L ^ 738 +
        (n : ℝ) * L ^ 262 +
        (n : ℝ) * L ^ 162 * Real.sqrt ((n : ℝ) + 1)) := by
      unfold majorApproxError
      dsimp [L]
      field_simp [hnR.ne', hLpos.ne']
      ring

theorem eventually_major_integral_error_envelope_le_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      184320 * ((n : ℝ) ^ 2 / (logScale n : ℝ) ^ 738 +
        (n : ℝ) * (logScale n : ℝ) ^ 262 +
        (n : ℝ) * (logScale n : ℝ) ^ 162 *
          Real.sqrt ((n : ℝ) + 1)) ≤ ε * (n : ℝ) ^ 2 := by
  let C : ℝ := 552960 / ε
  have hC : 0 < C := by dsimp [C]; positivity
  have hLreal : Tendsto (fun n : ℕ => (logScale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_logScale
  have hLlarge := hLreal.eventually_ge_atTop C
  have hL738Nat : Tendsto (fun n : ℕ => logScale n ^ 738) atTop atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : 738 ≠ 0)).comp tendsto_logScale
  have hL738 : Tendsto (fun n : ℕ => ((logScale n ^ 738 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hL738Nat
  have hL738large := hL738.eventually_ge_atTop C
  filter_upwards [hLlarge, hL738large,
    Erdos387.eventually_binaryLogScale_pow_le_half 263,
    Erdos387.eventually_binaryLogScale_pow_le_half 326,
    eventually_ge_atTop (1 : ℕ)] with n hnL hn738 hn263 hn326 hn
  let L : ℝ := logScale n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hnL' : C ≤ L := by simpa [L] using hnL
  have hn738' : C ≤ L ^ 738 := by
    simpa only [L, Nat.cast_pow] using hn738
  have hn263' : L ^ 263 ≤ (n : ℝ) / 2 := by
    have hcast : (((logScale n ^ 263 : ℕ) : ℝ)) ≤
        (((n / 2 : ℕ) : ℝ)) := by exact_mod_cast hn263
    calc
      L ^ 263 = ((logScale n ^ 263 : ℕ) : ℝ) := by rw [Nat.cast_pow]
      _ ≤ ((n / 2 : ℕ) : ℝ) := hcast
      _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hn326' : L ^ 326 ≤ (n : ℝ) / 2 := by
    have hcast : (((logScale n ^ 326 : ℕ) : ℝ)) ≤
        (((n / 2 : ℕ) : ℝ)) := by exact_mod_cast hn326
    calc
      L ^ 326 = ((logScale n ^ 326 : ℕ) : ℝ) := by rw [Nat.cast_pow]
      _ ≤ ((n / 2 : ℕ) : ℝ) := hcast
      _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hA : 184320 * ((n : ℝ) ^ 2 / L ^ 738) ≤
      (ε / 3) * (n : ℝ) ^ 2 := by
    have hden : 552960 ≤ ε * L ^ 738 := by
      have := (div_le_iff₀ hε).mp (by simpa [C] using hn738')
      nlinarith
    have hLpowpos : 0 < L ^ 738 := pow_pos hLpos _
    have hratio : 184320 / L ^ 738 ≤ ε / 3 := by
      rw [div_le_iff₀ hLpowpos]
      nlinarith
    calc
      184320 * ((n : ℝ) ^ 2 / L ^ 738) =
          (184320 / L ^ 738) * (n : ℝ) ^ 2 := by ring
      _ ≤ (ε / 3) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
  have hCL262 : C * L ^ 262 ≤ L ^ 263 := by
    calc
      C * L ^ 262 ≤ L * L ^ 262 :=
        mul_le_mul_of_nonneg_right hnL' (pow_nonneg hLpos.le _)
      _ = L ^ 263 := by ring
  have hB : 184320 * ((n : ℝ) * L ^ 262) ≤
      (ε / 3) * (n : ℝ) ^ 2 := by
    have hmain : C * L ^ 262 ≤ (n : ℝ) / 2 := hCL262.trans hn263'
    have hscaled := mul_le_mul_of_nonneg_left hmain hε.le
    dsimp [C] at hscaled
    field_simp [hε.ne'] at hscaled
    nlinarith [Nat.cast_nonneg (α := ℝ) n, pow_nonneg hLpos.le 262]
  have hCL162 : C * L ^ 162 ≤ L ^ 163 := by
    calc
      C * L ^ 162 ≤ L * L ^ 162 :=
        mul_le_mul_of_nonneg_right hnL' (pow_nonneg hLpos.le _)
      _ = L ^ 163 := by ring
  have hroot : L ^ 163 * Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) := by
    have hleft0 : 0 ≤ L ^ 163 * Real.sqrt ((n : ℝ) + 1) :=
      mul_nonneg (pow_nonneg hLpos.le _) (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ hleft0 hnR.le).mp
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (show 0 ≤ n + 1 by omega))]
    have hpow : (L ^ 163) ^ 2 = L ^ 326 := by
      rw [show (326 : ℕ) = 163 * 2 by norm_num, pow_mul]
    rw [hpow]
    have hprod := mul_le_mul_of_nonneg_right hn326'
      (show 0 ≤ (n : ℝ) + 1 by positivity)
    calc
      L ^ 326 * ((n : ℝ) + 1) ≤ ((n : ℝ) / 2) * ((n : ℝ) + 1) := hprod
      _ ≤ (n : ℝ) ^ 2 := by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
  have hCroot : C * L ^ 162 * Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hCL162 (Real.sqrt_nonneg _)).trans hroot
  have hCterm : 184320 * ((n : ℝ) * L ^ 162 *
      Real.sqrt ((n : ℝ) + 1)) ≤ (ε / 3) * (n : ℝ) ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hCroot hε.le
    dsimp [C] at hscaled
    field_simp [hε.ne'] at hscaled
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  dsimp [L] at hA hB hCterm ⊢
  linarith

theorem eventually_norm_major_integral_sub_model_le_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖(∫ α in torusMajorArcs (dirichletCutoff n)
            (majorDenominatorCutoff n), integrand n α) -
          ∑ q ∈ Finset.Icc 1 (majorDenominatorCutoff n),
            singularTerm q n * localBetaIntegral (dirichletCutoff n) q n‖ ≤
        ε * (n : ℝ) ^ 2 := by
  have henv := eventually_major_integral_error_envelope_le_mul hε
  filter_upwards [henv, eventually_four_majorDenominatorCutoff_le_dirichletCutoff,
    eventually_n_le_two_dirichletCutoff_mul_logScale_pow_100,
    eventually_majorArc_progression_estimate,
    eventually_ge_atTop (1 : ℕ)] with n hnEnv hnScale hnD hAP hn
  have hP : 1 ≤ majorDenominatorCutoff n :=
    pow_pos (Erdos387.binaryLogScale_pos n) _
  have hD : 2 ≤ dirichletCutoff n := by omega
  have hPD : 2 * majorDenominatorCutoff n ≤ dirichletCutoff n := by omega
  have hnDreal : (n : ℝ) ≤
      2 * (dirichletCutoff n : ℝ) * (logScale n : ℝ) ^ 100 := by
    exact_mod_cast hnD
  exact (norm_major_integral_sub_denominator_model_le hn hD hPD hnDreal hAP).trans
    ((major_integral_error_envelope_le hn hnDreal).trans hnEnv)

theorem eventually_dirichletCutoff_vaughan_conditions :
    ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (dirichletCutoff n : ℝ) ∧
      2 * (MathExtras.Helfgott.vaughanCutoff n *
        MathExtras.Helfgott.vaughanCutoff n) ≤ dirichletCutoff n := by
  let δ : ℝ := 1 / (8 * (3 : ℝ) ^ 100)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmallReal :=
    isLittleO_log_rpow_rpow_atTop (100 : ℝ)
      (show (0 : ℝ) < (1 : ℝ) / 5 by norm_num)
  have hsmallNat := hsmallReal.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hsmallNat.bound hδ
  filter_upwards [hsmall, eventually_ge_atTop (4 : ℕ),
    eventually_n_le_two_dirichletCutoff_mul_logScale_pow_100]
      with n hnsmall hn4 hnD
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hnsmall' : Real.log (n : ℝ) ^ (100 : ℝ) ≤
      δ * (n : ℝ) ^ ((1 : ℝ) / 5) := by
    change |Real.log (n : ℝ) ^ (100 : ℝ)| ≤
      δ * |(n : ℝ) ^ ((1 : ℝ) / 5)| at hnsmall
    rw [abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg (Real.rpow_nonneg hnR.le _)] at hnsmall
    exact hnsmall
  have hlogNat : Real.log (n : ℝ) ^ (100 : ℝ) =
      Real.log (n : ℝ) ^ (100 : ℕ) := by norm_num
  rw [hlogNat] at hnsmall'
  have hLlog : (logScale n : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    simpa [logScale] using Erdos387.binaryLogScale_cast_le_three_mul_log hn4
  have hL100 : (logScale n : ℝ) ^ 100 ≤
      (3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100 := by
    calc
      (logScale n : ℝ) ^ 100 ≤ (3 * Real.log (n : ℝ)) ^ 100 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hLlog 100
      _ = (3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100 := by rw [mul_pow]
  have hscale : 8 * (logScale n : ℝ) ^ 100 ≤
      (n : ℝ) ^ ((1 : ℝ) / 5) := by
    have hmul := mul_le_mul_of_nonneg_left hnsmall'
      (show 0 ≤ 8 * (3 : ℝ) ^ 100 by positivity)
    dsimp [δ] at hmul
    have hcancel : 8 * (3 : ℝ) ^ 100 *
        (1 / (8 * (3 : ℝ) ^ 100) * (n : ℝ) ^ ((1 : ℝ) / 5)) =
      (n : ℝ) ^ ((1 : ℝ) / 5) := by field_simp
    calc
      8 * (logScale n : ℝ) ^ 100 ≤
          8 * ((3 : ℝ) ^ 100 * Real.log (n : ℝ) ^ 100) := by gcongr
      _ = (8 * (3 : ℝ) ^ 100) * Real.log (n : ℝ) ^ 100 := by ring
      _ ≤ (8 * (3 : ℝ) ^ 100) *
          (1 / (8 * (3 : ℝ) ^ 100) * (n : ℝ) ^ ((1 : ℝ) / 5)) := hmul
      _ = (n : ℝ) ^ ((1 : ℝ) / 5) := hcancel
  have hLbase : 0 < (logScale n : ℝ) := by
    exact_mod_cast Erdos387.binaryLogScale_pos n
  have hLpos : 0 < (logScale n : ℝ) ^ 100 := pow_pos hLbase _
  have hnDreal : (n : ℝ) ≤
      2 * (dirichletCutoff n : ℝ) * (logScale n : ℝ) ^ 100 := by
    exact_mod_cast hnD
  have hpow65 : (n : ℝ) ^ ((3 : ℝ) / 5) *
      (n : ℝ) ^ ((1 : ℝ) / 5) ≤ (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    have hpow : (n : ℝ) ^ ((4 : ℝ) / 5) ≤ (n : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
    convert hpow using 1 <;> norm_num
  have hD35 : 4 * (n : ℝ) ^ ((3 : ℝ) / 5) ≤
      (dirichletCutoff n : ℝ) := by
    have hmul : (4 * (n : ℝ) ^ ((3 : ℝ) / 5)) *
        (2 * (logScale n : ℝ) ^ 100) ≤
        (dirichletCutoff n : ℝ) *
          (2 * (logScale n : ℝ) ^ 100) := by
      calc
      (4 * (n : ℝ) ^ ((3 : ℝ) / 5)) *
          (2 * (logScale n : ℝ) ^ 100) =
        (n : ℝ) ^ ((3 : ℝ) / 5) *
          (8 * (logScale n : ℝ) ^ 100) := by ring
      _ ≤ (n : ℝ) ^ ((3 : ℝ) / 5) *
          (n : ℝ) ^ ((1 : ℝ) / 5) := by gcongr
      _ ≤ (n : ℝ) := hpow65
      _ ≤ 2 * (dirichletCutoff n : ℝ) * (logScale n : ℝ) ^ 100 := hnDreal
      _ = (dirichletCutoff n : ℝ) *
          (2 * (logScale n : ℝ) ^ 100) := by ring
    have hfac : (0 : ℝ) < 2 * (logScale n : ℝ) ^ 100 :=
      mul_pos (by norm_num) hLpos
    exact le_of_mul_le_mul_right hmul hfac
  have hpow85 : (n : ℝ) ^ ((4 : ℝ) / 5) *
      (n : ℝ) ^ ((1 : ℝ) / 5) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  have hD45 : 2 * (n : ℝ) ^ ((4 : ℝ) / 5) ≤
      (dirichletCutoff n : ℝ) := by
    have hmul : (2 * (n : ℝ) ^ ((4 : ℝ) / 5)) *
        (2 * (logScale n : ℝ) ^ 100) ≤
        (dirichletCutoff n : ℝ) *
          (2 * (logScale n : ℝ) ^ 100) := by
      calc
      (2 * (n : ℝ) ^ ((4 : ℝ) / 5)) *
          (2 * (logScale n : ℝ) ^ 100) =
        (n : ℝ) ^ ((4 : ℝ) / 5) *
          (4 * (logScale n : ℝ) ^ 100) := by ring
      _ ≤ (n : ℝ) ^ ((4 : ℝ) / 5) *
          (n : ℝ) ^ ((1 : ℝ) / 5) := by
        gcongr
        linarith [hscale]
      _ = (n : ℝ) := hpow85
      _ ≤ 2 * (dirichletCutoff n : ℝ) * (logScale n : ℝ) ^ 100 := hnDreal
      _ = (dirichletCutoff n : ℝ) *
          (2 * (logScale n : ℝ) ^ 100) := by ring
    have hfac : (0 : ℝ) < 2 * (logScale n : ℝ) ^ 100 :=
      mul_pos (by norm_num) hLpos
    exact le_of_mul_le_mul_right hmul hfac
  have hVreal : 2 *
      ((MathExtras.Helfgott.vaughanCutoff n : ℝ) *
        (MathExtras.Helfgott.vaughanCutoff n : ℝ)) ≤
      (dirichletCutoff n : ℝ) :=
    (mul_le_mul_of_nonneg_left
      (MathExtras.Helfgott.vaughanCutoff_sq_le_rpow45 n) (by norm_num)).trans hD45
  refine ⟨hD35, ?_⟩
  exact_mod_cast hVreal

theorem norm_minor_integral_le
    {n D P : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hpoint : ∀ α ∈ torusMinorArcs D P,
      ‖Vinogradov.vonMangoldtExpSum α n‖ ≤ B) :
    ‖∫ α in torusMinorArcs D P, integrand n α‖ ≤
      B * ((n + 1 : ℕ) * Real.log (n + 1 : ℝ) ^ 2) := by
  have hmajor_meas : MeasurableSet (torusMajorArcs D P) := by
    unfold torusMajorArcs
    exact Finset.measurableSet_biUnion _ fun aq _ =>
      torusLocalArc_measurableSet D aq
  have hminor_meas : MeasurableSet (torusMinorArcs D P) := by
    exact measurableSet_Icc.diff hmajor_meas
  have hminor_subset : torusMinorArcs D P ⊆ Set.Icc (0 : ℝ) 1 :=
    fun _ h => h.1
  have hsq_cont : Continuous (fun α : ℝ =>
      ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2) := by
    unfold Vinogradov.vonMangoldtExpSum Vinogradov.addChar
    fun_prop
  have hsq_int : IntegrableOn
      (fun α : ℝ => ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2)
      (Set.Icc (0 : ℝ) 1) := hsq_cont.integrableOn_Icc
  calc
    ‖∫ α in torusMinorArcs D P, integrand n α‖ ≤
        ∫ α in torusMinorArcs D P, ‖integrand n α‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ α in torusMinorArcs D P,
        B * ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2 := by
      apply setIntegral_mono_on
      · exact (integrand_continuous n).norm.integrableOn_Icc.mono_set hminor_subset
      · exact (hsq_cont.const_mul B).integrableOn_Icc.mono_set hminor_subset
      · exact hminor_meas
      · intro α hα
        unfold integrand
        rw [norm_mul, norm_pow, Vinogradov.norm_negAddChar]
        have hnorm0 : 0 ≤ ‖Vinogradov.vonMangoldtExpSum α n‖ := norm_nonneg _
        nlinarith [hpoint α hα]
    _ = B * ∫ α in torusMinorArcs D P,
        ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ B * ∫ α in Set.Icc (0 : ℝ) 1,
        ‖Vinogradov.vonMangoldtExpSum α n‖ ^ 2 := by
      gcongr
      filter_upwards [] with α
      positivity
    _ = B * ∑ m ∈ Finset.range (n + 1),
        (ArithmeticFunction.vonMangoldt m : ℝ) ^ 2 := by
      rw [integral_norm_vonMangoldtExpSum_sq]
    _ ≤ B * ((n + 1 : ℕ) * Real.log (n + 1 : ℝ) ^ 2) := by
      gcongr
      exact sum_vonMangoldt_sq_le n

end VinogradovsTheorem.Analytic
