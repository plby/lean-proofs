/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Probability.Martingale.BorelCantelli
import Mathlib.Analysis.PSeries
import ErdosProblems.Erdos1165.Clock
import ErdosProblems.Erdos1165.Recurrence

/-!
# The conditional Borel--Cantelli endgame for the planar lower bound

Hao--Li--Okada--Zheng obtain a conditional estimate of harmonic order for
the event that three sites simultaneously attain a new local-time level:

`P(M (m + 1) 3 | G m) >= c / (m + 1)`.

This file proves the measure-theoretic endgame from precisely that estimate.
It is deliberately independent of the random-walk definitions.  The missing
random-walk work is therefore exposed cleanly: construct the adapted level
events and prove the displayed conditional estimate.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal ProbabilityTheory Topology

namespace Erdos1165.Lower

variable {Omega : Type*} {m0 : MeasurableSpace Omega} {mu : Measure Omega}
  {F : Filtration Nat m0} {events : Nat -> Set Omega}

/-! ## Sigma-algebras at increasing stopping times -/

/-- An increasing sequence of stopping times induces a filtration by taking
the sigma-algebra available at each stopping time.  For HLOZ's lower bound,
the sequence is `m ↦ T_(m+1)^1`. -/
noncomputable def filtrationAtIncreasingStoppingTimes
    (base : Filtration Nat m0) (tau : Nat -> Omega -> WithTop Nat)
    (htau : ∀ n, IsStoppingTime base (tau n)) (htau_mono : Monotone tau) :
    Filtration Nat m0 where
  seq n := (htau n).measurableSpace
  mono' := by
    intro i j hij
    exact IsStoppingTime.measurableSpace_mono (htau i) (htau j) (htau_mono hij)
  le' n := (htau n).measurableSpace_le

/-- In discrete time, the strict-order event `{tau < pi}` is measurable in
the sigma-algebra at the right-hand stopping time.  This is the exact fact
needed for `M_m^k = {T_m^k < T_(m+1)^1}` to be visible at `T_(m+1)^1`. -/
theorem measurableSet_stoppingTime_lt_right
    {base : Filtration Nat m0} {tau pi : Omega -> WithTop Nat}
    (htau : IsStoppingTime base tau) (hpi : IsStoppingTime base pi) :
    MeasurableSet[hpi.measurableSpace] {omega | tau omega < pi omega} := by
  have hle : MeasurableSet[hpi.measurableSpace] {omega | tau omega ≤ pi omega} :=
    IsStoppingTime.measurableSet_stopping_time_le htau hpi
  have heq : MeasurableSet[hpi.measurableSpace] {omega | tau omega = pi omega} := by
    simpa only [eq_comm] using
      (IsStoppingTime.measurableSet_eq_stopping_time hpi htau)
  convert hle.diff heq using 1
  ext omega
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, lt_iff_le_and_ne]

/-! ## The two-stage tower estimate -/

/-- The tower calculation used to combine the two successive costs in the
creation of a second and a third favorite site.  If `B` is visible at the
intermediate sigma-algebra, the conditional cost of `C` there is at least
`a`, and the earlier conditional cost of `B` is at least `b`, then the earlier
conditional cost of `B ∩ C` is at least `a * b`.

This is a purely measure-theoretic lemma; its proof uses conditional-
expectation monotonicity, pull-out, and the tower property. -/
theorem condExp_indicator_inter_lower_bound
    [IsProbabilityMeasure mu] {mG mH : MeasurableSpace Omega}
    (hGH : mG ≤ mH) (hH : mH ≤ m0) {B C : Set Omega}
    (hB : MeasurableSet[mH] B) (hC : @MeasurableSet Omega m0 C)
    {a b : Real} (ha : 0 ≤ a)
    (hCcond : ∀ᵐ omega ∂mu,
      a ≤ (mu[C.indicator (1 : Omega -> Real) | mH]) omega)
    (hBcond : ∀ᵐ omega ∂mu,
      b ≤ (mu[B.indicator (1 : Omega -> Real) | mG]) omega) :
    ∀ᵐ omega ∂mu,
      a * b ≤ (mu[(B ∩ C).indicator (1 : Omega -> Real) | mG]) omega := by
  let iB : Omega -> Real := B.indicator 1
  let iC : Omega -> Real := C.indicator 1
  have hBglobal : @MeasurableSet Omega m0 B := hH B hB
  have hiB : Integrable iB mu := (integrable_const 1).indicator hBglobal
  have hiC : Integrable iC mu := (integrable_const 1).indicator hC
  have hinter : (B ∩ C).indicator (1 : Omega -> Real) = iB * iC := by
    funext omega
    by_cases hBo : omega ∈ B <;> by_cases hCo : omega ∈ C <;>
      simp [iB, iC, hBo, hCo]
  have hiBC : Integrable ((B ∩ C).indicator (1 : Omega -> Real)) mu :=
    (integrable_const 1).indicator (hBglobal.inter hC)
  have hprod : Integrable (iB * iC) mu := by simpa only [← hinter] using hiBC
  have hpull :
      mu[iB * iC | mH] =ᵐ[mu] iB * mu[iC | mH] := by
    exact condExp_mul_of_stronglyMeasurable_left
      (stronglyMeasurable_one.indicator hB) hprod hiC
  have hinner :
      (fun omega => a * iB omega) ≤ᵐ[mu]
        mu[(B ∩ C).indicator (1 : Omega -> Real) | mH] := by
    rw [hinter]
    filter_upwards [hCcond, hpull] with omega hCo hpull_o
    rw [hpull_o]
    by_cases hBo : omega ∈ B
    · simpa [iB, hBo] using hCo
    · simp [iB, hBo]
  have hmono :
      mu[fun omega => a * iB omega | mG] ≤ᵐ[mu]
        mu[mu[(B ∩ C).indicator (1 : Omega -> Real) | mH] | mG] := by
    exact condExp_mono (hiB.const_mul a) integrable_condExp hinner
  have htower :
      mu[mu[(B ∩ C).indicator (1 : Omega -> Real) | mH] | mG] =ᵐ[mu]
        mu[(B ∩ C).indicator (1 : Omega -> Real) | mG] :=
    condExp_condExp_of_le hGH hH
  have hscale :
      mu[fun omega => a * iB omega | mG] =ᵐ[mu]
        fun omega => a * (mu[iB | mG]) omega := by
    exact condExp_mul_of_stronglyMeasurable_left
      stronglyMeasurable_const (hiB.const_mul a) hiB
  filter_upwards [hmono, htower, hscale, hBcond]
    with omega hmono_o htower_o hscale_o hB_o
  change b ≤ (mu[iB | mG]) omega at hB_o
  calc
    a * b ≤ a * (mu[iB | mG]) omega := mul_le_mul_of_nonneg_left hB_o ha
    _ = (mu[fun omega => a * iB omega | mG]) omega := hscale_o.symm
    _ ≤ (mu[mu[(B ∩ C).indicator (1 : Omega -> Real) | mH] | mG]) omega := hmono_o
    _ = (mu[(B ∩ C).indicator (1 : Omega -> Real) | mG]) omega := htower_o

/-- Conditional-probability partial sums, with the indexing used in Lévy's
generalized Borel--Cantelli theorem. -/
noncomputable def conditionalProbabilitySum
    (F : Filtration Nat m0) (mu : Measure Omega) (events : Nat -> Set Omega)
    (n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    (mu[(events (k + 1)).indicator (1 : Omega -> Real) | F k]) omega

/-- A pointwise lower bound for all summands transfers divergence to the
conditional-probability partial sums. -/
theorem ae_conditionalProbabilitySum_tendsto_of_lower_bound
    [IsFiniteMeasure mu] (lower : Nat -> Real)
    (hlower : Tendsto (fun n => ∑ k ∈ Finset.range n, lower k) atTop atTop)
    (hbound : ∀ᵐ omega ∂mu, ∀ k,
      lower k ≤
        (mu[(events (k + 1)).indicator (1 : Omega -> Real) | F k]) omega) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun n => conditionalProbabilitySum F mu events n omega)
        atTop atTop := by
  filter_upwards [hbound] with omega homega
  apply Filter.tendsto_atTop_mono (fun n => ?_) hlower
  exact Finset.sum_le_sum fun k _ => homega k

/-- If adapted events have conditionally probability at least a positive
constant times `1 / (k + 1)`, they occur infinitely often almost surely. -/
theorem ae_frequently_mem_of_harmonic_conditional_lower_bound
    [IsFiniteMeasure mu] (hmeas : ∀ n, MeasurableSet[F n] (events n))
    {c : Real} (hc : 0 < c)
    (hbound : ∀ᵐ omega ∂mu, ∀ k,
      c / (k + 1 : Nat) ≤
        (mu[(events (k + 1)).indicator (1 : Omega -> Real) | F k]) omega) :
    ∀ᵐ omega ∂mu, ∃ᶠ n in atTop, omega ∈ events n := by
  have hharmonic :
      Tendsto (fun n => ∑ k ∈ Finset.range n, c / (k + 1 : Nat)) atTop atTop := by
    have h :=
      (Real.tendsto_sum_range_one_div_nat_succ_atTop).const_mul_atTop hc
    convert h using 1
    funext n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    norm_num [div_eq_mul_inv]
  have hdiv := ae_conditionalProbabilitySum_tendsto_of_lower_bound
    (fun k => c / (k + 1 : Nat)) hharmonic hbound
  filter_upwards [MeasureTheory.ae_mem_limsup_atTop_iff mu hmeas, hdiv]
    with omega hiff homega
  exact mem_limsup_iff_frequently_mem.mp (hiff.mpr homega)

/-- The eventual version of the harmonic conditional Borel--Cantelli
criterion.  This is the form needed for estimates deduced from an asymptotic
tail bound: no control of the finitely many initial events is required. -/
theorem ae_frequently_mem_of_eventually_harmonic_conditional_lower_bound
    [IsFiniteMeasure mu] (hmeas : ∀ n, MeasurableSet[F n] (events n))
    {c : Real} (hc : 0 < c)
    (hbound : ∀ᵐ omega ∂mu, ∀ᶠ k in atTop,
      c / (k + 1 : Nat) ≤
        (mu[(events (k + 1)).indicator (1 : Omega -> Real) | F k]) omega) :
    ∀ᵐ omega ∂mu, ∃ᶠ n in atTop, omega ∈ events n := by
  have hnonneg : ∀ᵐ omega ∂mu, ∀ k,
      0 ≤ (mu[(events (k + 1)).indicator (1 : Omega -> Real) | F k]) omega := by
    rw [ae_all_iff]
    intro k
    exact condExp_nonneg (Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ events (k + 1) <;> simp [Set.indicator, h])
  have hdiv : ∀ᵐ omega ∂mu,
      Tendsto (fun n => conditionalProbabilitySum F mu events n omega)
        atTop atTop := by
    filter_upwards [hbound, hnonneg] with omega homega hnonneg_o
    obtain ⟨K, hK⟩ := eventually_atTop.mp homega
    have hscaled : Tendsto
        (fun n => ∑ k ∈ Finset.range n,
          (c / (K + 1 : Nat)) * (1 / (k + 1 : Nat) : ℝ)) atTop atTop := by
      have h := Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop
        (div_pos hc (by positivity : (0 : ℝ) < (K + 1 : ℕ)))
      convert h using 1
      funext n
      rw [Finset.mul_sum]
      simp only [Nat.cast_add, Nat.cast_one]
    have htail : Tendsto
        (fun n => ∑ k ∈ Finset.range n, c / (K + k + 1 : Nat))
        atTop atTop := by
      apply Filter.tendsto_atTop_mono (fun n => ?_) hscaled
      apply Finset.sum_le_sum
      intro k _
      have hden : ((K + k + 1 : ℕ) : ℝ) ≤
          ((K + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
        norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
        nlinarith [mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
          (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      calc
        (c / (K + 1 : Nat)) * (1 / (k + 1 : Nat) : ℝ) =
            c / ((K + 1 : ℕ) * (k + 1 : ℕ)) := by
              push_cast
              field_simp
        _ ≤ c / (K + k + 1 : Nat) := by
          exact div_le_div_of_nonneg_left hc.le (by positivity) hden
    apply (Filter.tendsto_add_atTop_iff_nat K).mp
    apply Filter.tendsto_atTop_mono (fun n => ?_) htail
    rw [conditionalProbabilitySum, Nat.add_comm, Finset.sum_range_add]
    have htailLe :
        (∑ k ∈ Finset.range n, c / (K + k + 1 : Nat)) ≤
          ∑ k ∈ Finset.range n,
            (mu[(events (K + k + 1)).indicator (1 : Omega -> Real) |
              F (K + k)]) omega := by
      exact Finset.sum_le_sum fun k _ => hK (K + k) (by omega)
    have hprefix : 0 ≤ ∑ k ∈ Finset.range K,
        (mu[(events (k + 1)).indicator (1 : Omega -> Real) | F k]) omega :=
      Finset.sum_nonneg fun k _ => hnonneg_o k
    exact htailLe.trans (le_add_of_nonneg_left hprefix)
  filter_upwards [MeasureTheory.ae_mem_limsup_atTop_iff mu hmeas, hdiv]
    with omega hiff homega
  exact mem_limsup_iff_frequently_mem.mp (hiff.mpr homega)

/-- Probability-one version of the harmonic conditional lower-bound lemma. -/
theorem measure_limsup_eq_one_of_harmonic_conditional_lower_bound
    [IsProbabilityMeasure mu] (hmeas : ∀ n, MeasurableSet[F n] (events n))
    {c : Real} (hc : 0 < c)
    (hbound : ∀ᵐ omega ∂mu, ∀ k,
      c / (k + 1 : Nat) ≤
        (mu[(events (k + 1)).indicator (1 : Omega -> Real) | F k]) omega) :
    mu (limsup events atTop) = 1 := by
  have hdiv := ae_conditionalProbabilitySum_tendsto_of_lower_bound
    (fun k => c / (k + 1 : Nat))
    (by
      have h :=
        (Real.tendsto_sum_range_one_div_nat_succ_atTop).const_mul_atTop hc
      convert h using 1
      funext n
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      norm_num [div_eq_mul_inv])
    hbound
  apply (mem_ae_iff_prob_eq_one ?_).mp
  · filter_upwards [MeasureTheory.ae_mem_limsup_atTop_iff mu hmeas, hdiv]
      with omega hiff homega
    exact hiff.mpr homega
  · exact MeasurableSet.measurableSet_limsup fun n => F.le n _ (hmeas n)

/-! ## The complete abstract two-stage endgame -/

/-- The reusable lower-bound skeleton matching HLOZ Lemma 4.1 and the proof
following it.  At level `k + 1`, `firstStage` is the creation of the second
favorite and `secondStage` is the creation of the third.  The intermediate
sigma-algebra is the information at the second creation time.  If the two
successive conditional costs multiply to at least harmonic order, then their
intersections occur infinitely often almost surely. -/
theorem ae_frequently_inter_of_two_stage_harmonic_lower_bound
    [IsProbabilityMeasure mu]
    (middle : Nat -> MeasurableSpace Omega)
    (firstStage secondStage : Nat -> Set Omega)
    (hmeas : ∀ n,
      MeasurableSet[F n] (firstStage n ∩ secondStage n))
    (hfirst : ∀ n, MeasurableSet[middle n] (firstStage n))
    (hsecond : ∀ n, @MeasurableSet Omega m0 (secondStage n))
    (hFmiddle : ∀ k, F k ≤ middle (k + 1))
    (hmiddle : ∀ n, middle n ≤ m0)
    (a b : Nat -> Real) (ha : ∀ k, 0 ≤ a k) {c : Real} (hc : 0 < c)
    (hproduct : ∀ k, c / (k + 1 : Nat) ≤ a k * b k)
    (hsecondCond : ∀ k, ∀ᵐ omega ∂mu,
      a k ≤
        (mu[(secondStage (k + 1)).indicator (1 : Omega -> Real) |
          middle (k + 1)]) omega)
    (hfirstCond : ∀ k, ∀ᵐ omega ∂mu,
      b k ≤
        (mu[(firstStage (k + 1)).indicator (1 : Omega -> Real) | F k]) omega) :
    ∀ᵐ omega ∂mu, ∃ᶠ n in atTop,
      omega ∈ firstStage n ∩ secondStage n := by
  apply ae_frequently_mem_of_harmonic_conditional_lower_bound hmeas hc
  rw [ae_all_iff]
  intro k
  have htwo := condExp_indicator_inter_lower_bound
    (hFmiddle k) (hmiddle (k + 1)) (hfirst (k + 1))
    (hsecond (k + 1)) (ha k) (hsecondCond k) (hfirstCond k)
  filter_upwards [htwo] with omega homega
  exact (hproduct k).trans homega

/-! ## Canonical planar-walk corollaries -/

/-- For the canonical planar simple random walk, an almost-sure conclusion
that `M_m^3` occurs at infinitely many maximal-local-time levels already
implies that at least three favorite sites occur at infinitely many ordinary
times.  Recurrence supplies the only extra input: maximal local time tends to
infinity almost surely.

The substantial HLOZ estimate remains exactly the hypothesis `hlevel`; this
lemma merely discharges the recurrence/change-of-clock step. -/
theorem ae_frequently_favoriteCount_ge_three_of_frequently_levelFavorite
    (hlevel : ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ m in atTop, levelFavorite s m 3) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ n in atTop, 3 ≤ favoriteCount s n := by
  filter_upwards [hlevel, ae_maxLocalTime_tendsto_atTop]
    with s hs hdiv
  exact (frequently_favoriteCount_ge_iff_frequently_levelFavorite
    s 3 (by norm_num) hdiv).mpr hs

/-- Equivalent canonical corollary phrased directly in terms of HLOZ's
threshold-clock ordering `T_m^3 < T_(m+1)^1`. -/
theorem ae_frequently_favoriteCount_ge_three_of_frequently_thresholdTime_lt
    (hclock : ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ m in atTop,
        thresholdTime s m 3 < thresholdTime s (m + 1) 1) :
    ∀ᵐ s ∂simpleRandomWalk,
      ∃ᶠ n in atTop, 3 ≤ favoriteCount s n := by
  filter_upwards [hclock, ae_maxLocalTime_tendsto_atTop]
    with s hs hdiv
  exact (frequently_favoriteCount_ge_iff_frequently_thresholdTime_lt
    s 3 (by norm_num) hdiv).mpr hs

end Erdos1165.Lower
