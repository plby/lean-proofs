/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternRelativeCentered
import ErdosProblems.Erdos207.KSSSPatternSelectors
import ErdosProblems.Erdos207.KSSSPatternHazard
import ErdosProblems.Erdos207.KSSSPatternRateBound
import ErdosProblems.Erdos207.KSSSPatternLowerBound
import ErdosProblems.Erdos207.KSSSPatternCurvatureBound
import ErdosProblems.Erdos207.RelativePatternEnvelope

/-! # Relative pattern drift supplied by the actual KSSS coupled event -/

namespace Erdos207

open Finset

noncomputable section

def ksssPatternTaylorCoefficient (q : ℕ) (coeff : ℕ → ℝ) (h m : ℕ) : ℝ :=
  patternCurvatureBudget h m (∑ d ∈ ksssOrders q, (d : ℝ) * coeff d)
    (∑ d ∈ ksssOrders q, (d : ℝ) * (d - 1 : ℕ) * coeff d)

theorem ksssPatternTrajectory_unitStep_source_error
    (q : ℕ) (a coeff : ℕ → ℝ) (E A M time : ℝ) (h m : ℕ)
    (hE : 0 < E) (hA : 0 < A) (hM : 0 ≤ M) (htime : 0 ≤ time)
    (hclock : 3 * (time + 1) < E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d) :
    |ksssPatternTrajectory (ksssOrders q) a E M h m (time + 1) -
        ksssPatternTrajectory (ksssOrders q) a E M h m time +
        ksssPatternTrajectory (ksssOrders q) a E M h m time * ksssPatternHazardTrajectory q a E A h m time /
          ksssAvailableTrajectory (ksssOrders q) a E A time| ≤
      M * ksssPatternTaylorCoefficient q coeff h m / E ^ 2 := by
  have hc : 3 * time < E := by linarith
  have hp := ksssEdgeDensity_pos hE hc
  have hAt := ksssAvailableTrajectory_pos (ksssOrders q) a hE hA hc
  have hstep := ksssPatternTrajectory_unitStep_error_le_coefficients (ksssOrders q) a coeff E M time h m
    hE hM htime hclock (fun _ hd ↦ (mem_Icc.mp hd).1) ha hab
  rw [ksssPatternSlope_source q a E A M h m time hE.ne' hp.ne' hAt.ne'] at hstep
  simpa only [neg_mul, neg_div, sub_neg_eq_add, ksssPatternHazardTrajectory,
    ksssPatternTaylorCoefficient] using hstep

theorem KSSSOnTrajectories.pattern_relative_centered_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q b B : ℕ} {Q₀ : Finset (Finset V)}
    {a coeff : ℕ → ℝ} {E A time t : ℝ} {Kc : CrudeThresholds}
    (h : KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
      ((Fintype.card V : ℝ) / t ^ ksssPowerErrorExponent b B) B time)
    (hgeometry : KSSSResidualGeometry Q₀ S E time) (hcrude : CrudeStateBounds F S q Kc)
    (hS : GreedyInvariant F S) (hpack : ∀ C ∈ F, IsPackingOn C)
    (hcard : ∀ C ∈ F, 2 ≤ C.card → C.card + 2 ≤ q)
    (hE : 0 < E) (hA : 0 < A) (ht : 0 < t) (htime : 0 ≤ time) (hclock : 3 * (time + 1) < E)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (hexp : Real.exp (∑ d ∈ ksssOrders q, coeff d) ≤ t)
    (K : ℕ) (hK : 1 ≤ K) (hpairK : Kc.pair ≤ K) (hcommonK : Kc.common ≤ K)
    (hKe : (K : ℝ) ≤ ksssErrorEnvelope E ((Fintype.card V : ℝ) / t ^ ksssPowerErrorExponent b B) B time)
    (hsmall : ksssErrorEnvelope E ((Fintype.card V : ℝ) / t ^ ksssPowerErrorExponent b B) B time ≤
      ksssPairTrajectory (ksssOrders q) a E A time / 4)
    (Q : SimpleGraph V) (U : Finset V) (hU : U.Nonempty) (sigma : ℝ) (hsigma : |sigma| = 1)
    (hR : (patternSurvivalSelectors Q S).Nonempty)
    (hsize : (graphEdges Q).card * (Fintype.card V : ℝ) ≤
      E * ksssEdgeDensity E time *
        ksssErrorEnvelope E ((Fintype.card V : ℝ) / t ^ ksssPowerErrorExponent b B) B time / 3)
    (hY : ((properPatternExtensions S.available Q U).card : ℝ) ≤
      2 * ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card time)
    (hnext : ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card time / 2 ≤
      ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card (time + 1))
    (hconst : (patternHazardErrorCoefficient q (graphSupportFinset Q).card (graphEdges Q).card : ℝ) +
      2 * ksssPatternHazardCoefficient q coeff (graphSupportFinset Q).card (graphEdges Q).card ≤ t)
    (hTaylorSmall :
      4 * ((U.card : ℝ) * ksssPatternTaylorCoefficient q coeff (graphSupportFinset Q).card (graphEdges Q).card / E ^ 2) /
        ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card time ≤
      3 * relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time / (E * ksssEdgeDensity E time)) :
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
      patternRelativeCenteredObservable Q U
          (ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card)
          (relativePatternEnvelope E t (ksssPowerErrorExponent b B) B) sigma (time + 1) S' -
        patternRelativeCenteredObservable Q U
          (ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card)
          (relativePatternEnvelope E t (ksssPowerErrorExponent b B) B) sigma time S) ≤ 0 := by
  have hc : 3 * time < E := by linarith
  have hp := ksssEdgeDensity_pos hE hc
  have hx := ksssPairTrajectory_pos (ksssOrders q) a hE hA hc
  have hM : (0 : ℝ) < U.card := by exact_mod_cast card_pos.mpr hU
  have hN : (0 : ℝ) < Fintype.card V := hM.trans_le (by exact_mod_cast card_le_univ U)
  have he : 0 ≤ ksssErrorEnvelope E ((Fintype.card V : ℝ) / t ^ ksssPowerErrorExponent b B) B time := by
    unfold ksssErrorEnvelope
    positivity
  have hb : ∀ d ∈ ksssOrders q, 0 ≤ coeff d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hden := h.pattern_selector_bounds hgeometry hE hp he hsmall Q hsize
  have hH := ksssPatternHazardTrajectory_bounds q a coeff E A time (graphSupportFinset Q).card
    (graphEdges Q).card hE hA htime hc ha hab
  have hpairLower := ksssPairTrajectory_lower_fixed_initial_ratio (ksssOrders q) a coeff E A time
    (Fintype.card V) t hE hN ht htime hc ha hab hratio hexp
  have hcover : 8 * ((patternHazardErrorCoefficient q (graphSupportFinset Q).card (graphEdges Q).card : ℝ) +
      2 * ksssPatternHazardCoefficient q coeff (graphSupportFinset Q).card (graphEdges Q).card) *
        ksssErrorEnvelope E ((Fintype.card V : ℝ) / t ^ ksssPowerErrorExponent b B) B time /
          ksssPairTrajectory (ksssOrders q) a E A time ≤ relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time := by
    calc
      _ ≤ 8 * t * ksssErrorEnvelope E ((Fintype.card V : ℝ) / t ^ ksssPowerErrorExponent b B) B time /
          ksssPairTrajectory (ksssOrders q) a E A time := by gcongr
      _ ≤ _ := relativePatternEnvelope_pair_error E (Fintype.card V) t time _
        (ksssPowerErrorExponent b B) B hN ht hp hpairLower
  exact restrictedGreedyKernel_pattern_relative_centered_drift F Q U S hR _ _ sigma time _ _ _ _ _
    (ksssPatternHazardTrajectory q a E A (graphSupportFinset Q).card (graphEdges Q).card time)
    (ksssAvailableTrajectory (ksssOrders q) a E A time) _ hsigma
    (ksssPatternTrajectory_pos _ _ _ _ _ _ _ hM hp) hnext hY (Nat.cast_nonneg _)
    (ksssPatternHazardCoefficient_nonneg q coeff _ _ hb) he (mul_pos hE hp) hx hden.2
    (ksssAvailableTrajectory_eq_clock_pair _ _ _ _ _ hE.ne' hp.ne') hH.2 hden.1
    (fun u hu ↦ h.pattern_hazard_error hcrude hS hpack hcard hgeometry.cover K hK hpairK hcommonK hKe Q U u hu)
    (ksssPatternTrajectory_unitStep_source_error q a coeff E A U.card time _ _ hE hA hM.le htime hclock ha hab)
    hcover hTaylorSmall (relativePatternEnvelope_growth E t time (ksssPowerErrorExponent b B) B hE ht hclock)

end

end Erdos207
