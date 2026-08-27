/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RetainedSourceStageParameters

/-! # Fix ordinary-process and physical exponents before the finite vortex -/

namespace Erdos207

open Finset

noncomputable section

structure SourceOrdinaryParameters (q h b : ℕ) where
  B : ℕ
  S : ℕ
  P : ℕ
  K : ℕ
  S_pos : 1 ≤ S
  P_pos : 1 ≤ P
  K_pos : 1 ≤ K
  envelope : 4*q ≤ B
  pair : ksssPairDriftCoefficient q (fun d ↦ 9*24^d) +
    ksssPairTaylorCoefficient (ksssOrders q) (fun d ↦ 9*24^d) ≤ 3*(B : ℝ)
  configuration : ∀ i : CrudeOrderIndex q 4,
    ksssIndexedConfigurationDriftCoefficient q (fun d ↦ 9*24^d) i +
      ksssConfigurationTaylorCoefficient (ksssOrders q) (fun d ↦ 9*24^d)
        (i.order-3) i.chosen ≤ 3*(B : ℝ)/2
  physical : ∀ v D : ℕ, 1 ≤ v → K*v ≤ D →
    v+2*b+4 ≤ S*v ∧ v+b*(h+2)+4 ≤ S*v ∧
    2*(S*v)+2*b+v+2 ≤ P*v ∧ b+1 ≤ P*v ∧
    ksssPowerDenominatorExponent q 2 B (26*q+12) 1*(P*v+1) ≤ D ∧
    2*(S*v)+3*b+v+2 ≤ D-v ∧
    v+(q+1)*(1+v+S*v+2*b)+2 ≤ D-v ∧
    b*(h+1)+v+2 ≤ D-v ∧ S*v+4*b+2 ≤ D

theorem exists_source_ordinary_parameters (q h b : ℕ) : Nonempty (SourceOrdinaryParameters q h b) := by
  obtain ⟨B, hB, hpair, hconfiguration⟩ :=
    exists_ksss_indexed_envelope_exponent q (fun d ↦ 9*24^d)
  obtain ⟨S, P, K, hS, hP, hK, hphysical⟩ := exists_source_stage_exponent_schedule q h b
    (ksssPowerDenominatorExponent q 2 B (26*q+12) 1)
  exact ⟨⟨B, S, P, K, hS, hP, hK, hB, hpair, hconfiguration, hphysical⟩⟩

theorem SourceOrdinaryParameters.denominator_budget
    {q h b : ℕ} (E : SourceOrdinaryParameters q h b) :
    ksssPowerDenominatorExponent q 2 E.B (26*q+12) 1*(E.P+1) ≤ E.K := by
  simpa only [mul_one] using (E.physical 1 E.K le_rfl (by simp)).2.2.2.2.1

theorem SourceOrdinaryParameters.scaled_crude_cutoff
    {q h b : ℕ} (_E : SourceOrdinaryParameters q h b) (c : ℕ) (hc : 1 ≤ c) :
    2*(5*c)+2*q*(5*(2*c)+3)+2 ≤ (26*q+12)*c :=
  source_stage_scaled_crude_cutoff q 5 (26*q+12) c hc (by omega)

theorem SourceOrdinaryParameters.retained_stage_scales
    {q h b n ell t rootPower step length m Rfixed : ℕ}
    (E : SourceOrdinaryParameters q h b)
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (T : ℕ) (hsplit : length+m = ell) (hlength : 2 ≤ length) (ht : 2 ≤ t)
    (hroot : rootPower ≤ step*m) (hrootUpper : step*m ≤ rootPower+step)
    (hrootGap : E.K*(2*step+1) ≤ rootPower)
    (hfirstGap : E.K*(Rfixed+step+1) ≤ Rfixed+step*ell)
    (hnlo : t^(Rfixed+step*ell) ≤ n) (hnhi : n ≤ t^(Rfixed+step*ell+1))
    (hthreshold : (max 2 T)^(Rfixed+step*ell+1) ≤ t) (i : Fin length) :
    let W := P.retainedVortex length (by omega) (by omega)
    let D := retainedStageExponent Rfixed step ell i.val
    let v := retainedRatioExponent Rfixed step i.val
    let c := D+1
    let den := ksssPowerDenominatorExponent q (2*c) E.B ((26*q+12)*c) c
    let u := dyadicPowerScale den (W.U i.castSucc).card
    1 ≤ v ∧ E.K*v ≤ D ∧
      t^D ≤ (W.U i.castSucc).card ∧ (W.U i.castSucc).card ≤ t^(D+1) ∧
      t^step*(W.U i.succ).card ≤ 2*(W.U i.castSucc).card ∧
      (W.U i.castSucc).card ≤ t^v*(W.U i.succ).card ∧
      t^(D-v) ≤ (W.U i.succ).card ∧
      1 ≤ c ∧ u^den ≤ (W.U i.castSucc).card ∧ 1 ≤ u ∧ u ≤ t ∧
      t^(E.P*v) ≤ u^c ∧ T ≤ u ∧ n ≤ u^(c*(Rfixed+step*ell+1)) := by
  dsimp only
  have hgeom := P.retainedVortex_stage_power_geometry hsplit hlength ht hroot hrootUpper
    hrootGap hfirstGap hnlo hnhi i
  have hgaps := retained_stage_exponent_ratio_gap Rfixed step ell length m rootPower E.K
    hsplit hroot hrootGap hfirstGap i
  have hvD : retainedRatioExponent Rfixed step i.val ≤ retainedStageExponent Rfixed step ell i.val := by
    apply le_trans _ hgaps.2
    simpa only [one_mul] using Nat.mul_le_mul_right (retainedRatioExponent Rfixed step i.val) E.K_pos
  have hinner := source_stage_inner_power_lower t _ _ _ _ (by omega) hvD hgeom.1 hgeom.2.2.2.1
  have hscale := P.retained_source_process_scales E.B (26*q+12) 1 E.P T le_rfl E.P_pos
    E.denominator_budget hsplit hlength ht hroot hrootUpper hrootGap hfirstGap hnlo hnhi hthreshold i
  simp only [one_mul] at hscale
  exact ⟨hgaps.1, hgaps.2, hgeom.1, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.1, hinner, hscale⟩

end

end Erdos207
