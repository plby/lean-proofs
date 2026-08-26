/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedProfileBound
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedSourceWeight

/-!
# A uniform reciprocal-prime main bound for the literal source coefficients

The finitely many profile-pair constants are combined with the absolute
values of both pinning amplitudes. A single joint coordinate cutoff
works for every forced prime and every prescribed residue.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem exists_eventually_pinnedSourceForcedGraphKernel_bound
    {α J : Type*} {l : Filter α} {K : ℕ}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (hFcompact : ∀ j i, HasCompactSupport (F j i))
    (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (w m p₀ Y : α → ℕ) (V : α → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hY : Tendsto Y l atTop)
    (hm : ∀ᶠ a in l, 0 < m a) (hp₀ : ∀ᶠ a in l, (p₀ a).Prime)
    (hwY : ∀ᶠ a in l, w a ≤ Y a) (hYp₀ : ∀ᶠ a in l, Y a < p₀ a)
    (hcop : ∀ᶠ a in l, (m a * p₀ a - 1).Coprime (primorial (Y a)))
    (hcutoff : ∀ᶠ a in l, (w a : ℝ) ≤ Real.log (V a + 1))
    (hmV : ∀ᶠ a in l, Real.log (m a) ≤ V a)
    (hp₀V : ∀ᶠ a in l, Real.log (p₀ a) ≤ 2 * V a)
    (hLElower : ∀ᶠ a in l, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ Real.log (Y a))
    (hLEupper : ∀ᶠ a in l, Real.log (Y a) ≤ V a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in l, ∀ (p : Nat.Primes), w a < p.val →
      ∀ (r N : ℕ), jointSourceCommonPrimeBound S F G (V a) (Real.log (Y a)) ≤ N →
        ‖(((V a ^ (K - 1) * Real.log (Y a) ^ (K - 1) : ℝ) : ℂ) /
          (pinnedSingularSeries h (w a) (m a) (p₀ a) (Y a) : ℂ)) *
          pinnedSourceForcedGraphKernel S F G h
            (selectedFourierPrimeCutoff (fun q ↦ decide (w a < q)) (boundedFourierPrimes N))
            (w a) (m a) (p₀ a) (Y a) p r (V a) (Real.log (Y a))‖ ≤ C / (p : ℝ) := by
  classical
  let L (a : α) : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ :=
    twoFamilySelbergScales (V a) (Real.log (Y a))
  have hLlower : ∀ᶠ a in l, ∀ i, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ L a i := by
    filter_upwards [hLElower, hLEupper] with a hla hua
    intro i
    cases i
    · exact hla.trans hua
    · exact hla
  have hLupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a := by
    filter_upwards [hLEupper] with a hua
    intro i
    cases i
    · exact le_rfl
    · exact hua
  choose C hC hbound using fun (j k : J) ↦
    exists_eventually_pinned_forcedProfile_finite_bound h w m p₀ Y V L
      hw hV hY hm hp₀ hwY hYp₀ hcop hcutoff hmV hp₀V hLlower hLupper
      (pairedSelbergProfiles (pinnedSourceProfileFamily F G h j)
        (pinnedSourceProfileFamily F G h k))
      (hasCompactSupport_pairedSelbergProfiles _ _
        (hasCompactSupport_pinnedSourceProfileFamily F G h j (hFcompact j) hGcompact)
        (hasCompactSupport_pinnedSourceProfileFamily F G h k (hFcompact k) hGcompact))
      (contDiff_pairedSelbergProfiles _ _
        (contDiff_pinnedSourceProfileFamily F G h j (hFsmooth j) hGsmooth)
        (contDiff_pinnedSourceProfileFamily F G h k (hFsmooth k) hGsmooth))
  let c := pinnedSourceProfileAmplitude F G h
  refine ⟨∑ j ∈ S, ∑ k ∈ S, ‖c j * c k‖ * C j k,
    Finset.sum_nonneg (fun j hj ↦ Finset.sum_nonneg (fun k hk ↦
      mul_nonneg (norm_nonneg _) (hC j k))), ?_⟩
  have hall := (eventually_all_finset S).mpr (fun j hj ↦
    (eventually_all_finset S).mpr (fun k hk ↦ hbound j k))
  filter_upwards [hall] with a ha
  intro p hp r N hN
  rw [← pinnedFiniteFourierNormalization_twoFamily, pinnedSourceForcedGraphKernel_eq_profile_pairs]
  simp only [Finset.mul_sum]
  calc
    _ ≤ ∑ j ∈ S, ∑ k ∈ S, ‖c j * c k‖ * (C j k / (p : ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hcap := (compactProfileTensorCommonBound_le_family S
        (pinnedSourceProfileFamily F G h)
        (twoFamilySelbergScales (V a) (Real.log (Y a))) hj hk).trans
          ((pinnedSourceCommonPrimeBound_le_joint S F G h _ _).trans hN)
      have hb := ha j hj k hk p hp r N hcap
      calc
        _ = ‖c j * c k‖ * ‖pinnedFiniteFourierNormalization h (w a) (m a) (p₀ a) (Y a) (L a) *
            cutoffForcedSelbergProfileTensorSum
              (selectedFourierPrimeCutoff (fun q ↦ decide (w a < q)) (boundedFourierPrimes N))
              (roughPinnedFourierEdges h (w a) (m a) (p₀ a) (Y a))
              (truncatedPinnedFourierCompanion (m a) (Y a)) p
              (PinnedForcedLocalEquations h (w a) (m a) (p₀ a) p r)
              (pairedSelbergProfiles (pinnedSourceProfileFamily F G h j)
                (pinnedSourceProfileFamily F G h k)) (fun i _ ↦ L a i)‖ := by
          rw [← norm_mul]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_div, mul_div_assoc]

end

end Erdos4b
