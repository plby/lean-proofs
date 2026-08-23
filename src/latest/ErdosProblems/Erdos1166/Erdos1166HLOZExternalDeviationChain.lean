import ErdosProblems.Erdos1166.Erdos1166HLOZExternalChain
import ErdosProblems.Erdos1166.Erdos1166HLOZExternalDeviation

namespace Erdos1166.HLOZExternalDeviationChain

open Filter MeasureTheory Set
open scoped ENNReal

open HLOZExternalUpper HLOZExternalChain HLOZExternalDeviation
open HLOZFixedOriginKac

/-- Exact fixed-origin Kac kernel for the terminal-label external chain.
This isolates the one probability factorization which must be proved from
independence of disjoint blocks of iid non-distinguished pair labels. -/
def HasExternalFixedOriginKernel : Prop :=
  ∀ n k (t : KacMoment.TimeTuple n (k + 1)),
    t ∈ KacMoment.sortedTuples n (k + 1) →
    externalPathLaw.real
        (fixedHitSet n (k + 1)
          (fun (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val) (0, 0) t) ≤
      fixedGapWeight n k
        (fun d : Fin (n + 1) ↦ externalReturnProb d.val) t

private theorem external_fixedHitSet_measurable
    (n r : ℕ) (t : KacMoment.TimeTuple n r) :
    MeasurableSet
      (fixedHitSet n r
        (fun (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val) (0, 0) t) := by
  have heq :
      fixedHitSet n r
          (fun (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val) (0, 0) t =
        ⋂ i : Fin r, {s : ℕ → Site | s (t i).val = (0, 0)} := by
    ext s
    simp [fixedHitSet]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq_fun (measurable_pi_apply (t i).val) measurable_const

private theorem sum_externalReturnProb_fin (n : ℕ) :
    (∑ d : Fin (n + 1), externalReturnProb d.val) =
      externalFiniteGreen n := by
  rw [externalFiniteGreen]
  exact Fin.sum_univ_eq_sum_range externalReturnProb (n + 1)

/-- Source-clock HLOZ (2.19), reduced to the two exact external-chain facts:
the iid terminal-label fixed-origin kernel and the sharp Green estimate.
The conclusion is on `externalChainUpperBad`, hence on genuine external time,
not on the weaker original-time deleted local time. -/
theorem hasExternalChainUpperDeviation_of_kernel_and_sharpGreen
    (hKernel : HasExternalFixedOriginKernel)
    (hGreen : HasExternalSharpGreenUpper) :
    HasExternalChainUpperDeviation := by
  have hpath : ∀ᶠ n : ℕ in atTop,
      externalPathLaw.real {s | externalThreshold n ≤
        (KacMoment.finiteLocalTime n
          (fun i : Fin (n + 1) ↦ s i.val) (0, 0) : ℝ)} ≤
        externalRate n := by
    apply eventually_externalThreshold_measureReal_le_rate_of_fixedOriginKac
      (μ := externalPathLaw)
      (X := fun n (s : ℕ → Site) (i : Fin (n + 1)) ↦ s i.val)
      (x := (0, 0))
      (q := fun n (d : Fin (n + 1)) ↦ externalReturnProb d.val)
    · intro n
      simpa only [finiteLocalTime_finiteCoordinateProcess] using
        measurable_localTime_eval n (0, 0)
    · exact external_fixedHitSet_measurable
    · intro n d
      exact measureReal_nonneg
    · exact hKernel
    · obtain ⟨C, hC⟩ := hGreen
      refine ⟨C, ?_⟩
      filter_upwards [hC] with n hn
      rwa [sum_externalReturnProb_fin]
  filter_upwards [hpath] with n hn
  have hfinite :
      {s : ℕ → Site | externalThreshold n ≤
          (KacMoment.finiteLocalTime n
            (fun i : Fin (n + 1) ↦ s i.val) (0, 0) : ℝ)} =
        {s | externalThreshold n ≤ (localTime s n (0, 0) : ℝ)} := by
    ext s
    change externalThreshold n ≤
      (KacMoment.finiteLocalTime n (fun i : Fin (n + 1) ↦ s i.val) (0, 0) : ℝ) ↔
        externalThreshold n ≤ (localTime s n (0, 0) : ℝ)
    rw [finiteLocalTime_finiteCoordinateProcess]
  rw [hfinite] at hn
  have hbridge := externalPathLaw_highLocalTime_eq_externalChainUpperBad n
  have hbridgeReal :
      externalPathLaw.real
          {s | externalThreshold n ≤ (localTime s n (0, 0) : ℝ)} =
        incrementLaw.real (externalChainUpperBad n) := by
    simpa only [Measure.real] using congrArg ENNReal.toReal hbridge
  rw [← hbridgeReal]
  exact hn

end Erdos1166.HLOZExternalDeviationChain
