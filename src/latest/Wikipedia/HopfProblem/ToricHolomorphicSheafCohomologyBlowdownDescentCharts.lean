import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowdownDescentHolomorphic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Gluing

/-!
# Blowdown descent in the two explicit affine charts

Compatible entire functions `F(x,t)` and `D(u,s)` first glue to an actual
holomorphic function on the incidence blowup. The proved blowdown theorem
then produces a unique entire function `H(s,t)` with
`F(x,t) = H(x*t,t)` and `D(u,s) = H(s,u*s)`.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowdownDescent

open AffineBlowup ToricCharts
open PeriodTorusLineBundleClassificationPolydiscAnalytic

def chartFamily (F D : ℂ × ℂ → ℂ) (b : Bool) (q : ℂ × ℂ) : ℂ :=
  if b then D (q.2, q.1) else F (q.2, q.1)

theorem chartFamily_compatible {F D : ℂ × ℂ → ℂ}
    (hFD : ∀ x t : ℂ, x ≠ 0 → F (x, t) = D (x⁻¹, x * t)) :
    BlowupH1.CompatibleOn univ (chartFamily F D) := by
  apply BlowupH1.compatibleOn_of_cross
  intro q hq _
  change F (q.2, q.1) = D (q.2⁻¹, q.1 * q.2)
  simpa only [mul_comm q.2 q.1] using hFD q.2 q.1 hq

theorem chartFamily_analytic {F D : ℂ × ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hD : AnalyticOnNhd ℂ D univ) (b : Bool) :
    AnalyticOnNhd ℂ (chartFamily F D b) univ := by
  intro q _
  cases b
  · change AnalyticAt ℂ (fun p : ℂ × ℂ => F (p.2, p.1)) q
    exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2, p.1))
      (hF (q.2, q.1) (mem_univ _)) (analyticAt_snd.prod analyticAt_fst)
  · change AnalyticAt ℂ (fun p : ℂ × ℂ => D (p.2, p.1)) q
    exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2, p.1))
      (hD (q.2, q.1) (mem_univ _)) (analyticAt_snd.prod analyticAt_fst)

theorem chartGlue_holomorphic {F D : ℂ × ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hD : AnalyticOnNhd ℂ D univ)
    (hFD : ∀ x t : ℂ, x ≠ 0 → F (x, t) = D (x⁻¹, x * t)) :
    ContMDiff 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω
      (BlowupH1.chartGlue (chartFamily F D)) := by
  apply contMDiffOn_univ.mp
  apply BlowupH1.chartGlue_contMDiffOn isOpen_univ _ (chartFamily_compatible hFD)
  intro b
  simpa only [preimage_univ] using chartFamily_analytic hF hD b

/-- The compatible chart functions descend through the actual blowup.
Only their analyticity and their literal overlap identity are assumed. -/
theorem exists_chart_descent {F D : ℂ × ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hD : AnalyticOnNhd ℂ D univ)
    (hFD : ∀ x t : ℂ, x ≠ 0 → F (x, t) = D (x⁻¹, x * t)) :
    ∃ H : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ H univ ∧
      (∀ x t : ℂ, H (x * t, t) = F (x, t)) ∧
      (∀ u s : ℂ, H (s, u * s) = D (u, s)) := by
  let f : Space → ℂ := BlowupH1.chartGlue (chartFamily F D)
  have hf : ContMDiff 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω f :=
    chartGlue_holomorphic hF hD hFD
  let H : ℂ × ℂ → ℂ := descend f ∘ complexPairEquiv.symm
  have hH : AnalyticOnNhd ℂ H univ := by
    intro q _
    exact (descend_analytic hf _ (mem_univ _)).comp
      (complexPairEquiv.symm.toContinuousLinearMap.analyticAt q)
  refine ⟨H, hH, ?_, ?_⟩
  · intro x t
    have he := descend_projection hf (BlowupH1.chartMap false (t, x))
    have hg := BlowupH1.chartGlue_chartMap (chartFamily F D) (chartFamily_compatible hFD)
      false (t, x) (mem_univ _)
    exact he.trans hg
  · intro u s
    have he := descend_projection hf (BlowupH1.chartMap true (s, u))
    have hg := BlowupH1.chartGlue_chartMap (chartFamily F D) (chartFamily_compatible hFD)
      true (s, u) (mem_univ _)
    change descend f ![s, u * s] = D (u, s)
    rw [mul_comm u s]
    exact he.trans hg

theorem chart_descent_unique {F D H K : ℂ × ℂ → ℂ}
    (hHF : ∀ x t : ℂ, H (x * t, t) = F (x, t))
    (hHD : ∀ u s : ℂ, H (s, u * s) = D (u, s))
    (hKF : ∀ x t : ℂ, K (x * t, t) = F (x, t))
    (hKD : ∀ u s : ℂ, K (s, u * s) = D (u, s)) : H = K := by
  funext q
  change H (q.1, q.2) = K (q.1, q.2)
  by_cases ht : q.2 = 0
  · simpa only [zero_mul, ht] using (hHD 0 q.1).trans (hKD 0 q.1).symm
  · have he := (hHF (q.1 / q.2) q.2).trans (hKF (q.1 / q.2) q.2).symm
    simpa only [div_mul_cancel₀ _ ht] using he

theorem exists_unique_chart_descent {F D : ℂ × ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hD : AnalyticOnNhd ℂ D univ)
    (hFD : ∀ x t : ℂ, x ≠ 0 → F (x, t) = D (x⁻¹, x * t)) :
    ∃! H : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ H univ ∧
      (∀ x t : ℂ, H (x * t, t) = F (x, t)) ∧
      (∀ u s : ℂ, H (s, u * s) = D (u, s)) := by
  obtain ⟨H, hH, hHF, hHD⟩ := exists_chart_descent hF hD hFD
  refine ⟨H, ⟨hH, hHF, hHD⟩, ?_⟩
  intro K hK
  exact chart_descent_unique hK.2.1 hK.2.2 hHF hHD

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowdownDescent
