import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneDomains
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneApproximationContours

/-!
# First-coordinate Cauchy contours with an open parameter domain

A small translated parameter disc lets the actual compact-circle
integral theorem apply at every point of the parameter domain. Thus no
extension across a punctured parameter axis is assumed.
-/

noncomputable section

open Set Metric Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

open HolomorphicCousin Laurent

def firstPositiveContour (f : ℂ × ℂ → ℂ) (R : ℝ) (q : ℂ × ℂ) : ℂ :=
  cauchyTransform (fun z => f (z, q.2)) R q.1

def firstReciprocalContour (f : ℂ × ℂ → ℂ) (R : ℝ) (q : ℂ × ℂ) : ℂ :=
  infinityKernel (fun z => f (z, q.2)) R q.1

theorem exists_translated_circle_data {f : ℂ × ℂ → ℂ} {R : ℝ} {V : Set ℂ}
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f (sphere (0 : ℂ) R ×ˢ V))
    {w : ℂ} (hw : w ∈ V) :
    ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ (fun p : ℂ × ℂ => f (p.2, w + p.1))
      (closedBall (0 : ℂ) r ×ˢ sphere 0 R) := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hw)
  refine ⟨r, hr, ?_⟩
  intro p hp
  have hmem : w + p.1 ∈ V := by
    apply hsub
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hp.1
  exact AnalyticAt.comp (f := fun a : ℂ × ℂ => (a.2, w + a.1))
    (hf (p.2, w + p.1) ⟨hp.2, hmem⟩)
    (analyticAt_snd.prod (analyticAt_const.add analyticAt_fst))

theorem firstPositiveContour_analytic {f : ℂ × ℂ → ℂ} {R : ℝ} {V : Set ℂ}
    (hR : 0 < R) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f (sphere (0 : ℂ) R ×ˢ V)) :
    AnalyticOnNhd ℂ (firstPositiveContour f R) (ball (0 : ℂ) R ×ˢ V) := by
  intro q hq
  obtain ⟨r, hr, hdata⟩ := exists_translated_circle_data hV hf hq.2
  let g : ℂ × ℂ → ℂ := fun p => f (p.2, q.2 + p.1)
  have hcontour : AnalyticAt ℂ (positiveContour g R) (q.2 - q.2, q.1) := by
    simpa only [sub_self] using
      PuncturedDbarOne.positiveContour_local_analytic hr hR hdata
        (0, q.1) ⟨mem_ball_self hr, hq.1⟩
  have hcomp : AnalyticAt ℂ (fun p : ℂ × ℂ => positiveContour g R (p.2 - q.2, p.1)) q :=
    AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2 - q.2, p.1)) hcontour
      ((analyticAt_snd.sub analyticAt_const).prod analyticAt_fst)
  have he : (fun p : ℂ × ℂ => positiveContour g R (p.2 - q.2, p.1)) =
      firstPositiveContour f R := by
    funext p
    have hc : q.2 + (p.2 - q.2) = p.2 := by abel
    simp only [positiveContour, g, firstPositiveContour, hc]
  rwa [he] at hcomp

theorem firstReciprocalContour_analytic {f : ℂ × ℂ → ℂ} {R : ℝ} {V : Set ℂ}
    (hR : 0 < R) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f (sphere (0 : ℂ) R ×ˢ V)) :
    AnalyticOnNhd ℂ (firstReciprocalContour f R) (ball (0 : ℂ) R⁻¹ ×ˢ V) := by
  intro q hq
  obtain ⟨r, hr, hdata⟩ := exists_translated_circle_data hV hf hq.2
  let g : ℂ × ℂ → ℂ := fun p => f (p.2, q.2 + p.1)
  have hcontour : AnalyticAt ℂ (reciprocalContour g R) (q.2 - q.2, q.1) := by
    simpa only [sub_self] using
      PuncturedDbarOne.reciprocalContour_local_analytic hr hR hdata
        (0, q.1) ⟨mem_ball_self hr, hq.1⟩
  have hcomp : AnalyticAt ℂ
      (fun p : ℂ × ℂ => reciprocalContour g R (p.2 - q.2, p.1)) q :=
    AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2 - q.2, p.1)) hcontour
      ((analyticAt_snd.sub analyticAt_const).prod analyticAt_fst)
  have he : (fun p : ℂ × ℂ => reciprocalContour g R (p.2 - q.2, p.1)) =
      firstReciprocalContour f R := by
    funext p
    have hc : q.2 + (p.2 - q.2) = p.2 := by abel
    simp only [reciprocalContour, g, firstReciprocalContour, hc]
  rwa [he] at hcomp

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
