import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Genuine relative transverse charts in both endpoint slice domains

Restrict the actual relative transverse map at source and target to
prescribed positive-radius balls. Both actual maps are retained, zero
remains in the source and fixed, and every remaining point lies in the
two required endpoint slice domains.
-/

noncomputable section

open Set Function Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A fixed-origin partial diffeomorphism can be restricted inside any
prescribed source and image balls, retaining its actual coordinate map. -/
theorem exists_transverse_chart_in_balls
    (H : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞)
    (h0 : (0 : Z) ∈ H.source) (hfix : H 0 = 0) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ G : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞,
      (0 : Z) ∈ G.source ∧ G 0 = 0 ∧ (G : Z → Z) = H ∧ G.source ⊆ H.source ∧
      G.target ⊆ H.target ∧ ∀ z ∈ G.source, ‖z‖ < r ∧ ‖G z‖ < s := by
  let A := PartialChart.restrictTarget H (isOpen_ball : IsOpen (ball (0 : Z) s))
  let G := PartialChart.restrictSource A (isOpen_ball : IsOpen (ball (0 : Z) r))
  have hG0 : (0 : Z) ∈ G.source := by
    change (0 ∈ H.source ∧ H 0 ∈ ball (0 : Z) s) ∧ (0 : Z) ∈ ball 0 r
    exact ⟨⟨h0, hfix.symm ▸ mem_ball_self hs⟩, mem_ball_self hr⟩
  refine ⟨G, hG0, hfix, rfl, fun _ hz => hz.1.1, fun _ hz => hz.1.1, ?_⟩
  intro z hz
  have hzr : z ∈ ball (0 : Z) r := hz.2
  have hzs : G z ∈ ball (0 : Z) s := hz.1.2
  exact ⟨by simpa only [mem_ball, dist_zero_right] using hzr,
    by simpa only [mem_ball, dist_zero_right] using hzs⟩

/-- Two actual transverse charts fixing zero construct their relative
chart inside both prescribed endpoint transverse slice radii. -/
theorem exists_relative_transverse_chart_in_balls
    (P Q : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞)
    (hP0 : (0 : Z) ∈ P.source) (hPfix : P 0 = 0)
    (hQ0 : (0 : Z) ∈ Q.source) (hQfix : Q 0 = 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ H : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞,
      (0 : Z) ∈ H.source ∧ H 0 = 0 ∧ (H : Z → Z) = Q.trans P.symm ∧
      H.source ⊆ (Q.trans P.symm).source ∧
      ∀ z ∈ H.source, ‖z‖ < r ∧ ‖H z‖ < s := by
  let G := Q.trans P.symm
  have hPt : (0 : Z) ∈ P.target := hPfix ▸ P.map_source' hP0
  have hG0 : (0 : Z) ∈ G.source := by
    change (0 : Z) ∈ Q.source ∧ Q 0 ∈ P.target
    exact ⟨hQ0, hQfix.symm ▸ hPt⟩
  have hGfix : G 0 = 0 := by
    change P.symm (Q 0) = 0
    rw [hQfix]
    have hh : P.symm (P 0) = 0 := P.left_inv' hP0
    rwa [hPfix] at hh
  obtain ⟨H, hH0, hHfix, hmap, hsub, _, hnorm⟩ :=
    exists_transverse_chart_in_balls G hG0 hGfix hr hs
  exact ⟨H, hH0, hHfix, hmap, hsub, hnorm⟩

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
