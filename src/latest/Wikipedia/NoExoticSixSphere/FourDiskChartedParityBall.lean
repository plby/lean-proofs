import Wikipedia.NoExoticSixSphere.FourDiskParityBall

/-!
# Arbitrarily small parity-one balls at the original native disk singularities

The actual regular chart residual supplies a linking ball inside any
specified open neighborhood of the native singularity. The whole ball
stays in the original disk interior and the original target chart. Its
operators and singularity characterization are those of the original map.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

theorem exists_parityBall_in_neighborhood (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
    (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (ρ : ℝ) (hρ1 : ρ < 1)
    (hi : ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x))
    (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
    (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
    (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
      (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source})
    (x : Vector 4) (hx : x ∈ closedBall 0 1)
    (hs : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x))
    (N : Set (Vector 4)) (hN : IsOpen N) (hxN : x ∈ N) :
    ∃ B : ParityBall g x, B.closedRegion ⊆ N := by
  have hxρ : ‖x‖ < ρ := by
    apply lt_of_not_ge
    intro hn
    exact hs ((injective_embedded_derivative_iff e g x
      ((hg x hx).mdifferentiableAt (by simp))).mp (hi x hx hn))
  obtain ⟨c, hc, hxc⟩ := hC (g x)
  let U₀ : Set (Vector 4) := {y | ‖y‖ < ρ}
  have hU₀ : IsOpen U₀ := isOpen_lt continuous_norm continuous_const
  have hU₀K : U₀ ⊆ closedBall 0 1 := fun y hy ↦
    mem_closedBall_zero_iff.mpr (hy.trans hρ1).le
  have hgU₀ : ContinuousOn g U₀ := fun y hy ↦
    (hg y (hU₀K hy)).continuousAt.continuousWithinAt
  let U := U₀ ∩ g ⁻¹' c.source
  have hU : IsOpen U := hgU₀.isOpen_inter_preimage hU₀ c.open_source
  let V := U ∩ N
  have hV : IsOpen V := hU.inter hN
  have hxV : x ∈ V := ⟨⟨hxρ, hxc⟩, hxN⟩
  have hD : ContDiffOn ℝ ∞ (fun y ↦ fderiv ℝ (c ∘ g) y) V := by
    intro y hy
    have hcs := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hy.1.2)
    have hcg := (hcs.comp y (hg y (hU₀K hy.1.1))).contDiffAt
    exact (hcg.fderiv_right (by simp)).contDiffWithinAt
  have hcompare (y : Vector 4) (hy : y ∈ U) :
      Injective (fderiv ℝ (c ∘ g) y) ↔ Injective (mfderiv (𝓡 4) (𝓡 7) g y) :=
    injective_chart_derivative_iff g y ((hg y (hU₀K hy.1)).mdifferentiableAt (by simp)) c hy.2
  have hcsing : ¬ Injective (fderiv ℝ (c ∘ g) x) :=
    (hcompare x ⟨hxρ, hxc⟩).not.mpr hs
  obtain ⟨b, hball, hb0, hbV, hsing, L, hL, hparity⟩ :=
    FourSevenLocalParity.hasChartedLocalContributionOn_of_regular_residual
      (fun y ↦ fderiv ℝ (c ∘ g) y) hV hD x hxV
      ((hgen c hc).residual_regular x ⟨hxρ, hxc⟩ hcsing)
  let B : ParityBall g x := {
    targetChart := c
    chart := b
    ball_source := hball
    center := hb0
    chart_valid := fun z hz ↦
      ⟨mem_ball_zero_iff.mpr ((hbV hz).1.1.trans hρ1), (hbV hz).1.2⟩
    singular_iff := fun z hz ↦ (hcompare (b z) (hbV hz).1).not.symm.trans (hsing z hz)
    link := L
    link_value := hL
    parity_one := hparity }
  refine ⟨B, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hbV hz).2

end NoExoticSixSphere.GenericFourDisk
