import Wikipedia.NoExoticSixSphere.FourDiskParityBall
import Wikipedia.NoExoticSixSphere.AnnulusDoublePointDiagonal

/-!
# Arbitrarily small parity-one balls at actual annulus singularities

The original chart residual gives a linking ball within any prescribed
open neighborhood. The whole ball stays in the original open annulus and
an original target chart. The local operators are the actual derivatives
of the original map, and their sphere parity is proved to be one.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus

open GLOrthonormalization SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

abbrev ParityBall (g : Vector 4 → M) (x : Vector 4) :=
  GenericFourDisk.ParityBall g x (openDomain 3)

theorem exists_parityBall_in_neighborhood (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
    (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
    (hi : ∀ x ∈ domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
      Injective (fderiv ℝ (e.toFun ∘ g) x))
    (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
    (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
    (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
      (fun x ↦ fderiv ℝ (c ∘ g) x) {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source})
    (x : Vector 4) (hx : x ∈ domain 3)
    (hs : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x))
    (N : Set (Vector 4)) (hN : IsOpen N) (hxN : x ∈ N) :
    ∃ B : ParityBall g x, B.closedRegion ⊆ N := by
  have hnot : ¬ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) := by
    intro hend
    exact hs ((GenericFourDisk.injective_embedded_derivative_iff e g x
      ((hg x hx).mdifferentiableAt (by simp))).mp (hi x hx hend))
  have hxactive : r₀ < ‖x‖ ∧ ‖x‖ < r₁ :=
    ⟨lt_of_not_ge (fun h ↦ hnot (Or.inl h)), lt_of_not_ge (fun h ↦ hnot (Or.inr h))⟩
  obtain ⟨c, hc, hxc⟩ := hC (g x)
  let U₀ : Set (Vector 4) := {y | r₀ < ‖y‖ ∧ ‖y‖ < r₁}
  have hU₀ : IsOpen U₀ := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hU₀K : U₀ ⊆ domain 3 :=
    fun _ hy ↦ ⟨(hr₀.trans hy.1).le, (hy.2.trans hr₁).le⟩
  have hgU₀ : ContinuousOn g U₀ :=
    fun y hy ↦ (hg y (hU₀K hy)).continuousAt.continuousWithinAt
  let U := U₀ ∩ g ⁻¹' c.source
  have hU : IsOpen U := hgU₀.isOpen_inter_preimage hU₀ c.open_source
  let V := U ∩ N
  have hV : IsOpen V := hU.inter hN
  have hxV : x ∈ V := ⟨⟨hxactive, hxc⟩, hxN⟩
  have hD : ContDiffOn ℝ ∞ (fun y ↦ fderiv ℝ (c ∘ g) y) V := by
    intro y hy
    have hcs := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hy.1.2)
    have hcg := (hcs.comp y (hg y (hU₀K hy.1.1))).contDiffAt
    exact (hcg.fderiv_right (by simp)).contDiffWithinAt
  have hcompare (y : Vector 4) (hy : y ∈ U) :
      Injective (fderiv ℝ (c ∘ g) y) ↔ Injective (mfderiv (𝓡 4) (𝓡 7) g y) :=
    GenericFourDisk.injective_chart_derivative_iff g y
      ((hg y (hU₀K hy.1)).mdifferentiableAt (by simp)) c hy.2
  have hcsing : ¬ Injective (fderiv ℝ (c ∘ g) x) :=
    (hcompare x ⟨hxactive, hxc⟩).not.mpr hs
  obtain ⟨b, hball, hb0, hbV, hsing, L, hL, hparity⟩ :=
    FourSevenLocalParity.hasChartedLocalContributionOn_of_regular_residual
      (fun y ↦ fderiv ℝ (c ∘ g) y) hV hD x hxV
      ((hgen c hc).residual_regular x ⟨hxactive, hxc⟩ hcsing)
  let B : ParityBall g x := {
    targetChart := c
    chart := b
    ball_source := hball
    center := hb0
    chart_valid := fun z hz ↦
      ⟨⟨hr₀.trans (hbV hz).1.1.1, (hbV hz).1.1.2.trans hr₁⟩, (hbV hz).1.2⟩
    singular_iff := fun z hz ↦ (hcompare (b z) (hbV hz).1).not.symm.trans (hsing z hz)
    link := L
    link_value := hL
    parity_one := hparity }
  refine ⟨B, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hbV hz).2

end NoExoticSixSphere.GenericFourAnnulus
