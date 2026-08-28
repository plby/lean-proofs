import Wikipedia.NoExoticSixSphere.DiskDoublePointGerm
import Wikipedia.NoExoticSixSphere.DiskDoublePointDiagonal
import Wikipedia.NoExoticSixSphere.ReflectionQuotientChart

/-!
# Actual reflection and half-line charts at generic disk singularities

The original immersive outer annulus places each native singularity in the
region of regular chart jets. Its actual rank-three residual gives a local
reflection chart on the original ordered double-point closure. The genuine
swap quotient gives a half-line chart, with coordinate zero exactly at the
actual diagonal orbits throughout its source.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiskDoublePoints

open GLOrthonormalization InvolutionQuotient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
  (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (ρ : ℝ) (hρ1 : ρ < 1)
  (hi : ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x))
  (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
  (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
  (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
    (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source})

include e hg hρ1 hi hC hgen

theorem exists_closed_curve_at_singular (x : Vector 4) (hx : x ∈ closedBall 0 1)
    (hs : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)) :
    ∃ ha : (x, x) ∈ closure (points g),
      ∃ d : OpenPartialHomeomorph (ClosedPoints g) ℝ,
        (⟨(x, x), ha⟩ : ClosedPoints g) ∈ d.source ∧ d ⟨(x, x), ha⟩ = 0 ∧
        (∀ a ∈ d.source, swapClosure g a ∈ d.source) ∧
        ∀ a ∈ d.source, d (swapClosure g a) = -d a := by
  have hxρ : ‖x‖ < ρ := by
    apply lt_of_not_ge
    intro hn
    exact hs ((GenericFourDisk.injective_embedded_derivative_iff e g x
      ((hg x hx).mdifferentiableAt (by simp))).mp (hi x hx hn))
  have hxb : x ∈ ball 0 1 := mem_ball_zero_iff.mpr (hxρ.trans hρ1)
  obtain ⟨c, hc, hxc⟩ := hC (g x)
  let V : Set (Vector 4) := {y | ‖y‖ < ρ}
  have hVK : V ⊆ closedBall 0 1 := fun y hy ↦
    mem_closedBall_zero_iff.mpr (hy.trans hρ1).le
  have hV : IsOpen V := isOpen_lt continuous_norm continuous_const
  have hgV : ContinuousOn g V := fun y hy ↦
    (hg y (hVK hy)).continuousAt.continuousWithinAt
  let U := V ∩ g ⁻¹' c.source
  have hU : IsOpen U := hgV.isOpen_inter_preimage hV c.open_source
  have hxU : x ∈ U := ⟨hxρ, hxc⟩
  have hcg : ContDiffOn ℝ ∞ (c ∘ g) U := by
    intro y hy
    have hcs := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hy.2)
    exact (hcs.comp y (hg y (hVK hy.1))).contDiffAt.contDiffWithinAt
  have hcsing : ¬ Injective (fderiv ℝ (c ∘ g) x) :=
    (GenericFourDisk.injective_chart_derivative_iff g x
      ((hg x hx).mdifferentiableAt (by simp)) c hxc).not.mpr hs
  have hcurve := MapDoublePoints.exists_closed_curve_of_local_regular_residual
    (c ∘ g) hU hcg x hxU ((hgen c hc).residual_regular x ⟨hxρ, hxc⟩ hcsing)
  have hcont : ContinuousOn g (ball 0 1) :=
    fun y hy ↦ (hg y (ball_subset_closedBall hy)).continuousAt.continuousWithinAt
  exact exists_curve_of_closed_germ g (c ∘ g) x
    (closedPoints_chart_eventuallyEq g hcont c x hxb hxc) hcurve

theorem singular_diagonal_mem_closure (x : Vector 4) (hx : x ∈ closedBall 0 1)
    (hs : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)) : (x, x) ∈ closure (points g) :=
  (exists_closed_curve_at_singular e g hg ρ hρ1 hi C hC hgen x hx hs).choose

theorem exists_unordered_chart_at_singular (x : Vector 4) (hx : x ∈ closedBall 0 1)
    (hs : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)) :
    ∃ ha : (x, x) ∈ closure (points g),
      ∃ d : OpenPartialHomeomorph (Unordered g) HalfLine,
        unorderedProj g ⟨(x, x), ha⟩ ∈ d.source ∧
        d (unorderedProj g ⟨(x, x), ha⟩) = ⟨0, le_rfl⟩ ∧
        ∀ a ∈ d.source, (d a).val = 0 ↔ a ∈ diagonalOrbits g := by
  obtain ⟨ha, c, hcp, hcz, hcs, hcn⟩ :=
    exists_closed_curve_at_singular e g hg ρ hρ1 hi C hC hgen x hx hs
  let k : ReflectionChart (swapClosure g) := ⟨c, hcs, hcn⟩
  let d := k.quotientChart (swapClosure_involutive g) (swapClosure g).continuous
  have hcenter := k.quotientChart_center (swapClosure_involutive g)
    (swapClosure g).continuous hcp hcz
  refine ⟨ha, d, hcenter.1, hcenter.2, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := ha
  exact (k.quotientChart_zero_iff_fixed (swapClosure_involutive g)
    (swapClosure g).continuous hb).trans
    ((swapClosure_fixed_iff g b).trans (mem_diagonalOrbits_iff g b).symm)

theorem exists_unordered_boundary_chart (q : Unordered g) (hq : q ∈ diagonalOrbits g) :
    ∃ d : OpenPartialHomeomorph (Unordered g) HalfLine,
      q ∈ d.source ∧ d q = ⟨0, le_rfl⟩ ∧
      ∀ y ∈ d.source, (d y).val = 0 ↔ y ∈ diagonalOrbits g := by
  obtain ⟨a, hdiag, rfl⟩ := hq
  rcases a with ⟨⟨x, y⟩, hcl⟩
  change x = y at hdiag
  subst y
  have hx : x ∈ closedBall 0 1 := (closure_subset_closedBall g hcl).1
  have hs := singular_of_diagonal_mem_closure e g hg ⟨(x, x), hcl⟩ rfl
  obtain ⟨ha, d, hdp, hdz, hiff⟩ :=
    exists_unordered_chart_at_singular e g hg ρ hρ1 hi C hC hgen x hx hs
  exact ⟨d, hdp, hdz, hiff⟩

end NoExoticSixSphere.DiskDoublePoints
