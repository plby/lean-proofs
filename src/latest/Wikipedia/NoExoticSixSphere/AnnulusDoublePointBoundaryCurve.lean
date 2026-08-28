import Wikipedia.NoExoticSixSphere.AnnulusDoublePointGerm
import Wikipedia.NoExoticSixSphere.AnnulusDoublePointDiagonal
import Wikipedia.NoExoticSixSphere.ReflectionQuotientChart

/-!
# Reflection and half-line charts at original annulus singularities

Both protected immersive collars force each intrinsic singularity into
the region of regular chart jets. The actual rank-three residual gives
a reflection chart on the original ordered double-point closure. The
genuine swap quotient gives a half-line chart whose coordinate zero is
exactly the actual diagonal orbit set throughout its source.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.AnnulusDoublePoints

open GLOrthonormalization InvolutionQuotient SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
  (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
  (hi : ∀ x ∈ domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
    Injective (fderiv ℝ (e.toFun ∘ g) x))
  (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
  (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
  (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
    (fun x ↦ fderiv ℝ (c ∘ g) x) {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source})

include e hg hr₀ hr₁ hi hC hgen

theorem exists_closed_curve_at_singular (x : Vector 4) (hx : x ∈ domain 3)
    (hs : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)) :
    ∃ ha : (x, x) ∈ closure (points g),
      ∃ d : OpenPartialHomeomorph (ClosedPoints g) ℝ,
        (⟨(x, x), ha⟩ : ClosedPoints g) ∈ d.source ∧ d ⟨(x, x), ha⟩ = 0 ∧
        (∀ a ∈ d.source, swapClosure g a ∈ d.source) ∧
        ∀ a ∈ d.source, d (swapClosure g a) = -d a := by
  have hnot : ¬ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) := by
    intro hend
    exact hs ((GenericFourDisk.injective_embedded_derivative_iff e g x
      ((hg x hx).mdifferentiableAt (by simp))).mp (hi x hx hend))
  have hxactive : r₀ < ‖x‖ ∧ ‖x‖ < r₁ :=
    ⟨lt_of_not_ge (fun h ↦ hnot (Or.inl h)), lt_of_not_ge (fun h ↦ hnot (Or.inr h))⟩
  have hxb : x ∈ openDomain 3 := ⟨hr₀.trans hxactive.1, hxactive.2.trans hr₁⟩
  obtain ⟨c, hc, hxc⟩ := hC (g x)
  let V : Set (Vector 4) := {y | r₀ < ‖y‖ ∧ ‖y‖ < r₁}
  have hVK : V ⊆ domain 3 :=
    fun _ hy ↦ ⟨(hr₀.trans hy.1).le, (hy.2.trans hr₁).le⟩
  have hV : IsOpen V := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hgV : ContinuousOn g V :=
    fun y hy ↦ (hg y (hVK hy)).continuousAt.continuousWithinAt
  let U := V ∩ g ⁻¹' c.source
  have hU : IsOpen U := hgV.isOpen_inter_preimage hV c.open_source
  have hxU : x ∈ U := ⟨hxactive, hxc⟩
  have hcg : ContDiffOn ℝ ∞ (c ∘ g) U := by
    intro y hy
    have hcs := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hy.2)
    exact (hcs.comp y (hg y (hVK hy.1))).contDiffAt.contDiffWithinAt
  have hcsing : ¬ Injective (fderiv ℝ (c ∘ g) x) :=
    (GenericFourDisk.injective_chart_derivative_iff g x
      ((hg x hx).mdifferentiableAt (by simp)) c hxc).not.mpr hs
  have hcurve := MapDoublePoints.exists_closed_curve_of_local_regular_residual
    (c ∘ g) hU hcg x hxU ((hgen c hc).residual_regular x ⟨hxactive, hxc⟩ hcsing)
  have hcont : ContinuousOn g (openDomain 3) :=
    fun y hy ↦ (hg y (openDomain_subset_domain 3 hy)).continuousAt.continuousWithinAt
  exact exists_curve_of_closed_germ g (c ∘ g) x
    (closedPoints_chart_eventuallyEq g hcont c x hxb hxc) hcurve

theorem singular_diagonal_mem_closure (x : Vector 4) (hx : x ∈ domain 3)
    (hs : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)) : (x, x) ∈ closure (points g) :=
  (exists_closed_curve_at_singular e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen x hx hs).choose

theorem exists_unordered_chart_at_singular (x : Vector 4) (hx : x ∈ domain 3)
    (hs : ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)) :
    ∃ ha : (x, x) ∈ closure (points g),
      ∃ d : OpenPartialHomeomorph (Unordered g) HalfLine,
        unorderedProj g ⟨(x, x), ha⟩ ∈ d.source ∧
        d (unorderedProj g ⟨(x, x), ha⟩) = ⟨0, le_rfl⟩ ∧
        ∀ a ∈ d.source, (d a).val = 0 ↔ a ∈ diagonalOrbits g := by
  obtain ⟨ha, c, hcp, hcz, hcs, hcn⟩ :=
    exists_closed_curve_at_singular e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen x hx hs
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
  have hx : x ∈ domain 3 := (closure_subset_domain g hcl).1
  have hs := singular_of_diagonal_mem_closure e g hg ⟨(x, x), hcl⟩ rfl
  obtain ⟨ha, d, hdp, hdz, hiff⟩ :=
    exists_unordered_chart_at_singular e g hg r₀ r₁ hr₀ hr₁ hi C hC hgen x hx hs
  exact ⟨d, hdp, hdz, hiff⟩

end NoExoticSixSphere.AnnulusDoublePoints
