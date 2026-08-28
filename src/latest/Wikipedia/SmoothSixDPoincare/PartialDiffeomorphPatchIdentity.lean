import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Exact native patch identities imply smoothness on the actual patch images

A map agreeing with two native partial diffeomorphisms is smooth on their
overlap image. For full-source matching patches of a homeomorphism, the
same argument supplies its smooth inverse on the corresponding image.
-/

noncomputable section

open Set Function Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.PartialChart

variable {E F G H K L V X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace L]
  {I₀ : ModelWithCorners ℝ E H} {I : ModelWithCorners ℝ F K}
  {J : ModelWithCorners ℝ G L}
  [TopologicalSpace V] [ChartedSpace H V]
  [TopologicalSpace X] [ChartedSpace K X]
  [TopologicalSpace Y] [ChartedSpace L Y]

theorem contMDiffOn_of_patchIdentity (f : X → Y)
    (p : PartialDiffeomorph I₀ I V X ∞) (q : PartialDiffeomorph I₀ J V Y ∞)
    (hsource : p.source ⊆ q.source) (hpoint : ∀ v ∈ p.source, f (p v) = q v) :
    ContMDiffOn I J ∞ f p.target := by
  intro x hx
  have hp : ContMDiffAt I I₀ ∞ p.symm x :=
    p.symm.contMDiffOn.contMDiffAt (p.open_target.mem_nhds hx)
  have hq : ContMDiffAt I₀ J ∞ q (p.symm x) :=
    q.contMDiffOn.contMDiffAt (q.open_source.mem_nhds (hsource (p.map_target hx)))
  have he : f =ᶠ[𝓝 x] (fun y => q (p.symm y)) := by
    filter_upwards [p.open_target.mem_nhds hx] with y hy
    exact (congrArg f (p.right_inv hy)).symm.trans (hpoint _ (p.map_target hy))
  exact ((hq.comp x hp).congr_of_eventuallyEq he).contMDiffWithinAt

theorem map_target_of_patchIdentity (f : X → Y)
    (p : PartialDiffeomorph I₀ I V X ∞) (q : PartialDiffeomorph I₀ J V Y ∞)
    (hsource : p.source ⊆ q.source) (hpoint : ∀ v ∈ p.source, f (p v) = q v)
    {x : X} (hx : x ∈ p.target) : f x ∈ q.target := by
  have he : f x = q (p.symm x) := (congrArg f (p.right_inv hx)).symm.trans
    (hpoint _ (p.map_target hx))
  exact he.symm ▸ q.map_source (hsource (p.map_target hx))

theorem contMDiffOn_homeomorph_of_full_patches (e : X ≃ₜ Y)
    (p : PartialDiffeomorph I₀ I V X ∞) (q : PartialDiffeomorph I₀ J V Y ∞)
    (hp : p.source = univ) (hq : q.source = univ) (hpoint : ∀ v, e (p v) = q v) :
    ContMDiffOn I J ∞ e p.target ∧ ContMDiffOn J I ∞ e.symm q.target := by
  constructor
  · exact contMDiffOn_of_patchIdentity e p q (by rw [hp, hq]) (fun v _ => hpoint v)
  · apply contMDiffOn_of_patchIdentity e.symm q p (by rw [hp, hq])
    intro v _
    apply e.injective
    exact (e.apply_symm_apply (q v)).trans (hpoint v).symm

end Wikipedia.SmoothSixDPoincare.PartialChart
