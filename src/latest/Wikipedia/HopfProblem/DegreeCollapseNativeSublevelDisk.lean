import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.SmoothSixDPoincare.Hemisphere

/-!
# A sublevel disk with a native smooth neighborhood

The parametrization is a partial diffeomorphism whose open source contains
the entire closed unit ball. Its two exact image identities record the
full sublevel and its boundary. Transport by an actual ambient
diffeomorphism retains this stronger data, including the neighborhood.
-/

noncomputable section

open Set Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

structure NativeSublevelDisk (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (a : ℝ) where
  chart : PartialDiffeomorph 𝓘(ℝ, Hemisphere.Ambient n) 𝓘(ℝ, E) (Hemisphere.Ambient n) M ∞
  closedBall_source : closedBall (0 : Hemisphere.Ambient n) 1 ⊆ chart.source
  image_closedBall : chart '' closedBall (0 : Hemisphere.Ambient n) 1 = {x : M | f x ≤ a}
  image_sphere : chart '' sphere (0 : Hemisphere.Ambient n) 1 = {x : M | f x = a}

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {a b : ℝ} {n : ℕ}

def NativeSublevelDisk.transport (d : NativeSublevelDisk n E f a)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hsub : D '' {x : M | f x ≤ a} = {x : M | f x ≤ b})
    (hlevel : D '' {x : M | f x = a} = {x : M | f x = b}) :
    NativeSublevelDisk n E f b where
  chart := d.chart.trans D.toPartialDiffeomorph
  closedBall_source v hv := ⟨d.closedBall_source hv, mem_univ _⟩
  image_closedBall := by
    change (fun v => D (d.chart v)) '' closedBall (0 : Hemisphere.Ambient n) 1 = _
    rw [← image_image, d.image_closedBall, hsub]
  image_sphere := by
    change (fun v => D (d.chart v)) '' sphere (0 : Hemisphere.Ambient n) 1 = _
    rw [← image_image, d.image_sphere, hlevel]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
