import Wikipedia.HopfProblem.DegreeCollapseCubicFlowCylinder
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Constructing full spatial overlap germs from the matched time formulas

Endpoint convergence chooses an actual regular slice inside the endpoint
box and in a prescribed open time region. The matched transverse-time
formula holds near that whole slice center. The genuine cubic cylinder's
inverse transports it to a full spatial chart germ at the chosen cut.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ} {M : Type*}

theorem exists_cubic_spatial_overlap_germ (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ Ψ : Model m → M) {c r : ℝ} (hr : 0 < r)
    {l : Filter ℝ} [NeBot l]
    (hlim : Tendsto (fun t => cubicFlowCylinder σ a (0, t)) l
      (𝓝 (c, (0 : Fin m → ℝ))))
    {J : Set ℝ} (hJ : IsOpen J) (hJl : J ∈ l)
    (hmatch : ∀ᶠ z : Fin m → ℝ in 𝓝 0, ∀ t ∈ J,
      cubicFlowCylinder σ a (z, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r →
      Φ (cubicFlowCylinder σ a (z, t)) = Ψ (cubicFlowCylinder σ a (z, t))) :
    ∃ T ∈ J, cubicFlowCylinder σ a (0, T) ∈ ball (c, (0 : Fin m → ℝ)) r ∧
      Φ =ᶠ[𝓝 (cubicFlowCylinder σ a (0, T))] Ψ := by
  have hnear : ∀ᶠ t in l, cubicFlowCylinder σ a (0, t) ∈
      ball (c, (0 : Fin m → ℝ)) r := hlim.eventually (ball_mem_nhds _ hr)
  have hJevent : ∀ᶠ t in l, t ∈ J := hJl
  obtain ⟨T, hTJ, hTball⟩ := (hJevent.and hnear).exists
  let C := cubicFlowCylinderChart σ ha
  let p₀ : (Fin m → ℝ) × ℝ := (0, T)
  have htime : (fun p => Φ (C p)) =ᶠ[𝓝 p₀] (fun p => Ψ (C p)) := by
    have hball : ∀ᶠ p in 𝓝 p₀, C p ∈ ball (c, (0 : Fin m → ℝ)) r :=
      (contDiff_cubicFlowCylinder σ a).continuous.continuousAt.eventually
        (isOpen_ball.mem_nhds hTball)
    filter_upwards [continuousAt_fst.eventually hmatch,
      continuousAt_snd.eventually (hJ.mem_nhds hTJ), hball] with p hp hpt hpball
    exact hp p.2 hpt (ball_subset_closedBall hpball)
  have hCt : C p₀ ∈ C.target := C.map_source' (mem_univ p₀)
  have hi : C.symm (C p₀) = p₀ := C.left_inv' (mem_univ p₀)
  have hInv : Tendsto C.symm (𝓝 (C p₀)) (𝓝 p₀) := by
    have hh : Tendsto C.symm (𝓝 (C p₀)) (𝓝 (C.symm (C p₀))) :=
      C.toOpenPartialHomeomorph.symm.continuousAt hCt |>.tendsto
    rwa [hi] at hh
  refine ⟨T, hTJ, hTball, ?_⟩
  filter_upwards [hInv.eventually htime, C.open_target.mem_nhds hCt] with p hp hpt
  have hright : C (C.symm p) = p := C.right_inv' hpt
  change Φ (C (C.symm p)) = Ψ (C (C.symm p)) at hp
  rwa [hright] at hp

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
