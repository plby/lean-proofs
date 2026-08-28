import Wikipedia.HopfProblem.DegreeCollapseSignedTimeDerivative
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# A smooth strictly decreasing height on the complete crossing basin

The difference of the signed times to two strictly crossed levels is
positive and constant on each orbit. Their normalized ratio therefore
gives an actual smooth height, with the prescribed boundary values and
strictly negative native directional derivative. Equality on boundary
collars is a separate extension step, not claimed here.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

def crossingBasin (F : Flow ℝ X) (f : X → ℝ) (c d : ℝ) : Set X :=
  levelBasin F f c ∩ levelBasin F f d

def crossingDuration (F : Flow ℝ X) (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  signedLevelTime F f c x - signedLevelTime F f d x

def flowBandHeight (F : Flow ℝ X) (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  c + (d - c) * signedLevelTime F f c x / crossingDuration F f c d x

variable (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
  (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t)
  {c d : ℝ} (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0)

include hf hD hder hc

theorem crossingDuration_pos (hcd : c < d) {x : X} (hx : x ∈ crossingBasin F f c d) :
    0 < crossingDuration F f c d x := by
  apply sub_pos.mpr
  by_contra h
  have hle := le_of_not_gt h
  have hh := forwardInvariant_sublevel_of_boundary F hf hD hder hc
    (F (signedLevelTime F f c x) x) (signedLevelTime_hits F f c hx.1).le
    (signedLevelTime F f d x - signedLevelTime F f c x) (sub_nonneg.mpr hle)
  rw [← F.map_add, sub_add_cancel, signedLevelTime_hits F f d hx.2] at hh
  exact (not_le_of_gt hcd) hh

include hd

theorem crossingDuration_flow {x : X} (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    crossingDuration F f c d (F s x) = crossingDuration F f c d x := by
  simp only [crossingDuration,
    signedLevelTime_flow F hf hD hder hc hx.1 s,
    signedLevelTime_flow F hf hD hder hd hx.2 s]
  ring

theorem flowBandHeight_flow {x : X} (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    flowBandHeight F f c d (F s x) = flowBandHeight F f c d x -
      ((d - c) / crossingDuration F f c d x) * s := by
  simp only [flowBandHeight, crossingDuration_flow F hf hD hder hc hd hx s,
    signedLevelTime_flow F hf hD hder hc hx.1 s]
  ring

omit hd in
theorem flowBandHeight_lower {x : X} (hx : f x = c) :
    flowBandHeight F f c d x = c := by
  simp only [flowBandHeight, signedLevelTime_eq_zero F hf hD hder hc hx,
    mul_zero, zero_div, add_zero]

theorem flowBandHeight_upper (hcd : c < d) {x : X}
    (hx : x ∈ crossingBasin F f c d) (hfx : f x = d) :
    flowBandHeight F f c d x = d := by
  have hz := signedLevelTime_eq_zero F hf hD hder hd hfx
  have hpos := crossingDuration_pos F hf hD hder hc hcd hx
  have heq : signedLevelTime F f c x = crossingDuration F f c d x := by
    simp only [crossingDuration, hz, sub_zero]
  rw [flowBandHeight, heq, mul_div_cancel_right₀ _ hpos.ne']
  ring

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

omit hf hD hder hc hd in
/-- The normalized signed-time height is smooth on its actual open basin,
with its exact strictly negative native directional derivative. -/
theorem smooth_flowBandHeight {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (crossingBasin F f c d) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d)
        (crossingBasin F f c d) ∧
      ∀ x ∈ crossingBasin F f c d,
        mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) =
          -((d - c) / crossingDuration F f c d x) ∧
        mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) < 0 := by
  obtain ⟨hBc, htc, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  obtain ⟨hBd, htd, -⟩ := smooth_signed_level_time hf hV F hcurve hd
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    Wikipedia.SmoothSixDPoincare.FlowConstruction.hasDerivAt_comp_integralCurve
      hf (hcurve x) t
  have hB : IsOpen (crossingBasin F f c d) := hBc.inter hBd
  have hpos (x : M) (hx : x ∈ crossingBasin F f c d) :
      0 < crossingDuration F f c d x :=
    crossingDuration_pos F hf.continuous hD hder hc hcd hx
  have hsc := htc.mono (inter_subset_left : crossingBasin F f c d ⊆ levelBasin F f c)
  have hsd := htd.mono (inter_subset_right : crossingBasin F f c d ⊆ levelBasin F f d)
  have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (crossingDuration F f c d)
      (crossingBasin F f c d) := hsc.sub hsd
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d)
      (crossingBasin F f c d) :=
    contMDiffOn_const.add ((contMDiffOn_const.mul hsc).div₀ hA
      (fun x hx => (hpos x hx).ne'))
  refine ⟨hB, hg, ?_⟩
  intro x hx
  have hlocal : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (flowBandHeight F f c d) (F 0 x) := by
    rw [F.map_zero_apply]
    exact ((hg x hx).contMDiffAt (hB.mem_nhds hx)).mdifferentiableAt (by simp)
  have hchain := hasDerivAt_comp_native_integralCurve_at hlocal (hcurve x)
  have heq : (flowBandHeight F f c d ∘ (fun t => F t x)) =
      fun t => flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * t :=
    funext (fun t => flowBandHeight_flow F hf.continuous hD hder hc hd hx t)
  rw [heq] at hchain
  have hline := ((hasDerivAt_id (0 : ℝ)).const_mul
    ((d - c) / crossingDuration F f c d x)).const_sub (flowBandHeight F f c d x)
  have hnative : mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) =
      -((d - c) / crossingDuration F f c d x) := by
    have he := congrArg
      (fun y : M => mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) y (V y)) (F.map_zero_apply x)
    exact he.symm.trans (by simpa using hchain.unique hline)
  exact ⟨hnative, hnative ▸ neg_neg_of_pos (div_pos (sub_pos.mpr hcd) (hpos x hx))⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
