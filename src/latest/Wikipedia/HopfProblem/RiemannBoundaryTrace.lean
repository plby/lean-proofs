import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Boundary traces of bounded primitives

The primitives, rather than the original holomorphic maps, have continuous
boundary traces.  A vanishing jump of their derivatives forces the difference
of those traces to be constant.  This is the step which permits reflection
from a modulus limit without assuming a limit for the complex argument.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology Interval ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- A horizontal derivative of a holomorphic function is its complex
derivative, regarded as a real derivative. -/
theorem hasDerivAt_horizontal {F : ℂ → ℂ} {f : ℂ} {x y : ℝ}
    (hF : HasDerivAt F f ((x : ℂ) + y * I)) :
    HasDerivAt (fun t : ℝ => F (t + y * I)) f x := by
  have h := hF.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (y * I))
  simpa only [mul_one, Function.comp_def, id_eq] using h.comp_ofReal

/-- The mean-value bound for the difference of two horizontal traces
passes to the boundary.  Neither derivative is required to have a boundary
value. -/
theorem boundary_trace_norm_le {F G f g : ℂ → ℂ} {a b h C : ℝ}
    (hh : 0 < h) (hF : Continuous F) (hG : Continuous G)
    (hFd : ∀ x ∈ [[a, b]], ∀ y ∈ Ioo 0 h,
      HasDerivAt F (f (x + y * I)) (x + y * I))
    (hGd : ∀ x ∈ [[a, b]], ∀ y ∈ Ioo 0 h,
      HasDerivAt G (g (x - y * I)) (x - y * I))
    (hbound : ∀ x ∈ [[a, b]], ∀ y ∈ Ioo 0 h,
      ‖f (x + y * I) - g (x - y * I)‖ ≤ C) :
    ‖(F (b : ℂ) - G (b : ℂ)) - (F (a : ℂ) - G (a : ℂ))‖ ≤ C * ‖b - a‖ := by
  have hle : ∀ y ∈ Ioo 0 h,
      ‖(F (b + y * I) - G (b - y * I)) -
        (F (a + y * I) - G (a - y * I))‖ ≤ C * ‖b - a‖ := by
    intro y hy
    let H : ℝ → ℂ := fun x => F (x + y * I) - G (x - y * I)
    have hd : ∀ x ∈ [[a, b]],
        HasDerivWithinAt H (f (x + y * I) - g (x - y * I)) [[a, b]] x := by
      intro x hx
      have hu := hasDerivAt_horizontal (hFd x hx y hy)
      have hl : HasDerivAt (fun t : ℝ => G (t - y * I)) (g (x - y * I)) x := by
        have h := hasDerivAt_horizontal (y := -y) (by
          simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using hGd x hx y hy)
        simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using h
      exact (hu.sub hl).hasDerivWithinAt
    exact (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun x hx => hbound x hx y hy) left_mem_uIcc right_mem_uIcc
  have ht : Tendsto (fun y : ℝ =>
      ‖(F (b + y * I) - G (b - y * I)) -
        (F (a + y * I) - G (a - y * I))‖) (𝓝[>] 0)
      (𝓝 ‖(F (b : ℂ) - G (b : ℂ)) - (F (a : ℂ) - G (a : ℂ))‖) := by
    have hc : Continuous (fun y : ℝ =>
        ‖(F (b + y * I) - G (b - y * I)) -
          (F (a + y * I) - G (a - y * I))‖) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT hh] with y hy using hle y hy

/-- A full one-sided limit gives the locally uniform convergence of the
parallel horizontal traces. This is stronger than pointwise convergence
along individual vertical lines. -/
theorem upper_limit_tendstoUniformlyOnFilter {q : ℂ → ℂ} {x : ℝ}
    (hq : Tendsto q (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0)) :
    TendstoUniformlyOnFilter (fun y t : ℝ => q (t + y * I)) (fun _ => 0)
      (𝓝[>] 0) (𝓝 x) := by
  have ht : Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ) + p.1 * I)
      ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h₁ : Tendsto (fun p : ℝ × ℝ => (p.1 : ℂ))
          ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (0 : ℂ)) :=
        continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_fst.mono_right nhdsWithin_le_nhds)
      have h₂ : Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ))
          ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (x : ℂ)) :=
        continuous_ofReal.continuousAt.tendsto.comp tendsto_snd
      simpa using h₂.add (h₁.mul_const I)
    · have hy : ∀ᶠ p : ℝ × ℝ in (𝓝[>] 0) ×ˢ 𝓝 x, 0 < p.1 :=
        tendsto_fst.eventually eventually_mem_nhdsWithin
      filter_upwards [hy] with p hp
      simpa using hp
  apply Metric.tendstoUniformlyOnFilter_iff.mpr
  intro ε hε
  simpa only [Function.comp_def, dist_zero_left, dist_zero_right] using
    Metric.tendsto_nhds.mp (hq.comp ht) ε hε

/-- If the upper and lower derivatives have vanishing jump, the
difference of the continuous primitive traces has zero real derivative. -/
theorem hasDerivAt_boundary_trace_sub {F G f g : ℂ → ℂ} {a b h x : ℝ}
    (hh : 0 < h) (hx : x ∈ Ioo a b) (hF : Continuous F) (hG : Continuous G)
    (hFd : ∀ t ∈ Ioo a b, ∀ y ∈ Ioo 0 h,
      HasDerivAt F (f (t + y * I)) (t + y * I))
    (hGd : ∀ t ∈ Ioo a b, ∀ y ∈ Ioo 0 h,
      HasDerivAt G (g (t - y * I)) (t - y * I))
    (hjump : ∀ t ∈ Ioo a b,
      Tendsto (fun z => f z - g (conj z))
        (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 0)) :
    HasDerivAt (fun t : ℝ => F t - G t) 0 x := by
  let H : ℝ → ℝ → ℂ := fun y t => F (t + y * I) - G (t - y * I)
  let H' : ℝ → ℝ → ℂ := fun y t => f (t + y * I) - g (t - y * I)
  have hd : ∀ᶠ y in 𝓝[>] 0, ∀ t ∈ Ioo a b, HasDerivAt (H y) (H' y t) t := by
    filter_upwards [Ioo_mem_nhdsGT hh] with y hy t ht
    have hu := hasDerivAt_horizontal (hFd t ht y hy)
    have hl : HasDerivAt (fun s : ℝ => G (s - y * I)) (g (t - y * I)) t := by
      have hi := hasDerivAt_horizontal (y := -y) (by
        simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using hGd t ht y hy)
      simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using hi
    exact hu.sub hl
  have hdu : TendstoLocallyUniformlyOn H' (fun _ => 0) (𝓝[>] 0) (Ioo a b) := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro t ht
    rw [isOpen_Ioo.nhdsWithin_eq ht]
    simpa only [H', map_add, map_mul, conj_ofReal, conj_I, mul_neg,
      ← sub_eq_add_neg] using upper_limit_tendstoUniformlyOnFilter (hjump t ht)
  have hlim : ∀ t ∈ Ioo a b, Tendsto (fun y => H y t) (𝓝[>] 0)
      (𝓝 (F (t : ℂ) - G (t : ℂ))) := by
    intro t _
    have hc : Continuous (fun y : ℝ => H y t) := by dsimp [H]; fun_prop
    simpa [H] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hdu hd hlim hx

/-- The two primitive traces differ by one constant on the whole
diameter interval. -/
theorem boundary_trace_sub_eq {F G f g : ℂ → ℂ} {a b h x t : ℝ}
    (hh : 0 < h) (hx : x ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hF : Continuous F) (hG : Continuous G)
    (hFd : ∀ s ∈ Ioo a b, ∀ y ∈ Ioo 0 h,
      HasDerivAt F (f (s + y * I)) (s + y * I))
    (hGd : ∀ s ∈ Ioo a b, ∀ y ∈ Ioo 0 h,
      HasDerivAt G (g (s - y * I)) (s - y * I))
    (hjump : ∀ s ∈ Ioo a b,
      Tendsto (fun z => f z - g (conj z))
        (𝓝[{z : ℂ | 0 < z.im}] (s : ℂ)) (𝓝 0)) :
    F (x : ℂ) - G (x : ℂ) = F (t : ℂ) - G (t : ℂ) := by
  have hd (s : ℝ) (hs : s ∈ Ioo a b) :=
    hasDerivAt_boundary_trace_sub hh hs hF hG hFd hGd hjump
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) hx ht

end Wikipedia.HopfProblem.RiemannBoundary
