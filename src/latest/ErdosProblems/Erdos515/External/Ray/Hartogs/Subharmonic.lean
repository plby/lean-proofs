module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import ErdosProblems.Erdos515.External.Ray.Misc.Defs
public import ErdosProblems.Erdos515.External.Ray.Misc.Measure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Analytic.Holomorphic
import ErdosProblems.Erdos515.External.Ray.Hartogs.Duals
import ErdosProblems.Erdos515.External.Ray.Hartogs.FubiniBall
import ErdosProblems.Erdos515.External.Ray.Hartogs.MaxLog
import ErdosProblems.Erdos515.External.Ray.Misc.Complex
import ErdosProblems.Erdos515.External.Ray.Misc.Max
import ErdosProblems.Erdos515.External.Ray.Misc.Multilinear

/-!
## Subharmonic and harmonic functions and Hartogs' lemma

We define subharmonic and harmonic functions from `C → E` for any separable normed space `E`:

1. `f : ℂ → E` is harmonic if its circle averages are equal to the center value
2. `f : ℂ → ℝ` is subharmonic if its circle averages are greater than or equal to the center value

For harmonic functions on `s`, we require (1) for any circle bounding a ball contained in `s`,
because this is easy to prove in the cases we need (harmonic functions derived from analytic
functions).  For subharmonic functions, we require (2) to hold only for small balls near each point
in the interior of `s`.

The usual definition of subharmonic allows `f z = -∞`, but we found it quite difficult to work
over the extended reals when developing the theory.  Thus, we instead restrict to `→ ℝ`.  Our
main application of Hartogs' theorem uses subharmonicity of `log ‖f z‖` which would hit `-∞`
at any zero of `f`; we work around this by replace `log ‖f z‖` with `max b (log ‖f z‖)` for
suitable `b : ℝ`.

Possibly we could avoid this by working over `ℝ≥0∞` using superharmonic functions instead of
harmonic functions, but (1) I'm not sure that's desired and (2) I didn't think of it until late
in the Hartogs' theorem proof.  We do define `SuperharmonicOn f s` for `f : ℂ → ℝ≥0∞` late in
the file.

After deriving the basic theory, we prove Hartogs' lemma as `SubharmonicOn.hartogs`:
subharmonic functions that are bounded above and limsup bounded pointwise are limsup bounded
uniformly.  This is the key piece of measure theory needed for Hartogs' theorem.
-/

open Complex (exp I log)
open Filter (Tendsto liminf limsup atTop)
open Function (uncurry)
open MeasureTheory
open Metric (ball closedBall sphere)
open Set (Ioc Icc univ)
open scoped Real NNReal ENNReal Topology ComplexConjugate
noncomputable section

variable {S : Type} [_root_.RCLike S] [SMulCommClass ℝ S S]
variable {T : Type} [_root_.RCLike T] [SMulCommClass ℝ T T]
variable {E : Type} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- `f : ℂ → E` is harmonic if it is continuous and equal to means on circles.
    We require the mean property for large circles because it is easy to prove
    for the cases we need, and will be needed for the large submean theorem
    for subharmonic functions. -/
public structure HarmonicOn (f : ℂ → E) (s : Set ℂ) : Prop where
  /-- `f` is continuous throughout `s` -/
  cont : ContinuousOn f s
  /-- If a circle bounds a disk contained in `s`, the circle mean is equal to the center value. -/
  mean : ∀ (c : ℂ) (r : ℝ), r > 0 → closedBall c r ⊆ s → f c = ⨍ t in itau, f (circleMap c r t)

/-- `f : ℂ → ℝ` is subharmonic if it is upper semicontinuous and is below means on small disks.
    We require the submean property only locally in the definition (for sufficiently small circles
    in the interior of `s`), but prove the global version below.

    Out of laziness, we assume continuity as well for now.  Ideally we'd allow `-∞` as values, but
    using `ereal` instead of `ℝ` adds many annoying technicalities. -/
public structure SubharmonicOn (f : ℂ → ℝ) (s : Set ℂ) : Prop where
  /-- The usual definition requires upper semicontinuity; we use continuity out of laziness. -/
  cont : ContinuousOn f s
  /-- Near each `c ∈ interior s`, for sufficiently small radii, `f c ≤` the circle mean of `f` -/
  submean' : ∀ c, c ∈ interior s → ∃ r, 0 < r ∧
    ∀ s, 0 < s → s < r → f c ≤ ⨍ t in itau, f (circleMap c s t)

/-- Subharmonic functions are subharmonic on smaller sets -/
public theorem SubharmonicOn.mono {f : ℂ → ℝ} {s t : Set ℂ} (fs : SubharmonicOn f s) (ts : t ⊆ s) :
    SubharmonicOn f t :=
  { cont := fs.cont.mono ts
    submean' := fun c cs ↦ fs.submean' c (interior_mono ts cs) }

/-- Convex functions of harmonic functions are subharmonic -/
theorem HarmonicOn.convex {f : ℂ → E} {s : Set ℂ} {g : E → ℝ} (fh : HarmonicOn f s)
    (c : Continuous g) (gc : ConvexOn ℝ Set.univ g) : SubharmonicOn (fun z ↦ g (f z)) s :=
  { cont := c.comp_continuousOn fh.cont
    submean' := by
      intro z zs
      rcases Metric.isOpen_iff.mp isOpen_interior z zs with ⟨r, rp, rh⟩
      exists r, rp; intro t tp tr
      have cs : closedBall z t ⊆ s :=
        _root_.trans (Metric.closedBall_subset_ball tr) (_root_.trans rh interior_subset)
      simp only [fh.mean z t tp cs]
      have n := NiceVolume.itau
      apply ConvexOn.map_set_average_le gc c.continuousOn isClosed_univ n.ne_zero n.ne_top
      simp only [Set.mem_univ, Filter.eventually_true]
      exact (fh.cont.mono cs).integrableOn_sphere tp
      exact ((c.comp_continuousOn fh.cont).mono cs).integrableOn_sphere tp }

/-- Harmonic functions are subharmonic -/
public theorem HarmonicOn.subharmonicOn {f : ℂ → ℝ} {s : Set ℂ} (h : HarmonicOn f s) :
    SubharmonicOn (fun z ↦ f z) s := by
  have e : (fun z ↦ f z) = fun z ↦ (fun x ↦ x) (f z) := rfl
  rw [e]; exact h.convex continuous_id (convexOn_id convex_univ)

/-- Norms of harmonic functions are subharmonic -/
public theorem HarmonicOn.norm {f : ℂ → E} {s : Set ℂ} (h : HarmonicOn f s) :
    SubharmonicOn (fun z ↦ ‖f z‖) s :=
  h.convex continuous_norm (convexOn_norm convex_univ)

/-- `SubharmonicOn` depends only on values in `s` (`→` version) -/
public theorem SubharmonicOn.congr {f g : ℂ → ℝ} {s : Set ℂ} (fs : SubharmonicOn f s)
    (h : Set.EqOn g f s) : SubharmonicOn g s :=
  { cont := fs.cont.congr h
    submean' := by
      intro c cs
      rcases Metric.isOpen_iff.mp isOpen_interior c cs with ⟨r0, r0p, r0s⟩
      rcases fs.submean' c cs with ⟨r1, r1p, sm⟩
      have r01p : min r0 r1 > 0 := by bound
      exists min r0 r1, r01p
      intro t tp tr
      specialize sm t tp (lt_of_lt_of_le tr (by bound))
      have hs : (fun u ↦ f (circleMap c t u)) =ᵐ[volume.restrict itau]
          fun u ↦ g (circleMap c t u) := by
        rw [Filter.EventuallyEq]; rw [ae_restrict_iff' measurableSet_itau]
        apply Filter.Eventually.of_forall
        intro u _; apply h.symm
        apply _root_.trans r0s interior_subset
        simp only [Metric.mem_ball, Complex.dist_eq, circleMap_sub_center, norm_circleMap_zero,
          abs_of_pos tp]
        exact lt_of_lt_of_le tr (by bound)
      rw [average_eq] at sm ⊢
      rwa [← h.symm (interior_subset cs), ← integral_congr_ae hs] }

/-- `SubharmonicOn` depends only on values in `s` (`↔` version) -/
public theorem subharmonicOn_congr {f g : ℂ → ℝ} {s : Set ℂ} (h : Set.EqOn f g s) :
    SubharmonicOn f s ↔ SubharmonicOn g s :=
  ⟨fun fs ↦ fs.congr h.symm, fun gs ↦ gs.congr h⟩

/-- Constants are harmonic -/
public theorem HarmonicOn.const (a : E) {s : Set ℂ} : HarmonicOn (fun _ ↦ a) s :=
  { cont := continuousOn_const
    mean := by
      intro c r _ _
      rw [average_eq]
      simp [← smul_assoc, smul_eq_mul]
      field_simp [NiceVolume.itau.real_pos.ne']
      simp }

/-- Differences are harmonic -/
public theorem HarmonicOn.sub {f g : ℂ → F} {s : Set ℂ} (fh : HarmonicOn f s)
    (gh : HarmonicOn g s) : HarmonicOn (f - g) s :=
  { cont := ContinuousOn.sub fh.cont gh.cont
    mean := by
      intro c r rp cs; simp [fh.mean c r rp cs, gh.mean c r rp cs]
      rw [Average.sub ((fh.cont.mono cs).integrableOn_sphere rp)
        ((gh.cont.mono cs).integrableOn_sphere rp)] }

/-- Subharmonic functions add (note that they don't subtract) -/
public theorem SubharmonicOn.add {f g : ℂ → ℝ} {s : Set ℂ} (fs : SubharmonicOn f s)
    (gs : SubharmonicOn g s) : SubharmonicOn (fun z ↦ f z + g z) s :=
  { cont := fs.cont.add gs.cont
    submean' := by
      intro c cs
      rcases fs.submean' c cs with ⟨r0, r0p, r0m⟩
      rcases gs.submean' c cs with ⟨r1, r1p, r1m⟩
      rcases Metric.isOpen_iff.mp isOpen_interior c cs with ⟨r2, r2p, r2s⟩
      set r := min r0 (min r1 r2)
      have rr1 : r ≤ r1 := le_trans (min_le_right _ _) (by bound)
      have rr2 : r ≤ r2 := le_trans (min_le_right _ _) (by bound)
      use r; use by bound
      intro u up ur
      have us : closedBall c u ⊆ s :=
        _root_.trans (Metric.closedBall_subset_ball (lt_of_lt_of_le ur (by bound)))
          (_root_.trans r2s interior_subset)
      rw [Average.add ((fs.cont.mono us).integrableOn_sphere up)
          ((gs.cont.mono us).integrableOn_sphere up)]
      have m0 := r0m u up (lt_of_lt_of_le ur (by bound))
      have m1 := r1m u up (lt_of_lt_of_le ur (by bound))
      exact add_le_add m0 m1 }

/-- Negations are harmonic -/
public theorem HarmonicOn.neg {f : ℂ → E} {s : Set ℂ} (fh : HarmonicOn f s) :
    HarmonicOn (-f) s := by
  have nh := HarmonicOn.sub (HarmonicOn.const (0 : E)) fh
  have e : (fun _ : ℂ ↦ (0 : E)) - f = -f := by ext; simp
  rwa [← e]

/-- Additions are harmonic -/
public theorem HarmonicOn.add {f g : ℂ → E} {s : Set ℂ} (fh : HarmonicOn f s)
    (gh : HarmonicOn g s) : HarmonicOn (f + g) s := by
  have e : f + g = f - -g := by ext; simp
  rw [e]; exact fh.sub gh.neg

/-- Scalar multiples are harmonic -/
public theorem HarmonicOn.const_mul {f : ℂ → S} {s : Set ℂ} (fh : HarmonicOn f s) (a : S) :
    HarmonicOn (fun z ↦ a * f z) s :=
  { cont := ContinuousOn.mul continuousOn_const fh.cont
    mean := by
      intro c r rp cs; rw [average_eq]
      simp_rw [← smul_eq_mul, integral_smul, smul_comm _ a, ← average_eq, ← fh.mean c r rp cs] }

/-- Nonnegative scalar multiples are subharmonic -/
public theorem SubharmonicOn.const_mul {f : ℂ → ℝ} {s : Set ℂ} {a : ℝ} (fs : SubharmonicOn f s)
    (ap : 0 ≤ a) : SubharmonicOn (fun z ↦ a * f z) s :=
  { cont := ContinuousOn.mul continuousOn_const fs.cont
    submean' := by
      intro c cs; rcases fs.submean' c cs with ⟨r, rp, rm⟩; use r, rp; intro s sp sr
      specialize rm s sp sr
      simp only [average_eq, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul] at rm ⊢
      calc a * f c
        _ ≤ a * ((volume.real itau)⁻¹ * ∫ t in itau, f (circleMap c s t)) := by bound
        _ = (volume.real itau)⁻¹ * (a * ∫ t in itau, f (circleMap c s t)) := by ring
        _ = (volume.real itau)⁻¹ * ∫ t in itau, a * f (circleMap c s t) := by
          rw [integral_const_mul] }

/-- Analytic functions equal circle means -/
theorem AnalyticOnNhd.circle_mean_eq [CompleteSpace H] {f : ℂ → H} {c : ℂ} {r : ℝ}
    (fa : AnalyticOnNhd ℂ f (closedBall c r)) (rp : r > 0) :
    ⨍ t in itau, f (circleMap c r t) = f c := by
  have h := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty (Metric.mem_ball_self rp) fa.continuousOn ?_
  · simp_rw [circleIntegral, deriv_circleMap, circleMap_sub_center, smul_smul, mul_comm _ I] at h
    field_simp [circleMap_ne_center rp.ne'] at h
    simp only [intervalIntegral.integral_smul] at h
    rw [mul_assoc, ← smul_smul, IsUnit.smul_left_cancel (Ne.isUnit Complex.I_ne_zero)] at h
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le] at h
    rw [average_eq, itau, h]
    simp only [MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, Real.volume_real_Ioc,
      sub_zero]
    rw [max_eq_left Real.two_pi_pos.le]
    rw [← smul_assoc, Complex.real_smul]
    field_simp [Real.pi_ne_zero]
    simp
  · intro z zs; rw [Set.sdiff_empty] at zs
    exact (fa z (Metric.ball_subset_closedBall zs)).differentiableAt

/-- Analytic functions are harmonic -/
theorem AnalyticOnNhd.harmonicOn [CompleteSpace H] {f : ℂ → H} {s : Set ℂ} (fa : AnalyticOnNhd ℂ f s) :
    HarmonicOn f s :=
  { cont := fa.continuousOn
    mean := by intro c r rp cs; rw [(fa.mono cs).circle_mean_eq rp] }

/-- Harmonic functions compose with linear maps -/
theorem HarmonicOn.linear [CompleteSpace F] {f : ℂ → E} {s : Set ℂ} (fh : HarmonicOn f s)
    (g : E →L[ℝ] F) : HarmonicOn (fun z ↦ g (f z)) s :=
  { cont := g.continuous.comp_continuousOn fh.cont
    mean := by
      intro c r rp cs
      rw [average_linear_comm ((fh.cont.mono cs).integrableOn_sphere rp)]
      rw [fh.mean c r rp cs] }

/-- Real parts of harmonic functions are harmonic -/
theorem HarmonicOn.re {f : ℂ → ℂ} {s : Set ℂ} (fh : HarmonicOn f s) :
    HarmonicOn (fun z ↦ (f z).re) s := by simp only [← Complex.reCLM_apply]; exact fh.linear _

/-- Complex conjugates of harmonic functions are harmonic (since `conj` is linear) -/
theorem HarmonicOn.conj {f : ℂ → ℂ} {s : Set ℂ} (fh : HarmonicOn f s) :
    HarmonicOn (fun z ↦ conj (f z)) s := by simp only [← conjCLM_apply]; exact fh.linear _

/-- Real parts of analytic functions are subharmonic -/
theorem AnalyticOnNhd.reSubharmonicOn {f : ℂ → ℂ} {s : Set ℂ} (fa : AnalyticOnNhd ℂ f s) :
    SubharmonicOn (fun z ↦ (f z).re) s :=
  fa.harmonicOn.re.subharmonicOn

/-- The submean property holds at minima -/
theorem Minimum.submean {f : ℂ → ℝ} {s : Set ℂ} {c : ℂ} (fc : ContinuousOn f s)
    (cs : c ∈ interior s) (fm : ∀ z, f c ≤ f z) :
    ∃ (r : _), 0 < r ∧ ∀ s, 0 < s → s < r → f c ≤ ⨍ t in itau, f (circleMap c s t) := by
  rcases Metric.isOpen_iff.mp isOpen_interior c cs with ⟨r, rp, rs⟩
  use r, rp; intro t tp tr; rw [average_eq]
  have fg : ∀ (u) (_ : u ∈ itau), f c ≤ f (circleMap c t u) := fun _ _ ↦ fm _
  have ss : closedBall c t ⊆ s :=
    _root_.trans (Metric.closedBall_subset_ball tr) (_root_.trans rs interior_subset)
  have n := NiceVolume.itau
  have m := setIntegral_ge_of_const_le n.measurable n.ne_top fg
    ((fc.mono ss).integrableOn_sphere tp)
  simpa only [MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, smul_eq_mul,
    le_inv_mul_iff₀ n.real_pos, mul_comm, ge_iff_le] using m

/-- `max b (log ‖f z‖)` is subharmonic for analytic `f` (`ℂ` case) -/
theorem AnalyticOnNhd.maxLogAbsSubharmonicOn {f : ℂ → ℂ} {s : Set ℂ} (fa : AnalyticOnNhd ℂ f s)
    (b : ℝ) : SubharmonicOn (fun z ↦ maxLog b ‖f z‖) s :=
  { cont := fa.continuousOn.maxLog_norm b
    submean' := by
      intro c cs
      by_cases bf : b.exp ≥ ‖f c‖
      · apply Minimum.submean (fa.continuousOn.maxLog_norm b) cs
        intro z; simp only [maxLog_eq_b bf, le_maxLog]
      simp only [not_le] at bf
      have anz : ‖f c‖ ≠ 0 := (lt_trans (Real.exp_pos _) bf).ne'
      have fac : ContinuousAt f c :=
        fa.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp cs)
      -- We define g carefully to avoid the logarithmic branch cut
      generalize hh : (fun z ↦ Complex.log (‖f c‖ / f c * f z)) = h
      generalize hg : (fun z ↦ (h z).re) = g
      have ha : AnalyticAt ℂ h c := by
        rw [← hh]
        apply (analyticAt_const.mul (fa c (interior_subset cs))).clog
        simp only [Pi.mul_apply]
        field_simp [norm_ne_zero_iff.mp anz]
        exact Complex.ofReal_mem_slitPlane.mpr
          (norm_pos_iff.mpr (ne_zero_of_norm_ne_zero anz))
      rcases Metric.isOpen_iff.mp (isOpen_analyticAt ℂ h) c ha with ⟨r0, r0p, r0a⟩
      rcases Metric.continuousAt_iff.mp fac (‖f c‖ - b.exp) (sub_pos.mpr bf) with
        ⟨r1, r1p, r1h⟩
      set r := min r0 r1
      have fg : Set.EqOn (fun z ↦ maxLog b ‖f z‖) g (ball c r) := by
        intro z zs
        simp only [Metric.mem_ball, Complex.dist_eq] at zs r1h
        specialize r1h (lt_of_lt_of_le zs (by bound))
        have zp : ‖f z‖ > b.exp := by
          calc ‖f z‖
            _ = ‖f c + (f z - f c)‖ := by ring_nf
            _ ≥ ‖f c‖ - ‖f z - f c‖ := by bound
            _ > ‖f c‖ - (‖f c‖ - b.exp) := by bound
            _ = b.exp := by abel
        simp only [maxLog_eq_log zp.le]
        rw [←hg, ←hh]
        simp only [Complex.log_re, norm_mul, norm_div, Complex.norm_real,
          norm_norm, div_self anz, one_mul]
      have gs : SubharmonicOn g (ball c r) := by
        rw [← hg]; apply AnalyticOnNhd.reSubharmonicOn; intro z zs
        exact r0a (Metric.ball_subset_ball (by bound) zs)
      rw [subharmonicOn_congr fg.symm] at gs
      refine gs.submean' c ?_
      rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self (by bound) }

/-- If a subharmonic function is maximal at the center of a ball, it is constant on the ball. -/
theorem SubharmonicOn.maximum_principle_ball {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (fs : SubharmonicOn f (closedBall c r)) (rp : r > 0) :
    IsMaxOn f (closedBall c r) c → ∀ z, z ∈ closedBall c r → f c = f z := by
  intro cm g gs
  by_cases gc : g = c; · rw [gc]
  generalize hu : ‖g - c‖ = u
  have u0 : u > 0 := by
    simp only [← hu, gt_iff_lt, norm_pos_iff, Ne]
    contrapose gc; simp only [sub_eq_zero] at gc ⊢; exact gc
  have ur : u ≤ r := by
    simp only [Complex.dist_eq, Metric.mem_closedBall] at gs; simp only [←hu, gs]
  generalize hy : (g - c) / u = y
  have y1 : ‖y‖ = 1 := by
    simp only [← hy, ← hu, Complex.norm_div, Complex.norm_real, norm_norm, ne_eq,
      norm_sub_eq_zero_iff.not.mpr gc, not_false_eq_true, div_self]
  generalize hs : (fun t : ℝ ↦ f (c + t * y)) ⁻¹' {f c} = s
  have s0 : (0 : ℝ) ∈ s := by
    simp only [← hs, Set.mem_preimage, Complex.ofReal_zero, MulZeroClass.zero_mul, add_zero,
      Set.mem_singleton]
  have us : u ∈ s := by
    refine IsClosed.mem_of_ge_of_forall_exists_gt ?_ s0 u0.le ?_
    · rw [← hs]; rw [Set.inter_comm]
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_ isClosed_Icc isClosed_singleton
      apply fs.cont.comp (Continuous.continuousOn _) _
      · exact continuous_const.add (Continuous.mul Complex.continuous_ofReal continuous_const)
      · intro t ts
        simp only [Set.mem_Icc] at ts
        simp only [y1, abs_of_nonneg ts.1, _root_.trans ts.2 ur, Metric.mem_closedBall,
          dist_self_add_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          mul_one]
    · intro t ts
      simp only [← hs, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_Ico] at ts
      generalize hz : c + t * y = z
      rcases ts with ⟨fz, tp, tu⟩
      have tz : ‖z - c‖ = t := by
        simp only [y1, abs_of_nonneg tp, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, mul_one, ← hz]
      have zs : z ∈ ball c r := by
        simp only [y1, abs_of_nonneg tp, Metric.mem_ball, dist_self_add_left, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, mul_one, ← hz]
        exact lt_of_lt_of_le tu ur
      rw [← interior_closedBall _ rp.ne'] at zs
      rcases fs.submean' z zs with ⟨e, ep, lo⟩
      generalize he' : min (e / 2) (u - t) = e'
      have e'p : e' > 0 := by rw [←he']; exact lt_min (half_pos ep) (by linarith)
      have teu : t + e' ≤ u := by
        rw [← he']; trans t + (u - t)
        · exact add_le_add_right (min_le_right _ _) _
        · simp only [add_sub_cancel, le_refl]
      have e's : e' < e := by rw [← he']; exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self ep)
      specialize lo e' e'p e's
      rw [← hz, fz] at lo
      have ss : closedBall z e' ⊆ closedBall c r := by
        apply Metric.closedBall_subset_closedBall'; rw [Complex.dist_eq, tz]; linarith
      have hi : ∀ x, x ∈ itau → f (circleMap z e' x) ≤ f c := by
        intro x _; apply isMaxOn_iff.mp cm; apply ss
        simp only [Complex.dist_eq, Metric.mem_closedBall, circleMap_sub_center,
          norm_circleMap_zero, abs_of_pos e'p, le_refl]
      have fcc : ContinuousOn (fun a ↦ f (circleMap z e' a)) itau := by
        apply (fs.cont.mono ss).comp (continuous_circleMap _ _).continuousOn; intro a _
        simp only [Complex.dist_eq, abs_of_pos e'p, Metric.mem_closedBall, circleMap_sub_center,
          norm_circleMap_zero, le_refl]
      rw [hz] at lo
      have fw := mean_squeeze NiceVolume.itau LocalVolume.itau fcc
        ((fs.cont.mono ss).integrableOn_sphere e'p) lo hi
      have eys : z + e' * y ∈ sphere z e' := by
        simp only [Real.norm_eq_abs, abs_of_pos e'p, y1, mem_sphere_iff_norm, add_sub_cancel_left,
          norm_mul, Complex.norm_real, mul_one]
      rcases circleMap_Ioc eys with ⟨a, as, aey⟩
      specialize fw a as; simp only [← aey] at fw
      use t + e'
      simp only [Set.mem_inter_iff, Set.mem_Ioc, lt_add_iff_pos_right]
      refine ⟨?_, e'p, teu⟩
      simp only [← hs, right_distrib, Set.mem_preimage, Complex.ofReal_add, Set.mem_singleton_iff]
      rw [← add_assoc, hz]; exact fw
  simp only [← hs, ← hy, Set.mem_preimage, Set.mem_singleton_iff] at us
  have unz : (u : ℂ) ≠ 0 := by
    simp only [u0.ne', Ne, Complex.ofReal_eq_zero, not_false_iff]
  field_simp [unz] at us
  simpa using us.symm

/-- A subharmonic function achieves its maximum on the boundary -/
theorem SubharmonicOn.maximum_principle {f : ℂ → ℝ} {s : Set ℂ} (fs : SubharmonicOn f s)
    (sc : IsCompact s) (sn : s.Nonempty) : ∃ w, w ∈ frontier s ∧ IsMaxOn f s w := by
  rcases sc.exists_isMaxOn sn fs.cont with ⟨x, xs, xm⟩
  rcases exists_mem_frontier_infDist_compl_eq_dist xs sc.ne_univ with ⟨w, wb, h⟩
  exists w, wb
  generalize hr : ‖w - x‖ = r
  by_cases wx : w = x; · rwa [wx]
  have rp : r > 0 := by
    simp only [← hr, norm_pos_iff, Ne]; exact sub_ne_zero.mpr wx
  rw [dist_comm, Complex.dist_eq, hr] at h
  have rs : closedBall x r ⊆ s := by
    rw [← closure_ball x rp.ne', ← sc.isClosed.closure_eq]; apply closure_mono
    rw [← h]; apply Metric.ball_infDist_compl_subset
  have rm : IsMaxOn f (closedBall x r) x := by intro y ys; exact xm (rs ys)
  have wx : f x = f w := by
    apply SubharmonicOn.maximum_principle_ball (fs.mono rs) rp rm
    simp only [Complex.dist_eq, Metric.mem_closedBall, hr, le_refl]
  intro y ys; rw [← wx]; exact xm ys

/-- A harmonic function achieves its maximum norm on the boundary -/
theorem HarmonicOn.maximum_principle {f : ℂ → E} {s : Set ℂ} (fh : HarmonicOn f s)
    (sc : IsCompact s) (sn : s.Nonempty) : ∃ w, w ∈ frontier s ∧ ∀ z, z ∈ s → ‖f z‖ ≤ ‖f w‖ := by
  rcases fh.norm.maximum_principle sc sn with ⟨w, wf, wh⟩; exists w, wf

omit [CompleteSpace E] in
/-- Uniform limits of harmonic functions are harmonic -/
theorem uniform_harmonic_lim [SecondCountableTopology E] {f : ℕ → ℂ → E} {g : ℂ → E} {s : Set ℂ}
    (h : ∀ n, HarmonicOn (f n) s) (u : TendstoUniformlyOn f g atTop s) : HarmonicOn g s :=
  { cont := u.continuousOn (Filter.Eventually.of_forall fun n ↦ (h n).cont).frequently
    mean := by
      intro c r rp cs
      have m := fun n ↦ (h n).mean c r rp cs
      simp_rw [average_eq] at m ⊢
      have se : itau =ᵐ[volume] Icc 0 (2 * π) := Ioc_ae_eq_Icc
      simp only [MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        setIntegral_congr_set se] at m ⊢
      generalize hv : volume.real itau = v; simp_rw [hv] at m ⊢; clear hv
      have cc : Icc 0 (2 * π) ⊆ circleMap c r ⁻¹' s := by
        rw [Set.subset_def]; intro t _; simp only [Set.mem_preimage]; apply cs
        simp only [Complex.dist_eq, abs_of_pos rp, Metric.mem_closedBall, circleMap_sub_center,
          norm_circleMap_zero, le_refl]
      have fu := (u.comp (circleMap c r)).mono cc
      have fc : ∀ n, ContinuousOn (fun t ↦ f n (circleMap c r t)) (Icc 0 (2 * π)) := by
        intro n; apply Continuous.continuousOn
        apply ((h n).cont.mono cs).comp_continuous (continuous_circleMap _ _); intro t
        simp only [Complex.dist_eq, abs_of_pos rp, Metric.mem_closedBall, circleMap_sub_center,
          norm_circleMap_zero, le_refl]
      have ti' := fu.integral_tendsto fc isCompact_Icc
      have ti := ti'.const_smul v⁻¹; clear ti'
      have ci := u.tendsto_at (cs (Metric.mem_closedBall_self (by linarith)))
      simp only [← m, Function.comp_apply] at ti ⊢
      exact tendsto_nhds_unique ci ti }

section HarmonicExtension

/-!
## Harmonic extensions

We show that continuous functions on circles extend to harmonic functions on the interior disk,
by showing that all trigonometric polynomials extend and taking limits.

This is needed below for the global submean property for subharmonic functions.
-/

variable {c : ℂ} {r : ℝ}

theorem rri (rp : 0 < r) (z : ℂ) : c + r * ((↑r)⁻¹ * (z - c)) = z := by
  ring_nf; field_simp [rp.ne']; simp

theorem rir (rp : r > 0) (z : ℂ) : (↑r)⁻¹ * (c + r * z - c) = z := by
  ring_nf; field_simp [rp.ne']

/-- The continuous function `f` on the circle has a Harmonic extension `g` on the disk -/
structure HasExtension (f : C(AddCircle (2*π), S)) (g : ℂ → S) (c : ℂ) (r : ℝ) : Prop where
  gh : HarmonicOn g (closedBall c r)
  b : ∀ t, f t = g (c + r * t.toCircle)

/-- `f` has some harmonic extension to the disk -/
def Extendable (f : C(AddCircle (2*π), S)) (c : ℂ) (r : ℝ) :=
  ∃ g : ℂ → S, HasExtension f g c r

/-- `HasExtension` is linear -/
theorem HasExtension.sub {f0 f1 : C(AddCircle (2*π), ℂ)} {g0 g1 : ℂ → ℂ}
    (e0 : HasExtension f0 g0 c r) (e1 : HasExtension f1 g1 c r) :
    HasExtension (f0 - f1) (g0 - g1) c r :=
  { gh := e0.gh.sub e1.gh
    b := by simp only [e0.b, e1.b, ContinuousMap.coe_sub, Pi.sub_apply, forall_const] }

theorem mem_addCircle_iff_abs {z : ℂ} : ‖z‖ = 1 ↔ ∃ t : AddCircle (2 * π), z = t.toCircle := by
  constructor
  · intro az; rcases (Complex.norm_eq_one_iff z).mp az with ⟨t, h⟩; use t
    simp only [← h, AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp,
      Complex.ofReal_mul, Complex.ofReal_div]
    field_simp [Real.pi_pos.ne']
  · intro h; rcases h with ⟨t, h⟩; simp only [h, Circle.norm_coe]

/-- The extension is bounded by values on the circle -/
theorem Extension.maximum_principle {f : C(Real.Angle, ℂ)} {g : ℂ → ℂ} (e : HasExtension f g c r)
    {b : ℝ} (fb : ∀ z, ‖f z‖ ≤ b) (rp : 0 < r) : ∀ z, z ∈ closedBall c r → ‖g z‖ ≤ b := by
  rcases e.gh.maximum_principle (isCompact_closedBall _ _) (Metric.nonempty_closedBall.mpr rp.le)
    with ⟨w, wf, wh⟩
  intro z zs; specialize wh z zs
  rw [frontier_closedBall _ rp.ne'] at wf; simp at wf
  generalize hw' : (↑r)⁻¹ * (w - c) = w'
  have wf' : ‖w'‖ = 1 := by
    simp only [← hw', Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos rp, wf]
    field_simp [rp.ne']
  rcases mem_addCircle_iff_abs.mp wf' with ⟨t, tw⟩
  have fg := e.b t
  simp only [← tw, rri rp, ← hw'] at fg
  rw [← fg] at wh
  exact le_trans wh (fb _)

@[instance]
theorem Real.Angle.compactSpace : CompactSpace Real.Angle :=
  @AddCircle.compactSpace _ (fact_iff.mpr Real.two_pi_pos)

/-- `Extendable` is closed (limits of extendable functions are extendable) -/
theorem IsClosed.extendable {s : Set C(Real.Angle, ℂ)} (e : ∀ f, f ∈ s → Extendable f c r)
    (rp : r > 0) : ∀ f, f ∈ closure s → Extendable f c r := by
  intro F Fe
  have fu : FrechetUrysohnSpace C(Real.Angle, ℂ) := by
    apply @FirstCountableTopology.frechetUrysohnSpace
  rw [← seqClosure_eq_closure] at Fe
  rcases Fe with ⟨f, fs, fF⟩
  simp only [ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace] at fF
  generalize hg : (fun n ↦ Classical.choose (e _ (fs n))) = g
  have gs : ∀ n, HasExtension (f n) (g n) c r := by
    rw [← hg]; exact fun n ↦ Classical.choose_spec (e _ (fs n))
  have cauchy : UniformCauchySeqOn g atTop (closedBall c r) := by
    rw [Metric.uniformCauchySeqOn_iff]
    simp_rw [Metric.tendstoUniformly_iff, Filter.eventually_atTop] at fF
    intro t tp; rcases fF (t / 4) (by linarith) with ⟨N, H⟩; exists N
    intro a aN b bN z zs
    have eab := (gs a).sub (gs b)
    have fab : ∀ u : Real.Angle, ‖f a u - f b u‖ ≤ t / 2 := by
      intro u
      have ta := H a aN u
      have tb := H b bN u
      rw [← dist_eq_norm]; rw [dist_comm] at ta
      calc dist (f a u) (f b u)
        _ ≤ dist (f a u) (F u) + dist (F u) (f b u) := dist_triangle _ _ _
        _ ≤ t / 4 + t / 4 := by linarith
        _ = t / 2 := by ring_nf
    have m := Extension.maximum_principle eab fab rp z zs
    simp only [Complex.dist_eq, Pi.sub_apply] at m ⊢
    exact lt_of_le_of_lt m (by linarith)
  set G := fun z ↦ Filter.limUnder atTop fun n ↦ g n z
  have gG : TendstoUniformlyOn g G atTop (closedBall c r) := by
    apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto cauchy
    intro z zs; exact (cauchy.cauchySeq zs).tendsto_limUnder
  exists G
  exact
    { gh := uniform_harmonic_lim (fun n ↦ (gs n).gh) gG
      b := by
        intro z
        refine (Filter.Tendsto.limUnder_eq ?_).symm
        simp_rw [← (gs _).b]
        exact fF.tendsto_at z }

theorem toCircle_neg {T : ℝ} (x : AddCircle T) : (-x).toCircle = x.toCircle⁻¹ := by
  induction x using QuotientAddGroup.induction_on
  rw [←AddCircle.coe_neg]
  simp only [AddCircle.toCircle, Function.Periodic.lift_coe, mul_neg, Circle.exp_neg]

theorem toCircle_smul {T : ℝ} (n : ℕ) (x : AddCircle T) : (n • x).toCircle = x.toCircle ^ n := by
  induction' x using QuotientAddGroup.induction_on with z
  rw [←AddCircle.coe_nsmul]; simp only [AddCircle.toCircle, Function.Periodic.lift_coe]
  induction' n with n h
  · simp only [Circle.exp_zero, MulZeroClass.mul_zero, pow_zero, zero_smul]
  · simp only [succ_nsmul, left_distrib, Circle.exp_add, h, pow_succ]

@[simp] lemma Circle.pow_coe (z : Circle) (n : ℕ) : (↑(z ^ n) : ℂ) = z ^ n := rfl

/-- Fourier terms extend -/
theorem fourierExtend' (rp : r > 0) (n : ℤ) : Extendable (fourier n) c r := by
  have mh : ∀ n : ℕ, HarmonicOn (fun z ↦ ((↑r)⁻¹ * (z - c)) ^ n) (closedBall c r) := by
    intro n; apply AnalyticOnNhd.harmonicOn; refine AnalyticOnNhd.mono ?_ (Set.subset_univ _)
    rw [Complex.analyticOnNhd_iff_differentiableOn isOpen_univ]; apply Differentiable.differentiableOn
    apply Differentiable.pow; apply Differentiable.mul (differentiable_const _)
    apply Differentiable.sub differentiable_id (differentiable_const _)
  rcases n.eq_nat_or_neg with ⟨k, (e | e)⟩
  · simp only [e]
    exists fun z : ℂ ↦ ((↑r)⁻¹ * (z - c)) ^ k
    exact
      { gh := mh k
        b := by
          intro t; rw [rir rp]
          apply Eq.trans fourier_apply
          simp only [natCast_zsmul, toCircle_smul]
          rfl }
  · simp only [e]
    exists fun z : ℂ ↦ conj (((↑r)⁻¹ * (z - c)) ^ k)
    exact
      { gh := (mh k).conj
        b := by
          intro t; rw [rir rp]
          apply Eq.trans fourier_apply
          simp only [neg_smul, natCast_zsmul, toCircle_neg, toCircle_smul, Circle.coe_inv,
            Circle.pow_coe, Complex.inv_def, map_pow, Circle.normSq_coe, one_pow, inv_one,
            Complex.ofReal_one, mul_one] }

/-- Fourier sums extend -/
theorem fourierExtend {f : C(Real.Angle, ℂ)} (rp : r > 0)
    (s : f ∈ Submodule.span ℂ (Set.range (@fourier (2 * π)))) : Extendable f c r := by
  apply Submodule.span_induction (p := fun f _ ↦ Extendable f c r) (hx := s)
  · intro g gs
    simp only [Set.mem_range] at gs
    rcases gs with ⟨n, ng⟩
    rw [← ng]
    exact fourierExtend' rp _
  · use fun _ ↦ 0
    exact
      { gh := HarmonicOn.const _
        b := by simp only [ContinuousMap.coe_zero, Pi.zero_apply, forall_const] }
  · intro x y _ _ ⟨x',xh,xb⟩ ⟨y',yh,yb⟩
    use fun z ↦ x' z + y' z
    exact
      { gh := xh.add yh
        b := by
          simp only [xb, yb, ContinuousMap.coe_add, Pi.add_apply, forall_const] }
  · intro a x _ ⟨x', xh, xb⟩
    use fun z ↦ a * x' z
    exact
      { gh := xh.const_mul _
        b := by
          simp only [xb, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, forall_const] }

/-- All continuous functions on the circle extend to harmonic functions on the disk -/
theorem continuousExtend (f : C(Real.Angle, ℂ)) (c : ℂ) (rp : r > 0) : Extendable f c r := by
  set s : Submodule ℂ C(Real.Angle, ℂ) := Submodule.span ℂ (Set.range (@fourier (2 * π))) with hs
  have se : ∀ f, f ∈ s.carrier → Extendable f c r := fun f fs ↦ fourierExtend rp fs
  have ce : ∀ f, f ∈ closure s.carrier → Extendable f c r := IsClosed.extendable se rp
  have e : closure s.carrier = s.topologicalClosure.carrier := rfl
  rw [e] at ce
  apply ce
  have et : s.topologicalClosure = ⊤ := @span_fourier_closure_eq_top _ (fact_iff.mpr Real.two_pi_pos)
  rw [et]
  trivial

end HarmonicExtension

/-- Everything is "harmonic" on singletons -/
theorem HarmonicOn.subsingleton {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {f : ℂ → S} {s : Set ℂ} (ss : s.Subsingleton) : HarmonicOn f s :=
  { cont := ss.continuousOn _
    mean := by
      intro c r rp cs
      have cm : c ∈ s := cs (Metric.mem_closedBall_self (by linarith))
      have rm : c + r ∈ s := cs (by
        simp only [Metric.mem_closedBall, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos rp, le_refl])
      have e : c = c + r := ss cm rm
      simp [rp.ne'] at e }

/-- Continuous functions on the sphere extend to harmonic functions on the ball (`ℂ` case) -/
theorem continuous_to_harmonic_complex {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (fc : ContinuousOn f (sphere c r)) :
    ∃ g : ℂ → ℂ, HarmonicOn g (closedBall c r) ∧ ∀ z, z ∈ sphere c r → f z = g z := by
  by_cases rp : r ≤ 0
  · use f; use HarmonicOn.subsingleton (Metric.subsingleton_closedBall _ rp); intros; rfl
  simp only [not_le] at rp
  generalize hf' : (fun t : AddCircle (2 * π) ↦ f (c + r * t.toCircle)) = f'
  have fc' : Continuous f' := by
    rw [← hf']; apply fc.comp_continuous
    · exact continuous_const.add
        (continuous_const.mul (continuous_subtype_val.comp AddCircle.continuous_toCircle))
    · simp only [mem_sphere_iff_norm, add_sub_cancel_left, Complex.norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Circle.norm_coe, mul_one, abs_eq_self, rp.le, implies_true]
  rcases continuousExtend ⟨f', fc'⟩ c rp with ⟨g, e⟩
  use g, e.gh; intro z zs
  generalize hz' : (↑r)⁻¹ * (z - c) = z'
  have za' : ‖z'‖ = 1 := by
    simp only [mem_sphere_iff_norm] at zs
    simp only [← hz', Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos rp, zs, inv_mul_cancel₀ rp.ne']
  rcases mem_addCircle_iff_abs.mp za' with ⟨t, tz⟩
  have rr : c + r * t.toCircle = z := by rw [← tz, ← hz']; exact rri rp _
  have h := e.b t
  nth_rw 2 [← rr]
  rw [← h]
  simp only [← hf']
  show f z = f (c + ↑r * ↑t.toCircle)
  rw [rr]

/-- Continuous functions on the sphere extend to harmonic functions on the ball (`ℝ` case) -/
theorem continuous_to_harmonic_real {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (fc : ContinuousOn f (sphere c r)) :
    ∃ g : ℂ → ℝ, HarmonicOn g (closedBall c r) ∧ ∀ z, z ∈ sphere c r → f z = g z := by
  generalize hf' : (fun z ↦ (f z : ℂ)) = f'
  have fc' : ContinuousOn f' (sphere c r) := by
    rw [← hf']; exact Complex.continuous_ofReal.comp_continuousOn fc
  rcases continuous_to_harmonic_complex fc' with ⟨g, gh, b⟩
  use fun z ↦ (g z).re, gh.re
  intro z zs; simp only [← b z zs, Complex.ofReal_re, ← hf']

/-- If `f : ℂ → ℝ` is subharmonic on a disk, its center value is `≤` the circle mean.

    This is the global version of the local submean property in the definition. -/
theorem SubharmonicOn.submean {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (fs : SubharmonicOn f (closedBall c r))
    (rp : r > 0) : f c ≤ ⨍ t in itau, f (circleMap c r t) := by
  rcases continuous_to_harmonic_real (fs.cont.mono Metric.sphere_subset_closedBall) with ⟨g, gh, fg⟩
  generalize hd : (fun z ↦ f z - g z) = d
  have ds : SubharmonicOn d (closedBall c r) := by rw [← hd]; apply fs.add gh.neg.subharmonicOn
  have dz : ∀ z, z ∈ sphere c r → d z = 0 := by intro z zs; rw [← hd]; simp only [fg z zs, sub_self]
  have dz' : ∀ᵐ t, t ∈ itau → d (circleMap c r t) = 0 := by
    apply ae_of_all; intro t _; apply dz
    simp only [mem_sphere_iff_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_eq_self]
    linarith
  rcases ds.maximum_principle (isCompact_closedBall _ _) ⟨c, Metric.mem_closedBall_self rp.le⟩
    with ⟨w, wf, wm⟩
  rw [frontier_closedBall _ rp.ne'] at wf
  have fd : f = fun z ↦ d z + g z := by funext z; rw [← hd]; simp only [sub_add_cancel]
  simp_rw [fd, Average.add (ds.cont.integrableOn_sphere rp) (gh.cont.integrableOn_sphere rp)]
  simp only [← gh.mean c r rp (subset_refl _), add_le_add_iff_right]
  simp only [average_congr_on NiceVolume.itau dz', average_zero]
  rw [← dz w wf]; apply wm (Metric.mem_closedBall_self rp.le)

/-- A continuous function is subharmonic if it is globally subharmonic.
    This is useful since there are sometimes fewer technicalities in proving global
    subharmonicity. -/
theorem subharmonicOn_iff_submean {f : ℂ → ℝ} {s : Set ℂ} (fc : ContinuousOn f s) :
    SubharmonicOn f s ↔ ∀ (c : ℂ) (r : ℝ), r > 0 →
      closedBall c r ⊆ s → f c ≤ ⨍ t in itau, f (circleMap c r t) := by
  constructor; · intro fs c r rp cs; exact (fs.mono cs).submean rp
  · intro sm
    exact
      { cont := fc
        submean' := by
          intro c ci
          rcases Metric.isOpen_iff.mp isOpen_interior c ci with ⟨r, rp, rs⟩
          use r, rp; intro t tp tr; apply sm c t tp
          exact _root_.trans (Metric.closedBall_subset_ball tr) (_root_.trans rs interior_subset) }

/-- If `f : ℂ → ℝ` is subharmonic on a disk, its center valus is `≤` the disk average.

    This is the submean property applied to disks, rather than circles. -/
theorem SubharmonicOn.submean_disk {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (fs : SubharmonicOn f (closedBall c r)) (rp : r > 0) : f c ≤ ⨍ z in closedBall c r, f z := by
  simp only [average_eq, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
    smul_eq_mul]
  rw [Complex.volume_closedBall' rp.le, fubini_ball fs.cont]
  have m : (fun s ↦ (2 * π * s) • f c) ≤ᵐ[volume.restrict (Ioc 0 r)] fun s ↦
      s • ∫ t : ℝ in Set.Ioc 0 (2 * π), f (circleMap c s t) := by
    rw [Filter.EventuallyLE]; rw [ae_restrict_iff' measurableSet_Ioc]; apply ae_of_all; intro s sr
    simp only [Set.mem_Ioc] at sr
    have e := (fs.mono (Metric.closedBall_subset_closedBall sr.2)).submean sr.1
    rw [smul_eq_mul, ← itau]
    simp only [average_eq, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
      smul_eq_mul, itau_real_volume] at e
    generalize hi : ∫ t in itau, f (circleMap c s t) = i
    rw [hi] at e
    calc 2 * π * s * f c
      _ ≤ 2 * π * s * ((2 * π)⁻¹ * i) := by bound
      _ = s * (2 * π * (2 * π)⁻¹) * i := by ring_nf
      _ ≤ s * i := by field_simp [Real.two_pi_pos.ne']; rfl
  have im := integral_mono_ae ?_ ?_ m
  · generalize hi : ∫ s in Ioc 0 r, s • ∫ t in Ioc 0 (2 * π), f (circleMap c s t) = i
    rw [hi] at im; clear hi m
    simp only [← intervalIntegral.integral_of_le rp.le, smul_eq_mul,
      intervalIntegral.integral_mul_const] at im
    rw [intervalIntegral.integral_const_mul] at im
    simp only [integral_id] at im
    ring_nf at im ⊢
    calc f c
      _ = π⁻¹ * r⁻¹^2 * (π * r^2 * f c) := by ring_nf; field_simp [rp.ne', Real.pi_pos.ne']
      _ ≤ π⁻¹ * r⁻¹^2 * i := by bound
  · apply Continuous.integrableOn_Ioc; continuity
  · refine IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc; apply ContinuousOn.smul continuousOn_id
    simp_rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
    refine ContinuousOn.intervalIntegral ?_ isCompact_Icc Real.two_pi_pos.le
    simp only [Set.Icc_prod_Icc]
    refine fs.cont.comp (Continuous.continuousOn (by continuity)) ?_
    intro (a,b) ts
    simp only [Prod.mk_le_mk, Set.mem_Icc] at ts
    simp only [Metric.mem_closedBall, Complex.dist_eq, circleMap_sub_center, norm_circleMap_zero,
      abs_of_nonneg ts.1.1, ts.2.1]

/-- The max of two subharmonic functions is subharmonic -/
theorem SubharmonicOn.max {f g : ℂ → ℝ} {s : Set ℂ} (fs : SubharmonicOn f s)
    (gs : SubharmonicOn g s) : SubharmonicOn (fun z ↦ max (f z) (g z)) s := by
  have pc : ContinuousOn (fun z ↦ (f z, g z)) s := fs.cont.prodMk gs.cont
  have mc : ContinuousOn (fun z ↦ Max.max (f z) (g z)) s := continuous_max.comp_continuousOn pc
  rw [subharmonicOn_iff_submean mc]
  intro c r rp cs
  have pi : IntegrableOn (fun t ↦ (f (circleMap c r t), g (circleMap c r t))) itau := by
    refine ContinuousOn.integrableOn_sphere (f := fun z ↦ (f z, g z)) ?_ rp
    exact pc.mono cs
  refine _root_.trans ?_ (ConvexOn.map_set_average_le convexOn_max continuous_max.continuousOn
      isClosed_univ ?_ ?_ ?_ pi ?_)
  · apply max_le_max
    · have e : ∀ p : ℝ × ℝ, p.fst = ContinuousLinearMap.fst ℝ ℝ ℝ p := fun p ↦ by
        simp only [ContinuousLinearMap.fst, ContinuousLinearMap.coe_mk', LinearMap.fst_apply]
      rw [e]; rw [← average_linear_comm pi]
      simp only [ContinuousLinearMap.fst, ContinuousLinearMap.coe_mk', LinearMap.fst_apply]
      exact (fs.mono cs).submean rp
    · have e : ∀ p : ℝ × ℝ, p.snd = ContinuousLinearMap.snd ℝ ℝ ℝ p := fun p ↦ by
        simp only [ContinuousLinearMap.snd, ContinuousLinearMap.coe_mk', LinearMap.snd_apply]
      rw [e]; rw [← average_linear_comm pi]
      simp only [ContinuousLinearMap.snd, ContinuousLinearMap.coe_mk', LinearMap.snd_apply]
      exact (gs.mono cs).submean rp
  · simp only [Ne]; exact NiceVolume.itau.ne_zero
  · exact NiceVolume.itau.ne_top
  · simp only [Set.mem_univ, Filter.eventually_true]
  · exact (mc.mono cs).integrableOn_sphere rp

/-- The max of a finite set of subharmonic functions is subharmonic -/
theorem SubharmonicOn.partialSups {f : ℕ → ℂ → ℝ} {s : Set ℂ} (fs : ∀ n, SubharmonicOn (f n) s)
    (n : ℕ) : SubharmonicOn (fun z ↦ partialSups (fun k ↦ f k z) n) s := by
  induction' n with n h
  · simp only [fs 0, partialSups_zero]
  · simp only [← Order.succ_eq_add_one, partialSups_succ]
    exact h.max (fs (n + 1))

/-- Continuous, monotonic limits of subharmonic functions are subharmonic -/
theorem SubharmonicOn.monotone_lim {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {s : Set ℂ}
    (fs : ∀ n, SubharmonicOn (f n) s) (fm : Monotone f)
    (ft : ∀ z, z ∈ s → Tendsto (fun n ↦ f n z) atTop (𝓝 (g z))) (gc : ContinuousOn g s) :
    SubharmonicOn g s := by
  rw [subharmonicOn_iff_submean gc]; intro c r rp cs
  have sm := fun n ↦ ((fs n).mono cs).submean rp
  have r0 : 0 ≤ r := rp.le
  have cts : ∀ t, circleMap c r t ∈ s := fun _ ↦ cs (circleMap_mem_closedBall _ r0 _)
  have mt : Tendsto (fun n ↦ ⨍ t in itau, f n (circleMap c r t)) atTop
      (𝓝 (⨍ t in itau, g (circleMap c r t))) := by
    simp_rw [average_eq]; apply Filter.Tendsto.const_smul
    set b' := fun z ↦ |f 0 z| + |g z|
    set b := fun t ↦ b' (circleMap c r t)
    have bc' : ContinuousOn b' (closedBall c r) :=
      ContinuousOn.add ((fs 0).mono cs).cont.abs (gc.mono cs).abs
    have fcc : ∀ n, Continuous fun t ↦ f n (circleMap c r t) := fun n ↦
      ((fs n).cont.mono cs).comp_continuous (continuous_circleMap _ _) fun t ↦
        circleMap_mem_closedBall _ r0 _
    apply tendsto_integral_of_dominated_convergence b; · intro n; exact (fcc n).aestronglyMeasurable
    · exact bc'.integrableOn_sphere rp
    · intro n; rw [ae_restrict_iff' measurableSet_itau]; apply ae_of_all; intro t _
      generalize hz : circleMap c r t = z
      have zs : z ∈ s := by rw [← hz]; apply cts
      rw [Real.norm_eq_abs]; rw [abs_le]; constructor
      · calc -b t
          _ ≤ -(|f 0 z| + 0) := by rw [←hz]; bound
          _ = -|f 0 z| := by simp only [add_zero]
          _ ≤ f 0 z := (neg_abs_le _)
          _ ≤ f n z := fm (by simp only [zero_le]) _
      · have mn : Monotone fun n ↦ f n z := fun _ _ ab ↦ fm ab z
        calc f n z
          _ ≤ g z := Monotone.ge_of_tendsto (f := fun n ↦ f n z) mn (ft z zs) n
          _ ≤ |g z| := le_abs_self _
          _ = 0 + |g z| := by ring
          _ ≤ b t := by rw [← hz]; apply add_le_add; apply abs_nonneg; apply le_refl
    · rw [ae_restrict_iff' measurableSet_itau]; apply ae_of_all; intro t _; exact ft _ (cts _)
  exact le_of_tendsto_of_tendsto' (ft c (cs (Metric.mem_closedBall_self r0))) mt sm

/-- `max b (log ‖f z‖)` is subharmonic for analytic `f : ℂ → H`, for a separable Banach space `H`.

    Some machinery is required to handle general Banach spaces: we rewrite `‖f z‖` as the limit
    of norms along larger and larger finite subspaces, and use the fact that `linear ∘ analytic`
    is analytic to reduce to the case of `H = ℂ`. -/
public theorem AnalyticOnNhd.maxLog_norm_subharmonicOn [SecondCountableTopology H] {f : ℂ → H}
    {s : Set ℂ} (fa : AnalyticOnNhd ℂ f s) (b : ℝ) : SubharmonicOn (fun z ↦ maxLog b ‖f z‖) s := by
  have gc := fa.continuousOn.maxLog_norm b
  have ft := fun z (_ : z ∈ s) ↦ duals_lim_tendsto_maxLog_norm b (f z)
  have fs : ∀ n, SubharmonicOn (fun z ↦ partialSups (fun k ↦ maxLog b ‖duals k (f z)‖) n) s := by
    intro m; apply SubharmonicOn.partialSups; intro n
    exact ((duals n).comp_analyticOnNhd fa).maxLogAbsSubharmonicOn b
  refine SubharmonicOn.monotone_lim fs ?_ ft gc
  · intro a b ab z
    apply (partialSups _).monotone ab

/-- limsup -f = -liminf f -/
theorem Limsup.neg {f : ℕ → ℝ} : (atTop.limsup fun n ↦ f n) = -atTop.liminf fun n ↦ -f n := by
  rw [Filter.limsup_eq]; rw [Filter.liminf_eq]; rw [Real.sInf_def]
  have ns : -{a | ∀ᶠ n in atTop, a ≤ -f n} = {a | ∀ᶠ n in atTop, f n ≤ a} := by
    apply Set.ext
    simp only [Set.mem_neg, Set.mem_ofPred_eq, neg_le_neg_iff, iff_self, forall_const]
  simp_rw [← ns]; simp only [neg_neg]

/-- `p : ENNReal → Prop` is true for all `ENNReal`s if it is true for `⊤` and positive reals -/
theorem ENNReal.induction {p : ENNReal → Prop} (pi : p ⊤)
    (pf : ∀ (x : ℝ), 0 ≤ x → p (ENNReal.ofReal x)) : ∀ e, p e := by
  rw [ENNReal.forall_ennreal]; refine ⟨?_, pi⟩; rw [NNReal.forall]
  simpa only [← ENNReal.ofReal_eq_coe_nnreal]

theorem le_of_lt_imp_le {L : Type} [LinearOrder L] [DenselyOrdered L] {a b : L}
    (h : ∀ c, c < a → c ≤ b) : a ≤ b := by
  contrapose h
  simp only [not_forall, not_le, exists_prop] at h ⊢; rcases exists_between h with ⟨x, bx, xa⟩
  exact ⟨x, xa, bx⟩

/-- A simple characterization of `c ≤ liminf` -/
theorem le_liminf.simple {L : Type} [CompleteLinearOrder L] [DenselyOrdered L] {f : ℕ → L} {c : L} :
    c ≤ atTop.liminf f ↔ ∀ d, d < c → ∀ᶠ n in atTop, d ≤ f n := by
  constructor
  · intro h d dc; rw [Filter.liminf_eq, le_sSup_iff, upperBounds] at h
    simp only [Filter.eventually_atTop, ge_iff_le, Set.mem_ofPred_eq, forall_exists_index] at h
    specialize h d; contrapose h
    simp only [dc, not_forall, not_le, exists_prop, and_true, Filter.eventually_atTop,
      ge_iff_le, not_exists] at h ⊢
    intro a n an; rcases h n with ⟨m, nm, fmd⟩
    exact _root_.trans (an m nm) fmd.le
  · intro h; rw [Filter.liminf_eq, le_sSup_iff, upperBounds]
    simp only [Filter.eventually_atTop, ge_iff_le, Set.mem_ofPred_eq, forall_exists_index]
    intro a ah; apply le_of_lt_imp_le; intro d dc
    rcases Filter.eventually_atTop.mp (h d dc) with ⟨n, hn⟩; exact ah n hn

theorem ENNReal.ofReal_neg_lt_ofReal_neg {x y : ℝ} (xy : x < y) (xn : x < 0) :
    ENNReal.ofReal (-y) < ENNReal.ofReal (-x) := by
  apply (ENNReal.ofReal_lt_ofReal_iff _).mpr
  simp only [xy, neg_lt_neg_iff]; simp only [xn, Right.neg_pos_iff]

/-- Superharmonic `ENNReal` functions, which are allowed to take the value `∞` and required
    only to be measurable (which is not good: the right definition would require lower
    semicontinuity). -/
structure SuperharmonicOn (f : ℂ → ENNReal) (s : Set ℂ) : Prop where
  AEMeasurable : AEMeasurable f (volume.restrict s)
  supmean :
    ∀ (c : ℂ) (r : ℝ),
      r > 0 → closedBall c r ⊆ s → f c ≥ ENNReal.ofReal (π * r ^ 2)⁻¹ * ∫⁻ z in closedBall c r, f z

/-- `ENNReal.ofReal (-f)` is superharmonic if `f` is negative superharmonic -/
theorem SubharmonicOn.neg {f : ℂ → ℝ} {s : Set ℂ} (fs : SubharmonicOn f s)
    (fn : ∀ z, z ∈ s → f z ≤ 0) (sm : MeasurableSet s) :
    SuperharmonicOn (fun z ↦ ENNReal.ofReal (-f z)) s :=
  { AEMeasurable := by
      apply ENNReal.measurable_ofReal.aemeasurable.comp_aemeasurable
      apply fs.cont.neg.aemeasurable sm
    supmean := by
      intro c r rp cs
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · rw [← ENNReal.ofReal_mul]; apply ENNReal.ofReal_le_ofReal
        rw [integral_neg, mul_neg]; apply neg_le_neg
        rw [←Complex.volume_closedBall' rp.le, ←smul_eq_mul, ←setAverage_eq]
        exact (fs.mono cs).submean_disk rp; bound
      · exact (fs.mono cs).cont.neg.integrableOn_closedBall
      · rw [Filter.EventuallyLE]; rw [ae_restrict_iff' measurableSet_closedBall]
        apply Filter.Eventually.of_forall
        intro z zs; simp only [Pi.zero_apply, Right.nonneg_neg_iff]; exact fn z (cs zs) }

lemma NNReal.pi_eq_ofReal_pi : (NNReal.pi : ENNReal) = .ofReal π := by
  rw [←NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- Hartogs's lemma, superharmonic `ℝ≥0∞` case: superharmonic functions that are bounded below
    and liminf bounded pointwise are liminf bounded uniformly.

    See https://www-users.cse.umn.edu/~garrett/m/complex/hartogs.pdf -/
theorem SuperharmonicOn.hartogs {f : ℕ → ℂ → ENNReal} {s k : Set ℂ} {c : ENNReal}
    (fs : ∀ n, SuperharmonicOn (f n) s) (fc : ∀ z, z ∈ s → (atTop.liminf fun n ↦ f n z) ≥ c)
    (ck : IsCompact k) (ks : k ⊆ interior s) :
    ∀ d, d < c → ∀ᶠ n in atTop, ∀ z, z ∈ k → f n z ≥ d := by
  -- Prepare d and c
  intro d dc
  by_cases dz : d = 0
  · simp only [dz, ge_iff_le, zero_le, imp_true_iff, Filter.eventually_atTop, exists_const]
  have dp : d > 0 := pos_iff_ne_zero.mpr dz
  have df : d ≠ ⊤ := ne_top_of_lt dc
  have drp : d.toReal > 0 := ENNReal.toReal_pos dz df
  -- Choose e ∈ (c,d) so that c → e is due to Fatou, and e → d is due to area bounding
  rcases exists_between dc with ⟨e, de, ec⟩
  have ep : e > 0 := _root_.trans de dp
  have ez : e ≠ 0 := pos_iff_ne_zero.mp ep
  have ef : e ≠ ⊤ := ne_top_of_lt ec
  have erp : e.toReal > 0 := ENNReal.toReal_pos ez ef
  -- Handle induction up from small balls
  apply ck.induction_on (p := fun s ↦ ∀ᶠ (n : ℕ) in atTop, ∀ (z : ℂ), z ∈ s → f n z ≥ d)
  · simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, Filter.eventually_atTop, imp_true_iff,
      exists_const]
  · intro k0 k1 k01 h1
    refine h1.mp (.of_forall ?_)
    exact fun n a1 z z0 ↦ a1 z (k01 z0)
  · intro k0 k1 h0 h1
    refine (h0.and h1).mp (.of_forall ?_)
    intro n h z zs; cases' zs with zs zs; exact h.1 z zs; exact h.2 z zs
  -- Base case: Hartogs's lemma near a point.  We choose radii r1 < r2 within s, apply
  -- Fatou's lemma at r1, use monotonicity to bound by r2 integrals, and apply the submean
  -- property with radius r2 to get Hartogs's within radius r2-r1.
  intro z zs
  rcases Metric.isOpen_iff.mp isOpen_interior z (ks zs) with ⟨r, rp, rs⟩
  generalize hr2 : r / 2 = r2
  -- We'll use the submean property on disks of radius r2 < r
  generalize hr1 : r2 * Real.sqrt (d.toReal / e.toReal) = r1
  -- We'll apply Fatou's lemma to a disk of radius r1 < r2 < r
  have dep : d.toReal / e.toReal > 0 := div_pos drp erp
  have r2p : r2 > 0 := by rw [← hr2]; exact half_pos rp
  have r1p : r1 > 0 := by rw [← hr1]; exact mul_pos r2p (Real.sqrt_pos_of_pos (div_pos drp erp))
  have r12 : r1 < r2 := by
    rw [← hr1]; apply mul_lt_of_lt_one_right r2p; rw [Real.sqrt_lt dep.le zero_le_one]
    simp only [one_pow]
    apply (div_lt_one erp).mpr; exact (ENNReal.toReal_lt_toReal df ef).mpr de
  have r1r : r1 < r := by apply _root_.trans r12; rw [← hr2]; exact half_lt_self rp
  have r1s : closedBall z r1 ⊆ s :=
    _root_.trans (Metric.closedBall_subset_ball r1r) (_root_.trans rs interior_subset)
  have rde : d = e * (ENNReal.ofReal (π * r1 ^ 2) * ENNReal.ofReal (π * r2 ^ 2)⁻¹) := by
    rw [← ENNReal.ofReal_mul (by bound : π * r1 ^ 2 ≥ 0), ← hr1, mul_pow, Real.sq_sqrt dep.le]
    have smash : π * (r2 ^ 2 * (d.toReal / e.toReal)) * (π * r2 ^ 2)⁻¹ = d.toReal / e.toReal := by
      calc π * (r2 ^ 2 * (d.toReal / e.toReal)) * (π * r2 ^ 2)⁻¹
        _ = π * (r2 ^ 2 * (d.toReal / e.toReal)) * (π⁻¹ * (r2 ^ 2)⁻¹) := by simp_rw [mul_inv]
        _ = d.toReal / e.toReal * (π * π⁻¹) * (r2 ^ 2 * (r2 ^ 2)⁻¹) := by ring_nf
        _ = d.toReal / e.toReal := by simp only [mul_inv_cancel₀ Real.pi_pos.ne',
            mul_inv_cancel₀ (pow_ne_zero _ r2p.ne'), mul_one]
    rw [smash, ENNReal.ofReal_div_of_pos erp, ENNReal.ofReal_toReal df, ENNReal.ofReal_toReal ef]
    rw [ENNReal.mul_div_cancel ez ef]
  have s12 : ∀ w, w ∈ closedBall z (r2 - r1) → closedBall z r1 ⊆ closedBall w r2 := by
    intro w wr; apply Metric.closedBall_subset_closedBall'
    simp only [dist_comm, Metric.mem_closedBall, le_sub_iff_add_le] at wr; rwa [add_comm]
  have r2s : ∀ w, w ∈ closedBall z (r2 - r1) → closedBall w r2 ⊆ s := by
    intro w ws; refine _root_.trans ?_ (_root_.trans rs interior_subset)
    simp only [Complex.dist_eq, ← hr2, Metric.mem_closedBall] at ws ⊢
    apply Metric.closedBall_subset_ball'; simp only [Complex.dist_eq]
    calc r / 2 + ‖w - z‖
      _ ≤ r / 2 + (r / 2 - r1) := by bound
      _ = r - r1 := by ring_nf
      _ < r := sub_lt_self _ r1p
  -- Apply Fatou's lemma to closedBall z (r/2)
  set fi := fun z ↦ atTop.liminf fun n ↦ f n z
  have fm : ∀ n, _root_.AEMeasurable (f n) (volume.restrict (closedBall z r1)) := fun n ↦
    AEMeasurable.mono_set r1s (fs n).AEMeasurable
  have fatou' := lintegral_liminf_le' (u := Filter.atTop) fm
  have im := @set_lintegral_mono_aEMeasurable _ _ (closedBall z r1) (fun _ ↦ c) _
    measurableSet_closedBall fun _ zs ↦ fc _ (r1s zs)
  simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter] at im
  have vec : e * volume (closedBall z r1) < c * volume (closedBall z r1) :=
    haveI n := NiceVolume.closedBall z r1p
    (ENNReal.mul_lt_mul_iff_left n.ne_zero n.ne_top).mpr ec
  have fatou := le_liminf.simple.mp (_root_.trans im fatou') (e * volume (closedBall z r1)) vec
  rw [Complex.volume_closedBall, NNReal.pi_eq_ofReal_pi, ←ENNReal.ofReal_pow r1p.le,
    ←ENNReal.ofReal_mul' Real.pi_nonneg, mul_comm _ π] at fatou
  clear fatou' im fc vec
  -- Within radius r2-r1, Fatou's lemma implies local Hartogs's
  use closedBall z (r2 - r1),
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by bound))
  refine fatou.mp (.of_forall ?_)
  intro n fn w ws
  calc d
    _ = e * (ENNReal.ofReal (π * r1 ^ 2) * ENNReal.ofReal (π * r2 ^ 2)⁻¹) := by rw [rde]
    _ = e * ENNReal.ofReal (π * r1 ^ 2) * ENNReal.ofReal (π * r2 ^ 2)⁻¹ := by rw [mul_assoc]
    _ ≤ (∫⁻ v in closedBall z r1, f n v) * ENNReal.ofReal (π * r2 ^ 2)⁻¹ := (mul_left_mono fn)
    _ ≤ (∫⁻ v in closedBall w r2, f n v) * ENNReal.ofReal (π * r2 ^ 2)⁻¹ :=
      (mul_left_mono (lintegral_mono_set (s12 w ws)))
    _ = ENNReal.ofReal (π * r2 ^ 2)⁻¹ * ∫⁻ v in closedBall w r2, f n v := by rw [mul_comm]
    _ ≤ f n w := (fs n).supmean w r2 r2p (r2s w ws)

/-- Hartogs's lemma, subharmonic case: subharmonic functions that are bounded above and linsup
    bounded pointwise are linsup bounded uniformly.  We write out the definition of `limsup ≤ c`
    since `ℝ` not being complete makes it complicated otherwise.

    See https://www-users.cse.umn.edu/~garrett/m/complex/hartogs.pdf -/
public theorem SubharmonicOn.hartogs {f : ℕ → ℂ → ℝ} {s k : Set ℂ} {c b : ℝ}
    (fs : ∀ n, SubharmonicOn (f n) s) (fb : ∀ n z, z ∈ s → f n z ≤ b)
    (fc : ∀ z, z ∈ s → ∀ d, d > c → ∀ᶠ n in atTop, f n z ≤ d) (ck : IsCompact k)
    (ks : k ⊆ interior s) : ∀ d, d > c → ∀ᶠ n in atTop, ∀ z, z ∈ k → f n z ≤ d := by
  -- Deal with degenerate b ≤ c case
  by_cases bc : b ≤ c
  · exact fun d dc ↦ .of_forall fun n z zk ↦
      le_trans (fb n z (_root_.trans ks interior_subset zk)) (_root_.trans bc dc.le)
  simp only [not_le] at bc
  -- Port subharmonic problem to superharmonic ennreal problem
  generalize hf' : (fun n z ↦ f n z - b) = f'
  generalize hg : (fun n z ↦ ENNReal.ofReal (-f' n z)) = g
  have fs' : ∀ n, SubharmonicOn (f' n) s := by
    rw [← hf']; exact fun n ↦ (fs n).add (HarmonicOn.const _).subharmonicOn
  have fn' : ∀ n z, z ∈ interior s → f' n z ≤ 0 := fun n z zs ↦ by
    simp only [← hf', fb n z (interior_subset zs), sub_nonpos]
  have gs : ∀ n, SuperharmonicOn (g n) (interior s) := by
    rw [← hg]; exact fun n ↦ ((fs' n).mono interior_subset).neg (fn' n) measurableSet_interior
  have gc : ∀ z, z ∈ interior s → (atTop.liminf fun n ↦ g n z) ≥ ENNReal.ofReal (b - c) := by
    intro z zs; specialize fc z (interior_subset zs); refine le_liminf.simple.mpr ?_
    intro d dc
    have df : d ≠ ⊤ := ne_top_of_lt dc
    have dc' : b - d.toReal > c := by
      calc b - d.toReal
        _ > b - (ENNReal.ofReal (b - c)).toReal :=
          sub_lt_sub_left ((ENNReal.toReal_lt_toReal df ENNReal.ofReal_ne_top).mpr dc) b
        _ = b - (b - c) := by rw [ENNReal.toReal_ofReal (sub_pos.mpr bc).le]
        _ = c := by ring_nf
    refine (fc _ dc').mp (.of_forall ?_); intro n fb
    calc
      g n z = ENNReal.ofReal (b - f n z) := by simp only [← hg, ← hf', neg_sub]
      _ ≥ ENNReal.ofReal (b - (b - d.toReal)) := by bound
      _ = ENNReal.ofReal d.toReal := by ring_nf
      _ = d := by rw [ENNReal.ofReal_toReal df]
  -- Apply Hartogs's lemma to g
  have ks' := ks
  rw [← interior_interior] at ks'
  have h := SuperharmonicOn.hartogs gs gc ck ks'
  -- Finish up
  intro d dc
  have dc' : ENNReal.ofReal (b - d) < ENNReal.ofReal (b - c) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (sub_pos.mpr bc)]; simpa only [sub_lt_sub_iff_left]
  refine (h _ dc').mp (.of_forall ?_)
  intro n hn z zk; specialize hn z zk
  simp only [← hg, ← hf', neg_sub, ge_iff_le] at hn
  rw [ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr (fb n z (interior_subset (ks zk))))] at hn
  rwa [← sub_le_sub_iff_left]
