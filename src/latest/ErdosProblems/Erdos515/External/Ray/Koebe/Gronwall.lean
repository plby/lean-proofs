module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import ErdosProblems.Erdos515.External.Ray.Misc.Annuli
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Cases
import ErdosProblems.Erdos515.External.Ray.Analytic.ConjConj
import ErdosProblems.Erdos515.External.Ray.Analytic.Holomorphic
import ErdosProblems.Erdos515.External.Ray.Analytic.Integral
import ErdosProblems.Erdos515.External.Ray.Analytic.Series
import ErdosProblems.Erdos515.External.Ray.Koebe.Snap
import ErdosProblems.Erdos515.External.Ray.Koebe.Wind
import ErdosProblems.Erdos515.External.Ray.Koebe.WindArea
import ErdosProblems.Erdos515.External.Ray.Koebe.WindInj
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Circle
import ErdosProblems.Erdos515.External.Ray.Misc.Cobounded
import ErdosProblems.Erdos515.External.Ray.Misc.Complex
import ErdosProblems.Erdos515.External.Ray.Misc.Connected
import ErdosProblems.Erdos515.External.Ray.Misc.Deriv
import ErdosProblems.Erdos515.External.Ray.Misc.Linear
import ErdosProblems.Erdos515.External.Ray.Misc.MonotoneSeries
import ErdosProblems.Erdos515.External.Ray.Misc.Subexp
import ErdosProblems.Erdos515.External.Ray.Misc.Topology

attribute [local simp] Circle.norm_coe

/-!
## Grönwall's area theorem

Let `g : ℂ → ℂ` be analytic and injective for `1 < ‖z‖`, with `g z = z + b 1 / z + b 2 / z^2 + ...`.
Then the complement of the image of the `r < ‖z‖` annulus has area

  `π * (r ^ 2 - ∑ n ≥ 1, n * |b n| ^ 2 / r ^ (2 * n))`

Letting `r → 1`, nonnegativity of the area gives

  `∑ n ≥ 1, n * |b n| ^ 2 ≤ 1`

This is the key step in the proof of the Koebe quarter theorem, following
https://en.wikipedia.org/wiki/Koebe_quarter_theorem.

To avoid dealing with power series at infinity, we state the theorem in terms of `f z = z * g z⁻¹`,
which is analytic for `‖z‖ < 1` with `f 0 = 1`, `deriv f 0 = 0`.

Since Mathlib is missing the general formula for area within a curve, we prove that complement
image is star-shaped for sufficiently large `r`, then use the machinery in `WindArea.lean`.
-/

open Bornology (cobounded)
open Classical
open Complex (exp I)
open Function (uncurry)
open Metric (ball closedBall sphere)
open Set
open Filter (atTop Tendsto)
open MeasureTheory (volume IntegrableOn)
open scoped ComplexConjugate ContDiff Topology NNReal Real
noncomputable section

/-!
### Preliminaries
-/

/-- Properties of `f` as discussed above -/
structure Gronwall (f : ℂ → ℂ) : Prop where
  fa : AnalyticOnNhd ℂ f (ball 0 1)
  f0 : f 0 = 1
  inj' : InjOn (fun w ↦ w * f w⁻¹) (norm_Ioi 1)

namespace Gronwall

variable {α β ι : Type}
variable {f : ℂ → ℂ}
variable {r s t : ℝ} {n : ℕ} {z w : ℂ}

def g (_ : Gronwall f) (w : ℂ) : ℂ := w * f w⁻¹

/-- `g` is analytic for `1 < ‖z‖` -/
lemma ga (i : Gronwall f) {z : ℂ} (z1 : 1 < ‖z‖) : AnalyticAt ℂ i.g z := by
  refine analyticAt_id.mul ((i.fa _ (by simp; bound)).comp (analyticAt_inv ?_))
  rw [← norm_pos_iff]; linarith

/-- `g` is analytic for `1 < ‖z‖` -/
lemma ga' (i : Gronwall f) : AnalyticOnNhd ℂ i.g (norm_Ioi 1) := fun _ z1 ↦ i.ga z1

/-- `g` is injective on `norm_Ioi 1` -/
lemma inj (i : Gronwall f) : InjOn i.g (norm_Ioi 1) := i.inj'

/-- Power series coefficients of `f` -/
def coeff (_ : Gronwall f) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / n.factorial

-- The first two `coeffs` are known
@[simp] lemma coeff_zero (i : Gronwall f) : i.coeff 0 = 1 := by simp [coeff, i.f0]
@[simp] lemma coeff_one (i : Gronwall f) : i.coeff 1 = deriv f 0 := by simp [coeff]

/-- The power series of `f` over the whole unit ball -/
lemma hasFPowerSeriesOnBall (i : Gronwall f) :
    HasFPowerSeriesOnBall f (.ofScalars ℂ i.coeff) 0 1 := by
  have a0 := (i.fa 0 (by simp)).hasFPowerSeriesAt
  obtain ⟨p,a1⟩ := (analyticOnNhd_ball_iff_hasFPowerSeriesOnBall (by norm_num)).mp
    (Metric.eball_ofReal (α := ℂ) ▸ i.fa)
  have pe := a0.eq_formalMultilinearSeries a1.hasFPowerSeriesAt
  unfold coeff
  simp only [a0.eq_formalMultilinearSeries a1.hasFPowerSeriesAt] at a0 ⊢
  simpa using a1

/-- `coeff` decays geometrically as fast as we need to do our power series sums -/
lemma norm_coeff_le (i : Gronwall f) (r0 : 0 < r) (r1 : r < 1) :
    ∃ a ∈ Set.Ioo 0 1, ∃ C : ℝ, 0 < C ∧ ∀ n, ‖i.coeff n‖ ≤ C * (a / r) ^ n := by
  have le := i.hasFPowerSeriesOnBall.r_le
  set r' : ℝ≥0 := ⟨r, r0.le⟩
  have r'1 : r' < 1 := by
    have h : (r' : ℝ) < 1 := r1
    exact_mod_cast h
  have r'r : r' < (FormalMultilinearSeries.ofScalars ℂ i.coeff).radius :=
    lt_of_lt_of_le (by simp only [ENNReal.coe_lt_one_iff, r'1]) le
  obtain ⟨a,am,C,C0,le⟩ :=
    (FormalMultilinearSeries.ofScalars ℂ i.coeff).norm_mul_pow_le_mul_pow_of_lt_radius r'r
  refine ⟨a, am, C, C0, fun n ↦ ?_⟩
  specialize le n
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by bound)]
  have le'' : ‖i.coeff n‖ * (r' : ℝ) ^ n ≤ C * a ^ n := by
    simpa only [FormalMultilinearSeries.ofScalars_norm] using le
  exact le''
def norm_prop (i : Gronwall f) (r : ℝ) : Prop :=
  ∃ ac : ℝ × ℝ, ac.1 ∈ Set.Ioo 0 1 ∧ 0 < ac.2 ∧ ∀ n, ‖i.coeff n‖ ≤ ac.2 * (ac.1 * r) ^ n
def a (i : Gronwall f) (r : ℝ) : ℝ := if p : i.norm_prop r then (choose p).1 else 1
def C (i : Gronwall f) (r : ℝ) : ℝ := if p : i.norm_prop r then (choose p).2 else 1
lemma ac_prop (i : Gronwall f) (r1 : 1 < r) : i.a r ∈ Ioo 0 1 ∧ 0 < i.C r ∧
    ∀ n, ‖i.coeff n‖ ≤ i.C r * (i.a r * r) ^ n := by
  have p : i.norm_prop r := by
    obtain ⟨a,am,C,C0,le⟩ := i.norm_coeff_le (r := r⁻¹) (by bound) (by bound)
    exact ⟨⟨a, C⟩, am, C0, fun n ↦ div_inv_eq_mul a r ▸ le n⟩
  simp only [a, p, ↓reduceDIte, C]
  exact Classical.choose_spec p

/-!
### Injectivity of `z ↦ snap (g z)` on large circles
-/

/-- `f' 0` is unknown, but will cancel out in everything below -/
lemma df0 (i : Gronwall f) : HasDerivAt f (deriv f 0) 0 :=
  (i.fa 0 (by simp)).differentiableAt.hasDerivAt

/-- The derivative of `f⁻¹` at `0` -/
lemma df0_inv (i : Gronwall f) : HasDerivAt (fun z ↦ (f z)⁻¹) (-deriv f 0) 0 := by
  have e : -deriv f 0 = -deriv f 0 / f 0 ^ 2 := by simp [i.f0]
  nth_rw 1 [e]
  exact i.df0.inv (by simp [i.f0])

/-- `f x` is eventually nonzero near 0 -/
lemma f0' (i : Gronwall f) : ∀ᶠ z in 𝓝 0, f z ≠ 0 := by
  apply ContinuousAt.eventually_ne
  · exact (i.fa _ (by simp)).continuousAt
  · simp only [i.f0, ne_eq, one_ne_zero, not_false_eq_true]

/-- `g` is nonzero for large `r` -/
lemma g0 (i : Gronwall f) : ∀ᶠ r in atTop, ∀ z ∈ sphere 0 r, i.g z ≠ 0 := by
  rw [eventually_atTop_iff_nhdsGT_zero]
  filter_upwards [eventually_nhdsGT_zero_sphere_of_nhds i.f0', eventually_mem_nhdsWithin]
    with r f0 r0 z zr
  simp only [mem_sphere_iff_norm, sub_zero, mem_Ioi] at zr r0
  have z0 : z ≠ 0 := by rw [ne_eq, ← norm_eq_zero, zr]; apply ne_of_gt; bound
  simp only [g, ne_eq, mul_eq_zero, z0, false_or]
  apply f0
  simp only [mem_sphere_iff_norm, sub_zero, norm_inv, zr, inv_inv]

/-- The derative of `g` in terms of `f` -/
lemma deriv_g (i : Gronwall f) {z : ℂ} (z1 : 1 < ‖z‖) : deriv i.g z = f z⁻¹ - deriv f z⁻¹ / z := by
  have z0 : z ≠ 0 := by rw [← norm_pos_iff]; linarith
  suffices h : HasDerivAt i.g (1 * f z⁻¹ + z * (deriv f z⁻¹ * (-(z ^ 2)⁻¹))) z by
    simp only [one_mul, pow_two, mul_inv_rev, mul_comm _ z⁻¹, mul_neg, ← mul_assoc,
      inv_mul_cancel₀ z0, mul_one] at h
    simp only [← div_eq_inv_mul, ← sub_eq_add_neg] at h
    exact h.deriv
  refine (hasDerivAt_id _).mul (HasDerivAt.comp _ ?_ (hasDerivAt_inv z0))
  exact (i.fa (z⁻¹) (by simp [inv_lt_one_of_one_lt₀ z1])).differentiableAt.hasDerivAt

/-- `deriv f z⁻¹ / f z⁻¹` is bounded for sufficiently large `r` -/
lemma deriv_div_bound (i : Gronwall f) :
    ∃ m > 0, ∀ᶠ r in atTop, ∀ z, ‖z‖ = r → ‖(f z⁻¹)⁻¹ * deriv f z⁻¹‖ ≤ m := by
  have fa := i.fa 0 (by simp)
  have dc : ContinuousAt (fun z ↦ (f z)⁻¹ * deriv f z) 0 :=
    ContinuousAt.mul (fa.continuousAt.inv₀ (by simp [i.f0])) fa.deriv.continuousAt
  obtain ⟨e,e0,dc⟩ := Metric.continuousAt_iff.mp dc 1 (by norm_num)
  refine ⟨1 + ‖deriv f 0‖, by positivity, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop e⁻¹] with r er z zr
  specialize @dc z⁻¹ (by simp [zr, inv_lt_of_inv_lt₀ e0 er])
  simp only [i.f0, inv_one, one_mul, dist_eq_norm] at dc
  calc ‖(f z⁻¹)⁻¹ * deriv f z⁻¹‖
    _ = ‖(f z⁻¹)⁻¹ * deriv f z⁻¹ - deriv f 0 + deriv f 0‖ := by ring_nf
    _ ≤ ‖(f z⁻¹)⁻¹ * deriv f z⁻¹ - deriv f 0‖ + ‖deriv f 0‖ := by bound
    _ ≤ 1 + ‖deriv f 0‖ := by bound

/-- `z ↦ snap (i.g z)` is injective for large `r` -/
lemma g_inj (i : Gronwall f) : ∀ᶠ r in atTop, InjOn (fun z ↦ snap (i.g z)) (sphere 0 r) := by
  -- Keep f near 1
  have fa := i.fa 0 (by simp)
  have fc := Metric.continuousAt_iff.mp fa.continuousAt 20⁻¹ (by norm_num)
  obtain ⟨a,a0,fs⟩ := fc
  simp only [dist_eq_norm, sub_zero, i.f0] at fs
  -- Prove injectivity via `WindInj`
  obtain ⟨m,m0,em⟩ := i.deriv_div_bound
  filter_upwards [Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop a⁻¹,
    Filter.eventually_gt_atTop m, em] with r r1 ar mr em
  have r0 : 0 < r := by linarith
  exact WindInj.inj {
    r0 := r0
    fa := fun z zr ↦ i.ga (by simpa [zr])
    close := by
      intro z zr
      simp only [g, ← mul_sub_one, Complex.norm_mul, zr, div_eq_mul_inv, mul_le_mul_iff_right₀ r0]
      exact (fs (by simp only [norm_inv, zr, inv_lt_of_inv_lt₀ a0 ar])).le
    mono := by
      intro z zr
      have z1 : 1 < ‖z‖ := by simp only [zr, r1]
      have z0 : z ≠ 0 := by rw [← norm_pos_iff]; linarith
      have f0 : f z⁻¹ ≠ 0 := by
        specialize @fs z⁻¹ (by simp only [norm_inv, zr, inv_lt_of_inv_lt₀ a0 ar])
        contrapose fs
        norm_num [fs]
      simp only [g, i.deriv_g z1, mul_inv, ← mul_assoc, mul_inv_cancel₀ z0, one_mul, mul_sub,
        inv_mul_cancel₀ f0, ← mul_div_assoc, Complex.sub_re, Complex.one_re, sub_pos]
      refine lt_of_le_of_lt (Complex.re_le_norm _) ?_
      simp only [norm_div, zr, div_lt_one r0, lt_of_le_of_lt (em z zr) mr]
  }

/-!
### Topology of the inner and outer regions
-/

/-- The region outside a `g` cycle -/
def outer (i : Gronwall f) (r : ℝ) : Set ℂ := i.g '' norm_Ioi r

/-- The complement region inside a `g` cycle -/
def disk (i : Gronwall f) (r : ℝ) : Set ℂ := (i.outer r)ᶜ

-- Monotonicity of `i.outer` and `i.disk`
lemma outer_subset_outer (i : Gronwall f) (rs : r ≤ s) : i.outer s ⊆ i.outer r :=
  image_mono (norm_Ioi_subset_norm_Ioi rs)
lemma disk_subset_disk (i : Gronwall f) (rs : r ≤ s) : i.disk r ⊆ i.disk s :=
  compl_subset_compl.mpr (i.outer_subset_outer rs)

/-- The difference between two disks is the annulus between them -/
lemma disk_diff_disk (i : Gronwall f) (r1 : 1 ≤ r) (rs : r ≤ s) :
    i.disk s \ i.disk r = i.g '' annulus_oc 0 r s := by
  simp only [disk, compl_sdiff_compl, outer]
  rw [← (i.inj.mono _).image_sdiff_subset]
  · apply congr_arg₂ _ rfl
    ext w
    simp [norm_Ioi, annulus_oc, and_comm]
  · exact norm_Ioi_subset_norm_Ioi rs
  · exact norm_Ioi_subset_norm_Ioi r1

/-- The outer region is preconnected -/
lemma isPreconnected_outer (i : Gronwall f) : ∀ᶠ r in atTop, IsPreconnected (i.outer r) := by
  filter_upwards [Filter.eventually_gt_atTop 1] with r r1
  apply isPreconnected_norm_Ioi.image
  intro z m
  exact (i.ga (lt_trans r1 m)).continuousAt.continuousWithinAt

/-- `g` is an open map -/
lemma g_open (i : Gronwall f) : ∀ s ⊆ norm_Ioi 1, IsOpen s → IsOpen (i.g '' s) := by
  rcases i.ga'.is_constant_or_isOpen isPreconnected_norm_Ioi with c | o
  · obtain ⟨w,e⟩ := c
    have e : i.g 2 = i.g 3 := by rw [e, e]; all_goals simp [norm_Ioi]
    rw [i.inj.eq_iff] at e
    · norm_num at e
    · simp [norm_Ioi]
    · simp [norm_Ioi]
  · exact o

/-- The outer region is open -/
lemma isOpen_outer (i : Gronwall f) (r1 : 1 < r) : IsOpen (i.outer r) := by
  refine i.g_open _ ?_ isOpen_norm_Ioi
  intro z m
  simp only [norm_Ioi, mem_ofPred_eq] at m ⊢
  linarith

-- Measurability of `i.outer` and `i.disk`
lemma measurableSet_outer (i : Gronwall f) (r1 : 1 < r) : MeasurableSet (i.outer r) :=
  (i.isOpen_outer r1).measurableSet
lemma measurableSet_disk (i : Gronwall f) (r1 : 1 < r) : MeasurableSet (i.disk r) :=
  (i.measurableSet_outer r1).compl

/-- `g` tends to infinity at infinity -/
lemma g_tendsto (i : Gronwall f) : Tendsto i.g (cobounded ℂ) (cobounded ℂ) := by
  unfold g
  have f0 := (i.fa 0 (by simp)).continuousAt
  simp only [ContinuousAt, i.f0, Metric.tendsto_nhds_nhds] at f0
  obtain ⟨s,s0,sh⟩ := f0 (1/2) (by simp)
  simp only [dist_zero_right, Complex.dist_eq, one_div] at sh
  simp only [tendsto_cobounded, Complex.norm_mul, hasBasis_cobounded_norm_lt.eventually_iff,
    mem_ofPred_eq, true_and]
  intro r
  use max (2 * r) s⁻¹
  intro z lt
  simp only [sup_lt_iff] at lt
  have zs := inv_lt_of_inv_lt₀ (by bound) lt.2
  specialize @sh z⁻¹ (by simpa)
  have f2 : 2⁻¹ ≤ ‖f z⁻¹‖ := by
    calc ‖f z⁻¹‖
      _ = ‖1 + (f z⁻¹ - 1)‖ := by ring_nf
      _ ≥ ‖(1 : ℂ)‖ - ‖f z⁻¹ - 1‖ := by bound
      _ ≥ ‖(1 : ℂ)‖ - 2⁻¹ := by bound
      _ = 2⁻¹ := by norm_num
  rw [(by ring_nf : r = 2 * r * 2⁻¹)]
  exact mul_lt_mul lt.1 f2 (by norm_num) (norm_nonneg _)

/-- The outer region has the expected closure.
This proof is atrocious, but I'm tired of it and thus giving up on elegance. -/
lemma closure_outer (i : Gronwall f) : ∀ᶠ r in atTop, closure (i.outer r) = i.g '' norm_Ici r := by
  filter_upwards [Filter.eventually_gt_atTop 1] with r r1
  apply subset_antisymm
  · intro w m
    simp only [outer, mem_closure_iff_frequently, mem_image, norm_Ioi, norm_Ici, mem_ofPred_eq,
      Filter.frequently_iff_seq_forall, Classical.skolem] at m ⊢
    obtain ⟨s,st,z,m⟩ := m
    rcases tendsto_cobounded_or_mapClusterPt z atTop with t | ⟨a,c⟩
    · have zt := i.g_tendsto.comp t
      replace e : ∀ n, i.g (z n) = s n := fun n ↦ (m n).2
      contrapose e
      simp only [Function.comp_def, not_forall] at zt ⊢
      have large := zt.eventually (eventually_cobounded_le_norm (1 + 2 * ‖w‖))
      have small := st.eventually (eventually_norm_sub_lt (x₀ := w) (ε := 1 + ‖w‖) (by positivity))
      obtain ⟨n,le,lt⟩ := (large.and small).exists
      use n
      contrapose lt
      simp only [not_lt] at lt le ⊢
      simp only [lt] at le
      calc ‖s n - w‖
        _ ≥ ‖s n‖ - ‖w‖ := by bound
        _ ≥ 1 + 2 * ‖w‖ - ‖w‖ := by bound
        _ = 1 + ‖w‖ := by ring
    · use a
      simp only [Metric.nhds_basis_ball.mapClusterPt_iff_frequently] at c
      have ra : r ≤ ‖a‖ := by
        refine le_of_forall_pos_lt_add fun e e0 ↦ ?_
        obtain ⟨n,za⟩ := (c e e0).exists
        calc ‖a‖ + e
          _ = ‖z n - (z n - a)‖ + e := by ring_nf
          _ ≥ ‖z n‖ - ‖z n - a‖ + e := by bound
          _ > ‖z n‖ - e + e := by bound [mem_ball_iff_norm.mp za]
          _ = ‖z n‖ := by ring
          _ ≥ r := by bound [(m n).1]
      refine ⟨ra, ?_⟩
      refine eq_of_forall_dist_le fun e e0 ↦ ?_
      obtain ⟨d,d0,dg⟩ := Metric.continuousAt_iff.mp ((i.ga (z := a) (by order)).continuousAt) (e/2)
        (by bound)
      obtain ⟨n,sw,za⟩ := ((Metric.tendsto_nhds.mp st (e/2) (by bound)).and_frequently
        (c d d0)).exists
      specialize @dg (z n) (by simpa using za)
      calc dist (i.g a) w
        _ ≤ dist (i.g a) (i.g (z n)) + dist (i.g (z n)) w := by bound
        _ = dist (i.g (z n)) (i.g a) + dist (s n) w := by rw [dist_comm, (m _).2]
        _ ≤ e/2 + e/2 := by bound
        _ = e := by ring
  · rw [← closure_norm_Ioi]
    refine ContinuousOn.image_closure (i.ga'.continuousOn.mono ?_)
    simp only [closure_norm_Ioi, r1, norm_Ici_subset_norm_Ioi]

/-- The outer region has the expected frontier -/
lemma frontier_outer (i : Gronwall f) : ∀ᶠ r in atTop,
    frontier (i.outer r) = i.g '' sphere 0 r := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.closure_outer] with r r1 close
  rw [frontier, (i.isOpen_outer r1).interior_eq, close, outer,
    ← (i.inj.mono (norm_Ici_subset_norm_Ioi r1)).image_sdiff_subset norm_Ioi_subset_norm_Ici,
    norm_Ici_diff_norm_Ioi]

/-!
### Area within large radii

We show that `g` satisfies the `WindDiff` conditions for large `r`, then use `WindDiff.volume_eq`.
-/

/-- `g` as a circle map -/
def gc (i : Gronwall f) (r : ℝ) : Circle → ℂˣ := fun z ↦
  Units.mk1 (i.g (r * z.val))

/-- `gc` eventually winds -/
lemma wind (i : Gronwall f) : ∀ᶠ r in atTop, WindDiff (i.gc r) := by
  filter_upwards [i.g_inj, i.g0, Filter.eventually_gt_atTop 1] with r inj g0 r1
  have r0 : 0 < r := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    refine (Units.continuousAt_mk1 ?_).comp ?_
    · apply g0; simp [r0.le]
    · exact (i.ga (by simp [abs_of_pos r0, r1])).continuousAt.comp (by fun_prop)
  · intro x y e
    simp only [gc, Units.snap_mk1] at e
    simpa only [mul_eq_mul_left_iff, Circle.coe_inj, Complex.ofReal_eq_zero, r0.ne',
      or_false] using (inj.eq_iff (by simp [r0.le]) (by simp [r0.le])).mp e
  · have e : ∀ t, (i.gc r (Circle.exp t)).val = i.g (circleMap 0 r t) := by
      intro t
      rw [gc, Units.val_mk1]
      · simp [circleMap]
      · apply g0; simp [r0.le]
    intro t
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (.of_forall e)
    apply ((i.ga ?_).differentiableAt.restrictScalars _).comp
    · apply differentiable_circleMap
    · simp [abs_of_pos r0, r1]

lemma gc_exp (i : Gronwall f) : ∀ᶠ r in atTop, ∀ t,
    (i.gc r (Circle.exp t)).val = i.g (circleMap 0 r t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.g0, i.wind] with r r1 g0 w t
  rw [gc, Units.val_mk1]
  · simp [circleMap]
  · apply g0; simp; linarith

/-- `w.fe` is (real) analytic -/
lemma analyticAt_fe (i : Gronwall f) : ∀ᶠ r in atTop, ∀ (w : WindDiff (i.gc r)), ∀ t,
    AnalyticAt ℝ w.fe t := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.g0, i.gc_exp] with r r1 g0 gc_exp w t
  have r0 : 0 < r := by linarith
  unfold WindDiff.fe
  simp only [gc_exp]
  refine (i.ga ?_).restrictScalars.comp ?_
  · simp [abs_of_pos r0, r1]
  · apply analyticOnNhd_circleMap; trivial

/-- Eventually, the two notions of spheres coincide -/
lemma sphere_eq (i : Gronwall f) : ∀ᶠ r in atTop,
    i.g '' sphere 0 r = range (fun z ↦ (i.gc r z).val) := by
  filter_upwards [i.g0, Filter.eventually_gt_atTop 0] with r g0 r0
  ext w
  simp only [mem_image, mem_sphere_iff_norm, sub_zero, mem_range, gc]
  constructor
  · intro ⟨z,zr,e⟩
    have z0 : z ≠ 0 := by rw [ne_eq, ← norm_eq_zero]; linarith
    refine ⟨snap z, ?_⟩
    rw [Units.val_mk1]
    · simp [coe_snap, z0, zr, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr r0.ne'), e]
    · apply g0; simp [r0.le]
  · intro ⟨z,e⟩
    refine ⟨r * z.val, by simp [r0.le], ?_⟩
    rwa [Units.val_mk1] at e
    apply g0; simp [r0.le]

/-- Our two notions of outside (based on `g` and star-shaped extrapolation) match -/
lemma outer_eq_outer (i : Gronwall f) :
    ∀ᶠ r in atTop, ∀ w : Wind (i.gc r), i.outer r = w.outer := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.isPreconnected_outer, i.frontier_outer,
    i.sphere_eq] with r r1 c0 fo se w
  refine c0.eq_of_frontier_eq w.isPreconnected_outer (i.isOpen_outer r1) w.isOpen_outer ?_ ?_
  · simp only [fo, w.frontier_outer, w.sphere_eq, se]
  · obtain ⟨z,zo,zr⟩ := ((i.g_tendsto.eventually w.large_mem_outer).and
      (eventually_cobounded_lt_norm r)).exists
    exact ⟨i.g z, ⟨z, zr, rfl⟩, zo⟩

/-- Power series for `w.fe` -/
lemma hasSum_fe (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t,
    HasSum (fun n : ℕ ↦ i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)) (w.fe t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.gc_exp] with r r1 gc_exp w t
  have r0 : 0 < r := by linarith
  have ri0 : 0 < r⁻¹ := by bound
  have ri1 : r⁻¹ < 1 := by bound
  have sum : ∀ t, HasSum (fun n ↦ i.coeff n * circleMap 0 r⁻¹ t ^ n) (f (circleMap 0 r⁻¹ t)) := by
    intro t
    have sum := i.hasFPowerSeriesOnBall.hasSum (y := circleMap 0 r⁻¹ t)
      (by simp [← ofReal_norm, abs_of_pos ri0, ri1])
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm, zero_add, mul_pow, smul_eq_mul,
      ← mul_assoc, zero_add, Complex.ofReal_inv] using sum
  have pow : ∀ n : ℕ, circleMap 0 r t * circleMap 0 r⁻¹ (-t) ^ n =
      circleMap 0 r t ^ (1 - n : ℤ) := by
    intro n
    rw [zpow_sub₀, zpow_one, zpow_natCast, ← circleMap_zero_inv, inv_pow, div_eq_mul_inv]
    simp [r0.ne']
  rw [WindDiff.fe, gc_exp, g, circleMap_zero_inv]
  replace sum := (sum (-t)).mul_left (circleMap 0 r t)
  simp only [← mul_assoc, mul_comm _ (i.coeff _)] at sum
  simp only [mul_assoc, pow] at sum
  exact sum

-- Power series bound lemmas
def uf (i : Gronwall f) (r : ℝ) (n : ℕ) : ℝ := i.C r * r * i.a r ^ n
def udf (i : Gronwall f) (r : ℝ) (n : ℕ) : ℝ := i.C r * r * (n + 1) * i.a r ^ n
lemma summable_uf (i : Gronwall f) (r1 : 1 < r) : Summable (i.uf r) := by
  obtain ⟨⟨a0,a1⟩,C0,_⟩ := i.ac_prop r1
  exact summable_subexp_mul_pow a0.le a1
lemma summable_udf (i : Gronwall f) (r1 : 1 < r) : Summable (i.udf r) := by
  obtain ⟨⟨a0,a1⟩,C0,_⟩ := i.ac_prop r1
  exact summable_subexp_mul_pow a0.le a1
lemma le_uf (i : Gronwall f) (r1 : 1 < r) :
    ‖i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)‖ ≤ i.uf r n := by
  obtain ⟨⟨a0,a1⟩,C0,cle⟩ := i.ac_prop r1
  have r0 : 0 < r := by linarith
  simp only [Complex.norm_mul, norm_zpow, norm_circleMap_zero, abs_of_pos r0, zpow_sub₀ r0.ne',
    zpow_one, zpow_natCast, uf]
  calc ‖i.coeff n‖ * (r / r ^ n)
    _ ≤ i.C r * (i.a r * r) ^ n * (r / r ^ n) := by bound [cle n]
    _ = i.C r * r * i.a r ^ n * (r ^ n * (r ^ n)⁻¹) := by rw [← inv_pow]; ring
    _ ≤ i.C r * r * i.a r ^ n := by rw [mul_inv_cancel₀ (by positivity), mul_one]
lemma le_udf (i : Gronwall f) (r1 : 1 < r) :
    ‖(1 - n : ℤ) * I * i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)‖ ≤ i.udf r n := by
  obtain ⟨⟨a0,a1⟩,C0,cle⟩ := i.ac_prop r1
  have r0 : 0 < r := by linarith
  have nb : ‖(1 - n : ℂ)‖ ≤ n + 1 := by induction' n with n; all_goals simp; try linarith
  simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast, zpow_natCast, Complex.norm_mul, mul_one,
    norm_circleMap_zero, abs_of_pos r0, Complex.norm_I, udf, norm_zpow, zpow_sub₀ r0.ne', zpow_one]
  calc ‖(1 - n : ℂ)‖ * ‖i.coeff n‖ * (r / r ^ n)
    _ ≤ (n + 1) * (i.C r * (i.a r * r) ^ n) * (r / r ^ n) := by bound [cle n]
    _ = i.C r * r * (n + 1) * i.a r ^ n * (r ^ n * (r ^ n)⁻¹) := by rw [← inv_pow]; ring
    _ ≤ i.C r * r * (n + 1) * i.a r ^ n := by rw [mul_inv_cancel₀ (by positivity), mul_one]

/-- Power series for the derivative `w.dfe` -/
lemma hasSum_dfe (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t,
    HasSum (fun n : ℕ ↦ (1 - n : ℤ) * I * i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)) (w.dfe t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.hasSum_fe] with r r1 sum w t
  simp only [WindDiff.dfe]
  have c0 : ∀ {t}, circleMap 0 r t ≠ 0 := fun {t} ↦ circleMap_ne_center (by positivity)
  set f := fun (n : ℕ) t ↦ i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)
  set f' := fun (n : ℕ) t ↦ i.coeff n * ((1 - n : ℤ) * circleMap 0 r t ^ (1 - n - 1 : ℤ) *
    (circleMap 0 r t * I))
  have df : ∀ n t, HasDerivAt (f n) (f' n t) t := by
    intro n t
    simp only [f, f']
    apply HasDerivAt.const_mul
    exact (hasDerivAt_zpow (1 - n) (circleMap 0 r t) (.inl c0)).comp t (hasDerivAt_circleMap 0 r t)
  have hf : ∀ n t, f n t = i.coeff n * circleMap 0 r t ^ (1 - n : ℤ) := by intro n t; rfl
  have hf' : ∀ n t, f' n t = (1 - n : ℤ) * I * i.coeff n * circleMap 0 r t ^ (1 - n : ℤ) := by
    intro n t
    simp only [f', ← mul_assoc _ _ I, mul_assoc _ (_ ^ (_ : ℤ)) (circleMap _ _ _),
      ← zpow_add_one₀ c0]
    ring_nf
  have e : w.fe = fun t ↦ ∑' n, f n t := by ext t; exact (sum w t).tsum_eq.symm
  rw [e]
  simp only [← hf']
  have fu : ∀ n t, ‖f n t‖ ≤ i.uf r n := by intro n t; simp only [hf]; apply i.le_uf r1
  have f'v : ∀ n t, ‖f' n t‖ ≤ i.udf r n := by intro n t; simp only [hf']; apply i.le_udf r1
  rw [deriv_tsum_apply (i.summable_udf r1) (y₀ := t)]
  · simp only [(df _ _).deriv]
    exact ((i.summable_udf r1).of_norm_bounded (fun n ↦ f'v n t)).hasSum
  · intro n t
    exact (df n t).differentiableAt
  · intro n t
    simp only [(df _ _).deriv, f'v]
  · exact (i.summable_uf r1).of_norm_bounded (fun n ↦ fu n t)

/-- `inner ℝ (w.fe t * I) (w.dfe t)` is eventually nonnegative -/
lemma inner_nonneg (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t,
    0 ≤ inner ℝ (w.fe t * I) (w.dfe t) := by
  -- Choose sufficiently large `r`
  obtain ⟨m,m0,em⟩ := i.deriv_div_bound
  filter_upwards [Filter.eventually_gt_atTop 1, Filter.eventually_ge_atTop m, em, i.g0,
    i.gc_exp] with r r1 rm em g0 gc_exp w t
  have r0 : 0 < r := by linarith
  have ri1 : r⁻¹ < 1 := by bound
  simp only [WindDiff.fe, WindDiff.dfe]
  unfold WindDiff.fe
  -- Various derivatives
  set z := fun t ↦ circleMap 0 r t
  have hz : ∀ t, circleMap 0 r t = z t := by intro; rfl
  have circ : ∀ t, (r : ℂ) * Circle.exp t = z t := by intro; simp [circleMap, ← hz]
  have z0 : ∀ {t}, z t ≠ 0 := by intro t; simp [z, r0.ne']
  have fdz : ∀ t, DifferentiableAt ℂ f (z t)⁻¹ := by
    intro t; exact (i.fa (z t)⁻¹ (by simp [z, abs_of_pos r0, ri1])).differentiableAt
  have g0c : ∀ {t}, i.g (z t) ≠ 0 := by intro t; apply g0; simp [z, r0.le]
  simp only [gc_exp, hz]
  have dz : ∀ t, HasDerivAt z (z t * I) t := by
    intro t; simp only [← hz]; apply hasDerivAt_circleMap
  have dzi : ∀ t, HasDerivAt (fun t ↦ (z t)⁻¹) ((-(z t * I)) / (z t) ^ 2) t :=
    fun t ↦ (dz t).inv_tower z0
  simp only [pow_two, neg_div, mul_div_mul_comm, div_self z0, one_mul] at dzi
  have dg : HasDerivAt (fun t ↦ i.g (z t))
      (z t * I * f (z t)⁻¹ + z t * (deriv f (z t)⁻¹ * -(I / z t))) t :=
    (dz t).mul ((fdz t).hasDerivAt.comp t (dzi t))
  simp only [dg.deriv]
  -- Now a bunch of poorly organised algebra
  simp only [g, Complex.inner, add_mul, map_mul, Complex.conj_I]
  generalize hw : z t = w
  generalize hf : f w⁻¹ = fw
  generalize hd : deriv f w⁻¹ = dfw
  have nw : ‖w‖ = r := by simp [← hw, z, r0.le]
  have f0 : 0 < ‖fw‖ := by simp [g, ← hf, ← hw] at g0c ⊢; exact g0c.2
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  have e : w * fw * (starRingEnd ℂ) w * (starRingEnd ℂ) fw = ‖w‖^2 * ‖fw‖^2 := by
    simp only [mul_comm _ (conj w), ← mul_assoc, Complex.conj_mul']
    simp only [mul_assoc, Complex.mul_conj']
  simp only [e, Complex.mul_conj']
  simp only [mul_assoc, ← mul_sub, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
    Complex.ofReal_re]
  apply mul_nonneg (by positivity)
  rw [sub_nonneg]
  refine le_trans (Complex.re_le_norm _) ?_
  simp only [Complex.norm_mul, RCLike.norm_conj, norm_inv, nw, pow_two]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← div_eq_mul_inv, div_le_iff₀ r0, mul_comm _ r, ← div_le_iff₀ f0]
  specialize em w nw
  simp only [hd, hf, norm_div, ← div_eq_inv_mul] at em
  exact le_trans em rm

/-- Terms for our 2D sum -/
def term (i : Gronwall f) (r : ℝ) (n m : ℕ) (t : ℝ) : ℂ :=
  (1 - n) * I * i.coeff n * conj (i.coeff m) * r ^ 2 / r ^ (n + m) * exp ((m - n) * t * I)

/-- `i.term` is continuous -/
@[fun_prop] lemma continuous_term (i : Gronwall f) (r : ℝ) (n m : ℕ) :
    Continuous (i.term r n m) := by
  unfold term
  fun_prop

-- Bounds on `i.term`
def ut (i : Gronwall f) (r : ℝ) (p : ℕ × ℕ) : ℝ := i.C r ^ 2 * (p.1 + 1) * r ^ 2 * i.a r ^ (p.1 + p.2)
lemma le_ut (i : Gronwall f) (r1 : 1 < r) : ∀ n m t, ‖i.term r n m t‖ ≤ i.ut r (n,m) := by
  intro n m t
  obtain ⟨⟨a0,a1⟩,C0,cle⟩ := i.ac_prop r1
  simp only [term, ut]
  generalize i.a r = a at a0 a1 cle
  have r0 : 0 < r := by linarith
  have rn0 : ∀ {n}, r ^ n ≠ 0 := by intro n; positivity
  have nb : ‖(1 - n : ℂ)‖ ≤ n + 1 := by induction' n with n; all_goals simp; try linarith
  simp only [norm_mul, Complex.norm_div, Complex.norm_I, mul_one, RCLike.norm_conj, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos r0, Complex.norm_exp, Complex.mul_re,
    Complex.sub_re, Complex.natCast_re, Complex.ofReal_re, Complex.sub_im, Complex.natCast_im,
    sub_self, Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im, zero_mul,
    add_zero, Complex.I_im, Real.exp_zero]
  calc ‖(1 - n : ℂ)‖ * ‖i.coeff n‖ * ‖i.coeff m‖ * r ^ 2 / r ^ (n + m)
    _ ≤ (n + 1) * (i.C r * (a * r) ^ n) * (i.C r * (a * r) ^ m) * r ^ 2 / r ^ (n + m) := by bound
    _ = i.C r ^ 2 * (n + 1) * r ^ 2 * a ^ (n + m) * (r ^ (n + m) / r ^ (n + m)) := by ring
    _ = i.C r ^ 2 * (n + 1) * r ^ 2 * a ^ (n + m) := by simp only [div_self rn0, mul_one]
lemma summable_ut (i : Gronwall f) (r1 : 1 < r) : Summable (i.ut r) := by
  obtain ⟨⟨a0,a1⟩,C0,cle⟩ := i.ac_prop r1
  unfold ut
  generalize i.a r = a at a0 a1 cle
  simp only [← mul_assoc, mul_comm _ (r ^ 2)]
  simp only [mul_assoc _ (_ + _)]
  apply Summable.mul_left
  simp only [pow_add, ← mul_assoc]
  apply Summable.mul_of_nonneg (f := fun n : ℕ ↦ (n + 1) * a ^ n) (g := fun m ↦ a ^ m)
  · exact summable_subexp_mul_pow a0.le a1
  · exact summable_geometric_of_lt_one a0.le a1
  · intro n; simp only [Pi.zero_apply]; bound
  · intro n; simp only [Pi.zero_apply]; bound

/-- Power series for `w.dfe t * conj (w.fe t)` -/
lemma hasSum_inner (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t : ℝ,
    HasSum (fun ((n : ℕ), (m : ℕ)) ↦ i.term r n m t) (w.dfe t * conj (w.fe t)) := by
  filter_upwards [i.hasSum_fe, i.hasSum_dfe, Filter.eventually_gt_atTop 1] with r sfe sdfe r1 w t
  have c0 : ∀ {t}, circleMap 0 r t ≠ 0 := fun {t} ↦ circleMap_ne_center (by positivity)
  have snf := (i.summable_uf r1).of_nonneg_of_le (by bound) (fun n ↦ i.le_uf r1 (t := t))
  have sndf := (i.summable_udf r1).of_nonneg_of_le (by bound) (fun n ↦ i.le_udf r1 (t := t))
  simp only [← Complex.norm_conj (_ * _)] at snf
  have sp := (summable_mul_of_summable_norm sndf snf).hasSum
  simp only [← tsum_mul_tsum_of_summable_norm sndf snf,
    (Complex.hasSum_conj'.mpr (sfe w t)).tsum_eq, (sdfe w t).tsum_eq] at sp
  apply sp.congr_fun
  intro ⟨n,m⟩
  simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast, zpow_sub₀ c0, zpow_one, zpow_natCast,
    map_mul, map_div₀, Complex.conj_circleMap, map_zero, map_pow, term]
  simp only [pow_add, div_eq_mul_inv, mul_inv_rev, sub_mul (m : ℂ), sub_mul (m * t : ℂ),
    Complex.exp_sub, circleMap, zero_add, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_neg,
    neg_mul, Complex.exp_neg, inv_pow, inv_inv, inv_mul_cancel₀ (Complex.exp_ne_zero _),
    mul_comm _ (exp (t * I)), mul_comm _ (exp (t * I))⁻¹, ← mul_assoc, pow_two, one_mul]
  ring

/-- Our integrals commute with our sum -/
lemma sum_integral_comm (i : Gronwall f) : ∀ᶠ r in atTop,
    HasSum (fun (p : ℕ × ℕ) ↦ ∫ t in -π..π, i.term r p.1 p.2 t)
      (∫ t in -π..π, ∑' (p : ℕ × ℕ), i.term r p.1 p.2 t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.hasSum_inner, i.wind] with r r1 hasSum_inner w
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (bound := fun p t ↦ i.ut r p)
  · intro n; apply Continuous.aestronglyMeasurable; fun_prop
  · simp [i.le_ut r1]
  · simp [i.summable_ut r1]
  · apply intervalIntegrable_const
  · simp [(hasSum_inner w _).summable.hasSum]

/-- Diagonal term integrals -/
def term_diag (i : Gronwall f) (r : ℝ) (n : ℕ) : ℂ :=
  2 * π * (1 - n) * I * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)

/-- Only the diagonal `i.term` integrals survive -/
lemma integral_term_diag (i : Gronwall f) (r : ℝ) (n m : ℕ) :
    ∫ t in -π..π, i.term r n m t = if n = m then i.term_diag r n else 0 := by
  have ce : (m - n : ℂ) = (m - n : ℤ) := by simp
  simp only [term, term_diag, div_eq_mul_inv, intervalIntegral.integral_const_mul,
    integral_exp_mul_I, ce, sub_eq_zero, Nat.cast_inj]
  by_cases nm : n = m
  · simp only [← nm, ↓reduceIte, ← Complex.conj_mul', ← two_mul, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  · simp [nm, Ne.symm nm]

/-- Drop all but the diagonal, if offdiagonals are zero -/
@[simp] lemma tsum_diag {f : ι → ℂ} {d : (n m : ι) → Decidable (n = m)} :
   ∑' (p : ι × ι), @ite _ (p.1 = p.2) (d p.1 p.2) (f p.1) 0 = ∑' n, f n := by
  apply tsum_eq_tsum_of_ne_zero_bij (i := fun n ↦ (n.val, n.val))
  · intro ⟨n,_⟩ ⟨m,_⟩
    simp
  · intro ⟨n,m⟩ s
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at s
    simp [← s.1, s.2]
  · simp

/-- Our final series terms -/
def gronwall_term (i : Gronwall f) (r : ℝ) (n : ℕ) : ℝ :=
  π * (1 - n) * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)

/-- We also need the `ℂ` version -/
def gronwall_c (i : Gronwall f) (r : ℂ) (n : ℕ) : ℂ :=
  π * (1 - n) * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)

-- The two are related
lemma ofReal_gronwall_term (i : Gronwall f) (r : ℝ) (n : ℕ) :
    (i.gronwall_term r n : ℂ) = i.gronwall_c r n := by simp [gronwall_term, gronwall_c]
lemma gronwall_term_eq_c (i : Gronwall f) (r : ℝ) :
    i.gronwall_term r = fun n ↦ (i.gronwall_c r n).re := by simp [← ofReal_gronwall_term]

/-- `i.gronwall_c` is summable -/
def ug (i : Gronwall f) (r s : ℝ) (n : ℕ) : ℝ :=
  π * ‖(1 - n : ℂ)‖ * s ^ 2 * i.C r ^ 2 * i.a r ^ (2 * n)
lemma le_ug (i : Gronwall f) (r1 : 1 < r) (zr : r ≤ ‖z‖) (zs : ‖z‖ ≤ s) (n : ℕ) :
    ‖i.gronwall_c z n‖ ≤ i.ug r s n := by
  have r0 : 0 < r := by linarith
  obtain ⟨⟨a0,a1⟩,C0,cle⟩ := i.ac_prop r1
  simp only [gronwall_c, ug]
  simp only [Complex.norm_div, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_pow, sq_abs]
  calc π * ‖(1 - n : ℂ)‖ * ‖i.coeff n‖ ^ 2 * ‖z‖ ^ 2 / ‖z‖ ^ (2 * n)
    _ ≤ π * ‖(1 - n : ℂ)‖ * (i.C r * (i.a r * r) ^ n) ^ 2 * s ^ 2 / r ^ (2 * n) := by bound
    _ = π * ‖(1 - n : ℂ)‖ * s ^ 2 * i.C r ^ 2 * i.a r ^ (2 * n) * (r / r) ^ (2 * n) := by ring
    _ ≤ π * ‖(1 - n : ℂ)‖ * s ^ 2 * i.C r ^ 2 * i.a r ^ (2 * n) := by simp [div_self r0.ne']
lemma le_ug' (i : Gronwall f) (r1 : 1 < r) (n : ℕ) : ‖i.gronwall_term r n‖ ≤ i.ug r r n := by
  have ar : |r| = r := by rw [abs_of_pos (by linarith)]
  refine le_trans ?_ (le_trans (i.le_ug (z := r) (s := r) r1 ?_ ?_ n) ?_)
  all_goals simp [gronwall_term_eq_c, Complex.abs_re_le_norm, ar]
lemma summable_ug (i : Gronwall f) (r1 : 1 < r) : Summable (i.ug r s) := by
  obtain ⟨⟨a0,a1⟩,C0,cle⟩ := i.ac_prop r1
  unfold ug
  simp only [pow_mul]
  exact summable_subexp_mul_pow (by bound) (pow_lt_one₀ (by bound) a1 (by norm_num))
lemma summable_gronwall_term (i : Gronwall f) (r1 : 1 < r) : Summable (i.gronwall_term r) :=
  (i.summable_ug r1).of_norm_bounded (i.le_ug' r1)
lemma summable_gronwall_c (i : Gronwall f) {r : ℂ} (r1 : 1 < ‖r‖) : Summable (i.gronwall_c r) :=
  (i.summable_ug r1).of_norm_bounded (i.le_ug r1 (le_refl _) (le_refl _))

/-- The area within large radii is given by the Grönwall series -/
lemma large_volume_eq (i : Gronwall f) : ∀ᶠ r in atTop,
    HasSum (i.gronwall_term r) (volume.real (i.disk r)) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.wind, i.outer_eq_outer, i.inner_nonneg,
    i.analyticAt_fe, i.hasSum_inner, i.sum_integral_comm] with r r1 w oe i0 fa is sum_integral_comm
  have ed : i.disk r = w.wind.disk := by simp only [disk, ← w.wind.compl_outer, oe w.wind]
  simp only [ed, w.volume_eq, abs_of_nonneg (i0 w _)]
  simp only [Complex.inner, ← Complex.reCLM_apply]
  have ii : IntervalIntegrable (fun t ↦ w.dfe t * (starRingEnd ℂ) (w.fe t * I)) volume (-π) π := by
    apply Continuous.intervalIntegrable
    simp only [WindDiff.dfe]
    have fc1 : ContDiff ℝ 1 w.fe := by
      rw [contDiff_iff_contDiffAt]
      exact fun t ↦ (fa w t).contDiffAt.of_le le_top
    have dc := fc1.continuous_deriv_one
    have fc := fc1.continuous
    continuity
  have er : i.gronwall_term r = fun n ↦
      Complex.reCLM (π * (1 - ↑n) * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)) := by
    ext n
    simp only [Complex.reCLM_apply, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      Complex.ofReal_re, gronwall_term]
  rw [Complex.reCLM.intervalIntegral_comp_comm ii, Complex.reCLM_apply, ← Complex.re_ofReal_mul]
  simp only [er, ← Complex.reCLM_apply]
  apply Complex.reCLM.hasSum
  simp only [Complex.ofReal_inv, Complex.ofReal_ofNat, map_mul, Complex.conj_I, mul_neg,
    intervalIntegral.integral_neg, ← mul_assoc, intervalIntegral.integral_mul_const]
  simp only [mul_comm _ I, ← mul_assoc, ← div_eq_mul_inv, ← neg_mul, ← neg_div]
  simp only [←(is w _).tsum_eq, ← sum_integral_comm.tsum_eq, i.integral_term_diag, tsum_diag]
  rw [← tsum_mul_left]
  simp only [term_diag, mul_comm _ I, ← mul_assoc, div_eq_mul_inv, mul_neg, Complex.I_mul_I,
    neg_neg, one_mul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)]
  exact (i.summable_gronwall_c
    (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)])).hasSum

/-!
### Large areas restated as an analytic function
-/

/-- The area within large annuli is given by the complex Grönwall series -/
lemma large_volume_eq_series (i : Gronwall f) : ∀ᶠ r : ℝ in atTop,
    ∑' n, i.gronwall_c r n = volume.real (i.disk r) := by
  filter_upwards [i.large_volume_eq, Filter.eventually_gt_atTop 1] with r h r1
  simpa [gronwall_c, gronwall_term] using (Complex.ofRealCLM.hasSum h).tsum_eq

/-- The Gronwall series is analytic -/
lemma analyticAt_series (i : Gronwall f) {z : ℂ} (z1 : 1 < ‖z‖) :
    AnalyticAt ℂ (fun z ↦ ∑' n, i.gronwall_c z n) z := by
  obtain ⟨t,t1,tr⟩ := exists_between z1
  set s := ‖z‖ + 1
  obtain ⟨⟨a0,a1⟩,C0,_⟩ := i.ac_prop t1
  set b : ℝ := i.a t ^ 2
  have b1 : b < 1 := by rw [pow_lt_one_iff_of_nonneg]; exact a1; bound; norm_num
  have subexp : Subexp (fun n ↦ π * ‖(1 - n : ℂ)‖ * s ^ 2 * i.C t ^ 2) := by fun_prop
  obtain ⟨C,c,c0,c1,le⟩ := subexp.le_exp b (by positivity) b1
  have ta : AnalyticOnNhd ℂ (fun r ↦ ∑' n, i.gronwall_c r n) (norm_Ioo t s) := by
    apply fast_series_converge_tsum_at isOpen_norm_Ioo (c := C) (a := c) c0.le c1
    · intro n
      simp only [gronwall_c]
      intro z zm
      simp only [norm_Ioo, mem_preimage, mem_Ioo] at zm
      have z0 : z ≠ 0 := by rw [← norm_pos_iff]; linarith
      refine (analyticAt_const.mul (analyticAt_id.pow 2)).mul ?_
      simp only [← inv_pow]
      exact (analyticAt_inv z0).pow _
    · intro n z zm
      simp only [norm_Ioo, mem_preimage, mem_Ioo] at zm
      have z1 : 1 < ‖z‖ := by linarith
      refine le_trans (i.le_ug t1 zm.1.le zm.2.le n) (le_trans ?_ (le n))
      simp [abs_of_pos Real.pi_pos, b, ug, pow_mul]
  exact ta _ (by simp [norm_Ioo, tr, s])

/-- Disks have finite area -/
@[simp, aesop (rule_sets := [finiteness]) safe apply] lemma volume_disk_finite (i : Gronwall f) :
    volume (i.disk r) ≠ ⊤ := by
  have large : ∀ᶠ r in atTop, volume (i.disk r) ≠ ⊤ := by
    filter_upwards [i.wind, i.outer_eq_outer] with r w oe
    have ed : i.disk r = w.wind.disk := by simp only [disk, ← w.wind.compl_outer, oe w.wind]
    exact ed ▸ w.wind.isCompact_disk.measure_ne_top
  obtain ⟨s,rs,f⟩ := ((Filter.eventually_ge_atTop r).and large).exists
  simp only [← lt_top_iff_ne_top] at f ⊢
  exact lt_of_le_of_lt (MeasureTheory.measure_mono (i.disk_subset_disk rs)) f

lemma volume_diff_eq (i : Gronwall f) (r1 : 1 < r) (rs : r ≤ s) :
    volume.real (i.disk s \ i.disk r) = volume.real (i.disk s) - volume.real (i.disk r) := by
  rw [← MeasureTheory.measureReal_sdiff (i.disk_subset_disk rs) (i.measurableSet_disk r1)]

/-!
### Area within small annuli as an integral

We write small radii in terms of an integral, then show the integral is analytic.
We extend our formula down to small radii via analytic continuation.
-/

/-- Our volume differences as an integral -/
def volume_integral (i : Gronwall f) (r s : ℝ) : ℝ :=
  ∫ w in annulus_cc 0 r s, ‖deriv i.g w‖ ^ 2

/-- Integrand for complex volume integral -/
def integrand (i : Gronwall f) (w z : ℂ) : ℂ :=
  deriv i.g (w * z) * conj (deriv i.g (w * conj z))

/-- Our volume differences as a complex integral -/
def volume_integral_c (i : Gronwall f) (r s : ℝ) (z : ℂ) : ℂ :=
  ∫ w in annulus_cc 0 r s, i.integrand w z

lemma wz_norm (r1 : 1 < r) (wm : w ∈ annulus_cc 0 r s) (zr : r⁻¹ < ‖z‖) : 1 < ‖w‖ * ‖z‖ := by
  simp only [annulus_cc, mem_sdiff, Metric.mem_closedBall, dist_zero_right, Metric.mem_ball,
    not_lt] at wm zr
  calc ‖w‖ * ‖z‖
    _ > r * r⁻¹ := mul_lt_mul' wm.2 zr (by bound) (by linarith)
    _ = 1 := by rw [mul_inv_cancel₀]; positivity

/-- Our integrand is jointly continuous -/
lemma continuousOn_integrand (i : Gronwall f) (r1 : 1 < r) :
    ContinuousOn (uncurry i.integrand) (annulus_cc 0 r s ×ˢ norm_Ioi r⁻¹) := by
  have gc : ∀ {z}, 1 < ‖z‖ → ContinuousAt (deriv i.g) z :=
    fun {z} z1 ↦ (i.ga z1).deriv.continuousAt
  intro ⟨w,z⟩ ⟨wm,zm⟩
  have wz : 1 < ‖w‖ * ‖z‖ := wz_norm r1 wm zm
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul
  · exact (gc (by simpa)).comp (by fun_prop)
  · apply Complex.continuous_conj.continuousAt.comp
    exact (gc (by simpa)).comp (by fun_prop)

/-- Our integrand is analytic -/
lemma analyticAt_integrand (i : Gronwall f) (r1 : 1 < r) (wm : w ∈ annulus_cc 0 r s)
    (zr : r⁻¹ < ‖z‖) : AnalyticAt ℂ (i.integrand w) z := by
  have da : ∀ z, r⁻¹ < ‖z‖ → AnalyticAt ℂ (fun z ↦ deriv i.g (w * z)) z :=
    fun z zr ↦ (i.ga (by simp [wz_norm r1 wm zr])).deriv.comp (by fun_prop)
  exact (da z zr).mul (da (conj z) (by simpa)).conj_conj

/-- Our integrand is integrable -/
lemma integrable_sq_norm (i : Gronwall f) (r1 : 1 < r) :
    IntegrableOn (fun w ↦ ‖deriv i.g w‖ ^ 2) (annulus_cc 0 r s) := by
  apply ContinuousOn.integrableOn_compact isCompact_annulus_cc
  intro z m
  simp only [annulus_cc, mem_sdiff, Metric.mem_closedBall, dist_zero_right, Metric.mem_ball,
    not_lt] at m
  exact ((i.ga (by linarith)).deriv.continuousAt.norm.pow 2).continuousWithinAt

/-- Our volume integral is analytic -/
lemma analyticOnNhd_integral (i : Gronwall f) (r1 : 1 < r) :
    AnalyticOnNhd ℂ (i.volume_integral_c r s) (norm_Ioi r⁻¹) :=
  AnalyticOnNhd.integral (i.continuousOn_integrand r1)
    (fun x xm z ↦ i.analyticAt_integrand r1 xm) isCompact_annulus_cc (by finiteness) isOpen_norm_Ioi

/-- Write small volumes in terms of integrals -/
lemma small_volume_eq_integral (i : Gronwall f) (r1 : 1 < r) (rs : r ≤ s) :
    volume.real (i.disk s \ i.disk r) = i.volume_integral r s := by
  have r0 : 0 < r := by linarith
  have ie : ∫ z in i.g '' annulus_oc 0 r s, (1 : ℝ) = volume.real (i.g '' annulus_oc 0 r s) • 1 :=
    MeasureTheory.setIntegral_const _
  simp only [smul_eq_mul, mul_one] at ie
  rw [i.disk_diff_disk r1.le rs, ← ie]
  have ga : AnalyticOnNhd ℂ i.g (annulus_cc 0 r s) := i.ga'.mono (annulus_cc_subset_norm_Ioi r1)
  have ga' := ga.mono annulus_oc_subset_annulus_cc
  have gd : ∀ z ∈ annulus_oc 0 r s, HasFDerivWithinAt i.g (fderiv ℝ i.g z) (annulus_oc 0 r s) z :=
    fun z m ↦ (ga' z m).restrictScalars.hasStrictFDerivAt.hasFDerivAt.hasFDerivWithinAt
  have ed : ∀ z ∈ annulus_oc 0 r s, |(fderiv ℝ i.g z).det| = ‖deriv i.g z‖ ^ 2 :=
    fun z m ↦ by simp only [Complex.fderiv_det (ga' z m).differentiableAt, abs_sq]
  have ae : annulus_oc 0 r s =ᵐ[volume] annulus_cc 0 r s := by
    rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
    simp [symmDiff_annulus_oc_annulus_cc rs, MeasureTheory.Measure.addHaar_sphere]
  simp only [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
      measurableSet_annulus_oc (f' := fderiv ℝ i.g) gd
      (i.inj.mono (annulus_oc_subset_norm_Ioi r1.le)), smul_eq_mul, mul_one,
    MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_annulus_oc ed),
    MeasureTheory.setIntegral_congr_set ae,
    volume_integral]

/-- Write small volumes in terms of complex integrals -/
lemma small_volume_eq_integral_c (i : Gronwall f) (r1 : 1 < r) (rs : r ≤ s) (z : ℝ) (z0 : 0 < z) :
    volume.real (i.disk s \ i.disk r) =
      z ^ 2 * i.volume_integral_c (r / z) (s / z) z := by
  have z0' : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z0.ne'
  set u : ℂ → ℂ → ℂ := i.integrand
  have si : ∀ w, ‖deriv i.g w‖ ^ 2 = i.integrand w 1 := by
    intro w
    simp only [mul_one, map_one, integrand, ← real_inner_self_eq_norm_sq, Complex.inner,
      ← Complex.ofReal_pow, Complex.mul_conj, Complex.ofReal_re]
  simp only [i.small_volume_eq_integral r1 rs, volume_integral_c, volume_integral,
    ← MeasureTheory.integral_const_mul, ← Complex.ofRealCLM_apply]
  rw [← ContinuousLinearMap.integral_comp_comm]
  · set t : ℂ → ℂ := fun w ↦ w * z
    have tn : ∀ w, ‖t w‖ = ‖w‖ * z := by simp [t, z0.le]
    have ti : t '' annulus_cc 0 (r / ‖z‖) (s / ‖z‖) = annulus_cc 0 r s := by
      ext a
      simp only [annulus_cc, mem_image, mem_sdiff, Metric.mem_closedBall, dist_zero_right,
        Metric.mem_ball, not_lt, le_div_iff₀ z0, div_le_iff₀ z0, Real.norm_eq_abs, abs_of_pos z0]
      constructor
      · intro ⟨b,⟨bs,rb⟩,ba⟩
        simp only [← tn, ba] at bs rb
        exact ⟨bs, rb⟩
      · intro ⟨u,v⟩
        refine ⟨a / z, ?_⟩
        simp only [t, u, v, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos z0,
          div_mul_cancel₀ _ z0.ne', div_mul_cancel₀ _ z0', and_true]
    have dt : ∀ w, HasDerivAt t z w := fun w ↦ hasDerivAt_mul_const (z : ℂ)
    have dt' := fun w ↦ (dt w).hasFDerivAt.restrictScalars ℝ
    rw [← ti, MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
      (hf' := fun w _ ↦ (dt' w).hasFDerivWithinAt)]
    · simp only [Real.norm_eq_abs, Complex.real_smul, abs_of_pos z0]
      apply congr_arg₂ _ rfl
      ext w
      simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, integrand, t, si]
    · exact measurableSet_annulus_cc
    · exact (mul_left_injective₀ z0').injOn
  · exact i.integrable_sq_norm r1

/-!
### Area within small annuli via analytic continuation

We push the large radius formula down to small radii via analytic continuation.
-/

/-- Real numbers approach their complex target from above -/
lemma map_ofReal_nhdsGT_le_nhds {x : ℝ} : (𝓝[>] x).map (fun z : ℝ ↦ (z : ℂ)) ≤ 𝓝[≠] (x : ℂ) := by
  rw [Filter.map_le_iff_le_comap]
  apply Tendsto.le_comap
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact Filter.Tendsto.mono_left Complex.continuous_ofReal.continuousAt nhdsWithin_le_nhds
  · simp only [mem_compl_iff, mem_singleton_iff, eventually_nhdsWithin_iff, mem_Ioi,
      Complex.ofReal_inj]
    filter_upwards with t lt
    exact lt.ne'

/-- Our large radius formula holds for small radii, complex version -/
lemma small_volume_eq_c (i : Gronwall f) (r1 : 1 < r) :
    ∑' n, i.gronwall_c r n = volume.real (i.disk r) := by
  -- Reduce to an equality of two analytic functions
  have r0 : 0 < r := by positivity
  have ri : 0 < r⁻¹ := by positivity
  obtain ⟨s,large⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop r).and i.large_volume_eq_series)
  have rs := (large s (le_refl _)).1
  replace large := fun t ts ↦ (large t ts).2
  have s0 : 0 < s := by linarith
  have small : ∀ m > r⁻¹, volume.real (i.disk (s * m)) - volume.real (i.disk (r * m)) =
      m ^ 2 * i.volume_integral_c r s m := by
    intro m mr
    have m0 : 0 < m := lt_trans ri mr
    have rm1 : 1 < r * m := by
      calc r * m
        _ > r * r⁻¹ := by bound
        _ = 1 := by rw [mul_inv_cancel₀ r0.ne']
    rw [← Complex.ofReal_sub, ← volume_diff_eq _ rm1 (by bound),
      i.small_volume_eq_integral_c (z := m) rm1 (by bound) (by bound)]
    simp only [mul_div_cancel_right₀ _ m0.ne']
  suffices h : (∑' n, i.gronwall_c s n) - (∑' n, i.gronwall_c r n) =
      volume.real (i.disk s) - volume.real (i.disk r) by
    simpa [large s (le_refl _)] using h
  have small1 := small 1 (by bound)
  simp only [mul_one, Complex.ofReal_one, one_pow, one_mul] at small1
  rw [small1]
  -- Analytic continuation does the rest
  set u : ℂ → ℂ := fun z ↦ (∑' n, i.gronwall_c (s * z) n) - (∑' n, i.gronwall_c (r * z) n) -
    z ^ 2 * i.volume_integral_c r s z
  suffices u1 : u 1 = 0 by
    simp only [mul_one, u, one_pow, one_mul] at u1
    rwa [← sub_eq_zero]
  have ua : AnalyticOnNhd ℂ u (norm_Ioi r⁻¹) := by
    intro z zr
    simp only [norm_Ioi, mem_ofPred_eq] at zr
    have zr' := (inv_lt_iff_one_lt_mul₀' r0).mp zr
    refine AnalyticAt.sub (AnalyticAt.sub ?_ ?_) ?_
    · refine (i.analyticAt_series (lt_of_lt_of_le zr' ?_)).comp (by fun_prop)
      simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos s0]
      bound
    · exact (i.analyticAt_series (by simpa [abs_of_pos r0])).comp (by fun_prop)
    · exact (analyticAt_id.pow 2).mul (i.analyticOnNhd_integral r1 _ zr)
  have u0 : ∃ᶠ z in 𝓝[≠] ((s / r : ℝ) : ℂ), u z = 0 := by
    refine Filter.Frequently.filter_mono ?_ map_ofReal_nhdsGT_le_nhds
    simp only [Filter.frequently_map]
    apply Filter.Eventually.frequently
    simp only [eventually_nhdsWithin_iff]
    filter_upwards with z m
    simp only [mem_Ioi, u, ← Complex.ofReal_mul] at m ⊢
    rw [large, large, small, sub_self]
    · refine lt_trans ?_ m
      rw [div_eq_mul_inv]
      bound
    · rw [div_lt_iff₀ r0] at m
      nlinarith
    · have z1 : 1 ≤ z := le_trans (by bound) m.le
      bound
  have ue : EqOn u 0 (norm_Ioi r⁻¹) := by
    refine ua.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_norm_Ioi ?_ u0
    simp only [norm_Ioi, Complex.ofReal_div, mem_ofPred_eq, Complex.norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos s0, abs_of_pos r0]
    rw [div_eq_mul_inv]
    bound
  apply ue
  simp only [norm_Ioi, mem_ofPred_eq, one_mem, CStarRing.norm_of_mem_unitary]
  bound

/-- Our large radius formula holds for small radii, real version -/
lemma small_volume_sum (i : Gronwall f) (r1 : 1 < r) :
    HasSum (i.gronwall_term r) (volume.real (i.disk r)) := by
  rw [(i.summable_gronwall_term r1).hasSum_iff]
  rw [← Complex.ofReal_inj, ← i.small_volume_eq_c r1, ← Complex.ofRealCLM_apply (∑' _, _),
    ContinuousLinearMap.map_tsum]
  · simp only [Complex.ofRealCLM_apply, ofReal_gronwall_term]
  · exact i.summable_gronwall_term r1

/-!
### Volume in terms of a nonnegative series
-/

/-- The nonnegative terms in the Grönwall series (i.e., without the first term) -/
def gronwall_nonneg (i : Gronwall f) (r : ℝ) (n : ℕ) : ℝ :=
  π * n * ‖i.coeff (n + 1)‖ ^ 2 / r ^ (2 * n)

/-- Volume in terms of a nonnegative series -/
lemma small_volume_sum_nonneg (i : Gronwall f) (r1 : 1 < r) :
    HasSum (i.gronwall_nonneg r) (π * r ^ 2 - volume.real (i.disk r)) := by
  have r0 : 0 < r := by positivity
  have sum := (sum_drop (i.small_volume_sum r1)).neg
  unfold gronwall_nonneg
  simp only [gronwall_term, CharP.cast_eq_zero, sub_zero, mul_one, mul_zero, pow_zero, div_one,
    Nat.cast_add, Nat.cast_one, sub_add_cancel_right, mul_neg, neg_mul, neg_div, mul_div_assoc,
    ← inv_div _ (r ^ 2), ← div_eq_mul_inv, neg_neg, neg_sub, i.coeff_zero, norm_one,
    one_pow] at sum ⊢
  refine sum.congr_fun fun n ↦ ?_
  rw [div_eq_mul_inv _ (r ^ 2), ← pow_sub₀ _ r0.ne' (by omega), mul_add_one, Nat.add_sub_cancel]

/-- Volume in terms of a nonnegative series -/
lemma small_volume_eq_nonneg (i : Gronwall f) (r1 : 1 < r) :
    volume.real (i.disk r) = π * r ^ 2 - ∑' n, i.gronwall_nonneg r n := by
  rw [(i.small_volume_sum_nonneg r1).tsum_eq, sub_sub_cancel]

/-!
### Volume at `r = 1`
-/

/-- Grönwall's series for area at `r = 1` -/
lemma volume_one_sum (i : Gronwall f) :
    HasSum (fun n ↦ π * n * ‖i.coeff (n + 1)‖ ^ 2) (π - volume.real (i.disk 1)) := by
  have np : ∀ n : ℕ, 0 < (n + 1 : ℝ) := fun n ↦ by positivity
  set r : ℕ → ℝ := fun n ↦ 1 + 1 / (n + 1)
  have r1 : ∀ n, 1 < r n := by
    intro n
    simp only [one_div, lt_add_iff_pos_right, inv_pos, r]
    linarith
  have r0 : ∀ n, 0 < r n := by intro n; linarith [r1 n]
  have tv : Tendsto (fun n ↦ volume (i.disk (r n))) atTop (𝓝 (volume (i.disk 1))) := by
    have e : i.disk 1 = ⋂ n, (i.disk (r n)) := by
      apply subset_antisymm
      · simp only [subset_iInter_iff]
        exact fun n ↦ i.disk_subset_disk (by bound)
      · simp only [disk, ← compl_iUnion, compl_subset_compl, outer, ← image_iUnion]
        apply image_mono
        intro z m
        simp only [norm_Ioi, mem_ofPred_eq, mem_iUnion] at m ⊢
        obtain ⟨n, lt⟩ := exists_nat_gt (‖z‖ - 1)⁻¹
        refine ⟨n, ?_⟩
        simp only [r, add_comm (1 : ℝ), ← lt_sub_iff_add_lt, one_div]
        rw [inv_lt_comm₀ (by bound) (by linarith), ← sub_lt_iff_lt_add]
        exact lt_trans (by linarith) lt
    rw [e]
    apply MeasureTheory.tendsto_measure_iInter_atTop
    · exact fun n ↦ (i.measurableSet_disk (r1 _)).nullMeasurableSet
    · exact fun n m nm ↦ i.disk_subset_disk (by bound [np n])
    · use 0; finiteness
  replace tv : Tendsto (fun n ↦ volume.real (i.disk (r n))) atTop (𝓝 (volume.real (i.disk 1))) :=
    (ENNReal.continuousAt_toReal (by finiteness)).tendsto.comp tv
  have tr : Tendsto r atTop (𝓝 1) := by
    rw [← add_zero 1]
    exact tendsto_one_div_add_atTop_nhds_zero_nat.const_add 1
  have rm : ∀ {c}, Tendsto (fun n ↦ c * r n ^ 2) atTop (𝓝 c) := fun {c} ↦ by
    simpa using tendsto_const_nhds.mul (tr.pow 2)
  have rd : ∀ {c k}, Tendsto (fun n ↦ c / r n ^ k) atTop (𝓝 c) := fun {c k} ↦ by
    simpa [Pi.div_def] using tendsto_const_nhds.div (tr.pow k)
  have s := fun n ↦ i.small_volume_sum_nonneg (r1 n)
  have mono : Monotone fun n ↦ i.gronwall_nonneg (r n) := by
    intro n m nm
    simp only [gronwall_nonneg, Pi.le_def]
    intro k
    bound [np n]
  have bound : ∀ k, BddAbove (range fun n ↦ i.gronwall_nonneg (r n) k) := by
    intro k
    simp only [bddAbove_def]
    refine ⟨π * k * ‖i.coeff (k + 1)‖ ^ 2, fun x ⟨n,e⟩ ↦ ?_⟩
    simp only at e
    rw [← e, gronwall_nonneg]
    bound
  have sup : ∀ k, ⨆ n, i.gronwall_nonneg (r n) k = π * k * ‖i.coeff (k + 1)‖ ^ 2 :=
    fun k ↦ tendsto_nhds_unique (tendsto_atTop_ciSup (fun n m nm ↦ by bound) (bound k)) rd
  simp only [← sup]
  exact Real.hasSum_ciSup_of_tendsto s mono bound (rm.sub tv).bddAbove_range (rm.sub tv)

end Gronwall

/-!
### Grönwall's area theorem, standalone version
-/

variable {f : ℂ → ℂ}

/-- The Grönwall area is finite -/
public theorem gronwall_volume_ne_top (fa : AnalyticOnNhd ℂ f (ball 0 1)) (f0 : f 0 = 1)
    (inj : InjOn (fun z ↦ z * f z⁻¹) (norm_Ioi 1)) :
    volume ((fun z ↦ z * f z⁻¹) '' norm_Ioi 1)ᶜ ≠ ⊤ :=
  Gronwall.volume_disk_finite ⟨fa, f0, inj⟩

/-- The Grönwall area has a nice series-/
public theorem gronwall_volume_sum (fa : AnalyticOnNhd ℂ f (ball 0 1)) (f0 : f 0 = 1)
    (inj : InjOn (fun z ↦ z * f z⁻¹) (norm_Ioi 1)) :
    HasSum (fun n ↦ π * n * ‖iteratedDeriv (n + 1) f 0 / (n + 1).factorial‖ ^ 2)
      (π - volume.real ((fun z ↦ z * f z⁻¹) '' norm_Ioi 1)ᶜ) :=
  Gronwall.volume_one_sum ⟨fa, f0, inj⟩

/-- Upper bound on Grönwall's area due to a finite set of terms -/
public theorem gronwall_volume_le (fa : AnalyticOnNhd ℂ f (ball 0 1)) (f0 : f 0 = 1)
    (inj : InjOn (fun z ↦ z * f z⁻¹) (norm_Ioi 1)) (s : Finset ℕ) :
    volume.real ((fun z ↦ z * f z⁻¹) '' norm_Ioi 1)ᶜ ≤
      π - ∑ n ∈ s, π * n * ‖iteratedDeriv (n + 1) f 0 / (n + 1).factorial‖ ^ 2 := by
  linarith [sum_le_hasSum s (by bound) (gronwall_volume_sum fa f0 inj)]

/-- Upper bound on Grönwall's area using second derivative and lower -/
public theorem gronwall_volume_le_two (fa : AnalyticOnNhd ℂ f (ball 0 1)) (f0 : f 0 = 1)
    (inj : InjOn (fun z ↦ z * f z⁻¹) (norm_Ioi 1)) :
    volume.real ((fun z ↦ z * f z⁻¹) '' norm_Ioi 1)ᶜ ≤ π - π * ‖iteratedDeriv 2 f 0 / 2‖ ^ 2 := by
  simpa using gronwall_volume_le fa f0 inj {1}
