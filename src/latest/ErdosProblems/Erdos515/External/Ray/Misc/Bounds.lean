module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import ErdosProblems.Erdos515.External.Ray.Misc.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.MetricSpace.Basic
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Finset

/-!
## Assorted bound lemmas
-/

open Classical
open Complex (exp log I slitPlane)
open Filter (atTop)
open scoped Real NNReal Topology symmDiff

variable {α : Type}
variable {M : Type} [AddCommMonoid M]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type} [NormedAddCommGroup G]

public lemma late_iff_disjoint_range {m : ℕ} {A : Finset ℕ} :
    Late A m ↔ Disjoint A (Finset.range m) := by
  simp only [Late, ge_iff_le, Finset.disjoint_iff_ne, Finset.mem_range, ne_eq]; constructor
  · intro h n na b bm; linarith [h _ na]
  · intro h n na; specialize h n na n; simpa [not_true, imp_false, not_lt] using h

public lemma sdiff_late {m : ℕ} {B : Finset ℕ} (A : Finset ℕ) :
    B ≥ Finset.range m → Late (A \ B) m := by
  intro Bm n nAB
  rw [Finset.mem_sdiff] at nAB
  by_contra h; simp only [not_le] at h
  have nr := Finset.mem_range.mpr h
  have nB := Finset.mem_of_subset Bm nr
  exact nAB.2 nB

/-- Summing a subset of a geometric series is ≤ the series sum -/
public theorem partial_geometric_bound {a : ℝ} (N : Finset ℕ) (a0 : 0 ≤ a) (a1 : a < 1) :
    N.sum (fun n ↦ a^n) ≤ (1 - a)⁻¹ :=
  haveI pos : ∀ n, n ∉ N → 0 ≤ a^n := by intro n _; bound
  sum_le_hasSum N pos (hasSum_geometric_of_lt_one a0 a1)

public theorem partial_scaled_geometric_bound {a : ℝ} (c : ℝ≥0) (N : Finset ℕ) (a0 : 0 ≤ a)
    (a1 : a < 1) : N.sum (fun n ↦ (c:ℝ) * a^n) ≤ c * (1 - a)⁻¹ := by
  rw [←Finset.mul_sum]
  bound [partial_geometric_bound N a0 a1]

/-- Summing a late part of a series is equivalent to summing a shifted series -/
theorem late_series_sum {m : ℕ} {N : Finset ℕ} (h : Late N m) (f : ℕ → ℝ) :
    N.sum f = (N.image (fun n ↦ n - m)).sum (fun n ↦ f (n + m)) := by
  set Ns := Finset.image (fun n ↦ n - m) N
  have NNs : N = Finset.image (fun n ↦ n + m) Ns := by
    apply Finset.ext; intro k
    rw [Finset.image_image, Finset.mem_image]
    simp only [Function.comp_apply]
    apply Iff.intro
    · intro kN; exists k; apply And.intro
      assumption; exact Nat.sub_add_cancel (h k kN)
    · intro ha; rcases ha with ⟨a, aN, ak⟩
      rw [Nat.sub_add_cancel (h a aN)] at ak
      rw [← ak]; assumption
  rw [NNs]; apply Finset.sum_image
  intro a _ b _; exact Nat.add_right_cancel

/-- late_series_sum, but forgetting the image set -/
theorem late_series_sum' {m : ℕ} {N : Finset ℕ} (h : Late N m) (f : ℕ → ℝ) :
    ∃ M : Finset ℕ, N.sum f = M.sum (fun n ↦ f (n + m)) := by
  exists Finset.image (fun n ↦ n - m) N
  exact late_series_sum h f

public theorem late_geometric_bound {m : ℕ} {a : ℝ} {N : Finset ℕ} (h : Late N m) (a0 : 0 ≤ a)
    (a1 : a < 1) : N.sum (fun n ↦ a^n) ≤ a^m * (1 - a)⁻¹ := by
  rcases late_series_sum' h (fun n ↦ a^n) with ⟨M,L⟩
  rw [L]; clear L
  have pa : (fun n ↦ a^(n + m)) = (fun n ↦ a^n * a^m) := by apply funext; intro n; rw [pow_add]
  calc
    M.sum (fun n ↦ a^(n + m)) = M.sum (fun n ↦ a^n * a^m) := by rw [ pa ]
    _ = M.sum (fun n ↦ a^n) * a^m := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 - a)⁻¹ * a^m := by bound [partial_geometric_bound M a0 a1]
    _ = a^m * (1 - a)⁻¹ := by ring

theorem finset_partition (A B : Finset ℕ) : A = A \ B ∪ A ∩ B := by
  apply Finset.ext
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  intro x; constructor
  · intro a
    by_cases b : x ∈ B
    · right; use a,b
    · left; use a,b
  · intro h
    cases' h with m m
    repeat exact m.1

theorem finset_sum_partition (A B : Finset ℕ) (f : ℕ → M) :
    A.sum f = (A \ B).sum f + (A ∩ B).sum f := by
  have ha : A = A \ B ∪ A ∩ B := finset_partition A B
  nth_rw 1 [ha]
  exact Finset.sum_union (Finset.disjoint_sdiff_inter A B)

theorem sdiff_sdiff_disjoint (A B : Finset ℕ) : Disjoint (A \ B) (B \ A) :=
  Finset.disjoint_of_subset_right Finset.sdiff_subset Finset.sdiff_disjoint

theorem symmDiff_union (A B : Finset ℕ) : A ∆ B = A \ B ∪ B \ A := by
  rw [symmDiff_def, Finset.sup_eq_union]

public theorem symmDiff_bound (A B : Finset ℕ) (f : ℕ → G) :
    dist (A.sum f) (B.sum f) ≤ (A ∆ B).sum (fun n ↦ ‖f n‖) := by
  rw [finset_sum_partition A B f, finset_sum_partition B A f, Finset.inter_comm B A]
  rw [dist_add_right ((A \ B).sum f) ((B \ A).sum f) ((A ∩ B).sum f)]
  rw [dist_eq_norm]
  trans (A \ B).sum (fun n ↦ ‖f n‖) + (B \ A).sum (fun n ↦ ‖f n‖)
  · have ha := finset_norm_sum_le (A \ B) f
    have hb := finset_norm_sum_le (B \ A) f
    calc ‖(A \ B).sum f - (B \ A).sum f‖
      _ ≤ ‖(A \ B).sum f‖ + ‖(B \ A).sum f‖ := by bound
      _ ≤ (A \ B).sum (fun n ↦ ‖f n‖) + (B \ A).sum (fun n ↦ ‖f n‖) := by bound
  · apply le_of_eq
    rw [←Finset.sum_union (sdiff_sdiff_disjoint A B), symmDiff_union]

/-- Symmetric differences of sets containing ranges are late -/
public theorem symmDiff_late {A B : Finset ℕ} {m : ℕ} (ha : A ≥ Finset.range m)
    (hb : B ≥ Finset.range m) : Late (A ∆ B) m := by
  intro n ab
  rw [symmDiff_def, Finset.sup_eq_union, Finset.mem_union] at ab
  by_contra h; simp at h
  cases' ab with a b
  · rw [Finset.mem_sdiff] at a
    have h := Finset.mem_of_subset hb (Finset.mem_range.mpr h)
    exact a.2 h
  · rw [Finset.mem_sdiff] at b
    have h := Finset.mem_of_subset ha (Finset.mem_range.mpr h)
    exact b.2 h

/-- `a - z` has similar absolute value to `a` for small `z` -/
public theorem sub_near (a z : ℂ) : |‖a - z‖ - ‖a‖| ≤ ‖z‖ := by
  rw [abs_le]; constructor
  · simp only [neg_le_sub_iff_le_add]
    exact norm_le_norm_sub_add a z
  · calc
      ‖a - z‖ - ‖a‖ ≤ ‖a‖ + ‖z‖ - ‖a‖ := by bound
      _ = ‖z‖ := by simp only [add_sub_cancel_left]

public theorem add_near (a z : ℂ) : |‖a + z‖ - ‖a‖| ≤ ‖z‖ := by
  have h := sub_near a (-z)
  simp only [sub_neg_eq_add, norm_neg] at h
  assumption

theorem mem_slitPlane_of_near_one' {z : ℂ} (z1 : ‖z - 1‖ ≤ 1) (z0 : z ≠ 0) : z ∈ slitPlane := by
  rw [← sq_le_sq₀ (by bound) (by norm_num)] at z1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re, ← pow_two,
    Complex.sub_im, Complex.one_im, sub_zero, one_pow] at z1
  by_cases i0 : z.im ≠ 0
  · right
    exact i0
  · simp only [ne_eq, Decidable.not_not] at i0
    left
    contrapose z0
    simp [i0, abs_sub_le_iff, Complex.ext_iff] at z0 z1 ⊢
    grind

public theorem mem_slitPlane_of_near_one {z : ℂ} (z1 : ‖z - 1‖ < 1) : z ∈ slitPlane := by
  by_cases z0 : z = 0
  · simp [z0] at z1
  · exact mem_slitPlane_of_near_one' z1.le z0

public theorem near_one_avoids_zero {z : ℂ} : ‖z - 1‖ < 1 → z ≠ 0 := by
  intro h; exact Complex.slitPlane_ne_zero (mem_slitPlane_of_near_one h)

theorem derivWithin.cid {z : ℂ} {s : Set ℂ} (o : IsOpen s) (zs : z ∈ s) :
    derivWithin (fun z ↦ z) s z = 1 :=
  derivWithin_id z s (IsOpen.uniqueDiffWithinAt o zs)

theorem derivWithin.clog {f : ℂ → ℂ} {z : ℂ} {s : Set ℂ} (o : IsOpen s) (zs : z ∈ s)
    (hf : DifferentiableWithinAt ℂ f s z) (hx : (f z).re > 0 ∨ (f z).im ≠ 0) :
    derivWithin (fun z ↦ Complex.log (f z)) s z = derivWithin f s z / f z := by
  have hz := DifferentiableWithinAt.hasDerivWithinAt hf
  have h := HasDerivWithinAt.clog hz hx
  have u := o.uniqueDiffWithinAt (𝕜 := ℂ) zs
  rw [HasDerivWithinAt.derivWithin h u]

theorem weak_log1p_small {z : ℂ} {r : ℝ} (r1 : r < 1) (h : ‖z‖ < r) :
    ‖log (1 + z)‖ ≤ 1/(1 - r) * ‖z‖ := by
  by_cases rp : r ≤ 0
  · have a0 : ‖z‖ < 0 := lt_of_lt_of_le h rp
    have a0' : ‖z‖ ≥ 0 := by bound
    exfalso
    linarith [a0, a0']
  · simp only [not_le] at rp
    have L : ‖log (1 + z) - log 1‖ ≤ 1/(1 - r) * ‖1 + z - 1‖ := by
      generalize hs : Metric.ball (1:ℂ) r = s
      have o : IsOpen s := by rw [← hs]; exact Metric.isOpen_ball
      have s1z : 1 + z ∈ s := by simp [← hs]; assumption
      have s1 : (1:ℂ) ∈ s := by simp [← hs]; assumption
      have sp : ∀ w : ℂ, w ∈ s → w.re > 0 ∨ w.im ≠ 0 := by
        intro w ws
        apply mem_slitPlane_of_near_one
        simp only [Metric.mem_ball, Complex.dist_eq, ← hs] at ws
        calc ‖w - 1‖ < r := by assumption
          _ < 1 := r1
      have sa : ∀ w : ℂ, w ∈ s → ‖w‖ ≥ 1 - r := by
        intro w ws
        simp only [Metric.mem_ball, Complex.dist_eq, ← hs] at ws
        calc ‖w‖ = ‖1 + (w - 1)‖ := by ring_nf
          _ ≥ ‖(1 : ℂ)‖ - ‖w - 1‖ := by bound
          _ ≥ ‖(1 : ℂ)‖ - r := by bound
          _ = 1 - r := by rw [norm_one]
      refine Convex.norm_image_sub_le_of_norm_derivWithin_le ?_ ?_ ?_ s1 s1z
      · exact DifferentiableOn.clog differentiableOn_id sp
      · intro w ws
        rw [derivWithin.clog o ws, derivWithin.cid o ws]
        simp only [one_div, norm_inv]
        rw [inv_le_comm₀]
        have aw := sa w ws; simp at aw; field_simp; linarith
        have aw := sa w ws; linarith; norm_num; assumption
        exact differentiableWithinAt_id
        exact sp w ws
      · rw [← hs]; exact convex_ball _ _
    simp only [Complex.log_one, sub_zero, one_div, add_sub_cancel_left] at L
    simpa only [one_div, ge_iff_le]

public theorem le_of_forall_small_le_add {a b t : ℝ} (tp : 0 < t)
    (h : ∀ e, 0 < e → e < t → a ≤ b + e) : a ≤ b := by
  apply le_of_forall_pos_lt_add
  intro e ep
  by_cases et : e ≥ t
  · specialize h (t/2) (by bound) (by bound)
    calc a ≤ b + t/2 := h
      _ ≤ b + e/2 := by bound
      _ < b + e := by bound
  · simp only [ge_iff_le, not_le] at et
    calc a ≤ b + e/2 := h (e/2) (by bound) (by linarith)
      _ < b + e := by bound

theorem one_over_one_sub_le {x : ℝ} : 0 ≤ x → x ≤ 1/2 → 1/(1 - x) ≤ 1 + 2*x := by
  intro xp xh
  have x1 : 1 - x > 0 := by linarith
  rw [div_le_iff₀ x1]
  calc (1 + 2*x) * (1 - x) = 1 + x * (1 - 2*x) := by ring
    _ ≥ 1 + x * (1 - 2 * (1/2)) := by bound
    _ = 1 := by ring

theorem Metric.continuous_near {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (fc : ContinuousAt f z) (rp : 0 < r)
    : ∀ e, 0 < e → ∃ s, 0 < s ∧ s ≤ r ∧ ∀ {w} , ‖w - z‖ < s → ‖f w - f z‖ < e := by
  intro e ep
  rcases Metric.continuousAt_iff.mp fc e ep with ⟨s,sp,sc⟩
  simp_rw [ Complex.dist_eq ] at sc
  by_cases sr : s ≤ r; exists s
  simp only [not_le] at sr
  exists r
  refine ⟨rp, by bound, ?_⟩
  intro w wr
  refine @sc w ?_
  trans r; assumption; assumption

theorem slightly_smaller {z : ℂ} (nz : z ≠ 0) {r : ℝ} (rp : 0 < r) :
    ∃ w, ‖w - z‖ < r ∧ ‖w‖ < ‖z‖ := by
  by_cases rz : ‖z‖ < r
  · use 0
    simp only [zero_sub, norm_neg, rz, norm_zero, norm_pos_iff, ne_eq, nz, not_false_eq_true,
      and_self]
  simp only [not_lt] at rz
  have azp : 0 < ‖z‖ := norm_pos_iff.mpr nz
  generalize ha : 1 - r/2/‖z‖ = a
  have a0 : 0 ≤ a := by rw [←ha, sub_nonneg, div_le_one azp]; exact _root_.trans (by bound) rz
  have a1 : a < 1 := by rw [←ha, sub_lt_self_iff]; positivity
  generalize hw : ↑a * z = w
  use w; constructor
  · rw [ ←hw, ← ha]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
    rw [mul_sub_right_distrib]
    simp only [one_mul, Complex.ofReal_ofNat, sub_sub_cancel_left, norm_neg, Complex.norm_mul,
      Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rp, Complex.norm_ofNat,
      div_mul (r / 2), div_one, half_lt_self_iff, div_self azp.ne', abs_norm, rp]
  · simp only [← hw, Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg a0]
    exact mul_lt_of_lt_one_left azp a1

/-- There are smaller values nearby any z ≠ 0 -/
public theorem frequently_smaller {z : ℂ} (z0 : z ≠ 0) : ∃ᶠ w : ℂ in 𝓝 z, ‖w‖ < ‖z‖ := by
  simp only [Filter.Frequently, Metric.eventually_nhds_iff, not_exists, not_forall, not_not,
    Complex.dist_eq, not_and]
  intro r rp; rcases slightly_smaller z0 rp with ⟨w, b, lt⟩; use w, b, lt

theorem weak_to_strong_small {f : ℂ → ℂ} {z : ℂ} {r c : ℝ} (rp : 0 < r) (cp : 0 < c)
    (zr : ‖z‖ ≤ r) (fc : ContinuousAt f z) (h : ∀ z : ℂ, ‖z‖ < r → ‖f z‖ ≤ c * ‖z‖) :
    ‖f z‖ ≤ c * ‖z‖ := by
  by_cases nz : z = 0; · refine h z ?_; rw [nz]; simpa
  apply le_of_forall_small_le_add zero_lt_one
  intro e ep _
  rcases Metric.continuous_near fc rp e ep with ⟨s,sp,_,sc⟩
  rcases slightly_smaller nz sp with ⟨w,wz,awz⟩
  have wr : ‖w‖ < r := lt_of_lt_of_le awz zr
  calc ‖f z‖ = ‖f w - (f w - f z)‖ := by ring_nf
    _ ≤ ‖f w‖ + ‖f w - f z‖ := by bound
    _ ≤ c * ‖w‖ + e := by bound [h w wr, sc wz]
    _ ≤ c * ‖z‖ + e := by bound

theorem log1p_small' {z : ℂ} {r : ℝ} (r1 : r < 1) (zr : ‖z‖ ≤ r) :
    ‖log (1 + z)‖ ≤ 1 / (1 - r) * ‖z‖ := by
  by_cases r0 : r ≤ 0
  · have z0 := le_antisymm (le_trans zr r0) (norm_nonneg z)
    simp only [norm_eq_zero] at z0
    simp only [z0, add_zero, Complex.log_one, norm_zero, one_div, mul_zero, le_refl]
  simp only [not_le] at r0
  have fc : ContinuousAt (fun z ↦ log (1 + z)) z := by
    apply ContinuousAt.clog; apply ContinuousAt.add; exact continuousAt_const; exact continuousAt_id
    refine mem_slitPlane_of_near_one ?_
    simp only [add_sub_cancel_left, lt_of_le_of_lt zr r1]
  apply weak_to_strong_small r0 (by bound) zr fc
  intro w wr
  exact @weak_log1p_small w r (by bound) wr

theorem log1p_small {z : ℂ} (zs : ‖z‖ ≤ 1/2) : ‖log (1 + z)‖ ≤ 2 * ‖z‖ :=
  le_trans (log1p_small' (by norm_num) zs) (le_of_eq (by norm_num))

/-- `log (1+x)` is small for small `x` -/
theorem Real.log1p_small' {x r : ℝ} (r1 : r < 1) (xr : |x| ≤ r) :
    |Real.log (1 + x)| ≤ 1 / (1-r) * |x| := by
  set z := (x : ℂ)
  have zx : ‖z‖ = |x| := by simp only [Complex.norm_real, norm_eq_abs, z]
  simp only [← Complex.log_ofReal_re, ← zx] at xr ⊢
  refine _root_.trans (_root_.trans (Complex.abs_re_le_norm _) ?_) (_root_.log1p_small' r1 xr)
  simp only [Complex.ofReal_add, Complex.ofReal_one, le_refl, z]

/-- `log (1+x)` is small for small `x` -/
theorem Real.log1p_small {x : ℝ} (xr : |x| ≤ 1/2) : |Real.log (1 + x)| ≤ 2 * |x| :=
  le_trans (Real.log1p_small' (by norm_num) xr) (le_of_eq (by norm_num))

/-- `log z` is small for `z ≈ 1` -/
public theorem log_small {z : ℂ} (zs : ‖z - 1‖ ≤ 1 / 2) : ‖log z‖ ≤ 2 * ‖z - 1‖ := by
  generalize zw : z - 1 = z1; have wz : z = 1 + z1 := by rw [← zw]; ring
  rw [wz]; refine log1p_small ?_; rw [← zw]; assumption

theorem weak_exp_small' {z : ℂ} {r : ℝ} (zr : ‖z‖ < r) (r1 : r ≤ 1) :
    ‖exp z - 1‖ ≤ (1 + r) * ‖z‖ := by
  have r0 : 0 ≤ r := le_trans (norm_nonneg _) zr.le
  have L := Complex.locally_lipschitz_exp r0 r1 0 z (by simpa only [sub_zero])
  simpa only [Complex.exp_zero, norm_one, mul_one, sub_zero] using L

theorem weak_exp_small {z : ℂ} (h : ‖z‖ < 1) : ‖exp z - 1‖ ≤ 2 * ‖z‖ := by
  have L := weak_exp_small' h (by norm_num)
  norm_num at L
  exact L

/-- `exp z ≈ 1` for `z ≈ 0` -/
theorem exp_small' {z : ℂ} {r : ℝ} (zs : ‖z‖ ≤ r) (r1 : r ≤ 1) : ‖exp z - 1‖ ≤ (1 + r) * ‖z‖ := by
  by_cases z0 : z = 0
  · simp [z0]
  have r0 : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr z0) zs
  have cp : 0 < 1 + r := by linarith
  have fc : ContinuousAt (fun z ↦ exp z - 1) z := by
    apply ContinuousAt.sub; apply ContinuousAt.cexp
    exact continuousAt_id; exact continuousAt_const
  apply weak_to_strong_small r0 cp zs fc
  intro w wr
  exact weak_exp_small' wr r1

/-- `exp z ≈ 1` for `z ≈ 0` -/
theorem exp_small {z : ℂ} (zs : ‖z‖ ≤ 1) : ‖exp z - 1‖ ≤ 2 * ‖z‖ := by
  have s := exp_small' zs (by norm_num)
  norm_num at s
  exact s

/-- `exp_small'`, but for any ball -/
lemma exp_small_general {z : ℂ} {r : ℝ} (zs : ‖z‖ ≤ r) : ‖exp z - 1‖ ≤ Real.exp r * ‖z‖ := by
  have b := Complex.norm_exp_sub_sum_le_norm_mul_exp z 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    ne_eq, one_ne_zero, not_false_eq_true, div_self, pow_one, mul_comm ‖z‖] at b
  exact le_trans b (by bound)

@[bound] public lemma psg_nonzero {r s : ℝ} (r1 : r ≤ 1) : 0 ≤ psg r s := by
  unfold psg
  bound

public theorem pow1p_small_general {z w : ℂ} {r s : ℝ} (zr : ‖z‖ ≤ r) (ws : ‖w‖ ≤ s) (r1 : r < 1)  :
    ‖(1 + z) ^ w - 1‖ ≤ psg r s * ‖z‖ * ‖w‖ := by
  by_cases z0 : z = 0
  · simp [z0]
  have r0 : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr z0) zr
  have s0 : 0 ≤ s := le_trans (norm_nonneg _) ws
  have z1 : 1 + z ≠ 0 := by
    rw [← norm_pos_iff]
    calc ‖1 + z‖ ≥ ‖(1 : ℂ)‖ - ‖z‖ := by bound
      _ ≥ ‖(1 : ℂ)‖ - r := by bound
      _ > 0 := by simp only [norm_one, sub_pos, r1]
  rw [Complex.cpow_def_of_ne_zero z1]
  have ls := log1p_small' r1 zr
  have eas : ‖log (1 + z) * w‖ ≤ r * s / (1 - r) := by
    rw [Complex.norm_mul]
    calc ‖log (1 + z)‖ * ‖w‖ ≤ 1 / (1 - r) * ‖z‖ * s := by bound
      _ ≤ 1 / (1 - r) * r * s := by bound
      _ = _ := by ring
  have es := exp_small_general eas
  rw [Complex.norm_mul, ← mul_assoc] at es
  refine le_trans es ?_
  grw [ls]
  simp only [psg]
  apply le_of_eq
  grind

theorem pow1p_small' {z w : ℂ} {r s : ℝ} (zr : ‖z‖ ≤ r) (ws : ‖w‖ ≤ s) (r1 : r < 1)
    (rs1 : r * s ≤ 1 - r) :
    ‖(1 + z) ^ w - 1‖ ≤ (1 - r + r * s) / (1 - r) ^ 2 * ‖z‖ * ‖w‖ := by
  by_cases z0 : z = 0
  · simp [z0]
  have r0 : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr z0) zr
  have s0 : 0 ≤ s := le_trans (norm_nonneg _) ws
  have z1 : 1 + z ≠ 0 := by
    rw [← norm_pos_iff]
    calc ‖1 + z‖ ≥ ‖(1 : ℂ)‖ - ‖z‖ := by bound
      _ ≥ ‖(1 : ℂ)‖ - r := by bound
      _ > 0 := by simp only [norm_one, sub_pos, r1]
  rw [Complex.cpow_def_of_ne_zero z1]
  have ls := log1p_small' r1 zr
  have eas : ‖log (1 + z) * w‖ ≤ r * s / (1 - r) := by
    rw [Complex.norm_mul]
    calc ‖log (1 + z)‖ * ‖w‖ ≤ 1 / (1 - r) * ‖z‖ * s := by bound
      _ ≤ 1 / (1 - r) * r * s := by bound
      _ = _ := by ring
  have es := exp_small' eas (by rw [div_le_iff₀ (by bound)]; linarith)
  rw [Complex.norm_mul, ← mul_assoc] at es
  refine le_trans es ?_
  grw [ls]
  · apply le_of_eq
    grind
  · bound

public theorem pow1p_small {z w : ℂ} (zs : ‖z‖ ≤ 1/2) (ws : ‖w‖ ≤ 1) :
    ‖(1 + z) ^ w - 1‖ ≤ 4 * ‖z‖ * ‖w‖ := by
  have L := pow1p_small' zs ws (by norm_num) (by bound)
  norm_num at L
  exact L

/-- `‖z^w - 1‖ = O(‖z - 1‖ * ‖w‖)` for `z ≈ 1`, `w` small -/
theorem pow_small' {z w : ℂ} {r s : ℝ} (zr : ‖z - 1‖ ≤ r) (ws : ‖w‖ ≤ s) (r1 : r < 1)
    (rs1 : r * s ≤ 1 - r) :
    ‖z ^ w - 1‖ ≤ (1 - r + r * s) / (1 - r) ^ 2 * ‖z - 1‖ * ‖w‖ := by
  generalize zw : z - 1 = z1
  have wz : z = 1 + z1 := by rw [← zw]; ring
  exact wz ▸ pow1p_small' (by rwa [← zw]) ws r1 rs1

/-- `‖z^w - 1‖ = O(‖z - 1‖ * ‖w‖)` for `z ≈ 1`, `w` small -/
public theorem pow_small_general {z w : ℂ} {r s : ℝ} (zr : ‖z - 1‖ ≤ r) (ws : ‖w‖ ≤ s) (r1 : r < 1) :
    ‖z ^ w - 1‖ ≤ psg r s * ‖z - 1‖ * ‖w‖ := by
  generalize zw : z - 1 = z1
  have wz : z = 1 + z1 := by rw [← zw]; ring
  exact wz ▸ pow1p_small_general (by rwa [← zw]) ws r1

/-- `‖z^w - 1‖ ≤ 4 * ‖z - 1‖ * ‖w‖` for `z ≈ 1`, `w` small -/
public theorem pow_small {z w : ℂ} (zs : ‖z - 1‖ ≤ 1 / 2) (ws : ‖w‖ ≤ 1) :
    ‖z ^ w - 1‖ ≤ 4 * ‖z - 1‖ * ‖w‖ := by
  generalize zw : z - 1 = z1
  have wz : z = 1 + z1 := by rw [← zw]; ring
  exact wz ▸ pow1p_small (by rwa [← zw]) ws

/-- `a + b ≠ 0` from `abs b < abs a` -/
public theorem add_ne_zero_of_abs_lt {a b : ℂ} (h : ‖b‖ < ‖a‖) : a + b ≠ 0 := by
  have e : a + b = a - -b := by abel
  rw [e, sub_ne_zero]
  contrapose h
  simp only [h, not_lt, norm_neg, le_refl]

/-- `e < 3` -/
public theorem Real.exp_one_lt_3 : Real.exp 1 < 3 :=
  _root_.trans Real.exp_one_lt_d9 (by norm_num)

public theorem log_add (a b : ℝ) (a0 : 0 < a) (ab0 : 0 < a + b) :
    Real.log (a + b) = Real.log a + Real.log (1 + b/a) := by
  have d0 : 0 < 1 + b/a := by field_simp [a0.ne']; bound
  rw [←Real.log_mul a0.ne' d0.ne', left_distrib, mul_one, mul_div_cancel₀ _ a0.ne']

/-- `log (abs (a + b)) = log (abs a) + log (abs (1 + b/a))` -/
public theorem log_abs_add (a b : ℂ) (a0 : a ≠ 0) (ab0 : a + b ≠ 0) :
    Real.log (‖a + b‖) = Real.log (‖a‖) + Real.log (‖1 + b/a‖) := by
  have d0 : 1 + b/a ≠ 0 := by field_simp [a0, ab0]; exact div_ne_zero ab0 a0
  have a0' : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr a0
  have d0' : ‖1 + b / a‖ ≠ 0 := norm_ne_zero_iff.mpr d0
  rw [←Real.log_mul a0' d0', ← Complex.norm_mul, left_distrib, mul_one, mul_div_cancel₀ _ a0]

/-- `e^(1/4) ≤ 4/3` -/
theorem Real.exp_forth_lt_four_thirds : Real.exp (1/4) < 4/3 := by
  rw [←Real.exp_one_rpow, one_div, ←@Real.pow_rpow_inv_natCast (4/3) 4 (by norm_num) (by norm_num)]
  refine Real.rpow_lt_rpow (Real.exp_pos _).le ?_ (by norm_num)
  exact _root_.trans Real.exp_one_lt_d9 (by norm_num)

/-- Bound `abs (product - 1)` in terms of `abs (sum)` -/
public theorem dist_prod_one_le_abs_sum {f : ℕ → ℂ} {s : Finset ℕ} {c : ℝ}
    (le : s.sum (fun n ↦ ‖f n - 1‖) ≤ c) (c1 : c ≤ 1/2) : ‖s.prod f - 1‖ ≤ 4 * c := by
  set g := fun n ↦ Complex.log (f n)
  have b : ∀ n, n ∈ s → ‖f n - 1‖ ≤ c := by
    intro n m; refine _root_.trans ?_ le
    exact Finset.single_le_sum (f := fun n ↦ ‖f n - 1‖) (fun _ _ ↦ norm_nonneg _) m
  have f0 : ∀ n, n ∈ s → f n ≠ 0 := by
    intro n m; specialize b n m; contrapose b
    simp only [b, not_le]; norm_num; linarith
  have sg : ‖s.sum g‖ ≤ 2 * c := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n m ↦ log_small (le_trans (b n m) c1))) ?_
    rw [← Finset.mul_sum]; bound
  have e : s.prod f = Complex.exp (s.sum g) := by
    rw [Complex.exp_sum]; apply Finset.prod_congr rfl
    intro n m; rw [Complex.exp_log (f0 n m)]
  rw [e]; exact _root_.trans (exp_small (by linarith)) (by linarith)

/-- If `z, w` are close, then `0 < (z⁻¹ * w).re` -/
public lemma re_mul_inv_pos_of_close {z w : ℂ} (wz : ‖w - z‖ < ‖z‖) : 0 < (z⁻¹ * w).re := by
  have z0 : z ≠ 0 := norm_ne_zero_iff.mp (lt_of_le_of_lt (by bound) wz).ne'
  have h : ‖z⁻¹ * w - 1‖ < 1 := by
    nth_rw 1 [← inv_mul_cancel₀ z0]
    simp only [← mul_sub, norm_mul, norm_inv]
    simp only [← div_eq_inv_mul]
    bound [norm_pos_iff.mpr z0]
  generalize z⁻¹ * w = x at h
  rw [norm_sub_rev] at h
  simpa only [Complex.sub_re, Complex.one_re, sub_lt_self_iff] using
    lt_of_le_of_lt (Complex.re_le_norm _) h
