module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.PartialSups
public import ErdosProblems.Erdos515.External.Ray.Misc.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Basic
import ErdosProblems.Erdos515.External.Ray.Hartogs.MaxLog
import ErdosProblems.Erdos515.External.Ray.Misc.Topology

/-!
## Norms in a separable metric space as countable sups of linear functionals

In `Subharmonic.lean`, we want to show that `log ‖f z‖` is subharmonic when `f : ℂ → E` is
analytic, where `E` is any separable normed space.  Since countable suprema of subharmonic
functions are subharmonic, we can do this by showing `log (g (f z))` is subharmonic where
`g : E → ℂ` is any linear functional, then expressing `‖f z‖` as a countable suprema over
linear functions.

This file chooses a countable set of linear functions `duals n : E →L[ℂ] ℂ` for this purpose,
such that `‖x‖ = ⨆ n, ‖duals n x‖`.
-/

open Classical
open Filter (atTop)
open Function (curry uncurry)
open Metric (ball closedBall sphere)
open Set (range univ)
open scoped Real NNReal ENNReal Topology ComplexConjugate

noncomputable section

variable {G : Type} [NormedAddCommGroup G]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SecondCountableTopology E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A nonconstructive function which extracts a dual vector `f` exhibiting `f x = ‖x‖` -/
def dualVector (x : E) : E →L[ℂ] ℂ :=
  choose (exists_dual_vector'' ℂ x)

@[bound] lemma dualVector_norm (x : F) : ‖dualVector x‖ ≤ 1 :=
  (choose_spec (exists_dual_vector'' ℂ x)).1

@[bound] lemma dualVector_nnnorm (x : F) : ‖dualVector x‖₊ ≤ 1 :=
  dualVector_norm _

@[simp]
theorem dualVector_apply (x : F) : dualVector x x = ‖x‖ :=
  (choose_spec (exists_dual_vector'' ℂ x)).2

theorem dualVector_le (x y : F) : ‖dualVector x y‖ ≤ ‖y‖ := by
  calc ‖dualVector x y‖
    _ ≤ ‖dualVector x‖ * ‖y‖ := (dualVector x).le_opNorm y
    _ ≤ 1 * ‖y‖ := by bound
    _ = ‖y‖ := by simp only [one_mul]

/-- Dual vectors of a dense subset of `E` -/
public def duals : ℕ → E →L[ℂ] ℂ := fun n ↦ dualVector (TopologicalSpace.denseSeq E n)

/-- Lipschitz 0 functions are constant -/
theorem LipschitzWith.is_const {g : ℝ → ℝ} (g0 : LipschitzWith 0 g) : ∀ x y, g x = g y := by
  intro x y; simpa only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] using g0 x y

/-- `g ‖duals n x‖` is bounded above w.r.t. `n` for any monotone `g` -/
theorem duals_bddAbove {g : ℝ → ℝ} (gm : Monotone g) (x : E) :
    BddAbove (range fun n ↦ g ‖duals n x‖) := by
  rw [bddAbove_def]; use g ‖x‖
  simp only [Set.mem_range, forall_exists_index]
  intro _ _ h; rw [←h]; apply gm; apply dualVector_le

/-- One-sided Lipschitz bounds on the reals -/
theorem LipschitzWith.le {f : G → ℝ} {k : ℝ≥0} (fk : LipschitzWith k f) (x y : G) :
    f x ≤ f y + k * dist x y := by
  calc f x
    _ = f y + (f x - f y) := by ring_nf
    _ ≤ f y + |f x - f y| := by bound
    _ = f y + dist (f x) (f y) := by rw [Real.dist_eq]
    _ ≤ f y + k * dist x y := by linarith [fk.dist_le_mul x y]

/-- Norms are suprs over `duals` (version with an arbitrary monotone + Lipschitz function) -/
theorem norm_eq_duals_supr' {g : ℝ → ℝ} {k : NNReal} (gm : Monotone g) (gk : LipschitzWith k g)
    (x : E) : g ‖x‖ = ⨆ n, g ‖duals n x‖ := by
  by_cases k0 : k = 0; · rw [k0] at gk; have g0 := gk.is_const 0; simp only [← g0 _, ciSup_const]
  have kp : 0 < (k : ℝ) := by simp only [NNReal.coe_pos]; exact Ne.bot_lt k0
  apply le_antisymm
  · apply le_of_forall_pos_le_add; intro e ep
    rcases Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq E)
      x (e / 2 / k) (by bound) with ⟨n, nx⟩
    generalize hy : TopologicalSpace.denseSeq E n = y; rw [hy] at nx
    have hn : duals n = dualVector y := by rw [← hy, duals]
    have h := le_ciSup (duals_bddAbove gm x) n
    generalize hs : ⨆ n, g ‖duals n x‖ = s
    simp_rw [hs, hn] at h; clear hs hn hy
    have gk' : LipschitzWith k fun x ↦ g ‖dualVector y x‖ := by
      have k11 : (k : ℝ≥0) = k * 1 * 1 := by norm_num
      rw [k11]
      apply (gk.comp lipschitzWith_one_norm).comp
      exact (dualVector y).lipschitz.weaken (dualVector_nnnorm y)
    calc g ‖x‖
      _ ≤ g ‖y‖ + k * 1 * dist x y := (gk.comp lipschitzWith_one_norm).le x y
      _ ≤ g ‖y‖ + k * 1 * (e / 2 / k) := by bound
      _ = g ‖y‖ + k / k * e / 2 := by ring
      _ ≤ g ‖y‖ + 1 * e / 2 := by bound
      _ = g ‖y‖ + e / 2 := by simp only [one_mul]
      _ = g ‖dualVector y y‖ + e / 2 := by
        simp only [dualVector_apply, Complex.norm_real, norm_norm]
      _ ≤ g ‖dualVector y x‖ + k * dist y x + e / 2 := by bound [gk'.le]
      _ ≤ s + k * dist y x + e / 2 := by linarith
      _ = s + k * dist x y + e / 2 := by rw [dist_comm]
      _ ≤ s + k * (e / 2 / k) + e / 2 := by bound
      _ = s + k / k * e / 2 + e / 2 := by ring_nf
      _ ≤ s + 1 * e / 2 + e / 2 := by bound
      _ = s + e := by ring_nf
  · apply ciSup_le; intro n; apply gm; apply dualVector_le

/-- Norms are suprs over `duals` -/
theorem norm_eq_duals_iSup (x : E) : ‖x‖ = ⨆ n, ‖duals n x‖ := by
  have h := norm_eq_duals_supr' (@monotone_id ℝ _) LipschitzWith.id x
  simpa only [id_eq] using h

/-- Norms are suprs over `duals` (`maxLog` version) -/
theorem maxLog_norm_eq_duals_iSup (b : ℝ) (x : E) : maxLog b ‖x‖ = ⨆ n, maxLog b ‖duals n x‖ :=
  norm_eq_duals_supr' (monotone_maxLog b) (LipschitzWith.maxLog b) x

/-- Rewrite a `ℕ` supr into a monotonic limit -/
theorem Csupr.has_lim (s : ℕ → ℝ) (ba : BddAbove (range s)) :
    Filter.Tendsto (fun n ↦ partialSups s n) atTop (𝓝 (⨆ n, s n)) := by
  rw [Metric.tendsto_atTop]; intro e ep
  generalize hb : (⨆ n, s n) - e = b
  have bs : b < ⨆ n, s n := by rw [← hb]; exact sub_lt_self _ (by linarith)
  rcases exists_lt_of_lt_ciSup bs with ⟨N, sN⟩
  use N; intro n nN; rw [Real.dist_eq]; rw [abs_lt]; constructor
  · simp only [neg_lt_sub_iff_lt_add]; simp only [←hb] at sN
    calc iSup s
      _ = iSup s - e + e := by ring
      _ < s N + e := by linarith
      _ ≤ partialSups s n + e := by linarith [le_partialSups_of_le s nN]
      _ = e + partialSups s n := by ring
  · have rs : partialSups s n ≤ iSup s := partialSups_le _ _ _ fun a _ ↦ le_ciSup ba a
    calc partialSups s n - iSup s
      _ ≤ iSup s - iSup s := by linarith
      _ = 0 := by ring
      _ < e := ep

/-- Partial sups of `maxLog b ‖duals k x‖` converge to `maxLog b ‖x‖` -/
public theorem duals_lim_tendsto_maxLog_norm (b : ℝ) (x : E) :
    Filter.Tendsto (partialSups fun k ↦ maxLog b ‖duals k x‖) atTop (𝓝 (maxLog b ‖x‖)) := by
  rw [maxLog_norm_eq_duals_iSup]; exact Csupr.has_lim _ (duals_bddAbove (monotone_maxLog _) _)

/-- Partial sups of `maxLog b ‖duals k x‖` converge to `maxLog b ‖x‖` -/
theorem maxLog_norm_eq_duals_limUnder (b : ℝ) (x : E) :
    maxLog b ‖x‖ = Filter.limUnder atTop (partialSups fun k ↦ maxLog b ‖duals k x‖) :=
  haveI a := duals_lim_tendsto_maxLog_norm b x
  tendsto_nhds_unique a (tendsto_nhds_limUnder ⟨_, a⟩)
