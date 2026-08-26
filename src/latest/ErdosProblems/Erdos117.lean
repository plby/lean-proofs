import ErdosProblems.Erdos117.Heisenberg
import ErdosProblems.Erdos117.Compression
import ErdosProblems.Erdos117.FiniteReduction
import ErdosProblems.Erdos117.DerivedCentralizer
import ErdosProblems.Erdos117.FiniteCover
import ErdosProblems.Erdos117.TernaryClique
import ErdosProblems.Erdos117.CosetExtension
import ErdosProblems.Erdos117.Spread
import ErdosProblems.Erdos117.ScalarCliques
import ErdosProblems.Erdos117.TransversalClique
import ErdosProblems.Erdos117.CentralForm
import ErdosProblems.Erdos117.CentralSeries
import ErdosProblems.Erdos117.CentralRecursion
import ErdosProblems.Erdos117.InteractionSpaces
import ErdosProblems.Erdos117.GlobalCoverBound
import ErdosProblems.Erdos117.ErrorEnvelope
import ErdosProblems.Erdos117.LogAsymptotics
import ErdosProblems.Erdos117.BilinearLength
import ErdosProblems.Erdos117.ClassTwoSharp
import ErdosProblems.Erdos117.SharpUpper
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Group.ULift

/-!
# Erdős problem 117: sharp asymptotics for abelian covers

Source problem: https://www.erdosproblems.com/117

Selected claim: Guillaume Lecomte, *Sharp Asymptotics for Abelian Covers of
Groups with Bounded Noncommutativity*, Zenodo record 22033543, v6.
The selected 19-page PDF, dated 20 August 2026, was supplied as an attachment
and inspected directly. The author's arXiv text is also available at
https://arxiv.org/html/2608.20507v1.

The theorem `erdos_117` proves the exponential lower bound,
`log₂ h(n) = n/2 + O(sqrt(n) * log(n+2)^3)`, and the root limit `sqrt(2)`.
The definition of `h` quantifies over all groups, including infinite groups;
its finiteness and characterization as the least universal cover bound are
proved explicitly.

The upper bound follows the scalar-cover and interaction arguments of the
selected source. Its appeal to a general BFC derived-order theorem is
replaced by the proved centralizer-triple reduction in `ClassTwoReduction`.
The needed class-two prime-group derived-order estimate follows from the
bilinear composition-length argument proved in `BilinearLength`.
-/

universe u

namespace Erdos117

open Filter Asymptotics
open scoped Topology

/-- A universal bound for all groups, including infinite groups. -/
def UniversalAbelianCoverBound (n k : ℕ) : Prop :=
  ∀ (G : Type u) [Group G], NoncommutingBound G n → HasAbelianCover G k

/-- The least universal cover bound, with value `⊤` if no finite bound exists.
Using `ℕ∞` avoids assigning zero to an unbounded extremal problem. -/
noncomputable def h (n : ℕ) : ℕ∞ :=
  ⨅ k : {k : ℕ // UniversalAbelianCoverBound.{u} n k}, (k.1 : ℕ∞)

/-- A coarse universal bound, including infinite groups. This establishes
finiteness but does not have the sharp exponential rate. -/
theorem coarse_upper_bound (n : ℕ) :
    UniversalAbelianCoverBound.{u} n (((2 * n) ^ 2) ^ n) := by
  intro G inst hG
  obtain ⟨H, hHgroup, hHfinite, hclique, hcover⟩ := finite_reduction hG
  apply (hcover _).mp
  exact hasAbelianCover_mono hasAbelianCover_centerIndex
    (centerIndex_le ((hclique n).mpr hG))

theorem coarse_upper_bound_h (n : ℕ) :
    h.{u} n ≤ ((((2 * n) ^ 2) ^ n : ℕ) : ℕ∞) := by
  exact iInf_le (fun k : {k : ℕ // UniversalAbelianCoverBound.{u} n k} => (k.1 : ℕ∞))
    ⟨_, coarse_upper_bound n⟩

theorem h_lt_top (n : ℕ) : h.{u} n < ⊤ :=
  (coarse_upper_bound_h n).trans_lt (ENat.natCast_lt_top _)

/-- Any universal upper bound must cover the explicit extraspecial examples. -/
theorem lower_bound_at_odd {m k : ℕ} (hk : UniversalAbelianCoverBound.{u} (2 * m + 1) k) :
    2 ^ m ≤ k := by
  let e : ULift.{u} (Heisenberg m) ≃* Heisenberg m := MulEquiv.ulift
  have hbound := noncommutingBound_mulEquiv e.symm (Heisenberg.noncommutingBound m)
  exact Heisenberg.pow_le_cover_size (hasAbelianCover_mulEquiv e (hk _ hbound))

/-- Discrete form of the lower estimate `log₂ h(n) ≥ n/2 - O(1)`. -/
theorem lower_bound {n k : ℕ} (hn : 1 ≤ n) (hk : UniversalAbelianCoverBound.{u} n k) :
    2 ^ ((n - 1) / 2) ≤ k := by
  let m := (n - 1) / 2
  have hm : 2 * m + 1 ≤ n := by dsimp [m]; omega
  apply lower_bound_at_odd.{u} (m := m)
  intro G inst hG
  exact hk G (noncommutingBound_mono hG hm)

/-- An unconditional lower bound for the extremal function. -/
theorem lower_bound_h {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ ((n - 1) / 2) : ℕ∞) ≤ h.{u} n := by
  apply le_iInf
  intro k
  exact_mod_cast lower_bound hn k.2

/-- The lower half of the claimed sharp logarithmic asymptotic, with an
explicit constant error and the original universal extremal function. -/
theorem lower_log_bound_h {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / 2 - 1 ≤ Real.log (h.{u} n).toNat / Real.log 2 := by
  have hnat : 2 ^ ((n - 1) / 2) ≤ (h.{u} n).toNat := by
    have ht := ENat.toNat_le_toNat (lower_bound_h.{u} hn) (h_lt_top n).ne
    change ENat.toNatHom ((2 : ℕ∞) ^ ((n - 1) / 2)) ≤ (h.{u} n).toNat at ht
    rw [map_pow] at ht
    exact ht
  have hreal : (2 : ℝ) ^ ((n - 1) / 2) ≤ (h.{u} n).toNat := by exact_mod_cast hnat
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hreal
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquot : (((n - 1) / 2 : ℕ) : ℝ) ≤ Real.log (h.{u} n).toNat / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr hlog
  have hfloor : n ≤ 2 * ((n - 1) / 2) + 2 := by omega
  have hfloor' : (n : ℝ) ≤ 2 * (((n - 1) / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast hfloor
  linarith

/-- The finite extremal value is itself a universal cover bound. -/
theorem h_is_universal_bound (n : ℕ) :
    UniversalAbelianCoverBound.{u} n (h.{u} n).toNat := by
  have : Nonempty {k : ℕ // UniversalAbelianCoverBound.{u} n k} :=
    ⟨⟨_, coarse_upper_bound n⟩⟩
  obtain ⟨k, hk⟩ := ENat.exists_eq_iInf
    (fun k : {k : ℕ // UniversalAbelianCoverBound.{u} n k} => (k.1 : ℕ∞))
  have hnat : k.val = (h.{u} n).toNat := congrArg ENat.toNat hk
  rw [← hnat]
  exact k.property

/-- This identifies the extremal definition with the least bound valid for
every group in the original question. -/
theorem h_le_iff_universal {n k : ℕ} :
    h.{u} n ≤ (k : ℕ∞) ↔ UniversalAbelianCoverBound.{u} n k := by
  constructor
  · intro hnk G _ hG
    exact hasAbelianCover_mono (h_is_universal_bound n G hG)
      (ENat.toNat_le_of_le_natCast hnk)
  · intro hk
    exact iInf_le
      (fun k : {k : ℕ // UniversalAbelianCoverBound.{u} n k} => (k.1 : ℕ∞)) ⟨k, hk⟩

theorem h_toNat_pos {n : ℕ} (hn : 1 ≤ n) : 0 < (h.{u} n).toNat :=
  (Nat.pow_pos (by decide : 0 < 2)).trans_le (lower_bound hn (h_is_universal_bound n))

/-- An explicit integer cover bound, valid uniformly over all groups. -/
theorem sharp_upper_bound (n : ℕ) :
    UniversalAbelianCoverBound.{u} n
      ⌊Real.exp (Real.log 2 / 2 * n + finiteCoverError n (16 * logScale n ^ 2))⌋₊ := by
  intro G _ hG
  obtain ⟨k, hk, hlog⟩ := exists_cover_logScale hG
  have hk1 := one_le_of_noncommutingBound (noncommutingBound_of_abelianCover hk)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk1)
  apply hasAbelianCover_mono hk
  apply Nat.le_floor
  calc
    (k : ℝ) = Real.exp (Real.log k) := (Real.exp_log hk0).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- The upper logarithmic estimate before replacing the numerical envelope
by its asymptotic form. -/
theorem upper_log_bound_h {n : ℕ} (hn : 1 ≤ n) :
    Real.log (h.{u} n).toNat ≤
      Real.log 2 / 2 * n + finiteCoverError n (16 * logScale n ^ 2) := by
  have hh := h_le_iff_universal.mpr (sharp_upper_bound.{u} n)
  have hnat := ENat.toNat_le_of_le_natCast hh
  have hreal : ((h.{u} n).toNat : ℝ) ≤
      Real.exp (Real.log 2 / 2 * n + finiteCoverError n (16 * logScale n ^ 2)) :=
    (Nat.cast_le.mpr hnat).trans (Nat.floor_le (Real.exp_pos _).le)
  have hpos : (0 : ℝ) < (h.{u} n).toNat := by exact_mod_cast h_toNat_pos hn
  have hlog := Real.log_le_log hpos hreal
  rwa [Real.log_exp] at hlog

theorem eventual_upper_log_bound_h :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      Real.log (h.{u} n).toNat ≤ Real.log 2 / 2 * n +
        C * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) := by
  refine ⟨errorCoefficient 16 * (2 / Real.log 2) ^ 3, ?_, ?_⟩
  · exact mul_nonneg (errorCoefficient_nonneg _) (by positivity)
  filter_upwards [eventually_finiteCoverError_le_log 16, eventually_ge_atTop 1] with n hn hn1
  apply (upper_log_bound_h hn1).trans
  have herr := hn (16 * logScale n ^ 2) le_rfl
  simpa only [mul_assoc] using add_le_add (le_refl (Real.log 2 / 2 * n)) herr

/-- The full sharp logarithmic asymptotic, including both sides of the error. -/
theorem h_log_asymptotic :
    (fun n : ℕ => Real.log (h.{u} n).toNat / Real.log 2 - (n : ℝ) / 2) =O[atTop]
      (fun n : ℕ => Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) := by
  obtain ⟨C, hC, hupper⟩ := eventual_upper_log_bound_h.{u}
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := C / Real.log 2 + 1
  have hD : 1 ≤ D := by
    have hdiv := div_nonneg hC hlog2.le
    dsimp [D]
    linarith
  apply Asymptotics.IsBigO.of_bound D
  filter_upwards [hupper, eventually_ge_atTop 1, eventually_one_le_sqrt_log_cube]
    with n hn hn1 hE
  let E := Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3
  have hE0 : 0 ≤ E := by dsimp [E]; linarith only [hE]
  have hlower := lower_log_bound_h.{u} hn1
  have hupper' : Real.log (h.{u} n).toNat / Real.log 2 ≤
      (n : ℝ) / 2 + (C / Real.log 2) * E := by
    apply (div_le_iff₀ hlog2).mpr
    calc
      _ ≤ Real.log 2 / 2 * n + C * E := hn
      _ = ((n : ℝ) / 2 + (C / Real.log 2) * E) * Real.log 2 := by
        field_simp
  have hDE : 1 ≤ D * E := one_le_mul_of_one_le_of_one_le hD hE
  have hCE : (C / Real.log 2) * E ≤ D * E :=
    mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hE0
  change ‖Real.log (h.{u} n).toNat / Real.log 2 - (n : ℝ) / 2‖ ≤ D * ‖E‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hE0]
  apply abs_le.mpr
  constructor <;> linarith only [hlower, hupper', hDE, hCE]

/-- The extremal abelian-cover number has exponential growth rate `sqrt 2`. -/
theorem h_root_limit :
    Tendsto (fun n : ℕ => ((h.{u} n).toNat : ℝ) ^ (1 / (n : ℝ))) atTop
      (𝓝 (Real.sqrt 2)) := by
  obtain ⟨C, _, hupper⟩ := eventual_upper_log_bound_h.{u}
  apply tendsto_root_of_log_sandwich (C := C)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast h_toNat_pos.{u} hn
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hlow := lower_log_bound_h.{u} hn
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h := (le_div_iff₀ hlog2).mp hlow
    nlinarith only [h]
  · filter_upwards [hupper] with n hn
    simpa only [mul_comm (Real.log 2 / 2) (n : ℝ)] using hn

/-- Erdős problem 117: the universal cover bound is finite, has the sharp
exponential lower bound and logarithmic asymptotic, and has root limit `sqrt 2`.
The quantification in `h` includes arbitrary, possibly infinite groups. -/
theorem erdos_117 :
    (∀ n : ℕ, h.{u} n < ⊤) ∧
    (∀ n : ℕ, 1 ≤ n → (2 ^ ((n - 1) / 2) : ℕ∞) ≤ h.{u} n) ∧
    ((fun n : ℕ => Real.log (h.{u} n).toNat / Real.log 2 - (n : ℝ) / 2) =O[atTop]
      (fun n : ℕ => Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3)) ∧
    Tendsto (fun n : ℕ => ((h.{u} n).toNat : ℝ) ^ (1 / (n : ℝ))) atTop
      (𝓝 (Real.sqrt 2)) :=
  ⟨h_lt_top, fun _ hn => lower_bound_h hn, h_log_asymptotic, h_root_limit⟩

end Erdos117

#print axioms Erdos117.Heisenberg.noncommutingBound
#print axioms Erdos117.Heisenberg.pow_le_cover_size
#print axioms Erdos117.lower_bound_h
#print axioms Erdos117.lower_log_bound_h
#print axioms Erdos117.centralizerIndex_le
#print axioms Erdos117.finite_reduction
#print axioms Erdos117.h_lt_top
#print axioms Erdos117.nilpotent_centralizer_derived
#print axioms Erdos117.centralizerIndex_le_small_power
#print axioms Erdos117.exists_logarithmic_dominating_set
#print axioms Erdos117.exists_ternary_rank_six_clique
#print axioms Erdos117.hasAbelianCover_extension_polynomial
#print axioms Erdos117.exists_isotropic_cover
#print axioms Erdos117.exists_scalar_clique_of_rank
#print axioms Erdos117.exists_ternary_clique_of_rank
#print axioms Erdos117.exists_transversal_clique
#print axioms Erdos117.central_factor_descent
#print axioms Erdos117.AlternatingBicharacter.kernel_index
#print axioms Erdos117.exists_prime_character
#print axioms Erdos117.exists_class_two_branch_cover
#print axioms Erdos117.subgroupImageSpace_rank_loss
#print axioms Erdos117.subgroupImageHom_ker_index
#print axioms Erdos117.interaction_product_inequality
#print axioms Erdos117.expensive_stage_interaction
#print axioms Erdos117.exists_indexed_branch_cover
#print axioms Erdos117.LayeredCliques.total_credit_le
#print axioms Erdos117.CentralBranch.exists_stage_clique
#print axioms Erdos117.CentralBranch.selected_stage_credit_bound
#print axioms Erdos117.CentralBranch.rank_sum_cutoff
#print axioms Erdos117.CentralBranch.rank_sum_optimized
#print axioms Erdos117.exists_class_two_prime_cover
#print axioms Erdos117.hasAbelianCover_pi
#print axioms Erdos117.exists_factor_clique_bounds
#print axioms Erdos117.nilpotentSylowEquiv
#print axioms Erdos117.sum_sqrt_log_cube_le
#print axioms Erdos117.exists_class_two_sylow_cover
#print axioms Erdos117.exists_class_two_cover_bound
#print axioms Erdos117.centralizerIndex_le_two_pow_clog_sq
#print axioms Erdos117.exists_finite_cover_bound
#print axioms Erdos117.eventually_finiteCoverError_le_log
#print axioms Erdos117.tendsto_root_of_log_sandwich
#print axioms Erdos117.bilinearImage_length_le
#print axioms Erdos117.card_eq_pow_moduleLength
#print axioms Erdos117.class_two_derived_card_le
#print axioms Erdos117.class_two_prime_derived_card_le_clique
#print axioms Erdos117.class_two_sharp_upper
#print axioms Erdos117.exists_class_two_subgroup_small_index
#print axioms Erdos117.exists_cover_logScale
#print axioms Erdos117.erdos_117
