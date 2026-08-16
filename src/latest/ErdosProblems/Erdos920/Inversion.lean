/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Analytic inversion for Erdős Problem 920

This file isolates the analytic part of the Ramsey-to-chromatic argument.  It
contains no graph theory: `ramsey` is an abstract natural-valued function and
`f` is an abstract real-valued lower-bound target.  The hypotheses are exactly
the eventual Bradač-shaped Ramsey estimate and the elementary bridge from a
strict Ramsey inequality to a lower bound for `f`.

We deliberately use the slightly oversized inverse scale

`D * n ^ (1 / a) * (log n) ^ 2`.

It loses only a factor `(log n) ^ 2` and makes the inversion uniform in `a`.
-/

namespace Erdos920.Inversion

open Filter Asymptotics

noncomputable def inverseScale (a : ℕ) (D : ℝ) (n : ℕ) : ℝ :=
  D * (n : ℝ) ^ (1 / (a : ℝ)) * Real.log (n : ℝ) ^ 2

noncomputable def inverseIndex (a : ℕ) (D : ℝ) (n : ℕ) : ℕ :=
  ⌈inverseScale a D n⌉₊

private lemma rpow_inv_nat_pow {a n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    ((n : ℝ) ^ (1 / (a : ℝ))) ^ a = n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  rw [show 1 / (a : ℝ) * (a : ℝ) = 1 by field_simp, Real.rpow_one]

private lemma inverseScale_pow {a n : ℕ} {D : ℝ} (ha : 0 < a) (hn : 0 < n) :
    inverseScale a D n ^ a =
      D ^ a * (n : ℝ) * Real.log (n : ℝ) ^ (2 * a) := by
  rw [inverseScale, mul_pow, mul_pow, rpow_inv_nat_pow ha hn, ← pow_mul]

theorem eventually_two_mul_inverseScale_le (a : ℕ) (ha : 2 ≤ a)
    (D : ℝ) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop, 2 * inverseScale a D n ≤ (n : ℝ) := by
  let δ : ℝ := 1 - 1 / (a : ℝ)
  have haR : (1 : ℝ) < a := by exact_mod_cast ha
  have hδ : 0 < δ := by
    dsimp [δ]
    rw [sub_pos, div_lt_one (by positivity)]
    exact haR
  have hlittle :
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ δ) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hδ).natCast_atTop
  have hcoefficient : 0 < (2 * D)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hD)
  have hsmall := hlittle.bound hcoefficient
  filter_upwards [hsmall, eventually_ge_atTop 3] with n hnsmall hn3
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsmall' :
      Real.log (n : ℝ) ^ 2 ≤ (2 * D)⁻¹ * (n : ℝ) ^ δ := by
    simpa [Real.norm_eq_abs, Real.rpow_two, abs_of_pos hlogpos,
      abs_of_nonneg (Real.rpow_nonneg hnpos.le δ)] using hnsmall
  calc
    2 * inverseScale a D n =
        (2 * D * (n : ℝ) ^ (1 / (a : ℝ))) * Real.log (n : ℝ) ^ 2 := by
          rw [inverseScale]
          ring
    _ ≤ (2 * D * (n : ℝ) ^ (1 / (a : ℝ))) *
        ((2 * D)⁻¹ * (n : ℝ) ^ δ) := by
          exact mul_le_mul_of_nonneg_left hsmall' (by positivity)
    _ = (n : ℝ) ^ (1 / (a : ℝ)) * (n : ℝ) ^ δ := by
          field_simp [ne_of_gt hD]
    _ = (n : ℝ) ^ (1 / (a : ℝ) + δ) := by
          rw [Real.rpow_add hnpos]
    _ = (n : ℝ) := by
          simp [δ]

theorem tendsto_inverseIndex_atTop (a : ℕ) (ha : 0 < a)
    (D : ℝ) (hD : 1 ≤ D) :
    Tendsto (inverseIndex a D) atTop atTop := by
  have haR : (0 : ℝ) < 1 / (a : ℝ) := by positivity
  have hroot :
      Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / (a : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop haR).comp tendsto_natCast_atTop_atTop
  have hlog :
      ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hcomparison :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ (1 / (a : ℝ)) ≤ (inverseIndex a D n : ℝ) := by
    filter_upwards [hlog, eventually_ge_atTop 1] with n hnlog hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hroot_nonneg : 0 ≤ (n : ℝ) ^ (1 / (a : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc
      (n : ℝ) ^ (1 / (a : ℝ)) =
          1 * (n : ℝ) ^ (1 / (a : ℝ)) * 1 := by ring
      _ ≤ D * (n : ℝ) ^ (1 / (a : ℝ)) * Real.log (n : ℝ) ^ 2 := by
        gcongr
        nlinarith [sq_nonneg (Real.log (n : ℝ) - 1)]
      _ = inverseScale a D n := rfl
      _ ≤ (inverseIndex a D n : ℝ) := Nat.le_ceil _
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  exact tendsto_atTop_mono' atTop hcomparison hroot

private lemma scaled_inverseScale_quotient {a n : ℕ} {A D : ℝ}
    (ha : 2 ≤ a) (hn : 0 < n) (hlog : 0 < Real.log (n : ℝ)) :
    A * inverseScale a D n ^ a / Real.log (n : ℝ) ^ (2 * a - 2) =
      A * D ^ a * (n : ℝ) * Real.log (n : ℝ) ^ 2 := by
  rw [inverseScale_pow (by omega : 0 < a) hn]
  have hpow :
      Real.log (n : ℝ) ^ (2 * a) =
        Real.log (n : ℝ) ^ (2 * a - 2) * Real.log (n : ℝ) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp [ne_of_gt hlog]

/--
Analytic inversion of a Bradač-shaped Ramsey lower bound.

The integer `a` is the polynomial Ramsey exponent (`a = s - 1` in the
application).  The logarithmic exponent `2 * a - 2` is exactly `2 * s - 4`.
The conclusion deliberately uses logarithmic exponent `2`, which is weaker
than the sharp inversion but sufficient for Erdős Problem 920.
-/
theorem isBigO_of_eventual_ramsey_lower_bound
    (a : ℕ) (ha : 2 ≤ a)
    (ramsey : ℕ → ℕ) (f : ℕ → ℝ)
    (A D : ℝ) (hA : 0 < A) (hD : 1 ≤ D)
    (hscale : 2 ≤ A * D ^ a)
    (hRamsey :
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ a / Real.log (m : ℝ) ^ (2 * a - 2) ≤ (ramsey m : ℝ))
    (hbridge : ∀ {n m : ℕ}, 0 < m → n < ramsey m → (n : ℝ) / m ≤ f n) :
    (fun n : ℕ ↦
      (n : ℝ) ^ (1 - 1 / (a : ℝ)) / Real.log (n : ℝ) ^ 2) =O[atTop] f := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hindex_tendsto : Tendsto (inverseIndex a D) atTop atTop :=
    tendsto_inverseIndex_atTop a (by omega) D hD
  have hRamseyIndex :
      ∀ᶠ n : ℕ in atTop,
        A * (inverseIndex a D n : ℝ) ^ a /
            Real.log (inverseIndex a D n : ℝ) ^ (2 * a - 2) ≤
          (ramsey (inverseIndex a D n) : ℝ) :=
    hindex_tendsto.eventually hRamsey
  have hloglarge :
      ∀ᶠ n : ℕ in atTop, 2 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hscaleSmall := eventually_two_mul_inverseScale_le a ha D hDpos
  refine IsBigO.of_bound (2 * D) ?_
  filter_upwards [hRamseyIndex, hloglarge, hscaleSmall, eventually_ge_atTop 1] with
      n hnRamsey hnlog hnScale hnNat
  let x : ℝ := inverseScale a D n
  let m : ℕ := inverseIndex a D n
  have hnpos : 0 < n := by omega
  have hnRpos : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := hlogpos.le
  have hroot_one : 1 ≤ (n : ℝ) ^ (1 / (a : ℝ)) := by
    apply Real.one_le_rpow
    · exact_mod_cast hnNat
    · positivity
  have hx_four : 4 ≤ x := by
    dsimp [x, inverseScale]
    calc
      (4 : ℝ) = 1 * 1 * 2 ^ 2 := by norm_num
      _ ≤ D * (n : ℝ) ^ (1 / (a : ℝ)) * Real.log (n : ℝ) ^ 2 := by
        gcongr
  have hx_nonneg : 0 ≤ x := le_trans (by norm_num) hx_four
  have hx_le_m : x ≤ (m : ℝ) := by
    dsimp [m, inverseIndex]
    exact Nat.le_ceil _
  have hm_le_two_x : (m : ℝ) ≤ 2 * x := by
    have hm_lt : (m : ℝ) < x + 1 := by
      dsimp [m, inverseIndex]
      exact Nat.ceil_lt_add_one hx_nonneg
    exact hm_lt.le.trans (by linarith [hx_four])
  have hm_le_n_real : (m : ℝ) ≤ n := by
    exact hm_le_two_x.trans (by simpa [x] using hnScale)
  have hm_le_n : m ≤ n := by exact_mod_cast hm_le_n_real
  have hm_pos : 0 < m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le (by linarith [hx_four]) hx_le_m
    exact_mod_cast this
  have hlogm_pos : 0 < Real.log (m : ℝ) := by
    apply Real.log_pos
    have hm4 : 4 ≤ m := by
      exact_mod_cast hx_four.trans hx_le_m
    exact_mod_cast (show 1 < m by omega)
  have hlogm_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hm_le_n_real
  have hpow_x_le_m : x ^ a ≤ (m : ℝ) ^ a :=
    pow_le_pow_left₀ hx_nonneg hx_le_m a
  have hdenom_le :
      Real.log (m : ℝ) ^ (2 * a - 2) ≤
        Real.log (n : ℝ) ^ (2 * a - 2) :=
    pow_le_pow_left₀ hlogm_pos.le hlogm_le _
  have htwo_n_le_scaled :
      2 * (n : ℝ) ≤ A * D ^ a * (n : ℝ) * Real.log (n : ℝ) ^ 2 := by
    calc
      2 * (n : ℝ) = 2 * (n : ℝ) * 1 := by ring
      _ ≤ (A * D ^ a) * (n : ℝ) * Real.log (n : ℝ) ^ 2 := by
        gcongr
        nlinarith [sq_nonneg (Real.log (n : ℝ) - 1)]
      _ = A * D ^ a * (n : ℝ) * Real.log (n : ℝ) ^ 2 := rfl
  have htwo_n_le_quotient :
      2 * (n : ℝ) ≤
        A * (m : ℝ) ^ a / Real.log (m : ℝ) ^ (2 * a - 2) := by
    calc
      2 * (n : ℝ) ≤
          A * D ^ a * (n : ℝ) * Real.log (n : ℝ) ^ 2 := htwo_n_le_scaled
      _ = A * x ^ a / Real.log (n : ℝ) ^ (2 * a - 2) := by
        symm
        simpa [x] using scaled_inverseScale_quotient (A := A) (D := D) ha hnpos hlogpos
      _ ≤ A * (m : ℝ) ^ a / Real.log (m : ℝ) ^ (2 * a - 2) := by
        apply div_le_div₀
        · positivity
        · exact mul_le_mul_of_nonneg_left hpow_x_le_m hA.le
        · exact pow_pos hlogm_pos _
        · exact hdenom_le
  have hn_lt_ramsey : n < ramsey m := by
    have hn_lt_ramsey_real : (n : ℝ) < ramsey m := by
      calc
        (n : ℝ) < 2 * n := by linarith
        _ ≤ A * (m : ℝ) ^ a / Real.log (m : ℝ) ^ (2 * a - 2) :=
          htwo_n_le_quotient
        _ ≤ (ramsey m : ℝ) := by simpa [m] using hnRamsey
    exact_mod_cast hn_lt_ramsey_real
  have hbridge_nm : (n : ℝ) / m ≤ f n := hbridge hm_pos hn_lt_ramsey
  have hf_nonneg : 0 ≤ f n :=
    le_trans (div_nonneg (by positivity) (by positivity)) hbridge_nm
  let target : ℝ :=
    (n : ℝ) ^ (1 - 1 / (a : ℝ)) / Real.log (n : ℝ) ^ 2
  have htarget_nonneg : 0 ≤ target := by
    dsimp [target]
    positivity
  have htarget_mul_scale : target * (2 * x) = 2 * D * (n : ℝ) := by
    dsimp [target, x, inverseScale]
    have hrpow :
        (n : ℝ) ^ (1 - 1 / (a : ℝ)) *
            (n : ℝ) ^ (1 / (a : ℝ)) = (n : ℝ) := by
      rw [← Real.rpow_add hnRpos]
      rw [show 1 - 1 / (a : ℝ) + 1 / (a : ℝ) = 1 by ring, Real.rpow_one]
    calc
      ((n : ℝ) ^ (1 - 1 / (a : ℝ)) / Real.log (n : ℝ) ^ 2) *
          (2 * (D * (n : ℝ) ^ (1 / (a : ℝ)) * Real.log (n : ℝ) ^ 2)) =
          2 * D * ((n : ℝ) ^ (1 - 1 / (a : ℝ)) *
            (n : ℝ) ^ (1 / (a : ℝ))) := by
              field_simp [ne_of_gt hlogpos]
      _ = 2 * D * (n : ℝ) := by rw [hrpow]
  have htarget_le_bridge : target ≤ 2 * D * ((n : ℝ) / m) := by
    rw [div_eq_mul_inv]
    rw [show 2 * D * ((n : ℝ) * (m : ℝ)⁻¹) =
      (2 * D * (n : ℝ)) * (m : ℝ)⁻¹ by ring]
    apply (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < m)).2
    calc
      target * (m : ℝ) ≤ target * (2 * x) :=
        mul_le_mul_of_nonneg_left hm_le_two_x htarget_nonneg
      _ = 2 * D * (n : ℝ) := htarget_mul_scale
  have htarget_le : target ≤ 2 * D * f n :=
    htarget_le_bridge.trans (mul_le_mul_of_nonneg_left hbridge_nm (by positivity))
  change
    |(n : ℝ) ^ (1 - 1 / (a : ℝ)) / Real.log (n : ℝ) ^ 2| ≤
      2 * D * |f n|
  rw [abs_div, abs_of_nonneg (Real.rpow_nonneg hnRpos.le _),
    abs_of_pos (pow_pos hlogpos 2), abs_of_nonneg hf_nonneg]
  exact htarget_le

/-- A positive polynomial coefficient can always be amplified by the inverse scale. -/
theorem exists_scale_constant (a : ℕ) (ha : 1 ≤ a) (A : ℝ) (hA : 0 < A) :
    ∃ D : ℝ, 1 ≤ D ∧ 2 ≤ A * D ^ a := by
  let D : ℝ := max 1 (2 / A)
  have hD : 1 ≤ D := le_max_left _ _
  have hquotient : 2 / A ≤ D := le_max_right _ _
  have hAD : 2 ≤ A * D := by
    rw [show A * D = D * A by ring]
    exact (div_le_iff₀ hA).mp hquotient
  have hDpow : D ≤ D ^ a := by
    have := pow_le_pow_right₀ hD ha
    simpa using this
  refine ⟨D, hD, hAD.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hDpow hA.le

/--
Version matching the Ramsey-to-chromatic bridge used in the main development:
the independent-set parameter is `m + 1`, while the coloring estimate has
denominator `m`.  The harmless factor `2 ^ (2 * a - 2)` absorbs replacing
`log (m + 1)` by `log m`.
-/
theorem isBigO_of_eventual_ramsey_lower_bound_succ
    (a : ℕ) (ha : 2 ≤ a)
    (ramsey : ℕ → ℕ) (f : ℕ → ℝ)
    (A D : ℝ) (hA : 0 < A) (hD : 1 ≤ D)
    (hscale : 2 ≤ (A / (2 : ℝ) ^ (2 * a - 2)) * D ^ a)
    (hRamsey :
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ a / Real.log (m : ℝ) ^ (2 * a - 2) ≤ (ramsey m : ℝ))
    (hbridge : ∀ {n m : ℕ}, 0 < m → n < ramsey (m + 1) → (n : ℝ) / m ≤ f n) :
    (fun n : ℕ ↦
      (n : ℝ) ^ (1 - 1 / (a : ℝ)) / Real.log (n : ℝ) ^ 2) =O[atTop] f := by
  let A' : ℝ := A / (2 : ℝ) ^ (2 * a - 2)
  have hA' : 0 < A' := by dsimp [A']; positivity
  have hRamsey' :
      ∀ᶠ m : ℕ in atTop,
        A' * (m : ℝ) ^ a / Real.log (m : ℝ) ^ (2 * a - 2) ≤
          (ramsey (m + 1) : ℝ) := by
    have hshift := (tendsto_add_atTop_nat 1).eventually hRamsey
    filter_upwards [hshift, eventually_ge_atTop 2] with m hmRamsey hm2
    have hmpos : (0 : ℝ) < m := by positivity
    have hm1pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hlogmpos : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hlogm1pos : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))
    have hm1_le_sq_nat : m + 1 ≤ m ^ 2 := by nlinarith
    have hm1_le_sq : ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 := by
      exact_mod_cast hm1_le_sq_nat
    have hlogm1_le : Real.log ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.log (m : ℝ) := by
      calc
        Real.log ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m : ℝ) ^ 2) :=
          Real.log_le_log hm1pos hm1_le_sq
        _ = 2 * Real.log (m : ℝ) := by rw [Real.log_pow]; norm_num
    have hdenom :
        Real.log ((m + 1 : ℕ) : ℝ) ^ (2 * a - 2) ≤
          (2 : ℝ) ^ (2 * a - 2) * Real.log (m : ℝ) ^ (2 * a - 2) := by
      calc
        Real.log ((m + 1 : ℕ) : ℝ) ^ (2 * a - 2) ≤
            (2 * Real.log (m : ℝ)) ^ (2 * a - 2) :=
          pow_le_pow_left₀ hlogm1pos.le hlogm1_le _
        _ = (2 : ℝ) ^ (2 * a - 2) * Real.log (m : ℝ) ^ (2 * a - 2) :=
          mul_pow _ _ _
    have hnum : A * (m : ℝ) ^ a ≤ A * ((m + 1 : ℕ) : ℝ) ^ a := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      exact pow_le_pow_left₀ (by positivity) (by norm_num) _
    calc
      A' * (m : ℝ) ^ a / Real.log (m : ℝ) ^ (2 * a - 2) =
          A * (m : ℝ) ^ a /
            ((2 : ℝ) ^ (2 * a - 2) * Real.log (m : ℝ) ^ (2 * a - 2)) := by
        dsimp [A']
        field_simp [ne_of_gt hlogmpos]
      _ ≤ A * ((m + 1 : ℕ) : ℝ) ^ a /
          Real.log ((m + 1 : ℕ) : ℝ) ^ (2 * a - 2) := by
        apply div_le_div₀
        · positivity
        · exact hnum
        · exact pow_pos hlogm1pos _
        · exact hdenom
      _ ≤ (ramsey (m + 1) : ℝ) := hmRamsey
  apply isBigO_of_eventual_ramsey_lower_bound a ha (fun m ↦ ramsey (m + 1)) f A' D
  · exact hA'
  · exact hD
  · simpa [A'] using hscale
  · exact hRamsey'
  · exact hbridge

/--
Turn the eventual Ramsey estimate in its usual `s`-parameterization directly
into the logarithmic-exponent-`2` lower bound required by Problem 920.
-/
theorem isBigO_problem920_of_eventual_ramsey_lower_bound
    (s : ℕ) (hs : 3 ≤ s)
    (ramsey : ℕ → ℕ) (f : ℕ → ℝ)
    (A : ℝ) (hA : 0 < A)
    (hRamsey :
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ (s - 1) / Real.log (m : ℝ) ^ (2 * s - 4) ≤
          (ramsey m : ℝ))
    (hbridge : ∀ {n m : ℕ}, 0 < m → n < ramsey (m + 1) → (n : ℝ) / m ≤ f n) :
    (fun n : ℕ ↦
      (n : ℝ) ^ (1 - 1 / ((s : ℝ) - 1)) / Real.log (n : ℝ) ^ 2) =O[atTop] f := by
  let a : ℕ := s - 1
  have ha : 2 ≤ a := by dsimp [a]; omega
  let A' : ℝ := A / (2 : ℝ) ^ (2 * a - 2)
  have hA' : 0 < A' := by dsimp [A']; positivity
  obtain ⟨D, hD, hscale⟩ := exists_scale_constant a (by omega) A' hA'
  have hRamseyA :
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ a / Real.log (m : ℝ) ^ (2 * a - 2) ≤
          (ramsey m : ℝ) := by
    have hexponent : 2 * a - 2 = 2 * s - 4 := by dsimp [a]; omega
    simpa only [a, hexponent] using hRamsey
  have hresult := isBigO_of_eventual_ramsey_lower_bound_succ
    a ha ramsey f A D hA hD (by simpa [A'] using hscale) hRamseyA hbridge
  simpa [a, Nat.cast_sub (by omega : 1 ≤ s)] using hresult

end Erdos920.Inversion
