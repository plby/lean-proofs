/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 227.
https://www.erdosproblems.com/forum/thread/227

Informal authors:
- J. Clunie
- W. K. Hayman

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos227.md
-/
/-
Erdős Problem 227: the ordinary limit of the maximum term divided by the
maximum modulus need not vanish.

The construction and all estimates are documented in `tex/227.tex` at the
repository root.
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Filter Set
open scoped BigOperators Topology

namespace Erdos227

/-- The maximum term of a power series on the circle of radius `r`. -/
noncomputable def maximumTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  sSup (Set.range fun n : ℕ ↦ ‖a n‖ * r ^ n)

/-- The maximum modulus of a function on the circle of radius `r`.
The parametrization by `Complex.exp (θ * I)` is surjective when `0 ≤ r`. -/
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup (Set.range fun θ : ℝ ↦ ‖f (r * Complex.exp (θ * Complex.I))‖)

/-- An exact power-series presentation of an entire function. -/
def IsEntirePowerSeries (a : ℕ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, HasSum (fun n : ℕ ↦ a n * z ^ n) (f z)

/-- The coefficient condition saying that the power series is not a polynomial. -/
def IsTranscendentalSeries (a : ℕ → ℂ) : Prop :=
  ¬ ∃ N : ℕ, ∀ n ≥ N, a n = 0

/-- Erdős's proposed conclusion, stated for an arbitrary coefficient sequence
and its exact entire power-series sum. -/
def Erdos227Claim : Prop :=
  ∀ (a : ℕ → ℂ) (f : ℂ → ℂ) (L : ℝ),
    IsEntirePowerSeries a f →
    IsTranscendentalSeries a →
    Tendsto (fun r : ℝ ↦ maximumTerm a r / maximumModulus f r) atTop (𝓝 L) →
    L = 0

namespace Construction

noncomputable section

/-- Successive crossing radii. -/
def radius (k : ℕ) : ℝ := k + 2

/-- The gap between successive carrier exponents. -/
def gap (k : ℕ) : ℕ := (k + 2) ^ 6

/-- Alternating packet sign. -/
def packetSign (k : ℕ) : ℝ := (-1 : ℝ) ^ k

/-- Carrier exponents. -/
def carrierIndex : ℕ → ℕ
  | 0 => 2
  | k + 1 => carrierIndex k + gap k

/-- Positive carrier coefficients. -/
def carrierCoeff : ℕ → ℝ
  | 0 => 1
  | k + 1 => carrierCoeff k / radius k ^ gap k

/-- The magnitude of the central term of packet `k` at radius `r`. -/
def carrier (k : ℕ) (r : ℝ) : ℝ :=
  carrierCoeff k * r ^ carrierIndex k

/-- A summable majorant for all three terms of a packet on a fixed circle. -/
def weightedCarrier (k : ℕ) (r : ℝ) : ℝ :=
  carrier k r * radius k

/-- The three-term polynomial packet. -/
def packet (k : ℕ) (z : ℂ) : ℂ :=
  (carrierCoeff k : ℂ) * z ^ carrierIndex k +
    (packetSign k * carrierCoeff k / (2 * radius k) : ℂ) *
      z ^ (carrierIndex k + 1) +
    (packetSign k * carrierCoeff k * radius k / 2 : ℂ) *
      z ^ (carrierIndex k - 1)

/-- Contribution of packet `k` to Taylor coefficient `n`. -/
def packetCoefficient (k n : ℕ) : ℂ :=
  if n = carrierIndex k then carrierCoeff k
  else if n = carrierIndex k + 1 then
    packetSign k * carrierCoeff k / (2 * radius k)
  else if n = carrierIndex k - 1 then
    packetSign k * carrierCoeff k * radius k / 2
  else 0

/-- Taylor coefficients of the counterexample.  The finite range is enough
because `k < carrierIndex k`. -/
def coeff (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), packetCoefficient k n

/-- The entire function used for the counterexample. -/
noncomputable def function (z : ℂ) : ℂ :=
  ∑' n : ℕ, coeff n * z ^ n

lemma radius_pos (k : ℕ) : 0 < radius k := by
  unfold radius
  positivity

lemma radius_ge_two (k : ℕ) : 2 ≤ radius k := by
  simp [radius]

lemma gap_pos (k : ℕ) : 0 < gap k := by
  simp [gap]

lemma gap_ge (k : ℕ) : 4 ≤ gap k := by
  unfold gap
  exact (by norm_num : 4 ≤ 2 ^ 6).trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ k + 2) 6)

lemma carrierIndex_ge_add_two (k : ℕ) : k + 2 ≤ carrierIndex k := by
  induction k with
  | zero => simp [carrierIndex]
  | succ k ih =>
      rw [carrierIndex]
      have hg := gap_ge k
      omega

lemma carrierIndex_pos (k : ℕ) : 0 < carrierIndex k := by
  exact (by omega : 0 < k + 2).trans_le (carrierIndex_ge_add_two k)

lemma carrierIndex_strictMono : StrictMono carrierIndex := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [carrierIndex]
  exact Nat.lt_add_of_pos_right (gap_pos k)

lemma carrierIndex_injective : Function.Injective carrierIndex :=
  carrierIndex_strictMono.injective

lemma carrierIndex_mono : Monotone carrierIndex :=
  carrierIndex_strictMono.monotone

lemma carrierIndex_add_four_le_succ (k : ℕ) :
    carrierIndex k + 4 ≤ carrierIndex (k + 1) := by
  rw [carrierIndex]
  exact Nat.add_le_add_left (gap_ge k) _

lemma carrierIndex_add_four_le_of_lt {i j : ℕ} (hij : i < j) :
    carrierIndex i + 4 ≤ carrierIndex j := by
  exact (carrierIndex_add_four_le_succ i).trans
    (carrierIndex_mono (Nat.succ_le_iff.mpr hij))

lemma carrierIndex_ne_other_triple {i j : ℕ} (hij : i ≠ j) :
    carrierIndex i ≠ carrierIndex j ∧
      carrierIndex i ≠ carrierIndex j + 1 ∧
      carrierIndex i ≠ carrierIndex j - 1 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsep := carrierIndex_add_four_le_of_lt hlt
    omega
  · have hsep := carrierIndex_add_four_le_of_lt hgt
    omega

lemma carrierCoeff_pos (k : ℕ) : 0 < carrierCoeff k := by
  induction k with
  | zero => simp [carrierCoeff]
  | succ k ih =>
      simp only [carrierCoeff]
      exact div_pos ih (pow_pos (radius_pos k) _)

lemma carrier_pos {k : ℕ} {r : ℝ} (hr : 0 < r) : 0 < carrier k r := by
  exact mul_pos (carrierCoeff_pos k) (pow_pos hr _)

lemma carrier_nonneg {k : ℕ} {r : ℝ} (hr : 0 ≤ r) : 0 ≤ carrier k r := by
  exact mul_nonneg (carrierCoeff_pos k).le (pow_nonneg hr _)

lemma weightedCarrier_nonneg {k : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ weightedCarrier k r := by
  exact mul_nonneg (carrier_nonneg hr) (radius_pos k).le

lemma packetCoefficient_other_at_carrier {i j : ℕ} (hij : i ≠ j) :
    packetCoefficient j (carrierIndex i) = 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := carrierIndex_ne_other_triple hij
  simp [packetCoefficient, h₀, h₁, h₂]

lemma coeff_carrierIndex (k : ℕ) :
    coeff (carrierIndex k) = carrierCoeff k := by
  rw [coeff]
  calc
    ∑ j ∈ Finset.range (carrierIndex k + 1),
        packetCoefficient j (carrierIndex k) =
        packetCoefficient k (carrierIndex k) := by
      apply Finset.sum_eq_single k
      · intro j hj hjk
        exact packetCoefficient_other_at_carrier hjk.symm
      · intro hk
        simp only [Finset.mem_range, not_lt] at hk
        have hindex := carrierIndex_ge_add_two k
        omega
    _ = carrierCoeff k := by simp [packetCoefficient]

lemma carrier_succ_ratio (k : ℕ) (r : ℝ) :
    carrier (k + 1) r = carrier k r * (r / radius k) ^ gap k := by
  simp only [carrier, carrierIndex, carrierCoeff]
  rw [pow_add, div_pow]
  field_simp [ne_of_gt (radius_pos k)]

lemma radius_succ_le_twice (k : ℕ) : radius (k + 1) ≤ 2 * radius k := by
  simp only [radius, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linarith

lemma eventually_four_mul_le_radius (x : ℝ) :
    ∀ᶠ k : ℕ in atTop, 4 * x ≤ radius k := by
  obtain ⟨K : ℕ, hK⟩ := exists_nat_ge (4 * x)
  filter_upwards [eventually_ge_atTop K] with k hk
  calc
    4 * x ≤ (K : ℝ) := hK
    _ ≤ (k : ℝ) := by exact_mod_cast hk
    _ ≤ radius k := by simp [radius]

lemma pow_ratio_le_quarter {x : ℝ} (hx : 0 ≤ x) {k : ℕ}
    (hk : 4 * x ≤ radius k) :
    (x / radius k) ^ gap k ≤ (1 / 4 : ℝ) := by
  have hr : 0 < radius k := radius_pos k
  have hratio_nonneg : 0 ≤ x / radius k := div_nonneg hx hr.le
  have hratio_quarter : x / radius k ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hr).2
    linarith
  have hratio_one : x / radius k ≤ 1 := hratio_quarter.trans (by norm_num)
  exact (pow_le_of_le_one hratio_nonneg hratio_one (Nat.ne_of_gt (gap_pos k))).trans
    hratio_quarter

lemma summable_weightedCarrier (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun k : ℕ ↦ weightedCarrier k x) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [eventually_four_mul_le_radius x] with k hk
  have hq := pow_ratio_le_quarter hx hk
  have hA : 0 ≤ carrier k x := carrier_nonneg hx
  have hR : 0 ≤ radius (k + 1) := (radius_pos _).le
  have hfactor :
      (x / radius k) ^ gap k * radius (k + 1) ≤
        (1 / 2 : ℝ) * radius k := by
    calc
      (x / radius k) ^ gap k * radius (k + 1) ≤
          (1 / 4 : ℝ) * radius (k + 1) :=
        mul_le_mul_of_nonneg_right hq hR
      _ ≤ (1 / 4 : ℝ) * (2 * radius k) :=
        mul_le_mul_of_nonneg_left (radius_succ_le_twice k) (by norm_num)
      _ = (1 / 2 : ℝ) * radius k := by ring
  simp only [Real.norm_eq_abs, abs_of_nonneg (weightedCarrier_nonneg hx)]
  rw [weightedCarrier, weightedCarrier, carrier_succ_ratio]
  calc
    carrier k x * (x / radius k) ^ gap k * radius (k + 1) =
        carrier k x * ((x / radius k) ^ gap k * radius (k + 1)) := by ring
    _ ≤ carrier k x * ((1 / 2 : ℝ) * radius k) :=
      mul_le_mul_of_nonneg_left hfactor hA
    _ = (1 / 2 : ℝ) * (carrier k x * radius k) := by ring

lemma packetSign_abs (k : ℕ) : |packetSign k| = 1 := by
  simp [packetSign]

lemma norm_central_coefficient_term (k : ℕ) (z : ℂ) :
    ‖(carrierCoeff k : ℂ) * z ^ carrierIndex k‖ = carrier k ‖z‖ := by
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (carrierCoeff_pos k), Complex.norm_pow]
  rfl

lemma norm_upper_coefficient_term (k : ℕ) (z : ℂ) :
    ‖(packetSign k * carrierCoeff k / (2 * radius k) : ℂ) *
        z ^ (carrierIndex k + 1)‖ =
      carrier k ‖z‖ * ‖z‖ / (2 * radius k) := by
  rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_div, Complex.norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, packetSign_abs,
    abs_of_pos (carrierCoeff_pos k),
    abs_of_pos (radius_pos k)]
  norm_num
  rw [pow_add]
  simp only [pow_one]
  unfold carrier
  ring

lemma norm_lower_coefficient_term (k : ℕ) (z : ℂ) (hz : 0 < ‖z‖) :
    ‖(packetSign k * carrierCoeff k * radius k / 2 : ℂ) *
        z ^ (carrierIndex k - 1)‖ =
      weightedCarrier k ‖z‖ / (2 * ‖z‖) := by
  rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_div, Complex.norm_mul,
    Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, packetSign_abs,
    abs_of_pos (carrierCoeff_pos k), abs_of_pos (radius_pos k),
    ]
  norm_num
  have hindex := carrierIndex_pos k
  have hpow : ‖z‖ ^ (carrierIndex k - 1) * ‖z‖ = ‖z‖ ^ carrierIndex k := by
    rw [← pow_succ]
    congr
    omega
  unfold weightedCarrier carrier
  field_simp [ne_of_gt hz]
  calc
    carrierCoeff k * radius k * ‖z‖ ^ (carrierIndex k - 1) * ‖z‖ =
        carrierCoeff k * radius k *
          (‖z‖ ^ (carrierIndex k - 1) * ‖z‖) := by ring
    _ = carrierCoeff k * radius k * ‖z‖ ^ carrierIndex k := by rw [hpow]

/-- The three exponents occupied by packet `k`. -/
def packetSupport (k : ℕ) : Finset ℕ :=
  {carrierIndex k - 1, carrierIndex k, carrierIndex k + 1}

lemma packetCoefficient_eq_zero_of_not_mem {k n : ℕ}
    (hn : n ∉ packetSupport k) : packetCoefficient k n = 0 := by
  simp only [packetSupport, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [packetCoefficient, hn.1, hn.2.1, hn.2.2]

/-- A fixed-circle constant used to dominate each of the three terms. -/
def coefficientMajorant (z : ℂ) : ℝ :=
  1 + ‖z‖ + ‖z‖⁻¹

lemma coefficientMajorant_nonneg (z : ℂ) : 0 ≤ coefficientMajorant z := by
  unfold coefficientMajorant
  positivity

lemma one_le_coefficientMajorant (z : ℂ) : 1 ≤ coefficientMajorant z := by
  unfold coefficientMajorant
  nlinarith [norm_nonneg z, inv_nonneg.mpr (norm_nonneg z)]

lemma norm_packetCoefficient_mul_pow_le (k n : ℕ) (z : ℂ) (hz : 0 < ‖z‖) :
    ‖packetCoefficient k n * z ^ n‖ ≤
      coefficientMajorant z * weightedCarrier k ‖z‖ := by
  let x : ℝ := ‖z‖
  let A : ℝ := carrier k x
  let W : ℝ := weightedCarrier k x
  let C : ℝ := coefficientMajorant z
  have hx : 0 ≤ x := norm_nonneg z
  have hA : 0 ≤ A := carrier_nonneg hx
  have hW : 0 ≤ W := weightedCarrier_nonneg hx
  have hR1 : 1 ≤ radius k := (by linarith [radius_ge_two k])
  have hAW : A ≤ W := by
    change carrier k x ≤ carrier k x * radius k
    simpa using mul_le_mul_of_nonneg_left hR1 hA
  have hC1 : 1 ≤ C := one_le_coefficientMajorant z
  have hWC : W ≤ C * W := by
    simpa using mul_le_mul_of_nonneg_right hC1 hW
  have hxC : x ≤ C := by
    dsimp [x, C, coefficientMajorant]
    nlinarith [norm_nonneg z, inv_nonneg.mpr (norm_nonneg z)]
  have hinvC : x⁻¹ ≤ C := by
    dsimp [x, C, coefficientMajorant]
    nlinarith [norm_nonneg z, inv_nonneg.mpr (norm_nonneg z)]
  by_cases h₀ : n = carrierIndex k
  · rw [packetCoefficient, if_pos h₀]
    subst n
    rw [norm_central_coefficient_term]
    exact hAW.trans hWC
  by_cases h₁ : n = carrierIndex k + 1
  · rw [packetCoefficient, if_neg h₀, if_pos h₁]
    subst n
    rw [norm_upper_coefficient_term]
    have hden : 1 ≤ 2 * radius k := by linarith [radius_ge_two k]
    calc
      A * x / (2 * radius k) ≤ A * x := div_le_self (mul_nonneg hA hx) hden
      _ = x * A := by ring
      _ ≤ x * W := mul_le_mul_of_nonneg_left hAW hx
      _ ≤ C * W := mul_le_mul_of_nonneg_right hxC hW
  by_cases h₂ : n = carrierIndex k - 1
  · rw [packetCoefficient, if_neg h₀, if_neg h₁, if_pos h₂]
    subst n
    rw [norm_lower_coefficient_term k z hz]
    have hhalf :
        W / (2 * x) = (1 / 2 : ℝ) * (x⁻¹ * W) := by
      dsimp [x]
      field_simp [ne_of_gt hz]
    rw [hhalf]
    have hInvW : 0 ≤ x⁻¹ * W := mul_nonneg (inv_nonneg.mpr hx) hW
    calc
      (1 / 2 : ℝ) * (x⁻¹ * W) ≤ x⁻¹ * W := by nlinarith
      _ ≤ C * W := mul_le_mul_of_nonneg_right hinvC hW
  · rw [packetCoefficient, if_neg h₀, if_neg h₁, if_neg h₂]
    simp only [zero_mul, norm_zero]
    exact mul_nonneg (coefficientMajorant_nonneg z)
      (weightedCarrier_nonneg (norm_nonneg z))

lemma summable_packetCoefficient_norm (k : ℕ) (z : ℂ) :
    Summable (fun n : ℕ ↦ ‖packetCoefficient k n * z ^ n‖) := by
  apply summable_of_hasFiniteSupport
  exact (packetSupport k).finite_toSet.subset (by
    intro n hn
    contrapose! hn
    simp [packetCoefficient_eq_zero_of_not_mem hn])

lemma packetSupport_card_le_three (k : ℕ) : (packetSupport k).card ≤ 3 := by
  unfold packetSupport
  have h₁ := Finset.card_insert_le (carrierIndex k - 1)
    ({carrierIndex k, carrierIndex k + 1} : Finset ℕ)
  have h₂ := Finset.card_insert_le (carrierIndex k)
    ({carrierIndex k + 1} : Finset ℕ)
  simp only [Finset.card_singleton] at h₂
  omega

lemma tsum_packetCoefficient_norm_le (k : ℕ) (z : ℂ) (hz : 0 < ‖z‖) :
    (∑' n : ℕ, ‖packetCoefficient k n * z ^ n‖) ≤
      3 * coefficientMajorant z * weightedCarrier k ‖z‖ := by
  rw [tsum_eq_sum (s := packetSupport k) (fun n hn ↦ by
    rw [packetCoefficient_eq_zero_of_not_mem hn, zero_mul, norm_zero])]
  calc
    ∑ n ∈ packetSupport k, ‖packetCoefficient k n * z ^ n‖ ≤
        ∑ _n ∈ packetSupport k,
          coefficientMajorant z * weightedCarrier k ‖z‖ := by
      exact Finset.sum_le_sum fun n hn ↦ norm_packetCoefficient_mul_pow_le k n z hz
    _ = ((packetSupport k).card : ℝ) *
          (coefficientMajorant z * weightedCarrier k ‖z‖) := by simp
    _ ≤ 3 * (coefficientMajorant z * weightedCarrier k ‖z‖) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast packetSupport_card_le_three k)
        (mul_nonneg (coefficientMajorant_nonneg z)
          (weightedCarrier_nonneg (norm_nonneg z)))
    _ = 3 * coefficientMajorant z * weightedCarrier k ‖z‖ := by ring

lemma summable_tsum_packetCoefficient_norm (z : ℂ) (hz : 0 < ‖z‖) :
    Summable (fun k : ℕ ↦ ∑' n : ℕ, ‖packetCoefficient k n * z ^ n‖) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact tsum_nonneg fun _ ↦ norm_nonneg _
  · intro k
    exact tsum_packetCoefficient_norm_le k z hz
  · simpa [mul_assoc] using
      (summable_weightedCarrier ‖z‖ (norm_nonneg z)).mul_left
        (3 * coefficientMajorant z)

lemma summable_packetCoefficient_norm_prod (z : ℂ) (hz : 0 < ‖z‖) :
    Summable (fun p : ℕ × ℕ ↦ ‖packetCoefficient p.1 p.2 * z ^ p.2‖) := by
  apply (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).2
  exact ⟨fun k ↦ summable_packetCoefficient_norm k z,
    summable_tsum_packetCoefficient_norm z hz⟩

lemma summable_coeff_mul_pow (z : ℂ) :
    Summable (fun n : ℕ ↦ coeff n * z ^ n) := by
  by_cases hz : z = 0
  · subst z
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton 0).subset (by
      intro n hn
      have hn0 : n = 0 := by
        by_contra hn0
        exact hn (by simp [hn0])
      simpa [hn0])
  · have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hprod := summable_packetCoefficient_norm_prod z hznorm
    have hmajor :
        Summable (fun n : ℕ ↦ ∑' k : ℕ, ‖packetCoefficient k n * z ^ n‖) := by
      simpa only [Prod.swap_prod_mk] using hprod.prod_symm.prod
    apply Summable.of_norm_bounded hmajor
    intro n
    rw [coeff, Finset.sum_mul]
    have hfiber : Summable (fun k : ℕ ↦ ‖packetCoefficient k n * z ^ n‖) := by
      simpa only [Prod.swap_prod_mk] using hprod.prod_symm.prod_factor n
    exact (norm_sum_le (Finset.range (n + 1))
      (fun k ↦ packetCoefficient k n * z ^ n)).trans
        (hfiber.sum_le_tsum (Finset.range (n + 1)) (fun _ _ ↦ norm_nonneg _))

lemma function_hasSum (z : ℂ) :
    HasSum (fun n : ℕ ↦ coeff n * z ^ n) (function z) := by
  exact (summable_coeff_mul_pow z).hasSum

theorem isEntirePowerSeries : IsEntirePowerSeries coeff function :=
  function_hasSum

theorem coeff_isTranscendental : IsTranscendentalSeries coeff := by
  rintro ⟨N, hN⟩
  have hzero := hN (carrierIndex N) (carrierIndex_ge_add_two N |>.trans' (Nat.le_add_right N 2))
  rw [coeff_carrierIndex] at hzero
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt (carrierCoeff_pos N))) hzero

lemma packetCoefficient_zero_zero (k : ℕ) : packetCoefficient k 0 = 0 := by
  have hindex := carrierIndex_ge_add_two k
  have h₀ : (0 : ℕ) ≠ carrierIndex k := by omega
  have h₁ : (0 : ℕ) ≠ carrierIndex k + 1 := by omega
  have h₂ : (0 : ℕ) ≠ carrierIndex k - 1 := by omega
  simp [packetCoefficient, h₀, h₁, h₂]

lemma packetCoefficient_eq_zero_of_lt {k n : ℕ} (hnk : n < k) :
    packetCoefficient k n = 0 := by
  have hindex := carrierIndex_ge_add_two k
  have h₀ : n ≠ carrierIndex k := by omega
  have h₁ : n ≠ carrierIndex k + 1 := by omega
  have h₂ : n ≠ carrierIndex k - 1 := by omega
  simp [packetCoefficient, h₀, h₁, h₂]

lemma coeff_eq_tsum_packetCoefficient (n : ℕ) :
    coeff n = ∑' k : ℕ, packetCoefficient k n := by
  rw [coeff, tsum_eq_sum (s := Finset.range (n + 1))]
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  exact packetCoefficient_eq_zero_of_lt (by omega)

lemma tsum_packetCoefficient_mul_pow_eq_packet (k : ℕ) (z : ℂ) :
    (∑' n : ℕ, packetCoefficient k n * z ^ n) = packet k z := by
  rw [tsum_eq_sum (s := packetSupport k) (fun n hn ↦ by
    rw [packetCoefficient_eq_zero_of_not_mem hn, zero_mul])]
  have hindex := carrierIndex_pos k
  have hpred_lt : carrierIndex k - 1 < carrierIndex k := by omega
  have hpred_ne : carrierIndex k - 1 ≠ carrierIndex k := ne_of_lt hpred_lt
  have hpred_ne_succ : carrierIndex k - 1 ≠ carrierIndex k + 1 := by omega
  have hself_ne_succ : carrierIndex k ≠ carrierIndex k + 1 := by omega
  simp [packetSupport, packetCoefficient, packet, hpred_ne, hpred_ne_succ,
    hself_ne_succ]
  ring

lemma summable_packetCoefficient_prod (z : ℂ) :
    Summable (fun p : ℕ × ℕ ↦ packetCoefficient p.1 p.2 * z ^ p.2) := by
  by_cases hz : z = 0
  · subst z
    have hzero : ∀ p : ℕ × ℕ,
        packetCoefficient p.1 p.2 * (0 : ℂ) ^ p.2 = 0 := by
      rintro ⟨k, n⟩
      by_cases hn : n = 0
      · subst n
        simp [packetCoefficient_zero_zero]
      · simp [hn]
    simpa only [hzero] using
      (summable_zero : Summable (fun _p : ℕ × ℕ ↦ (0 : ℂ)))
  · exact (summable_packetCoefficient_norm_prod z (norm_pos_iff.mpr hz)).of_norm

lemma function_eq_tsum_packet (z : ℂ) :
    function z = ∑' k : ℕ, packet k z := by
  have hdouble := summable_packetCoefficient_prod z
  unfold function
  calc
    (∑' n : ℕ, coeff n * z ^ n) =
        ∑' n : ℕ, ∑' k : ℕ, packetCoefficient k n * z ^ n := by
      apply tsum_congr
      intro n
      rw [coeff_eq_tsum_packetCoefficient n]
      have hfiber : Summable (fun k : ℕ ↦ packetCoefficient k n) := by
        apply summable_of_hasFiniteSupport
        exact (Finset.range (n + 1)).finite_toSet.subset (by
          intro k hk
          simp only [Function.mem_support] at hk
          simp only [Finset.mem_coe, Finset.mem_range]
          by_contra hkn
          exact hk (packetCoefficient_eq_zero_of_lt (by omega)))
      rw [hfiber.tsum_mul_right]
    _ = ∑' k : ℕ, ∑' n : ℕ, packetCoefficient k n * z ^ n :=
      hdouble.tsum_comm
    _ = ∑' k : ℕ, packet k z := by
      exact tsum_congr fun k ↦ tsum_packetCoefficient_mul_pow_eq_packet k z

lemma summable_packet (z : ℂ) : Summable (fun k : ℕ ↦ packet k z) := by
  have hdouble := summable_packetCoefficient_prod z
  have hinner :
      (fun k : ℕ ↦ ∑' n : ℕ, packetCoefficient k n * z ^ n) =
        (fun k : ℕ ↦ packet k z) := by
    funext k
    exact tsum_packetCoefficient_mul_pow_eq_packet k z
  rw [← hinner]
  exact hdouble.prod

/-- The annulus on which packet `k` is the dominant packet. -/
def InCell (k : ℕ) (r : ℝ) : Prop :=
  (k : ℝ) + 1 ≤ r ∧ r ≤ (k : ℝ) + 2

lemma carrier_le_succ_of_radius_le {j : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hR : radius j ≤ r) : carrier j r ≤ carrier (j + 1) r := by
  rw [carrier_succ_ratio]
  have hcarrier : 0 ≤ carrier j r := carrier_nonneg hr
  have hbase : 1 ≤ r / radius j := (le_div_iff₀ (radius_pos j)).2 (by simpa using hR)
  have hpow : 1 ≤ (r / radius j) ^ gap j := one_le_pow₀ hbase
  simpa using mul_le_mul_of_nonneg_left hpow hcarrier

lemma carrier_succ_le_of_le_radius {j : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hR : r ≤ radius j) : carrier (j + 1) r ≤ carrier j r := by
  rw [carrier_succ_ratio]
  have hcarrier : 0 ≤ carrier j r := carrier_nonneg hr
  have hbase0 : 0 ≤ r / radius j := div_nonneg hr (radius_pos j).le
  have hbase1 : r / radius j ≤ 1 := (div_le_one (radius_pos j)).2 hR
  have hpow : (r / radius j) ^ gap j ≤ 1 := pow_le_one₀ hbase0 hbase1
  simpa using mul_le_mul_of_nonneg_left hpow hcarrier

lemma carrier_le_of_le_cell {j k : ℕ} {r : ℝ} (hjk : j ≤ k)
    (hr : InCell k r) : carrier j r ≤ carrier k r := by
  have hr0 : 0 ≤ r := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hmono : Monotone (fun i : ℕ ↦ carrier (min i k) r) := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hik : i < k
    · rw [Nat.min_eq_left hik.le, Nat.min_eq_left (Nat.succ_le_iff.mpr hik)]
      apply carrier_le_succ_of_radius_le hr0
      unfold radius
      have hnat : i + 2 ≤ k + 1 := by omega
      have hcast : (i : ℝ) + 2 ≤ (k : ℝ) + 1 := by exact_mod_cast hnat
      linarith [hr.1]
    · have hki : k ≤ i := Nat.le_of_not_gt hik
      rw [Nat.min_eq_right hki, Nat.min_eq_right (hki.trans (Nat.le_succ i))]
  simpa only [Nat.min_eq_left hjk, Nat.min_self] using hmono hjk

lemma carrier_le_of_cell_le {k j : ℕ} {r : ℝ} (hkj : k ≤ j)
    (hr : InCell k r) : carrier j r ≤ carrier k r := by
  have hr0 : 0 ≤ r := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  induction j, hkj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hkj ih =>
      exact (carrier_succ_le_of_le_radius hr0 (by
        have hcast : (k : ℝ) ≤ j := by exact_mod_cast hkj
        unfold radius
        linarith [hr.2])).trans ih

lemma carrier_le_dominant {j k : ℕ} {r : ℝ} (hr : InCell k r) :
    carrier j r ≤ carrier k r := by
  rcases le_total j k with hjk | hkj
  · exact carrier_le_of_le_cell hjk hr
  · exact carrier_le_of_cell_le hkj hr

/-- A quantitative form of the elementary estimate
`(m / (m + 1)) ^ m ≤ 1 / 2`.  The extra exponent `q` is what turns the
large gaps between carriers into a geometric error term. -/
lemma pow_ratio_le_half_pow {m D q : ℕ} (hm : 1 ≤ m) (hD : m * q ≤ D) :
    ((m : ℝ) / (m + 1)) ^ D ≤ (1 / 2 : ℝ) ^ q := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  let x : ℝ := (m : ℝ) / (m + 1)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_one (by positivity : (0 : ℝ) < m + 1)).2
    norm_num
  have hBernoulli : (2 : ℝ) ≤ (1 + 1 / (m : ℝ)) ^ m := by
    have hdiv0 : 0 ≤ 1 / (m : ℝ) := by positivity
    have h := one_add_mul_le_pow (a := 1 / (m : ℝ))
      (by linarith : (-2 : ℝ) ≤ 1 / (m : ℝ)) m
    calc
      (2 : ℝ) = 1 + (m : ℝ) * (1 / (m : ℝ)) := by
        field_simp [ne_of_gt hmR]
        norm_num
      _ ≤ (1 + 1 / (m : ℝ)) ^ m := h
  have hbase : x ^ m ≤ (1 / 2 : ℝ) := by
    have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hBernoulli
    have hxinv : x = (1 + 1 / (m : ℝ))⁻¹ := by
      dsimp [x]
      field_simp [ne_of_gt hmR]
    rw [hxinv, inv_pow]
    simpa only [one_div] using hinv
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hD
  rw [pow_add]
  have he : x ^ e ≤ 1 := pow_le_one₀ hx0 hx1
  calc
    x ^ (m * q) * x ^ e ≤ x ^ (m * q) * 1 :=
      mul_le_mul_of_nonneg_left he (pow_nonneg hx0 _)
    _ = (x ^ m) ^ q := by rw [mul_one, pow_mul]
    _ ≤ (1 / 2 : ℝ) ^ q := pow_le_pow_left₀ (pow_nonneg hx0 _) hbase q

/-- The three elementary gap inequalities used below. -/
lemma gap_pred_large {k : ℕ} (hk : 2 ≤ k) :
    (2 * k + 2) * k ≤ gap (k - 1) := by
  have h1 : 2 ≤ (k + 1) ^ 2 := by nlinarith [Nat.zero_le k]
  have h2 : k + 1 ≤ (k + 1) ^ 2 := by nlinarith [Nat.zero_le k]
  have h3 : k ≤ (k + 1) ^ 2 := by nlinarith [Nat.zero_le k]
  have h := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hpred : k - 1 + 2 = k + 1 := by omega
  rw [gap, hpred]
  convert h using 1 <;> ring

lemma gap_self_large (k : ℕ) : (2 * k + 3) * k ≤ gap k := by
  have h1 : 2 * k + 3 ≤ (k + 2) ^ 2 := by nlinarith [Nat.zero_le k]
  have h2 : k ≤ (k + 2) ^ 4 := by
    exact (by omega : k ≤ k + 2) |>.trans
      (by simpa using
        Nat.pow_le_pow_right (by omega : 0 < k + 2) (by omega : 1 ≤ 4))
  have h := Nat.mul_le_mul h1 h2
  unfold gap
  convert h using 1 <;> ring

lemma gap_lower_distant_large {k : ℕ} (hk : 2 ≤ k) :
    k * k ≤ gap (k - 2) := by
  have h := Nat.pow_le_pow_right (by omega : 0 < k) (by omega : 2 ≤ 6)
  have hpred : k - 2 + 2 = k := by omega
  rw [gap, hpred]
  simpa [pow_two] using h

lemma gap_upper_distant_large (k : ℕ) : (k + 2) * k ≤ gap (k + 1) := by
  have h1 : k + 2 ≤ (k + 3) ^ 2 := by nlinarith [Nat.zero_le k]
  have h2 : k ≤ (k + 3) ^ 4 := by
    exact (by omega : k ≤ k + 3) |>.trans
      (by simpa using
        Nat.pow_le_pow_right (by omega : 0 < k + 3) (by omega : 1 ≤ 4))
  have h := Nat.mul_le_mul h1 h2
  unfold gap
  convert h using 1 <;> ring

/-- The adjacent-ratio identity solved in the opposite direction. -/
lemma carrier_pred_ratio {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) :
    carrier (k - 1) r =
      carrier k r * (radius (k - 1) / r) ^ gap (k - 1) := by
  have hsucc : k - 1 + 1 = k := by omega
  have hnext : carrier k r =
      carrier (k - 1) r * (r / radius (k - 1)) ^ gap (k - 1) := by
    simpa only [hsucc] using carrier_succ_ratio (k - 1) r
  rw [hnext]
  have hcancel : r / radius (k - 1) * (radius (k - 1) / r) = 1 := by
    field_simp [ne_of_gt hr, ne_of_gt (radius_pos (k - 1))]
  calc
    carrier (k - 1) r = carrier (k - 1) r * 1 := by ring
    _ = carrier (k - 1) r *
        (r / radius (k - 1) * (radius (k - 1) / r)) ^ gap (k - 1) := by
      rw [hcancel, one_pow]
    _ = carrier (k - 1) r * (r / radius (k - 1)) ^ gap (k - 1) *
        (radius (k - 1) / r) ^ gap (k - 1) := by
      rw [mul_pow]
      ring

/-- A geometric error used uniformly throughout one cell. -/
def geometricError (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

lemma geometricError_nonneg (k : ℕ) : 0 ≤ geometricError k := by
  unfold geometricError
  positivity

lemma carrier_succ_le_geometricError_of_le_midpoint {k : ℕ} {r : ℝ}
    (hr : InCell k r) (hmiddle : 2 * r ≤ 2 * (k : ℝ) + 3) :
    carrier (k + 1) r ≤ carrier k r * geometricError k := by
  have hr0 : 0 ≤ r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hbase0 : 0 ≤ r / radius k := div_nonneg hr0 (radius_pos k).le
  have hbase :
      r / radius k ≤ ((2 * k + 3 : ℕ) : ℝ) / ((2 * k + 4 : ℕ) : ℝ) := by
    unfold radius
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < k + 2)
      (by positivity : (0 : ℝ) < ((2 * k + 4 : ℕ) : ℝ))).2
    push_cast
    nlinarith
  have hpow := pow_le_pow_left₀ hbase0 hbase (gap k)
  have hdecay := pow_ratio_le_half_pow (m := 2 * k + 3) (D := gap k) (q := k)
    (by omega) (gap_self_large k)
  have hdecay' :
      (((2 * k + 3 : ℕ) : ℝ) / ((2 * k + 4 : ℕ) : ℝ)) ^ gap k ≤
        geometricError k := by
    convert hdecay using 1 <;> norm_num [geometricError] <;> ring
  rw [carrier_succ_ratio]
  exact mul_le_mul_of_nonneg_left (hpow.trans hdecay') (carrier_nonneg hr0)

lemma carrier_pred_le_geometricError_of_midpoint_le {k : ℕ} {r : ℝ}
    (hk : 2 ≤ k) (hr : InCell k r) (hmiddle : 2 * (k : ℝ) + 3 ≤ 2 * r) :
    carrier (k - 1) r ≤ carrier k r * geometricError k := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hbase0 : 0 ≤ radius (k - 1) / r :=
    div_nonneg (radius_pos _).le hrpos.le
  have hbase :
      radius (k - 1) / r ≤
        ((2 * k + 2 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ) := by
    rw [show radius (k - 1) = (k : ℝ) + 1 by
      unfold radius
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast
      ring]
    apply (div_le_div_iff₀ hrpos
      (by positivity : (0 : ℝ) < ((2 * k + 3 : ℕ) : ℝ))).2
    push_cast
    nlinarith
  have hpow := pow_le_pow_left₀ hbase0 hbase (gap (k - 1))
  have hdecay := pow_ratio_le_half_pow (m := 2 * k + 2)
    (D := gap (k - 1)) (q := k) (by omega) (gap_pred_large hk)
  have hdecay' :
      (((2 * k + 2 : ℕ) : ℝ) / ((2 * k + 3 : ℕ) : ℝ)) ^ gap (k - 1) ≤
        geometricError k := by
    convert hdecay using 1 <;> norm_num [geometricError] <;> ring
  rw [carrier_pred_ratio (by omega) hrpos]
  exact mul_le_mul_of_nonneg_left (hpow.trans hdecay') (carrier_nonneg hrpos.le)

lemma neighbor_carriers_le {k : ℕ} {r : ℝ} (hk : 2 ≤ k) (hr : InCell k r) :
    carrier (k - 1) r + carrier (k + 1) r ≤
      carrier k r * (1 + geometricError k) := by
  have hBk : 0 ≤ carrier k r := carrier_nonneg (by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1])
  rcases le_total (2 * r) (2 * (k : ℝ) + 3) with hleft | hright
  · have hprev : carrier (k - 1) r ≤ carrier k r :=
      carrier_le_dominant hr
    have hnext := carrier_succ_le_geometricError_of_le_midpoint hr hleft
    nlinarith [geometricError_nonneg k]
  · have hprev := carrier_pred_le_geometricError_of_midpoint_le hk hr hright
    have hnext : carrier (k + 1) r ≤ carrier k r :=
      carrier_le_dominant hr
    nlinarith [geometricError_nonneg k]

lemma gap_mono : Monotone gap := by
  intro i j hij
  exact Nat.pow_le_pow_left (Nat.add_le_add_right hij 2) 6

lemma radius_mono : Monotone radius := by
  intro i j hij
  unfold radius
  exact_mod_cast Nat.add_le_add_right hij 2

lemma carrier_mono_below_radius {i j : ℕ} (hij : i ≤ j) {r : ℝ}
    (hR : radius j ≤ r) : carrier i r ≤ carrier j r := by
  revert r
  induction hij with
  | refl =>
      intro r hR
      exact le_rfl
  | @step j hij ih =>
      intro r hR
      have hRj : radius j ≤ r := (radius_mono (Nat.le_succ j)).trans hR
      exact (ih hRj).trans
        (carrier_le_succ_of_radius_le (by linarith [radius_pos j]) hRj)

lemma carrier_lower_distant_le {j k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hj : j ≤ k - 2) (hr : InCell k r) :
    carrier j r ≤ carrier k r * geometricError k := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hmono : carrier j r ≤ carrier (k - 2) r :=
    carrier_mono_below_radius hj (by
      rw [show radius (k - 2) = (k : ℝ) by
        unfold radius
        rw [Nat.cast_sub (by omega : 2 ≤ k)]
        push_cast
        ring]
      linarith [hr.1])
  have hbase0 : 0 ≤ radius (k - 2) / r :=
    div_nonneg (radius_pos _).le hrpos.le
  have hbase : radius (k - 2) / r ≤ (k : ℝ) / (k + 1) := by
    rw [show radius (k - 2) = (k : ℝ) by
      unfold radius
      rw [Nat.cast_sub (by omega : 2 ≤ k)]
      push_cast
      ring]
    apply (div_le_div_iff₀ hrpos (by positivity : (0 : ℝ) < k + 1)).2
    nlinarith [hr.1]
  have hpow := pow_le_pow_left₀ hbase0 hbase (gap (k - 2))
  have hdecay := pow_ratio_le_half_pow (m := k) (D := gap (k - 2)) (q := k)
    (by omega) (gap_lower_distant_large hk)
  have hdecay' : ((k : ℝ) / (k + 1)) ^ gap (k - 2) ≤ geometricError k := by
    simpa only [geometricError] using hdecay
  have hpred : carrier (k - 2) r ≤
      carrier (k - 1) r * geometricError k := by
    have hratio := carrier_pred_ratio (k := k - 1) (by omega) hrpos
    simp only [Nat.sub_sub, one_add_one_eq_two] at hratio
    rw [hratio]
    exact mul_le_mul_of_nonneg_left (hpow.trans hdecay')
      (carrier_nonneg hrpos.le)
  have hprev : carrier (k - 1) r ≤ carrier k r := carrier_le_dominant hr
  exact hmono.trans (hpred.trans
    (mul_le_mul_of_nonneg_right hprev (geometricError_nonneg k)))

lemma upper_adjacent_ratio_le_quarter {k i : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hi : k + 1 ≤ i) (hr : InCell k r) :
    carrier (i + 1) r ≤ carrier i r * (1 / 4 : ℝ) := by
  have hr0 : 0 ≤ r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hbase0 : 0 ≤ r / radius i := div_nonneg hr0 (radius_pos _).le
  have hbase : r / radius i ≤ (k + 2 : ℝ) / (k + 3) := by
    apply (div_le_div_iff₀ (radius_pos i) (by positivity : (0 : ℝ) < k + 3)).2
    have hiR : (k : ℝ) + 3 ≤ radius i := by
      unfold radius
      exact_mod_cast (by omega : k + 3 ≤ i + 2)
    nlinarith [hr.2]
  have hpow := pow_le_pow_left₀ hbase0 hbase (gap i)
  have hD : (k + 2) * 2 ≤ gap i := by
    exact (Nat.mul_le_mul_left (k + 2) hk).trans
      ((gap_upper_distant_large k).trans (gap_mono hi))
  have hdecay := pow_ratio_le_half_pow (m := k + 2) (D := gap i) (q := 2)
    (by omega) hD
  have hdecay' : ((k + 2 : ℝ) / (k + 3)) ^ gap i ≤ (1 / 4 : ℝ) := by
    convert hdecay using 1 <;> norm_num <;> ring
  rw [carrier_succ_ratio]
  exact mul_le_mul_of_nonneg_left (hpow.trans hdecay') (carrier_nonneg hr0)

lemma carrier_first_upper_distant_le {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    carrier (k + 2) r ≤ carrier k r * geometricError k := by
  have hr0 : 0 ≤ r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hbase0 : 0 ≤ r / radius (k + 1) := div_nonneg hr0 (radius_pos _).le
  have hbase : r / radius (k + 1) ≤ (k + 2 : ℝ) / (k + 3) := by
    rw [show radius (k + 1) = (k : ℝ) + 3 by
      unfold radius
      push_cast
      ring]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < k + 3)
      (by positivity : (0 : ℝ) < k + 3)).2
    nlinarith [hr.2]
  have hpow := pow_le_pow_left₀ hbase0 hbase (gap (k + 1))
  have hdecay := pow_ratio_le_half_pow (m := k + 2) (D := gap (k + 1)) (q := k)
    (by omega) (gap_upper_distant_large k)
  have hdecay' : ((k + 2 : ℝ) / (k + 3)) ^ gap (k + 1) ≤
      geometricError k := by
    convert hdecay using 1 <;> norm_num [geometricError] <;> ring
  rw [carrier_succ_ratio]
  exact (mul_le_mul_of_nonneg_left (hpow.trans hdecay')
    (carrier_nonneg hr0)).trans
      (mul_le_mul_of_nonneg_right (carrier_le_dominant hr) (geometricError_nonneg k))

lemma carrier_upper_distant_le {k m : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    carrier (k + 2 + m) r ≤
      carrier k r * geometricError k * (1 / 4 : ℝ) ^ m := by
  induction m with
  | zero => simpa using carrier_first_upper_distant_le hk hr
  | succ m ih =>
      have hadj := upper_adjacent_ratio_le_quarter hk
        (i := k + 2 + m) (by omega) hr
      rw [show k + 2 + (m + 1) = (k + 2 + m) + 1 by omega]
      calc
        carrier (k + 2 + m + 1) r ≤ carrier (k + 2 + m) r * (1 / 4 : ℝ) := hadj
        _ ≤ (carrier k r * geometricError k * (1 / 4 : ℝ) ^ m) * (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = carrier k r * geometricError k * (1 / 4 : ℝ) ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- A pointwise norm bound for one packet on a circle. -/
def packetNormBound (j : ℕ) (r : ℝ) : ℝ :=
  carrier j r * (1 + r / (2 * radius j) + radius j / (2 * r))

lemma norm_packet_le {j : ℕ} {z : ℂ} (hz : 0 < ‖z‖) :
    ‖packet j z‖ ≤ packetNormBound j ‖z‖ := by
  unfold packet
  calc
    ‖(carrierCoeff j : ℂ) * z ^ carrierIndex j +
          (packetSign j * carrierCoeff j / (2 * radius j) : ℂ) *
            z ^ (carrierIndex j + 1) +
          (packetSign j * carrierCoeff j * radius j / 2 : ℂ) *
            z ^ (carrierIndex j - 1)‖ ≤
        ‖(carrierCoeff j : ℂ) * z ^ carrierIndex j‖ +
          ‖(packetSign j * carrierCoeff j / (2 * radius j) : ℂ) *
            z ^ (carrierIndex j + 1)‖ +
          ‖(packetSign j * carrierCoeff j * radius j / 2 : ℂ) *
            z ^ (carrierIndex j - 1)‖ := by
      calc
        ‖((carrierCoeff j : ℂ) * z ^ carrierIndex j +
              (packetSign j * carrierCoeff j / (2 * radius j) : ℂ) *
                z ^ (carrierIndex j + 1)) +
            (packetSign j * carrierCoeff j * radius j / 2 : ℂ) *
              z ^ (carrierIndex j - 1)‖ ≤
            ‖(carrierCoeff j : ℂ) * z ^ carrierIndex j +
              (packetSign j * carrierCoeff j / (2 * radius j) : ℂ) *
                z ^ (carrierIndex j + 1)‖ +
              ‖(packetSign j * carrierCoeff j * radius j / 2 : ℂ) *
                z ^ (carrierIndex j - 1)‖ := norm_add_le _ _
        _ ≤ (‖(carrierCoeff j : ℂ) * z ^ carrierIndex j‖ +
              ‖(packetSign j * carrierCoeff j / (2 * radius j) : ℂ) *
                z ^ (carrierIndex j + 1)‖) +
              ‖(packetSign j * carrierCoeff j * radius j / 2 : ℂ) *
                z ^ (carrierIndex j - 1)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ = packetNormBound j ‖z‖ := by
      rw [norm_central_coefficient_term, norm_upper_coefficient_term,
        norm_lower_coefficient_term j z hz]
      unfold packetNormBound weightedCarrier
      field_simp [ne_of_gt hz]

lemma packetNormBound_nonneg {j : ℕ} {r : ℝ} (hr : 0 < r) :
    0 ≤ packetNormBound j r := by
  unfold packetNormBound
  exact mul_nonneg (carrier_nonneg hr.le)
    (add_nonneg
      (add_nonneg zero_le_one
        (div_nonneg hr.le (mul_nonneg (by norm_num) (radius_pos j).le)))
      (div_nonneg (radius_pos j).le (mul_nonneg (by norm_num) hr.le)))

lemma packetNormBound_lower_distant_le {j k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hj : j ≤ k - 2) (hr : InCell k r) :
    packetNormBound j r ≤
      ((k : ℝ) + 3) * (carrier k r * geometricError k) := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hRj : radius j ≤ (k : ℝ) := by
    unfold radius
    exact_mod_cast (by omega : j + 2 ≤ k)
  have hupper : r / (2 * radius j) ≤ ((k : ℝ) + 2) / 4 := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (radius_pos j))
      (by norm_num : (0 : ℝ) < 4)).2
    calc
      r * 4 ≤ ((k : ℝ) + 2) * 4 :=
        mul_le_mul_of_nonneg_right hr.2 (by norm_num)
      _ ≤ ((k : ℝ) + 2) * (2 * radius j) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [radius_ge_two j]
      _ = ((k : ℝ) + 2) * (2 * radius j) := rfl
  have hlower : radius j / (2 * r) ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hrpos)
      (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [hRj, hr.1]
  have hfactor :
      1 + r / (2 * radius j) + radius j / (2 * r) ≤ (k : ℝ) + 3 := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [hupper, hlower]
  have hcarrier := carrier_lower_distant_le hk hj hr
  unfold packetNormBound
  calc
    carrier j r * (1 + r / (2 * radius j) + radius j / (2 * r)) ≤
        carrier j r * ((k : ℝ) + 3) :=
      mul_le_mul_of_nonneg_left hfactor (carrier_nonneg hrpos.le)
    _ ≤ (carrier k r * geometricError k) * ((k : ℝ) + 3) :=
      mul_le_mul_of_nonneg_right hcarrier (by positivity)
    _ = ((k : ℝ) + 3) * (carrier k r * geometricError k) := by ring

lemma nat_succ_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      omega

lemma packetNormBound_upper_distant_le {k m : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    packetNormBound (k + 2 + m) r ≤
      ((k : ℝ) + 6) * (carrier k r * geometricError k) * (1 / 2 : ℝ) ^ m := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hrR : r ≤ radius (k + 2 + m) := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    unfold radius
    push_cast
    nlinarith [hr.2]
  have hupper : r / (2 * radius (k + 2 + m)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (radius_pos (k + 2 + m)))
      (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  have hlower : radius (k + 2 + m) / (2 * r) ≤ radius (k + 2 + m) := by
    exact div_le_self (radius_pos _).le (by nlinarith [hr.1])
  have hfactor :
      1 + r / (2 * radius (k + 2 + m)) + radius (k + 2 + m) / (2 * r) ≤
        (k : ℝ) + m + 6 := by
    have hReq : radius (k + 2 + m) = (k : ℝ) + m + 4 := by
      unfold radius
      push_cast
      ring
    rw [hReq] at hupper hlower ⊢
    nlinarith [hupper]
  have hcarrier := carrier_upper_distant_le hk (m := m) hr
  have hmfac : (k : ℝ) + m + 6 ≤ ((k : ℝ) + 6) * (m + 1) := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hmpow : (m : ℝ) + 1 ≤ (2 : ℝ) ^ m := by
    exact_mod_cast nat_succ_le_two_pow m
  have hweight :
      ((k : ℝ) + m + 6) * (1 / 4 : ℝ) ^ m ≤
        ((k : ℝ) + 6) * (1 / 2 : ℝ) ^ m := by
    calc
      ((k : ℝ) + m + 6) * (1 / 4 : ℝ) ^ m ≤
          (((k : ℝ) + 6) * (m + 1)) * (1 / 4 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hmfac (by positivity)
      _ ≤ (((k : ℝ) + 6) * (2 : ℝ) ^ m) * (1 / 4 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmpow (by positivity)) (by positivity)
      _ = ((k : ℝ) + 6) * ((2 : ℝ) ^ m * (1 / 4 : ℝ) ^ m) := by ring
      _ = ((k : ℝ) + 6) * (1 / 2 : ℝ) ^ m := by
        rw [← mul_pow]
        norm_num
  unfold packetNormBound
  calc
    carrier (k + 2 + m) r *
        (1 + r / (2 * radius (k + 2 + m)) +
          radius (k + 2 + m) / (2 * r)) ≤
        carrier (k + 2 + m) r * ((k : ℝ) + m + 6) :=
      mul_le_mul_of_nonneg_left hfactor (carrier_nonneg hrpos.le)
    _ ≤ (carrier k r * geometricError k * (1 / 4 : ℝ) ^ m) *
        ((k : ℝ) + m + 6) :=
      mul_le_mul_of_nonneg_right hcarrier (by positivity)
    _ = (carrier k r * geometricError k) *
        (((k : ℝ) + m + 6) * (1 / 4 : ℝ) ^ m) := by ring
    _ ≤ (carrier k r * geometricError k) *
        (((k : ℝ) + 6) * (1 / 2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hweight
        (mul_nonneg (carrier_nonneg hrpos.le) (geometricError_nonneg k))
    _ = ((k : ℝ) + 6) * (carrier k r * geometricError k) *
        (1 / 2 : ℝ) ^ m := by ring

/-- The explicit normalized error for all packets outside the nearest three. -/
def tailError (k : ℕ) : ℝ :=
  ((k : ℝ) * (k + 3) + 2 * (k + 6)) * geometricError k

lemma tailError_nonneg (k : ℕ) : 0 ≤ tailError k := by
  unfold tailError
  exact mul_nonneg (by positivity) (geometricError_nonneg k)

lemma sum_lower_packetNormBound_le {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    (∑ j ∈ Finset.range (k - 1), packetNormBound j r) ≤
      (k : ℝ) * (k + 3) * (carrier k r * geometricError k) := by
  calc
    (∑ j ∈ Finset.range (k - 1), packetNormBound j r) ≤
        ∑ _j ∈ Finset.range (k - 1),
          ((k : ℝ) + 3) * (carrier k r * geometricError k) := by
      apply Finset.sum_le_sum
      intro j hj
      exact packetNormBound_lower_distant_le hk (by
        simp only [Finset.mem_range] at hj
        omega) hr
    _ = ((k - 1 : ℕ) : ℝ) *
        (((k : ℝ) + 3) * (carrier k r * geometricError k)) := by simp
    _ ≤ (k : ℝ) * (k + 3) * (carrier k r * geometricError k) := by
      have hkcast : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      have hnonneg : 0 ≤ ((k : ℝ) + 3) * (carrier k r * geometricError k) :=
        mul_nonneg (by positivity) (mul_nonneg (carrier_nonneg (by
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith [hr.1])) (geometricError_nonneg k))
      calc
        ((k - 1 : ℕ) : ℝ) *
            (((k : ℝ) + 3) * (carrier k r * geometricError k)) ≤
            (k : ℝ) * (((k : ℝ) + 3) * (carrier k r * geometricError k)) :=
          mul_le_mul_of_nonneg_right hkcast hnonneg
        _ = (k : ℝ) * (k + 3) * (carrier k r * geometricError k) := by ring

lemma tsum_upper_packetNormBound_le {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    (∑' m : ℕ, packetNormBound (k + 2 + m) r) ≤
      2 * (k + 6) * (carrier k r * geometricError k) := by
  let C : ℝ := ((k : ℝ) + 6) * (carrier k r * geometricError k)
  have hgeom : HasSum (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) 2 := by
    convert hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have hmajor : Summable (fun m : ℕ ↦ C * (1 / 2 : ℝ) ^ m) :=
    hgeom.summable.mul_left C
  have hpoint : ∀ m : ℕ,
      packetNormBound (k + 2 + m) r ≤ C * (1 / 2 : ℝ) ^ m := by
    intro m
    exact packetNormBound_upper_distant_le hk hr
  have hleft : Summable (fun m : ℕ ↦ packetNormBound (k + 2 + m) r) := by
    apply Summable.of_nonneg_of_le
    · intro m
      exact packetNormBound_nonneg (by
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith [hr.1])
    · exact hpoint
    · exact hmajor
  calc
    (∑' m : ℕ, packetNormBound (k + 2 + m) r) ≤
        ∑' m : ℕ, C * (1 / 2 : ℝ) ^ m :=
      hleft.tsum_le_tsum hpoint hmajor
    _ = C * 2 := (hgeom.mul_left C).tsum_eq
    _ = 2 * (k + 6) * (carrier k r * geometricError k) := by
      dsimp [C]
      ring

lemma tailError_tendsto_zero : Tendsto tailError atTop (𝓝 0) := by
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have h := h2.add ((h1.const_mul 5).add (h0.const_mul 12))
  convert h using 1
  · funext n
    simp [tailError, geometricError]
    ring
  · norm_num

lemma distant_packetNormBounds_le {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    (∑ j ∈ Finset.range (k - 1), packetNormBound j r) +
        (∑' m : ℕ, packetNormBound (k + 2 + m) r) ≤
      tailError k * carrier k r := by
  have hlower := sum_lower_packetNormBound_le hk hr
  have hupper := tsum_upper_packetNormBound_le hk hr
  calc
    (∑ j ∈ Finset.range (k - 1), packetNormBound j r) +
        (∑' m : ℕ, packetNormBound (k + 2 + m) r) ≤
        (k : ℝ) * (k + 3) * (carrier k r * geometricError k) +
          2 * (k + 6) * (carrier k r * geometricError k) := add_le_add hlower hupper
    _ = tailError k * carrier k r := by
      unfold tailError
      ring

/-- Uniform error used when the three active packets are replaced by their ideal shapes. -/
def activeError (k : ℕ) : ℝ := 2 / (k : ℝ)

lemma activeError_nonneg (k : ℕ) : 0 ≤ activeError k := by
  unfold activeError
  positivity

lemma activeError_tendsto_zero : Tendsto activeError atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦ (2 : ℝ) / (k : ℝ)) atTop (𝓝 0)
  simpa using tendsto_const_div_pow (2 : ℝ) 1 (by norm_num)

/-- The Laurent shape of a packet on a circle of radius `r`. -/
def radialShape (j : ℕ) (r : ℝ) (w : ℂ) : ℂ :=
  1 + (packetSign j / 2 : ℂ) *
    (((r / radius j : ℝ) : ℂ) * w +
      ((radius j / r : ℝ) : ℂ) * w⁻¹)

/-- The complementary ideal shape obtained when the packet radius equals the circle radius. -/
def idealShape (j : ℕ) (w : ℂ) : ℂ :=
  1 + (packetSign j / 2 : ℂ) * (w + w⁻¹)

/-- The idealized packet on a circle. -/
def idealPacket (j : ℕ) (r : ℝ) (w : ℂ) : ℂ :=
  (carrier j r : ℂ) * w ^ carrierIndex j * idealShape j w

/-- Radial error in replacing a packet by its ideal shape. -/
def radialError (j : ℕ) (r : ℝ) : ℝ :=
  |r / radius j - 1| / 2 + |radius j / r - 1| / 2

lemma radialError_le_of_close {R r K : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hK : 0 < K) (hKR : K ≤ R) (hKr : K ≤ r) (hclose : |r - R| ≤ 2) :
    |r / R - 1| / 2 + |R / r - 1| / 2 ≤ 2 / K := by
  have hfirst : |r / R - 1| ≤ 2 / K := by
    rw [show r / R - 1 = (r - R) / R by field_simp [ne_of_gt hR],
      abs_div, abs_of_pos hR]
    apply (div_le_div_iff₀ hR hK).2
    calc
      |r - R| * K ≤ 2 * K := mul_le_mul_of_nonneg_right hclose hK.le
      _ ≤ 2 * R := mul_le_mul_of_nonneg_left hKR (by norm_num)
  have hsecond : |R / r - 1| ≤ 2 / K := by
    rw [show R / r - 1 = (R - r) / r by field_simp [ne_of_gt hr],
      abs_div, abs_of_pos hr, abs_sub_comm]
    apply (div_le_div_iff₀ hr hK).2
    calc
      |r - R| * K ≤ 2 * K := mul_le_mul_of_nonneg_right hclose hK.le
      _ ≤ 2 * r := mul_le_mul_of_nonneg_left hKr (by norm_num)
  nlinarith

lemma active_radialError_le {j k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) (hj : j = k - 1 ∨ j = k ∨ j = k + 1) :
    radialError j r ≤ activeError k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hrpos : 0 < r := by linarith [hr.1, hkpos]
  have hKr : (k : ℝ) ≤ r := by linarith [hr.1]
  rcases hj with hj | hj | hj
  · subst j
    have hRform : radius (k - 1) = (k : ℝ) + 1 := by
      unfold radius
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast
      ring
    unfold radialError activeError
    apply radialError_le_of_close (R := radius (k - 1)) (r := r) (K := k)
      (radius_pos _) hrpos hkpos
    · rw [hRform]
      linarith
    · exact hKr
    · rw [hRform]
      apply abs_le.2
      constructor <;> linarith [hr.1, hr.2]
  · subst j
    unfold radialError activeError
    apply radialError_le_of_close (R := radius k) (r := r) (K := k)
      (radius_pos _) hrpos hkpos
    · unfold radius
      push_cast
      linarith
    · exact hKr
    · unfold radius
      push_cast
      apply abs_le.2
      constructor <;> linarith [hr.1, hr.2]
  · subst j
    unfold radialError activeError
    apply radialError_le_of_close (R := radius (k + 1)) (r := r) (K := k)
      (radius_pos _) hrpos hkpos
    · unfold radius
      push_cast
      linarith
    · exact hKr
    · unfold radius
      push_cast
      apply abs_le.2
      constructor <;> linarith [hr.1, hr.2]

lemma packetSign_succ (k : ℕ) : packetSign (k + 1) = -packetSign k := by
  simp [packetSign, pow_succ]

lemma packetSign_sq (k : ℕ) : packetSign k * packetSign k = 1 := by
  rw [← pow_two, packetSign]
  simp [← pow_mul]

lemma packetSign_pred {k : ℕ} (hk : 1 ≤ k) :
    packetSign (k - 1) = -packetSign k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [packetSign_succ]

lemma pow_mul_inv_eq_pow_pred {w : ℂ} (hw : w ≠ 0) {n : ℕ} (hn : 0 < n) :
    w ^ n * w⁻¹ = w ^ (n - 1) := by
  have hn' : n - 1 + 1 = n := by omega
  calc
    w ^ n * w⁻¹ = (w ^ (n - 1) * w) * w⁻¹ := by rw [← pow_succ, hn']
    _ = w ^ (n - 1) := by field_simp

lemma packet_on_circle (j : ℕ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) :
    packet j ((r : ℂ) * w) =
      (carrier j r : ℂ) * w ^ carrierIndex j * radialShape j r w := by
  have hindex := carrierIndex_pos j
  have hpowpred :
      ((r : ℂ) * w) ^ (carrierIndex j - 1) =
        (r : ℂ) ^ (carrierIndex j - 1) * w ^ (carrierIndex j - 1) := by
    rw [mul_pow]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  unfold packet radialShape carrier
  rw [mul_pow, mul_pow, hpowpred, pow_add, pow_add]
  simp only [pow_one]
  have hrpow :
      (r : ℂ) ^ (carrierIndex j - 1) * r = (r : ℂ) ^ carrierIndex j := by
    rw [← pow_succ]
    congr
    omega
  have hwpow := pow_mul_inv_eq_pow_pred hw hindex
  push_cast
  field_simp [hrC, Complex.ofReal_ne_zero.mpr (ne_of_gt (radius_pos j)), hw]
  ring_nf at hrpow hwpow ⊢
  rw [← hrpow, ← hwpow]
  field_simp [hw]
  ring

lemma idealShape_eq_real {j : ℕ} {w : ℂ} (hw : ‖w‖ = 1) :
    idealShape j w = ((1 + packetSign j * w.re : ℝ) : ℂ) := by
  unfold idealShape
  rw [Complex.inv_eq_conj hw, Complex.add_conj]
  push_cast
  ring

lemma idealShape_real_nonneg {j : ℕ} {w : ℂ} (hw : ‖w‖ = 1) :
    0 ≤ 1 + packetSign j * w.re := by
  have hre : |w.re| ≤ 1 := by
    simpa [hw] using Complex.abs_re_le_norm w
  have habs : |packetSign j * w.re| ≤ 1 := by
    rw [abs_mul, packetSign_abs, one_mul]
    exact hre
  exact (abs_le.mp habs).1 |> fun h ↦ by linarith

lemma norm_idealShape {j : ℕ} {w : ℂ} (hw : ‖w‖ = 1) :
    ‖idealShape j w‖ = 1 + packetSign j * w.re := by
  rw [idealShape_eq_real hw, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (idealShape_real_nonneg hw)]

lemma norm_idealPacket {j : ℕ} {r : ℝ} (hr : 0 ≤ r) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖idealPacket j r w‖ =
      carrier j r * (1 + packetSign j * w.re) := by
  unfold idealPacket
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (carrier_nonneg hr), Complex.norm_pow, hw, one_pow,
    norm_idealShape hw]
  ring

/-- Sum of the three idealized packets nearest the dominant carrier. -/
def idealThree (k : ℕ) (r : ℝ) (w : ℂ) : ℂ :=
  idealPacket k r w + idealPacket (k - 1) r w + idealPacket (k + 1) r w

lemma norm_idealThree_le {k : ℕ} {r : ℝ} (hk : 2 ≤ k) (hr : InCell k r)
    {w : ℂ} (hw : ‖w‖ = 1) :
    ‖idealThree k r w‖ ≤ 2 * (1 + geometricError k) * carrier k r := by
  have hr0 : 0 ≤ r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  let B : ℝ := carrier k r
  let A : ℝ := carrier (k - 1) r + carrier (k + 1) r
  let x : ℝ := packetSign k * w.re
  have hB : 0 ≤ B := carrier_nonneg hr0
  have hA : 0 ≤ A := add_nonneg (carrier_nonneg hr0) (carrier_nonneg hr0)
  have hxabs : |x| ≤ 1 := by
    dsimp [x]
    rw [abs_mul, packetSign_abs, one_mul]
    simpa [hw] using Complex.abs_re_le_norm w
  have hxlo : 0 ≤ 1 - x := by linarith [abs_le.mp hxabs]
  have hxhi : 0 ≤ 1 + x := by linarith [abs_le.mp hxabs]
  have hAB : A ≤ B * (1 + geometricError k) := by
    dsimp [A, B]
    exact neighbor_carriers_le hk hr
  have hscalar : B * (1 + x) + A * (1 - x) ≤
      2 * (1 + geometricError k) * B := by
    rcases le_total A B with hAle | hBle
    · calc
        B * (1 + x) + A * (1 - x) ≤
            B * (1 + x) + B * (1 - x) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hAle hxlo)
        _ = 2 * B := by ring
        _ ≤ 2 * (1 + geometricError k) * B := by
          nlinarith [geometricError_nonneg k]
    · calc
        B * (1 + x) + A * (1 - x) ≤
            A * (1 + x) + A * (1 - x) :=
          add_le_add (mul_le_mul_of_nonneg_right hBle hxhi) le_rfl
        _ = 2 * A := by ring
        _ ≤ 2 * (B * (1 + geometricError k)) :=
          mul_le_mul_of_nonneg_left hAB (by norm_num)
        _ = 2 * (1 + geometricError k) * B := by ring
  unfold idealThree
  calc
    ‖idealPacket k r w + idealPacket (k - 1) r w + idealPacket (k + 1) r w‖ ≤
        ‖idealPacket k r w‖ + ‖idealPacket (k - 1) r w‖ +
          ‖idealPacket (k + 1) r w‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = B * (1 + x) + A * (1 - x) := by
      rw [norm_idealPacket hr0 hw, norm_idealPacket hr0 hw,
        norm_idealPacket hr0 hw, packetSign_pred (by omega), packetSign_succ]
      dsimp [A, B, x]
      ring
    _ ≤ 2 * (1 + geometricError k) * carrier k r := by
      simpa only [B] using hscalar

/-- The point on the unit circle at which the central ideal packet peaks. -/
def peakPoint (k : ℕ) : ℂ := packetSign k

lemma norm_peakPoint (k : ℕ) : ‖peakPoint k‖ = 1 := by
  unfold peakPoint
  rw [Complex.norm_real, Real.norm_eq_abs, packetSign_abs]

lemma idealShape_peak (k : ℕ) : idealShape k (peakPoint k) = 2 := by
  rw [idealShape_eq_real (norm_peakPoint k)]
  unfold peakPoint
  simp only [Complex.ofReal_re]
  rw [packetSign_sq]
  norm_num

lemma idealShape_pred_peak {k : ℕ} (hk : 1 ≤ k) :
    idealShape (k - 1) (peakPoint k) = 0 := by
  rw [idealShape_eq_real (norm_peakPoint k)]
  unfold peakPoint
  simp only [Complex.ofReal_re, packetSign_pred hk]
  apply Complex.ofReal_eq_zero.mpr
  nlinarith [packetSign_sq k]

lemma idealShape_succ_peak (k : ℕ) :
    idealShape (k + 1) (peakPoint k) = 0 := by
  rw [idealShape_eq_real (norm_peakPoint k)]
  unfold peakPoint
  simp only [Complex.ofReal_re, packetSign_succ]
  apply Complex.ofReal_eq_zero.mpr
  nlinarith [packetSign_sq k]

lemma norm_idealThree_peak {k : ℕ} {r : ℝ} (hk : 2 ≤ k) (hr : InCell k r) :
    ‖idealThree k r (peakPoint k)‖ = 2 * carrier k r := by
  have hr0 : 0 ≤ r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hprev : idealPacket (k - 1) r (peakPoint k) = 0 := by
    unfold idealPacket
    rw [idealShape_pred_peak (by omega)]
    ring
  have hnext : idealPacket (k + 1) r (peakPoint k) = 0 := by
    unfold idealPacket
    rw [idealShape_succ_peak]
    ring
  unfold idealThree
  rw [hprev, hnext, add_zero, add_zero, norm_idealPacket hr0 (norm_peakPoint k)]
  unfold peakPoint
  simp only [Complex.ofReal_re]
  rw [show packetSign k * packetSign k = 1 from packetSign_sq k]
  ring

lemma radialShape_sub_idealShape_bound {j : ℕ} {r : ℝ} {w : ℂ}
    (hw : ‖w‖ = 1) :
    ‖radialShape j r w - idealShape j w‖ ≤ radialError j r := by
  unfold radialShape idealShape radialError
  have hsign : ‖(packetSign j / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, packetSign_abs]
    norm_num
  rw [show
    1 + (packetSign j / 2 : ℂ) *
          (((r / radius j : ℝ) : ℂ) * w +
            ((radius j / r : ℝ) : ℂ) * w⁻¹) -
        (1 + (packetSign j / 2 : ℂ) * (w + w⁻¹)) =
      (packetSign j / 2 : ℂ) *
        ((((r / radius j - 1 : ℝ) : ℂ) * w) +
          (((radius j / r - 1 : ℝ) : ℂ) * w⁻¹)) by
        push_cast
        ring]
  rw [Complex.norm_mul, hsign]
  calc
    (1 / 2 : ℝ) *
        ‖(((r / radius j - 1 : ℝ) : ℂ) * w) +
          (((radius j / r - 1 : ℝ) : ℂ) * w⁻¹)‖ ≤
      (1 / 2 : ℝ) *
        (‖((r / radius j - 1 : ℝ) : ℂ) * w‖ +
          ‖((radius j / r - 1 : ℝ) : ℂ) * w⁻¹‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = |r / radius j - 1| / 2 + |radius j / r - 1| / 2 := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, hw,
        Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv, hw]
      norm_num
      ring

lemma norm_packet_sub_idealPacket_le (j : ℕ) {r : ℝ} (hr : 0 < r)
    {w : ℂ} (hw : ‖w‖ = 1) :
    ‖packet j ((r : ℂ) * w) - idealPacket j r w‖ ≤
      carrier j r * radialError j r := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by simp [hw])
  rw [packet_on_circle j hr hw0]
  unfold idealPacket
  rw [← mul_sub]
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (carrier_pos hr), Complex.norm_pow, hw, one_pow]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (radialShape_sub_idealShape_bound hw)
      (carrier_pos hr).le

/-- The finite lower and reindexed infinite upper parts of the packet series. -/
def lowerPackets (k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (k - 1), packet j z

def upperPackets (k : ℕ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, packet (k + 2 + m) z

lemma function_packet_decomposition {k : ℕ} (hk : 2 ≤ k) (z : ℂ) :
    function z = lowerPackets k z + packet (k - 1) z + packet k z +
      packet (k + 1) z + upperPackets k z := by
  have hs := summable_packet z
  have hsplit := (hs.sum_add_tsum_nat_add (k + 2)).symm
  rw [function_eq_tsum_packet]
  calc
    (∑' j : ℕ, packet j z) =
        (∑ j ∈ Finset.range (k + 2), packet j z) +
          ∑' m : ℕ, packet (m + (k + 2)) z := hsplit
    _ = lowerPackets k z + packet (k - 1) z + packet k z +
        packet (k + 1) z + upperPackets k z := by
      have htail : (∑' m : ℕ, packet (m + (k + 2)) z) = upperPackets k z := by
        unfold upperPackets
        apply tsum_congr
        intro m
        apply congrArg (fun j : ℕ ↦ packet j z)
        omega
      rw [htail]
      rw [show k + 2 = ((k - 1) + 1) + 2 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      unfold lowerPackets
      rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega]

lemma summable_upper_packetNormBound {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    Summable (fun m : ℕ ↦ packetNormBound (k + 2 + m) r) := by
  let C : ℝ := ((k : ℝ) + 6) * (carrier k r * geometricError k)
  have hgeom : Summable (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmajor : Summable (fun m : ℕ ↦ C * (1 / 2 : ℝ) ^ m) :=
    hgeom.mul_left C
  apply Summable.of_nonneg_of_le
  · intro m
    exact packetNormBound_nonneg (by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith [hr.1])
  · intro m
    exact packetNormBound_upper_distant_le hk hr
  · exact hmajor

lemma summable_norm_upperPackets {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) {w : ℂ} (hw : ‖w‖ = 1) :
    Summable (fun m : ℕ ↦ ‖packet (k + 2 + m) ((r : ℂ) * w)‖) := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  apply Summable.of_nonneg_of_le
  · intro m
    exact norm_nonneg _
  · intro m
    have hz : ‖(r : ℂ) * w‖ = r := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, hw,
        mul_one]
    have hzpos : 0 < ‖(r : ℂ) * w‖ := by rw [hz]; exact hrpos
    simpa only [hz] using
      (norm_packet_le (j := k + 2 + m) (z := (r : ℂ) * w) hzpos)
  · exact summable_upper_packetNormBound hk hr

lemma norm_add_five_le (a b c d e : ℂ) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)

lemma active_packet_error_le {j k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) (hj : j = k - 1 ∨ j = k ∨ j = k + 1)
    {w : ℂ} (hw : ‖w‖ = 1) :
    ‖packet j ((r : ℂ) * w) - idealPacket j r w‖ ≤
      carrier k r * activeError k := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hpacket := norm_packet_sub_idealPacket_le j hrpos hw
  have hcarrier : carrier j r ≤ carrier k r := carrier_le_dominant hr
  have hradial := active_radialError_le hk hr hj
  exact hpacket.trans (mul_le_mul hcarrier hradial
    (by unfold radialError; positivity) (carrier_nonneg hrpos.le))

/-- Total normalized error between the function and the ideal three-packet sum. -/
def circleError (k : ℕ) : ℝ := 3 * activeError k + tailError k

lemma circleError_nonneg (k : ℕ) : 0 ≤ circleError k := by
  unfold circleError
  exact add_nonneg (mul_nonneg (by norm_num) (activeError_nonneg k))
    (tailError_nonneg k)

lemma circleError_tendsto_zero : Tendsto circleError atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦ 3 * activeError k + tailError k) atTop (𝓝 0)
  simpa using (activeError_tendsto_zero.const_mul 3).add tailError_tendsto_zero

lemma norm_function_sub_idealThree_le {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖function ((r : ℂ) * w) - idealThree k r w‖ ≤
      circleError k * carrier k r := by
  let z : ℂ := (r : ℂ) * w
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hz : ‖z‖ = r := by
    dsimp [z]
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, hw,
      mul_one]
  have hdecomp := function_packet_decomposition hk z
  have halgebra :
      lowerPackets k z + packet (k - 1) z + packet k z + packet (k + 1) z +
          upperPackets k z - idealThree k r w =
        lowerPackets k z + (packet (k - 1) z - idealPacket (k - 1) r w) +
          (packet k z - idealPacket k r w) +
          (packet (k + 1) z - idealPacket (k + 1) r w) + upperPackets k z := by
    unfold idealThree
    ring
  rw [hdecomp, halgebra]
  have hlowerNorm : ‖lowerPackets k z‖ ≤
      ∑ j ∈ Finset.range (k - 1), packetNormBound j r := by
    unfold lowerPackets
    exact (norm_sum_le (Finset.range (k - 1)) (fun j ↦ packet j z)).trans
      (Finset.sum_le_sum fun j hj ↦ by
        have := norm_packet_le (j := j) (z := z) (by simpa [hz])
        simpa only [hz] using this)
  have hupperNorm : ‖upperPackets k z‖ ≤
      ∑' m : ℕ, packetNormBound (k + 2 + m) r := by
    unfold upperPackets
    have hsNorm := summable_norm_upperPackets hk hr hw
    exact (norm_tsum_le_tsum_norm hsNorm).trans
      (hsNorm.tsum_le_tsum (fun m ↦ by
        have := norm_packet_le (j := k + 2 + m) (z := z) (by simpa [hz])
        simpa only [hz] using this) (summable_upper_packetNormBound hk hr))
  have hePrev := active_packet_error_le hk hr (Or.inl rfl) hw
  have heSelf := active_packet_error_le hk hr (Or.inr (Or.inl rfl)) hw
  have heNext := active_packet_error_le hk hr (Or.inr (Or.inr rfl)) hw
  calc
    ‖lowerPackets k z + (packet (k - 1) z - idealPacket (k - 1) r w) +
          (packet k z - idealPacket k r w) +
          (packet (k + 1) z - idealPacket (k + 1) r w) + upperPackets k z‖ ≤
        ‖lowerPackets k z‖ +
          ‖packet (k - 1) z - idealPacket (k - 1) r w‖ +
          ‖packet k z - idealPacket k r w‖ +
          ‖packet (k + 1) z - idealPacket (k + 1) r w‖ + ‖upperPackets k z‖ :=
      norm_add_five_le _ _ _ _ _
    _ ≤ (∑ j ∈ Finset.range (k - 1), packetNormBound j r) +
          carrier k r * activeError k + carrier k r * activeError k +
          carrier k r * activeError k +
          (∑' m : ℕ, packetNormBound (k + 2 + m) r) :=
      add_le_add (add_le_add (add_le_add (add_le_add hlowerNorm hePrev) heSelf) heNext)
        hupperNorm
    _ ≤ circleError k * carrier k r := by
      have htail := distant_packetNormBounds_le hk hr
      unfold circleError
      nlinarith

lemma norm_exp_mul_I (θ : ℝ) : ‖Complex.exp (θ * Complex.I)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I θ

lemma exp_nat_pi_mul_I (k : ℕ) :
    Complex.exp (((k : ℝ) * Real.pi) * Complex.I) = peakPoint k := by
  calc
    Complex.exp (((k : ℝ) * Real.pi) * Complex.I) =
        Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
      congr 1
      push_cast
      ring
    _ = Complex.exp ((Real.pi : ℂ) * Complex.I) ^ k :=
      Complex.exp_nat_mul ((Real.pi : ℂ) * Complex.I) k
    _ = (-1 : ℂ) ^ k := by rw [Complex.exp_pi_mul_I]
    _ = peakPoint k := by simp [peakPoint, packetSign]

/-- Upper normalized bound for the maximum modulus on cell `k`. -/
def modulusUpperError (k : ℕ) : ℝ :=
  2 * geometricError k + circleError k

/-- Lower normalized error for the maximum modulus on cell `k`. -/
def modulusLowerError (k : ℕ) : ℝ := circleError k

lemma modulusUpperError_nonneg (k : ℕ) : 0 ≤ modulusUpperError k := by
  unfold modulusUpperError
  exact add_nonneg (mul_nonneg (by norm_num) (geometricError_nonneg k))
    (circleError_nonneg k)

lemma modulusLowerError_nonneg (k : ℕ) : 0 ≤ modulusLowerError k :=
  circleError_nonneg k

lemma geometricError_tendsto_zero : Tendsto geometricError atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) atTop (𝓝 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma modulusUpperError_tendsto_zero : Tendsto modulusUpperError atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦ 2 * geometricError k + circleError k) atTop (𝓝 0)
  simpa using (geometricError_tendsto_zero.const_mul 2).add circleError_tendsto_zero

lemma modulusLowerError_tendsto_zero : Tendsto modulusLowerError atTop (𝓝 0) :=
  circleError_tendsto_zero

lemma norm_function_circle_upper {k : ℕ} {r θ : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    ‖function (r * Complex.exp (θ * Complex.I))‖ ≤
      (2 + modulusUpperError k) * carrier k r := by
  let w : ℂ := Complex.exp (θ * Complex.I)
  have hw : ‖w‖ = 1 := norm_exp_mul_I θ
  have happ := norm_function_sub_idealThree_le hk hr hw
  have hideal := norm_idealThree_le hk hr hw
  change ‖function ((r : ℂ) * w)‖ ≤ _
  calc
    ‖function ((r : ℂ) * w)‖ =
        ‖(function ((r : ℂ) * w) - idealThree k r w) + idealThree k r w‖ := by
      congr 1
      ring
    _ ≤ ‖function ((r : ℂ) * w) - idealThree k r w‖ + ‖idealThree k r w‖ :=
      norm_add_le _ _
    _ ≤ circleError k * carrier k r +
        2 * (1 + geometricError k) * carrier k r := add_le_add happ hideal
    _ = (2 + modulusUpperError k) * carrier k r := by
      unfold modulusUpperError
      ring

lemma norm_function_peak_lower {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    (2 - modulusLowerError k) * carrier k r ≤
      ‖function ((r : ℂ) * peakPoint k)‖ := by
  have happ := norm_function_sub_idealThree_le hk hr (norm_peakPoint k)
  have hideal := norm_idealThree_peak hk hr
  have htri : ‖idealThree k r (peakPoint k)‖ ≤
      ‖function ((r : ℂ) * peakPoint k)‖ +
        ‖function ((r : ℂ) * peakPoint k) - idealThree k r (peakPoint k)‖ := by
    calc
      ‖idealThree k r (peakPoint k)‖ =
          ‖function ((r : ℂ) * peakPoint k) -
              (function ((r : ℂ) * peakPoint k) - idealThree k r (peakPoint k))‖ := by
        congr 1
        ring
      _ ≤ ‖function ((r : ℂ) * peakPoint k)‖ +
          ‖function ((r : ℂ) * peakPoint k) - idealThree k r (peakPoint k)‖ :=
        norm_sub_le _ _
  unfold modulusLowerError
  rw [hideal] at htri
  nlinarith

lemma maximumModulus_upper {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    maximumModulus function r ≤ (2 + modulusUpperError k) * carrier k r := by
  unfold maximumModulus
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro y ⟨θ, rfl⟩
    exact norm_function_circle_upper hk hr

lemma maximumModulus_lower {k : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    (2 - modulusLowerError k) * carrier k r ≤ maximumModulus function r := by
  have hbdd : BddAbove (Set.range fun θ : ℝ ↦
      ‖function (r * Complex.exp (θ * Complex.I))‖) := by
    refine ⟨(2 + modulusUpperError k) * carrier k r, ?_⟩
    rintro y ⟨θ, rfl⟩
    exact norm_function_circle_upper hk hr
  have hmem : ‖function ((r : ℂ) * peakPoint k)‖ ∈
      Set.range (fun θ : ℝ ↦ ‖function (r * Complex.exp (θ * Complex.I))‖) := by
    refine ⟨(k : ℝ) * Real.pi, ?_⟩
    change ‖function ((r : ℂ) *
      Complex.exp (((((k : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I)))‖ =
        ‖function ((r : ℂ) * peakPoint k)‖
    have hexp : Complex.exp (((((k : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I)) =
        peakPoint k := by
      rw [show ((((k : ℝ) * Real.pi : ℝ) : ℂ)) =
        (k : ℂ) * (Real.pi : ℂ) by push_cast; rfl]
      exact exp_nat_pi_mul_I k
    rw [hexp]
  exact (norm_function_peak_lower hk hr).trans (by
    unfold maximumModulus
    exact le_csSup hbdd hmem)

lemma packetSupport_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (packetSupport i) (packetSupport j) := by
  apply Finset.disjoint_left.2
  intro n hni hnj
  simp only [packetSupport, Finset.mem_insert, Finset.mem_singleton] at hni hnj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsep := carrierIndex_add_four_le_of_lt hlt
    rcases hni with hni | hni | hni <;> rcases hnj with hnj | hnj | hnj <;> omega
  · have hsep := carrierIndex_add_four_le_of_lt hgt
    rcases hni with hni | hni | hni <;> rcases hnj with hnj | hnj | hnj <;> omega

lemma packetCoefficient_ne_zero_mem {j n : ℕ} (h : packetCoefficient j n ≠ 0) :
    n ∈ packetSupport j := by
  contrapose! h
  exact packetCoefficient_eq_zero_of_not_mem h

lemma packetCoefficient_unique {i j n : ℕ} (hi : packetCoefficient i n ≠ 0)
    (hj : packetCoefficient j n ≠ 0) : i = j := by
  by_contra hij
  exact Finset.disjoint_left.1 (packetSupport_disjoint hij)
    (packetCoefficient_ne_zero_mem hi) (packetCoefficient_ne_zero_mem hj)

lemma coeff_eq_packetCoefficient_of_ne_zero {j n : ℕ}
    (hj : packetCoefficient j n ≠ 0) : coeff n = packetCoefficient j n := by
  have hjle : j ≤ n := by
    by_contra h
    exact hj (packetCoefficient_eq_zero_of_lt (by omega))
  rw [coeff]
  apply Finset.sum_eq_single j
  · intro i hi hij
    by_contra hi0
    exact hij (packetCoefficient_unique hi0 hj)
  · simp only [Finset.mem_range, not_lt]
    omega

lemma coeff_eq_zero_or_packetCoefficient (n : ℕ) :
    coeff n = 0 ∨ ∃ j : ℕ, coeff n = packetCoefficient j n := by
  by_cases h : ∃ j : ℕ, packetCoefficient j n ≠ 0
  · obtain ⟨j, hj⟩ := h
    exact Or.inr ⟨j, coeff_eq_packetCoefficient_of_ne_zero hj⟩
  · left
    push_neg at h
    unfold coeff
    exact Finset.sum_eq_zero fun j hj ↦ h j

lemma norm_packetCoefficient_term_le_packetNormBound (j n : ℕ) {r : ℝ}
    (hr : 0 < r) :
    ‖packetCoefficient j n‖ * r ^ n ≤ packetNormBound j r := by
  have hA : 0 ≤ carrier j r := carrier_nonneg hr.le
  have hupper : 0 ≤ carrier j r * r / (2 * radius j) :=
    div_nonneg (mul_nonneg hA hr.le) (mul_nonneg (by norm_num) (radius_pos j).le)
  have hlower : 0 ≤ weightedCarrier j r / (2 * r) :=
    div_nonneg (weightedCarrier_nonneg hr.le) (mul_nonneg (by norm_num) hr.le)
  by_cases h₀ : n = carrierIndex j
  · subst n
    rw [packetCoefficient, if_pos rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (carrierCoeff_pos j)]
    change carrier j r ≤ packetNormBound j r
    unfold packetNormBound
    have hfactor : 1 ≤ 1 + r / (2 * radius j) + radius j / (2 * r) := by
      have hu : 0 ≤ r / (2 * radius j) :=
        div_nonneg hr.le (mul_nonneg (by norm_num) (radius_pos j).le)
      have hl : 0 ≤ radius j / (2 * r) :=
        div_nonneg (radius_pos j).le (mul_nonneg (by norm_num) hr.le)
      linarith
    simpa using mul_le_mul_of_nonneg_left hfactor hA
  by_cases h₁ : n = carrierIndex j + 1
  · subst n
    rw [packetCoefficient, if_neg h₀, if_pos rfl]
    have hz : ‖((r : ℝ) : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hexact := norm_upper_coefficient_term j (r : ℂ)
    rw [Complex.norm_mul, Complex.norm_pow, hz] at hexact
    change ‖(packetSign j * carrierCoeff j / (2 * radius j) : ℂ)‖ *
      r ^ (carrierIndex j + 1) ≤ packetNormBound j r
    rw [hexact]
    calc
      carrier j r * r / (2 * radius j) ≤
          carrier j r + carrier j r * r / (2 * radius j) +
            weightedCarrier j r / (2 * r) := by linarith
      _ = packetNormBound j r := by
        unfold packetNormBound weightedCarrier
        ring
  by_cases h₂ : n = carrierIndex j - 1
  · subst n
    rw [packetCoefficient, if_neg h₀, if_neg h₁, if_pos rfl]
    have hz : ‖((r : ℝ) : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hexact := norm_lower_coefficient_term j (r : ℂ) (by rw [hz]; exact hr)
    rw [Complex.norm_mul, Complex.norm_pow, hz] at hexact
    change ‖(packetSign j * carrierCoeff j * radius j / 2 : ℂ)‖ *
      r ^ (carrierIndex j - 1) ≤ packetNormBound j r
    rw [hexact]
    calc
      weightedCarrier j r / (2 * r) ≤
          carrier j r + carrier j r * r / (2 * radius j) +
            weightedCarrier j r / (2 * r) := by linarith
      _ = packetNormBound j r := by
        unfold packetNormBound weightedCarrier
        ring
  · rw [packetCoefficient, if_neg h₀, if_neg h₁, if_neg h₂, norm_zero, zero_mul]
    exact packetNormBound_nonneg hr

lemma active_packetCoefficient_term_le {j k n : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) (hj : j = k - 1 ∨ j = k ∨ j = k + 1) :
    ‖packetCoefficient j n‖ * r ^ n ≤ carrier k r := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcarrier : carrier j r ≤ carrier k r := carrier_le_dominant hr
  have hradiusUpper : r ≤ 2 * radius j := by
    rcases hj with hj | hj | hj
    · subst j
      unfold radius
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast
      nlinarith [hr.2]
    · subst j
      unfold radius
      push_cast
      nlinarith [hr.2]
    · subst j
      unfold radius
      push_cast
      nlinarith [hr.2]
  have hradiusLower : radius j ≤ 2 * r := by
    rcases hj with hj | hj | hj
    · subst j
      unfold radius
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast
      nlinarith [hr.1]
    · subst j
      unfold radius
      push_cast
      nlinarith [hr.1]
    · subst j
      unfold radius
      push_cast
      nlinarith [hr.1]
  by_cases h₀ : n = carrierIndex j
  · subst n
    rw [packetCoefficient, if_pos rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (carrierCoeff_pos j)]
    exact hcarrier
  by_cases h₁ : n = carrierIndex j + 1
  · subst n
    rw [packetCoefficient, if_neg h₀, if_pos rfl]
    have hz : ‖((r : ℝ) : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    have hexact := norm_upper_coefficient_term j (r : ℂ)
    rw [Complex.norm_mul, Complex.norm_pow, hz] at hexact
    change ‖(packetSign j * carrierCoeff j / (2 * radius j) : ℂ)‖ *
      r ^ (carrierIndex j + 1) ≤ carrier k r
    rw [hexact]
    have hside : carrier j r * r / (2 * radius j) ≤ carrier j r := by
      apply (div_le_iff₀ (mul_pos (by norm_num) (radius_pos j))).2
      nlinarith [carrier_nonneg (k := j) hrpos.le]
    exact hside.trans hcarrier
  by_cases h₂ : n = carrierIndex j - 1
  · subst n
    rw [packetCoefficient, if_neg h₀, if_neg h₁, if_pos rfl]
    have hz : ‖((r : ℝ) : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    have hexact := norm_lower_coefficient_term j (r : ℂ) (by rw [hz]; exact hrpos)
    rw [Complex.norm_mul, Complex.norm_pow, hz] at hexact
    change ‖(packetSign j * carrierCoeff j * radius j / 2 : ℂ)‖ *
      r ^ (carrierIndex j - 1) ≤ carrier k r
    rw [hexact]
    have hside : weightedCarrier j r / (2 * r) ≤ carrier j r := by
      unfold weightedCarrier
      apply (div_le_iff₀ (mul_pos (by norm_num) hrpos)).2
      nlinarith [carrier_nonneg (k := j) hrpos.le]
    exact hside.trans hcarrier
  · rw [packetCoefficient, if_neg h₀, if_neg h₁, if_neg h₂, norm_zero, zero_mul]
    exact carrier_nonneg hrpos.le

lemma lower_packetCoefficient_term_le_tail {j k n : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hj : j ≤ k - 2) (hr : InCell k r) :
    ‖packetCoefficient j n‖ * r ^ n ≤ tailError k * carrier k r := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hpacket := norm_packetCoefficient_term_le_packetNormBound j n hrpos
  have hlower := packetNormBound_lower_distant_le hk hj hr
  have hC : 0 ≤ carrier k r * geometricError k :=
    mul_nonneg (carrier_nonneg hrpos.le) (geometricError_nonneg k)
  calc
    ‖packetCoefficient j n‖ * r ^ n ≤ packetNormBound j r := hpacket
    _ ≤ ((k : ℝ) + 3) * (carrier k r * geometricError k) := hlower
    _ ≤ ((k : ℝ) * (k + 3) + 2 * (k + 6)) *
        (carrier k r * geometricError k) := by
      apply mul_le_mul_of_nonneg_right _ hC
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    _ = tailError k * carrier k r := by
      unfold tailError
      ring

lemma upper_packetCoefficient_term_le_tail {k m n : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    ‖packetCoefficient (k + 2 + m) n‖ * r ^ n ≤ tailError k * carrier k r := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hpacket := norm_packetCoefficient_term_le_packetNormBound (k + 2 + m) n hrpos
  have hupper := packetNormBound_upper_distant_le hk (m := m) hr
  have hpow : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hC : 0 ≤ carrier k r * geometricError k :=
    mul_nonneg (carrier_nonneg hrpos.le) (geometricError_nonneg k)
  calc
    ‖packetCoefficient (k + 2 + m) n‖ * r ^ n ≤
        packetNormBound (k + 2 + m) r := hpacket
    _ ≤ ((k : ℝ) + 6) * (carrier k r * geometricError k) *
        (1 / 2 : ℝ) ^ m := hupper
    _ ≤ ((k : ℝ) + 6) * (carrier k r * geometricError k) * 1 :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (by positivity) hC)
    _ = ((k : ℝ) + 6) * (carrier k r * geometricError k) := by ring
    _ ≤ 2 * ((k : ℝ) + 6) * (carrier k r * geometricError k) := by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    _ ≤ ((k : ℝ) * (k + 3) + 2 * (k + 6)) *
        (carrier k r * geometricError k) := by
      apply mul_le_mul_of_nonneg_right _ hC
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    _ = tailError k * carrier k r := by
      unfold tailError
      ring

lemma coefficient_term_le_cell {k n : ℕ} {r : ℝ} (hk : 2 ≤ k)
    (hr : InCell k r) :
    ‖coeff n‖ * r ^ n ≤ (1 + tailError k) * carrier k r := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  rcases coeff_eq_zero_or_packetCoefficient n with hzero | ⟨j, hj⟩
  · rw [hzero, norm_zero, zero_mul]
    exact mul_nonneg (by nlinarith [tailError_nonneg k]) (carrier_nonneg hrpos.le)
  · rw [hj]
    by_cases hlower : j ≤ k - 2
    · have h := lower_packetCoefficient_term_le_tail (n := n) hk hlower hr
      calc
        ‖packetCoefficient j n‖ * r ^ n ≤ tailError k * carrier k r := h
        _ ≤ (1 + tailError k) * carrier k r :=
          mul_le_mul_of_nonneg_right (by linarith) (carrier_nonneg hrpos.le)
    by_cases hupper : k + 2 ≤ j
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hupper
      have h := upper_packetCoefficient_term_le_tail (k := k) (m := m) (n := n) hk hr
      calc
        ‖packetCoefficient (k + 2 + m) n‖ * r ^ n ≤
            tailError k * carrier k r := h
        _ ≤ (1 + tailError k) * carrier k r :=
          mul_le_mul_of_nonneg_right (by linarith) (carrier_nonneg hrpos.le)
    · have hactive : j = k - 1 ∨ j = k ∨ j = k + 1 := by omega
      have h := active_packetCoefficient_term_le hk hr hactive (n := n)
      calc
        ‖packetCoefficient j n‖ * r ^ n ≤ carrier k r := h
        _ ≤ (1 + tailError k) * carrier k r := by
          calc
            carrier k r = 1 * carrier k r := by ring
            _ ≤ (1 + tailError k) * carrier k r :=
              mul_le_mul_of_nonneg_right (by linarith [tailError_nonneg k])
                (carrier_nonneg hrpos.le)

lemma maximumTerm_lower {k : ℕ} {r : ℝ} (hk : 2 ≤ k) (hr : InCell k r) :
    carrier k r ≤ maximumTerm coeff r := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  have hbdd : BddAbove (Set.range fun n : ℕ ↦ ‖coeff n‖ * r ^ n) := by
    refine ⟨(1 + tailError k) * carrier k r, ?_⟩
    rintro y ⟨n, rfl⟩
    exact coefficient_term_le_cell hk hr
  have hmem : carrier k r ∈ Set.range (fun n : ℕ ↦ ‖coeff n‖ * r ^ n) := by
    refine ⟨carrierIndex k, ?_⟩
    change ‖coeff (carrierIndex k)‖ * r ^ carrierIndex k = carrier k r
    rw [coeff_carrierIndex, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (carrierCoeff_pos k)]
    rfl
  unfold maximumTerm
  exact le_csSup hbdd hmem

lemma maximumTerm_upper {k : ℕ} {r : ℝ} (hk : 2 ≤ k) (hr : InCell k r) :
    maximumTerm coeff r ≤ (1 + tailError k) * carrier k r := by
  unfold maximumTerm
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro y ⟨n, rfl⟩
    exact coefficient_term_le_cell hk hr

/-- The two scalar squeeze bounds for the quotient on cell `k`. -/
def ratioLower (k : ℕ) : ℝ := 1 / (2 + modulusUpperError k)

def ratioUpper (k : ℕ) : ℝ :=
  (1 + tailError k) / (2 - modulusLowerError k)

lemma ratioLower_tendsto_half : Tendsto ratioLower atTop (𝓝 (1 / 2 : ℝ)) := by
  change Tendsto (fun k : ℕ ↦ 1 / (2 + modulusUpperError k)) atTop (𝓝 (1 / 2 : ℝ))
  have hden : Tendsto (fun k : ℕ ↦ (2 : ℝ) + modulusUpperError k) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds.add modulusUpperError_tendsto_zero)
  have hnum : Tendsto (fun _k : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  convert hnum.div hden (by norm_num : (2 : ℝ) ≠ 0) using 1
  · funext k
    rfl

lemma ratioUpper_tendsto_half : Tendsto ratioUpper atTop (𝓝 (1 / 2 : ℝ)) := by
  change Tendsto
    (fun k : ℕ ↦ (1 + tailError k) / (2 - modulusLowerError k))
      atTop (𝓝 (1 / 2 : ℝ))
  have hnum : Tendsto (fun k : ℕ ↦ (1 : ℝ) + tailError k) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add tailError_tendsto_zero)
  have hden : Tendsto (fun k : ℕ ↦ (2 : ℝ) - modulusLowerError k) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds.sub modulusLowerError_tendsto_zero)
  convert hnum.div hden (by norm_num : (2 : ℝ) ≠ 0) using 1
  · funext k
    rfl

lemma ratioLower_le_cell {k : ℕ} {r : ℝ} (hk : 2 ≤ k) (hr : InCell k r)
    (hsmall : modulusLowerError k < 1) :
    ratioLower k ≤ maximumTerm coeff r / maximumModulus function r := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  let B : ℝ := carrier k r
  let M : ℝ := maximumModulus function r
  let μ : ℝ := maximumTerm coeff r
  have hB : 0 < B := carrier_pos hrpos
  have hMlower : (2 - modulusLowerError k) * B ≤ M := maximumModulus_lower hk hr
  have hMupper : M ≤ (2 + modulusUpperError k) * B := maximumModulus_upper hk hr
  have hμlower : B ≤ μ := maximumTerm_lower hk hr
  have hdenLower : 0 < 2 - modulusLowerError k := by linarith
  have hdenUpper : 0 < 2 + modulusUpperError k := by
    nlinarith [modulusUpperError_nonneg k]
  have hMpos : 0 < M :=
    lt_of_lt_of_le (mul_pos hdenLower hB) hMlower
  unfold ratioLower
  change 1 / (2 + modulusUpperError k) ≤ μ / M
  apply (le_div_iff₀ hMpos).2
  calc
    (1 / (2 + modulusUpperError k)) * M ≤
        (1 / (2 + modulusUpperError k)) *
          ((2 + modulusUpperError k) * B) :=
      mul_le_mul_of_nonneg_left hMupper (by positivity)
    _ = B := by field_simp [ne_of_gt hdenUpper]
    _ ≤ μ := hμlower

lemma ratio_le_ratioUpper_cell {k : ℕ} {r : ℝ} (hk : 2 ≤ k) (hr : InCell k r)
    (hsmall : modulusLowerError k < 1) :
    maximumTerm coeff r / maximumModulus function r ≤ ratioUpper k := by
  have hrpos : 0 < r := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hr.1]
  let B : ℝ := carrier k r
  let M : ℝ := maximumModulus function r
  let μ : ℝ := maximumTerm coeff r
  have hB : 0 < B := carrier_pos hrpos
  have hMlower : (2 - modulusLowerError k) * B ≤ M := maximumModulus_lower hk hr
  have hμupper : μ ≤ (1 + tailError k) * B := maximumTerm_upper hk hr
  have hden : 0 < 2 - modulusLowerError k := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le (mul_pos hden hB) hMlower
  have hquot : 0 ≤ (1 + tailError k) / (2 - modulusLowerError k) :=
    div_nonneg (by linarith [tailError_nonneg k]) hden.le
  unfold ratioUpper
  change μ / M ≤ (1 + tailError k) / (2 - modulusLowerError k)
  apply (div_le_iff₀ hMpos).2
  calc
    μ ≤ (1 + tailError k) * B := hμupper
    _ = ((1 + tailError k) / (2 - modulusLowerError k)) *
        ((2 - modulusLowerError k) * B) := by
      field_simp [ne_of_gt hden]
    _ ≤ ((1 + tailError k) / (2 - modulusLowerError k)) * M :=
      mul_le_mul_of_nonneg_left hMlower hquot

/-- The cell containing a sufficiently large real radius. -/
def cellIndex (r : ℝ) : ℕ := ⌊r⌋₊ - 1

lemma cellIndex_spec {r : ℝ} (hr : 3 ≤ r) :
    2 ≤ cellIndex r ∧ InCell (cellIndex r) r := by
  have hr0 : 0 ≤ r := by linarith
  have hfloor3 : 3 ≤ ⌊r⌋₊ := Nat.le_floor hr
  have hfloorle : ((⌊r⌋₊ : ℕ) : ℝ) ≤ r := Nat.floor_le hr0
  have hupper : r ≤ (((⌊r⌋₊ : ℕ) : ℝ) + 1) := (Nat.lt_floor_add_one r).le
  have hidx1 : cellIndex r + 1 = ⌊r⌋₊ := by
    unfold cellIndex
    omega
  have hidx2 : cellIndex r + 2 = ⌊r⌋₊ + 1 := by
    unfold cellIndex
    omega
  constructor
  · unfold cellIndex
    omega
  · constructor
    · have h : ((cellIndex r + 1 : ℕ) : ℝ) ≤ r := by
        rw [hidx1]
        exact hfloorle
      simpa [Nat.cast_add] using h
    · have h : r ≤ ((cellIndex r + 2 : ℕ) : ℝ) := by
        rw [hidx2, Nat.cast_add, Nat.cast_one]
        exact hupper
      simpa [Nat.cast_add] using h

lemma cellIndex_tendsto_atTop : Tendsto cellIndex atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  refine ⟨(((K + 1 : ℕ) : ℝ)), ?_⟩
  intro r hr
  have hfloor : K + 1 ≤ ⌊r⌋₊ := Nat.le_floor hr
  unfold cellIndex
  omega

lemma counterexample_limit :
    Tendsto (fun r : ℝ ↦ maximumTerm coeff r / maximumModulus function r)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlower := ratioLower_tendsto_half.comp cellIndex_tendsto_atTop
  have hupper := ratioUpper_tendsto_half.comp cellIndex_tendsto_atTop
  have hsmall : ∀ᶠ r : ℝ in atTop, modulusLowerError (cellIndex r) < 1 :=
    (modulusLowerError_tendsto_zero.comp cellIndex_tendsto_atTop)
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop (3 : ℝ), hsmall] with r hr hs
    exact ratioLower_le_cell (cellIndex_spec hr).1 (cellIndex_spec hr).2 hs
  · filter_upwards [eventually_ge_atTop (3 : ℝ), hsmall] with r hr hs
    exact ratio_le_ratioUpper_cell (cellIndex_spec hr).1 (cellIndex_spec hr).2 hs

/-- The explicit Clunie--Hayman type counterexample at the endpoint `1/2`. -/
theorem counterexample :
    IsEntirePowerSeries coeff function ∧
      IsTranscendentalSeries coeff ∧
      Tendsto (fun r : ℝ ↦ maximumTerm coeff r / maximumModulus function r)
        atTop (𝓝 (1 / 2 : ℝ)) :=
  ⟨isEntirePowerSeries, coeff_isTranscendental, counterexample_limit⟩

end

end Construction

/-- Erdős Problem 227 has a negative answer: an ordinary nonzero limit exists. -/
theorem not_erdos_227 :
    ¬ (∀ (a : ℕ → ℂ) (f : ℂ → ℂ) (L : ℝ),
      IsEntirePowerSeries a f →
      IsTranscendentalSeries a →
      Tendsto (fun r : ℝ ↦ maximumTerm a r / maximumModulus f r) atTop (𝓝 L) →
      L = 0) := by
  intro hclaim
  have hzero := hclaim Construction.coeff Construction.function (1 / 2 : ℝ)
    Construction.counterexample.1 Construction.counterexample.2.1
    Construction.counterexample.2.2
  norm_num at hzero

#print axioms not_erdos_227

end Erdos227

alias _root_.Erdos227.erdos_227 := _root_.Erdos227.not_erdos_227
