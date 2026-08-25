import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

/-!
# Positive real power sums

For zero repulsion one needs a lower bound for the real part of a power
sum, not merely its norm.  The finite Fejér-kernel argument below applies
to points of the closed unit disk, with one point on the boundary.
-/

namespace Linnik

open Complex
open scoped BigOperators ComplexConjugate

/-- The triangularly weighted real power sum, including the constant term. -/
def triangularPowerSum (z : ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ((N : ℝ) - k) * (z ^ k).re

theorem triangularPowerSum_succ (z : ℂ) (N : ℕ) :
    triangularPowerSum z (N + 1) =
      triangularPowerSum z N + (∑ k ∈ Finset.range (N + 1), z ^ k).re := by
  unfold triangularPowerSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul,
    Complex.add_re, Complex.re_sum]
  have hterm (k : ℕ) :
      ((N : ℝ) + 1 - k) * (z ^ k).re =
        ((N : ℝ) - k) * (z ^ k).re + (z ^ k).re := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  ring

/-- Positivity of the finite Fejér kernel throughout the closed disk. -/
theorem normSq_geometricSum_le_triangularPowerSum
    {z : ℂ} (hz : ‖z‖ ≤ 1) (N : ℕ) :
    normSq (∑ k ∈ Finset.range N, z ^ k) ≤
      2 * triangularPowerSum z N - N := by
  have hzsq : normSq z ≤ 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  induction N with
  | zero => simp [triangularPowerSum]
  | succ N ih =>
    let S : ℂ := ∑ k ∈ Finset.range N, z ^ k
    have hS : (∑ k ∈ Finset.range (N + 1), z ^ k) = 1 + z * S := by
      simp only [S, Finset.sum_range_succ', pow_succ', Finset.mul_sum, pow_zero]
      ring
    have hnorm : normSq (1 + z * S) =
        normSq z * normSq S + 2 * (1 + z * S).re - 1 := by
      rw [Complex.normSq_add, Complex.normSq_mul]
      simp only [Complex.normSq_one, Complex.add_re, one_re, one_mul, conj_re]
      ring
    have hmul : normSq z * normSq S ≤ normSq S :=
      mul_le_of_le_one_left (normSq_nonneg S) hzsq
    rw [triangularPowerSum_succ, hS, hnorm, Nat.cast_add, Nat.cast_one]
    change normSq z * normSq S + 2 * (1 + z * S).re - 1 ≤ _
    change normSq S ≤ 2 * triangularPowerSum z N - N at ih
    linarith

theorem triangularPowerSum_lower {z : ℂ} (hz : ‖z‖ ≤ 1) (N : ℕ) :
    (N : ℝ) / 2 ≤ triangularPowerSum z N := by
  have h := normSq_geometricSum_le_triangularPowerSum hz N
  have hnonneg := normSq_nonneg (∑ k ∈ Finset.range N, z ^ k)
  linarith

/-- The nonconstant part of the triangularly weighted power sum. -/
def positiveTriangularPowerSum (z : ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ((N : ℝ) - k) * (z ^ (k + 1)).re

theorem positiveTriangularPowerSum_eq (z : ℂ) (N : ℕ) :
    positiveTriangularPowerSum z N = triangularPowerSum z (N + 1) - (N + 1) := by
  unfold positiveTriangularPowerSum triangularPowerSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_re, Nat.cast_zero, sub_zero, mul_one,
    Nat.cast_add, Nat.cast_one]
  have hterm (k : ℕ) : (N : ℝ) + 1 - (k + 1) = N - k := by ring
  simp_rw [hterm]
  ring

theorem positiveTriangularPowerSum_lower {z : ℂ} (hz : ‖z‖ ≤ 1) (N : ℕ) :
    -((N : ℝ) + 1) / 2 ≤ positiveTriangularPowerSum z N := by
  rw [positiveTriangularPowerSum_eq]
  have h := triangularPowerSum_lower hz (N + 1)
  push_cast at h
  linarith

theorem sum_triangular_weights (N : ℕ) :
    (∑ k ∈ Finset.range N, ((N : ℝ) - k)) = (N : ℝ) * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
    have hterm (k : ℕ) : (N : ℝ) + 1 - k = ((N : ℝ) - k) + 1 := by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ih]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring

/-- A nonnegative phase weight used to make one distinguished root contribute
quadratically while preserving a lower bound for all the other roots. -/
def phaseWeightedPowerSum (u z : ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    ((N : ℝ) - k) * (1 + (u ^ (k + 1)).re) * (z ^ (k + 1)).re

theorem phaseWeightedPowerSum_eq (u z : ℂ) (N : ℕ) :
    phaseWeightedPowerSum u z N = positiveTriangularPowerSum z N +
      (positiveTriangularPowerSum (u * z) N +
        positiveTriangularPowerSum (conj u * z) N) / 2 := by
  unfold phaseWeightedPowerSum positiveTriangularPowerSum
  rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_pow, ← map_pow, Complex.mul_re, conj_re, conj_im]
  ring

theorem phaseWeightedPowerSum_lower {u z : ℂ}
    (hu : ‖u‖ ≤ 1) (hz : ‖z‖ ≤ 1) (N : ℕ) :
    -((N : ℝ) + 1) ≤ phaseWeightedPowerSum u z N := by
  have huz : ‖u * z‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hu (norm_nonneg z) hz
  have hucz : ‖conj u * z‖ ≤ 1 := by
    simpa only [norm_mul, norm_conj] using huz
  rw [phaseWeightedPowerSum_eq]
  have h₁ := positiveTriangularPowerSum_lower hz N
  have h₂ := positiveTriangularPowerSum_lower huz N
  have h₃ := positiveTriangularPowerSum_lower hucz N
  linarith

theorem phaseWeightedPowerSum_self_eq {u : ℂ} (hu : ‖u‖ = 1) (N : ℕ) :
    phaseWeightedPowerSum u u N = positiveTriangularPowerSum u N +
      ((N : ℝ) * (N + 1) / 2 + positiveTriangularPowerSum (u ^ 2) N) / 2 := by
  have hconj : conj u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, hu]
    norm_num
  rw [phaseWeightedPowerSum_eq, hconj, ← pow_two]
  have hone : positiveTriangularPowerSum 1 N = (N : ℝ) * (N + 1) / 2 := by
    simpa only [positiveTriangularPowerSum, one_pow, one_re, mul_one] using
      sum_triangular_weights N
  rw [hone]
  ring

theorem phaseWeightedPowerSum_self_lower {u : ℂ} (hu : ‖u‖ = 1) (N : ℕ) :
    ((N : ℝ) + 1) * (N - 3) / 4 ≤ phaseWeightedPowerSum u u N := by
  rw [phaseWeightedPowerSum_self_eq hu]
  have h₁ := positiveTriangularPowerSum_lower hu.le N
  have h₂ := positiveTriangularPowerSum_lower
    (show ‖u ^ 2‖ ≤ 1 by simp [norm_pow, hu]) N
  nlinarith

theorem sum_phaseWeightedPowerSum_lower
    {K : ℕ} (z : Fin K → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (j₀ : Fin K) (hj₀ : ‖z j₀‖ = 1) (N : ℕ) :
    ((N : ℝ) + 1) ^ 2 / 4 - (K : ℝ) * (N + 1) ≤
      ∑ j, phaseWeightedPowerSum (z j₀) (z j) N := by
  have hnonneg (j : Fin K) :
      0 ≤ phaseWeightedPowerSum (z j₀) (z j) N + ((N : ℝ) + 1) := by
    have h := phaseWeightedPowerSum_lower hj₀.le (hz j) N
    linarith
  have hsingle := Finset.single_le_sum (fun j _ ↦ hnonneg j)
    (Finset.mem_univ j₀)
  have hself := phaseWeightedPowerSum_self_lower hj₀ N
  rw [Finset.sum_add_distrib] at hsingle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsingle
  nlinarith

theorem sum_phaseWeightedPowerSum_eq
    {K : ℕ} (u : ℂ) (z : Fin K → ℂ) (N : ℕ) :
    (∑ j, phaseWeightedPowerSum u (z j) N) =
      ∑ k ∈ Finset.range N, ((N : ℝ) - k) * (1 + (u ^ (k + 1)).re) *
        (∑ j, z j ^ (k + 1)).re := by
  unfold phaseWeightedPowerSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.re_sum, Finset.mul_sum]

theorem phase_weight_nonneg {u : ℂ} (hu : ‖u‖ ≤ 1) (k : ℕ) :
    0 ≤ 1 + (u ^ k).re := by
  have hnorm : ‖u ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg u) hu
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (u ^ k)).trans hnorm)).1
  linarith

theorem phase_weight_le_two {u : ℂ} (hu : ‖u‖ ≤ 1) (k : ℕ) :
    1 + (u ^ k).re ≤ 2 := by
  have hnorm : ‖u ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg u) hu
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (u ^ k)).trans hnorm)).2
  linarith

/-- A positive real power sum is found among the first `8K` powers.  The
constant is absolute and no separation of the roots is required. -/
theorem exists_re_powerSum_gt_one_eighth
    {K : ℕ} (z : Fin K → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (j₀ : Fin K) (hj₀ : ‖z j₀‖ = 1) :
    ∃ k ∈ Finset.Icc 1 (8 * K), (1 : ℝ) / 8 < (∑ j, z j ^ k).re := by
  by_contra h
  push Not at h
  let N := 8 * K
  have hlower := sum_phaseWeightedPowerSum_lower z hz j₀ hj₀ N
  have hupper : (∑ j, phaseWeightedPowerSum (z j₀) (z j) N) ≤
      (N : ℝ) * (N + 1) / 8 := by
    rw [sum_phaseWeightedPowerSum_eq]
    calc
      (∑ k ∈ Finset.range N, ((N : ℝ) - k) *
          (1 + (z j₀ ^ (k + 1)).re) * (∑ j, z j ^ (k + 1)).re) ≤
          ∑ k ∈ Finset.range N, ((N : ℝ) - k) / 4 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k < N := Finset.mem_range.mp hk
        have hw : 0 ≤ (N : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hkN.le)
        have hphase₀ := phase_weight_nonneg (hz j₀) (k + 1)
        have hphase₂ := phase_weight_le_two (hz j₀) (k + 1)
        have hsmall := h (k + 1) (Finset.mem_Icc.mpr
          ⟨by omega, by dsimp [N] at hkN; omega⟩)
        calc
          ((N : ℝ) - k) * (1 + (z j₀ ^ (k + 1)).re) *
              (∑ j, z j ^ (k + 1)).re ≤
              ((N : ℝ) - k) * (1 + (z j₀ ^ (k + 1)).re) * (1 / 8) :=
            mul_le_mul_of_nonneg_left hsmall (mul_nonneg hw hphase₀)
          _ ≤ ((N : ℝ) - k) / 4 := by nlinarith
      _ = (N : ℝ) * (N + 1) / 8 := by
        rw [← Finset.sum_div, sum_triangular_weights]
        ring
  have hN : (N : ℝ) = 8 * K := by simp [N]
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

theorem sum_half_pow_succ (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1)) = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- The same positive-power argument tolerates an exponentially decreasing
error in each power.  This is useful for the analytic regular factor in a
fixed-disk logarithmic derivative. -/
theorem exists_re_powerSum_gt_geometric_error
    {K N : ℕ} (z : Fin K → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (j₀ : Fin K) (hj₀ : ‖z j₀‖ = 1)
    {B : ℝ} (hB : 0 ≤ B) (hN : 32 * ((K : ℝ) + B + 1) ≤ N) :
    ∃ k ∈ Finset.Icc 1 N,
      (1 : ℝ) / 8 + B * (1 / 2 : ℝ) ^ k < (∑ j, z j ^ k).re := by
  by_contra h
  push Not at h
  have hlower := sum_phaseWeightedPowerSum_lower z hz j₀ hj₀ N
  have hupper : (∑ j, phaseWeightedPowerSum (z j₀) (z j) N) ≤
      (N : ℝ) * (N + 1) / 8 + 2 * N * B := by
    rw [sum_phaseWeightedPowerSum_eq]
    calc
      (∑ k ∈ Finset.range N, ((N : ℝ) - k) *
          (1 + (z j₀ ^ (k + 1)).re) * (∑ j, z j ^ (k + 1)).re) ≤
          ∑ k ∈ Finset.range N,
            (((N : ℝ) - k) / 4 + 2 * N * B * (1 / 2 : ℝ) ^ (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k < N := Finset.mem_range.mp hk
        have hw : 0 ≤ (N : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hkN.le)
        have hwN : (N : ℝ) - k ≤ N := sub_le_self _ (Nat.cast_nonneg k)
        have hphase₀ := phase_weight_nonneg (hz j₀) (k + 1)
        have hphase₂ := phase_weight_le_two (hz j₀) (k + 1)
        have hsmall := h (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hp : 0 ≤ B * (1 / 2 : ℝ) ^ (k + 1) := by positivity
        have hweight : ((N : ℝ) - k) * (1 + (z j₀ ^ (k + 1)).re) ≤
            2 * ((N : ℝ) - k) := by nlinarith
        have hconstant : ((N : ℝ) - k) *
            (1 + (z j₀ ^ (k + 1)).re) * (1 / 8) ≤ ((N : ℝ) - k) / 4 := by
          linarith
        have herror := mul_le_mul_of_nonneg_right
          (hweight.trans (by linarith : 2 * ((N : ℝ) - k) ≤ 2 * N)) hp
        have htotal := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hw hphase₀)
        nlinarith
      _ = (N : ℝ) * (N + 1) / 8 +
          2 * N * B * (1 - (1 / 2 : ℝ) ^ N) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, sum_triangular_weights,
          ← Finset.mul_sum, sum_half_pow_succ]
        ring
      _ ≤ (N : ℝ) * (N + 1) / 8 + 2 * N * B := by
        have hprod : 0 ≤ 2 * (N : ℝ) * B * (1 / 2 : ℝ) ^ N := by positivity
        nlinarith
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hN₀ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlarge : ((K : ℝ) + 2 * B) * ((N : ℝ) + 1) ≤
      (N : ℝ) * (N + 1) / 16 := by
    have hsmall : (K : ℝ) + 2 * B ≤ (N : ℝ) / 16 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ (N : ℝ) + 1)
    nlinarith
  nlinarith

/-- Convert upper bounds for real power sums into a quantitative bound for
the largest root.  The `9⁻ᵏ` remainder is the regular-factor error on a
radius-three disk after taking derivatives of odd order. -/
theorem largestRoot_pow_lt_of_powerSum_bound
    {K N : ℕ} (w : Fin K → ℂ) (j₀ : Fin K)
    {r B D epsilon : ℝ}
    (hr : (1 : ℝ) / 4 ≤ r) (hr₁ : r ≤ 1)
    (hw : ∀ j, ‖w j‖ ≤ r) (hj₀ : ‖w j₀‖ = r)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hepsilon : 0 ≤ epsilon)
    (hN : 32 * ((K : ℝ) + B + 1) ≤ N)
    (hpower : ∀ k ∈ Finset.Icc 1 N,
      (∑ j, w j ^ k).re ≤ D * k * epsilon + B * (1 / 9 : ℝ) ^ k) :
    r ^ N < 8 * D * N * epsilon := by
  have hr₀ : 0 < r := by linarith
  let z : Fin K → ℂ := fun j ↦ w j / (r : ℂ)
  have hz (j : Fin K) : ‖z j‖ ≤ 1 := by
    dsimp [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀]
    exact (div_le_one hr₀).mpr (hw j)
  have hzj₀ : ‖z j₀‖ = 1 := by
    dsimp [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀,
      hj₀, div_self hr₀.ne']
  obtain ⟨k, hk, hlarge⟩ :=
    exists_re_powerSum_gt_geometric_error z hz j₀ hzj₀ hB hN
  have hsum : (∑ j, z j ^ k).re = (∑ j, w j ^ k).re / r ^ k := by
    simp only [z, div_pow, ← Finset.sum_div, ← Complex.ofReal_pow,
      Complex.div_ofReal_re]
  have hrk : 0 < r ^ k := pow_pos hr₀ k
  have herror : B * (1 / 9 : ℝ) ^ k / r ^ k ≤ B * (1 / 2 : ℝ) ^ k := by
    rw [mul_div_assoc, ← div_pow]
    apply mul_le_mul_of_nonneg_left _ hB
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hr₀).mpr
    linarith
  have hupper := div_le_div_of_nonneg_right (hpower k hk) hrk.le
  rw [hsum] at hlarge
  rw [add_div] at hupper
  have hmain : (1 : ℝ) / 8 < D * k * epsilon / r ^ k := by linarith
  have hmain' : r ^ k < 8 * D * k * epsilon := by
    have hmul := (lt_div_iff₀ hrk).mp hmain
    nlinarith
  have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
  have hpow : r ^ N ≤ r ^ k := pow_le_pow_of_le_one hr₀.le hr₁ hkN
  have hcoeff : 8 * D * (k : ℝ) * epsilon ≤ 8 * D * N * epsilon := by
    gcongr
  exact hpow.trans_lt (hmain'.trans_le hcoeff)

/-- Natural multiplicities can be retained without a separation assumption
or a loss depending on the number of distinct roots. -/
theorem largestRoot_pow_lt_of_weighted_powerSum_bound
    (Z : ℂ →₀ ℕ) {N : ℕ} {z₀ : ℂ} (hz₀ : z₀ ∈ Z.support)
    {r B D epsilon : ℝ}
    (hr : (1 : ℝ) / 4 ≤ r) (hr₁ : r ≤ 1)
    (hw : ∀ z ∈ Z.support, ‖z‖ ≤ r) (hmax : ‖z₀‖ = r)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hepsilon : 0 ≤ epsilon)
    (hN : 32 * (Z.sum (fun _ m ↦ (m : ℝ)) + B + 1) ≤ N)
    (hpower : ∀ k ∈ Finset.Icc 1 N,
      (Z.sum (fun z m ↦ (m : ℂ) * z ^ k)).re ≤
        D * k * epsilon + B * (1 / 9 : ℝ) ^ k) :
    r ^ N < 8 * D * N * epsilon := by
  classical
  let I := (z : Z.support) × Fin (Z z)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let w : Fin (Fintype.card I) → ℂ := fun j ↦ (e.symm j).1.1
  have hz₀pos : 0 < Z z₀ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hz₀)
  let i₀ : I := ⟨⟨z₀, hz₀⟩, ⟨0, hz₀pos⟩⟩
  have hcard : (Fintype.card I : ℝ) = Z.sum (fun _ m ↦ (m : ℝ)) := by
    simp only [I, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum, Finsupp.sum]
    exact (Finset.sum_subtype Z.support (fun _ ↦ Iff.rfl) (fun z ↦ (Z z : ℝ))).symm
  have hsum (k : ℕ) : (∑ j, w j ^ k) = Z.sum (fun z m ↦ (m : ℂ) * z ^ k) := by
    calc
      (∑ j, w j ^ k) = ∑ i : I, (i.1.1 : ℂ) ^ k := by
        exact e.symm.sum_comp (fun i : I ↦ (i.1.1 : ℂ) ^ k)
      _ = ∑ z : Z.support, (Z z : ℂ) * (z : ℂ) ^ k := by
        rw [Fintype.sum_sigma]
        simp
      _ = Z.sum (fun z m ↦ (m : ℂ) * z ^ k) :=
        (Finset.sum_subtype Z.support (fun _ ↦ Iff.rfl) (fun z ↦ (Z z : ℂ) * z ^ k)).symm
  apply largestRoot_pow_lt_of_powerSum_bound w (e i₀) hr hr₁
      (fun j ↦ hw _ (e.symm j).1.2) ?_ hB hD hepsilon ?_ ?_
  · simpa only [w, Equiv.symm_apply_apply, i₀] using hmax
  · simpa only [hcard] using hN
  · intro k hk
    rw [hsum]
    exact hpower k hk

end Linnik
