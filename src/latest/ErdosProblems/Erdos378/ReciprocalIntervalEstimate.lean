/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.VaughanReciprocalEstimate

/-!
# A uniform Type-I reciprocal interval estimate

The second-derivative estimate is specialized to intervals `(x/t,y/t]`
with `x` and `y` comparable and frequency `X` comparable to `y^2`.  The
result deliberately uses a coarse ambient majorant independent of `t`.
-/

open scoped BigOperators

namespace Erdos378
namespace ReciprocalIntervalEstimate

open PrimeReciprocal
open ReciprocalExponential

noncomputable section

noncomputable def reciprocalIntervalMajorant (y L : ℕ) : ℝ :=
  2 * (y : ℝ) ^ 2 / (L : ℝ) +
    4 * (y : ℝ) *
      ((L : ℝ) + 24 * (y : ℝ) * (1 + Real.log (y : ℝ))) / (L : ℝ)

lemma reciprocalIntervalMajorant_nonneg {y L : ℕ}
    (hy : 1 ≤ y) (hL : 0 < L) :
    0 ≤ reciprocalIntervalMajorant y L := by
  unfold reciprocalIntervalMajorant
  have hlog : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy)
  positivity

private lemma product_floor_endpoint_le
    {y t : ℕ} (ht : 0 < t) (hty : t ≤ y) :
    t * (y / t + 1) ≤ 2 * y := by
  have hdiv := Nat.div_mul_le_self y t
  have htadd : t * (y / t + 1) = (y / t) * t + t := by ring
  rw [htadd]
  omega

private lemma reciprocal_interval_endpoint_factor_le
    {X : ℝ} {x y t b : ℕ}
    (hX : 0 < X) (ht : 0 < t) (hty : t ≤ y)
    (hxb : x / t ≤ b) (hby : b ≤ y / t)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X) :
    3 * (((x / t + 1 + (b - x / t) : ℕ) : ℝ) ^ 3) /
        (4 * (X / (t : ℝ))) ≤ 24 * (y : ℝ) := by
  have hendNat :
      t * (x / t + 1 + (b - x / t)) ≤ 2 * y := by
    have heq : x / t + 1 + (b - x / t) = b + 1 := by omega
    rw [heq]
    exact (Nat.mul_le_mul_left t (Nat.add_le_add_right hby 1)).trans
      (product_floor_endpoint_le ht hty)
  have hend :
      (t : ℝ) * ((x / t + 1 + (b - x / t) : ℕ) : ℝ) ≤
        2 * (y : ℝ) := by exact_mod_cast hendNat
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hXdiv : 0 < X / (t : ℝ) := div_pos hX htR
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hend' :
      ((x / t + 1 + (b - x / t) : ℕ) : ℝ) ≤
        2 * (y : ℝ) / (t : ℝ) := (le_div_iff₀ htR).2 (by
    simpa [mul_comm] using hend)
  have hnum :
      3 * (((x / t + 1 + (b - x / t) : ℕ) : ℝ) ^ 3) ≤
        3 * (2 * (y : ℝ) / (t : ℝ)) ^ 3 := by
    gcongr
  apply (div_le_iff₀ (by positivity : 0 < 4 * (X / (t : ℝ)))).2
  have htOne : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htarget :
      3 * (2 * (y : ℝ) / (t : ℝ)) ^ 3 ≤
        (24 * (y : ℝ)) * (4 * (X / (t : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_left hXlo
      (by positivity : (0 : ℝ) ≤ 24 * (y : ℝ))
    have htSq : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
    have hX0 : 0 ≤ X := hX.le
    field_simp
    have hstep : 96 * (y : ℝ) * X ≤
        96 * (y : ℝ) * X * (t : ℝ) ^ 2 := by
      exact le_mul_of_one_le_right (by positivity) htSq
    nlinarith
  exact hnum.trans htarget

private lemma reciprocal_interval_small_phase
    {X : ℝ} {x y t L : ℕ}
    (hX : 0 < X) (ht : 0 < t) (hL : 0 < L)
    (hXhi : X ≤ (y : ℝ) ^ 2)
    (hyx : y ≤ 2 * x) (hsize : 16 * L * t ^ 2 ≤ x) :
    2 * (X / (t : ℝ)) * L / (((x / t + 1 : ℕ) : ℝ) ^ 3) ≤ 1 / 2 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hxpos : 0 < x := by
    have : 0 < 16 * L * t ^ 2 := by
      positivity
    exact this.trans_le hsize
  have hquot : x < t * (x / t + 1) := Nat.lt_mul_div_succ x ht
  have hquotR : (x : ℝ) < (t : ℝ) * ((x / t + 1 : ℕ) : ℝ) := by
    exact_mod_cast hquot
  have hden : (x : ℝ) / (t : ℝ) < ((x / t + 1 : ℕ) : ℝ) :=
    (div_lt_iff₀ htR).2 (by simpa [mul_comm] using hquotR)
  have hden0 : (0 : ℝ) < ((x / t + 1 : ℕ) : ℝ) := by positivity
  have hcube : ((x : ℝ) / (t : ℝ)) ^ 3 <
      ((x / t + 1 : ℕ) : ℝ) ^ 3 := by
    exact pow_lt_pow_left₀ hden (by positivity) (by norm_num)
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hsizeR : 16 * (L : ℝ) * (t : ℝ) ^ 2 ≤ x := by exact_mod_cast hsize
  have hyxR : (y : ℝ) ≤ 2 * x := by exact_mod_cast hyx
  have hnum : 4 * (X / (t : ℝ)) * (L : ℝ) ≤
      ((x : ℝ) / (t : ℝ)) ^ 3 := by
    have hyxSq : (y : ℝ) ^ 2 ≤ 4 * (x : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((2 : ℝ) * x - y)]
    have hXx : X ≤ 4 * (x : ℝ) ^ 2 := hXhi.trans hyxSq
    have hscaled := mul_le_mul_of_nonneg_right hXx
      (by positivity : (0 : ℝ) ≤ 4 * (L : ℝ) * (t : ℝ) ^ 2)
    have hsizeScaled := mul_le_mul_of_nonneg_left hsizeR
      (by positivity : (0 : ℝ) ≤ (x : ℝ) ^ 2)
    field_simp
    nlinarith
  apply (div_le_iff₀ (pow_pos hden0 3)).2
  calc
    2 * (X / (t : ℝ)) * (L : ℝ) ≤
        (1 / 2 : ℝ) * (((x : ℝ) / (t : ℝ)) ^ 3) := by nlinarith
    _ ≤ (1 / 2 : ℝ) * (((x / t + 1 : ℕ) : ℝ) ^ 3) := by gcongr

/-- A uniform square-norm bound for every terminal point
`b ≤ y/t` of the reciprocal interval beginning at `x/t`. -/
theorem norm_reciprocalProductInterval_partial_sq_le_majorant
    {X : ℝ} {x y t L b : ℕ}
    (hX : 0 < X) (ht : 0 < t) (hty : t ≤ y)
    (hby : b ≤ y / t)
    (hN : 3 ≤ b - x / t) (hL : 2 ≤ L)
    (hLN : L ≤ b - x / t - 1)
    (hsize : 16 * L * t ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalProductIntervalSum X t (x / t) b‖ ^ 2 ≤
      reciprocalIntervalMajorant y L := by
  let N := b - x / t
  have hbase := reciprocalProductInterval_second_derivative_bound X hX ht
    hN hL hLN (reciprocal_interval_small_phase hX ht (by omega) hXhi hyx hsize)
  have hNle : N ≤ y := by
    dsimp only [N]
    exact (Nat.sub_le _ _).trans (hby.trans (Nat.div_le_self y t))
  have hNleR : (N : ℝ) ≤ y := by exact_mod_cast hNle
  have hy1 : 1 ≤ y := by omega
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy1)
  have hLleY : L ≤ y := hLN.trans (Nat.sub_le _ _) |>.trans hNle
  have hharm : (harmonic (L - 1) : ℝ) ≤ 1 + Real.log (y : ℝ) := by
    calc
      (harmonic (L - 1) : ℝ) ≤ 1 + Real.log (L - 1 : ℕ) := by
        exact_mod_cast harmonic_le_one_add_log (L - 1)
      _ ≤ 1 + Real.log (y : ℝ) := by
        have hLm1posNat : 0 < L - 1 := by omega
        have hLm1leNat : L - 1 ≤ y := by omega
        have hLm1pos : (0 : ℝ) < ((L - 1 : ℕ) : ℝ) := by exact_mod_cast hLm1posNat
        have hLm1le : ((L - 1 : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hLm1leNat
        have hlogle := Real.log_le_log
          hLm1pos hLm1le
        linarith
  have hxb : x / t ≤ b := by omega
  have hfactor := reciprocal_interval_endpoint_factor_le hX ht hty hxb hby hXlo
  have hharm0 : 0 ≤ (harmonic (L - 1) : ℝ) := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    exact Finset.sum_nonneg fun i hi ↦ by positivity
  have hfactor0 : 0 ≤
      3 * (((x / t + 1 + (b - x / t) : ℕ) : ℝ) ^ 3) /
        (4 * (X / (t : ℝ))) := by positivity
  have hinside :
      (L : ℝ) +
          (3 * ((((x / t + 1) + (b - x / t) : ℕ) : ℝ) ^ 3) /
            (4 * (X / (t : ℝ)))) * (harmonic (L - 1) : ℝ) ≤
        (L : ℝ) + 24 * (y : ℝ) * (1 + Real.log (y : ℝ)) := by
    have hmul := mul_le_mul hfactor hharm hharm0 (by positivity)
    linarith
  have hscaled :
      (L : ℝ) ^ 2 *
          ‖reciprocalProductIntervalSum X t (x / t) b‖ ^ 2 ≤
        (L : ℝ) ^ 2 * reciprocalIntervalMajorant y L := by
    apply hbase.trans
    have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    calc
      2 * (L : ℝ) * (N : ℝ) ^ 2 +
          4 * (N : ℝ) * (L : ℝ) *
            ((L : ℝ) +
              (3 * ((((x / t + 1) + N : ℕ) : ℝ) ^ 3) /
                (4 * (X / (t : ℝ)))) * (harmonic (L - 1) : ℝ)) ≤
        2 * (L : ℝ) * (y : ℝ) ^ 2 +
          4 * (y : ℝ) * (L : ℝ) *
            ((L : ℝ) + 24 * (y : ℝ) * (1 + Real.log (y : ℝ))) := by
        have horigInside0 : 0 ≤ (L : ℝ) +
            (3 * ((((x / t + 1) + N : ℕ) : ℝ) ^ 3) /
              (4 * (X / (t : ℝ)))) * (harmonic (L - 1) : ℝ) := by
          exact add_nonneg (by positivity) (mul_nonneg (by positivity) hharm0)
        gcongr
      _ = (L : ℝ) ^ 2 * reciprocalIntervalMajorant y L := by
        unfold reciprocalIntervalMajorant
        field_simp
  have hLsq : (0 : ℝ) < (L : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast
    (show 0 < L by omega))
  nlinarith

/-- Specialization to the complete interval `(x/t,y/t]`. -/
theorem norm_reciprocalProductInterval_sq_le_majorant
    {X : ℝ} {x y t L : ℕ}
    (hX : 0 < X) (ht : 0 < t) (hty : t ≤ y)
    (hN : 3 ≤ y / t - x / t) (hL : 2 ≤ L)
    (hLN : L ≤ y / t - x / t - 1)
    (hsize : 16 * L * t ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalProductIntervalSum X t (x / t) (y / t)‖ ^ 2 ≤
      reciprocalIntervalMajorant y L :=
  norm_reciprocalProductInterval_partial_sq_le_majorant
    hX ht hty le_rfl hN hL hLN hsize hXlo hXhi hyx

/-- Uniform norm bound for all partial endpoints.  Prefixes shorter than the
van der Corput shift are estimated trivially. -/
theorem norm_reciprocalProductInterval_partial_le
    {X : ℝ} {x y t L b : ℕ}
    (hX : 0 < X) (ht : 0 < t) (hty : t ≤ y)
    (hby : b ≤ y / t) (hL : 2 ≤ L)
    (hsize : 16 * L * t ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalProductIntervalSum X t (x / t) b‖ ≤
      (L : ℝ) + Real.sqrt (reciprocalIntervalMajorant y L) := by
  by_cases hlong : L + 1 ≤ b - x / t
  · have hN : 3 ≤ b - x / t := by omega
    have hLN : L ≤ b - x / t - 1 := by omega
    have hsq := norm_reciprocalProductInterval_partial_sq_le_majorant
      hX ht hty hby hN hL hLN hsize hXlo hXhi hyx
    have hy1 : 1 ≤ y := by omega
    have hA : 0 ≤ reciprocalIntervalMajorant y L :=
      reciprocalIntervalMajorant_nonneg hy1 (by omega)
    exact (Real.le_sqrt (norm_nonneg _) hA).2 hsq |>.trans
      (le_add_of_nonneg_left (by positivity))
  · have hshort : b - x / t ≤ L := by omega
    have htrivial :
        ‖reciprocalProductIntervalSum X t (x / t) b‖ ≤ (b - x / t : ℕ) := by
      unfold reciprocalProductIntervalSum
      calc
        ‖∑ r ∈ Finset.Ioc (x / t) b, reciprocalWeight X (t * r)‖ ≤
            ∑ r ∈ Finset.Ioc (x / t) b,
              ‖reciprocalWeight X (t * r)‖ := norm_sum_le _ _
        _ = (b - x / t : ℕ) := by
          simp only [norm_reciprocalWeight, Finset.sum_const, Nat.card_Ioc,
            nsmul_eq_mul, mul_one, Nat.cast_id]
    calc
      ‖reciprocalProductIntervalSum X t (x / t) b‖ ≤
          ((b - x / t : ℕ) : ℝ) := htrivial
      _ ≤ (L : ℝ) := by exact_mod_cast hshort
      _ ≤ (L : ℝ) + Real.sqrt (reciprocalIntervalMajorant y L) :=
        le_add_of_nonneg_right (Real.sqrt_nonneg _)

private lemma log_sum_by_parts_aux (z : ℕ → ℂ) (a n : ℕ) :
    (∑ i ∈ Finset.Ioc a (a + n + 1),
      ((Real.log (i : ℝ) : ℝ) : ℂ) * z i) =
      ((Real.log ((a + n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          (∑ i ∈ Finset.Ioc a (a + n + 1), z i) -
        ∑ j ∈ Finset.Ioc a (a + n),
          ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
            ∑ i ∈ Finset.Ioc a j, z i := by
  induction n with
  | zero =>
      have hsum :
          (∑ i ∈ Finset.Ioc a (a + 1),
            ((Real.log (i : ℝ) : ℝ) : ℂ) * z i) =
              ((Real.log ((a + 1 : ℕ) : ℝ) : ℝ) : ℂ) * z (a + 1) := by
        rw [show a + 1 = a + 1 by rfl,
          Finset.sum_Ioc_succ_top (le_refl a)]
        simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
      have hpref : (∑ i ∈ Finset.Ioc a (a + 1), z i) = z (a + 1) := by
        rw [Finset.sum_Ioc_succ_top (le_refl a)]
        simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
      rw [hsum, hpref]
      simp only [Nat.add_zero, Finset.Ioc_self, Finset.sum_empty, sub_zero]
  | succ n ih =>
      have hab : a ≤ a + n + 1 := by omega
      have hcorr : a ≤ a + n := by omega
      have hpref :
          (∑ i ∈ Finset.Ioc a ((a + n + 1) + 1), z i) =
            (∑ i ∈ Finset.Ioc a (a + n + 1), z i) + z ((a + n + 1) + 1) :=
        Finset.sum_Ioc_succ_top hab z
      have hcorrSum :
          (∑ j ∈ Finset.Ioc a (a + n + 1),
              ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
                ∑ i ∈ Finset.Ioc a j, z i) =
            (∑ j ∈ Finset.Ioc a (a + n),
              ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
                ∑ i ∈ Finset.Ioc a j, z i) +
              ((Real.log (((a + n + 1) + 1 : ℕ) : ℝ) -
                Real.log ((a + n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
                ∑ i ∈ Finset.Ioc a (a + n + 1), z i :=
        Finset.sum_Ioc_succ_top hcorr _
      rw [show a + (n + 1) + 1 = (a + n + 1) + 1 by omega]
      calc
        (∑ i ∈ Finset.Ioc a ((a + n + 1) + 1),
            ((Real.log (i : ℝ) : ℝ) : ℂ) * z i) =
          (∑ i ∈ Finset.Ioc a (a + n + 1),
            ((Real.log (i : ℝ) : ℝ) : ℂ) * z i) +
              ((Real.log (((a + n + 1) + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
                z ((a + n + 1) + 1) :=
          Finset.sum_Ioc_succ_top hab _
        _ = (((Real.log ((a + n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
              (∑ i ∈ Finset.Ioc a (a + n + 1), z i) -
            ∑ j ∈ Finset.Ioc a (a + n),
              ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
                ∑ i ∈ Finset.Ioc a j, z i) +
              ((Real.log (((a + n + 1) + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
                z ((a + n + 1) + 1) := by rw [ih]
        _ = _ := by
          simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hpref hcorrSum ⊢
          rw [hpref, hcorrSum]
          push_cast
          ring

private lemma sum_log_succ_sub_Ioc (a n : ℕ) :
    (∑ j ∈ Finset.Ioc a (a + n),
        (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ))) =
      Real.log ((a + n + 1 : ℕ) : ℝ) - Real.log ((a + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp only [Nat.add_zero, Finset.Ioc_self, Finset.sum_empty, sub_self]
  | succ n ih =>
      have ha : a ≤ a + n := by omega
      rw [show a + (n + 1) = (a + n) + 1 by omega,
        Finset.sum_Ioc_succ_top ha, ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Finite Abel summation for the logarithmic reciprocal product sum. -/
theorem norm_log_weighted_reciprocalProductInterval_le
    {X : ℝ} {x y t L : ℕ}
    (hX : 0 < X) (ht : 0 < t) (hty : t ≤ y)
    (hL : 2 ≤ L) (hsize : 16 * L * t ^ 2 ≤ x)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖∑ h ∈ Finset.Ioc (x / t) (y / t),
        (Real.log h : ℂ) * reciprocalWeight X (t * h)‖ ≤
      2 * Real.log (y : ℝ) *
        ((L : ℝ) + Real.sqrt (reciprocalIntervalMajorant y L)) := by
  let a := x / t
  let b := y / t
  let z : ℕ → ℂ := fun h ↦ reciprocalWeight X (t * h)
  by_cases hab : a < b
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n + 1 := by
      exact ⟨b - a - 1, by omega⟩
    have hparts := log_sum_by_parts_aux z a n
    change ‖∑ h ∈ Finset.Ioc a b,
        ((Real.log (h : ℝ) : ℝ) : ℂ) * z h‖ ≤ _
    rw [hn]
    change ‖∑ h ∈ Finset.Ioc a (a + n + 1),
        ((Real.log (h : ℝ) : ℝ) : ℂ) * z h‖ ≤ _
    rw [hparts]
    let B : ℝ := (L : ℝ) + Real.sqrt (reciprocalIntervalMajorant y L)
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    have hbY : a + n + 1 ≤ y := by
      rw [← hn]
      exact Nat.div_le_self y t
    have hlogb0 : 0 ≤ Real.log (a + n + 1 : ℕ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (a + n))
    have hlogbY : Real.log (a + n + 1 : ℕ) ≤ Real.log (y : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast Nat.zero_lt_succ (a + n)
      · exact_mod_cast hbY
    have hlogY0 : 0 ≤ Real.log (y : ℝ) := hlogb0.trans hlogbY
    have hfull : ‖∑ i ∈ Finset.Ioc a (a + n + 1), z i‖ ≤ B := by
      simpa only [reciprocalProductIntervalSum, a, hn, z] using
        norm_reciprocalProductInterval_partial_le hX ht hty
          (show a + n + 1 ≤ y / t by rw [← hn]) hL hsize
          hXlo hXhi hyx
    have hprefix (j : ℕ) (hj : j ∈ Finset.Ioc a (a + n)) :
        ‖∑ i ∈ Finset.Ioc a j, z i‖ ≤ B := by
      have hjle : j ≤ y / t := by
        calc
          j ≤ a + n := (Finset.mem_Ioc.mp hj).2
          _ ≤ a + n + 1 := by omega
          _ = b := hn.symm
          _ = y / t := rfl
      simpa only [reciprocalProductIntervalSum, a, z] using
        norm_reciprocalProductInterval_partial_le hX ht hty hjle hL hsize
          hXlo hXhi hyx
    have hdiff0 (j : ℕ) (hj : j ∈ Finset.Ioc a (a + n)) :
        0 ≤ Real.log ((j : ℝ) + 1) - Real.log (j : ℝ) := by
      have hjpos : 0 < j := by
        exact lt_of_le_of_lt (Nat.zero_le a) (Finset.mem_Ioc.mp hj).1
      exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hjpos) (by
        exact_mod_cast (Nat.le_add_right j 1)))
    have hcorrection :
        ‖∑ j ∈ Finset.Ioc a (a + n),
            ((Real.log ((j : ℝ) + 1) - Real.log (j : ℝ) : ℝ) : ℂ) *
              ∑ i ∈ Finset.Ioc a j, z i‖ ≤
          (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
      calc
        _ ≤ ∑ j ∈ Finset.Ioc a (a + n),
            ‖((Real.log ((j : ℝ) + 1) - Real.log (j : ℝ) : ℝ) : ℂ) *
              ∑ i ∈ Finset.Ioc a j, z i‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.Ioc a (a + n),
            (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ)) * B := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hdiff0 j hj)]
          exact mul_le_mul_of_nonneg_left (hprefix j hj) (hdiff0 j hj)
        _ = (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
          rw [← Finset.sum_mul]
          congr 1
          exact sum_log_succ_sub_Ioc a n
    have hlogSub :
        Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ) ≤
          Real.log (y : ℝ) := by
      have hloga1 : 0 ≤ Real.log (a + 1 : ℕ) := by
        apply Real.log_nonneg
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le a)
      linarith
    refine (norm_sub_le _ _).trans ?_
    calc
      _ ≤ Real.log (a + n + 1 : ℕ) * B +
          (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogb0]
          exact mul_le_mul_of_nonneg_left hfull hlogb0
        · simpa only [Nat.cast_add, Nat.cast_one] using hcorrection
      _ ≤ Real.log (y : ℝ) * B + Real.log (y : ℝ) * B := by
        gcongr
      _ = 2 * Real.log (y : ℝ) * B := by ring
  · have hba : b ≤ a := Nat.le_of_not_gt hab
    have hempty : Finset.Ioc (x / t) (y / t) = ∅ := by
      exact Finset.Ioc_eq_empty (by simpa only [a, b] using hab)
    rw [hempty]
    simp
    have hy1 : 1 ≤ y := by omega
    have hlog : 0 ≤ Real.log (y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hy1)
    have hmajor := reciprocalIntervalMajorant_nonneg hy1 (by omega : 0 < L)
    positivity

end

end ReciprocalIntervalEstimate
end Erdos378
