import ErdosProblems.Erdos448.Basic

namespace Erdos448

open Filter
open scoped Topology BigOperators

/-!
This file contains the discrete summation step in the specialization of
Erdos--Tenenbaum Proposition 4.  The only analytic input is the one-scale
bound: after multiplying Proposition 3 by the weight from Proposition 2,
its three terms have the shapes formalized below.
-/

/-- A finite part of a convergent real p-series is bounded by its full sum. -/
lemma sum_Icc_natCast_rpow_le_tsum {p : ℝ} (hp : p < -1) (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ p) ≤
      ∑' k : ℕ, (k : ℝ) ^ p := by
  exact (Real.summable_nat_rpow.mpr hp).sum_le_tsum _
    (fun k _hk ↦ Real.rpow_nonneg (Nat.cast_nonneg k) p)

/-- Reflection in the interval `[1,M]` preserves a finite power sum. -/
lemma sum_Icc_reflect_rpow (p : ℝ) (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, ((M + 1 - k : ℕ) : ℝ) ^ p) =
      ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ p := by
  apply Finset.sum_bij (fun k _hk ↦ M + 1 - k)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_Icc] at hk₁ hk₂
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨M + 1 - j, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro k hk
    rfl

/-- The elementary convolution estimate used for both logarithmic terms
in Proposition 3.  Splitting according to which of `k` and `M+1-k` is
smaller bounds the product by one of two copies of the p-series with
exponent `a+b`. -/
theorem sum_Icc_rpow_mul_reflect_rpow_le
    {a b : ℝ} (ha : a < 0) (hb : b < 0) (hab : a + b < -1)
    (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M,
        (k : ℝ) ^ a * ((M + 1 - k : ℕ) : ℝ) ^ b) ≤
      2 * ∑' k : ℕ, (k : ℝ) ^ (a + b) := by
  have hpoint : ∀ k ∈ Finset.Icc 1 M,
      (k : ℝ) ^ a * ((M + 1 - k : ℕ) : ℝ) ^ b ≤
        (k : ℝ) ^ (a + b) +
          ((M + 1 - k : ℕ) : ℝ) ^ (a + b) := by
    intro k hk
    have hkIcc := Finset.mem_Icc.mp hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hkIcc.1
    have hjposNat : 0 < M + 1 - k := by omega
    have hjpos : (0 : ℝ) < ((M + 1 - k : ℕ) : ℝ) := by
      exact_mod_cast hjposNat
    by_cases hkj : k ≤ M + 1 - k
    · have hbcomp : ((M + 1 - k : ℕ) : ℝ) ^ b ≤ (k : ℝ) ^ b := by
        apply Real.rpow_le_rpow_of_nonpos hkpos
        · exact_mod_cast hkj
        · exact hb.le
      calc
        (k : ℝ) ^ a * ((M + 1 - k : ℕ) : ℝ) ^ b
            ≤ (k : ℝ) ^ a * (k : ℝ) ^ b :=
          mul_le_mul_of_nonneg_left hbcomp
            (Real.rpow_nonneg (Nat.cast_nonneg k) a)
        _ = (k : ℝ) ^ (a + b) := (Real.rpow_add hkpos a b).symm
        _ ≤ (k : ℝ) ^ (a + b) +
            ((M + 1 - k : ℕ) : ℝ) ^ (a + b) := by
          exact le_add_of_nonneg_right
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hjk : M + 1 - k ≤ k := Nat.le_of_not_ge hkj
      have hacomp : (k : ℝ) ^ a ≤ ((M + 1 - k : ℕ) : ℝ) ^ a := by
        apply Real.rpow_le_rpow_of_nonpos hjpos
        · exact_mod_cast hjk
        · exact ha.le
      calc
        (k : ℝ) ^ a * ((M + 1 - k : ℕ) : ℝ) ^ b
            ≤ ((M + 1 - k : ℕ) : ℝ) ^ a *
                ((M + 1 - k : ℕ) : ℝ) ^ b :=
          mul_le_mul_of_nonneg_right hacomp
            (Real.rpow_nonneg (Nat.cast_nonneg _) b)
        _ = ((M + 1 - k : ℕ) : ℝ) ^ (a + b) :=
          (Real.rpow_add hjpos a b).symm
        _ ≤ (k : ℝ) ^ (a + b) +
            ((M + 1 - k : ℕ) : ℝ) ^ (a + b) := by
          exact le_add_of_nonneg_left
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    (∑ k ∈ Finset.Icc 1 M,
        (k : ℝ) ^ a * ((M + 1 - k : ℕ) : ℝ) ^ b)
        ≤ ∑ k ∈ Finset.Icc 1 M,
            ((k : ℝ) ^ (a + b) +
              ((M + 1 - k : ℕ) : ℝ) ^ (a + b)) :=
      Finset.sum_le_sum hpoint
    _ = (∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (a + b)) +
        ∑ k ∈ Finset.Icc 1 M,
          ((M + 1 - k : ℕ) : ℝ) ^ (a + b) :=
      Finset.sum_add_distrib
    _ = 2 * ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (a + b) := by
      rw [sum_Icc_reflect_rpow]
      ring
    _ ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ (a + b) := by
      gcongr
      exact sum_Icc_natCast_rpow_le_tsum hab M

/-- The explicit constant in the finite summation form of Proposition 4.
Here `a` is the combined outer exponent
`-(1/2+eps) log y + (y-3)/2`, while `b=(y-1)/2`.
The last p-series corresponds to the `L^(-1/2)` term. -/
noncomputable def prop4SummationConstant
    (a b δ C D : ℝ) : ℝ :=
  D * ((1 + 2 * δ ^ b) * (∑' k : ℕ, (k : ℝ) ^ (a + b)) +
    2 * C * δ ^ (-(1 : ℝ) / 2) *
      (∑' k : ℕ, (k : ℝ) ^ (a - 1 / 2)))

/-- Proposition 4's finite scale summation.  The hypothesis `hL` is the
only fact about the moving logarithm needed here: if `M` is the largest
admissible scale then `L(k)` is bounded below by a positive constant times
`M+1-k`. -/
theorem prop4_weighted_scale_sum_le_linear
    {a b δ C D : ℝ}
    (ha : a < 0) (hb : b < 0)
    (hab : a + b < -1) (haHalf : a - 1 / 2 < -1)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (s : ℕ → ℝ) (L : ℕ → ℝ) (M x : ℕ)
    (hL : ∀ k ∈ Finset.Icc 1 M,
      δ * (M + 1 - k : ℕ) ≤ L k)
    (hscale : ∀ k ∈ Finset.Icc 1 M,
      s k ≤ D * x *
        ((k : ℝ) ^ (a + b) + (k : ℝ) ^ a * L k ^ b +
          C * (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2))) :
    (∑ k ∈ Finset.Icc 1 M, s k) ≤
      prop4SummationConstant a b δ C D * x := by
  let T : ℝ := ∑' k : ℕ, (k : ℝ) ^ (a + b)
  let U : ℝ := ∑' k : ℕ, (k : ℝ) ^ (a - 1 / 2)
  have hT0 : 0 ≤ T := by
    exact tsum_nonneg fun k ↦ Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hU0 : 0 ≤ U := by
    exact tsum_nonneg fun k ↦ Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hδb0 : 0 ≤ δ ^ b := Real.rpow_nonneg hδ.le _
  have hδh0 : 0 ≤ δ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hδ.le _
  have hfirst :
      (∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (a + b)) ≤ T := by
    exact sum_Icc_natCast_rpow_le_tsum hab M
  have hmiddle :
      (∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ a * L k ^ b) ≤
        2 * δ ^ b * T := by
    calc
      (∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ a * L k ^ b)
          ≤ ∑ k ∈ Finset.Icc 1 M,
              δ ^ b * ((k : ℝ) ^ a *
                ((M + 1 - k : ℕ) : ℝ) ^ b) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkIcc := Finset.mem_Icc.mp hk
            have hjposNat : 0 < M + 1 - k := by omega
            have hjpos : (0 : ℝ) < ((M + 1 - k : ℕ) : ℝ) := by
              exact_mod_cast hjposNat
            have hbase : δ * ((M + 1 - k : ℕ) : ℝ) ≤ L k := by
              exact_mod_cast hL k hk
            have hrpow : L k ^ b ≤
                (δ * ((M + 1 - k : ℕ) : ℝ)) ^ b := by
              exact Real.rpow_le_rpow_of_nonpos (mul_pos hδ hjpos) hbase hb.le
            calc
              (k : ℝ) ^ a * L k ^ b ≤
                  (k : ℝ) ^ a *
                    (δ * ((M + 1 - k : ℕ) : ℝ)) ^ b :=
                mul_le_mul_of_nonneg_left hrpow
                  (Real.rpow_nonneg (Nat.cast_nonneg k) _)
              _ = δ ^ b * ((k : ℝ) ^ a *
                    ((M + 1 - k : ℕ) : ℝ) ^ b) := by
                rw [Real.mul_rpow hδ.le (Nat.cast_nonneg _)]
                ring
      _ = δ ^ b * (∑ k ∈ Finset.Icc 1 M,
            (k : ℝ) ^ a * ((M + 1 - k : ℕ) : ℝ) ^ b) := by
        rw [Finset.mul_sum]
      _ ≤ δ ^ b * (2 * T) := by
        apply mul_le_mul_of_nonneg_left _ hδb0
        exact sum_Icc_rpow_mul_reflect_rpow_le ha hb hab M
      _ = 2 * δ ^ b * T := by ring
  have hlast :
      (∑ k ∈ Finset.Icc 1 M,
          (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2)) ≤
        2 * δ ^ (-(1 : ℝ) / 2) * U := by
    have hbHalf : -(1 : ℝ) / 2 < 0 := by norm_num
    have habHalf : a + (-(1 : ℝ) / 2) < -1 := by
      linarith
    calc
      (∑ k ∈ Finset.Icc 1 M,
          (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2))
          ≤ ∑ k ∈ Finset.Icc 1 M,
              δ ^ (-(1 : ℝ) / 2) * ((k : ℝ) ^ a *
                ((M + 1 - k : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkIcc := Finset.mem_Icc.mp hk
            have hjposNat : 0 < M + 1 - k := by omega
            have hjpos : (0 : ℝ) < ((M + 1 - k : ℕ) : ℝ) := by
              exact_mod_cast hjposNat
            have hbase : δ * ((M + 1 - k : ℕ) : ℝ) ≤ L k := by
              exact_mod_cast hL k hk
            have hrpow : L k ^ (-(1 : ℝ) / 2) ≤
                (δ * ((M + 1 - k : ℕ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
              exact Real.rpow_le_rpow_of_nonpos (mul_pos hδ hjpos) hbase hbHalf.le
            calc
              (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2) ≤
                  (k : ℝ) ^ a *
                    (δ * ((M + 1 - k : ℕ) : ℝ)) ^ (-(1 : ℝ) / 2) :=
                mul_le_mul_of_nonneg_left hrpow
                  (Real.rpow_nonneg (Nat.cast_nonneg k) _)
              _ = δ ^ (-(1 : ℝ) / 2) * ((k : ℝ) ^ a *
                    ((M + 1 - k : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
                rw [Real.mul_rpow hδ.le (Nat.cast_nonneg _)]
                ring
      _ = δ ^ (-(1 : ℝ) / 2) * (∑ k ∈ Finset.Icc 1 M,
            (k : ℝ) ^ a *
              ((M + 1 - k : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
        rw [Finset.mul_sum]
      _ ≤ δ ^ (-(1 : ℝ) / 2) * (2 * U) := by
        apply mul_le_mul_of_nonneg_left _ hδh0
        dsimp [U]
        have hconv :=
          sum_Icc_rpow_mul_reflect_rpow_le ha hbHalf habHalf M
        rw [show a + (-(1 : ℝ) / 2) = a - 1 / 2 by ring] at hconv
        exact hconv
      _ = 2 * δ ^ (-(1 : ℝ) / 2) * U := by ring
  have hinside :
      (∑ k ∈ Finset.Icc 1 M,
          ((k : ℝ) ^ (a + b) + (k : ℝ) ^ a * L k ^ b +
            C * (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2))) ≤
        (1 + 2 * δ ^ b) * T +
          2 * C * δ ^ (-(1 : ℝ) / 2) * U := by
    rw [show (∑ k ∈ Finset.Icc 1 M,
        ((k : ℝ) ^ (a + b) + (k : ℝ) ^ a * L k ^ b +
          C * (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2))) =
      (∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (a + b)) +
      (∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ a * L k ^ b) +
      C * (∑ k ∈ Finset.Icc 1 M,
        (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2)) by
          simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
          ring_nf]
    calc
      _ ≤ T + 2 * δ ^ b * T +
          C * (2 * δ ^ (-(1 : ℝ) / 2) * U) := by
        gcongr
      _ = (1 + 2 * δ ^ b) * T +
          2 * C * δ ^ (-(1 : ℝ) / 2) * U := by ring
  calc
    (∑ k ∈ Finset.Icc 1 M, s k)
        ≤ ∑ k ∈ Finset.Icc 1 M, D * x *
            ((k : ℝ) ^ (a + b) + (k : ℝ) ^ a * L k ^ b +
              C * (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2)) :=
      Finset.sum_le_sum hscale
    _ = D * x * (∑ k ∈ Finset.Icc 1 M,
          ((k : ℝ) ^ (a + b) + (k : ℝ) ^ a * L k ^ b +
            C * (k : ℝ) ^ a * L k ^ (-(1 : ℝ) / 2))) := by
      rw [Finset.mul_sum]
    _ ≤ D * x * ((1 + 2 * δ ^ b) * T +
          2 * C * δ ^ (-(1 : ℝ) / 2) * U) := by
      gcongr
    _ = prop4SummationConstant a b δ C D * x := by
      dsimp [prop4SummationConstant, T, U]
      ring

/-- The summation constant is nonnegative in the parameter range used in
the moment argument. -/
theorem prop4SummationConstant_nonneg
    {a b δ C D : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    0 ≤ prop4SummationConstant a b δ C D := by
  unfold prop4SummationConstant
  positivity

/-- A direct interface matching Propositions 2 and 3.  Proposition 2
contributes the weight `k^c`; Proposition 3 contributes `k^q` and the
parenthesized three-term expression.  Thus `a=c+q` in the finite
summation theorem above. -/
theorem prop4_of_prop2_prop3_at
    {c q b δ C A B : ℝ}
    (ha : c + q < 0) (hb : b < 0)
    (hab : (c + q) + b < -1)
    (haHalf : (c + q) - 1 / 2 < -1)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (total : ℝ) (scale : ℕ → ℝ) (L : ℕ → ℝ) (M x : ℕ)
    (hL : ∀ k ∈ Finset.Icc 1 M,
      δ * (M + 1 - k : ℕ) ≤ L k)
    (hProp2 : total ≤
      A * ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ c * scale k)
    (hProp3 : ∀ k ∈ Finset.Icc 1 M,
      scale k ≤ B * x * (k : ℝ) ^ q *
        ((k : ℝ) ^ b + L k ^ b +
          C * L k ^ (-(1 : ℝ) / 2))) :
    total ≤ prop4SummationConstant (c + q) b δ C (A * B) * x := by
  let weighted : ℕ → ℝ := fun k ↦ A * (k : ℝ) ^ c * scale k
  have hweighted : ∀ k ∈ Finset.Icc 1 M,
      weighted k ≤ (A * B) * x *
        ((k : ℝ) ^ ((c + q) + b) +
          (k : ℝ) ^ (c + q) * L k ^ b +
          C * (k : ℝ) ^ (c + q) * L k ^ (-(1 : ℝ) / 2)) := by
    intro k hk
    have hkposNat : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
    calc
      weighted k = A * (k : ℝ) ^ c * scale k := rfl
      _ ≤ A * (k : ℝ) ^ c *
          (B * x * (k : ℝ) ^ q *
            ((k : ℝ) ^ b + L k ^ b +
              C * L k ^ (-(1 : ℝ) / 2))) := by
        exact mul_le_mul_of_nonneg_left (hProp3 k hk)
          (mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg k) _))
      _ = (A * B) * x *
          ((k : ℝ) ^ ((c + q) + b) +
            (k : ℝ) ^ (c + q) * L k ^ b +
            C * (k : ℝ) ^ (c + q) * L k ^ (-(1 : ℝ) / 2)) := by
        rw [Real.rpow_add hkpos (c + q) b,
          Real.rpow_add hkpos c q]
        ring
  calc
    total ≤ ∑ k ∈ Finset.Icc 1 M, weighted k := by
      calc
        total ≤ A * ∑ k ∈ Finset.Icc 1 M,
            (k : ℝ) ^ c * scale k := hProp2
        _ = ∑ k ∈ Finset.Icc 1 M, weighted k := by
          rw [Finset.mul_sum]
          simp only [weighted]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ ≤ prop4SummationConstant (c + q) b δ C (A * B) * x :=
      prop4_weighted_scale_sum_le_linear ha hb hab haHalf hδ hC
        (mul_nonneg hA hB) weighted L M x hL hweighted

/-- Eventual linear first moment, in the exact form consumed by the
density-theoretic Markov step. -/
theorem eventually_linear_firstMoment_of_prop2_prop3
    {c q b δ C A B : ℝ}
    (ha : c + q < 0) (hb : b < 0)
    (hab : (c + q) + b < -1)
    (haHalf : (c + q) - 1 / 2 < -1)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : ℕ → ℝ) (scale : ℕ → ℕ → ℝ)
    (L : ℕ → ℕ → ℝ) (M : ℕ → ℕ)
    (hL : ∀ᶠ x in atTop, ∀ k ∈ Finset.Icc 1 (M x),
      δ * (M x + 1 - k : ℕ) ≤ L x k)
    (hProp2 : ∀ᶠ x in atTop,
      (∑ n ∈ Finset.range x, f n) ≤
        A * ∑ k ∈ Finset.Icc 1 (M x),
          (k : ℝ) ^ c * (∑ n ∈ Finset.range x, scale k n))
    (hProp3 : ∀ᶠ x in atTop,
      ∀ k ∈ Finset.Icc 1 (M x),
        (∑ n ∈ Finset.range x, scale k n) ≤
          B * x * (k : ℝ) ^ q *
            ((k : ℝ) ^ b + L x k ^ b +
              C * L x k ^ (-(1 : ℝ) / 2))) :
    ∀ᶠ x in atTop,
      (∑ n ∈ Finset.range x, f n) ≤
        prop4SummationConstant (c + q) b δ C (A * B) * x := by
  filter_upwards [hL, hProp2, hProp3] with x hxL hxProp2 hxProp3
  exact prop4_of_prop2_prop3_at ha hb hab haHalf hδ hC hA hB
    (∑ n ∈ Finset.range x, f n)
    (fun k ↦ ∑ n ∈ Finset.range x, scale k n)
    (L x) (M x) x hxL hxProp2 hxProp3

/-- The numerical restriction in Erdos--Tenenbaum Proposition 4 is
exactly what is needed for all three p-series exponents above. -/
theorem et_prop4_exponent_conditions
    {y eps : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (_heps0 : 0 < eps)
    (heps : eps <
      (1 - y + (1 / 2 : ℝ) * Real.log y) / (-Real.log y)) :
    let c := -(1 / 2 + eps) * Real.log y
    let q := (y - 3) / 2
    let b := (y - 1) / 2
    c + q < 0 ∧ b < 0 ∧ (c + q) + b < -1 ∧
      (c + q) - 1 / 2 < -1 := by
  dsimp only
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy1
  have hden : 0 < -Real.log y := neg_pos.mpr hlog
  have hmul : eps * (-Real.log y) <
      1 - y + (1 / 2 : ℝ) * Real.log y :=
    (lt_div_iff₀ hden).mp heps
  have hc : -(1 / 2 + eps) * Real.log y < 1 - y := by
    nlinarith
  constructor
  · nlinarith
  constructor
  · linarith
  constructor <;> nlinarith

/-- The fixed parameters used in the formal proof satisfy the strict
admissibility inequality. -/
theorem et_half_one_fifth_admissible :
    (1 / 5 : ℝ) <
      (1 - (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) /
        (-Real.log (1 / 2 : ℝ)) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2lt : Real.log (2 : ℝ) < 5 / 7 := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hloghalf]
  rw [show - -Real.log (2 : ℝ) = Real.log 2 by ring]
  apply (lt_div_iff₀ hlog2pos).2
  nlinarith

/-- All concrete exponent inequalities for `y=1/2`, `eps=1/5`. -/
theorem et_half_one_fifth_exponent_conditions :
    let c := (7 / 10 : ℝ) * Real.log 2
    let q := -(5 / 4 : ℝ)
    let b := -(1 / 4 : ℝ)
    c + q < 0 ∧ b < 0 ∧ (c + q) + b < -1 ∧
      (c + q) - 1 / 2 < -1 := by
  have h := et_prop4_exponent_conditions
    (y := (1 / 2 : ℝ)) (eps := (1 / 5 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    et_half_one_fifth_admissible
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  dsimp only at h ⊢
  rw [hloghalf] at h
  convert h using 1 <;> ring_nf

end Erdos448
