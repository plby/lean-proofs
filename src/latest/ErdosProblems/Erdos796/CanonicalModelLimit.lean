import ErdosProblems.Erdos796.BucketWeightLimit
import ErdosProblems.Erdos796.ModelLimitFinite
import ErdosProblems.Erdos796.ModelScoreExcess
import ErdosProblems.Erdos796.BaselineAsymptotic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos796

open Filter Topology
open scoped BigOperators Nat.Prime

/-- The real total number of large-prime buckets. -/
noncomputable def totalBucketWeight (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n.sqrt, (bucketCount n j : ℝ)

/-- The finite correction made by the first `J` buckets relative to the
constant canonical tail excess at the cutoff. -/
noncomputable def canonicalHeadCorrection
    (J n : ℕ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.range J,
    (bucketCount n (k + 1) : ℝ) *
      (excess U (k + 1) - excess U J)

/-- The limiting weighted version of `canonicalHeadCorrection`. -/
noncomputable def canonicalHeadCorrectionValue
    (J : ℕ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.range J,
    cofactorWeight (k + 1) *
      (excess U (k + 1) - excess U J)

/-- Reindex the positive interval `1,…,J` by `k ↦ k+1`. -/
theorem sum_Icc_one_eq_sum_range_succ (J : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 J, f j) =
      ∑ k ∈ Finset.range J, f (k + 1) := by
  classical
  have hset :
      (Finset.range J).image (fun k : ℕ => k + 1) =
        Finset.Icc 1 J := by
    ext j
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨hj1, hjJ⟩
      refine ⟨j - 1, by omega, by omega⟩
  rw [← hset]
  refine Finset.sum_image (s := Finset.range J) (f := f)
    (g := fun k : ℕ => k + 1) ?_
  exact Set.injOn_of_injective (by
    intro x y hxy
    exact Nat.add_right_cancel hxy)

/-- On the second-order scale, division by `n/log n` eventually agrees with
multiplication by `log n/n`. -/
theorem eventually_div_secondOrderScale_eq (f : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      f n / secondOrderScale n =
        (Real.log (n : ℝ) / (n : ℝ)) * f n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlog0 : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  simp only [secondOrderScale]
  field_simp

/-- Fixed-bucket convergence in the normalization used by the model score. -/
theorem bucketCount_div_secondOrderScale_tendsto
    (hPNT : PrimeNumberTheorem) (j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun n : ℕ => (bucketCount n j : ℝ) / secondOrderScale n)
      atTop (nhds (cofactorWeight j)) := by
  have h := bucketCount_weight_tendsto hPNT j hj
  exact h.congr' ((eventually_div_secondOrderScale_eq
    (fun n : ℕ => (bucketCount n j : ℝ))).mono fun _ hn => hn.symm)

/-- The total bucket mass is exactly the difference between the prime counts
at `n` and at the square-root boundary. -/
theorem totalBucketWeight_eq (n : ℕ) :
    totalBucketWeight n =
      (Nat.primeCounting n : ℝ) -
        (Nat.primeCounting n.sqrt : ℝ) := by
  rw [totalBucketWeight, ← Nat.cast_sum, sum_bucketCount,
    Nat.cast_sub (primeCounting_sqrt_le n)]

/-- The normalized total mass of all large-prime buckets tends to one. -/
theorem totalBucketWeight_div_secondOrderScale_tendsto
    (hPNT : PrimeNumberTheorem) :
    Tendsto
      (fun n : ℕ => totalBucketWeight n / secondOrderScale n)
      atTop (nhds 1) := by
  have hsqrt : Tendsto
      (fun n : ℕ =>
        (Nat.primeCounting n.sqrt : ℝ) / secondOrderScale n)
      atTop (nhds 0) := sqrtPrimeBoundaryNegligible
  have hdiff := hPNT.sub hsqrt
  have heq : ∀ n : ℕ,
      totalBucketWeight n / secondOrderScale n =
        (Nat.primeCounting n : ℝ) / secondOrderScale n -
          (Nat.primeCounting n.sqrt : ℝ) / secondOrderScale n := by
    intro n
    rw [totalBucketWeight_eq]
    ring
  simpa using! hdiff.congr'
    (Eventually.of_forall fun n => (heq n).symm)

/-- The finitely many head corrections converge term by term. -/
theorem canonicalHeadCorrection_div_secondOrderScale_tendsto
    (hPNT : PrimeNumberTheorem) (J : ℕ) (U : ℕ → Finset ℕ) :
    Tendsto
      (fun n : ℕ =>
        canonicalHeadCorrection J n U / secondOrderScale n)
      atTop (nhds (canonicalHeadCorrectionValue J U)) := by
  have hsum : Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range J,
          ((bucketCount n (k + 1) : ℝ) / secondOrderScale n) *
            (excess U (k + 1) - excess U J))
      atTop
      (nhds (∑ k ∈ Finset.range J,
        cofactorWeight (k + 1) *
          (excess U (k + 1) - excess U J))) := by
    apply tendsto_finsetSum
    intro k hk
    exact (bucketCount_div_secondOrderScale_tendsto hPNT (k + 1)
      (by omega)).mul_const (excess U (k + 1) - excess U J)
  have heq : ∀ n : ℕ,
      canonicalHeadCorrection J n U / secondOrderScale n =
        ∑ k ∈ Finset.range J,
          ((bucketCount n (k + 1) : ℝ) / secondOrderScale n) *
            (excess U (k + 1) - excess U J) := by
    intro n
    rw [canonicalHeadCorrection, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simpa [canonicalHeadCorrectionValue] using! hsum.congr'
    (Eventually.of_forall fun n => (heq n).symm)

/-- Exact total-minus-head decomposition for a canonical extension.  The
square-root cutoff is the only reason for the explicit hypothesis `J ≤ √n`.
It is valid also at `J = 0`, when the head sum is empty. -/
theorem modelExcessSum_canonicalExtension_eq
    {J n : ℕ} {U : ℕ → Finset ℕ} (hU : CompatiblePrefix J U)
    (hJsqrt : J ≤ n.sqrt) :
    modelExcessSum n (canonicalExtension J U) =
      excess U J * totalBucketWeight n +
        canonicalHeadCorrection J n U := by
  classical
  have hUnion :
      Finset.Icc 1 J ∪ Finset.Ioc J n.sqrt =
        Finset.Icc 1 n.sqrt := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hDisjoint :
      Disjoint (Finset.Icc 1 J) (Finset.Ioc J n.sqrt) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjHead hjTail
    simp only [Finset.mem_Icc] at hjHead
    simp only [Finset.mem_Ioc] at hjTail
    omega
  have hHead :
      (∑ j ∈ Finset.Icc 1 J,
        (bucketCount n j : ℝ) *
          excess (canonicalExtension J U) j) =
        ∑ j ∈ Finset.Icc 1 J,
          (bucketCount n j : ℝ) * excess U j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ J := (Finset.mem_Icc.mp hj).2
    rw [show excess (canonicalExtension J U) j = excess U j by
      simp [excess, excessInt, canonicalExtension_of_le hjle]]
  have hTail :
      (∑ j ∈ Finset.Ioc J n.sqrt,
        (bucketCount n j : ℝ) *
          excess (canonicalExtension J U) j) =
        ∑ j ∈ Finset.Ioc J n.sqrt,
          (bucketCount n j : ℝ) * excess U J := by
    apply Finset.sum_congr rfl
    intro j hj
    have hJj : J < j := (Finset.mem_Ioc.mp hj).1
    rw [excess_canonicalExtension hJj (hU.1 J le_rfl)]
  have hTotal :
      totalBucketWeight n =
        (∑ j ∈ Finset.Icc 1 J, (bucketCount n j : ℝ)) +
          ∑ j ∈ Finset.Ioc J n.sqrt, (bucketCount n j : ℝ) := by
    rw [totalBucketWeight, ← hUnion, Finset.sum_union hDisjoint]
  have hCorrection :
      canonicalHeadCorrection J n U =
        ∑ j ∈ Finset.Icc 1 J,
          (bucketCount n j : ℝ) * (excess U j - excess U J) := by
    rw [canonicalHeadCorrection]
    exact (sum_Icc_one_eq_sum_range_succ J (fun j =>
      (bucketCount n j : ℝ) * (excess U j - excess U J))).symm
  have hHeadAlgebra :
      (∑ j ∈ Finset.Icc 1 J,
        (bucketCount n j : ℝ) * excess U j) =
        excess U J *
            (∑ j ∈ Finset.Icc 1 J, (bucketCount n j : ℝ)) +
          ∑ j ∈ Finset.Icc 1 J,
            (bucketCount n j : ℝ) * (excess U j - excess U J) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hTailAlgebra :
      (∑ j ∈ Finset.Ioc J n.sqrt,
        (bucketCount n j : ℝ) * excess U J) =
        excess U J *
          (∑ j ∈ Finset.Ioc J n.sqrt, (bucketCount n j : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [modelExcessSum, ← hUnion, Finset.sum_union hDisjoint,
    hHead, hTail, hTotal, hCorrection, hHeadAlgebra, hTailAlgebra]
  ring

/-- The total weight of the first `J` positive buckets. -/
theorem sum_cofactorWeight_range_eq (J : ℕ) :
    (∑ k ∈ Finset.range J, cofactorWeight (k + 1)) =
      1 - 1 / (J + 1 : ℕ) := by
  simpa [cofactorTailPartial, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using! (cofactorTailPartial_eq 0 J)

/-- The limiting head correction is the prefix value minus the mass already
accounted for by the constant cutoff excess. -/
theorem canonicalHeadCorrectionValue_eq
    (J : ℕ) (U : ℕ → Finset ℕ) :
    canonicalHeadCorrectionValue J U =
      prefixCofactorSum J U -
        excess U J * (1 - 1 / (J + 1 : ℕ)) := by
  have hconst :
      (∑ k ∈ Finset.range J,
        cofactorWeight (k + 1) * excess U J) =
        excess U J *
          ∑ k ∈ Finset.range J, cofactorWeight (k + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [canonicalHeadCorrectionValue]
  calc
    (∑ k ∈ Finset.range J,
        cofactorWeight (k + 1) *
          (excess U (k + 1) - excess U J)) =
        ∑ k ∈ Finset.range J,
          (cofactorWeight (k + 1) * excess U (k + 1) -
            cofactorWeight (k + 1) * excess U J) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ k ∈ Finset.range J,
          cofactorWeight (k + 1) * excess U (k + 1)) -
        ∑ k ∈ Finset.range J,
          cofactorWeight (k + 1) * excess U J :=
      by rw [Finset.sum_sub_distrib]
    _ = prefixCofactorSum J U -
        excess U J *
          ∑ k ∈ Finset.range J, cofactorWeight (k + 1) := by
      rw [hconst, prefixCofactorSum]
      simp only [cofactorTerm]
    _ = prefixCofactorSum J U -
        excess U J * (1 - 1 / (J + 1 : ℕ)) := by
      rw [sum_cofactorWeight_range_eq]

/-- The total limiting constant from the total-minus-head decomposition is
exactly the cofactor value of the canonical extension. -/
theorem excess_add_canonicalHeadCorrectionValue_eq
    {J : ℕ} {U : ℕ → Finset ℕ} (hU : CompatiblePrefix J U) :
    excess U J + canonicalHeadCorrectionValue J U =
      cofactorValue (canonicalExtension J U) := by
  rw [canonicalHeadCorrectionValue_eq,
    cofactorValue_canonicalExtension_eq hU]
  ring

/-- The normalized excess of a fixed canonical extension converges to its
cofactor value. -/
theorem canonical_modelExcessSum_limit
    (hPNT : PrimeNumberTheorem) {J : ℕ} {U : ℕ → Finset ℕ}
    (hU : CompatiblePrefix J U) :
    Tendsto
      (fun n : ℕ =>
        modelExcessSum n (canonicalExtension J U) /
          secondOrderScale n)
      atTop (nhds (cofactorValue (canonicalExtension J U))) := by
  have htotal :=
    (totalBucketWeight_div_secondOrderScale_tendsto hPNT).const_mul
      (excess U J)
  have hhead :=
    canonicalHeadCorrection_div_secondOrderScale_tendsto hPNT J U
  have hsum := htotal.add hhead
  have heq : ∀ᶠ n : ℕ in atTop,
      excess U J * (totalBucketWeight n / secondOrderScale n) +
          canonicalHeadCorrection J n U / secondOrderScale n =
        modelExcessSum n (canonicalExtension J U) /
          secondOrderScale n := by
    filter_upwards [eventually_ge_atTop (J * J)] with n hn
    have hJsqrt : J ≤ n.sqrt := Nat.le_sqrt.mpr hn
    rw [modelExcessSum_canonicalExtension_eq hU hJsqrt]
    ring
  rw [← excess_add_canonicalHeadCorrectionValue_eq hU]
  simpa using! hsum.congr' heq

/-- Model-limit theorem for every fixed compatible prefix and its canonical
extension.  The sole analytic hypothesis is the normalized prime number
theorem. -/
theorem canonical_modelScore_limit
    (hPNT : PrimeNumberTheorem) {J : ℕ} {U : ℕ → Finset ℕ}
    (hU : CompatiblePrefix J U) :
    Tendsto
      (fun n : ℕ =>
        ((modelScore n (canonicalExtension J U) : ℝ) -
            (baseline n : ℝ)) /
          secondOrderScale n)
      atTop (nhds (cofactorValue (canonicalExtension J U))) := by
  have h := canonical_modelExcessSum_limit hPNT hU
  exact h.congr' (Eventually.of_forall fun n =>
    (normalized_modelScore_sub_baseline_eq n
      (canonicalExtension J U)).symm)

end Erdos796
