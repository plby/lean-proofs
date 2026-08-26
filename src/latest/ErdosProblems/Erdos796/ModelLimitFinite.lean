import ErdosProblems.Erdos796.GammaFinite
import ErdosProblems.Erdos796.BucketCompression
import ErdosProblems.Erdos796.Model

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite core of the cofactor-model limit

This file contains the part of the model-limit argument that is independent
of prime-number asymptotics.  A compatible prefix is canonically extended by
new primes, and its cofactor series is evaluated exactly.  This gives the
uniform prefix inequality used in the upper bound and an exact error formula
for truncating any summable compatible family.
-/

namespace Erdos796

open Filter Topology
open scoped BigOperators

/-- The weighted excess of the first `J` positive fibres.  The summation
index `k = 0, ..., J-1` corresponds to the cofactor index `j = k+1`. -/
noncomputable def prefixCofactorSum (J : ℕ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.range J, cofactorTerm U k

/-- Before the cutoff, canonical extension leaves every cofactor-series term
unchanged. -/
theorem cofactorTerm_canonicalExtension_of_lt
    {J k : ℕ} {U : ℕ → Finset ℕ} (hk : k < J) :
    cofactorTerm (canonicalExtension J U) k = cofactorTerm U k := by
  have hle : k + 1 ≤ J := by omega
  rw [cofactorTerm, cofactorTerm]
  congr 1
  simp [excess, excessInt, canonicalExtension_of_le hle]

theorem prefixCofactorSum_canonicalExtension
    (J : ℕ) (U : ℕ → Finset ℕ) :
    prefixCofactorSum J (canonicalExtension J U) = prefixCofactorSum J U := by
  rw [prefixCofactorSum, prefixCofactorSum]
  apply Finset.sum_congr rfl
  intro k hk
  exact cofactorTerm_canonicalExtension_of_lt (Finset.mem_range.mp hk)

/-- Every term after the cutoff is the cutoff excess times the corresponding
cofactor weight. -/
theorem cofactorTerm_canonicalExtension_tail
    {J : ℕ} {U : ℕ → Finset ℕ} (hU : CompatiblePrefix J U)
    (k : ℕ) :
    cofactorTerm (canonicalExtension J U) (k + J) =
      excess U J * cofactorWeight (J + 1 + k) := by
  have hgt : J < k + J + 1 := by omega
  have hsubset : U J ⊆ positiveIcc J := hU.1 J le_rfl
  rw [cofactorTerm]
  change cofactorWeight (k + J + 1) *
      excess (canonicalExtension J U) (k + J + 1) = _
  rw [excess_canonicalExtension hgt hsubset]
  rw [show k + J + 1 = J + 1 + k by omega]
  ring

/-- The canonical tail has the exact value `e_J/(J+1)`. -/
theorem hasSum_cofactorTerm_canonicalExtension_tail
    {J : ℕ} {U : ℕ → Finset ℕ} (hU : CompatiblePrefix J U) :
    HasSum (fun k : ℕ => cofactorTerm (canonicalExtension J U) (k + J))
      (excess U J / (J + 1 : ℕ)) := by
  have h := (hasSum_cofactorTail J).mul_left (excess U J)
  convert! h using 1
  · funext k
    exact cofactorTerm_canonicalExtension_tail hU k
  · push_cast
    ring

/-- Exact evaluation of the complete canonical-extension series. -/
theorem hasSum_cofactorTerm_canonicalExtension
    {J : ℕ} {U : ℕ → Finset ℕ} (hU : CompatiblePrefix J U) :
    HasSum (cofactorTerm (canonicalExtension J U))
      (prefixCofactorSum J U + excess U J / (J + 1 : ℕ)) := by
  have hfull :=
    (hasSum_nat_add_iff (f := cofactorTerm (canonicalExtension J U)) J).mp
      (hasSum_cofactorTerm_canonicalExtension_tail hU)
  have hhead :
      (∑ i ∈ Finset.range J, cofactorTerm (canonicalExtension J U) i) =
        prefixCofactorSum J U := by
    rw [← prefixCofactorSum_canonicalExtension J U, prefixCofactorSum]
  rw [hhead] at hfull
  simpa [add_comm] using! hfull

theorem canonicalExtension_hasCofactorValue
    {J : ℕ} {U : ℕ → Finset ℕ} (hU : CompatiblePrefix J U) :
    HasCofactorValue (canonicalExtension J U) :=
  (hasSum_cofactorTerm_canonicalExtension hU).summable

/-- The canonical extension is exactly its weighted prefix plus the
telescoping cutoff tail. -/
theorem cofactorValue_canonicalExtension_eq
    {J : ℕ} {U : ℕ → Finset ℕ} (hU : CompatiblePrefix J U) :
    cofactorValue (canonicalExtension J U) =
      prefixCofactorSum J U + excess U J / (J + 1 : ℕ) :=
  (hasSum_cofactorTerm_canonicalExtension hU).tsum_eq

/-- Every compatible summable cofactor value is bounded by the variational
supremum `Gamma`. -/
theorem cofactorValue_le_Gamma {U : ℕ → Finset ℕ}
    (hU : Compatible U) (hValue : HasCofactorValue U) :
    cofactorValue U ≤ Gamma := by
  rw [Gamma_eq_sSup_gammaScores]
  exact le_csSup gammaScores_bddAbove ⟨U, hU, hValue, rfl⟩

/-- The elementary lower bound `e_J ≥ -1-π(J)`, coming only from the
nonnegativity of the fibre cardinality. -/
theorem neg_one_add_primeCounting_le_excess (U : ℕ → Finset ℕ) (J : ℕ) :
    -((1 : ℝ) + Nat.primeCounting J) ≤ excess U J := by
  have hcard : 0 ≤ ((U J).card : ℝ) := by positivity
  have hreal :
      -((1 : ℝ) + Nat.primeCounting J) ≤
        ((U J).card : ℝ) - 1 - Nat.primeCounting J := by
    linarith
  simpa [excess, excessInt, Int.cast_sub, Int.cast_natCast] using! hreal

/-- Exact finite-prefix inequality from the model-limit proof:

`sum_{j≤J} w_j e_j ≤ Gamma + (1+π(J))/(J+1)`.
-/
theorem prefixCofactorSum_le_Gamma_add_primeError
    {J : ℕ} {U : ℕ → Finset ℕ} (hU : CompatiblePrefix J U) :
    prefixCofactorSum J U ≤
      Gamma + ((1 : ℝ) + Nat.primeCounting J) / (J + 1 : ℕ) := by
  have hcompat : Compatible (canonicalExtension J U) :=
    compatible_canonicalExtension hU
  have hvalue : HasCofactorValue (canonicalExtension J U) :=
    canonicalExtension_hasCofactorValue hU
  have hGamma := cofactorValue_le_Gamma hcompat hvalue
  rw [cofactorValue_canonicalExtension_eq hU] at hGamma
  have hden : (0 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by positivity
  have htailLower :
      -(((1 : ℝ) + Nat.primeCounting J) / (J + 1 : ℕ)) ≤
        excess U J / (J + 1 : ℕ) := by
    have h := div_le_div_of_nonneg_right
      (neg_one_add_primeCounting_le_excess U J) hden
    simpa only [neg_div] using! h
  linarith

/-! ## Exact comparison with an original finite-valued family -/

/-- A summable cofactor series splits exactly into its first `J` terms and
the translated infinite tail. -/
theorem cofactorValue_eq_tail_add_prefix
    {U : ℕ → Finset ℕ} (hValue : HasCofactorValue U) (J : ℕ) :
    cofactorValue U =
      (∑' k : ℕ, cofactorTerm U (k + J)) + prefixCofactorSum J U := by
  have htail : Summable (fun k : ℕ => cofactorTerm U (k + J)) :=
    (summable_nat_add_iff J).mpr hValue
  have hfull :=
    (hasSum_nat_add_iff (f := cofactorTerm U) J).mp htail.hasSum
  simpa [cofactorValue, prefixCofactorSum] using! hfull.tsum_eq

/-- Exact truncation error: replacing the tail of a finite-valued compatible
family by its canonical prime tail changes the value by the new exact tail
`e_J/(J+1)` minus the old translated tail. -/
theorem cofactorValue_canonicalExtension_sub_eq
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (hValue : HasCofactorValue U) (J : ℕ) :
    cofactorValue (canonicalExtension J U) - cofactorValue U =
      excess U J / (J + 1 : ℕ) -
        ∑' k : ℕ, cofactorTerm U (k + J) := by
  have hPrefix : CompatiblePrefix J U := compatible_compatiblePrefix hU
  rw [cofactorValue_canonicalExtension_eq hPrefix,
    cofactorValue_eq_tail_add_prefix hValue J]
  ring

/-- Quantitative approximation inequality with no analytic assumptions. -/
theorem abs_cofactorValue_canonicalExtension_sub_le
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (hValue : HasCofactorValue U) (J : ℕ) :
    |cofactorValue (canonicalExtension J U) - cofactorValue U| ≤
      |excess U J / (J + 1 : ℕ)| +
        |∑' k : ℕ, cofactorTerm U (k + J)| := by
  rw [cofactorValue_canonicalExtension_sub_eq hU hValue J]
  exact abs_sub _ _

/-- Hence any cutoff at which both the original tail and the exact canonical
tail are small gives a correspondingly accurate canonical approximation. -/
theorem abs_cofactorValue_canonicalExtension_sub_lt_two_mul
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (hValue : HasCofactorValue U) {J : ℕ} {eps : ℝ}
    (hCanonical : |excess U J / (J + 1 : ℕ)| < eps)
    (hOriginal : |∑' k : ℕ, cofactorTerm U (k + J)| < eps) :
    |cofactorValue (canonicalExtension J U) - cofactorValue U| < 2 * eps := by
  calc
    |cofactorValue (canonicalExtension J U) - cofactorValue U| ≤
        |excess U J / (J + 1 : ℕ)| +
          |∑' k : ℕ, cofactorTerm U (k + J)| :=
      abs_cofactorValue_canonicalExtension_sub_le hU hValue J
    _ < eps + eps := add_lt_add hCanonical hOriginal
    _ = 2 * eps := by ring

/-- The old translated tail itself tends to zero for every summable cofactor
series.  Controlling the separate exact canonical correction is the only
remaining input needed for convergence of the canonical truncations. -/
theorem tendsto_cofactorTail_zero (U : ℕ → Finset ℕ)
    (_hValue : HasCofactorValue U) :
    Tendsto (fun J : ℕ => ∑' k : ℕ, cofactorTerm U (k + J))
      atTop (nhds 0) :=
  tendsto_sum_nat_add (cofactorTerm U)

end Erdos796
