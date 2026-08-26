import ErdosProblems.Erdos796.Certificate
import ErdosProblems.Erdos796.CanonicalCompatibility

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The certificate as an admissible cofactor score

This file joins the finite ten-fibre certificate to its canonical prime tail.
It proves that the resulting compatible family has cofactor value exactly
`4 / 15`, and hence that this value belongs to the set whose supremum defines
`Gamma`.
-/

namespace Erdos796

open scoped BigOperators

/-- The infinite compatible family obtained from the certified ten-fibre
prefix by the canonical prime extension. -/
def certificateFamily : ℕ → Finset ℕ :=
  canonicalExtension 10 Certificate.certificatePrefix

/-- The canonical extension preserves the checked multiplicative
compatibility of the certificate. -/
theorem certificateFamily_compatible : Compatible certificateFamily := by
  exact compatible_canonicalExtension Certificate.certificatePrefix_compatible

/-- At the cutoff, the finite certificate has excess two. -/
theorem certificatePrefix_excessInt_ten :
    excessInt Certificate.certificatePrefix 10 = 2 := by
  have hprimeCount : Nat.primeCounting 10 = 4 := by decide
  norm_num [excessInt, Certificate.certificatePrefix,
    Certificate.prefixFiber, Certificate.prefixFiberName,
    Certificate.fiber, Certificate.fiberG, hprimeCount]

/-- The real cofactor weight is the image of the exact rational weight used
to check the finite certificate. -/
theorem cofactorWeight_eq_ratCast (j : ℕ) :
    cofactorWeight j = (Certificate.cofactorWeight j : ℝ) := by
  simp [Erdos796.cofactorWeight, Certificate.cofactorWeight]

/-- Each of the first ten real series terms is the real image of the
corresponding exact rational certificate term. -/
theorem certificateFamily_head_term_eq (k : ℕ) (hk : k < 10) :
    cofactorTerm certificateFamily k =
      (((Certificate.prefixExcess ⟨k, hk⟩ : ℚ) *
          Certificate.cofactorWeight (k + 1) : ℚ) : ℝ) := by
  have hle : k + 1 ≤ 10 := by omega
  have hexcess :
      excessInt certificateFamily (k + 1) =
        Certificate.prefixExcess ⟨k, hk⟩ := by
    have hfiber :
        certificateFamily (k + 1) = Certificate.certificatePrefix (k + 1) := by
      exact canonicalExtension_of_le hle
    rw [excessInt, hfiber]
    exact (Certificate.prefixExcess_eq_core_excessInt ⟨k, hk⟩).symm
  rw [cofactorTerm, excess, hexcess, cofactorWeight_eq_ratCast]
  norm_cast
  ring

/-- The head of the real cofactor series is exactly the rationally checked
value `14 / 165`. -/
theorem certificateFamily_head_sum_eq :
    ∑ k ∈ Finset.range 10, cofactorTerm certificateFamily k =
      (14 : ℝ) / 165 := by
  calc
    ∑ k ∈ Finset.range 10, cofactorTerm certificateFamily k =
        ∑ k : Fin 10, cofactorTerm certificateFamily k := by
      exact (Fin.sum_univ_eq_sum_range (cofactorTerm certificateFamily) 10).symm
    _ =
        ∑ k : Fin 10,
          (((Certificate.prefixExcess k : ℚ) *
              Certificate.cofactorWeight (k.1 + 1) : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      exact certificateFamily_head_term_eq k.1 k.2
    _ = (Certificate.prefixValue : ℝ) := by
      rw [Certificate.prefixValue]
      norm_cast
    _ = (14 : ℝ) / 165 := by
      rw [Certificate.prefix_value_eq]
      norm_num

/-- Every term after the cutoff is twice the corresponding canonical
cofactor weight. -/
theorem certificateFamily_tail_term_eq (k : ℕ) :
    cofactorTerm certificateFamily (k + 10) =
      2 * cofactorWeight (10 + 1 + k) := by
  have hgt : 10 < k + 10 + 1 := by omega
  have hsubset :
      Certificate.certificatePrefix 10 ⊆ positiveIcc 10 :=
    Certificate.certificatePrefix_compatible.1 10 le_rfl
  rw [cofactorTerm]
  change cofactorWeight (k + 10 + 1) *
      excess (canonicalExtension 10 Certificate.certificatePrefix) (k + 10 + 1) = _
  rw [excess_canonicalExtension hgt hsubset, excess]
  rw [certificatePrefix_excessInt_ten]
  norm_num
  rw [show k + 10 + 1 = 10 + 1 + k by omega]
  ring

/-- The cofactor-series tail after the first ten terms has exact sum
`2 / 11`. -/
theorem hasSum_certificateFamily_tail :
    HasSum (fun k : ℕ => cofactorTerm certificateFamily (k + 10))
      ((2 : ℝ) / 11) := by
  have h := (hasSum_cofactorTail 10).mul_left (2 : ℝ)
  convert! h using 1
  · funext k
    rw [certificateFamily_tail_term_eq]
  · norm_num

/-- The full cofactor series of the certificate family sums to `4 / 15`. -/
theorem hasSum_certificateFamily :
    HasSum (cofactorTerm certificateFamily) ((4 : ℝ) / 15) := by
  have hfull :=
    (hasSum_nat_add_iff (f := cofactorTerm certificateFamily) 10).mp
      hasSum_certificateFamily_tail
  rw [certificateFamily_head_sum_eq] at hfull
  convert! hfull using 1
  norm_num

theorem certificateFamily_hasCofactorValue :
    HasCofactorValue certificateFamily :=
  hasSum_certificateFamily.summable

theorem certificateFamily_cofactorValue_eq :
    cofactorValue certificateFamily = (4 : ℝ) / 15 := by
  exact hasSum_certificateFamily.tsum_eq

/-- The value `4 / 15` is one of the actual compatible, summable scores in
the set whose real supremum is `Gamma`.  This membership statement does not
presuppose that the score set is bounded above. -/
theorem four_fifteenths_mem_gamma_scores :
    ((4 : ℝ) / 15) ∈
      {x : ℝ | ∃ U : ℕ → Finset ℕ,
        Compatible U ∧ HasCofactorValue U ∧ cofactorValue U = x} := by
  exact ⟨certificateFamily, certificateFamily_compatible,
    certificateFamily_hasCofactorValue, certificateFamily_cofactorValue_eq⟩

end Erdos796
