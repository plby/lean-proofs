import ErdosProblems.Erdos796.CanonicalCompatibility

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary facts about the variational constant

This module constructs the zero-score compatible family consisting of `1`
and all primes.  It also names the score set whose supremum is `Gamma`.
-/

namespace Erdos796

/-- The values over which the real supremum defining `Gamma` is taken. -/
def gammaScores : Set ℝ :=
  {x : ℝ | ∃ U : ℕ → Finset ℕ,
    Compatible U ∧ HasCofactorValue U ∧ cofactorValue U = x}

theorem Gamma_eq_sSup_gammaScores : Gamma = sSup gammaScores := rfl

/-- The one-fibre seed `{1}` at cutoff one. -/
def unitPrefix (j : ℕ) : Finset ℕ :=
  if j = 1 then {1} else ∅

theorem unitPrefix_compatible : CompatiblePrefix 1 unitPrefix := by
  constructor
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simp [unitPrefix, positiveIcc]
    · simp [unitPrefix, positiveIcc]
  · intro i hi j hj m
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    unfold productRepCount
    calc
      ((unitPrefix i ×ˢ unitPrefix j).filter
          fun uv => uv.1 * uv.2 = m).card ≤
          (unitPrefix i ×ˢ unitPrefix j).card := Finset.card_filter_le _ _
      _ ≤ 2 := by
        rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
          simp [unitPrefix]

/-- The compatible family `{1} ∪ {p : p ≤ j}`. -/
def primeFamily : ℕ → Finset ℕ := canonicalExtension 1 unitPrefix

theorem primeFamily_compatible : Compatible primeFamily := by
  exact compatible_canonicalExtension unitPrefix_compatible

theorem excessInt_unitPrefix_one : excessInt unitPrefix 1 = 0 := by
  norm_num [excessInt, unitPrefix, Nat.primeCounting]

/-- The prime family has zero excess in every positive fibre. -/
theorem primeFamily_excessInt (j : ℕ) (hj : 1 ≤ j) :
    excessInt primeFamily j = 0 := by
  rcases hj.eq_or_lt with rfl | hj
  · simpa [primeFamily] using! excessInt_unitPrefix_one
  · rw [primeFamily, excessInt_canonicalExtension hj]
    · exact excessInt_unitPrefix_one
    · simp [unitPrefix, positiveIcc]

theorem primeFamily_excess (j : ℕ) (hj : 1 ≤ j) :
    excess primeFamily j = 0 := by
  simp [excess, primeFamily_excessInt j hj]

@[simp] theorem primeFamily_cofactorTerm (k : ℕ) :
    cofactorTerm primeFamily k = 0 := by
  rw [cofactorTerm, primeFamily_excess (k + 1) (by omega), mul_zero]

theorem primeFamily_hasCofactorValue : HasCofactorValue primeFamily := by
  have hzero : cofactorTerm primeFamily = fun _ => 0 := by
    funext k
    exact primeFamily_cofactorTerm k
  rw [HasCofactorValue, hzero]
  exact summable_zero

theorem primeFamily_cofactorValue : cofactorValue primeFamily = 0 := by
  have hzero : cofactorTerm primeFamily = fun _ => 0 := by
    funext k
    exact primeFamily_cofactorTerm k
  rw [cofactorValue, hzero, tsum_zero]

/-- In particular the score set defining `Gamma` is nonempty. -/
theorem zero_mem_gammaScores : (0 : ℝ) ∈ gammaScores := by
  exact ⟨primeFamily, primeFamily_compatible,
    primeFamily_hasCofactorValue, primeFamily_cofactorValue⟩

theorem gammaScores_nonempty : gammaScores.Nonempty :=
  ⟨0, zero_mem_gammaScores⟩

end Erdos796
