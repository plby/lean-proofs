import ErdosProblems.Erdos67.StationaryTranslationStabilizer

/-!
# Equal masses at all primitive frequencies of a fixed order

The prime translation budget and the elementary proper-subgroup divergence
theorem force the stabilizer of the atom weights to be the whole unit group.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

def coprimePrimeBelowEquiv (q : ℕ+) (X : ℕ) :
    CoprimePrimeBelow q X ≃ {p : ℕ // p < X ∧ p.Prime ∧ Nat.Coprime p q.val} where
  toFun p := ⟨p.val.val.val, p.val.val.isLt, p.val.property, p.property⟩
  invFun p := ⟨⟨⟨p.val, p.property.1⟩, p.property.2.1⟩, p.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_coprime_prime_indicator (q : ℕ+) (X : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ range X, if n.Prime ∧ Nat.Coprime n q.val then g n else 0) =
      ∑ p : CoprimePrimeBelow q X, g p.val.val.val := by
  classical
  let S := (range X).filter (fun n ↦ n.Prime ∧ Nat.Coprime n q.val)
  let : Fintype {n : ℕ // n < X ∧ n.Prime ∧ Nat.Coprime n q.val} :=
    Fintype.ofEquiv (CoprimePrimeBelow q X) (coprimePrimeBelowEquiv q X)
  have hs := sum_subtype (p := fun n ↦ n < X ∧ n.Prime ∧ Nat.Coprime n q.val)
    (F := inferInstance) S (fun n ↦ by simp only [S, mem_filter, mem_range]) g
  have he := (coprimePrimeBelowEquiv q X).sum_comp
    (fun p : {p : ℕ // p < X ∧ p.Prime ∧ Nat.Coprime p q.val} ↦ g p.val)
  calc
    _ = ∑ n ∈ S, g n := (sum_filter (s := range X) _ g).symm
    _ = _ := hs.trans he.symm

noncomputable def primeTranslationReciprocal (σ : ProbabilityMeasure FrequencyCircle)
    (q : ℕ+) (p : ℕ) : ℝ :=
  if p.Prime ∧ Nat.Coprime p q.val then primitiveTranslationCost σ q (residueUnit q p) / p else 0

theorem primeTranslationReciprocal_nonneg (σ : ProbabilityMeasure FrequencyCircle)
    (q : ℕ+) (p : ℕ) : 0 ≤ primeTranslationReciprocal σ q p := by
  unfold primeTranslationReciprocal
  split_ifs
  · exact div_nonneg (translationCost_nonneg (primitiveAtomRoot σ q) _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem summable_primeTranslationReciprocal (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ) (q : ℕ+) :
    Summable (primeTranslationReciprocal σ q) := by
  apply summable_of_sum_range_le (primeTranslationReciprocal_nonneg σ q) (c := 1)
  intro X
  unfold primeTranslationReciprocal
  rw [sum_coprime_prime_indicator]
  have he : (∑ p : CoprimePrimeBelow q X,
      primitiveTranslationCost σ q (residueUnit q p.val.val.val) / p.val.val.val) =
      ∑ p : CoprimePrimeBelow q X,
        primitiveTranslationCost σ q (ZMod.unitOfCoprime p.val.val.val p.property) /
          p.val.val.val := by
    apply sum_congr rfl
    intro p _
    rw [residueUnit_of_coprime q _ p.property]
  rw [he]
  exact rational_prime_translation_budget Q hQ hCD σ hσ q X

theorem rational_atom_stabilizer_eq_top (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ) (q : ℕ+) :
    translationStabilizer (primitiveAtomRoot σ q) = ⊤ := by
  classical
  apply top_unique
  intro u _
  by_contra hu
  obtain ⟨ε, hε, hgap⟩ := exists_uniform_translationCost_gap (primitiveAtomRoot σ q) u hu
  have hsum := (summable_primeTranslationReciprocal Q hQ hCD σ hσ q).mul_left (1 / ε)
  have hbad : Summable (badPrimeReciprocal q (translationStabilizer (primitiveAtomRoot σ q))) := by
    apply hsum.of_nonneg_of_le (badPrimeReciprocal_nonneg q _)
    intro p
    by_cases hp : BadResiduePrime q (translationStabilizer (primitiveAtomRoot σ q)) p
    · have hcost : ε ≤ primitiveTranslationCost σ q (residueUnit q p) := hgap _ hp.2.2
      have hpc : p.Prime ∧ Nat.Coprime p q.val := ⟨hp.1, hp.2.1⟩
      simp only [badPrimeReciprocal, if_pos hp, primeTranslationReciprocal, if_pos hpc]
      have hh : 1 ≤ primitiveTranslationCost σ q (residueUnit q p) / ε :=
        (le_div_iff₀ hε).mpr (by simpa using hcost)
      have hd := div_le_div_of_nonneg_right hh (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
      calc
        _ ≤ (primitiveTranslationCost σ q (residueUnit q p) / ε) / p := hd
        _ = _ := by ring
    · rw [badPrimeReciprocal, if_neg hp]
      exact mul_nonneg (by positivity) (primeTranslationReciprocal_nonneg σ q p)
  exact not_summable_badPrimeReciprocal q _ u hu hbad

theorem primitive_atom_masses_equal (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (q : ℕ+) (a b : (ZMod q.val)ˣ) :
    (σ : Measure FrequencyCircle).real {primitiveFrequency q a} =
      (σ : Measure FrequencyCircle).real {primitiveFrequency q b} := by
  have he := constant_of_translationStabilizer_eq_top (primitiveAtomRoot σ q)
    (rational_atom_stabilizer_eq_top Q hQ hCD σ hσ q) a b
  have hs := congrArg (fun x : ℝ ↦ x ^ 2) he
  simpa only [primitiveAtomRoot, Real.sq_sqrt measureReal_nonneg] using hs

end Erdos67.StationaryModel
