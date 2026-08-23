/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos240
import ErdosProblems.Erdos240.RationalPrimeBaker

/-!
# Elementary specializations for the rational Baker--Wüstholz input

This file isolates the elementary bookkeeping needed to apply a uniform
rational-prime linear-forms theorem to the finite stages used in Erdős
Problem 240.  It contains no linear-forms theorem itself.
-/

namespace Erdos240
namespace BakerSpecialization

/-- An integral coefficient cutoff dominating a real cutoff `B`.  The extra
factor `exp 1` ensures that the resulting integer cutoff is at least `exp 2`
when the external convention only assumes `B ≥ exp 1`. -/
noncomputable def integerCoeffBound (B : ℝ) : ℕ :=
  ⌈Real.exp 1 * B⌉₊

lemma le_integerCoeffBound {B : ℝ} (hB : Real.exp 1 ≤ B) :
    B ≤ (integerCoeffBound B : ℝ) := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  calc
    B ≤ Real.exp 1 * B := by
      exact le_mul_of_one_le_left ((Real.exp_pos 1).trans_le hB).le he
    _ ≤ (integerCoeffBound B : ℝ) := Nat.le_ceil _

lemma exp_two_le_integerCoeffBound {B : ℝ} (hB : Real.exp 1 ≤ B) :
    Real.exp 2 ≤ (integerCoeffBound B : ℝ) := by
  calc
    Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    _ ≤ Real.exp 1 * B := mul_le_mul_of_nonneg_left hB (Real.exp_pos 1).le
    _ ≤ (integerCoeffBound B : ℝ) := Nat.le_ceil _

/-- Passing from a real coefficient cutoff to `ceil (e B)` costs at most a
factor three in its logarithm. -/
lemma log_integerCoeffBound_le_three_mul_log {B : ℝ}
    (hB : Real.exp 1 ≤ B) :
    Real.log (integerCoeffBound B : ℝ) ≤ 3 * Real.log B := by
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le hB
  have hxpos : 0 < Real.exp 1 * B := mul_pos (Real.exp_pos 1) hBpos
  have hxone : 1 ≤ Real.exp 1 * B := by
    calc
      1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      _ = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp 1 * B := mul_le_mul_of_nonneg_left hB (Real.exp_pos 1).le
  have hceil : (integerCoeffBound B : ℝ) ≤ 2 * (Real.exp 1 * B) := by
    have hlt : (integerCoeffBound B : ℝ) < Real.exp 1 * B + 1 :=
      Nat.ceil_lt_add_one hxpos.le
    linarith
  have hboundPos : 0 < (integerCoeffBound B : ℝ) :=
    hBpos.trans_le (le_integerCoeffBound hB)
  have hlogB : 1 ≤ Real.log B :=
    (Real.le_log_iff_exp_le hBpos).2 hB
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  calc
    Real.log (integerCoeffBound B : ℝ) ≤
        Real.log (2 * (Real.exp 1 * B)) :=
      Real.log_le_log hboundPos hceil
    _ = Real.log 2 + Real.log (Real.exp 1) + Real.log B := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (mul_ne_zero (Real.exp_ne_zero 1) hBpos.ne'),
        Real.log_mul (Real.exp_ne_zero 1) hBpos.ne']
      ring
    _ = Real.log 2 + 1 + Real.log B := by rw [Real.log_exp]
    _ ≤ 3 * Real.log B := by linarith

lemma abs_int_cast_le_integerCoeffBound {B : ℝ} {z : ℤ}
    (hB : Real.exp 1 ≤ B) (hz : |(z : ℝ)| ≤ B) :
    |(z : ℝ)| ≤ (integerCoeffBound B : ℝ) :=
  hz.trans (le_integerCoeffBound hB)

lemma natAbs_le_integerCoeffBound {B : ℝ} {z : ℤ}
    (hB : Real.exp 1 ≤ B) (hz : |(z : ℝ)| ≤ B) :
    z.natAbs ≤ integerCoeffBound B := by
  have hreal : (z.natAbs : ℝ) ≤ (integerCoeffBound B : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      abs_int_cast_le_integerCoeffBound hB hz
  exact_mod_cast hreal

/-- A fixed old height can be absorbed into a positive constant times the
logarithm of any prime.  The explicit constant is convenient for later
quantitative bookkeeping. -/
lemma log_max_le_fixed_mul_log (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃p : ℕ⦄, p.Prime →
      Real.log (max A (p : ℝ)) ≤ C * Real.log (p : ℝ) := by
  let ltwo : ℝ := Real.log 2
  let C : ℝ := 1 + Real.log A / ltwo
  have hltwo : 0 < ltwo := Real.log_pos (by norm_num)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpPos : 0 < (p : ℝ) := lt_of_lt_of_le (by norm_num) hpTwo
  have hlogp : ltwo ≤ Real.log (p : ℝ) := by
    dsimp [ltwo]
    exact Real.log_le_log (by norm_num) hpTwo
  have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (le_trans (by norm_num) hpTwo)
  by_cases hAp : A ≤ (p : ℝ)
  · rw [max_eq_right hAp]
    have hOneC : 1 ≤ C := by
      dsimp [C]
      exact le_add_of_nonneg_right (div_nonneg hlogA hltwo.le)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hOneC hlogp0
  · have hpA : (p : ℝ) ≤ A := le_of_not_ge hAp
    rw [max_eq_left hpA]
    have hratio : Real.log A ≤
        (Real.log A / ltwo) * Real.log (p : ℝ) := by
      calc
        Real.log A = (Real.log A / ltwo) * ltwo := by
          field_simp
        _ ≤ (Real.log A / ltwo) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_left hlogp (div_nonneg hlogA hltwo.le)
    dsimp [C]
    nlinarith

/-- A single positive constant absorbs all the fixed old-prime heights in a
finite indexed family, uniformly in the distinguished prime `p`. -/
lemma exists_log_max_old_prime_le_mul_log {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (ha : ∀ i, (a i).Prime) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : ι) ⦃p : ℕ⦄, p.Prime →
      Real.log (max (a i : ℝ) (p : ℝ)) ≤ C * Real.log (p : ℝ) := by
  classical
  let A : ℕ := max 1 (Finset.univ.sup a)
  have hA : (1 : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast Nat.le_max_left 1 (Finset.univ.sup a)
  obtain ⟨C, hC, hbound⟩ := log_max_le_fixed_mul_log (A : ℝ) hA
  refine ⟨C, hC, ?_⟩
  intro i p hp
  have haiA_nat : a i ≤ A := by
    exact (Finset.le_sup (f := a) (Finset.mem_univ i)).trans
      (Nat.le_max_right 1 (Finset.univ.sup a))
  have haiA : (a i : ℝ) ≤ (A : ℝ) := by exact_mod_cast haiA_nat
  have hleftPos : 0 < max (a i : ℝ) (p : ℝ) := by
    have hipos : 0 < (a i : ℝ) := by exact_mod_cast (ha i).pos
    exact hipos.trans_le (le_max_left _ _)
  exact (Real.log_le_log hleftPos (max_le_max haiA le_rfl)).trans (hbound hp)

/-- The finite indexed rational logarithmic form used by the uniform family
theorem below. -/
noncomputable def indexedRationalLogForm {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (p : ℕ) (c : ι → ℤ) (d : ℤ) : ℝ :=
  ∑ i, (c i : ℝ) * Real.log (a i : ℝ) +
    (d : ℝ) * Real.log (p : ℝ)

/-- A family-form interface for the one-varying-prime rational
Baker--Wüstholz estimate.  Unlike `HasRationalBakerWustholzBounds`, it is
independent of `FiniteStage`; the theorem below proves that it specializes to
that project-facing interface. -/
def HasUniformRationalPrimeLogBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℕ),
    (∀ i, (a i).Prime) → Function.Injective a →
    ∃ K : ℝ, 0 < K ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (B : ℝ),
        p.Prime → (∀ i, a i ≠ p) → Real.exp 1 ≤ B →
        (∀ i, |(c i : ℝ)| ≤ B) → |(d : ℝ)| ≤ B →
        d ≠ 0 →
        indexedRationalLogForm a p c d ≠ 0 →
        Real.exp (-K * Real.log (p : ℝ) * Real.log B) ≤
          |indexedRationalLogForm a p c d|

/-- Enumerating a finite stage by its subtype turns a uniform indexed-family
bound into the exact interface consumed by the Erdős 240 development. -/
theorem HasUniformRationalPrimeLogBounds.toFiniteStageBounds
    (h : HasUniformRationalPrimeLogBounds) :
    HasRationalBakerWustholzBounds := by
  classical
  intro s
  let ι := {q : ℕ // q ∈ s.carrier}
  let a : ι → ℕ := fun q => q.1
  have haPrime : ∀ i, (a i).Prime := fun i => s.prime_mem i.2
  have haInj : Function.Injective a := fun i j hij => Subtype.ext hij
  obtain ⟨K, hK, hbound⟩ := h ι a haPrime haInj
  refine ⟨K, hK, ?_⟩
  intro p c d B hp hpFresh hB hc hd hdne hne
  let ci : ι → ℤ := fun q => c q.1
  have hpDistinct : ∀ i, a i ≠ p := by
    intro i hip
    apply hpFresh
    rw [← hip]
    exact i.2
  have hci : ∀ i, |(ci i : ℝ)| ≤ B := by
    intro i
    exact hc i.1 i.2
  have hform : indexedRationalLogForm a p ci d =
      rationalLogForm s p c d := by
    simp only [indexedRationalLogForm, rationalLogForm, ci, a]
    congr 1
    symm
    exact Finset.sum_subtype s.carrier (fun q => Iff.rfl)
      (fun q => (c q : ℝ) * Real.log (q : ℝ))
  have hindexed : indexedRationalLogForm a p ci d ≠ 0 := by
    simpa only [hform] using hne
  simpa only [hform] using
    hbound ci d B hp hpDistinct hB hci hd hdne hindexed

/-! ## Bridge from the source-independent rational-prime theorem -/

/-- The audited source-independent family theorem has exactly the
distinguished-last-coefficient hypothesis needed by the finite-stage
development.  Enumerating the stage by its carrier subtype therefore gives
the main file's Baker--Wüstholz interface without any loss of strength. -/
theorem hasRationalBakerWustholzBounds_of_uniform
    (h : RationalPrimeBaker.HasUniformRationalPrimeLogBounds.{0}) :
    HasRationalBakerWustholzBounds := by
  intro s
  obtain ⟨K, hK, hbound⟩ :=
    RationalPrimeBaker.finset_bounds_of_uniform h s.carrier
      (fun _q hq ↦ s.prime_mem hq)
  refine ⟨K, hK, ?_⟩
  intro p c d B hp hpFresh hB hc hd hdne hform
  simpa only [RationalPrimeBaker.finsetRationalLogForm,
    rationalLogForm] using
      hbound c d B hp hpFresh hB hc hd hdne hform

/-- Once the uniform rational-prime logarithmic estimate is available, all
remaining steps of the resolution of Erdős 240 are the checked finite-stage
counting and limiting argument in the main module. -/
theorem problem240_of_uniformRationalPrimeLogBounds
    (h : RationalPrimeBaker.HasUniformRationalPrimeLogBounds.{0}) :
    Problem240 :=
  problem240_of_tijdemanSquareLogBounds
    (HasRationalBakerWustholzBounds.toSquareLogBounds
      (hasRationalBakerWustholzBounds_of_uniform h))

#print axioms hasRationalBakerWustholzBounds_of_uniform
#print axioms problem240_of_uniformRationalPrimeLogBounds

end BakerSpecialization
end Erdos240
