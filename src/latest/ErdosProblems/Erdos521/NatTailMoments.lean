/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite tail sums bound moments of a bounded natural-valued random variable.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RootStatistics

namespace Erdos521

open MeasureTheory
open scoped BigOperators

def natTailTerm {Ω : Type*} (X : Ω → ℕ) (k : ℕ) (A : ℝ) (ω : Ω) : ℝ :=
  if k ≤ X ω then A else 0

theorem natTailTerm_eq_indicator {Ω : Type*} (X : Ω → ℕ) (k : ℕ) (A : ℝ) :
    natTailTerm X k A = {ω | k ≤ X ω}.indicator (fun _ ↦ A) := by
  funext ω
  simp only [natTailTerm, Set.indicator_apply, Set.mem_ofPred_eq]

theorem natTailTerm_nonneg {Ω : Type*} (X : Ω → ℕ) (k : ℕ) {A : ℝ}
    (hA : 0 ≤ A) (ω : Ω) : 0 ≤ natTailTerm X k A ω := by
  unfold natTailTerm
  split_ifs <;> positivity

theorem natTailTerm_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X : Ω → ℕ} (hX : AEMeasurable X μ) (k : ℕ) (A : ℝ) :
    Integrable (natTailTerm X k A) μ := by
  have hE : NullMeasurableSet {ω | k ≤ X ω} μ :=
    hX.nullMeasurableSet_preimage measurableSet_Ici
  rw [natTailTerm_eq_indicator]
  exact (integrable_const A).indicator₀ hE

theorem integral_natTailTerm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℕ} (hX : AEMeasurable X μ) (k : ℕ) (A : ℝ) :
    (∫ ω, natTailTerm X k A ω ∂μ) = A * μ.real {ω | k ≤ X ω} := by
  have hE : NullMeasurableSet {ω | k ≤ X ω} μ :=
    hX.nullMeasurableSet_preimage measurableSet_Ici
  simp_rw [natTailTerm_eq_indicator]
  rw [integral_indicator₀ hE, setIntegral_const, smul_eq_mul, mul_comm]

theorem bounded_nat_pow_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X : Ω → ℕ} (hX : AEMeasurable X μ) (n p : ℕ)
    (hbound : ∀ ω, X ω ≤ n) : Integrable (fun ω ↦ (X ω : ℝ) ^ p) μ := by
  apply Integrable.mono' (integrable_const ((n : ℝ) ^ p))
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ) ^ p)).comp_aemeasurable hX).aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Function.comp_apply, Real.norm_of_nonneg (by positivity : 0 ≤ (X ω : ℝ) ^ p)] using
    pow_le_pow_left₀ (Nat.cast_nonneg (X ω)) (Nat.cast_le.mpr (hbound ω) : (X ω : ℝ) ≤ n) p

theorem nat_pow_le_tail_sum (n m J p : ℕ) (hm : m ≤ n) :
    (m : ℝ) ^ p ≤ 16 ^ p +
      (∑ j ∈ Finset.Ico 8 J, natTailTerm (fun _ : Unit ↦ m) (2 * j) ((2 * ((j : ℝ) + 1)) ^ p) ()) +
      natTailTerm (fun _ : Unit ↦ m) (2 * J) ((n : ℝ) ^ p) () := by
  have hsum : 0 ≤ ∑ j ∈ Finset.Ico 8 J,
      natTailTerm (fun _ : Unit ↦ m) (2 * j) ((2 * ((j : ℝ) + 1)) ^ p) () := by
    apply Finset.sum_nonneg
    intro j _
    exact natTailTerm_nonneg _ _ (by positivity) _
  have hlast := natTailTerm_nonneg (fun _ : Unit ↦ m) (2 * J) (by positivity : 0 ≤ (n : ℝ) ^ p) ()
  by_cases hsmall : m < 16
  · have hpow := pow_le_pow_left₀ (Nat.cast_nonneg m)
      (by exact_mod_cast hsmall.le : (m : ℝ) ≤ 16) p
    linarith
  by_cases htail : 2 * J ≤ m
  · have hpow := pow_le_pow_left₀ (Nat.cast_nonneg m) (Nat.cast_le.mpr hm : (m : ℝ) ≤ n) p
    rw [show natTailTerm (fun _ : Unit ↦ m) (2 * J) ((n : ℝ) ^ p) () = (n : ℝ) ^ p by
      simp only [natTailTerm, htail, if_true]]
    have : (0 : ℝ) ≤ 16 ^ p := by positivity
    linarith
  · have hk : m / 2 ∈ Finset.Ico 8 J := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hsingle := Finset.single_le_sum (fun j (_ : j ∈ Finset.Ico 8 J) ↦
      natTailTerm_nonneg (fun _ : Unit ↦ m) (2 * j) (by positivity : 0 ≤ (2 * ((j : ℝ) + 1)) ^ p) ()) hk
    have hkm : 2 * (m / 2) ≤ m := by omega
    have hmR : (m : ℝ) ≤ 2 * ((m / 2 : ℕ) + 1) := by
      exact_mod_cast (show m ≤ 2 * (m / 2 + 1) by omega)
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg m) hmR p
    rw [show natTailTerm (fun _ : Unit ↦ m) (2 * (m / 2)) ((2 * ((m / 2 : ℕ) + 1)) ^ p) () =
        (2 * ((m / 2 : ℕ) + 1 : ℝ)) ^ p by simp only [natTailTerm, hkm, if_true]] at hsingle
    have : (0 : ℝ) ≤ 16 ^ p := by positivity
    linarith

end Erdos521
