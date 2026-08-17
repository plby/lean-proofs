/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos900.AdaptiveDFS
import ErdosProblems.Erdos636.AugmentationGraphPartial

/-!
# Fixed-slice probability for the adaptive DFS exposure

This file connects the deterministic DFS certificate to the existing
bounded-difference inequality for a uniform Boolean slice.  No independence
claim is made about the adaptive answers: the weight-preserving equivalence
of `AdaptiveTree.lean` transports the uniform slice exactly.
-/

open scoped BigOperators

noncomputable section

namespace Erdos900

open Erdos88.Concentration
open Erdos88.Fourier

/-- A fixed-cardinality Boolean slice is nonempty whenever its requested
weight is at most the number of coordinates. -/
def boolSliceNonempty {I : Type*} [Fintype I] [DecidableEq I]
    {m : ℕ} (hm : m ≤ Fintype.card I) : Nonempty (BoolSlice I m) := by
  classical
  obtain ⟨S, _hS, hcard⟩ := Finset.exists_subset_card_eq
    (show m ≤ (Finset.univ : Finset I).card by simpa using hm)
  refine ⟨⟨fun i ↦ decide (i ∈ S), ?_⟩⟩
  simpa [Erdos88.Fourier.boolWeight] using hcard

/-- Coefficients selecting the first `q` coordinates. -/
def prefixCoefficients {r : ℕ} (q : ℕ) : Fin r → ℝ :=
  fun i ↦ if i.val < q then 1 else 0

/-- The slice linear statistic with prefix coefficients is the real cast of
`prefixWeight`. -/
theorem sliceSum_prefixCoefficients {r m q : ℕ} (omega : BoolSlice (Fin r) m) :
    Erdos636.AugmentationGraphPartial.sliceSum m (prefixCoefficients q) omega =
      (prefixWeight omega.1 q : ℝ) := by
  classical
  calc
    Erdos636.AugmentationGraphPartial.sliceSum m
        (prefixCoefficients q) omega =
        ∑ i, if omega.1 i then prefixCoefficients q i else 0 := by
      simp only [Erdos636.AugmentationGraphPartial.sliceSum,
        Erdos636.SlicePersistence.sampleFinset]
      conv_rhs => rw [← Finset.sum_filter]
      congr 1
    _ = ∑ i, if i.val < q then (if omega.1 i then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiq : i.val < q <;> by_cases hb : omega.1 i <;>
        simp [prefixCoefficients, hiq, hb]
    _ = (prefixWeight omega.1 q : ℝ) := by
      rw [prefixWeight_eq_sum]
      push_cast
      rfl

theorem prefixWeight_true {r q : ℕ} :
    prefixWeight (fun _ : Fin r ↦ true) q = min q r := by
  induction r generalizing q with
  | zero => simp [prefixWeight]
  | succ r ih =>
      cases q with
      | zero => simp [prefixWeight]
      | succ q =>
          simp only [prefixWeight, if_true]
          rw [show Fin.tail (fun _ : Fin (r + 1) ↦ true) =
            (fun _ : Fin r ↦ true) by rfl, ih]
          omega

theorem sum_prefixCoefficients {r q : ℕ} :
    (∑ i : Fin r, prefixCoefficients q i) = ((min q r : ℕ) : ℝ) := by
  have h := prefixWeight_eq_sum (fun _ : Fin r ↦ true) q
  rw [prefixWeight_true] at h
  simp only [if_true] at h
  change (∑ i : Fin r, if i.val < q then (1 : ℝ) else 0) = _
  exact_mod_cast h.symm

/-- Complementation for the normalized counting probability. -/
theorem uniformProbability_not {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) :
    uniformProbability (fun omega ↦ ¬P omega) =
      1 - uniformProbability P := by
  classical
  simp only [uniformProbability]
  have hcard : (Finset.univ.filter fun omega : Ω ↦ ¬P omega).card +
      (Finset.univ.filter P).card = Fintype.card Ω := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext omega
      by_cases h : P omega <;> simp [h]
    · rw [Finset.disjoint_left]
      intro omega hnot hyes
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot hyes
      exact hnot hyes
  have hcardPos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hcardReal :
      ((Finset.univ.filter fun omega : Ω ↦ ¬P omega).card : ℝ) +
        (Finset.univ.filter P).card = Fintype.card Ω := by
    exact_mod_cast hcard
  apply (div_eq_iff hcardPos.ne').2
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hcardPos.ne']
  apply eq_sub_iff_add_eq.mpr
  convert hcardReal using 1
  congr 1
  all_goals
    norm_cast
    apply congrArg Finset.card
    ext omega
    simp

/-- The exact expectation of the adaptive prefix count in the uniform
`m`-edge slice. -/
theorem adaptivePrefix_expectation {n m q : ℕ}
    (hm : m ≤ n.choose 2) (hmpos : 0 < m)
    [Nonempty (BoolSlice (Fin (n.choose 2)) m)] :
    uniformExpectation (fun omega : BoolSlice (Fin (n.choose 2)) m ↦
      (prefixWeight
        (AdaptiveTree.answerEquiv (canonicalDFSTree n) omega.1) q : ℝ)) =
      (m : ℝ) / (n.choose 2 : ℝ) * (min q (n.choose 2) : ℕ) := by
  letI : Nonempty (Fin (n.choose 2)) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le hmpos hm)
  let E := (canonicalDFSTree n).sliceEquiv m
  let a : Fin (n.choose 2) → ℝ := prefixCoefficients q
  calc
    uniformExpectation (fun omega : BoolSlice (Fin (n.choose 2)) m ↦
        (prefixWeight
          (AdaptiveTree.answerEquiv (canonicalDFSTree n) omega.1) q : ℝ)) =
        uniformExpectation (fun omega : BoolSlice (Fin (n.choose 2)) m ↦
          Erdos636.AugmentationGraphPartial.sliceSum m a (E omega)) := by
            apply congrArg uniformExpectation
            funext omega
            rw [sliceSum_prefixCoefficients]
            rfl
    _ = uniformExpectation (fun omega : BoolSlice (Fin (n.choose 2)) m ↦
          Erdos636.AugmentationGraphPartial.sliceSum m a omega) := by
            exact Erdos636.SlicePersistence.uniformExpectation_equiv E _
    _ = (m : ℝ) / (n.choose 2 : ℝ) *
          ∑ i : Fin (n.choose 2), a i := by
            simpa using
              (Erdos636.AugmentationGraphPartial.uniformExpectation_sliceSum
                m (by simpa using hm) a)
    _ = (m : ℝ) / (n.choose 2 : ℝ) *
          (min q (n.choose 2) : ℕ) := by
            rw [sum_prefixCoefficients]

/-- Two-sided concentration of the adaptive prefix count.  This is an exact
fixed-slice statement, obtained by transporting through `sliceEquiv`. -/
theorem adaptivePrefix_two_sided_probability {n m q : ℕ}
    (hm : m ≤ n.choose 2) (hmpos : 0 < m) (t : ℝ) (ht : 0 ≤ t)
    [Nonempty (BoolSlice (Fin (n.choose 2)) m)] :
    uniformProbability (fun omega : BoolSlice (Fin (n.choose 2)) m ↦
      t ≤ |(prefixWeight
          (AdaptiveTree.answerEquiv (canonicalDFSTree n) omega.1) q : ℝ) -
        (m : ℝ) / (n.choose 2 : ℝ) * (min q (n.choose 2) : ℕ)|) ≤
      2 * Real.exp (-t ^ 2 / (32 * m)) := by
  letI : Nonempty (Fin (n.choose 2)) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le hmpos hm)
  let E := (canonicalDFSTree n).sliceEquiv m
  let a : Fin (n.choose 2) → ℝ := prefixCoefficients q
  let center : ℝ :=
    (m : ℝ) / (n.choose 2 : ℝ) * ((min q (n.choose 2) : ℕ) : ℝ)
  let P : BoolSlice (Fin (n.choose 2)) m → Prop := fun omega ↦
    t ≤ |Erdos636.AugmentationGraphPartial.sliceSum m a omega - center|
  have hbounded : ∀ i, |a i| ≤ (1 : ℝ) := by
    intro i
    by_cases hi : i.val < q <;> simp [a, prefixCoefficients, hi]
  have hraw : uniformProbability P ≤
      2 * Real.exp (-t ^ 2 / (32 * m)) := by
    have h :=
      Erdos636.AugmentationGraphPartial.boolSlice_sum_two_sided_probability
        m (by simpa using hm) hmpos a 1 t (by norm_num) ht hbounded
    rw [Erdos636.AugmentationGraphPartial.uniformExpectation_sliceSum
        m (by simpa using hm) a] at h
    rw [show (∑ i : Fin (n.choose 2), a i) =
        ((min q (n.choose 2) : ℕ) : ℝ) from sum_prefixCoefficients] at h
    have h' : uniformProbability P ≤
        2 * Real.exp (-t ^ 2 / (2 * (m : ℝ) * (4 : ℝ) ^ 2)) := by
      simpa [P, center] using h
    convert h' using 1 <;> ring
  calc
    uniformProbability (fun omega : BoolSlice (Fin (n.choose 2)) m ↦
        t ≤ |(prefixWeight
            (AdaptiveTree.answerEquiv (canonicalDFSTree n) omega.1) q : ℝ) -
          (m : ℝ) / (n.choose 2 : ℝ) *
            (min q (n.choose 2) : ℕ)|) =
        uniformProbability (fun omega ↦ P (E omega)) := by
          apply congrArg uniformProbability
          funext omega
          simp only [P, E, center]
          rw [sliceSum_prefixCoefficients]
          rw [AdaptiveTree.sliceEquiv_val]
    _ = uniformProbability P :=
      Erdos636.SlicePersistence.uniformProbability_equiv E P
    _ ≤ 2 * Real.exp (-t ^ 2 / (32 * m)) := hraw

end Erdos900
