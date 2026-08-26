/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Measurability and integrability of finite-prefix root statistics for Erdős 521.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.InteriorBounds

namespace Erdos521

open MeasureTheory ProbabilityTheory

noncomputable def encodeSign (x : ℝ) : Bool := if x = 1 then true else false

theorem measurable_encodeSign : Measurable encodeSign := by
  exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const

def extendSigns {n : ℕ} (w : Fin n → Bool) (k : ℕ) : ℝ :=
  if hk : k < n then if w ⟨k, hk⟩ then 1 else -1 else 1

/-- Any statistic of finitely many sign coefficients has a measurable representative,
even when its extension to arbitrary real coefficient sequences is not known measurable. -/
theorem prefixStatistic_aemeasurable {β : Type*} [MeasurableSpace β]
    (n : ℕ) (F : (ℕ → ℝ) → β)
    (hF : ∀ a b, (∀ k < n, a k = b k) → F a = F b) :
    AEMeasurable F sequenceLaw := by
  let encode : (ℕ → ℝ) → Fin n → Bool := fun ε i ↦ encodeSign (ε i)
  have hencode : Measurable encode :=
    measurable_pi_lambda _ fun i ↦ measurable_encodeSign.comp (measurable_pi_apply (i : ℕ))
  have hmeas : Measurable (fun ε ↦ F (extendSigns (encode ε))) :=
    (measurable_of_finite (fun w : Fin n → Bool ↦ F (extendSigns w))).comp hencode
  apply hmeas.aemeasurable.congr
  filter_upwards [ae_sequence_signs] with ε hε
  apply hF
  intro k hk
  rcases hε k with h | h <;> norm_num [extendSigns, encode, encodeSign, hk, h]

theorem polynomial_congr_prefix (a b : ℕ → ℝ) (n : ℕ)
    (hab : ∀ k < n + 1, a k = b k) : polynomial a n = polynomial b n := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [hab k (Finset.mem_range.mp hk)]

theorem realRoots_congr_prefix (a b : ℕ → ℝ) (n : ℕ)
    (hab : ∀ k < n + 1, a k = b k) : realRoots a n = realRoots b n := by
  rw [realRoots, realRoots, polynomial_congr_prefix a b n hab]

theorem rootCount_aemeasurable (n : ℕ) :
    AEMeasurable (fun ε ↦ rootCount ε n) sequenceLaw := by
  apply prefixStatistic_aemeasurable (n + 1)
  intro a b hab
  rw [rootCount, rootCount, realRoots_congr_prefix a b n hab]

theorem interiorRootCount_aemeasurable (n : ℕ) :
    AEMeasurable (fun ε ↦ interiorRootCount ε n) sequenceLaw := by
  apply prefixStatistic_aemeasurable (n + 1)
  intro a b hab
  rw [interiorRootCount, interiorRootCount, realRoots_congr_prefix a b n hab]

theorem smallRootCount_aemeasurable (n : ℕ) (r : ℝ) :
    AEMeasurable (fun ε ↦ smallRootCount ε n r) sequenceLaw := by
  apply prefixStatistic_aemeasurable (n + 1)
  intro a b hab
  rw [smallRootCount, smallRootCount, realRoots_congr_prefix a b n hab]

theorem polynomial_natDegree_le (a : ℕ → ℝ) (n : ℕ) : (polynomial a n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem rootCount_le (a : ℕ → ℝ) (n : ℕ) : rootCount a n ≤ n := by
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans (polynomial_natDegree_le a n))

theorem rootCount_integrable (n : ℕ) :
    Integrable (fun ε ↦ (rootCount ε n : ℝ)) sequenceLaw := by
  apply Integrable.mono' (integrable_const (n : ℝ))
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp_aemeasurable
      (rootCount_aemeasurable n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ε ↦ by
    simpa only [Function.comp_apply, Real.norm_natCast] using (Nat.cast_le.mpr (rootCount_le ε n) :
      (rootCount ε n : ℝ) ≤ n)

theorem interiorRootCount_integrable (n : ℕ) :
    Integrable (fun ε ↦ (interiorRootCount ε n : ℝ)) sequenceLaw := by
  apply Integrable.mono' (rootCount_integrable n)
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp_aemeasurable
      (interiorRootCount_aemeasurable n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ε ↦ by
    simpa only [Function.comp_apply, Real.norm_natCast] using (Nat.cast_le.mpr (interiorRootCount_le ε n) :
      (interiorRootCount ε n : ℝ) ≤ rootCount ε n)

end Erdos521
