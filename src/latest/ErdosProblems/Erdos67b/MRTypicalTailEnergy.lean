import ErdosProblems.Erdos67b.MRAuxiliaryMissingEnergy

/-!
# Exact energy comparison after adjoining a family of typicality blocks

Nested typical supports make the difference coefficient either the original
coefficient or zero. Its support lies in the actual missing-tail set.
-/

open scoped BigOperators Interval
open MeasureTheory

namespace Erdos67b

noncomputable section

theorem mem_typicalFactorizationSet_union
    (blocks extra : Finset (ℕ × ℕ)) (Z n : ℕ) :
    n ∈ typicalFactorizationSet (blocks ∪ extra) Z ↔
      n ∈ typicalFactorizationSet blocks Z ∧ HasTypicalFactorization extra n := by
  classical
  simp only [mem_typicalFactorizationSet, HasTypicalFactorization, Finset.forall_mem_union]
  tauto

def mrTypicalTailCoefficient
    (blocks extra : Finset (ℕ × ℕ)) (Z : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (mrTypicalValueCoefficient blocks Z f n -
    mrTypicalValueCoefficient (blocks ∪ extra) Z f n) / (n : ℂ)

open Classical in
theorem mrTypicalTailCoefficient_eq
    (blocks extra : Finset (ℕ × ℕ)) (Z : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    mrTypicalTailCoefficient blocks extra Z f n =
      if n ∈ typicalFactorizationSet blocks Z ∧ ¬HasTypicalFactorization extra n
      then f n / (n : ℂ) else 0 := by
  unfold mrTypicalTailCoefficient mrTypicalValueCoefficient
  simp only [mem_typicalFactorizationSet_union]
  by_cases htyp : n ∈ typicalFactorizationSet blocks Z <;>
    by_cases htail : HasTypicalFactorization extra n <;> simp [htyp, htail]

def mrTypicalTailPolynomial
    (blocks extra : Finset (ℕ × ℕ)) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
    (mrTypicalTailCoefficient blocks extra (2 * X) f) t

theorem mrTypicalDyadicPolynomial_eq_union_add_tail
    (blocks extra : Finset (ℕ × ℕ)) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) :
    mrTypicalDyadicPolynomial blocks f X t =
      mrTypicalDyadicPolynomial (blocks ∪ extra) f X t +
        mrTypicalTailPolynomial blocks extra f X t := by
  unfold mrTypicalDyadicPolynomial mrTypicalTailPolynomial logarithmicDirichletPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  unfold mrTypicalTailCoefficient
  ring

theorem mrTypicalTailCoefficient_eq_zero_of_not_mem
    {blocks : Finset (ℕ × ℕ)} {extra : Finset (ℕ × ℕ)} {Z n : ℕ} (f : ℕ → ℂ)
    (hn : n ∉ atypicalFactorizationSet extra Z) :
    mrTypicalTailCoefficient blocks extra Z f n = 0 := by
  classical
  rw [mrTypicalTailCoefficient_eq]
  split_ifs with h
  · have htyp := mem_typicalFactorizationSet.mp h.1
    exact False.elim (hn (mem_atypicalFactorizationSet.mpr ⟨htyp.1, htyp.2.1, h.2⟩))
  · rfl

theorem norm_mrTypicalTailCoefficient_le
    {blocks : Finset (ℕ × ℕ)} {extra : Finset (ℕ × ℕ)} {Z : ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖mrTypicalTailCoefficient blocks extra Z f n‖ ≤ (n : ℝ)⁻¹ := by
  classical
  rw [mrTypicalTailCoefficient_eq]
  split_ifs
  · rw [norm_div, Complex.norm_natCast]
    simpa only [one_div] using
      div_le_div_of_nonneg_right (hbound n hn) (Nat.cast_nonneg n)
  · simp

theorem sum_normSq_mrTypicalTailCoefficient_le
    (blocks : Finset (ℕ × ℕ)) (extra : Finset (ℕ × ℕ)) {X : ℕ} (hX : 0 < X)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc X (2 * X),
      Complex.normSq (mrTypicalTailCoefficient blocks extra (2 * X) f n)) ≤
        (atypicalFactorizationSet extra (2 * X)).card / (X : ℝ) ^ 2 := by
  classical
  let S := (Finset.Ioc X (2 * X)).filter (fun n ↦ n ∈ atypicalFactorizationSet extra (2 * X))
  have hsubset : S ⊆ atypicalFactorizationSet extra (2 * X) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have heq : (∑ n ∈ Finset.Ioc X (2 * X),
      Complex.normSq (mrTypicalTailCoefficient blocks extra (2 * X) f n)) =
      ∑ n ∈ S, Complex.normSq (mrTypicalTailCoefficient blocks extra (2 * X) f n) := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hm : n ∈ atypicalFactorizationSet extra (2 * X)
    · simp only [hm, ↓reduceIte]
    · rw [if_neg hm, mrTypicalTailCoefficient_eq_zero_of_not_mem f hm]
      simp
  rw [heq]
  calc
    _ ≤ ∑ _n ∈ S, (X : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnX := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
      have hh := norm_mrTypicalTailCoefficient_le (blocks := blocks) (extra := extra)
        (Z := 2 * X) hbound (hX.trans hnX)
      have hinv : (n : ℝ)⁻¹ ≤ (X : ℝ)⁻¹ :=
        inv_anti₀ (by exact_mod_cast hX) (by exact_mod_cast hnX.le)
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hh.trans hinv) 2
    _ = (S.card : ℝ) * (X : ℝ)⁻¹ ^ 2 := by simp
    _ ≤ (atypicalFactorizationSet extra (2 * X)).card * (X : ℝ)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsubset) (sq_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, inv_pow]

theorem intervalIntegral_mrTypicalTailPolynomial_le
    (blocks : Finset (ℕ × ℕ)) (extra : Finset (ℕ × ℕ)) {X : ℕ} (hX : 0 < X)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖mrTypicalTailPolynomial blocks extra f X t‖ ^ 2) ≤
      (2 * T + 4 * Real.pi * X) *
        (atypicalFactorizationSet extra (2 * X)).card / (X : ℝ) ^ 2 := by
  have hmass := sum_normSq_mrTypicalTailCoefficient_le blocks extra hX hbound
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le_support
    (show 0 < 2 * X by omega)
    (fun n hn ↦ hX.trans (Finset.mem_Ioc.mp hn).1)
    (fun n hn ↦ (Finset.mem_Ioc.mp hn).2)
    (mrTypicalTailCoefficient blocks extra (2 * X) f) hT
  unfold mrTypicalTailPolynomial
  calc
    _ = ‖∫ t in -T..T,
        star (logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
          (mrTypicalTailCoefficient blocks extra (2 * X) f) t) *
        logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
          (mrTypicalTailCoefficient blocks extra (2 * X) f) t‖ :=
      intervalIntegral_norm_sq_eq_norm_conj_mul_self _ hT
    _ ≤ (2 * T + 2 * Real.pi * (2 * X : ℕ)) *
        ∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq (mrTypicalTailCoefficient blocks extra (2 * X) f n) := hmean
    _ ≤ (2 * T + 2 * Real.pi * (2 * X : ℕ)) *
        ((atypicalFactorizationSet extra (2 * X)).card / (X : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by push_cast; ring

theorem intervalIntegral_mrTypicalDyadicPolynomial_le_union_add_tail
    (blocks extra : Finset (ℕ × ℕ)) (f : ℕ → ℂ) (X : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) ≤
      2 * (∫ t in -T..T, ‖mrTypicalDyadicPolynomial (blocks ∪ extra) f X t‖ ^ 2) +
      2 * (∫ t in -T..T, ‖mrTypicalTailPolynomial blocks extra f X t‖ ^ 2) := by
  let A := mrTypicalDyadicPolynomial (blocks ∪ extra) f X
  let B := mrTypicalTailPolynomial blocks extra f X
  have hA : Continuous A := continuous_logarithmicDirichletPolynomial _ _
  have hB : Continuous B := continuous_logarithmicDirichletPolynomial _ _
  have hF : Continuous (mrTypicalDyadicPolynomial blocks f X) :=
    continuous_logarithmicDirichletPolynomial _ _
  calc
    _ ≤ ∫ t in -T..T, (2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hF.norm.pow 2).intervalIntegrable _ _)
        ((((hA.norm.pow 2).const_mul 2).add
          ((hB.norm.pow 2).const_mul 2)).intervalIntegrable _ _)
      intro t ht
      change ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2 ≤ 2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2
      rw [mrTypicalDyadicPolynomial_eq_union_add_tail]
      simpa only [Complex.normSq_eq_norm_sq] using normSq_add_le_two_mul (A t) (B t)
    _ = _ := by
      have hadd : (∫ t in -T..T, (2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2)) =
          (∫ t in -T..T, 2 * ‖A t‖ ^ 2) + ∫ t in -T..T, 2 * ‖B t‖ ^ 2 :=
        intervalIntegral.integral_add
          (((hA.norm.pow 2).const_mul 2).intervalIntegrable _ _)
          (((hB.norm.pow 2).const_mul 2).intervalIntegrable _ _)
      rw [hadd,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end

end Erdos67b
