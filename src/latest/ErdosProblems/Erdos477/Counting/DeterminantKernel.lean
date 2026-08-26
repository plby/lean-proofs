/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
From vanishing evaluation determinants to nonzero annihilating coefficients.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.Determinant

namespace Erdos477.Counting

open scoped BigOperators

variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Finite κ] [Field K]

lemma span_ne_top_of_det_eq_zero (V : κ → ι → K)
    (hdet : ∀ f : ι → κ, (Matrix.of fun i j => V (f i) j).det = 0) :
    Submodule.span K (Set.range V) ≠ ⊤ := by
  classical
  let := Fintype.ofFinite κ
  intro hspan
  have hrep (i : ι) : ∃ c : κ → K, ∑ k, c k • V k = Pi.single i 1 := by
    apply (Submodule.mem_span_range_iff_exists_fun K).mp
    rw [hspan]
    trivial
  choose c hc using hrep
  have hid : (Matrix.of fun i j => ∑ k, c i k * V k j) = (1 : Matrix ι ι K) := by
    ext i j
    have h := congrFun (hc i) j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Matrix.of_apply, Matrix.one_apply, eq_comm] using h
  have hzero : (Matrix.of fun i j => ∑ k, c i k * V k j).det = 0 := by
    rw [det_row_sum]
    apply Finset.sum_eq_zero
    intro f _
    have hmul := Matrix.det_mul_column (fun i => c i (f i))
      (Matrix.of fun i j => V (f i) j)
    simpa only [Matrix.of_apply, hdet f, mul_zero] using hmul
  rw [hid, Matrix.det_one] at hzero
  exact one_ne_zero hzero

/-- A finite family whose square evaluation determinants all vanish admits
a nonzero linear relation valid on every member of the family. -/
theorem exists_kernel_of_det_eq_zero (V : κ → ι → K)
    (hdet : ∀ f : ι → κ, (Matrix.of fun i j => V (f i) j).det = 0) :
    ∃ v : ι → K, (∃ i, v i ≠ 0) ∧ ∀ k, ∑ i, v i * V k i = 0 := by
  classical
  obtain ⟨f, hf, hker⟩ := (Submodule.span K (Set.range V)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr (span_ne_top_of_det_eq_zero V hdet))
  let v : ι → K := fun i => f (Pi.single i 1)
  have hformula (x : ι → K) : f x = ∑ i, v i * x i := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have heq : Pi.single i (x i) = x i • Pi.single i (1 : K) := by
      ext j
      simp [Pi.single_apply]
    rw [heq, map_smul]
    exact mul_comm _ _
  refine ⟨v, ?_, ?_⟩
  · by_contra h
    push Not at h
    apply hf
    ext x
    simp [hformula, h]
  · intro k
    rw [← hformula]
    exact hker (Submodule.subset_span (Set.mem_range_self k))

/-- Clear a common denominator to obtain an integral annihilator. -/
theorem exists_integer_kernel_of_det_eq_zero (V : κ → ι → ℤ)
    (hdet : ∀ f : ι → κ, (Matrix.of fun i j => V (f i) j).det = 0) :
    ∃ v : ι → ℤ, (∃ i, v i ≠ 0) ∧ ∀ k, ∑ i, v i * V k i = 0 := by
  classical
  have hrat (f : ι → κ) : (Matrix.of fun i j => (V (f i) j : ℚ)).det = 0 := by
    have hmap := (Int.castRingHom ℚ).map_det (Matrix.of fun i j => V (f i) j)
    rw [hdet f, map_zero] at hmap
    exact hmap.symm
  obtain ⟨v, ⟨i, hi⟩, hv⟩ := exists_kernel_of_det_eq_zero
    (fun k j => (V k j : ℚ)) hrat
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) v
  choose w hw using hb
  have hw' (j : ι) : (w j : ℚ) = (b : ℤ) * v j := by
    simpa [Algebra.smul_def] using hw j
  have hb0 : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hbq : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
  refine ⟨w, ⟨i, ?_⟩, ?_⟩
  · intro hwi
    have h := hw' i
    rw [hwi, Int.cast_zero] at h
    exact (mul_ne_zero hbq hi) h.symm
  · intro k
    have hq : ((∑ j, w j * V k j : ℤ) : ℚ) = 0 := by
      push_cast
      simp_rw [hw', mul_assoc]
      rw [← Finset.mul_sum, hv k, mul_zero]
    exact_mod_cast hq

#print axioms exists_kernel_of_det_eq_zero
-- 'Erdos477.Counting.exists_kernel_of_det_eq_zero' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

#print axioms exists_integer_kernel_of_det_eq_zero
-- 'Erdos477.Counting.exists_integer_kernel_of_det_eq_zero' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
