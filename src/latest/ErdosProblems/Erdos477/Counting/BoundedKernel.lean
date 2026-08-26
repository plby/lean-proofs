/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A bounded integer annihilator, using a row-space basis and Mathlib's proved Siegel lemma.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.DeterminantKernel

namespace Erdos477.Counting

open scoped BigOperators

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The bound depends only on the number of columns and the entry bound,
not on the number of rows. -/
theorem exists_bounded_integer_kernel {ι : Type*} [Finite ι] (m : ℕ) (hm : 0 < m)
    (V : ι → Fin m → ℤ) (A : ℝ) (hA : 1 ≤ A)
    (hentry : ∀ i j, |(V i j : ℝ)| ≤ A)
    (hdet : ∀ f : Fin m → ι, (Matrix.of fun i j => V (f i) j).det = 0) :
    ∃ v : Fin m → ℤ, (∃ j, v j ≠ 0) ∧
      (∀ i, ∑ j, v j * V i j = 0) ∧ ∀ j, |(v j : ℝ)| ≤ ((m : ℝ) * A) ^ m := by
  classical
  let Vq : ι → Fin m → ℚ := fun i j => (V i j : ℚ)
  let W := Submodule.span ℚ (Set.range Vq)
  have hdetq (f : Fin m → ι) : (Matrix.of fun i j => Vq (f i) j).det = 0 := by
    have h := (Int.castRingHom ℚ).map_det (Matrix.of fun i j => V (f i) j)
    rw [hdet f, map_zero] at h
    exact h.symm
  have hW : W ≠ ⊤ := span_ne_top_of_det_eq_zero Vq hdetq
  let r := Module.finrank ℚ W
  have hrm : r < m := by
    have h := Submodule.finrank_lt hW
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : 1 ≤ (m : ℝ) * A := one_le_mul_of_one_le_of_one_le hmR hA
  by_cases hr : r = 0
  · have hWbot : W = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hVzero (i) : Vq i = 0 := by
      have hmem := Submodule.subset_span (R := ℚ)
        (Set.mem_range_self i : Vq i ∈ Set.range Vq)
      rw [show Submodule.span ℚ (Set.range Vq) = ⊥ from hWbot] at hmem
      exact hmem
    refine ⟨fun _ => 1, ⟨⟨0, hm⟩, one_ne_zero⟩, ?_, ?_⟩
    · intro i
      apply Finset.sum_eq_zero
      intro j _
      have hq : (V i j : ℚ) = 0 := congrFun (hVzero i) j
      have hz : V i j = 0 := by exact_mod_cast hq
      simp [hz]
    · intro j
      simpa only [Int.cast_one, abs_one] using one_le_pow₀ hbase
  have hr0 : 0 < r := Nat.pos_of_ne_zero hr
  obtain ⟨f, hf, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range Vq)
  choose row hrow using hf
  have hsp : Submodule.span ℚ (Set.range (fun i : Fin r => Vq (row i))) = W := by
    have hfun : (fun i : Fin r => Vq (row i)) = f := funext hrow
    rw [hfun]
    exact hspan
  let M : Matrix (Fin r) (Fin m) ℤ := Matrix.of fun i j => V (row i) j
  obtain ⟨v, hv, hMv, hnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le M
    (by simpa only [Fintype.card_fin] using hrm) (by simpa only [Fintype.card_fin] using hr0)
  have hMnorm : ‖M‖ ≤ A := (Matrix.norm_le_iff (by linarith : 0 ≤ A)).mpr (by
    intro i j
    simpa only [M, Matrix.of_apply, Int.norm_eq_abs] using hentry (row i) j)
  have hmax : max 1 ‖M‖ ≤ A := max_le hA hMnorm
  have hexp0 : 0 ≤ (r : ℝ) / ((m : ℝ) - r) := by
    have hmr : (r : ℝ) < m := by exact_mod_cast hrm
    positivity
  have hexp : (r : ℝ) / ((m : ℝ) - r) ≤ m := by
    have hden : (1 : ℝ) ≤ (m : ℝ) - r := by
      have h : (r : ℝ) + 1 ≤ m := by exact_mod_cast hrm
      linarith
    apply (div_le_iff₀ (by linarith : 0 < (m : ℝ) - r)).mpr
    have hmul := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith [show (r : ℝ) ≤ m by exact_mod_cast hrm.le]
  have hnorm' : ‖v‖ ≤ ((m : ℝ) * A) ^ m := by
    simp only [Fintype.card_fin] at hnorm
    calc
      ‖v‖ ≤ ((m : ℝ) * max 1 ‖M‖) ^ ((r : ℝ) / ((m : ℝ) - r)) := hnorm
      _ ≤ ((m : ℝ) * A) ^ ((r : ℝ) / ((m : ℝ) - r)) :=
        Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)) hexp0
      _ ≤ ((m : ℝ) * A) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ = _ := Real.rpow_natCast _ _
  let L : (Fin m → ℚ) →ₗ[ℚ] ℚ := ∑ j, (v j : ℚ) • LinearMap.proj j
  have hL (w : Fin m → ℚ) : L w = ∑ j, (v j : ℚ) * w j := by simp [L]
  have hker : W ≤ LinearMap.ker L := by
    rw [← hsp]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change L (Vq (row i)) = 0
    rw [hL]
    have h := congrFun hMv i
    change ∑ j, V (row i) j * v j = 0 at h
    have hq : (∑ j, (V (row i) j : ℚ) * (v j : ℚ)) = 0 := by exact_mod_cast h
    simpa only [Vq, mul_comm] using hq
  refine ⟨v, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact hv (funext h)
  · intro i
    have h := hker (Submodule.subset_span (Set.mem_range_self i))
    rw [LinearMap.mem_ker, hL] at h
    dsimp only [Vq] at h
    exact_mod_cast h
  · intro j
    have h := (norm_le_pi_norm v j).trans hnorm'
    simpa only [Int.norm_eq_abs] using h

#print axioms exists_bounded_integer_kernel
-- 'Erdos477.Counting.exists_bounded_integer_kernel' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
