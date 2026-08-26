/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCoefficientSquare
import ErdosProblems.Erdos4b.GeneralFourierRawCrtKernel

/-!
# Explicit support ceilings exclude the auxiliary prime

The source profiles have fixed support ceilings on the nonnegative ray.
A nonzero tensor combination therefore has every divisor coordinate
strictly below `q` once the scaled ceiling is below `log q`.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem selbergTensorCoefficient_coordinate_lt
    {ι : Type*} [Fintype ι] (F : (ι ⊕ ι) → ℝ → ℂ) (L A : (ι ⊕ ι) → ℝ)
    (hL : ∀ i, 0 < L i)
    (hsupport : ∀ i t, 0 ≤ t → F i t ≠ 0 → t ≤ A i)
    {q : ℕ} (hq : 0 < q) (hAq : ∀ i, A i * L i < Real.log q)
    (d : (ι ⊕ ι) → ℕ) (hd : ∀ i, 0 < d i) (hne : selbergTensorCoefficient F L d ≠ 0) :
    ∀ i, d i < q := by
  intro i
  have hterm := (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  have hF : F i (Real.log (d i) / L i) ≠ 0 := (mul_ne_zero_iff.mp hterm).2
  have ht : 0 ≤ Real.log (d i) / L i := div_nonneg
    (Real.log_nonneg (by exact_mod_cast hd i)) (hL i).le
  have hlog : Real.log (d i) < Real.log q :=
    ((div_le_iff₀ (hL i)).mp (hsupport i _ ht hF)).trans_lt (hAq i)
  exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hd i) (by exact_mod_cast hq)).mp hlog

theorem selbergTensorCoefficient_sum_coordinate_lt
    {ι J : Type*} [Fintype ι] (S : Finset J)
    (F : J → (ι ⊕ ι) → ℝ → ℂ) (L A : (ι ⊕ ι) → ℝ)
    (hL : ∀ i, 0 < L i)
    (hsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ A i)
    {q : ℕ} (hq : 0 < q) (hAq : ∀ i, A i * L i < Real.log q)
    (d : (ι ⊕ ι) → ℕ) (hd : ∀ i, 0 < d i)
    (hne : (∑ j ∈ S, selbergTensorCoefficient (F j) L d) ≠ 0) :
    ∀ i, d i < q := by
  obtain ⟨j, hj, hcoef⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact selbergTensorCoefficient_coordinate_lt (F j) L A hL (hsupport j hj) hq hAq d hd hcoef

theorem cutoffSelbergBilinearSum_tensor_square_eq_raw
    {K w m q : ℕ} {J : Type*} (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w)
    (S : Finset J)
    (F : J → (preSievedShifts K w ⊕ preSievedShifts K w) → ℝ → ℂ)
    (L A : (preSievedShifts K w ⊕ preSievedShifts K w) → ℝ)
    (hL : ∀ i, 0 < L i)
    (hsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ A i)
    (hAq : ∀ i, A i * L i < Real.log q) :
    cutoffSelbergBilinearSum P (affineFourierCollisionEdges (preSievedShifts K w) m q)
        (affineFourierCompanionSwitch m)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d) =
      rawAffineDivisorKernel (preSievedShifts K w) P m q
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (F j) L d) := by
  apply cutoffSelbergBilinearSum_preSieved_eq_raw P hP hrough hm hq hKw
  intro d hd hne i b
  have hpos (i) (b) : 0 < d i b := Nat.pos_of_dvd_of_pos
    ((mem_rawDoubledCutoffDivisorTuples P hP d).mp hd i b) (primeFinsetProduct_pos P hP)
  have hboth := mul_ne_zero_iff.mp hne
  cases b
  · exact selbergTensorCoefficient_sum_coordinate_lt S F L A hL hsupport hq.pos hAq
      (fun i ↦ d i false) (fun i ↦ hpos i false) hboth.1 i
  · exact selbergTensorCoefficient_sum_coordinate_lt S F L A hL hsupport hq.pos hAq
      (fun i ↦ d i true) (fun i ↦ hpos i true) hboth.2 i

end

end Erdos4b
