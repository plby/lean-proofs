/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralOneDimensional
import ErdosProblems.Erdos378.PrimeReciprocal

/-!
# The small Vaughan terms in the central reciprocal range

At the cutoff `U = V = 1`, Vaughan's second term is exactly the
logarithmically weighted original interval, while the third term vanishes:
its only possible coefficient contains `Λ(1) = 0`.  This turns the two
small-factor terms into the one-dimensional estimates proved in
`CentralOneDimensional`.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace CentralVaughanSmallTerms

open BoundedGaps.Maynard
open PrimeReciprocal
open AdaptiveShifts
open CentralCorrelation
open CentralOneDimensional

noncomputable section

theorem weightedVaughanIntervalTwo_one_eq
    {X : ℝ} {x y : ℕ} (hy : 1 ≤ y) :
    weightedVaughanIntervalTwo (reciprocalWeight X) 1 x y =
      ∑ h ∈ Finset.Ioc x y,
        (Real.log (h : ℝ) : ℂ) * reciprocalWeight X h := by
  rw [weightedVaughanIntervalTwo_eq_nested]
  have hs : (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ 1) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro hd
      have hdle : d ≤ 1 := by exact_mod_cast hd.2
      omega
    · intro hd
      subst d
      simp [hy]
  rw [hs]
  simp

theorem norm_weightedVaughanIntervalTwo_one_le
    {X : ℝ} (hX : 0 < X) {x y : ℕ}
    (hx : 1 ≤ x) (hxy : x < y)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition x) :
    ‖weightedVaughanIntervalTwo (reciprocalWeight X) 1 x y‖ ≤
      2 * Real.log (y : ℝ) * adaptiveCorrelationEnvelope x := by
  rw [weightedVaughanIntervalTwo_one_eq (hx.trans hxy.le)]
  exact norm_log_weighted_central_interval_le
    hX hx hxy hXlo hXhi hyx hsize

theorem weightedVaughanIntervalThree_one_eq_zero
    {X : ℝ} {x y : ℕ} :
    weightedVaughanIntervalThree (reciprocalWeight X) 1 1 x y = 0 := by
  rw [← neg_eq_zero]
  rw [neg_weightedVaughanIntervalThree_eq_nested (reciprocalWeight X)
    (by norm_num) (by norm_num)]
  apply Finset.sum_eq_zero
  intro t ht
  apply mul_eq_zero_of_left
  have htpos : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  by_cases ht1 : t = 1
  · subst t
    unfold vaughanThirdCoefficient
    rw [Finset.sum_filter]
    simp [ArithmeticFunction.vonMangoldt_apply_one]
  · rw [vaughanThirdCoefficient_eq_zero_of_cutoffProduct_lt]
    · norm_num
    · norm_num
    · norm_num
    · exact_mod_cast (show 1 < t by omega)

end

end CentralVaughanSmallTerms
end Erdos378
