import ErdosProblems.Erdos587.HooleyInnerBox
import ErdosProblems.Erdos587.GAPSpanControl

/-! # Height-to-span control for an inner lattice-basis box -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

lemma deltaBasisBox_coefficientSpan (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (R : Fin X.rank → ℕ) :
    (deltaBasisBox X b R).coefficientSpan = 2 * ∑ i, (R i : ℤ) * |X.eval (b i)| := by
  simp only [coefficientSpan, deltaBasisBox, Nat.cast_mul, Nat.cast_ofNat, mul_assoc,
    Finset.mul_sum]
  rfl

lemma deltaBasisBox_point_le (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (R : Fin X.rank → ℕ)
    {z : ℤ} (hz : z ∈ (deltaBasisBox X b R).carrier) :
    z ≤ X.base + ∑ i, (R i : ℤ) * |X.eval (b i)| := by
  obtain ⟨x, rfl⟩ := (deltaBasisBox X b R).mem_carrier_iff.mp hz
  rw [deltaBasisBox_eval, eval_latticeSynthesis]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ |((x i : ℤ) - R i) * X.eval (b i)| := le_abs_self _
    _ = |(x i : ℤ) - R i| * |X.eval (b i)| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (deltaBasisBox_coeff_bound X b R x i) (abs_nonneg _)

lemma delta_sum_eval_le_of_coordinate_mass (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (U : Finset (Fin X.rank → ℤ))
    (R : Fin X.rank → ℕ) (K : ℝ)
    (hmass : ∀ i, (∑ u ∈ U, ((|latticeCoordinates b u i| : ℤ) : ℝ)) ≤ K * R i) :
    (∑ u ∈ U, (X.eval u : ℝ)) ≤ K * ∑ i, (R i : ℝ) * |(X.eval (b i) : ℝ)| := by
  have hlin (v : Fin X.rank → ℤ) :
      (X.eval v : ℝ) = ∑ i, (latticeCoordinates b v i : ℝ) * (X.eval (b i) : ℝ) := by
    have hh := eval_latticeSynthesis X.eval b (latticeCoordinates b v)
    rw [(latticeCoordinates b).symm_apply_apply] at hh
    exact_mod_cast hh
  have hterm (v : Fin X.rank → ℤ) : (X.eval v : ℝ) ≤
      ∑ i, ((|latticeCoordinates b v i| : ℤ) : ℝ) * |(X.eval (b i) : ℝ)| := by
    rw [hlin]
    apply Finset.sum_le_sum
    intro i _
    rw [Int.cast_abs, ← abs_mul]
    exact le_abs_self _
  calc
    _ ≤ ∑ u ∈ U, ∑ i, ((|latticeCoordinates b u i| : ℤ) : ℝ) * |(X.eval (b i) : ℝ)| :=
      Finset.sum_le_sum (fun u _ => hterm u)
    _ = ∑ i, (∑ u ∈ U, ((|latticeCoordinates b u i| : ℤ) : ℝ)) * |(X.eval (b i) : ℝ)| := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ i, (K * R i) * |(X.eval (b i) : ℝ)| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hmass i) (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem deltaBasisBox_height_of_coordinate_mass (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (U : Finset (Fin X.rank → ℤ))
    (R : Fin X.rank → ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hmass : ∀ i, (∑ u ∈ U, ((|latticeCoordinates b u i| : ℤ) : ℝ)) ≤ K * R i)
    (hbase : (X.base : ℝ) ≤ C * ∑ u ∈ U, (X.eval u : ℝ)) :
    ((deltaBasisBox X b R).upperEndpoint : ℝ) ≤
      (C * K + 1) * (deltaBasisBox X b R).coefficientSpan := by
  let M : ℝ := ∑ i, (R i : ℝ) * |(X.eval (b i) : ℝ)|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => by positivity)
  have hspan : ((deltaBasisBox X b R).coefficientSpan : ℝ) = 2 * M := by
    rw [deltaBasisBox_coefficientSpan]
    push_cast
    rfl
  have hpoint := deltaBasisBox_point_le X b R (deltaBasisBox X b R).upperEndpoint_mem
  have hpointR : ((deltaBasisBox X b R).upperEndpoint : ℝ) ≤ (X.base : ℝ) + M := by
    dsimp only [M]
    exact_mod_cast hpoint
  have hsum := delta_sum_eval_le_of_coordinate_mass X b U R K hmass
  calc
    _ ≤ (X.base : ℝ) + M := hpointR
    _ ≤ C * (∑ u ∈ U, (X.eval u : ℝ)) + M := add_le_add hbase le_rfl
    _ ≤ C * (K * M) + M := add_le_add (mul_le_mul_of_nonneg_left hsum hC) le_rfl
    _ = (C * K + 1) * M := by ring
    _ ≤ (C * K + 1) * (deltaBasisBox X b R).coefficientSpan := by
      rw [hspan]
      exact mul_le_mul_of_nonneg_left (by linarith : M ≤ 2 * M) (by positivity)

end Erdos587.GeneralizedAP
