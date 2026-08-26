import ErdosProblems.Erdos788.Shearer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Extracting an average-degree bound from the Shearer weight

This file isolates the elementary truncation argument used after the
triangle-free induction.  It requires only an upper bound for the total
degree and the already established comparison between graph weight and
independence number.
-/

namespace Erdos788.AKSRoute

open Finset

theorem shearerWeight_nonneg (d : ℕ) : 0 ≤ shearerWeight d := by
  rcases d with (_ | d)
  · simp
  · rw [shearerWeight_succ]
    exact div_nonneg (by linarith [one_le_harmonic_succ d]) (by positivity)

section FiniteGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- At least half the vertices have degree below twice any valid average
degree bound. -/
theorem card_le_two_mul_card_degree_lt
    {K : ℕ} (hK : 0 < K)
    (hdegree : ∑ v : V, G.degree v ≤ K * Fintype.card V) :
    Fintype.card V ≤
      2 * ((Finset.univ : Finset V).filter (fun v ↦ G.degree v < 2 * K)).card := by
  let bad := (Finset.univ : Finset V).filter (fun v ↦ 2 * K ≤ G.degree v)
  let good := (Finset.univ : Finset V).filter (fun v ↦ G.degree v < 2 * K)
  have hbadDegree : 2 * K * bad.card ≤ ∑ v : V, G.degree v := by
    calc
      2 * K * bad.card = ∑ _v ∈ bad, 2 * K := by simp [mul_comm]
      _ ≤ ∑ v ∈ bad, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v : V, G.degree v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro v _hv _hbad
        exact Nat.zero_le _
  have hbadScaled : K * (2 * bad.card) ≤ K * Fintype.card V := by
    calc
      K * (2 * bad.card) = 2 * K * bad.card := by ring
      _ ≤ ∑ v : V, G.degree v := hbadDegree
      _ ≤ K * Fintype.card V := hdegree
  have hbad : 2 * bad.card ≤ Fintype.card V := by
    exact Nat.le_of_mul_le_mul_left hbadScaled hK
  have hpartition : bad.card + good.card = Fintype.card V := by
    simpa [bad, good, not_le] using!
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (fun v ↦ 2 * K ≤ G.degree v))
  change Fintype.card V ≤ 2 * good.card
  omega

omit [DecidableEq V] in
/-- A total-degree bound converts the harmonic graph weight into a global
independence estimate, without a Jensen inequality. -/
theorem card_mul_shearerWeight_le_two_mul_indepNum
    {K : ℕ} (hK : 0 < K)
    (hdegree : ∑ v : V, G.degree v ≤ K * Fintype.card V)
    (hweight : graphWeight G ≤ (G.indepNum : ℚ)) :
    (Fintype.card V : ℚ) * shearerWeight (2 * K) ≤
      2 * (G.indepNum : ℚ) := by
  let good := (Finset.univ : Finset V).filter (fun v ↦ G.degree v < 2 * K)
  have hgoodCard : Fintype.card V ≤ 2 * good.card := by
    simpa [good] using! card_le_two_mul_card_degree_lt G hK hdegree
  have hw0 : (0 : ℚ) ≤ shearerWeight (2 * K) :=
    shearerWeight_nonneg _
  have hcard : (Fintype.card V : ℚ) * shearerWeight (2 * K) ≤
      (2 * good.card : ℕ) * shearerWeight (2 * K) := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hgoodCard) hw0
  have hgoodWeight : (good.card : ℚ) * shearerWeight (2 * K) ≤
      ∑ v ∈ good, shearerWeight (G.degree v) := by
    calc
      (good.card : ℚ) * shearerWeight (2 * K) =
          ∑ _v ∈ good, shearerWeight (2 * K) := by simp
      _ ≤ ∑ v ∈ good, shearerWeight (G.degree v) := by
        apply Finset.sum_le_sum
        intro v hv
        exact shearerWeight_antitone
          (Nat.le_of_lt (Finset.mem_filter.mp hv).2)
  have hgoodLe : (∑ v ∈ good, shearerWeight (G.degree v)) ≤
      graphWeight G := by
    rw [graphWeight]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro v _hv _hgood
    exact shearerWeight_nonneg _
  calc
    (Fintype.card V : ℚ) * shearerWeight (2 * K) ≤
        (2 * good.card : ℕ) * shearerWeight (2 * K) := hcard
    _ = 2 * ((good.card : ℚ) * shearerWeight (2 * K)) := by
      push_cast
      ring
    _ ≤ 2 * (∑ v ∈ good, shearerWeight (G.degree v)) := by gcongr
    _ ≤ 2 * graphWeight G := by gcongr
    _ ≤ 2 * (G.indepNum : ℚ) := by gcongr

omit [DecidableEq V] in
/-- Real-valued logarithmic form of the preceding truncation estimate. -/
theorem card_mul_log_le_eight_mul_average_mul_indepNum
    {K : ℕ} (hK : 0 < K)
    (hdegree : ∑ v : V, G.degree v ≤ K * Fintype.card V)
    (hweight : graphWeight G ≤ (G.indepNum : ℚ)) :
    (Fintype.card V : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
      8 * K * (G.indepNum : ℝ) := by
  have hw := card_mul_shearerWeight_le_two_mul_indepNum
    G hK hdegree hweight
  have hwR : (Fintype.card V : ℝ) * (shearerWeight (2 * K) : ℝ) ≤
      2 * (G.indepNum : ℝ) := by
    exact_mod_cast hw
  have hlog := log_le_two_mul_nat_mul_shearerWeight
    (d := 2 * K) (by positivity)
  have hlog' : Real.log ((2 * K + 1 : ℕ) : ℝ) ≤
      (2 * (2 * K) : ℝ) * (shearerWeight (2 * K) : ℝ) := by
    push_cast at hlog ⊢
    exact hlog
  calc
    (Fintype.card V : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
        (Fintype.card V : ℝ) *
          ((2 * (2 * K) : ℝ) * (shearerWeight (2 * K) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = (4 * K : ℝ) *
        ((Fintype.card V : ℝ) * (shearerWeight (2 * K) : ℝ)) := by
      ring
    _ ≤ (4 * K : ℝ) * (2 * (G.indepNum : ℝ)) := by gcongr
    _ = 8 * K * (G.indepNum : ℝ) := by
      ring

end FiniteGraph

end Erdos788.AKSRoute
