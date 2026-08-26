import ErdosProblems.Erdos788.SparseNeighborhood
import ErdosProblems.Erdos788.ShearerAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A logarithmic lower bound from the triangle-free sample

This file combines the exact finite sampling statement with the harmonic
weight bound for triangle-free graphs.  The only rounding loss comes from
replacing the sampled average degree by an integer upper bound.
-/

namespace Erdos788

open Finset

/-- Clearing a positive natural denominator, with one unit of rounding,
turns an edge bound into a total-degree bound. -/
private theorem two_mul_le_rounded_average
    {q B e r : ℕ} (hq : 0 < q) (hedge : q * e ≤ 2 * B * r) :
    2 * e ≤ (2 * (2 * B / q + 1)) * r := by
  have hround : 2 * B ≤ q * (2 * B / q + 1) :=
    (Nat.lt_mul_div_succ (2 * B) hq).le
  have hqedge : q * e ≤ q * ((2 * B / q + 1) * r) := by
    calc
      q * e ≤ 2 * B * r := hedge
      _ ≤ (q * (2 * B / q + 1)) * r :=
        Nat.mul_le_mul_right r hround
      _ = q * ((2 * B / q + 1) * r) := by
        simp only [mul_assoc]
  have he : e ≤ (2 * B / q + 1) * r :=
    Nat.le_of_mul_le_mul_left hqedge hq
  calc
    2 * e ≤ 2 * ((2 * B / q + 1) * r) := Nat.mul_le_mul_left 2 he
    _ = (2 * (2 * B / q + 1)) * r := by simp only [mul_assoc]

/-- Exact sampling followed by the triangle-free Shearer estimate.  Here
`q = 2^t`, `B = |A| + 1`, and `K` is an integral upper bound for the average
degree of the triangle-free sample. -/
theorem sumGraph_indepNum_log_lower {N : ℕ} (A : Finset ℕ) (t : ℕ)
    (hscale : 2 * A.card ^ 3 ≤ N * (2 ^ t) ^ 2) :
    let q : ℕ := 2 ^ t
    let B : ℕ := A.card + 1
    let K : ℕ := 2 * (2 * B / q + 1)
    (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
      16 * q * K * ((sumGraph N A).indepNum : ℝ) := by
  classical
  let q : ℕ := 2 ^ t
  let B : ℕ := A.card + 1
  let K : ℕ := 2 * (2 * B / q + 1)
  change (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
    16 * q * K * ((sumGraph N A).indepNum : ℝ)
  have hq : 0 < q := by
    simp [q]
  have hK : 0 < K := by
    simp [K]
  obtain ⟨R, htriangleFree, hcard, hedge⟩ :=
    exists_triangleFree_sample A t hscale
  let H := (sumGraph N A).induce (R : Set (Fin N))
  have hedge' : q * (H.cliqueFinset 2).card ≤ 2 * B * R.card := by
    simpa only [q, B, H] using! hedge
  have hRtypeCard : Fintype.card ↑(R : Set (Fin N)) = R.card := by
    rw [← Set.toFinset_card]
    simp
  have hdegree : ∑ v, H.degree v ≤ K * Fintype.card ↑(R : Set (Fin N)) := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    rw [← card_cliqueFinset_two_eq_card_edgeFinset (G := H)]
    rw [hRtypeCard]
    simpa only [K] using!
      (two_mul_le_rounded_average hq hedge')
  have hweight : AKSRoute.graphWeight H ≤ (H.indepNum : ℚ) :=
    AKSRoute.graphWeight_le_indepNum H (by simpa only [H] using! htriangleFree)
  have hsampleLog :=
    AKSRoute.card_mul_log_le_eight_mul_average_mul_indepNum
      H hK hdegree hweight
  have hsampleLog' :
      (R.card : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
        8 * K * (H.indepNum : ℝ) := by
    rw [← hRtypeCard]
    exact hsampleLog
  have hcardQ : (N : ℚ) / (2 * (q : ℚ)) ≤ (R.card : ℚ) := by
    simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using! hcard
  have hcardR : (N : ℝ) / (2 * (q : ℝ)) ≤ (R.card : ℝ) := by
    have hcardRcast := (Rat.cast_le (K := ℝ)).2 hcardQ
    push_cast at hcardRcast
    exact hcardRcast
  have hNle : (N : ℝ) ≤ (R.card : ℝ) * (2 * q) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mp hcardR
  have hlogNonneg : 0 ≤ Real.log ((2 * K + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * K + 1 by omega)
  have hind : (H.indepNum : ℝ) ≤ ((sumGraph N A).indepNum : ℝ) := by
    exact_mod_cast (by
      simpa only [H] using!
        (indepNum_induce_finset_le (G := sumGraph N A) R))
  calc
    (N : ℝ) * Real.log (2 * K + 1 : ℕ) ≤
        ((R.card : ℝ) * (2 * q)) * Real.log (2 * K + 1 : ℕ) :=
      mul_le_mul_of_nonneg_right hNle hlogNonneg
    _ = (2 * q) *
        ((R.card : ℝ) * Real.log (2 * K + 1 : ℕ)) := by ring
    _ ≤ (2 * q) * (8 * K * (H.indepNum : ℝ)) := by
      gcongr
    _ ≤ (2 * q) *
        (8 * K * ((sumGraph N A).indepNum : ℝ)) := by
      gcongr
    _ = 16 * q * K * ((sumGraph N A).indepNum : ℝ) := by ring

end Erdos788
