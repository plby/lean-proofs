import ErdosProblems.Erdos49.PairCluster
import ErdosProblems.Erdos49.PrimaryStructure

/-!
# Applying the primary packing estimate

This file discharges the cell-by-cell endpoint bookkeeping in the primary
estimate from one uniform theta estimate on `[W-1,N]`.
-/

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

theorem primary_global_bound_of_uniform_theta
    {N L D W : ℕ} {A : Finset ℕ} {Err : ℝ}
    (hAprim : A ⊆ primarySet N L D)
    (hmono : TotientMonotoneOn A)
    (hD : 1 ≤ D) (hW : 3 ≤ W)
    (hshort : ∀ n ∈ A,
      (W : ℝ) ≤ ((quotientBucket W n * W : ℕ) : ℝ) /
        (4 * (D : ℝ) ^ 2))
    (hErr : 0 ≤ Err)
    (htheta : ∀ x : ℕ, W - 1 ≤ x → x ≤ N →
      |Chebyshev.theta (x : ℝ) - x| ≤ Err) :
    (A.card : ℝ) ≤ (N : ℝ) / Real.log W +
      (((N / W + 1) * D : ℕ) : ℝ) * D *
        ((2 + 2 * Err) / Real.log W) := by
  have hWpos : 0 < W := by omega
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  apply primary_global_bound hAprim hmono hD hWpos hshort hlogW hErr
  intro k hk d₀ hd₀ hc
  let cell := primaryCell A (quotientBucket W) (primaryD N L D) k
  let u := cell.min' hc / d₀
  let v := cell.max' hc / d₀
  have hdData := mem_ratioFibre.mp hd₀
  have hd₀pos : 0 < d₀ := by omega
  have hd₀D : d₀ ≤ D := hdData.2.1
  have hminMem : cell.min' hc ∈ A :=
    (Finset.mem_filter.mp (cell.min'_mem hc)).1
  have hmaxMem : cell.max' hc ∈ A :=
    (Finset.mem_filter.mp (cell.max'_mem hc)).1
  have hminN : cell.min' hc ≤ N :=
    (mem_primarySet.mp (hAprim hminMem)).2.1
  have hmaxN : cell.max' hc ≤ N :=
    (mem_primarySet.mp (hAprim hmaxMem)).2.1
  have hbucket := (quotientBucket_bounds (W := W) (n := cell.min' hc) hWpos).1
  have hshortMin := hshort (cell.min' hc) hminMem
  have hscaleReal :
      (4 * D ^ 2 * W : ℕ) ≤ quotientBucket W (cell.min' hc) * W := by
    have hden : (0 : ℝ) < 4 * (D : ℝ) ^ 2 := by positivity
    have := (le_div_iff₀ hden).mp hshortMin
    have hreal : 4 * (D : ℝ) ^ 2 * W ≤
        ((quotientBucket W (cell.min' hc) * W : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
        mul_assoc, mul_comm, mul_left_comm] using this
    exact_mod_cast hreal
  have hWu : W ≤ u := by
    apply (Nat.le_div_iff_mul_le hd₀pos).2
    calc
      W * d₀ ≤ 4 * D ^ 2 * W := by
        have : d₀ ≤ 4 * D ^ 2 := by nlinarith
        nlinarith
      _ ≤ quotientBucket W (cell.min' hc) * W := hscaleReal
      _ ≤ cell.min' hc := hbucket
  have huOne : 1 < u := by omega
  have hlogu : Real.log (W : ℝ) ≤ Real.log (u : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hWu
  have huN : u ≤ N := (Nat.div_le_self _ _).trans hminN
  have hvN : v ≤ N := (Nat.div_le_self _ _).trans hmaxN
  have huv : u ≤ v := Nat.div_le_div_right (cell.min'_le_max' hc)
  have huErr :
      |Chebyshev.theta ((u - 1 : ℕ) : ℝ) - (u - 1 : ℕ)| ≤ Err := by
    apply htheta
    · omega
    · omega
  have hvErr : |Chebyshev.theta (v : ℝ) - v| ≤ Err :=
    htheta v (by omega) hvN
  exact ⟨huOne, hlogu, huErr, hvErr⟩

#print axioms primary_global_bound_of_uniform_theta

end

end Erdos49
