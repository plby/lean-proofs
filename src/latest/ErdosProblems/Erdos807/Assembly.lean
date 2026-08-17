import ErdosProblems.Erdos807.Core
import ErdosProblems.Erdos807.Parameters

/-!
# Numerical assembly for the Alon--Bohman--Huang bound

The structured witness saves `k-r` stars.  This file converts the integral
rounding bound for that saving and the real independence-number estimate into
the advertised multiplicative improvement.
-/

namespace Erdos807

/-- The rounded structured saving and the `2.001 log₂ n` independence bound
imply the ABH inequality with the explicit constant `c = 1/1000`. -/
theorem abh_inequality_of_structured_and_independence
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hk : structuredSize n ≤ n)
    (hsaving : 2008 * (logParameter n + 1) ≤
      1000 * (structuredSize n - blockCount n))
    (hstructured : bipartitionNumber G ≤
      n - structuredSize n + blockCount n)
    (hindependence : (G.indepNum : ℝ) <
      (2001 / 1000 : ℝ) * ((logParameter n : ℝ) + 1)) :
    (bipartitionNumber G : ℝ) ≤
      (n : ℝ) - (1 + (1 / 1000 : ℝ)) * (G.indepNum : ℝ) := by
  have hrk : blockCount n ≤ structuredSize n := by
    rw [structuredSize_eq_mul_blockCount]
    omega
  have hnk : n - structuredSize n + blockCount n =
      n - (structuredSize n - blockCount n) := by omega
  have hstructuredR : (bipartitionNumber G : ℝ) ≤
      (n : ℝ) - ((structuredSize n : ℝ) - (blockCount n : ℝ)) := by
    rw [← Nat.cast_sub hrk,
      ← Nat.cast_sub ((Nat.sub_le _ _).trans hk), ← hnk]
    exact_mod_cast hstructured
  have hsavingR : (2008 : ℝ) * ((logParameter n : ℝ) + 1) ≤
      1000 * ((structuredSize n : ℝ) - (blockCount n : ℝ)) := by
    exact_mod_cast hsaving
  have hm : (0 : ℝ) < (logParameter n : ℝ) + 1 := by positivity
  nlinarith

/-- The same rounded saving also gives the explicit logarithmic half of the
ABH theorem, again with `c = 1/1000`. -/
theorem abh_log_inequality_of_structured
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hk : structuredSize n ≤ n)
    (hsaving : 2008 * (logParameter n + 1) ≤
      1000 * (structuredSize n - blockCount n))
    (hstructured : bipartitionNumber G ≤
      n - structuredSize n + blockCount n)
    (hlog : Real.logb 2 n < (logParameter n : ℝ) + 1) :
    (bipartitionNumber G : ℝ) ≤
      (n : ℝ) - (2 + 2 * (1 / 1000 : ℝ)) * Real.logb 2 n := by
  have hrk : blockCount n ≤ structuredSize n := by
    rw [structuredSize_eq_mul_blockCount]
    omega
  have hnk : n - structuredSize n + blockCount n =
      n - (structuredSize n - blockCount n) := by omega
  have hstructuredR : (bipartitionNumber G : ℝ) ≤
      (n : ℝ) - ((structuredSize n : ℝ) - (blockCount n : ℝ)) := by
    rw [← Nat.cast_sub hrk,
      ← Nat.cast_sub ((Nat.sub_le _ _).trans hk), ← hnk]
    exact_mod_cast hstructured
  have hsavingR : (2008 : ℝ) * ((logParameter n : ℝ) + 1) ≤
      1000 * ((structuredSize n : ℝ) - (blockCount n : ℝ)) := by
    exact_mod_cast hsaving
  nlinarith

end Erdos807
