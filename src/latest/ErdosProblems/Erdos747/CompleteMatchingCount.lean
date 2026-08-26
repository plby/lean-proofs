import ErdosProblems.Erdos747.StructuralLayer

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Exact count in the complete hypergraph -/

/-- Removing one complete edge from the complete `3`-graph and reindexing
the remaining vertices again gives a complete `3`-graph. -/
lemma reindexGraphAway_allEdges {n : ℕ} {Z : Edge n}
    (hZ : Z ∈ allEdges n) :
    reindexGraphAway (allEdges n) Z hZ = allEdges (n - 1) := by
  ext W
  constructor
  · intro hW
    exact reindexGraphAway_subset_allEdges hZ (by exact fun _ h ↦ h) hW
  · intro hW
    exact (mem_reindexGraphAway hZ W).mpr
      (unreindexEdgeAway_mem_allEdges hZ hW)

/-- Every edge in the complete `3`-graph has as many completions as there
are perfect matchings on the remaining `3(n-1)` vertices. -/
lemma completionWeight_allEdges {n : ℕ} (hn : 0 < n)
    {Z : Edge n} (hZ : Z ∈ allEdges n) :
    completionWeight (allEdges n) Z =
      (perfectMatchings (n - 1) (allEdges (n - 1))).card := by
  rw [← card_perfectMatchings_reindexGraphAway hn (allEdges n) hZ,
    reindexGraphAway_allEdges hZ]

/-- Exact recurrence for the number of perfect matchings of the complete
`3`-uniform hypergraph. -/
lemma card_perfectMatchings_allEdges_recurrence {n : ℕ} (hn : 0 < n) :
    (perfectMatchings n (allEdges n)).card =
      (3 * n - 1).choose 2 *
        (perfectMatchings (n - 1) (allEdges (n - 1))).card := by
  let v : Vertex n := ⟨0, by omega⟩
  have hsum := sum_incident_matchingWeight n (allEdges n)
    (by exact fun _ h ↦ h) v
  calc
    (perfectMatchings n (allEdges n)).card =
        ∑ A ∈ incidentEdges n v, matchingWeight (allEdges n) A := by
      simpa [incidentEdges] using hsum.symm
    _ = ∑ _A ∈ incidentEdges n v,
        (perfectMatchings (n - 1) (allEdges (n - 1))).card := by
      apply Finset.sum_congr rfl
      intro A hA
      have hAall : A ∈ allEdges n := (Finset.mem_filter.mp hA).1
      rw [← completionWeight_eq_matchingWeight_of_mem (allEdges n) hAall,
        completionWeight_allEdges hn hAall]
    _ = (3 * n - 1).choose 2 *
        (perfectMatchings (n - 1) (allEdges (n - 1))).card := by
      rw [Finset.sum_const_nat, card_incidentEdges]
      simp

/-- Closed multiplicative form of the exact count.  It is equivalent to
`|PM(K^3_{3n})| = (3n)! / (6^n n!)`, but avoids natural-number division. -/
lemma completeMatchingCount_factorial_identity (n : ℕ) :
    6 ^ n * n.factorial * (perfectMatchings n (allEdges n)).card =
      (3 * n).factorial := by
  induction n with
  | zero =>
      simp only [pow_zero, Nat.factorial_zero, one_mul, mul_one, Nat.mul_zero]
      unfold perfectMatchings allEdges
      change (Finset.filter IsMatching {∅}).card = 1
      have hfilter :
          Finset.filter IsMatching ({∅} : Finset (Finset (Edge 0))) = {∅} := by
        apply Finset.filter_eq_self.mpr
        intro F hF
        have hFempty : F = ∅ := by simpa using hF
        subst F
        simp [IsMatching]
      rw [hfilter]
      simp
  | succ n ih =>
      have hrec := card_perfectMatchings_allEdges_recurrence
        (n := n + 1) (by omega)
      have hsub : n + 1 - 1 = n := by omega
      rw [hsub] at hrec
      rw [hrec, pow_succ, Nat.factorial_succ]
      have hreshape :
          6 ^ n * 6 * ((n + 1) * n.factorial) *
              ((3 * (n + 1) - 1).choose 2 *
                (perfectMatchings n (allEdges n)).card) =
            (6 ^ n * n.factorial *
                (perfectMatchings n (allEdges n)).card) *
              (6 * (n + 1) * (3 * (n + 1) - 1).choose 2) := by
        ring
      rw [hreshape, ih]
      have hchoose := Nat.choose_mul_factorial_mul_factorial
        (n := 3 * n + 2) (k := 2) (by omega)
      have hchoose' :
          (3 * n + 2).choose 2 * 2 * (3 * n).factorial =
            (3 * n + 2).factorial := by
        simpa using hchoose
      have hindex : 3 * (n + 1) - 1 = 3 * n + 2 := by omega
      rw [hindex]
      calc
        (3 * n).factorial *
              (6 * (n + 1) * (3 * n + 2).choose 2) =
            (3 * (n + 1)) *
              ((3 * n + 2).choose 2 * 2 * (3 * n).factorial) := by
                ring
        _ = (3 * (n + 1)) * (3 * n + 2).factorial := by rw [hchoose']
        _ = (3 * (n + 1)).factorial := by
          simpa only [show 3 * (n + 1) = (3 * n + 2) + 1 by omega] using
            (Nat.factorial_succ (3 * n + 2)).symm

/-- The upper half of Stirling's estimate with a simple explicit remainder.
This follows from monotonicity of Mathlib's Stirling sequence. -/
lemma log_factorial_le_stirling_explicit {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log n - n + Real.log n / 2 + 1 := by
  let k := n - 1
  have hkn : k + 1 = n := by dsimp only [k]; omega
  have hanti := Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  change Real.log (Stirling.stirlingSeq (k + 1)) ≤
    Real.log (Stirling.stirlingSeq (0 + 1)) at hanti
  rw [hkn, zero_add, Stirling.log_stirlingSeq_formula,
    Stirling.log_stirlingSeq_formula] at hanti
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlog2n : Real.log ((2 : ℝ) * n) =
      Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num) hn0]
  have hlognexp : Real.log ((n : ℝ) / Real.exp 1) =
      Real.log n - 1 := by
    rw [Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp]
  have hlogoneexp : Real.log ((1 : ℝ) / Real.exp 1) = -1 := by
    rw [Real.log_div (by norm_num) (Real.exp_ne_zero 1),
      Real.log_one, Real.log_exp]
    norm_num
  norm_num [hlog2n, hlognexp, hlogoneexp] at hanti ⊢
  linarith

/-- Sharp logarithmic lower bound for the number of complete matchings.  The
linear constant `log (9/2)` is the one lost by the earlier colored-matching
injection; only a logarithmic remainder remains. -/
lemma log_card_perfectMatchings_allEdges_sharp {n : ℕ} (hn : 1 ≤ n) :
    2 * (n : ℝ) * Real.log n +
          (n : ℝ) * Real.log ((9 : ℝ) / 2) - 2 * (n : ℝ) -
          Real.log n / 2 - 1 ≤
      Real.log ((perfectMatchings n (allEdges n)).card : ℝ) := by
  have hPnat := factorial_sq_le_card_perfectMatchings_allEdges
    (show 0 < n by omega)
  have hPpos : (0 : ℝ) <
      (perfectMatchings n (allEdges n)).card := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < n.factorial ^ 2) hPnat)
  have hidNat := completeMatchingCount_factorial_identity n
  have hid :
      (6 : ℝ) ^ n * (n.factorial : ℝ) *
          ((perfectMatchings n (allEdges n)).card : ℝ) =
        ((3 * n).factorial : ℝ) := by
    exact_mod_cast hidNat
  have h6 : (6 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hP : ((perfectMatchings n (allEdges n)).card : ℝ) ≠ 0 := hPpos.ne'
  have hlogid := congrArg Real.log hid
  rw [Real.log_mul (mul_ne_zero h6 hfac) hP,
    Real.log_mul h6 hfac, Real.log_pow] at hlogid
  have hlogP :
      Real.log ((perfectMatchings n (allEdges n)).card : ℝ) =
        Real.log ((3 * n).factorial : ℝ) -
          (n : ℝ) * Real.log 6 - Real.log (n.factorial : ℝ) := by
    linarith
  have hnumFull := Stirling.le_log_factorial_stirling
    (n := 3 * n) (show 3 * n ≠ 0 by omega)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog3n0 : 0 ≤ Real.log ((3 * n : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 3 * n by omega)
  have hlogpi0 : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  have hnum :
      ((3 * n : ℕ) : ℝ) * Real.log ((3 * n : ℕ) : ℝ) -
          ((3 * n : ℕ) : ℝ) ≤
        Real.log ((3 * n).factorial : ℝ) := by
    nlinarith
  have hden := log_factorial_le_stirling_explicit hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlog3n : Real.log ((3 * n : ℕ) : ℝ) =
      Real.log 3 + Real.log n := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num) hn0]
  have hlog6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hlognine : Real.log ((9 : ℝ) / 2) =
      2 * Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    ring
  rw [hlogP]
  rw [hlog3n] at hnum
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hnum
  rw [hlog6, hlognine]
  nlinarith

end

end Erdos747
