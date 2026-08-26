import ErdosProblems.Erdos1188.SparseAllCutoff
import ErdosProblems.Erdos1188.UpperBound

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Matching exponent-scale estimate for the covering-system count
-/

namespace Erdos1188

/-- Unconditional explicit lower function (zero only before the construction's
large-index gate becomes available). -/
noncomputable def sparseExplicitLower (D x : ℕ) : ℕ :=
  if 2 * (sparseSeed + 1) ≤ sparseAllCutoffQuotient D x then
    2 ^ ((sparseAllCutoffQuotient D x / 2).choose 2)
  else 0

/-- The explicit lower function is a pointwise lower bound for `F`. -/
theorem sparseExplicitLower_le (D x : ℕ)
    (hD : sparseSeedProduct * (256 ^ 3 * 2048 * 2049) ≤ D) :
    sparseExplicitLower D x ≤ coveringCount x := by
  unfold sparseExplicitLower
  split_ifs with h
  · exact explicit_sparse_quotient_lower D x hD h
  · exact Nat.zero_le _

/-- Exact two-sided estimate.  The lower exponent is quadratic in
`sqrt(x/D)/(log_2(x+1)+1)^2`, while the upper exponent is elementary. -/
theorem sparse_two_sided_estimate (D x : ℕ)
    (hD : sparseSeedProduct * (256 ^ 3 * 2048 * 2049) ≤ D)
    (hlarge : 2 * (sparseSeed + 1) ≤ sparseAllCutoffQuotient D x) :
    2 ^ ((sparseAllCutoffQuotient D x / 2).choose 2) ≤ coveringCount x ∧
      coveringCount x ≤ (x + 2) ^ (x + 1) := by
  exact ⟨explicit_sparse_quotient_lower D x hD hlarge,
    coveringCount_le_elementary x⟩

/-- The problem's formal estimate interface is satisfied by the explicit sparse
lower function and the elementary upper function.  Both inequalities actually
hold pointwise, not merely eventually. -/
theorem sparse_isAsymptoticEstimate (D : ℕ)
    (hD : sparseSeedProduct * (256 ^ 3 * 2048 * 2049) ≤ D) :
    IsAsymptoticEstimate
      (fun x => (sparseExplicitLower D x : ℝ))
      (fun x => (((x + 2) ^ (x + 1) : ℕ) : ℝ)) := by
  constructor
  · filter_upwards with x
    exact_mod_cast sparseExplicitLower_le D x hD
  · filter_upwards with x
    exact_mod_cast coveringCount_le_elementary x

end Erdos1188
