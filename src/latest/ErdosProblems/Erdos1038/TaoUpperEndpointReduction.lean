import ErdosProblems.Erdos1038.TaoUpperEquality
import ErdosProblems.Erdos1038.ExtremumOrder

/-!
# Reduction of the sharp upper theorem to endpoint exclusion

Tao's trial-measure argument rules out a closed-target endpoint beyond
`-sqrt 2` whenever the sublevel volume is at least the proposed sharp
value.  This conditional statement is the exact analytic interface needed
by the polynomial theorem.  Reflection handles the right endpoint, and the
separate algebraic module handles equality without a limiting measure
argument.
-/

open scoped ENNReal
open MeasureTheory Polynomial

namespace Erdos1038

noncomputable section

/-- The exact remaining analytic statement for the sharp upper bound.  The
volume hypothesis is essential: for example, `X + 1` has left endpoint
`-2`, but sublevel volume only `2`. -/
def TaoSharpLeftEndpointControl : Prop :=
  ∀ f : Polynomial ℝ, ∀ hf : IsAdmissible f,
    ENNReal.ofReal (2 * Real.sqrt 2) ≤ sublevelVolume f →
      -Real.sqrt 2 ≤ closedUnitSublevelLeft f hf

theorem polynomial_upper_bound_of_taoSharpLeftEndpointControl
    (hTao : TaoSharpLeftEndpointControl) (f : Polynomial ℝ)
    (hf : IsAdmissible f) :
    sublevelVolume f ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  apply le_of_not_gt
  intro hvolume
  obtain ⟨g, hg, hsame, hleft⟩ :=
    exists_left_oriented_of_volume_gt hf hvolume
  have hbound := hTao g hg (by rw [hsame]; exact hvolume.le)
  linarith

theorem polynomial_upper_equality_iff_of_taoSharpLeftEndpointControl
    (hTao : TaoSharpLeftEndpointControl) (f : Polynomial ℝ)
    (hf : IsAdmissible f) :
    sublevelVolume f = ENNReal.ofReal (2 * Real.sqrt 2) ↔
      ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m := by
  constructor
  · intro hvolume
    have hthreshold : ENNReal.ofReal (2 * Real.sqrt 2) ≤
        sublevelVolume f := hvolume.ge
    have hleft := hTao f hf hthreshold
    have hreflectedThreshold : ENNReal.ofReal (2 * Real.sqrt 2) ≤
        sublevelVolume (rootReflection f) := by
      rw [sublevelVolume_rootReflection, hvolume]
    have hright := hTao (rootReflection f) hf.reflection
      hreflectedThreshold
    rw [closedUnitSublevelLeft_rootReflection hf] at hright
    exact extremal_of_sublevelVolume_eq_of_endpoint_bounds hf
      hleft (by linarith) hvolume
  · rintro ⟨m, hm, rfl⟩
    exact sublevelVolume_extremal hm

/-- Conditional endpoint exclusion supplies every sharp-upper clause of
`MainTheorem`. -/
theorem mainTheorem_upper_clauses_of_taoSharpLeftEndpointControl
    (hTao : TaoSharpLeftEndpointControl) :
    supremumLength = ENNReal.ofReal (2 * Real.sqrt 2) ∧
    (∀ m : ℕ, 0 < m →
      IsAdmissible ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) ∧
      sublevelVolume ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) =
        ENNReal.ofReal (2 * Real.sqrt 2)) ∧
    (∀ f : Polynomial ℝ, IsAdmissible f →
      (sublevelVolume f = ENNReal.ofReal (2 * Real.sqrt 2) ↔
        ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m)) := by
  refine ⟨supremumLength_eq_proposed
    (polynomial_upper_bound_of_taoSharpLeftEndpointControl hTao), ?_, ?_⟩
  · exact extremalPolynomial_attains
  · exact polynomial_upper_equality_iff_of_taoSharpLeftEndpointControl hTao

end

end Erdos1038
