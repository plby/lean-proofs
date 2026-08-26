import ErdosProblems.Erdos1038.ExtremumOrder

/-!
# Order reduction for the sharp lower theorem

The global comparison and the positive-platform recovery construction are
separated from the final complete-lattice step.  Their conjunction implies
both the exact infimum identity and strict nonattainment for every finite
polynomial.
-/

open scoped ENNReal
open Filter Polynomial Topology

namespace Erdos1038

noncomputable section

/-- The two substantive remaining assertions in the sharp lower theorem.
This is a proposition to be proved, not an assumption or axiom. -/
def SharpLowerContent : Prop :=
  (∀ f : Polynomial ℝ, IsAdmissible f →
      ENNReal.ofReal L < sublevelVolume f) ∧
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop
        (𝓝 (ENNReal.ofReal L))

theorem mainTheorem_lower_clauses_of_sharpLowerContent
    (h : SharpLowerContent) :
    infimumLength = ENNReal.ofReal L ∧
      ∀ f : Polynomial ℝ, IsAdmissible f →
        ENNReal.ofReal L < sublevelVolume f := by
  obtain ⟨hstrict, f, hlim⟩ := h
  refine ⟨infimumLength_eq_of_lower_and_tendsto f ?_ hlim, hstrict⟩
  intro g hg
  exact (hstrict g hg).le

end

end Erdos1038
