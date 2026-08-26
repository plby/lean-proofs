import ErdosProblems.Erdos1038.HighKPlatformDeficitAssembly
import ErdosProblems.Erdos1038.LowerCaseSplit
import ErdosProblems.Erdos1038.LowerReduction

/-!
# Bridge from the high-ratio platform case to the sharp lower theorem

The low-ratio and pure-endpoint cases are already closed by
`LowerCaseSplit`.  This file isolates the exact remaining global assertion:
the endpoint-normalized configurations with residual ratio `k > 29/20`.
Once the platform/block argument proves that assertion, the strict lower
bound and `SharpLowerContent` follow without further analytic work.
-/

set_option warningAsError false

open scoped ENNReal
open Polynomial

namespace Erdos1038

noncomputable section

/-- The sole remaining configuration-level lower assertion after the
existing elementary case split. -/
def HighKEndpointStrictLowerBound : Prop :=
  ∀ (g : Polynomial ℝ) (h : EndpointNormalizationHypotheses g),
    endpointResidualRoots h.normalizedPolynomial ≠ 0 →
      29 / 20 < normalizedEndpointResidualRatio h →
        ENNReal.ofReal L < sublevelVolume g

theorem strict_lower_of_highKEndpointStrictLowerBound
    (hLtwo : L < 2) (hhigh : HighKEndpointStrictLowerBound) :
    ∀ f : Polynomial ℝ, IsAdmissible f →
      ENNReal.ofReal L < sublevelVolume f := by
  intro f hf
  have hOfRealTwo : ENNReal.ofReal L < ENNReal.ofReal 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 2)).2 hLtwo
  rcases admissible_low_or_high_endpoint_split hf with hlow | hhighCase
  · exact hOfRealTwo.trans_le hlow
  · rcases hhighCase with ⟨g, h, hvolume, hresidual, hratio⟩
    exact (hhigh g h hresidual hratio).trans_le hvolume

/-- A recovering sequence together with the high-`k` endpoint bound proves
the complete substantive lower content. -/
theorem sharpLowerContent_of_highKEndpointStrictLowerBound
    (hLtwo : L < 2) (hhigh : HighKEndpointStrictLowerBound)
    (hrecovery : ∃ f : ℕ → AdmissiblePolynomial,
      Filter.Tendsto (fun n ↦ sublevelVolume (f n).1) Filter.atTop
        (nhds (ENNReal.ofReal L))) :
    SharpLowerContent := by
  exact ⟨strict_lower_of_highKEndpointStrictLowerBound hLtwo hhigh,
    hrecovery⟩

/-- Direct final lower-clause interface for the platform/high-`k` route. -/
theorem mainTheorem_lower_clauses_of_highKEndpointStrictLowerBound
    (hLtwo : L < 2) (hhigh : HighKEndpointStrictLowerBound)
    (hrecovery : ∃ f : ℕ → AdmissiblePolynomial,
      Filter.Tendsto (fun n ↦ sublevelVolume (f n).1) Filter.atTop
        (nhds (ENNReal.ofReal L))) :
    infimumLength = ENNReal.ofReal L ∧
      ∀ f : Polynomial ℝ, IsAdmissible f →
        ENNReal.ofReal L < sublevelVolume f := by
  apply mainTheorem_lower_clauses_of_sharpLowerContent
  exact sharpLowerContent_of_highKEndpointStrictLowerBound
    hLtwo hhigh hrecovery

end

end Erdos1038
