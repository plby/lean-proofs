import Wikipedia.HopfProblem.CuspNormalizationSheafReduced
import Wikipedia.HopfProblem.CuspNormalizationGermsBasic

/-!
# The actual ambient analytic-germ restriction image

An ambient analytic germ restricts to the actual neighbourhood-within
filter of the subset. The image is a literal subring of that actual
function-germ ring, independent of any categorical stalk presentation.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (S : Set E) (x : S)

/-- Restriction of a genuine ambient analytic germ to the actual subset
neighbourhood filter at the given point. -/
def restrictAnalyticGerm : Germs.AnalyticGerm x.val →+* Filter.Germ (𝓝[S] x.val) ℂ :=
  (Germs.compTendstoRingHom (id : E → E)
    (tendsto_id.mono_left nhdsWithin_le_nhds)).comp (Germs.analyticSubring x.val).subtype

@[simp] theorem restrictAnalyticGerm_ofAnalytic (f : E → ℂ)
    (hf : AnalyticAt ℂ f x.val) :
    restrictAnalyticGerm S x (Germs.ofAnalytic f hf) =
      (f : Filter.Germ (𝓝[S] x.val) ℂ) := rfl

/-- The literal ring image of the actual ambient analytic-germ restriction. -/
abbrev RestrictedAnalyticGermImage := (restrictAnalyticGerm S x).range

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
