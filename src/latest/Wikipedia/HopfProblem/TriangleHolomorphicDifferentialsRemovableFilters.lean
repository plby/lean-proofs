import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Punctured-neighborhood images of nonconstant analytic germs

A nonconstant complex analytic germ maps the punctured-neighborhood
filter exactly onto the punctured-neighborhood filter at its value.
The two inequalities combine isolated zeros with the local open-mapping
theorem. Finite analytic order provides a convenient nonconstancy test.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable

/-- A nonconstant complex analytic germ maps punctured neighborhoods
exactly onto the punctured-neighborhood filter at its value. -/
theorem map_nhdsNE_eq_of_analytic_nonconstant {g : ℂ → ℂ} {a : ℂ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) :
    Filter.map g (𝓝[≠] a) = 𝓝[≠] (g a) := by
  apply le_antisymm (hg.map_nhdsNE hnc)
  have hopen : 𝓝 (g a) ≤ Filter.map g (𝓝 a) :=
    hg.eventually_constant_or_nhds_le_map_nhds.resolve_left (fun h =>
      hnc (eventuallyConst_iff_exists_eventuallyEq.mpr ⟨g a, h⟩))
  have hsub : g ⁻¹' ({g a}ᶜ : Set ℂ) ⊆ ({a}ᶜ : Set ℂ) := by
    intro z hz
    change g z ≠ g a at hz
    change z ≠ a
    exact fun h => hz (congrArg g h)
  change 𝓝 (g a) ⊓ 𝓟 ({g a}ᶜ : Set ℂ) ≤
    Filter.map g (𝓝 a ⊓ 𝓟 ({a}ᶜ : Set ℂ))
  calc
    𝓝 (g a) ⊓ 𝓟 ({g a}ᶜ : Set ℂ) ≤
        Filter.map g (𝓝 a) ⊓ 𝓟 ({g a}ᶜ : Set ℂ) := inf_le_inf_right _ hopen
    _ = Filter.map g (𝓝 a ⊓ 𝓟 (g ⁻¹' ({g a}ᶜ : Set ℂ))) :=
      map_inf_principal_preimage.symm
    _ ≤ Filter.map g (𝓝 a ⊓ 𝓟 ({a}ᶜ : Set ℂ)) :=
      Filter.map_mono (inf_le_inf_left _ (principal_mono.mpr hsub))

/-- The same filter equality with a separately named target value. -/
theorem map_nhdsNE_eq_of_analytic_nonconstant_of_eq {g : ℂ → ℂ} {a : ℂ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a))
    (b : ℂ) (hga : g a = b) : Filter.map g (𝓝[≠] a) = 𝓝[≠] b := by
  simpa only [hga] using map_nhdsNE_eq_of_analytic_nonconstant hg hnc

/-- A finite order for the centered germ rules out local constancy. -/
theorem not_eventuallyConst_of_finite_order {g : ℂ → ℂ} {a : ℂ}
    (horder : analyticOrderAt (fun z => g z - g a) a ≠ ⊤) :
    ¬ Filter.EventuallyConst g (𝓝 a) :=
  fun hc => horder (eventuallyConst_iff_analyticOrderAt_sub_eq_top.mp hc)

/-- Finite analytic order supplies the punctured-neighborhood image equality. -/
theorem map_nhdsNE_eq_of_finite_order {g : ℂ → ℂ} {a : ℂ}
    (hg : AnalyticAt ℂ g a)
    (horder : analyticOrderAt (fun z => g z - g a) a ≠ ⊤) :
    Filter.map g (𝓝[≠] a) = 𝓝[≠] (g a) :=
  map_nhdsNE_eq_of_analytic_nonconstant hg (not_eventuallyConst_of_finite_order horder)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable
