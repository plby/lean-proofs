import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovableFilters
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovableGrowth

/-!
# Genuine removability descended through a finite analytic branch

The exact punctured-filter image of a nonconstant analytic germ transfers
limits and bounds from the actual pullback. A punctured analytic scalar
therefore extends by the prescribed pullback value when the pullback has
a continuous or analytic extension. Vanishing of the pulled-back local-
parameter product also suffices, by the weak removable-singularity theorem.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable

/-- Any limit descends through the actual punctured-filter equality. -/
theorem tendsto_of_comp_analytic_nonconstant {Y : Type*} {f : ℂ → Y} {l : Filter Y}
    {g : ℂ → ℂ} {a b : ℂ} (hg : AnalyticAt ℂ g a)
    (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (ht : Tendsto (f ∘ g) (𝓝[≠] a) l) : Tendsto f (𝓝[≠] b) l := by
  rw [← map_nhdsNE_eq_of_analytic_nonconstant_of_eq hg hnc b hga, tendsto_map'_iff]
  exact ht

theorem tendsto_of_comp_finite_order {Y : Type*} {f : ℂ → Y} {l : Filter Y}
    {g : ℂ → ℂ} {a b : ℂ} (hg : AnalyticAt ℂ g a)
    (horder : analyticOrderAt (fun z => g z - g a) a ≠ ⊤) (hga : g a = b)
    (ht : Tendsto (f ∘ g) (𝓝[≠] a) l) : Tendsto f (𝓝[≠] b) l :=
  tendsto_of_comp_analytic_nonconstant hg (not_eventuallyConst_of_finite_order horder) hga ht

/-- Eventual statements, including local bounds, descend through the same branch. -/
theorem eventually_of_comp_analytic_nonconstant {P : ℂ → Prop}
    {g : ℂ → ℂ} {a b : ℂ} (hg : AnalyticAt ℂ g a)
    (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (hP : ∀ᶠ z in 𝓝[≠] a, P (g z)) : ∀ᶠ w in 𝓝[≠] b, P w := by
  rw [← map_nhdsNE_eq_of_analytic_nonconstant_of_eq hg hnc b hga]
  exact hP

/-- A continuous extension of the actual pullback prescribes the unique
downstairs punctured limit, independently of the original value at `b`. -/
theorem tendsto_of_continuous_pullback {F G g : ℂ → ℂ} {a b : ℂ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (hG : ContinuousAt G a) (hcomp : F ∘ g =ᶠ[𝓝[≠] a] G) :
    Tendsto F (𝓝[≠] b) (𝓝 (G a)) :=
  tendsto_of_comp_analytic_nonconstant hg hnc hga
    ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' hcomp.symm)

theorem analyticAt_update_of_continuous_pullback {F G g : ℂ → ℂ} {a b : ℂ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (hF : ∀ᶠ w in 𝓝[≠] b, AnalyticAt ℂ F w)
    (hG : ContinuousAt G a) (hcomp : F ∘ g =ᶠ[𝓝[≠] a] G) :
    AnalyticAt ℂ (Function.update F b (G a)) b :=
  analyticAt_update_of_tendsto hF (tendsto_of_continuous_pullback hg hnc hga hG hcomp)

/-- An analytic extension of the pullback makes the downstairs puncture
removable, with the exact value supplied by the upstairs germ. -/
theorem analyticAt_update_of_analytic_pullback {F G g : ℂ → ℂ} {a b : ℂ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (hF : ∀ᶠ w in 𝓝[≠] b, AnalyticAt ℂ F w)
    (hG : AnalyticAt ℂ G a) (hcomp : F ∘ g =ᶠ[𝓝[≠] a] G) :
    AnalyticAt ℂ (Function.update F b (G a)) b :=
  analyticAt_update_of_continuous_pullback hg hnc hga hF hG.continuousAt hcomp

theorem exists_analytic_extension_of_analytic_pullback {F G g : ℂ → ℂ} {a b : ℂ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (hF : ∀ᶠ w in 𝓝[≠] b, AnalyticAt ℂ F w)
    (hG : AnalyticAt ℂ G a) (hcomp : F ∘ g =ᶠ[𝓝[≠] a] G) :
    ∃ Fext : ℂ → ℂ, AnalyticAt ℂ Fext b ∧
      Fext =ᶠ[𝓝[≠] b] F ∧ Fext b = G a :=
  exists_analytic_extension_of_tendsto hF
    (tendsto_of_continuous_pullback hg hnc hga hG.continuousAt hcomp)

theorem exists_analytic_extension_of_finite_order_pullback {F G g : ℂ → ℂ} {a b : ℂ}
    (hg : AnalyticAt ℂ g a)
    (horder : analyticOrderAt (fun z => g z - g a) a ≠ ⊤) (hga : g a = b)
    (hF : ∀ᶠ w in 𝓝[≠] b, AnalyticAt ℂ F w)
    (hG : AnalyticAt ℂ G a) (hcomp : F ∘ g =ᶠ[𝓝[≠] a] G) :
    ∃ Fext : ℂ → ℂ, AnalyticAt ℂ Fext b ∧
      Fext =ᶠ[𝓝[≠] b] F ∧ Fext b = G a :=
  exists_analytic_extension_of_analytic_pullback hg
    (not_eventuallyConst_of_finite_order horder) hga hF hG hcomp

/-- Even a merely bounded analytic pullback gives an actual removable extension. -/
theorem exists_analytic_extension_of_bounded_pullback {F g : ℂ → ℂ} {a b : ℂ} {M : ℝ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (hF : ∀ᶠ w in 𝓝[≠] b, AnalyticAt ℂ F w)
    (hbound : ∀ᶠ z in 𝓝[≠] a, ‖F (g z)‖ ≤ M) :
    ∃ Fext : ℂ → ℂ, AnalyticAt ℂ Fext b ∧
      Fext =ᶠ[𝓝[≠] b] F ∧ Fext b = limUnder (𝓝[≠] b) F :=
  exists_analytic_extension_of_eventually_bounded hF
    (eventually_of_comp_analytic_nonconstant hg hnc hga hbound)

/-- Vanishing of the pulled-back local-parameter product gives the actual
finite downstairs limit. No factorization of the numerator is required. -/
theorem tendsto_limUnder_of_sub_mul_pullback_tendsto_zero {F g : ℂ → ℂ} {a b : ℂ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (hF : ∀ᶠ w in 𝓝[≠] b, AnalyticAt ℂ F w)
    (ht : Tendsto (fun z => (g z - b) * F (g z)) (𝓝[≠] a) (𝓝 0)) :
    Tendsto F (𝓝[≠] b) (𝓝 (limUnder (𝓝[≠] b) F)) :=
  tendsto_limUnder_of_sub_mul_tendsto_zero hF
    (tendsto_of_comp_analytic_nonconstant hg hnc hga ht)

theorem analyticAt_update_limUnder_of_sub_mul_pullback_tendsto_zero
    {F g : ℂ → ℂ} {a b : ℂ}
    (hg : AnalyticAt ℂ g a) (hnc : ¬ Filter.EventuallyConst g (𝓝 a)) (hga : g a = b)
    (hF : ∀ᶠ w in 𝓝[≠] b, AnalyticAt ℂ F w)
    (ht : Tendsto (fun z => (g z - b) * F (g z)) (𝓝[≠] a) (𝓝 0)) :
    AnalyticAt ℂ (Function.update F b (limUnder (𝓝[≠] b) F)) b :=
  analyticAt_update_of_tendsto hF
    (tendsto_limUnder_of_sub_mul_pullback_tendsto_zero hg hnc hga hF ht)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable
