import Wikipedia.HopfProblem.DegreeCollapseTripleChartSubmersion
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Generic affine parameters exclude all interior triple coincidences

The time and three source coordinates have dimension ten. The two target
differences have dimension twelve. Parametric regularity therefore forces
their common zero set to be empty, simultaneously on every chart in a
countable collection. No assertion about endpoint coincidences is made.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TripleParameters

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding ManifoldAffineSphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

theorem ae_no_triple_chart_zeros
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (a b c : SourceChart) (d : TargetChart 6 M) :
    ∀ᵐ p ∂μ, ∀ x : TripleCoordinates, (p, x) ∈ tripleDomain e r f hf a b c d →
      tripleChartDifference e r f a b c d (p, x) ≠ 0 := by
  have hreg := ParametricRegular.ae_parameters_on μ (tripleChartDifference e r f a b c d)
    (tripleDomain e r f hf a b c d) (contDiffOn_tripleChartDifference e r f hf a b c d)
    (fun q hq _ ↦ surjective_fderiv_tripleChartDifference e r f hf a b c d q hq)
  apply hreg.mono
  intro p hp x hx hz
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (f := (fderiv ℝ (fun y ↦ tripleChartDifference e r f a b c d (p, y)) x).toLinearMap)
    (hp x hx hz)
  norm_num [TripleCoordinates, Module.finrank_prod] at hdim

def TripleFreeInCharts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (S : Set SourceChart) (C : Set (TargetChart 6 M)) (p : Parameters e) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ C, ∀ x : TripleCoordinates,
    (p, x) ∈ tripleDomain e r f hf a b c d →
      tripleChartDifference e r f a b c d (p, x) ≠ 0

theorem ae_tripleFree_in_charts
    [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart 6 M)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, TripleFreeInCharts e r f hf S C p := by
  let : Countable S := hS.to_subtype
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ p ∂μ, ∀ a : S, ∀ b : S, ∀ c : S, ∀ d : C, ∀ x : TripleCoordinates,
      (p, x) ∈ tripleDomain e r f hf a.val b.val c.val d.val →
        tripleChartDifference e r f a.val b.val c.val d.val (p, x) ≠ 0 :=
    ae_all_iff.mpr fun a ↦ ae_all_iff.mpr fun b ↦ ae_all_iff.mpr fun c ↦
      ae_all_iff.mpr fun d ↦ ae_no_triple_chart_zeros e r f μ hf a.val b.val c.val d.val
  exact h.mono fun p hp a ha b hb c hc d hd ↦ hp ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩

end Wikipedia.HopfProblem.DegreeCollapse.TripleParameters
