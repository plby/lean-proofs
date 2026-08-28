import Wikipedia.NoExoticSixSphere.CompactRetractionPairDomain
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Regular double points for the actual compact-image perturbation

Parametric Sard applies to the genuine image-difference equations on the
coupled open pair domains. One almost-everywhere parameter set works for
all charts in a countable collection. Pairs with both cutoffs zero remain
outside the claim and require the prescribed collar's injectivity.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector d → M) (χ : Vector d → ℝ)
  (U : TopologicalSpace.Opens (Vector d)) (hf : ContMDiffOn (𝓡 d) (𝓡 n) ∞ f U)
  (hχ : ContDiff ℝ ∞ χ) (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)

theorem surjective_fderiv_chartDifference_parameter
    (q : Parameters d e × (Vector d × Vector d))
    (hq : q ∈ activePairDomain e r f χ U hf hχ c) :
    Surjective (fderiv ℝ
      (fun p : Parameters d e ↦ chartDifference e r f χ c (p, q.2)) q.1) := by
  have hleft := hq.1.1.1
  have hright := hq.1.1.2
  exact surjective_fderiv_chart_pair_difference_parameter e r f χ c q.1 q.2.1 q.2.2
    hq.1.2 hq.2 hleft.1.2 hright.1.2 hleft.2 hright.2

theorem surjective_fderiv_chartDifference
    (q : Parameters d e × (Vector d × Vector d))
    (hq : q ∈ activePairDomain e r f χ U hf hχ c) :
    Surjective (fderiv ℝ (chartDifference e r f χ c) q) := by
  have hp := surjective_fderiv_chartDifference_parameter e r f χ U hf hχ c q hq
  have hD := ((contDiffOn_chartDifference e r f χ U hf hχ c).contDiffAt
    ((pairDomain e r f χ U hf hχ c).isOpen.mem_nhds hq.1)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters d e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters d e) (Vector d × Vector d)) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters d e ↦ chartDifference e r f χ c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro w
  obtain ⟨v, hv⟩ := hp w
  exact ⟨(v, 0), hv⟩

theorem ae_regular_chart_double_points [MeasurableSpace (Parameters d e)]
    [BorelSpace (Parameters d e)] (μ : Measure (Parameters d e)) [IsAddHaarMeasure μ] :
    ∀ᵐ p ∂μ, ∀ x : Vector d × Vector d,
      (p, x) ∈ activePairDomain e r f χ U hf hχ c → chartDifference e r f χ c (p, x) = 0 →
        Surjective (fderiv ℝ (fun y ↦ chartDifference e r f χ c (p, y)) x) :=
  ParametricRegular.ae_parameters_on μ (chartDifference e r f χ c)
    (activePairDomain e r f χ U hf hχ c)
    ((contDiffOn_chartDifference e r f χ U hf hχ c).mono inter_subset_left)
    (fun q hq _ ↦ surjective_fderiv_chartDifference e r f χ U hf hχ c q hq)

theorem ae_regular_double_points_in_charts [MeasurableSpace (Parameters d e)]
    [BorelSpace (Parameters d e)] (μ : Measure (Parameters d e)) [IsAddHaarMeasure μ]
    (C : Set (PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, ∀ c ∈ C, ∀ x : Vector d × Vector d,
      (p, x) ∈ activePairDomain e r f χ U hf hχ c → chartDifference e r f χ c (p, x) = 0 →
        Surjective (fderiv ℝ (fun y ↦ chartDifference e r f χ c (p, y)) x) := by
  let : Countable C := hC.to_subtype
  have ha : ∀ᵐ p ∂μ, ∀ c : C, ∀ x : Vector d × Vector d,
      (p, x) ∈ activePairDomain e r f χ U hf hχ c.val →
      chartDifference e r f χ c.val (p, x) = 0 →
        Surjective (fderiv ℝ (fun y ↦ chartDifference e r f χ c.val (p, y)) x) :=
    ae_all_iff.mpr fun c ↦ ae_regular_chart_double_points e r f χ U hf hχ c.val μ
  exact ha.mono fun p hp c hc ↦ hp ⟨c, hc⟩

def RegularDoublePointsOn (g : Vector d → M) (U A : Set (Vector d))
    (C : Set (PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)) : Prop :=
  ∀ c ∈ C, ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (x ∈ A ∨ y ∈ A) →
    g x ∈ c.source → g y ∈ c.source → g x = g y →
      Surjective (fderiv ℝ (fun z : Vector d × Vector d ↦ c (g z.1) - c (g z.2)) (x, y))

theorem RegularDoublePointsOn.of_injOn_compl {g : Vector d → M} {U A : Set (Vector d)}
    {C : Set (PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)}
    (h : RegularDoublePointsOn g U A C) (hi : InjOn g (U \ A)) :
    RegularDoublePointsOn g U U C := by
  intro c hc x hx y hy hxy _ hcx hcy heq
  apply h c hc x hx y hy hxy _ hcx hcy heq
  by_contra hn
  exact hxy (hi ⟨hx, fun ha ↦ hn (Or.inl ha)⟩ ⟨hy, fun ha ↦ hn (Or.inr ha)⟩ heq)

theorem regularDoublePointsOn_of_chartwise
    (C : Set (PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)) (p : Parameters d e)
    (hdom : ∀ x ∈ U, ambient e f χ p x ∈ r.domain)
    (hreg : ∀ c ∈ C, ∀ x : Vector d × Vector d,
      (p, x) ∈ activePairDomain e r f χ U hf hχ c → chartDifference e r f χ c (p, x) = 0 →
        Surjective (fderiv ℝ (fun y ↦ chartDifference e r f χ c (p, y)) x)) :
    RegularDoublePointsOn (map e r f χ p) U {x | χ x ≠ 0} C := by
  intro c hc x hx y hy hxy hactive hcx hcy heq
  have hleft : (p, x) ∈ chartDomain e r f χ U hf hχ c := ⟨⟨hx, hdom x hx⟩, hcx⟩
  have hright : (p, y) ∈ chartDomain e r f χ U hf hχ c := ⟨⟨hy, hdom y hy⟩, hcy⟩
  apply hreg c hc (x, y) ⟨⟨⟨hleft, hright⟩, hxy⟩, hactive⟩
  change c (map e r f χ p x) - c (map e r f χ p y) = 0
  rw [heq, sub_self]

end NoExoticSixSphere.CompactRetractionAffineFamily
