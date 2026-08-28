import Wikipedia.HopfProblem.HolomorphicPicardNativeGaugeSmooth
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement

/-!
# Genuine Čech coboundaries produce actual native analytic isomorphisms

The scalar gauge equation is derived by evaluating the actual sheaf
restrictions in a Čech coboundary equation. Thus equality of actual Čech
classes on any common covering refinement gives an actual analytic,
fibrewise complex-linear isomorphism of the original native bundles.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open HolomorphicExponentialSheaf PeriodTorusLineBundleClassificationNative
  HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.Cech

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (V W : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W] [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]
    [ContMDiffVectorBundle ω ℂ V I] [ContMDiffVectorBundle ω ℂ W I]
    {ι : Type} (U : ι → Opens M) (r s : ι → M)
    (hV : ∀ i, U i ≤ nativeCover M V (r i))
    (hW : ∀ i, U i ≤ nativeCover M W (s i))
    (b : ZeroCochain (unitsSheaf I M) U)
    (hb : refinement (unitsSheaf I M) r hV (nativeCocycle I M V) -
      refinement (unitsSheaf I M) s hW (nativeCocycle I M W) =
        coboundary (unitsSheaf I M) U b)

include hb in
/-- The actual categorical section equation gives the required original
native scalar gauge identity at every point of every overlap. -/
theorem gauge_pointwise_of_refinement_sub_eq (i j : ι) (x : M)
    (hi : x ∈ U i) (hj : x ∈ U j) :
    unitSectionEval (b j) ⟨x, hj⟩ * (scalarTransition V (r i) (r j) x : ℂ) =
      (scalarTransition W (s i) (s j) x : ℂ) * unitSectionEval (b i) ⟨x, hi⟩ := by
  have hs := congrArg (fun c : CechOneCocycle (unitsSheaf I M) U => c.value i j) hb
  rw [sub_value, refinement_value, refinement_value, coboundary_value] at hs
  have ht := congrArg (fun u : UnitSection I M (U i ⊓ U j) =>
    unitSectionEval u ⟨x, ⟨hi, hj⟩⟩) hs
  change unitSectionEval
      (unitRestriction I M (inf_le_inf (hV i) (hV j))
          ((nativeCocycle I M V).value (r i) (r j)) -
        unitRestriction I M (inf_le_inf (hW i) (hW j))
          ((nativeCocycle I M W).value (s i) (s j))) ⟨x, ⟨hi, hj⟩⟩ =
    unitSectionEval
      (unitRestriction I M (U := U i ⊓ U j) (V := U i) inf_le_left (b i) -
        unitRestriction I M (U := U i ⊓ U j) (V := U j) inf_le_right (b j))
      ⟨x, ⟨hi, hj⟩⟩ at ht
  simp only [sub_eq_add_neg, unitSectionEval_add, unitSectionEval_neg] at ht
  change (scalarTransition V (r i) (r j) x : ℂ) *
      (scalarTransition W (s i) (s j) x : ℂ)⁻¹ =
        unitSectionEval (b i) ⟨x, hi⟩ * (unitSectionEval (b j) ⟨x, hj⟩)⁻¹ at ht
  have hdiv : (scalarTransition V (r i) (r j) x : ℂ) /
      (scalarTransition W (s i) (s j) x : ℂ) =
        unitSectionEval (b i) ⟨x, hi⟩ / unitSectionEval (b j) ⟨x, hj⟩ := by
    simpa only [div_eq_mul_inv] using ht
  have hmul := (div_eq_div_iff (scalarTransition W (s i) (s j) x).ne_zero
    (unitSectionEval_ne_zero (b j) ⟨x, hj⟩)).mp hdiv
  exact (mul_comm _ _).trans (hmul.trans (mul_comm _ _))

variable (hcover : ∀ x : M, ∃ i, x ∈ U i)

/-- A genuine unit-sheaf coboundary on a common refinement determines a
true analytic isomorphism of the original native holomorphic bundles. -/
def analyticBundleIsoOfCocycleGauge : AnalyticBundleIso I V W :=
  NativeGauge.analyticBundleIso I M V W U r s hV hW b
    (gauge_pointwise_of_refinement_sub_eq I M V W U r s hV hW b hb) hcover

theorem analyticBundleIsoOfCocycleGauge_coordinate (i : ι) (x : M)
    (hx : x ∈ U i) (v : V x) :
    (nativeTriv W (s i)
      ((analyticBundleIsoOfCocycleGauge I M V W U r s hV hW b hb hcover).diffeomorph
        ⟨x, v⟩)).2 =
      unitSectionEval (b i) ⟨x, hx⟩ * (nativeTriv V (r i) ⟨x, v⟩).2 :=
  NativeGauge.analyticBundleIso_coordinate I M V W U r s hV hW b
    (gauge_pointwise_of_refinement_sub_eq I M V W U r s hV hW b hb) hcover i x hx v

include hcover in
/-- Equality of the actual Čech classes on any common covering refinement
implies a genuine original native analytic bundle isomorphism. -/
theorem nonempty_analyticBundleIso_of_refinement_class_eq
    (h : classOf (unitsSheaf I M) U
        (refinement (unitsSheaf I M) r hV (nativeCocycle I M V)) =
      classOf (unitsSheaf I M) U
        (refinement (unitsSheaf I M) s hW (nativeCocycle I M W))) :
    Nonempty (AnalyticBundleIso I V W) := by
  obtain ⟨b, hb⟩ := (class_eq_class_iff (unitsSheaf I M) U _ _).mp h
  exact ⟨analyticBundleIsoOfCocycleGauge I M V W U r s hV hW b
    (cocycle_ext (unitsSheaf I M) U (fun i j => (hb i j).symm)) hcover⟩

end Wikipedia.HopfProblem.HolomorphicPicardNative
