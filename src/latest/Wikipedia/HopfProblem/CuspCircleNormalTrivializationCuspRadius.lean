import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspSmooth
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCompactSubtype

/-!
# A uniform injective round normal neighborhood in the actual threefold

The map is the original quotient-and-inclusion map. Local invertibility
and injectivity on its compact zero section give a single positive
radius on which it is injective. We then use the Euclidean sum of the
two squared complex norms, rather than the product maximum norm, to
choose a round normal domain.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.space_t2Space

/-- The original local quotient map is injective on one uniform normal neighborhood. -/
theorem exists_injective_normal_radius :
    ∃ r : ℝ, 0 < r ∧
      (univ : Set RiemannSphere) ×ˢ Metric.ball (0 : Fibre) r ⊆
        (smallNormalProduct : Set (RiemannSphere × Fibre)) ∧
      InjOn globalProductMap
        {x : smallNormalProduct | x.val.2 ∈ Metric.ball (0 : Fibre) r} :=
  exists_pos_injOn_open_subtype_prod_ball_of_isLocalHomeomorph
    zero_mem_smallNormalProduct globalProductMap_isLocalHomeomorph
    globalProductMap_injective_zeroSection

/-- A positive radius justified by the actual compact zero section and actual local quotient map. -/
def injectiveRadius : ℝ := Classical.choose exists_injective_normal_radius

theorem injectiveRadius_pos : 0 < injectiveRadius :=
  (Classical.choose_spec exists_injective_normal_radius).1

theorem injectiveRadius_product_subset :
    (univ : Set RiemannSphere) ×ˢ Metric.ball (0 : Fibre) injectiveRadius ⊆
      (smallNormalProduct : Set (RiemannSphere × Fibre)) :=
  (Classical.choose_spec exists_injective_normal_radius).2.1

theorem globalProductMap_injOn_radius :
    InjOn globalProductMap
      {x : smallNormalProduct | x.val.2 ∈ Metric.ball (0 : Fibre) injectiveRadius} :=
  (Classical.choose_spec exists_injective_normal_radius).2.2

/-- A round Euclidean ball is contained in the same-radius maximum-norm product ball. -/
theorem norm_lt_of_radiusSq_lt_sq {r : ℝ} (hr : 0 < r) {v : Fibre}
    (hv : radiusSq v < r ^ 2) : ‖v‖ < r := by
  simp only [radiusSq, Complex.normSq_eq_norm_sq] at hv
  rw [Prod.norm_def, max_lt_iff]
  constructor
  · nlinarith only [hr, hv, sq_nonneg ‖v.2‖, norm_nonneg v.1]
  · nlinarith only [hr, hv, sq_nonneg ‖v.1‖, norm_nonneg v.2]

/-- The chosen domain uses the literal Euclidean round normal radius. -/
def roundNormalProduct : TopologicalSpace.Opens (RiemannSphere × Fibre) :=
  ⟨{p | radiusSq p.2 < injectiveRadius ^ 2},
    isOpen_lt ((contDiff_radiusSq (n := ω)).continuous.comp continuous_snd) continuous_const⟩

theorem roundNormalProduct_subset_small :
    (roundNormalProduct : Set (RiemannSphere × Fibre)) ⊆ smallNormalProduct := by
  intro p hp
  apply injectiveRadius_product_subset
  refine ⟨mem_univ p.1, ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact norm_lt_of_radiusSq_lt_sq injectiveRadius_pos hp

theorem zero_mem_roundNormalProduct (p : RiemannSphere) :
    (p, (0 : Fibre)) ∈ roundNormalProduct := by
  change radiusSq (0 : Fibre) < injectiveRadius ^ 2
  rw [radiusSq_zero]
  exact sq_pos_of_pos injectiveRadius_pos

/-- The literal inclusion of the round product into the original quotient-map domain. -/
def roundToSmall (p : roundNormalProduct) : smallNormalProduct :=
  ⟨p.val, roundNormalProduct_subset_small p.property⟩

@[simp] theorem roundToSmall_coe (p : roundNormalProduct) :
    (roundToSmall p : RiemannSphere × Fibre) = p := rfl

/-- The unchanged quotient map on the round normal domain. -/
def roundProductMap : roundNormalProduct → Threefold.Space := globalProductMap ∘ roundToSmall

theorem roundProductMap_injective : Function.Injective roundProductMap := by
  intro p q hpq
  have hp : (roundToSmall p).val.2 ∈ Metric.ball (0 : Fibre) injectiveRadius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_lt_of_radiusSq_lt_sq injectiveRadius_pos p.property
  have hq : (roundToSmall q).val.2 ∈ Metric.ball (0 : Fibre) injectiveRadius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_lt_of_radiusSq_lt_sq injectiveRadius_pos q.property
  apply Subtype.ext
  exact congrArg (fun x : smallNormalProduct => x.val)
    (globalProductMap_injOn_radius hp hq hpq)

theorem roundProductMap_zeroSection (p : RiemannSphere) :
    roundProductMap ⟨(p, 0), zero_mem_roundNormalProduct p⟩ =
      CuspGeometry.doubleCurveParametrization 1 p :=
  globalProductMap_zeroSection p

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
