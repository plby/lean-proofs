import Wikipedia.SmoothSixDPoincare.MorseCollapseSurjectivity
import Wikipedia.SmoothSixDPoincare.MorseAttachingTransport
import Wikipedia.SmoothSixDPoincare.MorseCollapseCoverMap

/-!
# The actual attaching-homology diagram across the native band bridge

Restrict the original ambient homeomorphism to the whole sublevels. Its
agreement with the level bridge identifies the transported attaching map
with the next original core boundary, including its sphere parametrization.
Vanishing above that next handle then makes the transported map surjective
onto the preceding upper-sublevel homology.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p q : M}
  (d : MorseSurgeryData E f p) (d' : MorseSurgeryData E f q)

def upperLevelInclusion : C(d.UpperLevel, {y : M // f y ≤ f p + d.radius ^ 2}) :=
  ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

def bandSublevelHomeomorph (T : M ≃ₜ M)
    (hT : T '' {y : M | f y ≤ f p + d.radius ^ 2} =
      {y : M | f y ≤ f q - d'.radius ^ 2}) :
    {y : M // f y ≤ f p + d.radius ^ 2} ≃ₜ
      {y : M // f y ≤ f q - d'.radius ^ 2} :=
  (T.image {y : M | f y ≤ f p + d.radius ^ 2}).trans (Homeomorph.setCongr hT)

variable (n : ℕ) [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
  (e : d.UpperLevel ≃ₜ d'.LowerLevel)

def transportedCoreBoundary :
    C(Hemisphere.Sphere n, {y : M // f y ≤ f p + d.radius ^ 2}) :=
  d.upperLevelInclusion.comp (d.transportedAttachingSphere d' n e)

omit [T2Space M] in
theorem bandSublevel_transportedCore (T : M ≃ₜ M)
    (hT : T '' {y : M | f y ≤ f p + d.radius ^ 2} =
      {y : M | f y ≤ f q - d'.radius ^ 2})
    (he : ∀ x : d.UpperLevel, (e x : M) = T x) :
    (d.bandSublevelHomeomorph d' T hT).toHomotopyEquiv.toFun.comp
      (d.transportedCoreBoundary d' n e) =
      d'.coreBoundaryMap.comp
        (SphereCoordinates.standardParametrization
          d'.chart.NegativeCoordinates n).toHomeomorph.toHomotopyEquiv.toFun := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change T (d.transportedAttachingSphere d' n e x : M) =
    (d'.surgery.attachingSphere
      (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x) : M)
  exact (he _).symm.trans
    (congrArg Subtype.val (d.transportedAttachingSphere_apply d' n e x))

theorem transportedCore_homology_surjective (hf : Continuous f) (T : M ≃ₜ M)
    (hT : T '' {y : M | f y ≤ f p + d.radius ^ 2} =
      {y : M | f y ≤ f q - d'.radius ^ 2})
    (he : ∀ x : d.UpperLevel, (e x : M) = T x) (k : ℕ) (hk : k ≠ 0)
    [Subsingleton (SingularHomology {y : M // f y ≤ f q + d'.radius ^ 2} k)] :
    Surjective (singularHomologyMap (d.transportedCoreBoundary d' n e) k) := by
  let H := homeomorphHomologyEquiv (d.bandSublevelHomeomorph d' T hT) k
  let S := homeomorphHomologyEquiv
    (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n).toHomeomorph k
  intro a
  obtain ⟨b, hb⟩ := d'.coreBoundaryHomology_surjective_of_upper hf k hk (H a)
  obtain ⟨c, hc⟩ := S.surjective b
  refine ⟨c, H.injective ?_⟩
  change singularHomologyMap (d.bandSublevelHomeomorph d' T hT).toHomotopyEquiv.toFun k
    (singularHomologyMap (d.transportedCoreBoundary d' n e) k c) = H a
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    d.bandSublevel_transportedCore d' n e T hT he, singularHomologyMap_comp]
  change d'.coreBoundaryHomologyMap k (S c) = H a
  rw [hc]
  exact hb

theorem attachingCollapse_transportedCore (hf : Continuous f) :
    d.attachingCollapse hf n (d.transportedAttachingSphere d' n e) =
      (d.upperCollapseMap hf).comp (d.transportedCoreBoundary d' n e) := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
