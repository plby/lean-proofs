import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicFibreConstancy
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicCoverCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicDoubleCover
import Wikipedia.HopfProblem.HolomorphicMeromorphicUncountableBoxes

/-!
# Actual uncountable fibre constancy forces global double-cover equality

The canonical holomorphic representative of an arbitrary genuine
meromorphic function is expressed in the original regular coordinates.
A countable product-box argument supplies a nonempty box on which it
depends only on the base.  Equality of genuine fraction germs there
then propagates over the connected native double cover.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Metric UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  coverChartedSpace cover_isManifold doubleCoverChartedSpace doubleCover_isManifold

/-- Each actual constant regular fibre supplies a locally constant
fibre germ of the original coordinate representative. -/
theorem sectionCoordinates_locally_constant_on_good_fibres
    (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    ∀ a ∈ (fun z : TriangleRegularPoint => (z.val : ℂ)) '' constantSourceParameters g,
      ∃ v : ComplexPlane₂,
        (a, v) ∈ coord '' (holomorphicCoverDomain g : Set Cover) ∧
        (fun w => sectionCoordinates (holomorphicCoverDomain g) (coverRepresentative g) (a, w))
          =ᶠ[𝓝 v] fun _ =>
            sectionCoordinates (holomorphicCoverDomain g) (coverRepresentative g) (a, v) := by
  rintro a ⟨z, hz, rfl⟩
  obtain ⟨v, hv⟩ := hz.2
  refine ⟨v, ⟨(z, v), hv, rfl⟩, ?_⟩
  have hnear : ∀ᶠ w in 𝓝 v, (z, w) ∈ holomorphicCoverDomain g :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually
      ((holomorphicCoverDomain g).isOpen.mem_nhds hv)
  filter_upwards [hnear] with w hw
  change sectionCoordinates (holomorphicCoverDomain g) (coverRepresentative g) (coord (z, w)) =
    sectionCoordinates (holomorphicCoverDomain g) (coverRepresentative g) (coord (z, v))
  rw [sectionCoordinates_apply _ _ ⟨(z, w), hw⟩,
    sectionCoordinates_apply _ _ ⟨(z, v), hv⟩]
  exact coverRepresentative_fibre_constant g z hz w v hw hv

/-- From uncountably many constant genuine regular restrictions we
obtain an actual nonempty native holomorphic neighborhood with
fibre-independent values and the original meromorphic germs. -/
theorem exists_native_local_factor_of_uncountable
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (constantRegularFibres g).Countable) :
    ∃ (W : Opens Cover) (p : HolomorphicFunctionSheaf.Section IF Cover W) (_u : W),
      (∀ x : W, coverPullback g ⟨x.val, by trivial⟩ =
        HolomorphicMeromorphic.sectionGerm IF Cover W x p) ∧
      ∀ (z : TriangleRegularPoint) (v w : ComplexPlane₂)
        (hv : (z, v) ∈ W) (hw : (z, w) ∈ W),
        p ⟨(z, v), hv⟩ = p ⟨(z, w), hw⟩ := by
  let U := holomorphicCoverDomain g
  let p := coverRepresentative g
  let F := sectionCoordinates U p
  obtain ⟨a, b, r, hr, hsub, hconstant⟩ :=
    HolomorphicMeromorphicUncountableBoxes.exists_fibre_constant_ball_product
      (coord_image_isOpen U) (sectionCoordinates_analyticOnNhd U p)
      (complex_constantSourceParameters_uncountable g hg)
      (sectionCoordinates_locally_constant_on_good_fibres g)
  let B : Opens Model := ⟨ball a r ×ˢ ball b r, isOpen_ball.prod isOpen_ball⟩
  let W : Opens Cover := ⟨coord ⁻¹' B, B.isOpen.preimage coord_continuous⟩
  have hWU : W ≤ U := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hsub hx
    exact coord_injective he ▸ hy
  have hab : (a, b) ∈ ball a r ×ˢ ball b r := ⟨mem_ball_self hr, mem_ball_self hr⟩
  obtain ⟨u, _huU, hucoord⟩ := hsub hab
  have huW : u ∈ W := by
    change coord u ∈ B
    rw [hucoord]
    exact ⟨mem_ball_self hr, mem_ball_self hr⟩
  let pW := HolomorphicFunctionSheaf.restrictionAlgHom IF Cover hWU p
  refine ⟨W, pW, ⟨u, huW⟩, ?_, ?_⟩
  · intro x
    exact (coverRepresentative_germ g (Set.inclusion hWU x)).trans
      (HolomorphicMeromorphic.sectionGerm_restrict IF Cover hWU x p).symm
  · intro z v w hv hw
    have hvB : ((z.val : ℂ), v) ∈ ball a r ×ˢ ball b r := hv
    have hwB : ((z.val : ℂ), w) ∈ ball a r ×ˢ ball b r := hw
    calc
      pW ⟨(z, v), hv⟩ = F (coord (z, v)) :=
        (sectionCoordinates_apply U p ⟨(z, v), hWU hv⟩).symm
      _ = F (coord (z, w)) := hconstant (z.val : ℂ) hvB.1 v hvB.2 w hwB.2
      _ = pW ⟨(z, w), hw⟩ := sectionCoordinates_apply U p ⟨(z, w), hWU hw⟩

/-- The two original period-vector pullbacks of an arbitrary genuine
global meromorphic function agree whenever uncountably many actual
regular fibres have constant restrictions. -/
theorem double_cover_eq_of_uncountably_many_constant_fibres
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (constantRegularFibres g).Countable) :
    leftPullback (coverPullback g) = rightPullback (coverPullback g) := by
  obtain ⟨U, p, u, hp, hconstant⟩ := exists_native_local_factor_of_uncountable g hg
  exact leftPullback_eq_rightPullback_of_local_factor (coverPullback g) U p u hp hconstant

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
