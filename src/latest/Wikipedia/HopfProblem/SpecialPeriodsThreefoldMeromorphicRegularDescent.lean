import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicUncountable
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicLocalBaseFractions
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicLocalDescent
import Wikipedia.HopfProblem.HolomorphicMeromorphicDescentOnOpen

/-!
# Genuine meromorphic descent over the full actual regular sphere locus

For an arbitrary genuine global meromorphic function whose restrictions
are constant on uncountably many regular fibres, the original double
cover is fibre-independent. Every local fraction then supplies an
actual base fraction. Native local biholomorphic stalk transport and
connectedness of the full inverse images give descent near every
regular base value, and the original sheaf glues these fractions.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open MeromorphicRegularCover HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  coverChartedSpace cover_isManifold doubleCoverChartedSpace doubleCover_isManifold

/-- The coordinate factor map used by the local product fraction
construction is exactly the original free-base coordinate projection. -/
theorem baseCoordinateMap_eq_freeBase_comp_projection :
    baseCoordinateMap = freeBaseCoordinateMap.comp coverBaseProjection :=
  ContMDiffMap.ext fun _ => rfl

/-- Genuine local descent holds at every regular value, with no local
fraction, analytic factor, or base-extension hypothesis supplied. -/
theorem meromorphicallyDescendsNear_regular
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (constantRegularFibres g).Countable)
    (b : RiemannSphere) (hb : b ∈ sphereRegularPatch) :
    MeromorphicallyDescendsNear g b := by
  obtain ⟨x, hxb⟩ := projectionSphere_surjective b
  have hxr : x ∈ regularLocus :=
    (mem_regularLocus_iff_sphere x).mpr (hxb.symm ▸ hb)
  obtain ⟨u, hu⟩ := exists_toThreefold_eq x hxr
  obtain ⟨a, ha⟩ := exists_base_germ_of_double_cover_eq (coverPullback g)
    (double_cover_eq_of_uncountably_many_constant_fibres g hg) u
  have ha' : HolomorphicMeromorphic.germPullback IF I₁
      (freeBaseCoordinateMap.comp coverBaseProjection)
      (freeBaseCoordinateMap_isOpenMap.comp coverBaseProjection_isOpenMap) u a =
        coverPullback g ⟨u, by trivial⟩ := by
    exact ha
  obtain ⟨U, huU, s, hs⟩ := exists_local_sphere_section_of_coordinate_germ g u a ha'
  have h := meromorphicallyDescendsNear_of_local_germ g U s (toThreefold u) huU hs
  simpa only [hu, hxb] using h

/-- The arbitrary original meromorphic function is the genuine pullback
of a unique native section on the whole regular sphere domain. -/
theorem existsUnique_regular_sphere_descent
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (constantRegularFibres g).Countable) :
    ∃! s : HolomorphicMeromorphic.Section I₁ RiemannSphere sphereRegularPatch,
      HolomorphicMeromorphic.pullbackSection IF I₁ sphereProjection
        sphereProjection_isOpenMap sphereRegularPatch s =
          HolomorphicMeromorphic.restrict IF Threefold.Space (show
            HolomorphicMeromorphic.pullbackOpen IF I₁ sphereProjection sphereRegularPatch ≤ ⊤
              from le_top) g :=
  HolomorphicMeromorphic.existsUnique_descent_on_open IF I₁ sphereProjection
    sphereProjection_isOpenMap projectionSphere_surjective g sphereRegularPatch
    (fun b => meromorphicallyDescendsNear_regular g hg b.val b.property)

/-- The actual uniquely determined regular-base meromorphic section. -/
def regularSphereDescent (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (constantRegularFibres g).Countable) :
    HolomorphicMeromorphic.Section I₁ RiemannSphere sphereRegularPatch :=
  (existsUnique_regular_sphere_descent g hg).choose

theorem regularSphereDescent_pullback
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (constantRegularFibres g).Countable) :
    HolomorphicMeromorphic.pullbackSection IF I₁ sphereProjection
      sphereProjection_isOpenMap sphereRegularPatch (regularSphereDescent g hg) =
        HolomorphicMeromorphic.restrict IF Threefold.Space (show
          HolomorphicMeromorphic.pullbackOpen IF I₁ sphereProjection sphereRegularPatch ≤ ⊤
            from le_top) g :=
  (existsUnique_regular_sphere_descent g hg).choose_spec.1

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
