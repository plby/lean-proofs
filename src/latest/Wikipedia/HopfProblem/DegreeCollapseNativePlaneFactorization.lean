import Wikipedia.HopfProblem.DegreeCollapseNativeTransverseFactorization

/-!
# Smooth local factorization through a native coordinate plane

A continuous linear retraction of the coordinate plane supplies the
factor map explicitly. Membership of the actual sheet in that plane is
needed only as a germ. A second germ identifies any prescribed native
parametrization of the same plane.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A Z U E HU HE X M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace HU] [TopologicalSpace HE]
  {I : ModelWithCorners ℝ U HU} {J : ModelWithCorners ℝ E HE}
  [TopologicalSpace X] [ChartedSpace HU X]
  [TopologicalSpace M] [ChartedSpace HE M]

theorem exists_native_plane_factorization
    (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a)
    {F : X → M} {x : X} (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧
      F =ᶠ[𝓝 x] (fun y => P (L (u y))) := by
  let u : X → A := fun y => R (P.symm (F y))
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hi := (P.symm.mdifferentiableAt (by simp) hxt).comp x hF
  have hu : MDifferentiableAt I 𝓘(ℝ, A) u x :=
    R.differentiableAt.mdifferentiableAt.comp x hi
  have hu0 : u x = 0 := by
    change R (P.symm (F x)) = 0
    have hi0 : P.symm (P 0) = 0 := P.left_inv' hP0
    rw [hx, hi0, map_zero]
  refine ⟨u, hu, hu0, ?_⟩
  filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hplane] with y hy hplaneY
  obtain ⟨a, ha⟩ := hplaneY
  change F y = P (L (R (P.symm (F y))))
  rw [ha, hRL]
  exact (P.right_inv' hy).symm.trans (congrArg P ha)

theorem exists_native_plane_sheet_factorization
    (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a)
    {F : X → M} {x : X} (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a)
    {f : A → M} (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧
      F =ᶠ[𝓝 x] (f ∘ u) := by
  obtain ⟨u, hu, hu0, hfactor⟩ := exists_native_plane_factorization P hP0 L R hRL hF hx hplane
  have hut : Tendsto u (𝓝 x) (𝓝 (0 : A)) := hu0 ▸ hu.continuousAt
  have hcomp := hmodel.comp_tendsto hut
  exact ⟨u, hu, hu0, hfactor.trans hcomp.symm⟩

theorem exists_native_basin_sheet_factorization
    (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a)
    {F : X → M} {x : X} (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (Basin : M → Prop)
    (hbasin : ∀ z ∈ P.source, Basin (P z) → ∃ a, z = L a)
    (hFbasin : ∀ᶠ y in 𝓝 x, Basin (F y))
    {f : A → M} (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧
      F =ᶠ[𝓝 x] (f ∘ u) := by
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a := by
    filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hFbasin] with y hy hby
    have hb : Basin (P (P.symm (F y))) := (P.right_inv' hy).symm ▸ hby
    exact hbasin (P.symm (F y)) (P.map_target' hy) hb
  exact exists_native_plane_sheet_factorization P hP0 L R hRL hF hx hplane hmodel

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
