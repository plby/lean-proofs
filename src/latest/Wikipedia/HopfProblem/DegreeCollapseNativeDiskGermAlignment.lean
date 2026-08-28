import Wikipedia.HopfProblem.DegreeCollapseLocalDiskGermAlignment

/-!
# Native ambient alignment of two disk charts at a common center

The supported coordinate germ is extended through the second original
chart. Its support remains compact in that chart, and its endpoint agrees
pointwise with the desired disk parametrization on a neighborhood of zero.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {A B E H M ι κ : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nontrivial κ]

theorem exists_native_disk_germ_alignment (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B))
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ0 : (0 : A × B) ∈ Φ.source) (hΨ0 : (0 : A × B) ∈ Ψ.source)
    (hcenter : Φ 0 = Ψ 0) :
    ∃ (D : Diffeomorph J J M M ∞) (K : Set M), IsCompact K ∧ K ⊆ Ψ.target ∧
      Nonempty (SupportedRelativeIsotopy D K {Ψ 0}) ∧
      (fun x : A => D (Φ (x, 0))) =ᶠ[𝓝 (0 : A)] (fun x => Ψ (x, (0 : B))) := by
  let Θ := Φ.trans Ψ.symm
  have hΘ0 : (0 : A × B) ∈ Θ.source := by
    refine ⟨hΦ0, ?_⟩
    change Φ 0 ∈ Ψ.target
    rw [hcenter]
    exact Ψ.map_source' hΨ0
  have hΘzero : Θ 0 = 0 := by
    change Ψ.symm (Φ 0) = 0
    rw [hcenter]
    exact Ψ.left_inv' hΨ0
  obtain ⟨d, L, hL, hLsource, ⟨Hiso⟩, hgerm⟩ :=
    exists_supported_disk_germ_alignment b i basis Θ hΘ0 hΘzero Ψ.open_source hΨ0
  let D := extension Ψ d hL hLsource Hiso.endpoint_fixed_outside
  have hfixed : ∀ x ∈ Ψ.source, Ψ x ∈ ({Ψ 0} : Set M) → x ∈ ({0} : Set (A × B)) := by
    intro x hx hh
    exact mem_singleton_iff.mpr
      (Ψ.toOpenPartialHomeomorph.injOn hx hΨ0 (mem_singleton_iff.mp hh))
  have HD := Hiso.extension Ψ hL hLsource hfixed
  refine ⟨D, Ψ '' L,
    hL.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hLsource),
    ?_, ⟨HD⟩, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Ψ.map_source' (hLsource hx)
  · have hcore : Tendsto (fun x : A => (x, (0 : B))) (𝓝 0) (𝓝 (0 : A × B)) :=
      (continuous_id.prodMk continuous_const).tendsto 0
    filter_upwards [hgerm, hcore (Θ.open_source.mem_nhds hΘ0)] with x hx hxsource
    have ht : Φ (x, 0) ∈ Ψ.target := hxsource.2
    have hback : Ψ (Θ (x, 0)) = Φ (x, 0) := Ψ.right_inv' ht
    calc
      D (Φ (x, 0)) = D (Ψ (Θ (x, 0))) := congrArg D hback.symm
      _ = Ψ (d (Θ (x, 0))) :=
        extension_chart Ψ d hL hLsource Hiso.endpoint_fixed_outside (Ψ.map_target' ht)
      _ = Ψ (x, 0) := congrArg Ψ hx

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
