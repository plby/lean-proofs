import Wikipedia.HopfProblem.DegreeCollapseRelativeAmbientTransversality
import Wikipedia.HopfProblem.DegreeCollapseAmbientDimensionalAvoidance

/-!
# Prepare a sheet while fixing every other protected sheet at every time

Relative native transversality and the strict dimension inequality give
actual ambient avoidance. The constructed isotopy has one compact support
inside any prescribed open neighborhood of the first sheet. For a closed
protected subset disjoint from that sheet, its full complement supplies
the neighborhood and every real-time slice fixes the protected subset.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {D Z G H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_supported_ambient_disjoint_in_open {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G)
    {U : Set N} (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧ C ⊆ U ∧ Nonempty (SupportedRelativeIsotopy e C Uᶜ) ∧
      Disjoint (range (e ∘ f)) (range g) := by
  classical
  let d := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let f' : X × Hemisphere.Sphere d → N := f ∘ Prod.fst
  have hf' : ContMDiff (I.prod (𝓡 d)) J ∞ f' := hf.comp contMDiff_fst
  have hdim' : Module.finrank ℝ (D × EuclideanSpace ℝ (Fin d)) +
      Module.finrank ℝ Z = Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    dsimp [d]
    omega
  have hf'U : range f' ⊆ U := by
    rintro _ ⟨x, rfl⟩
    exact hfU (mem_range_self x.1)
  obtain ⟨e, C, hC, hCU, hIso, ht⟩ :=
    exists_supported_ambient_transverse_in_open hf' hg hdim' hU hf'U
  have htrans : ∀ x y, NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Hemisphere.Sphere d := Hemisphere.point true ⟨0, by simp [DiskDouble.Disk]⟩
    apply native_transverse_of_ignored_factor (I'' := 𝓡 d) w
      ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, C, hC, hCU, hIso, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩

theorem exists_supported_ambient_disjoint_fixing_closed {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G)
    {C : Set N} (hC : IsClosed C) (hfC : Disjoint (range f) C) :
    ∃ (e : Diffeomorph J J N N ∞) (K : Set N),
      IsCompact K ∧ K ⊆ Cᶜ ∧ Nonempty (SupportedRelativeIsotopy e K C) ∧
      Disjoint (range (e ∘ f)) (range g) := by
  have hfU : range f ⊆ Cᶜ := fun _ hx hy => Set.disjoint_left.mp hfC hx hy
  obtain ⟨e, K, hK, hKU, hIso, hdisj⟩ :=
    exists_supported_ambient_disjoint_in_open hf hg hdim hC.isOpen_compl hfU
  refine ⟨e, K, hK, hKU, ?_, hdisj⟩
  simpa only [compl_compl] using hIso

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
