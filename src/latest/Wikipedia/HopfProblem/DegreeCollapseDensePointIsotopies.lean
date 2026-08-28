import Wikipedia.SmoothSixDPoincare.OpenPointMoving
import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-!
# Supported isotopies place two distinct points in a dense subset

The existing local point motion is retained with its actual smooth isotopy.
Disjoint open supports then move two prescribed points independently into
the dense set. The constructed composite is isotopic to the identity.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [T2Space M]

theorem exists_open_isotopic_pointMoving {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V,
      ∃ d : Diffeomorph J J M M ∞, IsotopicToIdentity d ∧ d x = y ∧
        ∀ z ∉ U, d z = z := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) x
  let Φ := PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨ε, hε, hball, hmove⟩ := exists_supported_pointMoving Φ hxΦ
  refine ⟨Φ '' Metric.ball (c x) ε,
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball,
    ⟨c x, Metric.mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove v hv
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, ⟨A, hA, hzero, hd, hdiff⟩, ?_, ?_⟩
    · rw [hΦx] at hend
      exact (hd x).symm.trans hend
    · intro z hz
      exact (hd z).symm.trans (hfix 1 z (fun h => hz h.2))

theorem exists_isotopic_two_points_in_dense {B : Set M} (hB : Dense B)
    {x y : M} (hxy : x ≠ y) :
    ∃ d : Diffeomorph J J M M ∞, IsotopicToIdentity d ∧ d x ∈ B ∧ d y ∈ B := by
  obtain ⟨U, V, hU, hV, hx, hy, hdisj⟩ := t2_separation hxy
  obtain ⟨U', hU', hx', hU'U, hmoveU⟩ := exists_open_isotopic_pointMoving (J := J) hU hx
  obtain ⟨V', hV', hy', hV'V, hmoveV⟩ := exists_open_isotopic_pointMoving (J := J) hV hy
  obtain ⟨x', hx'B, hx'U⟩ := hB.exists_mem_open hU' ⟨x, hx'⟩
  obtain ⟨y', hy'B, hy'V⟩ := hB.exists_mem_open hV' ⟨y, hy'⟩
  obtain ⟨d, hd, hdx, hdfix⟩ := hmoveU x' hx'U
  obtain ⟨e, he, hey, hefix⟩ := hmoveV y' hy'V
  have hyU : y ∉ U := fun h => Set.disjoint_left.mp hdisj h hy
  have hxV : x' ∉ V := fun h => Set.disjoint_left.mp hdisj (hU'U hx'U) h
  refine ⟨d.trans e, hd.trans he, ?_, ?_⟩
  · change e (d x) ∈ B
    rw [hdx, hefix x' hxV]
    exact hx'B
  · change e (d y) ∈ B
    rw [hdfix y hyU, hey]
    exact hy'B

theorem isotopicToIdentity_joined {d : Diffeomorph J J M M ∞}
    (hd : IsotopicToIdentity d) (x : M) : Joined x (d x) := by
  obtain ⟨A, hA, hzero, hone, -⟩ := hd
  exact ⟨{
    toFun := fun t => A ((t : ℝ), x)
    continuous_toFun := hA.continuous.comp (continuous_subtype_val.prodMk continuous_const)
    source' := hzero x
    target' := hone x }⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
