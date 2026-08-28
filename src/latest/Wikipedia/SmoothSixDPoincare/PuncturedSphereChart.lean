import Wikipedia.SmoothSixDPoincare.CenteredParametrization
import Wikipedia.SmoothSixDPoincare.GlobalChartGerm
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# A prescribed sphere-chart germ extends over a punctured sphere

The reference chart is the native stereographic chart at the prescribed
center, translated to send zero to that center. Its source is all Euclidean
space and its target omits exactly the antipode. Global realization of the
coordinate transition then retains any given chart germ near zero.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.NativeParametrization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

omit [FiniteDimensional ℝ V] in
theorem centered_sphere_source (v : sphere (0 : V) 1) :
    (centered (D := EuclideanSpace ℝ (Fin n)) v).source = univ := by
  have ht : (NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓡 n) v).target =
      univ := by
    change (extChartAt (𝓡 n) v).target = univ
    rw [extChartAt_target]
    change (𝓡 n).symm ⁻¹' (stereographic' n (-v)).target ∩ range (𝓡 n) = univ
    simp
  ext x
  change (x ∈ (univ : Set (EuclideanSpace ℝ (Fin n))) ∧
    _ ∈ (NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓡 n) v).target) ↔
    x ∈ univ
  simp only [ht, mem_univ, and_self]

omit [FiniteDimensional ℝ V] in
theorem centered_sphere_target (v : sphere (0 : V) 1) :
    (centered (D := EuclideanSpace ℝ (Fin n)) v).target = {-v}ᶜ := by
  ext x
  change (x ∈ (extChartAt (𝓡 n) v).source ∧
    extChartAt (𝓡 n) v x ∈ (univ : Set (EuclideanSpace ℝ (Fin n)))) ↔ x ∈ {-v}ᶜ
  simp only [mem_univ, and_true, extChartAt_source]
  change x ∈ (stereographic' n (-v)).source ↔ x ∈ {-v}ᶜ
  rw [stereographic'_source]

end Wikipedia.SmoothSixDPoincare.NativeParametrization

namespace Wikipedia.SmoothSixDPoincare.PartialChart

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

omit [FiniteDimensional ℝ V] in
/-- A given native sphere parametrization germ extends to the complement of its antipode. -/
theorem exists_punctured_sphere_extension
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 n) E (sphere (0 : V) 1) ∞)
    (hzero : (0 : E) ∈ Φ.source) (hdim : Module.finrank ℝ E = n) :
    ∃ Ξ : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 n) E (sphere (0 : V) 1) ∞,
      Ξ.source = univ ∧ Ξ.target = {-Φ 0}ᶜ ∧
      (Ξ : E → sphere (0 : V) 1) =ᶠ[𝓝 (0 : E)] Φ := by
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hdim.trans finrank_euclideanSpace_fin.symm)
  let c := NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) (Φ 0)
  let c' := L.toDiffeomorph.toPartialDiffeomorph.trans c
  have hcsource : c'.source = univ := by
    ext x
    change (x ∈ (univ : Set E) ∧ L x ∈ c.source) ↔ x ∈ univ
    rw [NativeParametrization.centered_sphere_source]
    simp only [mem_univ, and_self]
  have hctarget : c'.target = {-Φ 0}ᶜ := by
    ext x
    change (x ∈ c.target ∧ c.symm x ∈ (univ : Set (EuclideanSpace ℝ (Fin n)))) ↔
      x ∈ {-Φ 0}ᶜ
    rw [NativeParametrization.centered_sphere_target]
    simp only [mem_univ, and_true]
  have hc₀ : c' (0 : E) = Φ 0 := by
    change c (L 0) = Φ 0
    rw [map_zero]
    exact NativeParametrization.centered_zero (Φ 0)
  obtain ⟨Ξ, hΞs, hΞt, hgerm⟩ := exists_full_source_extension Φ c' hzero hcsource hc₀
  exact ⟨Ξ, hΞs, hΞt.trans hctarget, hgerm⟩

/-- The extension compactifies to the entire sphere and retains the original local germ. -/
theorem exists_sphere_compactification_of_germ
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 n) E (sphere (0 : V) 1) ∞)
    (hzero : (0 : E) ∈ Φ.source) (hdim : Module.finrank ℝ E = n) :
    ∃ e : OnePoint E ≃ₜ sphere (0 : V) 1,
      e OnePoint.infty = -Φ 0 ∧
      (fun x : E => e (x : OnePoint E)) =ᶠ[𝓝 (0 : E)] Φ := by
  obtain ⟨Ξ, hΞs, hΞt, hgerm⟩ := exists_punctured_sphere_extension Φ hzero hdim
  have hemb : Topology.IsEmbedding (Ξ : E → sphere (0 : V) 1) :=
    Ξ.toOpenPartialHomeomorph.isEmbedding hΞs
  have hrange : range (Ξ : E → sphere (0 : V) 1) = {-Φ 0}ᶜ := by
    rw [← hΞt]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Ξ.map_source' (hΞs ▸ mem_univ x)
    · intro hy
      exact ⟨Ξ.symm y, Ξ.right_inv' hy⟩
  let e := OnePoint.equivOfIsEmbeddingOfRangeEq (-Φ 0) Ξ hemb hrange
  exact ⟨e, rfl, hgerm⟩

end Wikipedia.SmoothSixDPoincare.PartialChart
