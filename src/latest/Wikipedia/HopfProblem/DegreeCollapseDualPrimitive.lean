import Wikipedia.HopfProblem.DegreeCollapseDualCoverNaturality
import Wikipedia.HopfProblem.SphereHomologyTop

/-!
# A single transverse framed dual makes the actual sphere class primitive

The complement-and-tube detector composed with the original sphere's H3
map is an actual isomorphism. Its inverse followed by the literal S3 top
marking constructs an integral functional taking value one on the actual
sphere class. The regular-zero neighborhood and normal isomorphism are
constructed from native transversality, not supplied as degree data.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.DualCover

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₃" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

section LocalData

variable (g : C(S₃, X)) (q : S₃)
  (hunique : ∀ x, g x ∈ range (coreMap A) → x = q)
  {L : P₃ ≃L[ℝ] F}
  (d : LocalDegree.NeighborhoodData
    ((normalProjection A ∘ g) ∘ NativeParametrization.centered (D := P₃) q) L
    ((NativeParametrization.centered (D := P₃) q).source ∩
      NativeParametrization.centered (D := P₃) q ⁻¹' (g ⁻¹' A.chart.target)))

def primitiveFunctional : SingularHomology X 3 →ₗ[ℤ] ℤ := by
  let r := (compositeEquiv A g q d).symm.toLinearMap.comp (detector A 2)
  exact (unitSphereHomologyTopEquiv 2).toLinearMap.comp r

include hunique in
theorem primitiveFunctional_image (x : SingularHomology S₃ 3) :
    primitiveFunctional A g q d (singularHomologyMap g 3 x) =
      unitSphereHomologyTopEquiv 2 x := by
  change unitSphereHomologyTopEquiv 2
    ((compositeEquiv A g q d).symm (detector A 2 (singularHomologyMap g 3 x))) = _
  rw [← compositeEquiv_apply A g q hunique d x, LinearEquiv.symm_apply_apply]

include hunique in
theorem primitiveFunctional_class :
    primitiveFunctional A g q d (singularHomologyMap g 3 (unitSphereTopClass 2)) = 1 := by
  rw [primitiveFunctional_image A g q hunique d, unitSphereHomologyTopEquiv_topClass]

end LocalData

variable [FiniteDimensional ℝ F] [Fact (Module.finrank ℝ F = 2 + 1)]

theorem exists_transverse_neighborhood (g : C(S₃, X))
    (hg : ContMDiff (𝓡 3) J ∞ g) (q : S₃) (u : UnitSphere E)
    (hpoint : g q = coreMap A u)
    (htrans : Surjective ((mfderiv (𝓡 3) J g q).coprod
      (mfderiv (𝓡 m) J (coreMap A) u))) :
    ∃ L : P₃ ≃L[ℝ] F, Nonempty (LocalDegree.NeighborhoodData
      ((normalProjection A ∘ g) ∘ NativeParametrization.centered (D := P₃) q) L
      ((NativeParametrization.centered (D := P₃) q).source ∩
        NativeParametrization.centered (D := P₃) q ⁻¹' (g ⁻¹' A.chart.target))) := by
  have ht : g q ∈ A.chart.target := hpoint ▸ core_mem_chart_target A u
  have hn := (contMDiffOn_normalProjection A).contMDiffAt (A.chart.open_target.mem_nhds ht)
  have hF : ContMDiffAt (𝓡 3) 𝓘(ℝ, F) ∞ (normalProjection A ∘ g) q :=
    hn.comp q hg.contMDiffAt
  have hz : (normalProjection A ∘ g) q = 0 := by
    change normalProjection A (g q) = 0
    rw [hpoint, normalProjection_core]
  have hb := bijective_normalProjection_comp_of_transverse A 3
    (Fact.out (p := Module.finrank ℝ F = 2 + 1)) g hg q u hpoint.symm htrans
  let D : P₃ →L[ℝ] F := mfderiv (𝓡 3) 𝓘(ℝ, F) (normalProjection A ∘ g) q
  let B : P₃ ≃L[ℝ] F := (LinearEquiv.ofBijective D.toLinearMap hb).toContinuousLinearEquiv
  have hD : D.IsInvertible := ⟨B, rfl⟩
  have hi : (mfderiv (𝓡 3) 𝓘(ℝ, F) (normalProjection A ∘ g) q).IsInvertible :=
    hD
  have hW : g ⁻¹' A.chart.target ∈ 𝓝 q :=
    g.continuous.continuousAt.preimage_mem_nhds (A.chart.open_target.mem_nhds ht)
  obtain ⟨L, _, hd⟩ := LocalDegree.exists_native_neighborhoodData q hF hz hi
    (g ⁻¹' A.chart.target) hW
  exact ⟨L, hd⟩

theorem exists_primitive_functional_of_single_transverse_dual (g : C(S₃, X))
    (hg : ContMDiff (𝓡 3) J ∞ g) (q : S₃) (u : UnitSphere E)
    (hpoint : g q = coreMap A u)
    (hunique : ∀ x, g x ∈ range (coreMap A) → x = q)
    (htrans : Surjective ((mfderiv (𝓡 3) J g q).coprod
      (mfderiv (𝓡 m) J (coreMap A) u))) :
    ∃ l : SingularHomology X 3 →ₗ[ℤ] ℤ,
      l (singularHomologyMap g 3 (unitSphereTopClass 2)) = 1 := by
  obtain ⟨L, ⟨d⟩⟩ := exists_transverse_neighborhood A g hg q u hpoint htrans
  exact ⟨primitiveFunctional A g q d, primitiveFunctional_class A g q hunique d⟩

end Wikipedia.HopfProblem.DegreeCollapse.DualCover
