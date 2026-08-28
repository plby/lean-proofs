import Wikipedia.HopfProblem.DegreeCollapseSurgeryDualLocal
import Wikipedia.SmoothSixDPoincare.FramedFaceNormalCoordinates

/-!
# Native transversality supplies the single dual crossing's normal isomorphism

The inverse of the actual attaching-face chart defines the normal
projection. Its derivative annihilates the actual core tangent and is
onto. Transversality and equal dimension make its restriction to the dual
sheet invertible. The native centered source chart retains this property,
so the preceding belt-vanishing theorem needs no supplied normal degree
or invertible linear map.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryLink

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle
open SingularMayerVietoris

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₃" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  [Fact (Module.finrank ℝ F = 2 + 1)]

theorem single_transverse_dual_kills_belt (g : C(S₃, X))
    (hg : ContMDiff (𝓡 3) J ∞ g) (q : S₃) (u : UnitSphere E)
    (hpoint : g q = coreMap A u)
    (hunique : ∀ x, g x ∈ range (coreMap A) → x = q)
    (htrans : Surjective ((mfderiv (𝓡 3) J g q).coprod
      (mfderiv (𝓡 m) J (coreMap A) u))) :
    singularHomologyMap (beltMap A 2) 2 = 0 := by
  let Φ := NativeParametrization.centered (D := P₃) q
  have hΦ0 : (0 : P₃) ∈ Φ.source := NativeParametrization.zero_mem_centered_source q
  have hΦq : Φ 0 = q := NativeParametrization.centered_zero q
  have htarget : g q ∈ A.chart.target := hpoint ▸ core_mem_chart_target A u
  have hn := (contMDiffOn_normalProjection A).contMDiffAt
    (A.chart.open_target.mem_nhds htarget)
  have hc : ContMDiffAt (𝓡 3) 𝓘(ℝ, F) ∞ (normalProjection A ∘ g) q :=
    hn.comp q hg.contMDiffAt
  have hc' : ContMDiffAt (𝓡 3) 𝓘(ℝ, F) ∞ (normalProjection A ∘ g) (Φ 0) := by
    rw [hΦq]
    exact hc
  have hΦ : ContMDiffAt 𝓘(ℝ, P₃) (𝓡 3) ∞ Φ 0 :=
    Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hΦ0)
  have hd : ContDiffAt ℝ ∞ (dualNormal A g q) 0 := (hc'.comp 0 hΦ).contDiffAt
  have hb : Bijective (fderiv ℝ (dualNormal A g q) 0) := by
    change Bijective (fderiv ℝ ((normalProjection A ∘ g) ∘ Φ) 0)
    rw [← mfderiv_eq_fderiv, mfderiv_comp 0 (hc'.mdifferentiableAt (by simp))
      (hΦ.mdifferentiableAt (by simp)), hΦq]
    exact (bijective_normalProjection_comp_of_transverse A 3
      (Fact.out (p := Module.finrank ℝ F = 2 + 1)) g hg q u hpoint.symm htrans).comp
        (PartialChart.bijective_mfderiv Φ hΦ0)
  let L : P₃ ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ (dualNormal A g q) 0).toLinearMap hb).toContinuousLinearEquiv
  have hL : HasFDerivAt (dualNormal A g q) L.toContinuousLinearMap 0 :=
    (hd.differentiableAt (by simp)).hasFDerivAt
  exact single_regular_dual_kills_belt A g q u hpoint hunique L hL

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryLink
