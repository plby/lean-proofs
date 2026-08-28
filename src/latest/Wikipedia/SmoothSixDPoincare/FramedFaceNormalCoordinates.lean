import Wikipedia.SmoothSixDPoincare.FramedSurgeryPatches
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.SmoothSixDPoincare.TransverseNormalLinearMap
import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse

/-!
# Native normal coordinates of an actual framed face

The inverse of the full face chart supplies the normal projection. Its
differential is onto, annihilates the core tangent, and is invertible on
any complementary transverse sheet. The resulting local inverse uses
the original normal coordinate, not a replacement normal framing.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

def normalProjection (x : X) : F := (A.chart.symm x).2

theorem core_mem_chart_target (u : UnitSphere E) : coreMap A u ∈ A.chart.target := by
  rw [show coreMap A u = A.chart (u, 0) from (A.point u ⟨0, by simp⟩).symm]
  exact A.chart.map_source' (A.source ⟨mem_univ _, mem_closedBall_self zero_le_one⟩)

theorem chart_symm_core (u : UnitSphere E) : A.chart.symm (coreMap A u) = (u, 0) := by
  rw [show coreMap A u = A.chart (u, 0) from (A.point u ⟨0, by simp⟩).symm]
  exact A.chart.left_inv' (A.source ⟨mem_univ _, mem_closedBall_self zero_le_one⟩)

theorem normalProjection_core (u : UnitSphere E) : normalProjection A (coreMap A u) = 0 :=
  congrArg Prod.snd (chart_symm_core A u)

theorem normalProjection_chart (z : UnitSphere E × F) (hz : z ∈ A.chart.source) :
    normalProjection A (A.chart z) = z.2 := congrArg Prod.snd (A.chart.left_inv' hz)

theorem contMDiffOn_normalProjection : ContMDiffOn J 𝓘(ℝ, F) ∞
    (normalProjection A) A.chart.target :=
  contMDiff_snd.comp_contMDiffOn A.chart.contMDiffOn_invFun

theorem contMDiff_coreMap : ContMDiff (𝓡 m) J ∞ (coreMap A) := by
  have heq : (fun u : UnitSphere E => A.chart (u, 0)) = coreMap A :=
    funext (fun u => A.point u ⟨0, by simp⟩)
  rw [← heq, ← contMDiffOn_univ]
  exact A.chart.contMDiffOn_toFun.comp
    ((contMDiff_id.prodMk contMDiff_const).contMDiffOn)
      (fun _ _ => A.source ⟨mem_univ _, mem_closedBall_self zero_le_one⟩)

theorem normalProjection_derivative_comp_core (u : UnitSphere E) :
    (mfderiv J 𝓘(ℝ, F) (normalProjection A) (coreMap A u)).comp
      (mfderiv (𝓡 m) J (coreMap A) u) = 0 := by
  have hn := (contMDiffOn_normalProjection A).contMDiffAt
    (A.chart.open_target.mem_nhds (core_mem_chart_target A u))
  have heq : normalProjection A ∘ coreMap A = (fun _ : UnitSphere E => (0 : F)) :=
    funext (normalProjection_core A)
  have hz : mfderiv (𝓡 m) 𝓘(ℝ, F) (normalProjection A ∘ coreMap A) u = 0 := by
    rw [heq, mfderiv_const]
  exact (mfderiv_comp u (hn.mdifferentiableAt (by simp))
    ((contMDiff_coreMap A).mdifferentiableAt (by simp))).symm.trans hz

theorem surjective_normalProjection_derivative (x : X) (hx : x ∈ A.chart.target) :
    Surjective (mfderiv J 𝓘(ℝ, F) (normalProjection A) x) := by
  have hchart := (PartialChart.bijective_mfderiv A.chart.symm hx).2
  have hderiv : mfderiv J 𝓘(ℝ, F) (normalProjection A) x =
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) F).comp
        (mfderiv J ((𝓡 m).prod 𝓘(ℝ, F)) A.chart.symm x) := by
    change mfderiv J 𝓘(ℝ, F) (Prod.snd ∘ A.chart.symm) x = _
    rw [mfderiv_comp x mdifferentiableAt_snd
      (A.chart.symm.mdifferentiableAt (by simp) hx), mfderiv_snd]
    rfl
  rw [hderiv]
  intro w
  obtain ⟨v, hv⟩ := hchart (0, w)
  exact ⟨v, congrArg Prod.snd hv⟩

variable [FiniteDimensional ℝ F]

theorem bijective_normalProjection_comp_of_transverse (k : ℕ)
    (hdim : Module.finrank ℝ F = k) (g : Hemisphere.Sphere k → X)
    (hg : ContMDiff (𝓡 k) J ∞ g) (a : Hemisphere.Sphere k) (u : UnitSphere E)
    (hcross : coreMap A u = g a)
    (htrans : Surjective ((mfderiv (𝓡 k) J g a).coprod
      (mfderiv (𝓡 m) J (coreMap A) u))) :
    Bijective (mfderiv (𝓡 k) 𝓘(ℝ, F) (normalProjection A ∘ g) a) := by
  let Q : G →L[ℝ] F := mfderiv J 𝓘(ℝ, F) (normalProjection A) (coreMap A u)
  let B : EuclideanSpace ℝ (Fin m) →L[ℝ] G := mfderiv (𝓡 m) J (coreMap A) u
  let C : EuclideanSpace ℝ (Fin k) →L[ℝ] G := mfderiv (𝓡 k) J g a
  have hQ : Surjective Q :=
    surjective_normalProjection_derivative A _ (core_mem_chart_target A u)
  have hQB : Q.comp B = 0 := normalProjection_derivative_comp_core A u
  have hBC : Surjective (B.coprod C) := TransverseCoordinates.surjective_coprod_swap C B htrans
  have hi : Bijective (Q.comp C) := TransverseCoordinates.bijective_normal_comp Q B C hQ hBC hQB
    (by rw [finrank_euclideanSpace_fin, hdim])
  have ha : g a ∈ A.chart.target := hcross ▸ core_mem_chart_target A u
  have hn := (contMDiffOn_normalProjection A).contMDiffAt (A.chart.open_target.mem_nhds ha)
  rw [mfderiv_comp a (hn.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp)), ← hcross]
  exact hi

theorem exists_normal_chart_of_transverse (k : ℕ)
    (hdim : Module.finrank ℝ F = k) (g : Hemisphere.Sphere k → X)
    (hg : ContMDiff (𝓡 k) J ∞ g) (a : Hemisphere.Sphere k) (u : UnitSphere E)
    (hcross : coreMap A u = g a)
    (htrans : Surjective ((mfderiv (𝓡 k) J g a).coprod
      (mfderiv (𝓡 m) J (coreMap A) u))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, F) (𝓡 k) F (Hemisphere.Sphere k) ∞,
      0 ∈ Φ.source ∧ Φ 0 = a ∧ Φ.target ⊆ g ⁻¹' A.chart.target ∧
      (∀ v ∈ Φ.source, normalProjection A (g (Φ v)) = v) ∧
      ∀ x ∈ Φ.target, Φ.symm x = normalProjection A (g x) := by
  let U := g ⁻¹' A.chart.target
  have hU : IsOpen U := A.chart.open_target.preimage hg.continuous
  have ha : a ∈ U := by
    change g a ∈ A.chart.target
    exact hcross ▸ core_mem_chart_target A u
  have hn : ContMDiffOn (𝓡 k) 𝓘(ℝ, F) ∞ (normalProjection A ∘ g) U :=
    (contMDiffOn_normalProjection A).comp hg.contMDiffOn (fun _ hx => hx)
  let L : EuclideanSpace ℝ (Fin k) →L[ℝ] F :=
    mfderiv (𝓡 k) 𝓘(ℝ, F) (normalProjection A ∘ g) a
  have hL : Bijective L := bijective_normalProjection_comp_of_transverse A k hdim g hg
    a u hcross htrans
  have hLi : L.IsInvertible :=
    ⟨(LinearEquiv.ofBijective L.toLinearMap hL).toContinuousLinearEquiv, rfl⟩
  obtain ⟨ψ, haψ, hψU, heq⟩ := exists_partialDiffeomorph_boundaryless hU ha hn hLi
  have hψa : ψ a = 0 := by
    rw [← heq haψ]
    change normalProjection A (g a) = 0
    rw [← hcross, normalProjection_core]
  have hz : (0 : F) ∈ ψ.target := hψa ▸ ψ.map_source' haψ
  refine ⟨ψ.symm, hz, ?_, hψU, ?_, ?_⟩
  · rw [← hψa]
    exact ψ.left_inv' haψ
  · intro v hv
    exact (heq (ψ.map_target' hv)).trans (ψ.right_inv' hv)
  · intro x hx
    exact (heq hx).symm

end Wikipedia.SmoothSixDPoincare.FramedSurgery
