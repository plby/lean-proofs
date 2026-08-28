import Wikipedia.SmoothSixDPoincare.MorseBeltNormalCoordinates
import Wikipedia.SmoothSixDPoincare.MorseDescentModel
import Wikipedia.SmoothSixDPoincare.TransverseNormalLinearMap

/-!
# Regularity of the actual Morse belt normal map

Varying the original negative Morse coordinates at a belt point has zero
height derivative and identity normal derivative. The actual level tangent
kernel therefore supplies a right inverse for the restricted normal map.
Its kernel is exactly the belt tangent image, and transverse complementary
sheet intersections have invertible normal differentials.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- The fixed original normal coordinate is a submersion along the entire actual belt. -/
theorem surjective_beltNormal_derivative
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Surjective (mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (d.surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let w : d.chart.PositiveCoordinates := d.radius • (v : d.chart.PositiveCoordinates)
  let γ : d.chart.NegativeCoordinates → M := fun u => d.chart.splitChart.symm (u, w)
  let n : M → d.chart.NegativeCoordinates := fun x => (d.chart.splitChart x).1
  have hmodel : (0, w) ∈ d.chart.splitChart.target := d.belt_model_mem_target v
  have hγ : ContMDiffAt 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, E) ∞ γ 0 :=
    (d.chart.splitChart.contMDiffOn_invFun.contMDiffAt
      (d.chart.splitChart.open_target.mem_nhds hmodel)).comp 0
        (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hpoint : γ 0 = (d.surgery.beltSphere v : M) := by
    rw [d.belt_eq, d.chart.beltCoreMap_coe]
  have hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ n
      (d.surgery.beltSphere v : M) :=
    contDiff_fst.contMDiff.contMDiffAt.comp _
      (d.chart.splitChart.contMDiffOn_toFun.contMDiffAt
        (d.chart.splitChart.open_source.mem_nhds (d.belt_mem_normalDomain v)))
  have hnear : ∀ᶠ u : d.chart.NegativeCoordinates in 𝓝 0,
      (u, w) ∈ d.chart.splitChart.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (d.chart.splitChart.open_target.mem_nhds hmodel)
  have hheight : f ∘ γ =ᶠ[𝓝 (0 : d.chart.NegativeCoordinates)]
      (fun u => f p - ‖u‖ ^ 2 + ‖w‖ ^ 2) := by
    filter_upwards [hnear] with u hu
    exact d.chart.splitChart_inverse_equation hu
  have hheight₀ : mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, ℝ) (f ∘ γ) 0 = 0 := by
    rw [hheight.mfderiv_eq, mfderiv_eq_fderiv, fderiv_add_const, fderiv_const_sub,
      fderiv_norm_sq_apply]
    simp
    rfl
  have hnormal : n ∘ γ =ᶠ[𝓝 (0 : d.chart.NegativeCoordinates)] id := by
    filter_upwards [hnear] with u hu
    exact congrArg Prod.fst (d.chart.splitChart.right_inv' hu)
  have hnormal₀ : mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates)
      𝓘(ℝ, d.chart.NegativeCoordinates) (n ∘ γ) 0 =
        ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates := by
    rw [hnormal.mfderiv_eq, mfderiv_id]
    rfl
  let R : d.chart.NegativeCoordinates →L[ℝ] E :=
    mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, E) γ 0
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (d.surgery.beltSphere v : M)
  let B : E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (d.surgery.beltSphere v : M)
  have hLpoint : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ 0) : E →L[ℝ] ℝ) = L := by
    rw [hpoint]
    rfl
  have hLR₀ : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ 0) : E →L[ℝ] ℝ).comp R = 0 :=
    (mfderiv_comp 0 (hf.mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))).symm.trans hheight₀
  have hLR : L.comp R = 0 :=
    (congrArg (fun T : E →L[ℝ] ℝ => T.comp R) hLpoint).symm.trans hLR₀
  have hnγ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) := by
    rw [hpoint]
    exact hn.mdifferentiableAt (by simp)
  have hBpoint : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) :
      E →L[ℝ] d.chart.NegativeCoordinates) = B := by
    rw [hpoint]
  have hBR₀ : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) :
      E →L[ℝ] d.chart.NegativeCoordinates).comp R =
        ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates :=
    (mfderiv_comp 0 hnγ (hγ.mdifferentiableAt (by simp))).symm.trans hnormal₀
  have hBR : B.comp R = ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates :=
    (congrArg (fun T : E →L[ℝ] d.chart.NegativeCoordinates => T.comp R) hBpoint).symm.trans hBR₀
  exact RegularLevel.surjective_normal_derivative_of_tangent_lift hf d.upper_regular
    (d.surgery.beltSphere v) (hn.mdifferentiableAt (by simp)) R hLR hBR

open Classical in
/-- The kernel of the fixed normal derivative is exactly the actual belt tangent image. -/
theorem range_belt_derivative_eq_normal_kernel (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v).range =
      (mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
        d.beltNormal (d.surgery.beltSphere v)).ker := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let Q : RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (d.surgery.beltSphere v)
  change A.range = Q.ker
  have hQA : Q.comp A = 0 := d.beltNormal_derivative_comp_belt hf n v
  have hsub : A.range ≤ Q.ker := by
    rintro _ ⟨u, rfl⟩
    change Q (A u) = 0
    exact congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] d.chart.NegativeCoordinates => T u) hQA
  have hAi : Injective A := d.belt_derivative_injective hf n v
  have hArank : Module.finrank ℝ A.range = n := by
    rw [LinearMap.finrank_range_of_inj hAi]
    exact finrank_euclideanSpace_fin
  have hQ : Surjective Q := d.surjective_beltNormal_derivative hf v
  have hQrank : Module.finrank ℝ Q.range = Module.finrank ℝ d.chart.NegativeCoordinates := by
    rw [LinearMap.range_eq_top.mpr hQ, finrank_top]
  have hdimQ := Q.toLinearMap.finrank_range_add_finrank_ker
  have hsplit := d.chart.finrank_negative_add_positive
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
  have hmodel : Module.finrank ℝ (RegularLevel.Model E) = Module.finrank ℝ E - 1 :=
    finrank_euclideanSpace_fin
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [hArank]
  omega

open Classical in
/-- At a transverse complementary-sheet intersection the actual normal derivative is invertible. -/
theorem bijective_beltNormal_comp_of_transverse (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (x : Hemisphere.Sphere m) (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates),
      d.surgery.beltSphere v = g x →
      Surjective ((mfderiv (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) g x :
          EuclideanSpace ℝ (Fin m) →L[ℝ] RegularLevel.Model E).coprod
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v :
          EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E)) →
      Bijective (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg x v hxy ht
  let Q : RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (d.surgery.beltSphere v)
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) g x
  have hQ : Surjective Q := d.surjective_beltNormal_derivative hf v
  have hQB : Q.comp B = 0 := d.beltNormal_derivative_comp_belt hf n v
  have hBA : Surjective (B.coprod A) := TransverseCoordinates.surjective_coprod_swap A B ht
  have hi : Bijective (Q.comp A) := TransverseCoordinates.bijective_normal_comp Q B A hQ hBA hQB
    (by simpa only [finrank_euclideanSpace_fin] using hdim.symm)
  have hx : g x ∈ d.beltNormalDomain := hxy ▸ d.belt_mem_normalDomain v
  have hnormal := (d.contMDiffOn_beltNormal hf).contMDiffAt (d.isOpen_beltNormalDomain.mem_nhds hx)
  have heq : mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x =
      Q.comp A := by
    rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp)), ← hxy]
    rfl
  rw [heq]
  exact hi

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
