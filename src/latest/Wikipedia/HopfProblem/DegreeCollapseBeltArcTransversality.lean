import Wikipedia.HopfProblem.DegreeCollapseBeltLevelArc
import Wikipedia.SmoothSixDPoincare.MorseBeltNormalRegularity

/-!
# The constructed arc is transverse to an actual index-one belt

Its original negative coordinate is exactly rho times the scalar arc
parameter times a unit vector. In negative dimension one, that derivative
is surjective. The kernel of the normal derivative is the actual belt
tangent image, so the arc and belt derivatives span the whole native level
tangent space. The crossing itself and its transversality are constructed.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

open Classical in
theorem nativeBeltLevelArc_normal
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    (S.data q).beltNormal (nativeBeltLevelArc S q u v s) = ((S.data q).radius * s) • u.val := by
  change ((S.data q).chart.splitChart (nativeBeltLevelArc S q u v s).val).1 = _
  rw [nativeBeltLevelArc_coe S q u v hs]
  exact congrArg Prod.fst ((S.data q).chart.splitChart.right_inv'
    (nativeBeltArc_coordinates_mem_target S q u v hs))

open Classical in
theorem nativeBeltLevelArc_transverse
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 1)
    (n : ℕ) [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    Surjective ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) (nativeBeltLevelArc S q u v) 0 :
      ℝ →L[ℝ] RegularLevel.Model E).coprod
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let d := S.data q
  let γ := nativeBeltLevelArc S q u v
  let L : ℝ →L[ℝ] d.chart.NegativeCoordinates :=
    ContinuousLinearMap.toSpanSingleton ℝ (d.radius • u.val)
  have hpoint : γ 0 = d.surgery.beltSphere v := Subtype.ext
    ((nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans (nativeBeltArc_zero S q u v))
  have hgerm : d.beltNormal ∘ γ =ᶠ[𝓝 (0 : ℝ)] L := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with s hs
    change d.beltNormal (nativeBeltLevelArc S q u v s) = s • (d.radius • u.val)
    rw [nativeBeltLevelArc_normal S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩),
      smul_smul, mul_comm s d.radius]
  have hnormalDerivative : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, d.chart.NegativeCoordinates)
      (d.beltNormal ∘ γ) 0 = L := by
    rw [hgerm.mfderiv_eq, mfderiv_eq_fderiv, L.fderiv]
  have hγ := (nativeBeltLevelArc_contMDiffOn S hf q u v).contMDiffAt
    (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
  have hnormal := (d.contMDiffOn_beltNormal hf).contMDiffAt
    (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  let A : ℝ →L[ℝ] RegularLevel.Model E :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) γ 0
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let Q : RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (d.surgery.beltSphere v)
  have hnγ : MDifferentiableAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates)
      d.beltNormal (γ 0) := by
    rw [hpoint]
    exact hnormal.mdifferentiableAt (by simp)
  have hQA : Q.comp A = L := by
    have hh := mfderiv_comp 0 hnγ (hγ.mdifferentiableAt (by simp))
    rw [hpoint] at hh
    exact hh.symm.trans hnormalDerivative
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hLi : Injective L := smul_left_injective ℝ (smul_ne_zero d.radius_pos.ne' hu)
  have hdim : Module.finrank ℝ ℝ = Module.finrank ℝ d.chart.NegativeCoordinates := by
    rw [Module.finrank_self]
    exact ((nativeMorseIndex_eq_chart d.chart).symm.trans hq).symm
  have hLs : Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) hdim).mp hLi
  have hQAs : Surjective (Q.comp A) := hQA.symm ▸ hLs
  have hker : B.range = Q.ker := d.range_belt_derivative_eq_normal_kernel hf n v
  change Surjective (A.coprod B)
  intro z
  obtain ⟨s, hs⟩ := hQAs (Q z)
  have hmem : z - A s ∈ Q.ker := by
    change Q (z - A s) = 0
    change Q (A s) = Q z at hs
    rw [map_sub, hs, sub_self]
  rw [← hker] at hmem
  obtain ⟨w, hw⟩ := hmem
  change B w = z - A s at hw
  refine ⟨(s, w), ?_⟩
  change A s + B w = z
  rw [hw]
  abel

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
