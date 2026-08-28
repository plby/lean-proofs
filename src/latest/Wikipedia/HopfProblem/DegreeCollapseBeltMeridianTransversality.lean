import Wikipedia.HopfProblem.DegreeCollapseBeltMeridianCrossing
import Wikipedia.SmoothSixDPoincare.MorseBeltNormalRegularity

/-!
# The meridian disk is transverse to the whole native belt at its center

The actual belt normal map restricts to the scaled bounded radial disk
map. Its derivative is invertible. The native belt tangent image is the
kernel of that normal derivative, giving the required complementary span.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open DiskShrinking

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] in
theorem nativeBeltMeridianDisk_normal (S : AdaptedSurgeryWindows E f)
    (p : criticalPoints E f) (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (x : (S.data p).chart.NegativeCoordinates) :
    (S.data p).beltNormal (nativeBeltMeridianDisk S p v s hs x) =
      (S.data p).radius • boundedRadialDiskMap (s : ℝ) x := by
  exact congrArg Prod.fst ((S.data p).chart.splitChart.right_inv'
    (nativeBeltDiskCoordinates_mem_target S p v s hs x))

theorem nativeBeltMeridianDisk_transverse
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = n + 1)]
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    Surjective ((mfderiv 𝓘(ℝ, (S.data p).chart.NegativeCoordinates)
      𝓘(ℝ, RegularLevel.Model E) (nativeBeltMeridianDisk S p v s hs) 0).coprod
        (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data p).surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let d := S.data p
  let N := d.chart.NegativeCoordinates
  let γ := nativeBeltMeridianDisk S p v s hs
  let L : N →L[ℝ] N := d.radius • fderiv ℝ (boundedRadialDiskMap (N := N) (s : ℝ)) 0
  have hnormalDerivative : mfderiv 𝓘(ℝ, N) 𝓘(ℝ, N) (d.beltNormal ∘ γ) 0 = L := by
    have he : d.beltNormal ∘ γ = fun x : N => d.radius • boundedRadialDiskMap (s : ℝ) x :=
      funext (nativeBeltMeridianDisk_normal S p v s hs)
    rw [he, mfderiv_eq_fderiv]
    have hsm := boundedRadialDiskMap_smooth (N := N) (s : ℝ)
    have hr := (hsm.differentiable (by simp) 0).hasFDerivAt
    exact (hr.const_smul d.radius).fderiv
  have hLi : Injective L := by
    intro x y hxy
    exact boundedRadialDiskMap_derivative_injective hs0 0
      (smul_right_injective N d.radius_pos.ne' hxy)
  have hLs : Surjective L := LinearMap.surjective_of_injective hLi
  have hγ := (nativeBeltMeridianDisk_smooth S hf p v s hs).contMDiffAt (x := 0)
  have hpoint : γ 0 = d.surgery.beltSphere v := nativeBeltMeridianDisk_zero S p v s hs
  have hnormal := (d.contMDiffOn_beltNormal hf).contMDiffAt
    (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  let A : N →L[ℝ] RegularLevel.Model E := mfderiv 𝓘(ℝ, N) 𝓘(ℝ, RegularLevel.Model E) γ 0
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v
  let Q : RegularLevel.Model E →L[ℝ] N :=
    mfderiv 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, N) d.beltNormal (d.surgery.beltSphere v)
  have hnγ : MDifferentiableAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, N)
      d.beltNormal (γ 0) := by
    rw [hpoint]
    exact hnormal.mdifferentiableAt (by simp)
  have hQA : Q.comp A = L := by
    have hh := mfderiv_comp 0 hnγ (hγ.mdifferentiableAt (by simp))
    rw [hpoint] at hh
    exact hh.symm.trans hnormalDerivative
  have hQAs : Surjective (Q.comp A) := hQA.symm ▸ hLs
  have hker : B.range = Q.ker := d.range_belt_derivative_eq_normal_kernel hf n v
  change Surjective (A.coprod B)
  intro z
  obtain ⟨x, hx⟩ := hQAs (Q z)
  have hmem : z - A x ∈ Q.ker := by
    change Q (z - A x) = 0
    change Q (A x) = Q z at hx
    rw [map_sub, hx, sub_self]
  rw [← hker] at hmem
  obtain ⟨w, hw⟩ := hmem
  change B w = z - A x at hw
  refine ⟨(x, w), ?_⟩
  change A x + B w = z
  rw [hw]
  abel

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
