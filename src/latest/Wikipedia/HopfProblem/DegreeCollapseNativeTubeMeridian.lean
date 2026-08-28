import Wikipedia.HopfProblem.DegreeCollapseBoundaryUnitCoefficient
import Wikipedia.SmoothSixDPoincare.PuncturedBallHomotopy

/-!
# The original belt tube contracts to the native meridian

Use the uniform normal disk already contained in the original Morse block.
Radial contraction stays in the punctured normal disk. A nullhomotopy of
the positive direction therefore identifies the actual tube map with the
native meridian composed with its normalized normal map.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

def nativeBeltTubeSource (d : MorseSurgeryData E f p) :
    C(sphere (0 : d.chart.PositiveCoordinates) 1 ×
      PuncturedBall.Space d.chart.NegativeCoordinates 1,
      d.chart.beltSource d.radius d.radius_pos) where
  toFun z := ⟨(z.1, z.2.val), d.chart.enlarged_closed_belt_subset_source
    d.radius d.radius_pos d.block ⟨mem_univ _, by
      rw [mem_closedBall_zero_iff]
      exact z.2.property.2.le.trans (by norm_num)⟩⟩
  continuous_toFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def nativeBeltTubeInComplement (d : MorseSurgeryData E f p) :
    C(sphere (0 : d.chart.PositiveCoordinates) 1 ×
      PuncturedBall.Space d.chart.NegativeCoordinates 1,
      ((range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) where
  toFun z := by
    let y := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (nativeBeltTubeSource d z)
    refine ⟨y.val, ?_⟩
    intro hy
    have hz := (d.beltNormal_eq_zero_iff y.property).mpr hy
    have heq : d.beltNormal y.val = d.radius • z.2.val :=
      d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (nativeBeltTubeSource d z)
    rw [heq] at hz
    exact (smul_ne_zero d.radius_pos.ne' z.2.property.1) hz
  continuous_toFun := (continuous_subtype_val.comp
    ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp
      (nativeBeltTubeSource d).continuous)).subtype_mk _

def nativeBeltTubeMeridian (d : MorseSurgeryData E f p)
    (v : sphere (0 : d.chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    C(sphere (0 : d.chart.NegativeCoordinates) 1,
      ((range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    ((ContinuousMap.const _ v).prodMk (PuncturedBall.fromSphere 1 r hr hr1))

theorem nativeBeltTube_homotopic_meridian (d : MorseSurgeryData E f p)
    {X : Type} [TopologicalSpace X]
    (a : C(X, sphere (0 : d.chart.PositiveCoordinates) 1))
    (b : C(X, PuncturedBall.Space d.chart.NegativeCoordinates 1))
    (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    (ha : a.Homotopic (ContinuousMap.const _ v)) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ((nativeBeltTubeInComplement d).comp (a.prodMk b)).Homotopic
      ((nativeBeltTubeMeridian d v r hr hr1).comp ((PuncturedBall.toSphere 1).comp b)) := by
  let c := (PuncturedBall.toSphere 1).comp b
  let b' := (PuncturedBall.fromSphere 1 r hr hr1).comp c
  have hb : b.Homotopic b' := by
    have H := (PuncturedBall.deformation 1 r hr hr1).compContinuousMap b
    exact ⟨H⟩
  have hpair := ha.prodMk hb
  have hh := (Homotopic.refl (nativeBeltTubeInComplement d)).comp hpair
  have heq : (nativeBeltTubeInComplement d).comp ((ContinuousMap.const _ v).prodMk b') =
      (nativeBeltTubeMeridian d v r hr hr1).comp c := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [heq] at hh
  exact hh

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem nativeBeltTubeMeridian_eq (S : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    nativeBeltTubeMeridian (S.data q) v r hr hr1 =
      nativeUpperMeridianInComplement S q v ⟨r, hr.le, hr1.le⟩ hr := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  change (S.data q).chart.splitChart.symm
    ((MorseHandle.ambientMap (S.data q).radius (v.val, r • u.val)).swap) =
      (S.data q).chart.splitChart.symm (BeltPassage.upper (S.data q).radius r u.val v.val)
  congr 1
  simp only [MorseHandle.ambientMap, BeltPassage.upper, Prod.swap, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one, smul_smul]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
