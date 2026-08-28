import Wikipedia.HopfProblem.DegreeCollapseBeltBranchNeighborhood

/-!
# An actual local arc with exactly one original belt crossing

The native Morse coordinates construct a smooth arc in the actual upper
level. It is injective on the full closed parameter interval and meets the
original belt sphere exactly at parameter zero and its prescribed belt
direction. Transversality and closing the arc into a loop are separate steps.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

open Classical in
def nativeBeltArc (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) : M :=
  (S.data q).chart.splitChart.symm (BeltPassage.upper (S.data q).radius s u.val v.val)

open Classical in
theorem nativeBeltArc_coordinates_mem_target
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    BeltPassage.upper (S.data q).radius s u.val v.val ∈ (S.data q).chart.splitChart.target :=
  (S.data q).block (BeltPassage.upper_mem_block (S.data q).radius_pos hs
    (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property))

open Classical in
theorem nativeBeltArc_height
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    f (nativeBeltArc S q u v s) = S.toSurgeryWindows.upper q := by
  rw [nativeBeltArc, (S.data q).chart.splitChart_inverse_equation
    (nativeBeltArc_coordinates_mem_target S q u v hs)]
  have hh := BeltPassage.upper_height (S.data q).radius s
    (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property)
  change -‖(BeltPassage.upper (S.data q).radius s u.val v.val).1‖ ^ 2 +
    ‖(BeltPassage.upper (S.data q).radius s u.val v.val).2‖ ^ 2 = (S.data q).radius ^ 2 at hh
  dsimp only [SurgeryWindows.upper]
  linarith

open Classical in
theorem nativeBeltArc_zero
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    nativeBeltArc S q u v 0 = ((S.data q).surgery.beltSphere v).val := by
  rw [nativeBeltArc, BeltPassage.upper_zero, (S.data q).belt_eq,
    (S.data q).chart.beltCoreMap_coe]

open Classical in
theorem nativeBeltArc_belt_eq_iff
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v w : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val ↔ s = 0 ∧ v = w := by
  constructor
  · intro heq
    have hzero := nativeBeltArc_coordinates_mem_target S q u w (s := 0) (by simp)
    rw [BeltPassage.upper_zero] at hzero
    rw [nativeBeltArc, (S.data q).belt_eq, (S.data q).chart.beltCoreMap_coe] at heq
    have hcoords := (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
      (nativeBeltArc_coordinates_mem_target S q u v hs) hzero heq
    have hu : u.val ≠ 0 := by
      intro h
      have hn := mem_sphere_zero_iff_norm.mp u.property
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    have hs0 : s = 0 := by
      have hfst : ((S.data q).radius * s) • u.val = 0 := congrArg Prod.fst hcoords
      have hz : (S.data q).radius * s = 0 :=
        (smul_eq_zero.mp hfst).resolve_right hu
      exact (mul_eq_zero.mp hz).resolve_left (S.data q).radius_pos.ne'
    refine ⟨hs0, ?_⟩
    rw [hs0, BeltPassage.upper_zero] at hcoords
    exact Subtype.ext (smul_right_injective _ (S.data q).radius_pos.ne'
      (congrArg Prod.snd hcoords))
  · rintro ⟨rfl, rfl⟩
    exact nativeBeltArc_zero S q u v

open Classical in
theorem nativeBeltArc_injOn
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    InjOn (nativeBeltArc S q u v) (Icc (-1 : ℝ) 1) := by
  intro s hs t ht hst
  have hcoords := (S.data q).chart.splitChart.symm.toPartialEquiv.injOn
    (nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr hs))
    (nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr ht)) hst
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hfst : ((S.data q).radius * s) • u.val = ((S.data q).radius * t) • u.val :=
    congrArg Prod.fst hcoords
  exact mul_left_cancel₀ (S.data q).radius_pos.ne' (smul_left_injective ℝ hu hfst)

open Classical in
theorem nativeBeltArc_contMDiffOn
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (nativeBeltArc S q u v) (Ioo (-1 : ℝ) 1) := by
  apply (S.data q).chart.splitChart.contMDiffOn_invFun.comp
    (BeltPassage.contDiff_upper (S.data q).radius u.val v.val).contMDiff.contMDiffOn
  intro s hs
  exact nativeBeltArc_coordinates_mem_target S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
