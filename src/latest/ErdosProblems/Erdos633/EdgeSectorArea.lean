import ErdosProblems.Erdos633.VertexSectorAngle
import ErdosProblems.Erdos633.Split
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Local sectors at interior points and at open edges

The interior sector is a full unit disk. At an open edge, splitting the
triangle at the point gives two corner sectors with supplementary angles,
so their combined area is half the unit disk.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators EuclideanGeometry

theorem Triangle.localConeAt_eq_univ_of_interior (P : Triangle) (z : ℂ)
    (hz : z ∈ interior P.carrier) : P.localConeAt z = Set.univ := by
  have hp := (P.mem_interior_iff_barycentric z).mp hz
  apply Set.eq_univ_of_forall
  intro x i hi
  exact False.elim ((ne_of_gt (hp i)) hi)

theorem Triangle.localSectorArea_interior (P : Triangle) (z : ℂ)
    (hz : z ∈ interior P.carrier) : P.localSectorArea z = Real.pi := by
  rw [Triangle.localSectorArea, Triangle.localSector,
    P.localConeAt_eq_univ_of_interior z hz, Set.univ_inter, Complex.volume_ball]
  simp

theorem Triangle.localSectorArea_nonneg (P : Triangle) (z : ℂ) : 0 ≤ P.localSectorArea z :=
  ENNReal.toReal_nonneg

theorem Triangle.localSectorArea_le_pi (P : Triangle) (z : ℂ) :
    P.localSectorArea z ≤ Real.pi := by
  have h : volume (P.localSector z) ≤ volume (Metric.ball z 1) :=
    measure_mono Set.inter_subset_right
  have hf : volume (Metric.ball z (1 : ℝ)) ≠ ⊤ := by simp [Complex.volume_ball]
  have ht := ENNReal.toReal_mono hf h
  simpa only [Triangle.localSectorArea, Complex.volume_ball, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi] using ht

noncomputable def Triangle.splitDissection (P : Triangle) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) : TriangleDissection P 2 where
  tile := ![P.splitFirst r hr0, P.splitSecond r hr1]
  covers := by
    rw [← P.split_covers r hr0 hr1]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact P.split_disjoint r hr0 hr1
    · exact (P.split_disjoint r hr0 hr1).symm
    · exact False.elim (hij rfl)

theorem Triangle.splitPoint_eq_lineMap (P : Triangle) (r : ℝ) :
    P.coordinateEquiv (⟨0, r⟩ : ℂ) = AffineMap.lineMap P.a P.c r := by
  rw [Triangle.coordinateEquiv_apply, AffineMap.lineMap_apply]
  simp only [zero_smul, zero_add, vsub_eq_sub, vadd_eq_add]

theorem Triangle.localSectorArea_splitPoint (P : Triangle) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) :
    P.localSectorArea (P.coordinateEquiv (⟨0, r⟩ : ℂ)) = Real.pi / 2 := by
  let z := P.coordinateEquiv (⟨0, r⟩ : ℂ)
  let Q₁ := P.splitFirst r hr0
  let Q₂ := P.splitSecond r hr1
  have hz₁ : z ∈ Q₁.carrier := Q₁.vertex_mem_carrier 2
  have hz₂ : z ∈ Q₂.carrier := Q₂.vertex_mem_carrier 0
  have hz : z ∈ P.carrier := by
    rw [← P.split_covers r hr0 hr1]
    exact Or.inl hz₁
  have hmem : ∀ i : Fin 2, z ∈ ((P.splitDissection r hr0 hr1).tile i).carrier := by
    intro i
    fin_cases i
    · exact hz₁
    · exact hz₂
  have harea := (P.splitDissection r hr0 hr1).localSectorArea_eq_sum_of_mem_all z hz hmem
  simp only [Triangle.splitDissection, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero] at harea
  change P.localSectorArea z = Q₁.localSectorArea z + Q₂.localSectorArea z at harea
  have ha₁ : Q₁.localSectorArea z = Q₁.angleC / 2 := by
    simpa only [Q₁, Triangle.splitFirst_c] using Q₁.localSectorArea_c
  have ha₂ : Q₂.localSectorArea z = Q₂.angleA / 2 := Q₂.localSectorArea_a
  have hbetw : Sbtw ℝ P.a z P.c := by
    dsimp [z]
    rw [P.splitPoint_eq_lineMap]
    exact sbtw_lineMap_iff.mpr ⟨P.swapBC.a_ne_b, hr0, hr1⟩
  have hsup := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi P.b hbetw.angle₁₂₃_eq_pi
  have hang : Q₁.angleC + Q₂.angleA = Real.pi := by
    simp only [Q₁, Q₂, Triangle.angleC, Triangle.angleA, Triangle.splitFirst_a,
      Triangle.splitFirst_b, Triangle.splitFirst_c, Triangle.splitSecond_a,
      Triangle.splitSecond_b, Triangle.splitSecond_c]
    change ∠ P.a z P.b + ∠ P.b z P.c = Real.pi
    rw [EuclideanGeometry.angle_comm P.a z P.b]
    exact hsup
  rw [ha₁, ha₂] at harea
  change P.localSectorArea z = Real.pi / 2
  linarith

theorem Triangle.localSectorArea_openSegment_ac (P : Triangle) (z : ℂ)
    (hz : z ∈ openSegment ℝ P.a P.c) : P.localSectorArea z = Real.pi / 2 := by
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rw [← P.splitPoint_eq_lineMap]
  exact P.localSectorArea_splitPoint r hr.1 hr.2

theorem Triangle.localSectorArea_openSegment_ab (P : Triangle) (z : ℂ)
    (hz : z ∈ openSegment ℝ P.a P.b) : P.localSectorArea z = Real.pi / 2 := by
  have h := P.swapBC.localSectorArea_openSegment_ac z hz
  rw [P.swapBC.localSectorArea_eq_of_carrier_eq P P.swapBC_carrier z
    ((P.swapBC.convex_carrier.openSegment_subset
      (P.swapBC.vertex_mem_carrier 0) (P.swapBC.vertex_mem_carrier 2)) hz)] at h
  exact h

theorem Triangle.localSectorArea_openSegment_bc (P : Triangle) (z : ℂ)
    (hz : z ∈ openSegment ℝ P.b P.c) : P.localSectorArea z = Real.pi / 2 := by
  have h := P.rotate.localSectorArea_openSegment_ab z hz
  rw [P.rotate.localSectorArea_eq_of_carrier_eq P P.rotate_carrier z
    ((P.rotate.convex_carrier.openSegment_subset
      (P.rotate.vertex_mem_carrier 0) (P.rotate.vertex_mem_carrier 1)) hz)] at h
  exact h

end Erdos633
