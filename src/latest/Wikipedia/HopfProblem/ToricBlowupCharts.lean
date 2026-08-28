import Wikipedia.HopfProblem.ToricHexagon
import Wikipedia.HopfProblem.AffineBlowupManifold

/-!
# Pairing the six toric charts into affine blow-ups

The three odd rays of the hexagon subdivide the three cones of the
projective-plane fan. After reordering coordinates, each adjacent pair
has exactly the two incidence-model blow-up charts and their overlap.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

def blowupIndex (k : Fin 3) (b : Bool) : Fin 6 :=
  if b then ![1, 3, 5] k else ![0, 2, 4] k

def reorder (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) : CoordinateSpace 2 :=
  if k = 1 ∨ (k = 0 ∧ b = true) then ![z 1, z 0] else z

theorem reorder_involutive (k : Fin 3) (b : Bool) : Function.Involutive (reorder k b) := by
  intro z
  by_cases h : k = 1 ∨ (k = 0 ∧ b = true)
  · ext i
    fin_cases i <;> simp [reorder, h]
  · simp [reorder, h]

theorem reorder_holomorphic (k : Fin 3) (b : Bool) : ContDiff ℂ ω (reorder k b) := by
  change ContDiff ℂ ω (fun z : CoordinateSpace 2 =>
    if k = 1 ∨ (k = 0 ∧ b = true) then ![z 1, z 0] else z)
  by_cases h : k = 1 ∨ (k = 0 ∧ b = true)
  · simp only [if_pos h]
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_apply ℂ ℂ 1
    · exact contDiff_apply ℂ ℂ 0
  · simp only [if_neg h]
    exact contDiff_id

def reorderHomeomorph (k : Fin 3) (b : Bool) : CoordinateSpace 2 ≃ₜ CoordinateSpace 2 where
  toFun := reorder k b
  invFun := reorder k b
  left_inv := reorder_involutive k b
  right_inv := reorder_involutive k b
  continuous_toFun := (reorder_holomorphic k b).continuous
  continuous_invFun := (reorder_holomorphic k b).continuous

def blowupAffine (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) : rayDivisor 0 :=
  affineInclusion (zeroChart (blowupIndex k b)) (reorder k b z)

theorem blowupAffine_isOpenEmbedding (k : Fin 3) (b : Bool) :
    IsOpenEmbedding (blowupAffine k b) :=
  (affineInclusion_openEmbedding _).comp (reorderHomeomorph k b).isOpenEmbedding

theorem blowupAffine_holomorphic (k : Fin 3) (b : Bool) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (blowupAffine k b) :=
  (affineInclusion_holomorphic _).comp (reorder_holomorphic k b).contMDiff

def blowupVector (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) : CoordinateSpace 3 :=
  insertZero (zeroCoordinate (blowupIndex k b)) (reorder k b z)

@[simp] theorem blowupAffine_coe (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) :
    (blowupAffine k b z : Space) =
      inclusion (zeroTriangle (blowupIndex k b)) (blowupVector k b z) := rfl

theorem blowupVector_eq (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) :
    blowupVector k b z =
      if k = 0 then (if b then ![0, z 1, z 0] else ![0, z 0, z 1])
      else if k = 1 then (if b then ![z 1, z 0, 0] else ![z 1, 0, z 0])
      else (if b then ![z 0, 0, z 1] else ![z 0, z 1, 0]) := by
  fin_cases k <;> cases b <;> ext i <;> fin_cases i <;> rfl

theorem blowupTransition (k : Fin 3) (b : Bool) :
    transition (zeroTriangle (blowupIndex k b)) (zeroTriangle (blowupIndex k (!b))) =
      if k = 0 then !![1, 1, 0; 0, -1, 0; 0, 1, 1]
      else if (k = 1 ∧ b = false) ∨ (k = 2 ∧ b = true) then
        !![0, 0, -1; 1, 0, 1; 0, 1, 1]
      else !![1, 1, 0; 1, 0, 1; -1, 0, 0] := by
  fin_cases k <;> cases b <;> decide

theorem blowupVector_mem_changeSource (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) :
    blowupVector k b z ∈ (chartChange (zeroTriangle (blowupIndex k b))
      (zeroTriangle (blowupIndex k (!b)))).source ↔
        z (AffineBlowup.directionCoordinate b) ≠ 0 := by
  rw [chartChange_source, blowupTransition, blowupVector_eq]
  fin_cases k <;> cases b <;>
    norm_num [domain, Fin.forall_fin_succ, AffineBlowup.directionCoordinate,
      Fin.ext_iff, Matrix.cons_val] <;> rfl

theorem blowupVector_change (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) :
    chartChange (zeroTriangle (blowupIndex k b)) (zeroTriangle (blowupIndex k (!b)))
      (blowupVector k b z) =
        blowupVector k (!b) (AffineBlowup.crossCoordinates b z) := by
  change monomial _ _ = _
  rw [blowupTransition]
  fin_cases k <;> cases b <;> ext i <;> fin_cases i <;>
    simp [monomial, Fin.prod_univ_succ, blowupVector_eq,
      AffineBlowup.crossCoordinates, mul_comm, Fin.ext_iff, Matrix.cons_val]

theorem blowupAffine_crossCoordinates (k : Fin 3) (b : Bool) (z : CoordinateSpace 2)
    (hz : z (AffineBlowup.directionCoordinate b) ≠ 0) :
    blowupAffine k (!b) (AffineBlowup.crossCoordinates b z) = blowupAffine k b z := by
  apply Subtype.ext
  symm
  apply (inclusion_eq_iff _ _ _ _).mpr
  exact ⟨(blowupVector_mem_changeSource k b z).mpr hz, blowupVector_change k b z⟩

theorem blowupAffine_cross_eq_iff (k : Fin 3) (b : Bool) (z w : CoordinateSpace 2) :
    blowupAffine k b z = blowupAffine k (!b) w ↔
      z (AffineBlowup.directionCoordinate b) ≠ 0 ∧ w = AffineBlowup.crossCoordinates b z := by
  constructor
  · intro h
    have ht := (inclusion_eq_iff _ _ _ _).mp (congrArg Subtype.val h)
    have hz := (blowupVector_mem_changeSource k b z).mp ht.1
    refine ⟨hz, (blowupAffine_isOpenEmbedding k (!b)).injective ?_⟩
    exact h.symm.trans (blowupAffine_crossCoordinates k b z hz).symm
  · rintro ⟨hz, rfl⟩
    exact (blowupAffine_crossCoordinates k b z hz).symm

theorem blowupAffine_jointly_surjective (x : rayDivisor 0) :
    ∃ k b z, blowupAffine k b z = x := by
  obtain ⟨c, z, rfl⟩ := affineInclusion_jointly_surjective x
  obtain ⟨i, rfl⟩ := zeroChart_surjective c
  have h (k : Fin 3) (b : Bool) :
      blowupAffine k b (reorder k b z) = affineInclusion (zeroChart (blowupIndex k b)) z := by
    unfold blowupAffine
    rw [reorder_involutive]
  fin_cases i
  · exact ⟨0, false, _, h 0 false⟩
  · exact ⟨0, true, _, h 0 true⟩
  · exact ⟨1, false, _, h 1 false⟩
  · exact ⟨1, true, _, h 1 true⟩
  · exact ⟨2, false, _, h 2 false⟩
  · exact ⟨2, true, _, h 2 true⟩

end Wikipedia.HopfProblem.ToricComponent
