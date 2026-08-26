import ErdosProblems.Erdos633.LocalGeometry

/-!
# Consistent angle labels in an actual congruent tiling

The isometries in the definition of a tiling provide ordered copies of the
reference triangle. Their carriers are the original tile carriers, including
reflected copies. The angle labels are therefore geometric, not an extra
assumption about the dissection.
-/

namespace Erdos633

open scoped BigOperators EuclideanGeometry

noncomputable def Triangle.cornerAngle (P : Triangle) : Fin 3 → ℝ :=
  ![P.angleA, P.angleB, P.angleC]

theorem Triangle.cornerAngle_pos (P : Triangle) (i : Fin 3) : 0 < P.cornerAngle i := by
  fin_cases i
  · exact P.angleA_pos
  · exact P.angleB_pos
  · exact P.angleC_pos

theorem Triangle.sum_cornerAngle (P : Triangle) : ∑ i, P.cornerAngle i = Real.pi := by
  simpa only [Triangle.cornerAngle, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, ← add_assoc] using P.angle_sum

theorem Triangle.vertex_mapIsometry (P : Triangle) (e : ℂ ≃ᵢ ℂ) (i : Fin 3) :
    (P.mapIsometry e).vertex i = e (P.vertex i) := by
  fin_cases i <;> rfl

theorem Triangle.cornerAngle_mapIsometry (P : Triangle) (e : ℂ ≃ᵢ ℂ) (i : Fin 3) :
    (P.mapIsometry e).cornerAngle i = P.cornerAngle i := by
  fin_cases i
  · exact e.toRealAffineIsometryEquiv.toAffineIsometry.angle_map P.b P.a P.c
  · exact e.toRealAffineIsometryEquiv.toAffineIsometry.angle_map P.a P.b P.c
  · exact e.toRealAffineIsometryEquiv.toAffineIsometry.angle_map P.a P.c P.b

theorem Triangle.range_vertex_eq_of_carrier_eq (P Q : Triangle) (h : P.carrier = Q.carrier) :
    Set.range P.vertex = Set.range Q.vertex := by
  rw [← P.extremePoints_carrier, ← Q.extremePoints_carrier, h]

noncomputable def CongruentTiling.tileIsometry {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) : ℂ ≃ᵢ ℂ := Classical.choose (T.congruent i)

theorem CongruentTiling.tileIsometry_image {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) :
    T.tileIsometry i '' R.carrier = (T.tile i).carrier := Classical.choose_spec (T.congruent i)

noncomputable def CongruentTiling.labelledTile {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) : Triangle := R.mapIsometry (T.tileIsometry i)

theorem CongruentTiling.labelledTile_carrier {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) : (T.labelledTile i).carrier = (T.tile i).carrier := by
  rw [CongruentTiling.labelledTile, Triangle.mapIsometry_carrier, T.tileIsometry_image]

theorem CongruentTiling.labelledTile_cornerAngle {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (i : Fin N) (k : Fin 3) :
    (T.labelledTile i).cornerAngle k = R.cornerAngle k :=
  R.cornerAngle_mapIsometry (T.tileIsometry i) k

noncomputable def CongruentTiling.labelledDissection {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) : TriangleDissection P N where
  tile := T.labelledTile
  covers := by simp_rw [T.labelledTile_carrier]; exact T.covers
  disjoint := by
    intro i j hij
    simp_rw [T.labelledTile_carrier]
    exact T.disjoint hij

theorem CongruentTiling.labelled_vertexFinset {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) :
    T.labelledDissection.vertexFinset = T.toTriangleDissection.vertexFinset := by
  ext z
  rw [TriangleDissection.mem_vertexFinset, TriangleDissection.mem_vertexFinset]
  constructor
  · rintro ⟨i, k, hk⟩
    have hr := (T.labelledTile i).range_vertex_eq_of_carrier_eq
      (T.tile i) (T.labelledTile_carrier i)
    have hmem : z ∈ Set.range (T.labelledTile i).vertex := ⟨k, hk⟩
    rw [hr] at hmem
    exact ⟨i, hmem⟩
  · rintro ⟨i, k, hk⟩
    have hr := (T.labelledTile i).range_vertex_eq_of_carrier_eq
      (T.tile i) (T.labelledTile_carrier i)
    have hmem : z ∈ Set.range (T.tile i).vertex := ⟨k, hk⟩
    rw [← hr] at hmem
    exact ⟨i, hmem⟩

end Erdos633
