import ErdosProblems.Erdos633.DissectionCornerCounts

/-!
# Conjugate angle equations with the original outer-corner counts

Ordered squared side identities preserve labelled angles after a real field
embedding. Combined with geometric conjugation and injectivity on the original
vertices, this proves the full conjugate outer-angle equation using the counts
of the original congruent tiling. No conjugate tiling or angle equation is
assumed as an extra hypothesis.
-/

namespace Erdos633

open scoped BigOperators

theorem Triangle.isometryOfNormSq_vertex (P Q : Triangle) (hab hac hbc) (k : Fin 3) :
    P.isometryOfNormSq Q hab hac hbc (P.vertex k) = Q.vertex k := by
  fin_cases k
  · change P.isometryOfNormSq Q hab hac hbc P.a = Q.a
    rw [Triangle.isometryOfNormSq_apply, ← P.coordinateEquiv_zero,
      P.coordinateEquiv.symm_apply_apply, Q.coordinateEquiv_zero]
  · change P.isometryOfNormSq Q hab hac hbc P.b = Q.b
    rw [Triangle.isometryOfNormSq_apply, ← P.coordinateEquiv_one,
      P.coordinateEquiv.symm_apply_apply, Q.coordinateEquiv_one]
  · change P.isometryOfNormSq Q hab hac hbc P.c = Q.c
    rw [Triangle.isometryOfNormSq_apply, ← P.coordinateEquiv_I,
      P.coordinateEquiv.symm_apply_apply, Q.coordinateEquiv_I]

theorem Triangle.cornerAngle_eq_of_normSq (P Q : Triangle)
    (hab : Complex.normSq (P.b - P.a) = Complex.normSq (Q.b - Q.a))
    (hac : Complex.normSq (P.c - P.a) = Complex.normSq (Q.c - Q.a))
    (hbc : Complex.normSq (P.c - P.b) = Complex.normSq (Q.c - Q.b)) (k : Fin 3) :
    P.cornerAngle k = Q.cornerAngle k := by
  let e := P.isometryOfNormSq Q hab hac hbc
  have heq : P.mapIsometry e = Q := by
    apply Triangle.ext
    · exact P.isometryOfNormSq_vertex Q hab hac hbc 0
    · exact P.isometryOfNormSq_vertex Q hab hac hbc 1
    · exact P.isometryOfNormSq_vertex Q hab hac hbc 2
  have h := P.cornerAngle_mapIsometry e k
  rw [heq] at h
  exact h.symm

theorem normSq_fieldPoint_sub_transfer {F : Type*} [Field F]
    (τ σ : F →+* ℝ) (p q r s : F × F)
    (h : Complex.normSq (fieldPoint τ q - fieldPoint τ p) =
      Complex.normSq (fieldPoint τ s - fieldPoint τ r)) :
    Complex.normSq (fieldPoint σ q - fieldPoint σ p) =
      Complex.normSq (fieldPoint σ s - fieldPoint σ r) := by
  rw [normSq_fieldPoint_sub, normSq_fieldPoint_sub]
  exact congrArg σ (fieldSquaredDistance_eq_of_embedding τ p q r s h)

theorem FieldTriangle.realize_cornerAngle_eq_of_normSq {F : Type*} [Field F]
    (P Q : FieldTriangle F) (τ σ : F →+* ℝ)
    (hab : Complex.normSq ((P.realize τ).b - (P.realize τ).a) =
      Complex.normSq ((Q.realize τ).b - (Q.realize τ).a))
    (hac : Complex.normSq ((P.realize τ).c - (P.realize τ).a) =
      Complex.normSq ((Q.realize τ).c - (Q.realize τ).a))
    (hbc : Complex.normSq ((P.realize τ).c - (P.realize τ).b) =
      Complex.normSq ((Q.realize τ).c - (Q.realize τ).b)) (k : Fin 3) :
    (P.realize σ).cornerAngle k = (Q.realize σ).cornerAngle k :=
  (P.realize σ).cornerAngle_eq_of_normSq (Q.realize σ)
    (normSq_fieldPoint_sub_transfer τ σ P.a P.b Q.a Q.b hab)
    (normSq_fieldPoint_sub_transfer τ σ P.a P.c Q.a Q.c hac)
    (normSq_fieldPoint_sub_transfer τ σ P.b P.c Q.b Q.c hbc) k

theorem Triangle.VertexImage.unique {P Q S : Triangle} {f : ℂ → ℂ}
    (hQ : P.VertexImage Q f) (hS : P.VertexImage S f) : Q = S :=
  Triangle.ext ((hQ 0).trans (hS 0).symm) ((hQ 1).trans (hS 1).symm)
    ((hQ 2).trans (hS 2).symm)

theorem Triangle.toFieldTriangle_vertexImage (P : Triangle) (F : Subfield ℝ)
    (σ : F →+* ℝ) (hP : P.CoordinatesIn F) :
    P.VertexImage ((P.toFieldTriangle F hP).realize σ)
      (embeddingPointMap (algebraMap F ℝ) σ) := by
  have h := (P.toFieldTriangle F hP).realize_vertexImage (algebraMap F ℝ) σ
  rwa [P.toFieldTriangle_realize F hP] at h

theorem CongruentTiling.conjugate_outer_angle_total
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (F : Subfield ℝ) (σ : F →+* ℝ)
    (hP : P.CoordinatesIn F) (hR : R.CoordinatesIn F)
    (hQ : ∀ i : Fin N, (T.labelledTile i).CoordinatesIn F) :
    (∑ k : Fin 3, (T.outerCornerCount k : ℝ) *
      ((R.toFieldTriangle F hR).realize σ).cornerAngle k) = Real.pi := by
  obtain ⟨U, hU, hinj⟩ := T.exists_conjugate_coordinates F σ hP hR hQ
  let τ := algebraMap F ℝ
  let RF := R.toFieldTriangle F hR
  let QF (i : Fin N) := (T.labelledTile i).toFieldTriangle F (hQ i)
  have hRF : RF.realize τ = R := R.toFieldTriangle_realize F hR
  have hQF (i : Fin N) : (QF i).realize τ = T.labelledTile i :=
    (T.labelledTile i).toFieldTriangle_realize F (hQ i)
  have htarget (i : Fin N) : U.tile i = (QF i).realize σ :=
    (hU i).unique ((T.labelledTile i).toFieldTriangle_vertexImage F σ (hQ i))
  have hθ (i : Fin N) (k : Fin 3) :
      (U.tile i).cornerAngle k = (RF.realize σ).cornerAngle k := by
    rw [htarget i]
    symm
    apply RF.realize_cornerAngle_eq_of_normSq (QF i) τ σ _ _ _ k
    · rw [hRF, hQF i]
      exact (T.labelledTile_normSq i 1 0).symm
    · rw [hRF, hQF i]
      exact (T.labelledTile_normSq i 2 0).symm
    · rw [hRF, hQF i]
      exact (T.labelledTile_normSq i 2 1).symm
  have h := T.labelledDissection.transported_outer_angle_total U.toTriangleDissection
    (embeddingPointMap τ σ) hinj (P.toFieldTriangle_vertexImage F σ hP) hU
    (RF.realize σ).cornerAngle hθ
  simpa only [T.labelledDissection_outerCornerCount] using h

theorem CongruentTiling.conjugate_outer_angle_total_of_rotations
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (F : Subfield ℝ) (σ : F →+* ℝ) (hR : R.CoordinatesIn F)
    (ha : P.a ∈ complexCoordinateSubfield F)
    (hbase : P.unitEdgeVector 2 ∈ complexCoordinateSubfield F)
    (hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hc : R.sideLength 2 ∈ F) :
    (∑ k : Fin 3, (T.outerCornerCount k : ℝ) *
      ((R.toFieldTriangle F hR).realize σ).cornerAngle k) = Real.pi := by
  obtain ⟨hP, hQ⟩ := T.coefficient_field_vertices F ha hbase hA hB hc
  exact T.conjugate_outer_angle_total F σ hP hR hQ

theorem CongruentTiling.conjugate_angle_multiplicity_lt_pi
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (F : Subfield ℝ) (σ : F →+* ℝ)
    (hP : P.CoordinatesIn F) (hR : R.CoordinatesIn F)
    (hQ : ∀ i : Fin N, (T.labelledTile i).CoordinatesIn F)
    (k j : Fin 3) (hkj : k ≠ j) (hj : 0 < T.outerCornerCount j) :
    (T.outerCornerCount k : ℝ) * ((R.toFieldTriangle F hR).realize σ).cornerAngle k <
      Real.pi := by
  let S := (R.toFieldTriangle F hR).realize σ
  have hsum := T.conjugate_outer_angle_total F σ hP hR hQ
  have hpair := Finset.add_le_sum
    (fun l (_ : l ∈ (Finset.univ : Finset (Fin 3))) =>
      mul_nonneg (Nat.cast_nonneg (T.outerCornerCount l)) (S.cornerAngle_pos l).le)
    (Finset.mem_univ k) (Finset.mem_univ j) hkj
  change (T.outerCornerCount k : ℝ) * S.cornerAngle k +
    (T.outerCornerCount j : ℝ) * S.cornerAngle j ≤
    ∑ l : Fin 3, (T.outerCornerCount l : ℝ) * S.cornerAngle l at hpair
  have hpos : 0 < (T.outerCornerCount j : ℝ) * S.cornerAngle j :=
    mul_pos (by exact_mod_cast hj) (S.cornerAngle_pos j)
  change (T.outerCornerCount k : ℝ) * S.cornerAngle k < Real.pi
  linarith

end Erdos633
