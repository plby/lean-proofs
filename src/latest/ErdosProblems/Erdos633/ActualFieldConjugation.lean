import ErdosProblems.Erdos633.FieldConjugation
import ErdosProblems.Erdos633.ReferenceRelabelling

/-!
# Conjugating an actual congruent tiling with field coordinates

The ordered side identities required by field conjugation are extracted from
the original ambient isometries. Thus an actual tiling with field-valued outer,
reference, and labelled tile vertices has an actual congruent conjugate tiling,
with the same number of pieces and the original labelled vertex images.
-/

namespace Erdos633

noncomputable def CongruentTiling.labelledTiling
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) : CongruentTiling P R N where
  toTriangleDissection := T.labelledDissection
  congruent := fun i => ⟨T.tileIsometry i, (R.mapIsometry_carrier (T.tileIsometry i)).symm⟩

theorem CongruentTiling.labelledTile_normSq
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (i : Fin N) (j k : Fin 3) :
    Complex.normSq ((T.labelledTile i).vertex j - (T.labelledTile i).vertex k) =
      Complex.normSq (R.vertex j - R.vertex k) := by
  rw [normSq_sub_eq_dist_sq, normSq_sub_eq_dist_sq]
  change dist ((R.mapIsometry (T.tileIsometry i)).vertex k)
    ((R.mapIsometry (T.tileIsometry i)).vertex j) ^ 2 = _
  rw [R.vertex_mapIsometry, R.vertex_mapIsometry, (T.tileIsometry i).dist_eq]

theorem CongruentTiling.exists_conjugate_coordinates
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (F : Subfield ℝ) (σ : F →+* ℝ)
    (hP : P.CoordinatesIn F) (hR : R.CoordinatesIn F)
    (hQ : ∀ i : Fin N, (T.labelledTile i).CoordinatesIn F) :
    ∃ U : CongruentTiling ((P.toFieldTriangle F hP).realize σ)
        ((R.toFieldTriangle F hR).realize σ) N,
      (∀ i : Fin N, (T.labelledTile i).VertexImage (U.tile i)
        (embeddingPointMap (algebraMap F ℝ) σ)) ∧
      Set.InjOn (embeddingPointMap (algebraMap F ℝ) σ) T.labelledDissection.vertexFinset := by
  let τ := algebraMap F ℝ
  let PF := P.toFieldTriangle F hP
  let RF := R.toFieldTriangle F hR
  let QF (i : Fin N) := (T.labelledTile i).toFieldTriangle F (hQ i)
  have hPF : PF.realize τ = P := P.toFieldTriangle_realize F hP
  have hRF : RF.realize τ = R := R.toFieldTriangle_realize F hR
  have hQF (i : Fin N) : (QF i).realize τ = T.labelledTile i :=
    (T.labelledTile i).toFieldTriangle_realize F (hQ i)
  let T₀ : CongruentTiling (PF.realize τ) (RF.realize τ) N :=
    (T.labelledTiling.of_reference_carrier_eq (congrArg Triangle.carrier hRF)).of_carrier_eq
      (congrArg Triangle.carrier hPF)
  have htiles (i : Fin N) : T₀.tile i = (QF i).realize τ := (hQF i).symm
  have hab (i : Fin N) : Complex.normSq ((RF.realize τ).b - (RF.realize τ).a) =
      Complex.normSq (((QF i).realize τ).b - ((QF i).realize τ).a) := by
    rw [hRF, hQF i]
    exact (T.labelledTile_normSq i 1 0).symm
  have hac (i : Fin N) : Complex.normSq ((RF.realize τ).c - (RF.realize τ).a) =
      Complex.normSq (((QF i).realize τ).c - ((QF i).realize τ).a) := by
    rw [hRF, hQF i]
    exact (T.labelledTile_normSq i 2 0).symm
  have hbc (i : Fin N) : Complex.normSq ((RF.realize τ).c - (RF.realize τ).b) =
      Complex.normSq (((QF i).realize τ).c - ((QF i).realize τ).b) := by
    rw [hRF, hQF i]
    exact (T.labelledTile_normSq i 2 1).symm
  let U := T₀.conjugateFieldTriangles PF RF τ σ QF htiles hab hac hbc
  refine ⟨U, ?_, ?_⟩
  · intro i
    change (T.labelledTile i).VertexImage ((QF i).realize σ) (embeddingPointMap τ σ)
    rw [← hQF i]
    exact (QF i).realize_vertexImage τ σ
  · exact (embeddingPointMap_injOn τ σ).mono
      (T.labelledDissection.vertices_in_fieldPoint_range τ QF (fun i => (hQF i).symm))

theorem FieldTriangle.realize_vertex_eq_iff {F : Type*} [Field F]
    (P Q : FieldTriangle F) (τ σ : F →+* ℝ) (j k : Fin 3) :
    (P.realize σ).vertex j = (Q.realize σ).vertex k ↔
      (P.realize τ).vertex j = (Q.realize τ).vertex k := by
  simp only [FieldTriangle.realize_vertex, (fieldPoint_injective σ).eq_iff,
    (fieldPoint_injective τ).eq_iff]

open Classical in
theorem field_outer_corner_count_invariant {F : Type*} [Field F]
    (P : FieldTriangle F) {N : ℕ} (Q : Fin N → FieldTriangle F)
    (τ σ : F →+* ℝ) (j k : Fin 3) :
    (Finset.univ.filter fun i : Fin N => ((Q i).realize σ).vertex k =
      (P.realize σ).vertex j).card =
    (Finset.univ.filter fun i : Fin N => ((Q i).realize τ).vertex k =
      (P.realize τ).vertex j).card := by
  classical
  congr 1
  apply Finset.filter_congr
  intro i _
  exact (Q i).realize_vertex_eq_iff P τ σ k j

end Erdos633
