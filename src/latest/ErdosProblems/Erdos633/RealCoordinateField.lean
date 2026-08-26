import ErdosProblems.Erdos633.DirectionField
import ErdosProblems.Erdos633.FieldEmbeddingGeometry
import ErdosProblems.Erdos633.NormalizedSides

/-!
# Real coefficient fields of the edge vectors of a tiling

Complex numbers whose real and imaginary coordinates lie in a real subfield
form a subfield. The sine rule and the actual boundary counts then put all
side lengths, outer vertices, and labelled tile-edge vectors in the same
coefficient field. Only one outer vertex and one outer unit direction are
used as coordinate inputs.
-/

namespace Erdos633

open scoped BigOperators

def complexCoordinateSubfield (F : Subfield ℝ) : Subfield ℂ where
  carrier := {z | z.re ∈ F ∧ z.im ∈ F}
  zero_mem' := ⟨F.zero_mem, F.zero_mem⟩
  one_mem' := ⟨F.one_mem, F.zero_mem⟩
  add_mem' := by
    intro z w hz hw
    exact ⟨F.add_mem hz.1 hw.1, F.add_mem hz.2 hw.2⟩
  neg_mem' := by
    intro z hz
    exact ⟨F.neg_mem hz.1, F.neg_mem hz.2⟩
  mul_mem' := by
    intro z w hz hw
    exact ⟨F.sub_mem (F.mul_mem hz.1 hw.1) (F.mul_mem hz.2 hw.2),
      F.add_mem (F.mul_mem hz.1 hw.2) (F.mul_mem hz.2 hw.1)⟩
  inv_mem' := by
    intro z hz
    have hn : Complex.normSq z ∈ F := F.add_mem (F.mul_mem hz.1 hz.1)
      (F.mul_mem hz.2 hz.2)
    exact ⟨by rw [Complex.inv_re]; exact F.div_mem hz.1 hn,
      by rw [Complex.inv_im]; exact F.div_mem (F.neg_mem hz.2) hn⟩

@[simp] theorem mem_complexCoordinateSubfield (F : Subfield ℝ) (z : ℂ) :
    z ∈ complexCoordinateSubfield F ↔ z.re ∈ F ∧ z.im ∈ F := Iff.rfl

theorem ofReal_mem_complexCoordinateSubfield (F : Subfield ℝ) {r : ℝ} (hr : r ∈ F) :
    (r : ℂ) ∈ complexCoordinateSubfield F := ⟨hr, F.zero_mem⟩

theorem smul_mem_complexCoordinateSubfield (F : Subfield ℝ) {r : ℝ} {z : ℂ}
    (hr : r ∈ F) (hz : z ∈ complexCoordinateSubfield F) :
    r • z ∈ complexCoordinateSubfield F := by
  rw [Complex.real_smul]
  exact (complexCoordinateSubfield F).mul_mem (ofReal_mem_complexCoordinateSubfield F hr) hz

theorem exp_angle_mem_complexCoordinateSubfield_iff (F : Subfield ℝ) (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) ∈ complexCoordinateSubfield F ↔
      Real.cos θ ∈ F ∧ Real.sin θ ∈ F := by
  rw [mem_complexCoordinateSubfield, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

theorem Triangle.sideLengths_mem_of_rotations (P : Triangle) (F : Subfield ℝ)
    (hA : Complex.exp ((P.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hB : Complex.exp ((P.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hc : P.sideLength 2 ∈ F) : ∀ k : Fin 3, P.sideLength k ∈ F := by
  have hC := P.angleC_rotation_mem_subfield (complexCoordinateSubfield F) hA hB
  have ha := ((exp_angle_mem_complexCoordinateSubfield_iff F P.angleA).mp hA).2
  have hb := ((exp_angle_mem_complexCoordinateSubfield_iff F P.angleB).mp hB).2
  have hg := ((exp_angle_mem_complexCoordinateSubfield_iff F P.angleC).mp hC).2
  have hs : ∀ k : Fin 3, Real.sin (P.cornerAngle k) ∈ F := by
    intro k
    fin_cases k
    · simpa [Triangle.cornerAngle] using ha
    · simpa [Triangle.cornerAngle] using hb
    · simpa [Triangle.cornerAngle] using hg
  intro k
  rw [P.sideLength_eq_sineScale, Triangle.sineScale]
  exact F.mul_mem (F.div_mem hc hg) (hs k)

theorem Triangle.orientationSign_mem_subfield (P : Triangle) (F : Subfield ℝ) :
    P.orientationSign ∈ F := by
  unfold Triangle.orientationSign
  split_ifs
  · exact F.one_mem
  · exact F.neg_mem F.one_mem

theorem Triangle.edgeVector_mem_of_unit (P : Triangle) (F : Subfield ℝ) (k : Fin 3)
    (hs : P.sideLength k ∈ F) (hu : P.unitEdgeVector k ∈ complexCoordinateSubfield F) :
    P.edgeVector k ∈ complexCoordinateSubfield F := by
  have he : P.sideLength k • P.unitEdgeVector k = P.orientedEdgeVector k := by
    rw [Triangle.unitEdgeVector, smul_smul, mul_inv_cancel₀ (ne_of_gt (P.sideLength_pos k)),
      one_smul]
  have ho : P.orientationSign • P.orientedEdgeVector k = P.edgeVector k := by
    rw [Triangle.orientedEdgeVector, smul_smul, P.orientationSign_mul_self, one_smul]
  rw [← ho, ← he]
  exact smul_mem_complexCoordinateSubfield F (P.orientationSign_mem_subfield F)
    (smul_mem_complexCoordinateSubfield F hs hu)

theorem CongruentTiling.outer_sideLengths_mem_subfield
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (F : Subfield ℝ)
    (hR : ∀ k : Fin 3, R.sideLength k ∈ F) :
    ∀ k : Fin 3, P.sideLength k ∈ F := by
  intro k
  rw [T.boundary_side_count_equation]
  apply F.sum_mem
  intro l _
  exact F.mul_mem (natCast_mem F _) (hR l)

theorem Triangle.coordinatesIn_of_a_and_edgeVectors (P : Triangle) (F : Subfield ℝ)
    (ha : P.a ∈ complexCoordinateSubfield F)
    (he : ∀ k : Fin 3, P.edgeVector k ∈ complexCoordinateSubfield F) :
    P.CoordinatesIn F := by
  have hb : P.b ∈ complexCoordinateSubfield F := by
    have h := (complexCoordinateSubfield F).add_mem ha (he 2)
    simpa [Triangle.edgeVector, Triangle.edgeStart, Triangle.edgeEnd] using h
  have hc : P.c ∈ complexCoordinateSubfield F := by
    have h := (complexCoordinateSubfield F).sub_mem ha (he 1)
    simpa [Triangle.edgeVector, Triangle.edgeStart, Triangle.edgeEnd] using h
  intro k
  fin_cases k
  · exact ha
  · exact hb
  · exact hc

/-- The field data required for vertex rigidity are extracted from an actual
tiling, rather than imposed as hypotheses on its individual tile vectors. -/
theorem CongruentTiling.coefficient_field_edges
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (F : Subfield ℝ)
    (ha : P.a ∈ complexCoordinateSubfield F)
    (hbase : P.unitEdgeVector 2 ∈ complexCoordinateSubfield F)
    (hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hc : R.sideLength 2 ∈ F) :
    P.CoordinatesIn F ∧
      ∀ i : Fin N, ∀ k : Fin 3, (T.labelledTile i).edgeVector k ∈ complexCoordinateSubfield F := by
  have hsR := R.sideLengths_mem_of_rotations F hA hB hc
  have hsP := T.outer_sideLengths_mem_subfield F hsR
  have hPA : Complex.exp ((P.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F := by
    simpa [Triangle.cornerAngle] using
      T.outer_rotation_mem_subfield (complexCoordinateSubfield F) hA hB 0
  have hPB : Complex.exp ((P.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F := by
    simpa [Triangle.cornerAngle] using
      T.outer_rotation_mem_subfield (complexCoordinateSubfield F) hA hB 1
  have huP := P.unitEdgeVector_mem_of_one (complexCoordinateSubfield F) hPA hPB 2 hbase
  have huT := T.labelled_unitEdgeVectors_mem_of_base (complexCoordinateSubfield F) hbase hA hB
  constructor
  · exact P.coordinatesIn_of_a_and_edgeVectors F ha
      (fun k => P.edgeVector_mem_of_unit F k (hsP k) (huP k))
  · intro i k
    apply (T.labelledTile i).edgeVector_mem_of_unit F k _ (huT i k)
    rw [T.labelledTile_sideLength]
    exact hsR k

end Erdos633
