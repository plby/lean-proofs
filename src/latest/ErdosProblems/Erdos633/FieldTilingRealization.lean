import ErdosProblems.Erdos633.CrossingTransport
import ErdosProblems.Erdos633.RealCoordinateField

/-!
# Actual tilings with coordinates in the coefficient field

A field retraction fixes all tile-edge vectors and hence translates each tile.
It preserves the original marked supporting lines even when it changes the
order of points. The crossing transport theorem supplies coverage and disjoint
interiors. Thus the algebraic retraction now gives a geometric tiling, and it
can still be chosen injective on the original finite vertex set.
-/

namespace Erdos633

theorem Triangle.CoordinatesIn.edgeStart {P : Triangle} {F : Subfield ℝ}
    (h : P.CoordinatesIn F) (k : Fin 3) : P.edgeStart k ∈ complexCoordinateSubfield F := by
  obtain ⟨j, hj⟩ := P.edgeStart_mem_vertices k
  rw [← hj]
  exact h j

theorem Triangle.CoordinatesIn.edgeEnd {P : Triangle} {F : Subfield ℝ}
    (h : P.CoordinatesIn F) (k : Fin 3) : P.edgeEnd k ∈ complexCoordinateSubfield F := by
  obtain ⟨j, hj⟩ := P.edgeEnd_mem_vertices k
  rw [← hj]
  exact h j

theorem Triangle.CoordinatesIn.edgeVector {P : Triangle} {F : Subfield ℝ}
    (h : P.CoordinatesIn F) (k : Fin 3) : P.edgeVector k ∈ complexCoordinateSubfield F :=
  (complexCoordinateSubfield F).sub_mem (h.edgeEnd k) (h.edgeStart k)

theorem Triangle.vertex_sub_a_mem_of_edgeVectors (P : Triangle) (F : Subfield ℝ)
    (he : ∀ k : Fin 3, P.edgeVector k ∈ complexCoordinateSubfield F) (j : Fin 3) :
    P.vertex j - P.a ∈ complexCoordinateSubfield F := by
  fin_cases j
  · simp [Triangle.vertex]
  · exact he 2
  · have h := (complexCoordinateSubfield F).neg_mem (he 1)
    simpa [Triangle.edgeVector, Triangle.edgeStart, Triangle.edgeEnd, Triangle.vertex] using h

theorem fieldCoordinateMap_preserves_axis (F : Subfield ℝ) (f : ℝ →ₗ[F] F)
    (p d z : ℂ) (hd : d ≠ 0) (hre : d.re ∈ F) (him : d.im ∈ F)
    (hz : OnAxis p d z) : OnAxis (fieldCoordinateMap F f p) d (fieldCoordinateMap F f z) := by
  have heq : fieldCoordinateMap F f z = axisMap (fieldCoordinateMap F f p) d
      ((f (axisParameter p d z) : F) : ℝ) := by
    nth_rw 1 [← axisMap_axisParameter p d z hd hz]
    rw [axisMap_apply, fieldCoordinateMap_line F f p d _ hre him, axisMap_apply]
  rw [heq]
  exact onAxis_axisMap _ d hd _

theorem TriangleDissection.edgeLinePreserving_fieldCoordinateMap
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (hf : ∀ a : F, f (a : ℝ) = a)
    (hP : P.CoordinatesIn F)
    (he : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).edgeVector k ∈ complexCoordinateSubfield F) :
    T.EdgeLinePreserving (fieldCoordinateMap F f) := by
  intro Q hQ k
  have hd : Q.edgeVector k ∈ complexCoordinateSubfield F := by
    rcases hQ with rfl | ⟨i, rfl⟩
    · exact hP.edgeVector k
    · exact he i k
  have hvec : fieldCoordinateMap F f (Q.edgeEnd k) -
      fieldCoordinateMap F f (Q.edgeStart k) = Q.edgeVector k :=
    fieldCoordinateMap_sub_eq F f hf _ _ hd.1 hd.2
  constructor
  · intro h
    rw [h, sub_self] at hvec
    exact Q.edgeVector_ne_zero k hvec.symm
  · intro z _ hz
    rw [hvec]
    exact fieldCoordinateMap_preserves_axis F f _ _ z (Q.edgeVector_ne_zero k) hd.1 hd.2 hz

noncomputable def Triangle.fieldRetract (P : Triangle) (F : Subfield ℝ)
    (f : ℝ →ₗ[F] F) : Triangle :=
  P.mapIsometry (IsometryEquiv.vaddConst (fieldCoordinateMap F f P.a - P.a))

theorem Triangle.fieldRetract_vertexImage (P : Triangle) (F : Subfield ℝ)
    (f : ℝ →ₗ[F] F) (hf : ∀ a : F, f (a : ℝ) = a)
    (he : ∀ k : Fin 3, P.edgeVector k ∈ complexCoordinateSubfield F) :
    P.VertexImage (P.fieldRetract F f) (fieldCoordinateMap F f) := by
  intro k
  rw [Triangle.fieldRetract, P.vertex_mapIsometry]
  change P.vertex k + (fieldCoordinateMap F f P.a - P.a) = fieldCoordinateMap F f (P.vertex k)
  have h := P.vertex_sub_a_mem_of_edgeVectors F he k
  have hh := fieldCoordinateMap_sub_eq F f hf (P.vertex k) P.a h.1 h.2
  linear_combination -hh

theorem Triangle.fieldRetract_coordinatesIn (P : Triangle) (F : Subfield ℝ)
    (f : ℝ →ₗ[F] F) (hf : ∀ a : F, f (a : ℝ) = a)
    (he : ∀ k : Fin 3, P.edgeVector k ∈ complexCoordinateSubfield F) :
    (P.fieldRetract F f).CoordinatesIn F := by
  intro k
  rw [P.fieldRetract_vertexImage F f hf he k]
  exact ⟨(f (P.vertex k).re).property, (f (P.vertex k).im).property⟩

theorem Triangle.orientationSign_translate (P : Triangle) (u : ℂ) :
    (P.mapIsometry (IsometryEquiv.vaddConst u)).orientationSign = P.orientationSign := by
  have h : orientedDoubleArea (P.mapIsometry (IsometryEquiv.vaddConst u)).a
      (P.mapIsometry (IsometryEquiv.vaddConst u)).b
      (P.mapIsometry (IsometryEquiv.vaddConst u)).c = orientedDoubleArea P.a P.b P.c := by
    change orientedDoubleArea (P.a + u) (P.b + u) (P.c + u) = _
    simp [orientedDoubleArea]
  simp only [Triangle.orientationSign, h]

theorem Triangle.fieldRetract_orientationSign (P : Triangle) (F : Subfield ℝ)
    (f : ℝ →ₗ[F] F) : (P.fieldRetract F f).orientationSign = P.orientationSign :=
  P.orientationSign_translate _

noncomputable def TriangleDissection.fieldRetract
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (hf : ∀ a : F, f (a : ℝ) = a)
    (hP : P.CoordinatesIn F)
    (he : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).edgeVector k ∈ complexCoordinateSubfield F) :
    TriangleDissection P N :=
  T.mapVertexImages (fieldCoordinateMap F f)
    (T.edgeLinePreserving_fieldCoordinateMap F f hf hP he)
    P (fun i => (T.tile i).fieldRetract F f)
    (fun k => (fieldCoordinateMap_fixed F f hf (P.vertex k) (hP k).1 (hP k).2).symm)
    (fun i => (T.tile i).fieldRetract_vertexImage F f hf (he i))
    (fun i => by rw [Triangle.fieldRetract_orientationSign,
      (T.tile i).orientationSign_mul_self, P.orientationSign_mul_self])

noncomputable def CongruentTiling.fieldRetract
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (hf : ∀ a : F, f (a : ℝ) = a)
    (hP : P.CoordinatesIn F)
    (he : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).edgeVector k ∈ complexCoordinateSubfield F) :
    CongruentTiling P R N where
  toTriangleDissection := T.toTriangleDissection.fieldRetract F f hf hP he
  congruent := by
    intro i
    obtain ⟨e, he⟩ := T.congruent i
    let u := fieldCoordinateMap F f (T.tile i).a - (T.tile i).a
    let e' := IsometryEquiv.vaddConst u
    refine ⟨e.trans e', ?_⟩
    change (fun z => e' (e z)) '' R.carrier = ((T.tile i).fieldRetract F f).carrier
    rw [← Set.image_image e' e R.carrier, he]
    exact ((T.tile i).mapIsometry_carrier e').symm

theorem TriangleDissection.exists_field_realization
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (F : Subfield ℝ) (hP : P.CoordinatesIn F)
    (he : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).edgeVector k ∈ complexCoordinateSubfield F) :
    ∃ f : ℝ →ₗ[F] F, (∀ a : F, f (a : ℝ) = a) ∧
      Set.InjOn (fieldCoordinateMap F f) T.vertexFinset ∧
      ∃ U : TriangleDissection P N, ∀ i : Fin N,
        (U.tile i).CoordinatesIn F ∧
        (T.tile i).VertexImage (U.tile i) (fieldCoordinateMap F f) := by
  obtain ⟨f, hf, hinj⟩ := exists_fieldCoordinateMap_injective_on F T.vertexFinset
  refine ⟨f, hf, hinj, T.fieldRetract F f hf hP he, ?_⟩
  intro i
  exact ⟨(T.tile i).fieldRetract_coordinatesIn F f hf (he i),
    (T.tile i).fieldRetract_vertexImage F f hf (he i)⟩

end Erdos633
