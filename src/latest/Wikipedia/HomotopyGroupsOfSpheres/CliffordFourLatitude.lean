import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfBlock
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeTimeHomeomorph
import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryRotationGrading

/-! # Actual four-sphere latitudes and the Clifford block involution -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open Wikipedia.HopfProblem.SphereHomology

def fourLatitudeCoordinates (θ : ℝ) (q : EquatorCoordinates) : Coordinates :=
  Fin.cons (Real.cos θ) (fun i ↦ Real.sin θ * q i)

def fourLatitudeVector (θ : ℝ) (q : EquatorCoordinates) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (fourLatitudeCoordinates θ q)

theorem fourLatitudeVector_norm_sq (θ : ℝ) (q : EquatorCoordinates) :
    ‖fourLatitudeVector θ q‖ ^ 2 = Real.cos θ ^ 2 + Real.sin θ ^ 2 * ∑ i, q i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  change Real.cos θ ^ 2 + ∑ i : Fin 4, (Real.sin θ * q i) ^ 2 = _
  simp only [mul_pow, ← Finset.mul_sum]

def fourLatitudePoint (θ : ℝ) (q : EquatorSphere) : UnitSphere :=
  ⟨fourLatitudeVector θ q.val, mem_sphere_zero_iff_norm.mpr (by
    have hq : ∑ i, q.val i ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.mp q.property]
      norm_num
    have h := fourLatitudeVector_norm_sq θ (fun i ↦ q.val i)
    rw [hq, mul_one, Real.cos_sq_add_sin_sq] at h
    nlinarith [norm_nonneg (fourLatitudeVector θ (fun i ↦ q.val i))])⟩

theorem fourLatitudePoint_head (θ : ℝ) (q : EquatorSphere) :
    (fourLatitudePoint θ q).val 0 = Real.cos θ := rfl

theorem fourLatitudePoint_val (θ : ℝ) (q : EquatorSphere) :
    (fun i ↦ (fourLatitudePoint θ q).val i) =
      ![Real.cos θ, Real.sin θ * q.val 0, Real.sin θ * q.val 1,
        Real.sin θ * q.val 2, Real.sin θ * q.val 3] := by
  funext i
  fin_cases i <;> rfl

theorem continuous_fourLatitudePoint :
    Continuous (fun p : ℝ × EquatorSphere ↦ fourLatitudePoint p.1 p.2) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 5 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  cases i using Fin.cases
  · change Continuous (fun p : ℝ × EquatorSphere ↦ Real.cos p.1)
    fun_prop
  · change Continuous (fun p : ℝ × EquatorSphere ↦ Real.sin p.1 * p.2.val _)
    fun_prop

theorem fourLatitudePoint_zero (q : EquatorSphere) : fourLatitudePoint 0 q = pole := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i using Fin.cases <;>
    simp [fourLatitudePoint, fourLatitudeVector, fourLatitudeCoordinates,
      pole, EuclideanSpace.basisFun_apply]

theorem fourLatitudePoint_pi_eq (q r : EquatorSphere) :
    fourLatitudePoint Real.pi q = fourLatitudePoint Real.pi r := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i using Fin.cases <;>
    simp [fourLatitudePoint, fourLatitudeVector, fourLatitudeCoordinates]

theorem fourLatitudePoint_arccos (t : I) (q : EquatorSphere) :
    fourLatitudePoint (Real.arccos (Latitude.height t)) q = Latitude.point 3 t q := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i using Fin.cases
  · change Real.cos (Real.arccos (Latitude.height t)) = Latitude.height t
    apply Real.cos_arccos <;> nlinarith [Latitude.height_sq_le_one t]
  · change Real.sin (Real.arccos (Latitude.height t)) * q.val _ = Latitude.radius t * q.val _
    rw [Real.sin_arccos]
    rfl

theorem fourLatitudePoint_surjective (v : UnitSphere) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi ∧ ∃ q : EquatorSphere, fourLatitudePoint θ q = v := by
  obtain ⟨⟨t, q⟩, h⟩ := Latitude.point_surjective 3 v
  exact ⟨Real.arccos (Latitude.height t), Real.arccos_nonneg _, Real.arccos_le_pi _, q,
    (fourLatitudePoint_arccos t q).trans h⟩

def fourPolarAngle : C(UnitSphere, ℝ) :=
  ⟨fun v ↦ Real.arccos (v.val 0), by fun_prop⟩

theorem fourPolarAngle_latitude (θ : ℝ) (q : EquatorSphere) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    fourPolarAngle (fourLatitudePoint θ q) = θ :=
  Real.arccos_cos h0 hπ

theorem fourPolarAngle_pole : fourPolarAngle pole = 0 := by
  change Real.arccos (pole.val 0) = 0
  simp [pole, EuclideanSpace.basisFun_apply]

def hopfBlockIndex : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

theorem matrix_fourLatitudePoint (θ : ℝ) (q : EquatorSphere) :
    Matrix.reindex hopfBlockIndex.symm hopfBlockIndex.symm
      (matrix (fourLatitudePoint θ q).val) =
        ComplexUnitaryRotation.latitudeMatrix (offDiagonalUnitary q) θ := by
  have h0 : hopfBlockIndex (Sum.inl (0 : Fin 2)) = 0 := rfl
  have h1 : hopfBlockIndex (Sum.inl (1 : Fin 2)) = 1 := rfl
  have h2 : hopfBlockIndex (Sum.inr (0 : Fin 2)) = 2 := rfl
  have h3 : hopfBlockIndex (Sum.inr (1 : Fin 2)) = 3 := rfl
  apply Matrix.ext
  intro i j
  change matrix (fun k ↦ (fourLatitudePoint θ q).val k) (hopfBlockIndex i) (hopfBlockIndex j) = _
  rw [fourLatitudePoint_val]
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [h0, h1, h2, h3, matrix, ComplexUnitaryRotation.latitudeMatrix,
      offDiagonalUnitary, offDiagonal, Matrix.conjTranspose_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Complex.mul_re, Complex.mul_im, -Complex.ofReal_cos, -Complex.ofReal_sin]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
