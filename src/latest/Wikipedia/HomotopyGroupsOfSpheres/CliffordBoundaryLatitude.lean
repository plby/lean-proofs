import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfEndpointMatrices
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeTimeHomeomorph

/-! # Angular three-sphere coordinates for the actual orthogonal endpoint -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open CliffordFiveHermitian Wikipedia.HopfProblem.SphereHomology

def latitudeCoordinates (θ : ℝ) (v : Fin 3 → ℝ) : Fin 4 → ℝ :=
  Fin.cons (Real.cos θ) (fun i ↦ Real.sin θ * v i)

def latitudeVector (θ : ℝ) (v : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (latitudeCoordinates θ v)

theorem latitudeVector_norm_sq (θ : ℝ) (v : Fin 3 → ℝ) :
    ‖latitudeVector θ v‖ ^ 2 = Real.cos θ ^ 2 + Real.sin θ ^ 2 * ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  change Real.cos θ ^ 2 + ∑ i : Fin 3, (Real.sin θ * v i) ^ 2 = _
  simp only [mul_pow, ← Finset.mul_sum]

def latitudePoint (θ : ℝ) (v : Sphere 2) : EquatorSphere :=
  ⟨latitudeVector θ v.val, mem_sphere_zero_iff_norm.mpr (by
    have hv : ∑ i, v.val i ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.mp v.property]
      norm_num
    have h := latitudeVector_norm_sq θ (fun i ↦ v.val i)
    rw [hv, mul_one, Real.cos_sq_add_sin_sq] at h
    nlinarith [norm_nonneg (latitudeVector θ (fun i ↦ v.val i))])⟩

theorem latitudePoint_val (θ : ℝ) (v : Sphere 2) :
    (fun i ↦ (latitudePoint θ v).val i) =
      ![Real.cos θ, Real.sin θ * v.val 0, Real.sin θ * v.val 1,
        Real.sin θ * v.val 2] := by
  funext i
  fin_cases i <;> rfl

theorem continuous_latitudePoint :
    Continuous (fun p : ℝ × Sphere 2 ↦ latitudePoint p.1 p.2) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  cases i using Fin.cases
  · change Continuous (fun p : ℝ × Sphere 2 ↦ Real.cos p.1)
    fun_prop
  · change Continuous (fun p : ℝ × Sphere 2 ↦ Real.sin p.1 * p.2.val _)
    fun_prop

theorem latitudePoint_zero (v : Sphere 2) : latitudePoint 0 v = equatorPole := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i using Fin.cases <;>
    simp [latitudePoint, latitudeVector, latitudeCoordinates,
      equatorPole, EuclideanSpace.basisFun_apply]

theorem latitudePoint_pi_eq (v w : Sphere 2) :
    latitudePoint Real.pi v = latitudePoint Real.pi w := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i using Fin.cases <;> simp [latitudePoint, latitudeVector, latitudeCoordinates]

theorem latitudePoint_arccos (t : I) (v : Sphere 2) :
    latitudePoint (Real.arccos (Latitude.height t)) v = Latitude.point 2 t v := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i using Fin.cases
  · change Real.cos (Real.arccos (Latitude.height t)) = Latitude.height t
    apply Real.cos_arccos <;> nlinarith [Latitude.height_sq_le_one t]
  · change Real.sin (Real.arccos (Latitude.height t)) * v.val _ = Latitude.radius t * v.val _
    rw [Real.sin_arccos]
    rfl

def polarAngle : C(EquatorSphere, ℝ) :=
  ⟨fun q ↦ Real.arccos (q.val 0), by fun_prop⟩

theorem polarAngle_latitude (θ : ℝ) (v : Sphere 2) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    polarAngle (latitudePoint θ v) = θ := Real.arccos_cos h0 hπ

theorem polarAngle_equatorPole : polarAngle equatorPole = 0 := by
  change Real.arccos (equatorPole.val 0) = 0
  simp [equatorPole, EuclideanSpace.basisFun_apply]

def generatorMatrix (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 0 : ℂ) * Complex.I, -(v 1 : ℂ) + (v 2 : ℂ) * Complex.I;
     (v 1 : ℂ) + (v 2 : ℂ) * Complex.I, -(v 0 : ℂ) * Complex.I]

theorem boundaryUnitary_latitude (θ : ℝ) (v : Sphere 2) :
    (boundaryUnitary (latitudePoint θ v)).val =
      Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Real.sin θ • generatorMatrix v.val := by
  rw [boundaryUnitary_val]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [latitudePoint, latitudeVector, latitudeCoordinates, generatorMatrix,
      Complex.mul_re, Complex.mul_im, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      rfl

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
