import Wikipedia.HopfProblem.CuspRetractionPolar
import Wikipedia.HopfProblem.CuspPositiveRetractionOrthant

/-!
# Actual orthant charts on the positive toric space

The positive part of every affine toric chart is the ordinary nonnegative
real orthant.  The inclusions below are open embeddings for the inherited
subspace topologies, and their product height is the genuine toric
parameter.  Thus these charts cover the actual positive part of the glued
space, rather than an independently assembled model.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspPositive

open ToricCharts ToricFan ToricSpace CuspPositiveRetraction

/-- Coordinatewise real inclusion identifies the ordinary nonnegative
orthant with the nonnegative locus of complex coordinate space. -/
def orthantComplexHomeomorph :
    Orthant ≃ₜ (nonnegativeCoordinates : Set (CoordinateSpace 3)) where
  toFun r := ⟨fun i => (r.1 i : ℂ), ⟨r.1, r.2, rfl⟩⟩
  invFun z := ⟨fun i => (z.1 i).re, by
    obtain ⟨r, hr, hz⟩ := z.2
    intro i
    rw [hz]
    exact hr i⟩
  left_inv r := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    obtain ⟨r, hr, hz⟩ := z.2
    simp only [hz, Complex.ofReal_re]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => Complex.continuous_re.comp
      ((continuous_apply i).comp continuous_subtype_val)

@[simp] theorem orthantComplexHomeomorph_coe (r : Orthant) :
    (orthantComplexHomeomorph r : CoordinateSpace 3) = fun i => (r.1 i : ℂ) := rfl

@[simp] theorem orthantComplexHomeomorph_apply (r : Orthant) (i : Fin 3) :
    (orthantComplexHomeomorph r : CoordinateSpace 3) i = (r.1 i : ℂ) := rfl

@[simp] theorem orthantComplexHomeomorph_symm_coe
    (z : (nonnegativeCoordinates : Set (CoordinateSpace 3))) :
    (orthantComplexHomeomorph.symm z : Fin 3 → ℝ) = fun i => (z.1 i).re := rfl

@[simp] theorem orthantComplexHomeomorph_symm_apply
    (z : (nonnegativeCoordinates : Set (CoordinateSpace 3))) (i : Fin 3) :
    (orthantComplexHomeomorph.symm z : Fin 3 → ℝ) i = (z.1 i).re := rfl

theorem inclusion_preimage_positivePart (s : Triangle) :
    inclusion s ⁻¹' positivePart = (nonnegativeCoordinates : Set (CoordinateSpace 3)) := by
  ext z
  exact inclusion_mem_positivePart_iff s z

/-- The real orthant included in the actual positive part of the affine
toric chart indexed by `s`. -/
def positiveInclusion (s : Triangle) (r : Orthant) : PositivePart :=
  ⟨inclusion s (fun i => (r.1 i : ℂ)),
    (inclusion_mem_positivePart_iff s _).mpr ⟨r.1, r.2, rfl⟩⟩

@[simp] theorem positiveInclusion_coe (s : Triangle) (r : Orthant) :
    (positiveInclusion s r : Space) = inclusion s (fun i => (r.1 i : ℂ)) := rfl

/-- Restricting an actual toric chart to the positive part gives an open
embedding for the inherited subspace topologies. -/
theorem positiveInclusion_openEmbedding (s : Triangle) :
    IsOpenEmbedding (positiveInclusion s) := by
  let e : Orthant ≃ₜ (inclusion s ⁻¹' positivePart) :=
    orthantComplexHomeomorph.trans
      (Homeomorph.setCongr (inclusion_preimage_positivePart s).symm)
  have h : IsOpenEmbedding ((positivePart.restrictPreimage (inclusion s)) ∘ e) :=
    ((inclusion_openEmbedding s).restrictPreimage positivePart).comp e.isOpenEmbedding
  have he : ((positivePart.restrictPreimage (inclusion s)) ∘ e) = positiveInclusion s := by
    funext r
    apply Subtype.ext
    rfl
  rwa [he] at h

theorem positiveInclusion_continuous (s : Triangle) : Continuous (positiveInclusion s) :=
  (positiveInclusion_openEmbedding s).continuous

/-- An actual orthant parametrization, with full source and the open
image of the corresponding toric chart as target. -/
def positiveParametrization (s : Triangle) : OpenPartialHomeomorph Orthant PositivePart := by
  letI : Nonempty Orthant := ⟨⟨fun _ => 0, fun _ => le_rfl⟩⟩
  exact (positiveInclusion_openEmbedding s).toOpenPartialHomeomorph (positiveInclusion s)

@[simp] theorem positiveParametrization_apply (s : Triangle) (r : Orthant) :
    positiveParametrization s r = positiveInclusion s r := rfl

@[simp] theorem positiveParametrization_source (s : Triangle) :
    (positiveParametrization s).source = univ := rfl

@[simp] theorem positiveParametrization_target (s : Triangle) :
    (positiveParametrization s).target = range (positiveInclusion s) := by
  simp [positiveParametrization]

@[simp] theorem positiveParametrization_symm_positiveInclusion (s : Triangle) (r : Orthant) :
    (positiveParametrization s).symm (positiveInclusion s r) = r := by
  have h := (positiveParametrization s).left_inv
    (show r ∈ (positiveParametrization s).source by simp)
  simpa only [positiveParametrization_apply] using h

theorem positiveInclusion_positiveParametrization_symm (s : Triangle) {x : PositivePart}
    (hx : x ∈ range (positiveInclusion s)) :
    positiveInclusion s ((positiveParametrization s).symm x) = x := by
  have h := (positiveParametrization s).right_inv
    (show x ∈ (positiveParametrization s).target by simpa only [positiveParametrization_target]
      using hx)
  simpa only [positiveParametrization_apply] using h

@[simp] theorem time_positiveInclusion (s : Triangle) (r : Orthant) :
    time (positiveInclusion s r : Space) = (CuspPositiveRetraction.height r : ℂ) := by
  simp [positiveInclusion, Triangle.time, CuspPositiveRetraction.height,
    Fin.prod_univ_succ, mul_assoc]

@[simp] theorem norm_time_positiveInclusion (s : Triangle) (r : Orthant) :
    ‖time (positiveInclusion s r : Space)‖ = CuspPositiveRetraction.height r := by
  rw [time_positiveInclusion]
  exact Complex.norm_of_nonneg (height_nonneg r)

/-- Every point of the actual positive toric space lies in one of these
ordinary orthant charts. -/
theorem positiveInclusion_jointly_surjective (x : PositivePart) :
    ∃ s r, positiveInclusion s r = x := by
  obtain ⟨s, z, hz⟩ := inclusion_jointly_surjective (x : Space)
  have hp : inclusion s z ∈ positivePart := hz.symm ▸ x.property
  obtain ⟨r, hr, he⟩ := (inclusion_mem_positivePart_iff s z).mp hp
  refine ⟨s, ⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  change inclusion s (fun i => (r i : ℂ)) = (x : Space)
  rw [← he]
  exact hz

end Wikipedia.HopfProblem.CuspPositive
