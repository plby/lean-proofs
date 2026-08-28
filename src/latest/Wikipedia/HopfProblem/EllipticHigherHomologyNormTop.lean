import Wikipedia.HopfProblem.EllipticHigherHomologyNormData

/-!
# The top exterior-degree norm

The determinant of each actual fibre matrix is one.  Consequently its
finite norm on the top exterior lattice is multiplication by the order,
with exact image index three or four.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

/-- The determinant action on the top exterior lattice. -/
def fibreTopMonodromy (j : Kind) : ℤ →ₗ[ℤ] ℤ :=
  (fibreMatrix j).det • LinearMap.id

@[simp] theorem fibreTopMonodromy_eq_id (j : Kind) :
    fibreTopMonodromy j = LinearMap.id := by
  simp [fibreTopMonodromy, fibreMatrix_det]

/-- The literal sum of determinant powers defining the top norm. -/
def fibreTopNormCoefficient (j : Kind) : ℤ :=
  ∑ k ∈ Finset.range j.order, ((fibreMatrix j).det) ^ k

@[simp] theorem fibreTopNormCoefficient_eq_order (j : Kind) :
    fibreTopNormCoefficient j = j.order := by
  simp [fibreTopNormCoefficient, fibreMatrix_det]

/-- The top exterior norm on its actual integral lattice. -/
def fibreTopNorm (j : Kind) : ℤ →ₗ[ℤ] ℤ :=
  fibreTopNormCoefficient j • LinearMap.id

theorem fibreTopNorm_eq_smul (j : Kind) :
    fibreTopNorm j = (j.order : ℤ) • LinearMap.id := by
  rw [fibreTopNorm, fibreTopNormCoefficient_eq_order]

@[simp] theorem fibreTopNorm_apply (j : Kind) (k : ℤ) :
    fibreTopNorm j k = (j.order : ℤ) * k := by
  simp [fibreTopNorm_eq_smul]

theorem fibreTopNorm_range_eq_span (j : Kind) :
    LinearMap.range (fibreTopNorm j) = Submodule.span ℤ {(j.order : ℤ)} := by
  rw [fibreTopNorm_eq_smul]
  exact int_scaled_coordinate_range LinearMap.id Function.surjective_id _

theorem fibreTopNorm_range_iff (j : Kind) (k : ℤ) :
    k ∈ LinearMap.range (fibreTopNorm j) ↔ (j.order : ℤ) ∣ k := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, fibreTopNorm_apply j a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, fibreTopNorm_apply j a⟩

theorem fibreTopNorm_range_index (j : Kind) :
    (LinearMap.range (fibreTopNorm j)).toAddSubgroup.index = j.order := by
  rw [fibreTopNorm_range_eq_span, int_span_singleton_index]
  simp

theorem fibreTopNorm_injective (j : Kind) : Function.Injective (fibreTopNorm j) := by
  intro a b hab
  have horder : (j.order : ℤ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  apply mul_left_cancel₀ horder
  simpa using hab

end Wikipedia.HopfProblem.Elliptic.HigherHomology
