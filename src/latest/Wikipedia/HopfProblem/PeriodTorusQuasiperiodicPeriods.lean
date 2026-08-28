import Wikipedia.HopfProblem.PeriodTori
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Wikipedia.HopfProblem.PeriodTorusQuasiperiodic

/-!
# The fixed complex periods in the actual period matrix

The last two columns of the actual `[Z | I]` period matrix are the
standard complex basis.  Thus a complex-linear map vanishing on these
periods is zero.  The integral marking of the genuine lattice converts
integer-coordinate shift laws to lattice shift laws.  The proved affine
theorem then shows that a holomorphic function with these fixed periods
and constant increments along all integer periods is constant, with every
increment equal to zero.  The target may be any complex normed space.
-/

noncomputable section

open Set
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusQuasiperiodic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A column of the original period-domain matrix. -/
def periodColumn (p : PeriodDomain) (j : Fin 4) : ComplexPlane₂ :=
  fun i => p.val.matrix i j

@[simp] theorem periodColumn_two (p : PeriodDomain) :
    periodColumn p 2 = Pi.single (0 : Fin 2) (1 : ℂ) := by
  ext i
  fin_cases i <;> simp [periodColumn, PeriodPoint.matrix]

@[simp] theorem periodColumn_three (p : PeriodDomain) :
    periodColumn p 3 = Pi.single (1 : Fin 2) (1 : ℂ) := by
  ext i
  fin_cases i <;> simp [periodColumn, PeriodPoint.matrix]

theorem periodColumn_mem_lattice (p : PeriodDomain) (j : Fin 4) :
    periodColumn p j ∈ p.lattice :=
  Submodule.subset_span ⟨j, rfl⟩

/-- Both complex standard basis vectors are actual integral periods. -/
theorem standardVector_mem_lattice (p : PeriodDomain) (i : Fin 2) :
    (Pi.single i (1 : ℂ) : ComplexPlane₂) ∈ p.lattice := by
  change (Pi.single i (1 : ℂ) : ComplexPlane₂) ∈ Submodule.span ℤ
    (Set.range (fun j : Fin 4 => fun k : Fin 2 => p.val.matrix k j))
  refine Submodule.subset_span ⟨⟨i.val + 2, by omega⟩, ?_⟩
  ext k
  fin_cases i <;> fin_cases k <;> simp [PeriodPoint.matrix]

theorem eq_coordinate_smul_periodColumns (p : PeriodDomain) (z : ComplexPlane₂) :
    z = z 0 • periodColumn p 2 + z 1 • periodColumn p 3 := by
  ext i
  fin_cases i <;> simp

/-- Vanishing on the two fixed identity columns kills the whole
complex-linear part, not merely its restriction to the real lattice. -/
theorem continuousLinearMap_eq_zero_of_periodColumns (p : PeriodDomain)
    (L : ComplexPlane₂ →L[ℂ] F)
    (h₂ : L (periodColumn p 2) = 0) (h₃ : L (periodColumn p 3) = 0) : L = 0 := by
  apply DFunLike.ext
  intro z
  change L z = 0
  calc
    L z = L (z 0 • periodColumn p 2 + z 1 • periodColumn p 3) :=
      congrArg L (eq_coordinate_smul_periodColumns p z)
    _ = 0 := by simp only [map_add, map_smul, h₂, h₃, smul_zero, add_zero]

/-- Membership in the genuine period lattice has the literal matrix
formula in the source's four ordered integer coordinates. -/
theorem mem_lattice_iff_integer_period (p : PeriodDomain) (w : ComplexPlane₂) :
    w ∈ p.lattice ↔ ∃ v : Fin 4 → ℤ,
      w = p.val.matrix *ᵥ (fun i => (v i : ℂ)) := by
  rw [p.mem_lattice_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, hv.symm⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, hv.symm⟩

theorem integer_period_mem_lattice (p : PeriodDomain) (v : Fin 4 → ℤ) :
    p.val.matrix *ᵥ (fun i => (v i : ℂ)) ∈ p.lattice :=
  (mem_lattice_iff_integer_period p _).mpr ⟨v, rfl⟩

@[simp] theorem integer_period_single (p : PeriodDomain) (j : Fin 4) :
    p.val.matrix *ᵥ (fun i => ((Pi.single j (1 : ℤ) : Fin 4 → ℤ) i : ℂ)) =
      periodColumn p j := by
  have he : (fun i => ((Pi.single j (1 : ℤ) : Fin 4 → ℤ) i : ℂ)) =
      (Pi.single j (1 : ℂ) : Fin 4 → ℂ) := by
    ext i
    by_cases hij : i = j <;> simp [hij]
  rw [he]
  exact Matrix.mulVec_single_one p.val.matrix j

theorem quotient_add_lattice (p : PeriodDomain) (z w : ComplexPlane₂)
    (hw : w ∈ p.lattice) : p.lattice.mkQ (z + w) = p.lattice.mkQ z := by
  have hw' : p.lattice.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero p.lattice).mpr hw
  rw [map_add, hw', add_zero]

theorem quotient_add_periodColumn (p : PeriodDomain) (z : ComplexPlane₂) (j : Fin 4) :
    p.lattice.mkQ (z + periodColumn p j) = p.lattice.mkQ z :=
  quotient_add_lattice p z _ (periodColumn_mem_lattice p j)

theorem quotient_add_standardVector (p : PeriodDomain) (z : ComplexPlane₂) (i : Fin 2) :
    p.lattice.mkQ (z + Pi.single i (1 : ℂ)) = p.lattice.mkQ z :=
  quotient_add_lattice p z _ (standardVector_mem_lattice p i)

theorem quotient_add_integer_period (p : PeriodDomain) (z : ComplexPlane₂)
    (v : Fin 4 → ℤ) :
    p.lattice.mkQ (z + p.val.matrix *ᵥ (fun i => (v i : ℂ))) = p.lattice.mkQ z :=
  quotient_add_lattice p z _ (integer_period_mem_lattice p v)

omit [NormedSpace ℂ F] in
/-- Constant shifts for all integer period vectors give constant shifts
for every element of the actual lattice. -/
theorem lattice_quasiperiodic_of_integer_periods (p : PeriodDomain) (f : ComplexPlane₂ → F)
    (hshift : ∀ v : Fin 4 → ℤ, ∃ c : F, ∀ z,
      f (z + p.val.matrix *ᵥ (fun i => (v i : ℂ))) = f z + c) :
    ∀ w ∈ p.lattice, ∃ c : F, ∀ z, f (z + w) = f z + c := by
  intro w hw
  obtain ⟨v, rfl⟩ := (mem_lattice_iff_integer_period p w).mp hw
  exact hshift v

omit [NormedSpace ℂ F] in
theorem lattice_quasiperiodic_of_integer_period_law (p : PeriodDomain)
    (f : ComplexPlane₂ → F) (c : (Fin 4 → ℤ) → F)
    (hshift : ∀ v z, f (z + p.val.matrix *ᵥ (fun i => (v i : ℂ))) = f z + c v) :
    ∀ w ∈ p.lattice, ∃ b : F, ∀ z, f (z + w) = f z + b :=
  lattice_quasiperiodic_of_integer_periods p f (fun v => ⟨c v, hshift v⟩)

/-- The two fixed identity periods annihilate the actual derivative at
zero of a function with constant increments along every integer period. -/
theorem fderiv_zero_of_integer_periods (p : PeriodDomain) {f : ComplexPlane₂ → F}
    (hf : ContDiff ℂ 2 f)
    (hshift : ∀ v : Fin 4 → ℤ, ∃ c : F, ∀ z,
      f (z + p.val.matrix *ᵥ (fun i => (v i : ℂ))) = f z + c)
    (h₂ : ∀ z, f (z + periodColumn p 2) = f z)
    (h₃ : ∀ z, f (z + periodColumn p 3) = f z) : fderiv ℂ f 0 = 0 := by
  have hinc := lattice_quasiperiodic_of_integer_periods p f hshift
  apply continuousLinearMap_eq_zero_of_periodColumns p
  · exact (increment_eq_fderiv p.lattice hf hinc
      (w := periodColumn p 2) (c := 0) (by simpa only [add_zero] using h₂)).symm
  · exact (increment_eq_fderiv p.lattice hf hinc
      (w := periodColumn p 3) (c := 0) (by simpa only [add_zero] using h₃)).symm

/-- Constant integer-period increments and invariance under the two
fixed complex periods force the whole function to be constant. -/
theorem eq_at_zero_of_integer_periods (p : PeriodDomain) {f : ComplexPlane₂ → F}
    (hf : ContDiff ℂ 2 f)
    (hshift : ∀ v : Fin 4 → ℤ, ∃ c : F, ∀ z,
      f (z + p.val.matrix *ᵥ (fun i => (v i : ℂ))) = f z + c)
    (h₂ : ∀ z, f (z + periodColumn p 2) = f z)
    (h₃ : ∀ z, f (z + periodColumn p 3) = f z) (z : ComplexPlane₂) : f z = f 0 :=
  eq_at_zero_of_lattice_quasiperiodic_of_fderiv_zero p.lattice hf
    (lattice_quasiperiodic_of_integer_periods p f hshift)
    (fderiv_zero_of_integer_periods p hf hshift h₂ h₃) z

theorem eq_at_zero_of_holomorphic_integer_periods (p : PeriodDomain)
    {f : ComplexPlane₂ → F} (hf : ContDiff ℂ ω f)
    (hshift : ∀ v : Fin 4 → ℤ, ∃ c : F, ∀ z,
      f (z + p.val.matrix *ᵥ (fun i => (v i : ℂ))) = f z + c)
    (h₂ : ∀ z, f (z + periodColumn p 2) = f z)
    (h₃ : ∀ z, f (z + periodColumn p 3) = f z) (z : ComplexPlane₂) : f z = f 0 :=
  eq_at_zero_of_integer_periods p (hf.of_le (by simp)) hshift h₂ h₃ z

/-- The actual period-shift law has no residual constants once its
two fixed complex periods act trivially. -/
theorem constant_and_increments_zero_of_holomorphic_period_law (p : PeriodDomain)
    {f : ComplexPlane₂ → F} (hf : ContDiff ℂ ω f) (c : (Fin 4 → ℤ) → F)
    (hshift : ∀ v z, f (z + p.val.matrix *ᵥ (fun i => (v i : ℂ))) = f z + c v)
    (h₂ : ∀ z, f (z + periodColumn p 2) = f z)
    (h₃ : ∀ z, f (z + periodColumn p 3) = f z) :
    (∀ z, f z = f 0) ∧ ∀ v, c v = 0 := by
  have hz := eq_at_zero_of_holomorphic_integer_periods p hf
    (fun v => ⟨c v, hshift v⟩) h₂ h₃
  refine ⟨hz, ?_⟩
  intro v
  apply add_left_cancel (a := f 0)
  calc
    f 0 + c v = f (0 + p.val.matrix *ᵥ (fun i => (v i : ℂ))) := (hshift v 0).symm
    _ = f 0 := hz _
    _ = f 0 + 0 := (add_zero _).symm

/-- Equivalently, it suffices that the named increments at the two
identity columns are zero; all other increments then vanish as well. -/
theorem constant_and_increments_zero_of_identity_values (p : PeriodDomain)
    {f : ComplexPlane₂ → F} (hf : ContDiff ℂ ω f) (c : (Fin 4 → ℤ) → F)
    (hshift : ∀ v z, f (z + p.val.matrix *ᵥ (fun i => (v i : ℂ))) = f z + c v)
    (h₂ : c (Pi.single (2 : Fin 4) (1 : ℤ)) = 0)
    (h₃ : c (Pi.single (3 : Fin 4) (1 : ℤ)) = 0) :
    (∀ z, f z = f 0) ∧ ∀ v, c v = 0 := by
  apply constant_and_increments_zero_of_holomorphic_period_law p hf c hshift
  · intro z
    simpa only [integer_period_single, h₂, add_zero] using
      hshift (Pi.single (2 : Fin 4) (1 : ℤ)) z
  · intro z
    simpa only [integer_period_single, h₃, add_zero] using
      hshift (Pi.single (3 : Fin 4) (1 : ℤ)) z

end Wikipedia.HopfProblem.PeriodTorusQuasiperiodic
