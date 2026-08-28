import Wikipedia.HopfProblem.CuspRetractionPolar

/-!
# Compact-torus normalization for the positive cusp retraction

An integral translation shears the first two phase coordinates by powers of
the third. The resulting identity holds in every actual affine chart, including
the toric boundary.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

/-- The compact-torus shear induced by an integral lattice translation. -/
def phaseShear (v : Fin 2 → ℤ) (u : CompactTorus) : CompactTorus :=
  ![u 0 * u 2 ^ v 0, u 1 * u 2 ^ v 1, u 2]

@[simp] theorem phaseShear_apply_zero (v : Fin 2 → ℤ) (u : CompactTorus) :
    phaseShear v u 0 = u 0 * u 2 ^ v 0 := rfl

@[simp] theorem phaseShear_apply_one (v : Fin 2 → ℤ) (u : CompactTorus) :
    phaseShear v u 1 = u 1 * u 2 ^ v 1 := rfl

@[simp] theorem phaseShear_apply_two (v : Fin 2 → ℤ) (u : CompactTorus) :
    phaseShear v u 2 = u 2 := rfl

@[simp] theorem phaseShear_zero (u : CompactTorus) : phaseShear 0 u = u := by
  funext i
  fin_cases i <;> simp [phaseShear]

@[simp] theorem phaseShear_one (v : Fin 2 → ℤ) : phaseShear v 1 = 1 := by
  funext i
  fin_cases i <;> simp [phaseShear]

theorem phaseShear_mul (v : Fin 2 → ℤ) (u w : CompactTorus) :
    phaseShear v (u * w) = phaseShear v u * phaseShear v w := by
  funext i
  fin_cases i <;> simp [phaseShear, mul_zpow, mul_assoc, mul_left_comm]

theorem phaseShear_add (v w : Fin 2 → ℤ) (u : CompactTorus) :
    phaseShear v (phaseShear w u) = phaseShear (v + w) u := by
  funext i
  fin_cases i <;> simp [phaseShear, zpow_add, mul_left_comm, mul_comm]

/-- In complex coordinates the phase shear is the corresponding toric monomial. -/
theorem phaseShear_coe (v : Fin 2 → ℤ) (u : CompactTorus) :
    (fun j => (phaseShear v u j : ℂ)) =
      monomial (shear v) (fun j => (u j : ℂ)) := by
  funext i
  fin_cases i <;> simp [phaseShear, monomial, shear, Fin.prod_univ_succ]

theorem factors_shift_phaseShear (s : Triangle) (v : Fin 2 → ℤ) (u : CompactTorus) :
    factors (s.shift v) (compactTorusUnits (phaseShear v u)) =
      factors s (compactTorusUnits u) := by
  change monomial (s.shift v).dual (fun j => (phaseShear v u j : ℂ)) =
    monomial s.dual (fun j => (u j : ℂ))
  rw [dual_shift, phaseShear_coe,
    monomial_mul_on_torus _ _ (fun j => (u j).coe_ne_zero),
    Matrix.mul_assoc, shear_add]
  simp

/-- Integral translation normalizes the compact action on the entire toric space. -/
theorem translate_compactTorusAction (v : Fin 2 → ℤ) (u : CompactTorus) (x : Space) :
    translate v (compactTorusAction u x) =
      compactTorusAction (phaseShear v u) (translate v x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [compactTorusAction, scale, factors_shift_phaseShear]

end Wikipedia.HopfProblem.ToricSpace
