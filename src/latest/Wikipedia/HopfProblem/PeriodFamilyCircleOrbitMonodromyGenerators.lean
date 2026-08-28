import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMonodromyBasic

/-!
# The original period-change maps descend through the delta-circle quotient

The two native complex-linear factors fix the original vertical vector.
Consequently the actual period-change biholomorphisms intertwine the
actual circle actions, and induce homeomorphisms on their orbit quotients
and on the proved marked three-period models.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

open SpecialPeriods.Threefold.VerticalAction.Period (vector)

local notation "Circle" => AddCircle (1 : ℝ)

theorem step₁_matrix_vector (p : PeriodDomain) (s : ℂ) :
    p.val.R₁ *ᵥ vector s = vector s := by
  ext i
  fin_cases i <;> simp [PeriodPoint.R₁, vector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem step₂_matrix_vector (p : PeriodDomain) (s : ℂ) :
    p.val.R₂ *ᵥ vector s = vector s := by
  ext i
  fin_cases i <;> simp [PeriodPoint.R₂, vector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem step₁Biholomorph_circleFlow (p : PeriodDomain) (t : Circle) (x : p.Torus) :
    p.step₁Biholomorph (circleFlow p t x) =
      circleFlow p.step₁ t (p.step₁Biholomorph x) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨z, rfl⟩ := p.lattice.mkQ_surjective x
  simp only [circleFlow_coe_mkQ, p.step₁Biholomorph_mkQ,
    Matrix.mulVec_add, step₁_matrix_vector]

theorem step₂Biholomorph_circleFlow (p : PeriodDomain) (t : Circle) (x : p.Torus) :
    p.step₂Biholomorph (circleFlow p t x) =
      circleFlow p.step₂ t (p.step₂Biholomorph x) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨z, rfl⟩ := p.lattice.mkQ_surjective x
  simp only [circleFlow_coe_mkQ, p.step₂Biholomorph_mkQ,
    Matrix.mulVec_add, step₂_matrix_vector]

theorem step₀Biholomorph_circleFlow (p : PeriodDomain) (t : Circle) (x : p.Torus) :
    p.step₀Biholomorph (circleFlow p t x) =
      circleFlow p.step₀ t (p.step₀Biholomorph x) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨z, rfl⟩ := p.lattice.mkQ_surjective x
  simp only [circleFlow_coe_mkQ, p.step₀Biholomorph_mkQ]

/-- The first original period change on the actual circle-orbit spaces. -/
def step₁CircleOrbitHomeomorph (p : PeriodDomain) : CircleOrbit p ≃ₜ CircleOrbit p.step₁ :=
  circleOrbitCongr p.step₁Biholomorph.toHomeomorph (step₁Biholomorph_circleFlow p)

/-- The second original period change on the actual circle-orbit spaces. -/
def step₂CircleOrbitHomeomorph (p : PeriodDomain) : CircleOrbit p ≃ₜ CircleOrbit p.step₂ :=
  circleOrbitCongr p.step₂Biholomorph.toHomeomorph (step₂Biholomorph_circleFlow p)

/-- The cusp marking change on the actual circle-orbit spaces. -/
def step₀CircleOrbitHomeomorph (p : PeriodDomain) : CircleOrbit p ≃ₜ CircleOrbit p.step₀ :=
  circleOrbitCongr p.step₀Biholomorph.toHomeomorph (step₀Biholomorph_circleFlow p)

@[simp] theorem step₁CircleOrbitHomeomorph_projection (p : PeriodDomain) (x : p.Torus) :
    step₁CircleOrbitHomeomorph p (circleOrbitProjection p x) =
      circleOrbitProjection p.step₁ (p.step₁Biholomorph x) :=
  circleOrbitCongr_projection _ _ x

@[simp] theorem step₂CircleOrbitHomeomorph_projection (p : PeriodDomain) (x : p.Torus) :
    step₂CircleOrbitHomeomorph p (circleOrbitProjection p x) =
      circleOrbitProjection p.step₂ (p.step₂Biholomorph x) :=
  circleOrbitCongr_projection _ _ x

@[simp] theorem step₀CircleOrbitHomeomorph_projection (p : PeriodDomain) (x : p.Torus) :
    step₀CircleOrbitHomeomorph p (circleOrbitProjection p x) =
      circleOrbitProjection p.step₀ (p.step₀Biholomorph x) :=
  circleOrbitCongr_projection _ _ x

/-- The same first period change in the literal projected-lattice models. -/
def step₁OrbitHomeomorph (p : PeriodDomain) : OrbitModel p ≃ₜ OrbitModel p.step₁ :=
  orbitModelCongr p.step₁Biholomorph.toHomeomorph (step₁Biholomorph_circleFlow p)

/-- The same second period change in the literal projected-lattice models. -/
def step₂OrbitHomeomorph (p : PeriodDomain) : OrbitModel p ≃ₜ OrbitModel p.step₂ :=
  orbitModelCongr p.step₂Biholomorph.toHomeomorph (step₂Biholomorph_circleFlow p)

/-- The same cusp marking change in the literal projected-lattice models. -/
def step₀OrbitHomeomorph (p : PeriodDomain) : OrbitModel p ≃ₜ OrbitModel p.step₀ :=
  orbitModelCongr p.step₀Biholomorph.toHomeomorph (step₀Biholomorph_circleFlow p)

@[simp] theorem step₁OrbitHomeomorph_projection (p : PeriodDomain) (x : p.Torus) :
    step₁OrbitHomeomorph p (torusProjection p x) =
      torusProjection p.step₁ (p.step₁Biholomorph x) :=
  orbitModelCongr_projection _ _ x

@[simp] theorem step₂OrbitHomeomorph_projection (p : PeriodDomain) (x : p.Torus) :
    step₂OrbitHomeomorph p (torusProjection p x) =
      torusProjection p.step₂ (p.step₂Biholomorph x) :=
  orbitModelCongr_projection _ _ x

@[simp] theorem step₀OrbitHomeomorph_projection (p : PeriodDomain) (x : p.Torus) :
    step₀OrbitHomeomorph p (torusProjection p x) =
      torusProjection p.step₀ (p.step₀Biholomorph x) :=
  orbitModelCongr_projection _ _ x

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
