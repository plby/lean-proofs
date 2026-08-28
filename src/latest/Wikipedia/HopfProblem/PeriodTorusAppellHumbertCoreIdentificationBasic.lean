import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCore
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertQuotient

/-!
# Fibrewise identification with the actual Appell--Humbert quotient

The vector-bundle core and the diagonal orbit quotient are independently
defined. The explicit maps below identify them using the original quotient
charts of the period torus. Their fibre coordinates are the actual scalar
coordinates of the orbit quotient, with the given factor of automorphy.
-/

noncomputable section

open Set Topology Bundle

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- Send a bundle vector to its orbit using the preferred torus chart. -/
def toAssociated (u : (data F).core.TotalSpace) : AssociatedSpace F :=
  associatedMap F (lift p u.1 u.1, id (α := ℂ) u.2)

@[simp] theorem projection_toAssociated (u : (data F).core.TotalSpace) :
    projection F (toAssociated F u) = u.1 := by
  rw [toAssociated, projection_associatedMap]
  exact lift_project p u.1 (mem_baseSet p u.1)

/-- The quotient fibre coordinate in the preferred torus chart is the inverse. -/
def fromAssociated (u : AssociatedSpace F) : (data F).core.TotalSpace :=
  ⟨projection F u, fibreCoordinate F
    (lift p (projection F u) (projection F u)) u
    (lift_project p _ (mem_baseSet p _)).symm⟩

@[simp] theorem fromAssociated_proj (u : AssociatedSpace F) :
    (fromAssociated F u).proj = projection F u := rfl

@[simp] theorem toAssociated_fromAssociated (u : AssociatedSpace F) :
    toAssociated F (fromAssociated F u) = u :=
  associatedMap_fibreCoordinate F _ u (lift_project p _ (mem_baseSet p _)).symm

theorem toAssociated_injective : Function.Injective (toAssociated F) := by
  rintro ⟨b, z⟩ ⟨c, w⟩ he
  have hb : b = c := by
    simpa only [projection_toAssociated] using congrArg (projection F) he
  subst c
  have hz : z = w := associatedMap_fibre_injective F (lift p b b) he
  cases hz
  rfl

@[simp] theorem fromAssociated_toAssociated (u : (data F).core.TotalSpace) :
    fromAssociated F (toAssociated F u) = u := by
  apply toAssociated_injective F
  exact toAssociated_fromAssociated F _

/-- In every original torus chart, the map uses the bundle's scalar coordinate. -/
theorem toAssociated_localTriv (i : p.Torus) (u : (data F).core.TotalSpace)
    (hu : u.1 ∈ baseSet p i) :
    toAssociated F u =
      associatedMap F (lift p i u.1, ((data F).core.localTriv i u).2) := by
  change associatedMap F (lift p u.1 u.1, id (α := ℂ) u.2) =
    associatedMap F (lift p i u.1,
      (F.factor (deck p u.1 i u.1) (lift p u.1 u.1) : ℂ) * id (α := ℂ) u.2)
  rw [← deck_spec p u.1 i ⟨mem_baseSet p u.1, hu⟩]
  exact (associatedMap_diagonal F _ _).symm

/-- Quotient coordinates in a specified local lift use the actual factor at
the original covering point, not a constant character value. -/
theorem localTriv_fromAssociated_map (i : p.Torus) (a : ComplexPlane₂) (z : ℂ)
    (l : p.lattice) (ha : p.lattice.mkQ a ∈ baseSet p i)
    (hl : lift p i (p.lattice.mkQ a) = a + l) :
    (data F).core.localTriv i (fromAssociated F (associatedMap F (a, z))) =
      (p.lattice.mkQ a, (F.factor l a : ℂ) * z) := by
  apply Prod.ext
  · rfl
  · apply associatedMap_fibre_injective F (lift p i (p.lattice.mkQ a))
    calc
      associatedMap F (lift p i (p.lattice.mkQ a),
          ((data F).core.localTriv i (fromAssociated F (associatedMap F (a, z)))).2) =
          toAssociated F (fromAssociated F (associatedMap F (a, z))) :=
        (toAssociated_localTriv F i (fromAssociated F (associatedMap F (a, z))) ha).symm
      _ = associatedMap F (a, z) := toAssociated_fromAssociated F _
      _ = associatedMap F (lift p i (p.lattice.mkQ a), (F.factor l a : ℂ) * z) := by
        rw [hl]
        exact (associatedMap_diagonal F l (a, z)).symm

/-- The scalar coordinate of the image in any torus chart. -/
theorem fibreCoordinate_toAssociated (i b : p.Torus) (z : (data F).core.Fiber b)
    (hb : b ∈ baseSet p i) :
    fibreCoordinate F (lift p i b) (toAssociated F ⟨b, z⟩)
      ((projection_toAssociated F _).trans (lift_project p i hb).symm) =
        (F.factor (deck p b i b) (lift p b b) : ℂ) * id (α := ℂ) z := by
  apply associatedMap_fibre_injective F (lift p i b)
  exact (associatedMap_fibreCoordinate F _ _ _).trans
    (toAssociated_localTriv F i ⟨b, z⟩ hb)

/-- Actual scalar quotient coordinates give a complex-linear equivalence on
each fibre, with explicit inverse multiplication by the inverse factor. -/
def fibreLinearEquiv (i b : p.Torus) : (data F).core.Fiber b ≃ₗ[ℂ] ℂ where
  toFun z := (F.factor (deck p b i b) (lift p b b) : ℂ) * id (α := ℂ) z
  invFun z := (F.factor (deck p b i b) (lift p b b) : ℂ)⁻¹ * z
  left_inv z := by
    change (F.factor (deck p b i b) (lift p b b) : ℂ)⁻¹ *
      ((F.factor (deck p b i b) (lift p b b) : ℂ) * id (α := ℂ) z) = id (α := ℂ) z
    rw [← mul_assoc, inv_mul_cancel₀ (F.factor (deck p b i b) (lift p b b)).ne_zero,
      one_mul]
  right_inv z := by
    change (F.factor (deck p b i b) (lift p b b) : ℂ) *
      ((F.factor (deck p b i b) (lift p b b) : ℂ)⁻¹ * z) = z
    rw [← mul_assoc, mul_inv_cancel₀ (F.factor (deck p b i b) (lift p b b)).ne_zero,
      one_mul]
  map_add' z w := mul_add _ (id (α := ℂ) z) (id (α := ℂ) w)
  map_smul' a z := mul_left_comm _ a (id (α := ℂ) z)

@[simp] theorem fibreLinearEquiv_apply (i b : p.Torus) (z : (data F).core.Fiber b) :
    fibreLinearEquiv F i b z =
      (F.factor (deck p b i b) (lift p b b) : ℂ) * id (α := ℂ) z := rfl

theorem fibreCoordinate_toAssociated_linear (i b : p.Torus) (z : (data F).core.Fiber b)
    (hb : b ∈ baseSet p i) :
    fibreCoordinate F (lift p i b) (toAssociated F ⟨b, z⟩)
      ((projection_toAssociated F _).trans (lift_project p i hb).symm) =
        fibreLinearEquiv F i b z :=
  fibreCoordinate_toAssociated F i b z hb

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core
