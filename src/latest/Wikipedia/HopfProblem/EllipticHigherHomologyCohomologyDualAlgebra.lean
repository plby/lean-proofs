import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDual
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualAlgebraRankOne
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverAlgebraCoordinates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The integer dual of a triangular covering-coordinate map

For the genuine algebraic dual of a map `(x₀,x₁) ↦ (x₀+t*x₁,d*x₁)`,
the dual coordinates are `(a,b) ↦ (a,t*a+d*b)`.  Its exact image consists
of the pairs for which `b-t*a` is divisible by `d`.  Reduction of that
sheared coordinate gives the actual dual cokernel as `ZMod d`, with
additive index `d`, also at `d=0` under the infinite-index convention.
The imported rank-one counterpart treats multiplication by `d` in the
same actual-dual coordinates.

These are integer-linear algebra results.  No assertion about the
coordinates of a topological covering map is assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyDualAlgebra

abbrev Coordinates := Fin 2 → ℤ
abbrev IntegerDual := Coordinates →ₗ[ℤ] ℤ

/-- The triangular integer map with its off-diagonal coefficient retained. -/
def triangularMap (t : ℤ) (d : ℕ) : Coordinates →ₗ[ℤ] Coordinates where
  toFun x := ![x 0 + t * x 1, (d : ℤ) * x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp <;> ring

@[simp] theorem triangularMap_apply (t : ℤ) (d : ℕ) (x : Coordinates) :
    triangularMap t d x = ![x 0 + t * x 1, (d : ℤ) * x 1] := rfl

/-- The actual dual map has the transposed coordinate formula. -/
theorem dual_coordinates_of_formula (q : Coordinates →ₗ[ℤ] Coordinates)
    (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) (φ : IntegerDual) :
    intDualCoordinates 2 (q.dualMap φ) =
      ![intDualCoordinates 2 φ 0,
        t * intDualCoordinates 2 φ 0 + (d : ℤ) * intDualCoordinates 2 φ 1] := by
  have hzero : q (Pi.single 0 1) = Pi.single 0 1 := by
    rw [hq]
    ext i
    fin_cases i <;> simp
  have hone : q (Pi.single 1 1) =
      t • Pi.single 0 1 + (d : ℤ) • Pi.single 1 1 := by
    rw [hq]
    ext i
    fin_cases i <;> simp
  ext i
  fin_cases i
  · change intDualCoordinates 2 (q.dualMap φ) 0 = intDualCoordinates 2 φ 0
    rw [intDualCoordinates_apply, intDualCoordinates_apply]
    change φ (q (Pi.single 0 1)) = φ (Pi.single 0 1)
    rw [hzero]
  · change intDualCoordinates 2 (q.dualMap φ) 1 =
      t * intDualCoordinates 2 φ 0 + (d : ℤ) * intDualCoordinates 2 φ 1
    rw [intDualCoordinates_apply, intDualCoordinates_apply, intDualCoordinates_apply]
    change φ (q (Pi.single 1 1)) = t * φ (Pi.single 0 1) + (d : ℤ) * φ (Pi.single 1 1)
    rw [hone, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]

theorem triangularMap_dual_coordinates (t : ℤ) (d : ℕ) (φ : IntegerDual) :
    intDualCoordinates 2 ((triangularMap t d).dualMap φ) =
      ![intDualCoordinates 2 φ 0,
        t * intDualCoordinates 2 φ 0 + (d : ℤ) * intDualCoordinates 2 φ 1] :=
  dual_coordinates_of_formula (triangularMap t d) t d (fun _ => rfl) φ

/-- The exact dual image, including the off-diagonal correction. -/
theorem mem_dualRange_iff_of_formula (q : Coordinates →ₗ[ℤ] Coordinates)
    (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) (φ : IntegerDual) :
    φ ∈ LinearMap.range q.dualMap ↔
      (d : ℤ) ∣ intDualCoordinates 2 φ 1 - t * intDualCoordinates 2 φ 0 := by
  constructor
  · rintro ⟨ψ, rfl⟩
    rw [dual_coordinates_of_formula q t d hq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨intDualCoordinates 2 ψ 1, by ring⟩
  · rintro ⟨k, hk⟩
    refine ⟨(intDualCoordinates 2).symm ![intDualCoordinates 2 φ 0, k], ?_⟩
    apply (intDualCoordinates 2).injective
    rw [dual_coordinates_of_formula q t d hq, LinearEquiv.apply_symm_apply]
    ext i
    fin_cases i
    · simp
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      calc
        t * intDualCoordinates 2 φ 0 + (d : ℤ) * k =
            t * intDualCoordinates 2 φ 0 +
              (intDualCoordinates 2 φ 1 - t * intDualCoordinates 2 φ 0) := by rw [hk]
        _ = intDualCoordinates 2 φ 1 := by ring

/-- The sheared residue on the actual integer dual. -/
def dualResidue (t : ℤ) (d : ℕ) : IntegerDual →ₗ[ℤ] ZMod d :=
  (Int.castAddHom (ZMod d)).toIntLinearMap.comp
    (((LinearMap.proj 1 : Coordinates →ₗ[ℤ] ℤ) - t • LinearMap.proj 0).comp
      (intDualCoordinates 2).toLinearMap)

@[simp] theorem dualResidue_apply (t : ℤ) (d : ℕ) (φ : IntegerDual) :
    dualResidue t d φ =
      ((intDualCoordinates 2 φ 1 - t * intDualCoordinates 2 φ 0 : ℤ) : ZMod d) := by
  simp [dualResidue]

theorem dualResidue_surjective (t : ℤ) (d : ℕ) : Function.Surjective (dualResidue t d) := by
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨(intDualCoordinates 2).symm ![0, k], ?_⟩
  rw [dualResidue_apply, LinearEquiv.apply_symm_apply]
  simp

theorem dualRange_eq_ker_of_formula (q : Coordinates →ₗ[ℤ] Coordinates)
    (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) :
    LinearMap.range q.dualMap = LinearMap.ker (dualResidue t d) := by
  ext φ
  rw [mem_dualRange_iff_of_formula q t d hq, LinearMap.mem_ker, dualResidue_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The genuine dual cokernel is the sheared residue module. -/
def dualCokernelEquivZModOfFormula (q : Coordinates →ₗ[ℤ] Coordinates)
    (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) :
    (IntegerDual ⧸ LinearMap.range q.dualMap) ≃ₗ[ℤ] ZMod d :=
  (Submodule.quotEquivOfEq _ _ (dualRange_eq_ker_of_formula q t d hq)).trans
    ((dualResidue t d).quotKerEquivOfSurjective (dualResidue_surjective t d))

@[simp] theorem dualCokernelEquivZModOfFormula_apply_mk
    (q : Coordinates →ₗ[ℤ] Coordinates) (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) (φ : IntegerDual) :
    dualCokernelEquivZModOfFormula q t d hq (Submodule.Quotient.mk φ) =
      ((intDualCoordinates 2 φ 1 - t * intDualCoordinates 2 φ 0 : ℤ) : ZMod d) := by
  change dualResidue t d φ = _
  exact dualResidue_apply t d φ

@[simp] theorem dualCokernelEquivZModOfFormula_symm_apply_intCast
    (q : Coordinates →ₗ[ℤ] Coordinates) (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) (k : ℤ) :
    (dualCokernelEquivZModOfFormula q t d hq).symm (k : ZMod d) =
      Submodule.Quotient.mk ((intDualCoordinates 2).symm ![0, k]) := by
  apply (dualCokernelEquivZModOfFormula q t d hq).injective
  rw [LinearEquiv.apply_symm_apply, dualCokernelEquivZModOfFormula_apply_mk,
    LinearEquiv.apply_symm_apply]
  simp

/-- The exact additive image index; no positivity is needed for the index convention. -/
theorem dualRange_index_of_formula (q : Coordinates →ₗ[ℤ] Coordinates)
    (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) :
    (LinearMap.range q.dualMap).toAddSubgroup.index = d := by
  change Nat.card (IntegerDual ⧸ LinearMap.range q.dualMap) = d
  exact (Nat.card_congr (dualCokernelEquivZModOfFormula q t d hq).toEquiv).trans
    (Nat.card_zmod d)

theorem dualRange_finiteIndex_of_formula (q : Coordinates →ₗ[ℤ] Coordinates)
    (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) (hd : 0 < d) :
    (LinearMap.range q.dualMap).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [dualRange_index_of_formula q t d hq]
  exact hd.ne'

/-- Positive diagonal coefficient makes the actual dual map injective. -/
theorem dualMap_injective_of_formula (q : Coordinates →ₗ[ℤ] Coordinates)
    (t : ℤ) (d : ℕ)
    (hq : ∀ x, q x = ![x 0 + t * x 1, (d : ℤ) * x 1]) (hd : 0 < d) :
    Function.Injective q.dualMap := by
  intro φ ψ h
  apply (intDualCoordinates 2).injective
  have hc := congrArg (intDualCoordinates 2) h
  rw [dual_coordinates_of_formula q t d hq, dual_coordinates_of_formula q t d hq] at hc
  have hzero : intDualCoordinates 2 φ 0 = intDualCoordinates 2 ψ 0 := by
    simpa only [Matrix.cons_val_zero] using congrFun hc 0
  have hone : t * intDualCoordinates 2 φ 0 + (d : ℤ) * intDualCoordinates 2 φ 1 =
      t * intDualCoordinates 2 ψ 0 + (d : ℤ) * intDualCoordinates 2 ψ 1 := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using congrFun hc 1
  rw [hzero] at hone
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  ext i
  fin_cases i
  · exact hzero
  · exact mul_left_cancel₀ hd' (add_left_cancel hone)

/-- A unit diagonal gives surjectivity even when the shear is nonzero. -/
theorem dualMap_surjective_of_formula_one (q : Coordinates →ₗ[ℤ] Coordinates)
    (t : ℤ) (hq : ∀ x, q x = ![x 0 + t * x 1, x 1]) :
    Function.Surjective q.dualMap := by
  intro φ
  apply (mem_dualRange_iff_of_formula q t 1 (fun x => by simpa using hq x) φ).mpr
  simp

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyDualAlgebra
