import Wikipedia.HopfProblem.SphereHomologyCoefficientsBasic

/-!
# Explicit residues on integral scalar quotients

This algebraic helper identifies the quotient of an actually marked
infinite cyclic module by multiplication by `p`.  The quotient map is
the original integer marking followed by coefficient reduction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {M : Type} [AddCommGroup M] [Module ℤ M]

attribute [local instance] Submodule.Quotient.module

/-- The image of actual multiplication by the integer `p`. -/
def scalarImage (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] : Submodule ℤ M :=
  LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))

/-- An integral coordinate identifies the scalar image by genuine divisibility. -/
theorem mem_scalarImage_iff (p : ℕ) (e : M ≃ₗ[ℤ] ℤ) (x : M) :
    x ∈ scalarImage p M ↔ (p : ℤ) ∣ e x := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    change e ((p : ℤ) • y) = (p : ℤ) * e y
    simpa only [Int.cast_id, smul_eq_mul] using map_zsmul e (p : ℤ) y
  · rintro ⟨k, hk⟩
    refine ⟨e.symm k, ?_⟩
    apply e.injective
    change e ((p : ℤ) • e.symm k) = e x
    rw [map_zsmul, LinearEquiv.apply_symm_apply]
    exact hk.symm

/-- The explicit residue in an unchanged integral coordinate. -/
def markedResidue (p : ℕ) (e : M ≃ₗ[ℤ] ℤ) : M →ₗ[ℤ] ZMod p :=
  (Int.castAddHom (ZMod p)).toIntLinearMap.comp e.toLinearMap

@[simp] theorem markedResidue_apply (p : ℕ) (e : M ≃ₗ[ℤ] ℤ) (x : M) :
    markedResidue p e x = (e x : ZMod p) := rfl

theorem markedResidue_surjective (p : ℕ) (e : M ≃ₗ[ℤ] ℤ) :
    Function.Surjective (markedResidue p e) := by
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨e.symm k, ?_⟩
  rw [markedResidue_apply, LinearEquiv.apply_symm_apply]

/-- Exact equality of the integral scalar image and the residue kernel. -/
theorem scalarImage_eq_ker_markedResidue (p : ℕ) (e : M ≃ₗ[ℤ] ℤ) :
    scalarImage p M = LinearMap.ker (markedResidue p e) := by
  ext x
  rw [mem_scalarImage_iff p e, LinearMap.mem_ker, markedResidue_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The literal scalar quotient is the finite cyclic coefficient module. -/
def scalarQuotientEquivZMod (p : ℕ) (e : M ≃ₗ[ℤ] ℤ) :
    (M ⧸ scalarImage p M) ≃ₗ[ℤ] ZMod p := by
  let e₁ := Submodule.quotEquivOfEq _ _ (scalarImage_eq_ker_markedResidue p e)
  let e₂ := (markedResidue p e).quotKerEquivOfSurjective (markedResidue_surjective p e)
  let e₃ := e₁.trans e₂
  let ea : (M ⧸ scalarImage p M) ≃+ ZMod p :=
    { toEquiv := e₃.toEquiv
      map_add' := fun x y => e₃.map_add x y }
  exact ea.toIntLinearEquiv

@[simp] theorem scalarQuotientEquivZMod_mk (p : ℕ) (e : M ≃ₗ[ℤ] ℤ) (x : M) :
    scalarQuotientEquivZMod p e (Submodule.Quotient.mk x) = (e x : ZMod p) := rfl

end Wikipedia.HopfProblem.SphereHomologyCoefficients
