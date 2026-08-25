import Util.Bernays.FormIdeal

/-!
# Norm and invertibility of the form ideal
-/

open scoped nonZeroDivisors

namespace BinQuadForm

theorem formIdeal_isUnit {f : BinQuadForm} (hf : f.PosDef) (hprim : f.Primitive) :
    letI := hf.orderIsDomain
    IsUnit (f.formIdeal : FractionalIdeal f.Order⁰ (FractionRing f.Order)) := by
  letI := hf.orderIsDomain
  have ha : (f.a : f.Order) ≠ 0 := by
    intro h
    have hr := congrArg QuadraticAlgebra.re h
    have : f.a = 0 := by simpa using hr
    exact hf.1.ne' this
  have hunit : IsUnit
      ((Ideal.span ({(f.a : f.Order)} : Set f.Order) : Ideal f.Order) :
        FractionalIdeal f.Order⁰ (FractionRing f.Order)) := by
    apply IsUnit.of_mul_eq_one _
    exact FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing f.Order) ha
  rw [← formIdeal_mul_conjugate hprim, FractionalIdeal.coeIdeal_mul] at hunit
  exact isUnit_of_mul_isUnit_left hunit

def formIdealLinearMap (f : BinQuadForm) : (Fin 2 → ℤ) →ₗ[ℤ] f.formIdeal where
  toFun x := ⟨⟨f.a * x 0, x 1⟩, dvd_mul_right _ _⟩
  map_add' x y := by apply Subtype.ext; ext <;> simp <;> ring
  map_smul' r x := by apply Subtype.ext; ext <;> simp <;> ring

@[simp] theorem formIdealLinearMap_re (f : BinQuadForm) (x : Fin 2 → ℤ) :
    ((f.formIdealLinearMap x : f.formIdeal) : f.Order).re = f.a * x 0 := rfl

@[simp] theorem formIdealLinearMap_im (f : BinQuadForm) (x : Fin 2 → ℤ) :
    ((f.formIdealLinearMap x : f.formIdeal) : f.Order).im = x 1 := rfl

theorem formIdealLinearMap_bijective {f : BinQuadForm} (ha : f.a ≠ 0) :
    Function.Bijective f.formIdealLinearMap := by
  constructor
  · intro x y h
    have hval := congrArg (fun z : f.formIdeal => (z : f.Order)) h
    have hre := congrArg QuadraticAlgebra.re hval
    have him := congrArg QuadraticAlgebra.im hval
    funext i
    fin_cases i
    · exact mul_left_cancel₀ ha hre
    · exact him
  · intro z
    obtain ⟨u, hu⟩ := z.property
    refine ⟨![u, (z : f.Order).im], ?_⟩
    apply Subtype.ext
    exact QuadraticAlgebra.ext hu.symm rfl

noncomputable def formIdealBasis {f : BinQuadForm} (ha : f.a ≠ 0) :
    Module.Basis (Fin 2) ℤ f.formIdeal :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective f.formIdealLinearMap
    (formIdealLinearMap_bijective ha)).symm

theorem formIdeal_cardQuot {f : BinQuadForm} (hf : f.PosDef) :
    f.formIdeal.cardQuot = f.a.natAbs := by
  letI := hf.orderIsDomain
  rw [Erdos1081.cardQuot_eq_natAbs_det_basis_change
    (QuadraticAlgebra.basis (-f.a * f.c) f.b) f.formIdeal (formIdealBasis hf.1.ne')]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [formIdealBasis, Module.Basis.coe_ofEquivFun, formIdealLinearMap,
    Module.Basis.toMatrix_apply]

noncomputable def formIdealClass {f : BinQuadForm} (hf : f.PosDef) (hprim : f.Primitive) :
    letI := hf.orderIsDomain
    ClassGroup f.Order :=
  letI := hf.orderIsDomain
  ClassGroup.mk (FractionRing f.Order) (formIdeal_isUnit hf hprim).unit

end BinQuadForm
