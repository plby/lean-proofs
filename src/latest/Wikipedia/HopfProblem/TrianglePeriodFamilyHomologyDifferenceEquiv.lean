import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyOrientationAlgebra

/-!
# Kernel and cokernel transport through an actual commuting square

A proved commuting square of integral linear equivalences induces equivalences
of the literal kernel submodules and quotient cokernels. The formulas retain
the given maps on underlying kernel vectors and quotient representatives.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
  TrianglePeriodFamilyHomologyAlgebra.kernelModule

variable {M N M' N' : Type*}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module ℤ M] [Module ℤ N] [Module ℤ M'] [Module ℤ N']

/-- Membership in the two images agrees under a commuting square of equivalences. -/
theorem mem_range_iff_of_commuting (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N')
    (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N') (h : ∀ x, d (f x) = g (e x)) (y : N) :
    d y ∈ LinearMap.range g ↔ y ∈ LinearMap.range f := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, d.injective ?_⟩
    calc
      d (f (e.symm x)) = g (e (e.symm x)) := h _
      _ = g x := congrArg g (e.apply_symm_apply x)
      _ = d y := hx
  · rintro ⟨x, hx⟩
    exact ⟨e x, (h x).symm.trans (congrArg d hx)⟩

/-- A commuting square of integral equivalences identifies the literal kernels. -/
def kernelEquivOfCommuting (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N')
    (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N') (h : ∀ x, d (f x) = g (e x)) :
    LinearMap.ker f ≃ₗ[ℤ] LinearMap.ker g :=
  ({ toFun x := ⟨e x.val, by
       change g (e x.val) = 0
       calc
         g (e x.val) = d (f x.val) := (h x.val).symm
         _ = d 0 := congrArg d x.property
         _ = 0 := d.map_zero⟩
     invFun y := ⟨e.symm y.val, by
       change f (e.symm y.val) = 0
       apply d.injective
       calc
         d (f (e.symm y.val)) = g (e (e.symm y.val)) := h _
         _ = g y.val := congrArg g (e.apply_symm_apply y.val)
         _ = 0 := y.property
         _ = d 0 := d.map_zero.symm⟩
     left_inv x := Subtype.ext (e.symm_apply_apply x.val)
     right_inv y := Subtype.ext (e.apply_symm_apply y.val)
     map_add' x y := Subtype.ext (e.map_add x.val y.val)
   } : LinearMap.ker f ≃+ LinearMap.ker g).toIntLinearEquiv

@[simp] theorem kernelEquivOfCommuting_apply_val (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N')
    (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N') (h : ∀ x, d (f x) = g (e x))
    (x : LinearMap.ker f) :
    (kernelEquivOfCommuting f g e d h x : M') = e x.val := rfl

@[simp] theorem kernelEquivOfCommuting_symm_apply_val
    (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N') (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N')
    (h : ∀ x, d (f x) = g (e x)) (x : LinearMap.ker g) :
    ((kernelEquivOfCommuting f g e d h).symm x : M) = e.symm x.val := rfl

/-- The cokernel equivalence of a commuting square sends each representative
through its specified codomain equivalence. -/
def cokernelEquivOfCommuting (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N')
    (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N') (h : ∀ x, d (f x) = g (e x)) :
    (N ⧸ LinearMap.range f) ≃ₗ[ℤ] (N' ⧸ LinearMap.range g) :=
  ({ toEquiv := @Quotient.congr N N' (Submodule.quotientRel (LinearMap.range f))
       (Submodule.quotientRel (LinearMap.range g)) d.toEquiv (fun x y => by
         change (LinearMap.range f).quotientRel x y ↔
           (LinearMap.range g).quotientRel (d x) (d y)
         rw [Submodule.quotientRel_def, Submodule.quotientRel_def, ← map_sub]
         exact (mem_range_iff_of_commuting f g e d h (x - y)).symm)
     map_add' := by
       rintro ⟨x⟩ ⟨y⟩
       change Submodule.Quotient.mk (d (x + y)) = Submodule.Quotient.mk (d x + d y)
       exact congrArg Submodule.Quotient.mk (d.map_add x y)
   } : (N ⧸ LinearMap.range f) ≃+ (N' ⧸ LinearMap.range g)).toIntLinearEquiv

@[simp] theorem cokernelEquivOfCommuting_mk (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N')
    (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N') (h : ∀ x, d (f x) = g (e x)) (a : N) :
    cokernelEquivOfCommuting f g e d h (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (d a) := rfl

@[simp] theorem cokernelEquivOfCommuting_symm_mk
    (f : M →ₗ[ℤ] N) (g : M' →ₗ[ℤ] N') (e : M ≃ₗ[ℤ] M') (d : N ≃ₗ[ℤ] N')
    (h : ∀ x, d (f x) = g (e x)) (a : N') :
    (cokernelEquivOfCommuting f g e d h).symm (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (d.symm a) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference
