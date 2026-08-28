import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessProducts

/-!
# The kernel of a sum with an invertible column

For the actual map `F (a, b) = f a + e b`, where the second column `e` is
an integral linear equivalence, projection onto `a` identifies `ker F`
with `A`. Its inverse is the literal graph `a ↦ (a, -e.symm (f a))`.
The same invertible column also makes `F` surjective.

Both the product and its kernel may carry arbitrary supplied integer
module instances. The additive kernel equivalence is converted using
the proved compatibility of every integer action with repeated addition.
No geometric map or matrix identification is assumed by this algebraic
construction; callers must supply the stated equality of their actual maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldHomologyTopDegreeAlgebra

variable {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
  [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]

/-- The literal sum of a first column and an invertible second column,
with the supplied native integer action on the product. -/
def columnSum (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D) : (A × B) →ₗ[ℤ] D :=
  { f.toAddMonoidHom.coprod e.toAddEquiv.toAddMonoidHom with
    map_smul' n p := by
      convert! (f.toAddMonoidHom.coprod e.toAddEquiv.toAddMonoidHom).map_zsmul n p using 1
      · exact congrArg (f.toAddMonoidHom.coprod e.toAddEquiv.toAddMonoidHom)
          (int_smul_eq_zsmul ..)
      · exact int_smul_eq_zsmul .. }

@[simp] theorem columnSum_apply (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D) (a : A) (b : B) :
    columnSum f e (a, b) = f a + e b := rfl

/-- A supplied pointwise column formula is an equality of the actual linear maps. -/
theorem eq_columnSum_of_apply (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) : F = columnSum f e := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  exact hF a b

/-- The actual map is onto because its second column is onto. -/
theorem surjective_of_columnIso (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) : Function.Surjective F := by
  intro d
  refine ⟨(0, e.symm d), ?_⟩
  rw [hF, map_zero, LinearEquiv.apply_symm_apply, zero_add]

theorem columnSum_surjective (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D) :
    Function.Surjective (columnSum f e) :=
  surjective_of_columnIso (columnSum f e) f e (fun _ _ => rfl)

private def kernelProjectionAddEquiv (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) : LinearMap.ker F ≃+ A where
  toFun x := x.val.1
  invFun a := ⟨(a, -e.symm (f a)), by
    change F (a, -e.symm (f a)) = 0
    rw [hF, map_neg, LinearEquiv.apply_symm_apply, add_neg_cancel]⟩
  left_inv x := by
    apply Subtype.ext
    change (x.val.1, -e.symm (f x.val.1)) = x.val
    refine Prod.ext (by rfl) ?_
    apply e.injective
    change e (-e.symm (f x.val.1)) = e x.val.2
    rw [map_neg, LinearEquiv.apply_symm_apply]
    have hx : f x.val.1 + e x.val.2 = 0 := (hF x.val.1 x.val.2).symm.trans x.property
    calc
      -f x.val.1 = -f x.val.1 + 0 := (add_zero _).symm
      _ = -f x.val.1 + (f x.val.1 + e x.val.2) := congrArg (fun d => -f x.val.1 + d) hx.symm
      _ = e x.val.2 := by rw [← add_assoc, neg_add_cancel, zero_add]
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The kernel of the actual column-sum map is canonically its first factor.
The scalar action on the kernel need not be definitionally the inherited one. -/
def kernelEquivOfColumnIso (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) [Module ℤ (LinearMap.ker F)] :
    LinearMap.ker F ≃ₗ[ℤ] A :=
  (kernelProjectionAddEquiv F f e hF).toIntLinearEquiv

/-- The forward equivalence is literally first-coordinate projection. -/
@[simp] theorem kernelEquivOfColumnIso_apply (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) [Module ℤ (LinearMap.ker F)]
    (x : LinearMap.ker F) : kernelEquivOfColumnIso F f e hF x = x.val.1 := rfl

/-- The inverse retains both actual columns and the required negative sign. -/
@[simp] theorem kernelEquivOfColumnIso_symm_val (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) [Module ℤ (LinearMap.ker F)] (a : A) :
    ((kernelEquivOfColumnIso F f e hF).symm a : A × B) =
      (a, -e.symm (f a)) := rfl

/-- The specialization to the explicitly constructed column sum. -/
def kernelColumnSumEquiv (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    [Module ℤ (LinearMap.ker (columnSum f e))] :
    LinearMap.ker (columnSum f e) ≃ₗ[ℤ] A :=
  kernelEquivOfColumnIso (columnSum f e) f e (fun _ _ => rfl)

@[simp] theorem kernelColumnSumEquiv_apply (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    [Module ℤ (LinearMap.ker (columnSum f e))] (x : LinearMap.ker (columnSum f e)) :
    kernelColumnSumEquiv f e x = x.val.1 := rfl

@[simp] theorem kernelColumnSumEquiv_symm_val (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    [Module ℤ (LinearMap.ker (columnSum f e))] (a : A) :
    ((kernelColumnSumEquiv f e).symm a : A × B) = (a, -e.symm (f a)) := rfl

/-- Finiteness follows from the actual kernel equivalence, not from a presentation assumption. -/
theorem kernel_finite_of_columnIso (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) [Module ℤ (LinearMap.ker F)]
    [Module.Finite ℤ A] : Module.Finite ℤ (LinearMap.ker F) :=
  Module.Finite.of_surjective (kernelEquivOfColumnIso F f e hF).symm.toLinearMap
    (kernelEquivOfColumnIso F f e hF).symm.surjective

theorem kernel_free_of_columnIso (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) [Module ℤ (LinearMap.ker F)]
    [Module.Free ℤ A] : Module.Free ℤ (LinearMap.ker F) :=
  Module.Free.of_equiv (kernelEquivOfColumnIso F f e hF).symm

theorem kernel_finrank_of_columnIso (F : (A × B) →ₗ[ℤ] D)
    (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b) [Module ℤ (LinearMap.ker F)] :
    Module.finrank ℤ (LinearMap.ker F) = Module.finrank ℤ A :=
  (kernelEquivOfColumnIso F f e hF).finrank_eq

end Wikipedia.HopfProblem.ThreefoldHomologyTopDegreeAlgebra
