import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationCore

/-!
# The actual native cap-kernel presentation of second homology

The kernel of the three original cap maps is identified with the product
of the kernels of the three actual mapping-torus attachment maps.  The
remaining regular relation is literally the sum of the original regular
coefficients on these native kernels.  Thus second homology has a
canonical presentation using only the regular family and actual cap
kernels, without selecting any cap splitting or boundary matrix.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination

open SingularMayerVietoris ThreefoldOverlapMappingTorus PeriodTorusHigherHomology

/-- The kernel of one original native boundary-to-cap map. -/
abbrev NativeCapKernel (i : Puncture) (n : ℕ) :=
  LinearMap.ker (boundaryFillingHomologyMap i n)

/-- The actual regular-family coefficient on all native cap kernels. -/
def nativeCapKernelRegularMap (n : ℕ) :
    (∀ i : Puncture, NativeCapKernel i n) →ₗ[ℤ] SingularHomology SpecialRegularFamily n :=
  intLinearMapOfAddHom
    { toFun a := ∑ i : Puncture, boundaryRegularHomologyMap i n (a i).val
      map_zero' := by
        simp only [Pi.zero_apply, Submodule.coe_zero, map_zero, Finset.sum_const_zero]
      map_add' a b := by
        simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib] }

@[simp] theorem nativeCapKernelRegularMap_apply (n : ℕ)
    (a : ∀ i : Puncture, NativeCapKernel i n) :
    nativeCapKernelRegularMap n a =
      ∑ i : Puncture, boundaryRegularHomologyMap i n (a i).val := rfl

/-- A single native kernel class contributes exactly its original regular attachment column. -/
theorem nativeCapKernelRegularMap_single (n : ℕ) (i : Puncture) (a : NativeCapKernel i n) :
    nativeCapKernelRegularMap n (Pi.single i a) = boundaryRegularHomologyMap i n a.val := by
  classical
  rw [nativeCapKernelRegularMap_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, Submodule.coe_zero, map_zero]
  · simp

/-- Transport the literal original cap kernel through the actual overlap equivalences. -/
def nativeCapKernelEquiv (n : ℕ) :
    LinearMap.ker (starOverlapToFillingsHomologyMap n) ≃ₗ[ℤ]
      (∀ i : Puncture, NativeCapKernel i n) :=
  ({ toFun a i := ⟨overlapHomologyEquiv i n (a.val i), by
       have h := LinearMap.congr_fun (boundaryFillingHomologyMap_retraction i n) (a.val i)
       exact h.trans (congrFun a.property i)⟩
     invFun a := ⟨fun i => (overlapHomologyEquiv i n).symm (a i).val, by
       funext i
       have h := LinearMap.congr_fun (boundaryFillingHomologyMap_retraction i n)
         ((overlapHomologyEquiv i n).symm (a i).val)
       have hz := (congrArg (boundaryFillingHomologyMap i n)
         ((overlapHomologyEquiv i n).apply_symm_apply (a i).val)).trans (a i).property
       exact h.symm.trans hz⟩
     left_inv a := by
       apply Subtype.ext
       funext i
       exact (overlapHomologyEquiv i n).symm_apply_apply (a.val i)
     right_inv a := by
       funext i
       apply Subtype.ext
       exact (overlapHomologyEquiv i n).apply_symm_apply (a i).val
     map_add' a b := by
       funext i
       apply Subtype.ext
       exact (overlapHomologyEquiv i n).map_add (a.val i) (b.val i) } :
    LinearMap.ker (starOverlapToFillingsHomologyMap n) ≃+
      (∀ i : Puncture, NativeCapKernel i n)).toIntLinearEquiv

/-- The forward equivalence retains the original actual overlap homology map. -/
@[simp] theorem nativeCapKernelEquiv_apply_val (n : ℕ)
    (a : LinearMap.ker (starOverlapToFillingsHomologyMap n)) (i : Puncture) :
    (nativeCapKernelEquiv n a i).val = overlapHomologyEquiv i n (a.val i) := rfl

/-- The inverse retains the inverse of the same original equivalence. -/
@[simp] theorem nativeCapKernelEquiv_symm_val (n : ℕ)
    (a : ∀ i : Puncture, NativeCapKernel i n) (i : Puncture) :
    ((nativeCapKernelEquiv n).symm a).val i =
      (overlapHomologyEquiv i n).symm (a i).val := rfl

/-- The transported coefficient is exactly the original regular sum. -/
theorem nativeCapKernelRegularMap_equiv (n : ℕ)
    (a : LinearMap.ker (starOverlapToFillingsHomologyMap n)) :
    nativeCapKernelRegularMap n (nativeCapKernelEquiv n a) = capKernelRegularMap n a := by
  change (∑ i : Puncture, boundaryRegularHomologyMap i n
      (overlapHomologyEquiv i n (a.val i))) =
    ∑ i : Puncture, singularHomologyMap (overlapToRegularFamily i) n (a.val i)
  apply Finset.sum_congr rfl
  intro i _
  exact LinearMap.congr_fun (boundaryRegularHomologyMap_retraction i n) (a.val i)

/-- The image consists of the same genuine original regular relations. -/
theorem nativeCapKernelRegularMap_range (n : ℕ) :
    LinearMap.range (nativeCapKernelRegularMap n) = capKernelRegularImage n := by
  ext r
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(nativeCapKernelEquiv n).symm a, ?_⟩
    rw [← nativeCapKernelRegularMap_equiv, LinearEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨a, ha⟩
    exact ⟨nativeCapKernelEquiv n a, (nativeCapKernelRegularMap_equiv n a).trans ha⟩

/-- The original regular inclusion has exactly these native cap-kernel relations in every degree. -/
theorem regularInclusion_native_kernel (n : ℕ) :
    LinearMap.ker (singularHomologyMap originalRegularInclusion n) =
      LinearMap.range (nativeCapKernelRegularMap n) :=
  (regularInclusion_kernel n).trans (nativeCapKernelRegularMap_range n).symm

private def nativeRegularQuotientAddEquiv :
    (SingularHomology SpecialRegularFamily 2 ⧸ LinearMap.range (nativeCapKernelRegularMap 2)) ≃+
      (SingularHomology SpecialRegularFamily 2 ⧸ capKernelRegularImage 2) := by
  letI := Submodule.Quotient.module (LinearMap.range (nativeCapKernelRegularMap 2))
  letI := Submodule.Quotient.module (capKernelRegularImage 2)
  exact (Submodule.quotEquivOfEq _ _ (nativeCapKernelRegularMap_range 2)).toAddEquiv

/-- The native-kernel quotient maps canonically to actual second integral homology. -/
def nativeRegularCokernelEquiv :
    (SingularHomology SpecialRegularFamily 2 ⧸ LinearMap.range (nativeCapKernelRegularMap 2)) ≃ₗ[ℤ]
      SingularHomology Space 2 :=
  (nativeRegularQuotientAddEquiv.trans
    regularCapKernelCokernelEquiv.toAddEquiv).toIntLinearEquiv

/-- Its forward map is the original regular-family inclusion,
not a chosen abstract identification. -/
@[simp] theorem nativeRegularCokernelEquiv_mk (a : SingularHomology SpecialRegularFamily 2) :
    nativeRegularCokernelEquiv (Submodule.Quotient.mk a) =
      singularHomologyMap originalRegularInclusion 2 a := rfl

/-- Actual second homology as the regular family's quotient by genuine native cap-kernel images. -/
def homologyTwoNativeRegularCokernelEquiv :
    SingularHomology Space 2 ≃ₗ[ℤ]
      (SingularHomology SpecialRegularFamily 2 ⧸ LinearMap.range (nativeCapKernelRegularMap 2)) :=
  nativeRegularCokernelEquiv.symm

@[simp] theorem homologyTwoNativeRegularCokernelEquiv_inclusion
    (a : SingularHomology SpecialRegularFamily 2) :
    homologyTwoNativeRegularCokernelEquiv (singularHomologyMap originalRegularInclusion 2 a) =
      Submodule.Quotient.mk a :=
  nativeRegularCokernelEquiv.symm_apply_apply (Submodule.Quotient.mk a)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination
