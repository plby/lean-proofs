import Wikipedia.HopfProblem.DegreeCollapsePrimitiveClassSplit

/-!
# A kernel quotient retaining both maps into a common group

Suppose T is onto, N is one-to-one, and an old class maps into the range
of N exactly when an integral detector vanishes. If the kernel of T is
the span of the actual attaching class, the detector kernel modulo that
same class is isomorphic to the domain of N. The equivalence is determined
by the equation N(lift(x)) = T(x), not by a rank or an abstract splitting.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.DegreeCollapse.ExactKernelQuotient

variable {H W J : Type*} [AddCommGroup H] [Module ℤ H]
  [AddCommGroup W] [Module ℤ W] [AddCommGroup J] [Module ℤ J]
  (T : H →ₗ[ℤ] W) (N : J →ₗ[ℤ] W) (p : H →ₗ[ℤ] ℤ)
  (hN : Injective N) (he : ∀ x, T x ∈ LinearMap.range N ↔ p x = 0)

def traceIntoRange : LinearMap.ker p →ₗ[ℤ] LinearMap.range N :=
  (T.comp (PrimitiveSplitting.kernelInclusion p)).codRestrict _
    (fun x ↦ (he x).mpr x.property)

def liftMap : LinearMap.ker p →ₗ[ℤ] J := by
  let E := (LinearEquiv.ofInjective N hN).symm
  let r : LinearMap.ker p →+ J := {
    toFun x := E (traceIntoRange T N p he x)
    map_zero' := by rw [map_zero, map_zero]
    map_add' := by intro x y; rw [map_add, map_add] }
  exact {
    toFun := r
    map_add' := r.map_add
    map_smul' := by
      intro k x
      exact (r.map_zsmul k x).trans
        (int_smul_eq_zsmul (inferInstance : Module ℤ J) k (r x)).symm }

theorem liftMap_spec (x : LinearMap.ker p) : N (liftMap T N p hN he x) = T x := by
  change N ((LinearEquiv.ofInjective N hN).symm (traceIntoRange T N p he x)) = _
  exact LinearEquiv.ofInjective_symm_apply _ _

theorem liftMap_surjective (hT : Surjective T) : Surjective (liftMap T N p hN he) := by
  intro y
  obtain ⟨x, hx⟩ := hT (N y)
  have hp : p x = 0 := (he x).mp ⟨y, hx.symm⟩
  refine ⟨⟨x, hp⟩, hN ?_⟩
  rw [liftMap_spec]
  exact hx

variable (a : H) (hker : LinearMap.ker T = Submodule.span ℤ {a})

include he hker in
theorem attaching_detector_zero : p a = 0 := by
  have ha : T a = 0 := by
    change a ∈ LinearMap.ker T
    rw [hker]
    exact Submodule.subset_span (mem_singleton _)
  exact (he a).mp ⟨0, (map_zero N).trans ha.symm⟩

def attachingClass : LinearMap.ker p := ⟨a, attaching_detector_zero T N p he a hker⟩

theorem liftMap_attaching_zero : liftMap T N p hN he (attachingClass T N p he a hker) = 0 := by
  apply hN
  rw [liftMap_spec, map_zero]
  change a ∈ LinearMap.ker T
  rw [hker]
  exact Submodule.subset_span (mem_singleton _)

theorem liftMap_kernel : LinearMap.ker (liftMap T N p hN he) =
    Submodule.span ℤ {attachingClass T N p he a hker} := by
  ext x
  constructor
  · intro hx
    have hTx : T x.val = 0 := by
      rw [← liftMap_spec T N p hN he x, hx, map_zero]
    have hxa : x.val ∈ Submodule.span ℤ {a} := by
      rw [← hker]
      exact hTx
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hxa
    apply Submodule.mem_span_singleton.mpr
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact (int_smul_eq_zsmul (inferInstance : Module ℤ H) k a).symm.trans hk
  · intro hx
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hx
    change liftMap T N p hN he x = 0
    rw [← hk, map_zsmul, liftMap_attaching_zero T N p hN he a hker, zsmul_zero]

def quotientEquiv (hT : Surjective T) :
    (LinearMap.ker p ⧸ Submodule.span ℤ {attachingClass T N p he a hker}) ≃ₗ[ℤ] J := by
  let E := (Submodule.quotEquivOfEq _ _ (liftMap_kernel T N p hN he a hker).symm).trans
    ((liftMap T N p hN he).quotKerEquivOfSurjective (liftMap_surjective T N p hN he hT))
  let ea : (LinearMap.ker p ⧸ Submodule.span ℤ {attachingClass T N p he a hker}) ≃+ J := {
    toEquiv := E.toEquiv
    map_add' := fun x y ↦ E.map_add' x y }
  exact ea.toIntLinearEquiv

theorem quotientEquiv_mk (hT : Surjective T) (x : LinearMap.ker p) :
    quotientEquiv T N p hN he a hker hT (Submodule.Quotient.mk x) = liftMap T N p hN he x := by
  change (liftMap T N p hN he).quotKerEquivOfSurjective
    (liftMap_surjective T N p hN he hT)
    (Submodule.quotEquivOfEq _ _ (liftMap_kernel T N p hN he a hker).symm
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem quotientEquiv_trace (hT : Surjective T) (x : LinearMap.ker p) :
    N (quotientEquiv T N p hN he a hker hT (Submodule.Quotient.mk x)) = T x := by
  rw [quotientEquiv_mk, liftMap_spec]

end Wikipedia.HopfProblem.DegreeCollapse.ExactKernelQuotient
