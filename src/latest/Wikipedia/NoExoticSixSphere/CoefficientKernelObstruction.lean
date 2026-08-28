import Wikipedia.NoExoticSixSphere.CoefficientKernelLifting

/-!
# The actual additive obstruction to lifting a mod-two kernel class

The half-image quotient class is independent of all integral and half-image
choices. It gives a linear map on the mod-two kernel whose kernel is exactly
the image of the integral kernel. Its values have order dividing two.
No vanishing of the obstruction map itself is asserted.
-/

noncomputable section

namespace NoExoticSixSphere.CoefficientKernelLifting

open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] Submodule.Quotient.module

variable {A B V W : Type} [AddCommGroup A] [Module ℤ A]
  [AddCommGroup B] [Module ℤ B] [AddCommGroup V] [Module ℤ V]
  [AddCommGroup W] [Module ℤ W]
  (R : A →ₗ[ℤ] V) (hR : LinearMap.ker R = scalarImage 2 A) (f : A →ₗ[ℤ] B)
  (S : B →ₗ[ℤ] W) (hS : LinearMap.ker S = scalarImage 2 B)
  (g : V →ₗ[ℤ] W) (hcomm : ∀ a, g (R a) = S (f a))
  (honto : Function.Surjective R)

include hS hcomm honto in
theorem exists_half_pair (v : LinearMap.ker g) :
    ∃ p : A × B, R p.1 = v.val ∧ f p.1 = (2 : ℤ) • p.2 := by
  obtain ⟨a, b, ha, hb⟩ := (mod_kernel_iff_has_half R f S hS g hcomm honto v.val).mp v.property
  exact ⟨(a, b), ha, hb⟩

def halfLift (v : LinearMap.ker g) : A × B :=
  Classical.choose (exists_half_pair R f S hS g hcomm honto v)

theorem halfLift_spec (v : LinearMap.ker g) :
    R (halfLift R f S hS g hcomm honto v).1 = v.val ∧
      f (halfLift R f S hS g hcomm honto v).1 =
        (2 : ℤ) • (halfLift R f S hS g hcomm honto v).2 :=
  Classical.choose_spec (exists_half_pair R f S hS g hcomm honto v)

def obstructionValue (v : LinearMap.ker g) : B ⧸ halfIndeterminacy f :=
  Submodule.Quotient.mk (halfLift R f S hS g hcomm honto v).2

include hR in
theorem obstructionValue_eq (v : LinearMap.ker g) (a : A) (b : B)
    (ha : R a = v.val) (hb : f a = (2 : ℤ) • b) :
    obstructionValue R f S hS g hcomm honto v = Submodule.Quotient.mk b := by
  have hp := halfLift_spec R f S hS g hcomm honto v
  exact half_class_eq R hR f _ a _ b (hp.1.trans ha.symm) hp.2 hb

include hR in
theorem obstructionValue_add (u v : LinearMap.ker g) :
    obstructionValue R f S hS g hcomm honto (u + v) =
      obstructionValue R f S hS g hcomm honto u +
        obstructionValue R f S hS g hcomm honto v := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := exists_half_pair R f S hS g hcomm honto u
  obtain ⟨⟨a', b'⟩, ha', hb'⟩ := exists_half_pair R f S hS g hcomm honto v
  rw [obstructionValue_eq R hR f S hS g hcomm honto u a b ha hb,
    obstructionValue_eq R hR f S hS g hcomm honto v a' b' ha' hb']
  have hsum := obstructionValue_eq R hR f S hS g hcomm honto (u + v) (a + a') (b + b')
    (by change R (a + a') = u.val + v.val; rw [map_add, ha, ha'])
    (by rw [map_add, hb, hb', zsmul_add])
  exact hsum

/-- The obstruction defined by the given coefficient square, not a chosen substitute map. -/
def obstruction : LinearMap.ker g →ₗ[ℤ] B ⧸ halfIndeterminacy f :=
  (AddMonoidHom.mk' (obstructionValue R f S hS g hcomm honto)
    (obstructionValue_add R hR f S hS g hcomm honto)).toIntLinearMap

theorem obstruction_apply (v : LinearMap.ker g) :
    obstruction R hR f S hS g hcomm honto v =
      obstructionValue R f S hS g hcomm honto v := rfl

theorem obstruction_eq (v : LinearMap.ker g) (a : A) (b : B)
    (ha : R a = v.val) (hb : f a = (2 : ℤ) • b) :
    obstruction R hR f S hS g hcomm honto v = Submodule.Quotient.mk b :=
  obstructionValue_eq R hR f S hS g hcomm honto v a b ha hb

theorem obstruction_zero_iff (v : LinearMap.ker g) :
    obstruction R hR f S hS g hcomm honto v = 0 ↔
      ∃ a : A, f a = 0 ∧ R a = v.val := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := exists_half_pair R f S hS g hcomm honto v
  rw [obstruction_eq R hR f S hS g hcomm honto v a b ha hb,
    half_class_zero_iff R hR f a b hb, ha]

theorem obstruction_twice (v : LinearMap.ker g) :
    (2 : ℤ) • obstruction R hR f S hS g hcomm honto v = 0 := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := exists_half_pair R f S hS g hcomm honto v
  rw [obstruction_eq R hR f S hS g hcomm honto v a b ha hb, two_zsmul]
  change (halfIndeterminacy f).mkQ b + (halfIndeterminacy f).mkQ b = 0
  rw [← map_add, ← two_zsmul, ← hb]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (mem_halfIndeterminacy_iff f _).mpr ⟨a, 0, by rw [two_zsmul, add_zero], add_zero _⟩

def integralKernelReduction : LinearMap.ker f →ₗ[ℤ] LinearMap.ker g := by
  let F : LinearMap.ker f →+ LinearMap.ker g := {
    toFun a := ⟨R a, by rw [LinearMap.mem_ker, hcomm, a.property, map_zero]⟩
    map_zero' := Subtype.ext (map_zero R)
    map_add' := fun a b ↦ Subtype.ext (map_add R a.val b.val) }
  exact F.toIntLinearMap

theorem integralKernelReduction_val (a : LinearMap.ker f) :
    (integralKernelReduction R f S g hcomm a).val = R a := rfl

theorem obstruction_ker :
    LinearMap.ker (obstruction R hR f S hS g hcomm honto) =
      LinearMap.range (integralKernelReduction R f S g hcomm) := by
  ext v
  rw [LinearMap.mem_ker, obstruction_zero_iff]
  constructor
  · rintro ⟨a, ha, hv⟩
    exact ⟨⟨a, ha⟩, Subtype.ext hv⟩
  · rintro ⟨a, ha⟩
    exact ⟨a.val, a.property, congrArg Subtype.val ha⟩

end NoExoticSixSphere.CoefficientKernelLifting
