import Wikipedia.HopfProblem.SphereHomologyCoefficientsAlgebra

/-!
# The precise integral-lifting obstruction for a mod-two kernel

An integral lift of a mod-two kernel class has image twice some class.
That half-image is determined only modulo the integral image and the
two-torsion of the target. Its class in that quotient vanishes exactly
when the original mod-two class lifts to the integral kernel.

In particular, neither integral nullity nor absence of target torsion is
inferred from mod-two nullity. These are algebraic coefficient comparisons,
not a geometric proof that a quadratic form vanishes on the full kernel.
-/

noncomputable section

namespace NoExoticSixSphere.CoefficientKernelLifting

open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] Submodule.Quotient.module

variable {A B V : Type} [AddCommGroup A] [Module ℤ A]
  [AddCommGroup B] [Module ℤ B] [AddCommGroup V] [Module ℤ V]

theorem mem_twice_iff (a : A) :
    a ∈ scalarImage 2 A ↔ ∃ b : A, (2 : ℤ) • b = a := by
  rfl

variable (R : A →ₗ[ℤ] V) (hR : LinearMap.ker R = scalarImage 2 A)

include hR in
theorem reduction_twice (a : A) : R ((2 : ℤ) • a) = 0 := by
  have ha : (2 : ℤ) • a ∈ scalarImage 2 A := (mem_twice_iff _).mpr ⟨a, rfl⟩
  rw [← hR] at ha
  exact ha

include hR in
theorem same_reduction_iff (a a' : A) :
    R a = R a' ↔ ∃ t : A, (2 : ℤ) • t = a - a' := by
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, hR, mem_twice_iff]

variable (f : A →ₗ[ℤ] B)

/-- The half-image ambiguity includes genuine target two-torsion. -/
def halfIndeterminacy : Submodule ℤ B :=
  LinearMap.range f ⊔ LinearMap.ker ((2 : ℤ) • (LinearMap.id : B →ₗ[ℤ] B))

theorem mem_halfIndeterminacy_iff (b : B) :
    b ∈ halfIndeterminacy f ↔
      ∃ a : A, ∃ t : B, (2 : ℤ) • t = 0 ∧ f a + t = b := by
  simp only [halfIndeterminacy, Submodule.mem_sup, LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, t, ht, hb⟩
    exact ⟨a, t, ht, hb⟩
  · rintro ⟨a, t, ht, hb⟩
    exact ⟨f a, ⟨a, rfl⟩, t, ht, hb⟩

include hR in
theorem integral_kernel_lift_iff (a : A) :
    (∃ k : A, f k = 0 ∧ R k = R a) ↔
      ∃ t : A, (2 : ℤ) • f t = f a := by
  constructor
  · rintro ⟨k, hk, hred⟩
    obtain ⟨t, ht⟩ := (same_reduction_iff R hR a k).mp hred.symm
    refine ⟨t, ?_⟩
    rw [← map_zsmul, ht, map_sub, hk, sub_zero]
  · rintro ⟨t, ht⟩
    refine ⟨a - (2 : ℤ) • t, ?_, ?_⟩
    · rw [map_sub, map_zsmul, ht, sub_self]
    · rw [map_sub, reduction_twice R hR, sub_zero]

include hR in
theorem integral_kernel_lift_iff_half_mem (a : A) (b : B)
    (hab : f a = (2 : ℤ) • b) :
    (∃ k : A, f k = 0 ∧ R k = R a) ↔ b ∈ halfIndeterminacy f := by
  rw [integral_kernel_lift_iff R hR f, mem_halfIndeterminacy_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, b - f t, ?_, by abel⟩
    rw [zsmul_sub, ht, hab, sub_self]
  · rintro ⟨t, z, hz, hb⟩
    refine ⟨t, ?_⟩
    rw [hab, ← hb, zsmul_add, hz, add_zero]

include hR in
theorem half_class_eq (a a' : A) (b b' : B)
    (hred : R a = R a') (hab : f a = (2 : ℤ) • b)
    (hab' : f a' = (2 : ℤ) • b') :
    (Submodule.Quotient.mk b : B ⧸ halfIndeterminacy f) = Submodule.Quotient.mk b' := by
  apply (Submodule.Quotient.eq (halfIndeterminacy f)).mpr
  obtain ⟨t, ht⟩ := (same_reduction_iff R hR a a').mp hred
  apply (mem_halfIndeterminacy_iff f _).mpr
  refine ⟨t, b - b' - f t, ?_, by abel⟩
  rw [zsmul_sub, zsmul_sub, ← hab, ← hab', ← map_zsmul, ht, map_sub, sub_self]

include hR in
theorem half_class_zero_iff (a : A) (b : B) (hab : f a = (2 : ℤ) • b) :
    (Submodule.Quotient.mk b : B ⧸ halfIndeterminacy f) = 0 ↔
      ∃ k : A, f k = 0 ∧ R k = R a := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact (integral_kernel_lift_iff_half_mem R hR f a b hab).symm

variable {W : Type} [AddCommGroup W] [Module ℤ W]
  (S : B →ₗ[ℤ] W) (hS : LinearMap.ker S = scalarImage 2 B)
  (g : V →ₗ[ℤ] W) (hcomm : ∀ a, g (R a) = S (f a))
  (honto : Function.Surjective R)

include hS hcomm honto in
theorem mod_kernel_iff_has_half (v : V) :
    g v = 0 ↔ ∃ a : A, ∃ b : B, R a = v ∧ f a = (2 : ℤ) • b := by
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := honto v
    have hfa : f a ∈ LinearMap.ker S := by
      change S (f a) = 0
      rw [← hcomm, ha, hv]
    rw [hS, mem_twice_iff] at hfa
    obtain ⟨b, hb⟩ := hfa
    exact ⟨a, b, ha, hb.symm⟩
  · rintro ⟨a, b, rfl, hab⟩
    rw [hcomm, hab, reduction_twice S hS]

end NoExoticSixSphere.CoefficientKernelLifting
