import Wikipedia.HopfProblem.SingularCohomologyFreeCoinvariants

/-!
# Native cohomology pullback from a homological coinvariant quotient

The actual singular-cochain evaluation equivalence transports the standard
integral dual-map theorems to native cohomology. A surjective pushforward
gives an injective pullback. If its actual kernel is the image of an actual
monodromy map minus identity, the pullback image is precisely the literal
fixed submodule for the actual cochain pullback.

Projectivity is explicit here; the geometric cusp application supplies it
from the already proved freeness of all actual homology groups.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open SingularMayerVietoris SingularCohomologyFree

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

section TargetProjective

variable [∀ k, Module.Projective ℤ (SingularHomology Y k)]

/-- A surjective actual homology map makes the native cohomology pullback injective. -/
theorem nativePullback_injective_of_homology_surjective
    (c : C(X, Y)) (n : ℕ) (hs : Function.Surjective (singularHomologyMap c n)) :
    Function.Injective (singularCohomologyPullback c n) := by
  intro a b hab
  apply (singularEvaluationEquiv Y n).injective
  apply LinearMap.dualMap_injective_of_surjective (f := singularHomologyMap c n) hs
  ext x
  change singularEvaluation Y n a (singularHomologyMap c n x) =
    singularEvaluation Y n b (singularHomologyMap c n x)
  rw [← singularEvaluation_naturality, ← singularEvaluation_naturality, hab]

end TargetProjective

section SourceProjective

variable [∀ k, Module.Projective ℤ (SingularHomology X k)]

/-- Literal native fixed classes annihilate the actual difference `H(mon) - id`. -/
theorem nativeFixed_iff_annihilator (mon : C(X, X)) (n : ℕ)
    (a : SingularCohomology X n) :
    a ∈ singularCohomologyFixed mon n ↔ singularEvaluationEquiv X n a ∈
      (LinearMap.range (singularHomologyMap mon n - LinearMap.id)).dualAnnihilator := by
  rw [mem_singularCohomologyFixed_iff, Submodule.mem_dualAnnihilator]
  constructor
  · intro ha b hb
    obtain ⟨x, rfl⟩ := hb
    change singularEvaluation X n a (singularHomologyMap mon n x - x) = 0
    rw [map_sub, ← singularEvaluation_naturality, ha, sub_self]
  · intro ha
    apply (singularEvaluationEquiv X n).injective
    ext b
    have hb := ha (singularHomologyMap mon n b - b) ⟨b, rfl⟩
    change singularEvaluation X n a (singularHomologyMap mon n b - b) = 0 at hb
    rw [map_sub, sub_eq_zero] at hb
    exact (singularEvaluation_naturality mon n a b).trans hb

end SourceProjective

section BothProjective

variable [∀ k, Module.Projective ℤ (SingularHomology X k)]
  [∀ k, Module.Projective ℤ (SingularHomology Y k)]

/-- The actual pullback image is detected by annihilation of the actual pushforward kernel. -/
theorem nativePullback_mem_range_iff_annihilator
    (c : C(X, Y)) (n : ℕ) (hs : Function.Surjective (singularHomologyMap c n))
    (a : SingularCohomology X n) :
    a ∈ LinearMap.range (singularCohomologyPullback c n) ↔
      singularEvaluationEquiv X n a ∈
        (LinearMap.ker (singularHomologyMap c n)).dualAnnihilator := by
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective
    (singularHomologyMap c n) hs]
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨singularEvaluationEquiv Y n b, ?_⟩
    ext x
    exact (singularEvaluationEquiv_naturality c n b x).symm
  · rintro ⟨φ, hφ⟩
    refine ⟨(singularEvaluationEquiv Y n).symm φ, ?_⟩
    apply (singularEvaluationEquiv X n).injective
    ext x
    rw [singularEvaluationEquiv_naturality, LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun hφ x

/-- A proved homological coinvariant quotient has precisely the actual native fixed classes
as the image of its actual cohomological pullback. -/
theorem nativePullback_range_eq_fixed (c : C(X, Y)) (mon : C(X, X)) (n : ℕ)
    (hs : Function.Surjective (singularHomologyMap c n))
    (hk : LinearMap.ker (singularHomologyMap c n) =
      LinearMap.range (singularHomologyMap mon n - LinearMap.id)) :
    LinearMap.range (singularCohomologyPullback c n) = singularCohomologyFixed mon n := by
  ext a
  rw [nativePullback_mem_range_iff_annihilator c n hs a, hk,
    ← nativeFixed_iff_annihilator mon n a]

/-- Membership uses the literal fixed-point equation for the actual native pullback. -/
theorem nativePullback_mem_range_iff_fixed (c : C(X, Y)) (mon : C(X, X)) (n : ℕ)
    (hs : Function.Surjective (singularHomologyMap c n))
    (hk : LinearMap.ker (singularHomologyMap c n) =
      LinearMap.range (singularHomologyMap mon n - LinearMap.id))
    (a : SingularCohomology X n) :
    a ∈ LinearMap.range (singularCohomologyPullback c n) ↔
      singularCohomologyPullback mon n a = a := by
  rw [nativePullback_range_eq_fixed c mon n hs hk, mem_singularCohomologyFixed_iff]

end BothProjective

end Wikipedia.HopfProblem.CuspCentralCohomology
