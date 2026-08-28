import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelMap
import Wikipedia.HopfProblem.CuspCentralHomologyLowDegrees

/-!
# The actual degree-zero specialization and monodromy maps

Augmentation naturality for the actual path-connected source and central
fibre identifies the marked collapse with the identity of the integers.
Its injectivity then turns the proved geometric monodromy invariance into
the exact identity of actual degree-zero homology maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

/-- The actual collapse preserves the canonical integral augmentation. -/
theorem markedCollapse_homologyZero_augmentation
    (a : SingularHomology (ProductTorus 4) 0) :
    centralSingularH0Equiv C r hr (singularHomologyMap (markedCollapse C r hr) 0 a) =
      connectedHomologyZeroEquiv (ProductTorus 4) a :=
  centralSingularH0Equiv_natural C r hr (markedCollapse C r hr) a

/-- The original marked collapse is an isomorphism on actual degree-zero homology. -/
theorem markedCollapse_homologyZero_bijective :
    Function.Bijective (singularHomologyMap (markedCollapse C r hr) 0) := by
  constructor
  · intro a b hab
    apply (connectedHomologyZeroEquiv (ProductTorus 4)).injective
    rw [← markedCollapse_homologyZero_augmentation C r hr a,
      ← markedCollapse_homologyZero_augmentation C r hr b, hab]
  · intro b
    obtain ⟨a, ha⟩ := (connectedHomologyZeroEquiv (ProductTorus 4)).surjective
      (centralSingularH0Equiv C r hr b)
    refine ⟨a, ?_⟩
    apply (centralSingularH0Equiv C r hr).injective
    rw [markedCollapse_homologyZero_augmentation]
    exact ha

/-- The equivalence uses the actual induced collapse map as its forward map. -/
def markedCollapseHomologyZeroEquiv :
    SingularHomology (ProductTorus 4) 0 ≃ₗ[ℤ]
      SingularHomology (QuotientCentralFibre C r) 0 :=
  LinearEquiv.ofBijective (singularHomologyMap (markedCollapse C r hr) 0)
    (markedCollapse_homologyZero_bijective C r hr)

@[simp] theorem markedCollapseHomologyZeroEquiv_apply
    (a : SingularHomology (ProductTorus 4) 0) :
    markedCollapseHomologyZeroEquiv C r hr a =
      singularHomologyMap (markedCollapse C r hr) 0 a := rfl

theorem markedCollapse_homologyZero_kernel :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 0) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyZero_bijective C r hr).injective

theorem markedCollapse_homologyZero_eq_zero_iff
    (a : SingularHomology (ProductTorus 4) 0) :
    singularHomologyMap (markedCollapse C r hr) 0 a = 0 ↔ a = 0 :=
  (markedCollapseHomologyZeroEquiv C r hr).map_eq_zero_iff

include C r hr in
/-- Injectivity of the actual specialization turns its geometric invariance
into the exact identity map in degree zero. -/
theorem markedMonodromy_homologyZero :
    singularHomologyMap (torusMatrixMap M₀) 0 = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply (markedCollapse_homologyZero_bijective C r hr).injective
  exact markedCollapse_homology_invariant C r hr 0 a

include C r hr in
theorem markedMonodromy_homologyZero_variation_zero :
    singularHomologyMap (torusMatrixMap M₀) 0 - LinearMap.id = 0 := by
  rw [markedMonodromy_homologyZero C r hr, sub_self]

include C r hr in
theorem markedMonodromy_homologyZero_variation_range :
    LinearMap.range (singularHomologyMap (torusMatrixMap M₀) 0 - LinearMap.id) = ⊥ := by
  rw [markedMonodromy_homologyZero_variation_zero C r hr, LinearMap.range_zero]

/-- The actual specialization kernel equals the actual variation image also in degree zero. -/
theorem markedCollapse_homologyZero_kernel_eq_variation :
    LinearMap.ker (singularHomologyMap (markedCollapse C r hr) 0) =
      LinearMap.range (singularHomologyMap (torusMatrixMap M₀) 0 - LinearMap.id) := by
  rw [markedCollapse_homologyZero_kernel, markedMonodromy_homologyZero_variation_range C r hr]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
