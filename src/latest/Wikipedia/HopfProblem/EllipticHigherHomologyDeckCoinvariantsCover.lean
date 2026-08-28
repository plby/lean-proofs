import Wikipedia.HopfProblem.EllipticHigherHomologyRetraction

/-!
# The actual period cover annihilates deck differences

The original affine transformation is a literal deck transformation of
the original finite quotient.  The same is true of its inverse.
Functoriality then shows that the actual singular-homology covering map
kills the difference between the identity and the inverse affine map.
This statement holds for every admissible twist and every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

theorem periodCover_affine_eq (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : p.val.Torus) :
    periodCover j p v hv (affineBiholomorph j p v x) = periodCover j p v hv x := by
  let := affineAction j p v hv.1
  rw [← affineAction_generator_smul j p v hv.1 x]
  exact FiniteQuotient.project_smul (CyclicGroup j) p.val.Torus
    (CyclicAction.generator j.order) x

/-- Invariance is an equality of the actual continuous maps. -/
theorem periodCover_comp_affine (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (periodCover j p v hv).comp
      ((affineBiholomorph j p v).toHomeomorph : C(p.val.Torus, p.val.Torus)) =
      periodCover j p v hv := by
  ext x
  exact periodCover_affine_eq j p v hv x

theorem periodCover_affine_symm_eq (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : p.val.Torus) :
    periodCover j p v hv ((affineBiholomorph j p v).toHomeomorph.symm x) =
      periodCover j p v hv x := by
  have h := periodCover_affine_eq j p v hv
    ((affineBiholomorph j p v).toHomeomorph.symm x)
  change periodCover j p v hv
    ((affineBiholomorph j p v).toHomeomorph
      ((affineBiholomorph j p v).toHomeomorph.symm x)) = _ at h
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- The inverse-convention deck map is also killed before homology is taken. -/
theorem periodCover_comp_affine_symm (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (periodCover j p v hv).comp
      ((affineBiholomorph j p v).toHomeomorph.symm : C(p.val.Torus, p.val.Torus)) =
      periodCover j p v hv := by
  ext x
  exact periodCover_affine_symm_eq j p v hv x

theorem periodCover_homology_affine_symm_comp (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) :
    (singularHomologyMap (periodCover j p v hv) n).comp
      (singularHomologyMap ((affineBiholomorph j p v).toHomeomorph.symm :
        C(p.val.Torus, p.val.Torus)) n) = singularHomologyMap (periodCover j p v hv) n := by
  rw [← singularHomologyMap_comp, periodCover_comp_affine_symm]

/-- The actual covering map annihilates the literal inverse deck difference. -/
theorem periodCover_homology_comp_affineDifference (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ) :
    (singularHomologyMap (periodCover j p v hv) n).comp
      (LinearMap.id - singularHomologyMap
        ((affineBiholomorph j p v).toHomeomorph.symm : C(p.val.Torus, p.val.Torus)) n) = 0 := by
  rw [LinearMap.comp_sub, LinearMap.comp_id, periodCover_homology_affine_symm_comp, sub_self]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
