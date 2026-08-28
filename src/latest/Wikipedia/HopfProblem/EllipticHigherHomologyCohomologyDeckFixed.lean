import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariance
import Wikipedia.HopfProblem.SingularCohomologyFreeCoinvariants

/-!
# The literal affine generator detects every deck-invariant class

The cyclic group is the actual group acting on the original period torus.
Functoriality of its actual continuous maps proves that being fixed by the
generator, or by its inverse, is equivalent to being fixed by every deck
transformation.  No replacement of the action by an abstract matrix action
is made here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularCohomologyFree

@[simp] theorem surfaceDeckMap_one (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    surfaceDeckMap j p v hv 1 = ContinuousMap.id p.val.Torus := by
  let := affineAction j p v hv.1
  ext x
  exact one_smul (CyclicGroup j) x

theorem surfaceDeckMap_mul (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g h : CyclicGroup j) :
    surfaceDeckMap j p v hv (g * h) =
      (surfaceDeckMap j p v hv g).comp (surfaceDeckMap j p v hv h) := by
  let := affineAction j p v hv.1
  ext x
  exact mul_smul g h x

/-- The actual pullbacks by inverse deck transformations are inverse operators. -/
theorem surfaceDeckMap_cohomology_inv_apply (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (n : ℕ)
    (a : SingularCohomology p.val.Torus n) :
    singularCohomologyPullback (surfaceDeckMap j p v hv g⁻¹) n
      (singularCohomologyPullback (surfaceDeckMap j p v hv g) n a) = a := by
  change ((singularCohomologyPullback (surfaceDeckMap j p v hv g⁻¹) n).comp
    (singularCohomologyPullback (surfaceDeckMap j p v hv g) n)) a = a
  rw [← singularCohomologyPullback_comp, ← surfaceDeckMap_mul,
    mul_inv_cancel, surfaceDeckMap_one, singularCohomologyPullback_id]
  rfl

theorem surfaceDeckMap_cohomology_fixed_inv_iff (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (n : ℕ)
    (a : SingularCohomology p.val.Torus n) :
    singularCohomologyPullback (surfaceDeckMap j p v hv g) n a = a ↔
      singularCohomologyPullback (surfaceDeckMap j p v hv g⁻¹) n a = a := by
  constructor
  · intro ha
    calc
      _ = singularCohomologyPullback (surfaceDeckMap j p v hv g⁻¹) n
          (singularCohomologyPullback (surfaceDeckMap j p v hv g) n a) := congrArg _ ha.symm
      _ = a := surfaceDeckMap_cohomology_inv_apply j p v hv g n a
  · intro ha
    have hb := surfaceDeckMap_cohomology_inv_apply j p v hv g⁻¹ n a
    rw [inv_inv, ha] at hb
    exact hb

theorem surfaceDeckMap_cohomology_fixed_pow (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (n : ℕ)
    (a : SingularCohomology p.val.Torus n)
    (ha : singularCohomologyPullback (surfaceDeckMap j p v hv g) n a = a) (k : ℕ) :
    singularCohomologyPullback (surfaceDeckMap j p v hv (g ^ k)) n a = a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, surfaceDeckMap_mul, singularCohomologyPullback_comp,
        LinearMap.comp_apply, ih, ha]

/-- Every element of the actual cyclic deck group is a power of the distinguished generator. -/
theorem surfaceDeckGroup_eq_generator_pow (j : Kind) (g : CyclicGroup j) :
    g = CyclicAction.generator j.order ^ g.toAdd.val := by
  rw [CyclicAction.generator_pow, ZMod.natCast_zmod_val]
  rfl

/-- Fixing the literal affine generator is equivalent to the actual all-deck condition. -/
theorem mem_periodCohomologyInvariants_iff_affine (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ)
    (a : SingularCohomology p.val.Torus n) :
    a ∈ periodCohomologyInvariants j p v hv n ↔
      singularCohomologyPullback (surfaceAffineGenerator j p v) n a = a := by
  rw [mem_periodCohomologyInvariants_iff, ← surfaceDeckMap_generator j p v hv]
  constructor
  · intro ha
    exact ha _
  · intro ha g
    rw [surfaceDeckGroup_eq_generator_pow j g]
    exact surfaceDeckMap_cohomology_fixed_pow j p v hv _ n a ha _

/-- The inverse of the actual affine generator, as a continuous map. -/
def surfaceInverseAffineGenerator (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    C(p.val.Torus, p.val.Torus) :=
  ⟨(affineBiholomorph j p v).symm, (affineBiholomorph j p v).symm.continuous⟩

theorem surfaceDeckMap_inverse_generator (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    surfaceDeckMap j p v hv (CyclicAction.generator j.order)⁻¹ =
      surfaceInverseAffineGenerator j p v := by
  let := affineAction j p v hv.1
  ext x
  apply (affineBiholomorph j p v).injective
  change affineBiholomorph j p v ((CyclicAction.generator j.order)⁻¹ • x) =
    affineBiholomorph j p v ((affineBiholomorph j p v).symm x)
  rw [← affineAction_generator_smul j p v hv.1, smul_inv_smul]
  exact ((affineBiholomorph j p v).apply_symm_apply x).symm

/-- The inverse affine generator gives exactly the same actual invariant classes. -/
theorem mem_periodCohomologyInvariants_iff_inverse_affine (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ)
    (a : SingularCohomology p.val.Torus n) :
    a ∈ periodCohomologyInvariants j p v hv n ↔
      singularCohomologyPullback (surfaceInverseAffineGenerator j p v) n a = a := by
  rw [mem_periodCohomologyInvariants_iff_affine,
    ← surfaceDeckMap_generator j p v hv, ← surfaceDeckMap_inverse_generator j p v hv]
  exact surfaceDeckMap_cohomology_fixed_inv_iff j p v hv _ n a

/-- Equality of the native invariant and inverse-generator fixed submodules. -/
theorem periodCohomologyInvariants_eq_inverse_fixed (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ) :
    periodCohomologyInvariants j p v hv n =
      singularCohomologyFixed (surfaceInverseAffineGenerator j p v) n := by
  ext a
  rw [mem_periodCohomologyInvariants_iff_inverse_affine,
    mem_singularCohomologyFixed_iff]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
