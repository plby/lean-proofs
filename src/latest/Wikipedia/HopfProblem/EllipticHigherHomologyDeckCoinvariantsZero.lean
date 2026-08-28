import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariants
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesLowDegrees

/-!
# The actual degree-zero deck-coinvariant comparison

The period torus and elliptic surface are path connected.  Naturality
of the actual integral augmentation proves that the covering map is
bijective on zeroth homology and that the actual deck difference is
zero there.  The genuine descended covering map therefore gives an
integral linear equivalence on the literal degree-zero coinvariants.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual period cover preserves the injective integral augmentation. -/
theorem periodCover_h0_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 0) := by
  intro a b hab
  apply (connectedHomologyZeroEquiv p.val.Torus).injective
  have h := congrArg
    (connectedHomologyZeroEquiv (Surface j p j.twist (mainTwist_admissible j))) hab
  exact (connectedHomologyZeroEquiv_natural
    (periodCover j p j.twist (mainTwist_admissible j)) a).symm.trans
      (h.trans (connectedHomologyZeroEquiv_natural
        (periodCover j p j.twist (mainTwist_admissible j)) b))

/-- The genuine period covering induces a degree-zero integral isomorphism. -/
theorem periodCover_h0_bijective (j : Kind) (p : FixedPeriod j) :
    Function.Bijective (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 0) :=
  ⟨periodCover_h0_injective j p, surfacePeriodCover_h0_surjective j p⟩

/-- The inverse deck generator is the identity on actual zeroth homology. -/
theorem periodDeckDifference_zero (j : Kind) (p : FixedPeriod j) :
    periodDeckDifference j p 0 = 0 := by
  ext a
  rw [periodDeckDifference_apply]
  apply sub_eq_zero.mpr
  apply (connectedHomologyZeroEquiv p.val.Torus).injective
  exact (connectedHomologyZeroEquiv_natural
    ((periodAffineHomeomorph j p).symm : C(p.val.Torus, p.val.Torus)) a).symm

/-- Injectivity is proved for the literal quotient map, using actual representatives. -/
theorem periodCoverFromDeckCoinvariants_h0_injective (j : Kind) (p : FixedPeriod j) :
    Function.Injective (periodCoverFromDeckCoinvariants j p 0) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (LinearMap.range (periodDeckDifference j p 0)).mkQ_surjective a
  obtain ⟨b, rfl⟩ := (LinearMap.range (periodDeckDifference j p 0)).mkQ_surjective b
  apply congrArg Submodule.Quotient.mk
  apply periodCover_h0_injective j p
  exact hab

theorem periodCoverFromDeckCoinvariants_h0_surjective (j : Kind) (p : FixedPeriod j) :
    Function.Surjective (periodCoverFromDeckCoinvariants j p 0) := by
  intro a
  obtain ⟨b, hb⟩ := surfacePeriodCover_h0_surjective j p a
  exact ⟨Submodule.Quotient.mk b, hb⟩

theorem periodCoverFromDeckCoinvariants_h0_bijective (j : Kind) (p : FixedPeriod j) :
    Function.Bijective (periodCoverFromDeckCoinvariants j p 0) :=
  ⟨periodCoverFromDeckCoinvariants_h0_injective j p,
    periodCoverFromDeckCoinvariants_h0_surjective j p⟩

/-- The actual descended degree-zero covering map, equipped with its proved inverse. -/
def periodCoverFromDeckCoinvariantsH0Equiv (j : Kind) (p : FixedPeriod j) :
    PeriodDeckCoinvariants j p 0 ≃ₗ[ℤ]
      SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 0 :=
  LinearEquiv.ofBijective (periodCoverFromDeckCoinvariants j p 0)
    (periodCoverFromDeckCoinvariants_h0_bijective j p)

@[simp] theorem periodCoverFromDeckCoinvariantsH0Equiv_apply
    (j : Kind) (p : FixedPeriod j) (a : PeriodDeckCoinvariants j p 0) :
    periodCoverFromDeckCoinvariantsH0Equiv j p a =
      periodCoverFromDeckCoinvariants j p 0 a := rfl

@[simp] theorem periodCoverFromDeckCoinvariantsH0Equiv_mk
    (j : Kind) (p : FixedPeriod j) (a : SingularHomology p.val.Torus 0) :
    periodCoverFromDeckCoinvariantsH0Equiv j p (Submodule.Quotient.mk a) =
      singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 0 a := rfl

@[simp] theorem periodCoverFromDeckCoinvariantsH0Equiv_symm_apply_map
    (j : Kind) (p : FixedPeriod j) (a : SingularHomology p.val.Torus 0) :
    (periodCoverFromDeckCoinvariantsH0Equiv j p).symm
        (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 0 a) =
      Submodule.Quotient.mk a :=
  (periodCoverFromDeckCoinvariantsH0Equiv j p).symm_apply_apply (Submodule.Quotient.mk a)

theorem periodCover_h0_ker_eq_deckDifference_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.ker (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 0) =
      LinearMap.range (periodDeckDifference j p 0) := by
  rw [LinearMap.ker_eq_bot.mpr (periodCover_h0_injective j p), periodDeckDifference_zero,
    LinearMap.range_zero]

theorem periodCoverFromDeckCoinvariants_h0_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 0)).toAddSubgroup.index = 1 := by
  rw [LinearMap.range_eq_top.mpr (periodCoverFromDeckCoinvariants_h0_surjective j p)]
  simp

/-- The positive augmentation coordinate on actual degree-zero deck coinvariants. -/
def periodDeckCoinvariantsH0Equiv (j : Kind) (p : FixedPeriod j) :
    PeriodDeckCoinvariants j p 0 ≃ₗ[ℤ] ℤ :=
  (periodCoverFromDeckCoinvariantsH0Equiv j p).trans
    (connectedHomologyZeroEquiv (Surface j p j.twist (mainTwist_admissible j)))

@[simp] theorem periodDeckCoinvariantsH0Equiv_mk (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology p.val.Torus 0) :
    periodDeckCoinvariantsH0Equiv j p (Submodule.Quotient.mk a) =
      connectedHomologyZeroEquiv p.val.Torus a :=
  connectedHomologyZeroEquiv_natural (periodCover j p j.twist (mainTwist_admissible j)) a

@[simp] theorem periodDeckCoinvariantsH0Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 0) :
    periodDeckCoinvariantsH0Equiv j p
        (Submodule.Quotient.mk (singularHomologyMap (fibreIntoPeriodTorus j p) 0 a)) =
      torusH0Coordinates a := by
  rw [periodDeckCoinvariantsH0Equiv_mk]
  exact connectedHomologyZeroEquiv_natural (fibreIntoPeriodTorus j p) a

end Wikipedia.HopfProblem.Elliptic.HigherHomology
