import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariants
import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariantsZero
import Wikipedia.HopfProblem.EllipticFlatTorus

/-!
# The actual elliptic deck kernel in real-period coordinates

The proved finite-cover kernels are transported through the literal
real-period homeomorphism.  The period deck convention uses the inverse
affine generator; the genuine Wang operator uses the forward generator.
Their images agree because the generator induces an actual homology
equivalence.  No monodromy matrix is supplied to this comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.EllipticFibre

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open Elliptic Elliptic.HigherHomology

/-- The forward and inverse actual Wang differences have the same image. -/
theorem wangDifference_symm_range {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) :
    LinearMap.range (wangDifference f.symm n) =
      LinearMap.range (wangDifference f n) := by
  let e := homeomorphHomologyEquiv f n
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨-e.symm b, ?_⟩
    change -e.symm b - e (-e.symm b) = b - e.symm b
    rw [map_neg, LinearEquiv.apply_symm_apply]
    abel
  · rintro ⟨b, rfl⟩
    refine ⟨-e b, ?_⟩
    change -e b - e.symm (-e b) = b - e b
    rw [map_neg, LinearEquiv.symm_apply_apply]
    abel

/-- The actual period covering kills exactly its actual inverse-deck
difference in every degree.  Above four both source submodules vanish. -/
theorem periodCover_ker_eq_deckDifference_range (j : Kind) (p : FixedPeriod j)
    (n : ℕ) :
    LinearMap.ker
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n) =
      LinearMap.range (periodDeckDifference j p n) := by
  by_cases hn : n ≤ 4
  · interval_cases n
    · exact periodCover_h0_ker_eq_deckDifference_range j p
    · exact periodCover_h1_ker_eq_deckDifference_range j p
    · exact periodCover_h2_ker_eq_deckDifference_range j p
    · exact periodCover_h3_ker_eq_deckDifference_range j p
    · exact periodCover_h4_ker_eq_deckDifference_range j p
  · have := periodTorus_homology_subsingleton_of_lt p.val (Nat.lt_of_not_ge hn)
    ext a
    rw [Subsingleton.elim a 0]
    simp only [Submodule.zero_mem]

/-- The original real-period coordinate change intertwines the actual
affine maps on native singular homology. -/
theorem periodHomologyEquiv_affine (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n
        (singularHomologyMap (flatTorusAffine j j.twist : C(RealTorus₄, RealTorus₄)) n a) =
      singularHomologyMap (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) n
        (homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n a) := by
  have h : (flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)).comp
        (flatTorusAffine j j.twist : C(RealTorus₄, RealTorus₄)) =
      (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)).comp
        (flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)) := by
    ext x
    exact flatTorusAffine_periodHomeomorph j p j.twist x
  have hh := congrArg (fun u : C(RealTorus₄, p.val.Torus) => singularHomologyMap u n) h
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hh
  exact LinearMap.congr_fun hh a

/-- Inverting the two actual homology equivalences preserves the same
real-period coordinate change. -/
theorem periodHomologyEquiv_affine_symm (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n
        (singularHomologyMap
          ((flatTorusAffine j j.twist).symm : C(RealTorus₄, RealTorus₄)) n a) =
      singularHomologyMap ((periodAffineHomeomorph j p).symm :
        C(p.val.Torus, p.val.Torus)) n
        (homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n a) := by
  let A := homeomorphHomologyEquiv (flatTorusAffine j j.twist) n
  let B := homeomorphHomologyEquiv (periodAffineHomeomorph j p) n
  let E := homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n
  have h := periodHomologyEquiv_affine j p n (A.symm a)
  change E (A (A.symm a)) = B (E (A.symm a)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  change E (A.symm a) = B.symm (E a)
  apply B.injective
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The actual inverse Wang operator becomes the literal period deck
operator, including the inverse convention and subtraction sign. -/
theorem periodHomologyEquiv_inverseWangDifference (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n
        (wangDifference (flatTorusAffine j j.twist).symm n a) =
      periodDeckDifference j p n
        (homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n a) := by
  rw [wangDifference_apply, map_sub, periodDeckDifference_apply,
    periodHomologyEquiv_affine_symm]

/-- Transport of the actual deck image is the image of the actual forward
Wang operator in the unchanged real-period homology. -/
theorem periodHomologyEquiv_mem_deckDifference_range_iff (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n a ∈
        LinearMap.range (periodDeckDifference j p n) ↔
      a ∈ LinearMap.range (wangDifference (flatTorusAffine j j.twist) n) := by
  rw [← wangDifference_symm_range (flatTorusAffine j j.twist) n]
  let E := homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨E.symm b, E.injective ?_⟩
    change homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) n
      (wangDifference (flatTorusAffine j j.twist).symm n (E.symm b)) = E a
    rw [periodHomologyEquiv_inverseWangDifference]
    change periodDeckDifference j p n (E (E.symm b)) = E a
    rw [LinearEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨b, rfl⟩
    exact ⟨E b, (periodHomologyEquiv_inverseWangDifference j p n b).symm⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.EllipticFibre
