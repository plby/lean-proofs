import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariantsCover
import Wikipedia.HopfProblem.EllipticHigherHomologyDeckHomology

/-!
# The actual period covering descends to its deck coinvariants

The actual covering kills the inverse deck difference.  Its induced
map on the literal quotient of actual period-torus homology therefore
exists in every degree.  It sends each actual quotient class to its
original covering image, and has exactly the same image as that map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

theorem periodCover_homology_comp_periodDeckDifference (j : Kind) (p : FixedPeriod j)
    (n : ℕ) :
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n).comp
      (periodDeckDifference j p n) = 0 :=
  periodCover_homology_comp_affineDifference j p j.twist (mainTwist_admissible j) n

theorem periodCover_homology_periodDeckDifference (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology p.val.Torus n) :
    singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n
      (periodDeckDifference j p n a) = 0 :=
  DFunLike.congr_fun (periodCover_homology_comp_periodDeckDifference j p n) a

theorem periodDeckDifference_range_le_periodCover_ker (j : Kind) (p : FixedPeriod j)
    (n : ℕ) :
    LinearMap.range (periodDeckDifference j p n) ≤
      LinearMap.ker
        (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n) := by
  rintro a ⟨b, rfl⟩
  exact periodCover_homology_periodDeckDifference j p n b

/-- The genuine covering map on the literal actual deck coinvariants. -/
def periodCoverFromDeckCoinvariants (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (SingularHomology p.val.Torus n ⧸ LinearMap.range (periodDeckDifference j p n)) →ₗ[ℤ]
      SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n where
  toFun := (LinearMap.range (periodDeckDifference j p n)).liftQ
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n)
    (periodDeckDifference_range_le_periodCover_ker j p n)
  map_add' a b := map_add _ a b
  map_smul' r a := by
    let f := (LinearMap.range (periodDeckDifference j p n)).liftQ
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n)
      (periodDeckDifference_range_le_periodCover_ker j p n)
    change f (r • a) =
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n).isModule.smul r (f a)
    rw [int_smul_eq_zsmul]
    exact map_zsmul f r a

/-- The literal quotient projection, with the canonical integer module on the quotient. -/
def periodDeckCoinvariantProjection (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    SingularHomology p.val.Torus n →ₗ[ℤ]
      (SingularHomology p.val.Torus n ⧸ LinearMap.range (periodDeckDifference j p n)) where
  toFun := (LinearMap.range (periodDeckDifference j p n)).mkQ
  map_add' a b := map_add _ a b
  map_smul' r a := by
    let f := (LinearMap.range (periodDeckDifference j p n)).mkQ
    change f ((SingularHomology p.val.Torus n).isModule.smul r a) = r • f a
    rw [int_smul_eq_zsmul]
    exact map_zsmul f r a

@[simp] theorem periodDeckCoinvariantProjection_apply (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology p.val.Torus n) :
    periodDeckCoinvariantProjection j p n a = Submodule.Quotient.mk a := rfl

theorem periodDeckCoinvariantProjection_surjective (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Function.Surjective (periodDeckCoinvariantProjection j p n) :=
  Submodule.Quotient.mk_surjective (LinearMap.range (periodDeckDifference j p n))

@[simp] theorem periodCoverFromDeckCoinvariants_mk (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology p.val.Torus n) :
    periodCoverFromDeckCoinvariants j p n (Submodule.Quotient.mk a) =
      singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n a := rfl

theorem periodCoverFromDeckCoinvariants_comp_mkQ (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (periodCoverFromDeckCoinvariants j p n).comp
      (periodDeckCoinvariantProjection j p n) =
      singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n := by
  ext a
  rfl

/-- Taking the actual deck quotient changes neither the covering image nor its index. -/
theorem periodCoverFromDeckCoinvariants_range (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    LinearMap.range (periodCoverFromDeckCoinvariants j p n) =
      LinearMap.range
        (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := (LinearMap.range (periodDeckDifference j p n)).mkQ_surjective b
    exact ⟨c, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Submodule.Quotient.mk b, rfl⟩

end Wikipedia.HopfProblem.Elliptic.HigherHomology
