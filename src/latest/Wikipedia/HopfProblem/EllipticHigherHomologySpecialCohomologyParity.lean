import Wikipedia.HopfProblem.EllipticHigherHomologySpecialCohomologyParityPeriods
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCentralCoordinates
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingDescent

/-!
# The literal order-four parity subgroup in Appendix A.4

The genuine positive delta sweep makes the original covering shear even.
Combining this geometric fact with the actual marked covering matrix and
the actual period evaluations gives exactly the subgroup
`{a (γ ∪ η₂) + b q | a ≡ b mod 2}`.  In particular `q` does not descend,
whereas `2q` does.  Neither the subgroup nor the obstruction is inferred
from a rank or an index alone.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyParity

open SingularCohomologyFree PeriodTorusCohomology SpecialPeriods.EllipticFilling
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open SpecialPeriods.Threefold.Homology.DeltaSweep

/-- The genuine order-four dual-covering shear is even in the unchanged marking. -/
theorem special_cover_shear_four_even :
    (2 : ℤ) ∣ periodCoverDeckDualH2Shear .four (specialLocalData .four).centralPeriod := by
  rw [special_cover_shear_eq_sourceShearTwo]
  exact two_dvd_sourceShearTwo_four

/-- Exact descent of the source combination through the original order-four covering. -/
theorem sourceCombination_four_mem_range_iff (a b : ℤ) :
    sourceCombination .four (specialLocalData .four).centralPeriod a b ∈
        LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants .four 2) ↔
      (2 : ℤ) ∣ a - b := by
  rw [periodCoverCohomologyToInvariants_h2_mem_range, sourceCombination_four_coordinates,
    special_cover_shear_eq_sourceShearTwo]
  change (2 : ℤ) ∣ -a - 3 * b - sourceShearTwo .four * b ↔ (2 : ℤ) ∣ a - b
  rw [dvd_sub_left (dvd_mul_of_dvd_left two_dvd_sourceShearTwo_four b)]
  have h : -a - 3 * b = -(a - b) - 2 * (2 * b) := by ring
  rw [h, dvd_sub_left (dvd_mul_right 2 (2 * b)), dvd_neg]

/-- The literal congruence from Appendix A.4, for actual invariant cohomology classes. -/
theorem sourceCombination_four_mem_range_iff_modEq (a b : ℤ) :
    sourceCombination .four (specialLocalData .four).centralPeriod a b ∈
        LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants .four 2) ↔
      Int.ModEq 2 a b := by
  rw [sourceCombination_four_mem_range_iff, Int.modEq_iff_dvd, dvd_sub_comm]

/-- The image inside all genuine deck invariants is precisely the displayed parity subgroup. -/
theorem specialCentralCover_four_invariant_range (c :
    periodCohomologyInvariants .four (specialLocalData .four).centralPeriod
      Kind.four.twist (mainTwist_admissible .four) 2) :
    c ∈ LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants .four 2) ↔
      ∃ a b : ℤ, c = sourceCombination .four (specialLocalData .four).centralPeriod a b ∧
        Int.ModEq 2 a b := by
  obtain ⟨a, b, rfl⟩ := sourceCombination_surjective .four
    (specialLocalData .four).centralPeriod c
  constructor
  · intro h
    exact ⟨a, b, rfl, (sourceCombination_four_mem_range_iff_modEq a b).mp h⟩
  · rintro ⟨a', b', h, hab⟩
    rw [h]
    exact (sourceCombination_four_mem_range_iff_modEq a' b').mpr hab

/-- Descent means an equality under the original cochain-induced covering pullback. -/
theorem sourceCombination_four_descends_iff (a b : ℤ) :
    (∃ c : SingularCohomology (SpecialCentralSurface .four) 2,
      singularCohomologyPullback (specialCentralPeriodCover .four) 2 c =
        a • gammaEtaClass .four (specialLocalData .four).centralPeriod.val +
          b • etaClass (specialLocalData .four).centralPeriod.val) ↔
      Int.ModEq 2 a b := by
  rw [← sourceCombination_four_mem_range_iff_modEq]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, congrArg Subtype.val hc⟩

/-- The literal native pullback image, expressed using the two original source classes. -/
theorem specialCentralCover_four_range (c :
    SingularCohomology (SpecialCentralPeriodTorus .four) 2) :
    c ∈ LinearMap.range (singularCohomologyPullback (specialCentralPeriodCover .four) 2) ↔
      ∃ a b : ℤ,
        c = a • gammaEtaClass .four (specialLocalData .four).centralPeriod.val +
          b • etaClass (specialLocalData .four).centralPeriod.val ∧ Int.ModEq 2 a b := by
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨a, b, h, hab⟩ := (specialCentralCover_four_invariant_range
      (specialCentralPeriodCoverCohomologyToInvariants .four 2 d)).mp ⟨d, rfl⟩
    exact ⟨a, b, congrArg Subtype.val h, hab⟩
  · rintro ⟨a, b, rfl, hab⟩
    exact (sourceCombination_four_descends_iff a b).mpr hab

/-- The same literal parity subgroup is the image from the entire genuine elliptic filling. -/
theorem sourceCombination_four_filling_mem_range_iff (a b : ℤ) :
    sourceCombination .four (specialLocalData .four).centralPeriod a b ∈
        LinearMap.range (specialPeriodTorusIntoFillingCohomologyToInvariants .four 2) ↔
      Int.ModEq 2 a b := by
  rw [specialPeriodTorusIntoFillingCohomologyToInvariants_range]
  exact sourceCombination_four_mem_range_iff_modEq a b

/-- The distinguished `q = η` is not in the actual order-four covering pullback image. -/
theorem etaClass_four_not_mem_range :
    etaClass (specialLocalData .four).centralPeriod.val ∉
      LinearMap.range (singularCohomologyPullback (specialCentralPeriodCover .four) 2) := by
  have h := sourceCombination_four_descends_iff 0 1
  simpa using h.not.mpr (by decide)

/-- The other primitive invariant basis vector also fails to descend through this cover. -/
theorem gammaEtaClass_four_not_mem_range :
    gammaEtaClass .four (specialLocalData .four).centralPeriod.val ∉
      LinearMap.range (singularCohomologyPullback (specialCentralPeriodCover .four) 2) := by
  have h := sourceCombination_four_descends_iff 1 0
  simpa using h.not.mpr (by decide)

/-- Necessity as well as sufficiency of the factor two, for every integral multiple of `q`. -/
theorem etaClass_four_multiple_descends_iff (n : ℤ) :
    (∃ c : SingularCohomology (SpecialCentralSurface .four) 2,
      singularCohomologyPullback (specialCentralPeriodCover .four) 2 c =
        n • etaClass (specialLocalData .four).centralPeriod.val) ↔ (2 : ℤ) ∣ n := by
  have h := sourceCombination_four_descends_iff 0 n
  simpa [Int.modEq_iff_dvd] using h

/-- The already constructed class is the unique native descent of twice the original `q`. -/
theorem etaClass_four_twice_unique_descent :
    ∃! c : SingularCohomology (SpecialCentralSurface .four) 2,
      singularCohomologyPullback (specialCentralPeriodCover .four) 2 c =
        (2 : ℤ) • etaClass (specialLocalData .four).centralPeriod.val :=
  existsUnique_ellipticEtaClass .four (specialLocalData .four).centralPeriod

/-- The actual residue is generated by `q`, with its original positive `uw` normalization. -/
theorem specialCentralCover_four_cokernel_eta :
    specialCentralPeriodCoverInvariantCohomologyH2CokernelEquivZMod .four
      (Submodule.Quotient.mk
        (etaInvariantClass .four (specialLocalData .four).centralPeriod Kind.four.twist
          (mainTwist_admissible .four))) = (1 : ZMod 2) := by
  rw [specialCentralPeriodCoverInvariantCohomologyH2CokernelEquivZMod_apply_mk,
    etaInvariantClass_coordinates]
  have hs : ((periodCoverDeckDualH2Shear .four
      (specialLocalData .four).centralPeriod : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr special_cover_shear_four_even
  change ((-3 - periodCoverDeckDualH2Shear .four
    (specialLocalData .four).centralPeriod * 1 : ℤ) : ZMod 2) = 1
  rw [mul_one, Int.cast_sub, hs, sub_zero]
  decide

/-- Every class of the actual covering cokernel is an integer multiple of the original `q`. -/
theorem specialCentralCover_four_cokernel_generated_eta
    (c : SpecialCentralPeriodCoverInvariantCohomologyCokernel .four 2) :
    ∃ n : ℤ, n • (Submodule.Quotient.mk
      (etaInvariantClass .four (specialLocalData .four).centralPeriod Kind.four.twist
        (mainTwist_admissible .four)) :
      SpecialCentralPeriodCoverInvariantCohomologyCokernel .four 2) = c := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective
    (specialCentralPeriodCoverInvariantCohomologyH2CokernelEquivZMod .four c)
  refine ⟨n, (specialCentralPeriodCoverInvariantCohomologyH2CokernelEquivZMod .four).injective ?_⟩
  rw [map_zsmul, specialCentralCover_four_cokernel_eta]
  change n • (1 : ZMod 2) = _
  rw [zsmul_one]
  exact hn

/-- That actual cokernel generator is nonzero, not just a formally named residue. -/
theorem specialCentralCover_four_cokernel_eta_ne_zero :
    (Submodule.Quotient.mk
      (etaInvariantClass .four (specialLocalData .four).centralPeriod Kind.four.twist
        (mainTwist_admissible .four)) :
      SpecialCentralPeriodCoverInvariantCohomologyCokernel .four 2) ≠ 0 := by
  intro h
  have he := specialCentralCover_four_cokernel_eta
  rw [h, map_zero] at he
  exact (by decide : (0 : ZMod 2) ≠ 1) he

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyParity
