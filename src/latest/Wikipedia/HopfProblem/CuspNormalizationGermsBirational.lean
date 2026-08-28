import Wikipedia.HopfProblem.CuspNormalizationGermsIntegral
import Wikipedia.HopfProblem.CuspNormalizationGermsSeparators
import Wikipedia.HopfProblem.CuspNormalizationGermsFractions

/-!
# Total fractions of actual singular analytic function germs

Coordinate cofactors in the ambient analytic germ ring separate the
branches.  Thus the genuine total fraction ring of the singular
function-germ ring is the product of the fraction fields of its actual
analytic branch-germ rings.  Both the original restriction map and actual
fractions have the expected coordinatewise formulas.

Combined with `restrictionToBranches_finite` this proves a finite integral
birational extension.  It does not identify the integral closure without
an additional proof of integral closedness for the analytic branch rings.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

private theorem mem_nonZeroDivisors_equiv_iff {R S : Type*}
    [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    x ∈ nonZeroDivisors R ↔ e x ∈ nonZeroDivisors S := by
  constructor
  · intro hx
    rw [← MulEquivClass.map_nonZeroDivisors e]
    exact Submonoid.mem_map.mpr ⟨x, hx, rfl⟩
  · exact mem_nonZeroDivisors_of_injective e.injective

/-- A singular analytic function germ is a non-zero-divisor exactly
when its actual restriction to every branch is a nonzero germ. -/
theorem restricted_mem_nonZeroDivisors_iff (s : Finset (Fin 3))
    (φ : RestrictedAnalyticGerm s) :
    φ ∈ nonZeroDivisors (RestrictedAnalyticGerm s) ↔
      ∀ j : s, restrictionToBranches s φ j ≠ 0 := by
  rw [mem_nonZeroDivisors_equiv_iff (restrictedEquivBranchImage s) φ]
  exact (separatingFamily s).mem_nonZeroDivisors_iff _

/-- The singular function-germ ring is reduced, proved through its
injective actual branch restrictions into domains. -/
instance restrictedAnalyticGerm_isReduced (s : Finset (Fin 3)) :
    IsReduced (RestrictedAnalyticGerm s) :=
  isReduced_of_injective (restrictionToBranches s) (restrictionToBranches_injective s)

/-- The total fraction ring of the actual restriction image, with no
unproved separator or branch-surjectivity assumptions. -/
def branchImageTotalFractionEquiv (s : Finset (Fin 3)) :
    FractionRing (BranchImage s) ≃+* (s → FractionRing BranchGerm) :=
  GermsFractions.totalFractionEquiv (BranchImage s) (separatingFamily s)
    (branchImage_coordinate_surjective s)

@[simp] theorem branchImageTotalFractionEquiv_algebraMap_apply
    (s : Finset (Fin 3)) (φ : BranchImage s) (j : s) :
    branchImageTotalFractionEquiv s (algebraMap (BranchImage s)
      (FractionRing (BranchImage s)) φ) j =
        algebraMap BranchGerm (FractionRing BranchGerm) ((φ : s → BranchGerm) j) :=
  GermsFractions.totalFractionEquiv_algebraMap_apply
    (BranchImage s) (separatingFamily s) (branchImage_coordinate_surjective s) φ j

/-- The actual singular function-germ ring has the product of the branch
fraction fields as its genuine total fraction ring. -/
def restrictedTotalFractionEquiv (s : Finset (Fin 3)) :
    FractionRing (RestrictedAnalyticGerm s) ≃+* (s → FractionRing BranchGerm) :=
  (IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing (RestrictedAnalyticGerm s))
    (L := FractionRing (BranchImage s)) (restrictedEquivBranchImage s)).trans
      (branchImageTotalFractionEquiv s)

/-- The fraction-ring comparison commutes with the actual singular
germ restriction to each analytic branch. -/
@[simp] theorem restrictedTotalFractionEquiv_algebraMap_apply
    (s : Finset (Fin 3)) (φ : RestrictedAnalyticGerm s) (j : s) :
    restrictedTotalFractionEquiv s (algebraMap (RestrictedAnalyticGerm s)
      (FractionRing (RestrictedAnalyticGerm s)) φ) j =
        algebraMap BranchGerm (FractionRing BranchGerm) (restrictionToBranches s φ j) := by
  change branchImageTotalFractionEquiv s
    (IsFractionRing.ringEquivOfRingEquiv (restrictedEquivBranchImage s)
      (algebraMap (RestrictedAnalyticGerm s) (FractionRing (RestrictedAnalyticGerm s)) φ)) j = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    branchImageTotalFractionEquiv_algebraMap_apply]
  rfl

/-- Actual ambient germs are sent to their actual coordinate-plane
restrictions in the branch fraction fields. -/
@[simp] theorem restrictedTotalFractionEquiv_ambient_apply
    (s : Finset (Fin 3)) (φ : AmbientGerm) (j : s) :
    restrictedTotalFractionEquiv s (algebraMap (RestrictedAnalyticGerm s)
      (FractionRing (RestrictedAnalyticGerm s)) ((toPlaneUnion s).rangeRestrict φ)) j =
        algebraMap BranchGerm (FractionRing BranchGerm) (toBranch j φ) := by
  rw [restrictedTotalFractionEquiv_algebraMap_apply, restrictionToBranches_rangeRestrict,
    toBranches_apply]

/-- The actual numerator and non-zero-divisor denominator restrict to
the numerator and denominator on each branch. -/
theorem restrictedTotalFractionEquiv_mk'_apply (s : Finset (Fin 3))
    (φ : RestrictedAnalyticGerm s) (d : nonZeroDivisors (RestrictedAnalyticGerm s)) (j : s) :
    restrictedTotalFractionEquiv s
      (IsLocalization.mk' (FractionRing (RestrictedAnalyticGerm s)) φ d) j =
        algebraMap BranchGerm (FractionRing BranchGerm) (restrictionToBranches s φ j) /
          algebraMap BranchGerm (FractionRing BranchGerm)
            (restrictionToBranches s d.val j) := by
  have hd : algebraMap BranchGerm (FractionRing BranchGerm)
      (restrictionToBranches s d.val j) ≠ 0 :=
    (map_ne_zero_iff (algebraMap BranchGerm (FractionRing BranchGerm))
      (IsFractionRing.injective BranchGerm (FractionRing BranchGerm))).mpr
        ((restricted_mem_nonZeroDivisors_iff s d.val).mp d.prop j)
  apply (eq_div_iff hd).mpr
  have h := congrArg (fun x : FractionRing (RestrictedAnalyticGerm s) =>
    restrictedTotalFractionEquiv s x j)
      (IsLocalization.mk'_spec (FractionRing (RestrictedAnalyticGerm s)) φ d)
  simpa only [map_mul, Pi.mul_apply, restrictedTotalFractionEquiv_algebraMap_apply] using h

end Wikipedia.HopfProblem.CuspNormalization.Germs
