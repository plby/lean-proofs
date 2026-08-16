import Wikipedia.GreenTao.Sieve.CFZCanonicalCarryCellDiscrepancy
import Wikipedia.GreenTao.Sieve.SelectedCFZAffineLocalProduct

/-!
# Fixed-family Euler products on canonical CFZ carry cells

The canonical carry vector is chosen before the paired divisor variables.
On one of its fibers, every cyclic CFZ value is represented by one fixed
carry-adjusted affine family.  This file defines its residue model, proves
periodicity and the exact CRT Euler product, and inserts it into the
canonical-cell discrepancy theorem.

Unlike the quotient-block Euler average, the affine family in this file
does not depend on the divisor LCM.  This is the structural feature needed
to compare the coordinatewise-truncated divisor expansion with one
unrestricted prime-support Euler series.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A fixed family attached to one canonical carry vector -/

/-- Carry-adjusted affine family attached directly to a complete carry
vector, rather than to a divisor-dependent quotient block. -/
def cfzCarryAdjustedFamilyAtVector
    {κ : Type*} {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ) : AffineForm (CFZVariable k) ℤ :=
  cfzCarryAdjustedAffineForm N W b (forms q) (carry q)

/-- Natural representative modulo `D` of the fixed carry-adjusted affine
family. -/
def cfzCarryAdjustedResidueValueAtVector
    {κ : Type*} {k D : ℕ} [NeZero D]
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ)
    (x : CFZVariable k → ZMod D) : ℕ :=
  affineFormResidueValue
    (cfzCarryAdjustedFamilyAtVector N W b forms carry q) x

@[simp]
theorem natCast_cfzCarryAdjustedResidueValueAtVector
    {κ : Type*} {k D : ℕ} [NeZero D]
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ)
    (x : CFZVariable k → ZMod D) :
    (cfzCarryAdjustedResidueValueAtVector
        (D := D) N W b forms carry q x : ZMod D) =
      (cfzCarryAdjustedFamilyAtVector
        N W b forms carry q).evalZMod D x := by
  exact ZMod.natCast_zmod_val _

/-! ## Periodicity -/

/-- Coordinatewise congruent natural vectors have identical fixed-family
residue values. -/
theorem cfzCarryAdjustedResidueValueAtVector_eq_of_coordinate_modEq
    {κ : Type*} {k D : ℕ} [NeZero D]
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ)
    (x y : CFZVariable k → ℕ)
    (hxy : ∀ v, x v % D = y v % D) :
    cfzCarryAdjustedResidueValueAtVector
        (D := D) N W b forms carry q
        (fun v => (x v : ZMod D)) =
      cfzCarryAdjustedResidueValueAtVector
        (D := D) N W b forms carry q
        (fun v => (y v : ZMod D)) := by
  unfold cfzCarryAdjustedResidueValueAtVector
    affineFormResidueValue
  congr 2
  funext v
  exact
    (ZMod.natCast_eq_natCast_iff' (x v) (y v) D).2
      (hxy v)

/-- The paired divisibility indicator of a fixed carry-adjusted family is
genuinely periodic modulo the paired divisor LCM. -/
theorem
    periodicInEachCoordinate_pairedDivisibilityIndicator_cfzCarryVector
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    PeriodicInEachCoordinate
      (fun x : CFZVariable k → ℕ =>
        pairedDivisibilityIndicator
          (fun q y =>
            cfzCarryAdjustedResidueValueAtVector
              (D := pairedDivisorLcm z)
              N W b forms carry q
              (fun v => (y v : ZMod (pairedDivisorLcm z))))
          z x)
      (pairedDivisorLcm z) := by
  intro x y hxy
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  change
    natDivisibilityIndicator (z q).1
          (cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q
            (fun v => (x v : ZMod (pairedDivisorLcm z)))) *
        natDivisibilityIndicator (z q).2
          (cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q
            (fun v => (x v : ZMod (pairedDivisorLcm z)))) =
      natDivisibilityIndicator (z q).1
          (cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q
            (fun v => (y v : ZMod (pairedDivisorLcm z)))) *
        natDivisibilityIndicator (z q).2
          (cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q
            (fun v => (y v : ZMod (pairedDivisorLcm z))))
  rw [cfzCarryAdjustedResidueValueAtVector_eq_of_coordinate_modEq
    N W b forms carry q x y hxy]

/-! ## Agreement with the cyclic value on one canonical cell -/

/-- If the point has the prescribed carry vector, the cyclic CFZ value and
the fixed affine residue value agree modulo every positive modulus. -/
theorem
    natCast_cfzWTrickedLinearValue_eq_carryAdjustedResidueValueAtVector
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N] [NeZero D]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ)
    (x : CFZVariable k → ℕ)
    (hcarry :
      cfzCanonicalCarryVector (N := N) forms x = carry) :
    (cfzWTrickedLinearValue W b (forms q)
        (cubePointOfNat (N := N) x) : ZMod D) =
      (cfzCarryAdjustedResidueValueAtVector
        (D := D) N W b forms carry q
        (fun v => (x v : ZMod D)) : ZMod D) := by
  rw [natCast_cfzCarryAdjustedResidueValueAtVector]
  calc
    (cfzWTrickedLinearValue W b (forms q)
        (cubePointOfNat (N := N) x) : ZMod D) =
        (((cfzCarryAdjustedAffineForm N W b (forms q)
          (cfzCarry (N := N) (forms q) x)).eval
          (fun v => (x v : ℤ)) : ℤ) : ZMod D) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun n : ℤ => (n : ZMod D))
          (cfzCarryAdjustedAffineForm_eval_canonicalCarry
            (N := N) W b (forms q) x).symm
    _ = (((cfzCarryAdjustedAffineForm N W b (forms q)
          (carry q)).eval
          (fun v => (x v : ℤ)) : ℤ) : ZMod D) := by
      have hqcarry := congrFun hcarry q
      change
        cfzCarry (N := N) (forms q) x = carry q
        at hqcarry
      rw [hqcarry]
    _ = (cfzCarryAdjustedFamilyAtVector
          N W b forms carry q).evalZMod D
          (fun v => (x v : ZMod D)) := by
      simpa only [cfzCarryAdjustedFamilyAtVector,
        Int.cast_natCast] using
        AffineForm.intCast_eval_eq_evalZMod D
          (cfzCarryAdjustedFamilyAtVector
            N W b forms carry q)
          (fun v => (x v : ℤ))

/-- Pointwise paired-indicator equality on a prescribed canonical carry
cell. -/
theorem pairedDivisibilityIndicator_cfz_eq_carryVectorResidue_of_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (x : CFZVariable k → ℕ)
    (hcarry :
      cfzCanonicalCarryVector (N := N) forms x = carry) :
    pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x =
      pairedDivisibilityIndicator
        (fun q y =>
          cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q
            (fun v =>
              (y v : ZMod (pairedDivisorLcm z))))
        z x := by
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  have hvalue :=
    natCast_cfzWTrickedLinearValue_eq_carryAdjustedResidueValueAtVector
      (D := pairedDivisorLcm z)
      W b forms carry q x hcarry
  rw [natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_left_dvd_lcm z q) hvalue,
    natDivisibilityIndicator_eq_of_cast_eq_of_dvd
      (pairedDivisor_right_dvd_lcm z q) hvalue]

/-- Multiplication by the canonical-cell indicator makes the cyclic and
fixed-family residue models equal on the whole natural box. -/
theorem
    cfzCanonicalCarryIndicator_mul_pairedDivisibilityIndicator_eq_residue
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (x : CFZVariable k → ℕ) :
    cfzCanonicalCarryIndicator (N := N) forms carry x *
        pairedDivisibilityIndicator
          (fun q y =>
            cfzWTrickedLinearValue W b (forms q)
              (cubePointOfNat (N := N) y))
          z x =
      cfzCanonicalCarryIndicator (N := N) forms carry x *
        pairedDivisibilityIndicator
          (fun q y =>
            cfzCarryAdjustedResidueValueAtVector
              (D := pairedDivisorLcm z)
              N W b forms carry q
              (fun v =>
                (y v : ZMod (pairedDivisorLcm z))))
          z x := by
  by_cases hcarry :
      cfzCanonicalCarryVector (N := N) forms x = carry
  · rw [pairedDivisibilityIndicator_cfz_eq_carryVectorResidue_of_eq
      W b forms carry z x hcarry]
  · simp [cfzCanonicalCarryIndicator, hcarry]

/-! ## Exact residue mean and CRT product -/

/-- The residue-box mean of the fixed-family indicator is its paired
divisibility density on the finite residue module. -/
theorem
    meanMod_pairedDivisibilityIndicator_cfzCarryVector_eq_density
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    meanMod (pairedDivisorLcm z)
        (fun x : CFZVariable k → ℕ =>
          pairedDivisibilityIndicator
            (fun q y =>
              cfzCarryAdjustedResidueValueAtVector
                (D := pairedDivisorLcm z)
                N W b forms carry q
                (fun v =>
                  (y v : ZMod (pairedDivisorLcm z))))
            z x) =
      pairedDivisibilityDensity
        (fun q =>
          cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q)
        z := by
  rw [meanMod_eq_mean_zmodVector]
  unfold pairedDivisibilityDensity
  apply congrArg mean
  funext x
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  have hvalue :
      cfzCarryAdjustedResidueValueAtVector
          (D := pairedDivisorLcm z)
          N W b forms carry q
          (fun v =>
            ((x v).val : ZMod (pairedDivisorLcm z))) =
        cfzCarryAdjustedResidueValueAtVector
          (D := pairedDivisorLcm z)
          N W b forms carry q x := by
    unfold cfzCarryAdjustedResidueValueAtVector
      affineFormResidueValue
    congr 2
    funext v
    exact ZMod.natCast_zmod_val (x v)
  change
    natDivisibilityIndicator (z q).1
          (cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q
            (fun v =>
              ((x v).val : ZMod (pairedDivisorLcm z)))) *
        natDivisibilityIndicator (z q).2
          (cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q
            (fun v =>
              ((x v).val : ZMod (pairedDivisorLcm z)))) =
      natDivisibilityIndicator (z q).1
          (cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q x) *
        natDivisibilityIndicator (z q).2
          (cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q x)
  rw [hvalue]

/-- For a squarefree paired divisor choice, the preceding density is the
exact CRT Euler product of the fixed carry-adjusted affine family. -/
theorem pairedDivisibilityDensity_cfzCarryVector_eq_eulerProduct
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    pairedDivisibilityDensity
        (fun q =>
          cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q)
        z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ)
          (cfzCarryAdjustedFamilyAtVector
            N W b forms carry)
          (pairedPrimeSupport z p) := by
  exact
    pairedDivisibilityDensity_affineFormResidueValue_eq_prod
      (cfzCarryAdjustedFamilyAtVector
        N W b forms carry) z hz

/-! ## Per-cell cyclic-to-Euler comparison -/

/-- The periodic paired indicator of one fixed carry-adjusted family. -/
noncomputable def cfzCarryVectorResiduePairedIndicator
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (x : CFZVariable k → ℕ) : ℝ :=
  pairedDivisibilityIndicator
    (fun q y =>
      cfzCarryAdjustedResidueValueAtVector
        (D := pairedDivisorLcm z)
        N W b forms carry q
        (fun v =>
          (y v : ZMod (pairedDivisorLcm z))))
    z x

/-- Density of one canonical carry cell in the standard box. -/
noncomputable def cfzCanonicalCarryCellDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) : ℝ :=
  boxMean (fun _ : CFZVariable k => N)
    (cfzCanonicalCarryIndicator (N := N) forms carry)

/-- Contribution of one canonical carry cell to the original cyclic paired
divisibility density. -/
noncomputable def cfzCanonicalCarryCellCyclicContribution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ) : ℝ :=
  boxMean (fun _ : CFZVariable k => N) fun x =>
    cfzCanonicalCarryIndicator (N := N) forms carry x *
      pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x

/-- Exact finite residue density of the fixed family attached to a carry
vector. -/
noncomputable def cfzCarryVectorPairedDivisibilityDensity
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] : ℝ :=
  pairedDivisibilityDensity
    (fun q =>
      cfzCarryAdjustedResidueValueAtVector
        (D := pairedDivisorLcm z)
        N W b forms carry q)
    z

/-- Explicit per-cell error: outer incomplete blocks plus carry-transition
blocks. -/
noncomputable def cfzCanonicalCarryCellBoundaryError
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ)
    (forms : κ → CFZFormIndex k) : ℝ :=
  4 *
      (((∏ _v : CFZVariable k, N) -
          ∏ _v : CFZVariable k,
            trimToMultiple D N : ℕ) : ℝ) /
        ∏ _v : CFZVariable k, (N : ℝ) +
    2 *
      (((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
        ∏ _v : CFZVariable k,
          (trimToMultiple D N : ℝ))

/-- Contribution of the fixed residue model on one canonical cell. -/
noncomputable def cfzCanonicalCarryCellResidueContribution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] : ℝ :=
  boxMean (fun _ : CFZVariable k => N) fun x =>
    cfzCanonicalCarryIndicator (N := N) forms carry x *
      cfzCarryVectorResiduePairedIndicator
        N W b forms carry z x

theorem periodicInEachCoordinate_cfzCarryVectorResiduePairedIndicator
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    PeriodicInEachCoordinate
      (cfzCarryVectorResiduePairedIndicator
        N W b forms carry z)
      (pairedDivisorLcm z) := by
  unfold cfzCarryVectorResiduePairedIndicator
  exact
    periodicInEachCoordinate_pairedDivisibilityIndicator_cfzCarryVector
      N W b forms carry z

theorem abs_cfzCarryVectorResiduePairedIndicator_le_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (x : CFZVariable k → ℕ) :
    |cfzCarryVectorResiduePairedIndicator
        N W b forms carry z x| ≤ 1 := by
  have hnonneg :
      0 ≤ cfzCarryVectorResiduePairedIndicator
        N W b forms carry z x := by
    unfold cfzCarryVectorResiduePairedIndicator
      pairedDivisibilityIndicator
      natDivisibilityIndicator
    positivity
  rw [abs_of_nonneg hnonneg]
  unfold cfzCarryVectorResiduePairedIndicator
    pairedDivisibilityIndicator
  apply Finset.prod_le_one
  · intro q _hq
    unfold natDivisibilityIndicator
    positivity
  · intro q _hq
    unfold natDivisibilityIndicator
    split_ifs <;> norm_num

theorem meanMod_cfzCarryVectorResiduePairedIndicator_eq_density
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    meanMod (pairedDivisorLcm z)
        (cfzCarryVectorResiduePairedIndicator
          N W b forms carry z) =
      cfzCarryVectorPairedDivisibilityDensity
        N W b forms carry z := by
  unfold cfzCarryVectorResiduePairedIndicator
    cfzCarryVectorPairedDivisibilityDensity
  exact
    meanMod_pairedDivisibilityIndicator_cfzCarryVector_eq_density
      N W b forms carry z

/-- The cyclic and fixed residue contributions agree exactly after masking
by the canonical-cell indicator. -/
theorem cfzCanonicalCarryCellCyclicContribution_eq_residueContribution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    cfzCanonicalCarryCellCyclicContribution
        (N := N) W b forms carry z =
      cfzCanonicalCarryCellResidueContribution
        (N := N) W b forms carry z := by
  unfold cfzCanonicalCarryCellCyclicContribution
    cfzCanonicalCarryCellResidueContribution
    cfzCarryVectorResiduePairedIndicator
  apply congrArg
    (boxMean (fun _ : CFZVariable k => N))
  funext x
  exact
    cfzCanonicalCarryIndicator_mul_pairedDivisibilityIndicator_eq_residue
      W b forms carry z x

/-- The fixed residue contribution satisfies the canonical-cell discrepancy
estimate. -/
theorem
    abs_canonicalCarryCell_residueContribution_sub_density_mul_residueDensity_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hDle : pairedDivisorLcm z ≤ N) :
    |cfzCanonicalCarryCellResidueContribution
          (N := N) W b forms carry z -
        cfzCanonicalCarryCellDensity
            (N := N) forms carry *
          cfzCarryVectorPairedDivisibilityDensity
            N W b forms carry z| ≤
      cfzCanonicalCarryCellBoundaryError
        (N := N) (pairedDivisorLcm z) forms := by
  have h :=
    abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_density_mul_meanMod_le_full
      (NeZero.pos (pairedDivisorLcm z)) hDle forms carry
      (cfzCarryVectorResiduePairedIndicator
        N W b forms carry z)
      (periodicInEachCoordinate_cfzCarryVectorResiduePairedIndicator
        N W b forms carry z)
      (abs_cfzCarryVectorResiduePairedIndicator_le_one
        N W b forms carry z)
  rw [meanMod_cfzCarryVectorResiduePairedIndicator_eq_density
    N W b forms carry z] at h
  simpa only [cfzCanonicalCarryCellResidueContribution,
    cfzCanonicalCarryCellDensity,
    cfzCanonicalCarryCellBoundaryError] using h

/-- The contribution of one canonical carry cell is its box density times
the exact finite residue density, up to the explicit boundary error. -/
theorem
    abs_canonicalCarryCell_cyclicContribution_sub_density_mul_residueDensity_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hDle : pairedDivisorLcm z ≤ N) :
    |cfzCanonicalCarryCellCyclicContribution
          (N := N) W b forms carry z -
        cfzCanonicalCarryCellDensity
            (N := N) forms carry *
          cfzCarryVectorPairedDivisibilityDensity
            N W b forms carry z| ≤
      cfzCanonicalCarryCellBoundaryError
        (N := N) (pairedDivisorLcm z) forms := by
  rw [cfzCanonicalCarryCellCyclicContribution_eq_residueContribution
    W b forms carry z]
  exact
    abs_canonicalCarryCell_residueContribution_sub_density_mul_residueDensity_le
      W b forms carry z hDle

/-- The same comparison with the finite density rewritten as its exact CRT
Euler product. -/
theorem
    abs_canonicalCarryCell_cyclicContribution_sub_density_mul_eulerProduct_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDle : pairedDivisorLcm z ≤ N) :
    |cfzCanonicalCarryCellCyclicContribution
          (N := N) W b forms carry z -
        cfzCanonicalCarryCellDensity
            (N := N) forms carry *
          ∏ p : (pairedDivisorLcm z).primeFactors,
            affineFamilyZeroDensity (p : ℕ)
              (cfzCarryAdjustedFamilyAtVector
                N W b forms carry)
              (pairedPrimeSupport z p)| ≤
      cfzCanonicalCarryCellBoundaryError
        (N := N) (pairedDivisorLcm z) forms := by
  have h :=
    abs_canonicalCarryCell_cyclicContribution_sub_density_mul_residueDensity_le
      (N := N) W b forms carry z hDle
  have heuler :
      cfzCarryVectorPairedDivisibilityDensity
          N W b forms carry z =
        ∏ p : (pairedDivisorLcm z).primeFactors,
          affineFamilyZeroDensity (p : ℕ)
            (cfzCarryAdjustedFamilyAtVector
              N W b forms carry)
            (pairedPrimeSupport z p) := by
    unfold cfzCarryVectorPairedDivisibilityDensity
    exact
      pairedDivisibilityDensity_cfzCarryVector_eq_eulerProduct
        N W b forms carry z hz
  rw [heuler] at h
  exact h

/-! ## Summing the canonical carry cells -/

/-- Masking by the carry indicator is the same as summing over the
corresponding canonical carry finset. -/
theorem boxMean_cfzCanonicalCarryIndicator_mul_eq_cellSum_div
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ) :
    boxMean (fun _ : CFZVariable k => N)
        (fun x =>
          cfzCanonicalCarryIndicator
              (N := N) forms carry x *
            F x) =
      (∑ x ∈ cfzCanonicalCarryCell
          (N := N) forms carry, F x) /
        ∏ _v : CFZVariable k, (N : ℝ) := by
  rw [boxMean, boxSum_eq_sum_natBox]
  unfold cfzCanonicalCarryCell
    cfzCanonicalCarryIndicator
  simp only [Finset.sum_filter]
  apply congrArg (fun r : ℝ => r / ∏ _v : CFZVariable k, (N : ℝ))
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hcarry :
      cfzCanonicalCarryVector (N := N) forms x = carry
  · simp [hcarry]
  · simp [hcarry]

/-- The original cyclic paired divisibility density is the exact sum of its
canonical carry-cell contributions. -/
theorem sum_cfzCanonicalCarryCellCyclicContribution_eq_density
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) :
    ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        cfzCanonicalCarryCellCyclicContribution
          (N := N) W b forms carry z =
      pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z := by
  let F : (CFZVariable k → ℕ) → ℝ :=
    fun x =>
      pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x
  have hcell :
      ∀ carry : κ → ℤ,
        cfzCanonicalCarryCellCyclicContribution
            (N := N) W b forms carry z =
          (∑ x ∈ cfzCanonicalCarryCell
              (N := N) forms carry, F x) /
            ∏ _v : CFZVariable k, (N : ℝ) := by
    intro carry
    unfold cfzCanonicalCarryCellCyclicContribution
    exact
      boxMean_cfzCanonicalCarryIndicator_mul_eq_cellSum_div
        forms carry F
  calc
    ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        cfzCanonicalCarryCellCyclicContribution
          (N := N) W b forms carry z =
        ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
          (∑ x ∈ cfzCanonicalCarryCell
              (N := N) forms carry, F x) /
            ∏ _v : CFZVariable k, (N : ℝ) := by
      apply Finset.sum_congr rfl
      intro carry _hcarry
      exact hcell carry
    _ =
        (∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
          ∑ x ∈ cfzCanonicalCarryCell
              (N := N) forms carry, F x) /
            ∏ _v : CFZVariable k, (N : ℝ) := by
      symm
      rw [Finset.sum_div]
    _ = (∑ x ∈ natBox
            (fun _ : CFZVariable k => N), F x) /
          ∏ _v : CFZVariable k, (N : ℝ) := by
      rw [sum_cfzCanonicalCarryCell_eq_sum_natBox
        (N := N) forms F]
    _ = boxMean (fun _ : CFZVariable k => N) F := by
      rw [boxMean, boxSum_eq_sum_natBox]
    _ = pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z := by
      unfold pairedDivisibilityDensity
      rw [mean_cubePoint_eq_boxMean]
      rfl

/-- Weighted canonical-cell Euler model for one paired divisor choice.  Each
summand uses a fixed affine family independent of the divisor LCM. -/
noncomputable def cfzCanonicalCarryEulerAverage
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) : ℝ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    cfzCanonicalCarryCellDensity
        (N := N) forms carry *
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ)
          (cfzCarryAdjustedFamilyAtVector
            N W b forms carry)
          (pairedPrimeSupport z p)

/-- Global cyclic-to-fixed-family Euler bridge.  The error is the number of
possible carry vectors times the per-cell boundary error. -/
theorem
    abs_pairedDivisibilityDensity_cfz_sub_canonicalCarryEulerAverage_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDle : pairedDivisorLcm z ≤ N) :
    |pairedDivisibilityDensity
          (fun q (x : CubePoint k N) =>
            cfzWTrickedLinearValue W b (forms q) x)
          z -
        cfzCanonicalCarryEulerAverage
          (N := N) W b forms z| ≤
      ((cfzCanonicalCarryVectorChoices κ k).card : ℝ) *
        cfzCanonicalCarryCellBoundaryError
          (N := N) (pairedDivisorLcm z) forms := by
  rw [← sum_cfzCanonicalCarryCellCyclicContribution_eq_density
    (N := N) W b forms z]
  unfold cfzCanonicalCarryEulerAverage
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        (cfzCanonicalCarryCellCyclicContribution
            (N := N) W b forms carry z -
          cfzCanonicalCarryCellDensity
              (N := N) forms carry *
            ∏ p : (pairedDivisorLcm z).primeFactors,
              affineFamilyZeroDensity (p : ℕ)
                (cfzCarryAdjustedFamilyAtVector
                  N W b forms carry)
                (pairedPrimeSupport z p))| ≤
        ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
          |cfzCanonicalCarryCellCyclicContribution
              (N := N) W b forms carry z -
            cfzCanonicalCarryCellDensity
                (N := N) forms carry *
              ∏ p : (pairedDivisorLcm z).primeFactors,
                affineFamilyZeroDensity (p : ℕ)
                  (cfzCarryAdjustedFamilyAtVector
                    N W b forms carry)
                  (pairedPrimeSupport z p)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _carry ∈ cfzCanonicalCarryVectorChoices κ k,
          cfzCanonicalCarryCellBoundaryError
            (N := N) (pairedDivisorLcm z) forms := by
      apply Finset.sum_le_sum
      intro carry _hcarry
      exact
        abs_canonicalCarryCell_cyclicContribution_sub_density_mul_eulerProduct_le
          (N := N) W b forms carry z hz hDle
    _ = ((cfzCanonicalCarryVectorChoices κ k).card : ℝ) *
          cfzCanonicalCarryCellBoundaryError
            (N := N) (pairedDivisorLcm z) forms := by
      simp

end Wikipedia.SzemeredisTheorem
