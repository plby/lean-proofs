import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticFullProduct

/-!
# Original complex-vector lifts of the elliptic product coordinates

The forward and inverse formulas are defined on the original complex vector
covers.  The varying period coordinates and the original central period
coordinates are retained explicitly.  Both formulas commute with the native
quotient maps and the already proved full product homeomorphism, and they are
mutual inverses before taking the quotients.

The circle phase is also expressed as an exponential of the literal first
real-period coordinate.  This file supplies exact formulas for a separate
smoothness argument; it does not assert or install a different atlas.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth

open Elliptic SpecialPeriods EllipticModel EllipticGamma EllipticFullProduct
open TrianglePeriodFamily.GammaZero

/-- The normalized circle phase on an original real-lattice representative. -/
theorem normalizedGamma_mkQ (j : Kind) (a : RealPlane₄) :
    normalizedGamma j (standardLattice.mkQ a) =
      (((j.twist 0 : ℝ) * a 0 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [normalizedGamma_apply, fibreGamma_mkQ, ← AddCircle.coe_zsmul, zsmul_eq_mul]

variable {j : Kind} (D : Equivariant.Data j)

/-- The original complex vector cover followed by the actual finite filling quotient. -/
def fillingCover (p : Disc × ComplexPlane₂) : D.Space j.twist (mainTwist_admissible j) :=
  D.quotient j.twist (mainTwist_admissible j) (D.periods.quotientMap p)

/-- The original central complex vector cover, leaving the disc coordinate unchanged. -/
def centralCover (p : Disc × ComplexPlane₂) :
    Disc × Surface j D.centralPeriod j.twist (mainTwist_admissible j) :=
  (p.1, surfaceProjection j D.centralPeriod j.twist (mainTwist_admissible j)
    (D.centralPeriod.val.lattice.mkQ p.2))

@[simp] theorem fillingCover_apply (p : Disc × ComplexPlane₂) :
    fillingCover D p = D.quotient j.twist (mainTwist_admissible j)
      (p.1, standardLattice.mkQ ((D.periods.periodEquiv p.1).symm p.2)) := rfl

@[simp] theorem centralCover_apply (p : Disc × ComplexPlane₂) :
    centralCover D p =
      (p.1, surfaceProjection j D.centralPeriod j.twist (mainTwist_admissible j)
        (D.centralPeriod.val.lattice.mkQ p.2)) := rfl

/-- Rotate by the original normalized real-period circle and use the actual
central period vectors. -/
def forwardLift (p : Disc × ComplexPlane₂) : Disc × ComplexPlane₂ :=
  let a := (D.periods.periodEquiv p.1).symm p.2
  (rotate (normalizedGamma j (standardLattice.mkQ a)) p.1,
    Elliptic.periodEquiv D.centralPeriod.val a)

/-- Undo the phase and reconstruct the original varying-period vector at the
resulting disc point. -/
def inverseLift (p : Disc × ComplexPlane₂) : Disc × ComplexPlane₂ :=
  let a := (Elliptic.periodEquiv D.centralPeriod.val).symm p.2
  let s := rotate (-normalizedGamma j (standardLattice.mkQ a)) p.1
  (s, D.periods.periodEquiv s a)

@[simp] theorem forwardLift_fst (p : Disc × ComplexPlane₂) :
    (forwardLift D p).1 =
      rotate (normalizedGamma j
        (standardLattice.mkQ ((D.periods.periodEquiv p.1).symm p.2))) p.1 := rfl

@[simp] theorem forwardLift_snd (p : Disc × ComplexPlane₂) :
    (forwardLift D p).2 =
      Elliptic.periodEquiv D.centralPeriod.val ((D.periods.periodEquiv p.1).symm p.2) := rfl

@[simp] theorem inverseLift_fst (p : Disc × ComplexPlane₂) :
    (inverseLift D p).1 =
      rotate (-normalizedGamma j
        (standardLattice.mkQ ((Elliptic.periodEquiv D.centralPeriod.val).symm p.2))) p.1 := rfl

@[simp] theorem inverseLift_snd (p : Disc × ComplexPlane₂) :
    (inverseLift D p).2 = D.periods.periodEquiv (inverseLift D p).1
      ((Elliptic.periodEquiv D.centralPeriod.val).symm p.2) := rfl

/-- The forward disc coordinate has an explicit real-coordinate exponential phase. -/
theorem forwardLift_fst_val (p : Disc × ComplexPlane₂) :
    ((forwardLift D p).1 : ℂ) =
      CuspUniformization.exponential
        ((((j.twist 0 : ℝ) * ((D.periods.periodEquiv p.1).symm p.2) 0 : ℝ)) : ℂ) *
          (p.1 : ℂ) := by
  rw [forwardLift_fst, normalizedGamma_mkQ, rotate_real]

/-- The inverse disc coordinate uses the negative of the same literal normalized phase. -/
theorem inverseLift_fst_val (p : Disc × ComplexPlane₂) :
    ((inverseLift D p).1 : ℂ) =
      CuspUniformization.exponential
        (-((((j.twist 0 : ℝ) *
          ((Elliptic.periodEquiv D.centralPeriod.val).symm p.2) 0 : ℝ)) : ℂ)) *
            (p.1 : ℂ) := by
  rw [inverseLift_fst, normalizedGamma_mkQ, ← AddCircle.coe_neg, rotate_real,
    Complex.ofReal_neg]

/-- The original filling cover on its own varying period-vector representatives. -/
theorem fillingCover_periodCoordinates (s : Disc) (a : RealPlane₄) :
    fillingCover D (s, D.periods.periodEquiv s a) =
      D.quotient j.twist (mainTwist_admissible j) (s, standardLattice.mkQ a) := by
  rw [fillingCover_apply, LinearEquiv.symm_apply_apply]

/-- The original central cover on its own fixed period-vector representatives. -/
theorem centralCover_periodCoordinates (s : Disc) (a : RealPlane₄) :
    centralCover D (s, Elliptic.periodEquiv D.centralPeriod.val a) =
      (s, surfaceProjection j D.centralPeriod j.twist (mainTwist_admissible j)
        (flatTorusPeriodHomeomorph D.centralPeriod.val (standardLattice.mkQ a))) := rfl

/-- The vector-level forward formula on literal real-period representatives. -/
theorem forwardLift_periodCoordinates (s : Disc) (a : RealPlane₄) :
    forwardLift D (s, D.periods.periodEquiv s a) =
      (rotate (normalizedGamma j (standardLattice.mkQ a)) s,
        Elliptic.periodEquiv D.centralPeriod.val a) := by
  simp only [forwardLift, LinearEquiv.symm_apply_apply]

/-- The vector-level inverse formula on literal central-period representatives. -/
theorem inverseLift_periodCoordinates (s : Disc) (a : RealPlane₄) :
    inverseLift D (s, Elliptic.periodEquiv D.centralPeriod.val a) =
      (rotate (-normalizedGamma j (standardLattice.mkQ a)) s,
        D.periods.periodEquiv (rotate (-normalizedGamma j (standardLattice.mkQ a)) s) a) := by
  simp only [inverseLift, ContinuousLinearEquiv.symm_apply_apply]

/-- The explicit forward vector map descends to the exact original full product homeomorphism. -/
theorem centralCover_forwardLift (p : Disc × ComplexPlane₂) :
    centralCover D (forwardLift D p) = fillingProductHomeomorph D (fillingCover D p) := by
  rcases p with ⟨s, z⟩
  obtain ⟨a, rfl⟩ := (D.periods.periodEquiv s).surjective z
  rw [forwardLift_periodCoordinates, centralCover_periodCoordinates,
    fillingCover_periodCoordinates, fillingProductHomeomorph_quotient]

/-- The explicit inverse vector map descends to the inverse of the same original homeomorphism. -/
theorem fillingCover_inverseLift (p : Disc × ComplexPlane₂) :
    fillingCover D (inverseLift D p) = (fillingProductHomeomorph D).symm (centralCover D p) := by
  rcases p with ⟨s, z⟩
  obtain ⟨a, rfl⟩ := (Elliptic.periodEquiv D.centralPeriod.val).surjective z
  rw [inverseLift_periodCoordinates, fillingCover_periodCoordinates,
    centralCover_periodCoordinates, fillingProductHomeomorph_symm_surfaceProjection]

/-- The two vector-level maps are inverse before any lattice or finite quotient is taken. -/
@[simp] theorem inverseLift_forwardLift (p : Disc × ComplexPlane₂) :
    inverseLift D (forwardLift D p) = p := by
  rcases p with ⟨s, z⟩
  obtain ⟨a, rfl⟩ := (D.periods.periodEquiv s).surjective z
  rw [forwardLift_periodCoordinates, inverseLift_periodCoordinates, rotate_neg_rotate]

/-- The other inverse identity also holds on the literal complex vector covers. -/
@[simp] theorem forwardLift_inverseLift (p : Disc × ComplexPlane₂) :
    forwardLift D (inverseLift D p) = p := by
  rcases p with ⟨s, z⟩
  obtain ⟨a, rfl⟩ := (Elliptic.periodEquiv D.centralPeriod.val).surjective z
  rw [inverseLift_periodCoordinates, forwardLift_periodCoordinates, rotate_rotate_neg]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmooth
