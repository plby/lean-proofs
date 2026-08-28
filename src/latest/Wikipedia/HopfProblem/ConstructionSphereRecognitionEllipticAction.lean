import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticCoordinates
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusQuotientConjugacy

/-!
# The native clockwise disc-fibre cyclic action

The generator rotates the actual disc by `-1/m` and applies the supplied
finite-order fibre homeomorphism.  The finite action and its orbit quotient
are constructed from this literal generator.  A second action leaves the
disc fixed, for the explicit untwisting comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel

open SpecialPeriods ThreefoldOverlapMappingTorus
open Wikipedia.HopfProblem.Elliptic

variable {X : Type*} [TopologicalSpace X]

private def homeomorphPermHom : (X ≃ₜ X) →* Equiv.Perm X where
  toFun := Homeomorph.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fibrePermutation_pow_order (m : ℕ) (B : X ≃ₜ X) (hB : B ^ m = 1) :
    B.toEquiv ^ m = 1 := by
  change homeomorphPermHom B ^ m = 1
  rw [← map_pow, hB, map_one]

/-- The positive sector angle in the original additive circle. -/
def sector (m : ℕ) : Circle := (((1 : ℝ) / m : ℝ) : Circle)

theorem order_smul_sector (m : ℕ) [NeZero m] : m • sector m = 0 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  change m • (((1 : ℝ) / m : ℝ) : Circle) = 0
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  simp only [one_div, mul_inv_cancel₀ hm, AddCircle.coe_period]

/-- The literal clockwise rotation and original fibre map. -/
def capPermutation (m : ℕ) (B : X ≃ₜ X) : Equiv.Perm (Disc × X) :=
  (rotationHomeomorph (-sector m)).toEquiv.prodCongr B.toEquiv

@[simp] theorem capPermutation_apply (m : ℕ) (B : X ≃ₜ X) (p : Disc × X) :
    capPermutation m B p = (rotate (-sector m) p.1, B p.2) := rfl

theorem capPermutation_pow_apply (m : ℕ) (B : X ≃ₜ X) (n : ℕ) (p : Disc × X) :
    (capPermutation m B ^ n) p =
      (rotate (n • (-sector m)) p.1, (B.toEquiv ^ n) p.2) := by
  induction n with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply, zero_smul, rotate_zero]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, capPermutation_apply,
      succ_nsmul', rotate_add]
    rw [pow_succ']
    rfl

theorem capPermutation_pow_order (m : ℕ) [NeZero m] (B : X ≃ₜ X)
    (hB : B ^ m = 1) : capPermutation m B ^ m = 1 := by
  apply Equiv.ext
  intro p
  rw [capPermutation_pow_apply, smul_neg, order_smul_sector, neg_zero, rotate_zero,
    fibrePermutation_pow_order m B hB]
  rfl

/-- The comparison generator acts only on the fibre, in the same direction. -/
def verticalPermutation (B : X ≃ₜ X) : Equiv.Perm (Disc × X) :=
  (Equiv.refl Disc).prodCongr B.toEquiv

@[simp] theorem verticalPermutation_apply (B : X ≃ₜ X) (p : Disc × X) :
    verticalPermutation B p = (p.1, B p.2) := rfl

theorem verticalPermutation_pow_apply (B : X ≃ₜ X) (n : ℕ) (p : Disc × X) :
    (verticalPermutation B ^ n) p = (p.1, (B.toEquiv ^ n) p.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, verticalPermutation_apply]
    rw [pow_succ']
    rfl

theorem verticalPermutation_pow_order (m : ℕ) (B : X ≃ₜ X) (hB : B ^ m = 1) :
    verticalPermutation B ^ m = 1 := by
  apply Equiv.ext
  intro p
  rw [verticalPermutation_pow_apply, fibrePermutation_pow_order m B hB]
  rfl

variable (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)

@[instance_reducible] def fibreAction : MulAction (Multiplicative (ZMod m)) X :=
  CyclicAction.action B.toEquiv (fibrePermutation_pow_order m B hB)

@[instance_reducible] def capAction : MulAction (Multiplicative (ZMod m)) (Disc × X) :=
  CyclicAction.action (capPermutation m B) (capPermutation_pow_order m B hB)

@[instance_reducible] def verticalAction : MulAction (Multiplicative (ZMod m)) (Disc × X) :=
  CyclicAction.action (verticalPermutation B) (verticalPermutation_pow_order m B hB)

theorem fibreAction_continuous :
    letI := fibreAction m B hB
    ContinuousConstSMul (Multiplicative (ZMod m)) X :=
  CyclicAction.continuousConstSMul B.toEquiv (fibrePermutation_pow_order m B hB) B.continuous

theorem capAction_continuous :
    letI := capAction m B hB
    ContinuousConstSMul (Multiplicative (ZMod m)) (Disc × X) :=
  CyclicAction.continuousConstSMul (capPermutation m B) (capPermutation_pow_order m B hB)
    ((rotationHomeomorph (-sector m)).continuous.prodMap B.continuous)

theorem verticalAction_continuous :
    letI := verticalAction m B hB
    ContinuousConstSMul (Multiplicative (ZMod m)) (Disc × X) :=
  CyclicAction.continuousConstSMul (verticalPermutation B) (verticalPermutation_pow_order m B hB)
    (continuous_id.prodMap B.continuous)

abbrev FibreQuotient :=
  letI := fibreAction m B hB
  FiniteQuotient.Space (Multiplicative (ZMod m)) X

abbrev CapQuotient :=
  letI := capAction m B hB
  FiniteQuotient.Space (Multiplicative (ZMod m)) (Disc × X)

abbrev VerticalQuotient :=
  letI := verticalAction m B hB
  FiniteQuotient.Space (Multiplicative (ZMod m)) (Disc × X)

def fibreProject : X → FibreQuotient m B hB :=
  @FiniteQuotient.project (Multiplicative (ZMod m)) X _ (fibreAction m B hB)

def capProject : Disc × X → CapQuotient m B hB :=
  @FiniteQuotient.project (Multiplicative (ZMod m)) (Disc × X) _ (capAction m B hB)

def verticalProject : Disc × X → VerticalQuotient m B hB :=
  @FiniteQuotient.project (Multiplicative (ZMod m)) (Disc × X) _ (verticalAction m B hB)

theorem fibreProject_isOpenQuotientMap : IsOpenQuotientMap (fibreProject m B hB) := by
  let := fibreAction m B hB
  let := fibreAction_continuous m B hB
  exact FiniteQuotient.project_isOpenQuotientMap (Multiplicative (ZMod m)) X

theorem capProject_isOpenQuotientMap : IsOpenQuotientMap (capProject m B hB) := by
  let := capAction m B hB
  let := capAction_continuous m B hB
  exact FiniteQuotient.project_isOpenQuotientMap (Multiplicative (ZMod m)) (Disc × X)

theorem verticalProject_isOpenQuotientMap : IsOpenQuotientMap (verticalProject m B hB) := by
  let := verticalAction m B hB
  let := verticalAction_continuous m B hB
  exact FiniteQuotient.project_isOpenQuotientMap (Multiplicative (ZMod m)) (Disc × X)

theorem capAction_generator (p : Disc × X) :
    letI := capAction m B hB
    CyclicAction.generator m • p = (rotate (-sector m) p.1, B p.2) :=
  CyclicAction.generator_smul (capPermutation m B) (capPermutation_pow_order m B hB) p

theorem verticalAction_smul (g : Multiplicative (ZMod m)) (p : Disc × X) :
    letI := fibreAction m B hB
    letI := verticalAction m B hB
    g • p = (p.1, g • p.2) :=
  verticalPermutation_pow_apply B g.toAdd.val p

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel
