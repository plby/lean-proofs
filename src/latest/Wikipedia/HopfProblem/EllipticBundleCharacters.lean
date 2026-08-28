import Wikipedia.HopfProblem.EllipticCentralFamily
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCriterion
import Mathlib.LinearAlgebra.Determinant

/-!
# The actual elliptic canonical and transverse characters

The transverse multiplier is the derivative of the actual disc rotation.
The canonical multiplier is the inverse determinant of the actual complex
linear monodromy at the central period. Their cyclic characters have exact
orders three and four. Identifying the corresponding geometric line bundles
requires the chart-derivative identifications in the companion files.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

def normalPhase : Kind → ℂ
  | .three => -rho
  | .four => -Complex.I

def canonicalPhase : Kind → ℂ
  | .three => -rho
  | .four => Complex.I

theorem normalPhase_norm (j : Kind) : ‖normalPhase j‖ = 1 := by
  cases j <;> simp [normalPhase, norm_rho]

theorem canonicalPhase_norm (j : Kind) : ‖canonicalPhase j‖ = 1 := by
  cases j <;> simp [canonicalPhase, norm_rho]

theorem normalPhase_ne_zero (j : Kind) : normalPhase j ≠ 0 := by
  intro h
  have hn := normalPhase_norm j
  simp [h] at hn

theorem canonicalPhase_ne_zero (j : Kind) : canonicalPhase j ≠ 0 := by
  intro h
  have hn := canonicalPhase_norm j
  simp [h] at hn

theorem normalPhase_pow_order (j : Kind) : normalPhase j ^ j.order = 1 := by
  cases j
  · change (-rho) ^ 3 = 1
    calc
      (-rho) ^ 3 = -(rho ^ 3) := by ring
      _ = 1 := by rw [rho_cube]; ring
  · norm_num [normalPhase, Kind.order, pow_succ]

theorem canonicalPhase_pow_order (j : Kind) : canonicalPhase j ^ j.order = 1 := by
  cases j
  · exact normalPhase_pow_order .three
  · norm_num [canonicalPhase, Kind.order, pow_succ]

theorem normalPhase_pow_ne_one (j : Kind) {n : ℕ} (hn : 0 < n) (hm : n < j.order) :
    normalPhase j ^ n ≠ 1 := by
  cases j
  · exact neg_rho_pow_ne_one hn hm
  · exact neg_I_pow_ne_one hn hm

theorem canonicalPhase_pow_ne_one (j : Kind) {n : ℕ} (hn : 0 < n) (hm : n < j.order) :
    canonicalPhase j ^ n ≠ 1 := by
  cases j
  · exact neg_rho_pow_ne_one hn hm
  · change n < 4 at hm
    change Complex.I ^ n ≠ 1
    interval_cases n
    · intro h
      have hi := congrArg Complex.im h
      norm_num at hi
    · norm_num
    · intro h
      have hi := congrArg Complex.im h
      norm_num [pow_succ] at hi

def normalUnit (j : Kind) : ℂˣ := Units.mk0 (normalPhase j) (normalPhase_ne_zero j)

def canonicalUnit (j : Kind) : ℂˣ := Units.mk0 (canonicalPhase j) (canonicalPhase_ne_zero j)

@[simp] theorem normalUnit_val (j : Kind) : (normalUnit j : ℂ) = normalPhase j := rfl

@[simp] theorem canonicalUnit_val (j : Kind) : (canonicalUnit j : ℂ) = canonicalPhase j := rfl

theorem normalUnit_pow_order (j : Kind) : normalUnit j ^ j.order = 1 :=
  Units.ext (by simpa only [Units.val_pow_eq_pow_val, normalUnit_val, Units.val_one] using
    normalPhase_pow_order j)

theorem canonicalUnit_pow_order (j : Kind) : canonicalUnit j ^ j.order = 1 :=
  Units.ext (by simpa only [Units.val_pow_eq_pow_val, canonicalUnit_val, Units.val_one] using
    canonicalPhase_pow_order j)

theorem normalUnit_orderOf (j : Kind) : orderOf (normalUnit j) = j.order := by
  apply (orderOf_eq_iff j.order_pos).mpr
  refine ⟨normalUnit_pow_order j, ?_⟩
  intro n hm hn h
  apply normalPhase_pow_ne_one j hn hm
  simpa only [Units.val_pow_eq_pow_val, normalUnit_val, Units.val_one] using congrArg Units.val h

theorem canonicalUnit_orderOf (j : Kind) : orderOf (canonicalUnit j) = j.order := by
  apply (orderOf_eq_iff j.order_pos).mpr
  refine ⟨canonicalUnit_pow_order j, ?_⟩
  intro n hm hn h
  apply canonicalPhase_pow_ne_one j hn hm
  simpa only [Units.val_pow_eq_pow_val, canonicalUnit_val, Units.val_one] using congrArg Units.val h

namespace BundleCharacters

variable {m : ℕ} [NeZero m]

def cyclicCharacter (c : ℂˣ) (hc : c ^ m = 1) : Multiplicative (ZMod m) →* ℂˣ where
  toFun g := c ^ g.toAdd.val
  map_one' := by simp
  map_mul' g h := by
    change c ^ (g.toAdd + h.toAdd).val = c ^ g.toAdd.val * c ^ h.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hc, pow_add]

@[simp] theorem cyclicCharacter_apply (c : ℂˣ) (hc : c ^ m = 1)
    (g : Multiplicative (ZMod m)) : cyclicCharacter c hc g = c ^ g.toAdd.val := rfl

theorem cyclicCharacter_ofAdd_natCast (c : ℂˣ) (hc : c ^ m = 1) (n : ℕ) :
    cyclicCharacter c hc (Multiplicative.ofAdd (n : ZMod m)) = c ^ n := by
  change c ^ (n : ZMod m).val = c ^ n
  rw [ZMod.val_natCast, ← pow_eq_pow_mod n hc]

@[simp] theorem cyclicCharacter_generator (c : ℂˣ) (hc : c ^ m = 1) :
    cyclicCharacter c hc (CyclicAction.generator m) = c := by
  simpa only [CyclicAction.generator, Nat.cast_one, pow_one] using
    cyclicCharacter_ofAdd_natCast c hc 1

theorem cyclicCharacter_pow_eq_one_iff (c : ℂˣ) (hc : c ^ m = 1) (n : ℕ) :
    cyclicCharacter c hc ^ n = 1 ↔ c ^ n = 1 := by
  constructor
  · intro h
    have he := congrArg (fun f : Multiplicative (ZMod m) →* ℂˣ =>
      f (CyclicAction.generator m)) h
    simpa only [MonoidHom.pow_apply, cyclicCharacter_generator, MonoidHom.one_apply] using he
  · intro hn
    apply MonoidHom.ext
    intro g
    change (c ^ g.toAdd.val) ^ n = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, hn, one_pow]

theorem cyclicCharacter_orderOf (c : ℂˣ) (hc : c ^ m = 1) :
    orderOf (cyclicCharacter c hc) = orderOf c :=
  orderOf_eq_orderOf_iff.mpr (cyclicCharacter_pow_eq_one_iff c hc)

end BundleCharacters

def normalCharacter (j : Kind) : CyclicGroup j →* ℂˣ :=
  BundleCharacters.cyclicCharacter (normalUnit j) (normalUnit_pow_order j)

def canonicalCharacter (j : Kind) : CyclicGroup j →* ℂˣ :=
  BundleCharacters.cyclicCharacter (canonicalUnit j) (canonicalUnit_pow_order j)

@[simp] theorem normalCharacter_apply (j : Kind) (g : CyclicGroup j) :
    (normalCharacter j g : ℂ) = normalPhase j ^ g.toAdd.val :=
  Units.val_pow_eq_pow_val _ _

@[simp] theorem canonicalCharacter_apply (j : Kind) (g : CyclicGroup j) :
    (canonicalCharacter j g : ℂ) = canonicalPhase j ^ g.toAdd.val :=
  Units.val_pow_eq_pow_val _ _

@[simp] theorem normalCharacter_generator (j : Kind) :
    normalCharacter j (CyclicAction.generator j.order) = normalUnit j :=
  BundleCharacters.cyclicCharacter_generator _ _

@[simp] theorem canonicalCharacter_generator (j : Kind) :
    canonicalCharacter j (CyclicAction.generator j.order) = canonicalUnit j :=
  BundleCharacters.cyclicCharacter_generator _ _

theorem normalCharacter_orderOf (j : Kind) : orderOf (normalCharacter j) = j.order :=
  (BundleCharacters.cyclicCharacter_orderOf _ _).trans (normalUnit_orderOf j)

theorem canonicalCharacter_orderOf (j : Kind) : orderOf (canonicalCharacter j) = j.order :=
  (BundleCharacters.cyclicCharacter_orderOf _ _).trans (canonicalUnit_orderOf j)

theorem familyRotation_val (j : Kind) (z : Disc) :
    (familyRotation j z : ℂ) = normalPhase j * z := by
  cases j <;> rfl

theorem familyRotation_iterate_val (j : Kind) (n : ℕ) (z : Disc) :
    ((familyRotation j)^[n] z : ℂ) = normalPhase j ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', familyRotation_val, ih, pow_succ', mul_assoc]

@[simp] theorem centralPeriod_three_tau : (centralPeriod .three).val.val.τ = rho :=
  tauThree_zero

@[simp] theorem centralPeriod_four_tau : (centralPeriod .four).val.val.τ = Complex.I :=
  tauFour_zero

theorem central_linearMatrix_det (j : Kind) :
    (linearMatrix j (centralPeriod j).val).det = (canonicalPhase j)⁻¹ := by
  cases j
  · change (centralPeriod .three).val.val.R₁.det = _
    rw [PeriodPoint.det_R₁, centralPeriod_three_tau]
    simp [canonicalPhase, div_eq_mul_inv]
  · change (centralPeriod .four).val.val.R₂.det = _
    rw [PeriodPoint.det_R₂, centralPeriod_four_tau]
    simp [canonicalPhase]

/-- The actual complex linear monodromy, not an independently specified
matrix invariant, has the inverse canonical-character multiplier. -/
theorem central_linearEquiv_det (j : Kind) :
    LinearMap.det (linearEquiv j (centralPeriod j)).toLinearMap = (canonicalPhase j)⁻¹ := by
  have he : (linearEquiv j (centralPeriod j)).toLinearMap =
      Matrix.toLin' (linearMatrix j (centralPeriod j).val) := by
    apply LinearMap.ext
    intro z
    exact linearEquiv_apply j (centralPeriod j) z
  rw [he, LinearMap.det_toLin']
  exact central_linearMatrix_det j

theorem central_linearEquiv_det_inv (j : Kind) :
    (LinearMap.det (linearEquiv j (centralPeriod j)).toLinearMap)⁻¹ = canonicalPhase j := by
  rw [central_linearEquiv_det, inv_inv]

/-- The original surface projection, with its actual cyclic covering action. -/
theorem surfaceProjection_isQuotientCoveringMap (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := affineAction j p v hv.1
    IsQuotientCoveringMap (surfaceProjection j p v hv) (CyclicGroup j) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) p.val.Torus

end Wikipedia.HopfProblem.Elliptic
