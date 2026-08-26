/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.BranchEvents
import ErdosProblems.Erdos730.DigitBoxes
import ErdosProblems.Erdos730.ObstructionMaps
import ErdosProblems.Erdos730.HigherPowerDensity
import ErdosProblems.Erdos730.RangeAssembly

/-!
# Erdős 730: concrete higher-prime-power local events

This module closes the finite-combinatorial bridge left open by
`Erdos730HigherPowerDensity`.  For a fixed branch and prime power `p^a`,
divisibility of the branch value confines the parameter to one root
progression.  Equations (16)--(17) identify the obstruction value along that
progression with the generic p-adic permutation map, while the lower-half
digit condition places its residue in the exact digit box.

The resulting complete/padded block bound is summed over all branches and
higher prime powers.  The geometric part is discharged by Tannery and the
terminal `p^a > X` part by the sublinear prime-power-pair count.  In
particular, the depth-zero case is retained in the finite block theorem.
-/

open Filter Finset Topology

namespace Erdos730.HigherPowerEvents

open BranchEvents ConsecutiveTransition DensityEvents DigitBoxes
open FullDensityCore KummerTransition ObstructionMaps

/-! ## Branch slopes and exceptional-prime exclusions -/

def branchSlope : Branch → ℕ
  | .P => 222138
  | .Q => 380808
  | .R => 148092
  | .S => 380808

def branchOffset : Branch → ℕ
  | .P => 11
  | .Q => 13
  | .R => 5
  | .S => 19

theorem branchValue_eq_slope_mul_add (L : Branch) (x : ℕ) :
    branchValue L x = branchSlope L * x + branchOffset L := by
  cases L with
  | P => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).1
  | Q => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.1
  | R => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.2.1
  | S => simpa [branchValue, branchSlope, branchOffset] using
      (branch_expansions x).2.2.2

theorem branchSlope_pos (L : Branch) : 0 < branchSlope L := by
  cases L <;> norm_num [branchSlope]

theorem three_not_dvd_branchValue (L : Branch) (x : ℕ) :
    ¬3 ∣ branchValue L x := by
  rw [Nat.dvd_iff_mod_eq_zero]
  cases L with
  | P => simpa [branchValue] using ne_of_eq_of_ne (branch_mod_3 x).1 (by norm_num)
  | Q => simpa [branchValue] using ne_of_eq_of_ne (branch_mod_3 x).2.1 (by norm_num)
  | R => simpa [branchValue] using ne_of_eq_of_ne (branch_mod_3 x).2.2.1 (by norm_num)
  | S => simpa [branchValue] using ne_of_eq_of_ne (branch_mod_3 x).2.2.2 (by norm_num)

theorem fortyOne_not_dvd_branchValue (L : Branch) (x : ℕ) :
    ¬41 ∣ branchValue L x := by
  rcases fixed_primes_do_not_divide_branches x with ⟨h41, _h43⟩
  cases L with
  | P => exact h41.1
  | Q => exact h41.2.1
  | R => exact h41.2.2.1
  | S => exact h41.2.2.2

theorem fortyThree_not_dvd_branchValue (L : Branch) (x : ℕ) :
    ¬43 ∣ branchValue L x := by
  rcases fixed_primes_do_not_divide_branches x with ⟨_h41, h43⟩
  cases L with
  | P => exact h43.1
  | Q => exact h43.2.1
  | R => exact h43.2.2.1
  | S => exact h43.2.2.2

theorem localPrime_avoids_exceptional
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 41 ∧ p ≠ 43 := by
  have hpBranch : p ∣ branchValue L x :=
    prime_dvd_factor_of_exactPrimePowerCofactor hlocal.2.2.1
  refine ⟨hlocal.2.1, ?_, ?_, ?_⟩
  · rintro rfl
    exact three_not_dvd_branchValue L x hpBranch
  · rintro rfl
    exact fortyOne_not_dvd_branchValue L x hpBranch
  · rintro rfl
    exact fortyThree_not_dvd_branchValue L x hpBranch

theorem localPrime_not_dvd_branchSlope
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    ¬p ∣ branchSlope L := by
  intro hpSlope
  have hpValue : p ∣ branchValue L x :=
    prime_dvd_factor_of_exactPrimePowerCofactor hlocal.2.2.1
  have hpProduct : p ∣ branchSlope L * x := dvd_mul_of_dvd_left hpSlope x
  have hpOffset : p ∣ branchOffset L := by
    rw [branchValue_eq_slope_mul_add] at hpValue
    exact (Nat.dvd_add_iff_right hpProduct).mpr hpValue
  cases L with
  | P =>
      have hpEq : p = 11 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp
            (by simpa [branchOffset] using hpOffset) with hpOne | hpEq
        · exact (hlocal.1.ne_one hpOne).elim
        · exact hpEq
      subst p
      norm_num [branchSlope] at hpSlope
  | Q =>
      have hpEq : p = 13 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp
            (by simpa [branchOffset] using hpOffset) with hpOne | hpEq
        · exact (hlocal.1.ne_one hpOne).elim
        · exact hpEq
      subst p
      norm_num [branchSlope] at hpSlope
  | R =>
      have hpEq : p = 5 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp
            (by simpa [branchOffset] using hpOffset) with hpOne | hpEq
        · exact (hlocal.1.ne_one hpOne).elim
        · exact hpEq
      subst p
      norm_num [branchSlope] at hpSlope
  | S =>
      have hpEq : p = 19 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 19)).mp
            (by simpa [branchOffset] using hpOffset) with hpOne | hpEq
        · exact (hlocal.1.ne_one hpOne).elim
        · exact hpEq
      subst p
      norm_num [branchSlope] at hpSlope

theorem localPrimePow_coprime_branchSlope
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    Nat.Coprime (p ^ a) (branchSlope L) := by
  exact (hlocal.1.coprime_iff_not_dvd.mpr
    (localPrime_not_dvd_branchSlope hlocal)).pow_left a

/-- Divisibility by the same exact prime power confines two local events to
one parameter residue class. -/
theorem localBranchRoots_modEq
    {L : Branch} {x y p a d e : ℕ}
    (hx : LocalBranchObstruction L x p a d)
    (hy : LocalBranchObstruction L y p a e) :
    x ≡ y [MOD p ^ a] := by
  have hxDiv : p ^ a ∣ branchValue L x :=
    ⟨d, hx.2.2.1.2.1⟩
  have hyDiv : p ^ a ∣ branchValue L y :=
    ⟨e, hy.2.2.1.2.1⟩
  have hvalues : branchValue L x ≡ branchValue L y [MOD p ^ a] :=
    hxDiv.modEq_zero_nat.trans hyDiv.modEq_zero_nat.symm
  rw [branchValue_eq_slope_mul_add, branchValue_eq_slope_mul_add] at hvalues
  have hmul : branchSlope L * x ≡ branchSlope L * y [MOD p ^ a] :=
    (Nat.ModEq.refl (branchOffset L)).add_right_cancel hvalues
  exact Nat.ModEq.cancel_left_of_coprime
    (localPrimePow_coprime_branchSlope hx).gcd_eq_one hmul

/-- The least nonnegative representative of a witnessed root is again a
root of the branch congruence. -/
theorem branchValue_mod_pow_dvd
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    p ^ a ∣ branchValue L (x % p ^ a) := by
  have hxDiv : p ^ a ∣ branchValue L x :=
    ⟨d, hlocal.2.2.1.2.1⟩
  have hroot : branchValue L (x % p ^ a) ≡
      branchValue L x [MOD p ^ a] := by
    rw [branchValue_eq_slope_mul_add, branchValue_eq_slope_mul_add]
    exact (Nat.mod_modEq x (p ^ a)).mul_left (branchSlope L) |>.add
      (Nat.ModEq.refl (branchOffset L))
  exact Nat.modEq_zero_iff_dvd.mp
    (hroot.trans hxDiv.modEq_zero_nat)

/-! ## The natural branch tests are the four integral obstruction maps -/

theorem localCofactor_pos
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) : 0 < d := by
  have hbranchPos : 0 < branchValue L x := by
    cases L with
    | P => simpa [branchValue] using (branches_positive x).1
    | Q => simpa [branchValue] using (branches_positive x).2.1
    | R => simpa [branchValue] using (branches_positive x).2.2.1
    | S => simpa [branchValue] using (branches_positive x).2.2.2
  have hpPow : 0 < p ^ a := pow_pos hlocal.1.pos a
  have hfac := hlocal.2.2.1.2.1
  nlinarith

theorem branchTestValue_int_eq_phi
    {L : Branch} {x d : ℕ} (hd : 0 < d) :
    (branchTestValue L x d : ℤ) =
      match L with
      | .P => PhiP x d
      | .Q => PhiQ x d
      | .R => PhiR x d
      | .S => PhiS x d := by
  have hbranches := branch_casts x
  cases L with
  | P => simp [branchTestValue, PhiP, hbranches.2.1]
  | Q => simp [branchTestValue, PhiQ, hbranches.1]
  | R =>
      have hle : 1 ≤ 3 * d * S x := by
        have hS := (branches_positive x).2.2.2
        have hpos : 0 < 3 * d * S x := by positivity
        omega
      simp only [branchTestValue, PhiR]
      rw [Int.natCast_ediv]
      rw [Nat.cast_sub hle]
      simp [hbranches.2.2.2]
  | S =>
      have hle : 1 ≤ 3 * d * FullDensityCore.R x := by
        have hR := (branches_positive x).2.2.1
        have hpos : 0 < 3 * d * FullDensityCore.R x := by positivity
        omega
      simp only [branchTestValue, PhiS]
      rw [Int.natCast_ediv]
      rw [Nat.cast_sub hle]
      simp [hbranches.2.2.1]

/-! ## Exact specialization of equations (16)--(17) -/

def commonQuadraticCoefficient : ℤ := 3024 * Tz ^ 2

def branchUCoefficient : Branch → ℤ
  | .P => 144 * Tz
  | .Q => 84 * Tz
  | .R => 216 * Tz
  | .S => 84 * Tz

def branchResidualCoefficient : Branch → ℤ
  | .P => -246 * Tz
  | .Q => 246 * Tz
  | .R => 258 * Tz
  | .S => -258 * Tz

def branchResidualNat : Branch → ℕ
  | .P => 246 * T
  | .Q => 246 * T
  | .R => 258 * T
  | .S => 258 * T

theorem localPrime_not_dvd_branchResidualNat
    {L : Branch} {x p a d : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    ¬p ∣ branchResidualNat L := by
  intro hdiv
  have hsupp : p = 2 ∨ p = 3 ∨ p = 41 ∨ p = 43 := by
    apply prime_dvd_residual_support hlocal.1
    cases L with
    | P => exact Or.inl (by simpa [branchResidualNat] using hdiv)
    | Q => exact Or.inl (by simpa [branchResidualNat] using hdiv)
    | R => exact Or.inr (by simpa [branchResidualNat] using hdiv)
    | S => exact Or.inr (by simpa [branchResidualNat] using hdiv)
  rcases localPrime_avoids_exceptional hlocal with ⟨hp2, hp3, hp41, hp43⟩
  rcases hsupp with h | h | h | h
  · exact hp2 h
  · exact hp3 h
  · exact hp41 h
  · exact hp43 h

theorem branchResidualCoefficient_isUnit
    {L : Branch} {x p a d r : ℕ}
    (hlocal : LocalBranchObstruction L x p a d) :
    IsUnit (branchResidualCoefficient L : ZMod (p ^ r)) := by
  have hu := natCast_isUnit_zmod_primePow (j := r) hlocal.1
    (localPrime_not_dvd_branchResidualNat hlocal)
  cases L with
  | P => simpa [branchResidualCoefficient, branchResidualNat, Tz] using hu.neg
  | Q => simpa [branchResidualCoefficient, branchResidualNat, Tz] using hu
  | R => simpa [branchResidualCoefficient, branchResidualNat, Tz] using hu
  | S => simpa [branchResidualCoefficient, branchResidualNat, Tz] using hu.neg

def branchPadicQuadratic (p a : ℕ) : ℤ :=
  commonQuadraticCoefficient * (p ^ (a - 1) : ℕ)

def branchPadicLinear (L : Branch) (p a c₀ : ℕ) : ℤ :=
  (p ^ (a - 1) : ℕ) * (branchUCoefficient L * c₀)

/-- Exact integer polynomial for the test value on the root progression
selected by a base local event. -/
theorem branchTestValue_root_progression
    {L : Branch} {x₀ x p a d₀ d : ℕ}
    (h₀ : LocalBranchObstruction L x₀ p a d₀)
    (h : LocalBranchObstruction L x p a d) :
    let q : ℕ := p ^ a
    let s : ℕ := x₀ % q
    let c₀ : ℕ := branchValue L s / q
    let k : ℕ := x / q
    (branchTestValue L x d : ℤ) =
      commonQuadraticCoefficient * q * k ^ 2 +
        ((q : ℤ) * (branchUCoefficient L * c₀) +
          branchResidualCoefficient L) * k +
        branchTestValue L s c₀ := by
  dsimp only
  let q : ℕ := p ^ a
  let s : ℕ := x₀ % q
  let c₀ : ℕ := branchValue L s / q
  let k : ℕ := x / q
  have hqPos : 0 < q := pow_pos h₀.1.pos a
  have hsDiv : q ∣ branchValue L s := by
    simpa [q, s] using branchValue_mod_pow_dvd h₀
  have hbase : q * c₀ = branchValue L s := by
    simpa [c₀] using Nat.mul_div_cancel' hsDiv
  have hmod : x ≡ x₀ [MOD q] := by
    simpa [q] using localBranchRoots_modEq h h₀
  have hrem : x % q = s := by
    simpa [s, Nat.ModEq] using hmod
  have hxProgression : x = s + q * k := by
    calc
      x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
      _ = s + q * k := by rw [hrem]; simp [k, Nat.add_comm]
  have hdProgression : d = c₀ + branchSlope L * k := by
    have hfactor := h.2.2.1.2.1
    apply Nat.mul_left_cancel hqPos
    calc
      q * d = branchValue L x := hfactor.symm
      _ = branchSlope L * (s + q * k) + branchOffset L := by
        rw [hxProgression, branchValue_eq_slope_mul_add]
      _ = q * (c₀ + branchSlope L * k) := by
        rw [branchValue_eq_slope_mul_add] at hbase
        calc
          branchSlope L * (s + q * k) + branchOffset L =
              (branchSlope L * s + branchOffset L) +
                branchSlope L * (q * k) := by ring
          _ = q * c₀ + branchSlope L * (q * k) := by rw [← hbase]
          _ = q * (c₀ + branchSlope L * k) := by ring
  have hc₀Pos : 0 < c₀ := by
    have hsPos : 0 < branchValue L s := by
      cases L with
      | P => simpa [branchValue] using (branches_positive s).1
      | Q => simpa [branchValue] using (branches_positive s).2.1
      | R => simpa [branchValue] using (branches_positive s).2.2.1
      | S => simpa [branchValue] using (branches_positive s).2.2.2
    nlinarith
  have htest := branchTestValue_int_eq_phi (L := L)
    (x := x) (d := d) (localCofactor_pos h)
  have htest₀ := branchTestValue_int_eq_phi (L := L)
    (x := s) (d := c₀) hc₀Pos
  change (branchTestValue L x d : ℤ) =
    commonQuadraticCoefficient * (q : ℤ) * (k : ℤ) ^ 2 +
      ((q : ℤ) * (branchUCoefficient L * (c₀ : ℤ)) +
        branchResidualCoefficient L) * (k : ℤ) +
      (branchTestValue L s c₀ : ℤ)
  cases L with
  | P =>
      have hbaseZ : (q : ℤ) * (c₀ : ℤ) = Pz s := by
        rw [(branch_casts s).1]
        exact_mod_cast hbase
      have hphi := PhiP_root_progression hbaseZ (k : ℤ)
      rw [htest, htest₀, hxProgression, hdProgression]
      simpa [commonQuadraticCoefficient, branchUCoefficient,
        branchResidualCoefficient, branchSlope, Tz_eq] using! hphi
  | Q =>
      have hbaseZ : (q : ℤ) * (c₀ : ℤ) = Qz s := by
        rw [(branch_casts s).2.1]
        exact_mod_cast hbase
      have hphi := PhiQ_root_progression hbaseZ (k : ℤ)
      rw [htest, htest₀, hxProgression, hdProgression]
      simpa [commonQuadraticCoefficient, branchUCoefficient,
        branchResidualCoefficient, branchSlope, Tz_eq] using! hphi
  | R =>
      have hbaseZ : (q : ℤ) * (c₀ : ℤ) = Rz s := by
        rw [(branch_casts s).2.2.1]
        exact_mod_cast hbase
      have hphi := PhiR_root_progression hbaseZ (k : ℤ)
      rw [htest, htest₀, hxProgression, hdProgression]
      simpa [commonQuadraticCoefficient, branchUCoefficient,
        branchResidualCoefficient, branchSlope, Tz_eq] using! hphi
  | S =>
      have hbaseZ : (q : ℤ) * (c₀ : ℤ) = Sz s := by
        rw [(branch_casts s).2.2.2]
        exact_mod_cast hbase
      have hphi := PhiS_root_progression hbaseZ (k : ℤ)
      rw [htest, htest₀, hxProgression, hdProgression]
      simpa [commonQuadraticCoefficient, branchUCoefficient,
        branchResidualCoefficient, branchSlope, Tz_eq] using! hphi

/-- Equation (16) in the exact `padicBranchMap` form used by the finite block
count.  It is valid at every output depth, including depth zero. -/
theorem branchTestValue_eq_padicBranchMap
    {L : Branch} {x₀ x p a d₀ d r : ℕ}
    (h₀ : LocalBranchObstruction L x₀ p a d₀)
    (h : LocalBranchObstruction L x p a d) :
    let q : ℕ := p ^ a
    let s : ℕ := x₀ % q
    let c₀ : ℕ := branchValue L s / q
    let k : ℕ := x / q
    (branchTestValue L x d : ZMod (p ^ r)) =
      padicBranchMap (p : ZMod (p ^ r))
        (branchPadicQuadratic p a : ZMod (p ^ r))
        (branchPadicLinear L p a c₀ : ZMod (p ^ r))
        (branchResidualCoefficient L : ZMod (p ^ r))
        (branchTestValue L s c₀ : ZMod (p ^ r))
        (k : ZMod (p ^ r)) := by
  dsimp only
  let q : ℕ := p ^ a
  let s : ℕ := x₀ % q
  let c₀ : ℕ := branchValue L s / q
  let k : ℕ := x / q
  have haPos : 0 < a := h₀.2.2.1.1
  have hpow : p ^ a = p * p ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    ring
  have hroot := branchTestValue_root_progression h₀ h
  have hcast := congrArg (fun z : ℤ ↦ (z : ZMod (p ^ r))) hroot
  push_cast at hcast
  have hxquot :
      (((x : ℤ) / (p : ℤ) ^ a : ℤ) : ZMod (p ^ r)) =
        ((x / p ^ a : ℕ) : ZMod (p ^ r)) := by
    calc
      _ = (((x / p ^ a : ℕ) : ℤ) : ZMod (p ^ r)) :=
        congrArg (fun z : ℤ ↦ (z : ZMod (p ^ r)))
          (by simpa using (Int.natCast_ediv x (p ^ a)).symm)
      _ = _ := Int.cast_natCast (R := ZMod (p ^ r)) _
  have hcquot :
      ((((branchValue L (x₀ % p ^ a) : ℕ) : ℤ) /
          (p : ℤ) ^ a : ℤ) : ZMod (p ^ r)) =
        ((branchValue L (x₀ % p ^ a) / p ^ a : ℕ) :
          ZMod (p ^ r)) := by
    calc
      _ = (((branchValue L (x₀ % p ^ a) / p ^ a : ℕ) : ℤ) :
          ZMod (p ^ r)) :=
        congrArg (fun z : ℤ ↦ (z : ZMod (p ^ r)))
          (by simpa using
            (Int.natCast_ediv (branchValue L (x₀ % p ^ a)) (p ^ a)).symm)
      _ = _ := Int.cast_natCast (R := ZMod (p ^ r)) _
  rw [hxquot, hcquot] at hcast
  have hquadratic :
      (p : ZMod (p ^ r)) *
          (branchPadicQuadratic p a : ZMod (p ^ r)) =
        (commonQuadraticCoefficient : ZMod (p ^ r)) * (p ^ a : ℕ) := by
    simp [branchPadicQuadratic, hpow]
    ring
  have hlinear :
      (p : ZMod (p ^ r)) *
          (branchPadicLinear L p a c₀ : ZMod (p ^ r)) =
        (p ^ a : ℕ) *
          ((branchUCoefficient L : ZMod (p ^ r)) * (c₀ : ℕ)) := by
    simp [branchPadicLinear, hpow]
    ring
  change (branchTestValue L x d : ZMod (p ^ r)) = _
  rw [padicBranchMap, hquadratic, hlinear]
  simpa [q, s, c₀, k] using hcast

theorem halfDigitCount_cast_div_eq_rho
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (halfDigitCount p : ℝ) / (p : ℝ) = higherPowerRho p := by
  have hpOdd : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).2 hp2
  have htwo : 2 ∣ p + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  unfold halfDigitCount higherPowerRho
  rw [Nat.cast_div_charZero htwo]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  push_cast
  ring

/-! ## Fixed branch/prime-power fibers -/

/-- Parameters in `[1,X]` carrying at least one local obstruction on the
fixed branch at the fixed exact prime power.  The cofactor is existentially
quantified here because it is forced by the exact factorization. -/
noncomputable def localHigherPowerFiber
    (X : ℕ) (L : Branch) (p a : ℕ) : Finset ℕ := by
  classical
  exact (parameterRange X).filter fun x ↦
    ∃ d, LocalBranchObstruction L x p a d

@[simp] theorem mem_localHigherPowerFiber
    {X x p a : ℕ} {L : Branch} :
    x ∈ localHigherPowerFiber X L p a ↔
      x ∈ parameterRange X ∧
        ∃ d, LocalBranchObstruction L x p a d := by
  classical
  simp [localHigherPowerFiber]

/-- Exact complete/padded-block bound for one nonempty local fiber.  The
depth is `log_p (X/p^a)`, and no positivity hypothesis is imposed on it;
when `X/p^a=0` the theorem retains the intended depth-zero estimate. -/
theorem localHigherPowerFiber_card_le_block
    {X p a : ℕ} {L : Branch} :
    (localHigherPowerFiber X L p a).card ≤
      (((X / p ^ a + 1) / p ^ higherPowerDepth p a X) + 1) *
        halfDigitCount p ^ higherPowerDepth p a X := by
  classical
  by_cases hempty : localHigherPowerFiber X L p a = ∅
  · simp [hempty]
  · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases mem_localHigherPowerFiber.mp hx₀ with ⟨_hx₀Range, d₀, h₀⟩
    let r : ℕ := higherPowerDepth p a X
    let q : ℕ := p ^ a
    let s : ℕ := x₀ % q
    let c₀ : ℕ := branchValue L s / q
    let A : Finset (ZMod (p ^ r)) := lowerHalfResidues p r
    let admissible : Finset ℕ :=
      (Finset.range (X / q + 1)).filter fun k ↦
        padicBranchMap (p : ZMod (p ^ r))
          (branchPadicQuadratic p a : ZMod (p ^ r))
          (branchPadicLinear L p a c₀ : ZMod (p ^ r))
          (branchResidualCoefficient L : ZMod (p ^ r))
          (branchTestValue L s c₀ : ZMod (p ^ r))
          (k : ZMod (p ^ r)) ∈ A
    have hmap : ∀ x ∈ localHigherPowerFiber X L p a,
        x / q ∈ admissible := by
      intro x hx
      rcases mem_localHigherPowerFiber.mp hx with ⟨hxRange, d, hlocal⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right
          (mem_parameterRange.mp hxRange).2)
      · have hdigit := natCast_mem_lowerHalfResidues (r := r)
          hlocal.1 hlocal.2.1 hlocal.2.2.2
        change padicBranchMap (p : ZMod (p ^ r))
            (branchPadicQuadratic p a : ZMod (p ^ r))
            (branchPadicLinear L p a c₀ : ZMod (p ^ r))
            (branchResidualCoefficient L : ZMod (p ^ r))
            (branchTestValue L s c₀ : ZMod (p ^ r))
            (x / q : ZMod (p ^ r)) ∈ A
        rw [← branchTestValue_eq_padicBranchMap h₀ hlocal]
        exact hdigit
    have hinj : Set.InjOn (fun x : ℕ ↦ x / q)
        (localHigherPowerFiber X L p a : Set ℕ) := by
      intro x hx y hy hdiv
      rcases mem_localHigherPowerFiber.mp hx with ⟨_hxRange, d, hxlocal⟩
      rcases mem_localHigherPowerFiber.mp hy with ⟨_hyRange, e, hylocal⟩
      change x / q = y / q at hdiv
      have hmod : x % q = y % q := by
        have hxy : x ≡ y [MOD q] := by
          simpa [q] using localBranchRoots_modEq hxlocal hylocal
        exact hxy
      calc
        x = q * (x / q) + x % q := (Nat.div_add_mod x q).symm
        _ = q * (y / q) + y % q := by rw [hdiv, hmod]
        _ = y := Nat.div_add_mod y q
    have hfiber : (localHigherPowerFiber X L p a).card ≤ admissible.card :=
      Finset.card_le_card_of_injOn (fun x : ℕ ↦ x / q) hmap hinj
    have hp3 : 3 ≤ p := by
      have hp2le := h₀.1.two_le
      have hpne2 := h₀.2.1
      omega
    have hblock : admissible.card ≤
        (((X / q + 1) / p ^ r) + 1) * halfDigitCount p ^ r := by
      have hcount := padicBranchAllowedCount_le h₀.1
        (branchPadicQuadratic p a : ZMod (p ^ r))
        (branchPadicLinear L p a c₀ : ZMod (p ^ r))
        (branchTestValue L s c₀ : ZMod (p ^ r))
        (branchResidualCoefficient_isUnit (r := r) h₀)
        A (lowerHalfResidues_card hp3)
        (start := 0) (N := X / q + 1)
      simpa [admissible, padicBranchAllowedCount, intervalResidueCount]
        using hcount
    simpa [q, r] using hfiber.trans hblock

/-- Root-class count used for the terminal regime `X < p^a`. -/
theorem localHigherPowerFiber_card_le_rootCount
    {X p a : ℕ} {L : Branch} :
    (localHigherPowerFiber X L p a).card ≤ X / p ^ a + 1 := by
  classical
  by_cases hempty : localHigherPowerFiber X L p a = ∅
  · simp [hempty]
  · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases mem_localHigherPowerFiber.mp hx₀ with ⟨_hx₀Range, d₀, h₀⟩
    apply Erdos730.TransitionDensity.card_le_div_add_one_of_modEq
      (v := x₀)
    · intro x hx
      exact (mem_parameterRange.mp
        (mem_localHigherPowerFiber.mp hx).1).2
    · intro x hx
      rcases mem_localHigherPowerFiber.mp hx with ⟨_hxRange, d, hlocal⟩
      exact localBranchRoots_modEq hlocal h₀

theorem localHigherPowerFiber_card_le_one_of_lt
    {X p a : ℕ} {L : Branch} (hXq : X < p ^ a) :
    (localHigherPowerFiber X L p a).card ≤ 1 := by
  have hzero : X / p ^ a = 0 := Nat.div_eq_of_lt hXq
  simpa [hzero] using
    (localHigherPowerFiber_card_le_rootCount (X := X) (p := p)
      (a := a) (L := L))

/-- All four affine branch values are at most the common terminal cutoff
`380827 X` on the parameter interval `[1,X]`. -/
theorem branchValue_le_higherPowerBranchHeight
    {X x : ℕ} (L : Branch) (hx : x ∈ parameterRange X) :
    branchValue L x ≤ higherPowerBranchHeight * X := by
  rcases mem_parameterRange.mp hx with ⟨hx1, hxX⟩
  rw [branchValue_eq_slope_mul_add]
  cases L <;>
    simp only [branchSlope, branchOffset, higherPowerBranchHeight] <;>
    omega

theorem localPrimePower_le_higherPowerBranchHeight
    {X x p a d : ℕ} {L : Branch}
    (hx : x ∈ parameterRange X)
    (hlocal : LocalBranchObstruction L x p a d) :
    p ^ a ≤ higherPowerBranchHeight * X := by
  have hq : p ^ a ≤ p ^ a * d :=
    Nat.le_mul_of_pos_right _ (localCofactor_pos hlocal)
  rw [← hlocal.2.2.1.2.1] at hq
  exact hq.trans (branchValue_le_higherPowerBranchHeight L hx)

/-- Adding one to the numerator can increase a natural quotient by at most
one.  This is the only floor estimate used in normalizing the block bound. -/
theorem succ_div_le_div_add_one (U P : ℕ) :
    (U + 1) / P ≤ U / P + 1 := by
  rw [Nat.succ_div]
  split <;> omega

/-- A total encoding of prime-power pairs into the shifted Tannery index.
On the actual prime-pair set the fallback branch is never used. -/
noncomputable def higherPowerPairIndex (pa : ℕ × ℕ) : HigherPowerIndex := by
  classical
  exact if hp : pa.1.Prime then (⟨pa.1, hp⟩, pa.2 - 2)
    else (⟨2, Nat.prime_two⟩, pa.2 - 2)

theorem higherPowerPairIndex_eq
    {p a : ℕ} (hp : p.Prime) :
    higherPowerPairIndex (p, a) = (⟨p, hp⟩, a - 2) := by
  simp [higherPowerPairIndex, hp]

theorem higherPowerPairIndex_injOn (Z : ℕ) :
    Set.InjOn higherPowerPairIndex (higherPrimePowerPairs Z : Set (ℕ × ℕ)) := by
  classical
  rintro ⟨p, a⟩ hpa ⟨q, b⟩ hqb heq
  rcases mem_higherPrimePowerPairs_iff.mp hpa with ⟨hp, ha2, _hpaZ⟩
  rcases mem_higherPrimePowerPairs_iff.mp hqb with ⟨hq, hb2, _hqbZ⟩
  simp only [higherPowerPairIndex, dif_pos hp, dif_pos hq] at heq
  obtain ⟨hpq, hab⟩ := Prod.mk.inj heq
  have hpq' : p = q := congrArg Subtype.val hpq
  subst q
  have : a = b := by omega
  subst b
  rfl

/-! ## Normalization against the Tannery envelope -/

/-- In the complete-block regime `p^a ≤ X`, one fixed fiber is bounded by
twice the normalized envelope.  The factor two is an explicit payment for
the two padded `+1` terms; no asymptotic notation is hidden here. -/
theorem localHigherPowerFiber_normalized_le_two_envelope
    {X p a : ℕ} {L : Branch}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha2 : 2 ≤ a)
    (hqX : p ^ a ≤ X) :
    ((localHigherPowerFiber X L p a).card : ℝ) / (X : ℝ) ≤
      2 * higherPowerEnvelope X (⟨p, hp⟩, a - 2) := by
  let q : ℕ := p ^ a
  let r : ℕ := higherPowerDepth p a X
  let P : ℕ := p ^ r
  let H : ℕ := halfDigitCount p
  let U : ℕ := X / q
  let D : ℕ := U / P
  let B : ℕ := (localHigherPowerFiber X L p a).card
  have hqPos : 0 < q := pow_pos hp.pos a
  have hXPos : 0 < X := hqPos.trans_le hqX
  have hUPos : 0 < U := by
    exact Nat.div_pos hqX hqPos
  have hPPos : 0 < P := pow_pos hp.pos r
  have hPleU : P ≤ U := by
    simpa [P, r] using! Nat.pow_log_le_self p hUPos.ne'
  have hDPos : 0 < D := Nat.div_pos hPleU hPPos
  have hcoeff : (U + 1) / P + 1 ≤ 4 * D := by
    have hsucc := succ_div_le_div_add_one U P
    omega
  have hblock : B ≤ ((U + 1) / P + 1) * H ^ r := by
    simpa [B, U, P, H, r, q] using
      (localHigherPowerFiber_card_le_block
        (X := X) (p := p) (a := a) (L := L))
  have hBgeom : B ≤ 4 * D * H ^ r :=
    hblock.trans (Nat.mul_le_mul_right (H ^ r) hcoeff)
  have hDP : D * P ≤ U := by
    simpa [D] using Nat.div_mul_le_self U P
  have hUq : U * q ≤ X := by
    simpa [U] using Nat.div_mul_le_self X q
  have hDPq : D * P * q ≤ X :=
    (Nat.mul_le_mul_right q hDP).trans hUq
  have hnat : B * q * P ≤ 4 * X * H ^ r := by
    calc
      B * q * P ≤ (4 * D * H ^ r) * q * P :=
        Nat.mul_le_mul_right P (Nat.mul_le_mul_right q hBgeom)
      _ = (4 * H ^ r) * (D * P * q) := by ring
      _ ≤ (4 * H ^ r) * X := Nat.mul_le_mul_left _ hDPq
      _ = 4 * X * H ^ r := by ring
  have hreal : (B : ℝ) * (q : ℝ) * (P : ℝ) ≤
      4 * (X : ℝ) * (H : ℝ) ^ r := by
    exact_mod_cast hnat
  have hratio : (B : ℝ) / (X : ℝ) ≤
      (4 * (H : ℝ) ^ r) / ((q : ℝ) * (P : ℝ)) := by
    apply (div_le_div_iff₀ (by exact_mod_cast hXPos)
      (mul_pos (by exact_mod_cast hqPos) (by exact_mod_cast hPPos))).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hreal
  calc
    ((localHigherPowerFiber X L p a).card : ℝ) / (X : ℝ) =
        (B : ℝ) / (X : ℝ) := by rfl
    _ ≤ (4 * (H : ℝ) ^ r) / ((q : ℝ) * (P : ℝ)) := hratio
    _ = 2 * higherPowerEnvelope X (⟨p, hp⟩, a - 2) := by
      have ha : a - 2 + 2 = a := by omega
      rw [higherPowerEnvelope, ha,
        ← halfDigitCount_cast_div_eq_rho hp hp2, div_pow]
      simp only [q, P, H, r, Nat.cast_pow]
      ring

/-- Uniform one-pair estimate.  If `p^a ≤ X` it uses the geometric block
bound; otherwise the unique root class costs one terminal payment.  The
prime `2` fiber is empty by the local-event definition. -/
theorem localHigherPowerFiber_normalized_le_pair_payment
    {X p a Z : ℕ} {L : Branch} (hX : 0 < X)
    (hpa : (p, a) ∈ higherPrimePowerPairs Z) :
    ((localHigherPowerFiber X L p a).card : ℝ) / (X : ℝ) ≤
      2 * higherPowerEnvelope X (higherPowerPairIndex (p, a)) +
        1 / (X : ℝ) := by
  rcases mem_higherPrimePowerPairs_iff.mp hpa with ⟨hp, ha2, _hpowZ⟩
  by_cases hp2 : p = 2
  · subst p
    have hempty : localHigherPowerFiber X L 2 a = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      rcases mem_localHigherPowerFiber.mp hx with ⟨_hx, d, hlocal⟩
      exact hlocal.2.1 rfl
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    exact add_nonneg
      (mul_nonneg (by norm_num) (higherPowerEnvelope_nonneg X _))
      (by positivity)
  · rw [higherPowerPairIndex_eq hp]
    by_cases hqX : p ^ a ≤ X
    · exact (localHigherPowerFiber_normalized_le_two_envelope
        hp hp2 ha2 hqX).trans (le_add_of_nonneg_right (by positivity))
    · have hterminal := localHigherPowerFiber_card_le_one_of_lt
          (L := L) (Nat.lt_of_not_ge hqX)
      have hcast : ((localHigherPowerFiber X L p a).card : ℝ) ≤ 1 := by
        exact_mod_cast hterminal
      have hdiv : ((localHigherPowerFiber X L p a).card : ℝ) /
          (X : ℝ) ≤ 1 / (X : ℝ) :=
        div_le_div_of_nonneg_right hcast (by positivity)
      exact hdiv.trans (le_add_of_nonneg_left
        (mul_nonneg (by positivity) (higherPowerEnvelope_nonneg X _)))

/-! ## The global higher-power witness ledger -/

abbrev HigherPowerKey := Σ _L : Branch, Σ _pa : ℕ × ℕ, ℕ

def higherPowerWitnessKey (w : LocalBranchWitness) : HigherPowerKey :=
  ⟨localWitnessBranch w,
    ⟨(localWitnessPrime w, localWitnessExponent w),
      localWitnessParameter w⟩⟩

noncomputable def higherPowerKeys (X : ℕ) : Finset HigherPowerKey :=
  (Finset.univ : Finset Branch).sigma fun L ↦
    (higherPrimePowerPairs (higherPowerBranchHeight * X)).sigma fun pa ↦
      localHigherPowerFiber X L pa.1 pa.2

theorem higherPowerWitnessKey_mapsTo (X : ℕ) :
    Set.MapsTo higherPowerWitnessKey
      (localHigherPowerWitnessesUpTo X : Set LocalBranchWitness)
      (higherPowerKeys X : Set HigherPowerKey) := by
  intro w hw
  have hhigh := Finset.mem_filter.mp hw
  have hlocal := mem_localBranchWitnessesUpTo.mp hhigh.1
  have hx : localWitnessParameter w ∈ parameterRange X :=
    (mem_witnessBox.mp hlocal.1).1
  change higherPowerWitnessKey w ∈ higherPowerKeys X
  rw [higherPowerKeys]
  simp only [higherPowerWitnessKey, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  constructor
  · apply mem_higherPrimePowerPairs_iff.mpr
    exact ⟨hlocal.2.1, hhigh.2,
      localPrimePower_le_higherPowerBranchHeight hx hlocal.2⟩
  · exact mem_localHigherPowerFiber.mpr
      ⟨hx, ⟨localWitnessCofactor w, hlocal.2⟩⟩

theorem higherPowerWitnessKey_injOn (X : ℕ) :
    Set.InjOn higherPowerWitnessKey
      (localHigherPowerWitnessesUpTo X : Set LocalBranchWitness) := by
  rintro ⟨L, x, p, a, d⟩ hw ⟨K, y, q, b, e⟩ hv hkey
  have hL : L = K := congrArg (fun z : HigherPowerKey ↦ z.1) hkey
  have hpa : (p, a) = (q, b) :=
    congrArg (fun z : HigherPowerKey ↦ z.2.1) hkey
  have hxy : x = y := congrArg (fun z : HigherPowerKey ↦ z.2.2) hkey
  subst K
  injection hpa with hpq hab
  subst q
  subst b
  subst y
  have hwd := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.2.2.1.2.1
  have hve := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hv).1).2.2.2.1.2.1
  change branchValue L x = p ^ a * d at hwd
  change branchValue L x = p ^ a * e at hve
  have hp : 0 < p := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp hw).1).2.1.pos
  have hde : d = e := by
    apply Nat.mul_left_cancel (pow_pos hp a)
    rw [← hwd, ← hve]
  subst e
  rfl

theorem localHigherPowerWitnesses_card_le_keys (X : ℕ) :
    (localHigherPowerWitnessesUpTo X).card ≤ (higherPowerKeys X).card :=
  Finset.card_le_card_of_injOn higherPowerWitnessKey
    (higherPowerWitnessKey_mapsTo X) (higherPowerWitnessKey_injOn X)

theorem higherPowerKeys_card (X : ℕ) :
    (higherPowerKeys X).card =
      ∑ L : Branch,
        ∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
          (localHigherPowerFiber X L pa.1 pa.2).card := by
  simp [higherPowerKeys, Finset.card_sigma]

theorem higherPowerPair_envelope_sum_le_tsum (X Z : ℕ) :
    (∑ pa ∈ higherPrimePowerPairs Z,
      higherPowerEnvelope X (higherPowerPairIndex pa)) ≤
        ∑' i : HigherPowerIndex, higherPowerEnvelope X i := by
  classical
  rw [← Finset.sum_image (f := higherPowerEnvelope X)
    (higherPowerPairIndex_injOn Z)]
  have hsum : Summable (higherPowerEnvelope X) :=
    higherPowerMajorant_summable.of_nonneg_of_le
      (higherPowerEnvelope_nonneg X)
      (higherPowerEnvelope_le_majorant X)
  exact hsum.sum_le_tsum _
    (fun i _hi ↦ higherPowerEnvelope_nonneg X i)

/-- The normalized sum of all prime-power fibers on one branch is bounded
by the doubled Tannery series plus one terminal payment per eligible pair. -/
theorem branchHigherPowerFiberSum_normalized_le
    (X : ℕ) (hX : 0 < X) (L : Branch) :
    ((∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
        (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) /
        (X : ℝ) ≤
      2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
        ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          (X : ℝ) := by
  classical
  let S := higherPrimePowerPairs (higherPowerBranchHeight * X)
  have hterm :
      ∑ pa ∈ S,
          ((localHigherPowerFiber X L pa.1 pa.2).card : ℝ) / (X : ℝ) ≤
        ∑ pa ∈ S,
          (2 * higherPowerEnvelope X (higherPowerPairIndex pa) +
            1 / (X : ℝ)) := by
    apply Finset.sum_le_sum
    intro pa hpa
    exact localHigherPowerFiber_normalized_le_pair_payment hX hpa
  have hfinite :
      (∑ pa ∈ S, higherPowerEnvelope X (higherPowerPairIndex pa)) ≤
        ∑' i : HigherPowerIndex, higherPowerEnvelope X i := by
    simpa [S] using higherPowerPair_envelope_sum_le_tsum X
      (higherPowerBranchHeight * X)
  calc
    ((∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
        (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) /
        (X : ℝ) =
        ∑ pa ∈ S,
          ((localHigherPowerFiber X L pa.1 pa.2).card : ℝ) / (X : ℝ) := by
      simp only [S, Nat.cast_sum, Finset.sum_div]
    _ ≤ ∑ pa ∈ S,
          (2 * higherPowerEnvelope X (higherPowerPairIndex pa) +
            1 / (X : ℝ)) := hterm
    _ = 2 * (∑ pa ∈ S,
          higherPowerEnvelope X (higherPowerPairIndex pa)) +
          (S.card : ℝ) / (X : ℝ) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
          (S.card : ℝ) / (X : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hfinite
        (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl
    _ = _ := by simp [S]

/-- Exact finite global domination of the higher-power local-witness range.
The outer factor four is the branch count; every other constant is displayed
in the preceding one-fiber lemmas. -/
theorem normalizedHigherPowerWitnessCount_le_majorant
    (X : ℕ) (hX : 0 < X) :
    Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount X ≤
      4 * (2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
        ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          (X : ℝ)) := by
  have hcardNat := localHigherPowerWitnesses_card_le_keys X
  rw [higherPowerKeys_card] at hcardNat
  have hcardReal : ((localHigherPowerWitnessesUpTo X).card : ℝ) ≤
      ((∑ L : Branch,
        ∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
          (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  unfold Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount
  calc
    ((localHigherPowerWitnessesUpTo X).card : ℝ) / (X : ℝ) ≤
        ((∑ L : Branch,
          ∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
            (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) /
          (X : ℝ) :=
      div_le_div_of_nonneg_right hcardReal (by positivity)
    _ = ∑ L : Branch,
        (((∑ pa ∈ higherPrimePowerPairs (higherPowerBranchHeight * X),
          (localHigherPowerFiber X L pa.1 pa.2).card : ℕ) : ℝ) /
            (X : ℝ)) := by
      simp only [Nat.cast_sum, Finset.sum_div]
    _ ≤ ∑ _L : Branch,
        (2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
          ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
            (X : ℝ)) := by
      apply Finset.sum_le_sum
      intro L _hL
      exact branchHigherPowerFiberSum_normalized_le X hX L
    _ = 4 * (2 * (∑' i : HigherPowerIndex, higherPowerEnvelope X i) +
        ((higherPrimePowerPairs (higherPowerBranchHeight * X)).card : ℝ) /
          (X : ℝ)) := by
      have hcard : Fintype.card Branch = 4 := by decide
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
      norm_num

/-- Unconditional closure of the concrete higher-prime-power range required
by `RangeAssembly`. -/
theorem tendsto_normalizedHigherPowerWitnessCount_zero :
    Tendsto Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall
      Erdos730.RangeAssembly.normalizedHigherPowerWitnessCount_nonneg
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    exact normalizedHigherPowerWitnessCount_le_majorant X hX
  · have hgeo := tendsto_tsum_higherPowerEnvelope_zero.const_mul 2
    have hsum := hgeo.add tendsto_higherPrimePowerPairs_scaled_card_div
    simpa only [mul_zero, zero_add] using hsum.const_mul 4

end Erdos730.HigherPowerEvents
