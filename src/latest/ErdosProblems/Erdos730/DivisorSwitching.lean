/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.BranchEvents
import ErdosProblems.Erdos730.PNTAP
import ErdosProblems.Erdos730.PrimeBands
import ErdosProblems.Erdos730.TransitionDensity
import ErdosProblems.Erdos730.RangeAssembly

/-!
# Erdős 730: top-range divisor switching

This module implements the top-prime classification and the ensuing
fixed-modulus divisor switch for the exact local branch events.
-/

open Filter Finset MeasureTheory
open scoped Topology Chebyshev

namespace Erdos730
namespace DivisorSwitching

open BranchEvents ConsecutiveTransition FullDensityCore KummerTransition
open FullDensity

noncomputable section

def globalBranchBound : ℕ := 380827

def topPrimeScale (X : ℝ) : ℝ :=
  Real.sqrt X * Real.log X ^ 2

def topPrimeCut (X : ℕ) : ℕ :=
  ⌊topPrimeScale X⌋₊

def branchSlope : Branch → ℕ
  | .P => 222138
  | .Q => 380808
  | .R => 148092
  | .S => 380808

def branchIntercept : Branch → ℕ
  | .P => 11
  | .Q => 13
  | .R => 5
  | .S => 19

theorem branchValue_eq_slope_mul_add (L : Branch) (x : ℕ) :
    branchValue L x = branchSlope L * x + branchIntercept L := by
  cases L <;> simp [branchValue, branchSlope, branchIntercept,
    branch_expansions]

theorem branchValue_le_globalBranchBound_mul
    {L : Branch} {x X : ℕ} (hX : 1 ≤ X) (hx : x ≤ X) :
    branchValue L x ≤ globalBranchBound * X := by
  rw [branchValue_eq_slope_mul_add]
  cases L <;> simp only [branchSlope, branchIntercept, globalBranchBound] <;>
    nlinarith

/-- Finite-threshold hypothesis needed by the top digit calculation. -/
def TopCutoffHypothesis (X : ℕ) : Prop :=
  130 * globalBranchBound * X < topPrimeCut X ^ 2

theorem top_ratio_and_square
    {L : Branch} {X x p c : ℕ}
    (hX : 1 ≤ X) (hx : x ≤ X)
    (hcut : TopCutoffHypothesis X)
    (hpCut : topPrimeCut X < p)
    (hbranch : branchValue L x = p * c) :
    130 * c < p ∧ branchValue L x < p ^ 2 := by
  have hL := branchValue_le_globalBranchBound_mul hX hx (L := L)
  have hpSq : topPrimeCut X ^ 2 < p ^ 2 := by nlinarith
  have h130L : 130 * branchValue L x < p ^ 2 := by
    calc
      130 * branchValue L x ≤ 130 * (globalBranchBound * X) :=
        Nat.mul_le_mul_left 130 hL
      _ < topPrimeCut X ^ 2 := by
        simpa [TopCutoffHypothesis, mul_assoc] using hcut
      _ < p ^ 2 := hpSq
  constructor
  · rw [hbranch] at h130L
    have hp0 : 0 < p := by omega
    nlinarith
  · exact (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 130)).trans_lt h130L

lemma cofactor_pos_of_exact_one {p c N : ℕ}
    (hp : p.Prime) (h : ExactPrimePowerCofactor p 1 c N) : 0 < c := by
  rcases h with ⟨_, hN, hpc⟩
  apply Nat.pos_of_ne_zero
  rintro rfl
  exact hpc (dvd_zero p)

lemma least_digit_lower_half
    {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : 0 < t) (hlow : LowerHalfDigits p t) :
    2 * (t % p) ≤ p - 1 := by
  have hdigit : t % p ∈ p.digits t := by
    rw [Nat.digits_eq_cons_digits_div hp.one_lt ht.ne']
    simp
  have h := hlow (t % p) hdigit
  have hpodd := hp.odd_of_ne_two hp2
  have hhalf := two_mul_paperHalf_add_one hpodd
  omega

lemma branchTestValue_pos
    {L : Branch} {x p c : ℕ}
    (hlocal : LocalBranchObstruction L x p 1 c) :
    0 < branchTestValue L x c := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hc := cofactor_pos_of_exact_one hp hexact
  cases L with
  | P =>
      simp only [branchTestValue]
      exact mul_pos hc (branches_positive x).2.1
  | Q =>
      simp only [branchTestValue]
      exact mul_pos hc (branches_positive x).1
  | R =>
      simp only [branchTestValue]
      have hS := (branches_positive x).2.2.2
      have hlarge : 2 < 3 * c * S x := by nlinarith
      omega
  | S =>
      simp only [branchTestValue]
      have hR := (branches_positive x).2.2.1
      have hlarge : 2 < 3 * c * FullDensityCore.R x := by nlinarith
      omega

lemma P_branch_test_cleared {x p c : ℕ}
    (hbranch : P x = p * c) :
    7 * branchTestValue .P x c + 41 * c = 12 * p * c ^ 2 := by
  simp only [branchTestValue]
  have hid := identity_PQ x
  nlinarith

lemma Q_branch_test_cleared {x p c : ℕ}
    (hbranch : Q x = p * c) :
    12 * branchTestValue .Q x c = 7 * p * c ^ 2 + 41 * c := by
  simp only [branchTestValue]
  have hid := identity_PQ x
  nlinarith

lemma R_branch_test_cleared {x p c : ℕ}
    (hbranch : FullDensityCore.R x = p * c) :
    14 * branchTestValue .R x c + 7 =
      54 * p * c ^ 2 + 129 * c := by
  simp only [branchTestValue]
  have hRodd : Odd (FullDensityCore.R x) := by
    refine ⟨14 * T * x + 2, ?_⟩
    simp only [FullDensityCore.R]
    ring
  have hcodd : Odd c := by
    have hprod : Odd (p * c) := hbranch ▸ hRodd
    exact (Nat.odd_mul.mp hprod).2
  have hSodd : Odd (FullDensityCore.S x) := by
    refine ⟨36 * T * x + 9, ?_⟩
    simp only [FullDensityCore.S]
    ring
  have hnum : 2 * ((3 * c * FullDensityCore.S x - 1) / 2) =
      3 * c * FullDensityCore.S x - 1 := by
    rcases hcodd with ⟨u, rfl⟩
    rcases hSodd with ⟨v, hv⟩
    rw [hv]
    have hprod : 3 * (2 * u + 1) * (2 * v + 1) =
        2 * (6 * u * v + 3 * u + 3 * v + 1) + 1 := by ring
    rw [hprod]
    simp
  have hcpos : 0 < c := by
    by_contra hc
    have : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    exact (Nat.ne_of_gt (branches_positive x).2.2.1) hbranch
  have hone : 2 * branchTestValue .R x c + 1 =
      3 * c * FullDensityCore.S x := by
    simp only [branchTestValue]
    have hpos : 0 < 3 * c * FullDensityCore.S x :=
      mul_pos (mul_pos (by norm_num) hcpos) (branches_positive x).2.2.2
    omega
  have hid := identity_RS x
  calc
    14 * branchTestValue .R x c + 7 =
        7 * (2 * branchTestValue .R x c + 1) := by ring
    _ = 7 * (3 * c * FullDensityCore.S x) := by rw [hone]
    _ = 3 * c * (7 * FullDensityCore.S x) := by ring
    _ = 3 * c * (18 * FullDensityCore.R x + 43) := by rw [hid]
    _ = 54 * p * c ^ 2 + 129 * c := by rw [hbranch]; ring

lemma S_branch_test_cleared {x p c : ℕ}
    (hbranch : FullDensityCore.S x = p * c) :
    12 * branchTestValue .S x c + 43 * c + 6 =
      7 * p * c ^ 2 := by
  simp only [branchTestValue]
  have hSodd : Odd (FullDensityCore.S x) := by
    refine ⟨36 * T * x + 9, ?_⟩
    simp only [FullDensityCore.S]
    ring
  have hcodd : Odd c := by
    have hprod : Odd (p * c) := hbranch ▸ hSodd
    exact (Nat.odd_mul.mp hprod).2
  have hRodd : Odd (FullDensityCore.R x) := by
    refine ⟨14 * T * x + 2, ?_⟩
    simp only [FullDensityCore.R]
    ring
  have hnum : 2 * ((3 * c * FullDensityCore.R x - 1) / 2) =
      3 * c * FullDensityCore.R x - 1 := by
    rcases hcodd with ⟨u, rfl⟩
    rcases hRodd with ⟨v, hv⟩
    rw [hv]
    have hprod : 3 * (2 * u + 1) * (2 * v + 1) =
        2 * (6 * u * v + 3 * u + 3 * v + 1) + 1 := by ring
    rw [hprod]
    simp
  have hcpos : 0 < c := by
    by_contra hc
    have : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    exact (Nat.ne_of_gt (branches_positive x).2.2.2) hbranch
  have hone : 2 * branchTestValue .S x c + 1 =
      3 * c * FullDensityCore.R x := by
    simp only [branchTestValue]
    have hpos : 0 < 3 * c * FullDensityCore.R x :=
      mul_pos (mul_pos (by norm_num) hcpos) (branches_positive x).2.2.1
    omega
  have hid := identity_RS x
  calc
    12 * branchTestValue .S x c + 43 * c + 6 =
        6 * (2 * branchTestValue .S x c + 1) + 43 * c := by ring
    _ = 6 * (3 * c * FullDensityCore.R x) + 43 * c := by
      rw [hone]
    _ = c * (18 * FullDensityCore.R x + 43) := by ring
    _ = c * (7 * FullDensityCore.S x) := by rw [hid]
    _ = 7 * p * c ^ 2 := by rw [hbranch]; ring

lemma coprime_mod_left {c m : ℕ} (hc : c.Coprime m) :
    (c % m).Coprime m := by
  rw [Nat.Coprime] at hc ⊢
  rw [Nat.gcd_comm] at hc
  rwa [Nat.gcd_rec] at hc

lemma P_branch_coprime_seven {x p c : ℕ}
    (hbranch : P x = p * c) : c.Coprime 7 := by
  have hPcop : (P x).Coprime 7 := by
    have hmod := (branch_mod_7_fixed x).1
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hmod]
    norm_num
  apply Nat.Coprime.coprime_dvd_left (m := c) (k := P x)
  · exact ⟨p, by rw [hbranch]; ring⟩
  · exact hPcop

lemma Q_branch_coprime_twelve {x p c : ℕ}
    (hbranch : Q x = p * c) : c.Coprime 12 := by
  have hQmod : Q x % 12 = 1 := by
    simp only [Q, T]
    omega
  have hQcop : (Q x).Coprime 12 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hQmod]
    norm_num
  apply Nat.Coprime.coprime_dvd_left (m := c) (k := Q x)
  · exact ⟨p, by rw [hbranch]; ring⟩
  · exact hQcop

lemma R_branch_coprime_fourteen {x p c : ℕ}
    (hbranch : FullDensityCore.R x = p * c) : c.Coprime 14 := by
  have hRmod : FullDensityCore.R x % 14 = 5 := by
    simp only [FullDensityCore.R, T]
    omega
  have hRcop : (FullDensityCore.R x).Coprime 14 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hRmod]
    norm_num
  apply Nat.Coprime.coprime_dvd_left (m := c)
      (k := FullDensityCore.R x)
  · exact ⟨p, by rw [hbranch]; ring⟩
  · exact hRcop

lemma S_branch_coprime_twelve {x p c : ℕ}
    (hbranch : FullDensityCore.S x = p * c) : c.Coprime 12 := by
  have hSmod : FullDensityCore.S x % 12 = 7 := by
    simp only [FullDensityCore.S, T]
    omega
  have hScop : (FullDensityCore.S x).Coprime 12 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hSmod]
    norm_num
  apply Nat.Coprime.coprime_dvd_left (m := c)
      (k := FullDensityCore.S x)
  · exact ⟨p, by rw [hbranch]; ring⟩
  · exact hScop

/-- Exact top classification on the P branch. -/
theorem P_top_local_classification
    {x p c : ℕ} (hlocal : LocalBranchObstruction .P x p 1 c)
    (hratio : 130 * c < p) : c % 7 = 3 ∨ c % 7 = 4 := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hbranch : P x = p * c := by
    simpa [branchValue] using hexact.2.1
  have hcpos := cofactor_pos_of_exact_one hp hexact
  let t := branchTestValue .P x c
  let d := t % p
  let k := t / p
  have htpos : 0 < t := branchTestValue_pos ⟨hp, hp2, hexact, hlow⟩
  have hhalf : 2 * d ≤ p - 1 :=
    least_digit_lower_half hp hp2 htpos hlow
  have hp0 : 0 < p := hp.pos
  have hdlt : d < p := Nat.mod_lt _ hp0
  have htdecomp : t = d + p * k := by
    simpa [d, k, add_comm] using (Nat.mod_add_div t p).symm
  have hclear := P_branch_test_cleared hbranch
  have hclearZ :
      (7 : ℤ) * t + 41 * c = 12 * p * (c : ℤ) ^ 2 := by
    exact_mod_cast hclear
  have hrdef :
      ((7 * d + 41 * c : ℕ) : ℤ) =
        (p : ℤ) * (12 * (c : ℤ) ^ 2 - 7 * (k : ℤ)) := by
    have htdecompZ : (t : ℤ) = d + p * k := by exact_mod_cast htdecomp
    rw [htdecompZ] at hclearZ
    push_cast at hclearZ ⊢
    linear_combination hclearZ
  let r : ℤ := 12 * (c : ℤ) ^ 2 - 7 * (k : ℤ)
  have hrEq : ((7 * d + 41 * c : ℕ) : ℤ) = (p : ℤ) * r := by
    simpa [r] using hrdef
  have hrpos : 0 < r := by
    have hleft : 0 < (7 * d + 41 * c : ℕ) := by omega
    push_cast at hleft
    nlinarith
  have hrlt : r < 4 := by
    have hhalf' : 2 * d + 1 ≤ p := by omega
    push_cast at hhalf' hratio
    nlinarith
  have hcop := coprime_mod_left (P_branch_coprime_seven hbranch)
  have hcnot : c % 7 ≠ 0 := by
    intro hc0
    rw [Nat.Coprime, hc0] at hcop
    norm_num at hcop
  have hcmodlt : c % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hrformula : r = 12 * (c : ℤ) ^ 2 - 7 * (k : ℤ) := rfl
  have hrcong : r ≡ 12 * (c : ℤ) ^ 2 [ZMOD 7] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(k : ℤ), ?_⟩
    rw [hrformula]
    ring
  have hccong : (c : ℤ) ≡ ((c % 7 : ℕ) : ℤ) [ZMOD 7] := by
    exact_mod_cast (Nat.mod_modEq c 7).symm
  have hrsmallcong :
      r ≡ 12 * (((c % 7 : ℕ) : ℤ) ^ 2) [ZMOD 7] :=
    hrcong.trans ((hccong.pow 2).mul_left 12)
  interval_cases hcm : c % 7 <;>
    norm_num [Int.ModEq, hcm] at hrsmallcong ⊢ <;> omega

/-- The Q branch has no exponent-one local obstruction in the top range. -/
theorem Q_top_local_impossible
    {x p c : ℕ} (hlocal : LocalBranchObstruction .Q x p 1 c)
    (hratio : 130 * c < p) : False := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hbranch : Q x = p * c := by
    simpa [branchValue] using hexact.2.1
  have hcpos := cofactor_pos_of_exact_one hp hexact
  let t := branchTestValue .Q x c
  let d := t % p
  let k := t / p
  have htpos : 0 < t := branchTestValue_pos ⟨hp, hp2, hexact, hlow⟩
  have hhalf : 2 * d ≤ p - 1 :=
    least_digit_lower_half hp hp2 htpos hlow
  have hp0 : 0 < p := hp.pos
  have htdecomp : t = d + p * k := by
    simpa [d, k, add_comm] using (Nat.mod_add_div t p).symm
  have hclear := Q_branch_test_cleared hbranch
  have hclearZ :
      (12 : ℤ) * t = 7 * p * (c : ℤ) ^ 2 + 41 * c := by
    exact_mod_cast hclear
  have hrdef :
      (12 : ℤ) * d - 41 * c =
        (p : ℤ) * (7 * (c : ℤ) ^ 2 - 12 * (k : ℤ)) := by
    have htdecompZ : (t : ℤ) = d + p * k := by exact_mod_cast htdecomp
    rw [htdecompZ] at hclearZ
    push_cast at hclearZ ⊢
    linear_combination hclearZ
  let r : ℤ := 7 * (c : ℤ) ^ 2 - 12 * (k : ℤ)
  have hrEq : (12 : ℤ) * d - 41 * c = (p : ℤ) * r := by
    simpa [r] using hrdef
  have hrnonneg : 0 ≤ r := by
    push_cast at hratio
    have hlower : -(p : ℤ) < (12 : ℤ) * d - 41 * c := by nlinarith
    nlinarith
  have hrlt : r < 6 := by
    have hhalf' : 2 * d + 1 ≤ p := by omega
    push_cast at hhalf' hratio
    nlinarith
  have hremod : r % 12 = r :=
    Int.emod_eq_of_lt hrnonneg (by omega)
  have hcop := coprime_mod_left (Q_branch_coprime_twelve hbranch)
  have hcmodlt : c % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hrformula : r = 7 * (c : ℤ) ^ 2 - 12 * (k : ℤ) := rfl
  have hrcong : r ≡ 7 * (c : ℤ) ^ 2 [ZMOD 12] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(k : ℤ), ?_⟩
    rw [hrformula]
    ring
  have hccong : (c : ℤ) ≡ ((c % 12 : ℕ) : ℤ) [ZMOD 12] := by
    exact_mod_cast (Nat.mod_modEq c 12).symm
  have hrsmallcong :
      r ≡ 7 * (((c % 12 : ℕ) : ℤ) ^ 2) [ZMOD 12] :=
    hrcong.trans ((hccong.pow 2).mul_left 7)
  interval_cases hcm : c % 12
  all_goals norm_num [Nat.Coprime, hcm] at hcop
  all_goals norm_num [Int.ModEq, hcm, hremod] at hrsmallcong
  all_goals omega

/-- Exact top classification on the R branch. -/
theorem R_top_local_classification
    {x p c : ℕ} (hlocal : LocalBranchObstruction .R x p 1 c)
    (hratio : 130 * c < p) : c % 14 = 5 ∨ c % 14 = 9 := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hbranch : FullDensityCore.R x = p * c := by
    simpa [branchValue] using hexact.2.1
  have hcpos := cofactor_pos_of_exact_one hp hexact
  let t := branchTestValue .R x c
  let d := t % p
  let k := t / p
  have htpos : 0 < t := branchTestValue_pos ⟨hp, hp2, hexact, hlow⟩
  have hhalf : 2 * d ≤ p - 1 :=
    least_digit_lower_half hp hp2 htpos hlow
  have hp0 : 0 < p := hp.pos
  have htdecomp : t = d + p * k := by
    simpa [d, k, add_comm] using (Nat.mod_add_div t p).symm
  have hclear := R_branch_test_cleared hbranch
  have hclearZ :
      (14 : ℤ) * t + 7 = 54 * p * (c : ℤ) ^ 2 + 129 * c := by
    exact_mod_cast hclear
  have hrdef :
      (14 : ℤ) * d + 7 - 129 * c =
        (p : ℤ) * (54 * (c : ℤ) ^ 2 - 14 * (k : ℤ)) := by
    have htdecompZ : (t : ℤ) = d + p * k := by exact_mod_cast htdecomp
    rw [htdecompZ] at hclearZ
    push_cast at hclearZ ⊢
    linear_combination hclearZ
  let r : ℤ := 54 * (c : ℤ) ^ 2 - 14 * (k : ℤ)
  have hrEq :
      (14 : ℤ) * d + 7 - 129 * c = (p : ℤ) * r := by
    simpa [r] using hrdef
  have hrnonneg : 0 ≤ r := by
    push_cast at hratio
    have hlower : -(p : ℤ) < (14 : ℤ) * d + 7 - 129 * c := by
      nlinarith
    nlinarith
  have hrlt : r < 7 := by
    have hhalf' : 2 * d + 1 ≤ p := by omega
    push_cast at hhalf' hratio
    nlinarith
  have hremod : r % 14 = r :=
    Int.emod_eq_of_lt hrnonneg (by omega)
  have hcop := coprime_mod_left (R_branch_coprime_fourteen hbranch)
  have hcmodlt : c % 14 < 14 := Nat.mod_lt _ (by norm_num)
  have hrformula : r = 54 * (c : ℤ) ^ 2 - 14 * (k : ℤ) := rfl
  have hrcong : r ≡ 54 * (c : ℤ) ^ 2 [ZMOD 14] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(k : ℤ), ?_⟩
    rw [hrformula]
    ring
  have hccong : (c : ℤ) ≡ ((c % 14 : ℕ) : ℤ) [ZMOD 14] := by
    exact_mod_cast (Nat.mod_modEq c 14).symm
  have hrsmallcong :
      r ≡ 54 * (((c % 14 : ℕ) : ℤ) ^ 2) [ZMOD 14] :=
    hrcong.trans ((hccong.pow 2).mul_left 54)
  interval_cases hcm : c % 14
  all_goals norm_num [Nat.Coprime, hcm] at hcop
  all_goals norm_num [Int.ModEq, hcm, hremod] at hrsmallcong
  all_goals omega

/-- The S branch has no exponent-one local obstruction in the top range. -/
theorem S_top_local_impossible
    {x p c : ℕ} (hlocal : LocalBranchObstruction .S x p 1 c)
    (hratio : 130 * c < p) : False := by
  rcases hlocal with ⟨hp, hp2, hexact, hlow⟩
  have hbranch : FullDensityCore.S x = p * c := by
    simpa [branchValue] using hexact.2.1
  have hcpos := cofactor_pos_of_exact_one hp hexact
  let t := branchTestValue .S x c
  let d := t % p
  let k := t / p
  have htpos : 0 < t := branchTestValue_pos ⟨hp, hp2, hexact, hlow⟩
  have hhalf : 2 * d ≤ p - 1 :=
    least_digit_lower_half hp hp2 htpos hlow
  have hp0 : 0 < p := hp.pos
  have htdecomp : t = d + p * k := by
    simpa [d, k, add_comm] using (Nat.mod_add_div t p).symm
  have hclear := S_branch_test_cleared hbranch
  have hclearZ :
      (12 : ℤ) * t + 43 * c + 6 = 7 * p * (c : ℤ) ^ 2 := by
    exact_mod_cast hclear
  have hrdef :
      (12 : ℤ) * d + 43 * c + 6 =
        (p : ℤ) * (7 * (c : ℤ) ^ 2 - 12 * (k : ℤ)) := by
    have htdecompZ : (t : ℤ) = d + p * k := by exact_mod_cast htdecomp
    rw [htdecompZ] at hclearZ
    push_cast at hclearZ ⊢
    linear_combination hclearZ
  let r : ℤ := 7 * (c : ℤ) ^ 2 - 12 * (k : ℤ)
  have hrEq :
      (12 : ℤ) * d + 43 * c + 6 = (p : ℤ) * r := by
    simpa [r] using hrdef
  have hrpos : 0 < r := by
    push_cast at hcpos
    nlinarith
  have hrlt : r < 7 := by
    have hhalf' : 2 * d + 1 ≤ p := by omega
    have haux : 43 * c + 6 < p := by nlinarith
    push_cast at hhalf' haux
    nlinarith
  have hremod : r % 12 = r :=
    Int.emod_eq_of_lt (by omega) (by omega)
  have hcop := coprime_mod_left (S_branch_coprime_twelve hbranch)
  have hcmodlt : c % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hrformula : r = 7 * (c : ℤ) ^ 2 - 12 * (k : ℤ) := rfl
  have hrcong : r ≡ 7 * (c : ℤ) ^ 2 [ZMOD 12] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(k : ℤ), ?_⟩
    rw [hrformula]
    ring
  have hccong : (c : ℤ) ≡ ((c % 12 : ℕ) : ℤ) [ZMOD 12] := by
    exact_mod_cast (Nat.mod_modEq c 12).symm
  have hrsmallcong :
      r ≡ 7 * (((c % 12 : ℕ) : ℤ) ^ 2) [ZMOD 12] :=
    hrcong.trans ((hccong.pow 2).mul_left 7)
  interval_cases hcm : c % 12
  all_goals norm_num [Nat.Coprime, hcm] at hcop
  all_goals norm_num [Int.ModEq, hcm, hremod] at hrsmallcong
  all_goals omega

/-! ## Exact p-first divisor switch -/

lemma P_prime_residue_of_cofactor
    {x p c : ℕ} (hbranch : P x = p * c)
    (hc : c % 7 = 3 ∨ c % 7 = 4) :
    p % 7 = 1 ∨ p % 7 = 6 := by
  have hPmod := (branch_mod_7_fixed x).1
  have hprod : (p % 7) * (c % 7) % 7 = 4 := by
    rw [← Nat.mul_mod, ← hbranch]
    exact hPmod
  have hpmodlt : p % 7 < 7 := Nat.mod_lt _ (by norm_num)
  rcases hc with hc | hc
  · interval_cases hpm : p % 7
    all_goals norm_num [hc, hpm] at hprod
    all_goals norm_num [hpm]
  · interval_cases hpm : p % 7
    all_goals norm_num [hc, hpm] at hprod
    all_goals norm_num [hpm]

lemma R_prime_residue_of_cofactor
    {x p c : ℕ} (hbranch : FullDensityCore.R x = p * c)
    (hc : c % 14 = 5 ∨ c % 14 = 9) :
    p % 14 = 1 ∨ p % 14 = 13 := by
  have hRmod : FullDensityCore.R x % 14 = 5 := by
    simp only [FullDensityCore.R, T]
    omega
  have hprod : (p % 14) * (c % 14) % 14 = 5 := by
    rw [← Nat.mul_mod, ← hbranch]
    exact hRmod
  have hpmodlt : p % 14 < 14 := Nat.mod_lt _ (by norm_num)
  rcases hc with hc | hc
  · interval_cases hpm : p % 14
    all_goals norm_num [hc, hpm] at hprod
    all_goals norm_num [hpm]
  · interval_cases hpm : p % 14
    all_goals norm_num [hc, hpm] at hprod
    all_goals norm_num [hpm]

/-- The exact top witnesses on one branch. -/
noncomputable def topBranchWitnessesUpTo (L : Branch) (X : ℕ) :
    Finset LocalBranchWitness :=
  (localTopPrimeWitnessesUpTo X (topPrimeCut X)).filter fun w =>
    localWitnessBranch w = L

/-- Allowed top primes on the P branch, enlarged only by the common exact
linear height bound. -/
noncomputable def PTopPrimeSet (X : ℕ) : Finset ℕ :=
  (Ioc (topPrimeCut X) (globalBranchBound * X)).filter fun p =>
    p.Prime ∧ (p % 7 = 1 ∨ p % 7 = 6)

/-- Allowed top primes on the R branch. -/
noncomputable def RTopPrimeSet (X : ℕ) : Finset ℕ :=
  (Ioc (topPrimeCut X) (globalBranchBound * X)).filter fun p =>
    p.Prime ∧ (p % 14 = 1 ∨ p % 14 = 13)

abbrev PrimeParameterKey := Σ _p : ℕ, ℕ

def topWitnessKey (w : LocalBranchWitness) : PrimeParameterKey :=
  ⟨localWitnessPrime w, localWitnessParameter w⟩

noncomputable def topBranchKeys
    (L : Branch) (primes : Finset ℕ) (X : ℕ) : Finset PrimeParameterKey :=
  primes.sigma fun p =>
    TransitionDensity.branchDivisibilityParameters L p X

theorem topWitnessKey_injOn (L : Branch) (X : ℕ) :
    Set.InjOn topWitnessKey (topBranchWitnessesUpTo L X :
      Set LocalBranchWitness) := by
  rintro ⟨K, x, p, a, d⟩ hw ⟨M, y, q, b, e⟩ hv hkey
  have hK := (Finset.mem_filter.mp hw).2
  have hM := (Finset.mem_filter.mp hv).2
  change K = L at hK
  change M = L at hM
  subst K
  subst M
  simp only [topWitnessKey, localWitnessPrime, localWitnessParameter,
    Sigma.mk.injEq] at hkey
  rcases hkey with ⟨rfl, rfl⟩
  have hwa := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hw).1).2.1
  have hvb := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hv).1).2.1
  change a = 1 at hwa
  change b = 1 at hvb
  subst a
  subst b
  have hwd := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1).2.2.2.1.2.1
  have hve := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1).2.2.2.1.2.1
  change branchValue L x = p ^ 1 * d at hwd
  change branchValue L x = p ^ 1 * e at hve
  have hp : 0 < p := (mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1).2.1.pos
  have hde : d = e := by
    apply Nat.mul_left_cancel (pow_pos hp 1)
    rw [← hwd, ← hve]
  subst e
  rfl

lemma top_witness_prime_le
    {L : Branch} {X : ℕ} {w : LocalBranchWitness}
    (hX : 1 ≤ X) (hw : w ∈ topBranchWitnessesUpTo L X) :
    localWitnessPrime w ≤ globalBranchBound * X := by
  have hwlocal := mem_localBranchWitnessesUpTo.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  have ha := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2.1
  change localWitnessExponent w = 1 at ha
  have hbranch := hwlocal.2.2.2.1.2.1
  have hexact := hwlocal.2.2.2.1
  rw [ha] at hexact
  have hcpos := cofactor_pos_of_exact_one hwlocal.2.1 hexact
  have hp_le : localWitnessPrime w ≤ branchValue (localWitnessBranch w)
      (localWitnessParameter w) := by
    rw [hbranch, ha, pow_one]
    exact Nat.le_mul_of_pos_right (localWitnessPrime w) hcpos
  have hx := (DensityEvents.mem_witnessBox.mp hwlocal.1).1
  have htag := (Finset.mem_filter.mp hw).2
  change localWitnessBranch w = L at htag
  rw [htag] at hp_le
  exact hp_le.trans (branchValue_le_globalBranchBound_mul hX
    (DensityEvents.mem_parameterRange.mp hx).2)

theorem P_topWitnessKey_mapsTo
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X) :
    Set.MapsTo topWitnessKey (topBranchWitnessesUpTo .P X :
      Set LocalBranchWitness) (topBranchKeys .P (PTopPrimeSet X) X :
        Set PrimeParameterKey) := by
  intro w hw
  change topWitnessKey w ∈ topBranchKeys .P (PTopPrimeSet X) X
  have htop := Finset.mem_filter.mp hw
  have hlocalMem := Finset.mem_filter.mp htop.1
  have hlocal := (mem_localBranchWitnessesUpTo.mp hlocalMem.1).2
  have htag := htop.2
  change localWitnessBranch w = Branch.P at htag
  have ha := hlocalMem.2.1
  change localWitnessExponent w = 1 at ha
  have hpCut := hlocalMem.2.2
  have hxRange := (DensityEvents.mem_witnessBox.mp
    (mem_localBranchWitnessesUpTo.mp hlocalMem.1).1).1
  have hexact := hlocal.2.2.1
  have hbranch := hexact.2.1
  have hbranch1 : branchValue .P (localWitnessParameter w) =
      localWitnessPrime w * localWitnessCofactor w := by
    simpa [htag, ha] using hbranch
  have hratio := (top_ratio_and_square hX
    (DensityEvents.mem_parameterRange.mp hxRange).2 hcut hpCut hbranch1).1
  have hlocalP : LocalBranchObstruction .P
      (localWitnessParameter w) (localWitnessPrime w) 1
      (localWitnessCofactor w) := by
    simpa [htag, ha] using hlocal
  have hc := P_top_local_classification hlocalP hratio
  have hpResidue : localWitnessPrime w % 7 = 1 ∨
      localWitnessPrime w % 7 = 6 := by
    apply P_prime_residue_of_cofactor
      (x := localWitnessParameter w)
      (c := localWitnessCofactor w)
    · simpa [branchValue] using hbranch1
    · exact hc
  rw [topBranchKeys]
  simp only [topWitnessKey, Finset.mem_sigma]
  constructor
  · rw [PTopPrimeSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hpCut, top_witness_prime_le hX hw⟩, hlocal.1, hpResidue⟩
  · rw [TransitionDensity.branchDivisibilityParameters,
      Finset.mem_filter]
    exact ⟨hxRange,
      ⟨localWitnessCofactor w, by rw [hbranch1]⟩⟩

theorem R_topWitnessKey_mapsTo
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X) :
    Set.MapsTo topWitnessKey (topBranchWitnessesUpTo .R X :
      Set LocalBranchWitness) (topBranchKeys .R (RTopPrimeSet X) X :
        Set PrimeParameterKey) := by
  intro w hw
  change topWitnessKey w ∈ topBranchKeys .R (RTopPrimeSet X) X
  have htop := Finset.mem_filter.mp hw
  have hlocalMem := Finset.mem_filter.mp htop.1
  have hlocal := (mem_localBranchWitnessesUpTo.mp hlocalMem.1).2
  have htag := htop.2
  change localWitnessBranch w = Branch.R at htag
  have ha := hlocalMem.2.1
  change localWitnessExponent w = 1 at ha
  have hpCut := hlocalMem.2.2
  have hxRange := (DensityEvents.mem_witnessBox.mp
    (mem_localBranchWitnessesUpTo.mp hlocalMem.1).1).1
  have hexact := hlocal.2.2.1
  have hbranch := hexact.2.1
  have hbranch1 : branchValue .R (localWitnessParameter w) =
      localWitnessPrime w * localWitnessCofactor w := by
    simpa [htag, ha] using hbranch
  have hratio := (top_ratio_and_square hX
    (DensityEvents.mem_parameterRange.mp hxRange).2 hcut hpCut hbranch1).1
  have hlocalR : LocalBranchObstruction .R
      (localWitnessParameter w) (localWitnessPrime w) 1
      (localWitnessCofactor w) := by
    simpa [htag, ha] using hlocal
  have hc := R_top_local_classification hlocalR hratio
  have hpResidue : localWitnessPrime w % 14 = 1 ∨
      localWitnessPrime w % 14 = 13 := by
    apply R_prime_residue_of_cofactor
      (x := localWitnessParameter w)
      (c := localWitnessCofactor w)
    · simpa [branchValue] using hbranch1
    · exact hc
  rw [topBranchKeys]
  simp only [topWitnessKey, Finset.mem_sigma]
  constructor
  · rw [RTopPrimeSet, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hpCut, top_witness_prime_le hX hw⟩, hlocal.1, hpResidue⟩
  · rw [TransitionDensity.branchDivisibilityParameters,
      Finset.mem_filter]
    exact ⟨hxRange,
      ⟨localWitnessCofactor w, by rw [hbranch1]⟩⟩

theorem Q_topBranchWitnesses_eq_empty
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X) :
    topBranchWitnessesUpTo .Q X = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨w, hw⟩
  have htop := Finset.mem_filter.mp hw
  have hlocalMem := Finset.mem_filter.mp htop.1
  have hlocal := (mem_localBranchWitnessesUpTo.mp hlocalMem.1).2
  have htag := htop.2
  change localWitnessBranch w = Branch.Q at htag
  have ha := hlocalMem.2.1
  change localWitnessExponent w = 1 at ha
  have hpCut := hlocalMem.2.2
  have hxRange := (DensityEvents.mem_witnessBox.mp
    (mem_localBranchWitnessesUpTo.mp hlocalMem.1).1).1
  have hbranch : branchValue .Q (localWitnessParameter w) =
      localWitnessPrime w * localWitnessCofactor w := by
    simpa [htag, ha] using hlocal.2.2.1.2.1
  have hratio := (top_ratio_and_square hX
    (DensityEvents.mem_parameterRange.mp hxRange).2 hcut hpCut hbranch).1
  apply Q_top_local_impossible (p := localWitnessPrime w)
    (c := localWitnessCofactor w) (x := localWitnessParameter w)
    (hratio := hratio)
  simpa [htag, ha] using hlocal

theorem S_topBranchWitnesses_eq_empty
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X) :
    topBranchWitnessesUpTo .S X = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨w, hw⟩
  have htop := Finset.mem_filter.mp hw
  have hlocalMem := Finset.mem_filter.mp htop.1
  have hlocal := (mem_localBranchWitnessesUpTo.mp hlocalMem.1).2
  have htag := htop.2
  change localWitnessBranch w = Branch.S at htag
  have ha := hlocalMem.2.1
  change localWitnessExponent w = 1 at ha
  have hpCut := hlocalMem.2.2
  have hxRange := (DensityEvents.mem_witnessBox.mp
    (mem_localBranchWitnessesUpTo.mp hlocalMem.1).1).1
  have hbranch : branchValue .S (localWitnessParameter w) =
      localWitnessPrime w * localWitnessCofactor w := by
    simpa [htag, ha] using hlocal.2.2.1.2.1
  have hratio := (top_ratio_and_square hX
    (DensityEvents.mem_parameterRange.mp hxRange).2 hcut hpCut hbranch).1
  apply S_top_local_impossible (p := localWitnessPrime w)
    (c := localWitnessCofactor w) (x := localWitnessParameter w)
    (hratio := hratio)
  simpa [htag, ha] using hlocal

theorem P_topBranchWitnesses_card_le_sum
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X)
    (hlarge : 380808 ≤ topPrimeCut X) :
    (topBranchWitnessesUpTo .P X).card ≤
      ∑ p ∈ PTopPrimeSet X, (X / p + 1) := by
  calc
    _ ≤ (topBranchKeys .P (PTopPrimeSet X) X).card :=
      Finset.card_le_card_of_injOn topWitnessKey
        (P_topWitnessKey_mapsTo X hX hcut) (topWitnessKey_injOn .P X)
    _ = ∑ p ∈ PTopPrimeSet X,
        (TransitionDensity.branchDivisibilityParameters .P p X).card := by
      simp [topBranchKeys, Finset.card_sigma]
    _ ≤ ∑ p ∈ PTopPrimeSet X, (X / p + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.1
      have hpCut := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      apply TransitionDensity.branchDivisibilityParameters_card_le hp'
      have hslope := TransitionDensity.branchSlope_le_max Branch.P
      omega

theorem R_topBranchWitnesses_card_le_sum
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X)
    (hlarge : 380808 ≤ topPrimeCut X) :
    (topBranchWitnessesUpTo .R X).card ≤
      ∑ p ∈ RTopPrimeSet X, (X / p + 1) := by
  calc
    _ ≤ (topBranchKeys .R (RTopPrimeSet X) X).card :=
      Finset.card_le_card_of_injOn topWitnessKey
        (R_topWitnessKey_mapsTo X hX hcut) (topWitnessKey_injOn .R X)
    _ = ∑ p ∈ RTopPrimeSet X,
        (TransitionDensity.branchDivisibilityParameters .R p X).card := by
      simp [topBranchKeys, Finset.card_sigma]
    _ ≤ ∑ p ∈ RTopPrimeSet X, (X / p + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2.1
      have hpCut := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
      apply TransitionDensity.branchDivisibilityParameters_card_le hp'
      have hslope := TransitionDensity.branchSlope_le_max Branch.R
      omega

theorem topWitnesses_card_eq_sum_branches (X : ℕ) :
    (localTopPrimeWitnessesUpTo X (topPrimeCut X)).card =
      ∑ L : Branch, (topBranchWitnessesUpTo L X).card := by
  classical
  unfold topBranchWitnessesUpTo
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Exact finite divisor-switch bound for all four branches. -/
theorem topWitnesses_card_le_allowed_sums
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X)
    (hlarge : 380808 ≤ topPrimeCut X) :
    (localTopPrimeWitnessesUpTo X (topPrimeCut X)).card ≤
      (∑ p ∈ PTopPrimeSet X, (X / p + 1)) +
        ∑ p ∈ RTopPrimeSet X, (X / p + 1) := by
  rw [topWitnesses_card_eq_sum_branches]
  let pSum := ∑ p ∈ PTopPrimeSet X, (X / p + 1)
  let rSum := ∑ p ∈ RTopPrimeSet X, (X / p + 1)
  calc
    ∑ L : Branch, (topBranchWitnessesUpTo L X).card ≤
        ∑ L : Branch, match L with
          | .P => pSum
          | .Q => 0
          | .R => rSum
          | .S => 0 := by
      apply Finset.sum_le_sum
      intro L _
      cases L with
      | P => exact P_topBranchWitnesses_card_le_sum X hX hcut hlarge
      | Q => rw [Q_topBranchWitnesses_eq_empty X hX hcut]; simp
      | R => exact R_topBranchWitnesses_card_le_sum X hX hcut hlarge
      | S => rw [S_topBranchWitnesses_eq_empty X hX hcut]; simp
    _ = pSum + rSum := by
      have huniv : (Finset.univ : Finset Branch) =
          {.P, .Q, .R, .S} := by decide
      rw [huniv]
      simp
    _ = _ := rfl

/-! ## Reciprocal primes in one fixed arithmetic progression -/

/-- Reciprocal-prime partial sum in the exact class `a mod A`, with a real
cutoff and the same floor convention as `primeAPCountingReal`. -/
noncomputable def reciprocalPrimeAPSumReal (A a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ apPrimes A a x, (p : ℝ)⁻¹

/-- Abel summation for reciprocal primes in one arithmetic progression. -/
theorem reciprocalPrimeAPSumReal_eq_count_div_add_integral
    (A a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    reciprocalPrimeAPSumReal A a x =
      primeAPCountingReal A a x / x +
        ∫ t in (2 : ℝ)..x, primeAPCountingReal A a t / t ^ 2 := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun y : ℝ => y⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (zero_lt_two.trans_le ht.1))
  have hint : IntegrableOn (deriv fun y : ℝ => y⁻¹)
      (Set.Icc (2 : ℝ) x) := by
    rw [deriv_inv']
    refine ContinuousOn.integrableOn_Icc ?_
    exact ((continuous_id.pow 2).continuousOn.inv₀ fun t ht hzero =>
      (zero_lt_two.trans_le ht.1).ne' (eq_zero_of_pow_eq_zero hzero)).neg
  rw [reciprocalPrimeAPSumReal, apPrimes, Finset.sum_filter]
  let b : ℕ → ℝ := Set.indicator
    {p : ℕ | p.Prime ∧ p % A = a} (fun _ => 1)
  trans ∑ k ∈ Icc 0 ⌊x⌋₊, (k : ℝ)⁻¹ * b k
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · simp [b, hk]
    · simp [b, hk]
  rw [sum_mul_eq_sub_integral_mul₁ b
      (by simp [b, Nat.not_prime_zero])
      (by simp [b, Nat.not_prime_one]) x hdiff hint,
    ← intervalIntegral.integral_of_le hx]
  have int_deriv (f : ℝ → ℝ) :
      ∫ u in (2 : ℝ)..x,
          deriv (fun y : ℝ => y⁻¹) u * f u =
        ∫ u in (2 : ℝ)..x, f u * -(u ^ 2)⁻¹ :=
    intervalIntegral.integral_congr fun u _ => by rw [deriv_inv']; ring
  rw [int_deriv]
  simp [b, Set.indicator_apply, Finset.sum_filter,
    primeAPCountingReal, div_eq_mul_inv]
  ring

lemma integrableOn_primeAPCountingReal_div_sq
    (A a : ℕ) (x : ℝ) :
    IntegrableOn (fun t => primeAPCountingReal A a t / t ^ 2)
      (Set.Icc 2 x) MeasureTheory.volume := by
  unfold primeAPCountingReal
  conv =>
    arg 1
    ext t
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  conv =>
    arg 1
    ext t
    rw [div_eq_mul_one_div, mul_comm]
  refine integrableOn_mul_sum_Icc
      (a := 2) (b := x) (m := 0)
      (fun p : ℕ => if p.Prime ∧ p % A = a then (1 : ℝ) else 0)
      (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
  have ht0 : t ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [ht.1])
  fun_prop (disch := assumption)

/-! ## Moving top-band endpoints -/

def topPrimeUpper (X : ℕ) : ℝ :=
  (globalBranchBound : ℝ) * (X : ℝ)

def topLogBand (X : ℕ) : ℝ :=
  Real.log (Real.log (topPrimeUpper X)) -
    Real.log (Real.log (topPrimeScale X))

theorem tendsto_topPrimeScale_atTop :
    Tendsto (fun X : ℕ => topPrimeScale X) atTop atTop := by
  simpa [topPrimeScale, FullDensity.transitionPrimeBandUpper] using
    TransitionDensity.tendsto_transitionPrimeBandUpper_nat_atTop

theorem tendsto_topPrimeUpper_atTop :
    Tendsto topPrimeUpper atTop atTop := by
  unfold topPrimeUpper
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (by
    norm_num [globalBranchBound])

private theorem tendsto_log_log_div_log_nat :
    Tendsto (fun X : ℕ =>
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ))
      atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun X : ℝ => Real.log (Real.log X) / Real.log X)
      atTop (𝓝 0) := by
    simpa using!
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        Real.tendsto_log_atTop
  exact hreal.comp tendsto_natCast_atTop_atTop

theorem tendsto_top_log_ratio :
    Tendsto (fun X : ℕ =>
      Real.log (topPrimeUpper X) / Real.log (topPrimeScale X))
      atTop (𝓝 2) := by
  have hinvLog : Tendsto (fun X : ℕ =>
      (Real.log (X : ℝ))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hnum : Tendsto (fun X : ℕ =>
      1 + Real.log (globalBranchBound : ℝ) / Real.log (X : ℝ))
      atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).add
        (hinvLog.const_mul (Real.log (globalBranchBound : ℝ)))
    simpa [div_eq_mul_inv] using h
  have hden : Tendsto (fun X : ℕ =>
      (1 / 2 : ℝ) +
        2 * (Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_log_log_div_log_nat.const_mul 2))
  have hquot := hnum.div hden (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hquot' : Tendsto (fun X : ℕ =>
      (1 + Real.log (globalBranchBound : ℝ) / Real.log (X : ℝ)) /
        ((1 / 2 : ℝ) +
          2 * (Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ))))
      atTop (𝓝 2) := by
    norm_num at hquot ⊢
    exact hquot
  apply hquot'.congr'
  filter_upwards [eventually_gt_atTop (Nat.ceil (Real.exp 1))] with X hX
  have hXreal : Real.exp 1 < (X : ℝ) := by
    exact (Nat.le_ceil (Real.exp 1)).trans_lt (by exact_mod_cast hX)
  have hX1 : 1 < (X : ℝ) := (by
    have : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr zero_lt_one
    exact this.trans hXreal)
  have hlogX : Real.log (X : ℝ) ≠ 0 := (Real.log_pos hX1).ne'
  have hscaleEq : Real.log (topPrimeScale X) =
      Real.log (X : ℝ) / 2 +
        2 * Real.log (Real.log (X : ℝ)) := by
    simpa [topPrimeScale, FullDensity.transitionPrimeBandUpper] using
      (FullDensity.log_transitionPrimeBandUpper hX1)
  have hscaleLog : Real.log (topPrimeScale X) ≠ 0 := by
    rw [hscaleEq]
    have hloglog : 0 < Real.log (Real.log (X : ℝ)) := by
      have : 1 < Real.log (X : ℝ) := by
        apply Real.exp_lt_exp.mp
        simpa [Real.exp_log (by positivity)] using hXreal
      exact Real.log_pos this
    positivity
  rw [topPrimeUpper, Real.log_mul (by norm_num [globalBranchBound])
    (by positivity), hscaleEq]
  field_simp
  ring

theorem tendsto_topLogBand :
    Tendsto topLogBand atTop (𝓝 (Real.log 2)) := by
  have hlogRatio := (tendsto_top_log_ratio.log (by norm_num : (2 : ℝ) ≠ 0))
  apply hlogRatio.congr'
  filter_upwards
      [tendsto_topPrimeScale_atTop.eventually_gt_atTop (Real.exp 1),
       tendsto_topPrimeUpper_atTop.eventually_gt_atTop (Real.exp 1)]
      with X hscale hupper
  unfold topLogBand
  have hslog : Real.log (topPrimeScale X) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact (Real.exp_pos 1).trans hscale
    · linarith [Real.exp_one_gt_two]
  have hulog : Real.log (topPrimeUpper X) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact (Real.exp_pos 1).trans hupper
    · linarith [Real.exp_one_gt_two]
  rw [← Real.log_div hulog hslog]

theorem eventually_topPrimeScale_le_upper :
    ∀ᶠ X : ℕ in atTop, topPrimeScale X ≤ topPrimeUpper X := by
  have hdiv := TransitionDensity.tendsto_transitionPrimeBandUpper_div_nat
  have hlt := (tendsto_order.1 hdiv).2
    (globalBranchBound : ℝ) (by norm_num [globalBranchBound])
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with X hratio hX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have h := (div_lt_iff₀ hXreal).mp hratio
  simpa [topPrimeScale, FullDensity.transitionPrimeBandUpper,
    topPrimeUpper] using h.le

private lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t => Real.log (Real.log t)) x =
      1 / (x * Real.log x) := by
  rw [deriv.log (Real.differentiableAt_log (by linarith))
    (by simp; grind), Real.deriv_log]
  field

lemma integral_one_div_mul_log_between
    {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z) :
    ∫ t in y..z, 1 / (t * Real.log t) =
      Real.log (Real.log z) - Real.log (Real.log y) := by
  rw [← intervalIntegral.integral_deriv_eq_sub
    (f := fun t => Real.log (Real.log t))]
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hyz, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hyz, Set.mem_Icc] at ht
    have htlog : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := fun t => 1 / (t * Real.log t))
    · refine fun t ht => ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hyz, Set.mem_Icc] at ht
      have htlog : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hyz, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

noncomputable def reciprocalPrimeAPTopBand
    (A a : ℕ) (X : ℕ) : ℝ :=
  reciprocalPrimeAPSumReal A a (topPrimeUpper X) -
    reciprocalPrimeAPSumReal A a (topPrimeScale X)

/-- Pointwise PNT control on the moving interval gives the exact reciprocal
prime-band upper bound needed by the p-first switch. -/
theorem reciprocalPrimeAPTopBand_le_of_normalized
    (A a X : ℕ) (C : ℝ)
    (hscale : 2 ≤ topPrimeScale X)
    (hle : topPrimeScale X ≤ topPrimeUpper X)
    (hnorm : ∀ t : ℝ, topPrimeScale X ≤ t → t ≤ topPrimeUpper X →
      primeAPCountingReal A a t / (t / Real.log t) ≤ C) :
    reciprocalPrimeAPTopBand A a X ≤
      primeAPCountingReal A a (topPrimeUpper X) / topPrimeUpper X +
        C * topLogBand X := by
  let f : ℝ → ℝ := fun t => primeAPCountingReal A a t / t ^ 2
  have hupper : 2 ≤ topPrimeUpper X := hscale.trans hle
  have hi2s : IntervalIntegrable f MeasureTheory.volume 2
      (topPrimeScale X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hscale]
    exact integrableOn_primeAPCountingReal_div_sq A a _
  have hi2u : IntervalIntegrable f MeasureTheory.volume 2
      (topPrimeUpper X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hupper]
    exact integrableOn_primeAPCountingReal_div_sq A a _
  have hisu : IntervalIntegrable f MeasureTheory.volume
      (topPrimeScale X) (topPrimeUpper X) := by
    apply hi2u.mono_set
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le hupper]
    intro t ht
    exact ⟨hscale.trans ht.1, ht.2⟩
  have hband : reciprocalPrimeAPTopBand A a X =
      primeAPCountingReal A a (topPrimeUpper X) / topPrimeUpper X -
        primeAPCountingReal A a (topPrimeScale X) / topPrimeScale X +
          ∫ t in topPrimeScale X..topPrimeUpper X, f t := by
    unfold reciprocalPrimeAPTopBand
    rw [reciprocalPrimeAPSumReal_eq_count_div_add_integral A a hupper,
      reciprocalPrimeAPSumReal_eq_count_div_add_integral A a hscale]
    rw [← intervalIntegral.integral_add_adjacent_intervals hi2s hisu]
    dsimp [f]
    ring
  have hbaseInt : IntervalIntegrable
      (fun t : ℝ => C * (1 / (t * Real.log t)))
      MeasureTheory.volume (topPrimeScale X) (topPrimeUpper X) := by
    refine ContinuousOn.intervalIntegrable fun t ht =>
      ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at ht
    have htlog : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop (disch := grind)
  have hintLe :
      (∫ t in topPrimeScale X..topPrimeUpper X, f t) ≤
        ∫ t in topPrimeScale X..topPrimeUpper X,
          C * (1 / (t * Real.log t)) := by
    apply intervalIntegral.integral_mono_on hle hisu hbaseInt
    intro t ht
    have ht1 : 1 < t := (by linarith [hscale, ht.1])
    have htpos : 0 < t := zero_lt_one.trans ht1
    have htlog : 0 < Real.log t := Real.log_pos ht1
    have hn := hnorm t ht.1 ht.2
    have hid : f t =
        (primeAPCountingReal A a t / (t / Real.log t)) *
          (1 / (t * Real.log t)) := by
      dsimp [f]
      field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_right hn (by positivity)
  rw [hband]
  have hpiNonneg : 0 ≤
      primeAPCountingReal A a (topPrimeScale X) / topPrimeScale X := by
    exact div_nonneg (by unfold primeAPCountingReal; positivity)
      (by linarith)
  have hbase :
      (∫ t in topPrimeScale X..topPrimeUpper X,
        C * (1 / (t * Real.log t))) = C * topLogBand X := by
    rw [intervalIntegral.integral_const_mul,
      integral_one_div_mul_log_between (by linarith) hle]
    rfl
  rw [hbase] at hintLe
  linarith

theorem eventually_reciprocalPrimeAPTopBand_le
    {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A) (haA : a < A)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      reciprocalPrimeAPTopBand A a X ≤
        primeAPCountingReal A a (topPrimeUpper X) / topPrimeUpper X +
          ((A.totient : ℝ)⁻¹ + ε) * topLogBand X := by
  have hpnt := primeAPCountingReal_normalized_tendsto hA ha haA
  have hpntUpper : ∀ᶠ t : ℝ in atTop,
      primeAPCountingReal A a t / (t / Real.log t) ≤
        (A.totient : ℝ)⁻¹ + ε := by
    have hlt := (tendsto_order.1 hpnt).2
      ((A.totient : ℝ)⁻¹ + ε) (by linarith)
    exact hlt.mono fun _ h => h.le
  obtain ⟨M, hM⟩ := (eventually_atTop.1 hpntUpper)
  filter_upwards
      [tendsto_topPrimeScale_atTop.eventually_ge_atTop (max 2 M),
       eventually_topPrimeScale_le_upper]
      with X hscale hle
  apply reciprocalPrimeAPTopBand_le_of_normalized A a X
    ((A.totient : ℝ)⁻¹ + ε) ((le_max_left 2 M).trans hscale) hle
  intro t hst _htz
  exact hM t (le_trans (le_max_right 2 M) (hscale.trans hst))

theorem tendsto_primeAP_top_endpoint
    {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A) (haA : a < A) :
    Tendsto (fun X : ℕ =>
      primeAPCountingReal A a (topPrimeUpper X) / topPrimeUpper X)
      atTop (𝓝 0) := by
  have hpnt := (primeAPCountingReal_normalized_tendsto hA ha haA).comp
    tendsto_topPrimeUpper_atTop
  have hinvLog : Tendsto (fun X : ℕ =>
      (Real.log (topPrimeUpper X))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_topPrimeUpper_atTop).inv_tendsto_atTop
  have hprod := hpnt.mul hinvLog
  have hprod' : Tendsto (fun X : ℕ =>
      (primeAPCountingReal A a (topPrimeUpper X) /
        (topPrimeUpper X / Real.log (topPrimeUpper X))) *
          (Real.log (topPrimeUpper X))⁻¹)
      atTop (𝓝 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards
      [tendsto_topPrimeUpper_atTop.eventually_gt_atTop (Real.exp 1)]
      with X hupper
  have hu0 : topPrimeUpper X ≠ 0 :=
    ne_of_gt ((Real.exp_pos 1).trans hupper)
  have hlog0 : Real.log (topPrimeUpper X) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact (Real.exp_pos 1).trans hupper
    · linarith [Real.exp_one_gt_two]
  field_simp

noncomputable def topAPPrimeSet (A a X : ℕ) : Finset ℕ :=
  (Ioc (topPrimeCut X) (globalBranchBound * X)).filter fun p =>
    p.Prime ∧ p % A = a

theorem reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet
    (A a X : ℕ) (hle : topPrimeScale X ≤ topPrimeUpper X) :
    reciprocalPrimeAPTopBand A a X =
      ∑ p ∈ topAPPrimeSet A a X, (p : ℝ)⁻¹ := by
  have hfloorUpper : ⌊topPrimeUpper X⌋₊ = globalBranchBound * X := by
    rw [topPrimeUpper, ← Nat.cast_mul, Nat.floor_natCast]
  have hfloorScale : ⌊topPrimeScale X⌋₊ = topPrimeCut X := rfl
  have hsubset : apPrimes A a (topPrimeScale X) ⊆
      apPrimes A a (topPrimeUpper X) := by
    intro p hp
    rw [apPrimes, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hle)⟩, hp.2⟩
  have hdiff : apPrimes A a (topPrimeUpper X) \
      apPrimes A a (topPrimeScale X) = topAPPrimeSet A a X := by
    ext p
    simp only [apPrimes, topAPPrimeSet, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    rw [hfloorUpper, hfloorScale]
    constructor
    · rintro ⟨⟨⟨_, hpU⟩, hprime, hmod⟩, hnot⟩
      refine ⟨⟨?_, hpU⟩, hprime, hmod⟩
      by_contra hn
      apply hnot
      exact ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hn⟩, hprime, hmod⟩
    · rintro ⟨⟨hpL, hpU⟩, hprime, hmod⟩
      refine ⟨⟨⟨Nat.zero_le p, hpU⟩, hprime, hmod⟩, ?_⟩
      rintro ⟨⟨_, hpLe⟩, _, _⟩
      omega
  unfold reciprocalPrimeAPTopBand reciprocalPrimeAPSumReal
  rw [← hdiff]
  have hsum := Finset.sum_sdiff (f := fun p : ℕ => (p : ℝ)⁻¹) hsubset
  linarith

theorem PTopPrimeSet_eq_union (X : ℕ) :
    PTopPrimeSet X = topAPPrimeSet 7 1 X ∪ topAPPrimeSet 7 6 X := by
  ext p
  simp only [PTopPrimeSet, topAPPrimeSet, Finset.mem_filter,
    Finset.mem_Ioc, Finset.mem_union]
  aesop

theorem RTopPrimeSet_eq_union (X : ℕ) :
    RTopPrimeSet X = topAPPrimeSet 14 1 X ∪ topAPPrimeSet 14 13 X := by
  ext p
  simp only [RTopPrimeSet, topAPPrimeSet, Finset.mem_filter,
    Finset.mem_Ioc, Finset.mem_union]
  aesop

lemma topAPPrimeSet_disjoint
    {A a b X : ℕ} (hab : a ≠ b) :
    Disjoint (topAPPrimeSet A a X) (topAPPrimeSet A b X) := by
  rw [Finset.disjoint_left]
  intro p hpa hpb
  have ha := (Finset.mem_filter.mp hpa).2.2
  have hb := (Finset.mem_filter.mp hpb).2.2
  exact hab (ha.symm.trans hb)

theorem sum_PTopPrimeSet_eq_bands
    (X : ℕ) (hle : topPrimeScale X ≤ topPrimeUpper X) :
    (∑ p ∈ PTopPrimeSet X, (p : ℝ)⁻¹) =
      reciprocalPrimeAPTopBand 7 1 X +
        reciprocalPrimeAPTopBand 7 6 X := by
  rw [PTopPrimeSet_eq_union,
    Finset.sum_union (topAPPrimeSet_disjoint (by norm_num : (1 : ℕ) ≠ 6)),
    reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet 7 1 X hle,
    reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet 7 6 X hle]

theorem sum_RTopPrimeSet_eq_bands
    (X : ℕ) (hle : topPrimeScale X ≤ topPrimeUpper X) :
    (∑ p ∈ RTopPrimeSet X, (p : ℝ)⁻¹) =
      reciprocalPrimeAPTopBand 14 1 X +
        reciprocalPrimeAPTopBand 14 13 X := by
  rw [RTopPrimeSet_eq_union,
    Finset.sum_union (topAPPrimeSet_disjoint (by norm_num : (1 : ℕ) ≠ 13)),
    reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet 14 1 X hle,
    reciprocalPrimeAPTopBand_eq_sum_topAPPrimeSet 14 13 X hle]

lemma cast_sum_div_add_one_le
    (S : Finset ℕ) (X : ℕ) :
    ((∑ p ∈ S, (X / p + 1) : ℕ) : ℝ) ≤
      (X : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) + S.card := by
  calc
    ((∑ p ∈ S, (X / p + 1) : ℕ) : ℝ) =
        ∑ p ∈ S, (((X / p : ℕ) : ℝ) + 1) := by norm_cast
    _ ≤ ∑ p ∈ S, ((X : ℝ) * (p : ℝ)⁻¹ + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact add_le_add (by
        simpa [div_eq_mul_inv] using
          (Nat.cast_div_le (m := X) (n := p) (α := ℝ))) le_rfl
    _ = (X : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) + S.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

theorem allowedPrimeSets_card_le_ordinary_count (X : ℕ) :
    ((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card ≤
      2 * primeAPCountingReal 1 0 (topPrimeUpper X) := by
  have hP : ((PTopPrimeSet X).card : ℝ) ≤
      primeAPCountingReal 1 0 (topPrimeUpper X) := by
    unfold primeAPCountingReal
    norm_cast
    apply Finset.card_le_card
    intro p hp
    rw [PTopPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hfloor : ⌊topPrimeUpper X⌋₊ = globalBranchBound * X := by
      rw [topPrimeUpper, ← Nat.cast_mul, Nat.floor_natCast]
    exact ⟨⟨Nat.zero_le p, by simpa [hfloor] using hp.1.2⟩,
      hp.2.1, Nat.mod_one p⟩
  have hR : ((RTopPrimeSet X).card : ℝ) ≤
      primeAPCountingReal 1 0 (topPrimeUpper X) := by
    unfold primeAPCountingReal
    norm_cast
    apply Finset.card_le_card
    intro p hp
    rw [RTopPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hfloor : ⌊topPrimeUpper X⌋₊ = globalBranchBound * X := by
      rw [topPrimeUpper, ← Nat.cast_mul, Nat.floor_natCast]
    exact ⟨⟨Nat.zero_le p, by simpa [hfloor] using hp.1.2⟩,
      hp.2.1, Nat.mod_one p⟩
  linarith

theorem tendsto_ordinary_top_count_div_parameter :
    Tendsto (fun X : ℕ =>
      primeAPCountingReal 1 0 (topPrimeUpper X) / (X : ℝ))
      atTop (𝓝 0) := by
  have hend := tendsto_primeAP_top_endpoint
    (A := 1) (a := 0) (by norm_num) (by norm_num) (by norm_num)
  have hscaled := hend.const_mul (globalBranchBound : ℝ)
  have hscaled' : Tendsto (fun X : ℕ =>
      (globalBranchBound : ℝ) *
        (primeAPCountingReal 1 0 (topPrimeUpper X) / topPrimeUpper X))
      atTop (𝓝 0) := by simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hC0 : (globalBranchBound : ℝ) ≠ 0 := by
    norm_num [globalBranchBound]
  unfold topPrimeUpper
  field_simp

noncomputable def topAnalyticMajorant (ε : ℝ) (X : ℕ) : ℝ :=
  primeAPCountingReal 7 1 (topPrimeUpper X) / topPrimeUpper X +
    primeAPCountingReal 7 6 (topPrimeUpper X) / topPrimeUpper X +
    primeAPCountingReal 14 1 (topPrimeUpper X) / topPrimeUpper X +
    primeAPCountingReal 14 13 (topPrimeUpper X) / topPrimeUpper X +
    4 * ((1 / 6 : ℝ) + ε) * topLogBand X +
    2 * primeAPCountingReal 1 0 (topPrimeUpper X) / (X : ℝ)

theorem tendsto_topAnalyticMajorant (ε : ℝ) :
    Tendsto (topAnalyticMajorant ε) atTop
      (𝓝 (4 * ((1 / 6 : ℝ) + ε) * Real.log 2)) := by
  have h71 := tendsto_primeAP_top_endpoint
    (A := 7) (a := 1) (by norm_num) (by norm_num) (by norm_num)
  have h76 := tendsto_primeAP_top_endpoint
    (A := 7) (a := 6) (by norm_num) (by norm_num) (by norm_num)
  have h141 := tendsto_primeAP_top_endpoint
    (A := 14) (a := 1) (by norm_num) (by norm_num) (by norm_num)
  have h1413 := tendsto_primeAP_top_endpoint
    (A := 14) (a := 13) (by norm_num) (by norm_num) (by norm_num)
  have hmain := tendsto_topLogBand.const_mul
    (4 * ((1 / 6 : ℝ) + ε))
  have hcount := tendsto_ordinary_top_count_div_parameter.const_mul 2
  have htotal := (((((h71.add h76).add h141).add h1413).add hmain).add hcount)
  convert htotal using 1
  · funext X
    unfold topAnalyticMajorant
    ring
  · ring

/-- Finite normalized top count bounded by the analytic majorant. -/
theorem normalizedTopPrimeWitnessCount_le_majorant
    (X : ℕ) (hX : 1 ≤ X) (hcut : TopCutoffHypothesis X)
    (hlarge : 380808 ≤ topPrimeCut X)
    (hle : topPrimeScale X ≤ topPrimeUpper X)
    (ε : ℝ)
    (h71 : reciprocalPrimeAPTopBand 7 1 X ≤
      primeAPCountingReal 7 1 (topPrimeUpper X) / topPrimeUpper X +
        ((1 / 6 : ℝ) + ε) * topLogBand X)
    (h76 : reciprocalPrimeAPTopBand 7 6 X ≤
      primeAPCountingReal 7 6 (topPrimeUpper X) / topPrimeUpper X +
        ((1 / 6 : ℝ) + ε) * topLogBand X)
    (h141 : reciprocalPrimeAPTopBand 14 1 X ≤
      primeAPCountingReal 14 1 (topPrimeUpper X) / topPrimeUpper X +
        ((1 / 6 : ℝ) + ε) * topLogBand X)
    (h1413 : reciprocalPrimeAPTopBand 14 13 X ≤
      primeAPCountingReal 14 13 (topPrimeUpper X) / topPrimeUpper X +
        ((1 / 6 : ℝ) + ε) * topLogBand X) :
    ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) /
        (X : ℝ) ≤ topAnalyticMajorant ε X := by
  have hcard := topWitnesses_card_le_allowed_sums X hX hcut hlarge
  have hcardCast :
      ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) ≤
        ((∑ p ∈ PTopPrimeSet X, (X / p + 1) : ℕ) : ℝ) +
          ((∑ p ∈ RTopPrimeSet X, (X / p + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hP := cast_sum_div_add_one_le (PTopPrimeSet X) X
  have hR := cast_sum_div_add_one_le (RTopPrimeSet X) X
  have hmassP := sum_PTopPrimeSet_eq_bands X hle
  have hmassR := sum_RTopPrimeSet_eq_bands X hle
  have hraw :
      ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) ≤
        (X : ℝ) *
          (reciprocalPrimeAPTopBand 7 1 X +
            reciprocalPrimeAPTopBand 7 6 X +
            reciprocalPrimeAPTopBand 14 1 X +
            reciprocalPrimeAPTopBand 14 13 X) +
          ((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card := by
    rw [hmassP] at hP
    rw [hmassR] at hR
    linarith
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hnormalized :
      ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) /
          (X : ℝ) ≤
        reciprocalPrimeAPTopBand 7 1 X +
          reciprocalPrimeAPTopBand 7 6 X +
          reciprocalPrimeAPTopBand 14 1 X +
          reciprocalPrimeAPTopBand 14 13 X +
          (((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card) /
            (X : ℝ) := by
    apply (div_le_iff₀ hXreal).2
    calc
      ((localTopPrimeWitnessesUpTo X (topPrimeCut X)).card : ℝ) ≤ _ := hraw
      _ = (reciprocalPrimeAPTopBand 7 1 X +
          reciprocalPrimeAPTopBand 7 6 X +
          reciprocalPrimeAPTopBand 14 1 X +
          reciprocalPrimeAPTopBand 14 13 X +
          (((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card) /
            (X : ℝ)) * (X : ℝ) := by
        field_simp
        ring
  have hcards := allowedPrimeSets_card_le_ordinary_count X
  have hcardsDiv :
      (((PTopPrimeSet X).card : ℝ) + (RTopPrimeSet X).card) /
          (X : ℝ) ≤
        2 * primeAPCountingReal 1 0 (topPrimeUpper X) / (X : ℝ) :=
    div_le_div_of_nonneg_right hcards hXreal.le
  unfold topAnalyticMajorant
  linarith

/-! ## Eventual cutoff verification and limsup closure -/

theorem eventually_large_topPrimeCut :
    ∀ᶠ X : ℕ in atTop, 380808 ≤ topPrimeCut X := by
  filter_upwards
      [tendsto_topPrimeScale_atTop.eventually_ge_atTop (380808 : ℝ)]
      with X hX
  unfold topPrimeCut
  exact Nat.le_floor hX

theorem eventually_topCutoffHypothesis :
    ∀ᶠ X : ℕ in atTop, TopCutoffHypothesis X := by
  have hlogPow : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ 4)
      atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards
      [hlogPow.eventually_gt_atTop
        (4 * (130 * globalBranchBound : ℝ)),
       tendsto_topPrimeScale_atTop.eventually_gt_atTop 2,
       eventually_gt_atTop (0 : ℕ)]
      with X hlog hscale hX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hfloor : topPrimeScale X < (topPrimeCut X : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (topPrimeScale X)
  have hhalf : topPrimeScale X / 2 < (topPrimeCut X : ℝ) := by
    nlinarith
  have hscaleSq : topPrimeScale X ^ 2 =
      (X : ℝ) * Real.log (X : ℝ) ^ 4 := by
    unfold topPrimeScale
    rw [mul_pow, Real.sq_sqrt hXreal.le]
    ring
  have hreal :
      ((130 * globalBranchBound * X : ℕ) : ℝ) <
        ((topPrimeCut X ^ 2 : ℕ) : ℝ) := by
    push_cast
    rw [pow_two]
    have hhalfSq : (topPrimeScale X / 2) ^ 2 <
        (topPrimeCut X : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (topPrimeScale X / 2),
        sq_nonneg (topPrimeCut X : ℝ)]
    have hhalfSq' : topPrimeScale X ^ 2 / 4 <
        (topPrimeCut X : ℝ) ^ 2 := by
      nlinarith
    rw [hscaleSq] at hhalfSq'
    nlinarith
  unfold TopCutoffHypothesis
  exact_mod_cast hreal

theorem topPrimeCut_eq_transitionTopCut (X : ℕ) :
    topPrimeCut X = TransitionDensity.transitionTopCut X := by
  rfl

theorem eventually_normalizedTopPrimeWitnessCount_le_majorant
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      RangeAssembly.normalizedTopPrimeWitnessCount X ≤
        topAnalyticMajorant ε X := by
  have h71 := eventually_reciprocalPrimeAPTopBand_le
    (A := 7) (a := 1) (by norm_num) (by norm_num) (by norm_num) hε
  have h76 := eventually_reciprocalPrimeAPTopBand_le
    (A := 7) (a := 6) (by norm_num) (by norm_num) (by norm_num) hε
  have h141 := eventually_reciprocalPrimeAPTopBand_le
    (A := 14) (a := 1) (by norm_num) (by norm_num) (by norm_num) hε
  have h1413 := eventually_reciprocalPrimeAPTopBand_le
    (A := 14) (a := 13) (by norm_num) (by norm_num) (by norm_num) hε
  filter_upwards
      [h71, h76, h141, h1413, eventually_topCutoffHypothesis,
       eventually_large_topPrimeCut, eventually_topPrimeScale_le_upper,
       eventually_ge_atTop (1 : ℕ)]
      with X h71X h76X h141X h1413X hcut hlarge hle hX
  rw [RangeAssembly.normalizedTopPrimeWitnessCount,
    ← topPrimeCut_eq_transitionTopCut]
  apply normalizedTopPrimeWitnessCount_le_majorant X hX hcut hlarge hle ε
  · simpa [show Nat.totient 7 = 6 by decide] using h71X
  · simpa [show Nat.totient 7 = 6 by decide] using h76X
  · simpa [show Nat.totient 14 = 6 by decide] using h141X
  · simpa [show Nat.totient 14 = 6 by decide] using h1413X

theorem eventually_normalizedTopPrimeWitnessCount_lt
    {y : ℝ} (hy : (2 / 3 : ℝ) * Real.log 2 < y) :
    ∀ᶠ X : ℕ in atTop,
      RangeAssembly.normalizedTopPrimeWitnessCount X < y := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε : ℝ := (y - (2 / 3 : ℝ) * Real.log 2) /
    (8 * Real.log 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (sub_pos.mpr hy) (mul_pos (by norm_num) hlog2)
  have hbound := eventually_normalizedTopPrimeWitnessCount_le_majorant hε
  have hlim := tendsto_topAnalyticMajorant ε
  have hlimitLt :
      4 * ((1 / 6 : ℝ) + ε) * Real.log 2 < y := by
    dsimp [ε]
    field_simp
    linarith
  have hmajorLt := (tendsto_order.1 hlim).2 y hlimitLt
  filter_upwards [hbound, hmajorLt] with X hX hM
  exact hX.trans_lt hM

/-- The top-range normalized count is eventually bounded. -/
theorem normalizedTopPrimeWitnessCount_isBoundedUnder :
    IsBoundedUnder (· ≤ ·) atTop
      RangeAssembly.normalizedTopPrimeWitnessCount := by
  have h := eventually_normalizedTopPrimeWitnessCount_lt
    (y := (2 / 3 : ℝ) * Real.log 2 + 1) (by linarith)
  apply isBoundedUnder_of_eventually_le
  exact h.mono fun _ hx => hx.le

/-- Complete top-range closure: P and R each contribute at most
`(1/3) log 2`, while Q and S contribute zero. -/
theorem limsup_normalizedTopPrimeWitnessCount_le :
    limsup RangeAssembly.normalizedTopPrimeWitnessCount atTop ≤
      (2 / 3 : ℝ) * Real.log 2 := by
  apply (limsup_le_iff
    (h₁ := isCoboundedUnder_le_of_le atTop
      RangeAssembly.normalizedTopPrimeWitnessCount_nonneg)
    (h₂ := normalizedTopPrimeWitnessCount_isBoundedUnder)).2
  intro y hy
  exact eventually_normalizedTopPrimeWitnessCount_lt hy

end

end DivisorSwitching
end Erdos730
