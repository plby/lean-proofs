/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.DensityEvents

/-!
# Erdős 730: assigning every transition obstruction to a linear branch

The finite event ledger first records a drop or entry obstruction against the
products `P*Q` and `3*R*S`.  The analytic argument counts four linear-branch
events instead.  This file proves the exact bridge between those two views.

The only exceptional product factor is `3`.  We prove directly that it can
never be an entry obstruction: its exact quotient is `R*S`, and the least
base-three digit of `(R*S-1)/2` is `2`, outside the lower half.
-/

namespace Erdos730
namespace BranchEvents

open ConsecutiveTransition DensityEvents FullDensityCore KummerTransition

set_option backward.isDefEq.respectTransparency false in
inductive Branch where
  | P | Q | R | S
  deriving DecidableEq, Fintype, Repr

/-- The linear factor belonging to a branch. -/
def branchValue : Branch → ℕ → ℕ
  | .P => FullDensityCore.P
  | .Q => FullDensityCore.Q
  | .R => FullDensityCore.R
  | .S => FullDensityCore.S

/-- A global transition obstruction tagged by the branch containing its
prime.  The cofactor is still the exact cofactor of `P*Q` or `3*R*S`; later
branch-map lemmas identify it with the corresponding `Phi` value. -/
def TaggedObstruction (L : Branch) (x p a c : ℕ) : Prop :=
  match L with
  | .P => DropObstruction (n x) p a c ∧ p ∣ P x
  | .Q => DropObstruction (n x) p a c ∧ p ∣ Q x
  | .R => EntryObstruction (n x) p a c ∧ p ∣ R x
  | .S => EntryObstruction (n x) p a c ∧ p ∣ S x

/-! ## The fixed factor `3` is harmless -/

theorem R_mul_S_eq_six_mul_add_five (x : ℕ) :
    R x * S x =
      6 * (6 * (24682 * x) * (63468 * x + 3) +
        24682 * x + 5 * (63468 * x + 3)) + 5 := by
  simp only [R, S, T]
  ring

theorem R_mul_S_mod_three (x : ℕ) : R x * S x % 3 = 2 := by
  rw [R_mul_S_eq_six_mul_add_five]
  omega

theorem R_mul_S_not_dvd_three (x : ℕ) : ¬3 ∣ R x * S x := by
  rw [Nat.dvd_iff_mod_eq_zero, R_mul_S_mod_three]
  norm_num

theorem entry_three_exact_cofactor
    {x a c : ℕ}
    (hexact : ExactPrimePowerCofactor 3 a c (2 * n x + 1)) :
    a = 1 ∧ c = R x * S x := by
  rcases hexact with ⟨ha, hfac, hthreec⟩
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have hfactor : 3 * (R x * S x) = 3 * (3 ^ b * c) := by
    rw [two_n_add_one] at hfac
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hfac
  have hcancel : R x * S x = 3 ^ b * c :=
    Nat.mul_left_cancel (by norm_num) hfactor
  have hbzero : b = 0 := by
    by_contra hb
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have hthreePow : 3 ∣ 3 ^ b := dvd_pow_self 3 hbpos.ne'
    have hthreeRS : 3 ∣ R x * S x := by
      rw [hcancel]
      exact dvd_mul_of_dvd_left hthreePow c
    exact R_mul_S_not_dvd_three x hthreeRS
  subst b
  simpa using hcancel.symm

theorem entry_three_test_eq_three_mul_add_two (x : ℕ) :
    (R x * S x - 1) / 2 =
      3 * (6 * (24682 * x) * (63468 * x + 3) +
        24682 * x + 5 * (63468 * x + 3)) + 2 := by
  rw [R_mul_S_eq_six_mul_add_five]
  omega

theorem entry_three_test_mod (x : ℕ) :
    (R x * S x - 1) / 2 % 3 = 2 := by
  rw [entry_three_test_eq_three_mul_add_two]
  omega

theorem not_lowerHalfDigits_entry_three (x : ℕ) :
    ¬LowerHalfDigits 3 ((R x * S x - 1) / 2) := by
  intro hlow
  let t := (R x * S x - 1) / 2
  have htpos : 0 < t := by
    dsimp [t]
    rw [entry_three_test_eq_three_mul_add_two]
    omega
  have hdigits : t % 3 ∈ Nat.digits 3 t := by
    rw [Nat.digits_eq_cons_digits_div (by norm_num) htpos.ne']
    simp
  have hhalf := hlow (t % 3) hdigits
  have htmod : t % 3 = 2 := by
    simpa [t] using entry_three_test_mod x
  norm_num [htmod] at hhalf

theorem entry_obstruction_prime_ne_three
    {x p a c : ℕ} (hobs : EntryObstruction (n x) p a c) : p ≠ 3 := by
  rintro rfl
  rcases hobs with ⟨_hprime, _hne2, hexact, hlow⟩
  rcases entry_three_exact_cofactor hexact with ⟨rfl, rfl⟩
  exact not_lowerHalfDigits_entry_three x hlow

/-! ## Existence of a branch tag -/

theorem dropObstruction_has_branch
    {x p a c : ℕ} (hobs : DropObstruction (n x) p a c) :
    TaggedObstruction .P x p a c ∨ TaggedObstruction .Q x p a c := by
  have hp := hobs.1
  have hpFactor : p ∣ n x + 1 :=
    prime_dvd_factor_of_exactPrimePowerCofactor hobs.2.2.1
  rw [n_add_one] at hpFactor
  rcases hp.dvd_mul.mp hpFactor with hpP | hpQ
  · exact Or.inl ⟨hobs, hpP⟩
  · exact Or.inr ⟨hobs, hpQ⟩

theorem entryObstruction_has_branch
    {x p a c : ℕ} (hobs : EntryObstruction (n x) p a c) :
    TaggedObstruction .R x p a c ∨ TaggedObstruction .S x p a c := by
  have hp := hobs.1
  have hp3 : p ≠ 3 := entry_obstruction_prime_ne_three hobs
  have hpFactor : p ∣ 2 * n x + 1 :=
    prime_dvd_factor_of_exactPrimePowerCofactor hobs.2.2.1
  rw [two_n_add_one] at hpFactor
  rcases hp.dvd_mul.mp hpFactor with hpThree | hpRS
  · exact (hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpThree)).elim
  · rcases hp.dvd_mul.mp hpRS with hpR | hpS
    · exact Or.inl ⟨hobs, hpR⟩
    · exact Or.inr ⟨hobs, hpS⟩

/-- Every fully witnessed obstruction has one of the four branch tags. -/
theorem obstruction_has_branch
    {x p a c : ℕ}
    (hobs : DropObstruction (n x) p a c ∨ EntryObstruction (n x) p a c) :
    ∃ L, TaggedObstruction L x p a c := by
  rcases hobs with hdrop | hentry
  · rcases dropObstruction_has_branch hdrop with hP | hQ
    · exact ⟨.P, hP⟩
    · exact ⟨.Q, hQ⟩
  · rcases entryObstruction_has_branch hentry with hR | hS
    · exact ⟨.R, hR⟩
    · exact ⟨.S, hS⟩

/-! ## Recovering the exact branch cofactor -/

/-- If an exact prime power in a coprime product belongs to the left factor,
then the same exponent is exact in that factor and the global cofactor is the
local cofactor times the right factor. -/
theorem exactPrimePowerCofactor_left_of_coprime_product
    {p a c N A B : ℕ} (hp : p.Prime)
    (hexact : ExactPrimePowerCofactor p a c N)
    (hprod : N = A * B) (hcop : Nat.Coprime A B) (hpA : p ∣ A) :
    ∃ d, ExactPrimePowerCofactor p a d A ∧ c = d * B := by
  rcases hexact with ⟨ha, hN, hpc⟩
  have hpCopB : Nat.Coprime p B := hcop.coprime_dvd_left hpA
  have hpowProd : p ^ a ∣ A * B := by
    rw [← hprod, hN]
    exact dvd_mul_right _ _
  have hpowA : p ^ a ∣ A :=
    (hpCopB.pow_left a).dvd_of_dvd_mul_right hpowProd
  obtain ⟨d, hA⟩ := hpowA
  have hcancel : d * B = c := by
    apply Nat.mul_left_cancel (pow_pos hp.pos a)
    calc
      p ^ a * (d * B) = (p ^ a * d) * B := by ring
      _ = A * B := by rw [hA]
      _ = N := hprod.symm
      _ = p ^ a * c := hN
  have hpd : ¬p ∣ d := by
    intro hd
    apply hpc
    rw [← hcancel]
    exact dvd_mul_of_dvd_left hd B
  exact ⟨d, ⟨ha, hA, hpd⟩, hcancel.symm⟩

/-- Right-factor version of the preceding exact-cofactor lemma. -/
theorem exactPrimePowerCofactor_right_of_coprime_product
    {p a c N A B : ℕ} (hp : p.Prime)
    (hexact : ExactPrimePowerCofactor p a c N)
    (hprod : N = A * B) (hcop : Nat.Coprime A B) (hpB : p ∣ B) :
    ∃ d, ExactPrimePowerCofactor p a d B ∧ c = d * A := by
  apply exactPrimePowerCofactor_left_of_coprime_product hp hexact
      (hprod.trans (Nat.mul_comm A B)) hcop.symm hpB

/-- The obstruction value after extracting the exact prime power from one
linear branch.  These are the natural-number versions of `PhiP`--`PhiS`. -/
def branchTestValue : Branch → ℕ → ℕ → ℕ
  | .P, x, d => d * Q x
  | .Q, x, d => d * P x
  | .R, x, d => (3 * d * S x - 1) / 2
  | .S, x, d => (3 * d * R x - 1) / 2

/-- Cofactor of the full transition factor reconstructed from a local branch
cofactor. -/
def branchGlobalCofactor : Branch → ℕ → ℕ → ℕ
  | .P, x, d => d * Q x
  | .Q, x, d => d * P x
  | .R, x, d => 3 * d * S x
  | .S, x, d => 3 * d * R x

/-- Exact local branch event counted by the analytic argument. -/
def LocalBranchObstruction (L : Branch) (x p a d : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧
    ExactPrimePowerCofactor p a d (branchValue L x) ∧
      LowerHalfDigits p (branchTestValue L x d)

theorem R_coprime_three_mul_S (x : ℕ) :
    Nat.Coprime (R x) (3 * S x) := by
  have hR3 : Nat.Coprime (R x) 3 := by
    apply ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num : Nat.Prime 3)).2 ?_).symm
    rw [Nat.dvd_iff_mod_eq_zero, (branch_mod_3 x).2.2.1]
    norm_num
  exact hR3.mul_right (R_S_coprime x)

theorem S_coprime_three_mul_R (x : ℕ) :
    Nat.Coprime (S x) (3 * R x) := by
  have hS3 : Nat.Coprime (S x) 3 := by
    apply ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num : Nat.Prime 3)).2 ?_).symm
    rw [Nat.dvd_iff_mod_eq_zero, (branch_mod_3 x).2.2.2]
    norm_num
  exact hS3.mul_right (R_S_coprime x).symm

/-- A tagged global obstruction supplies the exact local branch cofactor and
recovers its original global cofactor exactly. -/
theorem taggedObstruction_has_local_exact
    {L : Branch} {x p a c : ℕ}
    (h : TaggedObstruction L x p a c) :
    ∃ d, LocalBranchObstruction L x p a d ∧
      branchGlobalCofactor L x d = c := by
  cases L with
  | P =>
      rcases h with ⟨hobs, hpP⟩
      rcases exactPrimePowerCofactor_left_of_coprime_product hobs.1
          hobs.2.2.1 (n_add_one x) (P_Q_coprime x) hpP with
        ⟨d, hdExact, hc⟩
      exact ⟨d, ⟨hobs.1, hobs.2.1, hdExact, by
        simpa [branchTestValue, hc] using hobs.2.2.2⟩,
        by simpa [branchGlobalCofactor] using hc.symm⟩
  | Q =>
      rcases h with ⟨hobs, hpQ⟩
      rcases exactPrimePowerCofactor_right_of_coprime_product hobs.1
          hobs.2.2.1 (n_add_one x) (P_Q_coprime x) hpQ with
        ⟨d, hdExact, hc⟩
      exact ⟨d, ⟨hobs.1, hobs.2.1, hdExact, by
        simpa [branchTestValue, hc] using hobs.2.2.2⟩,
        by simpa [branchGlobalCofactor] using hc.symm⟩
  | R =>
      rcases h with ⟨hobs, hpR⟩
      have hprod : 2 * n x + 1 = R x * (3 * S x) := by
        rw [two_n_add_one]
        ring
      rcases exactPrimePowerCofactor_left_of_coprime_product hobs.1
          hobs.2.2.1 hprod (R_coprime_three_mul_S x) hpR with
        ⟨d, hdExact, hc⟩
      exact ⟨d, ⟨hobs.1, hobs.2.1, hdExact, by
        simpa [branchTestValue, hc, mul_assoc, mul_left_comm, mul_comm]
          using hobs.2.2.2⟩, by
        simpa [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
          using hc.symm⟩
  | S =>
      rcases h with ⟨hobs, hpS⟩
      have hprod : 2 * n x + 1 = S x * (3 * R x) := by
        rw [two_n_add_one]
        ring
      rcases exactPrimePowerCofactor_left_of_coprime_product hobs.1
          hobs.2.2.1 hprod (S_coprime_three_mul_R x) hpS with
        ⟨d, hdExact, hc⟩
      exact ⟨d, ⟨hobs.1, hobs.2.1, hdExact, by
        simpa [branchTestValue, hc, mul_assoc, mul_left_comm, mul_comm]
          using hobs.2.2.2⟩, by
        simpa [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
          using hc.symm⟩

/-- Existential form used by event-counting clients. -/
theorem taggedObstruction_has_local
    {L : Branch} {x p a c : ℕ}
    (h : TaggedObstruction L x p a c) :
    ∃ d, LocalBranchObstruction L x p a d := by
  obtain ⟨d, hd, _⟩ := taggedObstruction_has_local_exact h
  exact ⟨d, hd⟩

/-! ## Finite local-branch event ledger -/

abbrev LocalBranchWitness := Branch × ObstructionWitness

def localWitnessBranch (w : LocalBranchWitness) : Branch := w.1
def localWitnessParameter (w : LocalBranchWitness) : ℕ := w.2.1
def localWitnessPrime (w : LocalBranchWitness) : ℕ := w.2.2.1
def localWitnessExponent (w : LocalBranchWitness) : ℕ := w.2.2.2.1
def localWitnessCofactor (w : LocalBranchWitness) : ℕ := w.2.2.2.2

def localBranchWitnessBox (X : ℕ) : Finset LocalBranchWitness :=
  Finset.univ.product (witnessBox X)

noncomputable def localBranchWitnessesUpTo (X : ℕ) : Finset LocalBranchWitness := by
  classical
  exact (localBranchWitnessBox X).filter fun w =>
    LocalBranchObstruction (localWitnessBranch w)
      (localWitnessParameter w) (localWitnessPrime w)
      (localWitnessExponent w) (localWitnessCofactor w)

@[simp] theorem mem_localBranchWitnessesUpTo
    {X : ℕ} {w : LocalBranchWitness} :
    w ∈ localBranchWitnessesUpTo X ↔
      w.2 ∈ witnessBox X ∧
        LocalBranchObstruction (localWitnessBranch w)
          (localWitnessParameter w) (localWitnessPrime w)
          (localWitnessExponent w) (localWitnessCofactor w) := by
  simp [localBranchWitnessesUpTo, localBranchWitnessBox]

theorem branchValue_lt_witnessBound
    {X x : ℕ} (L : Branch) (hx : x ∈ parameterRange X) :
    branchValue L x < witnessBound X := by
  have hxle := (mem_parameterRange.mp hx).2
  cases L with
  | P =>
      have hQ := (branches_positive x).2.1
      exact (Nat.le_mul_of_pos_right (P x) hQ).trans_lt (by
        rw [← n_add_one]
        exact drop_factor_lt_witnessBound hxle)
  | Q =>
      have hP := (branches_positive x).1
      exact (Nat.le_mul_of_pos_left (Q x) hP).trans_lt (by
        simpa [n_add_one, Nat.mul_comm] using
          drop_factor_lt_witnessBound hxle)
  | R =>
      have h3S : 0 < 3 * S x := mul_pos (by norm_num) (branches_positive x).2.2.2
      exact (Nat.le_mul_of_pos_right (R x) h3S).trans_lt (by
        rw [show R x * (3 * S x) = 3 * (R x * S x) by ring,
          ← two_n_add_one]
        exact entry_factor_lt_witnessBound hxle)
  | S =>
      have h3R : 0 < 3 * R x := mul_pos (by norm_num) (branches_positive x).2.2.1
      exact (Nat.le_mul_of_pos_right (S x) h3R).trans_lt (by
        rw [show S x * (3 * R x) = 3 * (R x * S x) by ring,
          ← two_n_add_one]
        exact entry_factor_lt_witnessBound hxle)

theorem localBranchWitness_mem
    {X x p a d : ℕ} {L : Branch}
    (hx : x ∈ parameterRange X)
    (hlocal : LocalBranchObstruction L x p a d) :
    (L, (x, (p, (a, d)))) ∈ localBranchWitnessesUpTo X := by
  rw [mem_localBranchWitnessesUpTo, mem_witnessBox]
  have hb := branchValue_lt_witnessBound L hx
  rcases exactPrimePowerCofactor_coordinate_bounds
      hlocal.1 hlocal.2.2.1 with ⟨hpB, haB, hdB⟩
  exact ⟨⟨hx, hpB.trans_lt hb, haB.trans_lt hb, hdB.trans_lt hb⟩, hlocal⟩

theorem localBranchObstruction_globalizes
    {L : Branch} {x p a d : ℕ}
    (h : LocalBranchObstruction L x p a d) :
    TaggedObstruction L x p a (branchGlobalCofactor L x d) := by
  rcases h with ⟨hp, hp2, hexact, hlow⟩
  have hpd := hexact.2.2
  have hpBranch := prime_dvd_factor_of_exactPrimePowerCofactor hexact
  cases L with
  | P =>
      change ExactPrimePowerCofactor p a d (P x) at hexact
      change p ∣ P x at hpBranch
      have hpQ : ¬p ∣ Q x := by
        intro hpQ
        apply hp.not_dvd_one
        rw [← P_Q_coprime x]
        exact Nat.dvd_gcd hpBranch hpQ
      refine ⟨⟨hp, hp2, ⟨hexact.1, ?_, ?_⟩, ?_⟩, hpBranch⟩
      · rw [n_add_one, hexact.2.1]
        simp [branchGlobalCofactor, mul_assoc]
      · intro hdiv
        rcases hp.dvd_mul.mp hdiv with hd | hQ
        · exact hpd hd
        · exact hpQ hQ
      · simpa [branchTestValue, branchGlobalCofactor] using hlow
  | Q =>
      change ExactPrimePowerCofactor p a d (Q x) at hexact
      change p ∣ Q x at hpBranch
      have hpP : ¬p ∣ P x := by
        intro hpP
        apply hp.not_dvd_one
        rw [← P_Q_coprime x]
        exact Nat.dvd_gcd hpP hpBranch
      refine ⟨⟨hp, hp2, ⟨hexact.1, ?_, ?_⟩, ?_⟩, hpBranch⟩
      · rw [n_add_one, hexact.2.1]
        simp [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
      · intro hdiv
        rcases hp.dvd_mul.mp hdiv with hd | hP
        · exact hpd hd
        · exact hpP hP
      · simpa [branchTestValue, branchGlobalCofactor] using hlow
  | R =>
      change ExactPrimePowerCofactor p a d (R x) at hexact
      change p ∣ R x at hpBranch
      have hp3 : ¬p ∣ 3 := by
        intro hpThree
        have hpeq : p = 3 :=
          (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpThree
        subst p
        exact R_mul_S_not_dvd_three x
          (dvd_mul_of_dvd_left hpBranch (S x))
      have hpS : ¬p ∣ S x := by
        intro hpS
        apply hp.not_dvd_one
        rw [← R_S_coprime x]
        exact Nat.dvd_gcd hpBranch hpS
      refine ⟨⟨hp, hp2, ⟨hexact.1, ?_, ?_⟩, ?_⟩, hpBranch⟩
      · rw [two_n_add_one, hexact.2.1]
        simp [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
      · intro hdiv
        rcases hp.dvd_mul.mp hdiv with hthreeD | hpS'
        · rcases hp.dvd_mul.mp hthreeD with hpThree | hd
          · exact hp3 hpThree
          · exact hpd hd
        · exact hpS hpS'
      · simpa [branchTestValue, branchGlobalCofactor] using hlow
  | S =>
      change ExactPrimePowerCofactor p a d (S x) at hexact
      change p ∣ S x at hpBranch
      have hp3 : ¬p ∣ 3 := by
        intro hpThree
        have hpeq : p = 3 :=
          (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpThree
        subst p
        exact R_mul_S_not_dvd_three x
          (dvd_mul_of_dvd_right hpBranch (R x))
      have hpR : ¬p ∣ R x := by
        intro hpR
        apply hp.not_dvd_one
        rw [← R_S_coprime x]
        exact Nat.dvd_gcd hpR hpBranch
      refine ⟨⟨hp, hp2, ⟨hexact.1, ?_, ?_⟩, ?_⟩, hpBranch⟩
      · rw [two_n_add_one, hexact.2.1]
        simp [branchGlobalCofactor, mul_assoc, mul_left_comm, mul_comm]
      · intro hdiv
        rcases hp.dvd_mul.mp hdiv with hthreeD | hpR'
        · rcases hp.dvd_mul.mp hthreeD with hpThree | hd
          · exact hp3 hpThree
          · exact hpd hd
        · exact hpR hpR'
      · simpa [branchTestValue, branchGlobalCofactor] using hlow

/-- Forget the branch tag and local cofactor, reconstructing the original
global obstruction witness. -/
def globalizeLocalWitness (w : LocalBranchWitness) : ObstructionWitness :=
  (localWitnessParameter w,
    (localWitnessPrime w,
      (localWitnessExponent w,
        branchGlobalCofactor (localWitnessBranch w)
          (localWitnessParameter w) (localWitnessCofactor w))))

theorem globalizeLocalWitness_mem
    {X : ℕ} {w : LocalBranchWitness}
    (hw : w ∈ localBranchWitnessesUpTo X) :
    globalizeLocalWitness w ∈ obstructionWitnessesUpTo X := by
  rcases w with ⟨L, ⟨x, p, a, d⟩⟩
  have hmem := mem_localBranchWitnessesUpTo.mp hw
  have hx : x ∈ parameterRange X := (mem_witnessBox.mp hmem.1).1
  have htag := localBranchObstruction_globalizes hmem.2
  rw [mem_obstructionWitnessesUpTo]
  cases L with
  | P => exact Or.inl (dropWitness_mem hx htag.1)
  | Q => exact Or.inl (dropWitness_mem hx htag.1)
  | R => exact Or.inr (entryWitness_mem hx htag.1)
  | S => exact Or.inr (entryWitness_mem hx htag.1)

theorem globalizeLocalWitness_surjOn (X : ℕ) :
    Set.SurjOn globalizeLocalWitness
      (localBranchWitnessesUpTo X : Set LocalBranchWitness)
      (obstructionWitnessesUpTo X : Set ObstructionWitness) := by
  intro w hw
  rcases w with ⟨x, p, a, c⟩
  have hobsMem := mem_obstructionWitnessesUpTo.mp hw
  have hobs : DropObstruction (n x) p a c ∨
      EntryObstruction (n x) p a c := by
    rcases hobsMem with hdrop | hentry
    · exact Or.inl (mem_dropWitnessesUpTo.mp hdrop).2
    · exact Or.inr (mem_entryWitnessesUpTo.mp hentry).2
  obtain ⟨L, htag⟩ := obstruction_has_branch hobs
  obtain ⟨d, hlocal, hc⟩ := taggedObstruction_has_local_exact htag
  have hx : x ∈ parameterRange X := by
    rcases hobsMem with hdrop | hentry
    · exact (mem_witnessBox.mp (mem_dropWitnessesUpTo.mp hdrop).1).1
    · exact (mem_witnessBox.mp (mem_entryWitnessesUpTo.mp hentry).1).1
  refine ⟨(L, (x, p, a, d)), localBranchWitness_mem hx hlocal, ?_⟩
  simp [globalizeLocalWitness, localWitnessParameter, localWitnessPrime,
    localWitnessExponent, localWitnessCofactor, localWitnessBranch, hc]

/-- The finite global obstruction count is bounded by the sum of the four
exact local branch-event counts. -/
theorem obstructionWitnesses_card_le_localBranchWitnesses_card (X : ℕ) :
    (obstructionWitnessesUpTo X).card ≤
      (localBranchWitnessesUpTo X).card :=
  Finset.card_le_card_of_surjOn globalizeLocalWitness
    (globalizeLocalWitness_surjOn X)

theorem bad_card_le_localBranchWitnesses_card (X : ℕ) :
    (badParametersUpTo X).card ≤ (localBranchWitnessesUpTo X).card :=
  (bad_card_le_obstructionWitnesses_card X).trans
    (obstructionWitnesses_card_le_localBranchWitnesses_card X)

/-! ## Exact four-range partition of the local branch ledger -/

noncomputable def localHigherPowerWitnessesUpTo (X : ℕ) : Finset LocalBranchWitness :=
  (localBranchWitnessesUpTo X).filter fun w => 2 ≤ localWitnessExponent w

noncomputable def localSmallPrimeWitnessesUpTo (X smallCut : ℕ) :
    Finset LocalBranchWitness :=
  (localBranchWitnessesUpTo X).filter fun w =>
    localWitnessExponent w = 1 ∧ localWitnessPrime w ≤ smallCut

noncomputable def localTransitionPrimeWitnessesUpTo (X smallCut topCut : ℕ) :
    Finset LocalBranchWitness :=
  (localBranchWitnessesUpTo X).filter fun w =>
    localWitnessExponent w = 1 ∧
      smallCut < localWitnessPrime w ∧ localWitnessPrime w ≤ topCut

noncomputable def localTopPrimeWitnessesUpTo (X topCut : ℕ) : Finset LocalBranchWitness :=
  (localBranchWitnessesUpTo X).filter fun w =>
    localWitnessExponent w = 1 ∧ topCut < localWitnessPrime w

theorem localWitness_exponent_pos
    {X : ℕ} {w : LocalBranchWitness}
    (hw : w ∈ localBranchWitnessesUpTo X) :
    0 < localWitnessExponent w := by
  exact (mem_localBranchWitnessesUpTo.mp hw).2.2.2.1.1

theorem localBranchWitnesses_fourRange (X smallCut topCut : ℕ) :
    localBranchWitnessesUpTo X =
      localHigherPowerWitnessesUpTo X ∪
        (localSmallPrimeWitnessesUpTo X smallCut ∪
          (localTransitionPrimeWitnessesUpTo X smallCut topCut ∪
            localTopPrimeWitnessesUpTo X topCut)) := by
  ext w
  simp only [localHigherPowerWitnessesUpTo, localSmallPrimeWitnessesUpTo,
    localTransitionPrimeWitnessesUpTo, localTopPrimeWitnessesUpTo,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hw
    have ha := localWitness_exponent_pos hw
    by_cases ha2 : 2 ≤ localWitnessExponent w
    · exact Or.inl ⟨hw, ha2⟩
    have ha1 : localWitnessExponent w = 1 := by omega
    by_cases hs : localWitnessPrime w ≤ smallCut
    · exact Or.inr (Or.inl ⟨hw, ha1, hs⟩)
    by_cases ht : localWitnessPrime w ≤ topCut
    · exact Or.inr (Or.inr (Or.inl
        ⟨hw, ha1, Nat.lt_of_not_ge hs, ht⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨hw, ha1, Nat.lt_of_not_ge ht⟩))
  · rintro (⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw

theorem localHigher_disjoint_rest (X smallCut topCut : ℕ) :
    Disjoint (localHigherPowerWitnessesUpTo X)
      (localSmallPrimeWitnessesUpTo X smallCut ∪
        (localTransitionPrimeWitnessesUpTo X smallCut topCut ∪
          localTopPrimeWitnessesUpTo X topCut)) := by
  rw [Finset.disjoint_left]
  intro w hh hr
  have ha2 := (Finset.mem_filter.mp hh).2
  rcases Finset.mem_union.mp hr with hs | hr
  · have ha1 := (Finset.mem_filter.mp hs).2.1
    omega
  rcases Finset.mem_union.mp hr with ht | hp
  · have ha1 := (Finset.mem_filter.mp ht).2.1
    omega
  · have ha1 := (Finset.mem_filter.mp hp).2.1
    omega

theorem localSmall_disjoint_rest
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    Disjoint (localSmallPrimeWitnessesUpTo X smallCut)
      (localTransitionPrimeWitnessesUpTo X smallCut topCut ∪
        localTopPrimeWitnessesUpTo X topCut) := by
  rw [Finset.disjoint_left]
  intro w hs hr
  have hpSmall := (Finset.mem_filter.mp hs).2.2
  rcases Finset.mem_union.mp hr with ht | hp
  · have hpLarge := (Finset.mem_filter.mp ht).2.2.1
    omega
  · have hpTop := (Finset.mem_filter.mp hp).2.2
    omega

theorem localTransition_disjoint_top (X smallCut topCut : ℕ) :
    Disjoint (localTransitionPrimeWitnessesUpTo X smallCut topCut)
      (localTopPrimeWitnessesUpTo X topCut) := by
  rw [Finset.disjoint_left]
  intro w ht hp
  have hle := (Finset.mem_filter.mp ht).2.2.2
  have hgt := (Finset.mem_filter.mp hp).2.2
  omega

theorem localBranchWitnesses_card_fourRange
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    (localBranchWitnessesUpTo X).card =
      (localHigherPowerWitnessesUpTo X).card +
        ((localSmallPrimeWitnessesUpTo X smallCut).card +
          ((localTransitionPrimeWitnessesUpTo X smallCut topCut).card +
            (localTopPrimeWitnessesUpTo X topCut).card)) := by
  rw [localBranchWitnesses_fourRange X smallCut topCut,
    Finset.card_union_of_disjoint
      (localHigher_disjoint_rest X smallCut topCut),
    Finset.card_union_of_disjoint
      (localSmall_disjoint_rest X smallCut topCut hcuts),
    Finset.card_union_of_disjoint
      (localTransition_disjoint_top X smallCut topCut)]

/-! ## Uniqueness of the branch tag -/

theorem taggedObstruction_branch_unique
    {L K : Branch} {x p a c : ℕ}
    (hL : TaggedObstruction L x p a c)
    (hK : TaggedObstruction K x p a c) : L = K := by
  cases L <;> cases K
  · rfl
  · apply False.elim
    apply hL.1.1.not_dvd_one
    rw [← P_Q_coprime x]
    exact Nat.dvd_gcd hL.2 hK.2
  · exact (not_dvd_two_mul_add_one_of_dvd_succ hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_two_mul_add_one_of_dvd_succ hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · apply False.elim
    apply hL.1.1.not_dvd_one
    rw [← (P_Q_coprime x).symm]
    exact Nat.dvd_gcd hL.2 hK.2
  · rfl
  · exact (not_dvd_two_mul_add_one_of_dvd_succ hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_two_mul_add_one_of_dvd_succ hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_succ_of_dvd_two_mul_add_one hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_succ_of_dvd_two_mul_add_one hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · rfl
  · apply False.elim
    apply hL.1.1.not_dvd_one
    rw [← R_S_coprime x]
    exact Nat.dvd_gcd hL.2 hK.2
  · exact (not_dvd_succ_of_dvd_two_mul_add_one hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · exact (not_dvd_succ_of_dvd_two_mul_add_one hL.1.1
      (prime_dvd_factor_of_exactPrimePowerCofactor hL.1.2.2.1)
      (prime_dvd_factor_of_exactPrimePowerCofactor hK.1.2.2.1)).elim
  · apply False.elim
    apply hL.1.1.not_dvd_one
    rw [← (R_S_coprime x).symm]
    exact Nat.dvd_gcd hL.2 hK.2
  · rfl

#print axioms entry_three_exact_cofactor
#print axioms not_lowerHalfDigits_entry_three
#print axioms entry_obstruction_prime_ne_three
#print axioms obstruction_has_branch
#print axioms exactPrimePowerCofactor_left_of_coprime_product
#print axioms taggedObstruction_has_local
#print axioms localBranchObstruction_globalizes
#print axioms bad_card_le_localBranchWitnesses_card
#print axioms localBranchWitnesses_card_fourRange
#print axioms taggedObstruction_branch_unique

end BranchEvents
end Erdos730
