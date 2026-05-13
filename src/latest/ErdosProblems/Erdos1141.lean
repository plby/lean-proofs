/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1141.
https://www.erdosproblems.com/forum/thread/1141

Formalization status:
- Conditional on: pollack_theorem_1_3, mertens_third_theorem

Informal authors:
- Boris Alexeev
- Moe Putterman
- Mehtaab Sawhney
- Mark Sellke
- Gregory Valiant
- an internal model at OpenAI

Formal authors:
- GPT-5.4 Pro
- Yuta Oriike

URLs:
- https://www.erdosproblems.com/forum/thread/1141#post-5335
- https://github.com/yuta0x89/ErdosProblems/blob/a1319f732cdee5140faf47d984e2c451c1184803/Erdos1141.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1141.lean
-/
import Mathlib

set_option linter.style.emptyLine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Erdős Problem 1141

We formalize the `Pa`-variant of Erdős Problem 1141 from the paper
https://arxiv.org/abs/2604.06609 and then deduce the Formal
Conjectures statement.
Fix `a ≥ 1`. Let `Pa a n` denote the property that
`n - a*k^2` is prime for every positive integer `k` with `(k,n)=1` and `a*k^2 < n`.
Then only finitely many `n` satisfy `Pa a n`.

The main development intentionally mirrors the style of Pietro Monticone's
`Erdos237.lean`:

* source: <https://gist.githubusercontent.com/pitmonticone/8ea0d1cdb963b6213ac639b11d33f811/raw/98a5824d16da14313f65d77eeab5563dd874613a/Erdos237.lean>

* the two deep external inputs are axiomatized;
* the rest is organized into helper lemmas matching the paper;
* the medium-weight arithmetic / analytic steps are spelled out in helper lemmas.

## External inputs

1. `Pollack17.theorem_1_3` (axiom): Pollack's Theorem 1.3 in the literal
   `DirichletCharacter`-based form from Pollack's paper
   <https://www.ams.org/journals/proc/2017-145-07/S0002-9939-2016-13432-1/S0002-9939-2016-13432-1.pdf>.
2. `mertens_third_theorem` (axiom): the same axiomized form as in Pietro Monticone's
   `Erdos237.lean`.

## Proof structure

Given `n`, write `a*n = u^2*d` with `d` squarefree.

* Case 1: `d > 1`.
  Pollack gives an odd prime `p ≲ (4*a*n)^(3/8)` for which `d` is a quadratic residue mod `p`.
  Hence `a*x^2 ≡ n [MOD p]` is solvable.

* Case 2: `d = 1`, so `a*n` is a square.
  We **do not** introduce a separate lemma producing a small odd prime `p ∤ a*n`.
  Instead, factor the fixed coefficient `a = v^2*dₐ` with `dₐ` squarefree.

  - If `dₐ > 1`, then from `a = v^2*dₐ` we get `4*dₐ ∣ 4*a*n`.  Pollack applied to the *fixed*
    squarefree part `dₐ` with modulus `4*a*n` again gives an odd prime `p ≲ (4*a*n)^(3/8)`
    with `p ∤ a*n`.
    Since `a*n` is a square, the congruence `a*x^2 ≡ n [MOD p]` is automatically solvable,
    so the same counting contradiction applies.

  - If `dₐ = 1`, then `a = v^2` is itself a square.  From `a*n = u^2` we deduce that `n`
    is also a square, say `n = m^2`.  Then `k = 1` already gives
    `n - a = m^2 - v^2 = (m-v)(m+v)`, which is composite for all sufficiently large `n`.

Thus the only deep inputs remain Pollack Theorem 1.3 and Mertens' third theorem.
-/


noncomputable section

namespace Pollack17

/-- The analytic cutoff `m^(1/4 + ε)` appearing in Theorem 1.3. -/
def residuePrimeUpperBound (m : ℕ) (ε : ℝ) : ℝ :=
  Real.rpow (m : ℝ) ((1 / 4 : ℝ) + ε)

/--
The finite set of primes `ℓ` with `ℓ ≤ m^(1/4 + ε)` and `χ(ℓ) = 1`.

This definition does **not** assume `χ` is quadratic; the quadraticity hypothesis
belongs only to `theorem_1_3`, matching the statement of the paper.
-/
def residuePrimesUpTo (m : ℕ) (χ : DirichletCharacter ℂ m) (ε : ℝ) : Finset ℕ := by
  classical
  exact
    ((Finset.range (Nat.ceil (residuePrimeUpperBound m ε) + 1)).filter fun ℓ =>
      Nat.Prime ℓ ∧
      (ℓ : ℝ) ≤ residuePrimeUpperBound m ε ∧
      χ (ℓ : ZMod m) = (1 : ℂ))

/--
Pollack, *Bounds for the First Several Prime Character Nonresidues*, Theorem 1.3.
-/
axiom theorem_1_3
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ m0 : ℕ, ∀ m : ℕ,
      m > m0 →
      ∀ χ : DirichletCharacter ℂ m,
        MulChar.IsQuadratic χ →
          Real.rpow (Real.log (m : ℝ)) A ≤
            ((residuePrimesUpTo m χ ε).card : ℝ)

end Pollack17

end

namespace Erdos1141

open scoped BigOperators
open Finset Real

/-! ## Basic definitions -/

/-- `Pa a n` means that every positive `k` coprime to `n` with `a*k^2 < n`
produces a prime value `n - a*k^2`. -/
def Pa (a n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Nat.Coprime k n → a * k ^ 2 < n → Nat.Prime (n - a * k ^ 2)

/-- `d` is a quadratic residue modulo `p`.  We use an elementary `Nat.ModEq` formulation,
which is enough for the formalization. -/
def QuadResidueMod (d p : ℕ) : Prop :=
  ∃ x : ℕ, Nat.ModEq p (x ^ 2) d

/-- The congruence `a*x^2 ≡ n [MOD p]` is solvable. -/
def SolvableAX2EqNMod (a n p : ℕ) : Prop :=
  ∃ x : ℕ, Nat.ModEq p (a * x ^ 2) n

/-- The size bound that naturally appears after specializing Pollack with `ε = 1/8`
and `m = 4*a*n`. -/
noncomputable def pollackSizeBound (a n : ℕ) : ℝ :=
  Real.rpow ((4 * a * n : ℕ) : ℝ) ((3 : ℝ) / 8)

/-- Candidate values of `k` used in both cases of the proof.  We range over `k < n`; this is
harmless because `a*k^2 < n` and `a ≥ 1` automatically force `k < n`. -/
def candidateKs (a n p : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun k ↦
    1 ≤ k ∧ a * k ^ 2 < n ∧ Nat.Coprime k n ∧ Nat.ModEq p (a * k ^ 2) n

/-! ## Axioms from analytic number theory -/

/-- A lightweight paper-facing formalization of “`χ` is a quadratic character modulo `m`”.

We record exactly the properties used by Pollack's theorem and by the specialization to the
Jacobi symbol `jacobiSym d`. -/
structure QuadraticCharacterMod (m : ℕ) where
  toFun : ℕ → ℤ
  periodic : ∀ {a b : ℕ}, Nat.ModEq m a b → toFun a = toFun b
  map_non_coprime : ∀ {a : ℕ}, ¬ Nat.Coprime a m → toFun a = 0
  map_coprime : ∀ {a : ℕ}, Nat.Coprime a m → toFun a = 1 ∨ toFun a = -1
  map_mul : ∀ {a b : ℕ}, Nat.Coprime a m → Nat.Coprime b m →
    toFun (a * b) = toFun a * toFun b

instance {m : ℕ} : CoeFun (QuadraticCharacterMod m) (fun _ ↦ ℕ → ℤ) :=
  ⟨QuadraticCharacterMod.toFun⟩

/-- A quadratic character modulo `m` takes the value `1` at `1`. -/
lemma QuadraticCharacterMod.map_one {m : ℕ} (χ : QuadraticCharacterMod m) : χ 1 = 1 := by
  have hcop : Nat.Coprime 1 m := by
    simpa using (Nat.coprime_one_left_iff m).2 trivial
  rcases χ.map_coprime hcop with h1 | h1
  · exact h1
  · have : False := by
      have hmul : χ (1 * 1) = χ 1 * χ 1 := χ.map_mul (a := 1) (b := 1) hcop hcop
      have hbad : (-1 : ℤ) = 1 := by
        simpa [h1] using hmul
      norm_num at hbad
    exact this.elim

/-- A unit of `ZMod m` has a representative coprime to `m`. -/
lemma natCoprime_val_of_isUnit_zmod {m : ℕ} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    Nat.Coprime a.val m := by
  rw [← ha.unit_spec]
  exact ZMod.val_coe_unit_coprime ha.unit

/-- A nonunit of `ZMod m` has no representative coprime to `m`. -/
lemma not_natCoprime_val_of_not_isUnit_zmod {m : ℕ} [NeZero m] {a : ZMod m}
    (ha : ¬ IsUnit a) : ¬ Nat.Coprime a.val m := by
  intro hcop
  apply ha
  simpa [ZMod.natCast_zmod_val a] using (ZMod.isUnit_iff_coprime a.val m).2 hcop

/-- Repackage a paper-facing quadratic character as a `DirichletCharacter` over `ℂ`. -/
def QuadraticCharacterMod.toDirichletCharacterComplex {m : ℕ} [NeZero m]
    (χ : QuadraticCharacterMod m) : DirichletCharacter ℂ m where
  toFun a := (χ a.val : ℂ)
  map_one' := by
    have hperiodic : χ ((1 : ZMod m).val) = χ 1 := by
      apply χ.periodic
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa using (ZMod.natCast_zmod_val (1 : ZMod m))
    rw [hperiodic]
    simpa using congrArg (fun z : ℤ => (z : ℂ)) χ.map_one
  map_mul' := by
    intro a b
    by_cases ha : IsUnit a
    · by_cases hb : IsUnit b
      · have hcopa : Nat.Coprime a.val m := natCoprime_val_of_isUnit_zmod ha
        have hcopb : Nat.Coprime b.val m := natCoprime_val_of_isUnit_zmod hb
        have hperiodic : χ ((a * b).val) = χ (a.val * b.val) := by
          apply χ.periodic
          rw [← ZMod.natCast_eq_natCast_iff]
          calc
            (((a * b).val : ℕ) : ZMod m) = a * b := by
              simpa using (ZMod.natCast_zmod_val (a * b))
            _ = ((a.val : ZMod m) * (b.val : ZMod m)) := by
              simpa using congrArg2 (· * ·)
                (ZMod.natCast_zmod_val a).symm (ZMod.natCast_zmod_val b).symm
            _ = ((a.val * b.val : ℕ) : ZMod m) := by simp
        have hperiodicC : (χ ((a * b).val) : ℂ) = (χ (a.val * b.val) : ℂ) :=
          congrArg (fun z : ℤ => (z : ℂ)) hperiodic
        rw [hperiodicC]
        simpa using congrArg (fun z : ℤ => (z : ℂ)) (χ.map_mul hcopa hcopb)
      · have hnon : ¬ IsUnit (a * b) := by
          intro hab
          exact hb (isUnit_of_mul_isUnit_right hab)
        have hzero_mul : χ ((a * b).val) = 0 :=
          χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hnon)
        have hzero_b : χ b.val = 0 :=
          χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hb)
        simp [hzero_mul, hzero_b]
    · have hnon : ¬ IsUnit (a * b) := by
        intro hab
        exact ha (isUnit_of_mul_isUnit_left hab)
      have hzero_mul : χ ((a * b).val) = 0 :=
        χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod hnon)
      have hzero_a : χ a.val = 0 :=
        χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod ha)
      simp [hzero_mul, hzero_a]
  map_nonunit' := by
    intro a ha
    have hzero : χ a.val = 0 :=
      χ.map_non_coprime (not_natCoprime_val_of_not_isUnit_zmod ha)
    simp [hzero]

@[simp] lemma QuadraticCharacterMod.toDirichletCharacterComplex_apply {m : ℕ} [NeZero m]
    (χ : QuadraticCharacterMod m) (a : ZMod m) :
    χ.toDirichletCharacterComplex a = (χ a.val : ℂ) := rfl

@[simp] lemma QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat
    {m n : ℕ} [NeZero m] (χ : QuadraticCharacterMod m) :
    χ.toDirichletCharacterComplex (n : ZMod m) = (χ n : ℂ) := by
  change ((χ ((n : ZMod m).val) : ℂ) = (χ n : ℂ))
  simpa [ZMod.val_natCast] using
    congrArg (fun z : ℤ => (z : ℂ)) (χ.periodic (Nat.mod_modEq n m))

/-- The associated complex Dirichlet character is quadratic in Pollack's sense. -/
lemma QuadraticCharacterMod.toDirichletCharacterComplex_isQuadratic
    {m : ℕ} [NeZero m] (χ : QuadraticCharacterMod m) :
    MulChar.IsQuadratic (χ.toDirichletCharacterComplex) := by
  intro a
  by_cases ha : IsUnit a
  · have hcop : Nat.Coprime a.val m := natCoprime_val_of_isUnit_zmod ha
    rcases χ.map_coprime hcop with h1 | hneg
    · right
      left
      simp [h1]
    · right
      right
      simp [hneg]
  · left
    have hcop : ¬ Nat.Coprime a.val m := not_natCoprime_val_of_not_isUnit_zmod ha
    simp [χ.map_non_coprime hcop]

/-- If the associated complex Dirichlet character takes the value `1` at a natural number,
then the original integer-valued character also takes the value `1` there. -/
lemma QuadraticCharacterMod.eq_one_of_toDirichletCharacterComplex_apply_nat_eq_one
    {m n : ℕ} [NeZero m] (χ : QuadraticCharacterMod m)
    (hχ : χ.toDirichletCharacterComplex (n : ZMod m) = (1 : ℂ)) :
    χ n = 1 := by
  have happly : χ.toDirichletCharacterComplex (n : ZMod m) = (χ n : ℂ) :=
    χ.toDirichletCharacterComplex_apply_nat (n := n)
  have hχ' : (χ n : ℂ) = (1 : ℂ) := by
    rw [← happly]
    exact hχ
  by_cases hcop : Nat.Coprime n m
  · rcases χ.map_coprime hcop with h1 | hneg
    · exact h1
    · exfalso
      rw [hneg] at hχ'
      norm_num at hχ'
  · exfalso
    rw [χ.map_non_coprime hcop] at hχ'
    norm_num at hχ'

/-- **Mertens' third theorem**, in exactly the same axiomized form as in
Pietro Monticone's `Erdos237.lean`. -/
axiom mertens_third_theorem (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Prime, (1 - 1 / (p : ℝ))

/-! ## Elementary setup -/

/-- Squarefree-part factorization of a natural number. -/
lemma exists_squarefree_factorization (m : ℕ) :
    ∃ u d : ℕ, u ^ 2 * d = m ∧ Squarefree d := by
  obtain ⟨d, u, h, hd⟩ := Nat.sq_mul_squarefree m
  exact ⟨u, d, h, hd⟩

/-- `1` is always a quadratic residue. -/
private lemma one_is_quad_residue (p : ℕ) : QuadResidueMod 1 p := by
  refine ⟨1, ?_⟩
  simpa using (Nat.ModEq.refl (1 : ℕ))

/-- A squarefree natural different from `1` is `> 1`. -/
lemma one_lt_of_squarefree_ne_one {d : ℕ} (hd : Squarefree d) (h : d ≠ 1) : 1 < d := by
  cases d with
  | zero => exact (hd.ne_zero rfl).elim
  | succ d =>
      cases d with
      | zero => exact (h rfl).elim
      | succ d => exact Nat.succ_lt_succ (Nat.succ_pos _)

/-- The obvious size comparison `n ≤ 4*a*n` for `a ≥ 1`, used to feed Pollack with `m = 4*a*n`. -/
lemma le_pollack_modulus {a n : ℕ} (ha : 1 ≤ a) : n ≤ 4 * a * n := by
  have hmul : 1 ≤ 4 * a := by
    nlinarith
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_right n hmul

/-- If `u^2*d = a*n`, then the conductor-relevant multiple `4*d` divides `4*a*n`. -/
private lemma squarefree_factor_dvd_pollack_modulus {a n u d : ℕ}
    (hdecomp : u ^ 2 * d = a * n) : 4 * d ∣ 4 * a * n := by
  refine ⟨u ^ 2, ?_⟩
  calc
    4 * a * n = 4 * (a * n) := by ac_rfl
    _ = 4 * (u ^ 2 * d) := by rw [← hdecomp]
    _ = (4 * d) * (u ^ 2) := by ac_rfl

/-- If `v^2*d = a`, then the conductor-relevant multiple `4*d` divides `4*a*n`. -/
private lemma squarefree_coeff_dvd_pollack_modulus {a n v d : ℕ}
    (hadecomp : v ^ 2 * d = a) : 4 * d ∣ 4 * a * n := by
  refine ⟨v ^ 2 * n, ?_⟩
  calc
    4 * a * n = 4 * (v ^ 2 * d) * n := by rw [← hadecomp]
    _ = (4 * d) * (v ^ 2 * n) := by ac_rfl

/-- A prime not dividing `4*a*n` certainly does not divide `a*n`. -/
lemma not_dvd_an_of_not_dvd_pollack_modulus {a n p : ℕ}
    (h : ¬ p ∣ 4 * a * n) : ¬ p ∣ a * n := by
  intro hp
  apply h
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using dvd_mul_of_dvd_right hp 4

/-- If the squarefree part of `a` is `1`, then `a` is a square. -/
private lemma coeff_is_square_of_squarefree_part_eq_one {a v d : ℕ}
    (hadecomp : v ^ 2 * d = a)
    (hd1 : d = 1) :
    a = v ^ 2 := by
  simpa [hd1] using hadecomp.symm

/-- If `4*d ∣ m`, then `d ∣ m`. -/
lemma d_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : d ∣ m := by
  exact dvd_trans (show d ∣ 4 * d by exact ⟨4, by ac_rfl⟩) hdvd

/-- If `4*d ∣ m`, then `2 ∣ m`. -/
lemma two_dvd_of_four_d_dvd {d m : ℕ} (hdvd : 4 * d ∣ m) : 2 ∣ m := by
  exact dvd_trans (show 2 ∣ 4 * d by exact ⟨2 * d, by ac_rfl⟩) hdvd

/-- A square root in `ZMod p` yields a witness for `QuadResidueMod d p`. -/
private lemma quadResidueMod_of_isSquare_zmod {d p : ℕ} (h : IsSquare (d : ZMod p)) :
    QuadResidueMod d p := by
  rcases h with ⟨x, hx⟩
  cases p with
  | zero =>
      refine ⟨x.val, ?_⟩
      rw [Nat.ModEq, Nat.mod_zero, Nat.mod_zero]
      simpa [pow_two] using congrArg ZMod.val hx.symm
  | succ p =>
      refine ⟨x.val, ?_⟩
      rw [← ZMod.natCast_eq_natCast_iff]
      calc
        (((x.val ^ 2 : ℕ) : ZMod (p + 1))) = (((x.val : ℕ) : ZMod (p + 1)) ^ 2) := by
          simp
        _ = x ^ 2 := by
          simpa using congrArg (fun y : ZMod (p + 1) ↦ y ^ 2) (ZMod.natCast_val x)
        _ = (d : ZMod (p + 1)) := by
          simpa [pow_two] using hx.symm

/-! ## Bridge from Pollack's literal theorem to the Jacobi-symbol specialization -/

/-- The quadratic character attached to `d`, viewed modulo any multiple `m` of `4*d`.

On integers coprime to `m` it is the Jacobi symbol `jacobiSym d`; on non-coprime integers it
is `0`.  The congruence invariance modulo `m` comes from `jacobiSym.mod_right`.

This is the canonical character used in the rest of the file; we no longer keep a separate
`pollack_theorem_1_3` compatibility wrapper. -/
def attachedQuadraticCharacter (d m : ℕ) (hdvd : 4 * d ∣ m) :
    QuadraticCharacterMod m where
  toFun n := if Nat.Coprime n m then jacobiSym (d : ℤ) n else 0
  periodic := by
    intro a b hmod
    have hcop : Nat.Coprime a m ↔ Nat.Coprime b m := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
    by_cases ha : Nat.Coprime a m
    · have hb : Nat.Coprime b m := hcop.mp ha
      have hmod' : Nat.ModEq (4 * d) a b := hmod.of_dvd hdvd
      have ha2 : Nat.Coprime a 2 := ha.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
      have hb2 : Nat.Coprime b 2 := hb.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
      have haOdd : Odd a := (Nat.coprime_two_right).1 ha2
      have hbOdd : Odd b := (Nat.coprime_two_right).1 hb2
      have hJ : jacobiSym (d : ℤ) a = jacobiSym (d : ℤ) b := by
        calc
          jacobiSym (d : ℤ) a = jacobiSym (d : ℤ) (a % (4 * d)) := by
            simpa using jacobiSym.mod_right (d : ℤ) haOdd
          _ = jacobiSym (d : ℤ) (b % (4 * d)) := by
            simpa using congrArg (fun t : ℕ ↦ jacobiSym (d : ℤ) t) hmod'
          _ = jacobiSym (d : ℤ) b := by
            simpa using (jacobiSym.mod_right (d : ℤ) hbOdd).symm
      rw [if_pos ha, if_pos hb]
      exact hJ
    · have hb : ¬ Nat.Coprime b m := mt hcop.mpr ha
      rw [if_neg ha, if_neg hb]
  map_non_coprime := by
    intro a ha
    rw [if_neg ha]
  map_coprime := by
    intro a ha
    have had : Nat.Coprime a d := ha.coprime_dvd_right (d_dvd_of_four_d_dvd hdvd)
    have hgcd : Int.gcd (d : ℤ) a = 1 := by
      simpa [Int.gcd_eq_natAbs, Nat.gcd_comm] using had.gcd_eq_one
    rw [if_pos ha]
    exact jacobiSym.eq_one_or_neg_one (a := (d : ℤ)) (b := a) hgcd
  map_mul := by
    intro a b ha hb
    have ha2 : Nat.Coprime a 2 := ha.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
    have hb2 : Nat.Coprime b 2 := hb.coprime_dvd_right (two_dvd_of_four_d_dvd hdvd)
    have haOdd : Odd a := (Nat.coprime_two_right).1 ha2
    have hbOdd : Odd b := (Nat.coprime_two_right).1 hb2
    have ha0 : a ≠ 0 := by
      intro h0
      simpa [h0] using haOdd
    have hb0 : b ≠ 0 := by
      intro h0
      simpa [h0] using hbOdd
    split_ifs at * with hab
    · exact jacobiSym.mul_right' (d : ℤ) ha0 hb0
    · exact (hab (Nat.coprime_mul_iff_left.2 ⟨ha, hb⟩)).elim

@[simp] lemma attachedQuadraticCharacter_apply_coprime {d m n : ℕ}
    (hdvd : 4 * d ∣ m) (hn : Nat.Coprime n m) :
    attachedQuadraticCharacter d m hdvd n = jacobiSym (d : ℤ) n := by
  simp [attachedQuadraticCharacter, hn]

@[simp] lemma attachedQuadraticCharacter_apply_not_coprime {d m n : ℕ}
    (hdvd : 4 * d ∣ m) (hn : ¬ Nat.Coprime n m) :
    attachedQuadraticCharacter d m hdvd n = 0 := by
  simp [attachedQuadraticCharacter, hn]

/-- If the attached character takes the value `1` at a prime `p`, then `p` is an odd prime
not dividing `m`, and `d` is a quadratic residue modulo `p`.

This is the exact downstream interface needed in the two contradiction arguments. -/
private lemma attachedQuadraticCharacter_spec
    {d m p : ℕ} (hdvd : 4 * d ∣ m)
    (hp : p.Prime)
    (hχ : attachedQuadraticCharacter d m hdvd p = 1) :
    p ≠ 2 ∧ ¬ p ∣ m ∧ QuadResidueMod d p := by
  have hcop : Nat.Coprime p m := by
    by_contra hnot
    have hzero : attachedQuadraticCharacter d m hdvd p = 0 := by
      simp [attachedQuadraticCharacter, hnot]
    have h01 : (0 : ℤ) = 1 := by
      simpa [hzero] using hχ
    norm_num at h01
  have hpndvd : ¬ p ∣ m := (hp.coprime_iff_not_dvd).1 hcop
  have hp2 : p ≠ 2 := by
    intro hp2
    apply hpndvd
    simpa [hp2] using two_dvd_of_four_d_dvd hdvd
  have hJacobi : jacobiSym (d : ℤ) p = 1 := by
    rw [attachedQuadraticCharacter_apply_coprime hdvd hcop] at hχ
    exact hχ
  haveI : Fact p.Prime := ⟨hp⟩
  have hsqInt : IsSquare ((d : ℤ) : ZMod p) :=
    ZMod.isSquare_of_jacobiSym_eq_one (a := (d : ℤ)) (p := p) hJacobi
  have hsq : IsSquare (d : ZMod p) := by
    rcases hsqInt with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa using hx
  exact ⟨hp2, hpndvd, quadResidueMod_of_isSquare_zmod hsq⟩

/-! ## Pollack specialized to the exact bound used in the paper -/

/-- The `A = 1`, `ε = 1/8` specialization of Pollack, reduced to the only output needed later:
the existence of one Pollack-sized odd prime with `d` a quadratic residue modulo `p`.

This is the abstraction boundary for the rest of the file.  All later arguments use only this
lemma, and never the full cardinality statement of `Pollack17.theorem_1_3`. -/
lemma exists_small_prime_from_pollack :
    ∃ M0 : ℕ, ∀ {m d : ℕ}, M0 ≤ m → 4 * d ∣ m →
      ∃ p : ℕ,
        p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ m ∧
        (p : ℝ) ≤ Real.rpow (m : ℝ) ((3 : ℝ) / 8) ∧
        QuadResidueMod d p := by
  classical
  obtain ⟨m0, hm0⟩ :=
    Pollack17.theorem_1_3 ((1 : ℝ) / 8) 1 (by norm_num) (by norm_num)
  refine ⟨max (m0 + 1) 2, ?_⟩
  intro m d hm hdvd
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm2
  haveI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  set χ : QuadraticCharacterMod m := attachedQuadraticCharacter d m hdvd
  set P : Finset ℕ :=
    Pollack17.residuePrimesUpTo m χ.toDirichletCharacterComplex ((1 : ℝ) / 8)
  have hgt : m > m0 := by
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self m0) (le_trans (le_max_left _ _) hm)
  have hcard : Real.rpow (Real.log (m : ℝ)) 1 ≤ (P.card : ℝ) := by
    simpa [P] using
      hm0 m hgt χ.toDirichletCharacterComplex χ.toDirichletCharacterComplex_isQuadratic
  have hcard' : Real.log (m : ℝ) ≤ (P.card : ℝ) := by
    simpa using hcard
  have hm1_real : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm2)
  have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm1_real
  have hcard_pos : 0 < P.card := by
    by_contra hcard_not
    have hcard0 : P.card = 0 := Nat.eq_zero_of_not_pos hcard_not
    have hcard_pos_real : (0 : ℝ) < (P.card : ℝ) := lt_of_lt_of_le hlog_pos hcard'
    have : (0 : ℝ) < 0 := by
      simpa [hcard0] using hcard_pos_real
    exact (lt_irrefl (0 : ℝ)) this
  obtain ⟨p, hpP⟩ := Finset.card_pos.mp hcard_pos
  have hpP' : p ∈ Pollack17.residuePrimesUpTo m χ.toDirichletCharacterComplex ((1 : ℝ) / 8) := by
    simpa [P] using hpP
  simp [Pollack17.residuePrimesUpTo, Pollack17.residuePrimeUpperBound] at hpP'
  rcases hpP' with ⟨_, hpp, hpbound, hχpComplex⟩
  have hχp : χ p = 1 := by
    exact χ.eq_one_of_toDirichletCharacterComplex_apply_nat_eq_one
      (n := p) (by simpa using hχpComplex)
  have hspec : p ≠ 2 ∧ ¬ p ∣ m ∧ QuadResidueMod d p := by
    simpa [χ] using attachedQuadraticCharacter_spec (d := d) (m := m) (p := p) hdvd hpp hχp
  rcases hspec with ⟨hp2, hpndvd, hres⟩
  refine ⟨p, hpp, hp2, hpndvd, ?_, hres⟩
  convert hpbound using 1 <;> norm_num

/-! ## Turning quadratic residuosity into solvability of `a*x^2 ≡ n [MOD p]` -/

/-- In the non-square case, Pollack gives `d` as a quadratic residue.  Combined with
`u^2*d = a*n` and `p ∤ a*n`, this yields solvability of `a*x^2 ≡ n [MOD p]`. -/
lemma solvable_of_squarefree_part
    {a n u d p : ℕ}
    (hdecomp : u ^ 2 * d = a * n)
    (hp : p.Prime)
    (hpn : ¬ p ∣ a * n)
    (hres : QuadResidueMod d p) :
    SolvableAX2EqNMod a n p := by
  obtain ⟨y, hy⟩ := hres
  have hpa : ¬ p ∣ a := by
    intro hpa
    exact hpn (dvd_mul_of_dvd_left hpa n)
  have hcop : Nat.Coprime a p := (hp.coprime_iff_not_dvd.2 hpa).symm
  have hfermat : Nat.ModEq p (a ^ (p - 1)) 1 :=
    Nat.ModEq.pow_card_sub_one_eq_one hp hcop
  let b : ℕ := a * a ^ (p - 2)
  have hp2le : 2 ≤ p := hp.two_le
  have hp_sub : p - 1 = (p - 2) + 1 := by
    omega
  have hb : Nat.ModEq p b 1 := by
    dsimp [b]
    simpa [hp_sub, Nat.pow_add, pow_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      hfermat
  have hb2 : Nat.ModEq p (b ^ 2) 1 := by
    simpa using Nat.ModEq.pow 2 hb
  have hsq : Nat.ModEq p ((u * y) ^ 2) (a * n) := by
    have hmul : Nat.ModEq p (u ^ 2 * y ^ 2) (u ^ 2 * d) := hy.mul_left (u ^ 2)
    have hmul' : Nat.ModEq p ((u * y) ^ 2) (u ^ 2 * d) := by
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    rw [← hdecomp]
    exact hmul'
  let x : ℕ := u * y * a ^ (p - 2)
  have hax : Nat.ModEq p (a * x ^ 2) (n * b ^ 2) := by
    have hmul :
        Nat.ModEq p (((u * y) ^ 2) * (a ^ (p - 2)) ^ 2)
          ((a * n) * (a ^ (p - 2)) ^ 2) :=
      hsq.mul_right ((a ^ (p - 2)) ^ 2)
    have hmul' :
        Nat.ModEq p (a * (((u * y) ^ 2) * (a ^ (p - 2)) ^ 2))
          (a * ((a * n) * (a ^ (p - 2)) ^ 2)) :=
      hmul.mul_left a
    simpa [x, b, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul'
  have hnb : Nat.ModEq p (n * b ^ 2) n := by
    simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hb2.mul_left n
  exact ⟨x, hax.trans hnb⟩

/-- In the square case `a*n = u^2`, every odd prime `p ∤ a*n` makes `a*x^2 ≡ n [MOD p]`
solvable. -/
private lemma solvable_of_square_case
    {a n u p : ℕ}
    (hsq : u ^ 2 = a * n)
    (hp : p.Prime)
    (hpn : ¬ p ∣ a * n) :
    SolvableAX2EqNMod a n p := by
  have hdecomp : u ^ 2 * 1 = a * n := by
    simpa using hsq
  exact solvable_of_squarefree_part hdecomp hp hpn (one_is_quad_residue p)

/-! ## Candidate set bounds -/

/-- If `Pa a n` holds, then for any prime `p` there is at most one candidate `k`.
Indeed, `p ∣ n - a*k^2` and primality force `n - a*k^2 = p`, and that equation has at most one
positive solution in `k`. -/
private lemma candidateKs_card_le_one
    {a n p : ℕ}
    (ha : 1 ≤ a)
    (hPa : Pa a n)
    (hp : p.Prime) :
    (candidateKs a n p).card ≤ 1 := by
  refine Finset.card_le_one.2 ?_
  intro k1 hk1 k2 hk2
  rw [candidateKs, Finset.mem_filter] at hk1 hk2
  rcases hk1 with ⟨_, hk1_pos, hk1_lt, hk1_coprime, hk1_mod⟩
  rcases hk2 with ⟨_, hk2_pos, hk2_lt, hk2_coprime, hk2_mod⟩
  have hprime1 : Nat.Prime (n - a * k1 ^ 2) := hPa k1 hk1_pos hk1_coprime hk1_lt
  have hprime2 : Nat.Prime (n - a * k2 ^ 2) := hPa k2 hk2_pos hk2_coprime hk2_lt
  have hdiv1 : p ∣ n - a * k1 ^ 2 :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hk1_lt)).1 hk1_mod
  have hdiv2 : p ∣ n - a * k2 ^ 2 :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hk2_lt)).1 hk2_mod
  have hEq1 : p = n - a * k1 ^ 2 := (Nat.prime_dvd_prime_iff_eq hp hprime1).1 hdiv1
  have hEq2 : p = n - a * k2 ^ 2 := (Nat.prime_dvd_prime_iff_eq hp hprime2).1 hdiv2
  let t1 : ℕ := a * k1 ^ 2
  let t2 : ℕ := a * k2 ^ 2
  have ht1lt : t1 < n := by
    simpa [t1] using hk1_lt
  have ht2lt : t2 < n := by
    simpa [t2] using hk2_lt
  have ht1eq : p = n - t1 := by
    simpa [t1] using hEq1
  have ht2eq : p = n - t2 := by
    simpa [t2] using hEq2
  have ht12 : t1 = t2 := by
    omega
  have hsq_eq : k1 ^ 2 = k2 ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < a by simpa using ha)
    simpa [t1, t2] using ht12
  exact Nat.pow_left_injective (show (2 : ℕ) ≠ 0 by decide) hsq_eq

/-! ### Counting helpers for `many_candidates_of_pollack_size` -/

private lemma factorial_card_le_prod_of_one_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  classical
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hidx : ∀ i : ℕ, ∀ hi : i < s.card, i + 1 ≤ f ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
        have hmem : f ⟨0, hi⟩ ∈ s := by
          simpa [f] using s.orderEmbOfFin_mem rfl ⟨0, hi⟩
        simpa [f] using hs (f ⟨0, hi⟩) hmem
    | succ i ih =>
        have hi' : i < s.card := Nat.lt_of_succ_lt hi
        have hprev : i + 1 ≤ f ⟨i, hi'⟩ := ih hi'
        have hlt : f ⟨i, hi'⟩ < f ⟨i + 1, hi⟩ := by
          exact f.strictMono (Nat.lt_succ_self i)
        exact le_trans (Nat.succ_le_succ hprev) (Nat.succ_le_of_lt hlt)
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, f i := by
    refine Finset.prod_le_prod' ?_
    intro i _
    exact hidx i.1 i.2
  have hleft : (∏ i : Fin s.card, (i.1 + 1)) = Nat.factorial s.card := by
    calc
      (∏ i : Fin s.card, (i.1 + 1)) = ∏ i ∈ Finset.range s.card, (i + 1) := by
        simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) s.card)
      _ = Nat.factorial s.card := Finset.prod_range_add_one_eq_factorial s.card
  have hright : (∏ i : Fin s.card, f i) = ∏ x ∈ s, x := by
    calc
      (∏ i : Fin s.card, f i) = ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
        symm
        simpa [f] using
          (Finset.prod_map (s := Finset.univ) (e := (s.orderEmbOfFin rfl).toEmbedding)
            (f := fun x : ℕ => x))
      _ = ∏ x ∈ s, x := by
        rw [Finset.map_orderEmbOfFin_univ (s := s) (h := rfl)]
  calc
    Nat.factorial s.card = ∏ i : Fin s.card, (i.1 + 1) := hleft.symm
    _ ≤ ∏ i : Fin s.card, f i := hprod
    _ = ∏ x ∈ s, x := hright

private lemma factorial_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    Nat.factorial n.primeFactors.card ≤ n := by
  have h1 : Nat.factorial n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    factorial_card_le_prod_of_one_le _ (by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).one_le)
  exact le_trans h1 (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))

private lemma two_pow_primeFactors_card_le_rpow_sixteenth_eventually :
    ∃ Nω : ℕ, ∀ {n : ℕ}, Nω ≤ n →
      (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / 16) := by
  have hfact : ∀ᶠ k : ℕ in Filter.atTop, (2 ^ 16) ^ k < Nat.factorial (k - 1) := by
    simpa using (Nat.eventually_pow_lt_factorial_sub (2 ^ 16) 1)
  rcases Filter.eventually_atTop.mp hfact with ⟨k0, hk0⟩
  refine ⟨max 3 ((2 ^ k0) ^ 16), ?_⟩
  intro n hn
  let k := n.primeFactors.card
  have hn3 : 3 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnpos : 0 < n := by omega
  by_cases hk_small : k < k0
  · have hk_le : k ≤ k0 := hk_small.le
    have hpow_nat : (2 ^ k : ℕ) ≤ 2 ^ k0 :=
      Nat.pow_le_pow_right Nat.zero_lt_two hk_le
    have hpow_real : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k0 := by
      exact_mod_cast hpow_nat
    have hconst_nat : ((2 ^ k0 : ℕ) ^ 16) ≤ n :=
      le_trans (Nat.le_max_right _ _) hn
    have hconst16_real : (((2 : ℝ) ^ k0) ^ (16 : ℕ)) ≤ (n : ℝ) := by
      exact_mod_cast hconst_nat
    have hconst_le' :
        (((2 : ℝ) ^ k0) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) ≤
          (n : ℝ) ^ ((1 : ℝ) / 16) := by
      exact Real.rpow_le_rpow
        (show 0 ≤ (((2 : ℝ) ^ k0) ^ (16 : ℕ)) by positivity)
        hconst16_real
        (by norm_num : 0 ≤ ((1 : ℝ) / 16))
    have hnonneg_k0 : 0 ≤ (2 : ℝ) ^ k0 := by positivity
    have hroot : (((2 : ℝ) ^ k0) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) = (2 : ℝ) ^ k0 := by
      simpa [one_div] using Real.pow_rpow_inv_natCast hnonneg_k0 (by norm_num : (16 : ℕ) ≠ 0)
    rw [hroot] at hconst_le'
    exact hpow_real.trans hconst_le'
  · have hk_ge : k0 ≤ k := Nat.le_of_not_gt hk_small
    have hmain_nat : (2 ^ 16) ^ k < Nat.factorial k := by
      exact lt_of_lt_of_le (hk0 k hk_ge) (Nat.factorial_le (Nat.sub_le _ _))
    have hk_fact_le_n : Nat.factorial k ≤ n := by
      simpa [k] using factorial_card_primeFactors_le n (Nat.ne_of_gt hnpos)
    have hpow16_nat' : (2 ^ 16) ^ k ≤ n := le_trans (Nat.le_of_lt hmain_nat) hk_fact_le_n
    have hpow16_nat : (2 ^ k : ℕ) ^ 16 ≤ n := by
      calc
        (2 ^ k : ℕ) ^ 16 = 2 ^ (k * 16) := by rw [pow_mul]
        _ = 2 ^ (16 * k) := by rw [Nat.mul_comm]
        _ = (2 ^ 16) ^ k := by rw [pow_mul]
        _ ≤ n := hpow16_nat'
    have hpow16_real : (((2 : ℝ) ^ k) ^ (16 : ℕ)) ≤ (n : ℝ) := by
      exact_mod_cast hpow16_nat
    have hgoal' :
        (((2 : ℝ) ^ k) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) ≤
          (n : ℝ) ^ ((1 : ℝ) / 16) := by
      exact Real.rpow_le_rpow
        (show 0 ≤ (((2 : ℝ) ^ k) ^ (16 : ℕ)) by positivity)
        hpow16_real
        (by norm_num : 0 ≤ ((1 : ℝ) / 16))
    have hnonneg_k : 0 ≤ (2 : ℝ) ^ k := by positivity
    have hroot : (((2 : ℝ) ^ k) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) = (2 : ℝ) ^ k := by
      simpa [one_div] using Real.pow_rpow_inv_natCast hnonneg_k (by norm_num : (16 : ℕ) ≠ 0)
    rw [hroot] at hgoal'
    exact hgoal'

private lemma nat_rpow_sixteenth_div_log_eventually_large (N : ℝ) :
    ∃ N0 : ℕ, 3 ≤ N0 ∧ ∀ n : ℕ, N0 ≤ n →
      N ≤ (n : ℝ) ^ ((1 : ℝ) / 16) / (3 * Real.log n) := by
  have h_tend : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 16) / (3 * Real.log n))
      Filter.atTop Filter.atTop := by
    have h_aux : Filter.Tendsto (fun u : ℝ ↦ Real.exp u / (48 * u)) Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun u : ℝ ↦ Real.exp u / u) Filter.atTop Filter.atTop := by
        simpa using Real.tendsto_exp_div_pow_atTop 1
      convert Filter.Tendsto.atTop_div_const (show 0 < (48 : ℝ) by norm_num) h1 using 1 with u
      ring_nf
    have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log n / 16) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_div_const (show 0 < (16 : ℝ) by norm_num) <|
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact (h_aux.comp hlog).congr' (by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hlog16 : Real.log n / 16 = Real.log n * ((1 : ℝ) / 16) := by ring
      have hden' : 48 * (Real.log n * ((1 : ℝ) / 16)) = 3 * Real.log n := by ring
      simp only [Function.comp_apply]
      rw [Real.rpow_def_of_pos hn', hlog16, hden'])
  rcases Filter.eventually_atTop.1 (h_tend.eventually_ge_atTop N) with ⟨N0, hN0⟩
  refine ⟨max N0 3, le_max_right _ _, ?_⟩
  intro n hn
  exact hN0 n (le_trans (le_max_left _ _) hn)

private lemma mem_finset_inf_iff {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α]
    {s : Finset ι} {f : ι → Finset α} {a : α} :
    a ∈ s.inf f ↔ ∀ i ∈ s, a ∈ f i := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert b s hb ih =>
      simp [Finset.inf_insert, hb, ih]

private lemma count_root_class_with_divisors
    {n p r K : ℕ} (hp : p.Prime) (hn0 : n ≠ 0) (hpn : ¬ p ∣ n)
    (t : Finset ℕ) (ht : t ⊆ n.primeFactors) :
    ∃ v : ℕ,
      #{k ∈ (Finset.range K) | Nat.ModEq p k r ∧ ∀ q ∈ t, q ∣ k}
        = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
  classical
  let d : ℕ := ∏ q ∈ t, q
  have hp_coprime_d : Nat.Coprime p d := by
    refine Nat.coprime_prod_right_iff.mpr ?_
    intro q hq
    have hqmem : q ∈ n.primeFactors := ht hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hpq : p ≠ q := by
      intro hpq
      apply hpn
      simpa [hpq] using (Nat.dvd_of_mem_primeFactors hqmem)
    exact (Nat.coprime_primes hp hqprime).2 hpq
  have hpair : Set.Pairwise (↑t : Set ℕ) (fun q q' : ℕ ↦ Nat.Coprime q q') := by
    intro q hq q' hq' hqq'
    exact (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (ht hq))
      (Nat.prime_of_mem_primeFactors (ht hq'))).2 hqq'
  have hlcm : t.lcm (fun q : ℕ ↦ q) = d := by
    simpa [d] using (Finset.lcm_eq_prod (s := t) (f := fun q : ℕ ↦ q) hpair)
  have hdiv_iff : ∀ k : ℕ, (∀ q ∈ t, q ∣ k) ↔ d ∣ k := by
    intro k
    simpa [d, hlcm] using
      (Finset.lcm_dvd_iff (s := t) (f := fun q : ℕ ↦ q) (a := k)).symm
  let v : ℕ := Nat.chineseRemainder hp_coprime_d r 0
  have hvp : Nat.ModEq p v r := by
    simpa [v] using (Nat.chineseRemainder hp_coprime_d r 0).prop.1
  have hvd : Nat.ModEq d v 0 := by
    simpa [v] using (Nat.chineseRemainder hp_coprime_d r 0).prop.2
  refine ⟨v, ?_⟩
  rw [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hkK, hkpr, hkt⟩
    refine ⟨hkK, ?_⟩
    have hk0 : d ∣ k := (hdiv_iff k).1 hkt
    simpa [d, v] using
      (Nat.chineseRemainder_modEq_unique hp_coprime_d hkpr
        (Nat.modEq_zero_iff_dvd.2 hk0))
  · rintro ⟨hkK, hk⟩
    have hk' : Nat.ModEq p k v ∧ Nat.ModEq d k v := by
      have hk'' : Nat.ModEq (p * d) k v := by
        simpa [d] using hk
      exact (Nat.modEq_and_modEq_iff_modEq_mul hp_coprime_d).mpr hk''
    refine ⟨hkK, hk'.1.trans hvp, ?_⟩
    exact (hdiv_iff k).2 <| Nat.modEq_zero_iff_dvd.1 (hk'.2.trans hvd)

private lemma root_class_good_count_lower_bound
    {a n p r K : ℕ}
    (ha : 1 ≤ a)
    (hn3 : 3 ≤ n)
    (hp : p.Prime)
    (hpndvd : ¬ p ∣ a * n)
    (hroot : Nat.ModEq p (a * r ^ 2) n)
    (hK : K = Nat.sqrt ((n - 1) / a) + 1) :
    let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
    let α := {k : ℕ // k ∈ U}
    let emb : α ↪ ℕ := ⟨Subtype.val, by intro x y h; exact Subtype.ext h⟩
    let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
    let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
    ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by
  classical
  let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
  let α := {k : ℕ // k ∈ U}
  let emb : α ↪ ℕ := ⟨Subtype.val, by intro x y h; exact Subtype.ext h⟩
  let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
  let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
  change ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card
  have hn0 : n ≠ 0 := by omega
  have hpn : ¬ p ∣ n := by
    intro hpn
    exact hpndvd (dvd_mul_of_dvd_right hpn a)

  have hIE : ((good.map emb).card : ℤ) =
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℤ) ^ t.card * ((t.inf S).card : ℤ) := by
    rw [Finset.card_map]
    simpa [good] using
      (Finset.inclusion_exclusion_card_inf_compl (s := n.primeFactors) (S := S))

  have hIE_real : ((good.map emb).card : ℝ) =
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    exact_mod_cast hIE

  have hterm :
      ∀ t ∈ n.primeFactors.powerset,
        (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q)) - 1 ≤
          (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    intro t ht
    have htsub : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
    obtain ⟨v, hv⟩ :=
      count_root_class_with_divisors (n := n) (p := p) (r := r) (K := K) hp hn0 hpn t htsub
    have hmap :
        (t.inf S).map emb =
          (Finset.range K).filter fun k ↦ Nat.ModEq p k r ∧ ∀ q ∈ t, q ∣ k := by
      ext k
      constructor
      · intro hk
        rcases Finset.mem_map.mp hk with ⟨x, hx, rfl⟩
        have hxU : (x : ℕ) ∈ U := x.property
        rcases Finset.mem_filter.mp hxU with ⟨hxK, hxr⟩
        have hxdiv : ∀ q ∈ t, q ∣ (x : ℕ) := by
          intro q hq
          have hxq : x ∈ S q :=
            (mem_finset_inf_iff (s := t) (f := S) (a := x)).1 hx q hq
          simpa [S] using hxq
        exact Finset.mem_filter.mpr ⟨hxK, ⟨hxr, hxdiv⟩⟩
      · intro hk
        rcases Finset.mem_filter.mp hk with ⟨hkK, hkcond⟩
        rcases hkcond with ⟨hkr, hkdiv⟩
        have hkU : k ∈ U := Finset.mem_filter.mpr ⟨hkK, hkr⟩
        let x : α := ⟨k, hkU⟩
        have hx : x ∈ t.inf S := by
          refine (mem_finset_inf_iff (s := t) (f := S) (a := x)).2 ?_
          intro q hq
          simpa [x, S] using hkdiv q hq
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hcard_map :
        ((t.inf S).map emb).card = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
      simpa [hmap] using hv
    have hcard_eq_count :
        (t.inf S).card = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
      simpa using hcard_map
    let m : ℕ := p * ∏ q ∈ t, q
    have hm_pos : 0 < m := by
      dsimp [m]
      refine Nat.mul_pos hp.pos ?_
      refine Finset.prod_pos ?_
      intro q hq
      exact (Nat.prime_of_mem_primeFactors (htsub hq)).pos
    have hcount_formula :
        (t.inf S).card = K / m + if v % m < K % m then 1 else 0 := by
      rw [hcard_eq_count, Nat.count_modEq_card (b := K) (r := m) (hr := hm_pos) v]
    have hcount_formula_real :
        ((t.inf S).card : ℝ) =
          ((K / m : ℕ) : ℝ) + ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast hcount_formula
    have hdiv_le : ((K / m : ℕ) : ℝ) ≤ (K : ℝ) / m := Nat.cast_div_le
    have hm_posR : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hlt_nat : K < (K / m + 1) * m := by
      exact (Nat.div_lt_iff_lt_mul hm_pos).mp (Nat.lt_succ_self _)
    have hlt_real : (K : ℝ) < ((((K / m : ℕ) : ℝ) + 1) * m) := by
      exact_mod_cast hlt_nat
    have hdiv_lt : (K : ℝ) / m < ((K / m : ℕ) : ℝ) + 1 := by
      exact (div_lt_iff₀ hm_posR).2 hlt_real
    have hbit_nonneg :
        (0 : ℝ) ≤ ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) := by
      split_ifs <;> norm_num
    have hbit_le_one :
        ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
      split_ifs <;> norm_num
    have hlower : (K : ℝ) / m - 1 ≤ ((t.inf S).card : ℝ) := by
      rw [hcount_formula_real]
      have hq_ge : (K : ℝ) / m - 1 ≤ (K / m : ℝ) := by
        linarith
      linarith
    have hupper : ((t.inf S).card : ℝ) ≤ (K : ℝ) / m + 1 := by
      rw [hcount_formula_real]
      linarith
    rcases neg_one_pow_eq_or ℝ t.card with hsgn | hsgn
    · rw [hsgn]
      simpa [m] using hlower
    · rw [hsgn]
      have hupper' : ((t.inf S).card : ℝ) ≤ (K : ℝ) / (p * ∏ q ∈ t, q) + 1 := by
        simpa [m] using hupper
      linarith

  have hsum_lower :
      ∑ t ∈ n.primeFactors.powerset,
        ((-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q)) - 1)
        ≤ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    exact Finset.sum_le_sum (fun t ht ↦ hterm t ht)

  have hsum_lower' :
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
        - ∑ t ∈ n.primeFactors.powerset, (1 : ℝ)
        ≤ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    simpa [Finset.sum_sub_distrib] using hsum_lower

  have hmain_expand :
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
        = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
    calc
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
          = ∑ t ∈ n.primeFactors.powerset,
              (-1 : ℝ) ^ t.card * ((K : ℝ) / p * ∏ q ∈ t, (1 / (q : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              have htsub : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
              have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
              have hprod_pos : 0 < ∏ q ∈ t, (q : ℝ) := by
                refine Finset.prod_pos ?_
                intro q hq
                exact_mod_cast (Nat.prime_of_mem_primeFactors (htsub hq)).pos
              have hprod_ne0 : (∏ q ∈ t, (q : ℝ)) ≠ 0 := by
                exact ne_of_gt hprod_pos
              have hprod_inv :
                  ∏ q ∈ t, (1 / (q : ℝ)) = 1 / ∏ q ∈ t, (q : ℝ) := by
                calc
                  ∏ q ∈ t, (1 / (q : ℝ)) = ∏ q ∈ t, ((q : ℝ)⁻¹) := by
                    simp [one_div]
                  _ = (∏ q ∈ t, (q : ℝ))⁻¹ := by
                    rw [Finset.prod_inv_distrib]
                  _ = 1 / ∏ q ∈ t, (q : ℝ) := by
                    simp [one_div]
              rw [hprod_inv]
              have hcast_prod : ((∏ q ∈ t, q : ℕ) : ℝ) = ∏ q ∈ t, (q : ℝ) := by
                simp
              rw [hcast_prod]
              field_simp [hp0, hprod_ne0]
      _ = ∑ t ∈ n.primeFactors.powerset,
            (K : ℝ) / p * ((-1 : ℝ) ^ t.card * ∏ q ∈ t, (1 / (q : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring
      _ = (K : ℝ) / p * ∑ t ∈ n.primeFactors.powerset,
            (-1 : ℝ) ^ t.card * ∏ q ∈ t, (1 / (q : ℝ)) := by
          symm
          rw [Finset.mul_sum]
      _ = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
          congr 1
          symm
          simpa using
            (Finset.prod_sub (s := n.primeFactors) (f := fun _ : ℕ => (1 : ℝ))
              (g := fun q : ℕ => 1 / (q : ℝ)))

  have herror :
      ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) = (2 : ℝ) ^ n.primeFactors.card := by
    calc
      ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) = (n.primeFactors.powerset.card : ℝ) := by simp
      _ = (2 : ℝ) ^ n.primeFactors.card := by simp

  calc
    ((good.map emb).card : ℝ)
        = ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := hIE_real
    _ ≥ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
          - ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) := hsum_lower'
    _ = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by rw [hmain_expand, herror]

private lemma mertens_primeFactors_lower_bound {n : ℕ} (hn3 : 3 ≤ n) :
    1 / (3 * Real.log n)
      ≤ ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
  let t : Finset ℕ := (Finset.range (n + 1)).filter Prime
  let f : ℕ → ℝ := fun q ↦ 1 - 1 / (q : ℝ)
  have hsubset : n.primeFactors ⊆ t := by
    intro q hq
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors hq)),
      Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hq)⟩
  have hfactor_nonneg : ∀ q ∈ t, 0 ≤ f q := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_iff.mpr (Finset.mem_filter.mp hq).2
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
    have hq_ge1 : (1 : ℝ) ≤ q := by exact_mod_cast hqprime.one_le
    have hdiv_le : 1 / (q : ℝ) ≤ 1 :=
      by simpa using (one_div_le_one_div_of_le zero_lt_one hq_ge1)
    nlinarith
  have hfactor_le_one : ∀ q ∈ t, f q ≤ 1 := by
    intro q hq
    have hdiv_nonneg : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    nlinarith
  have hs_nonneg : 0 ≤ ∏ q ∈ n.primeFactors, f q := by
    refine Finset.prod_nonneg ?_
    intro q hq
    exact hfactor_nonneg q (hsubset hq)
  have hextra_le_one : ∏ q ∈ t \ n.primeFactors, f q ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro q hq
      exact hfactor_nonneg q (Finset.mem_sdiff.mp hq).1
    · intro q hq
      exact hfactor_le_one q (Finset.mem_sdiff.mp hq).1
  have hprod_le : ∏ q ∈ t, f q ≤ ∏ q ∈ n.primeFactors, f q := by
    calc
      ∏ q ∈ t, f q = (∏ q ∈ t \ n.primeFactors, f q) * ∏ q ∈ n.primeFactors, f q := by
        symm
        exact Finset.prod_sdiff hsubset
      _ ≤ 1 * ∏ q ∈ n.primeFactors, f q := by
        exact mul_le_mul_of_nonneg_right hextra_le_one hs_nonneg
      _ = ∏ q ∈ n.primeFactors, f q := by simp
  have hmertens : 1 / (3 * Real.log n) ≤ ∏ q ∈ t, f q := by
    simpa [t, f] using mertens_third_theorem n hn3
  exact le_trans hmertens hprod_le

/-- Main counting lemma.

For fixed `a`, if `p` is an odd prime of Pollack-size, `p ∤ a*n`, and
`a*x^2 ≡ n [MOD p]` is solvable, then for all sufficiently large `n`
there are more than one candidates.

This is exactly where the Möbius-inversion count and `mertens_third_theorem` enter.
In this formalization, it is enough to count one chosen root class modulo `p`; the
factor `2` from the paper is not needed. -/
private lemma many_candidates_of_pollack_size
    (a : ℕ)
    (ha : 1 ≤ a) :
    ∃ N0 : ℕ, ∀ {n p : ℕ},
      N0 ≤ n →
      p.Prime →
      p ≠ 2 →
      ¬ p ∣ a * n →
      SolvableAX2EqNMod a n p →
      (p : ℝ) ≤ pollackSizeBound a n →
      1 < (candidateKs a n p).card := by
  classical
  obtain ⟨Nω, hω⟩ := two_pow_primeFactors_card_le_rpow_sixteenth_eventually
  obtain ⟨Nmain, hNmain_ge3, hmain⟩ := nat_rpow_sixteenth_div_log_eventually_large (48 * a)
  refine ⟨max Nω Nmain, ?_⟩
  intro n p hn hp hp2 hpndvd hsol hpbound
  have hnω : Nω ≤ n := le_trans (le_max_left _ _) hn
  have hnmain : Nmain ≤ n := le_trans (le_max_right _ _) hn
  have hn3 : 3 ≤ n := le_trans hNmain_ge3 hnmain
  have hn0 : n ≠ 0 := by omega
  let x : ℕ := Classical.choose hsol
  have hx : Nat.ModEq p (a * x ^ 2) n := Classical.choose_spec hsol
  let r : ℕ := x % p
  have hr_root : Nat.ModEq p (a * r ^ 2) n := by
    have hxr : Nat.ModEq p r x := Nat.mod_modEq x p
    exact ((Nat.ModEq.pow 2 hxr).mul_left a).trans hx
  have hr_lt_p : r < p := by
    dsimp [r]
    exact Nat.mod_lt _ hp.pos
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    have hmod : Nat.ModEq p n 0 := by
      simpa [r, hr0] using hr_root.symm
    have hpdvdn : p ∣ n := (Nat.modEq_zero_iff_dvd.mp hmod)
    exact hpndvd (dvd_mul_of_dvd_right hpdvdn a)
  let K : ℕ := Nat.sqrt ((n - 1) / a) + 1
  let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
  let α := {k : ℕ // k ∈ U}
  let emb : α ↪ ℕ := ⟨Subtype.val, by intro x y h; exact Subtype.ext h⟩
  let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
  let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
  have hgood_sub : good.map emb ⊆ candidateKs a n p := by
    intro k hk
    rcases Finset.mem_map.mp hk with ⟨y, hy, rfl⟩
    have hyU : (y : ℕ) ∈ U := y.property
    have hy_ltK : (y : ℕ) < K := by
      simpa [U] using (Finset.mem_filter.mp hyU).1
    have hy_mod : Nat.ModEq p (y : ℕ) r := by
      simpa [U] using (Finset.mem_filter.mp hyU).2
    have hy_notdvd : ∀ q ∈ n.primeFactors, ¬ q ∣ (y : ℕ) := by
      intro q hq
      have hyq : y ∈ (S q)ᶜ :=
        (mem_finset_inf_iff (s := n.primeFactors) (f := fun q ↦ (S q)ᶜ) (a := y)).1 hy q hq
      simpa [S] using hyq
    have hy_ne_zero : (y : ℕ) ≠ 0 := by
      intro hy0
      have hzr : Nat.ModEq p 0 r := by simpa [hy0] using hy_mod
      have hpdvdr : p ∣ r := Nat.modEq_zero_iff_dvd.mp hzr.symm
      exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hr_ne_zero) hr_lt_p) hpdvdr
    have hy_pos : 1 ≤ (y : ℕ) := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hy_ne_zero)
    have hy_disj : Disjoint (y : ℕ).primeFactors n.primeFactors := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      exact hy_notdvd q hq2 (Nat.dvd_of_mem_primeFactors hq1)
    have hy_coprime : Nat.Coprime (y : ℕ) n := by
      exact (Nat.disjoint_primeFactors hy_ne_zero hn0).mp hy_disj
    have hy_le_sqrt : (y : ℕ) ≤ Nat.sqrt ((n - 1) / a) := by
      simpa [K] using Nat.lt_succ_iff.mp hy_ltK
    have hy_sq_le : (y : ℕ) ^ 2 ≤ (n - 1) / a := (Nat.le_sqrt'.mp hy_le_sqrt)
    have hy_quad_le : a * (y : ℕ) ^ 2 ≤ n - 1 := by
      exact le_trans (Nat.mul_le_mul_left a hy_sq_le) (Nat.mul_div_le (n - 1) a)
    have hy_pred_lt : n - 1 < n := by
      have hnpos : 0 < n := by omega
      rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)]
      exact Nat.lt_succ_self _
    have hy_quad : a * (y : ℕ) ^ 2 < n := lt_of_le_of_lt hy_quad_le hy_pred_lt
    have hy_sq_lt_n : (y : ℕ) ^ 2 < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ha) hy_quad
    have hy_lt_n : (y : ℕ) < n := by
      have hy_le_sq : (y : ℕ) ≤ (y : ℕ) ^ 2 := by
        simpa [pow_two] using Nat.le_mul_of_pos_right (y : ℕ) (Nat.pos_of_ne_zero hy_ne_zero)
      exact lt_of_le_of_lt hy_le_sq hy_sq_lt_n
    have hy_root : Nat.ModEq p (a * (y : ℕ) ^ 2) n := by
      exact (((Nat.ModEq.pow 2 hy_mod).mul_left a).trans hr_root)
    rw [candidateKs, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hy_lt_n, hy_pos, hy_quad, hy_coprime, hy_root⟩
  have hlower : ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by
    simpa [U, α, emb, S, good, K] using
      (root_class_good_count_lower_bound (a := a) (n := n) (p := p) (r := r) (K := K)
        ha hn3 hp hpndvd hr_root rfl)
  have hmertens : 1 / (3 * Real.log n)
      ≤ ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) :=
    mertens_primeFactors_lower_bound hn3
  have hmain' : (48 * a : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 16) / (3 * Real.log n) := hmain n hnmain
  have hω' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / 16) := hω hnω
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_le : p ≤ (4 * a * n : ℝ) ^ ((3 : ℝ) / 8) := by
    simpa [pollackSizeBound] using hpbound
  have hK_over_p : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
      ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
    have ha_pos_nat : 0 < a := by omega
    have hn_pos_nat : 0 < n := by omega
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha_pos_nat
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
    have hnpow16_pos : 0 < (n : ℝ) ^ ((1 : ℝ) / 16) := by positivity
    have h4a_ne : (4 * a : ℝ) ≠ 0 := by positivity
    have hpow16_ne : (n : ℝ) ^ ((1 : ℝ) / 16) ≠ 0 := hnpow16_pos.ne'
    have hKp_lower : (n : ℝ) ^ ((1 : ℝ) / 8) / (4 * a) ≤ (K : ℝ) / p := by
      have hKsq_nat : ((n - 1) / a + 1) ≤ K ^ 2 := by
        dsimp [K]
        simpa [pow_two] using Nat.succ_le_succ_sqrt' ((n - 1) / a)
      have hn_le_div_nat : n ≤ a * (((n - 1) / a) + 1) := by
        have hlt : n - 1 < a * (((n - 1) / a) + 1) := by
          calc
            n - 1 = a * ((n - 1) / a) + ((n - 1) % a) := by
              simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                (Nat.div_add_mod' (n - 1) a).symm
            _ < a * ((n - 1) / a) + a := by
              exact Nat.add_lt_add_left (Nat.mod_lt _ ha_pos_nat) _
            _ = a * (((n - 1) / a) + 1) := by ring
        rw [← Nat.succ_pred_eq_of_pos hn_pos_nat]
        exact Nat.succ_le_of_lt hlt
      have hn_le_aKsq_nat : n ≤ a * K ^ 2 := by
        calc
          n ≤ a * (((n - 1) / a) + 1) := hn_le_div_nat
          _ ≤ a * K ^ 2 := Nat.mul_le_mul_left _ hKsq_nat
      have hn_le_aKsq : (n : ℝ) ≤ a * (K : ℝ) ^ 2 := by
        exact_mod_cast hn_le_aKsq_nat
      have hna_div : (n : ℝ) / a ≤ (K : ℝ) ^ 2 := by
        exact (div_le_iff₀ ha_pos).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hn_le_aKsq
      have hsqrt_leK : ((n : ℝ) / a) ^ ((1 : ℝ) / 2) ≤ K := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
        exact ⟨by positivity, hna_div⟩
      have hmid :
          ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (4 * a * n : ℝ) ^ ((3 : ℝ) / 8)
            ≤ (K : ℝ) / p := by
        have h1 :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (4 * a * n : ℝ) ^ ((3 : ℝ) / 8)
              ≤ ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / p := by
          exact div_le_div_of_nonneg_left (by positivity) hp_pos hp_le
        have h2 :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / p ≤ (K : ℝ) / p := by
          exact div_le_div_of_nonneg_right hsqrt_leK hp_pos.le
        exact le_trans h1 h2
      have hbase :
          (n : ℝ) ^ ((1 : ℝ) / 8) / (4 * a)
            ≤ ((n : ℝ) / a) ^ ((1 : ℝ) / 2) / (4 * a * n : ℝ) ^ ((3 : ℝ) / 8) := by
        have h4a_pos : 0 < (4 * a : ℝ) := by positivity
        have h4an_pos : 0 < (4 * a * n : ℝ) ^ ((3 : ℝ) / 8) := by positivity
        rw [div_le_div_iff₀ h4a_pos h4an_pos]
        have hrewrite :
            (4 * a * n : ℝ) ^ ((3 : ℝ) / 8)
              = ((4 : ℝ) * a) ^ ((3 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 8) := by
          have hmul : (4 * a * n : ℝ) = ((4 : ℝ) * a) * n := by ring
          rw [hmul, Real.mul_rpow (by positivity) (by positivity)]
        have hdivrpow :
            ((n : ℝ) / a) ^ ((1 : ℝ) / 2)
              = (n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [Real.div_rpow (by positivity) (by positivity)]
        have hncombine :
            (n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 8)
              = (n : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
        have hahalf :
            (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2) = (a : ℝ) ^ ((1 : ℝ) / 2) := by
          have hsub :
              (a : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 2)
                = (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [Real.rpow_sub ha_pos, Real.rpow_one]
          calc
            (a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2)
                = (a : ℝ) ^ ((1 : ℝ) - (1 : ℝ) / 2) := by simpa using hsub.symm
            _ = (a : ℝ) ^ ((1 : ℝ) / 2) := by norm_num
        have hconst :
            ((4 : ℝ) * a) ^ ((3 : ℝ) / 8) ≤ (4 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2) := by
          calc
            ((4 : ℝ) * a) ^ ((3 : ℝ) / 8)
                = (4 : ℝ) ^ ((3 : ℝ) / 8) * (a : ℝ) ^ ((3 : ℝ) / 8) := by
                    rw [Real.mul_rpow (by positivity) (by positivity)]
            _ ≤ (4 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2) := by
              have h4 : (4 : ℝ) ^ ((3 : ℝ) / 8) ≤ 4 := by
                have htmp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
                  (by norm_num : (3 : ℝ) / 8 ≤ 1)
                simpa [Real.rpow_one] using htmp
              have haexp : (a : ℝ) ^ ((3 : ℝ) / 8) ≤ (a : ℝ) ^ ((1 : ℝ) / 2) := by
                have ha_one : (1 : ℝ) ≤ a := by exact_mod_cast ha
                exact Real.rpow_le_rpow_of_exponent_le ha_one
                  (by norm_num : (3 : ℝ) / 8 ≤ (1 : ℝ) / 2)
              exact mul_le_mul h4 haexp (by positivity) (by positivity)
        rw [hrewrite, hdivrpow]
        calc
          (n : ℝ) ^ ((1 : ℝ) / 8) *
              (((4 : ℝ) * a) ^ ((3 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 8))
              = ((4 : ℝ) * a) ^ ((3 : ℝ) / 8) *
                  ((n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 8)) := by ring
          _ = ((4 : ℝ) * a) ^ ((3 : ℝ) / 8) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [hncombine]
          _ = (n : ℝ) ^ ((1 : ℝ) / 2) * (((4 : ℝ) * a) ^ ((3 : ℝ) / 8)) := by ring
          _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * ((4 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left hconst (by positivity)
          _ = ((n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2)) * ((4 : ℝ) * a) := by
            calc
              (n : ℝ) ^ ((1 : ℝ) / 2) * ((4 : ℝ) * (a : ℝ) ^ ((1 : ℝ) / 2))
                  = (4 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) * (a : ℝ) ^ ((1 : ℝ) / 2) := by ring
              _ = (4 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) *
                    ((a : ℝ) / (a : ℝ) ^ ((1 : ℝ) / 2)) := by rw [hahalf]
              _ = ((n : ℝ) ^ ((1 : ℝ) / 2) / (a : ℝ) ^ ((1 : ℝ) / 2)) * ((4 : ℝ) * a) := by
                ring
      exact le_trans hbase hmid
    have hlog_lower : (48 * a : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 16) ≤ 1 / (3 * Real.log n) := by
      have hmain'' : (48 * a : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 16) * (1 / (3 * Real.log n)) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain'
      have hmain''' : (48 * a : ℝ) ≤ (1 / (3 * Real.log n)) * (n : ℝ) ^ ((1 : ℝ) / 16) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmain''
      exact (div_le_iff₀ hnpow16_pos).2 hmain'''
    have hpow8_eq :
        (n : ℝ) ^ ((1 : ℝ) / 8)
          = (n : ℝ) ^ ((1 : ℝ) / 16) * (n : ℝ) ^ ((1 : ℝ) / 16) := by
      rw [show ((1 : ℝ) / 8) = (1 : ℝ) / 16 + (1 : ℝ) / 16 by norm_num]
      rw [Real.rpow_add hn_pos]
    have hprod_eq :
        ((n : ℝ) ^ ((1 : ℝ) / 8) / (4 * a)) *
            ((48 * a : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 16))
          = 12 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
      rw [hpow8_eq]
      field_simp [h4a_ne, hpow16_ne]
      ring
    have h12 :
        12 * (n : ℝ) ^ ((1 : ℝ) / 16)
          ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
      have hmul := mul_le_mul hKp_lower hlog_lower (by positivity) (by positivity)
      rw [hprod_eq] at hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hn16_ge_one : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 16) := by
      have hn_one : (1 : ℝ) ≤ n := by
        exact_mod_cast (show 1 ≤ n by omega)
      simpa using Real.rpow_le_rpow_of_exponent_le hn_one
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 16)
    have hlhs : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
        ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
      have h2le : (2 : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
        nlinarith
      linarith
    have h3 : 3 * (n : ℝ) ^ ((1 : ℝ) / 16)
        ≤ (K : ℝ) / p * (1 / (3 * Real.log n)) := by
      nlinarith [h12, hnpow16_pos]
    exact le_trans hlhs h3
  have hcard_ge : (2 : ℝ) ≤ (good.map emb).card := by
    have htmp : (2 : ℝ) + (2 : ℝ) ^ n.primeFactors.card
        ≤ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
      exact le_trans hK_over_p (mul_le_mul_of_nonneg_left hmertens (by positivity))
    linarith [hlower, htmp]
  have hmap_le : (good.map emb).card ≤ (candidateKs a n p).card := Finset.card_le_card hgood_sub
  have hge_nat : 2 ≤ (candidateKs a n p).card := by
    exact le_trans (by exact_mod_cast hcard_ge) hmap_le
  exact lt_of_lt_of_le (by decide : 1 < 2) hge_nat

/-- Contradiction engine for the two Pollack-driven branches.

Once we have one odd prime `p` of Pollack-size such that `p ∤ a*n` and
`a*x^2 ≡ n [MOD p]` is solvable, the counting argument rules out `Pa a n`. -/
private lemma not_Pa_of_good_prime
    (a : ℕ) (ha : 1 ≤ a) :
    ∃ N0 : ℕ, ∀ {n p : ℕ},
      N0 ≤ n →
      p.Prime →
      p ≠ 2 →
      ¬ p ∣ a * n →
      SolvableAX2EqNMod a n p →
      (p : ℝ) ≤ pollackSizeBound a n →
      ¬ Pa a n := by
  obtain ⟨N0, hcount⟩ := many_candidates_of_pollack_size a ha
  refine ⟨N0, ?_⟩
  intro n p hn hp hp2 hpndvd hsol hpbound hPa
  have hgt : 1 < (candidateKs a n p).card :=
    hcount hn hp hp2 hpndvd hsol hpbound
  have hle : (candidateKs a n p).card ≤ 1 :=
    candidateKs_card_le_one ha hPa hp
  exact not_lt_of_ge hle hgt


/-! ## Square-case helpers based on the fixed coefficient `a` -/

/-- If `a = v^2` and `u^2 = a*n`, with `a ≥ 1`, then `n` is also a square. -/
private lemma n_is_square_of_square_case_and_square_coeff
    {a n u v : ℕ}
    (ha : 1 ≤ a)
    (haSq : a = v ^ 2)
    (hsq : u ^ 2 = a * n) :
    ∃ m : ℕ, n = m ^ 2 := by
  have hv_pos : 0 < v := by
    by_contra hv
    have hv0 : v = 0 := Nat.eq_zero_of_not_pos hv
    have ha0 : a = 0 := by
      simpa [hv0] using haSq
    omega
  have hv2_dvd : v ^ 2 ∣ u ^ 2 := by
    refine ⟨n, ?_⟩
    simpa [haSq, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsq
  have hv_dvd_u : v ∣ u := by
    exact (Nat.pow_dvd_pow_iff (show (2 : ℕ) ≠ 0 by decide)).1 hv2_dvd
  rcases hv_dvd_u with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hmain : v ^ 2 * m ^ 2 = v ^ 2 * n := by
    calc
      v ^ 2 * m ^ 2 = (v * m) ^ 2 := by
        simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = u ^ 2 := by
        simpa [hm]
      _ = v ^ 2 * n := by
        simpa [haSq] using hsq
  have hm2 : m ^ 2 = n := Nat.eq_of_mul_eq_mul_left (pow_pos hv_pos 2) hmain
  exact hm2.symm

/-- If `a = v^2`, `n = m^2`, and `m` is sufficiently larger than `v`, then `Pa a n` already fails
at `k = 1`, since `n - a = (m-v)(m+v)` is composite. -/
private lemma not_Pa_of_large_square_difference
    {a n v m : ℕ}
    (haSq : a = v ^ 2)
    (hnSq : n = m ^ 2)
    (hm : v + 2 ≤ m) :
    ¬ Pa a n := by
  intro hPa
  have hvlt_aux : v < v + 2 := by
    exact Nat.lt_trans (Nat.lt_succ_self v) (Nat.lt_succ_self (v + 1))
  have hvlt : v < m := lt_of_lt_of_le hvlt_aux hm
  have hlt : a * 1 ^ 2 < n := by
    have hsq_lt : v ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hvlt (by decide : (2 : ℕ) ≠ 0)
    simpa [haSq, hnSq] using hsq_lt
  have hprime : Nat.Prime (n - a * 1 ^ 2) :=
    hPa 1 (by decide) (by simpa using Nat.coprime_one_left n) hlt
  have hprod : n - a * 1 ^ 2 = (m + v) * (m - v) := by
    calc
      n - a * 1 ^ 2 = m ^ 2 - v ^ 2 := by
        simpa [haSq, hnSq]
      _ = (m + v) * (m - v) := by
        simpa using Nat.sq_sub_sq m v
  have htwo_le_vaddtwo : 2 ≤ v + 2 := by
    simpa using Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le v))
  have hm_ge_two : 2 ≤ m := le_trans htwo_le_vaddtwo hm
  have hmplus_ge_two : 2 ≤ m + v := le_trans hm_ge_two (Nat.le_add_right m v)
  have hmplus_ne_one : m + v ≠ 1 :=
    ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hmplus_ge_two)
  have hvle : v ≤ m := le_trans (Nat.le_add_right v 2) hm
  have hmsub_ge_two : 2 ≤ m - v :=
    (Nat.le_sub_iff_add_le hvle).2 (by simpa [Nat.add_comm] using hm)
  have hmsub_ne_one : m - v ≠ 1 :=
    ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hmsub_ge_two)
  have hnotprime : ¬ Nat.Prime ((m + v) * (m - v)) :=
    Nat.not_prime_mul hmplus_ne_one hmsub_ne_one
  exact hnotprime (hprod ▸ hprime)

/-- Square case, non-square coefficient branch.

Here `a = v^2*d` with squarefree `d > 1`.  From `a = v^2*d` we get `4*d ∣ 4*a*n`, so
Pollack applied with modulus `m = 4*a*n` produces a prime `p` of Pollack-size with `p ∤ a*n`;
the square identity `u^2 = a*n`
then makes `a*x^2 ≡ n [MOD p]` solvable, and the contradiction is delegated to
`not_Pa_of_good_prime`. -/
lemma square_case_nonsquare_coeff_impossible_of_coeff
    (a v d : ℕ)
    (ha : 1 ≤ a)
    (_hdSq : Squarefree d)
    (_hdGt : 1 < d)
    (hadecomp : v ^ 2 * d = a) :
    ∃ N0 : ℕ, ∀ {n u : ℕ},
      N0 ≤ n →
      u ^ 2 = a * n →
      ¬ Pa a n := by
  obtain ⟨M0, hPollack⟩ := exists_small_prime_from_pollack
  obtain ⟨Nbad, hbad⟩ := not_Pa_of_good_prime a ha
  refine ⟨max M0 Nbad, ?_⟩
  intro n u hn hsq
  have hm : M0 ≤ 4 * a * n := by
    exact le_trans (le_trans (le_max_left _ _) hn) (le_pollack_modulus ha)
  have hdvd : 4 * d ∣ 4 * a * n :=
    squarefree_coeff_dvd_pollack_modulus (n := n) hadecomp
  obtain ⟨p, hp, hp2, hpndvdMod, hpbound, _hres⟩ := hPollack hm hdvd
  have hpndvd : ¬ p ∣ a * n := not_dvd_an_of_not_dvd_pollack_modulus hpndvdMod
  have hsol : SolvableAX2EqNMod a n p :=
    solvable_of_square_case hsq hp hpndvd
  exact hbad (le_trans (le_max_right _ _) hn) hp hp2 hpndvd hsol (by
    simpa [pollackSizeBound] using hpbound)

/-- Square case, square coefficient branch.

Once `a = v^2`, the relation `u^2 = a*n` forces `n = m^2`.  For all sufficiently large `n`
we then have `m ≥ v + 2`, and `k = 1` gives a composite value `n - a`. -/
lemma square_case_square_coeff_impossible_of_coeff
    (a v : ℕ)
    (ha : 1 ≤ a)
    (haSq : a = v ^ 2) :
    ∃ N0 : ℕ, ∀ {n u : ℕ},
      N0 ≤ n →
      u ^ 2 = a * n →
      ¬ Pa a n := by
  refine ⟨(v + 2) ^ 2, ?_⟩
  intro n u hn hsq
  obtain ⟨m, hnSq⟩ := n_is_square_of_square_case_and_square_coeff ha haSq hsq
  have hm_sq : (v + 2) ^ 2 ≤ m ^ 2 := by
    simpa [hnSq] using hn
  have hm : v + 2 ≤ m :=
    (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 hm_sq
  exact not_Pa_of_large_square_difference haSq hnSq hm

/-! ## The two contradiction arguments -/

/-- Case 1: the squarefree part `d` of `a*n` is `> 1`.

The only nontrivial input is the existence of one good Pollack prime; once that is in hand,
the rest is again delegated to `not_Pa_of_good_prime`. -/
lemma case1_non_square_impossible
    (a : ℕ)
    (ha : 1 ≤ a) :
    ∃ N1 : ℕ, ∀ {n u d : ℕ},
      N1 ≤ n →
      Squarefree d →
      1 < d →
      u ^ 2 * d = a * n →
      ¬ Pa a n := by
  obtain ⟨M0, hPollack⟩ := exists_small_prime_from_pollack
  obtain ⟨Nbad, hbad⟩ := not_Pa_of_good_prime a ha
  refine ⟨max M0 Nbad, ?_⟩
  intro n u d hn _hdSq _hdGt hdecomp
  have hm : M0 ≤ 4 * a * n := by
    exact le_trans (le_trans (le_max_left _ _) hn) (le_pollack_modulus ha)
  have hdvd : 4 * d ∣ 4 * a * n :=
    squarefree_factor_dvd_pollack_modulus hdecomp
  obtain ⟨p, hp, hp2, hpndvdMod, hpbound, hres⟩ := hPollack hm hdvd
  have hpndvd : ¬ p ∣ a * n := not_dvd_an_of_not_dvd_pollack_modulus hpndvdMod
  have hsol : SolvableAX2EqNMod a n p :=
    solvable_of_squarefree_part hdecomp hp hpndvd hres
  exact hbad (le_trans (le_max_right _ _) hn) hp hp2 hpndvd hsol (by
    simpa [pollackSizeBound] using hpbound)

/-- Case 2: `a*n` is a square.

We factor the fixed coefficient `a = v^2*d` with `d` squarefree and split according to whether
`d > 1` or `d = 1`.  This removes the need for any separate small-prime lemma in the square case. -/
lemma case2_square_impossible
    (a : ℕ)
    (ha : 1 ≤ a) :
    ∃ N2 : ℕ, ∀ {n u : ℕ},
      N2 ≤ n →
      u ^ 2 = a * n →
      ¬ Pa a n := by
  obtain ⟨v, d, hadecomp, hdSq⟩ := exists_squarefree_factorization a
  by_cases hd1 : d = 1
  · have haSq : a = v ^ 2 := coeff_is_square_of_squarefree_part_eq_one hadecomp hd1
    exact square_case_square_coeff_impossible_of_coeff a v ha haSq
  · have hdGt : 1 < d := one_lt_of_squarefree_ne_one hdSq hd1
    exact square_case_nonsquare_coeff_impossible_of_coeff a v d ha hdSq hdGt hadecomp

/-! ## Main theorem -/

/-- Eventual failure of `Pa a n` for every fixed `a ≥ 1`. -/
theorem eventually_not_Pa (a : ℕ) (ha : 1 ≤ a) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n → ¬ Pa a n := by
  obtain ⟨N1, h1⟩ := case1_non_square_impossible a ha
  obtain ⟨N2, h2⟩ := case2_square_impossible a ha
  refine ⟨max N1 N2, ?_⟩
  intro n hn hPa
  obtain ⟨u, d, hdecomp, hdSq⟩ := exists_squarefree_factorization (a * n)
  by_cases hd1 : d = 1
  · have hsq : u ^ 2 = a * n := by
      simpa [hd1] using hdecomp
    exact h2 (le_trans (le_max_right _ _) hn) hsq hPa
  · have hdGt : 1 < d := one_lt_of_squarefree_ne_one hdSq hd1
    exact h1 (le_trans (le_max_left _ _) hn) hdSq hdGt hdecomp hPa

/-- General finite-set formulation of the theorem. -/
theorem erdos_1141_variant_general (a : ℕ) (ha : 1 ≤ a) :
    Set.Finite {n : ℕ | Pa a n} := by
  obtain ⟨N, hN⟩ := eventually_not_Pa a ha
  refine (Set.finite_lt_nat N).subset ?_
  intro n hn
  by_contra hlt
  exact hN (n := n) (Nat.le_of_not_lt hlt) hn

/-- Paper-style `Pa` statement for `a = 1`, stronger than the Formal Conjectures statement `erdos_1141` below. -/
theorem erdos_1141_variant : Set.Finite {n : ℕ | Pa 1 n} := by
  simpa using erdos_1141_variant_general 1 (by decide : 1 ≤ 1)

#print axioms erdos_1141_variant
-- 'Erdos1141.erdos_1141_variant' depends on axioms: [propext, Classical.choice,
-- mertens_third_theorem, Pollack17.theorem_1_3, Quot.sound]

/-! ## Block Copied from Formal Conjectures -/

/-
The following block is copied as literally as possible from
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1141.lean
with only the proof of `erdos_1141` filled in via the stronger theorem `erdos_1141_variant` above.
-/

open Nat Set

/--
The property that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$.
-/
def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (Erdos1141Prop n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [Erdos1141Prop]
    | succ n' =>
      simp [Erdos1141Prop, Nat.le_sqrt, pow_two]

theorem erdos1141Prop_iff_pa_one_ne_one (n : ℕ) :
    Erdos1141Prop n ↔ Pa 1 n ∧ n ≠ 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk hcop hlt
      simpa [one_mul] using h k (by simpa [one_mul] using hlt) hcop.symm
    · intro hn
      have h0 := h 0 (by simpa [hn]) (by simpa [hn] using Nat.coprime_zero_right.2 rfl)
      have h1 : Nat.Prime 1 := by simpa [hn] using h0
      exact Nat.not_prime_one h1
  · rintro ⟨hPa, hn1⟩ k hk hcop
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exfalso
      have : ¬ Coprime n 0 := by simpa [Nat.coprime_zero_right] using hn1
      exact this hcop
    · simpa [one_mul] using hPa k hkpos hcop.symm (by simpa [one_mul] using hk)

/--
Are there infinitely many $n$ such that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$?

In [Va99] it is asked whether $968$ is the largest integer with this property, but this is an
error, since for example $968-9=7\cdot 137$.

The list of $n$ satisfying the given property is [A214583] in the OEIS. The largest known such $n$
is $1722$.
-/
theorem erdos_1141 :
    ¬ Infinite { n | Erdos1141Prop n } := by
  have hsubset : { n | Erdos1141Prop n } ⊆ { n | Pa 1 n } := by
    intro n hn
    exact (erdos1141Prop_iff_pa_one_ne_one n).1 hn |>.1
  simpa [Set.not_infinite] using (erdos_1141_variant.subset hsubset)

example : ¬ Erdos1141Prop 968 := by
  decide +native

example : Erdos1141Prop 1722 := by
  decide +native

#print axioms erdos_1141
-- 'Erdos1141.erdos_1141' depends on axioms: [propext, Classical.choice, mertens_third_theorem,
-- Pollack17.theorem_1_3, Quot.sound]

end Erdos1141
