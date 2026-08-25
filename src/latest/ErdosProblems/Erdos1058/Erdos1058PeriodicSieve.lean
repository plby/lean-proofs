import ErdosProblems.Erdos1058.Erdos1058Core

set_option Elab.async false

namespace Erdos1058.PeriodicSieveCertificate

/-- Repeat a finite residue mask by doubling.  One arithmetic operation handles
all the positions in a block; no list of positions is expanded in the proof. -/
def tile (mask width : ℕ) : ℕ → ℕ
  | 0 => mask
  | n + 1 => let t := tile mask width n; t ||| (t <<< (width * 2 ^ n))

lemma tile_accepts {mask width n p : ℕ} (_hw : 0 < width)
    (hp : p < width * 2 ^ n) (hbit : mask.testBit (p % width) = true) :
    (tile mask width n).testBit p = true := by
  induction n generalizing p with
  | zero =>
      have hpw : p < width := by simpa using hp
      simpa only [tile, Nat.mod_eq_of_lt hpw] using hbit
  | succ n ih =>
      rw [tile, Nat.testBit_or, Bool.or_eq_true]
      by_cases hsmall : p < width * 2 ^ n
      · exact Or.inl (ih hsmall hbit)
      · right
        rw [Nat.testBit_shiftLeft, Bool.and_eq_true]
        refine ⟨by simpa using (show width * 2 ^ n ≤ p by omega), ?_⟩
        have hbound : p - width * 2 ^ n < width * 2 ^ n := by
          rw [pow_succ, ← Nat.mul_assoc] at hp
          omega
        apply ih hbound
        have hmod : (p - width * 2 ^ n) % width = p % width := by
          have heq : p - width * 2 ^ n + width * 2 ^ n = p := by omega
          simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
            Nat.mod_mod] using congrArg (· % width) heq
        rw [hmod]
        exact hbit

structure PeriodicMask where
  period : ℕ
  bits : ℕ
  depth : ℕ

def intersection (bound : ℕ) : List PeriodicMask → ℕ
  | [] => (1 <<< bound) - 1
  | row :: rows => tile row.bits row.period row.depth &&& intersection bound rows

lemma interval_accepts {bound p : ℕ} (hp : p < bound) :
    (((1 : ℕ) <<< bound) - 1).testBit p = true := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hp

/-- A sparse set of exceptional positions, represented without printing a
large integer literal into the source. -/
def positions : List ℕ → ℕ
  | [] => 0
  | p :: ps => (1 <<< p) ||| positions ps

lemma positions_spec {ps : List ℕ} {p : ℕ} :
    (positions ps).testBit p = true ↔ p ∈ ps := by
  induction ps with
  | nil => simp [positions]
  | cons q qs ih =>
      simp only [positions, Nat.testBit_or, Bool.or_eq_true, Nat.shiftLeft_eq,
        Nat.one_mul, Nat.testBit_two_pow, decide_eq_true_eq, ih, List.mem_cons]
      simp only [eq_comm]

/-- A small divisor explains why an exceptional position cannot be a prime
pair.  The Boolean chooses which member of the pair is composite. -/
structure ExceptionWitness where
  position : ℕ
  divisor : ℕ
  second : Bool

def exceptionCheck (d : ℕ) (w : ExceptionWitness) : Bool :=
  decide (w.position ≤ 433) ||
    let n := if w.second then w.position + d else w.position
    decide (1 < w.divisor ∧ w.divisor < n ∧ n % w.divisor = 0)

lemma exception_not_prime_pair {d p : ℕ} {w : ExceptionWitness}
    (hc : exceptionCheck d w = true) (heq : p = w.position)
    (hp433 : 433 < p) (hp : p.Prime) (hq : (p + d).Prime) : False := by
  subst p
  simp only [exceptionCheck, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with hsmall | hdiv
  · omega
  · have hprime : (if w.second then w.position + d else w.position).Prime := by
      split <;> assumption
    have hdvd := Nat.dvd_iff_mod_eq_zero.mpr hdiv.2.2
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h <;> omega

def Obstruction (d kind : ℕ) : Prop :=
  ∀ p, 433 < p → p < 36000000 → p.Prime → (p + d).Prime →
    ¬∀ r ∈ cubicModuliList, cubicCRTLocalForm d kind r p = true

end Erdos1058.PeriodicSieveCertificate
