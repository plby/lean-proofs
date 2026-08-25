import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Shared definitions, mixed-radix arithmetic, and auxiliary digits for Erdős 157

Extracted without changing statements from the existing development.
All proofs use the default computational limits.
-/

open Filter

namespace Erdos157

/-- A Sidon set has unique unordered two-term sums. -/
def IsSidon (S : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Every sufficiently large natural number is the sum of exactly three
members of `S`. Repetition of summands is allowed. -/
def IsAsymptoticBasisOfOrderThree (S : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, n = a + b + c

/-- The unordered formulation of the Sidon property is equivalent to
uniqueness after sorting both pairs. -/
theorem isSidon_iff_ordered (S : Set ℕ) :
    IsSidon S ↔
      ∀ ⦃a b c d : ℕ⦄, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
        a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d := by
  constructor
  · intro h a b c d ha hb hc hd hab hcd hsum
    rcases h ha hb hc hd hsum with h | ⟨had, hbc⟩
    · exact h
    · subst c
      subst d
      have hab' : a = b := Nat.le_antisymm hab hcd
      exact ⟨hab', hab'.symm⟩
  · intro h a b c d ha hb hc hd hsum
    rcases le_total a b with hab | hba
    · rcases le_total c d with hcd | hdc
      · exact Or.inl (h ha hb hc hd hab hcd hsum)
      · have h' := h ha hb hd hc hab hdc (by omega)
        exact Or.inr h'
    · rcases le_total c d with hcd | hdc
      · have h' := h hb ha hc hd hba hcd (by omega)
        exact Or.inr ⟨h'.2, h'.1⟩
      · have h' := h hb ha hd hc hba hdc (by omega)
        exact Or.inl ⟨h'.2, h'.1⟩

/-- A set whose three-fold sum contains every sufficiently large natural is
necessarily infinite. -/
theorem infinite_of_isAsymptoticBasisOfOrderThree {S : Set ℕ}
    (hS : IsAsymptoticBasisOfOrderThree S) : S.Infinite := by
  intro hfinite
  obtain ⟨M, hM⟩ := hfinite.exists_le
  obtain ⟨N₀, hN₀⟩ := hS
  let n := max N₀ (3 * M + 1)
  obtain ⟨a, ha, b, hb, c, hc, hn⟩ := hN₀ n (le_max_left _ _)
  have haM := hM a ha
  have hbM := hM b hb
  have hcM := hM c hc
  have hnM : 3 * M + 1 ≤ n := le_max_right _ _
  omega

/-- Membership in the explicit triple-sum predicate, separated out for the
final conversion from Pilatte's probabilistic construction. -/
def TripleSumset (S : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, n = a + b + c}

@[simp]
theorem mem_tripleSumset {S : Set ℕ} {n : ℕ} :
    n ∈ TripleSumset S ↔
      ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, n = a + b + c :=
  Iff.rfl

/-- The threshold and cofinite formulations of an asymptotic basis agree on
the natural numbers. -/
theorem isAsymptoticBasisOfOrderThree_iff_eventually (S : Set ℕ) :
    IsAsymptoticBasisOfOrderThree S ↔ ∀ᶠ n : ℕ in atTop, n ∈ TripleSumset S := by
  rw [eventually_atTop]
  rfl

/-- The threshold formulation is also equivalent to finiteness of the set of
exceptions. -/
theorem isAsymptoticBasisOfOrderThree_iff_compl_finite (S : Set ℕ) :
    IsAsymptoticBasisOfOrderThree S ↔ (TripleSumset S)ᶜ.Finite := by
  rw [isAsymptoticBasisOfOrderThree_iff_eventually, ← Nat.cofinite_eq_atTop]
  exact eventually_cofinite.symm

/-! ## Generalized-base arithmetic -/

namespace MixedRadix

/-- A least-significant-digit-first generalized-base encoding.  A pair
`(b, d)` records a radix `b` and the digit `d` in that position. -/
def encode : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (b, d) :: xs => d + b * encode xs

/-- The place value immediately above a finite digit string. -/
def place (xs : List (ℕ × ℕ)) : ℕ := (xs.map Prod.fst).prod

/-- Every radix is at least two and every digit is normalized. -/
def Valid : List (ℕ × ℕ) → Prop
  | [] => True
  | (b, d) :: xs => 2 ≤ b ∧ d < b ∧ Valid xs

@[simp]
theorem valid_append (xs ys : List (ℕ × ℕ)) :
    Valid (xs ++ ys) ↔ Valid xs ∧ Valid ys := by
  induction xs with
  | nil => simp [Valid]
  | cons x xs ih =>
      rcases x with ⟨b, d⟩
      simp [Valid, ih, and_assoc]

@[simp] theorem encode_nil : encode [] = 0 := rfl
@[simp] theorem encode_cons (b d : ℕ) (xs) :
    encode ((b, d) :: xs) = d + b * encode xs := rfl
@[simp] theorem place_nil : place [] = 1 := rfl
@[simp] theorem place_cons (b d : ℕ) (xs) :
    place ((b, d) :: xs) = b * place xs := rfl

/-- Concatenating a higher digit block multiplies that block by the place
value of the lower block. -/
theorem encode_append (xs ys : List (ℕ × ℕ)) :
    encode (xs ++ ys) = encode xs + place xs * encode ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases x with ⟨b, d⟩
    simp only [List.cons_append, encode_cons, place_cons, ih]
    simp [mul_add, mul_assoc, add_assoc]

/-- A normalized digit string lies strictly below its next place value. -/
theorem encode_lt_place {xs : List (ℕ × ℕ)} (h : Valid xs) :
    encode xs < place xs := by
  induction xs with
  | nil => simp [encode, place]
  | cons x xs ih =>
    rcases x with ⟨b, d⟩
    obtain ⟨_hb, hd, hxs⟩ := h
    have hi := ih hxs
    rw [encode_cons, place_cons]
    calc
      d + b * encode xs < b + b * encode xs := Nat.add_lt_add_right hd _
      _ = b * (encode xs + 1) := by simp [mul_add, add_comm]
      _ ≤ b * place xs := Nat.mul_le_mul_left b (Nat.succ_le_iff.2 hi)

theorem valid_take {xs : List (ℕ × ℕ)} (h : Valid xs) (n : ℕ) :
    Valid (xs.take n) := by
  induction n generalizing xs with
  | zero => simp [Valid]
  | succ n ih =>
      cases xs with
      | nil => simp [Valid]
      | cons x xs =>
          rcases x with ⟨b, d⟩
          rcases h with ⟨hb, hd, hxs⟩
          exact ⟨hb, hd, ih hxs⟩

theorem place_pos_of_valid {xs : List (ℕ × ℕ)} (h : Valid xs) :
    0 < place xs := by
  induction xs with
  | nil => simp [place]
  | cons x xs ih =>
      rcases x with ⟨b, d⟩
      rcases h with ⟨hb, _hd, hxs⟩
      rw [place_cons]
      exact Nat.mul_pos (by omega) (ih hxs)

/-- The encoding modulo the place above an initial segment is precisely the
encoding of that initial segment. -/
theorem encode_mod_place_take {xs : List (ℕ × ℕ)} (h : Valid xs) (n : ℕ) :
    encode xs % place (xs.take n) = encode (xs.take n) := by
  have hsplit := encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at hsplit
  rw [hsplit, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (encode_lt_place (valid_take h n))]

/-- Normalized generalized-base digits are unique once the radices agree. -/
theorem encode_injective_of_valid {xs ys : List (ℕ × ℕ)}
    (hx : Valid xs) (hy : Valid ys)
    (hbases : xs.map Prod.fst = ys.map Prod.fst)
    (he : encode xs = encode ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at hbases
  | cons x xs ih =>
    cases ys with
    | nil => simp at hbases
    | cons y ys =>
      rcases x with ⟨b, d⟩
      rcases y with ⟨b', d'⟩
      simp only [List.map_cons] at hbases
      injection hbases with hbb hbases
      subst b'
      obtain ⟨hbase, hd, hxs⟩ := hx
      obtain ⟨_, hd', hys⟩ := hy
      have hdd : d = d' := by
        have hm := congrArg (fun n : ℕ => n % b) he
        have hdmod : d % b = d := Nat.mod_eq_of_lt hd
        have hdmod' : d' % b = d' := Nat.mod_eq_of_lt hd'
        simpa only [encode_cons, Nat.add_mul_mod_self_left, hdmod, hdmod'] using hm
      subst d'
      have henc : encode xs = encode ys := by
        simp only [encode_cons] at he
        have hmul : b * encode xs = b * encode ys := Nat.add_left_cancel he
        exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
      have htails : xs = ys := ih hxs hys hbases henc
      simp [htails]

/-- Equality of two normalized mixed-radix integers determines every common
initial segment, even when the complete digit strings have different
lengths.  Only the radices in the requested segment need agree. -/
theorem take_eq_of_encode_eq_of_valid {xs ys : List (ℕ × ℕ)} (n : ℕ)
    (hx : Valid xs) (hy : Valid ys)
    (hbases : (xs.take n).map Prod.fst = (ys.take n).map Prod.fst)
    (he : encode xs = encode ys) : xs.take n = ys.take n := by
  induction n generalizing xs ys with
  | zero => simp
  | succ n ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => rfl
          | cons y ys => simp at hbases
      | cons x xs =>
          cases ys with
          | nil => simp at hbases
          | cons y ys =>
              rcases x with ⟨b, d⟩
              rcases y with ⟨b', d'⟩
              simp only [List.take_succ_cons, List.map_cons] at hbases
              injection hbases with hbb hbases
              subst b'
              obtain ⟨hbase, hd, hxs⟩ := hx
              obtain ⟨_, hd', hys⟩ := hy
              have hdd : d = d' := by
                have hm := congrArg (fun m : ℕ => m % b) he
                have hdmod : d % b = d := Nat.mod_eq_of_lt hd
                have hdmod' : d' % b = d' := Nat.mod_eq_of_lt hd'
                simpa only [encode_cons, Nat.add_mul_mod_self_left, hdmod,
                  hdmod'] using hm
              subst d'
              have henc : encode xs = encode ys := by
                simp only [encode_cons] at he
                have hmul : b * encode xs = b * encode ys := Nat.add_left_cancel he
                exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
              simp only [List.take_succ_cons, List.cons.injEq, true_and]
              exact ih hxs hys hbases henc

/-- Euclidean division at one digit: the remainder is the normalized output
digit and the quotient is the outgoing carry. -/
theorem digit_decomposition (b n : ℕ) :
    n = n % b + b * (n / b) :=
  (Nat.mod_add_div n b).symm

/-- Adding two normalized digits and an incoming carry at most one produces
an outgoing carry at most one. -/
theorem two_digit_carry_le_one {b x y carry : ℕ}
    (hb : 0 < b) (hx : x < b) (hy : y < b) (hc : carry ≤ 1) :
    (x + y + carry) / b ≤ 1 := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hb]
  omega

/-- Adding three normalized digits and an incoming carry at most two
produces an outgoing carry at most two. -/
theorem three_digit_carry_le_two {b x y z carry : ℕ}
    (hb : 0 < b) (hx : x < b) (hy : y < b) (hz : z < b)
    (hc : carry ≤ 2) :
    (x + y + z + carry) / b ≤ 2 := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hb]
  omega

/-- If a digit total is already below the radix, it creates no carry. -/
theorem digit_carry_eq_zero {b x y carry : ℕ}
    (h : x + y + carry < b) :
    (x + y + carry) / b = 0 :=
  Nat.div_eq_of_lt h

end MixedRadix

/-! ## The finite auxiliary digit interface -/

namespace AuxiliaryDigits

/-- An integer has a three-term representation using digits from `A`. -/
def TripleRepresentedBy (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, n = a + b + c

/-- The separation property `A ∩ (A + A + {0,1}) = ∅`, written without
pointwise-set notation so its carry parameter is explicit. -/
def Separated (A : Set ℕ) : Prop :=
  ∀ ⦃a b c κ : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → κ ≤ 1 →
    a ≠ b + c + κ

/-- A target even-position digit is compatible with every carry that can
come from adding three preceding digits. -/
def CarryCovered (A : Set ℕ) (y : ℕ) : Prop :=
  ∀ κ : ℕ, κ ≤ 2 →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c + κ = y

/-- A normalized auxiliary digit arising from two summands and the binary
carry from the preceding logarithm position. -/
def PairCarryRepresentedBy (A : Set ℕ) (y : ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ κ : ℕ, κ ≤ 1 ∧ y = a + b + κ

/-- The exact two finite properties required of Pilatte's auxiliary set.
The interval `[L, L + p + 1]` has `p + 2` members. -/
def IsAuxiliarySet (p : ℕ) (A : Set ℕ) : Prop :=
  A ⊆ Set.Ico 1 (p / 2) ∧ Separated A ∧
    ∃ L : ℕ, ∀ n : ℕ, L ≤ n → n ≤ L + p + 1 → TripleRepresentedBy A n

/-- An explicit certificate replacing the probabilistic existence proof of
the finite auxiliary set. -/
def auxiliaryDigitList : List ℕ :=
  [10, 13, 14, 15, 16, 17, 22, 41, 42, 43, 46, 47, 48, 49, 50]

/-- The concrete auxiliary digit set used in the formal development. -/
def auxiliaryDigitSet : Set ℕ := (auxiliaryDigitList.toFinset : Set ℕ)

private def auxiliarySeparationCheck : Bool :=
  auxiliaryDigitList.all fun a =>
    auxiliaryDigitList.all fun b =>
      auxiliaryDigitList.all fun c =>
        (a != b + c) && (a != b + c + 1)

private def auxiliaryRepresentationCheck (n : ℕ) : Bool :=
  auxiliaryDigitList.any fun a =>
    auxiliaryDigitList.any fun b =>
      auxiliaryDigitList.any fun c => n == a + b + c

private def auxiliaryCoverageCheck : Bool :=
  (List.range' 37 105).all auxiliaryRepresentationCheck

private theorem auxiliarySeparationCheck_eq_true :
    auxiliarySeparationCheck = true := by decide

private theorem auxiliaryCoverageCheck_eq_true :
    auxiliaryCoverageCheck = true := by decide

/-- Direct access to the certified block of `105 = 103 + 2` consecutive
triple sums. -/
theorem explicitTripleCoverage {n : ℕ} (hnlo : 37 ≤ n) (hnhi : n ≤ 141) :
    TripleRepresentedBy auxiliaryDigitSet n := by
  have hnmem : n ∈ List.range' 37 105 := by
    simp only [List.mem_range'_1]
    omega
  have hh := (List.all_eq_true.mp auxiliaryCoverageCheck_eq_true) n hnmem
  simp only [auxiliaryRepresentationCheck, List.any_eq_true, beq_iff_eq] at hh
  obtain ⟨a, ha, b, hb, c, hc, hsum⟩ := hh
  exact ⟨a, by simpa [auxiliaryDigitSet] using ha,
    b, by simpa [auxiliaryDigitSet] using hb,
    c, by simpa [auxiliaryDigitSet] using hc, hsum⟩

/-- The explicit set has both properties of Pilatte's auxiliary-set lemma:
it lies in `{1, ..., floor(103/2)-1}`, is separated from its two-fold sums
with binary carry, and its triple sumset contains `[37,141]`, a block of
`103+2` consecutive integers.  The two finite certificates above are
evaluated by kernel reduction. -/
theorem explicitAuxiliarySet : IsAuxiliarySet 103 auxiliaryDigitSet := by
  refine ⟨?_, ?_, ⟨37, ?_⟩⟩
  · intro a ha
    have hal : a ∈ auxiliaryDigitList := by
      simpa [auxiliaryDigitSet] using ha
    simp [auxiliaryDigitList] at hal
    simp only [Set.mem_Ico]
    omega
  · intro a b c κ ha hb hc hκ
    have hal : a ∈ auxiliaryDigitList := by
      simpa [auxiliaryDigitSet] using ha
    have hbl : b ∈ auxiliaryDigitList := by
      simpa [auxiliaryDigitSet] using hb
    have hcl : c ∈ auxiliaryDigitList := by
      simpa [auxiliaryDigitSet] using hc
    have hh := (List.all_eq_true.mp auxiliarySeparationCheck_eq_true) a hal
    have hh := (List.all_eq_true.mp hh) b hbl
    have hh := (List.all_eq_true.mp hh) c hcl
    simp only [Bool.and_eq_true, bne_iff_ne] at hh
    interval_cases κ
    · simpa using hh.1
    · simpa using hh.2
  · intro n hnlo hnhi
    exact explicitTripleCoverage hnlo (by omega)

/-- A canonical member of `[39,141]` congruent to `m` modulo `103`.
The interval has exactly one representative of each residue class. -/
def compatibleTripleDigit (m : ℕ) : ℕ :=
  39 + (m + 64) % 103

theorem compatibleTripleDigit_bounds (m : ℕ) :
    39 ≤ compatibleTripleDigit m ∧ compatibleTripleDigit m ≤ 141 := by
  unfold compatibleTripleDigit
  have hmod : (m + 64) % 103 < 103 := Nat.mod_lt _ (by omega)
  omega

theorem compatibleTripleDigit_modEq (m : ℕ) :
    Nat.ModEq 103 (compatibleTripleDigit m) m := by
  rw [Nat.modEq_iff_dvd]
  unfold compatibleTripleDigit
  omega

/-- The canonical residue representative and its two predecessors are all
triple sums of auxiliary digits. -/
theorem compatibleTripleDigit_covered (m : ℕ) :
    TripleRepresentedBy auxiliaryDigitSet (compatibleTripleDigit m) ∧
      TripleRepresentedBy auxiliaryDigitSet (compatibleTripleDigit m - 1) ∧
      TripleRepresentedBy auxiliaryDigitSet (compatibleTripleDigit m - 2) := by
  have hb := compatibleTripleDigit_bounds m
  exact ⟨explicitTripleCoverage (by omega) (by omega),
    explicitTripleCoverage (by omega) (by omega),
    explicitTripleCoverage (by omega) (by omega)⟩

theorem compatibleTripleDigit_carryCovered (m : ℕ) :
    CarryCovered auxiliaryDigitSet (compatibleTripleDigit m) := by
  rcases compatibleTripleDigit_covered m with ⟨h0, h1, h2⟩
  intro κ hκ
  interval_cases κ
  · obtain ⟨a, ha, b, hb, c, hc, hs⟩ := h0
    exact ⟨a, ha, b, hb, c, hc, by omega⟩
  · obtain ⟨a, ha, b, hb, c, hc, hs⟩ := h1
    have hbnd := (compatibleTripleDigit_bounds m).1
    exact ⟨a, ha, b, hb, c, hc, by omega⟩
  · obtain ⟨a, ha, b, hb, c, hc, hs⟩ := h2
    have hbnd := (compatibleTripleDigit_bounds m).1
    exact ⟨a, ha, b, hb, c, hc, by omega⟩

/-- Three consecutive represented totals absorb any carry in `{0,1,2}`. -/
theorem carryCovered_of_three_consecutive {A : Set ℕ} {y : ℕ}
    (hy : 2 ≤ y)
    (h0 : TripleRepresentedBy A y)
    (h1 : TripleRepresentedBy A (y - 1))
    (h2 : TripleRepresentedBy A (y - 2)) :
    CarryCovered A y := by
  intro κ hκ
  interval_cases κ
  · obtain ⟨a, ha, b, hb, c, hc, hsum⟩ := h0
    exact ⟨a, ha, b, hb, c, hc, by omega⟩
  · obtain ⟨a, ha, b, hb, c, hc, hsum⟩ := h1
    exact ⟨a, ha, b, hb, c, hc, by omega⟩
  · obtain ⟨a, ha, b, hb, c, hc, hsum⟩ := h2
    exact ⟨a, ha, b, hb, c, hc, by omega⟩

/-- A single auxiliary digit cannot be mistaken for the sum of two such
digits and a binary incoming carry.  This is the marker used to recover the
shorter level in the deterministic Sidon proof. -/
theorem single_ne_pair_add_carry {A : Set ℕ} (hA : Separated A)
    {a b c κ : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hκ : κ ≤ 1) :
    a ≠ b + c + κ :=
  hA ha hb hc hκ

end AuxiliaryDigits

end Erdos157
