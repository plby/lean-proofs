/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
Finite arithmetic used in the Jackson--Mauldin rational-translate selector.

The main point of this file is to isolate the exact numerator appearing in
Equation (4.2) of the mathematical proof.  This makes the finite selector
condition a statement about divisibility in `ℤ`, with no ambiguity about
division in a residue ring.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos215.Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

abbrev RatPoint := ℚ × ℚ

/-- Squared Euclidean distance on rational coordinate pairs. -/
def sqDist (x y : RatPoint) : ℚ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

/-- The point selected above residue `(i,j)` modulo `d`, with integral lift `(k,l)`. -/
def liftedPoint (d : ℕ) (i j : Fin d) (k l : ℤ) : RatPoint :=
  (((i : ℕ) : ℚ) / d + k, ((j : ℕ) : ℚ) / d + l)

/-- The integral numerator in the squared-distance calculation (4.2). -/
def conflictNumerator (d : ℕ) (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) : ℤ :=
  let A := ((i₁ : ℕ) : ℤ) - ((i₂ : ℕ) : ℤ)
  let B := ((j₁ : ℕ) : ℤ) - ((j₂ : ℕ) : ℤ)
  let K := k₁ - k₂
  let M := l₁ - l₂
  A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M)

/-- The literal numerator of the squared distance.  It differs from
`conflictNumerator` by a multiple of `d²`. -/
def distanceNumerator (d : ℕ) (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) : ℤ :=
  let K := k₁ - k₂
  let M := l₁ - l₂
  conflictNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ + (d : ℤ) ^ 2 * (K ^ 2 + M ^ 2)

lemma sqDist_liftedPoint (d : ℕ) (hd : d ≠ 0)
    (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) :
    sqDist (liftedPoint d i₁ j₁ k₁ l₁) (liftedPoint d i₂ j₂ k₂ l₂) =
      (distanceNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ : ℚ) / (d : ℚ) ^ 2 := by
  simp only [sqDist, liftedPoint, distanceNumerator, conflictNumerator]
  push_cast
  field_simp [hd]
  ring

lemma distanceNumerator_dvd_iff (d : ℕ) (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) :
    (d : ℤ) ^ 2 ∣ distanceNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ ↔
      (d : ℤ) ^ 2 ∣ conflictNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ := by
  let Q : ℤ := (k₁ - k₂) ^ 2 + (l₁ - l₂) ^ 2
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z - Q, ?_⟩
    simp only [distanceNumerator, Q] at hz ⊢
    linear_combination hz
  · rintro ⟨z, hz⟩
    refine ⟨z + Q, ?_⟩
    simp only [distanceNumerator, Q] at hz ⊢
    linear_combination hz

/-- A rational number `N / d²` is integral exactly when `d² ∣ N`. -/
lemma div_sq_isInt_iff (d : ℕ) (hd : d ≠ 0) (N : ℤ) :
    (∃ z : ℤ, (N : ℚ) / (d : ℚ) ^ 2 = z) ↔ (d : ℤ) ^ 2 ∣ N := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    field_simp [hdq] at hz
    exact_mod_cast hz
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp [hdq]

/-- Exact integrality criterion (4.2). -/
theorem sqDist_liftedPoint_isInt_iff (d : ℕ) (hd : d ≠ 0)
    (i₁ j₁ i₂ j₂ : Fin d) (k₁ l₁ k₂ l₂ : ℤ) :
    (∃ z : ℤ,
        sqDist (liftedPoint d i₁ j₁ k₁ l₁) (liftedPoint d i₂ j₂ k₂ l₂) = z) ↔
      (d : ℤ) ^ 2 ∣ conflictNumerator d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂ := by
  rw [sqDist_liftedPoint d hd]
  rw [div_sq_isInt_iff d hd]
  exact distanceNumerator_dvd_iff d i₁ j₁ i₂ j₂ k₁ l₁ k₂ l₂

/-- Integral lift data over all `d²` residue pairs. -/
structure LiftData (d : ℕ) where
  k : Fin d → Fin d → ℤ
  l : Fin d → Fin d → ℤ

namespace LiftData

def point {d : ℕ} (s : LiftData d) (i j : Fin d) : RatPoint :=
  liftedPoint d i j (s.k i j) (s.l i j)

/-- The finite selector condition `(*)_d`, written without division. -/
def Separated {d : ℕ} (s : LiftData d) : Prop :=
  ∀ i₁ j₁ i₂ j₂, (i₁, j₁) ≠ (i₂, j₂) →
    ¬(d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)

theorem separated_iff_sqDist_not_int {d : ℕ} (hd : d ≠ 0) (s : LiftData d) :
    s.Separated ↔
      ∀ i₁ j₁ i₂ j₂, (i₁, j₁) ≠ (i₂, j₂) →
        ¬∃ z : ℤ, sqDist (s.point i₁ j₁) (s.point i₂ j₂) = z := by
  simp only [Separated, point]
  constructor
  · intro h i₁ j₁ i₂ j₂ hne hz
    exact h i₁ j₁ i₂ j₂ hne
      ((sqDist_liftedPoint_isInt_iff d hd i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)).mp hz)
  · intro h i₁ j₁ i₂ j₂ hne hdiv
    exact h i₁ j₁ i₂ j₂ hne
      ((sqDist_liftedPoint_isInt_iff d hd i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)).mpr hdiv)

/-- The zero lift is already a separated selector at denominator two. -/
def initialTwo : LiftData 2 where
  k := fun _ _ ↦ 0
  l := fun _ _ ↦ 0

theorem initialTwo_separated : initialTwo.Separated := by
  intro i₁ j₁ i₂ j₂ hne hdiv
  have hval : (i₁ : ℕ) ≠ (i₂ : ℕ) ∨ (j₁ : ℕ) ≠ (j₂ : ℕ) := by
    by_contra h
    have hiEq : (i₁ : ℕ) = (i₂ : ℕ) := by
      by_contra hiNe
      exact h (Or.inl hiNe)
    have hjEq : (j₁ : ℕ) = (j₂ : ℕ) := by
      by_contra hjNe
      exact h (Or.inr hjNe)
    apply hne
    exact Prod.ext (Fin.ext hiEq) (Fin.ext hjEq)
  have hi : (i₁ : ℕ) = 0 ∨ (i₁ : ℕ) = 1 := by omega
  have hi' : (i₂ : ℕ) = 0 ∨ (i₂ : ℕ) = 1 := by omega
  have hj : (j₁ : ℕ) = 0 ∨ (j₁ : ℕ) = 1 := by omega
  have hj' : (j₂ : ℕ) = 0 ∨ (j₂ : ℕ) = 1 := by omega
  rcases hi with hi | hi <;> rcases hi' with hi' | hi' <;>
    rcases hj with hj | hj <;> rcases hj' with hj' | hj' <;>
    simp [initialTwo, conflictNumerator, hi, hi', hj, hj'] at hdiv <;> omega

/-- `t` changes every integral lift in `s` by a multiple of the denominator.
This is the freedom used to force a finite selector into a prescribed rich pool. -/
def Congruent {d : ℕ} (s t : LiftData d) : Prop :=
  ∀ i j, ∃ a b : ℤ,
    t.k i j = s.k i j + d * a ∧ t.l i j = s.l i j + d * b

lemma congruent_refl {d : ℕ} (s : LiftData d) : s.Congruent s := by
  intro i j
  exact ⟨0, 0, by simp, by simp⟩

lemma conflictNumerator_congruent {d : ℕ} {s t : LiftData d}
    (hst : s.Congruent t) (i₁ j₁ i₂ j₂ : Fin d) :
    (d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
          (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂) -
        conflictNumerator d i₁ j₁ i₂ j₂
          (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂) := by
  rcases hst i₁ j₁ with ⟨a₁, b₁, hk₁, hl₁⟩
  rcases hst i₂ j₂ with ⟨a₂, b₂, hk₂, hl₂⟩
  let A : ℤ := ((i₁ : ℕ) : ℤ) - ((i₂ : ℕ) : ℤ)
  let B : ℤ := ((j₁ : ℕ) : ℤ) - ((j₂ : ℕ) : ℤ)
  refine ⟨2 * (A * (a₁ - a₂) + B * (b₁ - b₂)), ?_⟩
  simp only [conflictNumerator]
  rw [hk₁, hl₁, hk₂, hl₂]
  dsimp [A, B]
  ring

lemma dvd_conflict_iff_of_congruent {d : ℕ} {s t : LiftData d}
    (hst : s.Congruent t) (i₁ j₁ i₂ j₂ : Fin d) :
    ((d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂)) ↔
    ((d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂)) := by
  have hdiff := conflictNumerator_congruent hst i₁ j₁ i₂ j₂
  rcases hdiff with ⟨q, hq⟩
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z - q, ?_⟩
    linear_combination hz - hq
  · rintro ⟨z, hz⟩
    refine ⟨z + q, ?_⟩
    linear_combination hz + hq

theorem separated_of_congruent {d : ℕ} {s t : LiftData d}
    (hs : s.Separated) (hst : s.Congruent t) : t.Separated := by
  intro i₁ j₁ i₂ j₂ hne ht
  exact hs i₁ j₁ i₂ j₂ hne
    ((dvd_conflict_iff_of_congruent hst i₁ j₁ i₂ j₂).mp ht)

/-- A finite version of the rich-pool forcing step.  Once a separated residue
selector exists, one may independently replace every selected lift by any
congruent lift in `P`, without losing separation. -/
theorem choose_congruent_in_pool {d : ℕ} (s : LiftData d) (P : Set RatPoint)
    (hP : ∀ i j, ∃ k l a b : ℤ,
      k = s.k i j + d * a ∧ l = s.l i j + d * b ∧ liftedPoint d i j k l ∈ P) :
    ∃ t : LiftData d, s.Congruent t ∧
      (∀ i j, t.point i j ∈ P) ∧ (s.Separated → t.Separated) := by
  choose k l a b hk hl hp using hP
  let t : LiftData d := ⟨k, l⟩
  have hst : s.Congruent t := by
    intro i j
    exact ⟨a i j, b i j, hk i j, hl i j⟩
  refine ⟨t, hst, ?_, fun hs ↦ separated_of_congruent hs hst⟩
  intro i j
  exact hp i j

end LiftData

/-- The embedding of an old residue when the denominator is multiplied by `p`. -/
def oldIndex (p : ℕ) (hp : 0 < p) {d : ℕ} (i : Fin d) : Fin (p * d) :=
  ⟨p * (i : ℕ), (Nat.mul_lt_mul_left hp).2 i.isLt⟩

lemma oldIndex_injective (p : ℕ) (hp : 0 < p) {d : ℕ} :
    Function.Injective (oldIndex p hp : Fin d → Fin (p * d)) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  change p * (i : ℕ) = p * (j : ℕ) at hv
  exact Fin.ext (Nat.mul_left_cancel hp hv)

lemma liftedPoint_oldIndex (p d : ℕ) (hp : 0 < p) (hd : d ≠ 0)
    (i j : Fin d) (k l : ℤ) :
    liftedPoint (p * d) (oldIndex p hp i) (oldIndex p hp j) k l =
      liftedPoint d i j k l := by
  apply Prod.ext <;> simp only [liftedPoint, oldIndex]
  · congr 1
    push_cast
    field_simp [Nat.ne_of_gt hp, hd]
  · congr 1
    push_cast
    field_simp [Nat.ne_of_gt hp, hd]

/-- Literal extension of the integral lifts from denominator `d` to `p*d`. -/
def PrimeExtends (p : ℕ) (hp : 0 < p) {d : ℕ}
    (s : LiftData d) (t : LiftData (p * d)) : Prop :=
  ∀ i j,
    t.k (oldIndex p hp i) (oldIndex p hp j) = s.k i j ∧
    t.l (oldIndex p hp i) (oldIndex p hp j) = s.l i j

lemma point_oldIndex_of_primeExtends (p : ℕ) (hp : 0 < p) {d : ℕ} (hd : d ≠ 0)
    {s : LiftData d} {t : LiftData (p * d)} (hst : PrimeExtends p hp s t)
    (i j : Fin d) :
    t.point (oldIndex p hp i) (oldIndex p hp j) = s.point i j := by
  rcases hst i j with ⟨hk, hl⟩
  simp only [LiftData.point, hk, hl]
  exact liftedPoint_oldIndex p d hp hd i j (s.k i j) (s.l i j)

/-- Separation descends along a literal prime extension. -/
theorem separated_of_primeExtension (p : ℕ) (hp : 0 < p) {d : ℕ} (hd : d ≠ 0)
    {s : LiftData d} {t : LiftData (p * d)}
    (hst : PrimeExtends p hp s t) (ht : t.Separated) : s.Separated := by
  rw [LiftData.separated_iff_sqDist_not_int hd]
  intro i₁ j₁ i₂ j₂ hne
  have hpne : p * d ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hp) hd
  have hpair :
      (oldIndex p hp i₁, oldIndex p hp j₁) ≠
        (oldIndex p hp i₂, oldIndex p hp j₂) := by
    intro h
    apply hne
    exact Prod.ext
      (oldIndex_injective p hp (congrArg Prod.fst h))
      (oldIndex_injective p hp (congrArg Prod.snd h))
  have hsep := (LiftData.separated_iff_sqDist_not_int hpne t).mp ht
    (oldIndex p hp i₁) (oldIndex p hp j₁)
    (oldIndex p hp i₂) (oldIndex p hp j₂) hpair
  rw [point_oldIndex_of_primeExtends p hp hd hst i₁ j₁,
    point_oldIndex_of_primeExtends p hp hd hst i₂ j₂] at hsep
  exact hsep

/-- Quotient and parity of a residue at doubled denominator. -/
def halfIndex {d : ℕ} (i : Fin (2 * d)) : Fin d :=
  ⟨(i : ℕ) / 2, by omega⟩

def parity {d : ℕ} (i : Fin (2 * d)) : ℕ :=
  (i : ℕ) % 2

lemma parity_lt_two {d : ℕ} (i : Fin (2 * d)) : parity i < 2 := by
  exact Nat.mod_lt _ (by omega)

lemma val_eq_two_mul_half_add_parity {d : ℕ} (i : Fin (2 * d)) :
    (i : ℕ) = 2 * (halfIndex i : ℕ) + parity i := by
  simp only [halfIndex, parity]
  omega

/-- The forward extension across the trivial prime `2`: copy the old lift on
each of the four parity cosets. -/
def doubleLift {d : ℕ} (s : LiftData d) : LiftData (2 * d) where
  k := fun i j ↦ s.k (halfIndex i) (halfIndex j)
  l := fun i j ↦ s.l (halfIndex i) (halfIndex j)

lemma halfIndex_oldIndex_two {d : ℕ} (i : Fin d) :
    halfIndex (oldIndex 2 (by omega) i) = i := by
  apply Fin.ext
  change (2 * (i : ℕ)) / 2 = (i : ℕ)
  omega

lemma doubleLift_primeExtends {d : ℕ} (s : LiftData d) :
    PrimeExtends 2 (by omega) s (doubleLift s) := by
  intro i j
  simp [doubleLift, halfIndex_oldIndex_two]

lemma sqDist_doubleLift_of_same_parity {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (i₁ j₁ i₂ j₂ : Fin (2 * d))
    (hi : parity i₁ = parity i₂) (hj : parity j₁ = parity j₂) :
    sqDist ((doubleLift s).point i₁ j₁) ((doubleLift s).point i₂ j₂) =
      sqDist (s.point (halfIndex i₁) (halfIndex j₁))
        (s.point (halfIndex i₂) (halfIndex j₂)) := by
  have hvi₁ := val_eq_two_mul_half_add_parity i₁
  have hvi₂ := val_eq_two_mul_half_add_parity i₂
  have hvj₁ := val_eq_two_mul_half_add_parity j₁
  have hvj₂ := val_eq_two_mul_half_add_parity j₂
  simp only [LiftData.point, doubleLift, liftedPoint, sqDist]
  push_cast
  field_simp [hd]
  rw [hvi₁, hvi₂, hvj₁, hvj₂, hi, hj]
  push_cast
  ring

lemma doubleLift_cross_not_integral {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (i₁ j₁ i₂ j₂ : Fin (2 * d))
    (hbit : parity i₁ ≠ parity i₂ ∨ parity j₁ ≠ parity j₂) :
    ¬∃ z : ℤ, sqDist ((doubleLift s).point i₁ j₁) ((doubleLift s).point i₂ j₂) = z := by
  intro hInt
  have hd2 : 2 * d ≠ 0 := Nat.mul_ne_zero (by omega) hd
  have hdiv := (sqDist_liftedPoint_isInt_iff (2 * d) hd2 i₁ j₁ i₂ j₂
    ((doubleLift s).k i₁ j₁) ((doubleLift s).l i₁ j₁)
    ((doubleLift s).k i₂ j₂) ((doubleLift s).l i₂ j₂)).mp hInt
  rcases hdiv with ⟨z, hz⟩
  have hvi₁ := val_eq_two_mul_half_add_parity i₁
  have hvi₂ := val_eq_two_mul_half_add_parity i₂
  have hvj₁ := val_eq_two_mul_half_add_parity j₁
  have hvj₂ := val_eq_two_mul_half_add_parity j₂
  have hpi₁ : parity i₁ = 0 ∨ parity i₁ = 1 := by
    have := parity_lt_two i₁
    omega
  have hpi₂ : parity i₂ = 0 ∨ parity i₂ = 1 := by
    have := parity_lt_two i₂
    omega
  have hpj₁ : parity j₁ = 0 ∨ parity j₁ = 1 := by
    have := parity_lt_two j₁
    omega
  have hpj₂ : parity j₂ = 0 ∨ parity j₂ = 1 := by
    have := parity_lt_two j₂
    omega
  have h4 : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
  have h8 : (8 : ZMod 4) = 0 := by
    calc
      (8 : ZMod 4) = 4 + 4 := by ring
      _ = 0 := by rw [h4]; exact add_zero 0
  have h1 : (1 : ZMod 4) ≠ 0 := by decide
  have h2 : (2 : ZMod 4) ≠ 0 := by decide
  simp only [doubleLift, conflictNumerator] at hz
  rcases hpi₁ with hpi₁ | hpi₁ <;> rcases hpi₂ with hpi₂ | hpi₂ <;>
    rcases hpj₁ with hpj₁ | hpj₁ <;> rcases hpj₂ with hpj₂ | hpj₂ <;>
    rw [hvi₁, hvi₂, hvj₁, hvj₂, hpi₁, hpi₂, hpj₁, hpj₂] at hz <;>
    simp [hpi₁, hpi₂, hpj₁, hpj₂] at hbit
  all_goals
    have hz4 := congrArg (fun x : ℤ ↦ (x : ZMod 4)) hz
    norm_num at hz4
    ring_nf at hz4
    simp only [h4, h8, mul_zero, add_zero, sub_zero] at hz4
    first | exact h1 hz4 | exact h2 hz4

/-- A fully proved forward prime step for the trivial prime `2`. -/
theorem doubleLift_separated {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (hs : s.Separated) : (doubleLift s).Separated := by
  rw [LiftData.separated_iff_sqDist_not_int (Nat.mul_ne_zero (by omega) hd)]
  intro i₁ j₁ i₂ j₂ hne
  by_cases hi : parity i₁ = parity i₂
  · by_cases hj : parity j₁ = parity j₂
    · have hhalf :
          (halfIndex i₁, halfIndex j₁) ≠ (halfIndex i₂, halfIndex j₂) := by
        intro h
        apply hne
        apply Prod.ext <;> apply Fin.ext
        · have hq := congrArg (fun x : Fin d ↦ (x : ℕ)) (congrArg Prod.fst h)
          rw [val_eq_two_mul_half_add_parity i₁,
            val_eq_two_mul_half_add_parity i₂, hi, hq]
        · have hq := congrArg (fun x : Fin d ↦ (x : ℕ)) (congrArg Prod.snd h)
          rw [val_eq_two_mul_half_add_parity j₁,
            val_eq_two_mul_half_add_parity j₂, hj, hq]
      have hold := (LiftData.separated_iff_sqDist_not_int hd s).mp hs
        (halfIndex i₁) (halfIndex j₁) (halfIndex i₂) (halfIndex j₂) hhalf
      rwa [sqDist_doubleLift_of_same_parity hd s i₁ j₁ i₂ j₂ hi hj]
    · exact doubleLift_cross_not_integral hd s i₁ j₁ i₂ j₂ (Or.inr hj)
  · exact doubleLift_cross_not_integral hd s i₁ j₁ i₂ j₂ (Or.inl hi)

/-- The denominator sequence obtained by iterating the proved prime-`2` step. -/
def twoDenom : ℕ → ℕ
  | 0 => 2
  | n + 1 => 2 * twoDenom n

lemma twoDenom_ne_zero (n : ℕ) : twoDenom n ≠ 0 := by
  induction n with
  | zero => norm_num [twoDenom]
  | succ n ih => exact Nat.mul_ne_zero (by omega) ih

/-- A literal compatible selector chain along `2,4,8,…`. -/
def twoChain : (n : ℕ) → LiftData (twoDenom n)
  | 0 => LiftData.initialTwo
  | n + 1 => doubleLift (twoChain n)

lemma twoChain_primeExtends (n : ℕ) :
    PrimeExtends 2 (by omega) (twoChain n) (twoChain (n + 1)) := by
  simpa [twoChain] using doubleLift_primeExtends (twoChain n)

theorem twoChain_separated (n : ℕ) : (twoChain n).Separated := by
  induction n with
  | zero =>
      change LiftData.initialTwo.Separated
      exact LiftData.initialTwo_separated
  | succ n ih =>
      change (doubleLift (twoChain n)).Separated
      exact doubleLift_separated (twoDenom_ne_zero n) (twoChain n) ih

/-- Quotient and remainder of a residue at a denominator enlarged by `p`. -/
def quotientIndex (p : ℕ) {d : ℕ} (i : Fin (p * d)) : Fin d :=
  if hp : 0 < p then
    ⟨(i : ℕ) / p,
      (Nat.div_lt_iff_lt_mul hp).2 (lt_of_lt_of_eq i.isLt (Nat.mul_comm p d))⟩
  else by
    have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    exact Fin.elim0 (Fin.cast (by simp) i)

def remainderIndex (p : ℕ) {d : ℕ} (i : Fin (p * d)) : ℕ :=
  (i : ℕ) % p

lemma remainderIndex_lt (p : ℕ) (hp : 0 < p) {d : ℕ} (i : Fin (p * d)) :
    remainderIndex p i < p := Nat.mod_lt _ hp

lemma val_eq_mul_quotient_add_remainder (p : ℕ) (hp : 0 < p) {d : ℕ}
    (i : Fin (p * d)) :
    (i : ℕ) = p * (quotientIndex p i : ℕ) + remainderIndex p i := by
  simp only [quotientIndex, hp, ↓reduceDIte, remainderIndex]
  simpa [Nat.add_comm] using (Nat.mod_add_div (i : ℕ) p).symm

/-- Copy an old selector on every coset when multiplying its denominator by `p`. -/
def primeCopyLift (p : ℕ) {d : ℕ} (s : LiftData d) : LiftData (p * d) where
  k := fun i j ↦ s.k (quotientIndex p i) (quotientIndex p j)
  l := fun i j ↦ s.l (quotientIndex p i) (quotientIndex p j)

lemma quotientIndex_oldIndex (p : ℕ) (hp : 0 < p) {d : ℕ} (i : Fin d) :
    quotientIndex p (oldIndex p hp i) = i := by
  apply Fin.ext
  simp only [quotientIndex, hp, ↓reduceDIte, oldIndex]
  rw [Nat.mul_comm]
  exact Nat.mul_div_left (i : ℕ) hp

lemma primeCopy_primeExtends (p : ℕ) (hp : 0 < p) {d : ℕ} (s : LiftData d) :
    PrimeExtends p hp s (primeCopyLift p s) := by
  intro i j
  simp [primeCopyLift, quotientIndex_oldIndex p hp]

/-- An exact algebraic form of the source's condition that a prime be
"trivial": the binary norm form is anisotropic modulo `p`. -/
def NormAnisotropic (p : ℕ) : Prop :=
  ∀ x y : ZMod p, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0

/-- The finite-field fact used by the source for every prime `3 mod 4`. -/
theorem normAnisotropic_of_prime_mod_four_eq_three (p : ℕ) [Fact p.Prime]
    (hp3 : p % 4 = 3) : NormAnisotropic p := by
  intro x y hxy
  by_cases hy : y = 0
  · subst y
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hxy
    exact ⟨sq_eq_zero_iff.mp hxy, rfl⟩
  · have hsq : x ^ 2 = -(y ^ 2) := by linear_combination hxy
    exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy hsq hp3).elim

/-- A root of `-1` modulo a nontrivial prime, in the exact form used by
the line-permutation construction (4.4). -/
def NegOneRoot (p : ℕ) := {x : ZMod p // x ^ 2 = -1}

theorem negOneRoot_nonempty_of_prime_mod_four_eq_one (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) : Nonempty (NegOneRoot p) := by
  have hn3 : p % 4 ≠ 3 := by omega
  rcases ZMod.exists_sq_eq_neg_one_iff.mpr hn3 with ⟨x, hx⟩
  exact ⟨⟨x, by simpa [pow_two] using hx.symm⟩⟩

/-- The exact opposite-root shift calculation (S6)--(S7), isolated from the
choice of canonical integer representatives.  Here `i₁,i₂` are the two
distinguished arguments, while `i` is the argument being compared. -/
theorem oppositeRoot_shift_identity (p : ℕ) [Fact p.Prime]
    (i i₁ i₂ j₁ j₂ lam₁ lam₂ : ZMod p)
    (hpne : p ≠ 2) (hopp : lam₂ = -lam₁) (hlam : lam₁ ≠ 0)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂))
    (h₁ : i₁ * (lam₁ - lam₂) = -j₁)
    (h₂ : i₂ * (lam₂ - lam₁) = -j₂) :
    i = i₁ + i₂ ∧
      (i₁ - i = -i₂ ∧ i₂ - i = -i₁) ∧
      (i₁ - i) + (-i₁) = (i₂ - i) + (-i₂) := by
  have hp2 : (2 : ZMod p) ≠ 0 := by
    have hprime : p.Prime := Fact.out
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdiv
    have hge : 2 ≤ p := hprime.two_le
    exact hpne (by omega)
  have hdelta : lam₁ - lam₂ ≠ 0 := by
    rw [hopp]
    intro h
    apply hlam
    have : (2 : ZMod p) * lam₁ = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left hp2
  have hi : i = i₁ + i₂ := by
    apply mul_right_cancel₀ hdelta
    rw [add_mul]
    have h₂' : i₂ * (lam₁ - lam₂) = j₂ := by
      rw [hopp] at h₂ ⊢
      linear_combination -h₂
    linear_combination hline - h₁ - h₂'
  subst i
  constructor
  · rfl
  constructor
  · constructor <;> ring
  · ring

/-- The localized quotient from (4.6a).  The parameter `Dinv` represents the
inverse modulo `q` of the complementary factor `D` in `d = qD`. -/
def localizedQuotient (q : ℕ) (Dinv : ZMod q) (x : ℤ) : ZMod q :=
  ((x / (q : ℤ) : ℤ) : ZMod q) * Dinv

lemma localizedQuotient_mul (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q) (a : ℤ) :
    localizedQuotient q Dinv ((q : ℤ) * a) = (a : ZMod q) * Dinv := by
  simp only [localizedQuotient]
  rw [Int.mul_ediv_cancel_left a (Int.ofNat_ne_zero.mpr hq)]

lemma localizedQuotient_add (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q) (x y : ℤ)
    (hx : (q : ℤ) ∣ x) (hy : (q : ℤ) ∣ y) :
    localizedQuotient q Dinv (x + y) =
      localizedQuotient q Dinv x + localizedQuotient q Dinv y := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  rw [← Int.mul_add, localizedQuotient_mul q hq,
    localizedQuotient_mul q hq, localizedQuotient_mul q hq]
  push_cast
  ring

lemma localizedQuotient_neg (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q) (x : ℤ)
    (hx : (q : ℤ) ∣ x) :
    localizedQuotient q Dinv (-x) = -localizedQuotient q Dinv x := by
  rcases hx with ⟨a, rfl⟩
  rw [← mul_neg, localizedQuotient_mul q hq, localizedQuotient_mul q hq]
  push_cast
  ring

lemma localizedQuotient_sub (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q) (x y : ℤ)
    (hx : (q : ℤ) ∣ x) (hy : (q : ℤ) ∣ y) :
    localizedQuotient q Dinv (x - y) =
      localizedQuotient q Dinv x - localizedQuotient q Dinv y := by
  rw [sub_eq_add_neg, localizedQuotient_add q hq Dinv x (-y) hx (dvd_neg.mpr hy),
    localizedQuotient_neg q hq Dinv y hy]
  rw [sub_eq_add_neg]

/-- The correction-term telescope at the end of the new--new consistency
case (4.15a)--(4.16). -/
lemma localizedQuotient_telescope (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (j₁ j₂ j₃ j₄ : ℤ)
    (h₃₄ : (q : ℤ) ∣ j₃ - j₄) (h₁₃ : (q : ℤ) ∣ j₁ - j₃)
    (h₂₄ : (q : ℤ) ∣ j₂ - j₄) :
    localizedQuotient q Dinv (j₃ - j₄) + localizedQuotient q Dinv (j₁ - j₃) -
        localizedQuotient q Dinv (j₂ - j₄) =
      localizedQuotient q Dinv (j₁ - j₂) := by
  have hsum : (q : ℤ) ∣ (j₃ - j₄) + (j₁ - j₃) := dvd_add h₃₄ h₁₃
  calc
    _ = localizedQuotient q Dinv ((j₃ - j₄) + (j₁ - j₃)) -
        localizedQuotient q Dinv (j₂ - j₄) := by
          rw [localizedQuotient_add q hq Dinv _ _ h₃₄ h₁₃]
    _ = localizedQuotient q Dinv
        (((j₃ - j₄) + (j₁ - j₃)) - (j₂ - j₄)) := by
          rw [localizedQuotient_sub q hq Dinv _ _ hsum h₂₄]
    _ = localizedQuotient q Dinv (j₁ - j₂) := by ring_nf

/-- Formula (4.16) before replacing the second shift by its equal cross
shift from (S7).  This is a pure ring identity, so it is reusable at every
prime-power component. -/
lemma auxiliaryOldLines_relation {R : Type*} [CommRing R]
    (i s₁ s₂ j₁ j₂ j₃ j₄ lam₁ lam₂ : R)
    (hline : i * (lam₁ - lam₂) = -(j₁ - j₂))
    (haux₁ : (i + s₁) * (lam₁ - lam₂) = -(j₁ - j₃))
    (haux₂ : (i + s₂) * (lam₂ - lam₁) = -(j₂ - j₄)) :
    (i + s₁ + s₂) * (lam₂ - lam₁) = -(j₃ - j₄) := by
  have hj₃₁ : j₃ - j₁ = (i + s₁) * (lam₁ - lam₂) := by
    simpa only [neg_sub] using haux₁.symm
  have hj₁₂ : j₁ - j₂ = -(i * (lam₁ - lam₂)) := by
    linear_combination hline
  have hj₂₄ : j₂ - j₄ = (i + s₂) * (lam₁ - lam₂) := by
    linear_combination haux₂
  calc
    _ = -((i + s₁) * (lam₁ - lam₂) + (-(i * (lam₁ - lam₂))) +
        (i + s₂) * (lam₁ - lam₂)) := by ring
    _ = -((j₃ - j₁) + (j₁ - j₂) + (j₂ - j₄)) := by
      rw [hj₃₁, hj₁₂, hj₂₄]
    _ = -(j₃ - j₄) := by ring

lemma sqDist_primeCopy_of_same_remainders (p : ℕ) (hp : 0 < p) {d : ℕ}
    (hd : d ≠ 0) (s : LiftData d) (i₁ j₁ i₂ j₂ : Fin (p * d))
    (hi : remainderIndex p i₁ = remainderIndex p i₂)
    (hj : remainderIndex p j₁ = remainderIndex p j₂) :
    sqDist ((primeCopyLift p s).point i₁ j₁) ((primeCopyLift p s).point i₂ j₂) =
      sqDist (s.point (quotientIndex p i₁) (quotientIndex p j₁))
        (s.point (quotientIndex p i₂) (quotientIndex p j₂)) := by
  have hvi₁ := val_eq_mul_quotient_add_remainder p hp i₁
  have hvi₂ := val_eq_mul_quotient_add_remainder p hp i₂
  have hvj₁ := val_eq_mul_quotient_add_remainder p hp j₁
  have hvj₂ := val_eq_mul_quotient_add_remainder p hp j₂
  simp only [LiftData.point, primeCopyLift, liftedPoint, sqDist]
  push_cast
  field_simp [Nat.ne_of_gt hp, hd]
  rw [hvi₁, hvi₂, hvj₁, hvj₂, hi, hj]
  push_cast
  ring

lemma primeCopy_cross_not_integral (p : ℕ) (hp : 0 < p) (han : NormAnisotropic p)
    {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (i₁ j₁ i₂ j₂ : Fin (p * d))
    (hrem : remainderIndex p i₁ ≠ remainderIndex p i₂ ∨
      remainderIndex p j₁ ≠ remainderIndex p j₂) :
    ¬∃ z : ℤ,
      sqDist ((primeCopyLift p s).point i₁ j₁) ((primeCopyLift p s).point i₂ j₂) = z := by
  intro hInt
  have hpd : p * d ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hp) hd
  have hdiv := (sqDist_liftedPoint_isInt_iff (p * d) hpd i₁ j₁ i₂ j₂
    ((primeCopyLift p s).k i₁ j₁) ((primeCopyLift p s).l i₁ j₁)
    ((primeCopyLift p s).k i₂ j₂) ((primeCopyLift p s).l i₂ j₂)).mp hInt
  rcases hdiv with ⟨z, hz⟩
  have hvi₁ := val_eq_mul_quotient_add_remainder p hp i₁
  have hvi₂ := val_eq_mul_quotient_add_remainder p hp i₂
  have hvj₁ := val_eq_mul_quotient_add_remainder p hp j₁
  have hvj₂ := val_eq_mul_quotient_add_remainder p hp j₂
  have hzp := congrArg (fun x : ℤ ↦ (x : ZMod p)) hz
  simp only [primeCopyLift, conflictNumerator] at hzp
  rw [hvi₁, hvi₂, hvj₁, hvj₂] at hzp
  push_cast at hzp
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  simp only [hp0, zero_mul, mul_zero, zero_add, add_zero] at hzp
  ring_nf at hzp
  let xi₁ : ZMod p := remainderIndex p i₁
  let xi₂ : ZMod p := remainderIndex p i₂
  let xj₁ : ZMod p := remainderIndex p j₁
  let xj₂ : ZMod p := remainderIndex p j₂
  have hzp' : -(xi₁ * xi₂ * 2) + xi₁ ^ 2 + xi₂ ^ 2 - xj₁ * xj₂ * 2 +
      xj₁ ^ 2 + xj₂ ^ 2 = 0 := by
    simpa [xi₁, xi₂, xj₁, xj₂] using hzp
  have hnorm : (xi₁ - xi₂) ^ 2 + (xj₁ - xj₂) ^ 2 = 0 := by
    calc
      _ = -(xi₁ * xi₂ * 2) + xi₁ ^ 2 + xi₂ ^ 2 - xj₁ * xj₂ * 2 +
          xj₁ ^ 2 + xj₂ ^ 2 := by ring
      _ = 0 := hzp'
  rcases han (xi₁ - xi₂) (xj₁ - xj₂) hnorm with ⟨hi, hj⟩
  dsimp [xi₁, xi₂] at hi
  dsimp [xj₁, xj₂] at hj
  have hi' : remainderIndex p i₁ = remainderIndex p i₂ := by
    have hc := congrArg ZMod.val (sub_eq_zero.mp hi)
    simpa [ZMod.val_natCast_of_lt (remainderIndex_lt p hp i₁),
      ZMod.val_natCast_of_lt (remainderIndex_lt p hp i₂)] using hc
  have hj' : remainderIndex p j₁ = remainderIndex p j₂ := by
    have hc := congrArg ZMod.val (sub_eq_zero.mp hj)
    simpa [ZMod.val_natCast_of_lt (remainderIndex_lt p hp j₁),
      ZMod.val_natCast_of_lt (remainderIndex_lt p hp j₂)] using hc
  exact hrem.elim (fun h ↦ h hi') (fun h ↦ h hj')

/-- The explicit forward source construction for every anisotropic modulus;
in particular it applies to primes congruent to `3 mod 4`. -/
theorem primeCopy_separated (p : ℕ) (hp : 0 < p) (han : NormAnisotropic p)
    {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (hs : s.Separated) :
    (primeCopyLift p s).Separated := by
  rw [LiftData.separated_iff_sqDist_not_int (Nat.mul_ne_zero (Nat.ne_of_gt hp) hd)]
  intro i₁ j₁ i₂ j₂ hne
  by_cases hi : remainderIndex p i₁ = remainderIndex p i₂
  · by_cases hj : remainderIndex p j₁ = remainderIndex p j₂
    · have hquot :
          (quotientIndex p i₁, quotientIndex p j₁) ≠
            (quotientIndex p i₂, quotientIndex p j₂) := by
        intro h
        apply hne
        apply Prod.ext <;> apply Fin.ext
        · have hq := congrArg (fun x : Fin d ↦ (x : ℕ)) (congrArg Prod.fst h)
          rw [val_eq_mul_quotient_add_remainder p hp i₁,
            val_eq_mul_quotient_add_remainder p hp i₂, hi, hq]
        · have hq := congrArg (fun x : Fin d ↦ (x : ℕ)) (congrArg Prod.snd h)
          rw [val_eq_mul_quotient_add_remainder p hp j₁,
            val_eq_mul_quotient_add_remainder p hp j₂, hj, hq]
      have hold := (LiftData.separated_iff_sqDist_not_int hd s).mp hs
        (quotientIndex p i₁) (quotientIndex p j₁)
        (quotientIndex p i₂) (quotientIndex p j₂) hquot
      rwa [sqDist_primeCopy_of_same_remainders p hp hd s i₁ j₁ i₂ j₂ hi hj]
    · exact primeCopy_cross_not_integral p hp han hd s i₁ j₁ i₂ j₂ (Or.inr hj)
  · exact primeCopy_cross_not_integral p hp han hd s i₁ j₁ i₂ j₂ (Or.inl hi)

/-- The source's complete trivial odd-prime step, with literal preservation
of every old lift. -/
theorem primeCopy_step_of_prime_mod_four_eq_three (p : ℕ) [Fact p.Prime]
    (hp3 : p % 4 = 3) {d : ℕ} (hd : d ≠ 0) (s : LiftData d) (hs : s.Separated) :
    ∃ t : LiftData (p * d),
      PrimeExtends p (Nat.Prime.pos (Fact.out : p.Prime)) s t ∧ t.Separated := by
  have hprime : p.Prime := Fact.out
  exact ⟨primeCopyLift p s, primeCopy_primeExtends p hprime.pos s,
    primeCopy_separated p hprime.pos
      (normAnisotropic_of_prime_mod_four_eq_three p hp3) hd s hs⟩

/-- The prime-power modulus which survives after cancelling the common
prime-power content of an input difference. -/
def survivingModulus (d a : ℕ) : ℕ :=
  d / Nat.gcd d a

/-- Absolute difference between the canonical representatives of two residues. -/
def indexDiff {d : ℕ} (i j : Fin d) : ℕ :=
  Int.natAbs (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))

/-- Goodness condition (4.3), expressed using the equivalent quotient by the
capped gcd rather than prime valuations. -/
def GoodPerm (d : ℕ) (π : Equiv.Perm (Fin d)) : Prop :=
  ∀ i j, i ≠ j →
    ¬(survivingModulus d (indexDiff i j) : ℤ) ∣
      (((π i : Fin d) : ℕ) : ℤ) - (((π j : Fin d) : ℕ) : ℤ)

/-- The same condition for a raw endomap.  The source constructs the line
maps by formulas first and obtains permutations from goodness afterwards. -/
def GoodMap (d : ℕ) (f : Fin d → Fin d) : Prop :=
  ∀ i j, i ≠ j →
    ¬(survivingModulus d (indexDiff i j) : ℤ) ∣
      (((f i : Fin d) : ℕ) : ℤ) - (((f j : Fin d) : ℕ) : ℤ)

lemma GoodMap.injective {d : ℕ} {f : Fin d → Fin d} (hf : GoodMap d f) :
    Function.Injective f := by
  intro i j hij
  by_contra hne
  exact hf i j hne (by simp [hij])

noncomputable def GoodMap.toPerm {d : ℕ} (f : Fin d → Fin d) (hf : GoodMap d f) :
    Equiv.Perm (Fin d) :=
  Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf.injective, rfl⟩)

lemma GoodMap.toPerm_apply {d : ℕ} (f : Fin d → Fin d) (hf : GoodMap d f)
    (i : Fin d) : GoodMap.toPerm f hf i = f i := rfl

lemma GoodMap.goodPerm_toPerm {d : ℕ} (f : Fin d → Fin d) (hf : GoodMap d f) :
    GoodPerm d (GoodMap.toPerm f hf) := by
  simpa only [GoodPerm, GoodMap, GoodMap.toPerm_apply] using hf

lemma survivingModulus_dvd (d a : ℕ) : survivingModulus d a ∣ d := by
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d a)

/-- The identity permutation is good exactly when canonical input differences
remain distinct modulo their surviving modulus.  This elementary form is useful
for testing concrete digit permutations. -/
lemma goodPerm_iff (d : ℕ) (π : Equiv.Perm (Fin d)) :
    GoodPerm d π ↔ ∀ i j, i ≠ j →
      ¬(survivingModulus d (indexDiff i j) : ℤ) ∣
        (((π i : Fin d) : ℕ) : ℤ) - (((π j : Fin d) : ℕ) : ℤ) := by
  rfl

/-- Richness in all congruence classes of all rational translates, as in (4.1).
The infinitude is stronger than the nonemptiness used by the finite forcing
lemma, and is what permits repeated choices along a denominator chain. -/
def Rich (P : Set RatPoint) : Prop :=
  ∀ (d : ℕ), d ≠ 0 → ∀ (i j : Fin d) (a b : ℤ),
    Set.Infinite {x : RatPoint | ∃ k l : ℤ,
      x = liftedPoint d i j k l ∧
      a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d] ∧ x ∈ P}

/-- At one finite denominator, richness forces any separated selector into the
pool while preserving all its congruence data. -/
theorem finiteSelector_in_rich_pool {d : ℕ} (hd : d ≠ 0) (s : LiftData d)
    (P : Set RatPoint) (hP : Rich P) (hs : s.Separated) :
    ∃ t : LiftData d, t.Separated ∧ ∀ i j, t.point i j ∈ P := by
  have havail : ∀ i j, ∃ k l a b : ℤ,
      k = s.k i j + d * a ∧ l = s.l i j + d * b ∧ liftedPoint d i j k l ∈ P := by
    intro i j
    rcases (hP d hd i j (s.k i j) (s.l i j)).nonempty with ⟨x, hx⟩
    rcases hx with ⟨k, l, rfl, hk, hl, hp⟩
    rcases Int.modEq_iff_add_fac.mp hk with ⟨a, ha⟩
    rcases Int.modEq_iff_add_fac.mp hl with ⟨b, hb⟩
    exact ⟨k, l, a, b, ha, hb, hp⟩
  rcases s.choose_congruent_in_pool P havail with ⟨t, -, hmem, hsep⟩
  exact ⟨t, hsep hs, hmem⟩

/-- A set of rational points has the partial Steinhaus property in coordinates. -/
def IsPartial (T : Set RatPoint) : Prop :=
  ∀ ⦃x⦄, x ∈ T → ∀ ⦃y⦄, y ∈ T → x ≠ y → ¬∃ z : ℤ, sqDist x y = z

/-- An abstract compatible selector immediately gives a partial selected range. -/
theorem range_isPartial {ι : Type*} (f : ι → RatPoint)
    (hsep : ∀ i j, i ≠ j → ¬∃ z : ℤ, sqDist (f i) (f j) = z) :
    IsPartial (Set.range f) := by
  intro x hx y hy hxy
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨j, rfl⟩
  exact hsep i j (fun hij ↦ hxy (congrArg f hij))

/-- Rational translation classes modulo the integer lattice. -/
abbrev RatResidue := AddCircle (1 : ℚ) × AddCircle (1 : ℚ)

def residue (x : RatPoint) : RatResidue :=
  ((x.1 : AddCircle (1 : ℚ)), (x.2 : AddCircle (1 : ℚ)))

def HitsEveryIntegerTranslate (T : Set RatPoint) : Prop :=
  ∀ x : RatPoint, ∃ y ∈ T, residue y = residue x

lemma range_hitsEveryIntegerTranslate (f : RatResidue → RatPoint)
    (hsection : ∀ r, residue (f r) = r) :
    HitsEveryIntegerTranslate (Set.range f) := by
  intro x
  exact ⟨f (residue x), ⟨residue x, rfl⟩, hsection (residue x)⟩

/-- The final quotient-level assembly step: a separated section of the
rational torus gives a partial Steinhaus set meeting every rational translate
of `ℤ²`. -/
theorem selector_of_separated_section (P : Set RatPoint) (f : RatResidue → RatPoint)
    (hmem : ∀ r, f r ∈ P) (hsection : ∀ r, residue (f r) = r)
    (hsep : ∀ r s, r ≠ s → ¬∃ z : ℤ, sqDist (f r) (f s) = z) :
    ∃ T : Set RatPoint,
      T ⊆ P ∧ IsPartial T ∧ HitsEveryIntegerTranslate T := by
  refine ⟨Set.range f, ?_, range_isPartial f hsep, range_hitsEveryIntegerTranslate f hsection⟩
  rintro x ⟨r, rfl⟩
  exact hmem r

end

end Erdos215.Selector
