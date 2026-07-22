/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 424.
https://www.erdosproblems.com/forum/thread/424

Informal authors:
- ChatGPT 5.6 Pro
- Samuel Korsky

Formal authors:
- Codex
- Boris Alexeev

URLs:
- https://www.erdosproblems.com/forum/thread/424/proof-claims#proof-claim-91
- https://drive.google.com/file/d/1SGSUQhNB8KL75VPqdfAq9yzFNEYL6Mwn/view
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/424.lean
-/
import Mathlib

/-!
# Erdős Problem 424 (Hofstadter's `ab - 1` problem)
-/

namespace Erdos424

/-- The recursively generated set in Erdős Problem 424.  Using an inductive
predicate makes the phrase "the smallest set" literal: its constructors are
exactly the two seeds and the closure rule. -/
inductive Generated : ℕ → Prop where
  | two : Generated 2
  | three : Generated 3
  | mul_sub_one {a b : ℕ} : Generated a → Generated b → a ≠ b →
      Generated (a * b - 1)

namespace Generated

theorem five : Generated 5 := by
  simpa using mul_sub_one two three (by norm_num)

theorem nine : Generated 9 := by
  simpa using mul_sub_one two five (by norm_num)

theorem fourteen : Generated 14 := by
  simpa using mul_sub_one three five (by norm_num)

theorem seventeen : Generated 17 := by
  simpa using mul_sub_one two nine (by norm_num)

/-- Every generated number is positive. -/
theorem pos {n : ℕ} (hn : Generated n) : 0 < n := by
  induction hn with
  | two => norm_num
  | three => norm_num
  | @mul_sub_one a b ha hb hab iha ihb =>
      have hab' : 1 < a * b := by
        rcases lt_or_gt_of_ne hab with hab | hab <;> nlinarith
      omega

end Generated

/-- The affine generator `T_a(x) = ax - 1`. -/
def T (a x : ℕ) : ℕ := a * x - 1

/-- Apply a word of affine generators from left to right. -/
def eval : List ℕ → ℕ → ℕ
  | [], x => x
  | a :: w, x => eval w (T a x)

@[simp] theorem eval_cons (a : ℕ) (w : List ℕ) (x : ℕ) :
    eval (a :: w) x = eval w (T a x) := rfl

theorem lt_T_self {a x : ℕ} (ha : 2 ≤ a) (hx : 1 < x) : x < T a x := by
  simp only [T]
  have hax : x + 2 ≤ a * x := by nlinarith
  omega

/-- Starting above every multiplier, a word made from generated multipliers
can be evaluated inside the generated set.  The strict growth simultaneously
guarantees that every use of the closure rule has distinct inputs. -/
theorem eval_generated_of_lt
    (w : List ℕ) {x : ℕ} (hx : Generated x) (hx1 : 1 < x)
    (hgen : ∀ a ∈ w, Generated a) (htwo : ∀ a ∈ w, 2 ≤ a)
    (hlt : ∀ a ∈ w, a < x) :
    Generated (eval w x) ∧ x ≤ eval w x := by
  induction w generalizing x with
  | nil => exact ⟨hx, le_rfl⟩
  | cons a w ih =>
      have ha_gen : Generated a := hgen a (by simp)
      have ha_two : 2 ≤ a := htwo a (by simp)
      have ha_lt : a < x := hlt a (by simp)
      have hxT : x < T a x := lt_T_self ha_two hx1
      have ha_ne_x : a ≠ x := Nat.ne_of_lt ha_lt
      have hT_gen : Generated (T a x) := by
        exact Generated.mul_sub_one ha_gen hx ha_ne_x
      have hT1 : 1 < T a x := hx1.trans hxT
      have hgen' : ∀ b ∈ w, Generated b := by
        intro b hb
        exact hgen b (by simp [hb])
      have htwo' : ∀ b ∈ w, 2 ≤ b := by
        intro b hb
        exact htwo b (by simp [hb])
      have hlt' : ∀ b ∈ w, b < T a x := by
        intro b hb
        exact (hlt b (by simp [hb])).trans_le hxT.le
      obtain ⟨hfinal, hmono⟩ := ih hT_gen hT1 hgen' htwo' hlt'
      exact ⟨hfinal, hxT.le.trans hmono⟩

/-- The five multipliers used by the paper. -/
def multipliers : Finset ℕ := {2, 3, 5, 9, 14}

theorem mem_multipliers_generated {a : ℕ} (ha : a ∈ multipliers) : Generated a := by
  simp only [multipliers, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact Generated.two
  · exact Generated.three
  · exact Generated.five
  · exact Generated.nine
  · exact Generated.fourteen

theorem mem_multipliers_two_le {a : ℕ} (ha : a ∈ multipliers) : 2 ≤ a := by
  simp only [multipliers, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem mem_multipliers_lt_seventeen {a : ℕ} (ha : a ∈ multipliers) : a < 17 := by
  simp only [multipliers, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Every word over the paper's five multipliers evaluates at 17 to an element
of the generated set, with distinct inputs at every operation. -/
theorem eval_at_seventeen_generated (w : List ℕ)
    (hw : ∀ a ∈ w, a ∈ multipliers) : Generated (eval w 17) := by
  exact (eval_generated_of_lt w Generated.seventeen (by norm_num)
    (fun a ha ↦ mem_multipliers_generated (hw a ha))
    (fun a ha ↦ mem_multipliers_two_le (hw a ha))
    (fun a ha ↦ mem_multipliers_lt_seventeen (hw a ha))).1

/-! ## Affine words -/

/-- Evaluation over the integers, where subtraction does not truncate. -/
def evalInt : List ℕ → ℤ → ℤ
  | [], x => x
  | a :: w, x => evalInt w ((a : ℤ) * x - 1)

/-- Constant term of the affine map represented by a word. -/
def offset : List ℕ → ℤ
  | [] => 0
  | _ :: w => offset w - (w.prod : ℤ)

@[simp] theorem evalInt_cons (a : ℕ) (w : List ℕ) (x : ℤ) :
    evalInt (a :: w) x = evalInt w ((a : ℤ) * x - 1) := rfl

/-- A word acts as `x ↦ slope * x + offset`. -/
theorem evalInt_affine (w : List ℕ) (x : ℤ) :
    evalInt w x = (w.prod : ℤ) * x + offset w := by
  induction w generalizing x with
  | nil =>
      simp only [evalInt, offset, List.prod_nil, Nat.cast_one, one_mul, add_zero]
  | cons a w ih =>
      rw [evalInt_cons, ih]
      simp only [List.prod_cons, Nat.cast_mul, offset]
      ring

/-- On inputs above 1, integer evaluation agrees with natural-number
evaluation for words whose multipliers are at least 2. -/
theorem eval_cast_eq_evalInt (w : List ℕ) {x : ℕ} (hx : 1 < x)
    (htwo : ∀ a ∈ w, 2 ≤ a) : (eval w x : ℤ) = evalInt w x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
      have ha : 2 ≤ a := htwo a (by simp)
      have hxT : x < T a x := lt_T_self ha hx
      have htwo' : ∀ b ∈ w, 2 ≤ b := by
        intro b hb
        exact htwo b (by simp [hb])
      rw [eval_cons, evalInt_cons, ih (hx.trans hxT) htwo']
      simp only [T]
      rw [Int.ofNat_sub]
      · norm_num
      · nlinarith

/-- Two words of the same slope but different offsets give different values
at every natural input where no subtraction truncates. -/
theorem eval_ne_of_prod_eq_offset_ne
    {u v : List ℕ} {x : ℕ} (hx : 1 < x)
    (hu : ∀ a ∈ u, 2 ≤ a) (hv : ∀ a ∈ v, 2 ≤ a)
    (hprod : u.prod = v.prod) (hoffset : offset u ≠ offset v) :
    eval u x ≠ eval v x := by
  intro heval
  have hcast : (eval u x : ℤ) = (eval v x : ℤ) := by exact_mod_cast heval
  rw [eval_cast_eq_evalInt u hx hu, eval_cast_eq_evalInt v hx hv,
    evalInt_affine, evalInt_affine, hprod] at hcast
  exact hoffset (add_left_cancel hcast)

/-! ## Prime exponents and the common slope -/

/-- Exponents of `2,3,5,7` contributed by one allowed multiplier. -/
def primeIncrement (a : ℕ) : Fin 4 → ℕ :=
  match a with
  | 2 => ![1, 0, 0, 0]
  | 3 => ![0, 1, 0, 0]
  | 5 => ![0, 0, 1, 0]
  | 9 => ![0, 2, 0, 0]
  | 14 => ![1, 0, 0, 1]
  | _ => ![0, 0, 0, 0]

/-- Prime-exponent vector accumulated along a word. -/
def exponents (w : List ℕ) : Fin 4 → ℕ :=
  fun i ↦ (w.map fun a ↦ primeIncrement a i).sum

@[simp] theorem exponents_nil (i : Fin 4) : exponents [] i = 0 := by
  simp [exponents]

@[simp] theorem exponents_cons (a : ℕ) (w : List ℕ) (i : Fin 4) :
    exponents (a :: w) i = primeIncrement a i + exponents w i := by
  simp [exponents]

theorem allowed_factorization {a : ℕ} (ha : a ∈ multipliers) :
    a = 2 ^ primeIncrement a 0 * 3 ^ primeIncrement a 1 *
      5 ^ primeIncrement a 2 * 7 ^ primeIncrement a 3 := by
  simp only [multipliers, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Factorization of the slope of an allowed word. -/
theorem prod_factorization (w : List ℕ) (hw : ∀ a ∈ w, a ∈ multipliers) :
    w.prod = 2 ^ exponents w 0 * 3 ^ exponents w 1 *
      5 ^ exponents w 2 * 7 ^ exponents w 3 := by
  induction w with
  | nil => norm_num [exponents]
  | cons a w ih =>
      have ha : a ∈ multipliers := hw a (by simp)
      have hw' : ∀ b ∈ w, b ∈ multipliers := by
        intro b hb
        exact hw b (by simp [hb])
      rw [List.prod_cons, ih hw']
      simp only [exponents_cons]
      nth_rewrite 1 [allowed_factorization ha]
      simp only [pow_add]
      ring

/-- The imbalance vector `H` from the paper. -/
def imbalance (w : List ℕ) : Fin 3 → ℤ :=
  ![(exponents w 0 : ℤ) - 31 * exponents w 3,
    (exponents w 1 : ℤ) - 26 * exponents w 3,
    (exponents w 2 : ℤ) - 11 * exponents w 3]

/-- The common base slope `q = 2^31 3^26 5^11 7`. -/
def q : ℕ := 2 ^ 31 * 3 ^ 26 * 5 ^ 11 * 7

theorem exponents_eq_of_imbalance_eq_zero {w : List ℕ}
    (hH : imbalance w = 0) :
    exponents w 0 = 31 * exponents w 3 ∧
    exponents w 1 = 26 * exponents w 3 ∧
    exponents w 2 = 11 * exponents w 3 := by
  have h0 := congrFun hH (0 : Fin 3)
  have h1 := congrFun hH (1 : Fin 3)
  have h2 := congrFun hH (2 : Fin 3)
  simp [imbalance, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
  omega

/-- Returning to the same imbalance forces slope `q^m`. -/
theorem prod_eq_q_pow_of_imbalance_eq_zero (w : List ℕ)
    (hw : ∀ a ∈ w, a ∈ multipliers) (hH : imbalance w = 0) :
    w.prod = q ^ exponents w 3 := by
  obtain ⟨h2, h3, h5⟩ := exponents_eq_of_imbalance_eq_zero hH
  rw [prod_factorization w hw, h2, h3, h5]
  simp only [q, mul_pow, pow_mul]

/-! ## The finite interval coding -/

/-- The twenty rational endpoints displayed in Section 2 of the paper. -/
def endpoint : Fin 20 → ℚ :=
  ![1 / 9, 10 / 81, 1 / 7, 1 / 5, 2 / 9, 2 / 7, 1 / 3,
    10 / 27, 2 / 5, 11 / 27, 3 / 7, 37 / 81, 5 / 9, 3 / 5,
    2 / 3, 19 / 27, 59 / 81, 4 / 5, 23 / 27, 1]

def leftIndex (i : Fin 19) : Fin 20 := ⟨i, by omega⟩

def rightIndex (i : Fin 19) : Fin 20 := ⟨i + 1, by omega⟩

/-- The half-open state interval `K_i`; Lean uses zero-based indices. -/
def K (i : Fin 19) : Set ℚ := Set.Ico (endpoint (leftIndex i)) (endpoint (rightIndex i))

def width (i : Fin 19) : ℚ := endpoint (rightIndex i) - endpoint (leftIndex i)

theorem endpoint_strictMono : StrictMono endpoint := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;>
    norm_num [endpoint, Matrix.cons_val_two, Matrix.cons_val_three]

theorem width_pos (i : Fin 19) : 0 < width i := by
  exact sub_pos.mpr (endpoint_strictMono (by simp [leftIndex, rightIndex]))

structure Transition where
  source : Fin 19
  multiplier : ℕ
  first : Fin 19
  last : Fin 19

/-- The 23 rows in the interval-transition table. -/
def transitions : List Transition :=
  [⟨0, 14, 12, 15⟩,
   ⟨1, 14, 16, 18⟩, ⟨1, 9, 0, 4⟩,
   ⟨2, 9, 5, 16⟩,
   ⟨3, 9, 17, 18⟩,
   ⟨4, 5, 0, 9⟩,
   ⟨5, 5, 10, 13⟩,
   ⟨6, 5, 14, 17⟩,
   ⟨7, 5, 18, 18⟩, ⟨7, 3, 0, 2⟩,
   ⟨8, 3, 3, 3⟩,
   ⟨9, 3, 4, 4⟩,
   ⟨10, 3, 5, 6⟩,
   ⟨11, 3, 7, 13⟩,
   ⟨12, 3, 14, 16⟩, ⟨12, 2, 0, 2⟩,
   ⟨13, 3, 17, 18⟩, ⟨13, 2, 3, 5⟩,
   ⟨14, 2, 6, 8⟩,
   ⟨15, 2, 9, 10⟩,
   ⟨16, 2, 11, 12⟩,
   ⟨17, 2, 13, 14⟩,
   ⟨18, 2, 15, 18⟩]

def T_rat (a : ℕ) (x : ℚ) : ℚ := a * x - 1

/-- Endpoint form of an exact interval identity.  Positivity of the multiplier
then says that the image of the source interval is exactly the consecutive
block from `first` through `last`. -/
def Transition.Exact (tr : Transition) : Prop :=
  tr.first ≤ tr.last ∧ 0 < tr.multiplier ∧
  T_rat tr.multiplier (endpoint (leftIndex tr.source)) =
    endpoint (leftIndex tr.first) ∧
  T_rat tr.multiplier (endpoint (rightIndex tr.source)) =
    endpoint (rightIndex tr.last)

/-- Machine-checked certificate for every rational interval identity in the
table. -/
theorem transitions_exact : ∀ tr ∈ transitions, tr.Exact := by
  intro tr htr
  simp only [transitions, List.mem_cons, List.not_mem_nil, or_false] at htr
  rcases htr with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [Transition.Exact, T_rat, endpoint, leftIndex, rightIndex,
      Matrix.cons_val_two, Matrix.cons_val_three] ; norm_num

/-- The four choices `α₀,...,α₃`. -/
abbrev Assignment := Fin 4

/-- Multiplier prescribed by an assignment at a state. -/
def prescribed (α : Assignment) (i : Fin 19) : ℕ :=
  if i = 0 then 14
  else if i = 1 then if α = 1 then 9 else 14
  else if i = 2 ∨ i = 3 then 9
  else if i = 4 ∨ i = 5 ∨ i = 6 then 5
  else if i = 7 then if α = 2 then 3 else 5
  else if i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 then 3
  else if i = 12 ∨ i = 13 then if α = 3 then 2 else 3
  else 2

theorem prescribed_mem_multipliers (α : Assignment) (i : Fin 19) :
    prescribed α i ∈ multipliers := by decide +revert

theorem prescribed_ge_two (α : Assignment) (i : Fin 19) : 2 ≤ prescribed α i :=
  mem_multipliers_two_le (prescribed_mem_multipliers α i)

/-- A destination state allowed by the selected row of the table. -/
def allowedNext (α : Assignment) (i j : Fin 19) : Prop :=
  transitions.any (fun tr ↦ decide (tr.source = i ∧
    tr.multiplier = prescribed α i ∧ tr.first ≤ j ∧ j ≤ tr.last)) = true

instance (α : Assignment) (i j : Fin 19) : Decidable (allowedNext α i j) := by
  unfold allowedNext
  infer_instance

/-- Place-dependent transition probability from Section 2. -/
def probability (α : Assignment) (i j : Fin 19) : ℚ :=
  if allowedNext α i j then width j / (prescribed α i * width i) else 0

set_option maxHeartbeats 1000000 in
-- For some reason, adding 19 rational numbers is nontrivial.
private theorem probability_row_sum_zero (i : Fin 19) :
    ∑ j : Fin 19, probability 0 i j = 1 := by
  fin_cases i <;>
    simp [probability, allowedNext, transitions, prescribed, Fin.sum_univ_succ] <;>
    norm_num [width, endpoint, leftIndex, rightIndex,
      Matrix.cons_val_two, Matrix.cons_val_three]

set_option maxHeartbeats 1000000 in
-- For some reason, adding 19 rational numbers is nontrivial.
private theorem probability_row_sum_one (i : Fin 19) :
    ∑ j : Fin 19, probability 1 i j = 1 := by
  fin_cases i <;>
    simp [probability, allowedNext, transitions, prescribed, Fin.sum_univ_succ] <;>
    norm_num [width, endpoint, leftIndex, rightIndex,
      Matrix.cons_val_two, Matrix.cons_val_three]

set_option maxHeartbeats 1000000 in
-- For some reason, adding 19 rational numbers is nontrivial.
private theorem probability_row_sum_two (i : Fin 19) :
    ∑ j : Fin 19, probability 2 i j = 1 := by
  fin_cases i <;>
    simp [probability, allowedNext, transitions, prescribed, Fin.sum_univ_succ] <;>
    norm_num [width, endpoint, leftIndex, rightIndex,
      Matrix.cons_val_two, Matrix.cons_val_three]

set_option maxHeartbeats 1000000 in
-- For some reason, adding 19 rational numbers is nontrivial.
private theorem probability_row_sum_three (i : Fin 19) :
    ∑ j : Fin 19, probability 3 i j = 1 := by
  fin_cases i <;>
    simp [probability, allowedNext, transitions, prescribed, Fin.sum_univ_succ] <;>
    norm_num [width, endpoint, leftIndex, rightIndex,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The transition probabilities in every row sum to one. -/
theorem probability_row_sum (α : Assignment) (i : Fin 19) :
    ∑ j : Fin 19, probability α i j = 1 := by
  fin_cases α
  · exact probability_row_sum_zero i
  · exact probability_row_sum_one i
  · exact probability_row_sum_two i
  · exact probability_row_sum_three i

/-! ## Stationary distributions and drift data -/

/-- Increment of the imbalance vector caused by one multiplier. -/
def imbalanceIncrement (a : ℕ) : Fin 3 → ℚ :=
  ![(primeIncrement a 0 : ℚ) - 31 * primeIncrement a 3,
    (primeIncrement a 1 : ℚ) - 26 * primeIncrement a 3,
    (primeIncrement a 2 : ℚ) - 11 * primeIncrement a 3]

/-- The four stationary mean increments printed in the paper. -/
def listedDrift (α : Assignment) : Fin 3 → ℚ :=
  match α with
  | 0 => ![82502/209179, 60472/209179, 22315/209179]
  | 1 => ![4122816/9240032, 3176276/9240032, 1187745/9240032]
  | 2 => ![-17374/154297, 2952/154297, -12847/154297]
  | 3 => ![-410774/938829, -384064/938829, -82315/938829]

/-- Positive barycentric coordinates witnessing that zero lies strictly
inside the tetrahedron of drift vectors. -/
def baryWeight : Fin 4 → ℚ :=
  ![90039171528246091/965033798855459200,
    48712935304722/153863807215475,
    114688358060991/465076529568896,
    118388840756943/344654928162664]

theorem baryWeight_pos (α : Assignment) : 0 < baryWeight α := by
  fin_cases α <;> norm_num [baryWeight]

/-- Exact positive barycentric relation among the four drift vectors. -/
theorem weighted_drift_sum (k : Fin 3) :
    ∑ α : Assignment, baryWeight α * listedDrift α k = 0 := by
  fin_cases k <;>
    norm_num [baryWeight, listedDrift, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    simp <;> norm_num

/-- Number of generated positive integers at most `x`. -/
noncomputable def countUpTo (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter Generated).card

/-- The exact conclusion called "positive lower density" in the paper. -/
def HasPositiveLowerDensity : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
    c * (x : ℝ) ≤ (countUpTo x : ℝ)

/-! ## From common-slope affine words to density -/

theorem prod_pos_of_one_le (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) : 0 < w.prod := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have ha : 1 ≤ a := hw a (by simp)
      have htail : ∀ b ∈ w, 1 ≤ b := by
        intro b hb
        exact hw b (by simp [hb])
      simp only [List.prod_cons]
      exact Nat.mul_pos (by omega) (ih htail)

theorem eval_le_prod_mul (w : List ℕ) {x : ℕ} (hw : ∀ a ∈ w, 1 ≤ a) :
    eval w x ≤ w.prod * x := by
  induction w generalizing x with
  | nil =>
      simp only [eval, List.prod_nil, one_mul]
      exact le_rfl
  | cons a w ih =>
      have htail : ∀ b ∈ w, 1 ≤ b := by
        intro b hb
        exact hw b (by simp [hb])
      calc
        eval (a :: w) x = eval w (T a x) := rfl
        _ ≤ w.prod * T a x := ih htail
        _ ≤ w.prod * (a * x) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = (a :: w).prod * x := by simp [mul_assoc, mul_left_comm]

theorem countUpTo_mono : Monotone countUpTo := by
  intro x y hxy
  classical
  simp only [countUpTo]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hxy⟩, hn.2⟩

theorem card_le_countUpTo {S : Finset ℕ} {x : ℕ}
    (hS : ∀ n ∈ S, Generated n ∧ n ≤ x) : S.card ≤ countUpTo x := by
  classical
  simp only [countUpTo]
  apply Finset.card_le_card
  intro n hn
  have h := hS n hn
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Generated.pos h.1, h.2⟩, h.1⟩

/-! ## Filling the gaps between geometric scales -/

/-- A lower bound by a fixed proportion at all sufficiently large geometric
scales implies the paper's positive-lower-density conclusion. -/
theorem positiveLowerDensity_of_geometric_count {base denominator : ℕ}
    (hbase : 1 < base) (hdenominator : 0 < denominator)
    (hgeom : ∃ r₀ : ℕ, ∀ r ≥ r₀,
      base ^ r ≤ denominator * countUpTo (17 * base ^ r)) :
    HasPositiveLowerDensity := by
  obtain ⟨r₀, hgeom⟩ := hgeom
  let c : ℝ := 1 / (17 * base * denominator : ℕ)
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (17 * base ^ r₀)] with x hx
    let y := x / 17
    let r := Nat.log base y
    have hyPow : base ^ r₀ ≤ y := by
      dsimp [y]
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 17)).2
      simpa [mul_comm] using hx
    have hy : y ≠ 0 := by
      intro hy0
      rw [hy0] at hyPow
      exact (Nat.not_succ_le_zero _)
        ((Nat.pow_pos (Nat.zero_lt_one.trans hbase)).trans_le hyPow)
    have hr : r₀ ≤ r := by
      exact Nat.le_log_of_pow_le hbase hyPow
    have hscale : 17 * base ^ r ≤ x := by
      have hp := Nat.pow_log_le_self base hy
      have hmul : 17 * base ^ r ≤ 17 * y := Nat.mul_le_mul_left 17 hp
      exact hmul.trans (Nat.mul_div_le x 17)
    have hnext : y < base ^ (r + 1) := by
      simpa [r, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hbase y
    have hxnext : x < 17 * base ^ (r + 1) := by
      calc
        x < 17 * (x / 17 + 1) := Nat.lt_mul_div_succ x (by norm_num)
        _ = 17 * (y + 1) := by rfl
        _ ≤ 17 * base ^ (r + 1) := Nat.mul_le_mul_left 17 hnext
    have hcountMono : countUpTo (17 * base ^ r) ≤ countUpTo x :=
      countUpTo_mono hscale
    have hgeomr := hgeom r hr
    have hpowCount : base ^ r ≤ denominator * countUpTo x :=
      hgeomr.trans (Nat.mul_le_mul_left denominator hcountMono)
    have hxCount : x ≤ 17 * base * (denominator * countUpTo x) := by
      calc
        x ≤ 17 * base ^ (r + 1) := hxnext.le
        _ = 17 * base * base ^ r := by rw [pow_succ]; ring
        _ ≤ 17 * base * (denominator * countUpTo x) :=
          Nat.mul_le_mul_left (17 * base) hpowCount
    have hxCount' : x ≤ (17 * base * denominator) * countUpTo x := by
      calc
        x ≤ 17 * base * (denominator * countUpTo x) := hxCount
        _ = (17 * base * denominator) * countUpTo x := by ring
    have hxCountReal : (x : ℝ) ≤
        (17 * base * denominator : ℕ) * (countUpTo x : ℝ) := by
      exact_mod_cast hxCount'
    dsimp [c]
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ ?_).2
    · simpa [mul_assoc, mul_comm, mul_left_comm] using hxCountReal
    · positivity

/-! ## Typed interval paths and the telescoping identity -/

/-- A path through the interval graph.  The endpoints are type indices, so
composability is enforced by Lean.  Each step stores the assignment used and
proof that its transition is allowed. -/
inductive IntervalPath : Fin 19 → Fin 19 → Type where
  | nil (i : Fin 19) : IntervalPath i i
  | cons {i j k : Fin 19} (α : Assignment) (h : allowedNext α i j)
      (tail : IntervalPath j k) : IntervalPath i k

namespace IntervalPath

def word {i j : Fin 19} : IntervalPath i j → List ℕ
  | .nil _ => []
  | .cons α _ tail => prescribed α i :: tail.word

def mass {i j : Fin 19} : IntervalPath i j → ℚ
  | .nil _ => 1
  | @IntervalPath.cons i j _ α _ tail => probability α i j * tail.mass

@[simp] theorem word_cons {i j k : Fin 19} (α : Assignment)
    (h : allowedNext α i j) (tail : IntervalPath j k) :
    (IntervalPath.cons α h tail).word = prescribed α i :: tail.word := rfl

@[simp] theorem mass_cons {i j k : Fin 19} (α : Assignment)
    (h : allowedNext α i j) (tail : IntervalPath j k) :
    (IntervalPath.cons α h tail).mass = probability α i j * tail.mass := rfl

theorem probability_of_allowed {α : Assignment} {i j : Fin 19}
    (h : allowedNext α i j) :
    probability α i j = width j / (prescribed α i * width i) := by
  simp [probability, h]

theorem word_mem_multipliers {i j : Fin 19} (p : IntervalPath i j) :
    ∀ a ∈ p.word, a ∈ multipliers := by
  induction p with
  | nil =>
      intro a ha
      simp only [word, List.not_mem_nil] at ha
  | @cons i j k α h tail ih =>
      intro a ha
      simp only [word_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact prescribed_mem_multipliers α i
      · exact ih a ha

theorem word_two_le {i j : Fin 19} (p : IntervalPath i j) :
    ∀ a ∈ p.word, 2 ≤ a := by
  intro a ha
  exact mem_multipliers_two_le (p.word_mem_multipliers a ha)

/-- Equation (1): transition probabilities telescope to the ratio of endpoint
interval lengths divided by the affine slope.  The assignments may vary from
step to step. -/
theorem mass_eq_width_div {i j : Fin 19} (p : IntervalPath i j) :
    p.mass = width j / ((p.word.prod : ℚ) * width i) := by
  induction p with
  | nil i =>
      simp only [mass, word, List.prod_nil, Nat.cast_one, one_mul]
      field_simp [ne_of_gt (width_pos i)]
  | @cons i j k α h tail ih =>
      rw [mass_cons, probability_of_allowed h, ih, word_cons, List.prod_cons,
        Nat.cast_mul]
      have hi : width i ≠ 0 := ne_of_gt (width_pos i)
      have hj : width j ≠ 0 := ne_of_gt (width_pos j)
      have ha : (prescribed α i : ℚ) ≠ 0 := by
        exact_mod_cast (show prescribed α i ≠ 0 by
          have := prescribed_ge_two α i
          omega)
      have hp : (tail.word.prod : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (prod_pos_of_one_le tail.word
          (fun a ha ↦ (tail.word_two_le a ha).trans' (by omega))))
      field_simp

end IntervalPath

/-! ## Finite-chain certificates -/

theorem probability_nonneg (α : Assignment) (i j : Fin 19) :
  0 ≤ probability α i j := by
  by_cases h : allowedNext α i j
  · rw [IntervalPath.probability_of_allowed h]
    have ha : (0 : ℚ) ≤ prescribed α i := by positivity
    exact div_nonneg (width_pos j).le (mul_nonneg ha (width_pos i).le)
  · simp [probability, h]

/-! ## The drift tetrahedron -/

def listedDriftReal (α : Assignment) (k : Fin 3) : ℝ := listedDrift α k

def driftDot (v : Fin 3 → ℝ) (α : Assignment) : ℝ :=
  ∑ k : Fin 3, v k * listedDriftReal α k

theorem weighted_drift_real (k : Fin 3) :
    ∑ α : Assignment, (baryWeight α : ℝ) * listedDriftReal α k = 0 := by
  simpa [listedDriftReal] using
    congrArg (fun x : ℚ ↦ (x : ℝ)) (weighted_drift_sum k)

theorem weighted_driftDot (v : Fin 3 → ℝ) :
    ∑ α : Assignment, (baryWeight α : ℝ) * driftDot v α = 0 := by
  calc
    ∑ α : Assignment, (baryWeight α : ℝ) * driftDot v α =
        ∑ k : Fin 3, v k *
          (∑ α : Assignment, (baryWeight α : ℝ) * listedDriftReal α k) := by
      simp only [driftDot, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro α _
      ring
    _ = 0 := by simp [weighted_drift_real]

/-- The first three drift vectors span `ℝ³`. -/
theorem eq_zero_of_first_three_driftDot_eq_zero {v : Fin 3 → ℝ}
    (h0 : driftDot v 0 = 0) (h1 : driftDot v 1 = 0)
    (h2 : driftDot v 2 = 0) : v = 0 := by
  norm_num [driftDot, listedDriftReal, listedDrift, Fin.sum_univ_succ] at h0 h1 h2
  funext k
  fin_cases k
  · change v 0 = 0
    linear_combination
      (2317276647762287 / 49432245464000 : ℝ) * h0 -
      (620783464892 / 15762833375 : ℝ) * h1 -
      (1460755466599 / 1977289818560 : ℝ) * h2
  · change v 1 = 0
    linear_combination
      -(3381371791278219 / 98864490928000 : ℝ) * h0 +
      (495150792302 / 15762833375 : ℝ) * h1 +
      (18486937517763 / 3954579637120 : ℝ) * h2
  · change v 2 = 0
    linear_combination
      -(1761160941937753 / 24716122732000 : ℝ) * h0 +
      (953310271496 / 15762833375 : ℝ) * h1 -
      (9824239195199 / 988644909280 : ℝ) * h2

/-- Pointwise form of the statement that zero is in the interior of the drift
tetrahedron: every nonzero direction has strictly negative dot product with at
least one drift. -/
theorem exists_driftDot_neg {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    ∃ α : Assignment, driftDot v α < 0 := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hterm : ∀ α ∈ (Finset.univ : Finset Assignment),
      0 ≤ (baryWeight α : ℝ) * driftDot v α := by
    intro α _
    exact mul_nonneg (by exact_mod_cast (baryWeight_pos α).le) (h α)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 (weighted_driftDot v)
  have hdot (α : Assignment) : driftDot v α = 0 := by
    have hz := hzero α (Finset.mem_univ α)
    exact (mul_eq_zero.mp hz).resolve_left (by
      exact_mod_cast (baryWeight_pos α).ne')
  exact hv (eq_zero_of_first_three_driftDot_eq_zero (hdot 0) (hdot 1) (hdot 2))

/-- Minimum of the four drift dot products. -/
def minDriftDot (v : Fin 3 → ℝ) : ℝ :=
  min (driftDot v 0) (min (driftDot v 1) (min (driftDot v 2) (driftDot v 3)))

theorem minDriftDot_le (v : Fin 3 → ℝ) (α : Assignment) :
    minDriftDot v ≤ driftDot v α := by
  fin_cases α <;> simp [minDriftDot]

theorem minDriftDot_neg {v : Fin 3 → ℝ} (hv : v ≠ 0) : minDriftDot v < 0 := by
  obtain ⟨α, hα⟩ := exists_driftDot_neg hv
  exact (minDriftDot_le v α).trans_lt hα

theorem continuous_driftDot (α : Assignment) :
    Continuous (fun v : Fin 3 → ℝ ↦ driftDot v α) := by
  apply continuous_finset_sum
  intro k _
  exact (continuous_apply k).mul continuous_const

theorem continuous_minDriftDot : Continuous minDriftDot := by
  exact (continuous_driftDot 0).min ((continuous_driftDot 1).min
    ((continuous_driftDot 2).min (continuous_driftDot 3)))

/-- Quantitative drift consequence used in Lemma 2.  Compactness of the unit
sphere upgrades pointwise negativity to a uniform negative constant. -/
theorem exists_uniform_negative_drift :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Fin 3 → ℝ, ‖v‖ = 1 → minDriftDot v ≤ -δ := by
  let e : Fin 3 → ℝ := Pi.single 0 1
  have heNorm : ‖e‖ = 1 := by simp [e, Pi.norm_single]
  have hSphere : (Metric.sphere (0 : Fin 3 → ℝ) 1).Nonempty := by
    refine ⟨e, ?_⟩
    simpa [Metric.mem_sphere, dist_zero_left] using heNorm
  obtain ⟨v, hvSphere, hvMax⟩ :=
    (isCompact_sphere (0 : Fin 3 → ℝ) 1).exists_isMaxOn hSphere
      continuous_minDriftDot.continuousOn
  have hvNorm : ‖v‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_left] using hvSphere
  have hvNe : v ≠ 0 := by
    intro hv
    rw [hv, norm_zero] at hvNorm
    norm_num at hvNorm
  have hvNeg : minDriftDot v < 0 := minDriftDot_neg hvNe
  refine ⟨-minDriftDot v, neg_pos.mpr hvNeg, ?_⟩
  intro u huNorm
  have huSphere : u ∈ Metric.sphere (0 : Fin 3 → ℝ) 1 := by
    simpa [Metric.mem_sphere, dist_zero_left] using huNorm
  simpa using hvMax huSphere
/-! ## Exact finite Poisson equations

The paper uses the Poisson equation for each of its four finite Markov
chains.  The following rational vectors are exact certificates for those
equations, normalized to vanish at state 18.
-/

/-- A rational solution of the vector-valued Poisson equation for each
stationary assignment. -/
def poissonSolution (α : Assignment) : Fin 19 → Fin 3 → ℚ :=
  match α with
  | 0 =>
      ![![-92474603/2928506, -754100497/29285060, -157916873/14642530],
        ![-141489037/4601938, -1193514713/46019380, -1016602093/92038760],
        ![-1344010/627537, 18690823/7530444, 11052155/30121776],
        ![-134965/418358, 366968/209179, -223305/3346864],
        ![-5089025/836716, -4703447/1673432, 1128693/3346864],
        ![-847919/418358, 413833/418358, 3811471/3346864],
        ![-598777/418358, 164803/1045895, 20651439/16734320],
        ![-82502/209179, -60472/209179, 186864/209179],
        ![-299969/418358, 515675/209179, -580345/3346864],
        ![-5419033/836716, -3513791/1673432, 771653/3346864],
        ![-7231387/3346864, 44722847/33468640, 71878267/66937280],
        ![-1862623/836716, 3390443/2091790, 6428039/33468640],
        ![-812525/418358, 529703/418358, 1026335/3346864],
        ![-134965/418358, 157789/209179, -223305/3346864],
        ![-142033/418358, -16613/209179, 2845999/3346864],
        ![-1424395/418358, -1779727/4183580, 5068333/8367160],
        ![-18591689/12132382, 14821723/12132382, 11738933/97059056],
        ![811053/2928506, 245214/1464253, 515835/3346864],
        ![0, 0, 0]]
  | 1 =>
      ![![-18218137/577502, -59408041/2310008, -99531215/9240032],
        ![-244093727/44467654, 128903569/177870616, -271195465/711482464],
        ![-37590230/18191313, 745570207/291061008, 464215267/1164244032],
        ![-236545/577502, 1920191/1155004, -238977/2310008],
        ![-32776595/8085028, -43322975/64680224, 308810745/258720896],
        ![-8281797/4042514, 7810709/8085028, 4566315/4042514],
        ![-817701/577502, 401365/2310008, 11462711/9240032],
        ![-128838/288751, -794069/2310008, 8052287/9240032],
        ![-494221/577502, 5356321/2310008, -2143653/9240032],
        ![-36384059/8085028, -876683/64680224, 275553885/258720896],
        ![-71731617/32340112, 330044815/258720896, 1086194759/1034883584],
        ![-2450175/1155004, 31996559/18480064, 17466859/73920256],
        ![-1067185/577502, 6309223/4620016, 6402399/18480064],
        ![-236545/577502, 765187/1155004, -238977/2310008],
        ![-241517/577502, -187691/1155004, 471885/577502],
        ![-1525927/577502, 1752829/4620016, 17143453/18480064],
        ![-24831461/16747558, 21338725/16747558, 19016669/133980464],
        ![570537/4042514, 389745/16170056, 6259599/64680224],
        ![0, 0, 0]]
  | 2 =>
      ![![-70369625/2160158, -113547139/4320316, -6887181/617188],
        ![-104473735/3394534, -176188709/6789068, -75067917/6789068],
        ![-1645928/462891, 1333993/771485, -753691/4628910],
        ![-45427/308594, 5701947/3085940, -3119/3085940],
        ![-4738835/617188, -4518359/1234376, -321747/1234376],
        ![-768017/308594, 458693/617188, 596047/617188],
        ![-863695/308594, -352161/617188, 445457/617188],
        ![-2069882/154297, -5571617/771485, -12296049/3085940],
        ![-10679/308594, 8728847/3085940, 253821/3085940],
        ![-4669339/617188, -3307599/1234376, -218971/1234376],
        ![-6201025/2468752, 5674595/4937504, 4652415/4937504],
        ![-2382673/617188, 926495/1234376, -518733/1234376],
        ![-1092827/308594, 1279677/3085940, -902409/3085940],
        ![-45427/308594, 2616007/3085940, -3119/3085940],
        ![-1745479/308594, -1796229/617188, -704491/617188],
        ![-1100161/308594, -315251/617188, 336781/617188],
        ![-23705255/8949226, 56129683/89492260, -26607071/89492260],
        ![-2164725/2160158, -1584873/3085940, -7021593/21601580],
        ![0, 0, 0]]
  | 3 =>
      ![![-1115788487/32859015, -182354567/6571803, -372698614/32859015],
        ![-6383806027/206542380, -2153946893/82616952, -4578452623/413084760],
        ![-228316579/67595688, 190330739/135191376, 390245/135191376],
        ![1045843/2503544, 12388597/5007088, 1537835/5007088],
        ![-14159963/2503544, -12265589/5007088, 2221421/5007088],
        ![-34533503/7510632, -17583545/15021264, 8022361/15021264],
        ![-63544399/37553160, -888629/15021264, 88445129/75106320],
        ![410774/938829, 384064/938829, 1021144/938829],
        ![6423721/7510632, 58332079/15021264, 5930545/15021264],
        ![-39193697/7510632, -15630479/15021264, 7981303/15021264],
        ![-433980767/150212640, 43547075/60085056, 271371337/300425280],
        ![-294149719/75106320, 6110059/30042528, -30132271/150212640],
        ![-30532829/2503544, -41208115/5007088, -19551805/5007088],
        ![-21242167/7510632, -11462785/15021264, 8124545/15021264],
        ![6399233/7510632, 13991927/15021264, 17289929/15021264],
        ![-15333271/6258860, 944543/2503544, 10409221/12517720],
        ![-366525975/72602776, -291104273/145205552, -183323039/145205552],
        ![-1337967/17524808, 8804151/35049616, 29668185/35049616],
        ![0, 0, 0]]

/-- The transition operator applied to one coordinate of a function on the
nineteen interval states. -/
def expectedNext (α : Assignment) (g : Fin 19 → ℚ) (i : Fin 19) : ℚ :=
  ∑ j : Fin 19, probability α i j * g j

set_option maxHeartbeats 2000000 in
-- This expands 57 entries of the first exact rational Poisson certificate.
private theorem poisson_equation_zero (i : Fin 19) (k : Fin 3) :
    poissonSolution 0 i k - expectedNext 0 (fun j ↦ poissonSolution 0 j k) i =
      imbalanceIncrement (prescribed 0 i) k - listedDrift 0 k := by
  fin_cases i <;> fin_cases k <;>
    simp [poissonSolution, expectedNext, probability, allowedNext, transitions,
      prescribed, width, endpoint, leftIndex, rightIndex, imbalanceIncrement,
      primeIncrement, listedDrift, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    norm_num

set_option maxHeartbeats 2000000 in
-- This expands 57 entries of the second exact rational Poisson certificate.
private theorem poisson_equation_one (i : Fin 19) (k : Fin 3) :
    poissonSolution 1 i k - expectedNext 1 (fun j ↦ poissonSolution 1 j k) i =
      imbalanceIncrement (prescribed 1 i) k - listedDrift 1 k := by
  fin_cases i <;> fin_cases k <;>
    simp [poissonSolution, expectedNext, probability, allowedNext, transitions,
      prescribed, width, endpoint, leftIndex, rightIndex, imbalanceIncrement,
      primeIncrement, listedDrift, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    norm_num

set_option maxHeartbeats 2000000 in
-- This expands 57 entries of the third exact rational Poisson certificate.
private theorem poisson_equation_two (i : Fin 19) (k : Fin 3) :
    poissonSolution 2 i k - expectedNext 2 (fun j ↦ poissonSolution 2 j k) i =
      imbalanceIncrement (prescribed 2 i) k - listedDrift 2 k := by
  fin_cases i <;> fin_cases k <;>
    simp [poissonSolution, expectedNext, probability, allowedNext, transitions,
      prescribed, width, endpoint, leftIndex, rightIndex, imbalanceIncrement,
      primeIncrement, listedDrift, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    norm_num

set_option maxHeartbeats 2000000 in
-- This expands 57 entries of the fourth exact rational Poisson certificate.
private theorem poisson_equation_three (i : Fin 19) (k : Fin 3) :
    poissonSolution 3 i k - expectedNext 3 (fun j ↦ poissonSolution 3 j k) i =
      imbalanceIncrement (prescribed 3 i) k - listedDrift 3 k := by
  fin_cases i <;> fin_cases k <;>
    simp [poissonSolution, expectedNext, probability, allowedNext, transitions,
      prescribed, width, endpoint, leftIndex, rightIndex, imbalanceIncrement,
      primeIncrement, listedDrift, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    norm_num

/-- Exact verification of `g - P g = h - β` for all four assignments,
nineteen states, and three imbalance coordinates. -/
theorem poisson_equation (α : Assignment) (i : Fin 19) (k : Fin 3) :
    poissonSolution α i k - expectedNext α (fun j ↦ poissonSolution α j k) i =
      imbalanceIncrement (prescribed α i) k - listedDrift α k := by
  fin_cases α
  · exact poisson_equation_zero i k
  · exact poisson_equation_one i k
  · exact poisson_equation_two i k
  · exact poisson_equation_three i k
/-! ## Finite blocks with a fixed assignment -/

/-- Iteration of the transition operator belonging to one assignment. -/
def iterateExpected (α : Assignment) : ℕ → (Fin 19 → ℚ) → Fin 19 → ℚ
  | 0, f => f
  | n + 1, f => fun i ↦ expectedNext α (iterateExpected α n f) i

/-- Expected accumulated imbalance in one coordinate during `n` steps with
the assignment held fixed. -/
def expectedAccum (α : Assignment) : ℕ → Fin 19 → Fin 3 → ℚ
  | 0, _, _ => 0
  | n + 1, i, k =>
      imbalanceIncrement (prescribed α i) k +
        expectedNext α (fun j ↦ expectedAccum α n j k) i

@[simp] theorem iterateExpected_succ (α : Assignment) (n : ℕ)
    (f : Fin 19 → ℚ) (i : Fin 19) :
    iterateExpected α (n + 1) f i =
      expectedNext α (iterateExpected α n f) i := rfl

@[simp] theorem expectedAccum_succ (α : Assignment) (n : ℕ)
    (i : Fin 19) (k : Fin 3) :
    expectedAccum α (n + 1) i k =
      imbalanceIncrement (prescribed α i) k +
        expectedNext α (fun j ↦ expectedAccum α n j k) i := rfl

theorem expectedNext_const (α : Assignment) (c : ℚ) (i : Fin 19) :
    expectedNext α (fun _ ↦ c) i = c := by
  simp only [expectedNext, ← Finset.sum_mul, probability_row_sum, one_mul]

theorem expectedNext_add (α : Assignment) (f g : Fin 19 → ℚ) (i : Fin 19) :
    expectedNext α (fun j ↦ f j + g j) i =
      expectedNext α f i + expectedNext α g i := by
  simp only [expectedNext, mul_add, Finset.sum_add_distrib]

theorem expectedNext_sub (α : Assignment) (f g : Fin 19 → ℚ) (i : Fin 19) :
    expectedNext α (fun j ↦ f j - g j) i =
      expectedNext α f i - expectedNext α g i := by
  simp only [expectedNext, mul_sub, Finset.sum_sub_distrib]

/-- The finite Poisson certificate telescopes over an arbitrary block. -/
theorem expectedAccum_eq_poisson (α : Assignment) (n : ℕ)
    (i : Fin 19) (k : Fin 3) :
    expectedAccum α n i k =
      (n : ℚ) * listedDrift α k + poissonSolution α i k -
        iterateExpected α n (fun j ↦ poissonSolution α j k) i := by
  induction n generalizing i with
  | zero => simp [expectedAccum, iterateExpected]
  | succ n ih =>
      rw [expectedAccum_succ]
      simp_rw [ih]
      rw [expectedNext_sub, expectedNext_add]
      simp only [expectedNext_const]
      rw [iterateExpected_succ]
      have hp := poisson_equation α i k
      dsimp [expectedNext] at hp ⊢
      norm_num only [Nat.cast_add, Nat.cast_one]
      linear_combination -hp

set_option maxHeartbeats 800000 in
-- This checks all 228 entries of the four exact rational Poisson tables.
/-- Every entry of every exact Poisson solution is bounded by 40. -/
theorem poissonSolution_abs_le (α : Assignment) (i : Fin 19) (k : Fin 3) :
    |poissonSolution α i k| ≤ 40 := by
  fin_cases α <;> fin_cases i <;> fin_cases k <;>
    simp [poissonSolution, Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num

theorem expectedNext_mono (α : Assignment) {f g : Fin 19 → ℚ}
    (hfg : ∀ j, f j ≤ g j) (i : Fin 19) :
    expectedNext α f i ≤ expectedNext α g i := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hfg j) (probability_nonneg α i j)

theorem iterateExpected_bounds (α : Assignment) (n : ℕ)
    {f : Fin 19 → ℚ} {B : ℚ} (hf : ∀ i, -B ≤ f i ∧ f i ≤ B)
    (i : Fin 19) :
    -B ≤ iterateExpected α n f i ∧ iterateExpected α n f i ≤ B := by
  induction n generalizing i with
  | zero => exact hf i
  | succ n ih =>
      rw [iterateExpected_succ]
      constructor
      · rw [← expectedNext_const α (-B) i]
        exact expectedNext_mono α (fun j ↦ (ih j).1) i
      · rw [← expectedNext_const α B i]
        exact expectedNext_mono α (fun j ↦ (ih j).2) i

/-- The expected block increment differs from `n` times the stationary drift
by at most 80 in every coordinate, uniformly in the initial interval. -/
theorem expectedAccum_error_abs_le (α : Assignment) (n : ℕ)
    (i : Fin 19) (k : Fin 3) :
    |expectedAccum α n i k - (n : ℚ) * listedDrift α k| ≤ 80 := by
  rw [expectedAccum_eq_poisson]
  ring_nf
  have hi := poissonSolution_abs_le α i k
  have hi' := abs_le.mp hi
  have hj := iterateExpected_bounds α n
    (B := (40 : ℚ)) (f := fun j ↦ poissonSolution α j k)
    (fun j ↦ (abs_le.mp (poissonSolution_abs_le α j k))) i
  rw [abs_le]
  constructor <;> linarith

/-! ### Enumerating finite blocks -/

/-- The integer imbalance increment of one multiplier. -/
def imbalanceIncrementInt (a : ℕ) : Fin 3 → ℤ :=
  ![(primeIncrement a 0 : ℤ) - 31 * primeIncrement a 3,
    (primeIncrement a 1 : ℤ) - 26 * primeIncrement a 3,
    (primeIncrement a 2 : ℤ) - 11 * primeIncrement a 3]

theorem imbalanceIncrementInt_cast (a : ℕ) (k : Fin 3) :
    (imbalanceIncrementInt a k : ℚ) = imbalanceIncrement a k := by
  fin_cases k <;> simp [imbalanceIncrementInt, imbalanceIncrement]

/-- Endpoint of a tuple of successive interval choices. -/
def blockEndpoint : (n : ℕ) → Fin 19 → (Fin n → Fin 19) → Fin 19
  | 0, i, _ => i
  | n + 1, _, w => blockEndpoint n (w 0) (Fin.tail w)

/-- Probability of a tuple of successive interval choices under a fixed
assignment.  Tuples containing a forbidden transition have weight zero. -/
def blockWeight (α : Assignment) :
    (n : ℕ) → Fin 19 → (Fin n → Fin 19) → ℚ
  | 0, _, _ => 1
  | n + 1, i, w =>
      probability α i (w 0) * blockWeight α n (w 0) (Fin.tail w)

/-- Net integer imbalance accumulated along a finite block. -/
def blockIncrement (α : Assignment) :
    (n : ℕ) → Fin 19 → (Fin n → Fin 19) → Fin 3 → ℤ
  | 0, _, _, _ => 0
  | n + 1, i, w, k =>
      imbalanceIncrementInt (prescribed α i) k +
        blockIncrement α n (w 0) (Fin.tail w) k

/-- Multiplier word read along a finite block. -/
def blockWord (α : Assignment) :
    (n : ℕ) → Fin 19 → (Fin n → Fin 19) → List ℕ
  | 0, _, _ => []
  | n + 1, i, w =>
      prescribed α i :: blockWord α n (w 0) (Fin.tail w)

@[simp] theorem blockWeight_cons (α : Assignment) (n : ℕ) (i j : Fin 19)
    (w : Fin n → Fin 19) :
    blockWeight α (n + 1) i (Fin.cons j w) =
      probability α i j * blockWeight α n j w := by
  simp [blockWeight]

@[simp] theorem blockIncrement_cons (α : Assignment) (n : ℕ) (i j : Fin 19)
    (w : Fin n → Fin 19) (k : Fin 3) :
    blockIncrement α (n + 1) i (Fin.cons j w) k =
      imbalanceIncrementInt (prescribed α i) k + blockIncrement α n j w k := by
  simp [blockIncrement]

@[simp] theorem blockWord_cons (α : Assignment) (n : ℕ) (i j : Fin 19)
    (w : Fin n → Fin 19) :
    blockWord α (n + 1) i (Fin.cons j w) =
      prescribed α i :: blockWord α n j w := by
  simp [blockWord]

theorem sum_tuple_succ {A R : Type*} [Fintype A]
    [AddCommMonoid R] (n : ℕ) (F : (Fin (n + 1) → A) → R) :
    ∑ w, F w = ∑ a : A, ∑ u : Fin n → A, F (Fin.cons a u) := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ A)
  calc
    ∑ w, F w = ∑ z : A × (Fin n → A), F (e z) := (Equiv.sum_comp e F).symm
    _ = ∑ a : A, ∑ u : Fin n → A, F (Fin.cons a u) := by
      rw [Fintype.sum_prod_type]
      rfl

/-- Block-path probabilities sum to one. -/
theorem blockWeight_sum (α : Assignment) (n : ℕ) (i : Fin 19) :
    ∑ w : Fin n → Fin 19, blockWeight α n i w = 1 := by
  induction n generalizing i with
  | zero => simp [blockWeight]
  | succ n ih =>
      rw [sum_tuple_succ]
      simp_rw [blockWeight_cons, ← Finset.mul_sum, ih, mul_one]
      exact probability_row_sum α i

theorem blockWeight_nonneg (α : Assignment) (n : ℕ) (i : Fin 19)
    (w : Fin n → Fin 19) : 0 ≤ blockWeight α n i w := by
  induction n generalizing i with
  | zero => simp [blockWeight]
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from (Fin.cons_self_tail w).symm,
        blockWeight_cons]
      exact mul_nonneg (probability_nonneg α i (w 0)) (ih (w 0) (Fin.tail w))

/-- The path enumeration realizes `expectedAccum`. -/
theorem sum_blockWeight_mul_increment (α : Assignment) (n : ℕ)
    (i : Fin 19) (k : Fin 3) :
    ∑ w : Fin n → Fin 19,
        blockWeight α n i w * (blockIncrement α n i w k : ℚ) =
      expectedAccum α n i k := by
  induction n generalizing i with
  | zero => simp [blockWeight, blockIncrement, expectedAccum]
  | succ n ih =>
      rw [sum_tuple_succ, expectedAccum_succ]
      simp_rw [blockWeight_cons, blockIncrement_cons, Int.cast_add,
        imbalanceIncrementInt_cast, mul_add, Finset.sum_add_distrib]
      have hfirst :
          (∑ j : Fin 19, ∑ w : Fin n → Fin 19,
            probability α i j * blockWeight α n j w *
              imbalanceIncrement (prescribed α i) k) =
            imbalanceIncrement (prescribed α i) k := by
        calc
          _ = ∑ j : Fin 19, probability α i j *
                (∑ w : Fin n → Fin 19, blockWeight α n j w *
                  imbalanceIncrement (prescribed α i) k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              simp only [mul_assoc]
          _ = ∑ j : Fin 19, probability α i j *
                ((∑ w : Fin n → Fin 19, blockWeight α n j w) *
                  imbalanceIncrement (prescribed α i) k) := by
              simp_rw [Finset.sum_mul]
          _ = ∑ j : Fin 19, probability α i j *
                imbalanceIncrement (prescribed α i) k := by
              simp_rw [blockWeight_sum, one_mul]
          _ = imbalanceIncrement (prescribed α i) k := by
              rw [← Finset.sum_mul, probability_row_sum, one_mul]
      have hsecond :
          (∑ j : Fin 19, ∑ w : Fin n → Fin 19,
            probability α i j * blockWeight α n j w *
              (blockIncrement α n j w k : ℚ)) =
            ∑ j : Fin 19, probability α i j * expectedAccum α n j k := by
        apply Finset.sum_congr rfl
        intro j _
        calc
          _ = probability α i j *
              (∑ w : Fin n → Fin 19,
                blockWeight α n j w * (blockIncrement α n j w k : ℚ)) := by
                rw [Finset.mul_sum]
                simp only [mul_assoc]
          _ = probability α i j * expectedAccum α n j k := by rw [ih]
      rw [hfirst, hsecond]
      rfl

theorem blockIncrement_eq_imbalance (α : Assignment) (n : ℕ)
    (i : Fin 19) (w : Fin n → Fin 19) :
    blockIncrement α n i w = imbalance (blockWord α n i w) := by
  induction n generalizing i with
  | zero =>
      funext k
      fin_cases k <;> simp [blockIncrement, imbalance, exponents]
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from (Fin.cons_self_tail w).symm]
      funext k
      rw [blockIncrement_cons, blockWord_cons, ih]
      fin_cases k <;>
        simp [imbalanceIncrementInt, imbalance, exponents_cons] <;> ring
/-! ## Deterministic drift feedback -/

/-- The integer imbalance vector viewed in `ℝ³`. -/
def imbalanceReal (h : Fin 3 → ℤ) : Fin 3 → ℝ := fun k ↦ h k

/-- Squared Euclidean length, used as the Lyapunov function. -/
def squareLength (h : Fin 3 → ℤ) : ℝ :=
  ∑ k : Fin 3, (h k : ℝ) ^ 2

/-- A deterministic minimizer among the four drift directions. -/
noncomputable def minAssignment (v : Fin 3 → ℝ) : Assignment :=
  Classical.choose (Finset.exists_min_image Finset.univ (driftDot v)
    Finset.univ_nonempty)

theorem minAssignment_le (v : Fin 3 → ℝ) (α : Assignment) :
    driftDot v (minAssignment v) ≤ driftDot v α := by
  exact (Classical.choose_spec (Finset.exists_min_image Finset.univ (driftDot v)
    Finset.univ_nonempty)).2 α (Finset.mem_univ α)

/-- The feedback assignment used for the next block. -/
noncomputable def feedback (h : Fin 3 → ℤ) : Assignment :=
  minAssignment (imbalanceReal h)

/-- A fixed positive uniform drift constant supplied by compactness of the
unit sphere. -/
noncomputable def driftDelta : ℝ := Classical.choose exists_uniform_negative_drift

theorem driftDelta_pos : 0 < driftDelta :=
  (Classical.choose_spec exists_uniform_negative_drift).1

theorem minDriftDot_le_neg_delta {v : Fin 3 → ℝ} (hv : ‖v‖ = 1) :
    minDriftDot v ≤ -driftDelta :=
  (Classical.choose_spec exists_uniform_negative_drift).2 v hv

theorem exists_assignment_le_minDriftDot (v : Fin 3 → ℝ) :
    ∃ α : Assignment, driftDot v α ≤ minDriftDot v := by
  let α := minAssignment v
  refine ⟨α, ?_⟩
  apply le_min
  · exact minAssignment_le v 0
  · apply le_min
    · exact minAssignment_le v 1
    · exact le_min (minAssignment_le v 2) (minAssignment_le v 3)

theorem driftDot_smul (c : ℝ) (v : Fin 3 → ℝ) (α : Assignment) :
    driftDot (c • v) α = c * driftDot v α := by
  rw [driftDot, driftDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_imbalanceReal_pos {h : Fin 3 → ℤ} (hh : h ≠ 0) :
    0 < ‖imbalanceReal h‖ := by
  rw [norm_pos_iff]
  intro hz
  apply hh
  funext k
  have hk := congrFun hz k
  have hk' : (h k : ℝ) = 0 := by simpa [imbalanceReal] using hk
  exact_mod_cast hk'

/-- The chosen stationary drift has a uniformly negative radial component. -/
theorem feedback_drift_le (h : Fin 3 → ℤ) :
    driftDot (imbalanceReal h) (feedback h) ≤
      -driftDelta * ‖imbalanceReal h‖ := by
  by_cases hh : h = 0
  · subst h
    have hz : imbalanceReal (0 : Fin 3 → ℤ) = 0 := by
      funext k
      simp [imbalanceReal]
    rw [hz, norm_zero]
    simp [driftDot]
  · let r := ‖imbalanceReal h‖
    have hr : 0 < r := norm_imbalanceReal_pos hh
    let v : Fin 3 → ℝ := r⁻¹ • imbalanceReal h
    have hv : ‖v‖ = 1 := by
      rw [show v = r⁻¹ • imbalanceReal h from rfl, norm_smul]
      simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      exact inv_mul_cancel₀ hr.ne'
    obtain ⟨α, hα⟩ := exists_assignment_le_minDriftDot v
    have hαδ : driftDot v α ≤ -driftDelta :=
      hα.trans (minDriftDot_le_neg_delta hv)
    have hscale : imbalanceReal h = r • v := by
      simp only [v, smul_smul]
      rw [mul_inv_cancel₀ hr.ne']
      simp
    calc
      driftDot (imbalanceReal h) (feedback h) ≤
          driftDot (imbalanceReal h) α := minAssignment_le _ α
      _ = r * driftDot v α := by rw [hscale, driftDot_smul]
      _ ≤ r * (-driftDelta) := mul_le_mul_of_nonneg_left hαδ hr.le
      _ = -driftDelta * ‖imbalanceReal h‖ := by rw [show r = ‖imbalanceReal h‖ from rfl]; ring

/-! ### Uniform finite-block estimates -/

theorem prescribed_increment_abs_le (α : Assignment) (i : Fin 19) (k : Fin 3) :
    |imbalanceIncrementInt (prescribed α i) k| ≤ 30 := by
  have ha := prescribed_mem_multipliers α i
  simp only [multipliers, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha | ha | ha | ha <;> rw [ha] <;>
    fin_cases k <;>
    simp [imbalanceIncrementInt, primeIncrement, Matrix.cons_val_two,
      Matrix.cons_val_three]

theorem blockIncrement_abs_le (α : Assignment) (n : ℕ) (i : Fin 19)
    (w : Fin n → Fin 19) (k : Fin 3) :
    |blockIncrement α n i w k| ≤ 30 * n := by
  induction n generalizing i with
  | zero => simp [blockIncrement]
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from (Fin.cons_self_tail w).symm,
        blockIncrement_cons]
      calc
        |imbalanceIncrementInt (prescribed α i) k +
            blockIncrement α n (w 0) (Fin.tail w) k| ≤
            |imbalanceIncrementInt (prescribed α i) k| +
              |blockIncrement α n (w 0) (Fin.tail w) k| := abs_add_le _ _
        _ ≤ 30 + 30 * n := add_le_add (prescribed_increment_abs_le α i k)
          (ih (w 0) (Fin.tail w))
        _ = 30 * (n + 1) := by ring

theorem blockIncrement_square_sum_le (α : Assignment) (n : ℕ) (i : Fin 19)
    (w : Fin n → Fin 19) :
    (∑ k : Fin 3, (blockIncrement α n i w k : ℝ) ^ 2) ≤ 2700 * n ^ 2 := by
  have hbound (k : Fin 3) :
      |(blockIncrement α n i w k : ℝ)| ≤ 30 * n := by
    exact_mod_cast blockIncrement_abs_le α n i w k
  have hsquare (k : Fin 3) :
      (blockIncrement α n i w k : ℝ) ^ 2 ≤ (30 * (n : ℝ)) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 30 * n)] using hbound k
  calc
    _ ≤ ∑ _k : Fin 3, (30 * (n : ℝ)) ^ 2 :=
      Finset.sum_le_sum fun k _ ↦ hsquare k
    _ = 2700 * n ^ 2 := by norm_num [Fin.sum_univ_succ]; ring

theorem sum_blockWeight_real (α : Assignment) (n : ℕ) (i : Fin 19) :
    ∑ w : Fin n → Fin 19, (blockWeight α n i w : ℝ) = 1 := by
  exact_mod_cast blockWeight_sum α n i

theorem expected_block_square_le (α : Assignment) (n : ℕ) (i : Fin 19) :
    (∑ w : Fin n → Fin 19, (blockWeight α n i w : ℝ) *
      ∑ k : Fin 3, (blockIncrement α n i w k : ℝ) ^ 2) ≤
        (2700 : ℝ) * (n : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ w : Fin n → Fin 19, (blockWeight α n i w : ℝ) *
        ((2700 : ℝ) * (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro w _
      apply mul_le_mul_of_nonneg_left (blockIncrement_square_sum_le α n i w)
      exact_mod_cast blockWeight_nonneg α n i w
    _ = (2700 : ℝ) * (n : ℝ) ^ 2 := by
      rw [← Finset.sum_mul, sum_blockWeight_real, one_mul]

theorem sum_blockWeight_mul_increment_real (α : Assignment) (n : ℕ)
    (i : Fin 19) (k : Fin 3) :
    ∑ w : Fin n → Fin 19, (blockWeight α n i w : ℝ) *
        (blockIncrement α n i w k : ℝ) = expectedAccum α n i k := by
  exact_mod_cast sum_blockWeight_mul_increment α n i k

theorem expectedAccum_error_abs_le_real (α : Assignment) (n : ℕ)
    (i : Fin 19) (k : Fin 3) :
    |(expectedAccum α n i k : ℝ) - n * listedDriftReal α k| ≤ 80 := by
  simp only [listedDriftReal]
  exact_mod_cast expectedAccum_error_abs_le α n i k

/-- Expected Lyapunov increment over a block, expressed as a finite path sum. -/
def expectedSquareIncrement (α : Assignment) (n : ℕ)
    (i : Fin 19) (h : Fin 3 → ℤ) : ℝ :=
  ∑ w : Fin n → Fin 19, (blockWeight α n i w : ℝ) *
    (squareLength (fun k ↦ h k + blockIncrement α n i w k) - squareLength h)

theorem expectedSquareIncrement_le (α : Assignment) (n : ℕ)
    (i : Fin 19) (h : Fin 3 → ℤ) :
    expectedSquareIncrement α n i h ≤
      2 * n * driftDot (imbalanceReal h) α +
        480 * ‖imbalanceReal h‖ + 2700 * n ^ 2 := by
  have hcoord (k : Fin 3) : |(h k : ℝ)| ≤ ‖imbalanceReal h‖ := by
    have hk : ‖imbalanceReal h k‖₊ ≤
        Finset.univ.sup (fun j : Fin 3 ↦ ‖imbalanceReal h j‖₊) :=
      Finset.le_sup (s := Finset.univ)
        (f := fun j : Fin 3 ↦ ‖imbalanceReal h j‖₊) (Finset.mem_univ k)
    change ‖imbalanceReal h k‖ ≤ ‖imbalanceReal h‖
    change ‖imbalanceReal h k‖ ≤
      (↑(Finset.univ.sup (fun j : Fin 3 ↦ ‖imbalanceReal h j‖₊)) : ℝ)
    exact_mod_cast hk
  have herr (k : Fin 3) := expectedAccum_error_abs_le_real α n i k
  have hdotError :
      (∑ k : Fin 3, (h k : ℝ) * (expectedAccum α n i k : ℝ)) ≤
        n * driftDot (imbalanceReal h) α + 240 * ‖imbalanceReal h‖ := by
    have hterm (k : Fin 3) :
        (h k : ℝ) * ((expectedAccum α n i k : ℝ) - n * listedDriftReal α k) ≤
          80 * ‖imbalanceReal h‖ := by
      calc
        _ ≤ |(h k : ℝ) * ((expectedAccum α n i k : ℝ) -
              n * listedDriftReal α k)| := le_abs_self _
        _ = |(h k : ℝ)| * |(expectedAccum α n i k : ℝ) -
              n * listedDriftReal α k| := abs_mul _ _
        _ ≤ ‖imbalanceReal h‖ * 80 :=
          mul_le_mul (hcoord k) (herr k) (abs_nonneg _) (norm_nonneg _)
        _ = 80 * ‖imbalanceReal h‖ := by ring
    calc
      _ = n * driftDot (imbalanceReal h) α +
          ∑ k : Fin 3, (h k : ℝ) * ((expectedAccum α n i k : ℝ) -
            n * listedDriftReal α k) := by
          simp only [driftDot, imbalanceReal, Fin.sum_univ_succ]
          ring
      _ ≤ n * driftDot (imbalanceReal h) α +
          ∑ _k : Fin 3, 80 * ‖imbalanceReal h‖ := by
          apply add_le_add_left
          exact Finset.sum_le_sum fun k _ ↦ hterm k
      _ = n * driftDot (imbalanceReal h) α + 240 * ‖imbalanceReal h‖ := by
          norm_num [Fin.sum_univ_succ]
          ring
  have hexpand : expectedSquareIncrement α n i h =
      2 * (∑ k : Fin 3, (h k : ℝ) * (expectedAccum α n i k : ℝ)) +
        ∑ w : Fin n → Fin 19, (blockWeight α n i w : ℝ) *
          ∑ k : Fin 3, (blockIncrement α n i w k : ℝ) ^ 2 := by
    have hpoint (w : Fin n → Fin 19) :
        squareLength (fun k ↦ h k + blockIncrement α n i w k) - squareLength h =
          2 * (∑ k : Fin 3, (h k : ℝ) * (blockIncrement α n i w k : ℝ)) +
            ∑ k : Fin 3, (blockIncrement α n i w k : ℝ) ^ 2 := by
      simp only [squareLength, Int.cast_add, Fin.sum_univ_succ]
      ring
    simp only [expectedSquareIncrement]
    simp_rw [hpoint, mul_add, Finset.sum_add_distrib]
    apply congrArg₂ (· + ·)
    · calc
        (∑ w : Fin n → Fin 19, (blockWeight α n i w : ℝ) *
            (2 * ∑ k : Fin 3, (h k : ℝ) *
              (blockIncrement α n i w k : ℝ))) =
            ∑ w : Fin n → Fin 19, ∑ k : Fin 3,
              2 * (h k : ℝ) * ((blockWeight α n i w : ℝ) *
                (blockIncrement α n i w k : ℝ)) := by
              apply Finset.sum_congr rfl
              intro w _
              simp only [Fin.sum_univ_succ]
              ring
        _ = ∑ k : Fin 3, ∑ w : Fin n → Fin 19,
              2 * (h k : ℝ) * ((blockWeight α n i w : ℝ) *
                (blockIncrement α n i w k : ℝ)) := Finset.sum_comm
        _ = 2 * (∑ k : Fin 3, (h k : ℝ) *
              (expectedAccum α n i k : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              rw [← Finset.mul_sum, sum_blockWeight_mul_increment_real]
              ring
    · rfl
  rw [hexpand]
  calc
    _ ≤ 2 * (n * driftDot (imbalanceReal h) α +
        240 * ‖imbalanceReal h‖) + 2700 * n ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hdotError (by norm_num))
        (expected_block_square_le α n i)
    _ = 2 * n * driftDot (imbalanceReal h) α +
        480 * ‖imbalanceReal h‖ + 2700 * n ^ 2 := by ring

/-- A block length large enough for its negative stationary drift to dominate
the uniformly bounded Poisson correction. -/
noncomputable def controlBlockLength : ℕ :=
  Classical.choose (exists_nat_gt (241 / driftDelta))

theorem controlBlockLength_drift :
    241 < (controlBlockLength : ℝ) * driftDelta := by
  have h := Classical.choose_spec (exists_nat_gt (241 / driftDelta))
  apply (div_lt_iff₀ driftDelta_pos).mp
  simpa [mul_comm] using h

theorem controlBlockLength_pos : 0 < controlBlockLength := by
  by_contra h
  have hz : controlBlockLength = 0 := Nat.eq_zero_of_not_pos h
  have hN := controlBlockLength_drift
  rw [hz] at hN
  norm_num at hN

/-- A finite radius outside which the block Lyapunov drift is at most `-1`. -/
noncomputable def controlRadius : ℕ := 2700 * controlBlockLength ^ 2 + 1

theorem controlled_block_drift (i : Fin 19) (h : Fin 3 → ℤ)
    (hout : controlRadius < ‖imbalanceReal h‖) :
    expectedSquareIncrement (feedback h) controlBlockLength i h ≤ -1 := by
  calc
    expectedSquareIncrement (feedback h) controlBlockLength i h ≤
        2 * controlBlockLength * driftDot (imbalanceReal h) (feedback h) +
          480 * ‖imbalanceReal h‖ + 2700 * controlBlockLength ^ 2 :=
      expectedSquareIncrement_le _ _ _ _
    _ ≤ 2 * controlBlockLength *
          (-driftDelta * ‖imbalanceReal h‖) +
          480 * ‖imbalanceReal h‖ + 2700 * controlBlockLength ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left (feedback_drift_le h)
        (show 0 ≤ (2 : ℝ) * controlBlockLength by positivity)
      norm_num at hm
      linarith
    _ ≤ -1 := by
      have hN := controlBlockLength_drift
      dsimp [controlRadius] at hout
      push_cast at hout
      nlinarith [norm_nonneg (imbalanceReal h)]

/-! ## Elementary finite-choice Markov chains

This file develops only the hitting-time facts needed below.  Keeping the
sample space as a finite choice at every step makes all one-step expectations
finite sums and avoids importing an undeveloped general Markov-chain API.
-/

structure FiniteChoiceChain (S Ω : Type*) [Fintype Ω] where
  next : S → Ω → S
  probability : S → Ω → ℝ
  probability_nonneg : ∀ x ω, 0 ≤ probability x ω
  probability_sum : ∀ x, ∑ ω, probability x ω = 1

namespace FiniteChoiceChain

variable {S Ω : Type*} [Fintype Ω] [DecidableEq S]
variable (K : FiniteChoiceChain S Ω) (C : Finset S)

/-- Probability of avoiding `C` through time `n`, when time zero is included. -/
def survival : ℕ → S → ℝ
  | 0, x => if x ∈ C then 0 else 1
  | n + 1, x =>
      if x ∈ C then 0 else ∑ ω, K.probability x ω * survival n (K.next x ω)

/-- Probability of first hitting `C` exactly at time `n`, with the endpoint
summed over all members of `C`. -/
def hitTotal : ℕ → S → ℝ
  | 0, x => if x ∈ C then 1 else 0
  | n + 1, x =>
      if x ∈ C then 0 else ∑ ω, K.probability x ω * hitTotal n (K.next x ω)

/-- Expected hitting time truncated at `n`. -/
def truncatedHit : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, x =>
      if x ∈ C then 0 else
        1 + ∑ ω, K.probability x ω * truncatedHit n (K.next x ω)

@[simp] theorem survival_zero_of_mem {x : S} (hx : x ∈ C) :
    K.survival C 0 x = 0 := by simp [survival, hx]

@[simp] theorem survival_zero_of_not_mem {x : S} (hx : x ∉ C) :
    K.survival C 0 x = 1 := by simp [survival, hx]

@[simp] theorem survival_succ_of_mem (n : ℕ) {x : S} (hx : x ∈ C) :
    K.survival C (n + 1) x = 0 := by simp [survival, hx]

theorem survival_succ_of_not_mem (n : ℕ) {x : S} (hx : x ∉ C) :
    K.survival C (n + 1) x =
      ∑ ω, K.probability x ω * K.survival C n (K.next x ω) := by
  simp [survival, hx]

@[simp] theorem hitTotal_succ_of_mem (n : ℕ) {x : S} (hx : x ∈ C) :
    K.hitTotal C (n + 1) x = 0 := by simp [hitTotal, hx]

theorem hitTotal_succ_of_not_mem (n : ℕ) {x : S} (hx : x ∉ C) :
    K.hitTotal C (n + 1) x =
      ∑ ω, K.probability x ω * K.hitTotal C n (K.next x ω) := by
  simp [hitTotal, hx]

theorem truncatedHit_succ_of_not_mem (n : ℕ) {x : S} (hx : x ∉ C) :
    K.truncatedHit C (n + 1) x =
      1 + ∑ ω, K.probability x ω * K.truncatedHit C n (K.next x ω) := by
  simp [truncatedHit, hx]

theorem survival_of_mem (n : ℕ) {x : S} (hx : x ∈ C) :
    K.survival C n x = 0 := by
  cases n with
  | zero => exact survival_zero_of_mem K C hx
  | succ n => exact survival_succ_of_mem K C n hx

theorem hitTotal_nonneg (n : ℕ) (x : S) : 0 ≤ K.hitTotal C n x := by
  induction n generalizing x with
  | zero => simp only [hitTotal]; split_ifs <;> norm_num
  | succ n ih =>
      by_cases hx : x ∈ C
      · simp [hitTotal, hx]
      · rw [hitTotal_succ_of_not_mem K C n hx]
        exact Finset.sum_nonneg fun ω _ ↦
          mul_nonneg (K.probability_nonneg x ω) (ih (K.next x ω))

theorem survival_nonneg (n : ℕ) (x : S) : 0 ≤ K.survival C n x := by
  induction n generalizing x with
  | zero => simp only [survival]; split_ifs <;> norm_num
  | succ n ih =>
      by_cases hx : x ∈ C
      · simp [survival, hx]
      · rw [survival_succ_of_not_mem K C n hx]
        exact Finset.sum_nonneg fun ω _ ↦
          mul_nonneg (K.probability_nonneg x ω) (ih (K.next x ω))

theorem survival_le_one (n : ℕ) (x : S) : K.survival C n x ≤ 1 := by
  induction n generalizing x with
  | zero => simp only [survival]; split_ifs <;> norm_num
  | succ n ih =>
      by_cases hx : x ∈ C
      · simp [survival, hx]
      · rw [survival_succ_of_not_mem K C n hx, ← K.probability_sum x]
        apply Finset.sum_le_sum
        intro ω _
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (ih (K.next x ω)) (K.probability_nonneg x ω)

/-- Exact one-step tail recursion. -/
theorem hitTotal_succ_add_survival_succ (n : ℕ) (x : S) :
    K.hitTotal C (n + 1) x + K.survival C (n + 1) x =
      K.survival C n x := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ C
      · simp [hx]
      · rw [hitTotal_succ_of_not_mem K C 0 hx,
          survival_succ_of_not_mem K C 0 hx]
        rw [← Finset.sum_add_distrib]
        simp_rw [← mul_add]
        have hbase (y : S) : K.hitTotal C 0 y + K.survival C 0 y = 1 := by
          by_cases hy : y ∈ C <;> simp [hitTotal, survival, hy]
        simp_rw [hbase, mul_one, K.probability_sum]
        simp [survival, hx]
  | succ n ih =>
      by_cases hx : x ∈ C
      · simp [hx]
      · rw [hitTotal_succ_of_not_mem K C (n + 1) hx,
          survival_succ_of_not_mem K C (n + 1) hx,
          survival_succ_of_not_mem K C n hx, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        rw [← mul_add, ih]

/-- The probabilities of hitting by time `N` and surviving through time `N`
partition the sample space. -/
theorem sum_hitTotal_add_survival (N : ℕ) (x : S) :
    (∑ n ∈ Finset.range (N + 1), K.hitTotal C n x) +
      K.survival C N x = 1 := by
  induction N with
  | zero =>
      by_cases hx : x ∈ C <;> simp [hitTotal, survival, hx]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have htail := hitTotal_succ_add_survival_succ K C N x
      linarith

theorem sum_hitTotal_le_one (N : ℕ) (x : S) :
    (∑ n ∈ Finset.range (N + 1), K.hitTotal C n x) ≤ 1 := by
  have hpartition := sum_hitTotal_add_survival K C N x
  linarith [survival_nonneg K C N x]

/-- Truncation increases by the current survival probability. -/
theorem truncatedHit_succ_eq_add_survival (n : ℕ) (x : S) :
    K.truncatedHit C (n + 1) x =
      K.truncatedHit C n x + K.survival C n x := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ C <;> simp [truncatedHit, survival, hx]
  | succ n ih =>
      by_cases hx : x ∈ C
      · simp [hx, truncatedHit]
      · rw [truncatedHit_succ_of_not_mem K C (n + 1) hx,
          truncatedHit_succ_of_not_mem K C n hx,
          survival_succ_of_not_mem K C n hx]
        simp_rw [ih]
        simp_rw [mul_add, Finset.sum_add_distrib]
        ring

/-- Foster's drift inequality bounds all truncated hitting-time means. -/
theorem truncatedHit_le_of_drift (V : S → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hdrift : ∀ x, x ∉ C →
      (∑ ω, K.probability x ω * (V (K.next x ω) - V x)) ≤ -1)
    (n : ℕ) (x : S) : K.truncatedHit C n x ≤ V x := by
  induction n generalizing x with
  | zero => simpa using hV x
  | succ n ih =>
      by_cases hx : x ∈ C
      · simp [truncatedHit, hx, hV x]
      · rw [truncatedHit_succ_of_not_mem K C n hx]
        calc
          _ ≤ 1 + ∑ ω, K.probability x ω * V (K.next x ω) := by
            apply add_le_add_left
            apply Finset.sum_le_sum
            intro ω _
            exact mul_le_mul_of_nonneg_left (ih (K.next x ω))
              (K.probability_nonneg x ω)
          _ ≤ V x := by
            have hd := hdrift x hx
            simp_rw [mul_sub] at hd
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul, K.probability_sum,
              one_mul] at hd
            linarith

/-! ### Positive returns from a point already in the finite set -/

def returnSurvival (K : FiniteChoiceChain S Ω) (C : Finset S) : ℕ → S → ℝ
  | 0, _ => 1
  | n + 1, x => ∑ ω, K.probability x ω * K.survival C n (K.next x ω)

def returnHitTotal (K : FiniteChoiceChain S Ω) (C : Finset S) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, x => ∑ ω, K.probability x ω * K.hitTotal C n (K.next x ω)

def returnTruncated (K : FiniteChoiceChain S Ω) (C : Finset S) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, x => 1 + ∑ ω, K.probability x ω * K.truncatedHit C n (K.next x ω)

theorem returnSurvival_nonneg (n : ℕ) (x : S) :
    0 ≤ K.returnSurvival C n x := by
  cases n with
  | zero => simp [returnSurvival]
  | succ n =>
      simp only [returnSurvival]
      exact Finset.sum_nonneg fun ω _ ↦ mul_nonneg (K.probability_nonneg x ω)
        (survival_nonneg K C n (K.next x ω))

theorem returnHitTotal_nonneg (n : ℕ) (x : S) :
    0 ≤ K.returnHitTotal C n x := by
  cases n with
  | zero => simp [returnHitTotal]
  | succ n =>
      simp only [returnHitTotal]
      exact Finset.sum_nonneg fun ω _ ↦ mul_nonneg (K.probability_nonneg x ω)
        (hitTotal_nonneg K C n (K.next x ω))

theorem return_hit_add_survival (n : ℕ) (x : S) :
    K.returnHitTotal C (n + 1) x + K.returnSurvival C (n + 1) x =
      K.returnSurvival C n x := by
  cases n with
  | zero =>
      simp only [returnHitTotal, returnSurvival]
      rw [← Finset.sum_add_distrib]
      simp_rw [← mul_add]
      have hbase (y : S) : K.hitTotal C 0 y + K.survival C 0 y = 1 := by
        by_cases hy : y ∈ C <;> simp [hitTotal, survival, hy]
      simp_rw [hbase, mul_one, K.probability_sum]
  | succ n =>
      simp only [returnHitTotal, returnSurvival]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      rw [← mul_add, hitTotal_succ_add_survival_succ]

theorem returnTruncated_succ_eq_add_survival (n : ℕ) (x : S) :
    K.returnTruncated C (n + 1) x =
      K.returnTruncated C n x + K.returnSurvival C n x := by
  cases n with
  | zero => simp [returnTruncated, returnSurvival, truncatedHit]
  | succ n =>
      simp only [returnTruncated, returnSurvival]
      simp_rw [truncatedHit_succ_eq_add_survival]
      simp_rw [mul_add, Finset.sum_add_distrib]
      ring

theorem return_partialMean_add_tail (N : ℕ) (x : S) :
    (∑ n ∈ Finset.range (N + 1), (n : ℝ) * K.returnHitTotal C n x) +
        N * K.returnSurvival C N x = K.returnTruncated C N x := by
  induction N with
  | zero => simp [returnTruncated]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hhit := return_hit_add_survival K C N x
      have htrunc := returnTruncated_succ_eq_add_survival K C N x
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith

theorem returnTruncated_le (V : S → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hdrift : ∀ x, x ∉ C →
      (∑ ω, K.probability x ω * (V (K.next x ω) - V x)) ≤ -1)
    (n : ℕ) (x : S) :
    K.returnTruncated C n x ≤ 1 + ∑ ω, K.probability x ω * V (K.next x ω) := by
  cases n with
  | zero =>
      simp only [returnTruncated]
      exact add_nonneg (by norm_num) (Finset.sum_nonneg fun ω _ ↦
        mul_nonneg (K.probability_nonneg x ω) (hV (K.next x ω)))
  | succ n =>
      simp only [returnTruncated]
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
          (truncatedHit_le_of_drift K C V hV hdrift n (K.next x ω))
          (K.probability_nonneg x ω)

theorem return_mul_survival_le_truncated (n : ℕ) (x : S) :
    (n : ℝ) * K.returnSurvival C n x ≤ K.returnTruncated C n x := by
  induction n with
  | zero => simp [returnTruncated]
  | succ n ih =>
      rw [returnTruncated_succ_eq_add_survival K C n x,
        Nat.cast_add, Nat.cast_one]
      have hmono : K.returnSurvival C (n + 1) x ≤ K.returnSurvival C n x := by
        have h := return_hit_add_survival K C n x
        linarith [returnHitTotal_nonneg K C (n + 1) x]
      have hle : K.returnSurvival C (n + 1) x ≤ 1 := by
        cases n with
        | zero =>
            simp only [returnSurvival]
            rw [← K.probability_sum x]
            apply Finset.sum_le_sum
            intro ω _
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left (survival_le_one K C 0 (K.next x ω))
                (K.probability_nonneg x ω)
        | succ n =>
            exact hmono.trans (by
              simp only [returnSurvival]
              rw [← K.probability_sum x]
              apply Finset.sum_le_sum
              intro ω _
              simpa only [mul_one] using mul_le_mul_of_nonneg_left
                (survival_le_one K C n (K.next x ω)) (K.probability_nonneg x ω))
      nlinarith

theorem returnSurvival_tendsto_zero (V : S → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hdrift : ∀ x, x ∉ C →
      (∑ ω, K.probability x ω * (V (K.next x ω) - V x)) ≤ -1)
    (x : S) : Filter.Tendsto (fun n ↦ K.returnSurvival C n x)
      Filter.atTop (nhds 0) := by
  let B := 1 + ∑ ω, K.probability x ω * V (K.next x ω)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (by norm_num) (Finset.sum_nonneg fun ω _ ↦
      mul_nonneg (K.probability_nonneg x ω) (hV (K.next x ω)))
  have hbound (n : ℕ) :
      K.returnSurvival C (n + 1) x ≤ B / (n + 1 : ℝ) := by
    have hm := return_mul_survival_le_truncated K C (n + 1) x
    have ht := returnTruncated_le K C V hV hdrift (n + 1) x
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
    calc
      K.returnSurvival C (n + 1) x * (n + 1 : ℝ) =
          (n + 1 : ℝ) * K.returnSurvival C (n + 1) x := by ring
      _ ≤ K.returnTruncated C (n + 1) x := by simpa using hm
      _ ≤ B := by simpa [B] using ht
  have hupper : Filter.Tendsto (fun n : ℕ ↦ B / (n + 1 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hshift : Filter.Tendsto (fun n ↦ K.returnSurvival C (n + 1) x)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n ↦ returnSurvival_nonneg K C (n + 1) x)
      (Filter.Eventually.of_forall hbound) hupper
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by simpa [Nat.add_comm] using hshift)

theorem returnHitTotal_hasSum_one (V : S → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hdrift : ∀ x, x ∉ C →
      (∑ ω, K.probability x ω * (V (K.next x ω) - V x)) ≤ -1)
    (x : S) : HasSum (fun n ↦ K.returnHitTotal C n x) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n ↦ returnHitTotal_nonneg K C n x) 1]
  have hsurv := returnSurvival_tendsto_zero K C V hV hdrift x
  have hpartial (N : ℕ) :
      ∑ n ∈ Finset.range (N + 1), K.returnHitTotal C n x =
        1 - K.returnSurvival C N x := by
    induction N with
    | zero => simp [returnHitTotal, returnSurvival]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        have htail := return_hit_add_survival K C N x
        linarith
  have hshift : Filter.Tendsto
      (fun N ↦ ∑ n ∈ Finset.range (N + 1), K.returnHitTotal C n x)
      Filter.atTop (nhds 1) := by
    rw [show (fun N ↦ ∑ n ∈ Finset.range (N + 1), K.returnHitTotal C n x) =
      fun N ↦ 1 - K.returnSurvival C N x from funext hpartial]
    simpa using tendsto_const_nhds.sub hsurv
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by
    simpa [Nat.add_comm] using hshift)

theorem weighted_returnHitTotal_summable (V : S → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hdrift : ∀ x, x ∉ C →
      (∑ ω, K.probability x ω * (V (K.next x ω) - V x)) ≤ -1)
    (x : S) : Summable (fun n : ℕ ↦ (n : ℝ) * K.returnHitTotal C n x) := by
  let B := 1 + ∑ ω, K.probability x ω * V (K.next x ω)
  apply summable_of_sum_range_le (c := B)
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (returnHitTotal_nonneg K C n x)
  · intro N
    cases N with
    | zero =>
        dsimp [B]
        exact add_nonneg (by norm_num) (Finset.sum_nonneg fun ω _ ↦
          mul_nonneg (K.probability_nonneg x ω) (hV (K.next x ω)))
    | succ N =>
        have htail := return_partialMean_add_tail K C N x
        have ht := returnTruncated_le K C V hV hdrift N x
        have hzero : (0 : ℝ) ≤ N * K.returnSurvival C N x :=
          mul_nonneg (Nat.cast_nonneg _) (returnSurvival_nonneg K C N x)
        dsimp [B]
        linarith

/-! ### Endpoints of finite-set excursions -/

/-- Probability of first hitting `C` at the specified point and exact time. -/
def hitAt (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S) : ℕ → S → ℝ
  | 0, x => if x ∈ C ∧ x = y then 1 else 0
  | n + 1, x => if x ∈ C then 0 else
      ∑ ω, K.probability x ω * K.hitAt C y n (K.next x ω)

theorem hitAt_nonneg (y : S) (n : ℕ) (x : S) : 0 ≤ K.hitAt C y n x := by
  induction n generalizing x with
  | zero => simp only [hitAt]; split_ifs <;> norm_num
  | succ n ih =>
      by_cases hx : x ∈ C
      · simp [hitAt, hx]
      · simp only [hitAt, hx, if_false]
        exact Finset.sum_nonneg fun ω _ ↦ mul_nonneg (K.probability_nonneg x ω)
          (ih (K.next x ω))

theorem sum_hitAt_eq_hitTotal (n : ℕ) (x : S) :
    ∑ y ∈ C, K.hitAt C y n x = K.hitTotal C n x := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ C
      · simp [hitAt, hitTotal, hx]
      · simp [hitAt, hitTotal, hx]
  | succ n ih =>
      by_cases hx : x ∈ C
      · simp [hitAt, hitTotal, hx]
      · simp only [hitAt, hitTotal, hx, if_false]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ω _
        rw [← Finset.mul_sum, ih]

/-- Probability of a positive first return to `C` ending at `y`. -/
def returnAt (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, x => ∑ ω, K.probability x ω * K.hitAt C y n (K.next x ω)

theorem returnAt_nonneg (y : S) (n : ℕ) (x : S) :
    0 ≤ K.returnAt C y n x := by
  cases n with
  | zero => simp [returnAt]
  | succ n =>
      simp only [returnAt]
      exact Finset.sum_nonneg fun ω _ ↦ mul_nonneg (K.probability_nonneg x ω)
        (hitAt_nonneg K C y n (K.next x ω))

theorem sum_returnAt_eq_returnHitTotal (n : ℕ) (x : S) :
    ∑ y ∈ C, K.returnAt C y n x = K.returnHitTotal C n x := by
  cases n with
  | zero => simp [returnAt, returnHitTotal]
  | succ n =>
      simp only [returnAt, returnHitTotal]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      rw [← Finset.mul_sum, sum_hitAt_eq_hitTotal]

theorem returnAt_le_returnHitTotal {y : S} (hy : y ∈ C) (n : ℕ) (x : S) :
    K.returnAt C y n x ≤ K.returnHitTotal C n x := by
  rw [← sum_returnAt_eq_returnHitTotal K C n x]
  exact Finset.single_le_sum (fun z _ ↦ returnAt_nonneg K C z n x) hy

theorem returnAt_summable (V : S → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hdrift : ∀ x, x ∉ C →
      (∑ ω, K.probability x ω * (V (K.next x ω) - V x)) ≤ -1)
    {y : S} (hy : y ∈ C) (x : S) : Summable (fun n ↦ K.returnAt C y n x) := by
  apply Summable.of_nonneg_of_le (fun n ↦ returnAt_nonneg K C y n x)
    (fun n ↦ returnAt_le_returnHitTotal K C hy n x)
  exact (returnHitTotal_hasSum_one K C V hV hdrift x).summable

/-- Transition probability of the chain induced by successive visits to `C`. -/
noncomputable def inducedProbability (K : FiniteChoiceChain S Ω) (C : Finset S)
    (x y : S) : ℝ := ∑' n, K.returnAt C y n x

theorem inducedProbability_nonneg (x y : S) : 0 ≤ K.inducedProbability C x y := by
  exact tsum_nonneg fun n ↦ returnAt_nonneg K C y n x

theorem inducedProbability_row_sum (V : S → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hdrift : ∀ x, x ∉ C →
      (∑ ω, K.probability x ω * (V (K.next x ω) - V x)) ≤ -1)
    (x : S) : ∑ y ∈ C, K.inducedProbability C x y = 1 := by
  have hsummable (y : S) (hy : y ∈ C) :
      Summable (fun n ↦ K.returnAt C y n x) :=
    returnAt_summable K C V hV hdrift hy x
  simp only [inducedProbability]
  rw [← Summable.tsum_finsetSum hsummable]
  simp_rw [sum_returnAt_eq_returnHitTotal]
  exact (returnHitTotal_hasSum_one K C V hV hdrift x).tsum_eq

end FiniteChoiceChain

/-! ## The feedback-controlled augmented chain -/

abbrev ImbalanceState := Fin 3 → ℤ
abbrev AugmentedState := Fin 19 × ImbalanceState
abbrev BlockChoice := Fin controlBlockLength → Fin 19

/-- One controlled block, including its endpoint and net imbalance. -/
noncomputable def controlledNext (x : AugmentedState) (w : BlockChoice) :
    AugmentedState :=
  (blockEndpoint controlBlockLength x.1 w,
    fun k ↦ x.2 k + blockIncrement (feedback x.2) controlBlockLength x.1 w k)

noncomputable def controlledProbability (x : AugmentedState) (w : BlockChoice) : ℝ :=
  blockWeight (feedback x.2) controlBlockLength x.1 w

noncomputable def controlledChain : FiniteChoiceChain AugmentedState BlockChoice where
  next := controlledNext
  probability := controlledProbability
  probability_nonneg := by
    intro x w
    change (0 : ℝ) ≤ (blockWeight (feedback x.2) controlBlockLength x.1 w : ℝ)
    exact_mod_cast blockWeight_nonneg (feedback x.2) controlBlockLength x.1 w
  probability_sum := by
    intro x
    exact sum_blockWeight_real (feedback x.2) controlBlockLength x.1

noncomputable abbrev BoundedCoordinate :=
  {z : ℤ // z ∈ Finset.Icc (-(controlRadius : ℤ)) controlRadius}

/-- The finite collection of integer imbalance vectors in the control box. -/
noncomputable def boundedImbalances : Finset ImbalanceState :=
  Finset.univ.image fun f : Fin 3 → BoundedCoordinate ↦ fun k ↦ (f k : ℤ)

theorem mem_boundedImbalances_iff (h : ImbalanceState) :
    h ∈ boundedImbalances ↔
      ∀ k, -(controlRadius : ℤ) ≤ h k ∧ h k ≤ controlRadius := by
  constructor
  · intro hh k
    simp only [boundedImbalances, Finset.mem_image] at hh
    obtain ⟨f, _, rfl⟩ := hh
    exact Finset.mem_Icc.mp (f k).property
  · intro hh
    let f : Fin 3 → BoundedCoordinate := fun k ↦ ⟨h k, Finset.mem_Icc.mpr (hh k)⟩
    simp only [boundedImbalances, Finset.mem_image]
    exact ⟨f, Finset.mem_univ f, by rfl⟩

/-- The finite small set used in the Foster argument. -/
noncomputable def controlSet : Finset AugmentedState :=
  Finset.univ.product boundedImbalances

theorem mem_controlSet_iff (x : AugmentedState) :
    x ∈ controlSet ↔
      ∀ k, -(controlRadius : ℤ) ≤ x.2 k ∧ x.2 k ≤ controlRadius := by
  simp [controlSet, mem_boundedImbalances_iff]

theorem controlRadius_lt_norm_of_not_mem {x : AugmentedState} (hx : x ∉ controlSet) :
    controlRadius < ‖imbalanceReal x.2‖ := by
  by_contra h
  apply hx
  apply (mem_controlSet_iff x).mpr
  have hnorm : ‖imbalanceReal x.2‖ ≤ controlRadius := le_of_not_gt h
  have hcoords := (pi_norm_le_iff_of_nonneg
    (by positivity : (0 : ℝ) ≤ controlRadius)).mp hnorm
  intro k
  have hk := hcoords k
  rw [Real.norm_eq_abs, abs_le] at hk
  have hk' : (-(controlRadius : ℝ) ≤ (x.2 k : ℝ) ∧
      (x.2 k : ℝ) ≤ controlRadius) := by simpa [imbalanceReal] using hk
  exact_mod_cast hk'

def controlledLyapunov (x : AugmentedState) : ℝ := squareLength x.2

theorem controlledLyapunov_nonneg (x : AugmentedState) : 0 ≤ controlledLyapunov x := by
  simp only [controlledLyapunov, squareLength]
  exact Finset.sum_nonneg fun k _ ↦ sq_nonneg (x.2 k : ℝ)

theorem controlled_drift (x : AugmentedState) (hx : x ∉ controlSet) :
    (∑ w : BlockChoice, controlledChain.probability x w *
      (controlledLyapunov (controlledChain.next x w) - controlledLyapunov x)) ≤ -1 := by
  simpa [controlledChain, controlledNext, controlledProbability, controlledLyapunov,
    expectedSquareIncrement] using
      controlled_block_drift x.1 x.2 (controlRadius_lt_norm_of_not_mem hx)

theorem controlled_return_mean_finite (x : AugmentedState) :
    Summable (fun n : ℕ ↦ (n : ℝ) *
      controlledChain.returnHitTotal controlSet n x) :=
  controlledChain.weighted_returnHitTotal_summable controlSet controlledLyapunov
    controlledLyapunov_nonneg controlled_drift x

theorem controlled_returnAt_summable {y : AugmentedState} (hy : y ∈ controlSet)
    (x : AugmentedState) :
    Summable (fun n ↦ controlledChain.returnAt controlSet y n x) :=
  controlledChain.returnAt_summable controlSet controlledLyapunov
    controlledLyapunov_nonneg controlled_drift hy x
/-! ## Repeated excursions to the finite control set -/

/-- Cauchy convolution, written using the finite antidiagonal of a natural
number. -/
def convolution (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal n, f p.1 * g p.2

theorem summable_prod_of_nonnegative {f g : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hf : Summable f) (hg : Summable g) :
    Summable fun p : ℕ × ℕ ↦ f p.1 * g p.2 := by
  rw [summable_prod_of_nonneg (fun p ↦ mul_nonneg (hf0 p.1) (hg0 p.2))]
  constructor
  · intro n
    exact hg.mul_left (f n)
  · simpa only [hg.tsum_mul_left] using hf.mul_right (∑' m, g m)

theorem convolution_nonneg {f g : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ convolution f g n := by
  exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hf0 p.1) (hg0 p.2)

theorem convolution_summable {f g : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hf : Summable f) (hg : Summable g) : Summable (convolution f g) := by
  have hprod := summable_prod_of_nonnegative hf0 hg0 hf hg
  exact summable_sum_mul_antidiagonal_of_summable_mul hprod

theorem tsum_convolution {f g : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hf : Summable f) (hg : Summable g) :
    ∑' n, convolution f g n = (∑' n, f n) * ∑' n, g n := by
  exact (hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg
    (summable_prod_of_nonnegative hf0 hg0 hf hg)).symm

theorem weighted_convolution_eq (f g : ℕ → ℝ) (n : ℕ) :
    (n : ℝ) * convolution f g n =
      convolution (fun a ↦ (a : ℝ) * f a) g n +
        convolution f (fun b ↦ (b : ℝ) * g b) n := by
  simp only [convolution, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  rw [← hpn, Nat.cast_add]
  ring

theorem weighted_convolution_summable {f g : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hf : Summable f) (hg : Summable g)
    (hfw : Summable fun n : ℕ ↦ (n : ℝ) * f n)
    (hgw : Summable fun n : ℕ ↦ (n : ℝ) * g n) :
    Summable fun n : ℕ ↦ (n : ℝ) * convolution f g n := by
  have hleft := convolution_summable
    (fun n ↦ mul_nonneg (Nat.cast_nonneg n) (hf0 n)) hg0 hfw hg
  have hright := convolution_summable hf0
    (fun n ↦ mul_nonneg (Nat.cast_nonneg n) (hg0 n)) hf hgw
  have heq : (fun n : ℕ ↦ (n : ℝ) * convolution f g n) =
      fun n ↦ convolution (fun a ↦ (a : ℝ) * f a) g n +
        convolution f (fun b ↦ (b : ℝ) * g b) n := by
    funext n
    exact weighted_convolution_eq f g n
  rw [heq]
  exact hleft.add hright

theorem tsum_weighted_convolution {f g : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hf : Summable f) (hg : Summable g)
    (hfw : Summable fun n : ℕ ↦ (n : ℝ) * f n)
    (hgw : Summable fun n : ℕ ↦ (n : ℝ) * g n) :
    (∑' n : ℕ, (n : ℝ) * convolution f g n) =
      (∑' n : ℕ, (n : ℝ) * f n) * (∑' n, g n) +
        (∑' n, f n) * ∑' n : ℕ, (n : ℝ) * g n := by
  have hleft := convolution_summable
    (fun n ↦ mul_nonneg (Nat.cast_nonneg n) (hf0 n)) hg0 hfw hg
  have hright := convolution_summable hf0
    (fun n ↦ mul_nonneg (Nat.cast_nonneg n) (hg0 n)) hf hgw
  rw [show (fun n : ℕ ↦ (n : ℝ) * convolution f g n) =
      fun n ↦ convolution (fun a ↦ (a : ℝ) * f a) g n +
        convolution f (fun b ↦ (b : ℝ) * g b) n from
    funext (weighted_convolution_eq f g)]
  rw [hleft.tsum_add hright,
    tsum_convolution (fun n ↦ mul_nonneg (Nat.cast_nonneg n) (hf0 n))
      hg0 hfw hg,
    tsum_convolution hf0
      (fun n ↦ mul_nonneg (Nat.cast_nonneg n) (hg0 n)) hf hgw]

theorem summable_finset_sum {A : Type*} (s : Finset A) (f : A → ℕ → ℝ)
    (hf : ∀ a ∈ s, Summable (f a)) :
    Summable fun n ↦ ∑ a ∈ s, f a n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.mem_insert] at hf
      simpa [ha] using (hf a (Or.inl rfl)).add
        (ih fun b hb ↦ hf b (Or.inr hb))

theorem controlled_weighted_returnAt_summable {y : AugmentedState}
    (hy : y ∈ controlSet) (x : AugmentedState) :
    Summable fun n : ℕ ↦ (n : ℝ) * controlledChain.returnAt controlSet y n x := by
  apply Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (Nat.cast_nonneg n)
      (controlledChain.returnAt_nonneg controlSet y n x))
    (fun n ↦ mul_le_mul_of_nonneg_left
      (controlledChain.returnAt_le_returnHitTotal controlSet hy n x)
      (Nat.cast_nonneg n))
  exact controlled_return_mean_finite x

/-- One plus the sum of the mean return times over the finite control set. -/
noncomputable def excursionMeanBound : ℝ :=
  1 + ∑ x ∈ controlSet,
    ∑' n : ℕ, (n : ℝ) * controlledChain.returnHitTotal controlSet n x

theorem excursionMeanBound_pos : 0 < excursionMeanBound := by
  dsimp only [excursionMeanBound]
  have hsum : 0 ≤ ∑ x ∈ controlSet,
      ∑' n : ℕ, (n : ℝ) * controlledChain.returnHitTotal controlSet n x :=
    Finset.sum_nonneg fun x _ ↦ tsum_nonneg fun n ↦
      mul_nonneg (Nat.cast_nonneg n)
        (controlledChain.returnHitTotal_nonneg controlSet n x)
  linarith

theorem returnMean_le_excursionMeanBound {x : AugmentedState} (hx : x ∈ controlSet) :
    (∑' n : ℕ, (n : ℝ) * controlledChain.returnHitTotal controlSet n x) ≤
      excursionMeanBound := by
  have hsingle :
      (∑' n : ℕ, (n : ℝ) * controlledChain.returnHitTotal controlSet n x) ≤
        ∑ y ∈ controlSet,
          ∑' n : ℕ, (n : ℝ) *
            controlledChain.returnHitTotal controlSet n y := by
    exact Finset.single_le_sum (fun y _ ↦ tsum_nonneg fun n ↦
      mul_nonneg (Nat.cast_nonneg n)
        (controlledChain.returnHitTotal_nonneg controlSet n y)) hx
  dsimp only [excursionMeanBound]
  linarith

theorem sum_weighted_returnAt (x : AugmentedState) :
    (∑ y ∈ controlSet,
      ∑' n : ℕ, (n : ℝ) * controlledChain.returnAt controlSet y n x) =
      ∑' n : ℕ, (n : ℝ) *
        controlledChain.returnHitTotal controlSet n x := by
  have hs (y : AugmentedState) (hy : y ∈ controlSet) :=
    controlled_weighted_returnAt_summable hy x
  rw [← Summable.tsum_finsetSum hs]
  apply tsum_congr
  intro n
  rw [← Finset.mul_sum,
    controlledChain.sum_returnAt_eq_returnHitTotal controlSet n x]

/-- The zero imbalance at interval zero is a concrete member of the finite
control set. -/
def originState : AugmentedState := (0, fun _ ↦ 0)

theorem originState_mem_controlSet : originState ∈ controlSet := by
  rw [mem_controlSet_iff]
  intro j
  simp [originState]

/-! ## Finite-choice paths -/

/-- A noncomputable indicator, convenient for finite sums over predicates. -/
noncomputable def selectedWeight (P : Prop) (r : ℝ) : ℝ := by
  classical
  exact if P then r else 0

theorem selectedWeight_mul_left (P : Prop) (a r : ℝ) :
    selectedWeight P (a * r) = a * selectedWeight P r := by
  classical
  by_cases hP : P <;> simp [selectedWeight, hP]

theorem sum_subtype_eq_selected {A : Type*} [Fintype A]
    (P : A → Prop) [Fintype {a : A // P a}] (g : A → ℝ) :
    (∑ x : {a : A // P a}, g x.1) = ∑ a, selectedWeight (P a) (g a) := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) g]
  simpa only [selectedWeight] using Finset.sum_filter P g

theorem sum_finset_subtype {A : Type*} (s : Finset A) (g : A → ℝ) :
    (∑ x : ↑s, g x.1) = ∑ x ∈ s, g x := by
  classical
  simpa using Finset.sum_attach s g

theorem sum_subtype_eq_sum_attach {A : Type*} (s : Finset A) (g : ↑s → ℝ) :
    (∑ x : ↑s, g x) = ∑ x ∈ s.attach, g x := by
  classical
  rfl

namespace FiniteChoiceChain

variable {S Ω : Type*} [Fintype Ω] [DecidableEq S]

/-- Endpoint after a tuple of choices. -/
def pathEndpoint (K : FiniteChoiceChain S Ω) :
    (n : ℕ) → S → (Fin n → Ω) → S
  | 0, x, _ => x
  | n + 1, x, w => K.pathEndpoint n (K.next x (w 0)) (Fin.tail w)

/-- Product of the one-step choice probabilities along a tuple. -/
def pathWeight (K : FiniteChoiceChain S Ω) :
    (n : ℕ) → S → (Fin n → Ω) → ℝ
  | 0, _, _ => 1
  | n + 1, x, w =>
      K.probability x (w 0) * K.pathWeight n (K.next x (w 0)) (Fin.tail w)

/-- A path that hits `C` for the first time at its endpoint `y`; time zero
counts as a hit. -/
def IsHitPath (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S) :
    (n : ℕ) → S → (Fin n → Ω) → Prop
  | 0, x, _ => x ∈ C ∧ x = y
  | n + 1, x, w => x ∉ C ∧
      K.IsHitPath C y n (K.next x (w 0)) (Fin.tail w)

/-- A positive first return to `C`, ending at `y`. -/
def IsReturnPath (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S) :
    (n : ℕ) → S → (Fin n → Ω) → Prop
  | 0, _, _ => False
  | n + 1, x, w =>
      K.IsHitPath C y n (K.next x (w 0)) (Fin.tail w)

omit [DecidableEq S] in
@[simp] theorem pathEndpoint_cons (K : FiniteChoiceChain S Ω) (n : ℕ)
    (x : S) (a : Ω) (w : Fin n → Ω) :
    K.pathEndpoint (n + 1) x (Fin.cons a w) =
      K.pathEndpoint n (K.next x a) w := by
  simp [pathEndpoint]

omit [DecidableEq S] in
@[simp] theorem pathWeight_cons (K : FiniteChoiceChain S Ω) (n : ℕ)
    (x : S) (a : Ω) (w : Fin n → Ω) :
    K.pathWeight (n + 1) x (Fin.cons a w) =
      K.probability x a * K.pathWeight n (K.next x a) w := by
  simp [pathWeight]

omit [DecidableEq S] in
@[simp] theorem isHitPath_zero (K : FiniteChoiceChain S Ω) (C : Finset S)
    (x y : S) (w : Fin 0 → Ω) : K.IsHitPath C y 0 x w ↔ x ∈ C ∧ x = y :=
  Iff.rfl

omit [DecidableEq S] in
@[simp] theorem isHitPath_cons (K : FiniteChoiceChain S Ω) (C : Finset S)
    (n : ℕ) (x y : S) (a : Ω) (w : Fin n → Ω) :
    K.IsHitPath C y (n + 1) x (Fin.cons a w) ↔
      x ∉ C ∧ K.IsHitPath C y n (K.next x a) w := by
  simp [IsHitPath]

omit [DecidableEq S] in
@[simp] theorem isReturnPath_zero (K : FiniteChoiceChain S Ω) (C : Finset S)
    (x y : S) (w : Fin 0 → Ω) : ¬ K.IsReturnPath C y 0 x w := by
  simp [IsReturnPath]

omit [DecidableEq S] in
@[simp] theorem isReturnPath_cons (K : FiniteChoiceChain S Ω) (C : Finset S)
    (n : ℕ) (x y : S) (a : Ω) (w : Fin n → Ω) :
    K.IsReturnPath C y (n + 1) x (Fin.cons a w) ↔
      K.IsHitPath C y n (K.next x a) w := by
  simp [IsReturnPath]

theorem sum_hitPath_weight (K : FiniteChoiceChain S Ω) (C : Finset S)
    (y : S) (n : ℕ) (x : S) :
    ∑ w : Fin n → Ω,
      selectedWeight (K.IsHitPath C y n x w) (K.pathWeight n x w) =
      K.hitAt C y n x := by
  classical
  induction n generalizing x with
  | zero =>
      by_cases hxy : x ∈ C ∧ x = y <;>
        simp [selectedWeight, IsHitPath, hitAt, pathWeight, hxy]
  | succ n ih =>
      rw [sum_tuple_succ]
      by_cases hx : x ∈ C
      · simp [selectedWeight, IsHitPath, hitAt, hx]
      · simp only [isHitPath_cons, hx, not_false_eq_true,
          true_and, pathWeight_cons, hitAt, if_false]
        apply Finset.sum_congr rfl
        intro a _
        simp_rw [selectedWeight_mul_left]
        rw [← Finset.mul_sum, ih]

theorem sum_returnPath_weight (K : FiniteChoiceChain S Ω) (C : Finset S)
    (y : S) (n : ℕ) (x : S) :
    ∑ w : Fin n → Ω,
      selectedWeight (K.IsReturnPath C y n x w) (K.pathWeight n x w) =
      K.returnAt C y n x := by
  classical
  cases n with
  | zero => simp [selectedWeight, IsReturnPath, returnAt]
  | succ n =>
      rw [sum_tuple_succ]
      simp only [isReturnPath_cons, pathWeight_cons, returnAt]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [selectedWeight_mul_left]
      rw [← Finset.mul_sum, sum_hitPath_weight]

end FiniteChoiceChain

/-! ## Recurrence in a finite stochastic kernel -/

structure FiniteKernel (F : Type*) [Fintype F] where
  probability : F → F → ℝ
  probability_nonneg : ∀ x y, 0 ≤ probability x y
  probability_sum : ∀ x, ∑ y, probability x y = 1

namespace FiniteKernel

variable {F : Type*} [Fintype F] [DecidableEq F] [Nonempty F]

def Edge (P : FiniteKernel F) (x y : F) : Prop := 0 < P.probability x y

def EdgePath (P : FiniteKernel F) : F → List F → F → Prop
  | x, [], y => x = y
  | x, z :: zs, y => P.Edge x z ∧ P.EdgePath z zs y

omit [DecidableEq F] [Nonempty F] in
theorem EdgePath.append (P : FiniteKernel F) {x y z : F} {u v : List F}
    (hu : P.EdgePath x u y) (hv : P.EdgePath y v z) :
    P.EdgePath x (u ++ v) z := by
  induction u generalizing x with
  | nil => simpa [EdgePath] using hu ▸ hv
  | cons a u ih =>
      obtain ⟨hxa, hau⟩ := hu
      exact ⟨hxa, ih hau⟩

noncomputable def reachable (P : FiniteKernel F) (x : F) : Finset F :=
  by
    classical
    exact Finset.univ.filter fun y ↦ ∃ w, P.EdgePath x w y

omit [DecidableEq F] [Nonempty F] in
theorem mem_reachable_iff (P : FiniteKernel F) (x y : F) :
    y ∈ P.reachable x ↔ ∃ w, P.EdgePath x w y := by
  classical
  simp [reachable]

omit [DecidableEq F] [Nonempty F] in
theorem self_mem_reachable (P : FiniteKernel F) (x : F) : x ∈ P.reachable x := by
  exact (P.mem_reachable_iff x x).2 ⟨[], rfl⟩

omit [DecidableEq F] [Nonempty F] in
theorem reachable_mono {P : FiniteKernel F} {x y : F} (hxy : y ∈ P.reachable x) :
    P.reachable y ⊆ P.reachable x := by
  intro z hz
  obtain ⟨u, hu⟩ := (P.mem_reachable_iff x y).1 hxy
  obtain ⟨v, hv⟩ := (P.mem_reachable_iff y z).1 hz
  exact (P.mem_reachable_iff x z).2 ⟨u ++ v, hu.append P hv⟩

/-- A state whose reachable set has minimum cardinality. -/
noncomputable def recurrentState (P : FiniteKernel F) : F :=
  Classical.choose (Finset.exists_min_image Finset.univ
    (fun x ↦ (P.reachable x).card) Finset.univ_nonempty)

omit [DecidableEq F] in
theorem recurrentState_minimal (P : FiniteKernel F) (x : F) :
    (P.reachable P.recurrentState).card ≤ (P.reachable x).card := by
  exact (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (fun x ↦ (P.reachable x).card) Finset.univ_nonempty)).2 x (Finset.mem_univ x)

omit [DecidableEq F] in
theorem recurrent_reachable_eq {P : FiniteKernel F} {y : F}
    (hy : y ∈ P.reachable P.recurrentState) :
    P.reachable y = P.reachable P.recurrentState := by
  apply Finset.eq_of_subset_of_card_le (reachable_mono hy)
  exact P.recurrentState_minimal y

omit [DecidableEq F] in
theorem recurrentState_reachable_from {P : FiniteKernel F} {y : F}
    (hy : y ∈ P.reachable P.recurrentState) :
    P.recurrentState ∈ P.reachable y := by
  rw [recurrent_reachable_eq hy]
  exact P.self_mem_reachable P.recurrentState

omit [DecidableEq F] in
theorem reachable_closed_edge {P : FiniteKernel F} {x y : F}
    (hx : x ∈ P.reachable P.recurrentState) (hxy : P.Edge x y) :
    y ∈ P.reachable P.recurrentState := by
  obtain ⟨u, hu⟩ := (P.mem_reachable_iff P.recurrentState x).1 hx
  exact (P.mem_reachable_iff P.recurrentState y).2
    ⟨u ++ [y], hu.append P ⟨hxy, rfl⟩⟩

noncomputable abbrev RecurrentClass (P : FiniteKernel F) :=
  {x : F // x ∈ P.reachable P.recurrentState}

omit [DecidableEq F] in
theorem probability_zero_outside {P : FiniteKernel F}
    (x : P.RecurrentClass) {y : F}
    (hy : y ∉ P.reachable P.recurrentState) : P.probability x.1 y = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hpos
    exact hy (reachable_closed_edge x.2 hpos)
  · exact P.probability_nonneg x.1 y

/-- Restriction to the closed minimal reachable class. -/
noncomputable def recurrentKernel (P : FiniteKernel F) :
    FiniteKernel P.RecurrentClass where
  probability x y := P.probability x.1 y.1
  probability_nonneg x y := P.probability_nonneg x.1 y.1
  probability_sum x := by
    classical
    rw [← P.probability_sum x.1]
    rw [← Finset.sum_subtype (P.reachable P.recurrentState)
      (fun y ↦ by simp) (fun y ↦ P.probability x.1 y)]
    apply Finset.sum_subset (by simp)
    intro y _ hy
    exact probability_zero_outside x hy

omit [DecidableEq F] in
theorem lift_edgePath_recurrent {P : FiniteKernel F} {x y : F} {w : List F}
    (hx : x ∈ P.reachable P.recurrentState)
    (hy : y ∈ P.reachable P.recurrentState) (hw : P.EdgePath x w y) :
    ∃ v : List P.RecurrentClass,
      P.recurrentKernel.EdgePath ⟨x, hx⟩ v ⟨y, hy⟩ := by
  induction w generalizing x with
  | nil =>
      subst x
      exact ⟨[], rfl⟩
  | cons z zs ih =>
      have hz := reachable_closed_edge hx hw.1
      obtain ⟨v, hv⟩ := ih hz hw.2
      refine ⟨⟨z, hz⟩ :: v, ?_⟩
      exact ⟨hw.1, hv⟩

noncomputable def recurrentClassBase (P : FiniteKernel F) : P.RecurrentClass :=
  ⟨P.recurrentState, P.self_mem_reachable P.recurrentState⟩

omit [DecidableEq F] in
theorem recurrentKernel_reaches_base (P : FiniteKernel F)
    (x : P.RecurrentClass) :
    P.recurrentClassBase ∈ P.recurrentKernel.reachable x := by
  have hs := P.recurrentState_reachable_from x.2
  obtain ⟨w, hw⟩ := (P.mem_reachable_iff x.1 P.recurrentState).1 hs
  obtain ⟨v, hv⟩ := lift_edgePath_recurrent x.2
    (P.self_mem_reachable P.recurrentState) hw
  exact (P.recurrentKernel.mem_reachable_iff x P.recurrentClassBase).2 ⟨v, hv⟩

/-! ### A uniform hitting estimate in a finite communicating class -/

noncomputable def toChain (P : FiniteKernel F) : FiniteChoiceChain F F where
  next _ y := y
  probability := P.probability
  probability_nonneg := P.probability_nonneg
  probability_sum := P.probability_sum

def pathProbability (P : FiniteKernel F) : F → List F → ℝ
  | _, [] => 1
  | x, y :: ys => P.probability x y * P.pathProbability y ys

omit [DecidableEq F] [Nonempty F] in
theorem probability_le_one (P : FiniteKernel F) (x y : F) :
    P.probability x y ≤ 1 := by
  rw [← P.probability_sum x]
  exact Finset.single_le_sum (fun z _ ↦ P.probability_nonneg x z) (Finset.mem_univ y)

omit [DecidableEq F] [Nonempty F] in
theorem pathProbability_nonneg (P : FiniteKernel F) (x : F) (w : List F) :
    0 ≤ P.pathProbability x w := by
  induction w generalizing x with
  | nil => simp [pathProbability]
  | cons y ys ih =>
      exact mul_nonneg (P.probability_nonneg x y) (ih y)

omit [DecidableEq F] [Nonempty F] in
theorem pathProbability_le_one (P : FiniteKernel F) (x : F) (w : List F) :
    P.pathProbability x w ≤ 1 := by
  induction w generalizing x with
  | nil => simp [pathProbability]
  | cons y ys ih =>
      simp only [pathProbability]
      nlinarith [P.probability_nonneg x y, P.probability_le_one x y,
        P.pathProbability_nonneg y ys, ih y]

omit [DecidableEq F] [Nonempty F] in
theorem pathProbability_pos {P : FiniteKernel F} {x y : F} {w : List F}
    (hw : P.EdgePath x w y) : 0 < P.pathProbability x w := by
  induction w generalizing x with
  | nil => simp [pathProbability]
  | cons z zs ih =>
      exact mul_pos hw.1 (ih hw.2)

omit [Nonempty F] in
theorem survival_antitone (P : FiniteKernel F) (C : Finset F) (x : F) :
    Antitone fun n ↦ P.toChain.survival C n x := by
  apply antitone_nat_of_succ_le
  intro n
  have htail := P.toChain.hitTotal_succ_add_survival_succ C n x
  linarith [P.toChain.hitTotal_nonneg C (n + 1) x]

omit [Nonempty F] in
theorem pathProbability_le_hitBy {P : FiniteKernel F} {x s : F} {w : List F}
    (hw : P.EdgePath x w s) :
    P.pathProbability x w ≤
      1 - P.toChain.survival {s} w.length x := by
  induction w generalizing x with
  | nil =>
      subst x
      simp [pathProbability]
  | cons y ys ih =>
      by_cases hxs : x = s
      · subst x
        rw [P.toChain.survival_of_mem {s} (y :: ys).length
          (Finset.mem_singleton_self s)]
        simp only [sub_zero]
        exact P.pathProbability_le_one s (y :: ys)
      · have hxmem : x ∉ ({s} : Finset F) := by simpa
        have hrest := ih hw.2
        have hhit0 (z : F) :
            0 ≤ 1 - P.toChain.survival {s} ys.length z := by
          linarith [P.toChain.survival_le_one {s} ys.length z]
        have hone :
            1 - P.toChain.survival {s} (y :: ys).length x =
              ∑ z, P.probability x z *
                (1 - P.toChain.survival {s} ys.length z) := by
          rw [List.length_cons,
            P.toChain.survival_succ_of_not_mem {s} ys.length hxmem]
          calc
            1 - ∑ z, P.toChain.probability x z *
                P.toChain.survival {s} ys.length (P.toChain.next x z) =
                (∑ z, P.probability x z) -
                  ∑ z, P.toChain.probability x z *
                    P.toChain.survival {s} ys.length (P.toChain.next x z) := by
              rw [P.probability_sum]
            _ = ∑ z, (P.probability x z -
                  P.toChain.probability x z *
                    P.toChain.survival {s} ys.length (P.toChain.next x z)) := by
              rw [Finset.sum_sub_distrib]
            _ = ∑ z, P.probability x z *
                (1 - P.toChain.survival {s} ys.length z) := by
              apply Finset.sum_congr rfl
              intro z _
              simp only [toChain]
              ring
        rw [hone]
        calc
          P.pathProbability x (y :: ys) =
              P.probability x y * P.pathProbability y ys := rfl
          _ ≤ P.probability x y *
              (1 - P.toChain.survival {s} ys.length y) :=
            mul_le_mul_of_nonneg_left hrest (P.probability_nonneg x y)
          _ ≤ ∑ z, P.probability x z *
              (1 - P.toChain.survival {s} ys.length z) :=
            Finset.single_le_sum (fun z _ ↦
              mul_nonneg (P.probability_nonneg x z) (hhit0 z)) (Finset.mem_univ y)

noncomputable def route (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) (x : F) : List F :=
  Classical.choose ((P.mem_reachable_iff x s).1 (hreach x))

omit [DecidableEq F] [Nonempty F] in
theorem route_spec (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) (x : F) :
    P.EdgePath x (P.route s hreach x) s :=
  Classical.choose_spec ((P.mem_reachable_iff x s).1 (hreach x))

noncomputable def routeLength (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) : ℕ :=
  1 + ∑ x, (P.route s hreach x).length

noncomputable def routeMinorization (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) : ℝ :=
  ∏ x, P.pathProbability x (P.route s hreach x)

omit [DecidableEq F] [Nonempty F] in
theorem routeLength_pos (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) : 0 < P.routeLength s hreach := by
  simp [routeLength]

omit [DecidableEq F] [Nonempty F] in
theorem route_length_lt (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) (x : F) :
    (P.route s hreach x).length < P.routeLength s hreach := by
  dsimp only [routeLength]
  have hle : (P.route s hreach x).length ≤
      ∑ y, (P.route s hreach y).length :=
    Finset.single_le_sum
      (fun y _ ↦ Nat.zero_le (P.route s hreach y).length) (Finset.mem_univ x)
  omega

omit [DecidableEq F] [Nonempty F] in
theorem routeMinorization_pos (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) :
    0 < P.routeMinorization s hreach := by
  apply Finset.prod_pos
  intro x _
  exact pathProbability_pos (P.route_spec s hreach x)

omit [Nonempty F] in
theorem routeMinorization_le_route (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) (x : F) :
    P.routeMinorization s hreach ≤
      P.pathProbability x (P.route s hreach x) := by
  classical
  rw [routeMinorization, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
  nth_rewrite 2 [← mul_one (P.pathProbability x (P.route s hreach x))]
  apply mul_le_mul_of_nonneg_left
  · exact Finset.prod_le_one (fun y _ ↦ P.pathProbability_nonneg y _)
      (fun y _ ↦ P.pathProbability_le_one y _)
  · exact P.pathProbability_nonneg x _

omit [Nonempty F] in
theorem uniform_survival_bound (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) (x : F) :
    P.toChain.survival {s} (P.routeLength s hreach) x ≤
      1 - P.routeMinorization s hreach := by
  have hpath := P.pathProbability_le_hitBy (P.route_spec s hreach x)
  have hmono := P.survival_antitone {s} x
    (Nat.le_of_lt (P.route_length_lt s hreach x))
  have hminor := P.routeMinorization_le_route s hreach x
  linarith

omit [Nonempty F] in
theorem survival_add_le (P : FiniteKernel F) (C : Finset F) (c : ℝ) {n : ℕ}
    (hn : ∀ y, P.toChain.survival C n y ≤ c) (m : ℕ) (x : F) :
    P.toChain.survival C (m + n) x ≤
      c * P.toChain.survival C m x := by
  induction m generalizing x with
  | zero =>
      by_cases hx : x ∈ C
      · simp [P.toChain.survival_of_mem C n hx,
          P.toChain.survival_zero_of_mem C hx]
      · simpa [P.toChain.survival_zero_of_not_mem C hx] using hn x
  | succ m ih =>
      by_cases hx : x ∈ C
      · simp [P.toChain.survival_of_mem C (m + 1 + n) hx,
          P.toChain.survival_of_mem C (m + 1) hx]
      · rw [show m + 1 + n = (m + n) + 1 by omega,
          P.toChain.survival_succ_of_not_mem C (m + n) hx,
          P.toChain.survival_succ_of_not_mem C m hx]
        calc
          ∑ y, P.probability x y * P.toChain.survival C (m + n) y ≤
              ∑ y, P.probability x y *
                (c * P.toChain.survival C m y) := by
            apply Finset.sum_le_sum
            intro y _
            exact mul_le_mul_of_nonneg_left (ih y) (P.probability_nonneg x y)
          _ = c * ∑ y, P.probability x y *
                P.toChain.survival C m y := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring

omit [DecidableEq F] [Nonempty F] in
theorem minorization_le_one (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) :
    P.routeMinorization s hreach ≤ 1 := by
  classical
  exact (P.routeMinorization_le_route s hreach s).trans
    (P.pathProbability_le_one s (P.route s hreach s))

omit [Nonempty F] in
theorem survival_blocks (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) (k : ℕ) (x : F) :
    P.toChain.survival {s} (P.routeLength s hreach * k) x ≤
      (1 - P.routeMinorization s hreach) ^ k := by
  let r := 1 - P.routeMinorization s hreach
  have hr0 : 0 ≤ r := sub_nonneg.mpr (P.minorization_le_one s hreach)
  induction k with
  | zero => exact P.toChain.survival_le_one {s} 0 x
  | succ k ih =>
      have hcontract := P.survival_add_le {s} r
        (P.uniform_survival_bound s hreach) (P.routeLength s hreach * k) x
      rw [Nat.mul_succ]
      calc
        P.toChain.survival {s}
            (P.routeLength s hreach * k + P.routeLength s hreach) x ≤
            r * P.toChain.survival {s} (P.routeLength s hreach * k) x := hcontract
        _ ≤ r * r ^ k := mul_le_mul_of_nonneg_left ih hr0
        _ = r ^ (k + 1) := by rw [pow_succ']

omit [Nonempty F] in
theorem returnSurvival_antitone (P : FiniteKernel F) (C : Finset F) (x : F) :
    Antitone fun n ↦ P.toChain.returnSurvival C n x := by
  apply antitone_nat_of_succ_le
  intro n
  have htail := P.toChain.return_hit_add_survival C n x
  linarith [P.toChain.returnHitTotal_nonneg C (n + 1) x]

omit [Nonempty F] in
theorem returnSurvival_blocks (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) (k : ℕ) :
    P.toChain.returnSurvival {s} (P.routeLength s hreach * k + 1) s ≤
      (1 - P.routeMinorization s hreach) ^ k := by
  simp only [FiniteChoiceChain.returnSurvival]
  calc
    ∑ y, P.probability s y *
        P.toChain.survival {s} (P.routeLength s hreach * k) y ≤
        ∑ y, P.probability s y *
          ((1 - P.routeMinorization s hreach) ^ k) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (P.survival_blocks s hreach k y)
        (P.probability_nonneg s y)
    _ = (1 - P.routeMinorization s hreach) ^ k := by
      rw [← Finset.sum_mul, P.probability_sum, one_mul]

theorem summable_pow_nat_div {L : ℕ} (hL : 0 < L) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ ↦ r ^ (n / L) := by
  letI : NeZero L := ⟨hL.ne'⟩
  have hgeom : Summable fun n : ℕ ↦ r ^ n :=
    summable_geometric_of_lt_one hr0 hr1
  have hprod : Summable fun p : ℕ × Fin L ↦ r ^ p.1 := by
    rw [summable_prod_of_nonneg (fun p ↦ pow_nonneg hr0 p.1)]
    constructor
    · intro n
      exact (hasSum_fintype (fun _ : Fin L ↦ r ^ n)).summable
    · simpa only [tsum_fintype, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, Fintype.card_fin, mul_comm] using
        hgeom.mul_left (L : ℝ)
  have hcomp := ((Nat.divModEquiv L).summable_iff).2 hprod
  simpa [Function.comp_def, Nat.divModEquiv] using hcomp

omit [Nonempty F] in
theorem returnSurvival_summable (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) :
    Summable fun n ↦ P.toChain.returnSurvival {s} n s := by
  let L := P.routeLength s hreach
  let r := 1 - P.routeMinorization s hreach
  have hL : 0 < L := P.routeLength_pos s hreach
  have hr0 : 0 ≤ r := sub_nonneg.mpr (P.minorization_le_one s hreach)
  have hr1 : r < 1 := by
    dsimp only [r]
    linarith [P.routeMinorization_pos s hreach]
  have hbound (n : ℕ) : P.toChain.returnSurvival {s} (n + 1) s ≤
      r ^ (n / L) := by
    have hindex : L * (n / L) + 1 ≤ n + 1 := by
      apply Nat.add_le_add_right
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n L
    exact (P.returnSurvival_antitone {s} s hindex).trans
      (P.returnSurvival_blocks s hreach (n / L))
  have hshift : Summable fun n ↦ P.toChain.returnSurvival {s} (n + 1) s := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ P.toChain.returnSurvival_nonneg {s} (n + 1) s) hbound
    exact summable_pow_nat_div hL hr0 hr1
  exact (summable_nat_add_iff 1).1 (by simpa [Nat.add_comm] using hshift)

omit [Nonempty F] in
theorem returnTruncated_eq_sum_survival (P : FiniteKernel F)
    (C : Finset F) (N : ℕ) (x : F) :
    P.toChain.returnTruncated C N x =
      ∑ n ∈ Finset.range N, P.toChain.returnSurvival C n x := by
  induction N with
  | zero => simp [FiniteChoiceChain.returnTruncated]
  | succ N ih =>
      rw [P.toChain.returnTruncated_succ_eq_add_survival C N x, ih,
        Finset.sum_range_succ]

omit [Nonempty F] in
theorem returnHitTotal_hasSum_one_finite (P : FiniteKernel F) (s : F)
    (hreach : ∀ x, s ∈ P.reachable x) :
    HasSum (fun n ↦ P.toChain.returnHitTotal {s} n s) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n ↦ P.toChain.returnHitTotal_nonneg {s} n s) 1]
  have hzero : Filter.Tendsto (fun n ↦ P.toChain.returnSurvival {s} n s)
      Filter.atTop (nhds 0) :=
    (P.returnSurvival_summable s hreach).tendsto_atTop_zero
  have hpartial (N : ℕ) :
      ∑ n ∈ Finset.range (N + 1), P.toChain.returnHitTotal {s} n s =
        1 - P.toChain.returnSurvival {s} N s := by
    induction N with
    | zero => simp [FiniteChoiceChain.returnHitTotal,
        FiniteChoiceChain.returnSurvival]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        have htail := P.toChain.return_hit_add_survival {s} N s
        linarith
  have hlim : Filter.Tendsto
      (fun N ↦ ∑ n ∈ Finset.range (N + 1),
        P.toChain.returnHitTotal {s} n s) Filter.atTop (nhds 1) := by
    rw [show (fun N ↦ ∑ n ∈ Finset.range (N + 1),
      P.toChain.returnHitTotal {s} n s) =
        fun N ↦ 1 - P.toChain.returnSurvival {s} N s from funext hpartial]
    simpa using tendsto_const_nhds.sub hzero
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by
    simpa [Nat.add_comm] using hlim)

end FiniteKernel

/-! ## A recurrent augmented state in the induced control-set chain -/

abbrev ControlState := {x : AugmentedState // x ∈ controlSet}

noncomputable instance : Nonempty ControlState :=
  ⟨⟨originState, originState_mem_controlSet⟩⟩

/-- The stochastic kernel obtained by observing successive positive returns
to the finite control set. -/
noncomputable def inducedControlKernel : FiniteKernel ControlState where
  probability x y := controlledChain.inducedProbability controlSet x.1 y.1
  probability_nonneg x y :=
    controlledChain.inducedProbability_nonneg controlSet x.1 y.1
  probability_sum x := by
    rw [show (∑ y : ControlState,
        controlledChain.inducedProbability controlSet x.1 y.1) =
        ∑ y ∈ controlSet,
          controlledChain.inducedProbability controlSet x.1 y by
      exact sum_finset_subtype controlSet
        (fun y ↦ controlledChain.inducedProbability controlSet x.1 y)]
    exact controlledChain.inducedProbability_row_sum controlSet controlledLyapunov
      controlledLyapunov_nonneg controlled_drift x.1

abbrev RecurrentControlClass := inducedControlKernel.RecurrentClass

/-- The base point of the minimal closed communicating class. -/
noncomputable def recurrentControlState : RecurrentControlClass :=
  inducedControlKernel.recurrentClassBase

noncomputable def recurrentAugmentedState : AugmentedState :=
  recurrentControlState.1.1

theorem recurrentAugmentedState_mem : recurrentAugmentedState ∈ controlSet :=
  recurrentControlState.1.2

theorem recurrentClass_reaches_base (x : RecurrentControlClass) :
    recurrentControlState ∈ inducedControlKernel.recurrentKernel.reachable x :=
  inducedControlKernel.recurrentKernel_reaches_base x

theorem recurrent_visit_return_total :
    HasSum (fun n ↦
      inducedControlKernel.recurrentKernel.toChain.returnHitTotal
        {recurrentControlState} n recurrentControlState) 1 :=
  inducedControlKernel.recurrentKernel.returnHitTotal_hasSum_one_finite
    recurrentControlState recurrentClass_reaches_base

/-! ## Lifting recurrence through control-set excursion durations -/

noncomputable section

abbrev EmbeddedKernel := inducedControlKernel.recurrentKernel
abbrev EmbeddedChain := EmbeddedKernel.toChain
abbrev EmbeddedState := RecurrentControlClass

/-- Joint mass of an excursion duration and its next embedded state. -/
noncomputable def holdingMass (x y : EmbeddedState) (n : ℕ) : ℝ :=
  controlledChain.returnAt controlSet y.1.1 n x.1.1

theorem holdingMass_nonneg (x y : EmbeddedState) (n : ℕ) :
    0 ≤ holdingMass x y n :=
  controlledChain.returnAt_nonneg controlSet y.1.1 n x.1.1

theorem holdingMass_summable (x y : EmbeddedState) :
    Summable fun n ↦ holdingMass x y n :=
  controlled_returnAt_summable y.1.2 x.1.1

theorem tsum_holdingMass (x y : EmbeddedState) :
    (∑' n, holdingMass x y n) = EmbeddedKernel.probability x y := by
  rfl

theorem weighted_holdingMass_summable (x y : EmbeddedState) :
    Summable fun n : ℕ ↦ (n : ℝ) * holdingMass x y n :=
  controlled_weighted_returnAt_summable y.1.2 x.1.1

theorem sum_holdingMean_le (x : EmbeddedState) :
    (∑ y, ∑' n : ℕ, (n : ℝ) * holdingMass x y n) ≤
      excursionMeanBound := by
  let g : ControlState → ℝ := fun y ↦
    ∑' n : ℕ, (n : ℝ) *
      controlledChain.returnAt controlSet y.1 n x.1.1
  have hsub₁ : (∑ y, ∑' n : ℕ, (n : ℝ) * holdingMass x y n) ≤
      ∑ y : ControlState, g y := by
    rw [show (∑ y : EmbeddedState,
        ∑' n : ℕ, (n : ℝ) * holdingMass x y n) =
        ∑ y ∈ inducedControlKernel.reachable inducedControlKernel.recurrentState,
          g y by
      simpa [holdingMass, g] using
        (sum_finset_subtype
          (inducedControlKernel.reachable inducedControlKernel.recurrentState)
          g)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro y _ _
    exact tsum_nonneg fun n ↦ mul_nonneg (Nat.cast_nonneg n)
      (controlledChain.returnAt_nonneg controlSet y.1 n x.1.1)
  have hall : (∑ y : ControlState, g y) =
      ∑ y ∈ controlSet,
        ∑' n : ℕ, (n : ℝ) *
          controlledChain.returnAt controlSet y n x.1.1 := by
    simpa [g] using (sum_finset_subtype controlSet fun y ↦
      ∑' n : ℕ, (n : ℝ) *
        controlledChain.returnAt controlSet y n x.1.1)
  calc
    _ ≤ ∑ y : ControlState, g y := hsub₁
    _ ≤ ∑ y ∈ controlSet,
        ∑' n : ℕ, (n : ℝ) *
          controlledChain.returnAt controlSet y n x.1.1 := hall.le
    _ = ∑' n : ℕ, (n : ℝ) *
          controlledChain.returnHitTotal controlSet n x.1.1 :=
      sum_weighted_returnAt x.1.1
    _ ≤ excursionMeanBound := returnMean_le_excursionMeanBound x.1.2

/-- First hit of the base state after exactly `k` embedded visits and total
underlying block duration `n`. -/
noncomputable def holdingHit : ℕ → ℕ → EmbeddedState → ℝ
  | 0, n, x => if n = 0 ∧ x = recurrentControlState then 1 else 0
  | k + 1, n, x =>
      if x = recurrentControlState then 0 else
        ∑ y, convolution (holdingMass x y) (fun b ↦ holdingHit k b y) n

/-- Positive return of the base state after exactly `k` embedded visits. -/
noncomputable def holdingReturn : ℕ → ℕ → ℝ
  | 0, _ => 0
  | k + 1, n =>
      ∑ y, convolution (holdingMass recurrentControlState y)
        (fun b ↦ holdingHit k b y) n

theorem holdingHit_nonneg (k n : ℕ) (x : EmbeddedState) :
    0 ≤ holdingHit k n x := by
  induction k generalizing n x with
  | zero =>
      simp only [holdingHit]
      split_ifs <;> norm_num
  | succ k ih =>
      simp only [holdingHit]
      split_ifs
      · norm_num
      · exact Finset.sum_nonneg fun y _ ↦
          convolution_nonneg (holdingMass_nonneg x y) (fun b ↦ ih b y) n

theorem holdingReturn_nonneg (k n : ℕ) : 0 ≤ holdingReturn k n := by
  cases k with
  | zero => simp [holdingReturn]
  | succ k =>
      simp only [holdingReturn]
      exact Finset.sum_nonneg fun y _ ↦ convolution_nonneg
        (holdingMass_nonneg recurrentControlState y)
        (fun b ↦ holdingHit_nonneg k b y) n

theorem holdingHit_summable_and_mass (k : ℕ) (x : EmbeddedState) :
    Summable (fun n ↦ holdingHit k n x) ∧
      (∑' n, holdingHit k n x) =
        EmbeddedChain.hitAt {recurrentControlState} recurrentControlState k x := by
  induction k generalizing x with
  | zero =>
      by_cases hx : x = recurrentControlState
      · subst x
        have hs : HasSum (fun n : ℕ ↦ if n = 0 then (1 : ℝ) else 0) 1 :=
          hasSum_ite_eq 0 1
        constructor
        · simpa [holdingHit] using hs.summable
        · rw [show (fun n ↦ holdingHit 0 n recurrentControlState) =
              fun n ↦ if n = 0 then (1 : ℝ) else 0 by
            funext n
            simp [holdingHit]]
          rw [hs.tsum_eq]
          simp [FiniteChoiceChain.hitAt]
      · have hs : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0 := hasSum_zero
        constructor
        · simpa [holdingHit, hx] using hs.summable
        · rw [show (fun n ↦ holdingHit 0 n x) = fun _ ↦ (0 : ℝ) by
            funext n
            simp [holdingHit, hx]]
          rw [tsum_zero]
          simp [FiniteChoiceChain.hitAt, hx]
  | succ k ih =>
      by_cases hx : x = recurrentControlState
      · subst x
        constructor
        · have hz : (fun n ↦ holdingHit (k + 1) n recurrentControlState) =
              fun _ ↦ (0 : ℝ) := by
            funext n
            simp [holdingHit]
          rw [hz]
          exact summable_zero
        · simp [holdingHit, FiniteChoiceChain.hitAt]
      · have hconv (y : EmbeddedState) : Summable
            (convolution (holdingMass x y) (fun b ↦ holdingHit k b y)) :=
          convolution_summable (holdingMass_nonneg x y)
            (fun b ↦ holdingHit_nonneg k b y) (holdingMass_summable x y) (ih y).1
        have hsum : Summable (fun n ↦ holdingHit (k + 1) n x) := by
          simp only [holdingHit, hx, if_false]
          exact summable_finset_sum Finset.univ
            (fun y n ↦ convolution (holdingMass x y)
              (fun b ↦ holdingHit k b y) n) (by simpa using hconv)
        refine ⟨hsum, ?_⟩
        simp only [holdingHit, hx, if_false]
        rw [Summable.tsum_finsetSum (fun y _ ↦ hconv y)]
        have hxmem : x ∉ ({recurrentControlState} : Finset EmbeddedState) := by
          simpa using hx
        simp only [FiniteChoiceChain.hitAt, hxmem, if_false, EmbeddedChain,
          FiniteKernel.toChain]
        apply Finset.sum_congr rfl
        intro y _
        rw [tsum_convolution (holdingMass_nonneg x y)
          (fun b ↦ holdingHit_nonneg k b y) (holdingMass_summable x y) (ih y).1,
          tsum_holdingMass, (ih y).2]
        rfl

theorem holdingReturn_summable_and_mass (k : ℕ) :
    Summable (fun n ↦ holdingReturn k n) ∧
      (∑' n, holdingReturn k n) =
        EmbeddedChain.returnAt {recurrentControlState} recurrentControlState k
          recurrentControlState := by
  cases k with
  | zero =>
      constructor
      · simpa [holdingReturn] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
      · simp [holdingReturn, FiniteChoiceChain.returnAt]
  | succ k =>
      have hconv (y : EmbeddedState) : Summable
          (convolution (holdingMass recurrentControlState y)
            (fun b ↦ holdingHit k b y)) :=
        convolution_summable (holdingMass_nonneg recurrentControlState y)
          (fun b ↦ holdingHit_nonneg k b y)
          (holdingMass_summable recurrentControlState y)
          (holdingHit_summable_and_mass k y).1
      have hsum : Summable (fun n ↦ holdingReturn (k + 1) n) := by
        simp only [holdingReturn]
        exact summable_finset_sum Finset.univ
          (fun y n ↦ convolution (holdingMass recurrentControlState y)
            (fun b ↦ holdingHit k b y) n) (by simpa using hconv)
      refine ⟨hsum, ?_⟩
      simp only [holdingReturn]
      rw [Summable.tsum_finsetSum (fun y _ ↦ hconv y)]
      simp only [FiniteChoiceChain.returnAt, EmbeddedChain, FiniteKernel.toChain]
      apply Finset.sum_congr rfl
      intro y _
      rw [tsum_convolution (holdingMass_nonneg recurrentControlState y)
        (fun b ↦ holdingHit_nonneg k b y)
        (holdingMass_summable recurrentControlState y)
        (holdingHit_summable_and_mass k y).1, tsum_holdingMass,
        (holdingHit_summable_and_mass k y).2]
      rfl

theorem holdingHit_weighted_summable (k : ℕ) (x : EmbeddedState) :
    Summable fun n : ℕ ↦ (n : ℝ) * holdingHit k n x := by
  induction k generalizing x with
  | zero =>
      have hz : (fun n : ℕ ↦ (n : ℝ) * holdingHit 0 n x) =
          fun _ ↦ (0 : ℝ) := by
        funext n
        by_cases h : n = 0 ∧ x = recurrentControlState <;>
          simp [holdingHit, h]
      rw [hz]
      exact summable_zero
  | succ k ih =>
      by_cases hx : x = recurrentControlState
      · subst x
        have hz : (fun n : ℕ ↦ (n : ℝ) *
            holdingHit (k + 1) n recurrentControlState) = fun _ ↦ (0 : ℝ) := by
          funext n
          simp [holdingHit]
        rw [hz]
        exact summable_zero
      · have hconv (y : EmbeddedState) : Summable fun n : ℕ ↦ (n : ℝ) *
            convolution (holdingMass x y) (fun b ↦ holdingHit k b y) n :=
          weighted_convolution_summable (holdingMass_nonneg x y)
            (fun b ↦ holdingHit_nonneg k b y) (holdingMass_summable x y)
            (holdingHit_summable_and_mass k y).1
            (weighted_holdingMass_summable x y) (ih y)
        have hfinite := summable_finset_sum Finset.univ
          (fun y n ↦ (n : ℝ) * convolution (holdingMass x y)
            (fun b ↦ holdingHit k b y) n) (by simpa using hconv)
        simpa only [holdingHit, hx, if_false, Finset.mul_sum] using hfinite

theorem holdingReturn_weighted_summable (k : ℕ) :
    Summable fun n : ℕ ↦ (n : ℝ) * holdingReturn k n := by
  cases k with
  | zero =>
      simpa [holdingReturn] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  | succ k =>
      have hconv (y : EmbeddedState) : Summable fun n : ℕ ↦ (n : ℝ) *
          convolution (holdingMass recurrentControlState y)
            (fun b ↦ holdingHit k b y) n :=
        weighted_convolution_summable
          (holdingMass_nonneg recurrentControlState y)
          (fun b ↦ holdingHit_nonneg k b y)
          (holdingMass_summable recurrentControlState y)
          (holdingHit_summable_and_mass k y).1
          (weighted_holdingMass_summable recurrentControlState y)
          (holdingHit_weighted_summable k y)
      have hfinite := summable_finset_sum Finset.univ
        (fun y n ↦ (n : ℝ) * convolution
          (holdingMass recurrentControlState y)
          (fun b ↦ holdingHit k b y) n) (by simpa using hconv)
      simpa only [holdingReturn, Finset.mul_sum] using hfinite

theorem tsum_weighted_holdingHit_succ {k : ℕ} {x : EmbeddedState}
    (hx : x ≠ recurrentControlState) :
    (∑' n : ℕ, (n : ℝ) * holdingHit (k + 1) n x) =
      ∑ y : EmbeddedState,
        ((∑' n : ℕ, (n : ℝ) * holdingMass x y n) *
            EmbeddedChain.hitAt {recurrentControlState} recurrentControlState k y +
          EmbeddedKernel.probability x y *
            ∑' n : ℕ, (n : ℝ) * holdingHit k n y) := by
  have hconv (y : EmbeddedState) : Summable fun n : ℕ ↦ (n : ℝ) *
      convolution (holdingMass x y) (fun b ↦ holdingHit k b y) n :=
    weighted_convolution_summable (holdingMass_nonneg x y)
      (fun b ↦ holdingHit_nonneg k b y) (holdingMass_summable x y)
      (holdingHit_summable_and_mass k y).1 (weighted_holdingMass_summable x y)
      (holdingHit_weighted_summable k y)
  simp only [holdingHit, hx, if_false, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (by simpa using hconv)]
  apply Finset.sum_congr rfl
  intro y _
  rw [tsum_weighted_convolution (holdingMass_nonneg x y)
    (fun b ↦ holdingHit_nonneg k b y) (holdingMass_summable x y)
    (holdingHit_summable_and_mass k y).1 (weighted_holdingMass_summable x y)
    (holdingHit_weighted_summable k y), (holdingHit_summable_and_mass k y).2,
    tsum_holdingMass]

theorem tsum_weighted_holdingReturn_succ (k : ℕ) :
    (∑' n : ℕ, (n : ℝ) * holdingReturn (k + 1) n) =
      ∑ y : EmbeddedState,
        ((∑' n : ℕ, (n : ℝ) * holdingMass recurrentControlState y n) *
            EmbeddedChain.hitAt {recurrentControlState} recurrentControlState k y +
          EmbeddedKernel.probability recurrentControlState y *
            ∑' n : ℕ, (n : ℝ) * holdingHit k n y) := by
  have hconv (y : EmbeddedState) : Summable fun n : ℕ ↦ (n : ℝ) *
      convolution (holdingMass recurrentControlState y)
        (fun b ↦ holdingHit k b y) n :=
    weighted_convolution_summable
      (holdingMass_nonneg recurrentControlState y)
      (fun b ↦ holdingHit_nonneg k b y)
      (holdingMass_summable recurrentControlState y)
      (holdingHit_summable_and_mass k y).1
      (weighted_holdingMass_summable recurrentControlState y)
      (holdingHit_weighted_summable k y)
  simp only [holdingReturn, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (by simpa using hconv)]
  apply Finset.sum_congr rfl
  intro y _
  rw [tsum_weighted_convolution (holdingMass_nonneg recurrentControlState y)
    (fun b ↦ holdingHit_nonneg k b y)
    (holdingMass_summable recurrentControlState y)
    (holdingHit_summable_and_mass k y).1
    (weighted_holdingMass_summable recurrentControlState y)
    (holdingHit_weighted_summable k y), (holdingHit_summable_and_mass k y).2,
    tsum_holdingMass]

noncomputable def holdingHitMean (k : ℕ) (x : EmbeddedState) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * holdingHit k n x

noncomputable def holdingReturnMean (k : ℕ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * holdingReturn k n

@[simp] theorem holdingHitMean_zero (x : EmbeddedState) : holdingHitMean 0 x = 0 := by
  have hz : (fun n : ℕ ↦ (n : ℝ) * holdingHit 0 n x) = fun _ ↦ (0 : ℝ) := by
    funext n
    by_cases h : n = 0 ∧ x = recurrentControlState <;> simp [holdingHit, h]
  simp [holdingHitMean, hz]

@[simp] theorem holdingHitMean_base (k : ℕ) :
    holdingHitMean k recurrentControlState = 0 := by
  cases k with
  | zero => simp
  | succ k =>
      have hz : (fun n : ℕ ↦ (n : ℝ) *
          holdingHit (k + 1) n recurrentControlState) = fun _ ↦ (0 : ℝ) := by
        funext n
        simp [holdingHit]
      simp [holdingHitMean, hz]

@[simp] theorem holdingReturnMean_zero : holdingReturnMean 0 = 0 := by
  simp [holdingReturnMean, holdingReturn]

theorem embedded_hitAt_partial_le_one (N : ℕ) (x : EmbeddedState) :
    (∑ k ∈ Finset.range (N + 1),
      EmbeddedChain.hitAt {recurrentControlState} recurrentControlState k x) ≤ 1 := by
  have heq (k : ℕ) :
      EmbeddedChain.hitAt {recurrentControlState} recurrentControlState k x =
        EmbeddedChain.hitTotal {recurrentControlState} k x := by
    rw [← EmbeddedChain.sum_hitAt_eq_hitTotal
      {recurrentControlState} k x]
    simp
  simp_rw [heq]
  exact EmbeddedChain.sum_hitTotal_le_one {recurrentControlState} N x

theorem holdingHitMean_partial_le (N : ℕ) (x : EmbeddedState) :
    (∑ k ∈ Finset.range (N + 1), holdingHitMean k x) ≤
      excursionMeanBound *
        EmbeddedChain.truncatedHit {recurrentControlState} N x := by
  induction N generalizing x with
  | zero => simp [FiniteChoiceChain.truncatedHit]
  | succ N ih =>
      by_cases hx : x = recurrentControlState
      · subst x
        simp [FiniteChoiceChain.truncatedHit]
      · have hxmem : x ∉ ({recurrentControlState} : Finset EmbeddedState) := by
          simpa using hx
        rw [Finset.sum_range_succ']
        simp only [holdingHitMean_zero, add_zero]
        have hsplit :
            (∑ k ∈ Finset.range (N + 1), holdingHitMean (k + 1) x) =
              ∑ y : EmbeddedState,
                ((∑' n : ℕ, (n : ℝ) * holdingMass x y n) *
                    (∑ k ∈ Finset.range (N + 1),
                      EmbeddedChain.hitAt {recurrentControlState}
                        recurrentControlState k y) +
                  EmbeddedKernel.probability x y *
                    (∑ k ∈ Finset.range (N + 1), holdingHitMean k y)) := by
          simp_rw [holdingHitMean, tsum_weighted_holdingHit_succ hx]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [hsplit]
        calc
          _ ≤ ∑ y : EmbeddedState,
              ((∑' n : ℕ, (n : ℝ) * holdingMass x y n) +
                EmbeddedKernel.probability x y *
                  (excursionMeanBound *
                    EmbeddedChain.truncatedHit {recurrentControlState} N y)) := by
              apply Finset.sum_le_sum
              intro y _
              apply add_le_add
              · exact mul_le_of_le_one_right
                  (tsum_nonneg fun n ↦ mul_nonneg (Nat.cast_nonneg n)
                    (holdingMass_nonneg x y n))
                  (embedded_hitAt_partial_le_one N y)
              · exact mul_le_mul_of_nonneg_left (ih y)
                  (EmbeddedKernel.probability_nonneg x y)
          _ = (∑ y : EmbeddedState,
                ∑' n : ℕ, (n : ℝ) * holdingMass x y n) +
              excursionMeanBound *
                (∑ y : EmbeddedState, EmbeddedKernel.probability x y *
                  EmbeddedChain.truncatedHit {recurrentControlState} N y) := by
              rw [Finset.sum_add_distrib]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
          _ ≤ excursionMeanBound + excursionMeanBound *
                (∑ y : EmbeddedState, EmbeddedKernel.probability x y *
                  EmbeddedChain.truncatedHit {recurrentControlState} N y) := by
              exact add_le_add_right (sum_holdingMean_le x) _
          _ = excursionMeanBound *
              EmbeddedChain.truncatedHit {recurrentControlState} (N + 1) x := by
              rw [EmbeddedChain.truncatedHit_succ_of_not_mem
                {recurrentControlState} N hxmem]
              simp only [EmbeddedChain, FiniteKernel.toChain]
              ring

theorem holdingReturnMean_partial_le (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), holdingReturnMean k) ≤
      excursionMeanBound * EmbeddedChain.returnTruncated
        {recurrentControlState} N recurrentControlState := by
  cases N with
  | zero => simp [FiniteChoiceChain.returnTruncated]
  | succ N =>
      rw [Finset.sum_range_succ']
      simp only [holdingReturnMean_zero, add_zero]
      have hsplit :
          (∑ k ∈ Finset.range (N + 1), holdingReturnMean (k + 1)) =
            ∑ y : EmbeddedState,
              ((∑' n : ℕ, (n : ℝ) *
                  holdingMass recurrentControlState y n) *
                  (∑ k ∈ Finset.range (N + 1),
                    EmbeddedChain.hitAt {recurrentControlState}
                      recurrentControlState k y) +
                EmbeddedKernel.probability recurrentControlState y *
                  (∑ k ∈ Finset.range (N + 1), holdingHitMean k y)) := by
        simp_rw [holdingReturnMean, holdingHitMean,
          tsum_weighted_holdingReturn_succ]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hsplit]
      calc
        _ ≤ ∑ y : EmbeddedState,
            ((∑' n : ℕ, (n : ℝ) *
                holdingMass recurrentControlState y n) +
              EmbeddedKernel.probability recurrentControlState y *
                (excursionMeanBound *
                  EmbeddedChain.truncatedHit {recurrentControlState} N y)) := by
            apply Finset.sum_le_sum
            intro y _
            apply add_le_add
            · exact mul_le_of_le_one_right
                (tsum_nonneg fun n ↦ mul_nonneg (Nat.cast_nonneg n)
                  (holdingMass_nonneg recurrentControlState y n))
                (embedded_hitAt_partial_le_one N y)
            · exact mul_le_mul_of_nonneg_left (holdingHitMean_partial_le N y)
                (EmbeddedKernel.probability_nonneg recurrentControlState y)
        _ = (∑ y : EmbeddedState,
              ∑' n : ℕ, (n : ℝ) * holdingMass recurrentControlState y n) +
            excursionMeanBound *
              (∑ y : EmbeddedState,
                EmbeddedKernel.probability recurrentControlState y *
                  EmbeddedChain.truncatedHit {recurrentControlState} N y) := by
            rw [Finset.sum_add_distrib]
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
        _ ≤ excursionMeanBound + excursionMeanBound *
              (∑ y : EmbeddedState,
                EmbeddedKernel.probability recurrentControlState y *
                  EmbeddedChain.truncatedHit {recurrentControlState} N y) := by
            exact add_le_add_right (sum_holdingMean_le recurrentControlState) _
        _ = excursionMeanBound * EmbeddedChain.returnTruncated
              {recurrentControlState} (N + 1) recurrentControlState := by
            simp only [FiniteChoiceChain.returnTruncated, EmbeddedChain,
              FiniteKernel.toChain]
            ring

noncomputable def recurrentReturnDurationBound : ℝ :=
  excursionMeanBound *
    ∑' k, EmbeddedChain.returnSurvival
      {recurrentControlState} k recurrentControlState

theorem holdingReturnMean_summable : Summable holdingReturnMean := by
  apply summable_of_sum_range_le (c := recurrentReturnDurationBound)
  · intro k
    exact tsum_nonneg fun n ↦ mul_nonneg (Nat.cast_nonneg n)
      (holdingReturn_nonneg k n)
  · intro N
    cases N with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        exact mul_nonneg excursionMeanBound_pos.le
          (tsum_nonneg fun k ↦ EmbeddedChain.returnSurvival_nonneg
            {recurrentControlState} k recurrentControlState)
    | succ N =>
        refine (holdingReturnMean_partial_le N).trans ?_
        apply mul_le_mul_of_nonneg_left _ excursionMeanBound_pos.le
        rw [EmbeddedKernel.returnTruncated_eq_sum_survival
          {recurrentControlState} N recurrentControlState]
        exact (EmbeddedKernel.returnSurvival_summable recurrentControlState
          recurrentClass_reaches_base).sum_le_tsum (Finset.range N)
          (fun k _ ↦ EmbeddedChain.returnSurvival_nonneg
            {recurrentControlState} k recurrentControlState)

theorem embedded_returnAt_eq_returnHitTotal (k : ℕ) :
    EmbeddedChain.returnAt {recurrentControlState} recurrentControlState k
        recurrentControlState =
      EmbeddedChain.returnHitTotal {recurrentControlState} k
        recurrentControlState := by
  rw [← EmbeddedChain.sum_returnAt_eq_returnHitTotal
    {recurrentControlState} k recurrentControlState]
  simp

end

/-! ## Injectivity of the interval coding -/

def inverseT (a : ℕ) (x : ℚ) : ℚ := (x + 1) / a

def inverseWord : List ℕ → ℚ → ℚ
  | [], x => x
  | a :: w, x => inverseT a (inverseWord w x)

def intervalMidpoint (i : Fin 19) : ℚ :=
  (endpoint (leftIndex i) + endpoint (rightIndex i)) / 2

theorem intervalMidpoint_mem (i : Fin 19) : intervalMidpoint i ∈ K i := by
  have h := width_pos i
  simp only [width] at h
  constructor <;> simp only [intervalMidpoint] <;> linarith

/-- Finite certificate saying that every allowed destination lies inside the
image interval of its source. -/
theorem allowed_endpoint_bounds (α : Assignment) (i j : Fin 19)
    (h : allowedNext α i j) :
    T_rat (prescribed α i) (endpoint (leftIndex i)) ≤ endpoint (leftIndex j) ∧
      endpoint (rightIndex j) ≤
        T_rat (prescribed α i) (endpoint (rightIndex i)) := by
  obtain ⟨tr, htr, hrow⟩ := List.any_eq_true.mp h
  have hrow' : tr.source = i ∧ tr.multiplier = prescribed α i ∧
      tr.first ≤ j ∧ j ≤ tr.last := of_decide_eq_true hrow
  rcases hrow' with ⟨hsource, hmultiplier, hfirst, hlast⟩
  have hexact := transitions_exact tr htr
  have hleftIndex : leftIndex tr.first ≤ leftIndex j := by
    simpa [leftIndex] using hfirst
  have hrightIndex : rightIndex j ≤ rightIndex tr.last := by
    simpa [rightIndex] using hlast
  constructor
  · calc
      T_rat (prescribed α i) (endpoint (leftIndex i)) =
          T_rat tr.multiplier (endpoint (leftIndex tr.source)) := by
            rw [hsource, hmultiplier]
      _ = endpoint (leftIndex tr.first) := hexact.2.2.1
      _ ≤ endpoint (leftIndex j) := endpoint_strictMono.monotone hleftIndex
  · calc
      endpoint (rightIndex j) ≤ endpoint (rightIndex tr.last) :=
        endpoint_strictMono.monotone hrightIndex
      _ = T_rat tr.multiplier (endpoint (rightIndex tr.source)) :=
        hexact.2.2.2.symm
      _ = T_rat (prescribed α i) (endpoint (rightIndex i)) := by
        rw [hsource, hmultiplier]

theorem inverseT_mem_of_allowed {α : Assignment} {i j : Fin 19}
    (h : allowedNext α i j) {x : ℚ} (hx : x ∈ K j) :
    inverseT (prescribed α i) x ∈ K i := by
  have ha : (0 : ℚ) < prescribed α i := by
    exact_mod_cast (show 0 < prescribed α i by
      exact (prescribed_ge_two α i).trans' (by omega))
  have hb := allowed_endpoint_bounds α i j h
  simp only [K, Set.mem_Ico] at hx ⊢
  simp only [T_rat] at hb
  constructor
  · apply (le_div_iff₀ ha).2
    linarith [hb.1, hx.1]
  · apply (div_lt_iff₀ ha).2
    linarith [hb.2, hx.2]

theorem mem_K_unique {i j : Fin 19} {x : ℚ}
    (hi : x ∈ K i) (hj : x ∈ K j) : i = j := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hindex : rightIndex i ≤ leftIndex j := by
      apply Fin.mk_le_mk.mpr
      omega
    have hend := endpoint_strictMono.monotone hindex
    simp only [K, Set.mem_Ico] at hi hj
    linarith
  · have hindex : rightIndex j ≤ leftIndex i := by
      apply Fin.mk_le_mk.mpr
      omega
    have hend := endpoint_strictMono.monotone hindex
    simp only [K, Set.mem_Ico] at hi hj
    linarith

namespace IntervalPath

def destinations {i j : Fin 19} : IntervalPath i j → List (Fin 19)
  | .nil _ => []
  | @IntervalPath.cons _ j _ _ _ tail => j :: tail.destinations

def append {i j k : Fin 19} : IntervalPath i j → IntervalPath j k →
    IntervalPath i k
  | .nil _, q => q
  | .cons α h tail, q => .cons α h (tail.append q)

@[simp] theorem word_append {i j k : Fin 19} (p : IntervalPath i j)
    (q : IntervalPath j k) : (p.append q).word = p.word ++ q.word := by
  induction p with
  | nil => rfl
  | cons α h tail ih => simp [append, ih]

@[simp] theorem destinations_append {i j k : Fin 19} (p : IntervalPath i j)
    (q : IntervalPath j k) :
    (p.append q).destinations = p.destinations ++ q.destinations := by
  induction p with
  | nil => rfl
  | cons α h tail ih => simp [append, destinations, ih]

@[simp] theorem mass_append {i j k : Fin 19} (p : IntervalPath i j)
    (q : IntervalPath j k) : (p.append q).mass = p.mass * q.mass := by
  induction p with
  | nil => simp [append, mass]
  | cons α h tail ih => simp [append, ih, mul_assoc]

theorem inverseWord_mem_source {i j : Fin 19} (p : IntervalPath i j)
    {x : ℚ} (hx : x ∈ K j) : inverseWord p.word x ∈ K i := by
  induction p with
  | nil => simpa [inverseWord] using hx
  | @cons i j k α h tail ih =>
      simp only [word_cons, inverseWord]
      exact inverseT_mem_of_allowed h (ih hx)

/-- For fixed endpoints, the multiplier word uniquely determines the entire
sequence of interval destinations.  Assignments themselves are deliberately
ignored here. -/
theorem destinations_eq_of_word_eq {i k : Fin 19} (p q : IntervalPath i k)
    (hword : p.word = q.word) : p.destinations = q.destinations := by
  induction p with
  | nil i =>
      cases q with
      | nil => rfl
      | cons α h tail => simp [word] at hword
  | @cons i j k α h tail ih =>
      cases q with
      | nil => simp [word] at hword
      | @cons _ j' _ β h' tail' =>
          have htail : tail.word = tail'.word := (List.cons.inj hword).2
          let z := inverseWord tail.word (intervalMidpoint k)
          have hzj : z ∈ K j := by
            exact tail.inverseWord_mem_source (intervalMidpoint_mem k)
          have hzj' : z ∈ K j' := by
            dsimp only [z]
            rw [htail]
            exact tail'.inverseWord_mem_source (intervalMidpoint_mem k)
          have hj : j = j' := mem_K_unique hzj hzj'
          subst j'
          simp only [destinations]
          rw [ih tail' htail]

theorem destinations_eq_of_word_eq_of_endpoint_eq {i j k : Fin 19}
    (p : IntervalPath i j) (q : IntervalPath i k) (hend : j = k)
    (hword : p.word = q.word) : p.destinations = q.destinations := by
  cases hend
  exact destinations_eq_of_word_eq p q hword

end IntervalPath

/-! ### Controlled blocks as typed interval paths -/

theorem FiniteChoiceChain.pathWeight_nonneg {S Ω : Type*} [Fintype Ω]
    [DecidableEq S] (K : FiniteChoiceChain S Ω) (n : ℕ) (x : S)
    (w : Fin n → Ω) : 0 ≤ K.pathWeight n x w := by
  induction n generalizing x with
  | zero => simp [FiniteChoiceChain.pathWeight]
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from (Fin.cons_self_tail w).symm,
        K.pathWeight_cons]
      exact mul_nonneg (K.probability_nonneg x (w 0))
        (ih (K.next x (w 0)) (Fin.tail w))

noncomputable def blockIntervalPath (α : Assignment) :
    (n : ℕ) → (i : Fin 19) → (w : Fin n → Fin 19) →
      0 < blockWeight α n i w → IntervalPath i (blockEndpoint n i w)
  | 0, i, _, _ => .nil i
  | n + 1, i, w, hpos => by
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm, blockWeight_cons] at hpos
      have hp0 := probability_nonneg α i (w 0)
      have htail0 := blockWeight_nonneg α n (w 0) (Fin.tail w)
      have hp : 0 < probability α i (w 0) := by nlinarith
      have htail : 0 < blockWeight α n (w 0) (Fin.tail w) := by nlinarith
      have hallowed : allowedNext α i (w 0) := by
        by_contra hnot
        simp [probability, hnot] at hp
      exact .cons α hallowed (blockIntervalPath α n (w 0) (Fin.tail w) htail)

@[simp] theorem blockIntervalPath_word (α : Assignment) (n : ℕ)
    (i : Fin 19) (w : Fin n → Fin 19) (hpos : 0 < blockWeight α n i w) :
    (blockIntervalPath α n i w hpos).word = blockWord α n i w := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp [blockIntervalPath, ih]
      rfl

@[simp] theorem blockIntervalPath_destinations (α : Assignment) (n : ℕ)
    (i : Fin 19) (w : Fin n → Fin 19) (hpos : 0 < blockWeight α n i w) :
    (blockIntervalPath α n i w hpos).destinations = List.ofFn w := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp [blockIntervalPath, IntervalPath.destinations, ih]
      rfl

theorem inverseT_injective {a : ℕ} (ha : 0 < a) :
    Function.Injective (inverseT a) := by
  intro x y h
  simp only [inverseT] at h
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  exact add_right_cancel ((div_left_inj' haQ).mp h)

/-- Inside a block the assignment is fixed.  Consequently, equality of two
pulled-back points forces equality of every interval destination in the
block, even when the terminal points are initially different. -/
theorem blockChoice_eq_of_inverse_eq (α : Assignment) (n : ℕ) (i : Fin 19)
    {u v : Fin n → Fin 19} (hu : 0 < blockWeight α n i u)
    (hv : 0 < blockWeight α n i v) {xu xv : ℚ}
    (hxu : xu ∈ K (blockEndpoint n i u))
    (hxv : xv ∈ K (blockEndpoint n i v))
    (hinv : inverseWord (blockWord α n i u) xu =
      inverseWord (blockWord α n i v) xv) :
    u = v ∧ xu = xv := by
  induction n generalizing i with
  | zero =>
      constructor
      · exact Subsingleton.elim u v
      · simpa [blockWord, inverseWord] using hinv
  | succ n ih =>
      rw [show u = Fin.cons (u 0) (Fin.tail u) from
        (Fin.cons_self_tail u).symm, blockWeight_cons] at hu
      rw [show v = Fin.cons (v 0) (Fin.tail v) from
        (Fin.cons_self_tail v).symm, blockWeight_cons] at hv
      have hpu0 := probability_nonneg α i (u 0)
      have hpv0 := probability_nonneg α i (v 0)
      have htu0 := blockWeight_nonneg α n (u 0) (Fin.tail u)
      have htv0 := blockWeight_nonneg α n (v 0) (Fin.tail v)
      have htu : 0 < blockWeight α n (u 0) (Fin.tail u) := by nlinarith
      have htv : 0 < blockWeight α n (v 0) (Fin.tail v) := by nlinarith
      change xu ∈ K (blockEndpoint n (u 0) (Fin.tail u)) at hxu
      change xv ∈ K (blockEndpoint n (v 0) (Fin.tail v)) at hxv
      have huInner : inverseWord (blockWord α n (u 0) (Fin.tail u)) xu ∈
          K (u 0) := by
        simpa only [blockIntervalPath_word] using
          (blockIntervalPath α n (u 0) (Fin.tail u) htu).inverseWord_mem_source hxu
      have hvInner : inverseWord (blockWord α n (v 0) (Fin.tail v)) xv ∈
          K (v 0) := by
        simpa only [blockIntervalPath_word] using
          (blockIntervalPath α n (v 0) (Fin.tail v) htv).inverseWord_mem_source hxv
      have hinner : inverseWord (blockWord α n (u 0) (Fin.tail u)) xu =
          inverseWord (blockWord α n (v 0) (Fin.tail v)) xv := by
        apply inverseT_injective (show 0 < prescribed α i by
          exact (prescribed_ge_two α i).trans' (by omega))
        simpa [blockWord, inverseWord] using hinv
      have hfirst : u 0 = v 0 := mem_K_unique huInner (hinner ▸ hvInner)
      rw [← hfirst] at htv hxv hinner
      have htail := ih (u 0) htu htv hxu hxv hinner
      constructor
      · rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v]
        exact Fin.cons_inj.mpr ⟨hfirst, htail.1⟩
      · exact htail.2

noncomputable def controlledPathWord :
    (n : ℕ) → AugmentedState → (Fin n → BlockChoice) → List ℕ
  | 0, _, _ => []
  | n + 1, x, w =>
      blockWord (feedback x.2) controlBlockLength x.1 (w 0) ++
        controlledPathWord n (controlledNext x (w 0)) (Fin.tail w)

noncomputable def flattenBlockChoices :
    (n : ℕ) → (Fin n → BlockChoice) → List (Fin 19)
  | 0, _ => []
  | n + 1, w => List.ofFn (w 0) ++ flattenBlockChoices n (Fin.tail w)

theorem flattenBlockChoices_injective (n : ℕ) :
    Function.Injective (flattenBlockChoices n) := by
  induction n with
  | zero =>
      intro u v _
      exact Subsingleton.elim u v
  | succ n ih =>
      intro u v huv
      simp only [flattenBlockChoices] at huv
      have hhead : List.ofFn (u 0) = List.ofFn (v 0) :=
        List.append_inj_left huv (by simp)
      have hzero : u 0 = v 0 := List.ofFn_injective hhead
      have htailList : flattenBlockChoices n (Fin.tail u) =
          flattenBlockChoices n (Fin.tail v) := by
        rw [hzero] at huv
        exact List.append_cancel_left huv
      have htail : Fin.tail u = Fin.tail v := ih htailList
      rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v]
      exact Fin.cons_inj.mpr ⟨hzero, htail⟩

noncomputable def controlledIntervalPath :
    (n : ℕ) → (x : AugmentedState) → (w : Fin n → BlockChoice) →
      0 < controlledChain.pathWeight n x w →
        IntervalPath x.1 (controlledChain.pathEndpoint n x w).1
  | 0, x, _, _ => .nil x.1
  | n + 1, x, w, hpos => by
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm, controlledChain.pathWeight_cons] at hpos
      have hp0 := controlledChain.probability_nonneg x (w 0)
      have ht0 := controlledChain.pathWeight_nonneg n
        (controlledChain.next x (w 0)) (Fin.tail w)
      have hp : 0 < controlledChain.probability x (w 0) := by nlinarith
      have ht : 0 < controlledChain.pathWeight n
          (controlledChain.next x (w 0)) (Fin.tail w) := by nlinarith
      have hpq : 0 < blockWeight (feedback x.2) controlBlockLength x.1 (w 0) := by
        change 0 < (blockWeight (feedback x.2) controlBlockLength x.1 (w 0) : ℝ)
          at hp
        exact_mod_cast hp
      exact (blockIntervalPath (feedback x.2) controlBlockLength x.1 (w 0) hpq).append
        (controlledIntervalPath n (controlledNext x (w 0)) (Fin.tail w) ht)

@[simp] theorem controlledIntervalPath_word (n : ℕ) (x : AugmentedState)
    (w : Fin n → BlockChoice) (hpos : 0 < controlledChain.pathWeight n x w) :
    (controlledIntervalPath n x w hpos).word = controlledPathWord n x w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp [controlledIntervalPath, controlledPathWord, ih]

@[simp] theorem controlledIntervalPath_destinations (n : ℕ)
    (x : AugmentedState) (w : Fin n → BlockChoice)
    (hpos : 0 < controlledChain.pathWeight n x w) :
    (controlledIntervalPath n x w hpos).destinations = flattenBlockChoices n w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp [controlledIntervalPath, flattenBlockChoices, ih]

/-- Positive controlled paths with the same initial and final augmented state
are uniquely determined by their multiplier word. -/
theorem controlledPathWord_injective_of_return (n : ℕ) (x : AugmentedState)
    {u v : Fin n → BlockChoice}
    (hu : 0 < controlledChain.pathWeight n x u)
    (hv : 0 < controlledChain.pathWeight n x v)
    (huend : controlledChain.pathEndpoint n x u = x)
    (hvend : controlledChain.pathEndpoint n x v = x)
    (hword : controlledPathWord n x u = controlledPathWord n x v) :
    u = v := by
  have hend : (controlledChain.pathEndpoint n x u).1 =
      (controlledChain.pathEndpoint n x v).1 := by rw [huend, hvend]
  let pu := controlledIntervalPath n x u hu
  let pv := controlledIntervalPath n x v hv
  have hdest : pu.destinations = pv.destinations := by
    apply IntervalPath.destinations_eq_of_word_eq_of_endpoint_eq pu pv hend
    simpa [pu, pv] using hword
  apply flattenBlockChoices_injective n
  simpa [pu, pv] using hdest

/-! ### Algebra and probability of a positive controlled path -/

theorem exponents_append (u v : List ℕ) (i : Fin 4) :
    exponents (u ++ v) i = exponents u i + exponents v i := by
  simp [exponents]

theorem imbalance_append (u v : List ℕ) :
    imbalance (u ++ v) = fun i ↦ imbalance u i + imbalance v i := by
  funext i
  fin_cases i <;> simp [imbalance, exponents_append] <;> ring

theorem blockWord_mem_multipliers (α : Assignment) (n : ℕ) (i : Fin 19)
    (w : Fin n → Fin 19) : ∀ a ∈ blockWord α n i w, a ∈ multipliers := by
  induction n generalizing i with
  | zero => simp [blockWord]
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm]
      simp only [blockWord_cons, List.mem_cons]
      intro a ha
      rcases ha with rfl | ha
      · exact prescribed_mem_multipliers α i
      · exact ih (w 0) (Fin.tail w) a ha

theorem controlledPathWord_mem_multipliers (n : ℕ) (x : AugmentedState)
    (w : Fin n → BlockChoice) :
    ∀ a ∈ controlledPathWord n x w, a ∈ multipliers := by
  induction n generalizing x with
  | zero => simp [controlledPathWord]
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm]
      simp only [controlledPathWord, List.mem_append]
      intro a ha
      rcases ha with ha | ha
      · exact blockWord_mem_multipliers _ _ _ _ a ha
      · exact ih (controlledNext x (w 0)) (Fin.tail w) a ha

@[simp] theorem blockWord_length (α : Assignment) (n : ℕ) (i : Fin 19)
    (w : Fin n → Fin 19) : (blockWord α n i w).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp [blockWord, ih]

@[simp] theorem controlledPathWord_length (n : ℕ) (x : AugmentedState)
    (w : Fin n → BlockChoice) :
    (controlledPathWord n x w).length = controlBlockLength * n := by
  induction n generalizing x with
  | zero => simp [controlledPathWord]
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm]
      simp only [controlledPathWord, List.length_append, blockWord_length, ih]
      ring

theorem controlledPathWord_imbalance (n : ℕ) (x : AugmentedState)
    (w : Fin n → BlockChoice) :
    imbalance (controlledPathWord n x w) = fun i ↦
      (controlledChain.pathEndpoint n x w).2 i - x.2 i := by
  induction n generalizing x with
  | zero =>
      funext i
      fin_cases i <;> simp [controlledPathWord, FiniteChoiceChain.pathEndpoint,
        imbalance, exponents]
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm]
      rw [controlledPathWord, imbalance_append,
        ← blockIncrement_eq_imbalance]
      rw [ih]
      simp only [FiniteChoiceChain.pathEndpoint_cons, controlledChain,
        controlledNext]
      funext i
      simp only [Fin.cons_zero, Fin.tail_cons]
      ring

@[simp] theorem blockIntervalPath_mass (α : Assignment) (n : ℕ)
    (i : Fin 19) (w : Fin n → Fin 19) (hpos : 0 < blockWeight α n i w) :
    (blockIntervalPath α n i w hpos).mass = blockWeight α n i w := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp [blockIntervalPath, ih]
      rfl

@[simp] theorem controlledIntervalPath_mass_real (n : ℕ) (x : AugmentedState)
    (w : Fin n → BlockChoice) (hpos : 0 < controlledChain.pathWeight n x w) :
    ((controlledIntervalPath n x w hpos).mass : ℝ) =
      controlledChain.pathWeight n x w := by
  induction n generalizing x with
  | zero =>
      norm_num [controlledIntervalPath, IntervalPath.mass,
        FiniteChoiceChain.pathWeight]
  | succ n ih =>
      simp [controlledIntervalPath, IntervalPath.mass_append,
        blockIntervalPath_mass, ih, controlledChain, controlledProbability,
        FiniteChoiceChain.pathWeight]

theorem controlledPathWeight_eq_reciprocal (n : ℕ) (x : AugmentedState)
    (w : Fin n → BlockChoice) (hpos : 0 < controlledChain.pathWeight n x w)
    (hend : controlledChain.pathEndpoint n x w = x) :
    controlledChain.pathWeight n x w =
      1 / (controlledPathWord n x w).prod := by
  let p := controlledIntervalPath n x w hpos
  have hp : p.mass = 1 / (p.word.prod : ℚ) := by
    rw [p.mass_eq_width_div]
    have hwidth : width (controlledChain.pathEndpoint n x w).1 = width x.1 := by
      rw [hend]
    rw [hwidth]
    have hw : width x.1 ≠ 0 := ne_of_gt (width_pos x.1)
    field_simp
  have hpReal : (p.mass : ℝ) = 1 / (p.word.prod : ℝ) := by
    rw [hp]
    simp [Function.comp_def]
  simpa [p] using hpReal

theorem controlledPathWord_imbalance_zero (n : ℕ) (x : AugmentedState)
    (w : Fin n → BlockChoice) (hend : controlledChain.pathEndpoint n x w = x) :
    imbalance (controlledPathWord n x w) = 0 := by
  rw [controlledPathWord_imbalance, hend]
  funext i
  simp

/-! ## Concrete first-return records -/

/-- A first return to the control set, viewed as an explicit tuple of
controlled block choices. -/
abbrev ControlReturnSegment (n : ℕ) (x y : AugmentedState) :=
  {w : Fin n → BlockChoice //
    controlledChain.IsReturnPath controlSet y n x w}

noncomputable instance controlReturnSegmentFintype (n : ℕ)
    (x y : AugmentedState) : Fintype (ControlReturnSegment n x y) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- A concrete realization of a first hit of the recurrent embedded state
after `k` visits to the control set and `n` original controlled blocks. -/
def HoldingHitRecord : ℕ → ℕ → EmbeddedState → Type
  | 0, n, x => ULift {_unit : Unit // n = 0 ∧ x = recurrentControlState}
  | k + 1, n, x =>
      {_guard : Unit // x ≠ recurrentControlState} ×
        Σ p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n},
          Σ y : EmbeddedState,
            ControlReturnSegment p.1.1 x.1.1 y.1.1 ×
              HoldingHitRecord k p.1.2 y

/-- A concrete positive first return to the recurrent embedded state. -/
def RecurrentLoopRecord : ℕ → ℕ → Type
  | 0, _ => Empty
  | k + 1, n =>
      Σ p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n},
        Σ y : EmbeddedState,
          ControlReturnSegment p.1.1 recurrentAugmentedState y.1.1 ×
            HoldingHitRecord k p.1.2 y

noncomputable instance holdingHitRecordFintype (k n : ℕ) (x : EmbeddedState) :
    Fintype (HoldingHitRecord k n x) := by
  classical
  induction k generalizing n x with
  | zero =>
      simp only [HoldingHitRecord]
      letI : Fintype {_unit : Unit // n = 0 ∧ x = recurrentControlState} :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      exact Fintype.ofEquiv _ Equiv.ulift.symm
  | succ k ih =>
      simp only [HoldingHitRecord]
      letI : Fintype {_guard : Unit // x ≠ recurrentControlState} :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      letI (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n})
          (y : EmbeddedState) : Fintype (HoldingHitRecord k p.1.2 y) :=
        ih p.1.2 y
      letI (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n})
          (y : EmbeddedState) :
          Fintype (ControlReturnSegment p.1.1 x.1.1 y.1.1) :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      infer_instance

noncomputable instance recurrentLoopRecordFintype (k n : ℕ) :
    Fintype (RecurrentLoopRecord k n) := by
  classical
  cases k with
  | zero =>
      change Fintype Empty
      exact Fintype.ofFinite Empty
  | succ k =>
      simp only [RecurrentLoopRecord]
      letI (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n})
          (y : EmbeddedState) : Fintype (HoldingHitRecord k p.1.2 y) :=
        holdingHitRecordFintype k p.1.2 y
      letI (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n})
          (y : EmbeddedState) :
          Fintype (ControlReturnSegment p.1.1 recurrentAugmentedState y.1.1) :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      infer_instance

noncomputable def holdingHitRecordWeight :
    {k n : ℕ} → {x : EmbeddedState} → HoldingHitRecord k n x → ℝ
  | 0, _, _, _ => 1
  | _ + 1, _, x, ⟨_, p, _, w, r⟩ =>
      controlledChain.pathWeight p.1.1 x.1.1 w.1 * holdingHitRecordWeight r

noncomputable def recurrentLoopRecordWeight :
    {k n : ℕ} → RecurrentLoopRecord k n → ℝ
  | 0, _, r => r.elim
  | _ + 1, _, ⟨p, _, w, r⟩ =>
      controlledChain.pathWeight p.1.1 recurrentAugmentedState w.1 *
        holdingHitRecordWeight r

noncomputable def holdingHitRecordChoices :
    {k n : ℕ} → {x : EmbeddedState} → HoldingHitRecord k n x → List BlockChoice
  | 0, _, _, _ => []
  | _ + 1, _, _, ⟨_, _, _, w, r⟩ =>
      List.ofFn w.1 ++ holdingHitRecordChoices r

noncomputable def recurrentLoopRecordChoices :
    {k n : ℕ} → RecurrentLoopRecord k n → List BlockChoice
  | 0, _, r => r.elim
  | _ + 1, _, ⟨_, _, w, r⟩ =>
      List.ofFn w.1 ++ holdingHitRecordChoices r

@[simp] theorem holdingHitRecordChoices_length {k n : ℕ} {x : EmbeddedState}
    (r : HoldingHitRecord k n x) :
    (holdingHitRecordChoices (k := k) (n := n) (x := x) r).length = n := by
  induction k generalizing n x with
  | zero =>
      simp only [HoldingHitRecord] at r
      have hn := r.down.2.1
      subst n
      rfl
  | succ k ih =>
      obtain ⟨guard, p, y, w, tail⟩ := r
      simp only [holdingHitRecordChoices, List.length_append, List.length_ofFn,
        ih tail]
      exact Finset.mem_antidiagonal.mp p.2

@[simp] theorem recurrentLoopRecordChoices_length {k n : ℕ}
    (r : RecurrentLoopRecord k n) :
    (recurrentLoopRecordChoices (k := k) (n := n) r).length = n := by
  cases k with
  | zero => exact r.elim
  | succ k =>
      obtain ⟨p, y, w, tail⟩ := r
      simp only [recurrentLoopRecordChoices, List.length_append, List.length_ofFn,
        holdingHitRecordChoices_length]
      exact Finset.mem_antidiagonal.mp p.2

theorem sum_controlReturnSegment_weight (n : ℕ) (x y : AugmentedState) :
    (∑ w : ControlReturnSegment n x y,
      controlledChain.pathWeight n x w.1) =
        controlledChain.returnAt controlSet y n x := by
  classical
  rw [sum_subtype_eq_selected]
  exact controlledChain.sum_returnPath_weight controlSet y n x

theorem sum_holdingHitRecordWeight (k n : ℕ) (x : EmbeddedState) :
    (∑ r : HoldingHitRecord k n x, holdingHitRecordWeight r) =
      holdingHit k n x := by
  classical
  induction k generalizing n x with
  | zero =>
      by_cases h : n = 0 ∧ x = recurrentControlState
      · rcases h with ⟨rfl, rfl⟩
        simp [HoldingHitRecord, holdingHitRecordWeight, holdingHit]
      · letI : IsEmpty (HoldingHitRecord 0 n x) :=
          ⟨fun r ↦ h r.down.2⟩
        rw [show holdingHit 0 n x = 0 by simp [holdingHit, h]]
        apply Finset.sum_eq_zero
        intro r _
        exact isEmptyElim r
  | succ k ih =>
      by_cases hx : x = recurrentControlState
      · subst x
        letI : IsEmpty (HoldingHitRecord (k + 1) n recurrentControlState) :=
          ⟨fun r ↦ r.1.2 rfl⟩
        rw [show holdingHit (k + 1) n recurrentControlState = 0 by
          simp [holdingHit]]
        apply Finset.sum_eq_zero
        intro r _
        exact isEmptyElim r
      · letI : Fintype {_guard : Unit // x ≠ recurrentControlState} :=
          Fintype.ofInjective Subtype.val Subtype.val_injective
        letI (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n})
            (y : EmbeddedState) : Fintype (HoldingHitRecord k p.1.2 y) :=
          holdingHitRecordFintype k p.1.2 y
        letI (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n})
            (y : EmbeddedState) :
            Fintype (ControlReturnSegment p.1.1 x.1.1 y.1.1) :=
          Fintype.ofInjective Subtype.val Subtype.val_injective
        simp only [HoldingHitRecord]
        rw [Fintype.sum_prod_type]
        simp only [holdingHitRecordWeight]
        simp_rw [Fintype.sum_sigma, Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, ih]
        simp_rw [← Finset.sum_mul, sum_controlReturnSegment_weight]
        rw [show (∑ _guard : {_guard : Unit // x ≠ recurrentControlState},
            ∑ p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n},
              ∑ y : EmbeddedState,
                controlledChain.returnAt controlSet y.1.1 p.1.1 x.1.1 *
                  holdingHit k p.1.2 y) =
            ∑ p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n},
              ∑ y : EmbeddedState,
                controlledChain.returnAt controlSet y.1.1 p.1.1 x.1.1 *
                  holdingHit k p.1.2 y by simp [hx]]
        rw [sum_subtype_eq_sum_attach]
        rw [Finset.sum_comm]
        simp only [holdingHit, hx, if_false, convolution]
        apply Finset.sum_congr rfl
        intro y _
        simpa using Finset.sum_attach (Finset.antidiagonal n)
          (fun p ↦ controlledChain.returnAt controlSet y.1.1 p.1 x.1.1 *
            holdingHit k p.2 y)

theorem sum_recurrentLoopRecordWeight (k n : ℕ) :
    (∑ r : RecurrentLoopRecord k n, recurrentLoopRecordWeight r) =
      holdingReturn k n := by
  classical
  cases k with
  | zero =>
      simp [RecurrentLoopRecord, recurrentLoopRecordWeight, holdingReturn]
  | succ k =>
      letI (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n})
          (y : EmbeddedState) : Fintype (HoldingHitRecord k p.1.2 y) :=
        holdingHitRecordFintype k p.1.2 y
      letI (p : {p : ℕ × ℕ // p ∈ Finset.antidiagonal n})
          (y : EmbeddedState) :
          Fintype (ControlReturnSegment p.1.1 recurrentAugmentedState y.1.1) :=
        Fintype.ofInjective Subtype.val Subtype.val_injective
      simp only [RecurrentLoopRecord]
      rw [Fintype.sum_sigma]
      simp_rw [Fintype.sum_sigma, Fintype.sum_prod_type]
      simp only [recurrentLoopRecordWeight]
      simp_rw [← Finset.mul_sum, sum_holdingHitRecordWeight]
      simp_rw [← Finset.sum_mul, sum_controlReturnSegment_weight]
      rw [sum_subtype_eq_sum_attach, Finset.sum_comm]
      simp only [holdingReturn, convolution]
      apply Finset.sum_congr rfl
      intro y _
      simpa using Finset.sum_attach (Finset.antidiagonal n)
        (fun p ↦ controlledChain.returnAt controlSet y.1.1 p.1
          recurrentAugmentedState * holdingHit k p.2 y)

/-! ### Flat finite-choice lists -/

namespace FiniteChoiceChain

def listEndpoint {S Ω : Type*} [Fintype Ω] (K : FiniteChoiceChain S Ω) :
    S → List Ω → S
  | x, [] => x
  | x, a :: w => K.listEndpoint (K.next x a) w

def listWeight {S Ω : Type*} [Fintype Ω] (K : FiniteChoiceChain S Ω) :
    S → List Ω → ℝ
  | _, [] => 1
  | x, a :: w => K.probability x a * K.listWeight (K.next x a) w

theorem listEndpoint_append {S Ω : Type*} [Fintype Ω]
    (K : FiniteChoiceChain S Ω) (x : S) (u v : List Ω) :
    K.listEndpoint x (u ++ v) = K.listEndpoint (K.listEndpoint x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => exact ih (K.next x a)

theorem listWeight_append {S Ω : Type*} [Fintype Ω]
    (K : FiniteChoiceChain S Ω) (x : S) (u v : List Ω) :
    K.listWeight x (u ++ v) =
      K.listWeight x u * K.listWeight (K.listEndpoint x u) v := by
  induction u generalizing x with
  | nil => simp [listWeight, listEndpoint]
  | cons a u ih =>
      simp only [List.cons_append, listWeight, listEndpoint, ih]
      ring

theorem listWeight_nonneg {S Ω : Type*} [Fintype Ω]
    (K : FiniteChoiceChain S Ω) (x : S) (u : List Ω) :
    0 ≤ K.listWeight x u := by
  induction u generalizing x with
  | nil => simp [listWeight]
  | cons a u ih =>
      exact mul_nonneg (K.probability_nonneg x a) (ih (K.next x a))

def IsHitList {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S) : S → List Ω → Prop
  | x, [] => x ∈ C ∧ x = y
  | x, a :: w => x ∉ C ∧ K.IsHitList C y (K.next x a) w

def IsReturnList {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S) : S → List Ω → Prop
  | _, [] => False
  | x, a :: w => K.IsHitList C y (K.next x a) w

theorem listEndpoint_ofFn {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (n : ℕ) (x : S) (w : Fin n → Ω) :
    K.listEndpoint x (List.ofFn w) = K.pathEndpoint n x w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, listEndpoint, ih]
      simpa only [Fin.cons_self_tail] using
        (K.pathEndpoint_cons n x (w 0) (Fin.tail w)).symm

theorem listWeight_ofFn {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (n : ℕ) (x : S) (w : Fin n → Ω) :
    K.listWeight x (List.ofFn w) = K.pathWeight n x w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, listWeight, ih]
      simpa only [Fin.cons_self_tail] using
        (K.pathWeight_cons n x (w 0) (Fin.tail w)).symm

theorem isHitList_of_isHitPath {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S) (n : ℕ)
    (x : S) (w : Fin n → Ω) (h : K.IsHitPath C y n x w) :
    K.IsHitList C y x (List.ofFn w) := by
  induction n generalizing x with
  | zero => simpa [IsHitList] using h
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm] at h
      rw [List.ofFn_succ]
      change x ∉ C ∧ K.IsHitList C y (K.next x (w 0))
        (List.ofFn (Fin.tail w))
      exact ⟨h.1, ih _ _ h.2⟩

theorem isReturnList_of_isReturnPath {S Ω : Type*} [Fintype Ω]
    [DecidableEq S] (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S)
    (n : ℕ) (x : S) (w : Fin n → Ω) (h : K.IsReturnPath C y n x w) :
    K.IsReturnList C y x (List.ofFn w) := by
  cases n with
  | zero => exact (K.isReturnPath_zero C x y w h).elim
  | succ n =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm] at h
      rw [List.ofFn_succ]
      change K.IsHitList C y (K.next x (w 0))
        (List.ofFn (Fin.tail w))
      exact K.isHitList_of_isHitPath C y n _ _ h

theorem isReturnPath_length_pos {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (y : S) (n : ℕ)
    (x : S) (w : Fin n → Ω) (h : K.IsReturnPath C y n x w) : 0 < n := by
  cases n with
  | zero => exact (K.isReturnPath_zero C x y w h).elim
  | succ n => omega

theorem isHitList_endpoint {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (y x : S) (w : List Ω)
    (h : K.IsHitList C y x w) : K.listEndpoint x w = y := by
  induction w generalizing x with
  | nil => exact h.2
  | cons a w ih => exact ih _ h.2

theorem isReturnList_endpoint {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (y x : S) (w : List Ω)
    (h : K.IsReturnList C y x w) : K.listEndpoint x w = y := by
  cases w with
  | nil => exact h.elim
  | cons a w => exact K.isHitList_endpoint C y _ w h

/-- Two first-hit prefixes of one common choice list have the same cut point. -/
theorem isHitList_append_unique {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) {x y z : S}
    {u v r s : List Ω} (hu : K.IsHitList C y x u)
    (hv : K.IsHitList C z x v) (happend : u ++ r = v ++ s) :
    u = v ∧ r = s := by
  induction u generalizing x v with
  | nil =>
      cases v with
      | nil => exact ⟨rfl, happend⟩
      | cons b v => exact (hv.1 hu.1).elim
  | cons a u ih =>
      cases v with
      | nil => exact (hu.1 hv.1).elim
      | cons b v =>
          have hab : a = b := (List.cons.inj happend).1
          subst b
          have h := ih hu.2 hv.2 (List.cons.inj happend).2
          exact ⟨congrArg (List.cons a) h.1, h.2⟩

theorem isReturnList_append_unique {S Ω : Type*} [Fintype Ω]
    [DecidableEq S] (K : FiniteChoiceChain S Ω) (C : Finset S)
    {x y z : S} {u v r s : List Ω} (hu : K.IsReturnList C y x u)
    (hv : K.IsReturnList C z x v) (happend : u ++ r = v ++ s) :
    u = v ∧ r = s := by
  cases u with
  | nil => exact hu.elim
  | cons a u =>
      cases v with
      | nil => exact hv.elim
      | cons b v =>
          have hab : a = b := (List.cons.inj happend).1
          subst b
          have htail := (List.cons.inj happend).2
          have h := K.isHitList_append_unique C hu hv htail
          exact ⟨congrArg (List.cons a) h.1, h.2⟩

end FiniteChoiceChain

noncomputable def controlledListWord : AugmentedState → List BlockChoice → List ℕ
  | _, [] => []
  | x, w :: tail =>
      blockWord (feedback x.2) controlBlockLength x.1 w ++
        controlledListWord (controlledNext x w) tail

theorem controlledListWord_ofFn (n : ℕ) (x : AugmentedState)
    (w : Fin n → BlockChoice) :
    controlledListWord x (List.ofFn w) = controlledPathWord n x w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [show w = Fin.cons (w 0) (Fin.tail w) from
        (Fin.cons_self_tail w).symm]
      simp [controlledListWord, controlledPathWord, ih]
      rfl

theorem holdingHitRecordWeight_eq_listWeight {k n : ℕ} {x : EmbeddedState}
    (r : HoldingHitRecord k n x) :
    holdingHitRecordWeight r =
      controlledChain.listWeight x.1.1
        (holdingHitRecordChoices (k := k) (n := n) (x := x) r) := by
  induction k generalizing n x with
  | zero =>
      simp only [HoldingHitRecord] at r
      have hn := r.down.2.1
      subst n
      rfl
  | succ k ih =>
      obtain ⟨guard, p, y, w, tail⟩ := r
      simp only [holdingHitRecordWeight, holdingHitRecordChoices]
      rw [controlledChain.listWeight_append,
        controlledChain.listWeight_ofFn]
      have hw := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 x.1.1 w.1 w.2
      rw [controlledChain.isReturnList_endpoint controlSet y.1.1 x.1.1
        (List.ofFn w.1) hw, ← ih tail]

theorem recurrentLoopRecordWeight_eq_listWeight {k n : ℕ}
    (r : RecurrentLoopRecord k n) :
    recurrentLoopRecordWeight r = controlledChain.listWeight
      recurrentAugmentedState
        (recurrentLoopRecordChoices (k := k) (n := n) r) := by
  cases k with
  | zero => exact r.elim
  | succ k =>
      obtain ⟨p, y, w, tail⟩ := r
      simp only [recurrentLoopRecordWeight, recurrentLoopRecordChoices]
      rw [controlledChain.listWeight_append,
        controlledChain.listWeight_ofFn]
      have hw := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 recurrentAugmentedState w.1 w.2
      rw [controlledChain.isReturnList_endpoint controlSet y.1.1
        recurrentAugmentedState (List.ofFn w.1) hw,
        ← holdingHitRecordWeight_eq_listWeight tail]

theorem holdingHitRecord_endpoint {k n : ℕ} {x : EmbeddedState}
    (r : HoldingHitRecord k n x) : controlledChain.listEndpoint x.1.1
      (holdingHitRecordChoices (k := k) (n := n) (x := x) r) =
        recurrentAugmentedState := by
  induction k generalizing n x with
  | zero =>
      simp only [HoldingHitRecord] at r
      have hx := r.down.2.2
      subst x
      rfl
  | succ k ih =>
      obtain ⟨guard, p, y, w, tail⟩ := r
      rw [holdingHitRecordChoices, controlledChain.listEndpoint_append]
      have hw := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 x.1.1 w.1 w.2
      rw [controlledChain.isReturnList_endpoint controlSet y.1.1 x.1.1
        (List.ofFn w.1) hw]
      exact ih tail

theorem recurrentLoopRecord_endpoint {k n : ℕ}
    (r : RecurrentLoopRecord k n) : controlledChain.listEndpoint
      recurrentAugmentedState
        (recurrentLoopRecordChoices (k := k) (n := n) r) =
        recurrentAugmentedState := by
  cases k with
  | zero => exact r.elim
  | succ k =>
      obtain ⟨p, y, w, tail⟩ := r
      rw [recurrentLoopRecordChoices, controlledChain.listEndpoint_append]
      have hw := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 recurrentAugmentedState w.1 w.2
      rw [controlledChain.isReturnList_endpoint controlSet y.1.1
        recurrentAugmentedState (List.ofFn w.1) hw]
      exact holdingHitRecord_endpoint tail

theorem holdingHitRecordChoices_injective (k n : ℕ) (x : EmbeddedState) :
    Function.Injective (holdingHitRecordChoices :
      HoldingHitRecord k n x → List BlockChoice) := by
  induction k generalizing n x with
  | zero =>
      intro r s _
      simp only [HoldingHitRecord] at r s
      apply ULift.ext
      apply Subtype.ext
      exact Subsingleton.elim _ _
  | succ k ih =>
      intro r s hrs
      obtain ⟨gr, p, y, w, tail⟩ := r
      obtain ⟨gs, q, z, v, tail'⟩ := s
      simp only [holdingHitRecordChoices] at hrs
      have hwret := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 x.1.1 w.1 w.2
      have hvret := controlledChain.isReturnList_of_isReturnPath controlSet z.1.1
        q.1.1 x.1.1 v.1 v.2
      have hsplit := controlledChain.isReturnList_append_unique controlSet
        hwret hvret hrs
      have hlen : p.1.1 = q.1.1 := by
        simpa using congrArg List.length hsplit.1
      have hpSum := Finset.mem_antidiagonal.mp p.2
      have hqSum := Finset.mem_antidiagonal.mp q.2
      have hrest : p.1.2 = q.1.2 := by omega
      have hpval : p.1 = q.1 := Prod.ext hlen hrest
      have hp : p = q := Subtype.ext hpval
      subst q
      have hwval : w.1 = v.1 := List.ofFn_injective hsplit.1
      have hyval : y.1.1 = z.1.1 := by
        have hyend := controlledChain.isReturnList_endpoint controlSet y.1.1
          x.1.1 (List.ofFn w.1) hwret
        have hzend := controlledChain.isReturnList_endpoint controlSet z.1.1
          x.1.1 (List.ofFn v.1) hvret
        rw [hsplit.1] at hyend
        exact hyend.symm.trans hzend
      have hy : y = z := by
        apply Subtype.ext
        apply Subtype.ext
        exact hyval
      subst z
      have hw : w = v := Subtype.ext hwval
      subst v
      have ht : tail = tail' := ih p.1.2 y hsplit.2
      subst tail'
      have hg : gr = gs := Subsingleton.elim gr gs
      subst gs
      rfl

theorem recurrentLoopRecordChoices_injective (k n : ℕ) :
    Function.Injective (recurrentLoopRecordChoices :
      RecurrentLoopRecord k n → List BlockChoice) := by
  cases k with
  | zero =>
      intro r
      exact r.elim
  | succ k =>
      intro r s hrs
      obtain ⟨p, y, w, tail⟩ := r
      obtain ⟨q, z, v, tail'⟩ := s
      simp only [recurrentLoopRecordChoices] at hrs
      have hwret := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 recurrentAugmentedState w.1 w.2
      have hvret := controlledChain.isReturnList_of_isReturnPath controlSet z.1.1
        q.1.1 recurrentAugmentedState v.1 v.2
      have hsplit := controlledChain.isReturnList_append_unique controlSet
        hwret hvret hrs
      have hlen : p.1.1 = q.1.1 := by
        simpa using congrArg List.length hsplit.1
      have hpSum := Finset.mem_antidiagonal.mp p.2
      have hqSum := Finset.mem_antidiagonal.mp q.2
      have hrest : p.1.2 = q.1.2 := by omega
      have hpval : p.1 = q.1 := Prod.ext hlen hrest
      have hp : p = q := Subtype.ext hpval
      subst q
      have hwval : w.1 = v.1 := List.ofFn_injective hsplit.1
      have hyval : y.1.1 = z.1.1 := by
        have hyend := controlledChain.isReturnList_endpoint controlSet y.1.1
          recurrentAugmentedState (List.ofFn w.1) hwret
        have hzend := controlledChain.isReturnList_endpoint controlSet z.1.1
          recurrentAugmentedState (List.ofFn v.1) hvret
        rw [hsplit.1] at hyend
        exact hyend.symm.trans hzend
      have hy : y = z := by
        apply Subtype.ext
        apply Subtype.ext
        exact hyval
      subst z
      have hw : w = v := Subtype.ext hwval
      subst v
      have ht : tail = tail' := holdingHitRecordChoices_injective k p.1.2 y hsplit.2
      subst tail'
      rfl

/-! ### The controlled word carried by a loop record -/

noncomputable def recurrentLoopRecordTuple {k n : ℕ}
    (r : RecurrentLoopRecord k n) : Fin n → BlockChoice := fun i ↦
  (recurrentLoopRecordChoices (k := k) (n := n) r).get
    (Fin.cast (recurrentLoopRecordChoices_length r).symm i)

@[simp] theorem ofFn_recurrentLoopRecordTuple {k n : ℕ}
    (r : RecurrentLoopRecord k n) :
    List.ofFn (recurrentLoopRecordTuple r) =
      recurrentLoopRecordChoices (k := k) (n := n) r := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp [recurrentLoopRecordTuple]

noncomputable def recurrentLoopRecordWord {k n : ℕ}
    (r : RecurrentLoopRecord k n) : List ℕ :=
  controlledListWord recurrentAugmentedState
    (recurrentLoopRecordChoices (k := k) (n := n) r)

@[simp] theorem recurrentLoopRecordWord_eq_controlledPathWord {k n : ℕ}
    (r : RecurrentLoopRecord k n) : recurrentLoopRecordWord r =
      controlledPathWord n recurrentAugmentedState
        (recurrentLoopRecordTuple r) := by
  rw [recurrentLoopRecordWord, ← controlledListWord_ofFn,
    ofFn_recurrentLoopRecordTuple]

theorem recurrentLoopRecord_pathEndpoint {k n : ℕ}
    (r : RecurrentLoopRecord k n) :
    controlledChain.pathEndpoint n recurrentAugmentedState
      (recurrentLoopRecordTuple r) = recurrentAugmentedState := by
  rw [← controlledChain.listEndpoint_ofFn, ofFn_recurrentLoopRecordTuple]
  exact recurrentLoopRecord_endpoint r

theorem recurrentLoopRecordWeight_eq_pathWeight {k n : ℕ}
    (r : RecurrentLoopRecord k n) : recurrentLoopRecordWeight r =
      controlledChain.pathWeight n recurrentAugmentedState
        (recurrentLoopRecordTuple r) := by
  rw [recurrentLoopRecordWeight_eq_listWeight,
    ← controlledChain.listWeight_ofFn, ofFn_recurrentLoopRecordTuple]

theorem recurrentLoopRecordWeight_nonneg {k n : ℕ}
    (r : RecurrentLoopRecord k n) : 0 ≤ recurrentLoopRecordWeight r := by
  rw [recurrentLoopRecordWeight_eq_listWeight]
  exact controlledChain.listWeight_nonneg _ _

theorem recurrentLoopRecordWord_mem_multipliers {k n : ℕ}
    (r : RecurrentLoopRecord k n) :
    ∀ a ∈ recurrentLoopRecordWord r, a ∈ multipliers := by
  rw [recurrentLoopRecordWord_eq_controlledPathWord]
  exact controlledPathWord_mem_multipliers n recurrentAugmentedState
    (recurrentLoopRecordTuple r)

@[simp] theorem recurrentLoopRecordWord_length {k n : ℕ}
    (r : RecurrentLoopRecord k n) :
    (recurrentLoopRecordWord r).length = controlBlockLength * n := by
  rw [recurrentLoopRecordWord_eq_controlledPathWord,
    controlledPathWord_length]

theorem recurrentLoopRecord_imbalance_zero {k n : ℕ}
    (r : RecurrentLoopRecord k n) : imbalance (recurrentLoopRecordWord r) = 0 := by
  rw [recurrentLoopRecordWord_eq_controlledPathWord]
  exact controlledPathWord_imbalance_zero n recurrentAugmentedState
    (recurrentLoopRecordTuple r) (recurrentLoopRecord_pathEndpoint r)

theorem recurrentLoopRecordWeight_eq_reciprocal {k n : ℕ}
    (r : RecurrentLoopRecord k n) (hpos : 0 < recurrentLoopRecordWeight r) :
    recurrentLoopRecordWeight r = 1 / ((recurrentLoopRecordWord r).prod : ℝ) := by
  rw [recurrentLoopRecordWeight_eq_pathWeight] at hpos ⊢
  rw [recurrentLoopRecordWord_eq_controlledPathWord]
  exact controlledPathWeight_eq_reciprocal n recurrentAugmentedState
    (recurrentLoopRecordTuple r) hpos (recurrentLoopRecord_pathEndpoint r)

theorem recurrentLoopRecord_blockLength_pos {k n : ℕ}
    (r : RecurrentLoopRecord k n) : 0 < n := by
  cases k with
  | zero => exact r.elim
  | succ k =>
      obtain ⟨p, y, w, tail⟩ := r
      have hp : 0 < p.1.1 :=
        controlledChain.isReturnPath_length_pos controlSet y.1.1 p.1.1
          recurrentAugmentedState w.1 w.2
      have hsum := Finset.mem_antidiagonal.mp p.2
      omega

theorem recurrentLoopRecordWord_ne_nil {k n : ℕ}
    (r : RecurrentLoopRecord k n) : recurrentLoopRecordWord r ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp only [recurrentLoopRecordWord_length, List.length_nil] at hlen
  have hN := controlBlockLength_pos
  have hn := recurrentLoopRecord_blockLength_pos r
  have hprod : 0 < controlBlockLength * n := Nat.mul_pos hN hn
  omega

noncomputable def recurrentLoopReward {k n : ℕ}
    (r : RecurrentLoopRecord k n) : ℕ :=
  exponents (recurrentLoopRecordWord r) 3

theorem recurrentLoopRecord_prod_eq_q_pow {k n : ℕ}
    (r : RecurrentLoopRecord k n) :
    (recurrentLoopRecordWord r).prod = q ^ recurrentLoopReward r := by
  exact prod_eq_q_pow_of_imbalance_eq_zero (recurrentLoopRecordWord r)
    (recurrentLoopRecordWord_mem_multipliers r)
    (recurrentLoopRecord_imbalance_zero r)

theorem prod_two_le_of_ne_nil {w : List ℕ} (hne : w ≠ [])
    (htwo : ∀ a ∈ w, 2 ≤ a) : 2 ≤ w.prod := by
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha := htwo a (by simp)
  have htail : 1 ≤ tail.prod := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply List.prod_ne_zero
    intro hzero
    have hb2 := htwo 0 (by simp [hzero])
    omega
  simp only [List.prod_cons]
  nlinarith

theorem recurrentLoopReward_pos {k n : ℕ} (r : RecurrentLoopRecord k n) :
    0 < recurrentLoopReward r := by
  by_contra hnot
  have hz : recurrentLoopReward r = 0 := Nat.eq_zero_of_not_pos hnot
  have hprod := recurrentLoopRecord_prod_eq_q_pow r
  rw [hz, pow_zero] at hprod
  have htwo : ∀ a ∈ recurrentLoopRecordWord r, 2 ≤ a := by
    intro a ha
    exact mem_multipliers_two_le (recurrentLoopRecordWord_mem_multipliers r a ha)
  have := prod_two_le_of_ne_nil (recurrentLoopRecordWord_ne_nil r) htwo
  omega

theorem recurrentLoopRecordWeight_eq_q_reward {k n : ℕ}
    (r : RecurrentLoopRecord k n) (hpos : 0 < recurrentLoopRecordWeight r) :
    recurrentLoopRecordWeight r = 1 / (q ^ recurrentLoopReward r : ℕ) := by
  rw [recurrentLoopRecordWeight_eq_reciprocal r hpos,
    recurrentLoopRecord_prod_eq_q_pow]

/-! ### Recovering the number of embedded visits from the flat path -/

namespace FiniteChoiceChain

def listVisitCount {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) : S → List Ω → ℕ
  | _, [] => 0
  | x, a :: w => (if K.next x a ∈ C then 1 else 0) +
      K.listVisitCount C (K.next x a) w

theorem listVisitCount_append {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (x : S)
    (u v : List Ω) : K.listVisitCount C x (u ++ v) =
      K.listVisitCount C x u +
        K.listVisitCount C (K.listEndpoint x u) v := by
  induction u generalizing x with
  | nil => simp [listVisitCount, listEndpoint]
  | cons a u ih =>
      simp only [List.cons_append, listVisitCount, listEndpoint, ih]
      omega

theorem isHitList_visitCount {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (y x : S) (w : List Ω)
    (h : K.IsHitList C y x w) :
    K.listVisitCount C x w = if x ∈ C then 0 else 1 := by
  cases w with
  | nil => simp [listVisitCount, h.1]
  | cons a w =>
      have hx : x ∉ C := h.1
      have ih := K.isHitList_visitCount C y (K.next x a) w h.2
      simp only [listVisitCount, hx, if_false]
      by_cases hn : K.next x a ∈ C <;> simp [hn] at ih ⊢ <;> omega
termination_by w.length

theorem isReturnList_visitCount {S Ω : Type*} [Fintype Ω] [DecidableEq S]
    (K : FiniteChoiceChain S Ω) (C : Finset S) (y x : S) (w : List Ω)
    (h : K.IsReturnList C y x w) : K.listVisitCount C x w = 1 := by
  cases w with
  | nil => exact h.elim
  | cons a w =>
      have ih := K.isHitList_visitCount C y (K.next x a) w h
      simp only [listVisitCount]
      by_cases hn : K.next x a ∈ C <;> simp [hn] at ih ⊢ <;> omega

end FiniteChoiceChain

theorem holdingHitRecord_visitCount {k n : ℕ} {x : EmbeddedState}
    (r : HoldingHitRecord k n x) : controlledChain.listVisitCount controlSet
      x.1.1 (holdingHitRecordChoices (k := k) (n := n) (x := x) r) = k := by
  induction k generalizing n x with
  | zero => simp [holdingHitRecordChoices,
      FiniteChoiceChain.listVisitCount]
  | succ k ih =>
      obtain ⟨guard, p, y, w, tail⟩ := r
      rw [holdingHitRecordChoices, controlledChain.listVisitCount_append]
      have hw := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 x.1.1 w.1 w.2
      rw [controlledChain.isReturnList_visitCount controlSet y.1.1 x.1.1
        (List.ofFn w.1) hw]
      rw [controlledChain.isReturnList_endpoint controlSet y.1.1 x.1.1
        (List.ofFn w.1) hw, ih tail]
      omega

theorem recurrentLoopRecord_visitCount {k n : ℕ}
    (r : RecurrentLoopRecord k n) : controlledChain.listVisitCount controlSet
      recurrentAugmentedState
        (recurrentLoopRecordChoices (k := k) (n := n) r) = k := by
  cases k with
  | zero => exact r.elim
  | succ k =>
      obtain ⟨p, y, w, tail⟩ := r
      rw [recurrentLoopRecordChoices, controlledChain.listVisitCount_append]
      have hw := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 recurrentAugmentedState w.1 w.2
      rw [controlledChain.isReturnList_visitCount controlSet y.1.1
        recurrentAugmentedState (List.ofFn w.1) hw]
      rw [controlledChain.isReturnList_endpoint controlSet y.1.1
        recurrentAugmentedState (List.ofFn w.1) hw,
        holdingHitRecord_visitCount tail]
      omega

/-- A loop record is determined globally by its flat choice list, including
its two duration indices. -/
theorem recurrentLoopRecord_sigma_choices_injective :
    Function.Injective (fun r : Σ k : ℕ, Σ n : ℕ, RecurrentLoopRecord k n ↦
      recurrentLoopRecordChoices (k := r.1) (n := r.2.1) r.2.2) := by
  intro r s hrs
  obtain ⟨k, n, r⟩ := r
  obtain ⟨l, m, s⟩ := s
  have hnm : n = m := by
    simpa using congrArg List.length hrs
  subst m
  have hkl : k = l := by
    have hr := recurrentLoopRecord_visitCount r
    have hs := recurrentLoopRecord_visitCount s
    change recurrentLoopRecordChoices r = recurrentLoopRecordChoices s at hrs
    rw [hrs] at hr
    omega
  subst l
  have hrs' : r = s := recurrentLoopRecordChoices_injective k n hrs
  subst s
  rfl

/-! ### First-return status with respect to the recurrent base itself -/

namespace FiniteChoiceChain

theorem isHitList_append_of_subset {S Ω : Type*} [Fintype Ω]
    [DecidableEq S] (K : FiniteChoiceChain S Ω) {B C : Finset S}
    (hBC : B ⊆ C) {x y z : S} {u v : List Ω}
    (hu : K.IsHitList C y x u) (hv : K.IsHitList B z y v) :
    K.IsHitList B z x (u ++ v) := by
  induction u generalizing x with
  | nil =>
      have hxy := hu.2
      subst x
      exact hv
  | cons a u ih =>
      have hxB : x ∉ B := fun hx ↦ hu.1 (hBC hx)
      exact ⟨hxB, ih hu.2⟩

theorem isReturnList_append_hit_of_subset {S Ω : Type*} [Fintype Ω]
    [DecidableEq S] (K : FiniteChoiceChain S Ω) {B C : Finset S}
    (hBC : B ⊆ C) {x y z : S} {u v : List Ω}
    (hu : K.IsReturnList C y x u) (hv : K.IsHitList B z y v) :
    K.IsReturnList B z x (u ++ v) := by
  cases u with
  | nil => exact hu.elim
  | cons a u =>
      exact K.isHitList_append_of_subset hBC hu hv

theorem isHitList_of_returnList_of_not_mem {S Ω : Type*} [Fintype Ω]
    [DecidableEq S] (K : FiniteChoiceChain S Ω) (B : Finset S)
    {x y : S} {u : List Ω} (hx : x ∉ B) (hu : K.IsReturnList B y x u) :
    K.IsHitList B y x u := by
  cases u with
  | nil => exact hu.elim
  | cons a u => exact ⟨hx, hu⟩

end FiniteChoiceChain

theorem holdingHitRecord_isHitBase {k n : ℕ} {x : EmbeddedState}
    (r : HoldingHitRecord k n x) : controlledChain.IsHitList
      {recurrentAugmentedState} recurrentAugmentedState x.1.1
        (holdingHitRecordChoices (k := k) (n := n) (x := x) r) := by
  induction k generalizing n x with
  | zero =>
      simp only [HoldingHitRecord] at r
      have hn := r.down.2.1
      have hx := r.down.2.2
      subst n
      subst x
      change recurrentAugmentedState ∈ ({recurrentAugmentedState} :
        Finset AugmentedState) ∧ recurrentAugmentedState = recurrentAugmentedState
      simp
  | succ k ih =>
      obtain ⟨guard, p, y, w, tail⟩ := r
      have hseg := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 x.1.1 w.1 w.2
      have hsub : ({recurrentAugmentedState} : Finset AugmentedState) ⊆
          controlSet := by
        intro z hz
        simp only [Finset.mem_singleton] at hz
        subst z
        exact recurrentAugmentedState_mem
      have hreturn := controlledChain.isReturnList_append_hit_of_subset hsub
        hseg (ih tail)
      have hx : x.1.1 ∉ ({recurrentAugmentedState} : Finset AugmentedState) := by
        simp only [Finset.mem_singleton]
        intro heq
        apply guard.2
        apply Subtype.ext
        apply Subtype.ext
        exact heq
      exact controlledChain.isHitList_of_returnList_of_not_mem
        {recurrentAugmentedState} hx hreturn

theorem recurrentLoopRecord_isReturnBase {k n : ℕ}
    (r : RecurrentLoopRecord k n) : controlledChain.IsReturnList
      {recurrentAugmentedState} recurrentAugmentedState recurrentAugmentedState
        (recurrentLoopRecordChoices (k := k) (n := n) r) := by
  cases k with
  | zero => exact r.elim
  | succ k =>
      obtain ⟨p, y, w, tail⟩ := r
      have hseg := controlledChain.isReturnList_of_isReturnPath controlSet y.1.1
        p.1.1 recurrentAugmentedState w.1 w.2
      have hsub : ({recurrentAugmentedState} : Finset AugmentedState) ⊆
          controlSet := by
        intro z hz
        simp only [Finset.mem_singleton] at hz
        subst z
        exact recurrentAugmentedState_mem
      exact controlledChain.isReturnList_append_hit_of_subset hsub hseg
        (holdingHitRecord_isHitBase tail)

/-! ## The first-return reward distribution -/

abbrev FirstReturnLoop := Σ k : ℕ, Σ n : ℕ, RecurrentLoopRecord k n

noncomputable def firstReturnLoopWeight (r : FirstReturnLoop) : ℝ :=
  recurrentLoopRecordWeight r.2.2

noncomputable def firstReturnLoopWord (r : FirstReturnLoop) : List ℕ :=
  recurrentLoopRecordWord r.2.2

noncomputable def firstReturnLoopReward (r : FirstReturnLoop) : ℕ :=
  recurrentLoopReward r.2.2

theorem firstReturnLoopWeight_nonneg (r : FirstReturnLoop) :
    0 ≤ firstReturnLoopWeight r :=
  recurrentLoopRecordWeight_nonneg r.2.2

theorem firstReturnLoopReward_pos (r : FirstReturnLoop) :
    0 < firstReturnLoopReward r := recurrentLoopReward_pos r.2.2

theorem firstReturnLoopWeight_eq_q_reward (r : FirstReturnLoop)
    (hpos : 0 < firstReturnLoopWeight r) :
    firstReturnLoopWeight r = 1 / (q ^ firstReturnLoopReward r : ℕ) :=
  recurrentLoopRecordWeight_eq_q_reward r.2.2 hpos

theorem firstReturnLoopWord_mem_multipliers (r : FirstReturnLoop) :
    ∀ a ∈ firstReturnLoopWord r, a ∈ multipliers :=
  recurrentLoopRecordWord_mem_multipliers r.2.2

theorem firstReturnLoopWord_length (r : FirstReturnLoop) :
    (firstReturnLoopWord r).length = controlBlockLength * r.2.1 :=
  recurrentLoopRecordWord_length r.2.2

theorem firstReturnLoopWeight_summable : Summable firstReturnLoopWeight := by
  have hk (k : ℕ) : Summable fun z : Σ n : ℕ, RecurrentLoopRecord k n ↦
      recurrentLoopRecordWeight z.2 := by
    rw [summable_sigma_of_nonneg fun z ↦ recurrentLoopRecordWeight_nonneg z.2]
    constructor
    · intro n
      exact Summable.of_finite
    · have heq : (fun n ↦ ∑' r : RecurrentLoopRecord k n,
            recurrentLoopRecordWeight r) = fun n ↦ holdingReturn k n := by
        funext n
        rw [tsum_fintype, sum_recurrentLoopRecordWeight]
      rw [heq]
      exact (holdingReturn_summable_and_mass k).1
  rw [summable_sigma_of_nonneg firstReturnLoopWeight_nonneg]
  constructor
  · exact hk
  · have heq : (fun k ↦ ∑' z : Σ n : ℕ, RecurrentLoopRecord k n,
          recurrentLoopRecordWeight z.2) =
      fun k ↦ EmbeddedChain.returnHitTotal {recurrentControlState} k
          recurrentControlState := by
      funext k
      rw [(hk k).tsum_sigma]
      simp_rw [tsum_fintype, sum_recurrentLoopRecordWeight,
        (holdingReturn_summable_and_mass k).2,
        embedded_returnAt_eq_returnHitTotal]
    change Summable fun k ↦ ∑' z : Σ n : ℕ, RecurrentLoopRecord k n,
      recurrentLoopRecordWeight z.2
    rw [heq]
    exact recurrent_visit_return_total.summable

theorem tsum_firstReturnLoopWeight : (∑' r, firstReturnLoopWeight r) = 1 := by
  have hk (k : ℕ) : Summable fun z : Σ n : ℕ, RecurrentLoopRecord k n ↦
      recurrentLoopRecordWeight z.2 := by
    rw [summable_sigma_of_nonneg fun z ↦ recurrentLoopRecordWeight_nonneg z.2]
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, sum_recurrentLoopRecordWeight] using
        (holdingReturn_summable_and_mass k).1
  rw [firstReturnLoopWeight_summable.tsum_sigma]
  change (∑' k, ∑' z : Σ n : ℕ, RecurrentLoopRecord k n,
    recurrentLoopRecordWeight z.2) = 1
  simp_rw [(hk _).tsum_sigma, tsum_fintype, sum_recurrentLoopRecordWeight,
    (holdingReturn_summable_and_mass _).2,
    embedded_returnAt_eq_returnHitTotal]
  exact recurrent_visit_return_total.tsum_eq

theorem weighted_firstReturnLoopDuration_summable :
    Summable fun r : FirstReturnLoop ↦
      (r.2.1 : ℝ) * firstReturnLoopWeight r := by
  rw [summable_sigma_of_nonneg fun r ↦ mul_nonneg (Nat.cast_nonneg r.2.1)
    (firstReturnLoopWeight_nonneg r)]
  constructor
  · intro k
    change Summable fun z : Σ n : ℕ, RecurrentLoopRecord k n ↦
      (z.1 : ℝ) * recurrentLoopRecordWeight z.2
    rw [summable_sigma_of_nonneg fun z ↦ mul_nonneg (Nat.cast_nonneg z.1)
      (recurrentLoopRecordWeight_nonneg z.2)]
    constructor
    · intro n
      exact Summable.of_finite
    · have heq : (fun n ↦ ∑' r : RecurrentLoopRecord k n,
            (n : ℝ) * recurrentLoopRecordWeight r) =
          fun n : ℕ ↦ (n : ℝ) * holdingReturn k n := by
        funext n
        rw [tsum_fintype, ← Finset.mul_sum, sum_recurrentLoopRecordWeight]
      rw [heq]
      exact holdingReturn_weighted_summable k
  · have heq : (fun k ↦ ∑' z : Σ n : ℕ, RecurrentLoopRecord k n,
          (z.1 : ℝ) * recurrentLoopRecordWeight z.2) = holdingReturnMean := by
      funext k
      have hk : Summable fun z : Σ n : ℕ, RecurrentLoopRecord k n ↦
          (z.1 : ℝ) * recurrentLoopRecordWeight z.2 := by
        rw [summable_sigma_of_nonneg fun z ↦ mul_nonneg (Nat.cast_nonneg z.1)
          (recurrentLoopRecordWeight_nonneg z.2)]
        constructor
        · intro n
          exact Summable.of_finite
        · simpa only [tsum_fintype, ← Finset.mul_sum,
            sum_recurrentLoopRecordWeight] using holdingReturn_weighted_summable k
      rw [hk.tsum_sigma]
      simp_rw [tsum_fintype, ← Finset.mul_sum, sum_recurrentLoopRecordWeight]
      rfl
    change Summable fun k ↦ ∑' z : Σ n : ℕ, RecurrentLoopRecord k n,
      (z.1 : ℝ) * recurrentLoopRecordWeight z.2
    rw [heq]
    exact holdingReturnMean_summable

theorem primeIncrement_seven_le_one {a : ℕ} (ha : a ∈ multipliers) :
    primeIncrement a 3 ≤ 1 := by
  simp only [multipliers, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide

theorem exponent_seven_le_length (w : List ℕ)
    (hw : ∀ a ∈ w, a ∈ multipliers) : exponents w 3 ≤ w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have ha := primeIncrement_seven_le_one (hw a (by simp))
      have htail : ∀ b ∈ w, b ∈ multipliers := by
        intro b hb
        exact hw b (by simp [hb])
      simp only [exponents_cons, List.length_cons]
      have ht := ih htail
      omega

theorem firstReturnLoopReward_le_duration (r : FirstReturnLoop) :
    firstReturnLoopReward r ≤ controlBlockLength * r.2.1 := by
  calc
    firstReturnLoopReward r ≤ (firstReturnLoopWord r).length :=
      exponent_seven_le_length _ (firstReturnLoopWord_mem_multipliers r)
    _ = controlBlockLength * r.2.1 := firstReturnLoopWord_length r

theorem weighted_firstReturnLoopReward_summable :
    Summable fun r : FirstReturnLoop ↦
      (firstReturnLoopReward r : ℝ) * firstReturnLoopWeight r := by
  apply Summable.of_nonneg_of_le
    (fun r ↦ mul_nonneg (Nat.cast_nonneg _) (firstReturnLoopWeight_nonneg r))
    (fun r ↦ by
      have hcast : (firstReturnLoopReward r : ℝ) ≤
          (controlBlockLength * r.2.1 : ℕ) := by
        exact_mod_cast firstReturnLoopReward_le_duration r
      exact mul_le_mul_of_nonneg_right hcast
        (firstReturnLoopWeight_nonneg r))
  simpa only [Nat.cast_mul, mul_assoc] using
    weighted_firstReturnLoopDuration_summable.mul_left
      (controlBlockLength : ℝ)

theorem firstReturnLoopWord_injective_of_pos :
    Set.InjOn firstReturnLoopWord {r | 0 < firstReturnLoopWeight r} := by
  intro r hr s hs hword
  obtain ⟨k, n, r⟩ := r
  obtain ⟨l, m, s⟩ := s
  have hnm : n = m := by
    have hlen := congrArg List.length hword
    simp only [firstReturnLoopWord, recurrentLoopRecordWord_length] at hlen
    have hN := controlBlockLength_pos
    exact Nat.mul_left_cancel hN hlen
  subst m
  have htuple : recurrentLoopRecordTuple r = recurrentLoopRecordTuple s := by
    apply controlledPathWord_injective_of_return n recurrentAugmentedState
    · rwa [← recurrentLoopRecordWeight_eq_pathWeight]
    · rwa [← recurrentLoopRecordWeight_eq_pathWeight]
    · exact recurrentLoopRecord_pathEndpoint r
    · exact recurrentLoopRecord_pathEndpoint s
    · simpa only [firstReturnLoopWord,
        recurrentLoopRecordWord_eq_controlledPathWord] using hword
  have hchoices : recurrentLoopRecordChoices r = recurrentLoopRecordChoices s := by
    rw [← ofFn_recurrentLoopRecordTuple, ← ofFn_recurrentLoopRecordTuple,
      htuple]
  exact recurrentLoopRecord_sigma_choices_injective hchoices

noncomputable def loopRewardMass (m : ℕ) : ℝ :=
  ∑' r : FirstReturnLoop,
    selectedWeight (firstReturnLoopReward r = m) (firstReturnLoopWeight r)

theorem selectedWeight_nonneg {P : Prop} {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ selectedWeight P x := by
  classical
  by_cases hP : P <;> simp [selectedWeight, hP, hx]

theorem selectedWeight_le {P : Prop} {x : ℝ} (hx : 0 ≤ x) :
    selectedWeight P x ≤ x := by
  classical
  by_cases hP : P <;> simp [selectedWeight, hP, hx]

theorem loopRewardMass_nonneg (m : ℕ) : 0 ≤ loopRewardMass m :=
  tsum_nonneg fun r ↦ selectedWeight_nonneg (firstReturnLoopWeight_nonneg r)

theorem rewardIndicator_hasSum (r : FirstReturnLoop) :
    HasSum (fun m ↦ selectedWeight (firstReturnLoopReward r = m)
      (firstReturnLoopWeight r)) (firstReturnLoopWeight r) := by
  simpa [selectedWeight, eq_comm] using
    (hasSum_ite_eq (firstReturnLoopReward r) (firstReturnLoopWeight r))

theorem loopRewardMass_summable : Summable loopRewardMass := by
  have hpair : Summable fun p : FirstReturnLoop × ℕ ↦
      selectedWeight (firstReturnLoopReward p.1 = p.2)
        (firstReturnLoopWeight p.1) := by
    rw [summable_prod_of_nonneg fun p ↦
      selectedWeight_nonneg (firstReturnLoopWeight_nonneg p.1)]
    constructor
    · exact fun r ↦ (rewardIndicator_hasSum r).summable
    · have heq : (fun r ↦ ∑' m, selectedWeight
            (firstReturnLoopReward r = m) (firstReturnLoopWeight r)) =
          firstReturnLoopWeight := by
        funext r
        exact (rewardIndicator_hasSum r).tsum_eq
      rw [heq]
      exact firstReturnLoopWeight_summable
  have hswap : Summable fun p : ℕ × FirstReturnLoop ↦
      selectedWeight (firstReturnLoopReward p.2 = p.1)
        (firstReturnLoopWeight p.2) := by
    simpa [Function.comp_def] using hpair.comp_injective
      (show Function.Injective
          (fun p : ℕ × FirstReturnLoop ↦ (p.2, p.1)) by
        exact (Equiv.prodComm ℕ FirstReturnLoop).injective)
  rw [summable_prod_of_nonneg fun p ↦
    selectedWeight_nonneg (firstReturnLoopWeight_nonneg p.2)] at hswap
  simpa only [loopRewardMass] using hswap.2

theorem tsum_loopRewardMass : (∑' m, loopRewardMass m) = 1 := by
  have hpair : Summable fun p : FirstReturnLoop × ℕ ↦
      selectedWeight (firstReturnLoopReward p.1 = p.2)
        (firstReturnLoopWeight p.1) := by
    rw [summable_prod_of_nonneg fun p ↦
      selectedWeight_nonneg (firstReturnLoopWeight_nonneg p.1)]
    exact ⟨fun r ↦ (rewardIndicator_hasSum r).summable, by
      simpa only [(rewardIndicator_hasSum _).tsum_eq] using
        firstReturnLoopWeight_summable⟩
  have hswap : Summable fun p : ℕ × FirstReturnLoop ↦
      selectedWeight (firstReturnLoopReward p.2 = p.1)
        (firstReturnLoopWeight p.2) := by
    simpa [Function.comp_def] using hpair.comp_injective
      (show Function.Injective
          (fun p : ℕ × FirstReturnLoop ↦ (p.2, p.1)) by
        exact (Equiv.prodComm ℕ FirstReturnLoop).injective)
  calc
    (∑' m, loopRewardMass m) = ∑' p : ℕ × FirstReturnLoop,
        selectedWeight (firstReturnLoopReward p.2 = p.1)
          (firstReturnLoopWeight p.2) := by
      rw [hswap.tsum_prod]
      rfl
    _ = ∑' p : FirstReturnLoop × ℕ,
        selectedWeight (firstReturnLoopReward p.1 = p.2)
          (firstReturnLoopWeight p.1) :=
      ((Equiv.prodComm FirstReturnLoop ℕ).tsum_eq _).symm
    _ = ∑' r, ∑' m, selectedWeight (firstReturnLoopReward r = m)
          (firstReturnLoopWeight r) := hpair.tsum_prod
    _ = ∑' r, firstReturnLoopWeight r := by
      apply tsum_congr
      exact fun r ↦ (rewardIndicator_hasSum r).tsum_eq
    _ = 1 := tsum_firstReturnLoopWeight

theorem weightedRewardIndicator_hasSum (r : FirstReturnLoop) :
    HasSum (fun m : ℕ ↦ (m : ℝ) *
      selectedWeight (firstReturnLoopReward r = m) (firstReturnLoopWeight r))
      ((firstReturnLoopReward r : ℝ) * firstReturnLoopWeight r) := by
  have h := hasSum_ite_eq (firstReturnLoopReward r)
    ((firstReturnLoopReward r : ℝ) * firstReturnLoopWeight r)
  have hfun : (fun m : ℕ ↦ (m : ℝ) *
      selectedWeight (firstReturnLoopReward r = m) (firstReturnLoopWeight r)) =
      fun m ↦ if m = firstReturnLoopReward r then
        (firstReturnLoopReward r : ℝ) * firstReturnLoopWeight r else 0 := by
    funext m
    by_cases hm : firstReturnLoopReward r = m
    · subst m
      simp [selectedWeight]
    · simp [selectedWeight, hm, Ne.symm hm]
  rw [hfun]
  exact h

theorem weighted_loopRewardMass_summable :
    Summable fun m : ℕ ↦ (m : ℝ) * loopRewardMass m := by
  have hpair : Summable fun p : FirstReturnLoop × ℕ ↦ (p.2 : ℝ) *
      selectedWeight (firstReturnLoopReward p.1 = p.2)
        (firstReturnLoopWeight p.1) := by
    rw [summable_prod_of_nonneg fun p ↦ mul_nonneg (Nat.cast_nonneg p.2)
      (selectedWeight_nonneg (firstReturnLoopWeight_nonneg p.1))]
    constructor
    · exact fun r ↦ (weightedRewardIndicator_hasSum r).summable
    · have heq : (fun r ↦ ∑' m : ℕ, (m : ℝ) * selectedWeight
            (firstReturnLoopReward r = m) (firstReturnLoopWeight r)) =
          fun r ↦ (firstReturnLoopReward r : ℝ) * firstReturnLoopWeight r := by
        funext r
        exact (weightedRewardIndicator_hasSum r).tsum_eq
      rw [heq]
      exact weighted_firstReturnLoopReward_summable
  have hswap : Summable fun p : ℕ × FirstReturnLoop ↦ (p.1 : ℝ) *
      selectedWeight (firstReturnLoopReward p.2 = p.1)
        (firstReturnLoopWeight p.2) := by
    simpa [Function.comp_def] using hpair.comp_injective
      (show Function.Injective
          (fun p : ℕ × FirstReturnLoop ↦ (p.2, p.1)) by
        exact (Equiv.prodComm ℕ FirstReturnLoop).injective)
  rw [summable_prod_of_nonneg fun p ↦ mul_nonneg (Nat.cast_nonneg p.1)
    (selectedWeight_nonneg (firstReturnLoopWeight_nonneg p.2))] at hswap
  have hslices (m : ℕ) : Summable fun r : FirstReturnLoop ↦
      selectedWeight (firstReturnLoopReward r = m) (firstReturnLoopWeight r) :=
    Summable.of_nonneg_of_le
      (fun r ↦ selectedWeight_nonneg (firstReturnLoopWeight_nonneg r))
      (fun r ↦ selectedWeight_le (firstReturnLoopWeight_nonneg r))
      firstReturnLoopWeight_summable
  have heq : (fun m : ℕ ↦ (m : ℝ) * loopRewardMass m) =
      fun m : ℕ ↦ ∑' r : FirstReturnLoop, (m : ℝ) *
        selectedWeight (firstReturnLoopReward r = m) (firstReturnLoopWeight r) := by
    funext m
    exact ((hslices m).tsum_mul_left (m : ℝ)).symm
  rw [heq]
  exact hswap.2

theorem loopRewardMass_zero : loopRewardMass 0 = 0 := by
  rw [loopRewardMass]
  calc
    (∑' r : FirstReturnLoop,
        selectedWeight (firstReturnLoopReward r = 0) (firstReturnLoopWeight r)) =
        ∑' _r : FirstReturnLoop, (0 : ℝ) := by
      apply tsum_congr
      intro r
      have hr := firstReturnLoopReward_pos r
      simp [selectedWeight, hr.ne']
    _ = 0 := tsum_zero

/-! ### Finiteness and the exact counting interpretation -/

theorem one_le_primeIncrement_sum {a : ℕ} (ha : a ∈ multipliers) :
    1 ≤ primeIncrement a 0 + primeIncrement a 1 +
      primeIncrement a 2 + primeIncrement a 3 := by
  simp only [multipliers, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide

theorem length_le_exponent_sum (w : List ℕ)
    (hw : ∀ a ∈ w, a ∈ multipliers) :
    w.length ≤ exponents w 0 + exponents w 1 + exponents w 2 + exponents w 3 := by
  induction w with
  | nil => simp
  | cons a w ih =>
      have ha := one_le_primeIncrement_sum (hw a (by simp))
      have htail : ∀ b ∈ w, b ∈ multipliers := by
        intro b hb
        exact hw b (by simp [hb])
      simp only [List.length_cons, exponents_cons]
      have ht := ih htail
      omega

theorem firstReturnLoopWord_length_le (r : FirstReturnLoop) :
    (firstReturnLoopWord r).length ≤ 69 * firstReturnLoopReward r := by
  have hlen := length_le_exponent_sum (firstReturnLoopWord r)
    (firstReturnLoopWord_mem_multipliers r)
  have hzero := recurrentLoopRecord_imbalance_zero r.2.2
  have heq := exponents_eq_of_imbalance_eq_zero hzero
  rcases heq with ⟨h0, h1, h2⟩
  dsimp only [firstReturnLoopWord, firstReturnLoopReward,
    recurrentLoopReward] at hlen h0 h1 h2 ⊢
  omega

abbrev AllowedMultiplier := {a : ℕ // a ∈ multipliers}

abbrev BoundedMultiplierWord (L : ℕ) :=
  Σ n : Fin (L + 1), Fin n → AllowedMultiplier

noncomputable def boundedMultiplierWordCode (L : ℕ) (w : List ℕ)
    (hL : w.length ≤ L) (hw : ∀ a ∈ w, a ∈ multipliers) :
    BoundedMultiplierWord L :=
  ⟨⟨w.length, by omega⟩, fun i ↦ ⟨w.get i, hw _ (List.get_mem w i)⟩⟩

def decodeBoundedMultiplierWord {L : ℕ} (c : BoundedMultiplierWord L) : List ℕ :=
  List.ofFn fun i ↦ (c.2 i).1

@[simp] theorem decode_boundedMultiplierWordCode (L : ℕ) (w : List ℕ)
    (hL : w.length ≤ L) (hw : ∀ a ∈ w, a ∈ multipliers) :
    decodeBoundedMultiplierWord (boundedMultiplierWordCode L w hL hw) = w := by
  exact List.ofFn_get w

abbrev PositiveLoopOfReward (m : ℕ) :=
  {r : FirstReturnLoop // firstReturnLoopReward r = m ∧
    0 < firstReturnLoopWeight r}

noncomputable instance positiveLoopOfRewardFintype (m : ℕ) :
    Fintype (PositiveLoopOfReward m) := by
  let encode : PositiveLoopOfReward m → BoundedMultiplierWord (69 * m) :=
    fun r ↦ boundedMultiplierWordCode (69 * m) (firstReturnLoopWord r.1)
      (by simpa [r.2.1] using firstReturnLoopWord_length_le r.1)
      (firstReturnLoopWord_mem_multipliers r.1)
  apply Fintype.ofInjective encode
  intro r s hrs
  apply Subtype.ext
  apply firstReturnLoopWord_injective_of_pos r.2.2 s.2.2
  have hdecode := congrArg decodeBoundedMultiplierWord hrs
  simpa [encode] using hdecode

noncomputable def firstReturnLoopCount (m : ℕ) : ℕ :=
  Fintype.card (PositiveLoopOfReward m)

theorem loopRewardMass_eq_count (m : ℕ) :
    loopRewardMass m = (firstReturnLoopCount m : ℝ) / (q ^ m : ℕ) := by
  have hsub : loopRewardMass m =
      ∑' r : PositiveLoopOfReward m, firstReturnLoopWeight r.1 := by
    rw [loopRewardMass]
    calc
      (∑' r : FirstReturnLoop,
          selectedWeight (firstReturnLoopReward r = m) (firstReturnLoopWeight r)) =
          ∑' r : FirstReturnLoop,
            ({r | firstReturnLoopReward r = m ∧ 0 < firstReturnLoopWeight r} :
              Set FirstReturnLoop).indicator firstReturnLoopWeight r := by
        apply tsum_congr
        intro r
        by_cases hr : firstReturnLoopReward r = m
        · by_cases hp : 0 < firstReturnLoopWeight r
          · simp [selectedWeight, hr, hp]
          · have hz : firstReturnLoopWeight r = 0 :=
              le_antisymm (le_of_not_gt hp) (firstReturnLoopWeight_nonneg r)
            simp [selectedWeight, hr, hz]
        · simp [selectedWeight, hr]
      _ = ∑' r : PositiveLoopOfReward m, firstReturnLoopWeight r.1 :=
        (tsum_subtype
          {r : FirstReturnLoop | firstReturnLoopReward r = m ∧
            0 < firstReturnLoopWeight r} firstReturnLoopWeight).symm
  rw [hsub, tsum_fintype]
  have hterm (r : PositiveLoopOfReward m) :
      firstReturnLoopWeight r.1 = 1 / (q ^ m : ℕ) := by
    rw [firstReturnLoopWeight_eq_q_reward r.1 r.2.2, r.2.1]
  simp_rw [hterm]
  simp [firstReturnLoopCount, div_eq_mul_inv]

/-! ## An elementary bounded-window renewal lemma

Instead of importing the arithmetic renewal theorem, we use the simpler fact
that a positive-integer renewal process crosses every level, and finite mean
makes a fixed overshoot window carry uniformly positive mass. -/

section AbstractRenewal

variable (p : ℕ → ℝ)
variable (hp0 : ∀ n, 0 ≤ p n)
variable (hp : Summable p)
variable (hpMass : (∑' n, p n) = 1)
variable (hpZero : p 0 = 0)

noncomputable def distributionTail (d : ℕ) : ℝ :=
  ∑' t, p (t + d)

include hp0 in
theorem distributionTail_nonneg (d : ℕ) :
    0 ≤ distributionTail p d := tsum_nonneg fun t ↦ hp0 (t + d)

include hp in
theorem distributionTail_summable (d : ℕ) :
    Summable fun t ↦ p (t + d) := (summable_nat_add_iff d).2 hp

include hp in
theorem distributionTail_succ (d : ℕ) :
    distributionTail p d = p d + distributionTail p (d + 1) := by
  rw [distributionTail, (distributionTail_summable p hp d).tsum_eq_zero_add]
  congr 1
  · simp
  apply tsum_congr
  intro t
  congr 1
  omega

include hp hpMass hpZero in
theorem distributionTail_one : distributionTail p 1 = 1 := by
  have h := distributionTail_succ p hp (d := 0)
  have hzero : distributionTail p 0 = 1 := by
    rw [distributionTail]
    simpa using hpMass
  rw [hzero, hpZero, zero_add] at h
  exact h.symm

noncomputable def natAddEquivIci (d : ℕ) : ℕ ≃ {j : ℕ // d ≤ j} where
  toFun t := ⟨d + t, by omega⟩
  invFun j := j.1 - d
  left_inv t := by simp
  right_inv j := by
    apply Subtype.ext
    simp only
    omega

theorem distributionTail_eq_tsum_ge (d : ℕ) :
    distributionTail p d =
      ∑' j, selectedWeight (d ≤ j) (p j) := by
  calc
    distributionTail p d = ∑' t : ℕ, p (d + t) := by
      apply tsum_congr
      intro t
      rw [Nat.add_comm]
    _ = ∑' j : {j : ℕ // d ≤ j}, p j.1 :=
      (natAddEquivIci d).tsum_eq (fun j : {j : ℕ // d ≤ j} ↦ p j.1)
    _ = ∑' j : ℕ, Set.indicator {j : ℕ | d ≤ j} p j :=
      tsum_subtype {j : ℕ | d ≤ j} p
    _ = ∑' j : ℕ, selectedWeight (d ≤ j) (p j) := by
      apply tsum_congr
      intro j
      by_cases h : d ≤ j <;> simp [selectedWeight, Set.indicator, h]

include hp in
theorem distributionTail_split (d L : ℕ) :
    distributionTail p d =
      (∑ j ∈ Finset.range L, p (j + d)) + distributionTail p (d + L) := by
  have h := (distributionTail_summable p hp d).sum_add_tsum_nat_add L
  simp only [distributionTail]
  rw [← h]
  congr 1
  apply tsum_congr
  intro j
  congr 1
  omega

/-- Renewal mass at a level, including the empty renewal at zero. -/
noncomputable def renewalMass : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ s : Fin (n + 1), renewalMass s * p (n + 1 - s)
termination_by n => n
decreasing_by exact s.isLt

@[simp] theorem renewalMass_zero : renewalMass p 0 = 1 := by
  rw [renewalMass]

theorem renewalMass_succ (n : ℕ) : renewalMass p (n + 1) =
    ∑ s ∈ Finset.range (n + 1), renewalMass p s * p (n + 1 - s) := by
  rw [renewalMass]
  exact Fin.sum_univ_eq_sum_range
    (fun s ↦ renewalMass p s * p (n + 1 - s)) (n + 1)

include hp0 in
theorem renewalMass_nonneg (n : ℕ) : 0 ≤ renewalMass p n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [renewalMass_succ]
          exact Finset.sum_nonneg fun s hs ↦ mul_nonneg
            (ih s (by simpa using hs)) (hp0 _)

noncomputable def crossingMass (M : ℕ) : ℝ :=
  ∑ s ∈ Finset.range M, renewalMass p s * distributionTail p (M - s)

include hp hpMass hpZero in
theorem crossingMass_one {M : ℕ} (hM : 0 < M) :
    crossingMass p M = 1 := by
  induction M, hM using Nat.le_induction with
  | base =>
      simp [crossingMass, distributionTail_one p hp hpMass hpZero]
  | succ M hM ih =>
      have hMpos : 0 < M := by omega
      have htail (s : ℕ) (hs : s ∈ Finset.range M) :
          distributionTail p (M - s) =
            p (M - s) + distributionTail p (M + 1 - s) := by
        rw [distributionTail_succ p hp]
        simp only [Finset.mem_range] at hs
        rw [show M - s + 1 = M + 1 - s by omega]
      rw [crossingMass, Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel_left]
      rw [distributionTail_one p hp hpMass hpZero, mul_one]
      have hrenew := renewalMass_succ p M
      have hsplit : crossingMass p M =
          (∑ s ∈ Finset.range M, renewalMass p s * p (M - s)) +
            ∑ s ∈ Finset.range M,
              renewalMass p s * distributionTail p (M + 1 - s) := by
        rw [crossingMass, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        rw [htail s hs, mul_add]
      rw [ih] at hsplit
      rw [show renewalMass p M =
          ∑ s ∈ Finset.range M, renewalMass p s * p (M - s) by
        cases M with
        | zero => omega
        | succ m => exact renewalMass_succ p m]
      linarith

include hp0 hp hpMass hpZero in
theorem renewalMass_le_one (n : ℕ) : renewalMass p n ≤ 1 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [renewalMass_succ]
      have hterm (s : ℕ) (hs : s ∈ Finset.range (n + 1)) :
          renewalMass p s * p (n + 1 - s) ≤
            renewalMass p s * distributionTail p (n + 1 - s) := by
        apply mul_le_mul_of_nonneg_left _ (renewalMass_nonneg p hp0 s)
        have ht := distributionTail_succ p hp (n + 1 - s)
        linarith [distributionTail_nonneg p hp0 (n + 1 - s + 1)]
      calc
        _ ≤ ∑ s ∈ Finset.range (n + 1),
            renewalMass p s * distributionTail p (n + 1 - s) :=
          Finset.sum_le_sum hterm
        _ = crossingMass p (n + 1) := rfl
        _ = 1 := crossingMass_one p hp hpMass hpZero (by omega)

noncomputable def goodCrossingMass (M K : ℕ) : ℝ :=
  ∑ s ∈ Finset.range M, renewalMass p s *
    ∑ j ∈ Finset.range (K + 1), p (j + (M - s))

noncomputable def badCrossingMass (M K : ℕ) : ℝ :=
  ∑ s ∈ Finset.range M, renewalMass p s *
    distributionTail p (M + K + 1 - s)

include hp in
theorem good_add_bad_eq_crossing (M K : ℕ) :
    goodCrossingMass p M K + badCrossingMass p M K = crossingMass p M := by
  rw [goodCrossingMass, badCrossingMass, crossingMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← mul_add]
  have hsplit := distributionTail_split p hp (M - s) (K + 1)
  have heq : M - s + (K + 1) = M + K + 1 - s := by
    simp only [Finset.mem_range] at hs
    omega
  rw [heq] at hsplit
  rw [hsplit]

include hp0 in
theorem goodCrossingMass_le_window {M : ℕ} (hM : 0 < M) (K : ℕ) :
    goodCrossingMass p M K ≤
      ∑ j ∈ Finset.range (K + 1), renewalMass p (M + j) := by
  rw [goodCrossingMass]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  have hrec : renewalMass p (M + j) =
      ∑ s ∈ Finset.range (M + j), renewalMass p s * p (M + j - s) := by
    cases M with
    | zero => omega
    | succ M =>
        rw [Nat.succ_add]
        exact renewalMass_succ p (M + j)
  rw [hrec]
  have hrewrite :
      (∑ s ∈ Finset.range M, renewalMass p s * p (j + (M - s))) =
        ∑ s ∈ Finset.range M, renewalMass p s * p (M + j - s) := by
    apply Finset.sum_congr rfl
    intro s hs
    congr 2
    simp only [Finset.mem_range] at hs
    omega
  rw [hrewrite]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    simp only [Finset.mem_range] at hs ⊢
    omega
  · intro s hs _
    exact mul_nonneg (renewalMass_nonneg p hp0 s) (hp0 _)

noncomputable def badJumpMass (M K j : ℕ) : ℝ :=
  ∑ s ∈ Finset.range M,
    selectedWeight (M + K + 1 ≤ s + j) (renewalMass p s * p j)

include hp0 in
theorem badJumpMass_nonneg (M K j : ℕ) :
    0 ≤ badJumpMass p M K j := by
  exact Finset.sum_nonneg fun s _ ↦ selectedWeight_nonneg
    (mul_nonneg (renewalMass_nonneg p hp0 s) (hp0 j))

include hp0 hp hpMass hpZero in
theorem badJumpMass_summable (M K : ℕ) :
    Summable fun j ↦ badJumpMass p M K j := by
  apply Summable.of_nonneg_of_le (badJumpMass_nonneg p hp0 M K)
  · intro j
    calc
      badJumpMass p M K j ≤ ∑ _s ∈ Finset.range M, p j := by
        apply Finset.sum_le_sum
        intro s _
        refine (selectedWeight_le
          (mul_nonneg (renewalMass_nonneg p hp0 s) (hp0 j))).trans ?_
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (renewalMass_le_one p hp0 hp hpMass hpZero s) (hp0 j)
      _ = (M : ℝ) * p j := by simp
  · exact hp.mul_left (M : ℝ)

include hp0 hp in
theorem badCrossingMass_eq_tsum_badJump (M K : ℕ) :
    badCrossingMass p M K = ∑' j, badJumpMass p M K j := by
  have hbase (s : ℕ) (hs : s ∈ Finset.range M) : Summable fun j ↦
      selectedWeight (M + K + 1 - s ≤ j) (p j) := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ selectedWeight_nonneg (hp0 j))
      (fun j ↦ selectedWeight_le (hp0 j))
    exact hp
  have hsumm (s : ℕ) (hs : s ∈ Finset.range M) : Summable fun j ↦
      selectedWeight (M + K + 1 - s ≤ j) (renewalMass p s * p j) := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ selectedWeight_nonneg
        (mul_nonneg (renewalMass_nonneg p hp0 s) (hp0 j)))
      (fun j ↦ selectedWeight_le
        (mul_nonneg (renewalMass_nonneg p hp0 s) (hp0 j)))
    exact hp.mul_left (renewalMass p s)
  have hmul (s : ℕ) (hs : s ∈ Finset.range M) :
      renewalMass p s *
          (∑' j, selectedWeight (M + K + 1 - s ≤ j) (p j)) =
        ∑' j, selectedWeight (M + K + 1 - s ≤ j)
          (renewalMass p s * p j) := by
    rw [← (hbase s hs).tsum_mul_left]
    apply tsum_congr
    intro j
    exact (selectedWeight_mul_left _ _ _).symm
  rw [badCrossingMass]
  simp_rw [distributionTail_eq_tsum_ge p]
  have hfinite :
      (∑ s ∈ Finset.range M, renewalMass p s *
          ∑' j, selectedWeight (M + K + 1 - s ≤ j) (p j)) =
        ∑ s ∈ Finset.range M, ∑' j,
          selectedWeight (M + K + 1 - s ≤ j)
            (renewalMass p s * p j) := by
    apply Finset.sum_congr rfl
    intro s hs
    exact hmul s hs
  rw [hfinite]
  rw [← Summable.tsum_finsetSum hsumm]
  apply tsum_congr
  intro j
  simp only [badJumpMass]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply propext
  exact Nat.sub_le_iff_le_add'

include hp0 hp hpMass hpZero in
theorem badJumpMass_le (M K j : ℕ) :
    badJumpMass p M K j ≤ (j : ℝ) * p j := by
  classical
  by_cases hM : M = 0
  · subst M
    simpa [badJumpMass] using
      (mul_nonneg (Nat.cast_nonneg j) (hp0 j))
  let E := (Finset.range M).filter fun s ↦ M + K + 1 ≤ s + j
  have hrewrite : badJumpMass p M K j =
      ∑ s ∈ E, renewalMass p s * p j := by
    simp only [badJumpMass, E, selectedWeight]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases h : M + K + 1 ≤ s + j <;> simp only [h, if_true, if_false]
  rw [hrewrite]
  have hcard : E.card ≤ j := by
    have hsub : E ⊆ Finset.Icc (M + K + 1 - j) (M - 1) := by
      intro s hs
      simp only [E, Finset.mem_filter, Finset.mem_range] at hs
      simp only [Finset.mem_Icc]
      omega
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    omega
  calc
    (∑ s ∈ E, renewalMass p s * p j) ≤ ∑ _s ∈ E, p j := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (renewalMass_le_one p hp0 hp hpMass hpZero s) (hp0 j)
    _ = (E.card : ℝ) * p j := by simp
    _ ≤ (j : ℝ) * p j := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hp0 j)

theorem badJumpMass_zero_of_le (M K j : ℕ) (hj : j ≤ K) :
    badJumpMass p M K j = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  have hslt : s < M := by simpa using hs
  have hnot : ¬M + K + 1 ≤ s + j := by omega
  simp [selectedWeight, hnot]

noncomputable def weightedDistributionTail (K : ℕ) : ℝ :=
  ∑' t, ((t + K + 1 : ℕ) : ℝ) * p (t + K + 1)

theorem weightedDistributionTail_summable
    (hpw : Summable fun j : ℕ ↦ (j : ℝ) * p j) (K : ℕ) :
    Summable fun t ↦ ((t + K + 1 : ℕ) : ℝ) * p (t + K + 1) := by
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff (K + 1)).2 hpw

set_option maxHeartbeats 800000 in
-- Expanding the two infinite sums in the crossing estimate needs a larger bound.
include hp0 hp hpMass hpZero in
theorem badCrossingMass_le_weightedTail
    (hpw : Summable fun j : ℕ ↦ (j : ℝ) * p j) (M K : ℕ) :
    badCrossingMass p M K ≤ weightedDistributionTail p K := by
  rw [badCrossingMass_eq_tsum_badJump p hp0 hp M K]
  have hg := badJumpMass_summable p hp0 hp hpMass hpZero M K
  have hsplit := hg.sum_add_tsum_nat_add (K + 1)
  have hhead : (∑ j ∈ Finset.range (K + 1), badJumpMass p M K j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    apply badJumpMass_zero_of_le p M K j
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  rw [hhead, zero_add] at hsplit
  rw [← hsplit]
  have hbadTail : Summable fun t ↦ badJumpMass p M K (t + (K + 1)) :=
    (summable_nat_add_iff (K + 1)).2 hg
  exact hbadTail.tsum_le_tsum
    (fun t ↦ badJumpMass_le p hp0 hp hpMass hpZero M K (t + (K + 1)))
    (weightedDistributionTail_summable p hpw K)

theorem weightedDistributionTail_tendsto_zero :
    Filter.Tendsto (weightedDistributionTail p) Filter.atTop (nhds 0) := by
  let f : ℕ → ℝ := fun j ↦ (j : ℝ) * p j
  have hbase := tendsto_sum_nat_add f
  have hshift := (Filter.tendsto_add_atTop_iff_nat 1).mpr hbase
  simpa only [weightedDistributionTail, f, Nat.add_assoc] using hshift

include hp0 hp hpMass hpZero in
theorem exists_uniform_renewal_window
    (hpw : Summable fun j : ℕ ↦ (j : ℝ) * p j) :
    ∃ K : ℕ, ∀ M : ℕ, 0 < M →
      (1 : ℝ) / 2 <
        ∑ j ∈ Finset.range (K + 1), renewalMass p (M + j) := by
  have hevent : ∀ᶠ K : ℕ in Filter.atTop,
      weightedDistributionTail p K < (1 : ℝ) / 2 :=
    (weightedDistributionTail_tendsto_zero p).eventually
      (by exact Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨K, hK⟩ := hevent.exists
  refine ⟨K, ?_⟩
  intro M hM
  have hcross := crossingMass_one p hp hpMass hpZero hM
  have hsplit := good_add_bad_eq_crossing p hp M K
  have hbad := badCrossingMass_le_weightedTail p hp0 hp hpMass hpZero hpw M K
  have hgood : (1 : ℝ) / 2 < goodCrossingMass p M K := by
    linarith
  exact hgood.trans_le (goodCrossingMass_le_window p hp0 hM K)

end AbstractRenewal

/-! ## Finite concatenations of first-return loops -/

/-- Ordered concatenations whose total reward is exactly `n`. In the
successor case, `s` is the reward left for the tail. -/
inductive LoopSequence : ℕ → Type
  | nil : LoopSequence 0
  | cons {n : ℕ} (s : Fin (n + 1))
      (atom : PositiveLoopOfReward (n + 1 - s.1))
      (tail : LoopSequence s.1) : LoopSequence (n + 1)

def loopSequenceZeroEquiv : Unit ≃ LoopSequence 0 where
  toFun _ := .nil
  invFun r := by cases r; exact ()
  left_inv u := by cases u; rfl
  right_inv r := by cases r; rfl

def loopSequenceSuccEquiv (n : ℕ) :
    (Σ s : Fin (n + 1),
      PositiveLoopOfReward (n + 1 - s.1) × LoopSequence s.1) ≃
      LoopSequence (n + 1) where
  toFun r := .cons r.1 r.2.1 r.2.2
  invFun r := by
    cases r with
    | cons s atom tail => exact ⟨s, atom, tail⟩
  left_inv r := by cases r; rfl
  right_inv r := by cases r; rfl

noncomputable instance loopSequenceFintype : (n : ℕ) → Fintype (LoopSequence n)
  | 0 => Fintype.ofEquiv Unit loopSequenceZeroEquiv
  | n + 1 => by
      letI (s : Fin (n + 1)) : Fintype (LoopSequence s.1) :=
        loopSequenceFintype s.1
      exact Fintype.ofEquiv
        (Σ s : Fin (n + 1),
          PositiveLoopOfReward (n + 1 - s.1) × LoopSequence s.1)
        (loopSequenceSuccEquiv n)
termination_by n => n
decreasing_by exact s.2

noncomputable def loopSequenceCount (n : ℕ) : ℕ :=
  Fintype.card (LoopSequence n)

@[simp] theorem loopSequenceCount_zero : loopSequenceCount 0 = 1 := by
  unfold loopSequenceCount
  rw [Fintype.card_congr loopSequenceZeroEquiv.symm]
  exact Fintype.card_unit

theorem loopSequenceCount_succ (n : ℕ) :
    loopSequenceCount (n + 1) =
      ∑ s ∈ Finset.range (n + 1),
        firstReturnLoopCount (n + 1 - s) * loopSequenceCount s := by
  unfold loopSequenceCount
  rw [Fintype.card_congr (loopSequenceSuccEquiv n).symm]
  simp only [Fintype.card_sigma, Fintype.card_prod, firstReturnLoopCount]
  exact Fin.sum_univ_eq_sum_range
    (fun s : ℕ => Fintype.card (PositiveLoopOfReward (n + 1 - s)) *
      Fintype.card (LoopSequence s)) (n + 1)

theorem q_pos : 0 < q := by norm_num [q]

/-- The renewal mass is exactly the number of ordered loop concatenations
divided by their common reciprocal slope. -/
theorem renewalMass_eq_sequenceCount (n : ℕ) :
    renewalMass loopRewardMass n = (loopSequenceCount n : ℝ) / (q ^ n : ℕ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [renewalMass_succ, loopSequenceCount_succ]
          rw [Nat.cast_sum]
          simp only [Nat.cast_mul]
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro s hs
          have hslt : s < n + 1 := by simpa using hs
          rw [ih s hslt, loopRewardMass_eq_count]
          have hsum : s + (n + 1 - s) = n + 1 := by omega
          push_cast
          rw [div_mul_div_comm, ← pow_add, hsum]
          ring

noncomputable def loopSequenceChoices : {n : ℕ} → LoopSequence n → List BlockChoice
  | 0, .nil => []
  | _ + 1, .cons _ atom tail =>
      recurrentLoopRecordChoices atom.1.2.2 ++ loopSequenceChoices tail

noncomputable def loopSequenceWord : {n : ℕ} → LoopSequence n → List ℕ
  | 0, .nil => []
  | _ + 1, .cons _ atom tail =>
      firstReturnLoopWord atom.1 ++ loopSequenceWord tail

theorem controlledListWord_append (x : AugmentedState) (u v : List BlockChoice) :
    controlledListWord x (u ++ v) = controlledListWord x u ++
      controlledListWord (controlledChain.listEndpoint x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih =>
      simp only [List.cons_append, controlledListWord]
      rw [ih]
      simp only [FiniteChoiceChain.listEndpoint]
      rw [List.append_assoc]
      rfl

theorem inverseWord_append (u v : List ℕ) (z : ℚ) :
    inverseWord (u ++ v) z = inverseWord u (inverseWord v z) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [inverseWord, ih]

@[simp] theorem controlledListWord_length (x : AugmentedState)
    (u : List BlockChoice) :
    (controlledListWord x u).length = controlBlockLength * u.length := by
  induction u generalizing x with
  | nil => simp [controlledListWord]
  | cons a u ih =>
      simp only [controlledListWord, List.length_append, blockWord_length,
        List.length_cons, ih]
      ring

theorem controlledListWord_mem_multipliers (x : AugmentedState)
    (u : List BlockChoice) :
    ∀ a ∈ controlledListWord x u, a ∈ multipliers := by
  have h := controlledPathWord_mem_multipliers u.length x u.get
  simpa only [← controlledListWord_ofFn, List.ofFn_get] using h

theorem controlledListWord_prod_two_le (x : AugmentedState)
    {u : List BlockChoice} (hu : u ≠ []) : 2 ≤ (controlledListWord x u).prod := by
  apply prod_two_le_of_ne_nil
  · intro hnil
    have hlen := congrArg List.length hnil
    simp only [controlledListWord_length, List.length_nil] at hlen
    have hN := controlBlockLength_pos
    have hulen : 0 < u.length := List.length_pos_iff.mpr hu
    have hprod : 0 < controlBlockLength * u.length := Nat.mul_pos hN hulen
    omega
  · intro a ha
    exact mem_multipliers_two_le (controlledListWord_mem_multipliers x u a ha)

theorem controlledList_inverse_mem (x : AugmentedState)
    (u : List BlockChoice) (hu : 0 < controlledChain.listWeight x u)
    {z : ℚ} (hz : z ∈ K (controlledChain.listEndpoint x u).1) :
    inverseWord (controlledListWord x u) z ∈ K x.1 := by
  have hpath : 0 < controlledChain.pathWeight u.length x u.get := by
    rwa [← controlledChain.listWeight_ofFn, List.ofFn_get]
  have hmem := (controlledIntervalPath u.length x u.get hpath).inverseWord_mem_source
    (by simpa only [← controlledChain.listEndpoint_ofFn, List.ofFn_get] using hz)
  simpa only [controlledIntervalPath_word, ← controlledListWord_ofFn,
    List.ofFn_get] using hmem

set_option maxHeartbeats 800000 in
-- The proof recursively peels variable-length blocks and normalizes their products.
/-- Two positive controlled paths with the same pulled-back point and the
same slope have identical block choices. This is the graph-directed
injectivity statement that excludes global nonfree affine identities. -/
theorem controlledLists_eq_of_inverse_eq (x : AugmentedState)
    (u v : List BlockChoice)
    (hu : 0 < controlledChain.listWeight x u)
    (hv : 0 < controlledChain.listWeight x v)
    {zu zv : ℚ}
    (hzu : zu ∈ K (controlledChain.listEndpoint x u).1)
    (hzv : zv ∈ K (controlledChain.listEndpoint x v).1)
    (hinv : inverseWord (controlledListWord x u) zu =
      inverseWord (controlledListWord x v) zv)
    (hprod : (controlledListWord x u).prod =
      (controlledListWord x v).prod) : u = v ∧ zu = zv := by
  induction u generalizing x v zu zv with
  | nil =>
      cases v with
      | nil => exact ⟨rfl, by simpa [controlledListWord, inverseWord] using hinv⟩
      | cons b v =>
          have htwo := controlledListWord_prod_two_le x
            (u := b :: v) (by simp)
          change 1 = (controlledListWord x (b :: v)).prod at hprod
          rw [← hprod] at htwo
          omega
  | cons a u ih =>
      cases v with
      | nil =>
          have htwo := controlledListWord_prod_two_le x
            (u := a :: u) (by simp)
          change (controlledListWord x (a :: u)).prod = 1 at hprod
          rw [hprod] at htwo
          omega
      | cons b v =>
          simp only [FiniteChoiceChain.listWeight] at hu hv
          have hpa0 := controlledChain.probability_nonneg x a
          have hpb0 := controlledChain.probability_nonneg x b
          have htu0 := controlledChain.listWeight_nonneg (controlledNext x a) u
          have htv0 := controlledChain.listWeight_nonneg (controlledNext x b) v
          have hpa : 0 < controlledChain.probability x a :=
            pos_of_mul_pos_left hu htu0
          have hpb : 0 < controlledChain.probability x b :=
            pos_of_mul_pos_left hv htv0
          have htu : 0 < controlledChain.listWeight (controlledNext x a) u :=
            pos_of_mul_pos_right hu hpa0
          have htv : 0 < controlledChain.listWeight (controlledNext x b) v :=
            pos_of_mul_pos_right hv hpb0
          let yu := inverseWord (controlledListWord (controlledNext x a) u) zu
          let yv := inverseWord (controlledListWord (controlledNext x b) v) zv
          have hyu : yu ∈ K (controlledNext x a).1 :=
            controlledList_inverse_mem (controlledNext x a) u htu hzu
          have hyv : yv ∈ K (controlledNext x b).1 :=
            controlledList_inverse_mem (controlledNext x b) v htv hzv
          have hblockA : 0 < blockWeight (feedback x.2) controlBlockLength x.1 a := by
            change 0 < (blockWeight (feedback x.2) controlBlockLength x.1 a : ℝ)
              at hpa
            exact_mod_cast hpa
          have hblockB : 0 < blockWeight (feedback x.2) controlBlockLength x.1 b := by
            change 0 < (blockWeight (feedback x.2) controlBlockLength x.1 b : ℝ)
              at hpb
            exact_mod_cast hpb
          have hblockInv : inverseWord
              (blockWord (feedback x.2) controlBlockLength x.1 a) yu =
            inverseWord (blockWord (feedback x.2) controlBlockLength x.1 b) yv := by
            simpa only [controlledListWord, inverseWord_append, yu, yv] using hinv
          have hblock := blockChoice_eq_of_inverse_eq (feedback x.2)
            controlBlockLength x.1 hblockA hblockB hyu hyv hblockInv
          have hab := hblock.1
          subst b
          have htailProd :
              (controlledListWord (controlledNext x a) u).prod =
                (controlledListWord (controlledNext x a) v).prod := by
            simp only [controlledListWord, List.prod_append] at hprod
            have hblockProd : 0 <
                (blockWord (feedback x.2) controlBlockLength x.1 a).prod := by
              exact List.prod_pos (fun z hz ↦ by
                have hz2 := mem_multipliers_two_le
                  (blockWord_mem_multipliers _ _ _ _ z hz)
                omega)
            exact Nat.eq_of_mul_eq_mul_left hblockProd hprod
          have hrec := ih (x := controlledNext x a) (v := v)
            htu htv hzu hzv hblock.2 htailProd
          exact ⟨congrArg (List.cons a) hrec.1, hrec.2⟩

theorem loopSequence_endpoint {n : ℕ} (r : LoopSequence n) :
    controlledChain.listEndpoint recurrentAugmentedState
      (loopSequenceChoices (n := n) r) =
      recurrentAugmentedState := by
  induction r with
  | nil => rfl
  | cons s atom tail ih =>
      rw [loopSequenceChoices, controlledChain.listEndpoint_append,
        recurrentLoopRecord_endpoint atom.1.2.2]
      exact ih

theorem loopSequence_listWeight_pos {n : ℕ} (r : LoopSequence n) :
    0 < controlledChain.listWeight recurrentAugmentedState
      (loopSequenceChoices (n := n) r) := by
  induction r with
  | nil => simp [loopSequenceChoices, FiniteChoiceChain.listWeight]
  | cons s atom tail ih =>
      rw [loopSequenceChoices, controlledChain.listWeight_append,
        recurrentLoopRecord_endpoint atom.1.2.2,
        ← recurrentLoopRecordWeight_eq_listWeight]
      exact mul_pos atom.2.2 ih

theorem loopSequenceWord_eq_controlled {n : ℕ} (r : LoopSequence n) :
    loopSequenceWord (n := n) r = controlledListWord recurrentAugmentedState
      (loopSequenceChoices (n := n) r) := by
  induction r with
  | nil => rfl
  | cons s atom tail ih =>
      simp only [loopSequenceWord, loopSequenceChoices]
      rw [controlledListWord_append, recurrentLoopRecord_endpoint, ← ih]
      rfl

theorem loopSequenceWord_mem_multipliers {n : ℕ} (r : LoopSequence n) :
    ∀ a ∈ loopSequenceWord (n := n) r, a ∈ multipliers := by
  induction r with
  | nil => simp [loopSequenceWord]
  | cons s atom tail ih =>
      simp only [loopSequenceWord, List.mem_append]
      intro a ha
      rcases ha with ha | ha
      · exact firstReturnLoopWord_mem_multipliers atom.1 a ha
      · exact ih a ha

theorem loopSequenceWord_prod {n : ℕ} (r : LoopSequence n) :
    (loopSequenceWord (n := n) r).prod = q ^ n := by
  induction r with
  | nil => simp [loopSequenceWord]
  | @cons n s atom tail ih =>
      simp only [loopSequenceWord, List.prod_append]
      have hatom := recurrentLoopRecord_prod_eq_q_pow atom.1.2.2
      change (firstReturnLoopWord atom.1).prod = q ^ firstReturnLoopReward atom.1
        at hatom
      rw [hatom, atom.2.1, ih, ← pow_add]
      congr 1
      omega

theorem loopSequenceChoices_injective (n : ℕ) :
    Function.Injective (loopSequenceChoices (n := n) :
      LoopSequence n → List BlockChoice) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro r t hchoices
      cases r with
      | nil => cases t; rfl
      | @cons n s atom tail =>
          cases t with
          | @cons _ s' atom' tail' =>
              simp only [loopSequenceChoices] at hchoices
              have hret := recurrentLoopRecord_isReturnBase atom.1.2.2
              have hret' := recurrentLoopRecord_isReturnBase atom'.1.2.2
              have hsplit := controlledChain.isReturnList_append_unique
                {recurrentAugmentedState} hret hret' hchoices
              have hatomVal : atom.1 = atom'.1 :=
                recurrentLoopRecord_sigma_choices_injective hsplit.1
              have hs : s = s' := by
                apply Fin.ext
                have hr := atom.2.1
                have ht := atom'.2.1
                rw [hatomVal] at hr
                omega
              subst s'
              have hatom : atom = atom' := Subtype.ext hatomVal
              subst atom'
              have htail : tail = tail' := ih s.1 s.2 hsplit.2
              subst tail'
              rfl

theorem controlledListWord_injective_of_return {u v : List BlockChoice}
    (hu : 0 < controlledChain.listWeight recurrentAugmentedState u)
    (hv : 0 < controlledChain.listWeight recurrentAugmentedState v)
    (huend : controlledChain.listEndpoint recurrentAugmentedState u =
      recurrentAugmentedState)
    (hvend : controlledChain.listEndpoint recurrentAugmentedState v =
      recurrentAugmentedState)
    (hword : controlledListWord recurrentAugmentedState u =
      controlledListWord recurrentAugmentedState v) : u = v := by
  have hz : intervalMidpoint recurrentAugmentedState.1 ∈
      K recurrentAugmentedState.1 := intervalMidpoint_mem _
  have hinv := congrArg
    (fun w ↦ inverseWord w (intervalMidpoint recurrentAugmentedState.1)) hword
  have hprod := congrArg List.prod hword
  exact (controlledLists_eq_of_inverse_eq recurrentAugmentedState u v hu hv
    (by simpa [huend] using hz) (by simpa [hvend] using hz)
    hinv hprod).1

theorem loopSequenceWord_injective (n : ℕ) :
    Function.Injective (loopSequenceWord (n := n) : LoopSequence n → List ℕ) := by
  intro r s hword
  apply loopSequenceChoices_injective n
  apply controlledListWord_injective_of_return
  · exact loopSequence_listWeight_pos r
  · exact loopSequence_listWeight_pos s
  · exact loopSequence_endpoint r
  · exact loopSequence_endpoint s
  · simpa only [← loopSequenceWord_eq_controlled] using hword

theorem inverseWord_eq_sub_div (w : List ℕ) (z : ℚ)
    (hw : ∀ a ∈ w, 0 < a) :
    inverseWord w z = (z - (offset w : ℚ)) / (w.prod : ℚ) := by
  induction w with
  | nil => simp [inverseWord, offset]
  | cons a w ih =>
      have ha : 0 < a := hw a (by simp)
      have htail : ∀ b ∈ w, 0 < b := by
        intro b hb
        exact hw b (by simp [hb])
      have hprod : (w.prod : ℚ) ≠ 0 := by
        have hprodNat : w.prod ≠ 0 := by
          apply List.prod_ne_zero
          intro hzero
          exact (htail 0 hzero).ne' rfl
        exact_mod_cast hprodNat
      have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      rw [inverseWord, ih htail]
      simp only [inverseT, offset, Int.cast_sub, Int.cast_natCast,
        List.prod_cons, Nat.cast_mul]
      field_simp
      ring

/-- At fixed total reward, different loop concatenations have different
affine offsets. -/
theorem loopSequence_offset_injective (n : ℕ) :
    Set.InjOn (fun r : LoopSequence n ↦
      offset (loopSequenceWord (n := n) r)) Set.univ := by
  intro r _ s _ hoffset
  change offset (loopSequenceWord (n := n) r) =
    offset (loopSequenceWord (n := n) s) at hoffset
  apply loopSequenceChoices_injective n
  have hrpos : ∀ a ∈ loopSequenceWord (n := n) r, 0 < a := by
    intro a ha
    have ha2 := mem_multipliers_two_le (loopSequenceWord_mem_multipliers r a ha)
    omega
  have hspos : ∀ a ∈ loopSequenceWord (n := n) s, 0 < a := by
    intro a ha
    have ha2 := mem_multipliers_two_le (loopSequenceWord_mem_multipliers s a ha)
    omega
  have hprod : (loopSequenceWord (n := n) r).prod =
      (loopSequenceWord (n := n) s).prod := by
    rw [loopSequenceWord_prod, loopSequenceWord_prod]
  have hinv : inverseWord (loopSequenceWord (n := n) r)
      (intervalMidpoint recurrentAugmentedState.1) =
      inverseWord (loopSequenceWord (n := n) s)
        (intervalMidpoint recurrentAugmentedState.1) := by
    rw [inverseWord_eq_sub_div _ _ hrpos, inverseWord_eq_sub_div _ _ hspos,
      hoffset, hprod]
  have hchoices := controlledLists_eq_of_inverse_eq recurrentAugmentedState
    (loopSequenceChoices (n := n) r) (loopSequenceChoices (n := n) s)
    (loopSequence_listWeight_pos r) (loopSequence_listWeight_pos s)
    (by rw [loopSequence_endpoint]; exact intervalMidpoint_mem _)
    (by rw [loopSequence_endpoint]; exact intervalMidpoint_mem _)
    (by simpa only [← loopSequenceWord_eq_controlled] using hinv)
    (by simpa only [← loopSequenceWord_eq_controlled] using hprod)
  exact hchoices.1

noncomputable def loopSequenceWordFamily (n : ℕ) : Finset (List ℕ) :=
  Finset.univ.image (loopSequenceWord : LoopSequence n → List ℕ)

theorem loopSequenceWordFamily_card (n : ℕ) :
    (loopSequenceWordFamily n).card = loopSequenceCount n := by
  rw [loopSequenceWordFamily, Finset.card_image_of_injective _
    (loopSequenceWord_injective n)]
  rfl

theorem mem_loopSequenceWordFamily {n : ℕ} {w : List ℕ}
    (hw : w ∈ loopSequenceWordFamily n) :
    ∃ r : LoopSequence n, loopSequenceWord (n := n) r = w := by
  simpa [loopSequenceWordFamily] using hw

theorem loopSequenceWordFamily_data {n : ℕ} (hn : 0 < n) :
    (∀ w ∈ loopSequenceWordFamily n,
      w ≠ [] ∧ (∀ a ∈ w, a ∈ multipliers) ∧ w.prod = q ^ n) ∧
    (∀ u ∈ loopSequenceWordFamily n, ∀ v ∈ loopSequenceWordFamily n,
      u ≠ v → offset u ≠ offset v) := by
  constructor
  · intro w hw
    obtain ⟨r, rfl⟩ := mem_loopSequenceWordFamily hw
    refine ⟨?_, loopSequenceWord_mem_multipliers r, loopSequenceWord_prod r⟩
    intro hempty
    have hprod := loopSequenceWord_prod r
    rw [hempty, List.prod_nil] at hprod
    have hq : 1 < q ^ n := one_lt_pow₀ (by norm_num [q] : 1 < q) hn.ne'
    omega
  · intro u hu v hv huv hoff
    obtain ⟨r, rfl⟩ := mem_loopSequenceWordFamily hu
    obtain ⟨s, rfl⟩ := mem_loopSequenceWordFamily hv
    have hrs := loopSequence_offset_injective n (Set.mem_univ r)
      (Set.mem_univ s) hoff
    exact huv (congrArg loopSequenceWord hrs)

/-- Pigeonholing the fixed renewal window selects one common slope at every
scale. -/
theorem exists_loopSequence_count_at_scale :
    ∃ K : ℕ, ∀ M : ℕ, 0 < M → ∃ j ∈ Finset.range (K + 1),
      q ^ (M + j) < 2 * (K + 1) * loopSequenceCount (M + j) := by
  obtain ⟨K, hK⟩ := exists_uniform_renewal_window loopRewardMass
    loopRewardMass_nonneg loopRewardMass_summable tsum_loopRewardMass
    loopRewardMass_zero weighted_loopRewardMass_summable
  refine ⟨K, ?_⟩
  intro M hM
  have hwindow := hK M hM
  by_contra hnone
  push_neg at hnone
  have hterm (j : ℕ) (hj : j ∈ Finset.range (K + 1)) :
      renewalMass loopRewardMass (M + j) ≤
        (1 : ℝ) / (2 * (K + 1)) := by
    rw [renewalMass_eq_sequenceCount]
    have hjbound := hnone j hj
    have hqReal : (0 : ℝ) < q := by exact_mod_cast q_pos
    have hq : (0 : ℝ) < (q ^ (M + j) : ℕ) := by
      exact_mod_cast pow_pos q_pos (M + j)
    have hjReal : (2 * (K + 1) : ℝ) * loopSequenceCount (M + j) ≤
        (q ^ (M + j) : ℕ) := by exact_mod_cast hjbound
    have hD : (0 : ℝ) < 2 * (K + 1) := by positivity
    apply (div_le_div_iff₀ hq hD).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hjReal
  have hsum : (∑ j ∈ Finset.range (K + 1),
      renewalMass loopRewardMass (M + j)) ≤ (1 : ℝ) / 2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (K + 1),
          (1 : ℝ) / (2 * (K + 1)) := Finset.sum_le_sum hterm
      _ = (1 : ℝ) / 2 := by
        simp
        field_simp
  linarith

/-! ## Unconditional completion of the proof -/

theorem q_one_lt_unconditional : 1 < q := by norm_num [q]

theorem geometric_count_from_loop_sequences :
    ∃ denominator r₀ : ℕ, 0 < denominator ∧ ∀ r ≥ r₀,
      q ^ r ≤ denominator * countUpTo (17 * q ^ r) := by
  classical
  obtain ⟨K, hscale⟩ := exists_loopSequence_count_at_scale
  let D : ℕ := 2 * (K + 1)
  let denominator : ℕ := q ^ K * D
  refine ⟨denominator, K + 1, ?_, ?_⟩
  · dsimp [denominator, D]
    exact Nat.mul_pos (pow_pos q_pos K) (by omega)
  · intro r hr
    let M := r - K
    have hM : 0 < M := by
      dsimp [M]
      omega
    have hrEq : M + K = r := by
      dsimp [M]
      omega
    obtain ⟨j, hj, hcount⟩ := hscale M hM
    have hjle : j ≤ K := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    let n := M + j
    let W := loopSequenceWordFamily n
    have hn : 0 < n := by dsimp [n]; omega
    have hdata := loopSequenceWordFamily_data hn
    let V : Finset ℕ := W.image fun w ↦ eval w 17
    have hinj : Set.InjOn (fun w : List ℕ ↦ eval w 17) W := by
      intro u hu v hv heval
      by_contra huv
      have huData := hdata.1 u hu
      have hvData := hdata.1 v hv
      have huTwo : ∀ a ∈ u, 2 ≤ a := by
        intro a ha
        exact mem_multipliers_two_le (huData.2.1 a ha)
      have hvTwo : ∀ a ∈ v, 2 ≤ a := by
        intro a ha
        exact mem_multipliers_two_le (hvData.2.1 a ha)
      have hprod : u.prod = v.prod := huData.2.2.trans hvData.2.2.symm
      exact (eval_ne_of_prod_eq_offset_ne (by norm_num) huTwo hvTwo hprod
        (hdata.2 u hu v hv huv)) heval
    have hVcard : V.card = W.card := Finset.card_image_of_injOn hinj
    have hV : ∀ x ∈ V, Generated x ∧ x ≤ 17 * q ^ r := by
      intro x hx
      simp only [V, Finset.mem_image] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      have hwData := hdata.1 w hw
      have hgenerated : Generated (eval w 17) :=
        eval_at_seventeen_generated w hwData.2.1
      have hone : ∀ a ∈ w, 1 ≤ a := by
        intro a ha
        exact (mem_multipliers_two_le (hwData.2.1 a ha)).trans' (by omega)
      have heval : eval w 17 ≤ w.prod * 17 := eval_le_prod_mul w hone
      rw [hwData.2.2] at heval
      have hnle : n ≤ r := by
        dsimp [n]
        omega
      have hpow : q ^ n ≤ q ^ r := Nat.pow_le_pow_right q_pos hnle
      exact ⟨hgenerated, heval.trans (by
        simpa [mul_comm] using Nat.mul_le_mul_left 17 hpow)⟩
    have hVle : W.card ≤ countUpTo (17 * q ^ r) := by
      rw [← hVcard]
      exact card_le_countUpTo hV
    have hWcard : W.card = loopSequenceCount n := by
      dsimp [W]
      exact loopSequenceWordFamily_card n
    have hscaleNat : q ^ n ≤ D * W.card := by
      rw [hWcard]
      dsimp [n, D] at hcount ⊢
      omega
    have hMcount : q ^ M ≤ D * countUpTo (17 * q ^ r) := by
      have hpowM : q ^ M ≤ q ^ n := by
        apply Nat.pow_le_pow_right q_pos
        dsimp [n]
        omega
      exact hpowM.trans (hscaleNat.trans (Nat.mul_le_mul_left D hVle))
    dsimp [denominator]
    calc
      q ^ r = q ^ (M + K) := by rw [hrEq]
      _ = q ^ M * q ^ K := pow_add q M K
      _ ≤ (D * countUpTo (17 * q ^ r)) * q ^ K :=
        Nat.mul_le_mul_right (q ^ K) hMcount
      _ = q ^ K * D * countUpTo (17 * q ^ r) := by ring

/-- Erdős Problem 424, fully formalized with no recurrence or renewal
assumption left as a hypothesis. -/
theorem theorem_one : HasPositiveLowerDensity := by
  obtain ⟨denominator, r₀, hdenominator, hgeom⟩ :=
    geometric_count_from_loop_sequences
  exact positiveLowerDensity_of_geometric_count q_one_lt_unconditional
    hdenominator ⟨r₀, hgeom⟩

open Set

/-!
## Compatibility with `formal-conjectures`

The three definitions below are the definitions used in
`FormalConjectures/ErdosProblems/424.lean`.  They describe the generated set
by finite stages, whereas the main development uses the inductive predicate
`Generated`.

The linked conjecture currently uses `Set.HasPosDensity`, which asks for the
existence of a full natural-density limit.  Erdős's intended question, and
the theorem proved by Hofstadter's argument, concern positive lower density.
The theorem `erdos_424_lower_density` below states that conclusion directly
for the `formal-conjectures` generated set.
-/

/-- The new numbers obtained from `A` by applying `x * y - 1` to distinct
members of `A`.  This agrees verbatim with the `formal-conjectures`
definition. -/
def nextGeneration (A : Set ℕ) : Set ℕ :=
  {z : ℕ | ∃ x y, x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ z = x * y - 1}

/-- The finite-stage closure used by `formal-conjectures`. -/
def sequenceSet : ℕ → Set ℕ
  | 0 => {2, 3}
  | n + 1 => sequenceSet n ∪ nextGeneration (sequenceSet n)

/-- The union of all finite stages, as in `formal-conjectures`. -/
def generatedSet : Set ℕ := ⋃ n : ℕ, sequenceSet n

theorem sequenceSet_subset_succ (n : ℕ) :
    sequenceSet n ⊆ sequenceSet (n + 1) := by
  intro x hx
  exact Or.inl hx

theorem sequenceSet_mono : Monotone sequenceSet :=
  monotone_nat_of_le_succ sequenceSet_subset_succ

theorem mem_sequenceSet_generated {n x : ℕ} (hx : x ∈ sequenceSet n) :
    Generated x := by
  induction n generalizing x with
  | zero =>
      simp only [sequenceSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Generated.two
      · exact Generated.three
  | succ n ih =>
      rw [sequenceSet] at hx
      rcases hx with hx | hx
      · exact ih hx
      · obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
        exact Generated.mul_sub_one (ih ha) (ih hb) hab

theorem generated_mem_generatedSet {x : ℕ} (hx : Generated x) :
    x ∈ generatedSet := by
  rw [generatedSet, Set.mem_iUnion]
  induction hx with
  | two => exact ⟨0, by simp [sequenceSet]⟩
  | three => exact ⟨0, by simp [sequenceSet]⟩
  | @mul_sub_one a b ha hb hab iha ihb =>
      obtain ⟨na, hna⟩ := iha
      obtain ⟨nb, hnb⟩ := ihb
      refine ⟨max na nb + 1, ?_⟩
      rw [sequenceSet]
      right
      exact ⟨a, b,
        sequenceSet_mono (Nat.le_max_left na nb) hna,
        sequenceSet_mono (Nat.le_max_right na nb) hnb,
        hab, rfl⟩

theorem mem_generatedSet_generated {x : ℕ} (hx : x ∈ generatedSet) :
    Generated x := by
  rw [generatedSet, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  exact mem_sequenceSet_generated hn

/-- The staged set in `formal-conjectures` is exactly the inductively
generated set used in the proof. -/
theorem mem_generatedSet_iff (x : ℕ) : x ∈ generatedSet ↔ Generated x :=
  ⟨mem_generatedSet_generated, generated_mem_generatedSet⟩

open Classical in
theorem countUpTo_eq_generatedSet_count (x : ℕ) :
    countUpTo x =
      ((Finset.Icc 1 x).filter fun n ↦ n ∈ generatedSet).card := by
  classical
  simp only [countUpTo]
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rw [mem_generatedSet_iff]

open Classical in
/-- The intended positive-lower-density statement of Erdős Problem 424,
expressed using the exact `nextGeneration`, `sequenceSet`, and `generatedSet`
definitions from `formal-conjectures`. -/
theorem generatedSet_has_positive_lower_density :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ≤
        (((Finset.Icc 1 x).filter fun n ↦ n ∈ generatedSet).card : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := theorem_one
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound] with x hx
  rwa [← countUpTo_eq_generatedSet_count]

open Classical in
/-- The intended problem statement in the staged-set formulation. -/
theorem erdos_424_lower_density :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ≤
        (((Finset.Icc 1 x).filter fun n ↦ n ∈ generatedSet).card : ℝ) :=
  generatedSet_has_positive_lower_density

end Erdos424

#print axioms Erdos424.erdos_424_lower_density
-- 'Erdos424.erdos_424_lower_density' depends on axioms: [propext, Classical.choice, Quot.sound]
