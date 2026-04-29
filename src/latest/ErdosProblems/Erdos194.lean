/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import Mathlib.Order.KonigLemma
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Logic.Denumerable
import Mathlib.Data.Rat.Denumerable
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.RCLike.Basic

/-!
# Erdős Problem 194
Authors: Stefano Rocca, Aristotle (Harmonic)

This file proves that there exists a linear ordering `≺` of `ℝ`
with no strictly monotone arithmetic progression of length 3 (or more),
answering Erdős Problem 194 in the negative.

The proof follows:
  H. Ardal, T. Brown, V. Jungić,
  *Chaotic orderings of the rationals and reals*,
  Amer. Math. Monthly **118** (2011), 921–925.

In particular:

1. **§2 – A chaotic ordering of ℤ.** The ordering `Aₙ` on
   `[-2^{n-1}, 2^{n-1}-1]` is defined inductively by `A₁ = ⟨0, -1⟩`
   and `Aₙ₊₁ = (2Aₙ)(2Aₙ + 1)`, and is extended to all of ℤ.
   (`OrderZ` below.)
2. **§3 – A chaotic ordering of ℚ.** Every finite subset of ℚ
   can be scaled to ℤ, where the chaotic ordering of ℤ provides a
   chaotic ordering.  König's infinity lemma yields a coherent
   chaotic ordering of all of ℚ.  (`orderQ` below.)
3. **§4 – A chaotic ordering of ℝ.** A Hamel basis for ℝ over ℚ
   is well-ordered, and ℝ is ordered lexicographically by
   coefficients in ℚ, using the chaotic ordering of ℚ.
   (`orderR` below.)

## Main results

* `erdos_194`: There exists a linear ordering of `ℝ` with no `StrictMono`
  or `StrictAnti` `k`-arithmetic progression for `k ≥ 3`.

## Key definitions

* `LinearOrdering`: A binary relation that is irreflexive,
  transitive, and trichotomous.
* `ChaoticOrder`: A linear ordering with no strictly monotone 3-term
  arithmetic progression.
* `ArithProgression a d k`: The arithmetic progression
  `fun i : Fin k => a + ↑i * d`.
* `LinearOrdering.toPreorder`: Constructs a `Preorder` from a
  `LinearOrdering`, allowing the use of Mathlib's `StrictMono` /
  `StrictAnti` predicates on `ArithProgression`.

## Tags

Erdős, arithmetic progression, linear ordering, chaotic order
-/

noncomputable section

namespace Erdos194

/-! ## Basic Definitions

We introduce three lightweight notions that are used throughout:
`LinearOrdering r` packages irreflexivity, transitivity, and trichotomy for
a binary relation `r`; `LinearOrdering.toPreorder` turns such an `r` into a
Mathlib `Preorder` so that `StrictMono` / `StrictAnti` become available;
`ArithProgression a d k` is the `k`-term arithmetic progression starting at
`a` with common difference `d`; and `ChaoticOrder r` asserts that `r` admits
no 3-term arithmetic progression `a ≺ b ≺ c` with `b = (a+c)/2`. -/

/-- A linear ordering is a relation that is irreflexive,
transitive, and trichotomous. -/
structure LinearOrdering {α : Type*}
    (r : α → α → Prop) : Prop where
  /-- The relation is irreflexive. -/
  irrefl : ∀ a, ¬ r a a
  /-- The relation is transitive. -/
  trans : ∀ a b c, r a b → r b c → r a c
  /-- The relation satisfies trichotomy. -/
  tri : ∀ a b, r a b ∨ a = b ∨ r b a

/-- Construct a `Preorder` from a `LinearOrdering`, where `≼`
corresponds to `r x y ∨ x = y` and `≺` corresponds to `r`.
This allows the use of Mathlib's `StrictMono` and `StrictAnti`
predicates with respect to a custom ordering. -/
@[reducible]
def LinearOrdering.toPreorder {α : Type*}
    {r : α → α → Prop}
    (h : LinearOrdering r) : Preorder α where
  le x y := r x y ∨ x = y
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases hxy with hxy | rfl
    · rcases hyz with hyz | rfl
      · exact Or.inl (h.trans x y z hxy hyz)
      · exact Or.inl hxy
    · exact hyz
  lt a b := r a b
  lt_iff_le_not_ge a b := by
    constructor
    · intro hab
      exact ⟨Or.inl hab, fun hba => by
        rcases hba with hba | hba
        · exact h.irrefl _
            (h.trans _ _ _ hab hba)
        · subst hba; exact h.irrefl _ hab⟩
    · rintro ⟨hab | rfl, hnle⟩
      · exact hab
      · exact absurd (Or.inr rfl) hnle

/-- The function defining a finite arithmetic progression of
length `k` with first term `a` and common difference `d`. -/
def ArithProgression (a d : ℝ) (k : ℕ) : Fin k → ℝ :=
  fun i => a + (i : ℝ) * d

/-- A **chaotic ordering** has no `x ≺ y ≺ z` with `y` the
midpoint of `x` and `z`. -/
def ChaoticOrder {α : Type*} [Add α] [Mul α]
    [OfNat α 2] (r : α → α → Prop) : Prop :=
  ∀ a b c, a + c = 2 * b → ¬(r a b ∧ r b c)

/-! ## Preliminary Lemmas

The key observation (`no_strictMono_arithProgression`) is that a chaotic
ordering forbids *every* `StrictMono` or `StrictAnti` arithmetic progression
of length `k ≥ 3`: the first three terms already form a 3-AP, so the
chaotic-order condition fires immediately. -/

/-- If `r` is chaotic, then for `k ≥ 3` no `k`-AP is `StrictMono`
or `StrictAnti` with respect to the preorder induced by `r`. -/
lemma no_strictMono_arithProgression (r : ℝ → ℝ → Prop) (hchaotic : ChaoticOrder r)
    (hlin : LinearOrdering r) (k : ℕ) (hk : k ≥ 3) (a d : ℝ) :
    ¬@StrictMono _ _ _ hlin.toPreorder (ArithProgression a d k) ∧
      ¬@StrictAnti _ _ _ hlin.toPreorder (ArithProgression a d k) := by
  have h_ap : ArithProgression a d k ⟨0, by omega⟩ + ArithProgression a d k ⟨2, by omega⟩ =
      2 * ArithProgression a d k ⟨1, by omega⟩ := by
    unfold ArithProgression; push_cast; ring
  have h01 : (⟨0, by omega⟩ : Fin k) < ⟨1, by omega⟩ := by exact Fin.mk_lt_mk.mpr (by omega)
  have h12 : (⟨1, by omega⟩ : Fin k) < ⟨2, by omega⟩ := by exact Fin.mk_lt_mk.mpr (by omega)
  constructor
  · intro h
    exact hchaotic _ _ _ h_ap ⟨h h01, h h12⟩
  · intro h
    -- StrictAnti: h h01 gives r(f 1, f 0), h h12 gives r(f 2, f 1)
    have h_ap' :
        ArithProgression a d k ⟨2, by omega⟩ + ArithProgression a d k ⟨0, by omega⟩ =
          2 * ArithProgression a d k ⟨1, by omega⟩ := by
      linarith
    exact hchaotic _ _ _ h_ap' ⟨h h12, h h01⟩

/-! ## §2 – Chaotic ordering of ℤ

Following Definition 2.1 of the paper, we define the ordering `Aₙ` on
`[-2^{n-1}, 2^{n-1} - 1]` by `A₁ = ⟨0, -1⟩` and
`Aₙ₊₁ = (2Aₙ)(2Aₙ + 1)`.  Operationally this amounts to comparing
integers by their residues modulo 2 (even < odd) and then recursing
on the quotients. -/

/-- The chaotic ordering on `ℤ` defined by parity recursion.
This implements the sequence `Aₙ` from §2 of the paper:
`A₁ = ⟨0,−1⟩`, `Aₙ₊₁ = (2·Aₙ)(2·Aₙ + 1)`.

Concretely, `a ≺ b` iff the least-significant bit where `a` and `b`
differ has value 0 in `a` and 1 in `b` (using the Euclidean binary
representation of integers). -/
def OrderZBool (a b : ℤ) : Bool :=
  if a = b then false
  else if a % 2 < b % 2 then true
  else if b % 2 < a % 2 then false
  else OrderZBool (a / 2) (b / 2)
termination_by a.natAbs + b.natAbs
decreasing_by simp_all; omega

/-- Prop-valued version of the chaotic ordering on ℤ. -/
def OrderZ (a b : ℤ) : Prop :=
  OrderZBool a b = true

/-- Decidability of `OrderZ`. -/
instance OrderZ.instDecidable (a b : ℤ) : Decidable (OrderZ a b) :=
  inferInstanceAs (Decidable (OrderZBool a b = true))

/-- `OrderZ` is irreflexive. -/
lemma orderZ_irrefl (a : ℤ) : ¬OrderZ a a := by
  unfold OrderZ OrderZBool; aesop

/-
`OrderZ` is transitive.
-/
lemma orderZ_trans {a b c : ℤ} (hab : OrderZ a b) (hbc : OrderZ b c) :
    OrderZ a c := by
  revert a b c;
  -- Apply the induction hypothesis to conclude the proof.
  apply Classical.byContradiction
  intro h_contra;
  obtain ⟨a, b, c, hab, hbc, hac⟩ :
      ∃ a b c : ℤ,
        OrderZ a b ∧ OrderZ b c ∧ ¬OrderZ a c ∧
        (a.natAbs + b.natAbs + c.natAbs) =
          sInf {n : ℕ |
            ∃ a b c : ℤ,
              OrderZ a b ∧ OrderZ b c ∧ ¬OrderZ a c ∧
                n = a.natAbs + b.natAbs + c.natAbs} := by
    have h_nonempty :
        {n : ℕ |
          ∃ a b c : ℤ,
            OrderZ a b ∧ OrderZ b c ∧ ¬OrderZ a c ∧
              n = a.natAbs + b.natAbs + c.natAbs}.Nonempty := by
      push Not at h_contra;
      exact ⟨_,
        ⟨h_contra.choose, h_contra.choose_spec.choose,
          h_contra.choose_spec.choose_spec.choose,
          h_contra.choose_spec.choose_spec.choose_spec.1,
          h_contra.choose_spec.choose_spec.choose_spec.2.1,
          h_contra.choose_spec.choose_spec.choose_spec.2.2,
          rfl⟩⟩;
    have := Nat.sInf_mem h_nonempty; aesop;
  -- By definition of `OrderZ`, we know that `a % 2 = b % 2` and `b % 2 = c % 2`.
  have h_mod : a % 2 = b % 2 ∧ b % 2 = c % 2 := by
    have h_mod : a % 2 ≤ b % 2 ∧ b % 2 ≤ c % 2 ∧ c % 2 ≤ a % 2 := by
      grind +locals;
    grind +extAll;
  -- By definition of `OrderZ`, we know that the divided terms remain ordered.
  have h_div : OrderZ (a / 2) (b / 2) ∧ OrderZ (b / 2) (c / 2) := by
    unfold OrderZ at *;
    unfold OrderZBool at hab hbc; aesop;
  -- By definition of `OrderZ`, we know that `OrderZ (a / 2) (c / 2)`.
  have h_div_c : OrderZ (a / 2) (c / 2) := by
    have h_div_c :
        (a / 2).natAbs + (b / 2).natAbs + (c / 2).natAbs <
          a.natAbs + b.natAbs + c.natAbs := by
      grind;
    contrapose! h_div_c;
    exact hac.2.symm ▸ Nat.sInf_le ⟨ _, _, _, h_div.1, h_div.2, h_div_c, rfl ⟩;
  grind +locals

/-
`OrderZ` satisfies trichotomy.
-/
lemma orderZ_tri (a b : ℤ) : OrderZ a b ∨ a = b ∨ OrderZ b a := by
  revert a b;
  -- We'll use induction on the sum of the absolute values of `a` and `b`.
  have h_ind :
      ∀ a b : ℤ, a.natAbs + b.natAbs = 0 → OrderZ a b ∨ a = b ∨ OrderZ b a := by
    aesop;
  -- Apply induction on the sum of the absolute values of `a` and `b`.
  have h_ind :
      ∀ n : ℕ,
        (∀ a b : ℤ,
          a.natAbs + b.natAbs ≤ n → OrderZ a b ∨ a = b ∨ OrderZ b a) →
        ∀ a b : ℤ,
          a.natAbs + b.natAbs = n + 1 → OrderZ a b ∨ a = b ∨ OrderZ b a := by
    intros n ih a b h_sum;
    by_cases h_cases : a % 2 < b % 2 ∨ b % 2 < a % 2;
    · cases h_cases <;> unfold OrderZ <;> simp +decide [ *, OrderZBool ];
      · grind;
      · grobner;
    · -- Since $a$ and $b$ have the same parity, apply the induction hypothesis.
      have h_ind_step :
          OrderZ (a / 2) (b / 2) ∨ a / 2 = b / 2 ∨ OrderZ (b / 2) (a / 2) := by
        grind +revert;
      rcases h_ind_step with hlt | heq | hgt
      · left
        unfold OrderZ
        rw [OrderZBool]
        by_cases hab : a = b
        · subst hab
          exact (orderZ_irrefl _ hlt).elim
        · have hnot_lt : ¬a % 2 < b % 2 := fun h => h_cases (Or.inl h)
          have hnot_gt : ¬b % 2 < a % 2 := fun h => h_cases (Or.inr h)
          simpa [hab, hnot_lt, hnot_gt, OrderZ] using hlt
      · right; left
        omega
      · right; right
        unfold OrderZ
        rw [OrderZBool]
        by_cases hba : b = a
        · subst hba
          exact (orderZ_irrefl _ hgt).elim
        · have hnot_lt : ¬b % 2 < a % 2 := fun h => h_cases (Or.inr h)
          have hnot_gt : ¬a % 2 < b % 2 := fun h => h_cases (Or.inl h)
          simpa [hba, hnot_lt, hnot_gt, OrderZ] using hgt
  -- By induction, we can conclude that the statement holds for all pairs of integers.
  have h_all :
      ∀ n : ℕ,
        ∀ a b : ℤ,
          a.natAbs + b.natAbs ≤ n → OrderZ a b ∨ a = b ∨ OrderZ b a := by
    intro n
    induction n with
    | zero =>
        intro a b hab
        have hsum : a.natAbs + b.natAbs = 0 := Nat.eq_zero_of_le_zero hab
        have ha : a = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_add_eq_zero_right hsum)
        have hb : b = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_add_eq_zero_left hsum)
        exact Or.inr (Or.inl (by rw [ha, hb]))
    | succ n ih =>
        intro a b hab
        by_cases hsum : a.natAbs + b.natAbs = n + 1
        · exact h_ind n ih a b hsum
        · exact ih a b (Nat.le_of_lt_succ (lt_of_le_of_ne hab hsum))
  exact fun a b => h_all _ _ _ le_rfl

/-- `OrderZ` defines a linear ordering on ℤ (Lemma 2.1 + Definition 2.2). -/
lemma orderZ_isLinear : LinearOrdering OrderZ where
  irrefl := orderZ_irrefl
  trans := fun _ _ _ => orderZ_trans
  tri := orderZ_tri

/-
When `a ≠ b` and `a % 2 = b % 2`, `OrderZ a b ↔ OrderZ (a/2) (b/2)`.
-/
lemma orderZ_recurse {a b : ℤ} (hne : a ≠ b) (hmod : a % 2 = b % 2) :
    OrderZ a b ↔ OrderZ (a / 2) (b / 2) := by
  unfold OrderZ;
  rw [ OrderZBool ];
  grind

/-
If `a + c = 2b` and `a ≺ b`, then `a, b, c` all have the
same parity (otherwise `b ≺ c` is impossible).
-/
lemma ap_orderZ_same_parity {a b c : ℤ} (h : a + c = 2 * b)
    (hab : OrderZ a b) (hbc : OrderZ b c) : a % 2 = b % 2 := by
  by_contra hne
  have h_ac : a % 2 = c % 2 := by
    omega
  have orderZ_mod_lt_of_ne :
      ∀ {x y : ℤ}, OrderZ x y → x % 2 ≠ y % 2 → x % 2 < y % 2 := by
    intro x y hxy hxy_ne
    have hxy' := hxy
    unfold OrderZ at hxy'
    rw [OrderZBool] at hxy'
    by_cases h_eq : x = y
    · subst h_eq
      exact (hxy_ne rfl).elim
    · by_cases h_lt : x % 2 < y % 2
      · exact h_lt
      · by_cases h_gt : y % 2 < x % 2
        · simp [h_eq, h_lt, h_gt] at hxy'
        · have h_eq_mod : x % 2 = y % 2 := le_antisymm (le_of_not_gt h_gt) (le_of_not_gt h_lt)
          exact (hxy_ne h_eq_mod).elim
  have hab_lt : a % 2 < b % 2 := orderZ_mod_lt_of_ne hab hne
  have hbc_ne : b % 2 ≠ c % 2 := by
    intro hbc_eq
    exact hne (by rw [h_ac, ← hbc_eq])
  have hbc_lt : b % 2 < c % 2 := orderZ_mod_lt_of_ne hbc hbc_ne
  omega

/-
The ordering `OrderZ` on ℤ is chaotic (Theorem 2.2):
no 3-AP is strictly monotone.
-/
theorem orderZ_chaotic : ChaoticOrder OrderZ := by
  -- By contradiction, assume there exist $a, b, c$ such that $a \prec b \prec c$ and $a + c = 2b$.
  by_contra h_contra;
  -- Obtain such a, b, c from the assumption.
  obtain ⟨a, b, c, h_sum, h_order⟩ :
      ∃ a b c : ℤ, a + c = 2 * b ∧ OrderZ a b ∧ OrderZ b c := by
    unfold ChaoticOrder at h_contra; aesop;
  -- Choose a counterexample minimizing the sum of absolute values.
  obtain ⟨a, b, c, h_sum, h_order, h_min⟩ :
      ∃ a b c : ℤ,
        a + c = 2 * b ∧ OrderZ a b ∧ OrderZ b c ∧
          ∀ a' b' c',
            a' + c' = 2 * b' →
            OrderZ a' b' →
            OrderZ b' c' →
            Int.natAbs a' + Int.natAbs b' + Int.natAbs c' ≥
              Int.natAbs a + Int.natAbs b + Int.natAbs c := by
    have h_well_founded : WellFounded fun x y : ℕ => x < y := by
      exact wellFounded_lt;
    have := h_well_founded.has_min
      { n : ℕ |
        ∃ a b c : ℤ,
          a + c = 2 * b ∧ OrderZ a b ∧ OrderZ b c ∧
            n = Int.natAbs a + Int.natAbs b + Int.natAbs c }
      ⟨_, ⟨a, b, c, h_sum, h_order.1, h_order.2, rfl⟩⟩;
    rcases this with ⟨n, ⟨a, b, c, h₁, h₂, h₃, rfl⟩, h₄⟩
    exact ⟨a, b, c, h₁, h₂, h₃, fun a' b' c' h₅ h₆ h₇ =>
      not_lt.1 fun h₈ => h₄ _ ⟨a', b', c', h₅, h₆, h₇, rfl⟩ h₈⟩ ;
  -- By `ap_orderZ_same_parity`, `a % 2 = b % 2`.
  have h_parity_ab : a % 2 = b % 2 := by
    apply ap_orderZ_same_parity h_sum h_order h_min.left;
  -- Since `a + c = 2b`, the integers `a` and `c` share the same parity.
  have h_parity_ac : a % 2 = c % 2 := by
    omega;
  -- Recurse from `a,b,c` to their halves.
  have h_recurse_ab : OrderZ a b ↔ OrderZ (a / 2) (b / 2) := by
    apply orderZ_recurse;
    · rintro rfl; simp_all +decide [ OrderZ ];
      unfold OrderZBool at h_order; aesop;
    · exact h_parity_ab
  have h_recurse_bc : OrderZ b c ↔ OrderZ (b / 2) (c / 2) := by
    apply orderZ_recurse;
    · rintro rfl;
      exact orderZ_irrefl _ h_min.1;
    · linarith;
  grind +locals

/-! ## §3 – Chaotic orderings of finite rational sets

The main idea is that every finite set of rationals can be uniformly
scaled to a set of integers (`finiteQ_integerScaling`), so the chaotic
ordering `OrderZ` of ℤ induces a chaotic ordering on any finite subset of ℚ
(`finiteQ_hasChaoticOrder`).  This is the first step of the paper's §3. -/

/-- Every finite set of rationals can be scaled to
integers. -/
lemma finiteQ_integerScaling (S : Finset ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∀ q ∈ S, ∃ n : ℤ, (m : ℚ) * q = ↑n := by
  let m := S.prod (fun q => q.den)
  refine ⟨m, Finset.prod_pos fun q hq => Nat.cast_pos.mpr q.pos, fun q hq => ?_⟩
  use m * q.num / q.den
  rw [Int.cast_div_charZero]
  · simp [mul_div_assoc, Rat.num_div_den]
  · exact dvd_mul_of_dvd_left (mod_cast Finset.dvd_prod_of_mem _ hq) _

/-- Every finite subset of `ℚ` admits a chaotic linear
ordering (cf. §3, first paragraph). -/
lemma finiteQ_hasChaoticOrder
    (n : ℕ) (vals : Fin n → ℚ) (hvals : Function.Injective vals) :
    ∃ r : Fin n → Fin n → Prop,
      (∀ i, ¬r i i) ∧
      (∀ i j k, r i j → r j k → r i k) ∧
      (∀ i j, i ≠ j → r i j ∨ r j i) ∧
      (∀ i j k, vals i + vals k = 2 * vals j → ¬(r i j ∧ r j k)) := by
  obtain ⟨m, hm_pos, h_shift⟩ :
      ∃ m : ℕ, 0 < m ∧ ∀ i : Fin n, ∃ n : ℤ, (m : ℚ) * vals i = ↑n := by
    have := finiteQ_integerScaling (Finset.univ.image vals)
    aesop
  choose f hf using h_shift
  -- Map each rational `vals i` to the integer `f i` via scaling by `m`.
  -- Use the chaotic ordering `OrderZ` on ℤ directly.
  set embed : Fin n → ℤ := f
  refine ⟨fun i j => OrderZ (embed i) (embed j), ?_, ?_, ?_, ?_⟩
  · exact fun i => orderZ_irrefl _
  · exact fun i j k hij hjk => orderZ_trans hij hjk
  · intro i j hij
    have h_distinct : embed i ≠ embed j := by
      have h_distinct : f i ≠ f j := by
        exact fun h => hij <| hvals <| by
          rw [← @Int.cast_inj ℚ] at *
          nlinarith [hf i, hf j, (by norm_cast : (0 : ℚ) < m)]
      exact h_distinct
    have := orderZ_isLinear.tri (embed i) (embed j)
    aesop
  · intros i j k h_eq h_order
    have h_sum : (embed i : ℤ) + (embed k : ℤ) = 2 * (embed j : ℤ) := by
      exact_mod_cast (by nlinarith [(by norm_cast : (1 : ℚ) ≤ m), hf i, hf j, hf k] :
        (f i + f k : ℚ) = 2 * f j)
    exact orderZ_chaotic _ _ _ h_sum h_order

/-! ## §3 (cont.) – Tree of compatible chaotic orders and König's lemma

We build an infinite finitely-branching tree (`TreeT`) whose level `n` consists
of all chaotic orderings of the first `n + 1` rationals (under a fixed
enumeration `Qenum`).  Each level is nonempty (`treeQ_nonemptyLevels`) and
finite (`treeQ_finiteLevels`), so König's infinity lemma
(`exists_seq_forall_proj_of_forall_finite`) yields an infinite branch
(`treeQ_infiniteBranch`) — a coherent system of chaotic orderings that
extends consistently to all of ℚ. -/

/-- An enumeration of `ℚ` as a bijection with `ℕ`. -/
def Qenum : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm

/-- The tree of chaotic orderings: level `n` has all chaotic
orderings of `{q₀, …, qₙ}`. -/
def TreeT (n : ℕ) : Type :=
  {r : Fin (n + 1) → Fin (n + 1) → Bool //
    (∀ i, r i i = false) ∧ (∀ i j k, r i j = true → r j k = true → r i k = true) ∧
    (∀ i j, i ≠ j → r i j = true ∨ r j i = true) ∧
    (∀ i j k : Fin (n + 1),
      Qenum (i : ℕ) + Qenum (k : ℕ) = 2 * Qenum (j : ℕ) →
        ¬(r i j = true ∧ r j k = true))}

open Classical in
/-- Every level of the tree is nonempty. -/
lemma treeQ_nonemptyLevels (n : ℕ) :
    Nonempty (TreeT n) := by
  obtain ⟨r, hr⟩ := finiteQ_hasChaoticOrder (n + 1)
      (fun i : Fin (n + 1) => Qenum i)
      (by exact fun i j h => by simpa [Fin.ext_iff] using Qenum.injective h)
  exact ⟨⟨fun i j => decide (r i j), by simpa using hr⟩⟩

/-- Every level of the tree is finite. -/
instance treeQ_finiteLevels (n : ℕ) : Finite (TreeT n) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- König's infinity lemma applied to our tree of chaotic
orderings. -/
lemma treeQ_infiniteBranch :
    ∃ f : (n : ℕ) → TreeT n, ∀ n (i j : Fin (n + 1)),
      (f (n + 1)).val (Fin.castSucc i) (Fin.castSucc j) = (f n).val i j := by
  set α : ℕ → Type := fun n => TreeT n
  set π : {i j : ℕ} → i ≤ j → α j → α i :=
    fun hij r =>
      ⟨fun i j => r.val (Fin.castLE (by omega) i) (Fin.castLE (by omega) j),
        by grind⟩
  have h_konig : ∃ f : ∀ n, α n, ∀ i j hij, π hij (f j) = f i := by
    apply_rules [exists_seq_forall_proj_of_forall_finite]
    · aesop
    · aesop
    · exact fun i a => Set.toFinite {b | π (Nat.le_add_right i 1) b = a}
    · exact fun i => treeQ_nonemptyLevels i
  obtain ⟨f, hf⟩ := h_konig
  use f
  intro n i j
  specialize hf n (n + 1) (Nat.le_succ _)
  replace hf := congr_arg (fun x => x.val i j) hf
  aesop

/-! ## Chaotic ordering of ℚ

From the infinite branch produced by König's lemma we extract a single
chaotic linear ordering `orderQ` on `ℚ` (Theorem 3.1 of the paper).
`CompatibleChain` is the chosen branch, `compatibleChain_spec` records its
coherence, and `compatibleChain_agree` generalises the coherence to
arbitrary level gaps.  The main results are `orderQ_linear` (linearity)
and `orderQ_chaotic` (no monotone 3-AP). -/

/-- Extract a specific compatible chain using choice. -/
def CompatibleChain : (n : ℕ) → TreeT n :=
  treeQ_infiniteBranch.choose

/-- The compatible chain property. -/
lemma compatibleChain_spec (n : ℕ) (i j : Fin (n + 1)) :
    (CompatibleChain (n + 1)).val (Fin.castSucc i) (Fin.castSucc j) = (CompatibleChain n).val i j :=
  treeQ_infiniteBranch.choose_spec n i j

/-- The chaotic ordering on `ℚ` (Theorem 3.1). -/
def orderQ (a b : ℚ) : Prop :=
  let ia := (Denumerable.eqv ℚ) a
  let ib := (Denumerable.eqv ℚ) b
  let n := max ia ib
  (CompatibleChain n).val ⟨ia, by omega⟩ ⟨ib, by omega⟩ = true

/-- The compatible chain at level `m` agrees with level `n`
on shared indices. -/
lemma compatibleChain_agree {n m : ℕ} (hnm : n ≤ m) (i j : Fin (n + 1)) :
    (CompatibleChain m).val (⟨i, by omega⟩) (⟨j, by omega⟩) =
      (CompatibleChain n).val i j := by
  induction hnm with
  | refl => rfl
  | step hmx ih =>
  convert compatibleChain_spec _ ⟨i, ?_⟩ ⟨j, ?_⟩ using 1
  exact ih.symm

/-- `orderQ` value at a larger level agrees with the defining
level. -/
lemma orderQ_at_level (a b : ℚ) (n : ℕ)
    (ha : (Denumerable.eqv ℚ) a ≤ n) (hb : (Denumerable.eqv ℚ) b ≤ n) :
    ((CompatibleChain n).val
      ⟨(Denumerable.eqv ℚ) a, by omega⟩
      ⟨(Denumerable.eqv ℚ) b, by omega⟩ = true) ↔
      orderQ a b := by
  rw [orderQ]
  rw [← compatibleChain_agree
    (show max (Denumerable.eqv ℚ a) (Denumerable.eqv ℚ b) ≤ n from max_le ha hb)]

/-- `orderQ` is a linear ordering on `ℚ` (Theorem 3.1). -/
lemma orderQ_linear : LinearOrdering orderQ := by
  constructor
  · intro a
    unfold orderQ
    grind
  · intro a b c hab hbc
    obtain ⟨n, hn⟩ :
        ∃ n,
          (Denumerable.eqv ℚ) a ≤ n ∧
          (Denumerable.eqv ℚ) b ≤ n ∧
          (Denumerable.eqv ℚ) c ≤ n := by
      exact ⟨Max.max (Denumerable.eqv ℚ a)
          (Max.max (Denumerable.eqv ℚ b) (Denumerable.eqv ℚ c)),
        le_max_left _ _,
        le_max_of_le_right (le_max_left _ _),
        le_max_of_le_right (le_max_right _ _)⟩
    have h_chain :
        (CompatibleChain n).val
            ⟨(Denumerable.eqv ℚ) a, by omega⟩
            ⟨(Denumerable.eqv ℚ) b, by omega⟩ = true ∧
          (CompatibleChain n).val
            ⟨(Denumerable.eqv ℚ) b, by omega⟩
            ⟨(Denumerable.eqv ℚ) c, by omega⟩ = true := by
      exact ⟨orderQ_at_level a b n hn.1 hn.2.1 |>.2 hab,
        orderQ_at_level b c n hn.2.1 hn.2.2 |>.2 hbc⟩
    exact orderQ_at_level a c n hn.1
      hn.2.2 |>.1 <| by
        have := (CompatibleChain n).2.2.1
        aesop
  · intro a b
    set ia := (Denumerable.eqv ℚ) a
    set ib := (Denumerable.eqv ℚ) b
    set n := max ia ib
    have h_tree :
        ∀ i j : Fin (n + 1),
          (CompatibleChain n).val i j ∨ i = j ∨ (CompatibleChain n).val j i := by
      grind
    specialize h_tree ⟨ia, by omega⟩ ⟨ib, by omega⟩
    convert h_tree using 1
    rw [orderQ_at_level]
    · simp +zetaDelta at *
    · exact le_max_right _ _
    · exact le_max_left _ _

/-- `orderQ` is chaotic (Theorem 3.1). -/
theorem orderQ_chaotic : ChaoticOrder orderQ := by
  intros a b c h_eq h_order
  obtain ⟨n, hn⟩ :
      ∃ n : ℕ,
        (Denumerable.eqv ℚ) a ≤ n ∧
        (Denumerable.eqv ℚ) b ≤ n ∧
        (Denumerable.eqv ℚ) c ≤ n := by
    exact ⟨Max.max (Denumerable.eqv ℚ a)
        (Max.max (Denumerable.eqv ℚ b) (Denumerable.eqv ℚ c)),
      le_max_left _ _,
      le_max_of_le_right (le_max_left _ _),
      le_max_of_le_right (le_max_right _ _)⟩
  have h_chain :
      (CompatibleChain n).val
          ⟨(Denumerable.eqv ℚ) a, by omega⟩
          ⟨(Denumerable.eqv ℚ) b, by omega⟩ = true ∧
        (CompatibleChain n).val
          ⟨(Denumerable.eqv ℚ) b, by omega⟩
          ⟨(Denumerable.eqv ℚ) c, by omega⟩ = true := by
    exact ⟨orderQ_at_level a b n hn.1 hn.2.1 |>.2 h_order.1,
      orderQ_at_level b c n hn.2.1 hn.2.2 |>.2 h_order.2⟩
  have h_ap :
      Qenum ((⟨(Denumerable.eqv ℚ) a, by linarith⟩ : Fin (n + 1)) : ℕ) +
          Qenum ((⟨(Denumerable.eqv ℚ) c, by linarith⟩ : Fin (n + 1)) : ℕ) =
        2 * Qenum ((⟨(Denumerable.eqv ℚ) b, by linarith⟩ : Fin (n + 1)) : ℕ) := by
    unfold Qenum
    aesop
  exact (CompatibleChain n).2.2.2.2
    ⟨(Denumerable.eqv ℚ) a, by linarith⟩
    ⟨(Denumerable.eqv ℚ) b, by linarith⟩
    ⟨(Denumerable.eqv ℚ) c, by linarith⟩
    h_ap h_chain

/-! ## §4 – Linear algebra setup for ℝ over ℚ

We fix a Hamel basis `HamelBasis` of `ℝ` as a `ℚ`-vector space and
record that its index set `QBASIS_R` admits a well-ordering
(`basisOrder_def`).  The auxiliary lemma
`first_differing_coefficient_exists` states that two distinct reals
must differ in at least one basis coefficient — the starting point
for the lexicographic comparison in §4 (cont.). -/

/-- The index type for a Hamel basis of `ℝ` over `ℚ`. -/
def QBASIS_R : Type := (Module.Free.exists_basis ℚ ℝ).some.1

/-- The Hamel basis of `ℝ` over `ℚ`. -/
def HamelBasis : Module.Basis QBASIS_R ℚ ℝ := (Module.Free.exists_basis ℚ ℝ).some.2

/-- The basis index set can be well-ordered. -/
lemma basisOrder_def : IsWellOrder QBASIS_R WellOrderingRel := WellOrderingRel.isWellOrder

/-- If `a ≠ b`, there exists a basis element where their
coefficients first differ. -/
lemma first_differing_coefficient_exists (a b : ℝ) (hab : a ≠ b) :
    ∃ i : QBASIS_R, HamelBasis.repr a i ≠ HamelBasis.repr b i := by
  exact Classical.not_forall.1 fun h => hab <| HamelBasis.repr.injective <| by ext i; simp [h]

/-! ## §4 (cont.) – Chaotic ordering of ℝ

The chaotic ordering `orderR` on `ℝ` is defined lexicographically:
given `a ≠ b`, find the well-order-least basis index `i` where the
Hamel-basis coefficients of `a` and `b` differ, and compare those
coefficients using the chaotic ordering `orderQ` of ℚ.  The resulting
relation is linear (`orderR_linear`).  It is also chaotic
(`orderR_chaotic`) because in any 3-AP `a + c = 2b` the
coordinatewise midpoint identity `aᵢ + cᵢ = 2bᵢ` reduces the
problem to the chaoticity of `orderQ`. -/

/-- The chaotic ordering on `ℝ` via Hamel basis and lexicographic comparison with
respect to the chaotic ordering on `ℚ` (§4 of the paper). -/
def orderR (a b : ℝ) : Prop := ∃ i : QBASIS_R, HamelBasis.repr a i ≠ HamelBasis.repr b i ∧
    (∀ j : QBASIS_R, WellOrderingRel j i → HamelBasis.repr a j = HamelBasis.repr b j) ∧
    orderQ (HamelBasis.repr a i) (HamelBasis.repr b i)

/-- `orderR` is a linear ordering on `ℝ`. -/
lemma orderR_linear : LinearOrdering orderR := by
  constructor
  · unfold orderR; aesop
  · intro a b c
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    by_cases hij : WellOrderingRel i j
    · refine ⟨i, ?_, ?_, ?_⟩
      · intro h_eq
        exact hi.1 (by rw [h_eq, ← hj.2.1 i hij])
      · intro k hk
        rw [hi.2.1 k hk, hj.2.1 k (lt_trans hk hij)]
      · exact (hj.2.1 i hij) ▸ hi.2.2
    · by_cases hji : WellOrderingRel j i
      · have := hi.2.1 j hji
        use j
        exact ⟨by aesop,
          fun k hk => by rw [hi.2.1 k (lt_trans hk hji), hj.2.1 k hk],
          by rw [this]; exact hj.2.2⟩
      · have hij_eq : i = j := by
          exact Classical.not_not.1 fun h =>
            hij <| by
              have := basisOrder_def.trichotomous i j
              tauto
        have h_trans : orderQ (HamelBasis.repr a i) (HamelBasis.repr c i) := by
          have h_trans : ∀ x y z : ℚ, orderQ x y → orderQ y z → orderQ x z := by
            exact fun x y z hxy hyz => orderQ_linear.trans x y z hxy hyz
          aesop
        grind +locals
  · intro a b
    by_cases hab : a = b
    · exact Or.inr (Or.inl hab)
    obtain ⟨i, hi⟩ :
        ∃ i : QBASIS_R,
          HamelBasis.repr a i ≠ HamelBasis.repr b i ∧
            ∀ j : QBASIS_R,
              HamelBasis.repr a j ≠ HamelBasis.repr b j → ¬WellOrderingRel j i := by
      have h_nonempty : ∃ i : QBASIS_R, HamelBasis.repr a i ≠ HamelBasis.repr b i :=
        first_differing_coefficient_exists a b hab
      have h_well_founded :
          WellFounded (WellOrderingRel : QBASIS_R → QBASIS_R → Prop) :=
        IsWellFounded.wf
      exact WellFounded.has_min h_well_founded
        (fun a_1 => (HamelBasis.repr a) a_1 = (HamelBasis.repr b) a_1 → False) h_nonempty
    rcases orderQ_linear.tri (HamelBasis.repr a i) (HamelBasis.repr b i) with h | h | h
    · exact Or.inl
        ⟨i, hi.1, fun j hj => Classical.not_not.1 fun hj' => hi.2 j hj' hj, h⟩
    · exact (hi.1 h).elim
    · exact Or.inr (Or.inr
        ⟨i, hi.1.symm, fun j hj => (Classical.not_not.1 fun hj' => hi.2 j hj' hj).symm,
          h⟩)

/-- If `a + c = 2b`, then coordinatewise
`aᵢ + cᵢ = 2bᵢ`. -/
lemma midpoint_coeffwise (a b c : ℝ) (h : a + c = 2 * b) (i : QBASIS_R) :
    HamelBasis.repr a i + HamelBasis.repr c i = 2 * HamelBasis.repr b i := by
  have h_i := congr_arg (fun x => HamelBasis.repr x i) h
  simpa [two_mul] using h_i

/-- The ordering `orderR` on `ℝ` is chaotic (Theorem 4.1). -/
theorem orderR_chaotic : ChaoticOrder orderR := by
  intro a b c h
  by_contra h_contra
  obtain ⟨i, hi⟩ := (h_contra.left : orderR a b)
  obtain ⟨j, hj⟩ := (h_contra.right : orderR b c)
  have hij : i = j := by
    by_cases h_cases : WellOrderingRel i j
    · have := midpoint_coeffwise a b c h i
      grind +ring
    · by_cases h_cases' : WellOrderingRel j i
      · have := midpoint_coeffwise a b c h j
        simp_all [two_mul]
      · cases trichotomous_of WellOrderingRel i j <;> tauto
  have h_midpoint : HamelBasis.repr a i + HamelBasis.repr c i = 2 * HamelBasis.repr b i := by
    convert midpoint_coeffwise a b c h i
      using 1
  have := orderQ_chaotic (HamelBasis.repr a i) (HamelBasis.repr b i) (HamelBasis.repr c i)
  simp_all [two_mul]

/-! ## Main theorem

Combining `orderR_chaotic` (no monotone 3-AP) with
`no_strictMono_arithProgression` (a chaotic ordering forbids
`StrictMono`/`StrictAnti` APs of length `≥ 3`), we obtain the
full statement of Erdős Problem 194. -/

/-- **Erdős Problem 194 (main theorem, Theorem 4.1)**: There exists a
linear ordering of `ℝ` (namely `orderR`) with no `StrictMono` or
`StrictAnti` `k`-term arithmetic progression for any `k ≥ 3`.

A strictly monotone AP is one where `ArithProgression a d k : Fin k → ℝ` is
`StrictMono` or `StrictAnti` with respect to the preorder induced
by the ordering. -/
theorem erdos_194 : ∃ (r : ℝ → ℝ → Prop) (hlin : LinearOrdering r),
    ∀ k : ℕ, k ≥ 3 → ∀ a d : ℝ,
      ¬@StrictMono _ _ _ hlin.toPreorder (ArithProgression a d k) ∧
        ¬@StrictAnti _ _ _ hlin.toPreorder (ArithProgression a d k) := by
  refine ⟨orderR, orderR_linear, ?_⟩
  intro k hk a d
  exact no_strictMono_arithProgression _ orderR_chaotic orderR_linear k hk a d

#print axioms erdos_194
-- 'Erdos194.erdos_194' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos194
