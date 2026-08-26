/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The standard structure on Mathlib's `ZFSet`, DeepMind's proposition, and the two-valued unfolding
of `Erdos501_f` in the standard structure.
-/
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Sentence

set_option relaxedAutoImplicit true

/-!
# The standard structure and the two-valued unfolding of `Erdos501_f`

This file is the first half of the *bridge* between the sentence `Erdos501_f` (`Sentence.lean`) and
DeepMind's proposition `erdos501_deepmind` (the right-hand side of `erdos_501` in
`formal-conjectures`).  It contains

* `erdos501_deepmind : Prop`, the DeepMind proposition verbatim;
* `stdStructure : Structure L_ZFC`, Mathlib's `ZFSet` with `∅`, Kuratowski pairs, `ω`, the power set,
  the union and `∈`;
* the two-valued predicates `StdSem.*` on `ZFSet` mirroring the blocks of `Sentence.lean` (exactly
  as `Sem.*` of `Semantics.lean` does for Boolean values), and the computation
  `realize_Erdos501_f_std : (stdStructure ⊨ₘ Erdos501_f) ↔ StdSem.erdos501`;
* a small `ZFSet` toolkit: the finite von Neumann ordinals `natZ n`, the characterization
  `mem_omega_iff` of the elements of `ZFSet.omega`, and the value `fval f x` of a function `f`
  (given as a set of pairs) at `x`.

The specification `stdStructure ⊨ₘ Erdos501_f ↔ erdos501_deepmind` itself is proved in
`Bridge.lean` from the two directions established in `RealsInZFSet.lean` and `ZFSetCOF.lean`.
-/

open Fol

namespace Flypitch.Erdos501

/-- The first question of Erdős problem #501, exactly as formalized in DeepMind's
`formal-conjectures` (`Erdos501.erdos_501 : answer(sorry) ↔ erdos501_deepmind`). -/
def erdos501_deepmind : Prop :=
  ∀ (A : ℝ → Set ℝ),
    (∀ x, Bornology.IsBounded (A x)) →
    (∀ x, MeasureTheory.volume.toOuterMeasure (A x) < 1) →
    ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y)

/-- Interpretation of the function symbols of `L_ZFC` in Mathlib's `ZFSet`. -/
noncomputable def stdFunMap : ∀ {n : ℕ}, L_ZFC.functions n → DVec ZFSet.{0} n → ZFSet.{0}
  | _, ZFC_func.emptyset, _ => ∅
  | _, ZFC_func.pr, DVec.cons x (DVec.cons y DVec.nil) => ZFSet.pair x y
  | _, ZFC_func.ω, _ => ZFSet.omega
  | _, ZFC_func.P, DVec.cons x DVec.nil => ZFSet.powerset x
  | _, ZFC_func.Union, DVec.cons x DVec.nil => ZFSet.sUnion x

/-- Interpretation of the relation symbol `∈` of `L_ZFC` in Mathlib's `ZFSet`. -/
def stdRelMap : ∀ {n : ℕ}, L_ZFC.relations n → DVec ZFSet.{0} n → Prop
  | _, ZFC_rel.ε, DVec.cons x (DVec.cons y DVec.nil) => x ∈ y

/-- The standard structure for `L_ZFC`: Mathlib's `ZFSet`, with `∅`, Kuratowski pairs, `ω`, the
power set, the union, and `∈`. -/
noncomputable def stdStructure : Structure L_ZFC where
  carrier := ZFSet.{0}
  fun_map := stdFunMap
  rel_map := stdRelMap

/-! ### Simp lemmas for the realization in the standard structure -/

@[simp] lemma std_forall {C : stdStructure → Prop} :
    (∀ x : stdStructure, C x) = ∀ x : ZFSet.{0}, C x := rfl

@[simp] lemma std_exists {C : stdStructure → Prop} :
    (∃ x : stdStructure, C x) = ∃ x : ZFSet.{0}, C x := rfl

@[simp] lemma std_eq {a b : stdStructure} : (a = b) = (@Eq ZFSet.{0} a b) := rfl

@[simp] lemma std_realize_bounded_formula_mem' {n} {v : DVec stdStructure n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    realize_bounded_formula v (mem' t₁ t₂) DVec.nil =
      @Membership.mem ZFSet.{0} ZFSet.{0} _ (realize_bounded_term v t₂ DVec.nil)
        (realize_bounded_term v t₁ DVec.nil) := rfl

@[simp] lemma std_realize_bounded_term_Powerset' {n} {v : DVec stdStructure n}
    (t : bounded_term L_ZFC n) :
    @Eq ZFSet.{0} (realize_bounded_term v (P' t) DVec.nil)
      (ZFSet.powerset (realize_bounded_term v t DVec.nil)) := rfl

@[simp] lemma std_realize_bounded_term_omega' {n} {v : DVec stdStructure n} :
    @Eq ZFSet.{0} (realize_bounded_term v ω' DVec.nil) ZFSet.omega := rfl

@[simp] lemma std_realize_bounded_term_emptyset' {n} {v : DVec stdStructure n} :
    @Eq ZFSet.{0} (realize_bounded_term v ∅' DVec.nil) ∅ := rfl

@[simp] lemma std_realize_bounded_term_pair' {n} {v : DVec stdStructure n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    @Eq ZFSet.{0} (realize_bounded_term v (pair' t₁ t₂) DVec.nil)
      (ZFSet.pair (realize_bounded_term v t₁ DVec.nil) (realize_bounded_term v t₂ DVec.nil)) := rfl

/-- The two-valued analogue of `boolean_realize_bounded_formula_or`. -/
@[simp] lemma realize_bounded_formula_or' {L : Language} {S : Structure L} {n} {v : DVec S n}
    {f g : bounded_formula L n} :
    realize_bounded_formula v (bd_or f g) DVec.nil ↔
      (realize_bounded_formula v f DVec.nil ∨ realize_bounded_formula v g DVec.nil) := by
  simp only [bd_or, realize_bounded_formula_imp, realize_bounded_formula_not]
  constructor
  · intro h; by_cases hf : realize_bounded_formula v f DVec.nil
    · exact Or.inl hf
    · exact Or.inr (h hf)
  · rintro (hf | hg) hnf
    · exact absurd hf hnf
    · exact hg

/-! ### Two-valued predicates on `ZFSet` -/

namespace StdSem

/-- `x < y`, for an order relation `ltR` given as a set of ordered pairs (`ltF`). -/
def lt (ltR x y : ZFSet.{0}) : Prop := ZFSet.pair x y ∈ ltR

/-- `x ≤ y`, i.e. `x < y ∨ x = y` (`leF`). -/
def le (ltR x y : ZFSet.{0}) : Prop := lt ltR x y ∨ x = y

/-- `f(x) = y`, for a function `f` given as a set of ordered pairs (`appF`). -/
def app (f x y : ZFSet.{0}) : Prop := ZFSet.pair x y ∈ f

/-- `op(x, y) = z`, for a binary operation `op` given as a set of pairs `((x, y), z)` (`app2F`). -/
def app2 (op x y z : ZFSet.{0}) : Prop := ZFSet.pair (ZFSet.pair x y) z ∈ op

/-- `f` is a (total, single-valued) function from `dom` to `cod` (`isFunF`). -/
def isFun (dom cod f : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ dom → ∃ y : ZFSet.{0}, y ∈ cod ∧
    (app f x y ∧ ∀ y' : ZFSet.{0}, app f x y' → y' = y)

/-- `op` is a binary operation on `R` (`isOp2F`). -/
def isOp2 (R op : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∀ y : ZFSet.{0}, y ∈ R → ∃ z : ZFSet.{0}, z ∈ R ∧
    (app2 op x y z ∧ ∀ z' : ZFSet.{0}, app2 op x y z' → z' = z)

/-- `m = n ∪ {n}` (`succF`). -/
def succ (n m : ZFSet.{0}) : Prop :=
  ∀ z : ZFSet.{0}, (z ∈ m ↔ z ∈ n ∨ z = n)

/-! #### The axioms of a complete ordered field, one by one -/

/-- Associativity of `op` on `R`. -/
def assoc (R op : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∀ y : ZFSet.{0}, y ∈ R → ∀ z : ZFSet.{0}, z ∈ R →
    ∀ u : ZFSet.{0}, ∀ v : ZFSet.{0}, ∀ w : ZFSet.{0}, ∀ w' : ZFSet.{0},
      app2 op x y u → (app2 op u z v → (app2 op y z w → (app2 op x w w' → v = w')))

/-- Commutativity of `op` on `R`. -/
def comm (R op : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∀ y : ZFSet.{0}, y ∈ R → ∀ u : ZFSet.{0},
    app2 op x y u → app2 op y x u

/-- `e` is a right identity for `op` on `R`: `x ∘ e = x`. -/
def ident (R op e : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → app2 op x e x

/-- Additive inverses. -/
def addInv (R plus zero : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∃ y : ZFSet.{0}, y ∈ R ∧ app2 plus x y zero

/-- Multiplicative inverses of nonzero elements. -/
def mulInv (R times zero one : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → (¬ x = zero → ∃ y : ZFSet.{0}, y ∈ R ∧ app2 times x y one)

/-- Distributivity. -/
def distrib (R plus times : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∀ y : ZFSet.{0}, y ∈ R → ∀ z : ZFSet.{0}, z ∈ R →
    ∀ u : ZFSet.{0}, ∀ v : ZFSet.{0}, ∀ w : ZFSet.{0}, ∀ t : ZFSet.{0}, ∀ t' : ZFSet.{0},
      app2 plus y z u → (app2 times x u v → (app2 times x y w → (app2 times x z t →
        (app2 plus w t t' → v = t'))))

/-- Irreflexivity of `<` on `R`. -/
def irrefl (R ltR : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ¬ lt ltR x x

/-- Transitivity of `<` on `R`. -/
def trans (R ltR : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∀ y : ZFSet.{0}, y ∈ R → ∀ z : ZFSet.{0}, z ∈ R →
    (lt ltR x y → (lt ltR y z → lt ltR x z))

/-- Totality of `<` on `R`. -/
def total (R ltR : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∀ y : ZFSet.{0}, y ∈ R →
    (lt ltR x y ∨ (x = y ∨ lt ltR y x))

/-- `<` is compatible with `+`. -/
def addCompat (R plus ltR : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∀ y : ZFSet.{0}, y ∈ R → ∀ z : ZFSet.{0}, z ∈ R →
    ∀ u : ZFSet.{0}, ∀ v : ZFSet.{0},
      lt ltR x y → (app2 plus x z u → (app2 plus y z v → lt ltR u v))

/-- Products of positive elements are positive. -/
def mulPos (R times ltR zero : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ R → ∀ y : ZFSet.{0}, y ∈ R → ∀ u : ZFSet.{0},
    lt ltR zero x → (lt ltR zero y → (app2 times x y u → lt ltR zero u))

/-- Dedekind completeness. -/
def complete (R ltR : ZFSet.{0}) : Prop :=
  ∀ S : ZFSet.{0}, S ∈ ZFSet.powerset R →
    (¬ S = ∅ →
      ((∃ b : ZFSet.{0}, b ∈ R ∧ ∀ s : ZFSet.{0}, s ∈ S → le ltR s b) →
        ∃ u : ZFSet.{0}, u ∈ R ∧
          ((∀ s : ZFSet.{0}, s ∈ S → le ltR s u) ∧
            ∀ v : ZFSet.{0}, v ∈ R → ((∀ s : ZFSet.{0}, s ∈ S → le ltR s v) → le ltR u v))))

/-- `(R, plus, times, ltR, zero, one)` is a complete ordered field (`CompleteOrderedFieldF`). -/
def completeOrderedField (R plus times ltR zero one : ZFSet.{0}) : Prop :=
  isOp2 R plus ∧
  (isOp2 R times ∧
  (zero ∈ R ∧
  (one ∈ R ∧
  (assoc R plus ∧
  (comm R plus ∧
  (ident R plus zero ∧
  (addInv R plus zero ∧
  (assoc R times ∧
  (comm R times ∧
  (ident R times one ∧
  (mulInv R times zero one ∧
  (¬ zero = one ∧
  (distrib R plus times ∧
  (irrefl R ltR ∧
  (trans R ltR ∧
  (total R ltR ∧
  (addCompat R plus ltR ∧
  (mulPos R times ltR zero ∧
  complete R ltR))))))))))))))))))

/-! #### The Erdős property -/

/-- `S` is bounded (above and below) in `(R, <)` (`BoundedF`). -/
def bounded (R ltR S : ZFSet.{0}) : Prop :=
  ∃ m₁ : ZFSet.{0}, m₁ ∈ R ∧ ∃ m₂ : ZFSet.{0}, m₂ ∈ R ∧
    ∀ y : ZFSet.{0}, y ∈ S → (lt ltR m₁ y ∧ lt ltR y m₂)

/-- The intervals `(aₙ, bₙ)` are nondegenerate. -/
def nondegenerate (ltR a b : ZFSet.{0}) : Prop :=
  ∀ n : ZFSet.{0}, n ∈ ZFSet.omega → ∀ u : ZFSet.{0}, ∀ v : ZFSet.{0},
    app a n u → (app b n v → lt ltR u v)

/-- The intervals `(aₙ, bₙ)` cover `S`. -/
def covers (ltR S a b : ZFSet.{0}) : Prop :=
  ∀ y : ZFSet.{0}, y ∈ S → ∃ n : ZFSet.{0}, n ∈ ZFSet.omega ∧ ∃ u : ZFSet.{0}, ∃ v : ZFSet.{0},
    app a n u ∧ (app b n v ∧ (lt ltR u y ∧ lt ltR y v))

/-- The partial sums recursion: `s (n+1) + aₙ = s n + bₙ`. -/
def partialSums (plus a b s : ZFSet.{0}) : Prop :=
  ∀ n : ZFSet.{0}, n ∈ ZFSet.omega → ∀ m : ZFSet.{0}, succ n m →
    ∀ u : ZFSet.{0}, ∀ v : ZFSet.{0}, ∀ w : ZFSet.{0}, ∀ w' : ZFSet.{0}, ∀ t : ZFSet.{0}, ∀ t' : ZFSet.{0},
      app a n u → (app b n v → (app s n w → (app s m w' →
        (app2 plus w' u t → (app2 plus w v t' → t = t')))))

/-- The partial sums are bounded by some `r < 1`. -/
def sumsBounded (R ltR one s : ZFSet.{0}) : Prop :=
  ∃ r : ZFSet.{0}, r ∈ R ∧ (lt ltR r one ∧
    ∀ n : ZFSet.{0}, n ∈ ZFSet.omega → ∀ w : ZFSet.{0}, app s n w → le ltR w r)

/-- The Lebesgue outer measure of `S ⊆ R` is `< 1` (`OuterMeasureLtOneF`). -/
def outerMeasureLtOne (R plus ltR zero one S : ZFSet.{0}) : Prop :=
  ∃ a : ZFSet.{0}, ∃ b : ZFSet.{0}, ∃ s : ZFSet.{0},
    isFun ZFSet.omega R a ∧
    (isFun ZFSet.omega R b ∧
    (isFun ZFSet.omega R s ∧
    (nondegenerate ltR a b ∧
    (covers ltR S a b ∧
    (app s ∅ zero ∧
    (partialSums plus a b s ∧
    sumsBounded R ltR one s))))))

/-- `X` is infinite: `ω` injects into `X` (`InfiniteF`). -/
def infinite (X : ZFSet.{0}) : Prop :=
  ∃ f : ZFSet.{0}, isFun ZFSet.omega X f ∧
    ∀ n : ZFSet.{0}, n ∈ ZFSet.omega → ∀ m : ZFSet.{0}, m ∈ ZFSet.omega → ∀ u : ZFSet.{0},
      app f n u → (app f m u → n = m)

/-- `X` is independent for the family `A` (`IndependentF`). -/
def independent (A X : ZFSet.{0}) : Prop :=
  ∀ x : ZFSet.{0}, x ∈ X → ∀ y : ZFSet.{0}, y ∈ X →
    (¬ x = y → ∀ Ay : ZFSet.{0}, app A y Ay → ¬ x ∈ Ay)

/-- The Erdős property for `(R, plus, times, ltR, zero, one)` (`ErdosPropertyF`). -/
def erdosProperty (R plus ltR zero one : ZFSet.{0}) : Prop :=
  ∀ A : ZFSet.{0}, isFun R (ZFSet.powerset R) A →
    ((∀ x : ZFSet.{0}, x ∈ R → ∀ Ax : ZFSet.{0}, app A x Ax →
        (bounded R ltR Ax ∧ outerMeasureLtOne R plus ltR zero one Ax)) →
      ∃ X : ZFSet.{0}, X ∈ ZFSet.powerset R ∧ (infinite X ∧ independent A X))

/-- The meaning of `Erdos501_f` in the standard structure, as an explicit proposition on `ZFSet.{0}`. -/
def erdos501 : Prop :=
  ∀ R : ZFSet.{0}, ∀ plus : ZFSet.{0}, ∀ times : ZFSet.{0}, ∀ ltR : ZFSet.{0}, ∀ zero : ZFSet.{0}, ∀ one : ZFSet.{0},
    completeOrderedField R plus times ltR zero one → erdosProperty R plus ltR zero one

end StdSem

/-! ### The computation -/

/-- **The meaning of `Erdos501_f` in the standard structure.**  Unfolding the depth-polymorphic
combinators of `Sentence.lean` at depth `0` and evaluating all de Bruijn indices gives exactly
`StdSem.erdos501`. -/
theorem realize_Erdos501_f_std : (stdStructure ⊨ₘ Erdos501_f) ↔ StdSem.erdos501 := by
  simp only [Erdos501_f, toSentence, allF, exF, allIn, exIn, andF, orF, impF, iffF, notF, memF,
    eqF, varT, powT, pairT, omT, empT, ltF, leF, appF, app2F, isFunF, isOp2F, succF, andsF,
    CompleteOrderedFieldF, ErdosPropertyF, BoundedF, OuterMeasureLtOneF, InfiniteF, IndependentF,
    realize_sentence, realize_bounded_formula,
    realize_bounded_formula_and, realize_bounded_formula_or', realize_bounded_formula_not, realize_bounded_formula_ex,
    realize_bounded_formula_biimp, std_realize_bounded_formula_mem',
    std_realize_bounded_term_pair', std_realize_bounded_term_Powerset',
    std_realize_bounded_term_omega', std_realize_bounded_term_emptyset',
    realize_bounded_term, DVec.nth, std_forall, std_exists, std_eq,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [StdSem.erdos501, StdSem.completeOrderedField, StdSem.erdosProperty, StdSem.isOp2,
    StdSem.isFun, StdSem.assoc, StdSem.comm, StdSem.ident, StdSem.addInv, StdSem.mulInv,
    StdSem.distrib, StdSem.irrefl, StdSem.trans, StdSem.total, StdSem.addCompat, StdSem.mulPos,
    StdSem.complete, StdSem.bounded, StdSem.outerMeasureLtOne, StdSem.nondegenerate,
    StdSem.covers, StdSem.partialSums, StdSem.sumsBounded, StdSem.infinite, StdSem.independent,
    StdSem.succ, StdSem.lt, StdSem.le, StdSem.app, StdSem.app2]
  exact Iff.rfl

/-! ### A `ZFSet` toolkit -/

namespace StdSem

open ZFSet

/-- The `n`-th finite von Neumann ordinal, as a `ZFSet.{0}`. -/
def natZ (n : ℕ) : ZFSet.{0} := ZFSet.mk (PSet.ofNat n)

@[simp] theorem natZ_zero : natZ 0 = ∅ := rfl

theorem natZ_succ (n : ℕ) : natZ (n + 1) = insert (natZ n) (natZ n) := rfl

theorem natZ_mem_omega (n : ℕ) : natZ n ∈ ZFSet.omega := by
  induction n with
  | zero => exact ZFSet.omega_zero
  | succ n ih => rw [natZ_succ]; exact ZFSet.omega_succ ih

theorem mem_omega_iff {x : ZFSet.{0}} : x ∈ ZFSet.omega ↔ ∃ n : ℕ, x = natZ n := by
  refine Quotient.inductionOn x fun y => ?_
  change ZFSet.mk y ∈ ZFSet.mk PSet.omega ↔ _
  rw [ZFSet.mk_mem_iff, PSet.mem_def]
  constructor
  · rintro ⟨⟨n⟩, h⟩
    exact ⟨n, ZFSet.sound h⟩
  · rintro ⟨n, h⟩
    exact ⟨⟨n⟩, ZFSet.exact h⟩

theorem natZ_mem_natZ_of_lt {m n : ℕ} (h : m < n) : natZ m ∈ natZ n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    rw [natZ_succ, ZFSet.mem_insert_iff]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inr (ih h)
    · exact Or.inl (congrArg natZ h)

theorem natZ_injective : Function.Injective natZ := by
  intro m n h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := natZ_mem_natZ_of_lt hlt
    rw [h] at this
    exact ZFSet.mem_irrefl _ this
  · have := natZ_mem_natZ_of_lt hlt
    rw [h] at this
    exact ZFSet.mem_irrefl _ this

theorem succ_natZ (n : ℕ) : succ (natZ n) (natZ (n + 1)) := by
  intro z
  rw [natZ_succ, ZFSet.mem_insert_iff]
  exact or_comm

theorem natZ_eq_of_succ {n : ℕ} {m : ZFSet.{0}} (h : succ (natZ n) m) : m = natZ (n + 1) := by
  apply ZFSet.ext
  intro z
  rw [h z, natZ_succ, ZFSet.mem_insert_iff]
  exact or_comm

/-- The value of a function `f` (given as a set of pairs) at `x`: the (unique) `y` with
`(x, y) ∈ f`, or an arbitrary set if there is none. -/
noncomputable def fval (f x : ZFSet.{0}) : ZFSet.{0} :=
  Classical.epsilon fun y => app f x y

theorem fval_spec {dom cod f x : ZFSet.{0}} (hf : isFun dom cod f) (hx : x ∈ dom) :
    app f x (fval f x) ∧ fval f x ∈ cod := by
  obtain ⟨y, hy, hxy, -⟩ := hf x hx
  have h : app f x (fval f x) := Classical.epsilon_spec (p := fun y => app f x y) ⟨y, hxy⟩
  refine ⟨h, ?_⟩
  obtain ⟨y', hy', hxy', huniq⟩ := hf x hx
  rw [huniq _ h]
  exact hy'

theorem app_fval {dom cod f x : ZFSet.{0}} (hf : isFun dom cod f) (hx : x ∈ dom) :
    app f x (fval f x) := (fval_spec hf hx).1

theorem fval_mem {dom cod f x : ZFSet.{0}} (hf : isFun dom cod f) (hx : x ∈ dom) :
    fval f x ∈ cod := (fval_spec hf hx).2

theorem eq_fval_of_app {dom cod f x y : ZFSet.{0}} (hf : isFun dom cod f) (hx : x ∈ dom)
    (h : app f x y) : y = fval f x := by
  obtain ⟨y', -, -, huniq⟩ := hf x hx
  rw [huniq _ h, huniq _ (app_fval hf hx)]

theorem app_iff_eq_fval {dom cod f x y : ZFSet.{0}} (hf : isFun dom cod f) (hx : x ∈ dom) :
    app f x y ↔ y = fval f x :=
  ⟨eq_fval_of_app hf hx, fun h => h ▸ app_fval hf hx⟩

/-- The value of a binary operation `op` (given as a set of pairs `((x, y), z)`) at `(x, y)`. -/
noncomputable def opval (op x y : ZFSet.{0}) : ZFSet.{0} :=
  Classical.epsilon fun z => app2 op x y z

theorem opval_spec {R op x y : ZFSet.{0}} (hop : isOp2 R op) (hx : x ∈ R) (hy : y ∈ R) :
    app2 op x y (opval op x y) ∧ opval op x y ∈ R := by
  obtain ⟨z, hz, hxyz, huniq⟩ := hop x hx y hy
  have h : app2 op x y (opval op x y) :=
    Classical.epsilon_spec (p := fun z => app2 op x y z) ⟨z, hxyz⟩
  refine ⟨h, ?_⟩
  rw [huniq _ h]
  exact hz

theorem app2_opval {R op x y : ZFSet.{0}} (hop : isOp2 R op) (hx : x ∈ R) (hy : y ∈ R) :
    app2 op x y (opval op x y) := (opval_spec hop hx hy).1

theorem opval_mem {R op x y : ZFSet.{0}} (hop : isOp2 R op) (hx : x ∈ R) (hy : y ∈ R) :
    opval op x y ∈ R := (opval_spec hop hx hy).2

theorem eq_opval_of_app2 {R op x y z : ZFSet.{0}} (hop : isOp2 R op) (hx : x ∈ R) (hy : y ∈ R)
    (h : app2 op x y z) : z = opval op x y := by
  obtain ⟨z', -, -, huniq⟩ := hop x hx y hy
  rw [huniq _ h, huniq _ (app2_opval hop hx hy)]

theorem app2_iff_eq_opval {R op x y z : ZFSet.{0}} (hop : isOp2 R op) (hx : x ∈ R) (hy : y ∈ R) :
    app2 op x y z ↔ z = opval op x y :=
  ⟨eq_opval_of_app2 hop hx hy, fun h => h ▸ app2_opval hop hx hy⟩

end StdSem

end Flypitch.Erdos501
