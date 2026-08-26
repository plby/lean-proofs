/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Boolean value of the sentence `Erdos501_f` in a Boolean-valued model `V 𝔹`, unfolded.
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Sentence

set_option relaxedAutoImplicit true

/-!
# The Boolean value of `Erdos501_f` in `V 𝔹`

`Erdos501_f` (`Sentence.lean`) is a sentence of the first-order language `L_ZFC`.  Its Boolean
value `⟦Erdos501_f⟧[V 𝔹]` in the Boolean-valued model `V 𝔹` of the Flypitch development is defined
by recursion on the syntax (`boolean_realize_bounded_formula`), so it is a large expression in
`⨅`, `⨆`, `⊓`, `⊔`, `ᶜ`, `⟹`, `∈ᴮ`, `=ᴮ`, `pair`, `bv_powerset`, `bSet.omega`, `bSet.empty`
over names `x : bSet 𝔹`.

This file computes that expression once and for all (`realize_Erdos501_f`), in terms of a family
of *Boolean-valued predicates* on names (`Sem.completeOrderedField`, `Sem.bounded`,
`Sem.outerMeasureLtOne`, `Sem.infinite`, `Sem.independent`, `Sem.erdosProperty`, …) which mirror the
blocks `CompleteOrderedFieldF`, `BoundedF`, … of `Sentence.lean` and are stated directly at the
level of `bSet 𝔹`.  Consequently

* `Γ ⊩[V 𝔹] Erdos501_f` is equivalent (`forced_Erdos501_f_iff`) to: for all names
  `R plus times lt zero one : bSet 𝔹`,
  `Γ ⊓ Sem.completeOrderedField R plus times lt zero one ≤ Sem.erdosProperty R plus lt zero one`;

so that the remaining units of the plan (`PLAN.md`: (F6), (F7)) can be carried out entirely at the
level of names and Boolean values, without any further reference to the syntax of `L_ZFC`.

The proof of `realize_Erdos501_f` is a (large but mechanical) computation: unfold the
depth-polymorphic combinators of `Sentence.lean` at depth `0`, evaluate the de Bruijn indices, and
compare with the definitions of the `Sem.*` predicates.  All Boolean values are stated for an
arbitrary nontrivial complete Boolean algebra `β : Type`.
-/

open Fol bSet
open scoped Flypitch

namespace Flypitch.Erdos501

variable {β : Type} [NontrivialCompleteBooleanAlgebra β]

/-! ### Boolean-valued predicates on names -/

namespace Sem

/-- `x < y`, for an order relation `ltR` given as a set of ordered pairs (`ltF`). -/
def lt (ltR x y : bSet β) : β := pair x y ∈ᴮ ltR

/-- `x ≤ y`, i.e. `x < y ∨ x = y` (`leF`). -/
def le (ltR x y : bSet β) : β := lt ltR x y ⊔ x =ᴮ y

/-- `f(x) = y`, for a function `f` given as a set of ordered pairs (`appF`). -/
def app (f x y : bSet β) : β := pair x y ∈ᴮ f

/-- `op(x, y) = z`, for a binary operation `op` given as a set of pairs `((x, y), z)` (`app2F`). -/
def app2 (op x y z : bSet β) : β := pair (pair x y) z ∈ᴮ op

/-- `f` is a (total, single-valued) function from `dom` to `cod` (`isFunF`). -/
def isFun (dom cod f : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ dom ⟹ ⨆ y : bSet β, y ∈ᴮ cod ⊓
    (app f x y ⊓ ⨅ y' : bSet β, app f x y' ⟹ y' =ᴮ y)

/-- `op` is a binary operation on `R` (`isOp2F`). -/
def isOp2 (R op : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ y : bSet β, y ∈ᴮ R ⟹ ⨆ z : bSet β, z ∈ᴮ R ⊓
    (app2 op x y z ⊓ ⨅ z' : bSet β, app2 op x y z' ⟹ z' =ᴮ z)

/-- `m = n ∪ {n}` (`succF`). -/
def succ (n m : bSet β) : β :=
  ⨅ z : bSet β, bihimp (z ∈ᴮ m) (z ∈ᴮ n ⊔ z =ᴮ n)

/-! #### The axioms of a complete ordered field, one by one -/

/-- Associativity of `op` on `R`: `x ∘ y = u → u ∘ z = v → y ∘ z = w → x ∘ w = w' → v = w'`. -/
def assoc (R op : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ y : bSet β, y ∈ᴮ R ⟹ ⨅ z : bSet β, z ∈ᴮ R ⟹
    ⨅ u : bSet β, ⨅ v : bSet β, ⨅ w : bSet β, ⨅ w' : bSet β,
      app2 op x y u ⟹ (app2 op u z v ⟹ (app2 op y z w ⟹ (app2 op x w w' ⟹ v =ᴮ w')))

/-- Commutativity of `op` on `R`. -/
def comm (R op : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ y : bSet β, y ∈ᴮ R ⟹ ⨅ u : bSet β,
    app2 op x y u ⟹ app2 op y x u

/-- `e` is a right identity for `op` on `R`: `x ∘ e = x`. -/
def ident (R op e : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ app2 op x e x

/-- Additive inverses: `∀ x ∈ R, ∃ y ∈ R, x + y = zero`. -/
def addInv (R plus zero : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨆ y : bSet β, y ∈ᴮ R ⊓ app2 plus x y zero

/-- Multiplicative inverses of nonzero elements. -/
def mulInv (R times zero one : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ((x =ᴮ zero)ᶜ ⟹ ⨆ y : bSet β, y ∈ᴮ R ⊓ app2 times x y one)

/-- Distributivity: `y + z = u → x · u = v → x · y = w → x · z = t → w + t = t' → v = t'`. -/
def distrib (R plus times : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ y : bSet β, y ∈ᴮ R ⟹ ⨅ z : bSet β, z ∈ᴮ R ⟹
    ⨅ u : bSet β, ⨅ v : bSet β, ⨅ w : bSet β, ⨅ t : bSet β, ⨅ t' : bSet β,
      app2 plus y z u ⟹ (app2 times x u v ⟹ (app2 times x y w ⟹ (app2 times x z t ⟹
        (app2 plus w t t' ⟹ v =ᴮ t'))))

/-- Irreflexivity of `<` on `R`. -/
def irrefl (R ltR : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ (lt ltR x x)ᶜ

/-- Transitivity of `<` on `R`. -/
def trans (R ltR : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ y : bSet β, y ∈ᴮ R ⟹ ⨅ z : bSet β, z ∈ᴮ R ⟹
    (lt ltR x y ⟹ (lt ltR y z ⟹ lt ltR x z))

/-- Totality of `<` on `R`. -/
def total (R ltR : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ y : bSet β, y ∈ᴮ R ⟹
    (lt ltR x y ⊔ (x =ᴮ y ⊔ lt ltR y x))

/-- `<` is compatible with `+`: `x < y → x + z = u → y + z = v → u < v`. -/
def addCompat (R plus ltR : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ y : bSet β, y ∈ᴮ R ⟹ ⨅ z : bSet β, z ∈ᴮ R ⟹
    ⨅ u : bSet β, ⨅ v : bSet β,
      lt ltR x y ⟹ (app2 plus x z u ⟹ (app2 plus y z v ⟹ lt ltR u v))

/-- Products of positive elements are positive: `0 < x → 0 < y → x · y = u → 0 < u`. -/
def mulPos (R times ltR zero : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ y : bSet β, y ∈ᴮ R ⟹ ⨅ u : bSet β,
    lt ltR zero x ⟹ (lt ltR zero y ⟹ (app2 times x y u ⟹ lt ltR zero u))

/-- Dedekind completeness: every nonempty bounded-above `S ⊆ R` has a least upper bound. -/
def complete (R ltR : bSet β) : β :=
  ⨅ S : bSet β, S ∈ᴮ bv_powerset R ⟹
    ((S =ᴮ bSet.empty)ᶜ ⟹
      ((⨆ b : bSet β, b ∈ᴮ R ⊓ ⨅ s : bSet β, s ∈ᴮ S ⟹ le ltR s b) ⟹
        ⨆ u : bSet β, u ∈ᴮ R ⊓
          ((⨅ s : bSet β, s ∈ᴮ S ⟹ le ltR s u) ⊓
            ⨅ v : bSet β, v ∈ᴮ R ⟹ ((⨅ s : bSet β, s ∈ᴮ S ⟹ le ltR s v) ⟹ le ltR u v))))

/-- `(R, plus, times, ltR, zero, one)` is a complete ordered field (`CompleteOrderedFieldF`):
the conjunction, in the order of `Sentence.lean`, of the twenty axioms above. -/
def completeOrderedField (R plus times ltR zero one : bSet β) : β :=
  isOp2 R plus ⊓
  (isOp2 R times ⊓
  (zero ∈ᴮ R ⊓
  (one ∈ᴮ R ⊓
  (assoc R plus ⊓
  (comm R plus ⊓
  (ident R plus zero ⊓
  (addInv R plus zero ⊓
  (assoc R times ⊓
  (comm R times ⊓
  (ident R times one ⊓
  (mulInv R times zero one ⊓
  ((zero =ᴮ one)ᶜ ⊓
  (distrib R plus times ⊓
  (irrefl R ltR ⊓
  (trans R ltR ⊓
  (total R ltR ⊓
  (addCompat R plus ltR ⊓
  (mulPos R times ltR zero ⊓
  complete R ltR))))))))))))))))))

/-! #### The Erdős property -/

/-- `S` is bounded (above and below) in `(R, <)` (`BoundedF`). -/
def bounded (R ltR S : bSet β) : β :=
  ⨆ m₁ : bSet β, m₁ ∈ᴮ R ⊓ ⨆ m₂ : bSet β, m₂ ∈ᴮ R ⊓
    ⨅ y : bSet β, y ∈ᴮ S ⟹ (lt ltR m₁ y ⊓ lt ltR y m₂)

/-- The intervals `(aₙ, bₙ)` are nondegenerate: `∀ n ∈ ω, aₙ < bₙ`. -/
def nondegenerate (ltR a b : bSet β) : β :=
  ⨅ n : bSet β, n ∈ᴮ bSet.omega ⟹ ⨅ u : bSet β, ⨅ v : bSet β,
    app a n u ⟹ (app b n v ⟹ lt ltR u v)

/-- The intervals `(aₙ, bₙ)` cover `S`: `∀ y ∈ S, ∃ n ∈ ω, aₙ < y < bₙ`. -/
def covers (ltR S a b : bSet β) : β :=
  ⨅ y : bSet β, y ∈ᴮ S ⟹ ⨆ n : bSet β, n ∈ᴮ bSet.omega ⊓ ⨆ u : bSet β, ⨆ v : bSet β,
    app a n u ⊓ (app b n v ⊓ (lt ltR u y ⊓ lt ltR y v))

/-- The partial sums recursion: `s (n+1) + aₙ = s n + bₙ`. -/
def partialSums (plus a b s : bSet β) : β :=
  ⨅ n : bSet β, n ∈ᴮ bSet.omega ⟹ ⨅ m : bSet β, succ n m ⟹
    ⨅ u : bSet β, ⨅ v : bSet β, ⨅ w : bSet β, ⨅ w' : bSet β, ⨅ t : bSet β, ⨅ t' : bSet β,
      app a n u ⟹ (app b n v ⟹ (app s n w ⟹ (app s m w' ⟹
        (app2 plus w' u t ⟹ (app2 plus w v t' ⟹ t =ᴮ t')))))

/-- The partial sums are bounded by some `r < 1`. -/
def sumsBounded (R ltR one s : bSet β) : β :=
  ⨆ r : bSet β, r ∈ᴮ R ⊓ (lt ltR r one ⊓
    ⨅ n : bSet β, n ∈ᴮ bSet.omega ⟹ ⨅ w : bSet β, app s n w ⟹ le ltR w r)

/-- The Lebesgue outer measure of `S ⊆ R` is `< 1` (`OuterMeasureLtOneF`). -/
def outerMeasureLtOne (R plus ltR zero one S : bSet β) : β :=
  ⨆ a : bSet β, ⨆ b : bSet β, ⨆ s : bSet β,
    isFun bSet.omega R a ⊓
    (isFun bSet.omega R b ⊓
    (isFun bSet.omega R s ⊓
    (nondegenerate ltR a b ⊓
    (covers ltR S a b ⊓
    (app s bSet.empty zero ⊓
    (partialSums plus a b s ⊓
    sumsBounded R ltR one s))))))

/-- `X` is infinite: `ω` injects into `X` (`InfiniteF`). -/
def infinite (X : bSet β) : β :=
  ⨆ f : bSet β, isFun bSet.omega X f ⊓
    ⨅ n : bSet β, n ∈ᴮ bSet.omega ⟹ ⨅ m : bSet β, m ∈ᴮ bSet.omega ⟹ ⨅ u : bSet β,
      app f n u ⟹ (app f m u ⟹ n =ᴮ m)

/-- `X` is independent for the family `A`: `∀ x y ∈ X, x ≠ y → x ∉ A(y)` (`IndependentF`). -/
def independent (A X : bSet β) : β :=
  ⨅ x : bSet β, x ∈ᴮ X ⟹ ⨅ y : bSet β, y ∈ᴮ X ⟹
    ((x =ᴮ y)ᶜ ⟹ ⨅ Ay : bSet β, app A y Ay ⟹ (x ∈ᴮ Ay)ᶜ)

/-- The Erdős property for `(R, plus, times, ltR, zero, one)` (`ErdosPropertyF`): for every
function `A : R → 𝒫(R)` all of whose values are bounded and of outer measure `< 1`, there is an
infinite independent `X ⊆ R`. -/
def erdosProperty (R plus ltR zero one : bSet β) : β :=
  ⨅ A : bSet β, isFun R (bv_powerset R) A ⟹
    ((⨅ x : bSet β, x ∈ᴮ R ⟹ ⨅ Ax : bSet β, app A x Ax ⟹
        (bounded R ltR Ax ⊓ outerMeasureLtOne R plus ltR zero one Ax)) ⟹
      ⨆ X : bSet β, X ∈ᴮ bv_powerset R ⊓ (infinite X ⊓ independent A X))

/-- The Boolean value of `Erdos501_f`, as an explicit expression over names. -/
def erdos501 : β :=
  ⨅ R : bSet β, ⨅ plus : bSet β, ⨅ times : bSet β, ⨅ ltR : bSet β, ⨅ zero : bSet β,
    ⨅ one : bSet β,
      completeOrderedField R plus times ltR zero one ⟹ erdosProperty R plus ltR zero one

/-- The Boolean value of `Erdos501_ex_f` (there is a complete ordered field with the Erdős
property), as an explicit expression over names. -/
def erdos501_ex : β :=
  ⨆ R : bSet β, ⨆ plus : bSet β, ⨆ times : bSet β, ⨆ ltR : bSet β, ⨆ zero : bSet β,
    ⨆ one : bSet β,
      completeOrderedField R plus times ltR zero one ⊓ erdosProperty R plus ltR zero one

end Sem

/-! ### The computation -/

/-- **The Boolean value of `Erdos501_f` in `V β`.**  Unfolding the depth-polymorphic combinators of
`Sentence.lean` at depth `0` and evaluating all de Bruijn indices gives exactly `Sem.erdos501`. -/
theorem realize_Erdos501_f : ⟦Erdos501_f⟧[V β] = (Sem.erdos501 : β) := by
  simp only [Erdos501_f, toSentence, allF, exF, allIn, exIn, andF, orF, impF, iffF, notF, memF,
    eqF, varT, powT, pairT, omT, empT, ltF, leF, appF, app2F, isFunF, isOp2F, succF, andsF,
    CompleteOrderedFieldF, ErdosPropertyF, BoundedF, OuterMeasureLtOneF, InfiniteF, IndependentF,
    boolean_realize_sentence, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_or,
    boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair', boolean_realize_bounded_term_Powerset',
    boolean_realize_bounded_term_omega', boolean_realize_bounded_term_emptyset',
    boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [Sem.erdos501, Sem.completeOrderedField, Sem.erdosProperty, Sem.isOp2, Sem.isFun,
    Sem.assoc, Sem.comm, Sem.ident, Sem.addInv, Sem.mulInv, Sem.distrib, Sem.irrefl, Sem.trans,
    Sem.total, Sem.addCompat, Sem.mulPos, Sem.complete, Sem.bounded, Sem.outerMeasureLtOne,
    Sem.nondegenerate, Sem.covers, Sem.partialSums, Sem.sumsBounded, Sem.infinite,
    Sem.independent, Sem.succ, Sem.lt, Sem.le, Sem.app, Sem.app2]
  rfl

/-- **`Erdos501_f` is forced by `Γ` iff the Erdős property is forced for every complete ordered
field of names.**  This is the form in which the remaining units of the plan will establish
`⊤ ⊩[V 𝔹] Erdos501_f`. -/
theorem forced_Erdos501_f_iff {Γ : β} :
    (Γ ⊩[V β] Erdos501_f) ↔
      ∀ R plus times ltR zero one : bSet β,
        Γ ⊓ Sem.completeOrderedField R plus times ltR zero one ≤
          Sem.erdosProperty R plus ltR zero one := by
  change Γ ≤ ⟦Erdos501_f⟧[V β] ↔ _
  rw [realize_Erdos501_f]
  simp only [Sem.erdos501, le_iInf_iff, _root_.deduction_simp]

/-- **The Boolean value of `Erdos501_ex_f` in `V β`.** -/
theorem realize_Erdos501_ex_f : ⟦Erdos501_ex_f⟧[V β] = (Sem.erdos501_ex : β) := by
  simp only [Erdos501_ex_f, toSentence, allF, exF, allIn, exIn, andF, orF, impF, iffF, notF, memF,
    eqF, varT, powT, pairT, omT, empT, ltF, leF, appF, app2F, isFunF, isOp2F, succF, andsF,
    CompleteOrderedFieldF, ErdosPropertyF, BoundedF, OuterMeasureLtOneF, InfiniteF, IndependentF,
    boolean_realize_sentence, boolean_realize_bounded_formula,
    boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_or,
    boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_ex,
    boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
    boolean_realize_bounded_term_pair', boolean_realize_bounded_term_Powerset',
    boolean_realize_bounded_term_omega', boolean_realize_bounded_term_emptyset',
    boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceDIte]
  simp only [Sem.erdos501_ex, Sem.completeOrderedField, Sem.erdosProperty, Sem.isOp2, Sem.isFun,
    Sem.assoc, Sem.comm, Sem.ident, Sem.addInv, Sem.mulInv, Sem.distrib, Sem.irrefl, Sem.trans,
    Sem.total, Sem.addCompat, Sem.mulPos, Sem.complete, Sem.bounded, Sem.outerMeasureLtOne,
    Sem.nondegenerate, Sem.covers, Sem.partialSums, Sem.sumsBounded, Sem.infinite,
    Sem.independent, Sem.succ, Sem.lt, Sem.le, Sem.app, Sem.app2]
  rfl

/-- `Erdos501_ex_f` is forced by `Γ` iff `Γ ≤ Sem.erdos501_ex`. -/
theorem forced_Erdos501_ex_f_iff {Γ : β} : (Γ ⊩[V β] Erdos501_ex_f) ↔ Γ ≤ Sem.erdos501_ex := by
  change Γ ≤ ⟦Erdos501_ex_f⟧[V β] ↔ _
  rw [realize_Erdos501_ex_f]

/-- **Introduction rule for `Erdos501_ex_f`**: six names forming a complete ordered field with the
Erdős property (on `Γ`) force `Erdos501_ex_f`. -/
theorem forced_Erdos501_ex_f_of {Γ : β} (R plus times ltR zero one : bSet β)
    (h : Γ ≤ Sem.completeOrderedField R plus times ltR zero one ⊓
      Sem.erdosProperty R plus ltR zero one) :
    Γ ⊩[V β] Erdos501_ex_f := by
  rw [forced_Erdos501_ex_f_iff, Sem.erdos501_ex]
  exact le_iSup_of_le R (le_iSup_of_le plus (le_iSup_of_le times (le_iSup_of_le ltR
    (le_iSup_of_le zero (le_iSup_of_le one h)))))

end Flypitch.Erdos501
