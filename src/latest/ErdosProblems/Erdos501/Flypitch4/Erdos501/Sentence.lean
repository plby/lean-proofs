/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Erdős problem #501, first question, as a first-order sentence of `L_ZFC`.
-/
import ErdosProblems.Erdos501.Flypitch4.Zfc

set_option relaxedAutoImplicit true

/-!
# Erdős problem #501 (first question) as a sentence of `L_ZFC`

The first question of Erdős problem #501 (erdosproblems.com/501; Erdős 1961, Problem II.9;
Erdős–Hajnal 1971, Problem 38(C)) is formalized in the DeepMind `formal-conjectures`
repository (`FormalConjectures/ErdosProblems/501.lean`) as the proposition

```
∀ (A : ℝ → Set ℝ),
  (∀ x, Bornology.IsBounded (A x)) →
  (∀ x, volume.toOuterMeasure (A x) < 1) →
  ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y)
```

("for every family `⟨A_x : x ∈ ℝ⟩` of bounded sets of reals of Lebesgue outer measure `< 1` there
is an infinite independent set `X ⊆ ℝ`, i.e. `x ∉ A_y` for all distinct `x, y ∈ X`").

To speak about this proposition inside a Boolean-valued model of set theory (`V 𝔹` of the
Flypitch development), we render it as a first-order sentence `Erdos501_f` of the language
`L_ZFC` (`∈`, `∅`, `pair`, `ω`, `𝒫`, `⋃`), in the same way as `CH_f` renders the continuum
hypothesis.  We follow the following conventions.

* **The real numbers.**  Rather than constructing `ℝ` inside first-order set theory (Dedekind
  cuts of rationals of pairs of naturals …), the sentence quantifies over *all* complete ordered
  fields `(R, +, ·, <, 0, 1)` given as sets (`+` and `·` as sets of triples `((x, y), z)`, `<` as
  a set of pairs) and asserts the Erdős property for each of them.  Since `ZFC` proves that any
  two complete ordered fields are isomorphic, and the Erdős property is invariant under
  isomorphisms of ordered fields, this is `ZFC`-equivalent to the property for "the" reals.
* **Boundedness.**  `Bornology.IsBounded (A x)` in `ℝ` means bounded above and below:
  `∃ m₁ m₂ ∈ R, ∀ y ∈ A_x, m₁ < y < m₂` (`BoundedF`).
* **Outer measure `< 1`.**  `volume.toOuterMeasure (A x)` is the Lebesgue outer measure of an
  arbitrary set of reals, i.e. the infimum of `∑ₙ (bₙ - aₙ)` over all covers of the set by
  countably many open intervals `(aₙ, bₙ)`.  It is `< 1` iff there is such a cover, indexed by
  `ω`, whose total length is `< 1`.  We express the total length through the sequence of partial
  sums `s` (`s 0 = 0`, `s (n+1) = s n + (bₙ - aₙ)`, written additively as
  `s (n+1) + aₙ = s n + bₙ`) and require all `s n` to be `≤ r` for some `r < 1`
  (`OuterMeasureLtOneF`).
* **Infinite.**  `X.Infinite` is rendered as "`ω` injects into `X`" (`InfiniteF`), which is
  `ZFC`-equivalent (the theory `ZFC` of Flypitch contains the axiom of choice in the form of
  Zorn's lemma).
* **Independent.**  `X.Pairwise (fun x y => x ∉ A y)` is `∀ x y ∈ X, x ≠ y → x ∉ A(y)`
  (`IndependentF`).

## Implementation: de Bruijn levels

Formulas of `Flypitch4.Fol` use de Bruijn indices (`bd_var ⟨k, _⟩`, `0` = innermost binder).
To make the (long) sentence auditable we build it through *depth-polymorphic* formulas
`Fm := ∀ n, bounded_formula L_ZFC n` and terms `Tm := ∀ n, bounded_term L_ZFC n`, in which
variables are referred to by their de Bruijn *level* (`0` = outermost binder).  A quantifier
`allF fun x => …` passes the level of the new variable to its body as the Lean variable `x`, so
that scoping is checked by Lean itself, and no lifting is ever needed.  The sentence is
obtained by evaluating at depth `0` (`toSentence`).
-/

open Fol

namespace Flypitch.Erdos501

/-! ### Depth-polymorphic formulas and terms -/

/-- Depth-polymorphic bounded formulas of `L_ZFC`. -/
abbrev Fm : Type 1 := ∀ n : ℕ, bounded_formula L_ZFC n

/-- Depth-polymorphic bounded terms of `L_ZFC`. -/
abbrev Tm : Type 1 := ∀ n : ℕ, bounded_term L_ZFC n

/-- The variable with de Bruijn *level* `ℓ` (`0` = outermost); at depth `n > ℓ` it has de Bruijn
index `n - 1 - ℓ`.  (For `ℓ ≥ n` — never used — we return `∅'`.) -/
def varT (ℓ : ℕ) : Tm := fun n =>
  if h : ℓ < n then bd_var ⟨n - 1 - ℓ, by omega⟩ else ∅'

/-- The constant `∅`. -/
def empT : Tm := fun _ => ∅'

/-- The constant `ω`. -/
def omT : Tm := fun _ => ω'

/-- The power set `𝒫 t`. -/
def powT (t : Tm) : Tm := fun n => P' (t n)

/-- The ordered pair `(s, t)`. -/
def pairT (s t : Tm) : Tm := fun n => pair' (s n) (t n)

/-- `s ∈ t`. -/
def memF (s t : Tm) : Fm := fun n => mem' (s n) (t n)

/-- `s = t`. -/
def eqF (s t : Tm) : Fm := fun n => bd_equal (s n) (t n)

def andF (φ ψ : Fm) : Fm := fun n => bd_and (φ n) (ψ n)
def orF (φ ψ : Fm) : Fm := fun n => bd_or (φ n) (ψ n)
def impF (φ ψ : Fm) : Fm := fun n => bd_imp (φ n) (ψ n)
def iffF (φ ψ : Fm) : Fm := fun n => bd_biimp (φ n) (ψ n)
def notF (φ : Fm) : Fm := fun n => bd_not (φ n)

/-- `∀ x, φ x`; the body receives the *level* of the bound variable. -/
def allF (φ : ℕ → Fm) : Fm := fun n => bd_all (φ n (n + 1))

/-- `∃ x, φ x`; the body receives the *level* of the bound variable. -/
def exF (φ : ℕ → Fm) : Fm := fun n => bd_ex (φ n (n + 1))

/-- `∀ x ∈ t, φ x`. -/
def allIn (t : Tm) (φ : ℕ → Fm) : Fm := allF fun x => impF (memF (varT x) t) (φ x)

/-- `∃ x ∈ t, φ x`. -/
def exIn (t : Tm) (φ : ℕ → Fm) : Fm := exF fun x => andF (memF (varT x) t) (φ x)

/-- Conjunction of a list of formulas (`⊤` for the empty list). -/
def andsF : List Fm → Fm
  | [] => notF (fun _ => bd_falsum)
  | [φ] => φ
  | φ :: φs => andF φ (andsF φs)

/-- The sentence denoted by a depth-polymorphic formula (evaluation at depth `0`). -/
def toSentence (φ : Fm) : sentence L_ZFC := φ 0

scoped infixr:35 " ⋀ " => andF
scoped infixr:30 " ⋁ " => orF
scoped infixr:25 " ⟶ " => impF

/-! ### Relations, functions, operations given as sets -/

/-- `x < y`, for an order relation `lt` given as a set of ordered pairs. -/
def ltF (lt x y : Tm) : Fm := memF (pairT x y) lt

/-- `x ≤ y`, i.e. `x < y ∨ x = y`. -/
def leF (lt x y : Tm) : Fm := ltF lt x y ⋁ eqF x y

/-- `f(x) = y`, for a function `f` given as a set of ordered pairs. -/
def appF (f x y : Tm) : Fm := memF (pairT x y) f

/-- `op(x, y) = z`, for a binary operation `op` given as a set of pairs `((x, y), z)`. -/
def app2F (op x y z : Tm) : Fm := memF (pairT (pairT x y) z) op

/-- `f` is a (total, single-valued) function from `dom` to `cod`: every `x ∈ dom` has exactly one
`f`-value, and it lies in `cod`. -/
def isFunF (dom cod f : Tm) : Fm :=
  allIn dom fun x => exIn cod fun y =>
    appF f (varT x) (varT y) ⋀
    (allF fun y' => appF f (varT x) (varT y') ⟶ eqF (varT y') (varT y))

/-- `op` is a binary operation on `R`: every pair `(x, y) ∈ R × R` has exactly one `op`-value,
and it lies in `R`. -/
def isOp2F (R op : Tm) : Fm :=
  allIn R fun x => allIn R fun y => exIn R fun z =>
    app2F op (varT x) (varT y) (varT z) ⋀
    (allF fun z' => app2F op (varT x) (varT y) (varT z') ⟶ eqF (varT z') (varT z))

/-- `m = n ∪ {n}` (the successor of a natural number `n ∈ ω`). -/
def succF (n m : Tm) : Fm :=
  allF fun z => iffF (memF (varT z) m) (memF (varT z) n ⋁ eqF (varT z) n)

/-! ### Complete ordered fields -/

/-- `(R, plus, times, lt, zero, one)` is a complete ordered field:
`plus`, `times` are binary operations on `R`, `zero, one ∈ R`, the field axioms, the axioms of
a total order compatible with `+` and `·`, and Dedekind completeness (every nonempty subset of
`R` with an upper bound has a least upper bound). -/
def CompleteOrderedFieldF (R plus times lt zero one : Tm) : Fm :=
  andsF [
    isOp2F R plus,
    isOp2F R times,
    memF zero R,
    memF one R,
    -- `+` is associative: x + y = u → u + z = v → y + z = w → x + w = w' → v = w'
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun w' =>
        app2F plus (varT x) (varT y) (varT u) ⟶ app2F plus (varT u) (varT z) (varT v) ⟶
        app2F plus (varT y) (varT z) (varT w) ⟶ app2F plus (varT x) (varT w) (varT w') ⟶
        eqF (varT v) (varT w'),
    -- `+` is commutative
    allIn R fun x => allIn R fun y => allF fun u =>
      app2F plus (varT x) (varT y) (varT u) ⟶ app2F plus (varT y) (varT x) (varT u),
    -- x + 0 = x
    allIn R fun x => app2F plus (varT x) zero (varT x),
    -- additive inverses
    allIn R fun x => exIn R fun y => app2F plus (varT x) (varT y) zero,
    -- `·` is associative
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun w' =>
        app2F times (varT x) (varT y) (varT u) ⟶ app2F times (varT u) (varT z) (varT v) ⟶
        app2F times (varT y) (varT z) (varT w) ⟶ app2F times (varT x) (varT w) (varT w') ⟶
        eqF (varT v) (varT w'),
    -- `·` is commutative
    allIn R fun x => allIn R fun y => allF fun u =>
      app2F times (varT x) (varT y) (varT u) ⟶ app2F times (varT y) (varT x) (varT u),
    -- x · 1 = x
    allIn R fun x => app2F times (varT x) one (varT x),
    -- multiplicative inverses of nonzero elements
    allIn R fun x => notF (eqF (varT x) zero) ⟶ exIn R fun y => app2F times (varT x) (varT y) one,
    -- 0 ≠ 1
    notF (eqF zero one),
    -- distributivity: y + z = u → x · u = v → x · y = w → x · z = t → w + t = t' → v = t'
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun t => allF fun t' =>
        app2F plus (varT y) (varT z) (varT u) ⟶ app2F times (varT x) (varT u) (varT v) ⟶
        app2F times (varT x) (varT y) (varT w) ⟶ app2F times (varT x) (varT z) (varT t) ⟶
        app2F plus (varT w) (varT t) (varT t') ⟶ eqF (varT v) (varT t'),
    -- `<` is irreflexive
    allIn R fun x => notF (ltF lt (varT x) (varT x)),
    -- `<` is transitive
    allIn R fun x => allIn R fun y => allIn R fun z =>
      ltF lt (varT x) (varT y) ⟶ ltF lt (varT y) (varT z) ⟶ ltF lt (varT x) (varT z),
    -- `<` is total
    allIn R fun x => allIn R fun y =>
      ltF lt (varT x) (varT y) ⋁ eqF (varT x) (varT y) ⋁ ltF lt (varT y) (varT x),
    -- `<` is compatible with `+`: x < y → x + z = u → y + z = v → u < v
    allIn R fun x => allIn R fun y => allIn R fun z => allF fun u => allF fun v =>
      ltF lt (varT x) (varT y) ⟶ app2F plus (varT x) (varT z) (varT u) ⟶
      app2F plus (varT y) (varT z) (varT v) ⟶ ltF lt (varT u) (varT v),
    -- products of positive elements are positive: 0 < x → 0 < y → x · y = u → 0 < u
    allIn R fun x => allIn R fun y => allF fun u =>
      ltF lt zero (varT x) ⟶ ltF lt zero (varT y) ⟶ app2F times (varT x) (varT y) (varT u) ⟶
      ltF lt zero (varT u),
    -- Dedekind completeness: every nonempty bounded-above `S ⊆ R` has a least upper bound
    allIn (powT R) fun S =>
      notF (eqF (varT S) empT) ⟶
      (exIn R fun b => allIn (varT S) fun s => leF lt (varT s) (varT b)) ⟶
      exIn R fun u =>
        (allIn (varT S) fun s => leF lt (varT s) (varT u)) ⋀
        (allIn R fun v => (allIn (varT S) fun s => leF lt (varT s) (varT v)) ⟶
          leF lt (varT u) (varT v))
  ]

/-! ### The Erdős property for a complete ordered field -/

/-- `S` is bounded (above and below) in `(R, <)`: `∃ m₁ m₂ ∈ R, ∀ y ∈ S, m₁ < y < m₂`.
This renders `Bornology.IsBounded (A x)`. -/
def BoundedF (R lt S : Tm) : Fm :=
  exIn R fun m₁ => exIn R fun m₂ => allIn S fun y =>
    ltF lt (varT m₁) (varT y) ⋀ ltF lt (varT y) (varT m₂)

/-- The Lebesgue outer measure of `S ⊆ R` is `< 1`: there are sequences `a, b : ω → R` with
`aₙ < bₙ`, such that the open intervals `(aₙ, bₙ)` cover `S`, and whose total length
`∑ₙ (bₙ - aₙ)` is `< 1`; the total length is expressed through the partial sums `s : ω → R`,
`s 0 = 0`, `s (n+1) + aₙ = s n + bₙ`, all of which are `≤ r` for some `r < 1`.
This renders `volume.toOuterMeasure (A x) < 1`. -/
def OuterMeasureLtOneF (R plus lt zero one S : Tm) : Fm :=
  exF fun a => exF fun b => exF fun s => andsF [
    isFunF omT R (varT a),
    isFunF omT R (varT b),
    isFunF omT R (varT s),
    -- the intervals are nondegenerate: ∀ n ∈ ω, aₙ < bₙ
    allIn omT fun n => allF fun u => allF fun v =>
      appF (varT a) (varT n) (varT u) ⟶ appF (varT b) (varT n) (varT v) ⟶ ltF lt (varT u) (varT v),
    -- they cover `S`: ∀ y ∈ S, ∃ n ∈ ω, aₙ < y < bₙ
    allIn S fun y => exIn omT fun n => exF fun u => exF fun v =>
      appF (varT a) (varT n) (varT u) ⋀ appF (varT b) (varT n) (varT v) ⋀
      ltF lt (varT u) (varT y) ⋀ ltF lt (varT y) (varT v),
    -- s 0 = 0
    appF (varT s) empT zero,
    -- s (n+1) + aₙ = s n + bₙ
    allIn omT fun n => allF fun m => succF (varT n) (varT m) ⟶
      allF fun u => allF fun v => allF fun w => allF fun w' => allF fun t => allF fun t' =>
        appF (varT a) (varT n) (varT u) ⟶ appF (varT b) (varT n) (varT v) ⟶
        appF (varT s) (varT n) (varT w) ⟶ appF (varT s) (varT m) (varT w') ⟶
        app2F plus (varT w') (varT u) (varT t) ⟶ app2F plus (varT w) (varT v) (varT t') ⟶
        eqF (varT t) (varT t'),
    -- the partial sums are bounded by some r < 1
    exIn R fun r => ltF lt (varT r) one ⋀
      allIn omT fun n => allF fun w => appF (varT s) (varT n) (varT w) ⟶ leF lt (varT w) (varT r)
  ]

/-- `X` is infinite: `ω` injects into `X`.  This renders `X.Infinite`. -/
def InfiniteF (X : Tm) : Fm :=
  exF fun f => isFunF omT X (varT f) ⋀
    allIn omT fun n => allIn omT fun m => allF fun u =>
      appF (varT f) (varT n) (varT u) ⟶ appF (varT f) (varT m) (varT u) ⟶ eqF (varT n) (varT m)

/-- `X` is independent for the family `A`: `∀ x y ∈ X, x ≠ y → x ∉ A(y)`.
This renders `X.Pairwise (fun x y => x ∉ A y)`. -/
def IndependentF (A X : Tm) : Fm :=
  allIn X fun x => allIn X fun y => notF (eqF (varT x) (varT y)) ⟶
    allF fun Ay => appF A (varT y) (varT Ay) ⟶ notF (memF (varT x) (varT Ay))

/-- The Erdős property for the complete ordered field `(R, plus, times, lt, zero, one)`:
for every function `A : R → 𝒫(R)` such that every `A(x)` is bounded and has outer measure `< 1`,
there is an infinite independent `X ⊆ R`. -/
def ErdosPropertyF (R plus lt zero one : Tm) : Fm :=
  allF fun A => isFunF R (powT R) (varT A) ⟶
    (allIn R fun x => allF fun Ax => appF (varT A) (varT x) (varT Ax) ⟶
      BoundedF R lt (varT Ax) ⋀ OuterMeasureLtOneF R plus lt zero one (varT Ax)) ⟶
    exIn (powT R) fun X => InfiniteF (varT X) ⋀ IndependentF (varT A) (varT X)

/-- **Erdős problem #501, first question, as a sentence of `L_ZFC`**: for every complete ordered
field `(R, +, ·, <, 0, 1)`, every family `⟨A_x : x ∈ R⟩` of bounded subsets of `R` of outer
measure `< 1` has an infinite independent set. -/
def Erdos501_f : sentence L_ZFC :=
  toSentence <|
    allF fun R => allF fun plus => allF fun times => allF fun lt => allF fun zeroR => allF fun oneR =>
      CompleteOrderedFieldF (varT R) (varT plus) (varT times) (varT lt) (varT zeroR) (varT oneR) ⟶
      ErdosPropertyF (varT R) (varT plus) (varT lt) (varT zeroR) (varT oneR)

/-- **The existential form of Erdős problem #501, first question**: there is a complete ordered
field `(R, +, ·, <, 0, 1)` with the Erdős property.

`ZFC` proves that any two complete ordered fields are isomorphic and that the Erdős property is
invariant under isomorphism (as is the existence of one, `ℝ`), so `ZFC ⊢ Erdos501_ex_f ↔ Erdos501_f`;
the two sentences are equally faithful renderings of DeepMind's `erdos_501`.  The existential form
is the one established directly by the forcing argument (`Main.lean`: `erdos501_ex_forced`), the
universal form `Erdos501_f` follows from it by the `ZFC`-theorem `Erdos501_ex_f → Erdos501_f`
(unit (F8) of `PLAN.md`). -/
def Erdos501_ex_f : sentence L_ZFC :=
  toSentence <|
    exF fun R => exF fun plus => exF fun times => exF fun lt => exF fun zeroR => exF fun oneR =>
      CompleteOrderedFieldF (varT R) (varT plus) (varT times) (varT lt) (varT zeroR) (varT oneR) ⋀
      ErdosPropertyF (varT R) (varT plus) (varT lt) (varT zeroR) (varT oneR)

end Flypitch.Erdos501
