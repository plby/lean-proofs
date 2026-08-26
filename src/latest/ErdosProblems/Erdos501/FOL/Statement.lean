/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The statement definitions of `Challenge.lean` (verbatim copy)

GENERATED FILE — do not edit.  This is Part A of `Challenge.lean` (the language `L`, the theory
`ZFC`, the sentence `Erdos501` and the `L`-structure on `ZFSet`), reproduced verbatim by
`scripts/sync-statement.py` so that the Solution — which must not import the Challenge — can
prove statements about *literally* the same constants.  The comparator checks that the two copies
define identical declarations; `scripts/sync-statement.py --check` (run in CI) checks the text.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.ZFC.Basic

open MeasureTheory
open scoped Cardinal FirstOrder
open FirstOrder FirstOrder.Language

namespace Erdos501.FOL

/-! ### The language `L` of set theory -/

/-- Function symbols: `∅` (arity 0), `ω` (arity 0), `𝒫` (arity 1), `⋃` (arity 1),
the ordered pair `(·,·)` (arity 2). -/
inductive Func : ℕ → Type
  | emptyset : Func 0
  | omega : Func 0
  | powerset : Func 1
  | union : Func 1
  | pair : Func 2

/-- Relation symbols: `∈` (arity 2). -/
inductive Rel : ℕ → Type
  | mem : Rel 2

/-- The first-order language of set theory used here: `∅, ω, 𝒫, ⋃, (·,·)` and `∈`. -/
abbrev L : Language := ⟨Func, Rel⟩

/-! ### Depth-polymorphic formulas

Formulas of Mathlib's `ModelTheory` are `L.BoundedFormula Empty n` with `n` bound
variables `&0, …, &(n-1)`; a quantifier `∀'`/`∃'` binds the *last* variable
`&n`.  So `&ℓ` is the variable of de Bruijn *level* `ℓ` (`0` = outermost).  We
build formulas through *depth-polymorphic* formulas `Fm := ∀ n, L.BoundedFormula Empty n`
and terms `Tm := ∀ n, L.Term (Empty ⊕ Fin n)`: `allF fun x => φ x` binds a new
variable and passes its level `x` to the body, so that scoping is checked by
Lean and no lifting is ever needed; a sentence is obtained by evaluating at
depth `0` (`toSentence`). -/

/-- Depth-polymorphic formulas. -/
abbrev Fm : Type := ∀ n : ℕ, L.BoundedFormula Empty n

/-- Depth-polymorphic terms. -/
abbrev Tm : Type := ∀ n : ℕ, L.Term (Empty ⊕ Fin n)

/-- The variable of de Bruijn level `ℓ` (`0` = outermost).  (For `ℓ ≥ n` — never
used — it is the constant `∅`.) -/
def varT (ℓ : ℕ) : Tm := fun n =>
  if h : ℓ < n then Term.var (Sum.inr ⟨ℓ, h⟩) else Term.func Func.emptyset Fin.elim0

/-- The constant `∅`. -/
def empT : Tm := fun _ => Term.func Func.emptyset Fin.elim0

/-- The constant `ω`. -/
def omT : Tm := fun _ => Term.func Func.omega Fin.elim0

/-- The power set `𝒫 t`. -/
def powT (t : Tm) : Tm := fun n => Term.func Func.powerset ![t n]

/-- The union `⋃ t`. -/
def unionT (t : Tm) : Tm := fun n => Term.func Func.union ![t n]

/-- The ordered pair `(s, t)`. -/
def pairT (s t : Tm) : Tm := fun n => Term.func Func.pair ![s n, t n]

/-- `s ∈ t`. -/
def memF (s t : Tm) : Fm := fun n => Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (s n) (t n)

/-- `s = t`. -/
def eqF (s t : Tm) : Fm := fun n => Term.bdEqual (s n) (t n)

def andF (φ ψ : Fm) : Fm := fun n => φ n ⊓ ψ n
def orF (φ ψ : Fm) : Fm := fun n => φ n ⊔ ψ n
def impF (φ ψ : Fm) : Fm := fun n => (φ n).imp (ψ n)
def iffF (φ ψ : Fm) : Fm := fun n => (φ n).iff (ψ n)
def notF (φ : Fm) : Fm := fun n => (φ n).not

/-- `∀ x, φ x`; the body receives the *level* of the bound variable. -/
def allF (φ : ℕ → Fm) : Fm := fun n => (φ n (n + 1)).all

/-- `∃ x, φ x`; the body receives the *level* of the bound variable. -/
def exF (φ : ℕ → Fm) : Fm := fun n => (φ n (n + 1)).ex

/-- `∀ x ∈ t, φ x`. -/
def allIn (t : Tm) (φ : ℕ → Fm) : Fm := allF fun x => impF (memF (varT x) t) (φ x)

/-- `∃ x ∈ t, φ x`. -/
def exIn (t : Tm) (φ : ℕ → Fm) : Fm := exF fun x => andF (memF (varT x) t) (φ x)

/-- Conjunction of a list of formulas (`⊤` for the empty list). -/
def andsF : List Fm → Fm
  | [] => notF (fun _ => ⊥)
  | [φ] => φ
  | φ :: φs => andF φ (andsF φs)

/-- The sentence denoted by a depth-polymorphic formula (evaluation at depth `0`). -/
def toSentence (φ : Fm) : L.Sentence := φ 0

/-- `s ⊆ t`. -/
def subsetF (s t : Tm) : Fm := allF fun z => impF (memF (varT z) s) (memF (varT z) t)

/-! ### The theory `ZFC` -/

/-- `∀ x, x ∉ ∅`. -/
def axiomOfEmptyset : L.Sentence := toSentence <|
  allF fun x => notF (memF (varT x) empT)

/-- `∀ x y z w, (x, y) = (z, w) ↔ x = z ∧ y = w`: the pairing symbol produces
ordered pairs. -/
def axiomOfOrderedPairs : L.Sentence := toSentence <|
  allF fun x => allF fun y => allF fun z => allF fun w =>
    iffF (eqF (pairT (varT x) (varT y)) (pairT (varT z) (varT w)))
      (andF (eqF (varT x) (varT z)) (eqF (varT y) (varT w)))

/-- `∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
def axiomOfExtensionality : L.Sentence := toSentence <|
  allF fun x => allF fun y =>
    impF (allF fun z => iffF (memF (varT z) (varT x)) (memF (varT z) (varT y)))
      (eqF (varT x) (varT y))

/-- `∀ u x, x ∈ ⋃ u ↔ ∃ y, y ∈ u ∧ x ∈ y`. -/
def axiomOfUnion : L.Sentence := toSentence <|
  allF fun u => allF fun x =>
    iffF (memF (varT x) (unionT (varT u)))
      (exF fun y => andF (memF (varT y) (varT u)) (memF (varT x) (varT y)))

/-- `∀ z y, y ∈ 𝒫 z ↔ ∀ x, x ∈ y → x ∈ z`. -/
def axiomOfPowerset : L.Sentence := toSentence <|
  allF fun z => allF fun y =>
    iffF (memF (varT y) (powT (varT z)))
      (allF fun x => impF (memF (varT x) (varT y)) (memF (varT x) (varT z)))

/-- `a` (a variable level) is an ordinal: `∈` is trichotomous and well-founded on
`a`, and `a` is transitive. -/
def ordF (a : ℕ) : Fm :=
  andF
    (andF
      -- ∈-trichotomy on `a`
      (allF fun y => impF (memF (varT y) (varT a)) (allF fun z => impF (memF (varT z) (varT a))
        (orF (orF (eqF (varT y) (varT z)) (memF (varT y) (varT z))) (memF (varT z) (varT y)))))
      -- ∈-well-foundedness on `a`: every nonempty subset has an ∈-minimal element
      (allF fun y => impF (subsetF (varT y) (varT a)) (impF (notF (eqF (varT y) empT))
        (exF fun z => andF (memF (varT z) (varT y))
          (allF fun w => impF (memF (varT w) (varT y)) (notF (memF (varT w) (varT z))))))))
    -- transitivity of `a`
    (allF fun y => impF (memF (varT y) (varT a)) (subsetF (varT y) (varT a)))

/-- Infinity: `∅ ∈ ω`, `ω` is closed under "there is a larger element", `ω` is an
ordinal, and `ω` is contained in every ordinal `a` with `∅ ∈ a` closed under
"there is a larger element" — i.e. `ω` is the least infinite ordinal. -/
def axiomOfInfinity : L.Sentence := toSentence <|
  andF
    (andF
      (andF
        (memF empT omT)
        (allF fun x => impF (memF (varT x) omT)
          (exF fun y => andF (memF (varT y) omT) (memF (varT x) (varT y)))))
      (exF fun a => andF (ordF a) (eqF omT (varT a))))
    (allF fun a => impF (ordF a) (impF
      (andF (memF empT (varT a))
        (allF fun x => impF (memF (varT x) (varT a))
          (exF fun y => andF (memF (varT y) (varT a)) (memF (varT x) (varT y)))))
      (subsetF omT (varT a))))

/-- `∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y`. -/
def axiomOfRegularity : L.Sentence := toSentence <|
  allF fun x => impF (notF (eqF (varT x) empT))
    (exF fun y => andF (memF (varT y) (varT x))
      (allF fun z => impF (memF (varT z) (varT x)) (notF (memF (varT z) (varT y)))))

/-- Zorn's lemma: if `x ≠ ∅` and the union of every chain `y ⊆ x` (a subset of `x`
linearly ordered by `⊆`) belongs to `x`, then `x` has a `⊆`-maximal element. -/
def zornsLemma : L.Sentence := toSentence <|
  allF fun x => impF (notF (eqF (varT x) empT)) (impF
    (allF fun y => impF
      (andF (subsetF (varT y) (varT x))
        (allF fun w₁ => allF fun w₂ =>
          impF (andF (memF (varT w₁) (varT y)) (memF (varT w₂) (varT y)))
            (orF (subsetF (varT w₁) (varT w₂)) (subsetF (varT w₂) (varT w₁)))))
      (memF (unionT (varT y)) (varT x)))
    (exF fun m => andF (memF (varT m) (varT x))
      (allF fun z => impF (memF (varT z) (varT x))
        (impF (subsetF (varT m) (varT z)) (eqF (varT m) (varT z))))))

/-- Strong collection for the formula `ψ`, whose bound variables are the `n`
parameters `&0, …, &(n-1)`, `x = &n` and `y = &(n+1)`:

`∀ params, ∀ u, (∀ x ∈ u, ∃ y, ψ) → ∃ v, (∀ x ∈ u, ∃ y ∈ v, ψ) ∧ (∀ y ∈ v, ∃ x ∈ u, ψ)`.

`ψ.liftAt k n` is `ψ` with `k` new variables inserted at level `n` (i.e. below
`x` and `y`, above the parameters); in the last conjunct the roles of the two
innermost variables are exchanged by introducing a copy `y'` of `y`.  The
levels of the variables in the three clauses are (`p` = parameters):
`p, u, x, y`; `p, u, v, x, y`; `p, u, v, y, x, y'`. -/
def collectionAxiom (n : ℕ) (ψ : L.BoundedFormula Empty (n + 2)) : L.Sentence :=
  BoundedFormula.alls (n := n + 1) <|
    BoundedFormula.imp
      -- ∀ x ∈ u, ∃ y, ψ                                    (levels: p, u, x, y)
      (BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 1, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) (BoundedFormula.ex (ψ.liftAt 1 n))))
      (BoundedFormula.ex
        -- ∀ x ∈ u, ∃ y ∈ v, ψ                              (levels: p, u, v, x, y)
        ((BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 2, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) (BoundedFormula.ex ((Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 3, by omega⟩)) (Term.var (Sum.inr ⟨n + 1, by omega⟩))) ⊓ (ψ.liftAt 2 n))))) ⊓
         -- ∀ y ∈ v, ∃ x ∈ u, ∃ y', y' = y ∧ ψ              (levels: p, u, v, y, x, y')
         (BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 2, by omega⟩)) (Term.var (Sum.inr ⟨n + 1, by omega⟩))) (BoundedFormula.ex ((Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 3, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) ⊓ (BoundedFormula.ex ((Term.bdEqual (Term.var (Sum.inr ⟨n + 4, by omega⟩)) (Term.var (Sum.inr ⟨n + 2, by omega⟩))) ⊓ (ψ.liftAt 3 n)))))))))

/-- **The theory `ZFC`**: extensionality, empty set, ordered pairs, union, power
set, infinity, regularity, Zorn's lemma, and the strong collection scheme.  This
is the axiom system of Han–van Doorn's Flypitch formalization of ZFC; it is
equivalent to the usual ZFC. -/
def ZFC : L.Theory :=
  {axiomOfEmptyset, axiomOfOrderedPairs, axiomOfExtensionality, axiomOfUnion,
    axiomOfPowerset, axiomOfInfinity, axiomOfRegularity, zornsLemma} ∪
  ⋃ n : ℕ, Set.range (collectionAxiom n)

/-! ### The sentence `Erdos501`

We follow DeepMind's formalization of the first question and render it as
follows.

* **The real numbers.**  Rather than constructing `ℝ` inside set theory, the
  sentence quantifies over *all* complete ordered fields `(R, +, ·, <, 0, 1)`
  given as sets (`+`, `·` as sets of triples `((x, y), z)`, `<` as a set of pairs)
  and asserts the Erdős property for each of them.  ZFC proves that any two
  complete ordered fields are isomorphic and the Erdős property is invariant
  under isomorphism, so this is ZFC-equivalent to the property for `ℝ`.
* **Bounded.**  `∃ m₁ m₂ ∈ R, ∀ y ∈ A_x, m₁ < y < m₂` (`boundedF`).
* **Outer measure `< 1`.**  Lebesgue outer measure is the infimum of `∑ (bₙ - aₙ)`
  over covers by countably many open intervals; it is `< 1` iff there is a cover
  `(aₙ, bₙ)ₙ∈ω` with all partial sums `sₙ = ∑_{k<n} (b_k - a_k)` (defined by
  `s₀ = 0`, `s_{n+1} + aₙ = sₙ + bₙ`) bounded by some `r < 1`
  (`outerMeasureLtOneF`).
* **Infinite.**  `ω` injects into `X` (`infiniteF`; ZFC-equivalent to "not
  finite" by choice).
* **Independent.**  `∀ x y ∈ X, x ≠ y → x ∉ A(y)` (`independentF`). -/

/-- `x < y`, for an order relation `lt` given as a set of ordered pairs. -/
def ltF (lt x y : Tm) : Fm := memF (pairT x y) lt

/-- `x ≤ y`, i.e. `x < y ∨ x = y`. -/
def leF (lt x y : Tm) : Fm := orF (ltF lt x y) (eqF x y)

/-- `f(x) = y`, for a function `f` given as a set of ordered pairs. -/
def appF (f x y : Tm) : Fm := memF (pairT x y) f

/-- `op(x, y) = z`, for a binary operation `op` given as a set of pairs `((x, y), z)`. -/
def app2F (op x y z : Tm) : Fm := memF (pairT (pairT x y) z) op

/-- `f` is a (total, single-valued) function from `dom` to `cod`: every `x ∈ dom`
has exactly one `f`-value, and it lies in `cod`. -/
def isFunF (dom cod f : Tm) : Fm :=
  allIn dom fun x => exIn cod fun y =>
    andF (appF f (varT x) (varT y))
      (allF fun y' => impF (appF f (varT x) (varT y')) (eqF (varT y') (varT y)))

/-- `op` is a binary operation on `R`: every pair `(x, y) ∈ R × R` has exactly one
`op`-value, and it lies in `R`. -/
def isOp2F (R op : Tm) : Fm :=
  allIn R fun x => allIn R fun y => exIn R fun z =>
    andF (app2F op (varT x) (varT y) (varT z))
      (allF fun z' => impF (app2F op (varT x) (varT y) (varT z')) (eqF (varT z') (varT z)))

/-- `m = n ∪ {n}` (the successor of `n`). -/
def succF (n m : Tm) : Fm :=
  allF fun z => iffF (memF (varT z) m) (orF (memF (varT z) n) (eqF (varT z) n))

/-- `(R, plus, times, lt, zero, one)` is a complete ordered field: `plus`, `times`
are binary operations on `R`, `zero, one ∈ R`, the field axioms, the axioms of a
total order compatible with `+` and `·`, and Dedekind completeness (every
nonempty subset of `R` with an upper bound has a least upper bound). -/
def completeOrderedFieldF (R plus times lt zero one : Tm) : Fm :=
  andsF [
    isOp2F R plus,
    isOp2F R times,
    memF zero R,
    memF one R,
    -- `+` is associative: x + y = u → u + z = v → y + z = w → x + w = w' → v = w'
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun w' =>
        impF (app2F plus (varT x) (varT y) (varT u)) <| impF (app2F plus (varT u) (varT z) (varT v)) <|
        impF (app2F plus (varT y) (varT z) (varT w)) <| impF (app2F plus (varT x) (varT w) (varT w')) <|
        eqF (varT v) (varT w'),
    -- `+` is commutative
    allIn R fun x => allIn R fun y => allF fun u =>
      impF (app2F plus (varT x) (varT y) (varT u)) (app2F plus (varT y) (varT x) (varT u)),
    -- x + 0 = x
    allIn R fun x => app2F plus (varT x) zero (varT x),
    -- additive inverses
    allIn R fun x => exIn R fun y => app2F plus (varT x) (varT y) zero,
    -- `·` is associative
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun w' =>
        impF (app2F times (varT x) (varT y) (varT u)) <| impF (app2F times (varT u) (varT z) (varT v)) <|
        impF (app2F times (varT y) (varT z) (varT w)) <| impF (app2F times (varT x) (varT w) (varT w')) <|
        eqF (varT v) (varT w'),
    -- `·` is commutative
    allIn R fun x => allIn R fun y => allF fun u =>
      impF (app2F times (varT x) (varT y) (varT u)) (app2F times (varT y) (varT x) (varT u)),
    -- x · 1 = x
    allIn R fun x => app2F times (varT x) one (varT x),
    -- multiplicative inverses of nonzero elements
    allIn R fun x => impF (notF (eqF (varT x) zero)) (exIn R fun y => app2F times (varT x) (varT y) one),
    -- 0 ≠ 1
    notF (eqF zero one),
    -- distributivity: y + z = u → x · u = v → x · y = w → x · z = t → w + t = t' → v = t'
    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun t => allF fun t' =>
        impF (app2F plus (varT y) (varT z) (varT u)) <| impF (app2F times (varT x) (varT u) (varT v)) <|
        impF (app2F times (varT x) (varT y) (varT w)) <| impF (app2F times (varT x) (varT z) (varT t)) <|
        impF (app2F plus (varT w) (varT t) (varT t')) <| eqF (varT v) (varT t'),
    -- `<` is irreflexive
    allIn R fun x => notF (ltF lt (varT x) (varT x)),
    -- `<` is transitive
    allIn R fun x => allIn R fun y => allIn R fun z =>
      impF (ltF lt (varT x) (varT y)) <| impF (ltF lt (varT y) (varT z)) <| ltF lt (varT x) (varT z),
    -- `<` is total
    allIn R fun x => allIn R fun y =>
      orF (ltF lt (varT x) (varT y)) (orF (eqF (varT x) (varT y)) (ltF lt (varT y) (varT x))),
    -- `<` is compatible with `+`: x < y → x + z = u → y + z = v → u < v
    allIn R fun x => allIn R fun y => allIn R fun z => allF fun u => allF fun v =>
      impF (ltF lt (varT x) (varT y)) <| impF (app2F plus (varT x) (varT z) (varT u)) <|
      impF (app2F plus (varT y) (varT z) (varT v)) <| ltF lt (varT u) (varT v),
    -- products of positive elements are positive: 0 < x → 0 < y → x · y = u → 0 < u
    allIn R fun x => allIn R fun y => allF fun u =>
      impF (ltF lt zero (varT x)) <| impF (ltF lt zero (varT y)) <|
      impF (app2F times (varT x) (varT y) (varT u)) <| ltF lt zero (varT u),
    -- Dedekind completeness: every nonempty bounded-above `S ⊆ R` has a least upper bound
    allIn (powT R) fun S =>
      impF (notF (eqF (varT S) empT)) <|
      impF (exIn R fun b => allIn (varT S) fun s => leF lt (varT s) (varT b)) <|
      exIn R fun u =>
        andF (allIn (varT S) fun s => leF lt (varT s) (varT u))
          (allIn R fun v => impF (allIn (varT S) fun s => leF lt (varT s) (varT v))
            (leF lt (varT u) (varT v)))
  ]

/-- `S` is bounded (above and below) in `(R, <)`: `∃ m₁ m₂ ∈ R, ∀ y ∈ S, m₁ < y < m₂`.
This renders `Bornology.IsBounded (A x)`. -/
def boundedF (R lt S : Tm) : Fm :=
  exIn R fun m₁ => exIn R fun m₂ => allIn S fun y =>
    andF (ltF lt (varT m₁) (varT y)) (ltF lt (varT y) (varT m₂))

/-- The Lebesgue outer measure of `S ⊆ R` is `< 1`: there are sequences
`a, b : ω → R` with `aₙ < bₙ`, such that the open intervals `(aₙ, bₙ)` cover `S`,
and whose total length `∑ₙ (bₙ - aₙ)` is `< 1`; the total length is expressed
through the partial sums `s : ω → R`, `s 0 = 0`, `s (n+1) + aₙ = s n + bₙ`, all of
which are `≤ r` for some `r < 1`.  This renders `volume.toOuterMeasure (A x) < 1`. -/
def outerMeasureLtOneF (R plus lt zero one S : Tm) : Fm :=
  exF fun a => exF fun b => exF fun s => andsF [
    isFunF omT R (varT a),
    isFunF omT R (varT b),
    isFunF omT R (varT s),
    -- the intervals are nondegenerate: ∀ n ∈ ω, aₙ < bₙ
    allIn omT fun n => allF fun u => allF fun v =>
      impF (appF (varT a) (varT n) (varT u)) <| impF (appF (varT b) (varT n) (varT v)) <|
      ltF lt (varT u) (varT v),
    -- they cover `S`: ∀ y ∈ S, ∃ n ∈ ω, aₙ < y < bₙ
    allIn S fun y => exIn omT fun n => exF fun u => exF fun v =>
      andF (appF (varT a) (varT n) (varT u)) <| andF (appF (varT b) (varT n) (varT v)) <|
      andF (ltF lt (varT u) (varT y)) (ltF lt (varT y) (varT v)),
    -- s 0 = 0
    appF (varT s) empT zero,
    -- s (n+1) + aₙ = s n + bₙ
    allIn omT fun n => allF fun m => impF (succF (varT n) (varT m)) <|
      allF fun u => allF fun v => allF fun w => allF fun w' => allF fun t => allF fun t' =>
        impF (appF (varT a) (varT n) (varT u)) <| impF (appF (varT b) (varT n) (varT v)) <|
        impF (appF (varT s) (varT n) (varT w)) <| impF (appF (varT s) (varT m) (varT w')) <|
        impF (app2F plus (varT w') (varT u) (varT t)) <| impF (app2F plus (varT w) (varT v) (varT t')) <|
        eqF (varT t) (varT t'),
    -- the partial sums are bounded by some r < 1
    exIn R fun r => andF (ltF lt (varT r) one)
      (allIn omT fun n => allF fun w => impF (appF (varT s) (varT n) (varT w)) (leF lt (varT w) (varT r)))
  ]

/-- `X` is infinite: `ω` injects into `X`.  This renders `X.Infinite`. -/
def infiniteF (X : Tm) : Fm :=
  exF fun f => andF (isFunF omT X (varT f))
    (allIn omT fun n => allIn omT fun m => allF fun u =>
      impF (appF (varT f) (varT n) (varT u)) <| impF (appF (varT f) (varT m) (varT u)) <|
      eqF (varT n) (varT m))

/-- `X` is independent for the family `A`: `∀ x y ∈ X, x ≠ y → x ∉ A(y)`.
This renders `X.Pairwise (fun x y => x ∉ A y)`. -/
def independentF (A X : Tm) : Fm :=
  allIn X fun x => allIn X fun y => impF (notF (eqF (varT x) (varT y)))
    (allF fun Ay => impF (appF A (varT y) (varT Ay)) (notF (memF (varT x) (varT Ay))))

/-- The Erdős property for the complete ordered field `(R, plus, times, lt, zero, one)`:
for every function `A : R → 𝒫(R)` such that every `A(x)` is bounded and has outer
measure `< 1`, there is an infinite independent `X ⊆ R`. -/
def erdosPropertyF (R plus lt zero one : Tm) : Fm :=
  allF fun A => impF (isFunF R (powT R) (varT A)) <|
    impF (allIn R fun x => allF fun Ax => impF (appF (varT A) (varT x) (varT Ax))
      (andF (boundedF R lt (varT Ax)) (outerMeasureLtOneF R plus lt zero one (varT Ax)))) <|
    exIn (powT R) fun X => andF (infiniteF (varT X)) (independentF (varT A) (varT X))

set_option linter.dupNamespace false in
/-- **Erdős problem #501, first question, as a sentence of `L`**: for every complete
ordered field `(R, +, ·, <, 0, 1)`, every family `⟨A_x : x ∈ R⟩` of bounded subsets
of `R` of outer measure `< 1` has an infinite independent set. -/
def Erdos501 : L.Sentence :=
  toSentence <|
    allF fun R => allF fun plus => allF fun times => allF fun lt => allF fun zeroR => allF fun oneR =>
      impF (completeOrderedFieldF (varT R) (varT plus) (varT times) (varT lt) (varT zeroR) (varT oneR))
        (erdosPropertyF (varT R) (varT plus) (varT lt) (varT zeroR) (varT oneR))

/-! ### The standard interpretation in Mathlib's `ZFSet` -/

/-- Mathlib's `ZFSet` as an `L`-structure: `∅ ↦ ∅`, `ω ↦ ω`, `𝒫 ↦ powerset`,
`⋃ ↦ sUnion`, `(·,·) ↦ Kuratowski pair`, `∈ ↦ ∈`. -/
noncomputable instance zfsetStructure : L.Structure ZFSet.{0} where
  funMap {n} f xs :=
    match n, f, xs with
    | _, Func.emptyset, _ => ∅
    | _, Func.omega, _ => ZFSet.omega
    | _, Func.powerset, xs => ZFSet.powerset (xs 0)
    | _, Func.union, xs => ZFSet.sUnion (xs 0)
    | _, Func.pair, xs => ZFSet.pair (xs 0) (xs 1)
  RelMap {n} r xs :=
    match n, r, xs with
    | _, Rel.mem, xs => xs 0 ∈ xs 1

end Erdos501.FOL
