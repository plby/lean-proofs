/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.ZFC.Basic

open MeasureTheory FirstOrder FirstOrder.Language
open scoped Cardinal FirstOrder

universe u

namespace Erdos501.FOL

inductive Func : ℕ → Type
  | emptyset : Func 0
  | omega : Func 0
  | powerset : Func 1
  | union : Func 1
  | pair : Func 2

inductive Rel : ℕ → Type
  | mem : Rel 2

abbrev L : Language := ⟨Func, Rel⟩

abbrev Fm : Type := ∀ n : ℕ, L.BoundedFormula Empty n

abbrev Tm : Type := ∀ n : ℕ, L.Term (Empty ⊕ Fin n)

def varT (ℓ : ℕ) : Tm := fun n =>
  if h : ℓ < n then Term.var (Sum.inr ⟨ℓ, h⟩) else Term.func Func.emptyset Fin.elim0

def empT : Tm := fun _ => Term.func Func.emptyset Fin.elim0

def omT : Tm := fun _ => Term.func Func.omega Fin.elim0

def powT (t : Tm) : Tm := fun n => Term.func Func.powerset ![t n]

def unionT (t : Tm) : Tm := fun n => Term.func Func.union ![t n]

def pairT (s t : Tm) : Tm := fun n => Term.func Func.pair ![s n, t n]

def memF (s t : Tm) : Fm := fun n => Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (s n) (t n)

def eqF (s t : Tm) : Fm := fun n => Term.bdEqual (s n) (t n)

def andF (φ ψ : Fm) : Fm := fun n => φ n ⊓ ψ n
def orF (φ ψ : Fm) : Fm := fun n => φ n ⊔ ψ n
def impF (φ ψ : Fm) : Fm := fun n => (φ n).imp (ψ n)
def iffF (φ ψ : Fm) : Fm := fun n => (φ n).iff (ψ n)
def notF (φ : Fm) : Fm := fun n => (φ n).not

def allF (φ : ℕ → Fm) : Fm := fun n => (φ n (n + 1)).all

def exF (φ : ℕ → Fm) : Fm := fun n => (φ n (n + 1)).ex

def allIn (t : Tm) (φ : ℕ → Fm) : Fm := allF fun x => impF (memF (varT x) t) (φ x)

def exIn (t : Tm) (φ : ℕ → Fm) : Fm := exF fun x => andF (memF (varT x) t) (φ x)

def andsF : List Fm → Fm
  | [] => notF (fun _ => ⊥)
  | [φ] => φ
  | φ :: φs => andF φ (andsF φs)

def toSentence (φ : Fm) : L.Sentence := φ 0

def subsetF (s t : Tm) : Fm := allF fun z => impF (memF (varT z) s) (memF (varT z) t)

def axiomOfEmptyset : L.Sentence := toSentence <|
  allF fun x => notF (memF (varT x) empT)

def axiomOfOrderedPairs : L.Sentence := toSentence <|
  allF fun x => allF fun y => allF fun z => allF fun w =>
    iffF (eqF (pairT (varT x) (varT y)) (pairT (varT z) (varT w)))
      (andF (eqF (varT x) (varT z)) (eqF (varT y) (varT w)))

def axiomOfExtensionality : L.Sentence := toSentence <|
  allF fun x => allF fun y =>
    impF (allF fun z => iffF (memF (varT z) (varT x)) (memF (varT z) (varT y)))
      (eqF (varT x) (varT y))

def axiomOfUnion : L.Sentence := toSentence <|
  allF fun u => allF fun x =>
    iffF (memF (varT x) (unionT (varT u)))
      (exF fun y => andF (memF (varT y) (varT u)) (memF (varT x) (varT y)))

def axiomOfPowerset : L.Sentence := toSentence <|
  allF fun z => allF fun y =>
    iffF (memF (varT y) (powT (varT z)))
      (allF fun x => impF (memF (varT x) (varT y)) (memF (varT x) (varT z)))

def ordF (a : ℕ) : Fm :=
  andF
    (andF

      (allF fun y => impF (memF (varT y) (varT a)) (allF fun z => impF (memF (varT z) (varT a))
        (orF (orF (eqF (varT y) (varT z)) (memF (varT y) (varT z))) (memF (varT z) (varT y)))))

      (allF fun y => impF (subsetF (varT y) (varT a)) (impF (notF (eqF (varT y) empT))
        (exF fun z => andF (memF (varT z) (varT y))
          (allF fun w => impF (memF (varT w) (varT y)) (notF (memF (varT w) (varT z))))))))

    (allF fun y => impF (memF (varT y) (varT a)) (subsetF (varT y) (varT a)))

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

def axiomOfRegularity : L.Sentence := toSentence <|
  allF fun x => impF (notF (eqF (varT x) empT))
    (exF fun y => andF (memF (varT y) (varT x))
      (allF fun z => impF (memF (varT z) (varT x)) (notF (memF (varT z) (varT y)))))

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

def collectionAxiom (n : ℕ) (ψ : L.BoundedFormula Empty (n + 2)) : L.Sentence :=
  BoundedFormula.alls (n := n + 1) <|
    BoundedFormula.imp

      (BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 1, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) (BoundedFormula.ex (ψ.liftAt 1 n))))
      (BoundedFormula.ex

        ((BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 2, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) (BoundedFormula.ex ((Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 3, by omega⟩)) (Term.var (Sum.inr ⟨n + 1, by omega⟩))) ⊓ (ψ.liftAt 2 n))))) ⊓

         (BoundedFormula.all (BoundedFormula.imp (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 2, by omega⟩)) (Term.var (Sum.inr ⟨n + 1, by omega⟩))) (BoundedFormula.ex ((Relations.boundedFormula₂ (Rel.mem : L.Relations 2) (Term.var (Sum.inr ⟨n + 3, by omega⟩)) (Term.var (Sum.inr ⟨n, by omega⟩))) ⊓ (BoundedFormula.ex ((Term.bdEqual (Term.var (Sum.inr ⟨n + 4, by omega⟩)) (Term.var (Sum.inr ⟨n + 2, by omega⟩))) ⊓ (ψ.liftAt 3 n)))))))))

def ZFC : L.Theory :=
  {axiomOfEmptyset, axiomOfOrderedPairs, axiomOfExtensionality, axiomOfUnion,
    axiomOfPowerset, axiomOfInfinity, axiomOfRegularity, zornsLemma} ∪
  ⋃ n : ℕ, Set.range (collectionAxiom n)

def ltF (lt x y : Tm) : Fm := memF (pairT x y) lt

def leF (lt x y : Tm) : Fm := orF (ltF lt x y) (eqF x y)

def appF (f x y : Tm) : Fm := memF (pairT x y) f

def app2F (op x y z : Tm) : Fm := memF (pairT (pairT x y) z) op

def isFunF (dom cod f : Tm) : Fm :=
  allIn dom fun x => exIn cod fun y =>
    andF (appF f (varT x) (varT y))
      (allF fun y' => impF (appF f (varT x) (varT y')) (eqF (varT y') (varT y)))

def isOp2F (R op : Tm) : Fm :=
  allIn R fun x => allIn R fun y => exIn R fun z =>
    andF (app2F op (varT x) (varT y) (varT z))
      (allF fun z' => impF (app2F op (varT x) (varT y) (varT z')) (eqF (varT z') (varT z)))

def succF (n m : Tm) : Fm :=
  allF fun z => iffF (memF (varT z) m) (orF (memF (varT z) n) (eqF (varT z) n))

def completeOrderedFieldF (R plus times lt zero one : Tm) : Fm :=
  andsF [
    isOp2F R plus,
    isOp2F R times,
    memF zero R,
    memF one R,

    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun w' =>
        impF (app2F plus (varT x) (varT y) (varT u)) <| impF (app2F plus (varT u) (varT z) (varT v)) <|
        impF (app2F plus (varT y) (varT z) (varT w)) <| impF (app2F plus (varT x) (varT w) (varT w')) <|
        eqF (varT v) (varT w'),

    allIn R fun x => allIn R fun y => allF fun u =>
      impF (app2F plus (varT x) (varT y) (varT u)) (app2F plus (varT y) (varT x) (varT u)),

    allIn R fun x => app2F plus (varT x) zero (varT x),

    allIn R fun x => exIn R fun y => app2F plus (varT x) (varT y) zero,

    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun w' =>
        impF (app2F times (varT x) (varT y) (varT u)) <| impF (app2F times (varT u) (varT z) (varT v)) <|
        impF (app2F times (varT y) (varT z) (varT w)) <| impF (app2F times (varT x) (varT w) (varT w')) <|
        eqF (varT v) (varT w'),

    allIn R fun x => allIn R fun y => allF fun u =>
      impF (app2F times (varT x) (varT y) (varT u)) (app2F times (varT y) (varT x) (varT u)),

    allIn R fun x => app2F times (varT x) one (varT x),

    allIn R fun x => impF (notF (eqF (varT x) zero)) (exIn R fun y => app2F times (varT x) (varT y) one),

    notF (eqF zero one),

    allIn R fun x => allIn R fun y => allIn R fun z =>
      allF fun u => allF fun v => allF fun w => allF fun t => allF fun t' =>
        impF (app2F plus (varT y) (varT z) (varT u)) <| impF (app2F times (varT x) (varT u) (varT v)) <|
        impF (app2F times (varT x) (varT y) (varT w)) <| impF (app2F times (varT x) (varT z) (varT t)) <|
        impF (app2F plus (varT w) (varT t) (varT t')) <| eqF (varT v) (varT t'),

    allIn R fun x => notF (ltF lt (varT x) (varT x)),

    allIn R fun x => allIn R fun y => allIn R fun z =>
      impF (ltF lt (varT x) (varT y)) <| impF (ltF lt (varT y) (varT z)) <| ltF lt (varT x) (varT z),

    allIn R fun x => allIn R fun y =>
      orF (ltF lt (varT x) (varT y)) (orF (eqF (varT x) (varT y)) (ltF lt (varT y) (varT x))),

    allIn R fun x => allIn R fun y => allIn R fun z => allF fun u => allF fun v =>
      impF (ltF lt (varT x) (varT y)) <| impF (app2F plus (varT x) (varT z) (varT u)) <|
      impF (app2F plus (varT y) (varT z) (varT v)) <| ltF lt (varT u) (varT v),

    allIn R fun x => allIn R fun y => allF fun u =>
      impF (ltF lt zero (varT x)) <| impF (ltF lt zero (varT y)) <|
      impF (app2F times (varT x) (varT y) (varT u)) <| ltF lt zero (varT u),

    allIn (powT R) fun S =>
      impF (notF (eqF (varT S) empT)) <|
      impF (exIn R fun b => allIn (varT S) fun s => leF lt (varT s) (varT b)) <|
      exIn R fun u =>
        andF (allIn (varT S) fun s => leF lt (varT s) (varT u))
          (allIn R fun v => impF (allIn (varT S) fun s => leF lt (varT s) (varT v))
            (leF lt (varT u) (varT v)))
  ]

def boundedF (R lt S : Tm) : Fm :=
  exIn R fun m₁ => exIn R fun m₂ => allIn S fun y =>
    andF (ltF lt (varT m₁) (varT y)) (ltF lt (varT y) (varT m₂))

def outerMeasureLtOneF (R plus lt zero one S : Tm) : Fm :=
  exF fun a => exF fun b => exF fun s => andsF [
    isFunF omT R (varT a),
    isFunF omT R (varT b),
    isFunF omT R (varT s),

    allIn omT fun n => allF fun u => allF fun v =>
      impF (appF (varT a) (varT n) (varT u)) <| impF (appF (varT b) (varT n) (varT v)) <|
      ltF lt (varT u) (varT v),

    allIn S fun y => exIn omT fun n => exF fun u => exF fun v =>
      andF (appF (varT a) (varT n) (varT u)) <| andF (appF (varT b) (varT n) (varT v)) <|
      andF (ltF lt (varT u) (varT y)) (ltF lt (varT y) (varT v)),

    appF (varT s) empT zero,

    allIn omT fun n => allF fun m => impF (succF (varT n) (varT m)) <|
      allF fun u => allF fun v => allF fun w => allF fun w' => allF fun t => allF fun t' =>
        impF (appF (varT a) (varT n) (varT u)) <| impF (appF (varT b) (varT n) (varT v)) <|
        impF (appF (varT s) (varT n) (varT w)) <| impF (appF (varT s) (varT m) (varT w')) <|
        impF (app2F plus (varT w') (varT u) (varT t)) <| impF (app2F plus (varT w) (varT v) (varT t')) <|
        eqF (varT t) (varT t'),

    exIn R fun r => andF (ltF lt (varT r) one)
      (allIn omT fun n => allF fun w => impF (appF (varT s) (varT n) (varT w)) (leF lt (varT w) (varT r)))
  ]

def infiniteF (X : Tm) : Fm :=
  exF fun f => andF (isFunF omT X (varT f))
    (allIn omT fun n => allIn omT fun m => allF fun u =>
      impF (appF (varT f) (varT n) (varT u)) <| impF (appF (varT f) (varT m) (varT u)) <|
      eqF (varT n) (varT m))

def independentF (A X : Tm) : Fm :=
  allIn X fun x => allIn X fun y => impF (notF (eqF (varT x) (varT y)))
    (allF fun Ay => impF (appF A (varT y) (varT Ay)) (notF (memF (varT x) (varT Ay))))

def erdosPropertyF (R plus lt zero one : Tm) : Fm :=
  allF fun A => impF (isFunF R (powT R) (varT A)) <|
    impF (allIn R fun x => allF fun Ax => impF (appF (varT A) (varT x) (varT Ax))
      (andF (boundedF R lt (varT Ax)) (outerMeasureLtOneF R plus lt zero one (varT Ax)))) <|
    exIn (powT R) fun X => andF (infiniteF (varT X)) (independentF (varT A) (varT X))

def Erdos501 : L.Sentence :=
  toSentence <|
    allF fun R => allF fun plus => allF fun times => allF fun lt => allF fun zeroR => allF fun oneR =>
      impF (completeOrderedFieldF (varT R) (varT plus) (varT times) (varT lt) (varT zeroR) (varT oneR))
        (erdosPropertyF (varT R) (varT plus) (varT lt) (varT zeroR) (varT oneR))

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

open Erdos501.FOL

theorem erdos501_closed_infinite :
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  sorry

theorem erdos501_closed_size3 :
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, 3 ≤ X.ncard ∧ X.Pairwise (fun x y => x ∉ A y) := by
  sorry

theorem erdos501_hechler_of_CH :
    ((ℵ₁ : Cardinal.{u}) = 𝔠) →
    ∃ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) ∧
      (∀ x, volume.toOuterMeasure (A x) < 1) ∧
      ¬ ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  sorry

theorem erdos501_not_refutable : ¬ (ZFC ⊨ᵇ ∼Erdos501) := by
  sorry

theorem erdos501_not_provable : ¬ (ZFC ⊨ᵇ Erdos501) := by
  sorry

theorem Erdos501.erdos_501 : ¬ (ZFC ⊨ᵇ Erdos501) ∧ ¬ (ZFC ⊨ᵇ ∼Erdos501) := by
  sorry

theorem erdos501_sentence_faithful :
    (ZFSet.{0} ⊨ Erdos501) ↔
      ∀ (A : ℝ → Set ℝ),
        (∀ x, Bornology.IsBounded (A x)) →
        (∀ x, volume.toOuterMeasure (A x) < 1) →
        ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  sorry
