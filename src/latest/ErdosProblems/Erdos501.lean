/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in Erdos501/LICENSE.

Formal authors: Claude Fable 5 and Claude Opus 4.8, directed by Elliot Glazer.
The Flypitch dependency credits Jesse Michael Han, Floris van Doorn, and
Ian Klatzco with Claude (Lean 4 port). See Erdos501/NOTICE.
Source: https://github.com/elliotglazer/erdos501
Revision: 218d1c1e46f77d4db80e566d1721782e85b94a17 (Lean 4.34.0-rc1).
Claim: https://www.erdosproblems.com/forum/thread/501/proof-claims#proof-claim-207
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.ZFC.Basic
import ErdosProblems.Erdos501.Development

open MeasureTheory
open scoped Cardinal FirstOrder
open FirstOrder FirstOrder.Language

universe u

open Erdos501.FOL

/-! ### Second question: closed sets of measure `< 1` -/

theorem erdos501_closed_infinite :
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) :=
  fun A hA hvol => Erdos501.erdos501_pairwise A hA hvol

theorem erdos501_closed_size3 :
    ∀ (A : ℝ → Set ℝ),
      (∀ x, IsClosed (A x)) →
      (∀ x, volume (A x) < 1) →
      ∃ X : Set ℝ, 3 ≤ X.ncard ∧ X.Pairwise (fun x y => x ∉ A y) :=
  fun A hA hvol => Erdos501.erdos501_ncard_three A hA hvol

/-! ### First question: Hechler's counterexample under `CH` -/

theorem erdos501_hechler_of_CH :
    ((ℵ₁ : Cardinal.{u}) = 𝔠) →
    ∃ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) ∧
      (∀ x, volume.toOuterMeasure (A x) < 1) ∧
      ¬ ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) :=
  fun hCH => Erdos501.hechler_of_CH hCH

/-! ### First question: independence from `ZFC` -/

theorem erdos501_not_refutable : ¬ (ZFC ⊨ᵇ ∼Erdos501) :=
  Erdos501.FOL.erdos501_not_refutable

theorem erdos501_not_provable : ¬ (ZFC ⊨ᵇ Erdos501) :=
  Erdos501.FOL.erdos501_not_provable

theorem Erdos501.erdos_501 : ¬ (ZFC ⊨ᵇ Erdos501) ∧ ¬ (ZFC ⊨ᵇ ∼Erdos501) :=
  Erdos501.FOL.erdos501_independent

theorem erdos501_sentence_faithful :
    (ZFSet.{0} ⊨ Erdos501) ↔
      ∀ (A : ℝ → Set ℝ),
        (∀ x, Bornology.IsBounded (A x)) →
        (∀ x, volume.toOuterMeasure (A x) < 1) →
        ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) :=
  Erdos501.FOL.realize_Erdos501_iff
