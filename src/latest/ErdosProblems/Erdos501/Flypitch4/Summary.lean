/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/summary.lean (96 lines) — Task 24 (FINAL FILE)
import ErdosProblems.Erdos501.Flypitch4.Zfc
import ErdosProblems.Erdos501.Flypitch4.Completeness
import ErdosProblems.Erdos501.Flypitch4.PrintFormula

set_option relaxedAutoImplicit true

open Fol bSet

/-
This file summarizes:
 - important definitions with #print statements, and
 - important theorems with duplicated proofs

 The user is encouraged to use their editor's jump-to-definition
 feature to inspect the source code of any expressions which are
 printed or which occur in the proofs below.
-/

-- ============================================================
-- #print statements for key definitions
-- ============================================================

#print Language

#print preterm

#print preformula

-- `term` is a reducible alias: @[reducible] def term := preterm L 0
#print Fol.term

-- `formula` is a reducible alias: @[reducible] def formula (L : Language.{u}) := preformula L 0
#print Fol.formula

-- `sentence` is a reducible alias: @[reducible] def sentence := presentence L 0
#print Fol.sentence

-- `soundness` in Lean 4 is `formula_soundness` / `ssatisfied_soundness`
#print Fol.formula_soundness

-- `prf` is the derivation inductive type
#print Fol.prf

-- `provable` is defined as Nonempty (T ⊢ f)
#print Fol.provable

-- `is_consistent` (formula-level)
#print Fol.is_consistent

-- pSet is from Mathlib (ZFSet / WFModel); in Lean 3 this was a custom inductive
-- `pSet` in Lean 4 corresponds to `PSet` from Mathlib
#print PSet

-- bSet is our boolean-valued sets
#print bSet

-- L_ZFC is the language of set theory
#print L_ZFC

-- ZFC is the theory (set of sentences)
#print ZFC

-- Print the ZFC axioms as readable formulas
#eval print_formula_list ([ axiom_of_emptyset,
                            axiom_of_ordered_pairs,
                            axiom_of_extensionality,
                            axiom_of_union,
                            axiom_of_powerset,
                            axiom_of_infinity,
                            axiom_of_regularity,
                            zorns_lemma ])

-- CH is the boolean value in bSet
-- Note: In Lean 3, CH was defined in bvm_extras; here it lives in BvmExtras
-- #print CH  -- CH is a noncomputable def in a variable section, not globally #print-able

-- CH_f is the first-order sentence expressing CH
#print CH_f

-- 𝔹_cohen is the Cohen forcing algebra (defined in Forcing.lean)
#print 𝔹_cohen

-- 𝔹_collapse is the collapse algebra (defined in ForcingCH.lean, in namespace collapse_algebra)
#print collapse_algebra.𝔹_collapse

-- ============================================================
-- The marquee theorems
-- ============================================================

/-- The Gödel Completeness Theorem: a sentence is provable from T iff it is semantically
    entailed by T. -/
theorem godel_completeness_theorem {L : Language} (T : SentTheory L) (ψ : sentence L) :
    (T ⊢ₛ' ψ) ↔ ssatisfied T ψ :=
  completeness T ψ

/-- Boolean-valued soundness: if a sentence is provable, then it is forced in any
    boolean-valued model. -/
theorem boolean_valued_soundness_theorem {L : Language} {β : Type*}
    [CompleteBooleanAlgebra β] {T : SentTheory L} {A : sentence L}
    (H : T ⊢ₛ' A) : T ⊨[β] A :=
  forced_of_bsatisfied (boolean_formula_soundness (β := β) (Classical.choice H))

/-- The Fundamental Theorem of Forcing: bSet β is a boolean-valued model of ZFC
    for any nontrivial complete boolean algebra β. -/
theorem fundamental_theorem_of_forcing {β : Type 0} [NontrivialCompleteBooleanAlgebra β] :
    ⊤ ⊩ₜ[V β] ZFC :=
  bSet_models_ZFC (β := β)

/-- ZFC is consistent (witnessed by a boolean-valued model). -/
theorem ZFC_is_consistent {β : Type 0} [NontrivialCompleteBooleanAlgebra β] :
    SentTheory.is_consistent ZFC :=
  consis_of_exists_bmodel (β := β) (S := V β) bSet_models_ZFC

/-- The Continuum Hypothesis is not provable from ZFC. -/
theorem CH_unprovable : ¬ (ZFC ⊢ₛ' CH_f) :=
  CH_f_unprovable

/-- The negation of the Continuum Hypothesis is not provable from ZFC. -/
theorem neg_CH_unprovable : ¬ (ZFC ⊢ₛ' (bd_not CH_f : sentence L_ZFC)) :=
  neg_CH_f_unprovable

/-- A sentence f is independent of theory T if neither f nor ¬f is provable from T. -/
def independent {L : Language} (T : SentTheory L) (f : sentence L) : Prop :=
  (¬ T ⊢ₛ' f) ∧ (¬ T ⊢ₛ' (bd_not f : sentence L))

/-- THE MARQUEE THEOREM: The Continuum Hypothesis is independent of ZFC. -/
theorem independence_of_CH : independent ZFC CH_f :=
  ⟨CH_unprovable, neg_CH_unprovable⟩

#print axioms independence_of_CH
/- Outputs: `[propext, Classical.choice, Quot.sound]` —
   the three foundational kernel axioms of Lean's logic, nothing else. -/
