/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Independence of `Erdos501` from `ZFC`, in Mathlib's model theory

The Flypitch development proves `¬ (ZFC ⊢ₛ' Erdos501_f)` and `¬ (ZFC ⊢ₛ' ∼Erdos501_f)` for
Flypitch's proof system.  By Flypitch's completeness theorem (`Fol.completeness`) each gives a
two-valued model of Flypitch's `ZFC` in which `Erdos501_f` fails, resp. holds.  Translated to an
`L`-structure (`toM`), such a model is a model of the Mathlib-side theory `ZFC` (`toM_models_ZFC`)
in which `Erdos501` fails, resp. holds (`realize_sentence_tr`, `tr_Erdos501`).  Mathlib's
`Theory.Model.isSatisfiable` (downward Löwenheim–Skolem, to bring the carrier down to `Type 0`)
and `Theory.models_iff_not_satisfiable` then give

* `erdos501_not_provable  : ¬ (ZFC ⊨ᵇ Erdos501)`,
* `erdos501_not_refutable : ¬ (ZFC ⊨ᵇ ∼Erdos501)`.
-/
import ErdosProblems.Erdos501.FOL.Sentence
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Main
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Hechler
import ErdosProblems.Erdos501.Flypitch4.Completeness

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Fol

namespace Erdos501.FOL

/-- Flypitch's completeness theorem, contrapositive form: an unprovable sentence has a nonempty
countermodel. -/
lemma exists_model_of_not_sprovable {φ : sentence L_ZFC} (h : ¬ (_root_.ZFC ⊢ₛ' φ)) :
    ∃ S : Fol.Structure L_ZFC, Nonempty S.carrier ∧ (S ⊨ₜ _root_.ZFC) ∧ ¬ (S ⊨ₘ φ) := by
  rw [Fol.completeness] at h
  by_contra hcon
  apply h
  intro S hne hZ
  by_contra hφ
  exact hcon ⟨S, hne, hZ, hφ⟩

section

variable (S : Fol.Structure L_ZFC)

attribute [local instance] toM

/-- A nonempty Flypitch model of `ZFC` in which the `L`-sentence `φ` fails witnesses
`¬ (ZFC ⊨ᵇ φ)`. -/
theorem not_models_of_countermodel [Nonempty S.carrier] (hZ : S ⊨ₜ _root_.ZFC) {φ : L.Sentence}
    (hφ : ¬ (S.carrier ⊨ φ)) : ¬ (ZFC ⊨ᵇ φ) := by
  rw [Theory.models_iff_not_satisfiable]
  intro hsat
  apply hsat
  have : S.carrier ⊨ ZFC ∪ {φ.not} :=
    Theory.model_union_iff.mpr ⟨toM_models_ZFC S hZ, Theory.model_singleton_iff.mpr hφ⟩
  exact Theory.Model.isSatisfiable S.carrier

end

/-- **`ZFC` does not prove `Erdos501`.**  Hechler's counterexample holds in the collapse model
(`Flypitch.Erdos501.Hechler.Erdos501_f_unprovable`). -/
theorem erdos501_not_provable : ¬ (ZFC ⊨ᵇ Erdos501.FOL.Erdos501) := by
  obtain ⟨S, hne, hZ, hφ⟩ :=
    exists_model_of_not_sprovable Flypitch.Erdos501.Hechler.Erdos501_f_unprovable
  have := hne
  refine not_models_of_countermodel S hZ ?_
  rw [realize_sentence_tr, tr_Erdos501]
  exact hφ

/-- **`ZFC` does not refute `Erdos501`.**  `Erdos501` holds after adding `𝔠⁺` random reals
(`Flypitch.Erdos501.neg_Erdos501_f_unprovable`). -/
theorem erdos501_not_refutable : ¬ (ZFC ⊨ᵇ ∼Erdos501.FOL.Erdos501) := by
  obtain ⟨S, hne, hZ, hφ⟩ :=
    exists_model_of_not_sprovable Flypitch.Erdos501.neg_Erdos501_f_unprovable
  have := hne
  refine not_models_of_countermodel S hZ ?_
  rw [Sentence.realize_not, not_not, realize_sentence_tr, tr_Erdos501]
  exact not_not.mp hφ

/-- **Independence of the first question of Erdős #501 from `ZFC`.** -/
theorem erdos501_independent :
    ¬ (ZFC ⊨ᵇ Erdos501.FOL.Erdos501) ∧ ¬ (ZFC ⊨ᵇ ∼Erdos501.FOL.Erdos501) :=
  ⟨erdos501_not_provable, erdos501_not_refutable⟩

end Erdos501.FOL
