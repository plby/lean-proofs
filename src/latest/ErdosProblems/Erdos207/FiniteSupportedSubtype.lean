/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteLawPushforward
import ErdosProblems.Erdos207.FiniteConditioning

/-! # Reindex a supported finite law on its good-outcome subtype without loss -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

variable {Omega : Type*} [Fintype Omega] {Good : Omega → Prop} [DecidablePred Good]

def supportedSubtype (L : FiniteLaw Omega) (hgood : L.SupportedOn Good) : FiniteLaw {x // Good x} where
  mass x := L.mass x.val
  sum_mass := by
    classical
    rw [← sum_subtype (univ.filter Good) (by simp) L.mass, sum_filter]
    rw [← L.sum_mass]
    apply sum_congr rfl
    intro x _
    by_cases hx : Good x
    · simp [hx]
    · have hzero : L.mass x = 0 := le_antisymm
        (not_lt.mp (fun h ↦ hx (hgood x h))) zero_le
      simp [hx, hzero]

theorem supportedSubtype_probability (L : FiniteLaw Omega) (hgood : L.SupportedOn Good)
    (Q : Omega → Prop) :
    (L.supportedSubtype hgood).probability (fun x ↦ Q x.val) = L.probability Q := by
  classical
  unfold probability
  change (∑ x : {x // Good x}, if Q x.val then L.mass x.val else 0) = _
  rw [← sum_subtype (univ.filter Good) (by simp) (fun x ↦ if Q x then L.mass x else 0), sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hg : Good x
  · simp [hg]
  · have hzero : L.mass x = 0 := by
      apply le_antisymm _ zero_le
      exact not_lt.mp (fun h ↦ hg (hgood x h))
    simp [hg, hzero]

theorem supportedSubtype_map_val [DecidableEq Omega] (L : FiniteLaw Omega)
    (hgood : L.SupportedOn Good) :
    (L.supportedSubtype hgood).map Subtype.val = L := by
  apply ext_probability
  intro Q
  rw [probability_map, supportedSubtype_probability]

theorem SupportedOn.supportedSubtype {L : FiniteLaw Omega} {Q : Omega → Prop}
    (hQ : L.SupportedOn Q) (hgood : L.SupportedOn Good) :
    (L.supportedSubtype hgood).SupportedOn (fun x ↦ Q x.val) :=
  fun x hx ↦ hQ x.val hx

def conditionSubtype (L : FiniteLaw Omega) (Good : Omega → Prop) [DecidablePred Good]
    (hpos : 0 < L.probability Good) : FiniteLaw {x // Good x} :=
  (L.conditionOn Good hpos).supportedSubtype (L.conditionOn_supported Good hpos)

theorem conditionSubtype_probability (L : FiniteLaw Omega) (Good : Omega → Prop)
    [DecidablePred Good] (hpos : 0 < L.probability Good) (Q : Omega → Prop) :
    (L.conditionSubtype Good hpos).probability (fun x ↦ Q x.val) =
      L.probability (fun x ↦ Good x ∧ Q x) / L.probability Good := by
  rw [conditionSubtype, supportedSubtype_probability, conditionOn_probability]

theorem conditionSubtype_map_val [DecidableEq Omega] (L : FiniteLaw Omega) (Good : Omega → Prop)
    [DecidablePred Good] (hpos : 0 < L.probability Good) :
    (L.conditionSubtype Good hpos).map Subtype.val = L.conditionOn Good hpos :=
  supportedSubtype_map_val _ _

end

end Erdos207.FiniteLaw
