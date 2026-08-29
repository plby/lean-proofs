/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ReducingBoundary

/-!
# Balance of a finitely indexed locally bi-unique edge relation

This module isolates the finite indicator calculation used by marked
residual-route toggles.  It is independent of the particular route encoding:
if a finite injective edge enumeration has no repeated source or target, its
edge balance is the sum of the endpoint contributions.
-/

namespace Erdos599
namespace Alternating

open Set

universe u v

variable {V : Type u}

private theorem propInt_exists_eq_sum_of_unique_finite
    {I : Type v} [Fintype I] (P : I → Prop)
    (huniq : ∀ {i j}, P i → P j → i = j) :
    propInt (∃ i, P i) = ∑ i, propInt (P i) := by
  classical
  by_cases h : ∃ i, P i
  · rcases h with ⟨i, hi⟩
    have hex : ∃ j, P j := ⟨i, hi⟩
    rw [Finset.sum_eq_single i]
    · simp [propInt, hi, hex]
    · intro j _ hji
      have hnj : ¬ P j := fun hj ↦ hji (huniq hj hi)
      simp [propInt, hnj]
    · simp
  · have hall : ∀ i, ¬ P i := fun i hi ↦ h ⟨i, hi⟩
    simp [propInt, h, hall]

/-- The balance of a finite injective, locally bi-unique edge enumeration is
the sum of plus one at every enumerated source and minus one at every
enumerated target. -/
theorem edgeBalance_range_eq_sum
    {I : Type v} [Fintype I] (e : I → V × V)
    (hinjective : Function.Injective e)
    (hunique : Relator.BiUnique
      (fun x y ↦ (x, y) ∈ Set.range e))
    (x : V) :
    edgeBalance (Set.range e) x =
      ∑ i, (propInt (x = (e i).1) - propInt (x = (e i).2)) := by
  classical
  have hout : HasOutgoing (Set.range e) x ↔
      ∃ i, x = (e i).1 := by
    constructor
    · rintro ⟨y, hy⟩
      rcases hy with ⟨i, hi⟩
      exact ⟨i, (congrArg Prod.fst hi).symm⟩
    · rintro ⟨i, hxi⟩
      refine ⟨(e i).2, ?_⟩
      rw [hxi]
      exact ⟨i, (Prod.eta (e i)).symm⟩
  have hin : HasIncoming (Set.range e) x ↔
      ∃ i, x = (e i).2 := by
    constructor
    · rintro ⟨y, hy⟩
      rcases hy with ⟨i, hi⟩
      exact ⟨i, (congrArg Prod.snd hi).symm⟩
    · rintro ⟨i, hxi⟩
      refine ⟨(e i).1, ?_⟩
      rw [hxi]
      exact ⟨i, (Prod.eta (e i)).symm⟩
  have houtuniq : ∀ {i j}, x = (e i).1 → x = (e j).1 → i = j := by
    intro i j hi hj
    apply hinjective
    apply Prod.ext
    · exact hi.symm.trans hj
    · apply hunique.2
      · exact ⟨i, rfl⟩
      · simpa [hi.symm.trans hj] using
          (show e j ∈ Set.range e from ⟨j, rfl⟩)
  have hinuniq : ∀ {i j}, x = (e i).2 → x = (e j).2 → i = j := by
    intro i j hi hj
    apply hinjective
    apply Prod.ext
    · apply hunique.1
      · exact ⟨i, rfl⟩
      · simpa [hi.symm.trans hj] using
          (show e j ∈ Set.range e from ⟨j, rfl⟩)
    · exact hi.symm.trans hj
  rw [edgeBalance, hout, hin,
    propInt_exists_eq_sum_of_unique_finite _ houtuniq,
    propInt_exists_eq_sum_of_unique_finite _ hinuniq,
    ← Finset.sum_sub_distrib]

/-- Endpoint indicators telescope along any finite nonempty vertex
sequence.  This is the list-free arithmetic core of a residual-route balance
calculation. -/
theorem sum_adjacent_propInt_eq_boundary
    (n : ℕ) (f : Fin (n + 1) → V) (x : V) :
    (∑ i : Fin n,
      (propInt (x = f i.castSucc) - propInt (x = f i.succ))) =
      propInt (x = f 0) - propInt (x = f (Fin.last n)) := by
  rw [Finset.sum_sub_distrib]
  let F : Fin (n + 1) → Int := fun i ↦ propInt (x = f i)
  have htotal :
      (∑ i : Fin n, F i.castSucc) + F (Fin.last n) =
        F 0 + ∑ i : Fin n, F i.succ := by
    calc
      (∑ i : Fin n, F i.castSucc) + F (Fin.last n) =
          ∑ i : Fin (n + 1), F i :=
        (Fin.sum_univ_castSucc F).symm
      _ = F 0 + ∑ i : Fin n, F i.succ :=
        Fin.sum_univ_succ F
  change (∑ i : Fin n, F i.castSucc) -
      ∑ i : Fin n, F i.succ = F 0 - F (Fin.last n)
  omega

/-- The total balance of a finite biunique relation is zero on any finite
vertex set containing both endpoints of all its edges. -/
theorem sum_edgeBalance_eq_zero {E : Set (V × V)} (hE : E.Finite)
    (hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (C : Finset V) (hC : ∀ e ∈ E, e.1 ∈ C ∧ e.2 ∈ C) :
    ∑ x ∈ C, edgeBalance E x = 0 := by
  classical
  let : Fintype E := hE.fintype
  have hrange : Set.range (fun e : E ↦ e.1) = E := by
    ext e
    simp
  have hpoint : ∀ x, edgeBalance E x =
      ∑ e : E, (propInt (x = e.1.1) - propInt (x = e.1.2)) := by
    intro x
    have h := edgeBalance_range_eq_sum (fun e : E ↦ e.1)
      Subtype.val_injective (by simpa only [hrange] using hbi) x
    simpa only [hrange] using h
  calc
    ∑ x ∈ C, edgeBalance E x =
        ∑ x ∈ C, ∑ e : E, (propInt (x = e.1.1) - propInt (x = e.1.2)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hpoint x
    _ = ∑ e : E, ∑ x ∈ C, (propInt (x = e.1.1) - propInt (x = e.1.2)) :=
      Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [Finset.sum_sub_distrib]
      simp [propInt, (hC e.1 e.2).1, (hC e.1 e.2).2]

#print axioms sum_edgeBalance_eq_zero

end Alternating
end Erdos599
