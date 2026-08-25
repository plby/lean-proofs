/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberGreedy

/-!
# Consequences of absorber localization for induced configurations

Property (A2) becomes useful once outside triangles are forbidden from
meeting a non-flexible vertex incident with the absorber graph.  Then the
second alternative in A2 is impossible, so the absorber portion of every
short configuration containing a prescribed root family lies in a bounded
local bank.
-/

namespace Erdos207

open Finset

/-- Every vertex of an outside triangle that is incident with the absorber
graph belongs to the flexible set. -/
def AvoidsAbsorberInterior {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (P : TripleSystemOn V) : Prop :=
  ∀ T ∈ P, ∀ v ∈ T.1, (∃ w, H.Adj v w) → v ∈ X

lemma AvoidsAbsorberInterior.mono
    {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {P P' : TripleSystemOn V}
    (h : AvoidsAbsorberInterior H X P) (hsub : P' ⊆ P) :
    AvoidsAbsorberInterior H X P' := by
  intro T hTP' v hvT hvH
  exact h T (hsub hTP') v hvT hvH

lemma consistsOfTriangles_completeGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : TripleSystemOn V) :
    ConsistsOfTriangles (SimpleGraph.completeGraph V) R := by
  intro T hTR u huT v hvT huv
  simpa using huv

/-- Bounded localization of the bank part of a minimal configuration. -/
theorem erdosConfig_bank_part_local
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P R E : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hPinterior : AvoidsAbsorberInterior H X P)
    (hRq : R.card ≤ q)
    {r : ℕ} (hr5 : 5 ≤ r) (hrq : r ≤ q)
    (hE : IsErdosConfigOn r E) (hRE : R ⊆ E)
    (houtside : E \ B ⊆ P) :
    ∃ L : TripleSystemOn V,
      L ⊆ B ∧ L.card ≤ M ∧ E ∩ B ⊆ L := by
  obtain ⟨L, hLB, hLM, hlocal⟩ :=
    hA2 (SimpleGraph.completeGraph V) le_top R hRq
      (consistsOfTriangles_completeGraph R)
  refine ⟨L, hLB, hLM, ?_⟩
  rcases hlocal r hr5 hrq E hE hRE with hEB | hnonlocal
  · exact hEB
  · obtain ⟨T, hTE, hTfree, v, hvT, hvH, hvX⟩ := hnonlocal
    exfalso
    apply hvX
    apply hPinterior T
    · apply houtside
      refine mem_sdiff.mpr ⟨hTE, ?_⟩
      intro hTB
      exact hTfree (Finset.mem_union.mpr (Or.inr hTB))
    · exact hvT
    · exact hvH

/-- Applied to an induced forbidden outside part, A2 confines all bank
triangles of its witnessing Erdős configuration to a bounded local family. -/
theorem inducedErdosForbidden_bank_part_local
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B P R S : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hPinterior : AvoidsAbsorberInterior H X P)
    (hSforbidden : S ∈ absorberErdosForbiddenConfigurationsOn q B)
    (hSP : S ⊆ P) (hRS : R ⊆ S) (hRq : R.card ≤ q)
    (hfive : ∀ r E, IsErdosConfigOn r E → E \ B = S → 5 ≤ r) :
    ∃ r E L, 5 ≤ r ∧ r ≤ q ∧ IsErdosConfigOn r E ∧
      E \ B = S ∧ L ⊆ B ∧ L.card ≤ M ∧ E ∩ B ⊆ L := by
  obtain ⟨_hSnonempty, r, hr4, hrq, E, hE, _hEpacking, hEsdiff⟩ :=
    mem_absorberErdosForbiddenConfigurationsOn_iff.mp hSforbidden
  have hr5 := hfive r E hE hEsdiff
  have hRE : R ⊆ E := by
    intro T hTR
    exact (mem_sdiff.mp (hEsdiff.symm ▸ hRS hTR)).1
  have houtside : E \ B ⊆ P := by
    simpa only [hEsdiff] using hSP
  obtain ⟨L, hLB, hLM, hEBL⟩ :=
    erdosConfig_bank_part_local hA2 hPinterior hRq hr5 hrq hE hRE houtside
  exact ⟨r, E, L, hr5, hrq, hE, hEsdiff, hLB, hLM, hEBL⟩

end Erdos207
