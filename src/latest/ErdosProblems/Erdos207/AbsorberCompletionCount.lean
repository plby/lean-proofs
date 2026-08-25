/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberLocalization
import Mathlib.Data.Finset.Powerset

/-!
# Counting absorber completions

Once A2 confines the bank portion of a short configuration to a local family
of at most `M` triangles, there are at most `2^M` possible bank portions.
This is the finite counting core behind the well-spreadness estimates.
-/

namespace Erdos207

open Finset

/-- Minimal short configurations with a prescribed outside part `S`.  The
cutoff starts at five because the two-triangle case is handled directly by
packinghood. -/
noncomputable def erdosBankCompletions
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B S : TripleSystemOn V) :
    Finset (ℕ × TripleSystemOn V) := by
  classical
  exact ((Icc 5 q).product (univ : Finset (TripleSystemOn V))).filter
    fun z ↦ IsErdosConfigOn z.1 z.2 ∧ z.2 \ B = S

@[simp]
lemma mem_erdosBankCompletions_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B S : TripleSystemOn V}
    {r : ℕ} {E : TripleSystemOn V} :
    (r, E) ∈ erdosBankCompletions q B S ↔
      5 ≤ r ∧ r ≤ q ∧ IsErdosConfigOn r E ∧ E \ B = S := by
  classical
  simp [erdosBankCompletions, and_assoc]

lemma erdosBankCompletion_reconstruct
    {V : Type*} [DecidableEq V]
    {B S E : TripleSystemOn V} (hE : E \ B = S) :
    E = S ∪ (E ∩ B) := by
  calc
    E = (E \ B) ∪ (E ∩ B) := (sdiff_union_inter E B).symm
    _ = S ∪ (E ∩ B) := by rw [hE]

/-- A fixed local bank `L` gives at most `q * 2^|L|` completions, including
the choice of the girth parameter `r`. -/
theorem card_erdosBankCompletions_le_of_local
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B S L : TripleSystemOn V}
    (hlocal : ∀ r E, (r, E) ∈ erdosBankCompletions q B S → E ∩ B ⊆ L) :
    (erdosBankCompletions q B S).card ≤ q * 2 ^ L.card := by
  classical
  let f : ℕ × TripleSystemOn V → ℕ × TripleSystemOn V :=
    fun z ↦ (z.1, z.2 ∩ B)
  have hinj : Set.InjOn f (erdosBankCompletions q B S) := by
    intro z hz w hw hzw
    change (z.1, z.2 ∩ B) = (w.1, w.2 ∩ B) at hzw
    have hparts : z.1 = w.1 ∧ z.2 ∩ B = w.2 ∩ B := by
      simpa only [Prod.mk.injEq] using hzw
    have hr := hparts.1
    have hbank := hparts.2
    have hzout := (mem_erdosBankCompletions_iff.mp hz).2.2.2
    have hwout := (mem_erdosBankCompletions_iff.mp hw).2.2.2
    apply Prod.ext hr
    calc
      z.2 = S ∪ (z.2 ∩ B) := erdosBankCompletion_reconstruct hzout
      _ = S ∪ (w.2 ∩ B) := by rw [hbank]
      _ = w.2 := (erdosBankCompletion_reconstruct hwout).symm
  have himage : (erdosBankCompletions q B S).image f ⊆
      (Icc 5 q).product L.powerset := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hw' := mem_erdosBankCompletions_iff.mp hw
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hw'.1, hw'.2.1⟩,
      mem_powerset.mpr (hlocal w.1 w.2 hw)⟩
  calc
    (erdosBankCompletions q B S).card =
        ((erdosBankCompletions q B S).image f).card :=
      (card_image_of_injOn hinj).symm
    _ ≤ ((Icc 5 q).product L.powerset).card := card_le_card himage
    _ = (Icc 5 q).card * 2 ^ L.card := by simp
    _ ≤ q * 2 ^ L.card := by
      apply Nat.mul_le_mul_right
      simp only [Nat.card_Icc]
      omega

/-- Property A2 gives a uniform `q * 2^M` bound on all completions of a fixed
outside part.  Apply A2 with the *entire* outside part as `R`: its nonlocal
alternative would produce a triangle of `E` belonging to neither `R` nor the
bank, contradicting `E \ B = R`. -/
theorem card_erdosBankCompletions_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B S : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hSq : S.card ≤ q) :
    (erdosBankCompletions q B S).card ≤ q * 2 ^ M := by
  obtain ⟨L, hLB, hLM, hL⟩ :=
    hA2 (SimpleGraph.completeGraph V) le_top S hSq
      (consistsOfTriangles_completeGraph S)
  have hlocal : ∀ r E, (r, E) ∈ erdosBankCompletions q B S →
      E ∩ B ⊆ L := by
    intro r E hcompletion
    have hc := mem_erdosBankCompletions_iff.mp hcompletion
    have hSE : S ⊆ E := by
      intro T hTS
      have hTdiff : T ∈ E \ B := by simpa only [hc.2.2.2] using hTS
      exact (mem_sdiff.mp hTdiff).1
    rcases hL r hc.1 hc.2.1 E hc.2.2.1 hSE with hEB | hbad
    · exact hEB
    · obtain ⟨T, hTE, hTfree, v, hvT, hvH, hvX⟩ := hbad
      exfalso
      have hTnotB : T ∉ B := by
        intro hTB
        exact hTfree (Finset.mem_union.mpr (Or.inr hTB))
      have hTdiff : T ∈ E \ B := mem_sdiff.mpr ⟨hTE, hTnotB⟩
      have hTS : T ∈ S := by simpa only [hc.2.2.2] using hTdiff
      exact hTfree (Finset.mem_union.mpr (Or.inl hTS))
  calc
    (erdosBankCompletions q B S).card ≤ q * 2 ^ L.card :=
      card_erdosBankCompletions_le_of_local hlocal
    _ ≤ q * 2 ^ M := by
      exact Nat.mul_le_mul_left q
        (pow_le_pow_right' (by omega : (1 : ℕ) ≤ 2) hLM)

end Erdos207
