/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexMonomial
import ErdosProblems.Erdos207.ErdosTouching
import ErdosProblems.Erdos207.ExactBankExtension

/-! # Geometric meaning of vortex prefix sums -/

namespace Erdos207

open Finset

noncomputable section

/-- Vertices of `S` whose exact vortex level occurs before coordinate `k`. -/
def Vortex.verticesBefore
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (S : Finset V) (k : ℕ) : Finset V :=
  S.filter fun x ↦ (W.vertexLevel x).val < k

/-- Triangles of `C` whose exact vortex level occurs before coordinate `k`. -/
def Vortex.trianglesBefore
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (k : ℕ) :
    TripleSystemOn V :=
  C.filter fun T ↦ (W.level T).val < k

@[simp]
lemma Vortex.mem_verticesBefore_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell k : ℕ}
    (W : Vortex V ell) (S : Finset V) (x : V) :
    x ∈ W.verticesBefore S k ↔ x ∈ S ∧ (W.vertexLevel x).val < k := by
  simp [Vortex.verticesBefore]

@[simp]
lemma Vortex.mem_trianglesBefore_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell k : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (T : TripleOn V) :
    T ∈ W.trianglesBefore C k ↔ T ∈ C ∧ (W.level T).val < k := by
  simp [Vortex.trianglesBefore]

/-- Prefix sums of a vertex profile count precisely the vertices before that
level. -/
lemma Vortex.finPrefixSum_vertexProfile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (S : Finset V) (k : ℕ) :
    finPrefixSum (W.vertexProfile S) k = (W.verticesBefore S k).card := by
  classical
  rw [← W.sum_vertexProfile (W.verticesBefore S k)]
  unfold finPrefixSum
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hik : i.val < k
  · rw [if_pos hik]
    apply congrArg Finset.card
    ext x
    simp only [mem_inter, Vortex.mem_verticesAtLevel_iff,
      Vortex.mem_verticesBefore_iff]
    constructor
    · rintro ⟨hxS, hxi⟩
      exact ⟨⟨hxS, by simpa only [hxi] using hik⟩, hxi⟩
    · rintro ⟨⟨hxS, _hxk⟩, hxi⟩
      exact ⟨hxS, hxi⟩
  · rw [if_neg hik]
    have hempty : W.verticesBefore S k ∩ W.verticesAtLevel i = ∅ := by
      ext x
      simp only [mem_inter, Vortex.mem_verticesAtLevel_iff,
        Vortex.mem_verticesBefore_iff]
      constructor
      · rintro ⟨⟨_hxS, hxk⟩, hxi⟩
        exact (hik (by simpa only [hxi] using hxk)).elim
      · intro hxempty
        simpa using hxempty
    simp [Vortex.vertexProfile, hempty]

/-- Up to a nonterminal coordinate, prefix sums of the outer triangle profile
count precisely the triangles before that level. -/
lemma Vortex.finPrefixSum_outerProfile
    {V : Type*} [Fintype V] [DecidableEq V] {ell k : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (hk : k ≤ ell) :
    finPrefixSum (W.outerProfile C) k = (W.trianglesBefore C k).card := by
  classical
  have htotal := W.sum_levelCount (W.trianglesBefore C k)
  rw [Fin.sum_univ_castSucc] at htotal
  have hterminal : W.levelCount (W.trianglesBefore C k) (Fin.last ell) = 0 := by
    unfold Vortex.levelCount
    have hempty : W.trianglesBefore C k ∩
        W.trianglesAtLevel (Fin.last ell) = ∅ := by
      ext T
      simp only [mem_inter, Vortex.mem_trianglesBefore_iff,
        Vortex.mem_trianglesAtLevel_iff]
      constructor
      · rintro ⟨⟨_hTC, hTk⟩, hTlast⟩
        simp only [hTlast, Fin.val_last] at hTk
        omega
      · intro hTempty
        simpa using hTempty
    rw [hempty, card_empty]
  have houterTotal :
      ∑ i : Fin ell,
        W.levelCount (W.trianglesBefore C k) i.castSucc =
          (W.trianglesBefore C k).card := by
    omega
  rw [← houterTotal]
  unfold finPrefixSum Vortex.outerProfile
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hik : i.val < k
  · rw [if_pos hik]
    unfold Vortex.levelCount
    apply congrArg Finset.card
    ext T
    simp only [mem_inter, Vortex.mem_trianglesAtLevel_iff,
      Vortex.mem_trianglesBefore_iff]
    constructor
    · rintro ⟨hTC, hTi⟩
      exact ⟨⟨hTC, by simpa only [hTi, Fin.val_castSucc] using hik⟩, hTi⟩
    · rintro ⟨⟨hTC, _hTk⟩, hTi⟩
      exact ⟨hTC, hTi⟩
  · rw [if_neg hik]
    unfold Vortex.levelCount
    have hempty : W.trianglesBefore C k ∩
        W.trianglesAtLevel i.castSucc = ∅ := by
      ext T
      simp only [mem_inter, Vortex.mem_trianglesBefore_iff,
        Vortex.mem_trianglesAtLevel_iff]
      constructor
      · rintro ⟨⟨_hTC, hTk⟩, hTi⟩
        exact (hik (by simpa only [hTi, Fin.val_castSucc] using hTk)).elim
      · intro hTempty
        simpa using hTempty
    rw [hempty, card_empty]

/-- A triangle containing a vertex at an early exact level is itself at an
early level. -/
lemma Vortex.level_lt_of_mem_of_vertexLevel_lt
    {V : Type*} [Fintype V] [DecidableEq V] {ell k : ℕ}
    (W : Vortex V ell) {T : TripleOn V} {x : V}
    (hxT : x ∈ T.1) (hx : (W.vertexLevel x).val < k) :
    (W.level T).val < k := by
  have hxU : x ∈ W.U (W.level T) := W.subset_at_level T hxT
  have hle : W.level T ≤ W.vertexLevel x :=
    (W.mem_U_iff_le_vertexLevel x (W.level T)).mp hxU
  exact lt_of_le_of_lt hle hx

/-- Early triangles touching vertices outside a fixed root stay in the early
part of the complementary triangle family. -/
lemma Vortex.trianglesTouching_verticesBefore_subset
    {V : Type*} [Fintype V] [DecidableEq V] {ell k : ℕ}
    (W : Vortex V ell) (E Q : TripleSystemOn V) :
    trianglesTouching E
        (W.verticesBefore (verticesOn E \ verticesOn Q) k) ⊆
      W.trianglesBefore (E \ Q) k := by
  intro T hT
  obtain ⟨hTE, x, hxextra, hxT⟩ := mem_trianglesTouching_iff.mp hT
  have hx := (W.mem_verticesBefore_iff _ x).mp hxextra
  have hxnotQ := (mem_sdiff.mp hx.1).2
  have hTnotQ : T ∉ Q := by
    intro hTQ
    exact hxnotQ (mem_biUnion.mpr ⟨T, hTQ, hxT⟩)
  exact W.mem_trianglesBefore_iff (E \ Q) T |>.mpr
    ⟨mem_sdiff.mpr ⟨hTE, hTnotQ⟩,
      W.level_lt_of_mem_of_vertexLevel_lt hxT hx.2⟩

end

end Erdos207
