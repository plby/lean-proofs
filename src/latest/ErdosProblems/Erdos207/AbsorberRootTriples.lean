/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberPadding

/-!
# Root triples and the fixed absorber bank

The flexible vertices of the sphere absorber are the roots.  Although the
two sphere decompositions cover the three root pairs on their inward side,
the root triple itself is not one of the bank triples.  This elementary fact
is the first input to the initial restricted-extension estimates.
-/

namespace Erdos207

open Finset

/-- The three distinguished roots do not themselves form a member of the
single-sphere bank. -/
theorem sphereRootTriple_not_mem_sphereBank
    {q : ℕ} (hq : 2 ≤ q) :
    sphereRootTriple hq ∉ sphereBank hq := by
  let z : Fin (2 * q) := ⟨0, by omega⟩
  let o : Fin (2 * q) := ⟨1, by omega⟩
  intro hmem
  obtain ⟨t, _ht, ht⟩ := Finset.mem_image.mp hmem
  have hpole : t.1.2 = true := by
    have h : SphereVertex.pole true ∈ (sphereTriangle hq t).1 := by
      rw [ht]
      simp [sphereRootTriple]
    simpa using (sphere_pole_mem hq t true).mp h
  have hzero : z = t.1.1 ∨
      z = finCycleSucc (by omega) t.1.1 := by
    have h : SphereVertex.cycle z ∈
        (sphereTriangle hq t).1 := by
      rw [ht]
      simp [sphereRootTriple, z, o]
    simpa using (sphere_cycle_mem hq t z).mp h
  have hone : o = t.1.1 ∨
      o = finCycleSucc (by omega) t.1.1 := by
    have h : SphereVertex.cycle o ∈
        (sphereTriangle hq t).1 := by
      rw [ht]
      simp [sphereRootTriple, z, o]
    simpa using (sphere_cycle_mem hq t o).mp h
  rcases hzero with hzero | hzero <;>
    rcases hone with hone | hone
  · have hval := congrArg Fin.val (hzero.trans hone.symm)
    simp [z, o] at hval
  · have htzero : t.1.1.val = 0 := by
      simpa [z] using congrArg Fin.val hzero.symm
    exact Bool.false_ne_true ((t.2 htzero).symm.trans hpole)
  · have htone : t.1.1.val = 1 := by
      simpa [o] using congrArg Fin.val hone.symm
    have hsuccZero : (finCycleSucc (by omega) t.1.1).val = 0 := by
      simpa [z] using congrArg Fin.val hzero.symm
    rw [finCycleSucc_val] at hsuccZero
    have htlt : t.1.1.val + 1 < 2 * q := by omega
    rw [Nat.mod_eq_of_lt htlt] at hsuccZero
    omega
  · have hval := congrArg Fin.val (hzero.trans hone.symm)
    simp [z, o] at hval

/-- Attaching the distinguished sphere root triple to `T` gives precisely
the image of `T` in the root copy of the expansion. -/
theorem attachSphereTriple_sphereRootTriple
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) :
    attachSphereTriple hq T (sphereRootTriple hq) =
      mapTriple (sphereExpansionRootEmbedding V q) T := by
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hycases : y = sphereRootVertex hq 0 ∨
        y = sphereRootVertex hq 1 ∨ y = sphereRootVertex hq 2 := by
      cases y with
      | pole b => cases b <;> simp [sphereRootTriple, sphereRootVertex] at hy ⊢
      | cycle j =>
          simp only [sphereRootTriple, mem_insert, mem_singleton,
            SphereVertex.cycle.injEq, SphereVertex.cycle.injEq] at hy
          rcases hy with h | h | h <;> simp [h, sphereRootVertex]
    rcases hycases with rfl | rfl | rfl
    · apply Finset.mem_map.mpr
      exact ⟨tripleVertex T 0, tripleVertex_mem T 0, by
        change SphereExpansionVertex.root (tripleVertex T 0) = _
        rfl⟩
    · apply Finset.mem_map.mpr
      exact ⟨tripleVertex T 1, tripleVertex_mem T 1, by
        change SphereExpansionVertex.root (tripleVertex T 1) = _
        rfl⟩
    · apply Finset.mem_map.mpr
      exact ⟨tripleVertex T 2, tripleVertex_mem T 2, by
        change SphereExpansionVertex.root (tripleVertex T 2) = _
        rfl⟩
  · intro hx
    obtain ⟨v, hvT, rfl⟩ := Finset.mem_map.mp hx
    let i : Fin 3 := (T.1.orderIsoOfFin T.2).symm ⟨v, hvT⟩
    have hvi : tripleVertex T i = v := by
      change ((T.1.orderIsoOfFin T.2 i).1 : V) = v
      simp [i]
    apply Finset.mem_map.mpr
    refine ⟨sphereRootVertex hq i, ?_, ?_⟩
    · rcases fin_three_cases i with hi | hi | hi <;> rw [hi] <;>
        simp [sphereRootTriple, sphereRootVertex]
    · change attachSphereVertex T (sphereRootVertex hq i) =
        SphereExpansionVertex.root v
      rw [attachSphereVertex_root, hvi]

/-- Consequently, an attached root triple is absent from the attached bank
of its sphere. -/
theorem attachSphereRootTriple_not_mem_bank
    {V : Type*} [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) :
    mapTriple (sphereExpansionRootEmbedding V q) T ∉
      attachSphereFamily hq T (sphereBank hq) := by
  rw [← attachSphereTriple_sphereRootTriple hq T]
  exact fun h ↦ sphereRootTriple_not_mem_sphereBank hq
    ((mem_mapTripleSystem_iff (attachSphereEmbedding hq T)
      (sphereBank hq) (sphereRootTriple hq)).mp h)

/-- No triple contained entirely in the root copy belongs to the universal
sphere bank.  Every bank triangle has an interior vertex in its attached
sphere, whereas a mapped root triple has only root vertices. -/
theorem mapTriple_root_not_mem_sphereTransformBank
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ} (hq : 2 ≤ q)
    (T : TripleOn V) :
    mapTriple (sphereExpansionRootEmbedding V q) T ∉
      sphereTransformBank hq := by
  intro hTbank
  obtain ⟨R, _hRuniv, hTR⟩ := by
    simpa only [sphereTransformBank, mem_biUnion] using hTbank
  obtain ⟨S, hSbank, hSimage⟩ := Finset.mem_map.mp hTR
  obtain ⟨t, _htuniv, rfl⟩ := Finset.mem_image.mp hSbank
  obtain ⟨x, hx⟩ := exists_interior_mem_sphereTriangle hq t
  have hxattached :
      SphereExpansionVertex.interior R x ∈
        (attachSphereTriple hq R (sphereTriangle hq t)).1 := by
    rw [← attachSphereVertex_interior R x]
    exact Finset.mem_map.mpr ⟨x.1, hx, rfl⟩
  have hxroot : SphereExpansionVertex.interior R x ∈
      (mapTriple (sphereExpansionRootEmbedding V q) T).1 := by
    rw [← hSimage]
    exact hxattached
  obtain ⟨v, _hvT, hv⟩ := Finset.mem_map.mp hxroot
  simp [sphereExpansionRootEmbedding] at hv

end Erdos207
