/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Basic

/-!
# Insensitive subsets of a finite word cube

This file formalizes the elementary ``insensitive-set'' constructions used in
the density-increment proof of density Hales--Jewett.  The distinguished symbol
in `Fin (k + 1)` is `Fin.last k`.  Replacing every occurrence of that symbol by
`i.castSucc` gives a canonical representative for the equivalence relation
which permits independent changes between these two symbols.
-/

namespace Erdos171

open Set

section Replacement

variable {k n : ℕ}

/-- Replace the distinguished last letter of `Fin (k + 1)` by `i`. -/
def replaceLastLetter (i : Fin k) (a : Fin (k + 1)) : Fin (k + 1) :=
  if a = Fin.last k then i.castSucc else a

@[simp] theorem replaceLastLetter_last (i : Fin k) :
    replaceLastLetter i (Fin.last k) = i.castSucc := by
  simp [replaceLastLetter]

@[simp] theorem replaceLastLetter_castSucc (i a : Fin k) :
    replaceLastLetter i a.castSucc = a.castSucc := by
  simp [replaceLastLetter, Fin.castSucc_ne_last]

theorem replaceLastLetter_ne_last (i : Fin k) (a : Fin (k + 1)) :
    replaceLastLetter i a ≠ Fin.last k := by
  by_cases h : a = Fin.last k
  · simp [h]
  · simpa [replaceLastLetter, h] using h

@[simp] theorem replaceLastLetter_idem (i : Fin k) (a : Fin (k + 1)) :
    replaceLastLetter i (replaceLastLetter i a) = replaceLastLetter i a := by
  change (if replaceLastLetter i a = Fin.last k then i.castSucc else replaceLastLetter i a) = _
  rw [if_neg (replaceLastLetter_ne_last i a)]

/-- Replace every occurrence of the distinguished last letter in a word by `i`. -/
def replaceLast (i : Fin k) (x : Word (k + 1) n) : Word (k + 1) n :=
  fun r ↦ replaceLastLetter i (x r)

@[simp] theorem replaceLast_apply (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    replaceLast i x r = replaceLastLetter i (x r) := rfl

@[simp] theorem replaceLast_idem (i : Fin k) (x : Word (k + 1) n) :
    replaceLast i (replaceLast i x) = replaceLast i x := by
  funext r
  exact replaceLastLetter_idem i (x r)

theorem replaceLast_ne_last (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    replaceLast i x r ≠ Fin.last k :=
  replaceLastLetter_ne_last i (x r)

/-- The word in the smaller alphabet obtained by treating every last letter as `i`. -/
def endpoint (i : Fin k) (x : Word (k + 1) n) : Word k n :=
  fun r ↦ (replaceLast i x r).castPred (replaceLast_ne_last i x r)

@[simp] theorem endpoint_last (i : Fin k) (r : Fin n) :
    endpoint i (fun _ : Fin n ↦ Fin.last k) r = i := by
  apply Fin.castSucc_injective
  simp [endpoint]

@[simp] theorem endpoint_castSucc (i : Fin k) (x : Word k n) :
    endpoint i (fun r ↦ (x r).castSucc) = x := by
  funext r
  apply Fin.castSucc_injective
  simp [endpoint]

@[simp] theorem castSucc_endpoint (i : Fin k) (x : Word (k + 1) n) (r : Fin n) :
    (endpoint i x r).castSucc = replaceLast i x r := by
  simp [endpoint]

theorem endpoint_eq_iff_replaceLast_eq (i : Fin k) (x y : Word (k + 1) n) :
    endpoint i x = endpoint i y ↔ replaceLast i x = replaceLast i y := by
  constructor
  · intro h
    funext r
    rw [← castSucc_endpoint i x r, ← castSucc_endpoint i y r, h]
  · intro h
    funext r
    apply Fin.castSucc_injective
    simpa only [castSucc_endpoint] using congrFun h r

/-- Two words are `(i,last)`-equivalent if changing `i` and the last letter independently
at any coordinates cannot distinguish them. -/
def LastEquivalent (i : Fin k) (x y : Word (k + 1) n) : Prop :=
  replaceLast i x = replaceLast i y

@[refl] theorem LastEquivalent.refl (i : Fin k) (x : Word (k + 1) n) :
    LastEquivalent i x x := rfl

@[symm] theorem LastEquivalent.symm (i : Fin k) {x y : Word (k + 1) n}
    (h : LastEquivalent i x y) : LastEquivalent i y x := Eq.symm h

@[trans] theorem LastEquivalent.trans (i : Fin k) {x y z : Word (k + 1) n}
    (hxy : LastEquivalent i x y) (hyz : LastEquivalent i y z) :
    LastEquivalent i x z := Eq.trans hxy hyz

theorem lastEquivalent_equivalence (i : Fin k) :
    Equivalence (LastEquivalent (n := n) i) :=
  ⟨LastEquivalent.refl i, LastEquivalent.symm i, LastEquivalent.trans i⟩

theorem lastEquivalent_iff_endpoint_eq (i : Fin k) (x y : Word (k + 1) n) :
    LastEquivalent i x y ↔ endpoint i x = endpoint i y := by
  rw [endpoint_eq_iff_replaceLast_eq]
  rfl

theorem lastEquivalent_replaceLast_left (i : Fin k) (x : Word (k + 1) n) :
    LastEquivalent i (replaceLast i x) x := by
  exact replaceLast_idem i x

theorem lastEquivalent_iff_coordinatewise (i : Fin k) (x y : Word (k + 1) n) :
    LastEquivalent i x y ↔
      ∀ r, x r = y r ∨
        ((x r = i.castSucc ∨ x r = Fin.last k) ∧
          (y r = i.castSucc ∨ y r = Fin.last k)) := by
  simp only [LastEquivalent, funext_iff, replaceLast_apply]
  apply forall_congr'
  intro r
  grind [replaceLastLetter]

end Replacement

section Insensitive

variable {k n : ℕ}

/-- A set is `(i,last)`-insensitive when it is constant on `LastEquivalent` classes. -/
def IsLastInsensitive (i : Fin k) (C : Set (Word (k + 1) n)) : Prop :=
  ∀ x y, LastEquivalent i x y → (x ∈ C ↔ y ∈ C)

theorem isLastInsensitive_iff_mem_replaceLast (i : Fin k)
    (C : Set (Word (k + 1) n)) :
    IsLastInsensitive i C ↔ ∀ x, x ∈ C ↔ replaceLast i x ∈ C := by
  constructor
  · intro h x
    exact (h (replaceLast i x) x (lastEquivalent_replaceLast_left i x)).symm
  · intro h x y hxy
    rw [h x, h y, hxy]

theorem isLastInsensitive_iff_saturated (i : Fin k)
    (C : Set (Word (k + 1) n)) :
    IsLastInsensitive i C ↔ replaceLast i ⁻¹' (replaceLast i '' C) = C := by
  rw [isLastInsensitive_iff_mem_replaceLast]
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [h x]
      rw [← hyx]
      simpa only [replaceLast_idem] using (h y).mp hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · intro h x
    constructor
    · intro hx
      have hx' : replaceLast i x ∈ replaceLast i ⁻¹' (replaceLast i '' C) :=
        ⟨x, hx, (replaceLast_idem i x).symm⟩
      simpa only [h] using hx'
    · intro hx
      rw [← h]
      exact ⟨replaceLast i x, hx, replaceLast_idem i x⟩

theorem isLastInsensitive_iff_preimage (i : Fin k)
    (C : Set (Word (k + 1) n)) :
    IsLastInsensitive i C ↔ ∃ B : Set (Word k n), C = endpoint i ⁻¹' B := by
  constructor
  · intro h
    refine ⟨endpoint i '' C, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact (h x y ((lastEquivalent_iff_endpoint_eq i x y).2 hyx.symm)).mpr hy
  · rintro ⟨B, rfl⟩ x y hxy
    simpa only [Set.mem_preimage, (lastEquivalent_iff_endpoint_eq i x y).mp hxy]

theorem IsLastInsensitive.compl {i : Fin k} {C : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) : IsLastInsensitive i Cᶜ := by
  intro x y hxy
  simpa only [Set.mem_compl_iff] using not_congr (hC x y hxy)

theorem IsLastInsensitive.inter {i : Fin k} {C D : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) (hD : IsLastInsensitive i D) :
    IsLastInsensitive i (C ∩ D) := by
  intro x y hxy
  simpa only [Set.mem_inter_iff] using and_congr (hC x y hxy) (hD x y hxy)

theorem IsLastInsensitive.union {i : Fin k} {C D : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) (hD : IsLastInsensitive i D) :
    IsLastInsensitive i (C ∪ D) := by
  intro x y hxy
  simpa only [Set.mem_union] using or_congr (hC x y hxy) (hD x y hxy)

theorem IsLastInsensitive.diff {i : Fin k} {C D : Set (Word (k + 1) n)}
    (hC : IsLastInsensitive i C) (hD : IsLastInsensitive i D) :
    IsLastInsensitive i (C \ D) := by
  intro x y hxy
  simpa only [Set.mem_sdiff] using and_congr (hC x y hxy) (not_congr (hD x y hxy))

theorem IsLastInsensitive.iInter {i : Fin k} {J : Type*}
    {C : J → Set (Word (k + 1) n)} (hC : ∀ j, IsLastInsensitive i (C j)) :
    IsLastInsensitive i (⋂ j, C j) := by
  intro x y hxy
  simp only [Set.mem_iInter]
  exact forall_congr' fun j ↦ hC j x y hxy

end Insensitive

section EndpointConstruction

variable {k n : ℕ}

/-- The `(i,last)`-insensitive cylinder generated by a set in the restricted cube `[k]^n`. -/
def endpointCylinder (i : Fin k) (A : Set (Word k n)) : Set (Word (k + 1) n) :=
  endpoint i ⁻¹' A

@[simp] theorem mem_endpointCylinder (i : Fin k) (A : Set (Word k n))
    (x : Word (k + 1) n) : x ∈ endpointCylinder i A ↔ endpoint i x ∈ A :=
  Iff.rfl

theorem endpointCylinder_isLastInsensitive (i : Fin k) (A : Set (Word k n)) :
    IsLastInsensitive i (endpointCylinder i A) := by
  intro x y hxy
  simpa only [mem_endpointCylinder, (lastEquivalent_iff_endpoint_eq i x y).mp hxy]

@[simp] theorem mem_iInter_endpointCylinder (A : Set (Word k n))
    (x : Word (k + 1) n) :
    x ∈ ⋂ i : Fin k, endpointCylinder i A ↔ ∀ i : Fin k, endpoint i x ∈ A := by
  simp

/-- Taking the `i`-endpoint of the wildcard word attached to a line recovers
the `i`-point of that line. -/
@[simp] theorem endpoint_templateEndpoint (i : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateEndpoint l) = l i := by
  funext r
  cases hr : l.idxFun r with
  | none =>
      simp [endpoint, replaceLast, replaceLastLetter, Combinatorics.Line.coe_apply, hr]
  | some a =>
      simp [endpoint, replaceLast, replaceLastLetter, Combinatorics.Line.coe_apply, hr]

@[simp] theorem endpoint_templateExtension_last (i : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateExtension l (Fin.last k)) = l i := by
  simp

@[simp] theorem endpoint_templateExtension_castSucc (i a : Fin k)
    (l : Combinatorics.Line (Fin k) (Fin n)) :
    endpoint i (templateExtension l a.castSucc) = l a := by
  rw [templateExtension_castSucc]
  change endpoint i (fun r ↦ (l a r).castSucc) = l a
  exact endpoint_castSucc i (l a)

/-- The wildcard endpoint of a line belongs to all of the insensitive cylinders
generated by `A` exactly when every point of the original line belongs to `A`. -/
@[simp] theorem templateEndpoint_mem_iInter_endpointCylinder_iff
    (A : Set (Word k n)) (l : Combinatorics.Line (Fin k) (Fin n)) :
    templateEndpoint l ∈ ⋂ i : Fin k, endpointCylinder i A ↔
      Set.range l ⊆ A := by
  rw [mem_iInter_endpointCylinder]
  simp only [endpoint_templateEndpoint]
  constructor
  · intro h _ hx
    obtain ⟨i, rfl⟩ := hx
    exact h i
  · intro h i
    exact h ⟨i, rfl⟩

/-- A word containing the last letter encodes a proper line in the restricted cube: last-letter
coordinates are wildcard coordinates, and every other coordinate is held constant. -/
def endpointLine (x : Word (k + 1) n)
    (hx : ∃ r, x r = Fin.last k) : Combinatorics.Line (Fin k) (Fin n) where
  idxFun r := if h : x r = Fin.last k then none else some ((x r).castPred h)
  proper := by
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, by simp [hr]⟩

@[simp] theorem endpointLine_apply (x : Word (k + 1) n)
    (hx : ∃ r, x r = Fin.last k) (i : Fin k) :
    endpointLine x hx i = endpoint i x := by
  funext r
  by_cases h : x r = Fin.last k
  · simp [endpointLine, Combinatorics.Line.coe_apply, endpoint, replaceLast,
      replaceLastLetter, h]
  · simp [endpointLine, Combinatorics.Line.coe_apply, endpoint, replaceLast,
      replaceLastLetter, h]

theorem iInter_endpointCylinder_iff_line (A : Set (Word k n))
    (x : Word (k + 1) n) (hx : ∃ r, x r = Fin.last k) :
    x ∈ ⋂ i : Fin k, endpointCylinder i A ↔
      Set.range (endpointLine x hx) ⊆ A := by
  rw [mem_iInter_endpointCylinder]
  constructor
  · intro h _ hy
    obtain ⟨i, rfl⟩ := hy
    simpa only [endpointLine_apply] using h i
  · intro h i
    exact h ⟨i, by simp⟩

theorem iInter_endpointCylinder_subset_lineEndpoints (A : Set (Word k n)) :
    (⋂ i : Fin k, endpointCylinder i A) ∩
        {x : Word (k + 1) n | ∃ r, x r = Fin.last k} =
      {x | ∃ hx : ∃ r, x r = Fin.last k, Set.range (endpointLine x hx) ⊆ A} := by
  ext x
  constructor
  · rintro ⟨hxC, hxlast⟩
    exact ⟨hxlast, (iInter_endpointCylinder_iff_line A x hxlast).mp hxC⟩
  · rintro ⟨hxlast, hxline⟩
    exact ⟨(iInter_endpointCylinder_iff_line A x hxlast).mpr hxline, hxlast⟩

end EndpointConstruction

end Erdos171
