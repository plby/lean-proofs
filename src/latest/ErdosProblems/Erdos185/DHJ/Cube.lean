/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Basic
import ErdosProblems.Erdos171.Insensitive
import ErdosProblems.Erdos171.SubspaceOps

/-!
# Finite cubes and pullbacks for Erdős problem 185

This file contains the elementary algebra needed to work inside a
combinatorial subspace without importing the larger Erdős 171 development.
The central operation is `pullbackFinset`: it records, as a finset in the
parameter cube, the points of a finset lying in a given subspace.
-/

namespace Combinatorics

namespace Subspace

variable {α : Type*}

/-- Product of finite-dimensional subspaces, with both disjoint sums reindexed
by the standard equivalence `Fin r ⊕ Fin s ≃ Fin (r+s)`. -/
def finSum {p q m n : ℕ} (U : Subspace (Fin m) α (Fin p))
    (V : Subspace (Fin n) α (Fin q)) :
    Subspace (Fin (m + n)) α (Fin (p + q)) :=
  (U.sum V).reindex finSumFinEquiv (Equiv.refl α) finSumFinEquiv

@[simp] theorem finSum_apply_castAdd {p q m n : ℕ}
    (U : Subspace (Fin m) α (Fin p)) (V : Subspace (Fin n) α (Fin q))
    (x : Fin (m + n) → α) (i : Fin p) :
    U.finSum V x (Fin.castAdd q i) = U (x ∘ Fin.castAdd n) i := by
  simp [finSum, Function.comp_def]

@[simp] theorem finSum_apply_natAdd {p q m n : ℕ}
    (U : Subspace (Fin m) α (Fin p)) (V : Subspace (Fin n) α (Fin q))
    (x : Fin (m + n) → α) (j : Fin q) :
    U.finSum V x (Fin.natAdd p j) = V (x ∘ Fin.natAdd m) j := by
  simp [finSum, Function.comp_def]

end Subspace

end Combinatorics

namespace Erdos185.DHJ

open Set

/-- Words use the same concrete representation as the Erdős 171 library. -/
abbrev Word := Erdos171.Word

section Lines

variable {α ι η : Type*}

/-- A finite family of words contains a proper combinatorial line. -/
def HasLine [DecidableEq (ι → α)] (A : Finset (ι → α)) : Prop :=
  ∃ l : Combinatorics.Line α ι, ∀ a : α, l a ∈ A

theorem hasLine_iff [DecidableEq (ι → α)] {A : Finset (ι → α)} :
    HasLine A ↔ ∃ l : Combinatorics.Line α ι, Set.range l ⊆ (A : Set (ι → α)) := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, by rintro _ ⟨a, rfl⟩; exact hl a⟩
  · rintro ⟨l, hl⟩
    exact ⟨l, fun a ↦ hl ⟨a, rfl⟩⟩

/-- A line in a parameter cube, lifted through a subspace. -/
abbrev liftLine (U : Combinatorics.Subspace η α ι)
    (l : Combinatorics.Line α η) : Combinatorics.Line α ι :=
  U.lineMap l

@[simp] theorem liftLine_apply (U : Combinatorics.Subspace η α ι)
    (l : Combinatorics.Line α η) (a : α) :
    liftLine U l a = U (l a) :=
  Combinatorics.Subspace.lineMap_apply U l a

end Lines

section Pullback

variable {α ι η ζ : Type*}

/-- The points of `A` seen in the parameter cube of `U`. -/
noncomputable def pullbackFinset [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x ↦ U x ∈ A

@[simp] theorem mem_pullbackFinset [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) (x : η → α) :
    x ∈ pullbackFinset U A ↔ U x ∈ A := by
  classical
  simp [pullbackFinset]

@[simp] theorem coe_pullbackFinset [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    (pullbackFinset U A : Set (η → α)) = U ⁻¹' (A : Set (ι → α)) := by
  ext x
  simp

@[simp] theorem pullbackFinset_univ [Fintype η] [Fintype α]
    [Fintype ι] [DecidableEq η] [DecidableEq ι]
    (U : Combinatorics.Subspace η α ι) :
    pullbackFinset U (Finset.univ : Finset (ι → α)) = Finset.univ := by
  classical
  ext x
  simp

@[simp] theorem pullbackFinset_empty [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) :
    pullbackFinset U (∅ : Finset (ι → α)) = ∅ := by
  classical
  ext x
  simp

theorem pullbackFinset_mono [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) {A B : Finset (ι → α)}
    (hAB : A ⊆ B) : pullbackFinset U A ⊆ pullbackFinset U B := by
  intro x hx
  exact (mem_pullbackFinset U B x).2 (hAB ((mem_pullbackFinset U A x).1 hx))

@[simp] theorem pullbackFinset_inter [Fintype η] [Fintype α]
    [DecidableEq (η → α)] [DecidableEq (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A B : Finset (ι → α)) :
    pullbackFinset U (A ∩ B) = pullbackFinset U A ∩ pullbackFinset U B := by
  classical
  ext x
  simp

@[simp] theorem pullbackFinset_union [Fintype η] [Fintype α]
    [DecidableEq (η → α)] [DecidableEq (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A B : Finset (ι → α)) :
    pullbackFinset U (A ∪ B) = pullbackFinset U A ∪ pullbackFinset U B := by
  classical
  ext x
  simp

@[simp] theorem pullbackFinset_sdiff [Fintype η] [Fintype α]
    [DecidableEq (η → α)] [DecidableEq (ι → α)]
    (U : Combinatorics.Subspace η α ι) (A B : Finset (ι → α)) :
    pullbackFinset U (A \ B) = pullbackFinset U A \ pullbackFinset U B := by
  classical
  ext x
  simp

@[simp] theorem pullback_comp [Fintype ζ] [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι)
    (V : Combinatorics.Subspace ζ α η) (A : Finset (ι → α)) :
    pullbackFinset (U.comp V) A = pullbackFinset V (pullbackFinset U A) := by
  classical
  ext x
  simp

/-- Density of `A` inside `U`, measured in the uniform parameter cube. -/
noncomputable def densityIn [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : ℝ :=
  ((pullbackFinset U A).card : ℝ) / Nat.card (η → α)

@[simp] theorem densityIn_eq_card_div [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    densityIn U A = ((pullbackFinset U A).card : ℝ) / Nat.card (η → α) :=
  rfl

theorem densityIn_nonneg [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    0 ≤ densityIn U A := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem densityIn_le_one [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    densityIn U A ≤ 1 := by
  classical
  rw [densityIn, Nat.card_eq_fintype_card]
  cases isEmpty_or_nonempty (η → α) with
  | inl h =>
      letI := h
      have hp : pullbackFinset U A = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hp]
  | inr h =>
      letI := h
      have hc : (0 : ℝ) < Fintype.card (η → α) := by
        exact_mod_cast Fintype.card_pos
      rw [div_le_one hc]
      exact_mod_cast Finset.card_le_univ (pullbackFinset U A)

@[simp] theorem densityIn_comp [Fintype ζ] [Fintype η] [Fintype α]
    (U : Combinatorics.Subspace η α ι)
    (V : Combinatorics.Subspace ζ α η) (A : Finset (ι → α)) :
    densityIn (U.comp V) A = densityIn V (pullbackFinset U A) := by
  simp [densityIn]

theorem HasLine.of_pullback [Fintype η] [Fintype α]
    [DecidableEq (η → α)] [DecidableEq (ι → α)]
    (U : Combinatorics.Subspace η α ι)
    {A : Finset (ι → α)} (h : HasLine (pullbackFinset U A)) : HasLine A := by
  obtain ⟨l, hl⟩ := h
  refine ⟨U.lineMap l, ?_⟩
  intro a
  rw [Combinatorics.Subspace.lineMap_apply]
  exact (mem_pullbackFinset U A (l a)).1 (hl a)

end Pullback

section RestrictedPart

/-- The part of an enlarged-alphabet finset using only the old letters. -/
noncomputable def restrictedPart {k m : ℕ}
    (A : Finset (Word (k + 1) m)) : Finset (Word k m) := by
  classical
  exact Finset.univ.filter fun x ↦ Erdos171.restrictWord x ∈ A

@[simp] theorem mem_restrictedPart {k m : ℕ}
    (A : Finset (Word (k + 1) m)) (x : Word k m) :
    x ∈ restrictedPart A ↔ Erdos171.restrictWord x ∈ A := by
  classical
  simp [restrictedPart]

/-- The binary part of a ternary finset. -/
noncomputable def binaryPart {m : ℕ} (A : Finset (Word 3 m)) : Finset (Word 2 m) :=
  restrictedPart A

/-- Every old-alphabet parameter word of `U` is carried into `A`. -/
def RestrictedPartContained {k m n : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (A : Finset (Word (k + 1) n)) : Prop :=
  ∀ x : Word k m, U (Erdos171.restrictWord x) ∈ A

theorem restrictedPartContained_iff {k m n : ℕ}
    (U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (A : Finset (Word (k + 1) n)) :
    RestrictedPartContained U A ↔
      restrictedPart (pullbackFinset U A) = Finset.univ := by
  classical
  constructor
  · intro h
    ext x
    simp [h x]
  · intro h x
    have hx : x ∈ restrictedPart (pullbackFinset U A) := by rw [h]; simp
    simpa using hx

end RestrictedPart

section Insensitive

variable {k m n : ℕ}

/-- A combinatorial subspace map preserves `(i,last)`-equivalence. -/
theorem lastEquivalent_subspace_apply
    (U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) (i : Fin k)
    {x y : Word (k + 1) m} (hxy : Erdos171.LastEquivalent i x y) :
    Erdos171.LastEquivalent i (U x) (U y) := by
  unfold Erdos171.LastEquivalent at hxy ⊢
  funext r
  cases hr : U.idxFun r with
  | inl a => simp [Erdos171.replaceLast, Combinatorics.Subspace.coe_apply, hr]
  | inr e =>
      simpa [Erdos171.replaceLast, Combinatorics.Subspace.coe_apply, hr] using
        congrFun hxy e

theorem isLastInsensitive_preimage_subspace
    (U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) (i : Fin k)
    {C : Set (Word (k + 1) n)} (hC : Erdos171.IsLastInsensitive i C) :
    Erdos171.IsLastInsensitive i (U ⁻¹' C) := by
  intro x y hxy
  exact hC (U x) (U y) (lastEquivalent_subspace_apply U i hxy)

theorem isLastInsensitive_pullbackFinset
    (U : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)) (i : Fin k)
    (C : Finset (Word (k + 1) n))
    (hC : Erdos171.IsLastInsensitive i (C : Set (Word (k + 1) n))) :
    Erdos171.IsLastInsensitive i
      (pullbackFinset U C : Set (Word (k + 1) m)) := by
  rw [coe_pullbackFinset]
  exact isLastInsensitive_preimage_subspace U i hC

end Insensitive

section Conversion

theorem hasLine_iff_containsLine {t n : ℕ} (A : Finset (Word t n)) :
    HasLine A ↔ Erdos171.ContainsLine (A : Set (Word t n)) := by
  simpa only [HasLine] using
    (Erdos171.containsLine_coe_finset_iff (A := A)).symm

theorem HasLine.containsLine {t n : ℕ} {A : Finset (Word t n)}
    (hA : HasLine A) : Erdos171.ContainsLine (A : Set (Word t n)) :=
  (hasLine_iff_containsLine A).1 hA

end Conversion

end Erdos185.DHJ
