/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite product boxes and minimal subcovers for Simpson's theorem.
Informal source: Balister--Bollobás--Morris--Sahasrabudhe--Tiba,
"The structure and number of Erdős covering systems", Appendix A.
Formal author: OpenAI Codex.
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Minimal
import Mathlib.Tactic

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ}

abbrev Point (q : ι → ℕ) := (i : ι) → Fin (q i)

/-- Each coordinate of a box is either free or fixed to one value. -/
abbrev Box (q : ι → ℕ) := (i : ι) → Option (Fin (q i))

def Contains (H : Box q) (x : Point q) : Prop :=
  ∀ i v, H i = some v → x i = v

def fixed [Fintype ι] (H : Box q) : Finset ι := univ.filter fun i => (H i).isSome

def familyFixed [Fintype ι] [DecidableEq ι] (H : α → Box q) (A : Finset α) : Finset ι :=
  A.biUnion fun a => fixed (H a)

lemma mem_fixed [Fintype ι] {H : Box q} {i : ι} : i ∈ fixed H ↔ ∃ v, H i = some v := by
  simp [fixed, Option.isSome_iff_exists]

lemma mem_familyFixed [Fintype ι] [DecidableEq ι] {H : α → Box q} {A : Finset α} {i : ι} :
    i ∈ familyFixed H A ↔ ∃ a ∈ A, i ∈ fixed (H a) := by
  simp [familyFixed]

lemma familyFixed_mono [Fintype ι] [DecidableEq ι] (H : α → Box q)
    {A B : Finset α} (h : A ⊆ B) :
    familyFixed H A ⊆ familyFixed H B := by
  intro i hi
  obtain ⟨a, ha, hia⟩ := mem_familyFixed.mp hi
  exact mem_familyFixed.mpr ⟨a, h ha, hia⟩

def CoversOn (H : α → Box q) (A : Finset α) (X : Set (Point q)) : Prop :=
  ∀ x ∈ X, ∃ a ∈ A, Contains (H a) x

def MinimalCoverOn (H : α → Box q) (A : Finset α) (X : Set (Point q)) : Prop :=
  CoversOn H A X ∧ ∀ B ⊂ A, ¬ CoversOn H B X

lemma CoversOn.mono {H : α → Box q} {A B : Finset α} {X : Set (Point q)}
    (h : CoversOn H A X) (hAB : A ⊆ B) : CoversOn H B X := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := h x hx
  exact ⟨a, hAB ha, hax⟩

lemma CoversOn.exists_minimal_subcover {H : α → Box q} {A : Finset α}
    {X : Set (Point q)} (h : CoversOn H A X) :
    ∃ B ⊆ A, MinimalCoverOn H B X := by
  classical
  obtain ⟨B, hBA, hB⟩ := exists_minimal_le_of_wellFoundedLT (fun B => CoversOn H B X) A h
  refine ⟨B, hBA, hB.1, ?_⟩
  intro C hC hcover
  exact hC.not_ge (hB.2 hcover hC.subset)

/-- Every member of a minimal cover has a private witness in the set covered. -/
lemma MinimalCoverOn.private_witness {H : α → Box q} {A : Finset α}
    {X : Set (Point q)} (h : MinimalCoverOn H A X) {a : α} (ha : a ∈ A) :
    ∃ x ∈ X, Contains (H a) x ∧ ∀ b ∈ A, b ≠ a → ¬ Contains (H b) x := by
  classical
  have hn := h.2 (A.erase a) (erase_ssubset ha)
  simp only [CoversOn, not_forall, not_exists, not_and] at hn
  obtain ⟨x, hx, hn⟩ := hn
  obtain ⟨b, hb, hbx⟩ := h.1 x hx
  have hba : b = a := by
    by_contra hba
    exact hn b (mem_erase.mpr ⟨hba, hb⟩) hbx
  subst b
  exact ⟨x, hx, hbx, fun b hb hba => hn b (mem_erase.mpr ⟨hba, hb⟩)⟩

/-- Forget one fixed coordinate. -/
def drop [DecidableEq ι] (i : ι) (H : Box q) : Box q := Function.update H i none

lemma contains_drop [DecidableEq ι] {H : Box q} {x : Point q} {i : ι} :
    Contains (drop i H) x ↔ ∀ j, j ≠ i → ∀ v, H j = some v → x j = v := by
  constructor
  · intro h j hji v hv
    exact h j v (by simpa [drop, hji] using hv)
  · intro h j v hv
    by_cases hji : j = i
    · subst j
      simp [drop] at hv
    · exact h j hji v (by simpa [drop, hji] using hv)

lemma fixed_drop [Fintype ι] [DecidableEq ι] (H : Box q) (i : ι) :
    fixed (drop i H) = (fixed H).erase i := by
  ext j
  rw [mem_fixed, mem_erase, mem_fixed]
  by_cases hji : j = i
  · subst j
    simp [drop]
  · simp [drop, hji]

lemma familyFixed_drop [Fintype ι] [DecidableEq ι] (H : α → Box q) (A : Finset α) (i : ι) :
    familyFixed (fun a => drop i (H a)) A = (familyFixed H A).erase i := by
  ext j
  simp only [mem_familyFixed, fixed_drop, mem_erase]
  aesop

def Compatible (H : Box q) (i : ι) (s : Fin (q i)) : Prop :=
  H i = none ∨ H i = some s

lemma contains_drop_update_iff [DecidableEq ι] {H : Box q} {x : Point q}
    {i : ι} {s : Fin (q i)}
    (hc : Compatible H i s) :
    Contains (drop i H) x ↔ Contains H (Function.update x i s) := by
  rw [contains_drop]
  constructor
  · intro h j v hv
    by_cases hji : j = i
    · subst j
      rcases hc with hc | hc
      · rw [hc] at hv
        contradiction
      · have hsv : s = v := Option.some.inj (hc.symm.trans hv)
        simpa using hsv
    · simpa [hji] using h j hji v hv
  · intro h j hji v hv
    simpa [hji] using h j v hv

lemma MinimalCoverOn.compatible_slice {H : α → Box q} {A : Finset α} {i : ι}
    {s : Fin (q i)} (h : MinimalCoverOn H A {x | x i = s}) {a : α} (ha : a ∈ A) :
    Compatible (H a) i s := by
  obtain ⟨x, hx, hax, _⟩ := h.private_witness ha
  cases hv : H a i with
  | none => exact Or.inl hv
  | some v =>
      have hvs : v = s := (hax i v hv).symm.trans hx
      exact Or.inr (by simpa [hvs] using hv)

lemma coversOn_slice_iff_drop [DecidableEq ι] {H : α → Box q} {A : Finset α} {i : ι}
    {s : Fin (q i)} (hc : ∀ a ∈ A, Compatible (H a) i s) :
    CoversOn H A {x | x i = s} ↔ CoversOn (fun a => drop i (H a)) A Set.univ := by
  constructor
  · intro h x _
    obtain ⟨a, ha, hax⟩ := h (Function.update x i s) (by simp)
    exact ⟨a, ha, (contains_drop_update_iff (hc a ha)).mpr hax⟩
  · intro h x hx
    obtain ⟨a, ha, hax⟩ := h x (Set.mem_univ _)
    refine ⟨a, ha, ?_⟩
    have heq : Function.update x i s = x := by
      have hs : s = x i := hx.symm
      rw [hs, Function.update_eq_self]
    simpa only [heq] using (contains_drop_update_iff (hc a ha)).mp hax

lemma MinimalCoverOn.drop_slice [DecidableEq ι] {H : α → Box q} {A : Finset α} {i : ι}
    {s : Fin (q i)} (h : MinimalCoverOn H A {x | x i = s}) :
    MinimalCoverOn (fun a => drop i (H a)) A Set.univ := by
  have hc : ∀ a ∈ A, Compatible (H a) i s := fun a ha => h.compatible_slice ha
  refine ⟨(coversOn_slice_iff_drop hc).mp h.1, ?_⟩
  intro B hB hcover
  exact h.2 B hB ((coversOn_slice_iff_drop (fun a ha => hc a (hB.subset ha))).mpr hcover)

end Erdos1189.Grid
