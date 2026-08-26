/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Restricting coordinate values in a finite box cover.
Informal source: the restriction to the sets R_i in BBMST Lemma 3.4.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.BoxMeasure
import Mathlib.Data.Finset.Sort

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ}

def restrictionPoint (R : (i : ι) → Finset (Fin (q i)))
    (u : Point (fun i => (R i).card)) : Point q :=
  fun i => ((R i).orderIsoOfFin rfl (u i)).val

def RestrictionCompatible (R : (i : ι) → Finset (Fin (q i))) (H : Box q) : Prop :=
  ∀ i v, H i = some v → v ∈ R i

def restrictedBox (R : (i : ι) → Finset (Fin (q i))) (H : Box q) :
    Box (fun i => (R i).card) := fun i =>
  (H i).bind fun v => if hv : v ∈ R i then some (((R i).orderIsoOfFin rfl).symm ⟨v, hv⟩)
    else none

lemma restrictionPoint_mem (R : (i : ι) → Finset (Fin (q i)))
    (u : Point (fun i => (R i).card)) (i : ι) : restrictionPoint R u i ∈ R i :=
  ((R i).orderIsoOfFin rfl (u i)).property

lemma restrictionPoint_coordinate_iff (R : (i : ι) → Finset (Fin (q i)))
    (u : Point (fun i => (R i).card)) (i : ι) {v : Fin (q i)} (hv : v ∈ R i) :
    u i = ((R i).orderIsoOfFin rfl).symm ⟨v, hv⟩ ↔ restrictionPoint R u i = v := by
  constructor
  · intro h
    simp only [restrictionPoint, h, OrderIso.apply_symm_apply]
  · intro h
    apply ((R i).orderIsoOfFin rfl).injective
    rw [OrderIso.apply_symm_apply]
    exact Subtype.ext h

lemma contains_restrictedBox_iff (R : (i : ι) → Finset (Fin (q i))) {H : Box q}
    (hH : RestrictionCompatible R H) (u : Point (fun i => (R i).card)) :
    Contains (restrictedBox R H) u ↔ Contains H (restrictionPoint R u) := by
  have hcoord : ∀ i, (∀ w, restrictedBox R H i = some w → u i = w) ↔
      (∀ v, H i = some v → restrictionPoint R u i = v) := by
    intro i
    cases hi : H i with
    | none => simp [restrictedBox, hi]
    | some v =>
      have hv := hH i v hi
      simpa [restrictedBox, hi, hv] using restrictionPoint_coordinate_iff R u i hv
  exact forall_congr' hcoord

lemma fixed_restrictedBox [Fintype ι] (R : (i : ι) → Finset (Fin (q i))) {H : Box q}
    (hH : RestrictionCompatible R H) : fixed (restrictedBox R H) = fixed H := by
  ext i
  rw [mem_fixed, mem_fixed]
  cases hi : H i with
  | none => simp [restrictedBox, hi]
  | some v => simp [restrictedBox, hi, hH i v hi]

lemma Contains.restriction_compatible (R : (i : ι) → Finset (Fin (q i))) {H : Box q}
    {u : Point (fun i => (R i).card)} (h : Contains H (restrictionPoint R u)) :
    RestrictionCompatible R H := by
  intro i v hv
  rw [← h i v hv]
  exact restrictionPoint_mem R u i

noncomputable def restrictionFamily (R : (i : ι) → Finset (Fin (q i)))
    (H : α → Box q) (A : Finset α) : Finset α := by
  classical
  exact A.filter (fun a => RestrictionCompatible R (H a))

lemma CoversOn.restrict_values (R : (i : ι) → Finset (Fin (q i)))
    {H : α → Box q} {A : Finset α} (h : CoversOn H A Set.univ) :
    CoversOn (fun a => restrictedBox R (H a))
      (restrictionFamily R H A) Set.univ := by
  classical
  intro u _
  obtain ⟨a, ha, hua⟩ := h (restrictionPoint R u) (Set.mem_univ _)
  have hcompat := hua.restriction_compatible R
  exact ⟨a, mem_filter.mpr ⟨ha, hcompat⟩, (contains_restrictedBox_iff R hcompat u).mpr hua⟩

end Erdos1189.Grid
