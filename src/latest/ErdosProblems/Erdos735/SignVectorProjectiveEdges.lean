/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.SignVectorIncidence

/-!
# Antipodal pairing of strict arrangement edges

A projective open edge has two spherical lifts. This file separates that
algebraic double cover from the geometric identification with cyclic-consecutive
projective intervals.
-/

open scoped Matrix
open Matrix
namespace Erdos735.SignVector

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma restrictedRealizable_antipodalSign_iff (n : I → Vec3) (h : Vec3)
    (s : I → Bool) :
    RestrictedRealizable n h (antipodalSign s) ↔ RestrictedRealizable n h s := by
  constructor
  · rintro ⟨x, hx, hxzero⟩
    refine ⟨-x, ?_, ?_⟩
    · exact (realizes_antipodalSign_neg_iff n s (-x)).mp (by simpa using hx)
    · simpa [dotProduct_neg, hxzero]
  · rintro ⟨x, hx, hxzero⟩
    refine ⟨-x, (realizes_antipodalSign_neg_iff n s x).mpr hx, ?_⟩
    simpa [dotProduct_neg, hxzero]

def antipodalEdge (n : I → Vec3) (e : StrictEdge n) : StrictEdge n :=
  ⟨⟨e.1.1, antipodalSign e.1.2⟩,
    (restrictedRealizable_antipodalSign_iff
      (otherNormals n e.1.1) (n e.1.1) e.1.2).2 e.2⟩

@[simp] theorem antipodalEdge_support (n : I → Vec3) (e : StrictEdge n) :
    (antipodalEdge n e).1.1 = e.1.1 := rfl

@[simp] theorem antipodalEdge_sign (n : I → Vec3) (e : StrictEdge n)
    (j : {j : I // j ≠ e.1.1}) :
    (antipodalEdge n e).1.2 j = !(e.1.2 j) := rfl

@[simp] theorem antipodalEdge_involutive (n : I → Vec3) (e : StrictEdge n) :
    antipodalEdge n (antipodalEdge n e) = e := by
  rcases e with ⟨⟨i, s⟩, hs⟩
  apply Subtype.ext
  change (⟨i, antipodalSign (antipodalSign s)⟩ : EdgeCode I) = ⟨i, s⟩
  rw [antipodalSign_antipodalSign]

abbrev OtherLineChoice (I : Type*) := ∀ i : I, {j : I // j ≠ i}

def IsPositiveEdgeRepresentative (pick : OtherLineChoice I)
    (n : I → Vec3) (e : StrictEdge n) : Prop :=
  e.1.2 (pick e.1.1) = true

abbrev ProjectiveStrictEdge (pick : OtherLineChoice I) (n : I → Vec3) :=
  {e : StrictEdge n // IsPositiveEdgeRepresentative pick n e}

noncomputable instance (pick : OtherLineChoice I) (n : I → Vec3) :
    Fintype (ProjectiveStrictEdge pick n) := Fintype.ofFinite _

noncomputable instance (pick : OtherLineChoice I) (n : I → Vec3) :
    DecidableEq (ProjectiveStrictEdge pick n) := Classical.decEq _

lemma antipodalEdge_isPositive_iff (pick : OtherLineChoice I)
    (n : I → Vec3) (e : StrictEdge n) :
    IsPositiveEdgeRepresentative pick n (antipodalEdge n e) ↔
      ¬ IsPositiveEdgeRepresentative pick n e := by
  unfold IsPositiveEdgeRepresentative
  cases h : e.1.2 (pick e.1.1) <;> simp [h]

noncomputable def normalizeProjectiveEdge (pick : OtherLineChoice I)
    (n : I → Vec3) (e : StrictEdge n) : ProjectiveStrictEdge pick n := by
  by_cases he : IsPositiveEdgeRepresentative pick n e
  · exact ⟨e, he⟩
  · exact ⟨antipodalEdge n e, (antipodalEdge_isPositive_iff pick n e).2 he⟩

def edgeSheet (pick : OtherLineChoice I) (n : I → Vec3)
    (e : StrictEdge n) : Bool := e.1.2 (pick e.1.1)

noncomputable def strictEdgeEquivProjectiveTimesBool (pick : OtherLineChoice I)
    (n : I → Vec3) : StrictEdge n ≃ ProjectiveStrictEdge pick n × Bool where
  toFun e := (normalizeProjectiveEdge pick n e, edgeSheet pick n e)
  invFun eb := if eb.2 then eb.1.1 else antipodalEdge n eb.1.1
  left_inv e := by
    cases he : edgeSheet pick n e with
    | false =>
        have hnot : ¬ IsPositiveEdgeRepresentative pick n e := by
          simpa [edgeSheet, IsPositiveEdgeRepresentative] using he
        simp [normalizeProjectiveEdge, hnot, he]
    | true =>
        have hpos : IsPositiveEdgeRepresentative pick n e := by
          simpa [edgeSheet, IsPositiveEdgeRepresentative] using he
        simp [normalizeProjectiveEdge, hpos, he]
  right_inv eb := by
    rcases eb with ⟨e, b⟩
    have he : IsPositiveEdgeRepresentative pick n e.1 := e.2
    cases b with
    | false =>
        have hanti : ¬ IsPositiveEdgeRepresentative pick n (antipodalEdge n e.1) :=
          (antipodalEdge_isPositive_iff pick n e.1).not.mpr (not_not.mpr he)
        change
          (normalizeProjectiveEdge pick n (antipodalEdge n e.1),
            edgeSheet pick n (antipodalEdge n e.1)) = (e, false)
        apply Prod.ext
        · apply Subtype.ext
          simp [normalizeProjectiveEdge, hanti]
        · unfold edgeSheet IsPositiveEdgeRepresentative at he ⊢
          simpa using he
    | true =>
        change (normalizeProjectiveEdge pick n e.1, edgeSheet pick n e.1) = (e, true)
        apply Prod.ext
        · apply Subtype.ext
          simp [normalizeProjectiveEdge, he]
        · exact he

theorem card_strictEdge_eq_two_mul_projective
    (pick : OtherLineChoice I) (n : I → Vec3) :
    Fintype.card (StrictEdge n) =
      2 * Fintype.card (ProjectiveStrictEdge pick n) := by
  rw [Fintype.card_congr (strictEdgeEquivProjectiveTimesBool pick n),
    Fintype.card_prod, Fintype.card_bool]
  omega

end Erdos735.SignVector
