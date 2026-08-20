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
# Reindexing finite sign-vector arrangements

Feasible face and restriction counts are invariant under an equivalence of their finite index
types. This is the bookkeeping needed to apply deletion--restriction to ordered prefixes indexed
by `Fin n`.
-/

namespace Erdos735.SignVector

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def reindexNormals (e : J ≃ I) (n : I → Vec3) : J → Vec3 :=
  fun j ↦ n (e j)

def reindexSigns (e : J ≃ I) (s : J → Bool) : I → Bool :=
  fun i ↦ s (e.symm i)

theorem realizes_reindex_iff (e : J ≃ I) (n : I → Vec3)
    (s : J → Bool) (x : Vec3) :
    Realizes (reindexNormals e n) s x ↔ Realizes n (reindexSigns e s) x := by
  constructor
  · intro h i
    simpa [reindexNormals, reindexSigns] using h (e.symm i)
  · intro h j
    simpa [reindexNormals, reindexSigns] using h (e j)

theorem realizable_reindex_iff (e : J ≃ I) (n : I → Vec3) (s : J → Bool) :
    Realizable (reindexNormals e n) s ↔ Realizable n (reindexSigns e s) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (realizes_reindex_iff e n s x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (realizes_reindex_iff e n s x).mpr hx⟩

theorem restrictedRealizable_reindex_iff (e : J ≃ I) (n : I → Vec3)
    (h : Vec3) (s : J → Bool) :
    RestrictedRealizable (reindexNormals e n) h s ↔
      RestrictedRealizable n h (reindexSigns e s) := by
  constructor
  · rintro ⟨x, hx, hzero⟩
    exact ⟨x, (realizes_reindex_iff e n s x).mp hx, hzero⟩
  · rintro ⟨x, hx, hzero⟩
    exact ⟨x, (realizes_reindex_iff e n s x).mpr hx, hzero⟩

def signReindexEquiv (e : J ≃ I) : (J → Bool) ≃ (I → Bool) where
  toFun := reindexSigns e
  invFun := reindexSigns e.symm
  left_inv s := by funext j; simp [reindexSigns]
  right_inv s := by funext i; simp [reindexSigns]

noncomputable def strictFaceReindexEquiv (e : J ≃ I) (n : I → Vec3) :
    StrictFace (reindexNormals e n) ≃ StrictFace n where
  toFun f := ⟨reindexSigns e f.1, (realizable_reindex_iff e n f.1).mp f.2⟩
  invFun f := ⟨reindexSigns e.symm f.1, by
    apply (realizable_reindex_iff e n (reindexSigns e.symm f.1)).mpr
    convert f.2 using 1
    funext i
    simp [reindexSigns]⟩
  left_inv f := by apply Subtype.ext; funext j; simp [reindexSigns]
  right_inv f := by apply Subtype.ext; funext i; simp [reindexSigns]

theorem faceCount_reindex [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) (n : I → Vec3) :
    faceCount (reindexNormals e n) = faceCount n := by
  rw [← card_strictFace, ← card_strictFace]
  exact Fintype.card_congr (strictFaceReindexEquiv e n)

abbrev StrictRestriction (n : I → Vec3) (h : Vec3) :=
  {s : I → Bool // RestrictedRealizable n h s}

noncomputable instance strictRestrictionFintype (n : I → Vec3) (h : Vec3) :
    Fintype (StrictRestriction n h) := Fintype.ofFinite _

theorem card_strictRestriction [DecidableEq I] (n : I → Vec3) (h : Vec3) :
    Fintype.card (StrictRestriction n h) = restrictedFaceCount n h := by
  classical
  rw [Fintype.card_subtype]
  unfold restrictedFaceCount restrictedFacePatterns
  apply congrArg Finset.card
  ext s
  simp

noncomputable def strictRestrictionReindexEquiv (e : J ≃ I) (n : I → Vec3) (h : Vec3) :
    StrictRestriction (reindexNormals e n) h ≃ StrictRestriction n h where
  toFun s := ⟨reindexSigns e s.1, (restrictedRealizable_reindex_iff e n h s.1).mp s.2⟩
  invFun s := ⟨reindexSigns e.symm s.1, by
    apply (restrictedRealizable_reindex_iff e n h (reindexSigns e.symm s.1)).mpr
    convert s.2 using 1
    funext i
    simp [reindexSigns]⟩
  left_inv s := by apply Subtype.ext; funext j; simp [reindexSigns]
  right_inv s := by apply Subtype.ext; funext i; simp [reindexSigns]

theorem restrictedFaceCount_reindex [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) (n : I → Vec3) (h : Vec3) :
    restrictedFaceCount (reindexNormals e n) h = restrictedFaceCount n h := by
  rw [← card_strictRestriction, ← card_strictRestriction]
  exact Fintype.card_congr (strictRestrictionReindexEquiv e n h)

end

end Erdos735.SignVector
