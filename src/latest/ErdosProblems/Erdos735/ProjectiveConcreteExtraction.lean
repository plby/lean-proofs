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

import ErdosProblems.Erdos735.ProjectiveBoundaryExtraction
import ErdosProblems.Erdos735.ProjectiveFullRestrictionCount
import ErdosProblems.Erdos735.PolarFace

open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos735.ProjectiveBoundaryExtraction

open Classical ChartOrder SignVector ProjectiveArrangement
noncomputable section

noncomputable def projectiveVertexEquivOfFinsetEq {B C : Finset Point} (h : B = C) :
    {v // v ∈ projectiveVertices B} ≃ {v // v ∈ projectiveVertices C} := by
  subst C
  exact Equiv.refl _

@[simp] theorem coe_projectiveVertexEquivOfFinsetEq {B C : Finset Point} (h : B = C)
    (v : {v // v ∈ projectiveVertices B}) :
    (projectiveVertexEquivOfFinsetEq h v : ℙ ℝ Vec3) = v.1 := by
  subst C
  rfl

theorem concreteRestrictedFaceCount
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    ∀ p : Line B,
      restrictedFaceCount (otherNormals (normals B) p) (normals B p) =
        2 * (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) p).card := by
  have hab : (⟨a, ha⟩ : Line B) ≠ ⟨b, hb⟩ := by
    intro hab'
    apply hncol
    have habp : a = b := congrArg Subtype.val hab'
    subst b
    simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]
  let : Nontrivial (Line B) := ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩⟩
  intro p
  rw [card_verticesOn_subtype]
  exact restrictedFaceCount_otherNormals_normalVec_eq_two_mul_verticesOn_card B p

theorem concreteStrictFaceCardNat
    (B : Finset Point) (a : Line B) [Nontrivial (Line B)] :
    Fintype.card (StrictFace (normals B)) =
      2 + ∑ v : Vertex B, 2 * (lineMultiplicity (OnLine B) v - 1) := by
  let m := Fintype.card {b : Line B // b ≠ a}
  let e : Fin (m + 1) ≃ Line B := selectedLastIndexEquiv a
  let p : Fin (m + 1) → Point := selectedLastPoints (fun b : Line B ↦ b.1) a
  have hp : Function.Injective p :=
    selectedLastPoints_injective (fun b : Line B ↦ b.1) Subtype.val_injective a
  have hpcomp : p = fun i ↦ (e i).1 := by
    exact selectedLastPoints_eq_comp_selectedLastIndexEquiv
      (fun b : Line B ↦ b.1) a
  have henum : enumeratedPointSet p = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
      rw [hpcomp] at hix
      rw [← hix]
      exact (e i).2
    · intro hx
      let y : Line B := ⟨x, hx⟩
      apply Finset.mem_image.mpr
      refine ⟨e.symm y, Finset.mem_univ _, ?_⟩
      rw [hpcomp]
      exact congrArg Subtype.val (e.apply_symm_apply y)
  have hmul (v : Vertex B) :
      lineMultiplicity (EnumeratedOnLine p) ⟨v.1, by simpa [henum] using v.2⟩ =
        lineMultiplicity (OnLine B) v := by
    classical
    apply Finset.card_bij (fun i _ ↦ e i)
    · intro i hi
      simp only [lineMultiplicity, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      simpa [EnumeratedOnLine, OnLine, hpcomp] using hi
    · intro i hi j hj hij
      exact e.injective hij
    · intro l hl
      refine ⟨e.symm l, ?_, e.apply_symm_apply l⟩
      simp only [lineMultiplicity, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      simpa [EnumeratedOnLine, OnLine, hpcomp] using hl
  have hcount := strictFace_card_normalVec_eq_two_add_sum_multiplicity m p hp
  have hleft :
      Fintype.card (StrictFace (fun i ↦ normalVec (p i))) =
        Fintype.card (StrictFace (normals B)) := by
    rw [card_strictFace, card_strictFace]
    have hn : (fun i ↦ normalVec (p i)) = reindexNormals e (normals B) := by
      funext i
      simp [hpcomp, reindexNormals, normals]
    rw [hn, faceCount_reindex]
  rw [hleft] at hcount
  have hright :
      (∑ v : EnumeratedVertex p,
          2 * (lineMultiplicity (EnumeratedOnLine p) v - 1)) =
        ∑ v : Vertex B, 2 * (lineMultiplicity (OnLine B) v - 1) := by
    let ve : EnumeratedVertex p ≃ Vertex B := projectiveVertexEquivOfFinsetEq henum
    apply Fintype.sum_equiv ve
    intro v
    apply congrArg (fun z : ℕ ↦ 2 * (z - 1))
    have hw := hmul (ve v)
    have hv :
        (⟨(ve v).1, by simpa only [henum] using (ve v).2⟩ : EnumeratedVertex p) = v := by
      apply Subtype.ext
      exact coe_projectiveVertexEquivOfFinsetEq henum v
    rw [hv] at hw
    exact hw
  rw [hright] at hcount
  exact hcount

theorem concreteStrictFaceCardInt
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    (Fintype.card (StrictFace (normals B)) : ℤ) =
      2 + ∑ v : Vertex B, 2 * ((lineMultiplicity (OnLine B) v : ℤ) - 1) := by
  have hab : (⟨a, ha⟩ : Line B) ≠ ⟨b, hb⟩ := by
    intro hab'
    apply hncol
    have habp : a = b := congrArg Subtype.val hab'
    subst b
    simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]
  let : Nontrivial (Line B) := ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩⟩
  have hnat := concreteStrictFaceCardNat B ⟨a, ha⟩
  calc
    (Fintype.card (StrictFace (normals B)) : ℤ) =
        ((2 + ∑ v : Vertex B, 2 * (lineMultiplicity (OnLine B) v - 1) : ℕ) : ℤ) := by
      exact congrArg (fun z : ℕ ↦ (z : ℤ)) hnat
    _ = 2 + ∑ v : Vertex B,
        2 * ((lineMultiplicity (OnLine B) v : ℤ) - 1) := by
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_mul]
      apply congrArg (fun z : ℤ ↦ 2 + z)
      apply Finset.sum_congr rfl
      intro v hv
      have hmul : 1 ≤ lineMultiplicity (OnLine B) v := by
        exact le_trans (by decide : 1 ≤ 2) (two_le_lineMultiplicity B v)
      rw [Nat.cast_sub hmul]
      norm_num

noncomputable def concreteBoundaryExtraction
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    BoundaryExtraction (normals B) (normals_ne_zero B) :=
  boundaryExtractionOfRestrictedFaceCounts B ha hb hc hncol
    (concreteRestrictedFaceCount B ha hb hc hncol)
    (fun f ↦ SignVector.PolarFace.normalVec_faceEdges_card_three_le B ha hb hc hncol f)
    (concreteStrictFaceCardInt B ha hb hc hncol)

end

end Erdos735.ProjectiveBoundaryExtraction
