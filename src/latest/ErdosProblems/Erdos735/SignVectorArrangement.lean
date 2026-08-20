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

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# Sign vectors of a central real hyperplane arrangement

This file develops the algebraic part of the finite great-circle cellulation.
Spherical two-cells are represented by feasible strict sign vectors.  It proves
the deletion--restriction recurrence, the free antipodal pairing, and the Euler
invariance calculation for an insertion.  No topological component theorem is
used here.
-/

open scoped BigOperators Matrix
open Matrix

namespace Erdos735
namespace SignVector

abbrev Vec3 := Fin 3 → ℝ

noncomputable def norm3 (v : Vec3) : ℝ := ‖WithLp.toLp 2 v‖

def signed (b : Bool) (r : ℝ) : ℝ := if b then r else -r

lemma signed_add (b : Bool) (r s : ℝ) :
    signed b (r + s) = signed b r + signed b s := by
  cases b <;> simp [signed] <;> ring

lemma signed_sub (b : Bool) (r s : ℝ) :
    signed b (r - s) = signed b r - signed b s := by
  cases b <;> simp [signed] <;> ring

lemma signed_mul (b : Bool) (c r : ℝ) :
    signed b (c * r) = c * signed b r := by
  cases b <;> simp [signed]

/-- A point lies in the open cone selected by a strict sign vector. -/
def Realizes {I : Type*} (n : I → Vec3) (s : I → Bool) (x : Vec3) : Prop :=
  ∀ i, 0 < signed (s i) (n i ⬝ᵥ x)

def Realizable {I : Type*} (n : I → Vec3) (s : I → Bool) : Prop :=
  ∃ x, Realizes n s x

/-- The same chamber represented on the unit sphere. -/
def SphereRealizable {I : Type*} (n : I → Vec3) (s : I → Bool) : Prop :=
  ∃ x, norm3 x = 1 ∧ Realizes n s x

def ExtensionRealizable {I : Type*}
    (n : I → Vec3) (h : Vec3) (s : I → Bool) (b : Bool) : Prop :=
  ∃ x, Realizes n s x ∧ 0 < signed b (h ⬝ᵥ x)

/-- Feasibility of `s` on the new hyperplane itself. -/
def RestrictedRealizable {I : Type*}
    (n : I → Vec3) (h : Vec3) (s : I → Bool) : Prop :=
  ∃ x, Realizes n s x ∧ h ⬝ᵥ x = 0

def antipodalSign {I : Type*} (s : I → Bool) : I → Bool := fun i ↦ !(s i)

lemma antipodalSign_antipodalSign {I : Type*} (s : I → Bool) :
    antipodalSign (antipodalSign s) = s := by
  funext i
  simp [antipodalSign]

lemma signed_not_neg (b : Bool) (r : ℝ) :
    signed (!b) (-r) = signed b r := by
  cases b <;> simp [signed]

lemma realizes_antipodalSign_neg_iff {I : Type*}
    (n : I → Vec3) (s : I → Bool) (x : Vec3) :
    Realizes n (antipodalSign s) (-x) ↔ Realizes n s x := by
  constructor <;> intro hx i
  · simpa [antipodalSign, signed_not_neg] using hx i
  · simpa [antipodalSign, signed_not_neg] using hx i

lemma realizable_antipodalSign_iff {I : Type*}
    (n : I → Vec3) (s : I → Bool) :
    Realizable n (antipodalSign s) ↔ Realizable n s := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨-x, ?_⟩
    have h := (realizes_antipodalSign_neg_iff n (antipodalSign s) x).mpr hx
    rw [antipodalSign_antipodalSign] at h
    exact h
  · rintro ⟨x, hx⟩
    exact ⟨-x, (realizes_antipodalSign_neg_iff n s x).mpr hx⟩

lemma antipodalSign_ne {I : Type*} [Nonempty I] (s : I → Bool) :
    antipodalSign s ≠ s := by
  intro h
  let i : I := Classical.choice inferInstance
  have hi := congrFun h i
  cases hs : s i <;> simp [antipodalSign, hs] at hi

lemma sphereRealizable_iff_realizable {I : Type*} [Nonempty I]
    (n : I → Vec3) (s : I → Bool) :
    SphereRealizable n s ↔ Realizable n s := by
  constructor
  · rintro ⟨x, -, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    have hxne : x ≠ 0 := by
      intro hzero
      let i : I := Classical.choice inferInstance
      have hi := hx i
      rw [hzero, dotProduct_zero] at hi
      cases hs : s i <;> simp [signed, hs] at hi
    have hnorm : 0 < norm3 x := by
      exact norm_pos_iff.mpr (by simpa [norm3] using hxne)
    let c : ℝ := (norm3 x)⁻¹
    let y : Vec3 := c • x
    refine ⟨y, ?_, ?_⟩
    · simp only [y, norm3, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr hnorm)]
      change (norm3 x)⁻¹ * norm3 x = 1
      exact inv_mul_cancel₀ hnorm.ne'
    · intro i
      have hc : 0 < c := inv_pos.mpr hnorm
      simp only [y, dotProduct_smul, smul_eq_mul, signed_mul]
      exact mul_pos hc (hx i)

lemma exists_pos_forall_abs_mul_lt_finset {I : Type*}
    (t : Finset I) (a b : I → ℝ) (ha : ∀ i ∈ t, 0 < a i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i ∈ t, |b i| * c < a i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert i t hi ih =>
      obtain ⟨c, hc, hct⟩ := ih (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
      obtain ⟨d, hd, hdi⟩ := exists_pos_mul_lt (ha i (by simp)) |b i|
      refine ⟨min c d, lt_min hc hd, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact (mul_le_mul_of_nonneg_left (min_le_right c d) (abs_nonneg _)).trans_lt hdi
      · exact (mul_le_mul_of_nonneg_left (min_le_left c d) (abs_nonneg _)).trans_lt
          (hct j hj)

/-- Strict signs survive a sufficiently small perturbation in either direction. -/
lemma exists_small_perturbation {I : Type*} [Fintype I]
    (n : I → Vec3) (s : I → Bool) {x : Vec3}
    (hx : Realizes n s x) (v : Vec3) :
    ∃ c : ℝ, 0 < c ∧ Realizes n s (x + c • v) ∧ Realizes n s (x - c • v) := by
  classical
  obtain ⟨c, hc, hbound⟩ := exists_pos_forall_abs_mul_lt_finset
    (Finset.univ : Finset I)
    (fun i ↦ signed (s i) (n i ⬝ᵥ x))
    (fun i ↦ signed (s i) (n i ⬝ᵥ v))
    (fun i _ ↦ hx i)
  refine ⟨c, hc, ?_, ?_⟩
  · intro i
    have hb := hbound i (Finset.mem_univ i)
    have hmul :
        -|signed (s i) (n i ⬝ᵥ v)| * c ≤ signed (s i) (n i ⬝ᵥ v) * c := by
      have := neg_abs_le (signed (s i) (n i ⬝ᵥ v))
      nlinarith
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, signed_add, signed_mul]
    nlinarith
  · intro i
    have hb := hbound i (Finset.mem_univ i)
    have hmul :
        signed (s i) (n i ⬝ᵥ v) * c ≤ |signed (s i) (n i ⬝ᵥ v)| * c := by
      have := le_abs_self (signed (s i) (n i ⬝ᵥ v))
      nlinarith
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, signed_sub, signed_mul]
    nlinarith

lemma dotProduct_self_pos {h : Vec3} (hh : h ≠ 0) : 0 < h ⬝ᵥ h := by
  have hnonneg : 0 ≤ h ⬝ᵥ h := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i hi ↦ mul_self_nonneg (h i)
  have hne : h ⬝ᵥ h ≠ 0 := fun hz ↦ hh (dotProduct_self_eq_zero.mp hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

lemma realizable_iff_extension_true_or_false {I : Type*} [Fintype I]
    (n : I → Vec3) {h : Vec3} (hh : h ≠ 0) (s : I → Bool) :
    Realizable n s ↔
      ExtensionRealizable n h s true ∨ ExtensionRealizable n h s false := by
  constructor
  · rintro ⟨x, hx⟩
    rcases lt_trichotomy (h ⬝ᵥ x) 0 with hneg | hzero | hpos
    · right
      exact ⟨x, hx, by simpa [signed] using hneg⟩
    · obtain ⟨c, hc, hplus, -⟩ := exists_small_perturbation n s hx h
      left
      refine ⟨x + c • h, hplus, ?_⟩
      have hself := dotProduct_self_pos hh
      simp [signed, dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith
    · left
      exact ⟨x, hx, by simpa [signed] using hpos⟩
  · rintro (⟨x, hx, -⟩ | ⟨x, hx, -⟩) <;> exact ⟨x, hx⟩

/-- A chamber is split by the inserted hyperplane exactly when its old signs
are feasible on that hyperplane. -/
lemma restrictedRealizable_iff_extensions_true_and_false
    {I : Type*} [Fintype I]
    (n : I → Vec3) {h : Vec3} (hh : h ≠ 0) (s : I → Bool) :
    RestrictedRealizable n h s ↔
      ExtensionRealizable n h s true ∧ ExtensionRealizable n h s false := by
  constructor
  · rintro ⟨x, hx, hxzero⟩
    obtain ⟨c, hc, hplus, hminus⟩ := exists_small_perturbation n s hx h
    have hself := dotProduct_self_pos hh
    constructor
    · refine ⟨x + c • h, hplus, ?_⟩
      simp [signed, dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith
    · refine ⟨x - c • h, hminus, ?_⟩
      simp [signed, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      nlinarith
  · rintro ⟨⟨xp, hxp, hp⟩, ⟨xm, hxm, hm⟩⟩
    have hp' : 0 < h ⬝ᵥ xp := by simpa [signed] using hp
    have hm' : h ⬝ᵥ xm < 0 := by simpa [signed] using hm
    let a : ℝ := h ⬝ᵥ xp
    let b : ℝ := h ⬝ᵥ xm
    have ha : 0 < a := hp'
    have hb : b < 0 := hm'
    have hden : 0 < a - b := by linarith
    let alpha : ℝ := -b / (a - b)
    let beta : ℝ := a / (a - b)
    have halpha : 0 < alpha := div_pos (neg_pos.mpr hb) hden
    have hbeta : 0 < beta := div_pos ha hden
    let z : Vec3 := alpha • xp + beta • xm
    refine ⟨z, ?_, ?_⟩
    · intro i
      simp only [z, dotProduct_add, dotProduct_smul, smul_eq_mul,
        signed_add, signed_mul]
      nlinarith [hxp i, hxm i]
    · simp only [z, dotProduct_add, dotProduct_smul, smul_eq_mul]
      change alpha * a + beta * b = 0
      dsimp only [alpha, beta]
      field_simp
      ring

noncomputable def facePatterns {I : Type*} [Fintype I]
    (n : I → Vec3) : Finset (I → Bool) := by
  classical
  exact Finset.univ.filter (Realizable n)

noncomputable def restrictedFacePatterns {I : Type*} [Fintype I]
    (n : I → Vec3) (h : Vec3) : Finset (I → Bool) := by
  classical
  exact Finset.univ.filter (RestrictedRealizable n h)

noncomputable def extensionFacePatterns {I : Type*} [Fintype I]
    (n : I → Vec3) (h : Vec3) : Finset ((I → Bool) × Bool) := by
  classical
  exact Finset.univ.filter fun p ↦ ExtensionRealizable n h p.1 p.2

noncomputable def faceCount {I : Type*} [Fintype I] (n : I → Vec3) : ℕ :=
  (facePatterns n).card

noncomputable def restrictedFaceCount {I : Type*} [Fintype I]
    (n : I → Vec3) (h : Vec3) : ℕ :=
  (restrictedFacePatterns n h).card

noncomputable def extensionFaceCount {I : Type*} [Fintype I]
    (n : I → Vec3) (h : Vec3) : ℕ :=
  (extensionFacePatterns n h).card

/-- Algebraic hyperplane-insertion recurrence for strict sign-vector faces. -/
theorem extensionFaceCount_eq_add_restrictedFaceCount
    {I : Type*} [Fintype I] (n : I → Vec3) {h : Vec3} (hh : h ≠ 0) :
    extensionFaceCount n h = faceCount n + restrictedFaceCount n h := by
  classical
  have hpoint (s : I → Bool) :
      (if ExtensionRealizable n h s true then 1 else 0) +
          (if ExtensionRealizable n h s false then 1 else 0) =
        (if Realizable n s then 1 else 0) +
          (if RestrictedRealizable n h s then 1 else 0) := by
    rw [realizable_iff_extension_true_or_false n hh s,
      restrictedRealizable_iff_extensions_true_and_false n hh s]
    by_cases hp : ExtensionRealizable n h s true <;>
      by_cases hm : ExtensionRealizable n h s false <;> simp [hp, hm]
  simp only [extensionFaceCount, extensionFacePatterns, faceCount, facePatterns,
    restrictedFaceCount, restrictedFacePatterns, Finset.card_filter]
  calc
    (∑ p ∈ (Finset.univ : Finset ((I → Bool) × Bool)),
        if ExtensionRealizable n h p.1 p.2 then 1 else 0) =
        ∑ s : I → Bool, ∑ b : Bool,
          if ExtensionRealizable n h s b then 1 else 0 := by
            rw [← Finset.univ_product_univ]
            exact Finset.sum_product _ _ _
    _ = ∑ s : I → Bool,
        ((if ExtensionRealizable n h s true then 1 else 0) +
          (if ExtensionRealizable n h s false then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [Fintype.sum_bool]
    _ = ∑ s : I → Bool,
        ((if Realizable n s then 1 else 0) +
          (if RestrictedRealizable n h s then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact hpoint s
    _ = (∑ s : I → Bool, if Realizable n s then 1 else 0) +
          ∑ s : I → Bool, if RestrictedRealizable n h s then 1 else 0 := by
            exact Finset.sum_add_distrib

def insertNormal {I : Type*} (n : I → Vec3) (h : Vec3) : Option I → Vec3
  | none => h
  | some i => n i

def optionSignEquiv {I : Type*} : (Option I → Bool) ≃ (I → Bool) × Bool where
  toFun s := (fun i ↦ s (some i), s none)
  invFun p
    | none => p.2
    | some i => p.1 i
  left_inv s := by funext i; cases i <;> rfl
  right_inv p := by ext <;> rfl

lemma realizable_insertNormal_iff_extensionRealizable
    {I : Type*} (n : I → Vec3) (h : Vec3) (s : Option I → Bool) :
    Realizable (insertNormal n h) s ↔
      ExtensionRealizable n h (optionSignEquiv s).1 (optionSignEquiv s).2 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (fun i ↦ hx (some i)), hx none⟩
  · rintro ⟨x, hx, hhx⟩
    refine ⟨x, fun i ↦ ?_⟩
    cases i with
    | none => exact hhx
    | some i => exact hx i

theorem faceCount_insertNormal_eq_extensionFaceCount
    {I : Type*} [Fintype I] (n : I → Vec3) (h : Vec3) :
    faceCount (insertNormal n h) = extensionFaceCount n h := by
  classical
  have hmap :
      extensionFacePatterns n h =
        (facePatterns (insertNormal n h)).map optionSignEquiv.toEmbedding := by
    ext p
    constructor
    · intro hp
      have hp' : ExtensionRealizable n h p.1 p.2 := by
        simpa [extensionFacePatterns] using hp
      refine Finset.mem_map.mpr ⟨optionSignEquiv.symm p, ?_, ?_⟩
      · simp only [facePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (realizable_insertNormal_iff_extensionRealizable n h _).mpr (by
          simpa using hp')
      · exact optionSignEquiv.apply_symm_apply p
    · intro hp
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hp
      simp only [extensionFacePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (realizable_insertNormal_iff_extensionRealizable n h s).mp (by
        simpa [facePatterns] using hs)
  simp only [faceCount, extensionFaceCount]
  rw [hmap, Finset.card_map]

/-- Deletion--restriction for insertion of a nonzero central hyperplane. -/
theorem faceCount_insertNormal
    {I : Type*} [Fintype I] (n : I → Vec3) {h : Vec3} (hh : h ≠ 0) :
    faceCount (insertNormal n h) = faceCount n + restrictedFaceCount n h := by
  rw [faceCount_insertNormal_eq_extensionFaceCount]
  exact extensionFaceCount_eq_add_restrictedFaceCount n hh

lemma antipodalSign_mem_facePatterns_iff
    {I : Type*} [Fintype I] (n : I → Vec3) (s : I → Bool) :
    antipodalSign s ∈ facePatterns n ↔ s ∈ facePatterns n := by
  classical
  simp only [facePatterns, Finset.mem_filter, Finset.mem_univ, true_and]
  exact realizable_antipodalSign_iff n s

theorem faceCount_empty :
    faceCount (fun i : Fin 0 ↦ Fin.elim0 i) = 1 := by
  classical
  have hall (s : Fin 0 → Bool) :
      Realizable (fun i : Fin 0 ↦ Fin.elim0 i) s :=
    ⟨0, fun i ↦ Fin.elim0 i⟩
  rw [faceCount, show facePatterns (fun i : Fin 0 ↦ Fin.elim0 i) = Finset.univ by
    ext s
    constructor
    · intro hs
      exact Finset.mem_univ s
    · intro hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hall s⟩]
  simp

theorem restrictedFaceCount_empty (h : Vec3) :
    restrictedFaceCount (fun i : Fin 0 ↦ Fin.elim0 i) h = 1 := by
  classical
  have hall (s : Fin 0 → Bool) :
      RestrictedRealizable (fun i : Fin 0 ↦ Fin.elim0 i) h s :=
    ⟨0, (fun i ↦ Fin.elim0 i), by simp⟩
  rw [restrictedFaceCount,
    show restrictedFacePatterns (fun i : Fin 0 ↦ Fin.elim0 i) h = Finset.univ by
      ext s
      constructor
      · intro hs
        exact Finset.mem_univ s
      · intro hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hall s⟩]
  simp

theorem faceCount_singleton {h : Vec3} (hh : h ≠ 0) :
    faceCount (insertNormal (fun i : Fin 0 ↦ Fin.elim0 i) h) = 2 := by
  rw [faceCount_insertNormal (fun i : Fin 0 ↦ Fin.elim0 i) hh,
    faceCount_empty, restrictedFaceCount_empty]

/-- If insertion creates `u` vertices and `u + restrictedFaceCount n h` edges,
deletion--restriction supplies exactly the face increment preserving Euler's equation. -/
theorem euler_invariant_under_hyperplane_insertion
    {I : Type*} [Fintype I] (n : I → Vec3) {h : Vec3} (hh : h ≠ 0)
    (v e u : ℕ) (hEuler : v + faceCount n = e + 2) :
    (v + u) + faceCount (insertNormal n h) =
      (e + u + restrictedFaceCount n h) + 2 := by
  rw [faceCount_insertNormal n hh]
  omega

end SignVector
end Erdos735
