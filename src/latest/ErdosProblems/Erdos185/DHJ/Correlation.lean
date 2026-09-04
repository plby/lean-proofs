/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos185.DHJ.Cube
import ErdosProblems.Erdos185.DHJ.Density
import ErdosProblems.Erdos185.DHJ.GrahamRothschildTwo
import ErdosProblems.Erdos185.DHJ.Uniformity
import ErdosProblems.Erdos171.StructuredCorrelation

/-!
# The correlation step for ternary density Hales--Jewett

This file contains the finite, quantitative part of the Dodos--Kanellopoulos--Tyros
argument which turns many binary lines into correlation with the intersection of
two insensitive sets.  The density `alpha` of the set being studied is always
kept separate from the fixed lower density floor in `CorrelationConstants`.
-/

open scoped BigOperators

namespace Erdos185.DHJ

open Combinatorics

/-! ## Constants -/

/-- Constants used throughout one ternary correlation argument.  In the DKT
proof `delta` is a fixed lower bound for the current density, while `theta`
comes from binary density Hales--Jewett and line counting. -/
structure CorrelationConstants where
  delta : ℝ
  theta : ℝ
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1

namespace CorrelationConstants

/-- The uniformity error used in the correlated-section argument. -/
noncomputable def eta (p : CorrelationConstants) : ℝ := p.delta * p.theta / 48

/-- The additive correlation increment. -/
noncomputable def gamma (p : CorrelationConstants) : ℝ := p.delta * p.eta ^ 2 / 2

theorem delta_nonneg (p : CorrelationConstants) : 0 ≤ p.delta := p.delta_pos.le

theorem theta_nonneg (p : CorrelationConstants) : 0 ≤ p.theta := p.theta_pos.le

theorem eta_pos (p : CorrelationConstants) : 0 < p.eta := by
  unfold eta
  exact div_pos (mul_pos p.delta_pos p.theta_pos) (by norm_num)

theorem eta_nonneg (p : CorrelationConstants) : 0 ≤ p.eta := p.eta_pos.le

theorem eta_le_one (p : CorrelationConstants) : p.eta ≤ 1 := by
  unfold eta
  nlinarith [p.delta_pos, p.delta_le_one, p.theta_pos, p.theta_le_one]

theorem eta_lt_theta_div_two (p : CorrelationConstants) : p.eta < p.theta / 2 := by
  unfold eta
  nlinarith [p.delta_pos, p.delta_le_one, p.theta_pos]

theorem gamma_pos (p : CorrelationConstants) : 0 < p.gamma := by
  unfold gamma
  exact div_pos (mul_pos p.delta_pos (pow_pos p.eta_pos 2)) (by norm_num)

theorem gamma_nonneg (p : CorrelationConstants) : 0 ≤ p.gamma := p.gamma_pos.le

theorem gamma_le_eta_div_two (p : CorrelationConstants) : p.gamma ≤ p.eta / 2 := by
  unfold gamma
  have he0 := p.eta_nonneg
  have he1 := p.eta_le_one
  nlinarith [p.delta_nonneg, p.delta_le_one]

theorem gamma_le_eta_sq_div_two (p : CorrelationConstants) :
    p.gamma ≤ p.eta ^ 2 / 2 := by
  unfold gamma
  nlinarith [sq_nonneg p.eta, p.delta_nonneg, p.delta_le_one]

theorem eta_le_delta (p : CorrelationConstants) : p.eta ≤ p.delta := by
  unfold eta
  nlinarith [p.delta_nonneg, p.theta_nonneg, p.theta_le_one]

theorem eta_sq_div_two_le_delta_div_two (p : CorrelationConstants) :
    p.eta ^ 2 / 2 ≤ p.delta / 2 := by
  have he0 := p.eta_nonneg
  have he1 := p.eta_le_one
  have hed := p.eta_le_delta
  nlinarith

theorem twelve_eta (p : CorrelationConstants) :
    12 * p.eta = p.delta * p.theta / 4 := by
  unfold eta
  ring

end CorrelationConstants

/-- The fixed binary-DHJ witness used to choose `theta`.  A
`CorrelationSystem` is chosen once from the density floor, before any target
dimension is requested; consequently its `eta` and `gamma` are uniform over
the whole density-increment iteration. -/
structure CorrelationSystem where
  constants : CorrelationConstants
  m0 : ℕ
  m0_pos : 0 < m0
  binary_dhj : ∀ B : Finset (Word 2 m0),
    constants.delta / 4 ≤ density B → HasLine B
  theta_mul_lineCount :
    constants.theta * (Fintype.card (Line (Fin 2) (Fin m0)) : ℝ) =
      constants.delta / 4

namespace CorrelationSystem

/-- Binary density Hales--Jewett supplies one correlation system for every
positive density floor at most one. -/
theorem exists_of_delta (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ s : CorrelationSystem, s.constants.delta = delta := by
  obtain ⟨N, hN⟩ :=
    Erdos171.exists_containsLine_of_dense_binary_finset (delta / 4) (by positivity)
  let m0 := N + 1
  let L : ℝ := Fintype.card (Line (Fin 2) (Fin m0))
  have hm0 : 0 < m0 := by simp [m0]
  let : Nonempty (Line (Fin 2) (Fin m0)) := by
    let l : Line (Fin 2) (Fin m0) :=
      { idxFun := fun _ ↦ none
        proper := ⟨⟨0, hm0⟩, rfl⟩ }
    exact ⟨l⟩
  have hLpos : 0 < L := by
    dsimp only [L]
    positivity
  have hLone : 1 ≤ L := by
    have hnat : 1 ≤ Fintype.card (Line (Fin 2) (Fin m0)) :=
      Fintype.card_pos_iff.mpr inferInstance
    dsimp only [L]
    exact_mod_cast hnat
  let theta := (delta / 4) / L
  have htheta : 0 < theta := by
    dsimp only [theta]
    positivity
  have htheta1 : theta ≤ 1 := by
    have hdelta4 : delta / 4 ≤ 1 := by linarith
    dsimp only [theta]
    calc
      delta / 4 / L ≤ delta / 4 / 1 := by
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hLone
      _ ≤ 1 := by simpa using hdelta4
  let p : CorrelationConstants :=
    { delta := delta
      theta := theta
      delta_pos := hdelta
      delta_le_one := hdelta1
      theta_pos := htheta
      theta_le_one := htheta1 }
  refine ⟨{
    constants := p
    m0 := m0
    m0_pos := hm0
    binary_dhj := ?_
    theta_mul_lineCount := ?_ }, rfl⟩
  · intro B hB
    apply (hasLine_iff_containsLine B).2
    apply hN m0 (by simp [m0]) B
    have hden : delta / 4 ≤ (B.card : ℝ) / (2 : ℝ) ^ m0 := by
      simpa [density, Word] using hB
    exact (le_div_iff₀ (by positivity)).mp hden
  · dsimp only [p]
    change theta * L = delta / 4
    dsimp only [theta]
    exact div_mul_cancel₀ _ hLpos.ne'

end CorrelationSystem

/-! ## Elementary density identities -/

section DensityLattice

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem density_sdiff_add_density_inter' (A B : Finset X) :
    density (A \ B) + density (A ∩ B) = density A := by
  simp only [density_eq_card_div_card]
  rw [← add_div, ← Nat.cast_add, Finset.card_sdiff_add_card_inter]

theorem density_union_add_density_inter' (A B : Finset X) :
    density (A ∪ B) + density (A ∩ B) = density A + density B := by
  simp only [density_eq_card_div_card]
  rw [← add_div, ← add_div, ← Nat.cast_add, ← Nat.cast_add,
    Finset.card_union_add_card_inter]

theorem density_inter_le_left' (A B : Finset X) : density (A ∩ B) ≤ density A :=
  density_mono Finset.inter_subset_left

theorem density_inter_le_right' (A B : Finset X) : density (A ∩ B) ≤ density B :=
  density_mono Finset.inter_subset_right

theorem density_compl' [Nonempty X] (A : Finset X) :
    density (Finset.univ \ A) = 1 - density A := by
  have h := density_sdiff_add_density_inter' (Finset.univ : Finset X) A
  simp only [Finset.univ_inter, density_univ] at h
  linarith

end DensityLattice

/-! ## Binary lines and their ternary completion -/

section Completion

/-- Binary lines whose two binary points belong to a ternary set. -/
noncomputable def goodBinaryLines {m : ℕ} (A : Finset (Word 3 m)) :
    Finset (Line (Fin 2) (Fin m)) := by
  classical
  exact Finset.univ.filter fun l ↦
    ∀ i : Fin 2, Erdos171.restrictWord (l i) ∈ A

@[simp] theorem mem_goodBinaryLines {m : ℕ} (A : Finset (Word 3 m))
    (l : Line (Fin 2) (Fin m)) :
    l ∈ goodBinaryLines A ↔
      ∀ i : Fin 2, Erdos171.restrictWord (l i) ∈ A := by
  classical
  simp [goodBinaryLines]

/-- The canonical completion map from binary lines to ternary words is
injective: the ternary word remembers the entire line template. -/
theorem templateEndpoint_injective (m : ℕ) :
    Function.Injective
      (Erdos171.templateEndpoint : Line (Fin 2) (Fin m) → Word 3 m) := by
  intro l r hlr
  apply Line.ext
  funext i
  apply finSuccEquivLast.symm.injective
  exact congrFun hlr i

/-- The ternary words which use only the first two letters. -/
noncomputable def binaryImage (m : ℕ) : Finset (Word 3 m) := by
  classical
  exact Finset.univ.image Erdos171.restrictWord

@[simp] theorem mem_binaryImage {m : ℕ} (x : Word 3 m) :
    x ∈ binaryImage m ↔ Erdos171.IsRestrictedWord x := by
  classical
  rw [binaryImage, Finset.mem_image]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact fun i ↦ Fin.castSucc_ne_last (y i)
  · intro hx
    obtain ⟨y, rfl⟩ :=
      (Set.ext_iff.1 Erdos171.range_restrictWord x).2 hx
    exact ⟨y, Finset.mem_univ _, rfl⟩

@[simp] theorem card_binaryImage (m : ℕ) : (binaryImage m).card = 2 ^ m := by
  classical
  rw [binaryImage, Finset.card_image_of_injective _ Erdos171.restrictWord_injective]
  simp [Erdos171.card_word]

theorem density_binaryImage (m : ℕ) :
    density (binaryImage m) = (2 : ℝ) ^ m / (3 : ℝ) ^ m := by
  rw [density_eq_card_div_card, card_binaryImage]
  simp [Erdos171.card_word]

/-- Finset version of the insensitive cylinder generated by a binary set. -/
noncomputable def endpointCylinderFinset {m : ℕ} (i : Fin 2)
    (B : Finset (Word 2 m)) : Finset (Word 3 m) := by
  classical
  exact Finset.univ.filter fun x ↦ Erdos171.endpoint i x ∈ B

@[simp] theorem mem_endpointCylinderFinset {m : ℕ} (i : Fin 2)
    (B : Finset (Word 2 m)) (x : Word 3 m) :
    x ∈ endpointCylinderFinset i B ↔ Erdos171.endpoint i x ∈ B := by
  classical
  simp [endpointCylinderFinset]

theorem endpointCylinderFinset_isLastInsensitive {m : ℕ} (i : Fin 2)
    (B : Finset (Word 2 m)) :
    Erdos171.IsLastInsensitive i
      (endpointCylinderFinset i B : Set (Word 3 m)) := by
  intro x y hxy
  change (x ∈ endpointCylinderFinset i B ↔ y ∈ endpointCylinderFinset i B)
  rw [mem_endpointCylinderFinset, mem_endpointCylinderFinset]
  exact Erdos171.endpointCylinder_isLastInsensitive i
    (B : Set (Word 2 m)) x y hxy

/-- The intersection of the two endpoint cylinders attached to the binary
part of `A`. -/
noncomputable def completionCore {m : ℕ} (A : Finset (Word 3 m)) :
    Finset (Word 3 m) :=
  endpointCylinderFinset 0 (binaryPart A) ∩
    endpointCylinderFinset 1 (binaryPart A)

@[simp] theorem mem_completionCore {m : ℕ} (A : Finset (Word 3 m))
    (x : Word 3 m) :
    x ∈ completionCore A ↔
      Erdos171.restrictWord (Erdos171.endpoint 0 x) ∈ A ∧
      Erdos171.restrictWord (Erdos171.endpoint 1 x) ∈ A := by
  simp [completionCore, binaryPart]

theorem templateEndpoint_mem_completionCore_iff {m : ℕ}
    (A : Finset (Word 3 m)) (l : Line (Fin 2) (Fin m)) :
    Erdos171.templateEndpoint l ∈ completionCore A ↔ l ∈ goodBinaryLines A := by
  simp only [mem_completionCore, Erdos171.endpoint_templateEndpoint,
    mem_goodBinaryLines]
  constructor
  · intro h i
    refine Fin.cases h.1 (fun j ↦ ?_) i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact h.2
  · intro h
    exact ⟨h 0, h 1⟩

/-- Completing good binary lines injects them into the completion core. -/
theorem card_goodBinaryLines_le_completionCore {m : ℕ}
    (A : Finset (Word 3 m)) :
    (goodBinaryLines A).card ≤ (completionCore A).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (f := Erdos171.templateEndpoint) ?_ ?_
  · intro l hl
    exact (templateEndpoint_mem_completionCore_iff A l).2 hl
  · exact (templateEndpoint_injective m).injOn

/-- Replacing the wildcards in `endpointLine x hx` by the new last letter
recovers `x`. -/
theorem templateEndpoint_endpointLine {m : ℕ} (x : Word 3 m)
    (hx : ∃ r, x r = Fin.last 2) :
    Erdos171.templateEndpoint (Erdos171.endpointLine x hx) = x :=
  Erdos171.templateEndpoint_endpointLine x hx

/-- In a line-free set, a point of the completion core that also lies in the
set must be a binary point. -/
theorem inter_completionCore_subset_binaryImage {m : ℕ}
    {A : Finset (Word 3 m)} (hline : ¬ HasLine A) :
    A ∩ completionCore A ⊆ binaryImage m := by
  intro x hx
  obtain ⟨hxA, hxCore⟩ := Finset.mem_inter.mp hx
  rw [mem_binaryImage]
  by_contra hrestricted
  simp only [Erdos171.IsRestrictedWord, not_forall, not_not] at hrestricted
  obtain ⟨r, hr⟩ := hrestricted
  have hxcore := (mem_completionCore A x).1 hxCore
  let l : Line (Fin 2) (Fin m) := Erdos171.endpointLine x ⟨r, hr⟩
  apply hline
  refine ⟨Erdos171.templateExtension l, ?_⟩
  intro a
  refine Fin.lastCases ?_ (fun i ↦ ?_) a
  · rw [Erdos171.templateExtension_last]
    simpa only [l, templateEndpoint_endpointLine x ⟨r, hr⟩] using hxA
  · rw [Erdos171.templateExtension_castSucc]
    cases i using Fin.cases with
    | zero =>
        simpa [l, Erdos171.endpointLine_apply] using hxcore.1
    | succ i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa [l, Erdos171.endpointLine_apply] using hxcore.2

/-- Line-freeness bounds the mass of `A` in its completion core by the mass
of the binary slice. -/
theorem density_inter_completionCore_le {m : ℕ}
    {A : Finset (Word 3 m)} (hline : ¬ HasLine A) :
    density (A ∩ completionCore A) ≤ (2 : ℝ) ^ m / (3 : ℝ) ^ m := by
  calc
    density (A ∩ completionCore A) ≤ density (binaryImage m) :=
      density_mono (inter_completionCore_subset_binaryImage hline)
    _ = _ := density_binaryImage m

end Completion

/-! ## Correlated sections and the many-lines dichotomy -/

section CorrelatedSections

variable {Y : Type*} [Fintype Y] [Nonempty Y]

/-- Swap the factors of a finite subset of a product.  This local name avoids
coupling the correlation argument to the suffix-section endgame. -/
noncomputable def transposeProductFinset {X Z : Type*}
    (A : Finset (X × Z)) : Finset (Z × X) :=
  A.map (Equiv.prodComm X Z).toEmbedding

@[simp] theorem mem_transposeProductFinset {X Z : Type*}
    [DecidableEq X] [DecidableEq Z] (A : Finset (X × Z)) (z : Z) (x : X) :
    (z, x) ∈ transposeProductFinset A ↔ (x, z) ∈ A := by
  classical
  rw [transposeProductFinset, Finset.mem_map]
  constructor
  · rintro ⟨⟨x', z'⟩, hxz, heq⟩
    simp only [Equiv.coe_toEmbedding, Equiv.prodComm_apply] at heq
    cases heq
    exact hxz
  · intro hxz
    exact ⟨(x, z), hxz, rfl⟩

@[simp] theorem card_transposeProductFinset {X Z : Type*}
    [DecidableEq X] [DecidableEq Z] (A : Finset (X × Z)) :
    (transposeProductFinset A).card = A.card := by
  simp [transposeProductFinset]

/-- Section of a product set obtained by fixing its second coordinate. -/
noncomputable def tailSlice {X Z : Type*} [Fintype X]
    (A : Finset (X × Z)) (z : Z) : Finset X :=
  fiber (transposeProductFinset A) z

@[simp] theorem mem_tailSlice {X Z : Type*} [Fintype X]
    [DecidableEq Z] (A : Finset (X × Z)) (z : Z) (x : X) :
    x ∈ tailSlice A z ↔ (x, z) ∈ A := by
  classical
  rw [tailSlice, mem_fiber, mem_transposeProductFinset]

/-- Density is also the average of the sections obtained by fixing the
second product coordinate. -/
theorem density_eq_average_tailSlice {X Z : Type*}
    [Fintype X] [Nonempty X] [Fintype Z] [Nonempty Z]
    (A : Finset (X × Z)) :
    density A = average fun z : Z ↦ density (tailSlice A z) := by
  classical
  let B : Finset (Z × X) := transposeProductFinset A
  have hB : density B = density A := by
    simp [B, density, Fintype.card_prod, mul_comm]
  rw [← hB, density_eq_average_fiber]
  rfl

/-- Pull a product set back in its first coordinate through a subspace. -/
noncomputable def prefixPullbackProduct {d n : ℕ} {α Z : Type*}
    [Fintype α] [Fintype Z]
    (U : Subspace (Fin d) α (Fin n)) (A : Finset ((Fin n → α) × Z)) :
    Finset ((Fin d → α) × Z) := by
  classical
  exact Finset.univ.filter fun p ↦ (U p.1, p.2) ∈ A

@[simp] theorem mem_prefixPullbackProduct {d n : ℕ} {α Z : Type*}
    [Fintype α] [Fintype Z]
    (U : Subspace (Fin d) α (Fin n)) (A : Finset ((Fin n → α) × Z))
    (x : Fin d → α) (z : Z) :
    (x, z) ∈ prefixPullbackProduct U A ↔ (U x, z) ∈ A := by
  classical
  simp [prefixPullbackProduct]

@[simp] theorem fiber_prefixPullbackProduct {d n : ℕ} {α Z : Type*}
    [Fintype α] [Fintype Z]
    (U : Subspace (Fin d) α (Fin n)) (A : Finset ((Fin n → α) × Z))
    (x : Fin d → α) :
    fiber (prefixPullbackProduct U A) x = fiber A (U x) := by
  classical
  ext z
  simp

@[simp] theorem tailSlice_prefixPullbackProduct {d n : ℕ} {α Z : Type*}
    [Fintype α] [Fintype Z] [DecidableEq Z]
    (U : Subspace (Fin d) α (Fin n)) (A : Finset ((Fin n → α) × Z)) (z : Z) :
    tailSlice (prefixPullbackProduct U A) z =
      pullbackFinset U (tailSlice A z) := by
  classical
  ext x
  simp

@[simp] theorem finLift_apply_restrictWord {d n : ℕ}
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (x : Word 2 d) :
    U.finLift (Erdos171.restrictWord x) = Erdos171.restrictWord (U x) := by
  calc
    U.finLift (Erdos171.restrictWord x) =
        U.finLift (Erdos171.liftWord x) := by rfl
    _ = Erdos171.liftWord (U x) := U.finLift_apply x
    _ = Erdos171.restrictWord (U x) := by rfl

/-- Restrict both the parameter and fixed alphabets of a binary subspace to
the binary part of a ternary product set. -/
noncomputable def binaryPrefixPullbackProduct {d n : ℕ} {Z : Type*}
    [Fintype Z]
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (A : Finset (Word 3 n × Z)) :
    Finset (Word 2 d × Z) := by
  classical
  exact Finset.univ.filter fun p ↦
    (Erdos171.restrictWord (U p.1), p.2) ∈ A

@[simp] theorem mem_binaryPrefixPullbackProduct {d n : ℕ} {Z : Type*}
    [Fintype Z]
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (A : Finset (Word 3 n × Z))
    (x : Word 2 d) (z : Z) :
    (x, z) ∈ binaryPrefixPullbackProduct U A ↔
      (Erdos171.restrictWord (U x), z) ∈ A := by
  classical
  simp [binaryPrefixPullbackProduct]

@[simp] theorem fiber_binaryPrefixPullbackProduct {d n : ℕ} {Z : Type*}
    [Fintype Z]
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (A : Finset (Word 3 n × Z))
    (x : Word 2 d) :
    fiber (binaryPrefixPullbackProduct U A) x =
      fiber A (Erdos171.restrictWord (U x)) := by
  classical
  ext z
  simp

@[simp] theorem tailSlice_binaryPrefixPullbackProduct {d n : ℕ} {Z : Type*}
    [Fintype Z] [DecidableEq Z]
    (U : Subspace (Fin d) (Fin 2) (Fin n)) (A : Finset (Word 3 n × Z)) (z : Z) :
    tailSlice (binaryPrefixPullbackProduct U A) z =
      binaryPart (tailSlice (prefixPullbackProduct U.finLift A) z) := by
  classical
  ext x
  rw [mem_tailSlice, mem_binaryPrefixPullbackProduct]
  rw [show x ∈ binaryPart (tailSlice (prefixPullbackProduct U.finLift A) z) ↔
      Erdos171.restrictWord x ∈ tailSlice (prefixPullbackProduct U.finLift A) z by
    exact mem_restrictedPart _ _]
  rw [mem_tailSlice, mem_prefixPullbackProduct, finLift_apply_restrictWord]

/-- Tails common to the two binary endpoints of a line. -/
noncomputable def lineSectionIntersection {m : ℕ}
    (A : Finset (Word 3 m × Y)) (l : Line (Fin 2) (Fin m)) : Finset Y := by
  classical
  exact fiber A (Erdos171.restrictWord (l 0)) ∩
    fiber A (Erdos171.restrictWord (l 1))

@[simp] theorem mem_lineSectionIntersection {m : ℕ}
    (A : Finset (Word 3 m × Y)) (l : Line (Fin 2) (Fin m)) (y : Y) :
    y ∈ lineSectionIntersection A l ↔
      (Erdos171.restrictWord (l 0), y) ∈ A ∧
      (Erdos171.restrictWord (l 1), y) ∈ A := by
  simp [lineSectionIntersection]

@[simp] theorem lineSectionIntersection_prefixFinLift {m r : ℕ}
    (A : Finset (Word 3 r × Y))
    (V : Subspace (Fin m) (Fin 2) (Fin r))
    (l : Line (Fin 2) (Fin m)) :
    lineSectionIntersection (prefixPullbackProduct V.finLift A) l =
      lineSectionIntersection A (V.lineMap l) := by
  classical
  ext y
  simp only [mem_lineSectionIntersection, mem_prefixPullbackProduct,
    finLift_apply_restrictWord, Subspace.lineMap_apply]

/-- The incidence set between binary lines and tails on which both endpoints
belong to the corresponding slice. -/
noncomputable def binaryLineIncidences {m : ℕ}
    (A : Finset (Word 3 m × Y)) :
    Finset (Line (Fin 2) (Fin m) × Y) := by
  classical
  exact Finset.univ.filter fun p ↦
    p.2 ∈ lineSectionIntersection A p.1

@[simp] theorem mem_binaryLineIncidences {m : ℕ}
    (A : Finset (Word 3 m × Y)) (l : Line (Fin 2) (Fin m)) (y : Y) :
    (l, y) ∈ binaryLineIncidences A ↔
      y ∈ lineSectionIntersection A l := by
  classical
  simp [binaryLineIncidences]

@[simp] theorem fiber_binaryLineIncidences {m : ℕ}
    (A : Finset (Word 3 m × Y)) (l : Line (Fin 2) (Fin m)) :
    fiber (binaryLineIncidences A) l = lineSectionIntersection A l := by
  classical
  ext y
  simp

@[simp] theorem tailSlice_binaryLineIncidences {m : ℕ}
    (A : Finset (Word 3 m × Y)) (y : Y) :
    tailSlice (binaryLineIncidences A) y = goodBinaryLines (tailSlice A y) := by
  classical
  ext l
  rw [mem_tailSlice, mem_binaryLineIncidences, mem_goodBinaryLines]
  simp only [mem_lineSectionIntersection, mem_tailSlice]
  constructor
  · rintro ⟨h0, h1⟩ i
    refine Fin.cases h0 (fun j ↦ ?_) i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact h1
  · intro h
    exact ⟨h 0, h 1⟩

/-- Exact double-counting identity for binary-line/tail incidences. -/
theorem average_density_lineSectionIntersection_eq {m : ℕ} (hm : 0 < m)
    (A : Finset (Word 3 m × Y)) :
    average (fun l : Line (Fin 2) (Fin m) ↦
      density (lineSectionIntersection A l)) =
    average (fun y : Y ↦ density (goodBinaryLines (tailSlice A y))) := by
  let : Nonempty (Line (Fin 2) (Fin m)) := by
    let l : Line (Fin 2) (Fin m) :=
      { idxFun := fun _ ↦ none
        proper := ⟨⟨0, hm⟩, rfl⟩ }
    exact ⟨l⟩
  have hleft := density_eq_average_fiber (binaryLineIncidences A)
  have hright := density_eq_average_tailSlice (binaryLineIncidences A)
  simp only [fiber_binaryLineIncidences] at hleft
  simp only [tailSlice_binaryLineIncidences] at hright
  linarith

/-- Abstract product form of the correlated-sections conclusion.  This is the
form consumed by the many-lines averaging argument and produced by the tower
uniformization/Ramsey construction. -/
structure CorrelatedSectionData (p : CorrelationConstants) (alpha : ℝ)
    (m : ℕ) (Y : Type*) [Fintype Y] where
  points : Finset (Word 3 m × Y)
  section_dense : ∀ u : Word 3 m,
    alpha - p.eta ^ 2 / 2 ≤ density (fiber points u)
  line_dense : ∀ l : Line (Fin 2) (Fin m),
    p.theta ≤ density (lineSectionIntersection points l)

/-- Graham--Rothschild homogenization plus the fixed binary-DHJ witness turn
uniform point sections into correlated line sections.  The returned binary
subspace records the prefix embedding, which is needed later to transport a
selected tail slice back into the ambient cube. -/
theorem exists_correlatedSectionData_of_uniform
    (s : CorrelationSystem) {alpha : ℝ} {m r : ℕ} (hm : s.m0 ≤ m)
    (A : Finset (Word 3 r × Y))
    (hfloor : s.constants.delta ≤ alpha)
    (huniform : ∀ x : Word 3 r,
      alpha - s.constants.eta ^ 2 / 2 ≤ density (fiber A x))
    (hGR : ∀ c : Line (Fin 2) (Fin r) → Bool,
      ∃ V : Subspace (Fin m) (Fin 2) (Fin r), ∃ b : Bool,
        ∀ l : Line (Fin 2) (Fin m), c (V.lineMap l) = b) :
    ∃ V : Subspace (Fin m) (Fin 2) (Fin r),
      ∃ S : CorrelatedSectionData s.constants alpha m Y,
        S.points = prefixPullbackProduct V.finLift A := by
  classical
  let p := s.constants
  let color : Line (Fin 2) (Fin r) → Bool := fun l ↦
    decide (p.theta ≤ density (lineSectionIntersection A l))
  obtain ⟨V, b, hV⟩ := hGR color
  have hb : b = true := by
    cases b with
    | true => rfl
    | false =>
      exfalso
      let F : Subspace (Fin s.m0) (Fin 2) (Fin m) :=
        Subspace.coordinateFace hm
      let Z : Subspace (Fin s.m0) (Fin 2) (Fin r) := V.comp F
      let Q : Finset (Word 2 s.m0 × Y) := binaryPrefixPullbackProduct Z A
      have hQ : p.delta / 2 ≤ density Q := by
        rw [density_eq_average_fiber]
        apply const_le_average
        intro x
        rw [fiber_binaryPrefixPullbackProduct]
        have hx := huniform (Erdos171.restrictWord (Z x))
        have herror := p.eta_sq_div_two_le_delta_div_two
        dsimp only [p] at hx herror ⊢
        nlinarith
      have hQavg : p.delta / 2 ≤
          average fun y : Y ↦ density (tailSlice Q y) := by
        rwa [← density_eq_average_tailSlice]
      let H : Finset Y := superlevel
        (fun y : Y ↦ density (tailSlice Q y)) (p.delta / 4)
      have hH : p.delta / 4 ≤ density H := by
        have hh := half_le_density_superlevel
          (fun y : Y ↦ density (tailSlice Q y))
          (show 0 ≤ p.delta / 2 from
            div_nonneg p.delta_nonneg (by norm_num)) hQavg
          (fun y ↦ density_le_one (tailSlice Q y))
        simpa only [H, show p.delta / 2 / 2 = p.delta / 4 by ring] using hh
      let PZ : Finset (Word 3 s.m0 × Y) := prefixPullbackProduct Z.finLift A
      let L : ℝ := Fintype.card (Line (Fin 2) (Fin s.m0))
      let : Nonempty (Line (Fin 2) (Fin s.m0)) := by
        let l : Line (Fin 2) (Fin s.m0) :=
          { idxFun := fun _ ↦ none
            proper := ⟨⟨0, s.m0_pos⟩, rfl⟩ }
        exact ⟨l⟩
      have hLpos : 0 < L := by
        have hnat : 0 < Fintype.card (Line (Fin 2) (Fin s.m0)) := Fintype.card_pos
        dsimp only [L]
        exact_mod_cast hnat
      have hpointGood (y : Y) :
          (if y ∈ H then 1 / L else 0) ≤
            density (goodBinaryLines (tailSlice PZ y)) := by
        by_cases hy : y ∈ H
        · rw [if_pos hy]
          have hQy : p.delta / 4 ≤ density (tailSlice Q y) := by
            exact (mem_superlevel _ _ y).1 hy
          have hlineQ : HasLine (tailSlice Q y) := by
            apply s.binary_dhj
            simpa only [p] using hQy
          rw [tailSlice_binaryPrefixPullbackProduct Z A y] at hlineQ
          obtain ⟨l, hl⟩ := hlineQ
          have hlGood : l ∈ goodBinaryLines (tailSlice PZ y) := by
            apply (mem_goodBinaryLines _ l).2
            intro i
            exact (mem_restrictedPart _ (l i)).1 (hl i)
          have hcard : 1 ≤ (goodBinaryLines (tailSlice PZ y)).card :=
            Finset.one_le_card.mpr ⟨l, hlGood⟩
          rw [density_eq_card_div_card]
          change 1 / L ≤ ((goodBinaryLines (tailSlice PZ y)).card : ℝ) / L
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hLpos.le
        · rw [if_neg hy]
          exact density_nonneg _
      have havgGoodLower : density H / L ≤
          average fun y : Y ↦ density (goodBinaryLines (tailSlice PZ y)) := by
        calc
          density H / L =
              average (fun y : Y ↦ if y ∈ H then 1 / L else 0) := by
            rw [average_piecewise_const]
            ring
          _ ≤ _ := average_mono hpointGood
      have hthetaH : p.theta ≤ density H / L := by
        rw [le_div_iff₀ hLpos]
        have hcount := s.theta_mul_lineCount
        change p.theta * L = p.delta / 4 at hcount
        linarith
      have havgGood : p.theta ≤
          average fun y : Y ↦ density (goodBinaryLines (tailSlice PZ y)) :=
        hthetaH.trans havgGoodLower
      have havgInter : p.theta ≤
          average fun l : Line (Fin 2) (Fin s.m0) ↦
            density (lineSectionIntersection PZ l) := by
        rw [average_density_lineSectionIntersection_eq s.m0_pos PZ]
        exact havgGood
      obtain ⟨l, hl⟩ := exists_average_le
        (fun l : Line (Fin 2) (Fin s.m0) ↦
          density (lineSectionIntersection PZ l))
      have hgoodZ : p.theta ≤
          density (lineSectionIntersection A (Z.lineMap l)) := by
        have := havgInter.trans hl
        simpa only [PZ, lineSectionIntersection_prefixFinLift] using this
      have hhom := hV (F.lineMap l)
      have hfalse :
          decide (p.theta ≤
            density (lineSectionIntersection A (V.lineMap (F.lineMap l)))) = false := by
        simpa only [color] using hhom
      have hbad : ¬p.theta ≤
          density (lineSectionIntersection A (V.lineMap (F.lineMap l))) :=
        of_decide_eq_false hfalse
      apply hbad
      simpa only [Z, Subspace.lineMap_comp] using hgoodZ
  let P : Finset (Word 3 m × Y) := prefixPullbackProduct V.finLift A
  let S : CorrelatedSectionData p alpha m Y :=
    { points := P
      section_dense := by
        intro x
        dsimp only [P]
        rw [fiber_prefixPullbackProduct]
        exact huniform (V.finLift x)
      line_dense := by
        intro l
        dsimp only [P]
        rw [lineSectionIntersection_prefixFinLift]
        have hc := hV l
        rw [hb] at hc
        exact of_decide_eq_true (by simpa only [color] using hc) }
  exact ⟨V, S, rfl⟩

/-- The DKT many-lines dichotomy in a product cube.  Either one tail slice
already has the desired `eta²/2` increment over the actual density `alpha`,
or one tail simultaneously has density at least `alpha-2 eta` and contains a
`theta/2` fraction of all binary lines. -/
theorem manyBinaryLines_of_correlatedSections (p : CorrelationConstants)
    {alpha : ℝ} {m : ℕ} (hm : 0 < m)
    (S : CorrelatedSectionData p alpha m Y) :
    (∃ y : Y, alpha + p.eta ^ 2 / 2 ≤ density (tailSlice S.points y)) ∨
      ∃ y : Y,
        alpha - 2 * p.eta ≤ density (tailSlice S.points y) ∧
        p.theta / 2 ≤ density (goodBinaryLines (tailSlice S.points y)) := by
  classical
  let : Nonempty (Word 3 m) := inferInstance
  let : Nonempty (Line (Fin 2) (Fin m)) := by
    let l : Line (Fin 2) (Fin m) :=
      { idxFun := fun _ ↦ none
        proper := ⟨⟨0, hm⟩, rfl⟩ }
    exact ⟨l⟩
  by_cases hinc : ∃ y : Y,
      alpha + p.eta ^ 2 / 2 ≤ density (tailSlice S.points y)
  · exact Or.inl hinc
  · right
    push_neg at hinc
    have hdensePoints : alpha - p.eta ^ 2 / 2 ≤ density S.points := by
      rw [density_eq_average_fiber]
      exact const_le_average S.section_dense
    have havgSlices : alpha - p.eta ^ 2 / 2 ≤
        average fun y : Y ↦ density (tailSlice S.points y) := by
      rwa [← density_eq_average_tailSlice]
    let H1 : Finset Y := superlevel
      (fun y : Y ↦ density (tailSlice S.points y)) (alpha - 2 * p.eta)
    have hH1raw :
        ((alpha - p.eta ^ 2 / 2) - (alpha - 2 * p.eta)) /
            ((alpha + p.eta ^ 2 / 2) - (alpha - 2 * p.eta)) ≤
          density H1 := by
      apply density_superlevel_ge
      · exact havgSlices
      · intro y
        exact (hinc y).le
      · have := p.eta_pos
        nlinarith
    have hratio :
        1 - p.eta ≤
          ((alpha - p.eta ^ 2 / 2) - (alpha - 2 * p.eta)) /
            ((alpha + p.eta ^ 2 / 2) - (alpha - 2 * p.eta)) := by
      rw [le_div_iff₀]
      · have he0 := p.eta_pos
        have he1 := p.eta_le_one
        nlinarith [sq_nonneg p.eta]
      · have := p.eta_pos
        nlinarith
    have hH1 : 1 - p.eta ≤ density H1 := hratio.trans hH1raw
    have havgLines : p.theta ≤
        average fun y : Y ↦ density (goodBinaryLines (tailSlice S.points y)) := by
      rw [← average_density_lineSectionIntersection_eq hm S.points]
      exact const_le_average S.line_dense
    let H2 : Finset Y := superlevel
      (fun y : Y ↦ density (goodBinaryLines (tailSlice S.points y)))
        (p.theta / 2)
    have hH2 : p.theta / 2 ≤ density H2 := by
      exact half_le_density_superlevel
        (fun y : Y ↦ density (goodBinaryLines (tailSlice S.points y)))
        p.theta_nonneg havgLines (fun y ↦ density_le_one _)
    have hinterLower : density H1 + density H2 - 1 ≤ density (H1 ∩ H2) := by
      have hu := density_union_add_density_inter' H1 H2
      have hule := density_le_one (H1 ∪ H2)
      linarith
    have hinterPos : 0 < density (H1 ∩ H2) := by
      have heta := p.eta_lt_theta_div_two
      linarith
    have hinterNonempty : (H1 ∩ H2).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, density_empty] at hinterPos
      exact lt_irrefl 0 hinterPos
    obtain ⟨y, hy⟩ := hinterNonempty
    obtain ⟨hy1, hy2⟩ := Finset.mem_inter.mp hy
    refine ⟨y, ?_, ?_⟩
    · exact (mem_superlevel _ _ y).1 hy1
    · exact (mem_superlevel _ _ y).1 hy2

end CorrelatedSections

/-! ## The excess decomposition -/

section Excess

variable {m : ℕ}

/-- The output of the correlation step in a standard ternary parameter cube. -/
structure InsensitiveCorrelation (p : CorrelationConstants)
    (alpha : ℝ) (A : Finset (Word 3 m)) where
  first : Finset (Word 3 m)
  second : Finset (Word 3 m)
  first_insensitive :
    Erdos171.IsLastInsensitive 0 (first : Set (Word 3 m))
  second_insensitive :
    Erdos171.IsLastInsensitive 1 (second : Set (Word 3 m))
  mass : p.gamma ≤ density (first ∩ second)
  correlated :
    (alpha + p.gamma) * density (first ∩ second) ≤
      density (A ∩ (first ∩ second))

theorem isLastInsensitive_univ (i : Fin 2) :
    Erdos171.IsLastInsensitive i (Set.univ : Set (Word 3 m)) := by
  intro x y _
  simp

theorem isLastInsensitive_finset_compl (i : Fin 2)
    (C : Finset (Word 3 m))
    (hC : Erdos171.IsLastInsensitive i (C : Set (Word 3 m))) :
    Erdos171.IsLastInsensitive i
      ((Finset.univ \ C : Finset (Word 3 m)) : Set (Word 3 m)) := by
  have hcoe :
      (((Finset.univ \ C : Finset (Word 3 m)) : Set (Word 3 m))) =
        (C : Set (Word 3 m))ᶜ := by
    ext x
    simp
  rw [hcoe]
  exact hC.compl

/-- An increment on the whole parameter cube is already an insensitive
correlation, using the whole cube for both insensitive factors. -/
theorem insensitiveCorrelation_of_increment (p : CorrelationConstants)
    {alpha : ℝ} {A : Finset (Word 3 m)}
    (hinc : alpha + p.gamma ≤ density A) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  refine ⟨
    { first := Finset.univ
      second := Finset.univ
      first_insensitive := by simpa using (isLastInsensitive_univ 0)
      second_insensitive := by simpa using (isLastInsensitive_univ 1)
      mass := ?_
      correlated := ?_ }⟩
  · have hhalf : p.gamma ≤ p.eta / 2 := p.gamma_le_eta_div_two
    have heta : p.eta / 2 ≤ 1 := by linarith [p.eta_le_one]
    simpa using hhalf.trans heta
  · simpa using hinc

/-- The direct-increment alternative in the DKT dichotomy implies the
correlation conclusion because `gamma ≤ eta²/2`. -/
theorem insensitiveCorrelation_of_eta_increment (p : CorrelationConstants)
    {alpha : ℝ} {A : Finset (Word 3 m)}
    (hinc : alpha + p.eta ^ 2 / 2 ≤ density A) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  apply insensitiveCorrelation_of_increment p
  nlinarith [p.gamma_le_eta_sq_div_two]

/-- A quantitative lower bound for the completion core obtained from many
good binary lines.  The power hypothesis is the only dimension estimate used
here; later modules arrange it by choosing the parameter dimension large. -/
theorem density_completionCore_ge_of_many_lines (p : CorrelationConstants)
    {A : Finset (Word 3 m)}
    (hmany : p.theta / 2 * ((3 : ℝ) ^ m - (2 : ℝ) ^ m) ≤
      ((goodBinaryLines A).card : ℝ))
    (hpow : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m) :
    p.theta / 4 ≤ density (completionCore A) := by
  have hcardNat := card_goodBinaryLines_le_completionCore A
  have hcard : ((goodBinaryLines A).card : ℝ) ≤
      ((completionCore A).card : ℝ) := by exact_mod_cast hcardNat
  have hthree : 0 < (3 : ℝ) ^ m := by positivity
  rw [density_eq_card_div_card]
  simp only [Erdos171.card_word, Nat.cast_pow, Nat.cast_ofNat]
  rw [le_div_iff₀ hthree]
  have htheta := p.theta_nonneg
  nlinarith

/-- Pure finite-probability heart of the correlation argument.  The sets
`C0,C1` are the two insensitive endpoint cylinders.  If their intersection
has noticeable mass but contains little of `A`, then one of the two disjoint
pieces of its complement has positive excess over density `alpha + gamma`. -/
theorem insensitiveCorrelation_of_core (p : CorrelationConstants)
    {alpha : ℝ} {A C0 C1 : Finset (Word 3 m)}
    (hfloor : p.delta ≤ alpha)
    (hA : alpha - 2 * p.eta ≤ density A)
    (hC0 : Erdos171.IsLastInsensitive 0 (C0 : Set (Word 3 m)))
    (hC1 : Erdos171.IsLastInsensitive 1 (C1 : Set (Word 3 m)))
    (hC : p.theta / 4 ≤ density (C0 ∩ C1))
    (hAC : density (A ∩ (C0 ∩ C1)) ≤ p.eta) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  classical
  let P0 : Finset (Word 3 m) := Finset.univ \ C0
  let P1 : Finset (Word 3 m) := C0 \ C1
  let C : Finset (Word 3 m) := C0 ∩ C1
  have hPdisj : Disjoint P0 P1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    simp only [P0, P1, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx0 hx1
    exact hx0 hx1.1
  have hPunion : P0 ∪ P1 = Finset.univ \ C := by
    ext x
    simp only [P0, P1, C, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_inter]
    tauto
  have hAPdisj : Disjoint (A ∩ P0) (A ∩ P1) := by
    exact hPdisj.mono Finset.inter_subset_right Finset.inter_subset_right
  have hAPunion : (A ∩ P0) ∪ (A ∩ P1) = A \ C := by
    ext x
    simp only [P0, P1, C, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  have hsumP : density P0 + density P1 = density (Finset.univ \ C) := by
    have hu := density_union_add_density_inter' P0 P1
    have hi : P0 ∩ P1 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hPdisj
    rw [hi, density_empty, add_zero, hPunion] at hu
    linarith
  have hsumAP : density (A ∩ P0) + density (A ∩ P1) = density (A \ C) := by
    have hu := density_union_add_density_inter' (A ∩ P0) (A ∩ P1)
    have hi : (A ∩ P0) ∩ (A ∩ P1) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hAPdisj
    rw [hi, density_empty, add_zero, hAPunion] at hu
    linarith
  have hsdiffA := density_sdiff_add_density_inter' A C
  have hsdiffU := density_compl' C
  have hAC' : density (A ∩ C) ≤ p.eta := by simpa [C] using hAC
  have hC' : p.theta / 4 ≤ density C := by simpa [C] using hC
  have hcoeff : 0 ≤ alpha + p.gamma := by
    linarith [p.delta_pos, p.gamma_pos]
  have hprodC :
      (alpha + p.gamma) * (p.theta / 4) ≤
        (alpha + p.gamma) * density C :=
    mul_le_mul_of_nonneg_left hC' hcoeff
  have hfloorProd :
      (p.delta + p.gamma) * (p.theta / 4) ≤
        (alpha + p.gamma) * (p.theta / 4) := by
    have hsum : p.delta + p.gamma ≤ alpha + p.gamma := by linarith
    exact mul_le_mul_of_nonneg_right hsum
      (div_nonneg p.theta_nonneg (by norm_num))
  let e0 : ℝ := density (A ∩ P0) - (alpha + p.gamma) * density P0
  let e1 : ℝ := density (A ∩ P1) - (alpha + p.gamma) * density P1
  have hexcess : 2 * p.gamma ≤ e0 + e1 := by
    have hgammaEta := p.gamma_le_eta_div_two
    have htwelve := p.twelve_eta
    have hdiff : alpha - 3 * p.eta ≤ density (A \ C) := by
      linarith
    have hprodDelta :
        p.delta * p.theta / 4 ≤ (alpha + p.gamma) * density C := by
      calc
        p.delta * p.theta / 4 ≤
            (p.delta + p.gamma) * (p.theta / 4) := by
              have hnonneg : 0 ≤ p.gamma * (p.theta / 4) :=
                mul_nonneg p.gamma_nonneg
                  (div_nonneg p.theta_nonneg (by norm_num))
              nlinarith
        _ ≤ (alpha + p.gamma) * (p.theta / 4) := hfloorProd
        _ ≤ (alpha + p.gamma) * density C := hprodC
    have hprodEta :
        12 * p.eta ≤ (alpha + p.gamma) * density C := by
      linarith
    have hdiff' : -3 * p.eta ≤ density (A \ C) - alpha := by
      linarith
    have hgamma3 : 3 * p.gamma ≤ 9 * p.eta := by
      linarith [p.eta_pos]
    dsimp only [e0, e1]
    rw [sub_add_sub_comm, hsumAP, ← mul_add, hsumP, hsdiffU]
    rw [show density (A \ C) - (alpha + p.gamma) * (1 - density C) =
        density (A \ C) - alpha - p.gamma +
          (alpha + p.gamma) * density C by ring]
    linarith
  have hchoice : p.gamma ≤ e0 ∨ p.gamma ≤ e1 := by
    by_cases h0 : p.gamma ≤ e0
    · exact Or.inl h0
    · right
      exact le_of_lt (by linarith)
  rcases hchoice with he0 | he1
  · have hP0mass : p.gamma ≤ density P0 := by
      have hinter := density_inter_le_right' A P0
      have hsubnonneg : 0 ≤ (alpha + p.gamma) * density P0 :=
        mul_nonneg hcoeff (density_nonneg P0)
      dsimp only [e0] at he0
      linarith
    refine ⟨
      { first := P0
        second := Finset.univ
        first_insensitive := ?_
        second_insensitive := by simpa using (isLastInsensitive_univ 1)
        mass := ?_
        correlated := ?_ }⟩
    · exact isLastInsensitive_finset_compl 0 C0 hC0
    · simpa using hP0mass
    · dsimp only [e0] at he0
      have hcorr : (alpha + p.gamma) * density P0 ≤ density (A ∩ P0) := by
        linarith [p.gamma_nonneg]
      simpa only [Finset.inter_univ] using hcorr
  · have hP1mass : p.gamma ≤ density P1 := by
      have hinter := density_inter_le_right' A P1
      have hsubnonneg : 0 ≤ (alpha + p.gamma) * density P1 :=
        mul_nonneg hcoeff (density_nonneg P1)
      dsimp only [e1] at he1
      linarith
    refine ⟨
      { first := C0
        second := Finset.univ \ C1
        first_insensitive := hC0
        second_insensitive := isLastInsensitive_finset_compl 1 C1 hC1
        mass := ?_
        correlated := ?_ }⟩
    · have hP1eq : C0 ∩ (Finset.univ \ C1) = P1 := by
        ext x
        simp [P1]
      rw [hP1eq]
      exact hP1mass
    · dsimp only [e1] at he1
      have hcorr : (alpha + p.gamma) * density P1 ≤ density (A ∩ P1) := by
        linarith [p.gamma_nonneg]
      have hP1eq : C0 ∩ (Finset.univ \ C1) = P1 := by
        ext x
        simp [P1]
      rw [hP1eq]
      exact hcorr

/-- The many-binary-lines alternative yields correlation with two insensitive
sets.  The current density `alpha` is independent of the fixed floor
`p.delta`; only `p.delta ≤ alpha` is used. -/
theorem insensitiveCorrelation_of_manyBinaryLines (p : CorrelationConstants)
    {alpha : ℝ} {A : Finset (Word 3 m)}
    (hfloor : p.delta ≤ alpha)
    (hA : alpha - 2 * p.eta ≤ density A)
    (hline : ¬ HasLine A)
    (hmany : p.theta / 2 * ((3 : ℝ) ^ m - (2 : ℝ) ^ m) ≤
      ((goodBinaryLines A).card : ℝ))
    (hhalf : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m)
    (hsmall : (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ p.eta) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  let C0 := endpointCylinderFinset 0 (binaryPart A)
  let C1 := endpointCylinderFinset 1 (binaryPart A)
  have hcore : completionCore A = C0 ∩ C1 := rfl
  apply insensitiveCorrelation_of_core p hfloor hA
  · exact endpointCylinderFinset_isLastInsensitive 0 (binaryPart A)
  · exact endpointCylinderFinset_isLastInsensitive 1 (binaryPart A)
  · rw [← hcore]
    exact density_completionCore_ge_of_many_lines p hmany hhalf
  · rw [← hcore]
    exact (density_inter_completionCore_le hline).trans hsmall

/-- Density-form wrapper for `insensitiveCorrelation_of_manyBinaryLines`.
This is the form returned directly by the many-lines averaging lemma. -/
theorem insensitiveCorrelation_of_manyBinaryLineDensity
    (p : CorrelationConstants) {alpha : ℝ} {A : Finset (Word 3 m)}
    (hm : 0 < m)
    (hfloor : p.delta ≤ alpha)
    (hA : alpha - 2 * p.eta ≤ density A)
    (hline : ¬ HasLine A)
    (hmany : p.theta / 2 ≤ density (goodBinaryLines A))
    (hhalf : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m)
    (hsmall : (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ p.eta) :
    Nonempty (InsensitiveCorrelation p alpha A) := by
  have : Nonempty (Line (Fin 2) (Fin m)) := by
    let l : Line (Fin 2) (Fin m) :=
      { idxFun := fun _ ↦ none
        proper := ⟨⟨0, hm⟩, rfl⟩ }
    exact ⟨l⟩
  have hcardpos : 0 < (Fintype.card (Line (Fin 2) (Fin m)) : ℝ) := by
    positivity
  have hcount :
      p.theta / 2 * (Fintype.card (Line (Fin 2) (Fin m)) : ℝ) ≤
        ((goodBinaryLines A).card : ℝ) := by
    rw [density_eq_card_div_card, le_div_iff₀ hcardpos] at hmany
    exact hmany
  have hlineCount :
      (Fintype.card (Line (Fin 2) (Fin m)) : ℝ) =
        (3 : ℝ) ^ m - (2 : ℝ) ^ m := by
    rw [Line.card_fin]
    norm_num only [Nat.cast_sub (Nat.pow_le_pow_left (by omega : 2 ≤ 3) m),
      Nat.cast_pow, Nat.cast_ofNat, Nat.reduceAdd]
  apply insensitiveCorrelation_of_manyBinaryLines p hfloor hA hline
  · simpa only [hlineCount] using hcount
  · exact hhalf
  · exact hsmall

/-- Combine the correlated-sections and many-lines lemmas with the
insensitive excess calculation.  This isolates precisely what remains for
the Ramsey/uniformization construction: produce `CorrelatedSectionData` and
transport its selected tail slice back to a subspace of the original cube. -/
theorem insensitiveCorrelation_of_correlatedSections
    (p : CorrelationConstants) {alpha : ℝ} {m : ℕ} {Y : Type*}
    [Fintype Y] [Nonempty Y]
    (hm : 0 < m)
    (S : CorrelatedSectionData p alpha m Y)
    (hfloor : p.delta ≤ alpha)
    (hline : ∀ y : Y, ¬ HasLine (tailSlice S.points y))
    (hhalf : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m)
    (hsmall : (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ p.eta) :
    ∃ y : Y, Nonempty (InsensitiveCorrelation p alpha (tailSlice S.points y)) := by
  rcases manyBinaryLines_of_correlatedSections p hm S with hinc | hmany
  · obtain ⟨y, hy⟩ := hinc
    exact ⟨y, insensitiveCorrelation_of_eta_increment p hy⟩
  · obtain ⟨y, hyA, hyLines⟩ := hmany
    exact ⟨y, insensitiveCorrelation_of_manyBinaryLineDensity p hm hfloor hyA
      (hline y) hyLines hhalf hsmall⟩

end Excess

/-! ## Concrete tower construction and ambient transport -/

section TowerBridge

/-- Product presentation of all fillings of a uniformized tower hole. -/
noncomputable def holeProduct {r b : ℕ}
    (A : Finset (Tower (Word 3 r) PUnit b))
    (h : BlockHole (Word 3 r) PUnit b) :
    Finset (Word 3 r × h.Tail) := by
  classical
  letI := h.tailFintype
  exact Finset.univ.filter fun p ↦ h.fill p.1 p.2 ∈ A

@[simp] theorem mem_holeProduct {r b : ℕ}
    (A : Finset (Tower (Word 3 r) PUnit b))
    (h : BlockHole (Word 3 r) PUnit b) (x : Word 3 r) (z : h.Tail) :
    (x, z) ∈ holeProduct A h ↔ h.fill x z ∈ A := by
  classical
  let := h.tailFintype
  simp [holeProduct]

@[simp] theorem fiber_holeProduct {r b : ℕ}
    (A : Finset (Tower (Word 3 r) PUnit b))
    (h : BlockHole (Word 3 r) PUnit b) (x : Word 3 r) :
    fiber (holeProduct A h) x = h.holeSection A x := by
  classical
  let := h.tailFintype
  ext z
  simp

/-- Fixed-dimension concrete correlation theorem.  Uniformization is applied
after the Graham--Rothschild source dimension has been chosen.  The selected
tail and homogeneous binary subspace are composed with the hole subspace and
reindexed back to a genuine `Fin N` cube. -/
theorem exists_insensitiveCorrelation_fixedDimension
    (s : CorrelationSystem) (m : ℕ)
    (hm0 : s.m0 ≤ m)
    (hhalf : 2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m)
    (hsmall : (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ s.constants.eta) :
    ∃ N : ℕ, ∀ A : Finset (Word 3 N),
      s.constants.delta ≤ density A →
      HasLine A ∨
        ∃ W : Subspace (Fin m) (Fin 3) (Fin N),
          Nonempty (InsensitiveCorrelation s.constants (density A)
            (pullbackFinset W A)) := by
  have hmpos : 0 < m := s.m0_pos.trans_le hm0
  obtain ⟨r, hGR⟩ := binary_line_homogeneous m
  have hrpos : 0 < r := by
    let c : Line (Fin 2) (Fin r) → Bool := fun _ ↦ false
    obtain ⟨V, _b, _hV⟩ := hGR c
    obtain ⟨i, _hi⟩ := V.proper (⟨0, hmpos⟩ : Fin m)
    exact Fin.pos_iff_nonempty.mpr ⟨i⟩
  have hblock : 1 < Fintype.card (Word 3 r) := by
    rw [Erdos171.card_word]
    exact Nat.one_lt_pow hrpos.ne' (by norm_num)
  obtain ⟨b, hb⟩ := exists_tower_uniform_sections
    (X := Word 3 r) (Y := PUnit) hblock
    (s.constants.eta ^ 2 / 2)
    (div_pos (pow_pos s.constants.eta_pos 2) (by norm_num))
  let N := Fintype.card (BlockIndex r b)
  let e : Tower (Word 3 r) PUnit b ≃ Word 3 N := towerFinEquiv 3 r b
  refine ⟨N, ?_⟩
  intro A hA
  classical
  by_cases hlineA : HasLine A
  · exact Or.inl hlineA
  · right
    let AT : Finset (Tower (Word 3 r) PUnit b) := A.map e.symm.toEmbedding
    have hAT : density AT = density A := by
      simpa [AT] using density_map_equiv e.symm A
    obtain ⟨h, hh⟩ := hb AT
    let := h.tailFintype
    let := h.tailNonempty
    let T : Finset (Word 3 r × h.Tail) := holeProduct AT h
    have huniform : ∀ x : Word 3 r,
        density A - s.constants.eta ^ 2 / 2 ≤ density (fiber T x) := by
      intro x
      dsimp only [T]
      rw [fiber_holeProduct]
      have hx := hh x
      rwa [hAT] at hx
    obtain ⟨V, S, hS⟩ := exists_correlatedSectionData_of_uniform
      s hm0 T hA huniform hGR
    have hPull (z : h.Tail) :
        pullbackFinset
            (((h.subspace z).comp V.finLift).reindex
              (Equiv.refl _) (Equiv.refl _)
              (Fintype.equivFin (BlockIndex r b))) A =
          tailSlice S.points z := by
      ext x
      rw [mem_pullbackFinset, mem_tailSlice, hS,
        mem_prefixPullbackProduct]
      dsimp only [T]
      rw [mem_holeProduct]
      have happly := reindex_hole_comp_apply h z V.finLift x
      rw [happly]
      simpa [AT, e]
    have hlineSlices : ∀ z : h.Tail, ¬HasLine (tailSlice S.points z) := by
      intro z hz
      apply hlineA
      let W : Subspace (Fin m) (Fin 3) (Fin N) :=
        ((h.subspace z).comp V.finLift).reindex
          (Equiv.refl _) (Equiv.refl _)
          (Fintype.equivFin (BlockIndex r b))
      apply HasLine.of_pullback W
      rw [hPull z]
      exact hz
    obtain ⟨z, hz⟩ := insensitiveCorrelation_of_correlatedSections
      s.constants hmpos S hA hlineSlices hhalf hsmall
    let W : Subspace (Fin m) (Fin 3) (Fin N) :=
      ((h.subspace z).comp V.finLift).reindex
        (Equiv.refl _) (Equiv.refl _)
        (Fintype.equivFin (BlockIndex r b))
    refine ⟨W, ?_⟩
    simpa only [W, hPull z] using hz

/-- Above one fixed dimension, both elementary power estimates needed in the
completion-core count hold. -/
theorem exists_correlation_dimension_threshold (s : CorrelationSystem) :
    ∃ M : ℕ, s.m0 ≤ M ∧ ∀ m ≥ M,
      2 * (2 : ℝ) ^ m ≤ (3 : ℝ) ^ m ∧
      (2 : ℝ) ^ m / (3 : ℝ) ^ m ≤ s.constants.eta := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one s.constants.eta_pos
    (by norm_num : (2 / 3 : ℝ) < 1)
  let M := max s.m0 (max 2 k)
  refine ⟨M, le_max_left _ _, ?_⟩
  intro m hm
  have hmM : max 2 k ≤ m := (le_max_right s.m0 (max 2 k)).trans hm
  have hm2 : 2 ≤ m := (le_max_left 2 k).trans hmM
  have hmk : k ≤ m := (le_max_right 2 k).trans hmM
  constructor
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm2
    have hp : 2 ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by omega) t
    have hpR : (2 : ℝ) ^ t ≤ (3 : ℝ) ^ t := by exact_mod_cast hp
    norm_num only [pow_add, pow_two]
    have hnonneg : 0 ≤ (3 : ℝ) ^ t := by positivity
    nlinarith
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hmk
    rw [← div_pow]
    rw [pow_add]
    have htail : (2 / 3 : ℝ) ^ t ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hbase : 0 ≤ (2 / 3 : ℝ) ^ k := by positivity
    calc
      (2 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ t ≤
          (2 / 3 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left htail hbase
      _ = (2 / 3 : ℝ) ^ k := mul_one _
      _ ≤ s.constants.eta := hk.le

/-- Uniform-in-dimension correlation theorem for one fixed correlation
system.  In particular, `s.constants.gamma` is chosen before `m`. -/
theorem exists_insensitiveCorrelation (s : CorrelationSystem) :
    ∃ M : ℕ, ∀ m ≥ M, ∃ N : ℕ, ∀ A : Finset (Word 3 N),
      s.constants.delta ≤ density A →
      HasLine A ∨
        ∃ W : Subspace (Fin m) (Fin 3) (Fin N),
          Nonempty (InsensitiveCorrelation s.constants (density A)
            (pullbackFinset W A)) := by
  obtain ⟨M, hm0, hM⟩ := exists_correlation_dimension_threshold s
  refine ⟨M, ?_⟩
  intro m hm
  obtain ⟨hhalf, hsmall⟩ := hM m hm
  exact exists_insensitiveCorrelation_fixedDimension s m (hm0.trans hm) hhalf hsmall

/-- Choose all correlation constants once from a prescribed density floor.
This is the quantifier order required by the subsequent density-increment
iteration. -/
theorem exists_uniform_insensitiveCorrelation (delta : ℝ)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ s : CorrelationSystem, s.constants.delta = delta ∧
      ∃ M : ℕ, ∀ m ≥ M, ∃ N : ℕ, ∀ A : Finset (Word 3 N),
        delta ≤ density A →
        HasLine A ∨
          ∃ W : Subspace (Fin m) (Fin 3) (Fin N),
            Nonempty (InsensitiveCorrelation s.constants (density A)
              (pullbackFinset W A)) := by
  obtain ⟨s, hs⟩ := CorrelationSystem.exists_of_delta delta hdelta hdelta1
  refine ⟨s, hs, ?_⟩
  obtain ⟨M, hM⟩ := exists_insensitiveCorrelation s
  refine ⟨M, ?_⟩
  intro m hm
  obtain ⟨N, hN⟩ := hM m hm
  exact ⟨N, fun A hA ↦ hN A (by simpa only [hs] using hA)⟩

end TowerBridge

end Erdos185.DHJ
