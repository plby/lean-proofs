/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.LocalLemma
import ErdosProblems.Erdos136.Completion
import ErdosProblems.Erdos136.PartialConstruction
import ErdosProblems.Erdos136.UpperParameters

/-!
# The sparse-leave local-lemma completion for Erdős 136

This file formalizes the second, elementary probabilistic step of the
Joos--Mubayi construction.  The sample space consists of all independent
uniform fresh colourings of the complete graph (coordinates outside the
leave are harmless).  The bad events are the three events from the paper:

* a prescribed fresh colour occurs on a two-edge leave path;
* a leave four-cycle is properly coloured with two alternating colours;
* a prescribed fresh colour occurs on the leave matching complementary to
  an old monochromatic matching.

Events are adjacent exactly when their coordinate supports meet.  We prove
the required cylinder independence and probability estimates directly on
the finite uniform product, apply `LocalLemma.exists_avoiding_of_four_mul`,
and turn avoidance into `Completion.AvoidsABC`.
-/

namespace Erdos136
namespace LeaveCompletion

open Finset
open Filter
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev EdgeN (n : ℕ) := Completion.Edge (Fin n)
abbrev Assignment (n t : ℕ) := EdgeN n → Fin t

/-! ## Uniform finite products and cylinder events -/

/-- A set of assignments depends only on the coordinates in `S`. -/
def DependsOn {E A : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (U : Finset (E → A)) : Prop :=
  ∀ ω ω', (∀ e ∈ S, ω e = ω' e) → (ω ∈ U ↔ ω' ∈ U)

lemma dependsOn_filter {E A : Type*} [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A]
    (S : Finset E) (p : (E → A) → Prop) [DecidablePred p]
    (hp : ∀ ω ω', (∀ e ∈ S, ω e = ω' e) → (p ω ↔ p ω')) :
    DependsOn S (Finset.univ.filter p) := by
  intro ω ω' h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hp ω ω' h

lemma DependsOn.mono {E A : Type*} [Fintype E] [DecidableEq E]
    {S T : Finset E} {U : Finset (E → A)}
    (h : DependsOn S U) (hST : S ⊆ T) : DependsOn T U := by
  intro ω ω' heq
  exact h ω ω' fun e he ↦ heq e (hST he)

lemma DependsOn.inter {E A : Type*} [Fintype E] [DecidableEq E]
    {S : Finset E} {U V : Finset (E → A)}
    (hU : DependsOn S U) (hV : DependsOn S V) : DependsOn S (U ∩ V) := by
  intro ω ω' h
  simp only [Finset.mem_inter]
  rw [hU ω ω' h, hV ω ω' h]

lemma DependsOn.compl {E A : Type*} [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A]
    {S : Finset E} {U : Finset (E → A)} (hU : DependsOn S U) :
    DependsOn S (Finset.univ \ U) := by
  intro ω ω' h
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact not_congr (hU ω ω' h)

/-- Split a function into its coordinates in `S` and outside `S`. -/
def splitEquiv {E A : Type*} [DecidableEq E] (S : Finset E) :
    (E → A) ≃ ((e : {e // e ∈ S}) → A) × ((e : {e // e ∉ S}) → A) :=
  Equiv.piEquivPiSubtypeProd (fun e ↦ e ∈ S) (fun _ ↦ A)

section CylinderIndependence

variable {E A : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [Nonempty A] [DecidableEq A]

/-- Two cylinder sets on complementary coordinate sets are independent in
the uniform finite product.  The cross-multiplied cardinality identity is
the useful integral form of independence. -/
lemma card_inter_mul_card_eq
    (S : Finset E) (U V : Finset (E → A))
    (hU : DependsOn S U)
    (hV : DependsOn (Finset.univ \ S) V) :
    (U ∩ V).card * Fintype.card (E → A) = U.card * V.card := by
  classical
  let X := (e : {e // e ∈ S}) → A
  let Y := (e : {e // e ∉ S}) → A
  let Φ : (E → A) ≃ X × Y := splitEquiv S
  let x₀ : X := fun _ ↦ Classical.choice inferInstance
  let y₀ : Y := fun _ ↦ Classical.choice inferInstance
  let UX := {x : X // Φ.symm (x, y₀) ∈ U}
  let VY := {y : Y // Φ.symm (x₀, y) ∈ V}

  have hU_coord (x : X) (y : Y) :
      Φ.symm (x, y) ∈ U ↔ Φ.symm (x, y₀) ∈ U := by
    apply hU
    intro e he
    simp [Φ, splitEquiv, Equiv.piEquivPiSubtypeProd, he]
  have hV_coord (x : X) (y : Y) :
      Φ.symm (x, y) ∈ V ↔ Φ.symm (x₀, y) ∈ V := by
    apply hV
    intro e he
    have heS : e ∉ S := by simpa using he
    simp [Φ, splitEquiv, Equiv.piEquivPiSubtypeProd, heS]

  let eU : {w : E → A // w ∈ U} ≃ UX × Y :=
    { toFun := fun w ↦
        (⟨(Φ w.1).1, (hU_coord (Φ w.1).1 (Φ w.1).2).mp (by
          simpa using w.2)⟩, (Φ w.1).2)
      invFun := fun p ↦
        ⟨Φ.symm (p.1.1, p.2), (hU_coord p.1.1 p.2).mpr p.1.2⟩
      left_inv := by intro w; apply Subtype.ext; exact Φ.symm_apply_apply w.1
      right_inv := by
        intro p
        rcases p with ⟨⟨x, hx⟩, y⟩
        apply Prod.ext <;> simp [Φ] }
  let eV : {w : E → A // w ∈ V} ≃ X × VY :=
    { toFun := fun w ↦
        ((Φ w.1).1, ⟨(Φ w.1).2,
          (hV_coord (Φ w.1).1 (Φ w.1).2).mp (by simpa using w.2)⟩)
      invFun := fun p ↦
        ⟨Φ.symm (p.1, p.2.1), (hV_coord p.1 p.2.1).mpr p.2.2⟩
      left_inv := by intro w; apply Subtype.ext; exact Φ.symm_apply_apply w.1
      right_inv := by
        intro p
        rcases p with ⟨x, ⟨y, hy⟩⟩
        apply Prod.ext <;> simp [Φ] }
  let eI : {w : E → A // w ∈ U ∩ V} ≃ UX × VY :=
    { toFun := fun w ↦
        (⟨(Φ w.1).1, (hU_coord (Φ w.1).1 (Φ w.1).2).mp
          (by simpa using (Finset.mem_inter.mp w.2).1)⟩,
         ⟨(Φ w.1).2, (hV_coord (Φ w.1).1 (Φ w.1).2).mp
          (by simpa using (Finset.mem_inter.mp w.2).2)⟩)
      invFun := fun p ↦
        ⟨Φ.symm (p.1.1, p.2.1), Finset.mem_inter.mpr
          ⟨(hU_coord p.1.1 p.2.1).mpr p.1.2,
           (hV_coord p.1.1 p.2.1).mpr p.2.2⟩⟩
      left_inv := by intro w; apply Subtype.ext; exact Φ.symm_apply_apply w.1
      right_inv := by
        intro p
        rcases p with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
        apply Prod.ext <;> simp [Φ] }

  have hcardU : U.card = Fintype.card UX * Fintype.card Y := by
    rw [← Fintype.card_coe]
    simpa using Fintype.card_congr eU
  have hcardV : V.card = Fintype.card X * Fintype.card VY := by
    rw [← Fintype.card_coe]
    simpa using Fintype.card_congr eV
  have hcardI : (U ∩ V).card = Fintype.card UX * Fintype.card VY := by
    rw [← Fintype.card_coe]
    simpa using Fintype.card_congr eI
  have hcardAll : Fintype.card (E → A) = Fintype.card X * Fintype.card Y := by
    simpa using Fintype.card_congr Φ
  rw [hcardU, hcardV, hcardI, hcardAll]
  ring

lemma uniformProbability_inter_eq_mul
    (S : Finset E) (U V : Finset (E → A))
    (hU : DependsOn S U)
    (hV : DependsOn (Finset.univ \ S) V) :
    LocalLemma.uniformProbability (U ∩ V) =
      LocalLemma.uniformProbability U * LocalLemma.uniformProbability V := by
  have hcard := card_inter_mul_card_eq S U V hU hV
  have hpos : (0 : ℝ) < Fintype.card (E → A) := by
    exact_mod_cast Fintype.card_pos
  unfold LocalLemma.uniformProbability
  field_simp [ne_of_gt hpos]
  exact_mod_cast hcard

end CylinderIndependence

/-! ## The three raw bad configurations -/

/-- An oriented two-edge path in the leave, with a prescribed fresh colour. -/
structure WedgeIndex {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))) where
  left : EdgeN n
  right : EdgeN n
  edges_ne : left ≠ right
  adjacent : ¬ Disjoint left.1.toFinset right.1.toFinset
  leftLeave : old left = none
  rightLeave : old right = none
  color : Fin t
  deriving Fintype

/-- Two ordered leave matchings supported on one four-set. -/
structure CycleIndex {n oldK : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))) where
  e01 : EdgeN n
  e12 : EdgeN n
  e23 : EdgeN n
  e30 : EdgeN n
  e01_ne_e12 : e01 ≠ e12
  e01_ne_e23 : e01 ≠ e23
  e01_ne_e30 : e01 ≠ e30
  e12_ne_e23 : e12 ≠ e23
  e12_ne_e30 : e12 ≠ e30
  e23_ne_e30 : e23 ≠ e30
  firstMatching : Disjoint e01.1.toFinset e23.1.toFinset
  secondMatching : Disjoint e12.1.toFinset e30.1.toFinset
  sameVertices : e01.1.toFinset ∪ e23.1.toFinset =
    e12.1.toFinset ∪ e30.1.toFinset
  e01Leave : old e01 = none
  e12Leave : old e12 = none
  e23Leave : old e23 = none
  e30Leave : old e30 = none

/-- A repeated old pair and a disjoint repeated fresh pair on one four-set. -/
structure CrossIndex {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))) where
  old01 : EdgeN n
  old23 : EdgeN n
  e12 : EdgeN n
  e30 : EdgeN n
  old01_ne_old23 : old01 ≠ old23
  e12_ne_e30 : e12 ≠ e30
  old_fresh_ne : old01 ≠ e12 ∧ old01 ≠ e30 ∧
    old23 ≠ e12 ∧ old23 ≠ e30
  freshMatching : Disjoint e12.1.toFinset e30.1.toFinset
  atMostFourVertices :
    (old01.1.toFinset ∪ old23.1.toFinset ∪ e12.1.toFinset ∪ e30.1.toFinset).card ≤ 4
  oldColor : Fin oldK
  e01Old : old old01 = some oldColor
  e23Old : old old23 = some oldColor
  e12Leave : old e12 = none
  e30Leave : old e30 = none
  color : Fin t

@[ext] lemma cycleIndex_ext {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    {i j : CycleIndex old}
    (h0 : i.e01 = j.e01) (h1 : i.e12 = j.e12)
    (h2 : i.e23 = j.e23) (h3 : i.e30 = j.e30) : i = j := by
  cases i
  cases j
  simp_all

@[ext] lemma crossIndex_ext {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    {i j : CrossIndex (t := t) old}
    (h0 : i.old01 = j.old01) (h1 : i.old23 = j.old23)
    (h2 : i.e12 = j.e12) (h3 : i.e30 = j.e30)
    (hc : i.oldColor = j.oldColor) (hf : i.color = j.color) : i = j := by
  cases i
  cases j
  simp_all

noncomputable instance instFintypeCycleIndex {n oldK : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))) :
    Fintype (CycleIndex old) := by
  apply Fintype.ofInjective (fun i (k : Fin 4) ↦
    ![i.e01, i.e12, i.e23, i.e30] k)
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp at h0 h1 h2 h3
  exact cycleIndex_ext h0 h1 h2 h3

noncomputable instance instFintypeCrossIndex {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))) :
    Fintype (CrossIndex (t := t) old) := by
  apply Fintype.ofInjective (fun i ↦
    ((fun k : Fin 4 ↦ ![i.old01, i.old23, i.e12, i.e30] k), i.oldColor, i.color))
  intro i j h
  have hedges := congrArg Prod.fst h
  have h0 := congrFun hedges 0
  have h1 := congrFun hedges 1
  have h2 := congrFun hedges 2
  have h3 := congrFun hedges 3
  have hcold := congrArg (fun z ↦ z.2.1) h
  have hcfresh := congrArg (fun z ↦ z.2.2) h
  simp at h0 h1 h2 h3
  exact crossIndex_ext h0 h1 h2 h3 hcold hcfresh

namespace WedgeIndex

variable {n oldK t : ℕ}
  {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}

def leftEdge (i : WedgeIndex (t := t) old) : EdgeN n :=
  i.left

def rightEdge (i : WedgeIndex (t := t) old) : EdgeN n :=
  i.right

def support (i : WedgeIndex (t := t) old) : Finset (EdgeN n) :=
  {i.leftEdge, i.rightEdge}

lemma leftEdge_ne_rightEdge (i : WedgeIndex (t := t) old) :
    i.leftEdge ≠ i.rightEdge := i.edges_ne

@[simp] lemma card_support (i : WedgeIndex (t := t) old) : i.support.card = 2 := by
  simp [support, leftEdge_ne_rightEdge]

end WedgeIndex

namespace CycleIndex

variable {n oldK : ℕ}
  {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}

def support (i : CycleIndex old) : Finset (EdgeN n) :=
  {i.e01, i.e12, i.e23, i.e30}

@[simp] lemma card_support (i : CycleIndex old) : i.support.card = 4 := by
  simp [support, i.e01_ne_e12, i.e01_ne_e23, i.e01_ne_e30,
    i.e12_ne_e23, i.e12_ne_e30, i.e23_ne_e30]

end CycleIndex

namespace CrossIndex

variable {n oldK t : ℕ}
  {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
def support (i : CrossIndex (t := t) old) : Finset (EdgeN n) := {i.e12, i.e30}

@[simp] lemma card_support (i : CrossIndex (t := t) old) : i.support.card = 2 := by
  simp [support, e12_ne_e30]

end CrossIndex

/-- All raw bad-event indices. -/
abbrev BadIndex {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))) :=
  WedgeIndex (t := t) old ⊕ CycleIndex old ⊕ CrossIndex (t := t) old

def badSupport {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : BadIndex (t := t) old) : Finset (EdgeN n) :=
  match i with
  | Sum.inl i => i.support
  | Sum.inr (Sum.inl i) => i.support
  | Sum.inr (Sum.inr i) => i.support

@[simp] lemma badSupport_card_le_four {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : BadIndex (t := t) old) : (badSupport i).card ≤ 4 := by
  rcases i with i | i
  · simp [badSupport]
  · rcases i with i | i <;> simp [badSupport]

/-- The raw bad event associated to an index. -/
noncomputable def badEvent {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : BadIndex (t := t) old) : Finset (Assignment n t) :=
  Finset.univ.filter fun ω ↦
    match i with
    | Sum.inl i => ω i.leftEdge = i.color ∧ ω i.rightEdge = i.color
    | Sum.inr (Sum.inl i) =>
        ω i.e01 = ω i.e23 ∧ ω i.e12 = ω i.e30 ∧ ω i.e01 ≠ ω i.e12
    | Sum.inr (Sum.inr i) => ω i.e12 = i.color ∧ ω i.e30 = i.color

lemma badEvent_dependsOn {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : BadIndex (t := t) old) : DependsOn (badSupport i) (badEvent i) := by
  apply dependsOn_filter
  rcases i with i | i
  · intro ω ω' h
    have h₁ := h i.leftEdge (by simp [badSupport, WedgeIndex.support])
    have h₂ := h i.rightEdge (by simp [badSupport, WedgeIndex.support])
    simp only
    rw [h₁, h₂]
  · rcases i with i | i
    · intro ω ω' h
      have h₀₁ := h i.e01 (by simp [badSupport, CycleIndex.support])
      have h₁₂ := h i.e12 (by simp [badSupport, CycleIndex.support])
      have h₂₃ := h i.e23 (by simp [badSupport, CycleIndex.support])
      have h₃₀ := h i.e30 (by simp [badSupport, CycleIndex.support])
      simp only
      rw [h₀₁, h₁₂, h₂₃, h₃₀]
    · intro ω ω' h
      have h₁ := h i.e12 (by simp [badSupport, CrossIndex.support])
      have h₂ := h i.e30 (by simp [badSupport, CrossIndex.support])
      simp only
      rw [h₁, h₂]

/-! ## Probability estimates by explicit recolouring injections -/

lemma uniformProbability_le_inv_sq_of_fixed_pair
    {E : Type*} [Fintype E] [DecidableEq E] {t : ℕ} (ht : 0 < t)
    (U : Finset (E → Fin t)) (e f : E) (hef : e ≠ f) (ce cf : Fin t)
    (hfixed : ∀ ω ∈ U, ω e = ce ∧ ω f = cf) :
    LocalLemma.uniformProbability U ≤ 1 / (t : ℝ) ^ 2 := by
  classical
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  let recolor : Fin t × Fin t × { ω // ω ∈ U } → (E → Fin t) :=
    fun p ↦ Function.update (Function.update p.2.2.1 e p.1) f p.2.1
  have hinj : Function.Injective recolor := by
    rintro ⟨x, y, ω⟩ ⟨x', y', ω'⟩ h
    have hy : y = y' := by
      have := congrFun h f
      simpa [recolor] using this
    have hx : x = x' := by
      have := congrFun h e
      simpa [recolor, hef] using this
    subst x'; subst y'
    congr 2
    apply Subtype.ext
    funext z
    by_cases hze : z = e
    · subst z
      exact (hfixed ω.1 ω.2).1.trans (hfixed ω'.1 ω'.2).1.symm
    by_cases hzf : z = f
    · subst z
      exact (hfixed ω.1 ω.2).2.trans (hfixed ω'.1 ω'.2).2.symm
    have := congrFun h z
    simpa [recolor, hze, hzf] using this
  have hcard : t * t * U.card ≤ Fintype.card (E → Fin t) := by
    have := Fintype.card_le_of_injective recolor hinj
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Nat.mul_assoc] using this
  have hN : (0 : ℝ) < Fintype.card (E → Fin t) := by
    exact_mod_cast Fintype.card_pos
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  unfold LocalLemma.uniformProbability
  rw [div_le_iff₀ hN]
  rw [one_div, inv_mul_eq_div]
  rw [le_div_iff₀ (sq_pos_of_pos htR)]
  have hcardR : (t : ℝ) * t * U.card ≤ Fintype.card (E → Fin t) := by
    exact_mod_cast hcard
  nlinarith

lemma uniformProbability_cycle_le_inv_sq {n oldK t : ℕ} (ht : 0 < t)
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : CycleIndex old) :
    LocalLemma.uniformProbability (badEvent (t := t) (Sum.inr (Sum.inl i))) ≤
      1 / (t : ℝ) ^ 2 := by
  classical
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  let U := badEvent (t := t) (Sum.inr (Sum.inl i))
  let recolor : Fin t × Fin t × { ω // ω ∈ U } → Assignment n t :=
    fun p ↦ Function.update (Function.update p.2.2.1 i.e23 p.1) i.e30 p.2.1
  have hmem (ω : Assignment n t) (hω : ω ∈ U) :
      ω i.e01 = ω i.e23 ∧ ω i.e12 = ω i.e30 ∧ ω i.e01 ≠ ω i.e12 := by
    simpa [U, badEvent] using hω
  have hinj : Function.Injective recolor := by
    rintro ⟨x, y, ω⟩ ⟨x', y', ω'⟩ h
    have hy : y = y' := by
      have := congrFun h i.e30
      simpa [recolor] using this
    have hx : x = x' := by
      have := congrFun h i.e23
      simpa [recolor, i.e23_ne_e30] using this
    subst x'; subst y'
    congr 2
    apply Subtype.ext
    funext z
    by_cases hz23 : z = i.e23
    · subst z
      have hret : ω.1 i.e01 = ω'.1 i.e01 := by
        have := congrFun h i.e01
        simpa [recolor, i.e01_ne_e23, i.e01_ne_e30] using this
      exact (hmem ω.1 ω.2).1.symm.trans (hret.trans (hmem ω'.1 ω'.2).1)
    by_cases hz30 : z = i.e30
    · subst z
      have hret : ω.1 i.e12 = ω'.1 i.e12 := by
        have := congrFun h i.e12
        simpa [recolor, i.e12_ne_e23, i.e12_ne_e30] using this
      exact (hmem ω.1 ω.2).2.1.symm.trans
        (hret.trans (hmem ω'.1 ω'.2).2.1)
    have := congrFun h z
    simpa [recolor, hz23, hz30] using this
  have hcard : t * t * U.card ≤ Fintype.card (Assignment n t) := by
    have := Fintype.card_le_of_injective recolor hinj
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Nat.mul_assoc] using this
  have hN : (0 : ℝ) < Fintype.card (Assignment n t) := by
    exact_mod_cast Fintype.card_pos
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  unfold LocalLemma.uniformProbability
  rw [div_le_iff₀ hN]
  rw [one_div, inv_mul_eq_div]
  rw [le_div_iff₀ (sq_pos_of_pos htR)]
  have hcardR : (t : ℝ) * t * U.card ≤ Fintype.card (Assignment n t) := by
    exact_mod_cast hcard
  nlinarith

lemma badEvent_probability_le {n oldK t : ℕ} (ht : 0 < t)
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : BadIndex (t := t) old) :
    LocalLemma.uniformProbability (badEvent i) ≤ 1 / (t : ℝ) ^ 2 := by
  rcases i with i | i
  · apply uniformProbability_le_inv_sq_of_fixed_pair ht _ i.leftEdge i.rightEdge
      i.leftEdge_ne_rightEdge i.color i.color
    intro ω hω
    simpa [badEvent] using hω
  · rcases i with i | i
    · exact uniformProbability_cycle_le_inv_sq ht i
    · apply uniformProbability_le_inv_sq_of_fixed_pair ht _ i.e12 i.e30
        i.e12_ne_e30 i.color i.color
      intro ω hω
      simpa [badEvent] using hω

/-! ## Support dependence and the local lemma -/

/-- The lopsidependency relation is intersection of coordinate supports. -/
def dependent {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i j : BadIndex (t := t) old) : Prop :=
  ¬ Disjoint (badSupport i) (badSupport j)

lemma avoiding_dependsOn_complement {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : BadIndex (t := t) old) (S : Finset (BadIndex (t := t) old))
    (hS : ∀ j ∈ S, ¬ dependent i j) :
    DependsOn (Finset.univ \ badSupport i) (LocalLemma.avoiding badEvent S) := by
  intro ω ω' heq
  simp only [LocalLemma.avoiding, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h j hj hbad
    apply h j hj
    have hd : Disjoint (badSupport i) (badSupport j) := by
      exact Classical.not_not.mp (hS j hj)
    apply (badEvent_dependsOn j ω' ω ?_).mp hbad
    intro e he
    apply (heq e ?_).symm
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e,
      fun hei ↦ Finset.disjoint_left.mp hd hei he⟩
  · intro h j hj hbad
    apply h j hj
    have hd : Disjoint (badSupport i) (badSupport j) := by
      exact Classical.not_not.mp (hS j hj)
    apply (badEvent_dependsOn j ω ω' ?_).mp hbad
    intro e he
    apply heq e
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e,
      fun hei ↦ Finset.disjoint_left.mp hd hei he⟩

lemma badEvent_independent_of_non_neighbours {n oldK t : ℕ} (ht : 0 < t)
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : BadIndex (t := t) old) (S : Finset (BadIndex (t := t) old))
    (hS : ∀ j ∈ S, ¬ dependent i j) :
    LocalLemma.uniformProbability
        (badEvent i ∩ LocalLemma.avoiding badEvent S) =
      LocalLemma.uniformProbability (badEvent i) *
        LocalLemma.uniformProbability (LocalLemma.avoiding badEvent S) := by
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  exact uniformProbability_inter_eq_mul (badSupport i) _ _
    (badEvent_dependsOn i)
    (avoiding_dependsOn_complement i S hS)

/-- The finite set of raw bad events using a given fresh-colour coordinate. -/
def eventsThrough {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (e : EdgeN n) : Finset (BadIndex (t := t) old) :=
  Finset.univ.filter fun i ↦ e ∈ badSupport i

def wedgesThrough {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (e : EdgeN n) : Finset (WedgeIndex (t := t) old) :=
  Finset.univ.filter fun i ↦ e ∈ i.support

def cyclesThrough {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (e : EdgeN n) : Finset (CycleIndex old) :=
  Finset.univ.filter fun i ↦ e ∈ i.support

def crossesThrough {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (e : EdgeN n) : Finset (CrossIndex (t := t) old) :=
  Finset.univ.filter fun i ↦ e ∈ i.support

/-! ### Leave-incidence estimates from (P4) -/

/-- The other endpoint of `e`, when `x` is an endpoint; its value away
from that case is irrelevant. -/
def otherAt {n : ℕ} (x : Fin n) (e : EdgeN n) : Fin n :=
  if h : x ∈ e.1 then Sym2.Mem.other h else x

lemma otherAt_spec {n : ℕ} (x : Fin n) (e : EdgeN n) (hx : x ∈ e.1) :
    s(x, otherAt x e) = e.1 := by
  simp only [otherAt, dif_pos hx]
  exact Sym2.other_spec hx

lemma otherAt_ne {n : ℕ} (x : Fin n) (e : EdgeN n) (hx : x ∈ e.1) :
    otherAt x e ≠ x := by
  simp only [otherAt, dif_pos hx]
  apply Sym2.other_ne
  simpa [SimpleGraph.mem_edgeSet] using e.2

/-- Leave edges incident with a specified vertex. -/
def incidentLeaves {n oldK B : ℕ} (P : PartialGood n oldK B) (x : Fin n) :
    Finset (EdgeN n) :=
  Finset.univ.filter fun e ↦
    x ∈ e.1.toFinset ∧ completionOld P e = none

lemma incidentLeaves_card_le {n oldK B : ℕ}
    (P : PartialGood n oldK B) (x : Fin n) :
    (incidentLeaves P x).card ≤ B := by
  let N := Finset.univ.filter fun y : Fin n ↦ y ≠ x ∧ P.old x y = none
  have hmap : ∀ e ∈ incidentLeaves P x, otherAt x e ∈ N := by
    intro e he
    have he' := (Finset.mem_filter.mp he).2
    have hx : x ∈ e.1 := Sym2.mem_toFinset.mp he'.1
    have hne : otherAt x e ≠ x := otherAt_ne x e hx
    have hedge : Completion.topEdge x (otherAt x e) hne.symm = e := by
      apply Subtype.ext
      exact otherAt_spec x e hx
    have hold : P.old x (otherAt x e) = none := by
      have h := he'.2
      rw [← hedge] at h
      simpa using h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hold⟩
  have hinj : Set.InjOn (otherAt x) (incidentLeaves P x) := by
    intro e he f hf hef
    have he' := (Finset.mem_filter.mp he).2
    have hf' := (Finset.mem_filter.mp hf).2
    have hxe : x ∈ e.1 := Sym2.mem_toFinset.mp he'.1
    have hxf : x ∈ f.1 := Sym2.mem_toFinset.mp hf'.1
    apply Subtype.ext
    calc
      e.1 = s(x, otherAt x e) := (otherAt_spec x e hxe).symm
      _ = s(x, otherAt x f) := by rw [hef]
      _ = f.1 := otherAt_spec x f hxf
  calc
    (incidentLeaves P x).card ≤ N.card :=
      Finset.card_le_card_of_injOn (otherAt x) hmap hinj
    _ = leaveDegree P.old x := rfl
    _ ≤ B := P.p4 x

/-- All leave edges meeting a fixed complete-graph edge. -/
def adjacentLeaves {n oldK B : ℕ} (P : PartialGood n oldK B)
    (e : EdgeN n) : Finset (EdgeN n) :=
  Finset.univ.filter fun f ↦
    ¬ Disjoint e.1.toFinset f.1.toFinset ∧ completionOld P f = none

lemma adjacentLeaves_card_le {n oldK B : ℕ}
    (P : PartialGood n oldK B) (e : EdgeN n) :
    (adjacentLeaves P e).card ≤ 2 * B := by
  let U := e.1.toFinset.biUnion (incidentLeaves P)
  have hsub : adjacentLeaves P e ⊆ U := by
    intro f hf
    have hf' := (Finset.mem_filter.mp hf).2
    rw [Finset.not_disjoint_iff] at hf'
    obtain ⟨x, hxe, hxf⟩ := hf'.1
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hxe, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxf, hf'.2⟩⟩
  have hcarde : e.1.toFinset.card = 2 := by
    apply Sym2.card_toFinset_of_not_isDiag e.1
    simpa [SimpleGraph.mem_edgeSet] using e.2
  calc
    (adjacentLeaves P e).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ e.1.toFinset, (incidentLeaves P x).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ e.1.toFinset, B := by
      gcongr with x hx
      exact incidentLeaves_card_le P x
    _ = e.1.toFinset.card * B := by simp
    _ = 2 * B := by rw [hcarde]

lemma cycleScratch_edgeFinset_card {n : ℕ} (e : EdgeN n) : e.1.toFinset.card = 2 := by
  apply Sym2.card_toFinset_of_not_isDiag e.1
  simpa [SimpleGraph.mem_edgeSet] using e.2

lemma cycleScratch_edge_ext {n : ℕ} {e f : EdgeN n}
    (h : e.1.toFinset = f.1.toFinset) : e = f := by
  apply Subtype.ext
  apply Sym2.ext
  intro x
  have hx := Finset.ext_iff.mp h x
  simpa only [Sym2.mem_toFinset] using hx

lemma cycleScratch_cross_meets {n : ℕ} {a b c d : EdgeN n}
    (hu : a.1.toFinset ∪ c.1.toFinset = b.1.toFinset ∪ d.1.toFinset)
    (had : a ≠ d) : ¬ Disjoint a.1.toFinset b.1.toFinset := by
  intro hab
  have hsub : a.1.toFinset ⊆ d.1.toFinset := by
    intro x hxa
    have hx : x ∈ b.1.toFinset ∪ d.1.toFinset := by
      rw [← hu]
      exact Finset.mem_union_left _ hxa
    rcases Finset.mem_union.mp hx with hxb | hxd
    · exact (Finset.disjoint_left.mp hab hxa hxb).elim
    · exact hxd
  have hcard : d.1.toFinset.card ≤ a.1.toFinset.card := by
    rw [cycleScratch_edgeFinset_card, cycleScratch_edgeFinset_card]
  have hsets := Finset.eq_of_subset_of_card_le hsub hcard
  exact had (cycleScratch_edge_ext hsets)

lemma cycleScratch_eq_of_disjoint_union_eq {n : ℕ} {a b c : EdgeN n}
    (hab : Disjoint a.1.toFinset b.1.toFinset)
    (hac : Disjoint a.1.toFinset c.1.toFinset)
    (hu : a.1.toFinset ∪ b.1.toFinset = a.1.toFinset ∪ c.1.toFinset) : b = c := by
  apply cycleScratch_edge_ext
  ext x
  constructor
  · intro hxb
    have hx : x ∈ a.1.toFinset ∪ c.1.toFinset := by
      rw [← hu]
      exact Finset.mem_union_right _ hxb
    rcases Finset.mem_union.mp hx with hxa | hxc
    · exact (Finset.disjoint_left.mp hab hxa hxb).elim
    · exact hxc
  · intro hxc
    have hx : x ∈ a.1.toFinset ∪ b.1.toFinset := by
      rw [hu]
      exact Finset.mem_union_right _ hxc
    rcases Finset.mem_union.mp hx with hxa | hxb
    · exact (Finset.disjoint_left.mp hac hxa hxc).elim
    · exact hxb

lemma cycleScratch_e01_e12_meet {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))} (i : CycleIndex old) :
    ¬ Disjoint i.e01.1.toFinset i.e12.1.toFinset :=
  cycleScratch_cross_meets i.sameVertices i.e01_ne_e30

lemma cycleScratch_e01_e30_meet {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))} (i : CycleIndex old) :
    ¬ Disjoint i.e01.1.toFinset i.e30.1.toFinset :=
  cycleScratch_cross_meets (i.sameVertices.trans (Finset.union_comm _ _)) i.e01_ne_e12

lemma cycleScratch_e23_e12_meet {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))} (i : CycleIndex old) :
    ¬ Disjoint i.e23.1.toFinset i.e12.1.toFinset :=
  cycleScratch_cross_meets ((Finset.union_comm _ _).trans i.sameVertices) i.e23_ne_e30

lemma cycleScratch_e23_e30_meet {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))} (i : CycleIndex old) :
    ¬ Disjoint i.e23.1.toFinset i.e30.1.toFinset :=
  cycleScratch_cross_meets
    ((Finset.union_comm _ _).trans (i.sameVertices.trans (Finset.union_comm _ _)))
    i.e12_ne_e23.symm

def cyclesAt01Scratch {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))} (e : EdgeN n) :
    Finset (CycleIndex old) := Finset.univ.filter fun i ↦ i.e01 = e
def cyclesAt12Scratch {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))} (e : EdgeN n) :
    Finset (CycleIndex old) := Finset.univ.filter fun i ↦ i.e12 = e
def cyclesAt23Scratch {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))} (e : EdgeN n) :
    Finset (CycleIndex old) := Finset.univ.filter fun i ↦ i.e23 = e
def cyclesAt30Scratch {n oldK : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))} (e : EdgeN n) :
    Finset (CycleIndex old) := Finset.univ.filter fun i ↦ i.e30 = e

lemma cyclesAt01Scratch_card_le {n oldK B : ℕ} (P : PartialGood n oldK B)
    (e : EdgeN n) : (cyclesAt01Scratch (old := completionOld P) e).card ≤ 4 * B ^ 2 := by
  let S := cyclesAt01Scratch (old := completionOld P) e
  let A := adjacentLeaves P e
  let T := A.product A
  let code : CycleIndex (completionOld P) → EdgeN n × EdgeN n := fun i ↦ (i.e12, i.e30)
  have hmap : Set.MapsTo code (S : Set (CycleIndex (completionOld P)))
      (T : Set (EdgeN n × EdgeN n)) := by
    intro i hi
    have hi01 : i.e01 = e := (Finset.mem_filter.mp hi).2
    change (i.e12, i.e30) ∈ (A.product A : Finset (EdgeN n × EdgeN n))
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.e12Leave⟩
      rw [← hi01]
      exact cycleScratch_e01_e12_meet i
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.e30Leave⟩
      rw [← hi01]
      exact cycleScratch_e01_e30_meet i
  have hinj : (S : Set (CycleIndex (completionOld P))).InjOn code := by
    intro i hi j hj hcode
    have hi01 : i.e01 = e := (Finset.mem_filter.mp hi).2
    have hj01 : j.e01 = e := (Finset.mem_filter.mp hj).2
    have h01 : i.e01 = j.e01 := hi01.trans hj01.symm
    have h12 : i.e12 = j.e12 := congrArg Prod.fst hcode
    have h30 : i.e30 = j.e30 := congrArg Prod.snd hcode
    have hu : i.e01.1.toFinset ∪ i.e23.1.toFinset =
        i.e01.1.toFinset ∪ j.e23.1.toFinset := by
      calc
        _ = i.e12.1.toFinset ∪ i.e30.1.toFinset := i.sameVertices
        _ = j.e12.1.toFinset ∪ j.e30.1.toFinset := by rw [h12, h30]
        _ = j.e01.1.toFinset ∪ j.e23.1.toFinset := j.sameVertices.symm
        _ = i.e01.1.toFinset ∪ j.e23.1.toFinset := by rw [h01]
    have hjdis : Disjoint i.e01.1.toFinset j.e23.1.toFinset := by
      rw [h01]
      exact j.firstMatching
    have h23 := cycleScratch_eq_of_disjoint_union_eq i.firstMatching hjdis hu
    exact cycleIndex_ext h01 h12 h23 h30
  have hadj := adjacentLeaves_card_le P e
  calc
    S.card ≤ T.card := Finset.card_le_card_of_injOn code hmap hinj
    _ = A.card * A.card := Finset.card_product A A
    _ ≤ (2 * B) * (2 * B) := Nat.mul_le_mul hadj hadj
    _ = 4 * B ^ 2 := by ring

lemma cyclesAt12Scratch_card_le {n oldK B : ℕ} (P : PartialGood n oldK B)
    (e : EdgeN n) : (cyclesAt12Scratch (old := completionOld P) e).card ≤ 4 * B ^ 2 := by
  let S := cyclesAt12Scratch (old := completionOld P) e
  let A := adjacentLeaves P e
  let T := A.product A
  let code : CycleIndex (completionOld P) → EdgeN n × EdgeN n := fun i ↦ (i.e01, i.e23)
  have hmap : Set.MapsTo code (S : Set (CycleIndex (completionOld P)))
      (T : Set (EdgeN n × EdgeN n)) := by
    intro i hi
    have hi12 : i.e12 = e := (Finset.mem_filter.mp hi).2
    change (i.e01, i.e23) ∈ (A.product A : Finset (EdgeN n × EdgeN n))
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.e01Leave⟩
      rw [← hi12]
      simpa [disjoint_comm] using cycleScratch_e01_e12_meet i
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.e23Leave⟩
      rw [← hi12]
      simpa [disjoint_comm] using cycleScratch_e23_e12_meet i
  have hinj : (S : Set (CycleIndex (completionOld P))).InjOn code := by
    intro i hi j hj hcode
    have hi12 : i.e12 = e := (Finset.mem_filter.mp hi).2
    have hj12 : j.e12 = e := (Finset.mem_filter.mp hj).2
    have h12 : i.e12 = j.e12 := hi12.trans hj12.symm
    have h01 : i.e01 = j.e01 := congrArg Prod.fst hcode
    have h23 : i.e23 = j.e23 := congrArg Prod.snd hcode
    have hu : i.e12.1.toFinset ∪ i.e30.1.toFinset =
        i.e12.1.toFinset ∪ j.e30.1.toFinset := by
      calc
        _ = i.e01.1.toFinset ∪ i.e23.1.toFinset := i.sameVertices.symm
        _ = j.e01.1.toFinset ∪ j.e23.1.toFinset := by rw [h01, h23]
        _ = j.e12.1.toFinset ∪ j.e30.1.toFinset := j.sameVertices
        _ = i.e12.1.toFinset ∪ j.e30.1.toFinset := by rw [h12]
    have hjdis : Disjoint i.e12.1.toFinset j.e30.1.toFinset := by
      rw [h12]
      exact j.secondMatching
    have h30 := cycleScratch_eq_of_disjoint_union_eq i.secondMatching hjdis hu
    exact cycleIndex_ext h01 h12 h23 h30
  have hadj := adjacentLeaves_card_le P e
  calc
    S.card ≤ T.card := Finset.card_le_card_of_injOn code hmap hinj
    _ = A.card * A.card := Finset.card_product A A
    _ ≤ (2 * B) * (2 * B) := Nat.mul_le_mul hadj hadj
    _ = 4 * B ^ 2 := by ring

lemma cyclesAt23Scratch_card_le {n oldK B : ℕ} (P : PartialGood n oldK B)
    (e : EdgeN n) : (cyclesAt23Scratch (old := completionOld P) e).card ≤ 4 * B ^ 2 := by
  let S := cyclesAt23Scratch (old := completionOld P) e
  let A := adjacentLeaves P e
  let T := A.product A
  let code : CycleIndex (completionOld P) → EdgeN n × EdgeN n := fun i ↦ (i.e12, i.e30)
  have hmap : Set.MapsTo code (S : Set (CycleIndex (completionOld P)))
      (T : Set (EdgeN n × EdgeN n)) := by
    intro i hi
    have hi23 : i.e23 = e := (Finset.mem_filter.mp hi).2
    change (i.e12, i.e30) ∈ (A.product A : Finset (EdgeN n × EdgeN n))
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.e12Leave⟩
      rw [← hi23]
      exact cycleScratch_e23_e12_meet i
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.e30Leave⟩
      rw [← hi23]
      exact cycleScratch_e23_e30_meet i
  have hinj : (S : Set (CycleIndex (completionOld P))).InjOn code := by
    intro i hi j hj hcode
    have hi23 : i.e23 = e := (Finset.mem_filter.mp hi).2
    have hj23 : j.e23 = e := (Finset.mem_filter.mp hj).2
    have h23 : i.e23 = j.e23 := hi23.trans hj23.symm
    have h12 : i.e12 = j.e12 := congrArg Prod.fst hcode
    have h30 : i.e30 = j.e30 := congrArg Prod.snd hcode
    have hu : i.e23.1.toFinset ∪ i.e01.1.toFinset =
        i.e23.1.toFinset ∪ j.e01.1.toFinset := by
      calc
        _ = i.e01.1.toFinset ∪ i.e23.1.toFinset := Finset.union_comm _ _
        _ = i.e12.1.toFinset ∪ i.e30.1.toFinset := i.sameVertices
        _ = j.e12.1.toFinset ∪ j.e30.1.toFinset := by rw [h12, h30]
        _ = j.e01.1.toFinset ∪ j.e23.1.toFinset := j.sameVertices.symm
        _ = j.e23.1.toFinset ∪ j.e01.1.toFinset := Finset.union_comm _ _
        _ = i.e23.1.toFinset ∪ j.e01.1.toFinset := by rw [h23]
    have hjdis : Disjoint i.e23.1.toFinset j.e01.1.toFinset := by
      rw [h23]
      exact j.firstMatching.symm
    have h01 := cycleScratch_eq_of_disjoint_union_eq i.firstMatching.symm hjdis hu
    exact cycleIndex_ext h01 h12 h23 h30
  have hadj := adjacentLeaves_card_le P e
  calc
    S.card ≤ T.card := Finset.card_le_card_of_injOn code hmap hinj
    _ = A.card * A.card := Finset.card_product A A
    _ ≤ (2 * B) * (2 * B) := Nat.mul_le_mul hadj hadj
    _ = 4 * B ^ 2 := by ring

lemma cyclesAt30Scratch_card_le {n oldK B : ℕ} (P : PartialGood n oldK B)
    (e : EdgeN n) : (cyclesAt30Scratch (old := completionOld P) e).card ≤ 4 * B ^ 2 := by
  let S := cyclesAt30Scratch (old := completionOld P) e
  let A := adjacentLeaves P e
  let T := A.product A
  let code : CycleIndex (completionOld P) → EdgeN n × EdgeN n := fun i ↦ (i.e01, i.e23)
  have hmap : Set.MapsTo code (S : Set (CycleIndex (completionOld P)))
      (T : Set (EdgeN n × EdgeN n)) := by
    intro i hi
    have hi30 : i.e30 = e := (Finset.mem_filter.mp hi).2
    change (i.e01, i.e23) ∈ (A.product A : Finset (EdgeN n × EdgeN n))
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.e01Leave⟩
      rw [← hi30]
      simpa [disjoint_comm] using cycleScratch_e01_e30_meet i
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.e23Leave⟩
      rw [← hi30]
      simpa [disjoint_comm] using cycleScratch_e23_e30_meet i
  have hinj : (S : Set (CycleIndex (completionOld P))).InjOn code := by
    intro i hi j hj hcode
    have hi30 : i.e30 = e := (Finset.mem_filter.mp hi).2
    have hj30 : j.e30 = e := (Finset.mem_filter.mp hj).2
    have h30 : i.e30 = j.e30 := hi30.trans hj30.symm
    have h01 : i.e01 = j.e01 := congrArg Prod.fst hcode
    have h23 : i.e23 = j.e23 := congrArg Prod.snd hcode
    have hu : i.e30.1.toFinset ∪ i.e12.1.toFinset =
        i.e30.1.toFinset ∪ j.e12.1.toFinset := by
      calc
        _ = i.e12.1.toFinset ∪ i.e30.1.toFinset := Finset.union_comm _ _
        _ = i.e01.1.toFinset ∪ i.e23.1.toFinset := i.sameVertices.symm
        _ = j.e01.1.toFinset ∪ j.e23.1.toFinset := by rw [h01, h23]
        _ = j.e12.1.toFinset ∪ j.e30.1.toFinset := j.sameVertices
        _ = j.e30.1.toFinset ∪ j.e12.1.toFinset := Finset.union_comm _ _
        _ = i.e30.1.toFinset ∪ j.e12.1.toFinset := by rw [h30]
    have hjdis : Disjoint i.e30.1.toFinset j.e12.1.toFinset := by
      rw [h30]
      exact j.secondMatching.symm
    have h12 := cycleScratch_eq_of_disjoint_union_eq i.secondMatching.symm hjdis hu
    exact cycleIndex_ext h01 h12 h23 h30
  have hadj := adjacentLeaves_card_le P e
  calc
    S.card ≤ T.card := Finset.card_le_card_of_injOn code hmap hinj
    _ = A.card * A.card := Finset.card_product A A
    _ ≤ (2 * B) * (2 * B) := Nat.mul_le_mul hadj hadj
    _ = 4 * B ^ 2 := by ring

theorem cyclesThrough_completionOld_card_le {n oldK B : ℕ}
    (P : PartialGood n oldK B) (e : EdgeN n) :
    (cyclesThrough (old := completionOld P) e).card ≤ 16 * B ^ 2 := by
  let S01 := cyclesAt01Scratch (old := completionOld P) e
  let S12 := cyclesAt12Scratch (old := completionOld P) e
  let S23 := cyclesAt23Scratch (old := completionOld P) e
  let S30 := cyclesAt30Scratch (old := completionOld P) e
  have hsub : cyclesThrough (old := completionOld P) e ⊆
      S01 ∪ S12 ∪ S23 ∪ S30 := by
    intro i hi
    have hs : e ∈ i.support := (Finset.mem_filter.mp hi).2
    simp only [CycleIndex.support, Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [Finset.mem_union, S01, S12, S23, S30, cyclesAt01Scratch,
      cyclesAt12Scratch, cyclesAt23Scratch, cyclesAt30Scratch,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hs with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h.symm))
    · exact Or.inl (Or.inl (Or.inr h.symm))
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr h.symm
  have h01 : S01.card ≤ 4 * B ^ 2 := cyclesAt01Scratch_card_le P e
  have h12 : S12.card ≤ 4 * B ^ 2 := cyclesAt12Scratch_card_le P e
  have h23 : S23.card ≤ 4 * B ^ 2 := cyclesAt23Scratch_card_le P e
  have h30 : S30.card ≤ 4 * B ^ 2 := cyclesAt30Scratch_card_le P e
  have hU1 := Finset.card_union_le S01 S12
  have hU2 := Finset.card_union_le (S01 ∪ S12) S23
  have hU3 := Finset.card_union_le (S01 ∪ S12 ∪ S23) S30
  have hmain := Finset.card_le_card hsub
  omega

def wedgeCode {n oldK B t : ℕ} (P : PartialGood n oldK B)
    (e : EdgeN n) (i : WedgeIndex (t := t) (completionOld P)) :
    Bool × (EdgeN n × Fin t) :=
  if i.left = e then (false, i.right, i.color) else (true, i.left, i.color)

lemma wedge_ext {n oldK B t : ℕ} {P : PartialGood n oldK B}
    {i j : WedgeIndex (t := t) (completionOld P)}
    (hl : i.left = j.left) (hr : i.right = j.right)
    (hc : i.color = j.color) : i = j := by
  cases i
  cases j
  simp_all

theorem wedgesThrough_completionOld_card_le {n oldK B t : ℕ}
    (P : PartialGood n oldK B) (e : EdgeN n) :
    (wedgesThrough (t := t) (old := completionOld P) e).card ≤ 4 * B * t := by
  let S := wedgesThrough (t := t) (old := completionOld P) e
  let T : Finset (Bool × (EdgeN n × Fin t)) :=
    Finset.univ.product ((adjacentLeaves P e).product Finset.univ)
  have hmap : ∀ i ∈ S, wedgeCode P e i ∈ T := by
    intro i hi
    have hisup : e ∈ i.support := (Finset.mem_filter.mp hi).2
    have heq : e = i.left ∨ e = i.right := by
      simpa [WedgeIndex.support, WedgeIndex.leftEdge, WedgeIndex.rightEdge] using hisup
    unfold wedgeCode T
    split_ifs with hleft
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.rightLeave⟩
      simpa [hleft] using i.adjacent
    · have hright : i.right = e := by
        rcases heq with he | he
        · exact (hleft he.symm).elim
        · exact he.symm
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, i.leftLeave⟩
      rw [← hright]
      exact fun hdisj ↦ i.adjacent hdisj.symm
  have hinj : Set.InjOn (wedgeCode P e)
      {i | i ∈ wedgesThrough (t := t) (old := completionOld P) e} := by
    intro i hi j hj hcode
    unfold wedgeCode at hcode
    split_ifs at hcode with hiLeft hjLeft
    · have hright : i.right = j.right := congrArg (fun q ↦ q.2.1) hcode
      have hcolor : i.color = j.color := congrArg (fun q ↦ q.2.2) hcode
      exact wedge_ext (hiLeft.trans hjLeft.symm) hright hcolor
    · simp at hcode
    · simp at hcode
    · have hleft : i.left = j.left := congrArg (fun q ↦ q.2.1) hcode
      have hcolor : i.color = j.color := congrArg (fun q ↦ q.2.2) hcode
      have hjLeft' : j.left ≠ e := fun h ↦ hiLeft (hleft.trans h)
      have hiSup : e ∈ i.support := (Finset.mem_filter.mp hi).2
      have hjSup : e ∈ j.support := (Finset.mem_filter.mp hj).2
      have hiRight : i.right = e := by
        have h : e = i.left ∨ e = i.right := by
          simpa [WedgeIndex.support, WedgeIndex.leftEdge,
            WedgeIndex.rightEdge] using hiSup
        rcases h with h | h
        · exact (hiLeft h.symm).elim
        · exact h.symm
      have hjRight : j.right = e := by
        have h : e = j.left ∨ e = j.right := by
          simpa [WedgeIndex.support, WedgeIndex.leftEdge,
            WedgeIndex.rightEdge] using hjSup
        rcases h with h | h
        · exact (hjLeft' h.symm).elim
        · exact h.symm
      exact wedge_ext hleft (hiRight.trans hjRight.symm) hcolor
  have hadj := adjacentLeaves_card_le P e
  calc
    S.card ≤ T.card :=
      Finset.card_le_card_of_injOn (wedgeCode P e) hmap hinj
    _ = 2 * ((adjacentLeaves P e).card * t) := by simp [T]
    _ ≤ 2 * ((2 * B) * t) := by
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right t hadj)
    _ = 4 * B * t := by
      rw [← Nat.mul_assoc 2 (2 * B) t, ← Nat.mul_assoc 2 2 B]

def orderedEnds {n : ℕ} (e : EdgeN n) : Fin n × Fin n :=
  if e.1.out.1 < e.1.out.2 then e.1.out else e.1.out.swap

lemma edge_out_ne {n : ℕ} (e : EdgeN n) : e.1.out.1 ≠ e.1.out.2 := by
  intro h
  have heq : e.1 = s(e.1.out.1, e.1.out.2) := by
    simpa [Sym2.mk] using e.1.out_eq.symm
  have he := e.2
  rw [heq, h] at he
  simpa [SimpleGraph.mem_edgeSet] using he

lemma orderedEnds_lt {n : ℕ} (e : EdgeN n) :
    (orderedEnds e).1 < (orderedEnds e).2 := by
  unfold orderedEnds
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) (edge_out_ne e).symm

lemma edge_eq_mk_orderedEnds {n : ℕ} (e : EdgeN n) :
    e.1 = s((orderedEnds e).1, (orderedEnds e).2) := by
  unfold orderedEnds
  split_ifs
  · simpa [Sym2.mk] using e.1.out_eq.symm
  · have hout : e.1 = s(e.1.out.1, e.1.out.2) := by
      simpa [Sym2.mk] using e.1.out_eq.symm
    exact hout.trans Sym2.eq_swap

lemma orderedEnds_injective {n : ℕ} : Function.Injective (@orderedEnds n) := by
  intro e f h
  apply Subtype.ext
  rw [edge_eq_mk_orderedEnds e, edge_eq_mk_orderedEnds f, h]

lemma edge_toFinset_card {n : ℕ} (e : EdgeN n) : e.1.toFinset.card = 2 := by
  apply Sym2.card_toFinset_of_not_isDiag e.1
  simpa [SimpleGraph.mem_edgeSet] using e.2

lemma cross_ne_of_disjoint {n : ℕ} {x y u v : Fin n}
    (h : Disjoint ({x, y} : Finset (Fin n)) {u, v}) :
    x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v := by
  rw [Finset.disjoint_left] at h
  constructor
  · intro e
    exact h (a := x) (by simp) (by simp [e])
  constructor
  · intro e
    exact h (a := x) (by simp) (by simp [e])
  constructor
  · intro e
    exact h (a := y) (by simp) (by simp [e])
  · intro e
    exact h (a := y) (by simp) (by simp [e])

lemma old_endpoints_in_fresh_union {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (i : CrossIndex (t := t) old) (g : EdgeN n)
    (hg : g = i.old01 ∨ g = i.old23) :
    g.1.toFinset ⊆ i.e12.1.toFinset ∪ i.e30.1.toFinset := by
  let F := i.e12.1.toFinset ∪ i.e30.1.toFinset
  let U := i.old01.1.toFinset ∪ i.old23.1.toFinset ∪ F
  have hFcard : F.card = 4 := by
    dsimp [F]
    rw [Finset.card_union_of_disjoint i.freshMatching]
    simp [edge_toFinset_card]
  have hFU : F ⊆ U := by
    intro x hx
    simp only [U, Finset.mem_union]
    exact Or.inr hx
  have hUcard : U.card ≤ 4 := by
    simpa only [U, F, union_assoc] using i.atMostFourVertices
  have hUF : U = F := by
    apply Finset.Subset.antisymm
    · have hEq : F = U := Finset.eq_of_subset_of_card_le hFU (by omega)
      exact hEq.symm.subset
    · exact hFU
  change g.1.toFinset ⊆ F
  rw [← hUF]
  rcases hg with rfl | rfl
  · intro z hz
    simp only [U, mem_union]
    exact Or.inl (Or.inl hz)
  · intro z hz
    simp only [U, mem_union]
    exact Or.inl (Or.inr hz)

/-- An edge distinct from two disjoint edges on their four endpoints is
one of the four cross edges. -/
lemma edge_cross_cases {n : ℕ} {x y u v : Fin n}
    (hxy : x ≠ y) (huv : u ≠ v)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v)
    (g : EdgeN n)
    (hsub : g.1.toFinset ⊆ ({x, y} : Finset (Fin n)) ∪ {u, v})
    (hne₁ : g.1 ≠ s(x, y)) (hne₂ : g.1 ≠ s(u, v)) :
    g.1 = s(x, u) ∨ g.1 = s(x, v) ∨ g.1 = s(y, u) ∨ g.1 = s(y, v) := by
  let a := g.1.out.1
  let b := g.1.out.2
  have hg : g.1 = s(a, b) := by
    simpa [a, b, Sym2.mk] using g.1.out_eq.symm
  have hab : a ≠ b := by simpa [a, b] using edge_out_ne g
  rw [hg] at hsub hne₁ hne₂ ⊢
  simp only [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff,
    mem_union, mem_insert, mem_singleton] at hsub
  simp only [Sym2.eq_iff] at hne₁ hne₂ ⊢
  grind

/-- Construction-specific closure consequence used by the cross count. -/
def MonoWedgeClosesE {n k : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))) : Prop :=
  ∀ c x y z (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z),
    old (Completion.topEdge x y hxy) = some c →
    old (Completion.topEdge x z hxz) = some c →
    old (Completion.topEdge y z hyz) ≠ none

/-- The two old edges in a raw cross index form one of the two matchings
between the two fresh edges. -/
lemma cross_old_matching {n k t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hclose : MonoWedgeClosesE old) (i : CrossIndex (t := t) old) :
    let x := (orderedEnds i.e12).1
    let y := (orderedEnds i.e12).2
    let u := (orderedEnds i.e30).1
    let v := (orderedEnds i.e30).2
    (i.old01.1 = s(x, u) ∧ i.old23.1 = s(y, v)) ∨
    (i.old23.1 = s(x, u) ∧ i.old01.1 = s(y, v)) ∨
    (i.old01.1 = s(x, v) ∧ i.old23.1 = s(y, u)) ∨
    (i.old23.1 = s(x, v) ∧ i.old01.1 = s(y, u)) := by
  dsimp only
  let x := (orderedEnds i.e12).1
  let y := (orderedEnds i.e12).2
  let u := (orderedEnds i.e30).1
  let v := (orderedEnds i.e30).2
  have hxy : x ≠ y := ne_of_lt (orderedEnds_lt i.e12)
  have huv : u ≠ v := ne_of_lt (orderedEnds_lt i.e30)
  have he12 : i.e12.1 = s(x, y) := edge_eq_mk_orderedEnds i.e12
  have he30 : i.e30.1 = s(u, v) := edge_eq_mk_orderedEnds i.e30
  have hdisj : Disjoint ({x, y} : Finset (Fin n)) {u, v} := by
    simpa only [← Sym2.toFinset_mk_eq, ← he12, ← he30] using i.freshMatching
  rcases cross_ne_of_disjoint hdisj with ⟨hxu, hxv, hyu, hyv⟩
  have hs₁ := old_endpoints_in_fresh_union i i.old01 (Or.inl rfl)
  have hs₂ := old_endpoints_in_fresh_union i i.old23 (Or.inr rfl)
  rw [he12, he30, Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at hs₁ hs₂
  have hn₁e : i.old01.1 ≠ s(x, y) := fun h ↦
    i.old_fresh_ne.1 (Subtype.ext (h.trans he12.symm))
  have hn₁f : i.old01.1 ≠ s(u, v) := fun h ↦
    i.old_fresh_ne.2.1 (Subtype.ext (h.trans he30.symm))
  have hn₂e : i.old23.1 ≠ s(x, y) := fun h ↦
    i.old_fresh_ne.2.2.1 (Subtype.ext (h.trans he12.symm))
  have hn₂f : i.old23.1 ≠ s(u, v) := fun h ↦
    i.old_fresh_ne.2.2.2 (Subtype.ext (h.trans he30.symm))
  have hc₁ := edge_cross_cases hxy huv hxu hxv hyu hyv i.old01 hs₁ hn₁e hn₁f
  have hc₂ := edge_cross_cases hxy huv hxu hxv hyu hyv i.old23 hs₂ hn₂e hn₂f
  have old01_of {a b : Fin n} (hab : a ≠ b) (h : i.old01.1 = s(a, b)) :
      old (Completion.topEdge a b hab) = some i.oldColor := by
    rw [show Completion.topEdge a b hab = i.old01 from Subtype.ext h.symm]
    exact i.e01Old
  have old23_of {a b : Fin n} (hab : a ≠ b) (h : i.old23.1 = s(a, b)) :
      old (Completion.topEdge a b hab) = some i.oldColor := by
    rw [show Completion.topEdge a b hab = i.old23 from Subtype.ext h.symm]
    exact i.e23Old
  have old01_rev {a b : Fin n} (hab : a ≠ b) (h : i.old01.1 = s(b, a)) :
      old (Completion.topEdge a b hab) = some i.oldColor :=
    old01_of hab (h.trans (Sym2.eq_swap (a := b) (b := a)))
  have old23_rev {a b : Fin n} (hab : a ≠ b) (h : i.old23.1 = s(b, a)) :
      old (Completion.topEdge a b hab) = some i.oldColor :=
    old23_of hab (h.trans (Sym2.eq_swap (a := b) (b := a)))
  have leave12 : old (Completion.topEdge x y hxy) = none := by
    rw [show Completion.topEdge x y hxy = i.e12 from Subtype.ext he12.symm]
    exact i.e12Leave
  have leave30 : old (Completion.topEdge u v huv) = none := by
    rw [show Completion.topEdge u v huv = i.e30 from Subtype.ext he30.symm]
    exact i.e30Leave
  rcases hc₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases hc₂ with h₂ | h₂ | h₂ | h₂
  · exact (i.old01_ne_old23 (Subtype.ext (h₁.trans h₂.symm))).elim
  · exfalso
    exact (hclose i.oldColor x u v hxu hxv huv
      (old01_of hxu h₁) (old23_of hxv h₂)) leave30
  · exfalso
    exact (hclose i.oldColor u x y hxu.symm hyu.symm hxy
      (old01_rev hxu.symm h₁) (old23_rev hyu.symm h₂)) leave12
  · exact Or.inl ⟨h₁, h₂⟩
  · exfalso
    exact (hclose i.oldColor x u v hxu hxv huv
      (old23_of hxu h₂) (old01_of hxv h₁)) leave30
  · exact (i.old01_ne_old23 (Subtype.ext (h₁.trans h₂.symm))).elim
  · exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂⟩))
  · exfalso
    exact (hclose i.oldColor v x y hxv.symm hyv.symm hxy
      (old01_rev hxv.symm h₁) (old23_rev hyv.symm h₂)) leave12
  · exfalso
    exact (hclose i.oldColor u x y hxu.symm hyu.symm hxy
      (old23_rev hxu.symm h₂) (old01_rev hyu.symm h₁)) leave12
  · exact Or.inr (Or.inr (Or.inr ⟨h₂, h₁⟩))
  · exact (i.old01_ne_old23 (Subtype.ext (h₁.trans h₂.symm))).elim
  · exfalso
    exact (hclose i.oldColor y u v hyu hyv huv
      (old01_of hyu h₁) (old23_of hyv h₂)) leave30
  · exact Or.inr (Or.inl ⟨h₂, h₁⟩)
  · exfalso
    exact (hclose i.oldColor v x y hxv.symm hyv.symm hxy
      (old23_rev hxv.symm h₂) (old01_rev hyv.symm h₁)) leave12
  · exfalso
    exact (hclose i.oldColor y u v hyu hyv huv
      (old23_of hyu h₂) (old01_of hyv h₁)) leave30
  · exact (i.old01_ne_old23 (Subtype.ext (h₁.trans h₂.symm))).elim

/-- Exchange the two fresh edges of a cross index. -/
def swapFresh {n k t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (i : CrossIndex (t := t) old) : CrossIndex (t := t) old where
  old01 := i.old01
  old23 := i.old23
  e12 := i.e30
  e30 := i.e12
  old01_ne_old23 := i.old01_ne_old23
  e12_ne_e30 := i.e12_ne_e30.symm
  old_fresh_ne := ⟨i.old_fresh_ne.2.1, i.old_fresh_ne.1,
    i.old_fresh_ne.2.2.2, i.old_fresh_ne.2.2.1⟩
  freshMatching := i.freshMatching.symm
  atMostFourVertices := by
    simpa only [union_assoc, union_left_comm, union_comm] using i.atMostFourVertices
  oldColor := i.oldColor
  e01Old := i.e01Old
  e23Old := i.e23Old
  e12Leave := i.e30Leave
  e30Leave := i.e12Leave
  color := i.color

@[simp] lemma swapFresh_swapFresh {n k t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (i : CrossIndex (t := t) old) : swapFresh (swapFresh i) = i := by
  apply crossIndex_ext <;> rfl

/-- Normalize an index through `e` so that its first fresh edge is `e`. -/
def normalizeAt {n k t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (e : EdgeN n) (i : CrossIndex (t := t) old) : CrossIndex (t := t) old :=
  if i.e12 = e then i else swapFresh i

lemma normalizeAt_e12 {n k t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (e : EdgeN n) (i : CrossIndex (t := t) old)
    (hi : i ∈ crossesThrough (t := t) (old := old) e) :
    (normalizeAt e i).e12 = e := by
  rw [crossesThrough, Finset.mem_filter] at hi
  simp only [Finset.mem_univ, true_and, CrossIndex.support,
    Finset.mem_insert, Finset.mem_singleton] at hi
  unfold normalizeAt
  split_ifs with h
  · exact h
  · have he : e = i.e30 := hi.resolve_left (fun he ↦ h he.symm)
    exact he.symm

lemma normalizeAt_injective_with_bit {n k t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (e : EdgeN n) {i j : CrossIndex (t := t) old}
    (hb : (i.e12 = e) ↔ (j.e12 = e))
    (hn : normalizeAt e i = normalizeAt e j) : i = j := by
  unfold normalizeAt at hn
  by_cases hi : i.e12 = e
  · have hj : j.e12 = e := hb.mp hi
    simp only [hi, hj, if_true] at hn
    exact hn
  · have hj : j.e12 ≠ e := fun hj ↦ hi (hb.mpr hj)
    simp only [hi, hj, if_false] at hn
    have h := congrArg swapFresh hn
    rw [swapFresh_swapFresh, swapFresh_swapFresh] at h
    exact h

def crossEdges {n : ℕ} (x y u v : Fin n) : Finset (Sym2 (Fin n)) :=
  {s(x, u), s(x, v), s(y, u), s(y, v)}

lemma crossEdges_card {n : ℕ} {x y u v : Fin n}
    (hxy : x ≠ y) (huv : u ≠ v)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) :
    (crossEdges x y u v).card = 4 := by
  simp [crossEdges, Sym2.eq_iff, hxy, huv, hxu, hxv, hyu, hyv]

/-- A normalized raw index supplies exactly one obstruction counted by P5. -/
lemma obstruction_of_normalized {n k t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k))
    {oldE : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hcompat : ∀ x y (h : x ≠ y), oldE (Completion.topEdge x y h) = old₂ x y)
    (hclose : MonoWedgeClosesE oldE)
    (i : CrossIndex (t := t) oldE) :
    IsCrossObstruction old₂ (orderedEnds i.e12).1 (orderedEnds i.e12).2
      (orderedEnds i.e30) := by
  let x := (orderedEnds i.e12).1
  let y := (orderedEnds i.e12).2
  let u := (orderedEnds i.e30).1
  let v := (orderedEnds i.e30).2
  have hxy : x ≠ y := ne_of_lt (orderedEnds_lt i.e12)
  have huv : u ≠ v := ne_of_lt (orderedEnds_lt i.e30)
  have he12 : i.e12.1 = s(x, y) := edge_eq_mk_orderedEnds i.e12
  have he30 : i.e30.1 = s(u, v) := edge_eq_mk_orderedEnds i.e30
  have hdisj : Disjoint ({x, y} : Finset (Fin n)) {u, v} := by
    simpa only [← Sym2.toFinset_mk_eq, ← he12, ← he30] using i.freshMatching
  rcases cross_ne_of_disjoint hdisj with ⟨hxu, hxv, hyu, hyv⟩
  have old01_of {a b : Fin n} (hab : a ≠ b) (h : i.old01.1 = s(a, b)) :
      old₂ a b = some i.oldColor := by
    rw [← hcompat a b hab]
    rw [show Completion.topEdge a b hab = i.old01 from Subtype.ext h.symm]
    exact i.e01Old
  have old23_of {a b : Fin n} (hab : a ≠ b) (h : i.old23.1 = s(a, b)) :
      old₂ a b = some i.oldColor := by
    rw [← hcompat a b hab]
    rw [show Completion.topEdge a b hab = i.old23 from Subtype.ext h.symm]
    exact i.e23Old
  have hleave : old₂ u v = none := by
    rw [← hcompat u v huv]
    rw [show Completion.topEdge u v huv = i.e30 from Subtype.ext he30.symm]
    exact i.e30Leave
  have hm := cross_old_matching hclose i
  change (i.old01.1 = s(x, u) ∧ i.old23.1 = s(y, v)) ∨
    (i.old23.1 = s(x, u) ∧ i.old01.1 = s(y, v)) ∨
    (i.old01.1 = s(x, v) ∧ i.old23.1 = s(y, u)) ∨
    (i.old23.1 = s(x, v) ∧ i.old01.1 = s(y, u)) at hm
  refine ⟨orderedEnds_lt i.e30, hxu.symm, hyu.symm, hxv.symm, hyv.symm,
    hleave, i.oldColor, ?_⟩
  rcases hm with hm | hm | hm | hm
  · exact Or.inl ⟨old01_of hxu hm.1, old23_of hyv hm.2⟩
  · exact Or.inl ⟨old23_of hxu hm.1, old01_of hyv hm.2⟩
  · exact Or.inr ⟨old01_of hxv hm.1, old23_of hyu hm.2⟩
  · exact Or.inr ⟨old23_of hxv hm.1, old01_of hyu hm.2⟩

lemma old23_eq_of_normalized_data {n k t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hclose : MonoWedgeClosesE old) {i j : CrossIndex (t := t) old}
    (h12 : i.e12 = j.e12) (h30 : i.e30 = j.e30)
    (h01 : i.old01 = j.old01) : i.old23 = j.old23 := by
  have hi := cross_old_matching hclose i
  have hj := cross_old_matching hclose j
  rw [← h12, ← h30] at hj
  have hxy := orderedEnds_lt i.e12
  have huv := orderedEnds_lt i.e30
  have hd := i.freshMatching
  let x := (orderedEnds i.e12).1
  let y := (orderedEnds i.e12).2
  let u := (orderedEnds i.e30).1
  let v := (orderedEnds i.e30).2
  have he12 : i.e12.1 = s(x, y) := edge_eq_mk_orderedEnds i.e12
  have he30 : i.e30.1 = s(u, v) := edge_eq_mk_orderedEnds i.e30
  have hdisj : Disjoint ({x, y} : Finset (Fin n)) {u, v} := by
    simpa only [← Sym2.toFinset_mk_eq, ← he12, ← he30] using hd
  rcases cross_ne_of_disjoint hdisj with ⟨hxu, hxv, hyu, hyv⟩
  change (i.old01.1 = s(x, u) ∧ i.old23.1 = s(y, v)) ∨
    (i.old23.1 = s(x, u) ∧ i.old01.1 = s(y, v)) ∨
    (i.old01.1 = s(x, v) ∧ i.old23.1 = s(y, u)) ∨
    (i.old23.1 = s(x, v) ∧ i.old01.1 = s(y, u)) at hi
  change (j.old01.1 = s(x, u) ∧ j.old23.1 = s(y, v)) ∨
    (j.old23.1 = s(x, u) ∧ j.old01.1 = s(y, v)) ∨
    (j.old01.1 = s(x, v) ∧ j.old23.1 = s(y, u)) ∨
    (j.old23.1 = s(x, v) ∧ j.old01.1 = s(y, u)) at hj
  apply Subtype.ext
  have h01' : i.old01.1 = j.old01.1 := congrArg Subtype.val h01
  rcases hi with hi | hi | hi | hi <;> rcases hj with hj | hj | hj | hj <;>
    simp_all only [Sym2.eq_iff] <;> grind

abbrev ObstructionChoice {n k : ℕ} (old₂ : Fin n → Fin n → Option (Fin k))
    (e : EdgeN n) :=
  {p : Fin n × Fin n // p ∈ crossObstructions old₂ (orderedEnds e).1 (orderedEnds e).2}

abbrev OldCrossChoice {n k : ℕ} {old₂ : Fin n → Fin n → Option (Fin k)}
    {e : EdgeN n} (p : ObstructionChoice old₂ e) :=
  {g : Sym2 (Fin n) // g ∈ crossEdges (orderedEnds e).1 (orderedEnds e).2 p.1.1 p.1.2}

abbrev CrossCode {n k t : ℕ} (old₂ : Fin n → Fin n → Option (Fin k))
    (e : EdgeN n) := Bool × (Σ p : ObstructionChoice old₂ e, OldCrossChoice p) × Fin t

def crossCode {n k t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k))
    {oldE : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hcompat : ∀ x y (h : x ≠ y), oldE (Completion.topEdge x y h) = old₂ x y)
    (hclose : MonoWedgeClosesE oldE) (e : EdgeN n)
    (i : {i : CrossIndex (t := t) oldE // i ∈ crossesThrough (t := t) (old := oldE) e}) :
    CrossCode (t := t) old₂ e := by
  let q := normalizeAt e i.1
  have hq12 : q.e12 = e := normalizeAt_e12 e i.1 i.2
  have ho := obstruction_of_normalized old₂ hcompat hclose q
  have hp : orderedEnds q.e30 ∈
      crossObstructions old₂ (orderedEnds e).1 (orderedEnds e).2 := by
    rw [crossObstructions, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [hq12] using ho
  let p : ObstructionChoice old₂ e := ⟨orderedEnds q.e30, hp⟩
  have hm := cross_old_matching hclose q
  have hg : q.old01.1 ∈ crossEdges (orderedEnds e).1 (orderedEnds e).2 p.1.1 p.1.2 := by
    simpa only [hq12, p, crossEdges, Finset.mem_insert, Finset.mem_singleton] using
      (show q.old01.1 = s((orderedEnds q.e12).1, (orderedEnds q.e30).1) ∨
          q.old01.1 = s((orderedEnds q.e12).1, (orderedEnds q.e30).2) ∨
          q.old01.1 = s((orderedEnds q.e12).2, (orderedEnds q.e30).1) ∨
          q.old01.1 = s((orderedEnds q.e12).2, (orderedEnds q.e30).2) by
        rcases hm with hm | hm | hm | hm
        · exact Or.inl hm.1
        · exact Or.inr (Or.inr (Or.inr hm.2))
        · exact Or.inr (Or.inl hm.1)
        · exact Or.inr (Or.inr (Or.inl hm.2)))
  exact (i.1.e12 = e, ⟨p, ⟨q.old01.1, hg⟩⟩, q.color)

@[simp] lemma crossCode_bit {n k t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k))
    {oldE : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hcompat : ∀ x y (h : x ≠ y), oldE (Completion.topEdge x y h) = old₂ x y)
    (hclose : MonoWedgeClosesE oldE) (e : EdgeN n)
    (i : {i : CrossIndex (t := t) oldE // i ∈ crossesThrough (t := t) (old := oldE) e}) :
    (crossCode old₂ hcompat hclose e i).1 = decide (i.1.e12 = e) := by
  simp [crossCode]

@[simp] lemma crossCode_obstruction {n k t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k))
    {oldE : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hcompat : ∀ x y (h : x ≠ y), oldE (Completion.topEdge x y h) = old₂ x y)
    (hclose : MonoWedgeClosesE oldE) (e : EdgeN n)
    (i : {i : CrossIndex (t := t) oldE // i ∈ crossesThrough (t := t) (old := oldE) e}) :
    (crossCode old₂ hcompat hclose e i).2.1.1.1 =
      orderedEnds (normalizeAt e i.1).e30 := by
  simp [crossCode]

@[simp] lemma crossCode_old01 {n k t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k))
    {oldE : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hcompat : ∀ x y (h : x ≠ y), oldE (Completion.topEdge x y h) = old₂ x y)
    (hclose : MonoWedgeClosesE oldE) (e : EdgeN n)
    (i : {i : CrossIndex (t := t) oldE // i ∈ crossesThrough (t := t) (old := oldE) e}) :
    (crossCode old₂ hcompat hclose e i).2.1.2.1 =
      (normalizeAt e i.1).old01.1 := by
  simp [crossCode]

@[simp] lemma crossCode_color {n k t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k))
    {oldE : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hcompat : ∀ x y (h : x ≠ y), oldE (Completion.topEdge x y h) = old₂ x y)
    (hclose : MonoWedgeClosesE oldE) (e : EdgeN n)
    (i : {i : CrossIndex (t := t) oldE // i ∈ crossesThrough (t := t) (old := oldE) e}) :
    (crossCode old₂ hcompat hclose e i).2.2 = (normalizeAt e i.1).color := by
  simp [crossCode]

lemma crossCode_injective {n k t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k))
    {oldE : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hcompat : ∀ x y (h : x ≠ y), oldE (Completion.topEdge x y h) = old₂ x y)
    (hclose : MonoWedgeClosesE oldE) (e : EdgeN n) :
    Function.Injective (crossCode (t := t) old₂ hcompat hclose e) := by
  intro i j hij
  let qi := normalizeAt e i.1
  let qj := normalizeAt e j.1
  have hb : decide (i.1.e12 = e) = decide (j.1.e12 = e) := by
    rw [← crossCode_bit old₂ hcompat hclose e i,
      ← crossCode_bit old₂ hcompat hclose e j, hij]
  have hbprop : (i.1.e12 = e) ↔ (j.1.e12 = e) := by
    constructor
    · intro hi
      by_contra hj
      simp [hi, hj] at hb
    · intro hj
      by_contra hi
      simp [hi, hj] at hb
  have hp : orderedEnds qi.e30 = orderedEnds qj.e30 := by
    rw [← crossCode_obstruction old₂ hcompat hclose e i,
      ← crossCode_obstruction old₂ hcompat hclose e j]
    exact congrArg (fun z : CrossCode (t := t) old₂ e ↦ z.2.1.1.1) hij
  have h30 : qi.e30 = qj.e30 := orderedEnds_injective hp
  have h01val : qi.old01.1 = qj.old01.1 := by
    rw [← crossCode_old01 old₂ hcompat hclose e i,
      ← crossCode_old01 old₂ hcompat hclose e j]
    exact congrArg (fun z : CrossCode (t := t) old₂ e ↦ z.2.1.2.1) hij
  have h01 : qi.old01 = qj.old01 := Subtype.ext h01val
  have h12i : qi.e12 = e := normalizeAt_e12 e i.1 i.2
  have h12j : qj.e12 = e := normalizeAt_e12 e j.1 j.2
  have h12 : qi.e12 = qj.e12 := h12i.trans h12j.symm
  have h23 : qi.old23 = qj.old23 :=
    old23_eq_of_normalized_data hclose h12 h30 h01
  have hc : qi.oldColor = qj.oldColor := by
    apply Option.some.inj
    calc
      some qi.oldColor = oldE qi.old01 := qi.e01Old.symm
      _ = oldE qj.old01 := by rw [h01]
      _ = some qj.oldColor := qj.e01Old
  have hf : qi.color = qj.color := by
    rw [← crossCode_color old₂ hcompat hclose e i,
      ← crossCode_color old₂ hcompat hclose e j]
    exact congrArg (fun z : CrossCode (t := t) old₂ e ↦ z.2.2) hij
  have hq : qi = qj := crossIndex_ext h01 h23 h12 h30 hc hf
  apply Subtype.ext
  exact normalizeAt_injective_with_bit e hbprop hq

@[simp] lemma card_oldCrossChoice {n k : ℕ}
    {old₂ : Fin n → Fin n → Option (Fin k)} {e : EdgeN n}
    (p : ObstructionChoice old₂ e) : Fintype.card (OldCrossChoice p) = 4 := by
  rw [Fintype.card_coe]
  have hp : IsCrossObstruction old₂ (orderedEnds e).1 (orderedEnds e).2 p.1 :=
    (Finset.mem_filter.1 p.2).2
  apply crossEdges_card
  · exact ne_of_lt (orderedEnds_lt e)
  · exact ne_of_lt hp.1
  · exact hp.2.1.symm
  · exact hp.2.2.2.1.symm
  · exact hp.2.2.1.symm
  · exact hp.2.2.2.2.1.symm

lemma card_crossCode {n k t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k)) (e : EdgeN n) :
    Fintype.card (CrossCode (t := t) old₂ e) =
      8 * (crossObstructions old₂ (orderedEnds e).1 (orderedEnds e).2).card * t := by
  simp only [CrossCode, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  rw [Fintype.card_sigma]
  simp_rw [card_oldCrossChoice]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
  ac_rfl

/-- Closed cross-incidence estimate: P5 bounds the other leave edge, and
the remaining factors are two support slots, four old matchings/orders,
and the prescribed fresh colour. -/
theorem crossesThrough_card_le_of_crossLeaveBound {n k B t : ℕ}
    (old₂ : Fin n → Fin n → Option (Fin k))
    {oldE : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin k))}
    (hcompat : ∀ x y (h : x ≠ y), oldE (Completion.topEdge x y h) = old₂ x y)
    (hclose : MonoWedgeClosesE oldE)
    (hP5 : ∀ x y, x ≠ y → (crossObstructions old₂ x y).card ≤ B)
    (e : EdgeN n) :
    (crossesThrough (t := t) (old := oldE) e).card ≤ 8 * B * t := by
  have hinj := crossCode_injective (t := t) old₂ hcompat hclose e
  have hcard := Fintype.card_le_of_injective
    (crossCode (t := t) old₂ hcompat hclose e) hinj
  rw [Fintype.card_coe, card_crossCode] at hcard
  have hobs := hP5 (orderedEnds e).1 (orderedEnds e).2
    (ne_of_lt (orderedEnds_lt e))
  calc
    _ ≤ 8 * (crossObstructions old₂ (orderedEnds e).1 (orderedEnds e).2).card * t := hcard
    _ ≤ 8 * B * t := Nat.mul_le_mul_right t (Nat.mul_le_mul_left 8 hobs)

lemma completionOld_monoWedgeClosesE {n k B : ℕ} (P : PartialGood n k B) :
    MonoWedgeClosesE (completionOld P) := by
  intro c x y z hxy hxz hyz h₁ h₂
  rw [completionOld_topEdge] at h₁ h₂ ⊢
  obtain ⟨b, hb, hp₁, hp₂⟩ := P.p1 c x y z h₁ h₂
  obtain ⟨q, hq⟩ := b.support_has_color
    (b.closes_supported_path (b.paints_supports hp₁) (b.paints_supports hp₂) hyz)
  have hold : P.old y z = some q :=
    (P.p0.2 y z q).2 ⟨b, hb, hq⟩
  simp [hold]

theorem crossesThrough_completionOld_card_le {n k B t : ℕ}
    (P : PartialGood n k B) (e : EdgeN n) :
    (crossesThrough (t := t) (old := completionOld P) e).card ≤ 8 * B * t := by
  exact crossesThrough_card_le_of_crossLeaveBound P.old
    (completionOld_topEdge P) (completionOld_monoWedgeClosesE P) P.p5 e


lemma eventsThrough_card_eq {n oldK t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (e : EdgeN n) :
    (eventsThrough (t := t) (old := old) e).card =
      (wedgesThrough (t := t) (old := old) e).card +
      (cyclesThrough (old := old) e).card +
      (crossesThrough (t := t) (old := old) e).card := by
  classical
  let U := eventsThrough (t := t) (old := old) e
  have hW : U.toLeft = wedgesThrough (t := t) (old := old) e := by
    ext i
    simp only [Finset.mem_toLeft, U, eventsThrough, wedgesThrough,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hC : U.toRight.toLeft = cyclesThrough (old := old) e := by
    ext i
    simp only [Finset.mem_toLeft, Finset.mem_toRight, U, eventsThrough,
      cyclesThrough, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hX : U.toRight.toRight = crossesThrough (t := t) (old := old) e := by
    ext i
    simp only [Finset.mem_toRight, U, eventsThrough, crossesThrough,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have h₁ := Finset.card_toLeft_add_card_toRight (u := U)
  have h₂ := Finset.card_toLeft_add_card_toRight (u := U.toRight)
  change U.card = _
  rw [← hW, ← hC, ← hX]
  omega

/-- Closed incidence expression used for the sparse leave. -/
def closedIncidenceR (B t : ℕ) : ℕ := 12 * B * t + 16 * B ^ 2

lemma eventsThrough_le_closedIncidenceR {n oldK B t : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (hW : ∀ e, (wedgesThrough (t := t) (old := old) e).card ≤ 4 * B * t)
    (hC : ∀ e, (cyclesThrough (old := old) e).card ≤ 16 * B ^ 2)
    (hX : ∀ e, (crossesThrough (t := t) (old := old) e).card ≤ 8 * B * t) :
    ∀ e, (eventsThrough (t := t) (old := old) e).card ≤ closedIncidenceR B t := by
  intro e
  rw [eventsThrough_card_eq]
  calc
    _ ≤ 4 * B * t + 16 * B ^ 2 + 8 * B * t :=
      Nat.add_le_add (Nat.add_le_add (hW e) (hC e)) (hX e)
    _ = closedIncidenceR B t := by
      unfold closedIncidenceR
      ring

/-- The construction's degree and cross-obstruction hypotheses close the
event-incidence estimate, with no remaining probabilistic assumption. -/
theorem eventsThrough_completionOld_card_le {n oldK B t : ℕ}
    (P : PartialGood n oldK B) :
    ∀ e, (eventsThrough (t := t) (old := completionOld P) e).card ≤
      closedIncidenceR B t := by
  apply eventsThrough_le_closedIncidenceR
  · exact wedgesThrough_completionOld_card_le P
  · exact cyclesThrough_completionOld_card_le P
  · exact crossesThrough_completionOld_card_le P

/-- An incidence bound through one leave edge gives a dependency-degree
bound.  The factor four is the maximum event-support size. -/
lemma dependency_degree_le {n oldK t R : ℕ}
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (hinc : ∀ e, (eventsThrough (t := t) (old := old) e).card ≤ R)
    (i : BadIndex (t := t) old) :
    ((Finset.univ.erase i).filter (dependent i)).card ≤ 4 * R := by
  let N := (Finset.univ.erase i).filter (dependent i)
  let C := (badSupport i).biUnion (eventsThrough (t := t) (old := old))
  have hNC : N ⊆ C := by
    intro j hj
    have hdep : dependent i j := (Finset.mem_filter.mp hj).2
    rw [dependent, Finset.not_disjoint_iff] at hdep
    obtain ⟨e, hei, hej⟩ := hdep
    exact Finset.mem_biUnion.mpr ⟨e, hei,
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hej⟩⟩
  calc
    N.card ≤ C.card := Finset.card_le_card hNC
    _ ≤ ∑ e ∈ badSupport i, (eventsThrough (t := t) (old := old) e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ badSupport i, R := by
      gcongr with e he
      exact hinc e
    _ = (badSupport i).card * R := by simp
    _ ≤ 4 * R := Nat.mul_le_mul_right R (badSupport_card_le_four i)

/-- Local-lemma extraction in the exact finite product.  `hinc` is the
single-coordinate incidence estimate obtained from the leave-degree and
mixed-obstruction bounds. -/
theorem exists_assignment_avoiding {n oldK t R : ℕ} (ht : 0 < t)
    {old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK))}
    (hinc : ∀ e, (eventsThrough (t := t) (old := old) e).card ≤ R)
    (hfour : 4 * (1 / (t : ℝ) ^ 2) * ((4 * R + 1 : ℕ) : ℝ) ≤ 1) :
    ∃ fresh : Assignment n t,
      ∀ i : BadIndex (t := t) old, fresh ∉ badEvent i := by
  letI : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht
  classical
  apply LocalLemma.exists_avoiding_of_four_mul badEvent dependent
    (1 / (t : ℝ) ^ 2) (4 * R + 1)
  · positivity
  · exact badEvent_probability_le ht
  · intro i
    exact (dependency_degree_le hinc i).trans (Nat.le_add_right _ _)
  · exact badEvent_independent_of_non_neighbours ht
  · omega
  · exact hfour

/-! ## From avoidance to the deterministic completion certificate -/

/-- The image of a genuine `K₄` edge under a vertex embedding. -/
def mapEdge4 {n : ℕ} (v : Fin 4 ↪ Fin n) : Completion.Edge4 ↪ EdgeN n :=
  let vg : (⊤ : SimpleGraph (Fin 4)) ↪g (⊤ : SimpleGraph (Fin n)) := ⟨v, by simp⟩
  vg.mapEdgeSet

@[simp] lemma pullOld_apply_mapEdge4 {n oldK : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK)))
    (v : Fin 4 ↪ Fin n) (e : Completion.Edge4) :
    Completion.pullOld old v e = old (mapEdge4 v e) := by
  rfl

@[simp] lemma pullFresh_apply_mapEdge4 {n t : ℕ}
    (fresh : SimpleGraph.TopEdgeLabeling (Fin n) (Fin t))
    (v : Fin 4 ↪ Fin n) (e : Completion.Edge4) :
    Completion.pullFresh fresh v e = fresh (mapEdge4 v e) := by
  rfl

@[simp] lemma mapEdge4_toFinset {n : ℕ} (v : Fin 4 ↪ Fin n)
    (e : Completion.Edge4) :
    (mapEdge4 v e).1.toFinset = e.1.toFinset.image v := by
  apply Finset.ext
  simp [mapEdge4, SimpleGraph.Embedding.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet]

lemma mapEdge4_preserves_disjoint {n : ℕ} (v : Fin 4 ↪ Fin n)
    {e f : Completion.Edge4}
    (h : Disjoint e.1.toFinset f.1.toFinset) :
    Disjoint (mapEdge4 v e).1.toFinset (mapEdge4 v f).1.toFinset := by
  simp only [mapEdge4_toFinset]
  rw [Finset.disjoint_left]
  intro x hxe hxf
  obtain ⟨a, hae, ha⟩ := Finset.mem_image.mp hxe
  obtain ⟨b, hbf, hb⟩ := Finset.mem_image.mp hxf
  subst x
  have : a = b := v.injective hb.symm
  subst b
  exact Finset.disjoint_left.mp h hae hbf

lemma disjoint_edges_cover_fin4 {e f : Completion.Edge4}
    (h : Disjoint e.1.toFinset f.1.toFinset) :
    e.1.toFinset ∪ f.1.toFinset = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_union_of_disjoint h]
  have he : e.1.toFinset.card = 2 := by
    apply Sym2.card_toFinset_of_not_isDiag e.1
    simpa [SimpleGraph.mem_edgeSet] using e.2
  have hf : f.1.toFinset.card = 2 := by
    apply Sym2.card_toFinset_of_not_isDiag f.1
    simpa [SimpleGraph.mem_edgeSet] using f.2
  simp [he, hf]

lemma mapEdge4_preserves_nondisjoint {n : ℕ} (v : Fin 4 ↪ Fin n)
    {e f : Completion.Edge4}
    (h : ¬ Disjoint e.1.toFinset f.1.toFinset) :
    ¬ Disjoint (mapEdge4 v e).1.toFinset (mapEdge4 v f).1.toFinset := by
  rw [Finset.not_disjoint_iff] at h ⊢
  obtain ⟨x, hxe, hxf⟩ := h
  refine ⟨v x, ?_, ?_⟩
  · simpa [mapEdge4, SimpleGraph.Embedding.mapEdgeSet,
      SimpleGraph.Hom.mapEdgeSet] using hxe
  · simpa [mapEdge4, SimpleGraph.Embedding.mapEdgeSet,
      SimpleGraph.Hom.mapEdgeSet] using hxf

/-- A matching in `K₄` has at most two edges.  This elementary endpoint
count is the only graph-theoretic fact needed to turn absence of wedge
events into the `noA` part of `AvoidsABC`. -/
lemma card_le_two_of_pairwise_disjoint
    (S : Finset Completion.Edge4)
    (hpair : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
      Disjoint e.1.toFinset f.1.toFinset) :
    S.card ≤ 2 := by
  let V : Finset (Fin 4) := S.biUnion fun e ↦ e.1.toFinset
  have hdisj : (↑S : Set Completion.Edge4).PairwiseDisjoint
      (fun e ↦ e.1.toFinset) := by
    intro e he f hf hef
    exact hpair e he f hf hef
  have hcardV : V.card = 2 * S.card := by
    change (S.biUnion fun e ↦ e.1.toFinset).card = 2 * S.card
    rw [Finset.card_biUnion hdisj]
    calc
      ∑ e ∈ S, e.1.toFinset.card = ∑ _e ∈ S, 2 := by
        apply Finset.sum_congr rfl
        intro e _he
        apply Sym2.card_toFinset_of_not_isDiag e.1
        simpa [SimpleGraph.mem_edgeSet] using e.2
      _ = 2 * S.card := by simp [Nat.mul_comm]
  have hVle : V.card ≤ 4 := by
    calc
      V.card ≤ (Finset.univ : Finset (Fin 4)).card :=
        Finset.card_le_card (Finset.subset_univ V)
      _ = 4 := by simp
  omega

lemma combined_eq_inr_iff {Old Fresh : Type*} [DecidableEq Old]
    (old : Completion.Edge4 → Option Old) (fresh : Completion.Edge4 → Fresh)
    (e : Completion.Edge4) (c : Fresh) :
    Completion.combined old fresh e = Sum.inr c ↔ old e = none ∧ fresh e = c := by
  cases h : old e <;> simp [Completion.combined, h]

lemma noA_of_avoids {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK)))
    (fresh : Assignment n t)
    (havoid : ∀ i : BadIndex (t := t) old, fresh ∉ badEvent i) :
    ∀ (v : Fin 4 ↪ Fin n) (c : Fin t),
      (Completion.fiber
        (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
        (Sum.inr c)).card ≤ 2 := by
  intro v c
  let S := Completion.fiber
    (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
    (Sum.inr c)
  apply card_le_two_of_pairwise_disjoint S
  intro e he f hf hef
  by_contra hdisj
  change e ∈ Completion.fiber
    (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
    (Sum.inr c) at he
  change f ∈ Completion.fiber
    (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
    (Sum.inr c) at hf
  have heval := (combined_eq_inr_iff (Completion.pullOld old v)
    (Completion.pullFresh fresh v) e c).mp (by simpa [Completion.fiber] using he)
  have hfval := (combined_eq_inr_iff (Completion.pullOld old v)
    (Completion.pullFresh fresh v) f c).mp (by simpa [Completion.fiber] using hf)
  change old (mapEdge4 v e) = none ∧ fresh (mapEdge4 v e) = c at heval
  change old (mapEdge4 v f) = none ∧ fresh (mapEdge4 v f) = c at hfval
  let i : WedgeIndex (t := t) old :=
    { left := mapEdge4 v e
      right := mapEdge4 v f
      edges_ne := (mapEdge4 v).injective.ne hef
      adjacent := mapEdge4_preserves_nondisjoint v hdisj
      leftLeave := by simpa using heval.1
      rightLeave := by simpa using hfval.1
      color := c }
  apply havoid (Sum.inl i)
  simp only [badEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by simpa [i, WedgeIndex.leftEdge] using heval.2,
    by simpa [i, WedgeIndex.rightEdge] using hfval.2⟩

lemma fiber_mem_data {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK)))
    (fresh : Assignment n t) (v : Fin 4 ↪ Fin n) (c : Fin t)
    {e : Completion.Edge4}
    (he : e ∈ Completion.fiber
      (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
      (Sum.inr c)) :
    old (mapEdge4 v e) = none ∧ fresh (mapEdge4 v e) = c := by
  have h := (combined_eq_inr_iff (Completion.pullOld old v)
    (Completion.pullFresh fresh v) e c).mp (by simpa [Completion.fiber] using he)
  change old (mapEdge4 v e) = none ∧ fresh (mapEdge4 v e) = c at h
  exact h

lemma sameColor_edges_disjoint_of_avoids {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK)))
    (fresh : Assignment n t)
    (havoid : ∀ i : BadIndex (t := t) old, fresh ∉ badEvent i)
    (v : Fin 4 ↪ Fin n) (c : Fin t) {e f : Completion.Edge4}
    (he : e ∈ Completion.fiber
      (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
      (Sum.inr c))
    (hf : f ∈ Completion.fiber
      (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
      (Sum.inr c)) (hef : e ≠ f) :
    Disjoint e.1.toFinset f.1.toFinset := by
  by_contra hdisj
  have heval := fiber_mem_data old fresh v c he
  have hfval := fiber_mem_data old fresh v c hf
  let i : WedgeIndex (t := t) old :=
    { left := mapEdge4 v e
      right := mapEdge4 v f
      edges_ne := (mapEdge4 v).injective.ne hef
      adjacent := mapEdge4_preserves_nondisjoint v hdisj
      leftLeave := heval.1
      rightLeave := hfval.1
      color := c }
  apply havoid (Sum.inl i)
  simp only [badEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by simpa [i, WedgeIndex.leftEdge] using heval.2,
    by simpa [i, WedgeIndex.rightEdge] using hfval.2⟩

lemma noAB_of_avoids {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK)))
    (fresh : Assignment n t)
    (havoid : ∀ i : BadIndex (t := t) old, fresh ∉ badEvent i) :
    ∀ (v : Fin 4 ↪ Fin n) (c d : Fin t),
      2 ≤ (Completion.fiber
        (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
        (Sum.inr c)).card →
      2 ≤ (Completion.fiber
        (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
        (Sum.inr d)).card → c = d := by
  intro v c d hc hd
  by_contra hcd
  let Sc := Completion.fiber
    (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
    (Sum.inr c)
  let Sd := Completion.fiber
    (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
    (Sum.inr d)
  change 2 ≤ Sc.card at hc
  change 2 ≤ Sd.card at hd
  have hc' : 1 < Sc.card := by omega
  have hd' : 1 < Sd.card := by omega
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp hc'
  obtain ⟨g, hg, h, hh, hgh⟩ := Finset.one_lt_card.mp hd'
  change e ∈ Completion.fiber _ (Sum.inr c) at he
  change f ∈ Completion.fiber _ (Sum.inr c) at hf
  change g ∈ Completion.fiber _ (Sum.inr d) at hg
  change h ∈ Completion.fiber _ (Sum.inr d) at hh
  have heval := fiber_mem_data old fresh v c he
  have hfval := fiber_mem_data old fresh v c hf
  have hgval := fiber_mem_data old fresh v d hg
  have hhval := fiber_mem_data old fresh v d hh
  have cross_ne (x y : Completion.Edge4)
      (hx : fresh (mapEdge4 v x) = c) (hy : fresh (mapEdge4 v y) = d) : x ≠ y := by
    intro hxy
    subst y
    exact hcd (hx.symm.trans hy)
  have heg := cross_ne e g heval.2 hgval.2
  have heh := cross_ne e h heval.2 hhval.2
  have hfg := cross_ne f g hfval.2 hgval.2
  have hfh := cross_ne f h hfval.2 hhval.2
  have hmatchc := sameColor_edges_disjoint_of_avoids old fresh havoid v c he hf hef
  have hmatchd := sameColor_edges_disjoint_of_avoids old fresh havoid v d hg hh hgh
  let i : CycleIndex old :=
    { e01 := mapEdge4 v e
      e12 := mapEdge4 v g
      e23 := mapEdge4 v f
      e30 := mapEdge4 v h
      e01_ne_e12 := (mapEdge4 v).injective.ne heg
      e01_ne_e23 := (mapEdge4 v).injective.ne hef
      e01_ne_e30 := (mapEdge4 v).injective.ne heh
      e12_ne_e23 := (mapEdge4 v).injective.ne hfg.symm
      e12_ne_e30 := (mapEdge4 v).injective.ne hgh
      e23_ne_e30 := (mapEdge4 v).injective.ne hfh
      firstMatching := mapEdge4_preserves_disjoint v hmatchc
      secondMatching := mapEdge4_preserves_disjoint v hmatchd
      sameVertices := by
        simp only [mapEdge4_toFinset, ← Finset.image_union]
        rw [disjoint_edges_cover_fin4 hmatchc, disjoint_edges_cover_fin4 hmatchd]
      e01Leave := heval.1
      e12Leave := hgval.1
      e23Leave := hfval.1
      e30Leave := hhval.1 }
  apply havoid (Sum.inr (Sum.inl i))
  simp only [badEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by simpa [i] using heval.2.trans hfval.2.symm,
    by simpa [i] using hgval.2.trans hhval.2.symm,
    by simpa [i, heval.2, hgval.2] using hcd⟩

lemma noAC_of_avoids {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK)))
    (fresh : Assignment n t)
    (havoid : ∀ i : BadIndex (t := t) old, fresh ∉ badEvent i) :
    ∀ (v : Fin 4 ↪ Fin n) (c : Fin oldK) (d : Fin t),
      2 ≤ (Completion.fiber (Completion.pullOld old v) (some c)).card →
      ¬ 2 ≤ (Completion.fiber
        (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
        (Sum.inr d)).card := by
  intro v c d hc hd
  let So := Completion.fiber (Completion.pullOld old v) (some c)
  let Sf := Completion.fiber
    (Completion.combined (Completion.pullOld old v) (Completion.pullFresh fresh v))
    (Sum.inr d)
  change 2 ≤ So.card at hc
  change 2 ≤ Sf.card at hd
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp (show 1 < So.card by omega)
  obtain ⟨g, hg, h, hh, hgh⟩ := Finset.one_lt_card.mp (show 1 < Sf.card by omega)
  change e ∈ Completion.fiber (Completion.pullOld old v) (some c) at he
  change f ∈ Completion.fiber (Completion.pullOld old v) (some c) at hf
  change g ∈ Completion.fiber _ (Sum.inr d) at hg
  change h ∈ Completion.fiber _ (Sum.inr d) at hh
  have heold : old (mapEdge4 v e) = some c := by
    change Completion.pullOld old v e = some c
    simpa [Completion.fiber] using he
  have hfold : old (mapEdge4 v f) = some c := by
    change Completion.pullOld old v f = some c
    simpa [Completion.fiber] using hf
  have hgval := fiber_mem_data old fresh v d hg
  have hhval := fiber_mem_data old fresh v d hh
  have heg : e ≠ g := by
    intro hEq
    subst g
    simp [hgval.1] at heold
  have heh : e ≠ h := by
    intro hEq
    subst h
    simp [hhval.1] at heold
  have hfg : f ≠ g := by
    intro hEq
    subst g
    simp [hgval.1] at hfold
  have hfh : f ≠ h := by
    intro hEq
    subst h
    simp [hhval.1] at hfold
  have hmatch := sameColor_edges_disjoint_of_avoids old fresh havoid v d hg hh hgh
  let i : CrossIndex (t := t) old :=
    { old01 := mapEdge4 v e
      old23 := mapEdge4 v f
      e12 := mapEdge4 v g
      e30 := mapEdge4 v h
      old01_ne_old23 := (mapEdge4 v).injective.ne hef
      e12_ne_e30 := (mapEdge4 v).injective.ne hgh
      old_fresh_ne := ⟨(mapEdge4 v).injective.ne heg,
        (mapEdge4 v).injective.ne heh, (mapEdge4 v).injective.ne hfg,
        (mapEdge4 v).injective.ne hfh⟩
      freshMatching := mapEdge4_preserves_disjoint v hmatch
      atMostFourVertices := by
        have himage (q : Completion.Edge4) :
            q.1.toFinset.image v ⊆ (Finset.univ : Finset (Fin 4)).image v :=
          Finset.image_mono v (Finset.subset_univ q.1.toFinset)
        have hsub :
            (mapEdge4 v e).1.toFinset ∪ (mapEdge4 v f).1.toFinset ∪
                (mapEdge4 v g).1.toFinset ∪ (mapEdge4 v h).1.toFinset ⊆
              (Finset.univ : Finset (Fin 4)).image v := by
          simp only [mapEdge4_toFinset]
          exact Finset.union_subset
            (Finset.union_subset (Finset.union_subset (himage e) (himage f)) (himage g))
            (himage h)
        calc
          _ ≤ ((Finset.univ : Finset (Fin 4)).image v).card := Finset.card_le_card hsub
          _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
          _ = 4 := by simp
      oldColor := c
      e01Old := heold
      e23Old := hfold
      e12Leave := hgval.1
      e30Leave := hhval.1
      color := d }
  refine (havoid (Sum.inr (Sum.inr i))) ?_
  simp only [badEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by simpa [i] using hgval.2, by simpa [i] using hhval.2⟩

/-- Avoidance of the three concrete raw event families gives exactly the
certificate consumed by deterministic completion. -/
theorem avoidsABC_of_avoids {n oldK t : ℕ}
    (old : SimpleGraph.TopEdgeLabeling (Fin n) (Option (Fin oldK)))
    (fresh : Assignment n t)
    (havoid : ∀ i : BadIndex (t := t) old, fresh ∉ badEvent i) :
    Completion.AvoidsABC old fresh :=
  { noA := noA_of_avoids old fresh havoid
    noAB := noAB_of_avoids old fresh havoid
    noAC := noAC_of_avoids old fresh havoid }

/-- Concrete sparse-leave completion: the finite LLL produces a fresh
labeling together with the exact `AvoidsABC` certificate. -/
theorem exists_fresh_avoidsABC {n oldK t R : ℕ} {Block : Type*}
    (P : Completion.TriangleBlockPartialGood n (Fin oldK) Block)
    (ht : 0 < t)
    (hinc : ∀ e, (eventsThrough (t := t) (old := P.old) e).card ≤ R)
    (hfour : 4 * (1 / (t : ℝ) ^ 2) * ((4 * R + 1 : ℕ) : ℝ) ≤ 1) :
    ∃ fresh : SimpleGraph.TopEdgeLabeling (Fin n) (Fin t),
      Completion.AvoidsABC P.old fresh := by
  obtain ⟨fresh, hAvoid⟩ := exists_assignment_avoiding ht hinc hfour
  exact ⟨fresh, avoidsABC_of_avoids P.old fresh hAvoid⟩

/-- End-to-end exact colouring theorem for the sparse leave. -/
theorem colorable_of_sparse_leave {n oldK t R : ℕ} {Block : Type*}
    (P : Completion.TriangleBlockPartialGood n (Fin oldK) Block)
    (ht : 0 < t)
    (hinc : ∀ e, (eventsThrough (t := t) (old := P.old) e).card ≤ R)
    (hfour : 4 * (1 / (t : ℝ) ^ 2) * ((4 * R + 1 : ℕ) : ℝ) ≤ 1) :
    Colorable n (oldK + t) := by
  obtain ⟨fresh, hABC⟩ := exists_fresh_avoidsABC P ht hinc hfour
  exact ⟨(Completion.completeLabeling P.old fresh).compRight finSumFinEquiv,
    Completion.completeTriangleBlocksFin_is45 P fresh hABC⟩

/-- Closed sparse-leave completion for a concrete `PartialGood`: the only
remaining hypothesis is the explicit numerical local-lemma inequality. -/
theorem exists_fresh_avoidsABC_of_partialGood {n oldK B t : ℕ}
    (P : PartialGood n oldK B) (ht : 0 < t)
    (hfour :
      4 * (1 / (t : ℝ) ^ 2) * ((4 * closedIncidenceR B t + 1 : ℕ) : ℝ) ≤ 1) :
    ∃ fresh : SimpleGraph.TopEdgeLabeling (Fin n) (Fin t),
      Completion.AvoidsABC (completionOld P) fresh := by
  exact exists_fresh_avoidsABC (toCompletionPartialGood P) ht
    (eventsThrough_completionOld_card_le P) hfour

/-- End-to-end colouring theorem from the concrete sparse partial
construction and the literal finite-LLL inequality. -/
theorem colorable_of_partialGood_sparse_leave {n oldK B t : ℕ}
    (P : PartialGood n oldK B) (ht : 0 < t)
    (hfour :
      4 * (1 / (t : ℝ) ^ 2) * ((4 * closedIncidenceR B t + 1 : ℕ) : ℝ) ≤ 1) :
    Colorable n (oldK + t) := by
  exact colorable_of_sparse_leave (toCompletionPartialGood P) ht
    (eventsThrough_completionOld_card_le P) hfour

/-- The closed completion theorem in the parameter vocabulary used by the
upper-construction estimates. -/
theorem colorable_of_partialGood_jmLeaveBound {n oldK B t : ℕ}
    (P : PartialGood n oldK B) (ht : 0 < t)
    (hfour :
      4 * (1 / (t : ℝ) ^ 2) * ((4 * jmLeaveIncidenceBound B t + 1 : ℕ) : ℝ) ≤ 1) :
    Colorable n (oldK + t) := by
  apply colorable_of_partialGood_sparse_leave P ht
  simpa [closedIncidenceR, jmLeaveIncidenceBound] using hfour

/-- Once sparse partial constructions exist eventually at the Joos--Mubayi
leave scale, their fresh random completion exists eventually as well. -/
theorem eventually_colorable_of_partialGood
    (oldK B : ℕ → ℕ) {delta : ℝ}
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hB : ∀ᶠ n : ℕ in atTop,
      (B n : ℝ) ≤ (n : ℝ) ^ (1 - 2 * delta))
    (hP : ∀ᶠ n : ℕ in atTop, Nonempty (PartialGood n (oldK n) (B n))) :
    ∀ᶠ n : ℕ in atTop,
      Colorable n (oldK n + jmFreshColors delta n) := by
  have hfour := eventually_jmLeave_four_mul_le_one B hdelta0 hdeltaHalf hB
  have hdelta1 : delta < 1 := hdeltaHalf.trans (by norm_num)
  have ht : ∀ᶠ n : ℕ in atTop, 0 < jmFreshColors delta n :=
    (jmFreshColors_tendsto_atTop hdelta1).eventually (eventually_gt_atTop 0)
  filter_upwards [hP, hfour, ht] with n hPn h4 htpos
  exact colorable_of_partialGood_jmLeaveBound hPn.some htpos h4

end

end LeaveCompletion
end Erdos136

#print axioms Erdos136.LeaveCompletion.colorable_of_partialGood_jmLeaveBound
