/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Erdős Problem 1119

The unrestricted question is independent of ZFC.  This file proves the exact
ZFC-positive range from the supplied specification: if `succ m < 𝔠`, then a
family of entire functions taking at most `m` values at each point has size at
most `m`.  It also derives Erdős's countable theorem when `ℵ_ 1 < 𝔠`.

The proof uses the identity theorem to show that two distinct entire functions
coincide at only countably many points.  A subfamily of size `succ m` therefore
has at most `succ m` collision points in total; a point outside that union
separates the whole subfamily.
-/

open Cardinal Order
open scoped Cardinal

namespace Erdos1119

/-- Two distinct entire functions coincide at only countably many points. -/
private lemma coincidenceSet_countable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hfg : f ≠ g) :
    {z : ℂ | f z = g z}.Countable := by
  have hdiff : Differentiable ℂ (fun z => f z - g z) := hf.sub hg
  obtain ⟨x, hx⟩ : ∃ x, f x - g x ≠ 0 := by
    by_contra h
    push Not at h
    apply hfg
    funext z
    exact sub_eq_zero.mp (h z)
  have han : AnalyticOnNhd ℂ (fun z => f z - g z) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 hdiff
  have hcod :
      (fun z => f z - g z) ⁻¹' ({0} : Set ℂ)ᶜ ∈ Filter.codiscrete ℂ :=
    han.preimage_zero_mem_codiscrete hx
  have hcod' :
      ((fun z => f z - g z) ⁻¹' ({0} : Set ℂ))ᶜ ∈ Filter.codiscrete ℂ := by
    simpa only [Set.preimage_compl] using hcod
  have hdisc : IsDiscrete ((fun z => f z - g z) ⁻¹' ({0} : Set ℂ)) :=
    (compl_mem_codiscrete_iff.mp hcod').2
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  change IsDiscrete {z : ℂ | f z - g z = 0} at hdisc
  simpa only [sub_eq_zero] using hdisc

/-- Entire functions are determined by their values on a fixed countable dense set. -/
private lemma entireFamily_cardinality_le_continuum (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f) : #F ≤ 𝔠 := by
  let code : F → ℕ → ℂ := fun f n => f.1 (TopologicalSpace.denseSeq ℂ n)
  have hcode : Function.Injective code := by
    intro f g hfg
    apply Subtype.ext
    apply TopologicalSpace.denseRange_denseSeq.equalizer
    · exact (hF f.1 f.2).continuous
    · exact (hF g.1 g.2).continuous
    · funext n
      exact congrFun hfg n
  calc
    #F ≤ #(ℕ → ℂ) := Cardinal.mk_le_of_injective hcode
    _ = #ℂ ^ #ℕ := (Cardinal.power_def ℂ ℕ).symm
    _ = 𝔠 ^ ℵ₀ := by rw [Cardinal.mk_complex, Cardinal.mk_nat]
    _ = 𝔠 := Cardinal.continuum_power_aleph0

/-- A family smaller than the continuum has a point at which all its members differ. -/
private lemma exists_separating_point_of_mk_lt_continuum (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f) (hFc : #F < 𝔠) :
    ∃ z : ℂ, Function.Injective (fun f : F => f.1 z) := by
  let k : Cardinal.{0} := max ℵ₀ #F
  let I : Set (F × F) := {p | p.1 ≠ p.2}
  let collision : I → Set ℂ := fun p => {z | p.1.1.1 z = p.1.2.1 z}
  let bad : Set ℂ := ⋃ p : I, collision p
  have hk_inf : ℵ₀ ≤ k := le_max_left _ _
  have hk_lt : k < 𝔠 := max_lt Cardinal.aleph0_lt_continuum hFc
  have hI : #I ≤ k := by
    calc
      #I ≤ #(F × F) := Cardinal.mk_set_le I
      _ = #F * #F := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
      _ ≤ k * k := mul_le_mul' (le_max_right _ _) (le_max_right _ _)
      _ = k := Cardinal.mul_eq_self hk_inf
  have hcollision : ∀ p : I, #(collision p) ≤ k := by
    intro p
    have hne : p.1.1.1 ≠ p.1.2.1 := by
      intro heq
      apply p.2
      apply Subtype.ext
      exact heq
    have hc : (collision p).Countable := by
      apply coincidenceSet_countable
      · exact hF _ p.1.1.2
      · exact hF _ p.1.2.2
      · exact hne
    exact hc.le_aleph0.trans hk_inf
  have hsup : (⨆ p : I, #(collision p)) ≤ k := ciSup_le' hcollision
  have hbad : #bad ≤ k := by
    calc
      #bad ≤ #I * ⨆ p : I, #(collision p) := Cardinal.mk_iUnion_le collision
      _ ≤ k := Cardinal.mul_le_of_le hk_inf hI hsup
  have hbad_lt : #bad < #ℂ := by
    rw [Cardinal.mk_complex]
    exact hbad.trans_lt hk_lt
  obtain ⟨z, hz⟩ := Cardinal.compl_nonempty_of_mk_lt_mk hbad_lt
  refine ⟨z, ?_⟩
  intro f g hfg
  by_contra hne
  let p : I := ⟨(f, g), hne⟩
  have hzcollision : z ∈ collision p := hfg
  exact hz (Set.mem_iUnion.2 ⟨p, hzcollision⟩)

/-- The cardinal argument common to the uncountable and countable positive cases. -/
private theorem cardinality_le_of_succ_lt_continuum (m : Cardinal.{0}) (hm : ℵ₀ ≤ m)
    (hsucc : succ m < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z : ℂ, #{y : ℂ | ∃ f ∈ F, f z = y} ≤ m) :
    #F ≤ m := by
  by_contra hle
  have hmF : m < #F := lt_of_not_ge hle
  have hsuccF : succ m ≤ #F := Order.succ_le_iff.2 hmF
  obtain ⟨G, hG⟩ := Cardinal.le_mk_iff_exists_set.1 hsuccF
  let funOf : G → ℂ → ℂ := fun g => g.1.1
  let I : Set (G × G) := {p | p.1 ≠ p.2}
  let collision : I → Set ℂ := fun p => {z | funOf p.1.1 z = funOf p.1.2 z}
  let bad : Set ℂ := ⋃ p : I, collision p
  have hinf : ℵ₀ ≤ succ m := hm.trans (lt_succ m).le
  have hI : #I ≤ succ m := by
    calc
      #I ≤ #(G × G) := Cardinal.mk_set_le I
      _ = #G * #G := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
      _ = succ m * succ m := by rw [hG]
      _ = succ m := Cardinal.mul_eq_self hinf
  have hcollision : ∀ p : I, #(collision p) ≤ succ m := by
    intro p
    have hne : funOf p.1.1 ≠ funOf p.1.2 := by
      intro heq
      apply p.2
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    have hc : (collision p).Countable := by
      apply coincidenceSet_countable
      · exact hF _ p.1.1.1.2
      · exact hF _ p.1.2.1.2
      · exact hne
    exact hc.le_aleph0.trans hinf
  have hsup : (⨆ p : I, #(collision p)) ≤ succ m :=
    ciSup_le' hcollision
  have hbad : #bad ≤ succ m := by
    calc
      #bad ≤ #I * ⨆ p : I, #(collision p) := Cardinal.mk_iUnion_le collision
      _ ≤ succ m := Cardinal.mul_le_of_le hinf hI hsup
  have hbad_lt : #bad < #ℂ := by
    rw [Cardinal.mk_complex]
    exact hbad.trans_lt hsucc
  obtain ⟨z, hz⟩ := Cardinal.compl_nonempty_of_mk_lt_mk hbad_lt
  let V : Set ℂ := {y | ∃ f ∈ F, f z = y}
  let ev : G → V := fun g => ⟨funOf g z, g.1.1, g.1.2, rfl⟩
  have hev : Function.Injective ev := by
    intro a b hab
    by_contra hne
    let p : I := ⟨(a, b), hne⟩
    have habv : funOf a z = funOf b z := congrArg Subtype.val hab
    have hzcollision : z ∈ collision p := by
      exact habv
    have hzbad : z ∈ bad := Set.mem_iUnion.2 ⟨p, hzcollision⟩
    exact hz hzbad
  have hGV : #G ≤ #V := Cardinal.mk_le_of_injective hev
  have hcontra : succ m ≤ m := by
    calc
      succ m = #G := hG.symm
      _ ≤ #V := hGV
      _ ≤ m := by simpa only [V] using hval z
  exact (lt_succ m).2 hcontra

/--
The ZFC-positive range of Erdős Problem 1119: the answer is yes when
`m⁺ < 𝔠`.
-/
theorem erdos_1119.variants.easy_case (m : Cardinal.{0}) (hm : ℵ₀ < m)
    (hsucc : succ m < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z : ℂ, #{y : ℂ | ∃ f ∈ F, f z = y} ≤ m) :
    #F ≤ m := by
  exact cardinality_le_of_succ_lt_continuum m hm.le hsucc F hF hval

/--
Erdős's theorem answering Wetzel: if `ℵ₁ < 𝔠`, a pointwise-countable family
of entire functions is countable.
-/
theorem erdos_1119.variants.erdos_wetzel
    (h : (ℵ_ 1 : Cardinal.{0}) < 𝔠) (F : Set (ℂ → ℂ))
    (hF : ∀ f ∈ F, Differentiable ℂ f)
    (hval : ∀ z : ℂ, {y : ℂ | ∃ f ∈ F, f z = y}.Countable) :
    F.Countable := by
  have hsucc : succ (ℵ₀ : Cardinal.{0}) < 𝔠 := by
    simpa only [Cardinal.succ_aleph0] using h
  have hval' : ∀ z : ℂ, #{y : ℂ | ∃ f ∈ F, f z = y} ≤ (ℵ₀ : Cardinal.{0}) := fun z =>
    (hval z).le_aleph0
  exact Cardinal.le_aleph0_iff_set_countable.1
    (cardinality_le_of_succ_lt_continuum (ℵ₀ : Cardinal.{0}) le_rfl hsucc F hF hval')

end Erdos1119

#print axioms Erdos1119.erdos_1119.variants.easy_case
#print axioms Erdos1119.erdos_1119.variants.erdos_wetzel
