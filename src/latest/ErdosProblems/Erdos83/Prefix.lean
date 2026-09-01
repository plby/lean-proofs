import ErdosProblems.Erdos83.Incidence
import ErdosProblems.Erdos83.PrefixSets
import ErdosProblems.Erdos83.Compression

/-!
# Prefix symmetrisation for Erdos Problem 83

This file contains the specialised Ahlswede--Khachatrian defect-level
replacement argument. The ambient points are Fin (4 * q), and all members
of the family have cardinality 2 * q.
-/

namespace Erdos83

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

/-- Membership in a family depends only on the part at or after ell and on
the cardinality of the part before ell. This is the permutation-free form of
invariance under all permutations of the first ell coordinates. -/
def PrefixInvariant {N : ℕ} (F : Finset (Finset (Fin N))) (ell : ℕ) : Prop :=
  ∀ ⦃A B : Finset (Fin N)⦄,
    A ∩ tailAfter N ell = B ∩ tailAfter N ell →
    (A ∩ «prefix» N ell).card = (B ∩ «prefix» N ell).card →
    (A ∈ F ↔ B ∈ F)

/-- All unions of an a-subset of the prefix with one of the supplied
tails. The tail family is represented in the ambient Fin N. -/
noncomputable def layerFromTails (N ell a : ℕ)
    (P : Finset (Finset (Fin N))) : Finset (Finset (Fin N)) :=
  P.biUnion fun C ↦
    («prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C

lemma mem_layerFromTails {N ell a : ℕ} {P : Finset (Finset (Fin N))}
    {A : Finset (Fin N)} :
    A ∈ layerFromTails N ell a P ↔
      ∃ C ∈ P, ∃ B ⊆ «prefix» N ell, B.card = a ∧ B ∪ C = A := by
  simp [layerFromTails, and_assoc]

private lemma union_right_injective_of_disjoint {α : Type*} [DecidableEq α]
    {S C : Finset α} (hSC : Disjoint S C) :
    Function.Injective (fun B : {B // B ⊆ S} ↦ (B : Finset α) ∪ C) := by
  intro B₁ B₂ h
  change (B₁ : Finset α) ∪ C = (B₂ : Finset α) ∪ C at h
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    have hxU : x ∈ (B₁ : Finset α) ∪ C := mem_union_left _ hx
    rw [h] at hxU
    rcases mem_union.mp hxU with hx₂ | hxC
    · exact hx₂
    · exact (Finset.disjoint_left.mp hSC (B₁.property hx) hxC).elim
  · intro hx
    have hxU : x ∈ (B₂ : Finset α) ∪ C := mem_union_left _ hx
    rw [← h] at hxU
    rcases mem_union.mp hxU with hx₁ | hxC
    · exact hx₁
    · exact (Finset.disjoint_left.mp hSC (B₂.property hx) hxC).elim

private lemma layer_piece_card {N ell a : ℕ} {C : Finset (Fin N)}
    (hC : C ⊆ tailAfter N ell) :
    ((«prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C).card =
      Nat.choose («prefix» N ell).card a := by
  rw [card_image_iff.mpr]
  · exact card_powersetCard _ _
  · intro B₁ hB₁ B₂ hB₂ hEq
    have hB₁s : B₁ ⊆ «prefix» N ell := (mem_powersetCard.mp hB₁).1
    have hB₂s : B₂ ⊆ «prefix» N ell := (mem_powersetCard.mp hB₂).1
    have hd : Disjoint («prefix» N ell) C :=
      (disjoint_prefix_tailAfter N ell).mono_right hC
    let B₁' : {B // B ⊆ «prefix» N ell} := ⟨B₁, hB₁s⟩
    let B₂' : {B // B ⊆ «prefix» N ell} := ⟨B₂, hB₂s⟩
    have hEq' : (B₁' : Finset (Fin N)) ∪ C =
        (B₂' : Finset (Fin N)) ∪ C := hEq
    have hi := union_right_injective_of_disjoint hd hEq'
    exact congrArg Subtype.val hi

private lemma layer_pieces_disjoint {N ell a : ℕ}
    {C₁ C₂ : Finset (Fin N)}
    (hC₁ : C₁ ⊆ tailAfter N ell) (hC₂ : C₂ ⊆ tailAfter N ell)
    (hne : C₁ ≠ C₂) :
    Disjoint
      ((«prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C₁)
      ((«prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C₂) := by
  rw [disjoint_left]
  intro A hA₁ hA₂
  obtain ⟨B₁, hB₁, rfl⟩ := mem_image.mp hA₁
  obtain ⟨B₂, hB₂, hEq⟩ := mem_image.mp hA₂
  have hB₁s : B₁ ⊆ «prefix» N ell := (mem_powersetCard.mp hB₁).1
  have hB₂s : B₂ ⊆ «prefix» N ell := (mem_powersetCard.mp hB₂).1
  have ht₁ : (B₁ ∪ C₁) ∩ tailAfter N ell = C₁ :=
    union_inter_tailAfter hB₁s hC₁
  have ht₂ : (B₂ ∪ C₂) ∩ tailAfter N ell = C₂ :=
    union_inter_tailAfter hB₂s hC₂
  apply hne
  rw [← ht₁, ← ht₂, ← hEq]

lemma card_layerFromTails {N ell a : ℕ} {P : Finset (Finset (Fin N))}
    (hP : ∀ C ∈ P, C ⊆ tailAfter N ell) :
    (layerFromTails N ell a P).card =
      Nat.choose («prefix» N ell).card a * P.card := by
  classical
  rw [layerFromTails, card_biUnion]
  · calc
      ∑ C ∈ P,
          ((«prefix» N ell).powersetCard a |>.image fun B ↦ B ∪ C).card =
          ∑ _C ∈ P, Nat.choose («prefix» N ell).card a := by
            apply sum_congr rfl
            intro C hC
            exact layer_piece_card (hP C hC)
      _ = Nat.choose («prefix» N ell).card a * P.card := by
        simp [Nat.mul_comm]
  · intro C₁ hC₁ C₂ hC₂ hne
    exact layer_pieces_disjoint (hP C₁ hC₁) (hP C₂ hC₂) hne

/-- The point immediately following a prefix. -/
def nextPoint {N ell : ℕ} (h : ell < N) : Fin N := ⟨ell, h⟩

@[simp] lemma nextPoint_val {N ell : ℕ} (h : ell < N) :
    (nextPoint h).val = ell := rfl

/-- Move one occupied prefix point to the first point after the prefix. -/
def rightExchange {N : ℕ} (h i : Fin N) (A : Finset (Fin N)) :
    Finset (Fin N) :=
  insert h (A.erase i)

@[simp] lemma mem_rightExchange {N : ℕ} {h i x : Fin N}
    {A : Finset (Fin N)} :
    x ∈ rightExchange h i A ↔ x = h ∨ (x ∈ A ∧ x ≠ i) := by
  simp [rightExchange, eq_comm, and_comm]

lemma rightExchange_eq_transpose {N : ℕ} {h i : Fin N}
    {A : Finset (Fin N)} (hi : i ∈ A) (hh : h ∉ A) :
    rightExchange h i A = setTranspose i h A := by
  classical
  ext x
  simp only [mem_rightExchange, mem_setTranspose]
  by_cases xh : x = h
  · subst x
    have hne : h ≠ i := by
      intro e
      subst i
      exact hh hi
    simp [hi, hne]
  by_cases xi : x = i
  · subst x
    have hne : i ≠ h := by
      intro e
      subst h
      exact hh hi
    simp [hh, hne]
  · simp [Equiv.swap_apply_of_ne_of_ne xi xh, xh, xi]

lemma card_rightExchange {N : ℕ} {h i : Fin N}
    {A : Finset (Fin N)} (hi : i ∈ A) (hh : h ∉ A) :
    (rightExchange h i A).card = A.card := by
  rw [rightExchange_eq_transpose hi hh, card_setTranspose]

/-- Defective members at the step from prefix length ell to ell+1. -/
noncomputable def defectFamily {N : ℕ}
    (F : Finset (Finset (Fin N))) (ell : ℕ) (hN : ell < N) :
    Finset (Finset (Fin N)) :=
  F.filter fun A ↦
    ∃ i ∈ «prefix» N ell,
      i ∈ A ∧ nextPoint hN ∉ A ∧ rightExchange (nextPoint hN) i A ∉ F

lemma mem_defectFamily {N : ℕ} {F : Finset (Finset (Fin N))}
    {ell : ℕ} {hN : ell < N} {A : Finset (Fin N)} :
    A ∈ defectFamily F ell hN ↔
      A ∈ F ∧ ∃ i ∈ «prefix» N ell,
        i ∈ A ∧ nextPoint hN ∉ A ∧
          rightExchange (nextPoint hN) i A ∉ F := by
  simp [defectFamily]

noncomputable def defectLayer {N : ℕ}
    (F : Finset (Finset (Fin N))) (ell a : ℕ) (hN : ell < N) :
    Finset (Finset (Fin N)) :=
  (defectFamily F ell hN).filter fun A ↦ (A ∩ «prefix» N ell).card = a

lemma mem_defectLayer {N : ℕ} {F : Finset (Finset (Fin N))}
    {ell a : ℕ} {hN : ell < N} {A : Finset (Fin N)} :
    A ∈ defectLayer F ell a hN ↔
      A ∈ defectFamily F ell hN ∧ (A ∩ «prefix» N ell).card = a := by
  simp [defectLayer]

/-- The far tails occurring at one defect level. -/
noncomputable def defectTails {N : ℕ}
    (F : Finset (Finset (Fin N))) (ell a : ℕ) (hN : ell < N) :
    Finset (Finset (Fin N)) :=
  (defectLayer F ell a hN).image fun A ↦ A ∩ tailAfter N (ell + 1)

lemma mem_defectTails {N : ℕ} {F : Finset (Finset (Fin N))}
    {ell a : ℕ} {hN : ell < N} {C : Finset (Fin N)} :
    C ∈ defectTails F ell a hN ↔
      ∃ A ∈ defectLayer F ell a hN,
        A ∩ tailAfter N (ell + 1) = C := by
  simp [defectTails, eq_comm]

lemma defectTails_subset_tailAfter {N : ℕ}
    {F : Finset (Finset (Fin N))} {ell a : ℕ} {hN : ell < N}
    {C : Finset (Fin N)} (hC : C ∈ defectTails F ell a hN) :
    C ⊆ tailAfter N (ell + 1) := by
  obtain ⟨A, _hA, rfl⟩ := mem_defectTails.mp hC
  exact inter_subset_right

/-- The exchanges associated with a defect level. -/
noncomputable def exchangeLayer {N : ℕ}
    (F : Finset (Finset (Fin N))) (ell a : ℕ) (hN : ell < N) :
    Finset (Finset (Fin N)) :=
  layerFromTails N ell (a - 1)
    ((defectTails F ell a hN).image fun C ↦ insert (nextPoint hN) C)

@[simp] lemma nextPoint_not_mem_prefix {N ell : ℕ} (hN : ell < N) :
    nextPoint hN ∉ «prefix» N ell := by simp

@[simp] lemma nextPoint_mem_tailAfter {N ell : ℕ} (hN : ell < N) :
    nextPoint hN ∈ tailAfter N ell := by simp

@[simp] lemma nextPoint_not_mem_farTail {N ell : ℕ} (hN : ell < N) :
    nextPoint hN ∉ tailAfter N (ell + 1) := by simp

private lemma rightExchange_inter_tail {N ell : ℕ} (hN : ell < N)
    {A : Finset (Fin N)} {i : Fin N} (hiP : i ∈ «prefix» N ell) :
    rightExchange (nextPoint hN) i A ∩ tailAfter N ell =
      insert (nextPoint hN) (A ∩ tailAfter N (ell + 1)) := by
  ext x
  simp only [mem_inter, mem_rightExchange, mem_tailAfter, mem_insert]
  constructor
  · rintro ⟨rfl | ⟨hxA, hxi⟩, hxell⟩
    · exact Or.inl rfl
    · by_cases hx : x.val = ell
      · left
        exact Fin.ext hx
      · right
        exact ⟨hxA, by omega⟩
  · rintro (rfl | ⟨hxA, hxell⟩)
    · exact ⟨Or.inl rfl, le_rfl⟩
    · refine ⟨Or.inr ⟨hxA, ?_⟩, by omega⟩
      intro hxi
      subst x
      have := mem_prefix.mp hiP
      omega

private lemma rightExchange_inter_prefix {N ell : ℕ} (hN : ell < N)
    {A : Finset (Fin N)} {i : Fin N} :
    rightExchange (nextPoint hN) i A ∩ «prefix» N ell =
      (A ∩ «prefix» N ell).erase i := by
  ext x
  simp only [mem_inter, mem_rightExchange, mem_prefix, mem_erase]
  constructor
  · rintro ⟨rfl | ⟨hxA, hxi⟩, hxell⟩
    · exfalso
      simp at hxell
    · exact ⟨hxi, hxA, hxell⟩
  · rintro ⟨hxi, hxA, hxell⟩
    exact ⟨Or.inr ⟨hxA, hxi⟩, hxell⟩

private lemma defect_exchange_not_mem
    {N ell : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) {A : Finset (Fin N)}
    (hA : A ∈ defectFamily F ell hN)
    {i : Fin N} (hiP : i ∈ «prefix» N ell) (hiA : i ∈ A) :
    rightExchange (nextPoint hN) i A ∉ F := by
  rcases (mem_defectFamily.mp hA).2 with
    ⟨j, hjP, hjA, hhA, hjMissing⟩
  intro hiMem
  apply hjMissing
  apply (hinv ?_ ?_).mp hiMem
  · ext x
    simp only [mem_inter, mem_rightExchange, mem_tailAfter]
    have hiVal : i.val < ell := mem_prefix.mp hiP
    have hjVal : j.val < ell := mem_prefix.mp hjP
    constructor
    · rintro ⟨rfl | ⟨hxA, hxi⟩, hxell⟩
      · exact ⟨Or.inl rfl, le_rfl⟩
      · refine ⟨Or.inr ⟨hxA, ?_⟩, hxell⟩
        intro hxj
        subst x
        omega
    · rintro ⟨rfl | ⟨hxA, hxj⟩, hxell⟩
      · exact ⟨Or.inl rfl, le_rfl⟩
      · refine ⟨Or.inr ⟨hxA, ?_⟩, hxell⟩
        intro hxi
        subst x
        omega
  · rw [rightExchange_inter_prefix hN,
      rightExchange_inter_prefix hN]
    have hiInter : i ∈ A ∩ «prefix» N ell := mem_inter.mpr ⟨hiA, hiP⟩
    have hjInter : j ∈ A ∩ «prefix» N ell := mem_inter.mpr ⟨hjA, hjP⟩
    rw [card_erase_of_mem hiInter, card_erase_of_mem hjInter]

private lemma defect_not_mem_next {N ell : ℕ}
    {F : Finset (Finset (Fin N))} {hN : ell < N}
    {A : Finset (Fin N)} (hA : A ∈ defectFamily F ell hN) :
    nextPoint hN ∉ A := by
  rcases (mem_defectFamily.mp hA).2 with ⟨i, hiP, hiA, hhA, hiM⟩
  exact hhA

private lemma inter_tail_eq_far_of_not_next {N ell : ℕ}
    (hN : ell < N) {A : Finset (Fin N)}
    (hh : nextPoint hN ∉ A) :
    A ∩ tailAfter N ell = A ∩ tailAfter N (ell + 1) := by
  ext x
  simp only [mem_inter, mem_tailAfter]
  constructor
  · rintro ⟨hxA, hx⟩
    refine ⟨hxA, ?_⟩
    by_cases heq : x.val = ell
    · have : x = nextPoint hN := Fin.ext heq
      exact (hh (this ▸ hxA)).elim
    · omega
  · rintro ⟨hxA, hx⟩
    exact ⟨hxA, by omega⟩

private lemma defectLayer_eq_layerFromTails
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a) :
    defectLayer F ell a hN =
      layerFromTails N ell a (defectTails F ell a hN) := by
  classical
  ext A
  constructor
  · intro hA
    have hAD := (mem_defectLayer.mp hA).1
    have hcard := (mem_defectLayer.mp hA).2
    have hh := defect_not_mem_next hAD
    apply mem_layerFromTails.mpr
    refine ⟨A ∩ tailAfter N (ell + 1), ?_, A ∩ «prefix» N ell,
      inter_subset_right, hcard, ?_⟩
    · exact mem_defectTails.mpr ⟨A, hA, rfl⟩
    · rw [← inter_tail_eq_far_of_not_next hN hh]
      exact inter_prefix_union_inter_tailAfter A
  · intro hA
    rcases mem_layerFromTails.mp hA with
      ⟨C, hCP, B, hBP, hBcard, rfl⟩
    rcases mem_defectTails.mp hCP with ⟨X, hXD, hXC⟩
    have hXdef := (mem_defectLayer.mp hXD).1
    have hXcard := (mem_defectLayer.mp hXD).2
    have hXmem : X ∈ F := (mem_defectFamily.mp hXdef).1
    have hhX := defect_not_mem_next hXdef
    have hCs : C ⊆ tailAfter N (ell + 1) :=
      defectTails_subset_tailAfter hCP
    have hCt : C ⊆ tailAfter N ell := by
      intro x hx
      have := mem_tailAfter.mp (hCs hx)
      exact mem_tailAfter.mpr (by omega)
    have htailBC : (B ∪ C) ∩ tailAfter N ell = C :=
      union_inter_tailAfter hBP hCt
    have htailX : X ∩ tailAfter N ell = C := by
      rw [inter_tail_eq_far_of_not_next hN hhX, hXC]
    have hprefixBC : (B ∪ C) ∩ «prefix» N ell = B :=
      union_inter_prefix hBP hCt
    have hBCmem : B ∪ C ∈ F :=
      (hinv (htailBC.trans htailX.symm)
        (by rw [hprefixBC, hBcard, hXcard])).mpr hXmem
    have hBpos : 0 < B.card := hBcard ▸ ha
    obtain ⟨i, hiB⟩ := card_pos.mp hBpos
    have hiP : i ∈ «prefix» N ell := hBP hiB
    have hhC : nextPoint hN ∉ C :=
      fun hh ↦ nextPoint_not_mem_farTail hN (hCs hh)
    have hhB : nextPoint hN ∉ B :=
      fun hh ↦ nextPoint_not_mem_prefix hN (hBP hh)
    have hhBC : nextPoint hN ∉ B ∪ C := by
      simp [hhB, hhC]
    have hiBC : i ∈ B ∪ C := mem_union_left _ hiB
    refine mem_defectLayer.mpr ⟨mem_defectFamily.mpr
      ⟨hBCmem, ⟨i, hiP, hiBC, hhBC, ?_⟩⟩, ?_⟩
    · intro hExMem
      have hXprefixPos : 0 < (X ∩ «prefix» N ell).card := hXcard ▸ ha
      obtain ⟨j, hjXprefix⟩ := card_pos.mp hXprefixPos
      have hjX : j ∈ X := (mem_inter.mp hjXprefix).1
      have hjP : j ∈ «prefix» N ell := (mem_inter.mp hjXprefix).2
      have hjMissing := defect_exchange_not_mem hinv hXdef hjP hjX
      apply hjMissing
      apply (hinv ?_ ?_).mp hExMem
      · have hBP' : B ⊆ «prefix» N (ell + 1) := by
          intro x hx
          have := mem_prefix.mp (hBP hx)
          exact mem_prefix.mpr (by omega)
        have htfar : (B ∪ C) ∩ tailAfter N (ell + 1) = C :=
          union_inter_tailAfter hBP' hCs
        rw [rightExchange_inter_tail hN hiP,
          rightExchange_inter_tail hN hjP, htfar, hXC]
      · rw [rightExchange_inter_prefix hN,
          rightExchange_inter_prefix hN, hprefixBC]
        have hiBP : i ∈ B ∩ «prefix» N ell := mem_inter.mpr ⟨hiB, hiP⟩
        rw [card_erase_of_mem hiB, card_erase_of_mem hjXprefix,
          hBcard, hXcard]
    · rw [hprefixBC, hBcard]

private lemma card_defectLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a) :
    (defectLayer F ell a hN).card =
      Nat.choose ell a * (defectTails F ell a hN).card := by
  rw [defectLayer_eq_layerFromTails hinv ha,
    card_layerFromTails (fun C hC ↦
      (defectTails_subset_tailAfter hC).trans ?_),
    card_prefix hN.le]
  intro x hx
  simp only [mem_tailAfter] at hx ⊢
  omega

private lemma insert_next_injective_on_farTails {N ell : ℕ}
    (hN : ell < N) (P : Finset (Finset (Fin N)))
    (hP : ∀ C ∈ P, C ⊆ tailAfter N (ell + 1)) :
    Set.InjOn (fun C ↦ insert (nextPoint hN) C)
      (↑P : Set (Finset (Fin N))) := by
  intro C₁ hC₁ C₂ hC₂ hEq
  ext x
  have hh₁ : nextPoint hN ∉ C₁ :=
    fun hh ↦ nextPoint_not_mem_farTail hN (hP C₁ hC₁ hh)
  have hh₂ : nextPoint hN ∉ C₂ :=
    fun hh ↦ nextPoint_not_mem_farTail hN (hP C₂ hC₂ hh)
  by_cases hx : x = nextPoint hN
  · subst x
    simp [hh₁, hh₂]
  · have := congrArg (fun S : Finset (Fin N) ↦ x ∈ S) hEq
    simpa [hx] using this

private lemma card_exchangeLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N} :
    (exchangeLayer F ell a hN).card =
      Nat.choose ell (a - 1) * (defectTails F ell a hN).card := by
  let P := defectTails F ell a hN
  have hPfar : ∀ C ∈ P, C ⊆ tailAfter N (ell + 1) :=
    fun C hC ↦ defectTails_subset_tailAfter hC
  have hPtail :
      ∀ C ∈ P.image (fun C ↦ insert (nextPoint hN) C),
        C ⊆ tailAfter N ell := by
    intro C hC
    rcases mem_image.mp hC with ⟨D, hDP, rfl⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hxD
    · exact nextPoint_mem_tailAfter hN
    · have := mem_tailAfter.mp (hPfar D hDP hxD)
      exact mem_tailAfter.mpr (by omega)
  rw [exchangeLayer, card_layerFromTails hPtail, card_prefix hN.le,
    card_image_iff.mpr (insert_next_injective_on_farTails hN P hPfar)]

private lemma exchangeLayer_disjoint_family
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a) :
    Disjoint (exchangeLayer F ell a hN) F := by
  rw [disjoint_left]
  intro E hE hEF
  rcases mem_layerFromTails.mp hE with
    ⟨D, hD, B, hBP, hBcard, rfl⟩
  rcases mem_image.mp hD with ⟨C, hCP, rfl⟩
  rcases mem_defectTails.mp hCP with ⟨X, hXD, hXC⟩
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXcard := (mem_defectLayer.mp hXD).2
  have hXprefixPos : 0 < (X ∩ «prefix» N ell).card := hXcard ▸ ha
  obtain ⟨j, hjXP⟩ := card_pos.mp hXprefixPos
  have hjX : j ∈ X := (mem_inter.mp hjXP).1
  have hjP : j ∈ «prefix» N ell := (mem_inter.mp hjXP).2
  apply defect_exchange_not_mem hinv hXdef hjP hjX
  apply (hinv ?_ ?_).mpr hEF
  · rw [rightExchange_inter_tail hN hjP, hXC]
    symm
    apply union_inter_tailAfter hBP
    intro x hx
    rcases mem_insert.mp hx with rfl | hxC
    · exact nextPoint_mem_tailAfter hN
    · have hxFar := defectTails_subset_tailAfter hCP hxC
      simp only [mem_tailAfter] at hxFar ⊢
      omega
  · rw [rightExchange_inter_prefix hN,
      union_inter_prefix hBP]
    · rw [hBcard, card_erase_of_mem hjXP, hXcard]
    · intro x hx
      rcases mem_insert.mp hx with rfl | hxC
      · exact nextPoint_mem_tailAfter hN
      · have hxFar := defectTails_subset_tailAfter hCP hxC
        simp only [mem_tailAfter] at hxFar ⊢
        omega

private lemma exchangeLayer_exists_source
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    {E : Finset (Fin N)} (hE : E ∈ exchangeLayer F ell a hN) :
    ∃ X ∈ defectLayer F ell a hN, ∃ i ∈ «prefix» N ell,
      i ∈ X ∧ E = rightExchange (nextPoint hN) i X := by
  rcases mem_layerFromTails.mp hE with
    ⟨D, hD, B, hBP, hBcard, hEeq⟩
  rcases mem_image.mp hD with ⟨C, hCP, rfl⟩
  rcases mem_defectTails.mp hCP with ⟨X₀, hX₀D, hX₀C⟩
  have hX₀card := (mem_defectLayer.mp hX₀D).2
  have haell : a ≤ ell := by
    have hs : (X₀ ∩ «prefix» N ell).card ≤
        («prefix» N ell).card := card_le_card inter_subset_right
    rw [hX₀card, card_prefix hN.le] at hs
    exact hs
  have hBlt : B.card < («prefix» N ell).card := by
    rw [hBcard, card_prefix hN.le]
    omega
  obtain ⟨i, hiP, hiB⟩ :=
    exists_mem_notMem_of_card_lt_card hBlt
  let X := insert i B ∪ C
  have hCs : C ⊆ tailAfter N (ell + 1) :=
    defectTails_subset_tailAfter hCP
  have hCt : C ⊆ tailAfter N ell := by
    intro x hx
    have := mem_tailAfter.mp (hCs hx)
    exact mem_tailAfter.mpr (by omega)
  have hiC : i ∉ C := by
    intro hi
    have hiFar := mem_tailAfter.mp (hCs hi)
    have hiVal := mem_prefix.mp hiP
    omega
  have hXP : insert i B ⊆ «prefix» N ell := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hxB
    · exact hiP
    · exact hBP hxB
  have hXcard : (insert i B).card = a := by
    rw [card_insert_of_notMem hiB, hBcard]
    omega
  have hXD : X ∈ defectLayer F ell a hN := by
    rw [defectLayer_eq_layerFromTails hinv ha]
    exact mem_layerFromTails.mpr
      ⟨C, hCP, insert i B, hXP, hXcard, rfl⟩
  refine ⟨X, hXD, i, hiP, ?_, ?_⟩
  · exact mem_union_left _ (mem_insert_self i B)
  · rw [← hEeq]
    ext x
    simp only [X, mem_union, mem_insert, mem_rightExchange]
    constructor
    · rintro (hxB | rfl | hxC)
      · exact Or.inr ⟨Or.inl (Or.inr hxB), by
          intro hxi
          subst x
          exact hiB hxB⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Or.inr hxC, by
          intro hxi
          subst x
          exact hiC hxC⟩
    · rintro (rfl | ⟨(rfl | hxB) | hxC, hxi⟩)
      · exact Or.inr (Or.inl rfl)
      · exact (hxi rfl).elim
      · exact Or.inl hxB
      · exact Or.inr (Or.inr hxC)

private lemma exchange_cross_nondefect
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    (hinter : TwoIntersecting F)
    {E Y : Finset (Fin N)}
    (hE : E ∈ exchangeLayer F ell a hN)
    (hYF : Y ∈ F) (hYD : Y ∉ defectFamily F ell hN) :
    2 ≤ (E ∩ Y).card := by
  obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
    exchangeLayer_exists_source hinv ha hE
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXF : X ∈ F := (mem_defectFamily.mp hXdef).1
  have hhX := defect_not_mem_next hXdef
  rw [rightExchange_eq_transpose hiX hhX,
    card_inter_transpose_cross]
  by_cases hbad : i ∈ Y ∧ nextPoint hN ∉ Y
  · have hYex : rightExchange (nextPoint hN) i Y ∈ F := by
      by_contra hmissing
      apply hYD
      exact mem_defectFamily.mpr
        ⟨hYF, ⟨i, hiP, hbad.1, hbad.2, hmissing⟩⟩
    rw [← rightExchange_eq_transpose hbad.1 hbad.2]
    exact hinter hXF hYex
  · exact le_trans (hinter hXF hYF) (card_le_card
      (by
        have hs := inter_subset_inter_transpose_right
          (i := nextPoint hN) (j := i) ⟨hiX, hhX⟩ hbad
        have heq : setTranspose (nextPoint hN) i Y =
            setTranspose i (nextPoint hN) Y := by
          unfold setTranspose
          rw [Equiv.swap_comm]
        simpa only [heq] using hs))

private lemma exists_prefix_subset_disjoint
    {N ell a : ℕ} (hN : ell ≤ N) (B : Finset (Fin N))
    (hB : B ⊆ «prefix» N ell) (ha : a + B.card ≤ ell) :
    ∃ A : Finset (Fin N),
      A ⊆ «prefix» N ell ∧ A.card = a ∧ Disjoint A B := by
  let C := «prefix» N ell \ B
  have hBC : B.card ≤ ell := by
    have := card_le_card hB
    simpa [card_prefix hN] using this
  have hCcard : C.card = ell - B.card := by
    dsimp [C]
    simpa [card_prefix hN] using card_sdiff_of_subset hB
  have haC : a ≤ C.card := by omega
  obtain ⟨A, hAC, hAcard⟩ := exists_subset_card_eq haC
  refine ⟨A, hAC.trans sdiff_subset, hAcard, ?_⟩
  exact disjoint_left.mpr fun x hxA hxB ↦
    (mem_sdiff.mp (hAC hxA)).2 hxB

private lemma defect_inter_card_three
    {q ell a b : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hinter : TwoIntersecting F) (hleft : LeftCompressed F)
    {X Y : Finset (Fin (4 * q))}
    (hXD : X ∈ defectLayer F ell a (by omega))
    (hYD : Y ∈ defectLayer F ell b (by omega))
    (hsum : a + b ≠ ell + 2) :
    3 ≤ (X ∩ Y).card := by
  let hN : ell < 4 * q := by omega
  have hXdef := (mem_defectLayer.mp hXD).1
  have hYdef := (mem_defectLayer.mp hYD).1
  have hXF : X ∈ F := (mem_defectFamily.mp hXdef).1
  have hYF : Y ∈ F := (mem_defectFamily.mp hYdef).1
  have hXcard := (mem_defectLayer.mp hXD).2
  have hYcard := (mem_defectLayer.mp hYD).2
  have hhX := defect_not_mem_next hXdef
  have hhY := defect_not_mem_next hYdef
  by_contra hnot
  have hXYle : (X ∩ Y).card ≤ 2 := by omega
  have hXYeq : (X ∩ Y).card = 2 := by
    exact Nat.le_antisymm hXYle (hinter hXF hYF)
  by_cases hlarge : ell + 2 < a + b
  · have hlower := prefix_inter_card_lower_bound (N := 4 * q)
      (ell := ell) (a := a) (b := b) (by omega)
      (A := X ∩ «prefix» (4 * q) ell)
      (B := Y ∩ «prefix» (4 * q) ell)
      inter_subset_right inter_subset_right hXcard hYcard
    have hsub :
        (X ∩ «prefix» (4 * q) ell) ∩
            (Y ∩ «prefix» (4 * q) ell) ⊆ X ∩ Y := by
      intro z hz
      simp only [mem_inter] at hz ⊢
      exact ⟨hz.1.1, hz.2.1⟩
    have hc := card_le_card hsub
    omega
  · have hsmall : a + b ≤ ell + 1 := by omega
    let PX := X ∩ «prefix» (4 * q) ell
    let PY := Y ∩ «prefix» (4 * q) ell
    let CX := X ∩ tailAfter (4 * q) (ell + 1)
    let CY := Y ∩ tailAfter (4 * q) (ell + 1)
    have hPXs : PX ⊆ «prefix» (4 * q) ell := inter_subset_right
    have hPYs : PY ⊆ «prefix» (4 * q) ell := inter_subset_right
    have hPXcard : PX.card = a := hXcard
    have hPYcard : PY.card = b := hYcard
    have hCXmem : CX ∈ defectTails F ell a hN :=
      mem_defectTails.mpr ⟨X, hXD, rfl⟩
    have haell : a ≤ ell := by
      have hc := card_le_card hPXs
      rw [card_prefix (by omega)] at hc
      rw [hPXcard] at hc
      exact hc
    obtain ⟨PZ, hPZs, hPZcard, hPZinter⟩ :
        ∃ PZ : Finset (Fin (4 * q)),
          PZ ⊆ «prefix» (4 * q) ell ∧ PZ.card = a ∧
            (if a + b ≤ ell then (PZ ∩ PY).card = 0
             else (PZ ∩ PY).card ≤ 1) := by
      by_cases hab : a + b ≤ ell
      · obtain ⟨PZ, hPZs, hPZcard, hdisj⟩ :=
          exists_prefix_subset_disjoint (N := 4 * q) (ell := ell)
            (a := a) (by omega) PY hPYs (by simpa [hPYcard] using hab)
        exact ⟨PZ, hPZs, hPZcard, by
          simp [hab, disjoint_iff_inter_eq_empty.mp hdisj]⟩
      · obtain ⟨PZ, hPZs, hPZcard, hinter'⟩ :=
          exists_prefix_subset_card_inter_le_one
            (N := 4 * q) (ell := ell) (a := a) (b := b)
            (by omega) PY hPYs hPYcard haell hsmall
        exact ⟨PZ, hPZs, hPZcard, by simp [hab, hinter']⟩
    let Z := PZ ∪ CX
    have hCXs : CX ⊆ tailAfter (4 * q) ell := by
      intro z hz
      have hz' := mem_tailAfter.mp (inter_subset_right hz)
      exact mem_tailAfter.mpr (by omega)
    have hZD : Z ∈ defectLayer F ell a hN := by
      rw [defectLayer_eq_layerFromTails hinv (by
        rcases (mem_defectFamily.mp hXdef).2 with ⟨i, hiP, hiX, _⟩
        have : 0 < PX.card := card_pos.mpr ⟨i, mem_inter.mpr ⟨hiX, hiP⟩⟩
        simpa [hPXcard] using this)]
      exact mem_layerFromTails.mpr
        ⟨CX, hCXmem, PZ, hPZs, hPZcard, rfl⟩
    have hZF : Z ∈ F :=
      (mem_defectFamily.mp (mem_defectLayer.mp hZD).1).1
    have hhZ := defect_not_mem_next (mem_defectLayer.mp hZD).1
    have hprefixZY :
        (Z ∩ Y) ∩ «prefix» (4 * q) ell = PZ ∩ PY := by
      ext z
      simp only [Z, PY, mem_inter, mem_union]
      constructor
      · rintro ⟨⟨hzPZ | hzCX, hzY⟩, hzP⟩
        · exact ⟨hzPZ, hzY, hzP⟩
        · exact ((disjoint_left.mp
            (disjoint_prefix_tailAfter (4 * q) ell))
              hzP (hCXs hzCX)).elim
      · rintro ⟨hzPZ, hzY, hzP⟩
        exact ⟨⟨Or.inl hzPZ, hzY⟩, hzP⟩
    have htailZY :
        (Z ∩ Y) ∩ tailAfter (4 * q) ell = CX ∩ CY := by
      ext z
      simp only [Z, CY, mem_inter, mem_union]
      constructor
      · rintro ⟨⟨hzPZ | hzCX, hzY⟩, hzTail⟩
        · exact ((disjoint_left.mp
            (disjoint_prefix_tailAfter (4 * q) ell))
              (hPZs hzPZ) hzTail).elim
        · exact ⟨hzCX, hzY, inter_subset_right hzCX⟩
      · rintro ⟨hzCX, hzY, hzFar⟩
        refine ⟨⟨Or.inr hzCX, hzY⟩, ?_⟩
        have hzval := mem_tailAfter.mp hzFar
        exact mem_tailAfter.mpr (by omega)
    have hZYsplit :=
      card_inter_prefix_add_card_inter_tailAfter (ell := ell) (Z ∩ Y)
    rw [hprefixZY, htailZY] at hZYsplit
    have hXYprefix :
        (X ∩ Y) ∩ «prefix» (4 * q) ell = PX ∩ PY := by
      ext z
      simp [PX, PY, and_left_comm, and_comm]
    have hXYtail :
        (X ∩ Y) ∩ tailAfter (4 * q) ell = CX ∩ CY := by
      have hhXY : nextPoint hN ∉ X ∩ Y :=
        fun h ↦ hhX (mem_inter.mp h).1
      rw [inter_tail_eq_far_of_not_next hN hhXY]
      ext z
      simp [CX, CY, and_left_comm, and_comm]
    have hXYsplit :=
      card_inter_prefix_add_card_inter_tailAfter (ell := ell) (X ∩ Y)
    rw [hXYprefix, hXYtail, hXYeq] at hXYsplit
    have hfarLe : (CX ∩ CY).card ≤ 2 := by omega
    have hZYle : (Z ∩ Y).card ≤ 2 := by
      by_cases hab : a + b ≤ ell
      · have hPZinterZero : (PZ ∩ PY).card = 0 := by
          simpa [hab] using hPZinter
        calc
          (Z ∩ Y).card =
              (PZ ∩ PY).card + (CX ∩ CY).card := hZYsplit.symm
          _ = (CX ∩ CY).card := by rw [hPZinterZero]; simp
          _ ≤ 2 := hfarLe
      · have hpLower := prefix_inter_card_lower_bound (N := 4 * q)
          (ell := ell) (a := a) (b := b) (by omega)
          hPXs hPYs hPXcard hPYcard
        have hPZinterOne : (PZ ∩ PY).card ≤ 1 := by
          simpa [hab] using hPZinter
        have hpPos : 1 ≤ (PX ∩ PY).card := by omega
        have hfarLeOne : (CX ∩ CY).card ≤ 1 := by omega
        calc
          (Z ∩ Y).card =
              (PZ ∩ PY).card + (CX ∩ CY).card := hZYsplit.symm
          _ ≤ 1 + 1 := Nat.add_le_add hPZinterOne hfarLeOne
          _ = 2 := rfl
    have hZYeq : (Z ∩ Y).card = 2 :=
      Nat.le_antisymm hZYle (hinter hZF hYF)
    have hfarPos : 0 < (CX ∩ CY).card := by
      by_cases hab : a + b ≤ ell
      · have hPZinterZero : (PZ ∩ PY).card = 0 := by
          simpa [hab] using hPZinter
        have hfarEq : (CX ∩ CY).card = 2 := by
          calc
            (CX ∩ CY).card = 0 + (CX ∩ CY).card := by omega
            _ = (PZ ∩ PY).card + (CX ∩ CY).card := by
              simp [hPZinterZero]
            _ = (Z ∩ Y).card := hZYsplit
            _ = 2 := hZYeq
        exact hfarEq ▸ by decide
      · have hPZinterOne : (PZ ∩ PY).card ≤ 1 := by
          simpa [hab] using hPZinter
        have hsum :
            (PZ ∩ PY).card + (CX ∩ CY).card = 2 :=
          hZYsplit.trans hZYeq
        omega
    obtain ⟨z, hzfar⟩ := card_pos.mp hfarPos
    have hzZ : z ∈ Z := by
      exact mem_union_right _ (mem_inter.mp hzfar).1
    have hzY : z ∈ Y := by
      have hzCY : z ∈ CY := (mem_inter.mp hzfar).2
      exact (mem_inter.mp hzCY).1
    have hzval : ell + 1 ≤ z.val :=
      mem_tailAfter.mp (inter_subset_right (mem_inter.mp hzfar).1)
    let S := singletonLeftShift (nextPoint hN) z Z
    have hhz : nextPoint hN < z := by
      exact Fin.mk_lt_mk.mpr (by simpa using hzval)
    have hSF : S ∈ F :=
      hleft.shifted_mem hhz hZF
    have hshift :
        S = insert (nextPoint hN) (Z.erase z) := by
      change singletonLeftShift (nextPoint hN) z Z =
        insert (nextPoint hN) (Z.erase z)
      rw [singletonLeftShift_eq_transpose ⟨hzZ, hhZ⟩,
        setTranspose_eq_insert_erase ⟨hzZ, hhZ⟩]
    have hSY : S ∩ Y = (Z ∩ Y).erase z := by
      rw [hshift]
      ext w
      simp only [mem_inter, mem_insert, mem_erase]
      constructor
      · rintro ⟨rfl | ⟨hwz, hwZ⟩, hwY⟩
        · exact (hhY hwY).elim
        · exact ⟨hwz, hwZ, hwY⟩
      · rintro ⟨hwz, hwZ, hwY⟩
        exact ⟨Or.inr ⟨hwz, hwZ⟩, hwY⟩
    have hzInter : z ∈ Z ∩ Y := mem_inter.mpr ⟨hzZ, hzY⟩
    have : (S ∩ Y).card = 1 := by
      rw [hSY, card_erase_of_mem hzInter, hZYeq]
    have := hinter hSF hYF
    omega

private lemma two_le_inter_rightExchange_left
    {N : ℕ} {h i : Fin N} {X Y : Finset (Fin N)}
    (hthree : 3 ≤ (X ∩ Y).card) :
    2 ≤ (rightExchange h i X ∩ Y).card := by
  have hsub :
      (X ∩ Y).erase i ⊆ rightExchange h i X ∩ Y := by
    intro z hz
    rcases mem_erase.mp hz with ⟨hzi, hzXY⟩
    rcases mem_inter.mp hzXY with ⟨hzX, hzY⟩
    exact mem_inter.mpr ⟨mem_rightExchange.mpr
      (Or.inr ⟨hzX, hzi⟩), hzY⟩
  have hc := card_le_card hsub
  by_cases hi : i ∈ X ∩ Y
  · rw [card_erase_of_mem hi] at hc
    omega
  · rw [erase_eq_of_notMem hi] at hc
    omega

private lemma two_le_inter_rightExchange_both
    {N : ℕ} {h i j : Fin N} {X Y : Finset (Fin N)}
    (hhX : h ∉ X) (hhY : h ∉ Y)
    (hthree : 3 ≤ (X ∩ Y).card) :
    2 ≤ (rightExchange h i X ∩ rightExchange h j Y).card := by
  let R := ((X ∩ Y).erase i).erase j
  have hsub :
      insert h R ⊆ rightExchange h i X ∩ rightExchange h j Y := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hzR
    · exact mem_inter.mpr ⟨by simp, by simp⟩
    · rcases mem_erase.mp hzR with ⟨hzj, hzRi⟩
      rcases mem_erase.mp hzRi with ⟨hzi, hzXY⟩
      rcases mem_inter.mp hzXY with ⟨hzX, hzY⟩
      exact mem_inter.mpr
        ⟨mem_rightExchange.mpr (Or.inr ⟨hzX, hzi⟩),
         mem_rightExchange.mpr (Or.inr ⟨hzY, hzj⟩)⟩
  have hhR : h ∉ R := by
    intro hh
    have hhXY : h ∈ X ∩ Y := (mem_erase.mp (mem_erase.mp hh).2).2
    exact hhX (mem_inter.mp hhXY).1
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hhR] at hc
  have hR : (X ∩ Y).card - 2 ≤ R.card := by
    dsimp [R]
    have h₁ : (X ∩ Y).card - 1 ≤ ((X ∩ Y).erase i).card := by
      by_cases hi : i ∈ X ∩ Y
      · rw [card_erase_of_mem hi]
      · rw [erase_eq_of_notMem hi]
        omega
    have h₂ :
        ((X ∩ Y).erase i).card - 1 ≤
          (((X ∩ Y).erase i).erase j).card := by
      by_cases hj : j ∈ (X ∩ Y).erase i
      · rw [card_erase_of_mem hj]
      · rw [erase_eq_of_notMem hj]
        omega
    omega
  omega

private lemma uniform_exchangeLayer
    {N ell a k : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    (hunif : Uniform k F) :
    Uniform k (exchangeLayer F ell a hN) := by
  intro E hE
  obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
    exchangeLayer_exists_source hinv ha hE
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXF := (mem_defectFamily.mp hXdef).1
  exact (card_rightExchange hiX (defect_not_mem_next hXdef)).trans
    (hunif hXF)

noncomputable def replaceDefectLevel {N : ℕ}
    (F D E : Finset (Finset (Fin N))) : Finset (Finset (Fin N)) :=
  (F \ D) ∪ E

private lemma uniform_replaceDefectLevel
    {N k : ℕ} {F D E : Finset (Finset (Fin N))}
    (hF : Uniform k F) (hE : Uniform k E) :
    Uniform k (replaceDefectLevel F D E) := by
  intro A hA
  rcases mem_union.mp hA with hAF | hAE
  · exact hF (mem_sdiff.mp hAF).1
  · exact hE hAE

private lemma twoIntersecting_noncentral_replacement
    {q ell a b : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hinter : TwoIntersecting F) (hleft : LeftCompressed F)
    (ha : 0 < a)
    (hab : a + b = ell + 2) (hane : a ≠ b) :
    TwoIntersecting
      (replaceDefectLevel F
        (defectLayer F ell b (by omega))
        (exchangeLayer F ell a (by omega))) := by
  intro A B hA hB
  rcases mem_union.mp hA with hAF | hAE
  · rcases mem_union.mp hB with hBF | hBE
    · exact hinter (mem_sdiff.mp hAF).1 (mem_sdiff.mp hBF).1
    · rw [inter_comm]
      have hBF' := (mem_sdiff.mp hAF).1
      have hBDnot := (mem_sdiff.mp hAF).2
      by_cases hBdef : A ∈ defectFamily F ell (by omega)
      · let j := (A ∩ «prefix» (4 * q) ell).card
        have hADj : A ∈ defectLayer F ell j (by omega) :=
          mem_defectLayer.mpr ⟨hBdef, rfl⟩
        have hjne : j ≠ b := by
          intro e
          apply hBDnot
          simpa [e] using hADj
        obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
          exchangeLayer_exists_source hinv ha hBE
        exact two_le_inter_rightExchange_left
          (defect_inter_card_three hell hinv hinter hleft
            hXD hADj (by omega))
      · exact exchange_cross_nondefect hinv ha hinter hBE hBF' hBdef
  · rcases mem_union.mp hB with hBF | hBE
    · have hBF' := (mem_sdiff.mp hBF).1
      have hBDnot := (mem_sdiff.mp hBF).2
      by_cases hBdef : B ∈ defectFamily F ell (by omega)
      · let j := (B ∩ «prefix» (4 * q) ell).card
        have hBDj : B ∈ defectLayer F ell j (by omega) :=
          mem_defectLayer.mpr ⟨hBdef, rfl⟩
        have hjne : j ≠ b := by
          intro e
          apply hBDnot
          simpa [e] using hBDj
        obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
          exchangeLayer_exists_source hinv ha hAE
        exact two_le_inter_rightExchange_left
          (defect_inter_card_three hell hinv hinter hleft
            hXD hBDj (by omega))
      · exact exchange_cross_nondefect hinv ha hinter hAE hBF' hBdef
    · obtain ⟨X, hXD, i, hiP, hiX, rfl⟩ :=
        exchangeLayer_exists_source hinv ha hAE
      obtain ⟨Y, hYD, j, hjP, hjY, rfl⟩ :=
        exchangeLayer_exists_source hinv ha hBE
      exact two_le_inter_rightExchange_both
        (defect_not_mem_next (mem_defectLayer.mp hXD).1)
        (defect_not_mem_next (mem_defectLayer.mp hYD).1)
        (defect_inter_card_three hell hinv hinter hleft hXD hYD
          (by omega))

private lemma card_replaceDefectLevel
    {N : ℕ} {F D E : Finset (Finset (Fin N))}
    (hD : D ⊆ F) (hE : Disjoint E F) :
    (replaceDefectLevel F D E).card = F.card - D.card + E.card := by
  rw [replaceDefectLevel, card_union_of_disjoint]
  · rw [card_sdiff_of_subset hD, add_comm]
  · exact hE.symm.mono_left sdiff_subset

private lemma defectLayer_subset_family
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N} :
    defectLayer F ell a hN ⊆ F := by
  intro A hA
  exact (mem_defectFamily.mp (mem_defectLayer.mp hA).1).1

private lemma noncentral_defectLayer_empty
    {q ell a : ℕ} {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F)
    (ha : 2 ≤ a) (hale : a ≤ ell)
    (hcentral : 2 * a ≠ ell + 2) :
    defectLayer F ell a (by omega) = ∅ := by
  let hN : ell < 4 * q := by omega
  let b := ell + 2 - a
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hble : b ≤ ell := by dsimp [b]; omega
  have hab : a + b = ell + 2 := by dsimp [b]; omega
  have hane : a ≠ b := by
    intro e
    apply hcentral
    omega
  by_contra hne
  have hDaPos : 0 < (defectTails F ell a hN).card := by
    have hDapos : 0 < (defectLayer F ell a hN).card := card_pos.mpr (by
      simpa only [nonempty_iff_ne_empty] using hne)
    rw [card_defectLayer hinv (by omega)] at hDapos
    exact Nat.pos_of_mul_pos_left hDapos
  let H₁ := replaceDefectLevel F
    (defectLayer F ell b hN) (exchangeLayer F ell a hN)
  let H₂ := replaceDefectLevel F
    (defectLayer F ell a hN) (exchangeLayer F ell b hN)
  have hH₁unif : Uniform (2 * q) H₁ :=
    uniform_replaceDefectLevel hunif
      (uniform_exchangeLayer hinv (by omega) hunif)
  have hH₂unif : Uniform (2 * q) H₂ :=
    uniform_replaceDefectLevel hunif
      (uniform_exchangeLayer hinv (by omega) hunif)
  have hH₁inter : TwoIntersecting H₁ :=
    twoIntersecting_noncentral_replacement hell hinv hinter hleft
      (by omega) hab hane
  have hH₂inter : TwoIntersecting H₂ :=
    twoIntersecting_noncentral_replacement hell hinv hinter hleft
      (by omega) (by omega) hane.symm
  have hH₁max := hmax H₁ hH₁unif hH₁inter
  have hH₂max := hmax H₂ hH₂unif hH₂inter
  have hH₁card := card_replaceDefectLevel
    (defectLayer_subset_family (N := 4 * q) (ell := ell) (a := b)
      (F := F) (hN := hN))
    (exchangeLayer_disjoint_family (N := 4 * q) (ell := ell) (a := a)
      (F := F) (hN := hN) hinv (by omega))
  have hH₂card := card_replaceDefectLevel
    (defectLayer_subset_family (N := 4 * q) (ell := ell) (a := a)
      (F := F) (hN := hN))
    (exchangeLayer_disjoint_family (N := 4 * q) (ell := ell) (a := b)
      (F := F) (hN := hN) hinv (by omega))
  have hE₁D₂ :
      (exchangeLayer F ell a hN).card ≤
        (defectLayer F ell b hN).card := by
    have hDcard := card_le_card
      (defectLayer_subset_family (N := 4 * q) (ell := ell) (a := b)
        (F := F) (hN := hN))
    rw [hH₁card] at hH₁max
    omega
  have hE₂D₁ :
      (exchangeLayer F ell b hN).card ≤
        (defectLayer F ell a hN).card := by
    have hDcard := card_le_card
      (defectLayer_subset_family (N := 4 * q) (ell := ell) (a := a)
        (F := F) (hN := hN))
    rw [hH₂card] at hH₂max
    omega
  rw [card_exchangeLayer, card_defectLayer hinv (by omega)] at hE₁D₂
  rw [card_exchangeLayer, card_defectLayer hinv (by omega)] at hE₂D₁
  have hDbPos : 0 < (defectTails F ell b hN).card := by
    by_contra hz
    have : (defectTails F ell b hN).card = 0 := by omega
    rw [this, mul_zero] at hE₁D₂
    have hchoose : 0 < Nat.choose ell (a - 1) :=
      Nat.choose_pos (by omega)
    have hprod :
        0 < Nat.choose ell (a - 1) *
          (defectTails F ell a hN).card :=
      Nat.mul_pos hchoose hDaPos
    omega
  have hcross := mul_mul_le_mul_mul_of_cross_bounds
    hDaPos hDbPos hE₁D₂ hE₂D₁
  have hstrict :=
    choose_product_lt_pred_product_of_add_eq
      (n := ell) (a := a) (b := b) (by omega) (by omega) hab
  have hcross' :
      Nat.choose ell (a - 1) * Nat.choose ell (b - 1) ≤
        Nat.choose ell a * Nat.choose ell b := by
    simpa [Nat.mul_comm] using hcross
  exact (Nat.not_lt_of_ge hcross') hstrict

private lemma exists_incidence_ge_average_on {α : Type*} [DecidableEq α]
    (T : Finset α) (hT : T.Nonempty) (P : Finset (Finset α)) (r : ℕ)
    (hsub : ∀ C ∈ P, C ⊆ T)
    (hcard : ∀ C ∈ P, C.card = r) :
    ∃ z ∈ T, T.card * (P.filter fun C ↦ z ∈ C).card ≥ r * P.card := by
  have hdouble :
      ∑ z ∈ T, (P.filter fun C ↦ z ∈ C).card = r * P.card := by
    calc
      ∑ z ∈ T, (P.filter fun C ↦ z ∈ C).card =
          ∑ z ∈ T, ∑ C ∈ P, if z ∈ C then (1 : ℕ) else 0 := by
            apply sum_congr rfl
            intro z hz
            simp
      _ = ∑ C ∈ P, ∑ z ∈ T, if z ∈ C then (1 : ℕ) else 0 := by
            rw [sum_comm]
      _ = ∑ C ∈ P, C.card := by
            apply sum_congr rfl
            intro C hC
            have hs := hsub C hC
            calc
              ∑ z ∈ T, (if z ∈ C then (1 : ℕ) else 0) =
                  (T.filter fun z ↦ z ∈ C).card := by
                    rw [Finset.sum_boole (R := ℕ)]
                    simp
              _ = C.card := by
                rw [filter_mem_eq_inter, inter_eq_right.mpr hs]
      _ = ∑ _C ∈ P, r := by
            apply sum_congr rfl
            intro C hC
            exact hcard C hC
      _ = r * P.card := by simp [Nat.mul_comm]
  by_contra h
  push Not at h
  have hlt :
      ∑ z ∈ T, T.card * (P.filter fun C ↦ z ∈ C).card <
        ∑ _z ∈ T, r * P.card := by
    exact sum_lt_sum_of_nonempty hT
      (fun z hz ↦ h z hz)
  rw [← mul_sum, hdouble] at hlt
  simp at hlt

/-- Exchanges generated by an explicitly supplied subfamily of far tails. -/
noncomputable def exchangeFromTails {N : ℕ}
    (ell a : ℕ) (hN : ell < N) (P : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  layerFromTails N ell (a - 1)
    (P.image fun C ↦ insert (nextPoint hN) C)

private lemma exchangeFromTails_subset_exchangeLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    {P : Finset (Finset (Fin N))}
    (hP : P ⊆ defectTails F ell a hN) :
    exchangeFromTails ell a hN P ⊆ exchangeLayer F ell a hN := by
  intro E hE
  rcases mem_layerFromTails.mp hE with
    ⟨D, hD, B, hBP, hBcard, rfl⟩
  rcases mem_image.mp hD with ⟨C, hCP, rfl⟩
  exact mem_layerFromTails.mpr
    ⟨insert (nextPoint hN) C,
      mem_image.mpr ⟨C, hP hCP, rfl⟩,
      B, hBP, hBcard, rfl⟩

private lemma card_exchangeFromTails
    {N ell a : ℕ} {hN : ell < N} {P : Finset (Finset (Fin N))}
    (hP : ∀ C ∈ P, C ⊆ tailAfter N (ell + 1)) :
    (exchangeFromTails ell a hN P).card =
      Nat.choose ell (a - 1) * P.card := by
  have hPtail :
      ∀ C ∈ P.image (fun C ↦ insert (nextPoint hN) C),
        C ⊆ tailAfter N ell := by
    intro C hC
    rcases mem_image.mp hC with ⟨D, hDP, rfl⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hxD
    · exact nextPoint_mem_tailAfter hN
    · have := mem_tailAfter.mp (hP D hDP hxD)
      exact mem_tailAfter.mpr (by omega)
  rw [exchangeFromTails, card_layerFromTails hPtail, card_prefix hN.le,
    card_image_iff.mpr (insert_next_injective_on_farTails hN P hP)]

private lemma card_defectLayer_from_tail_subfamily
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    {P : Finset (Finset (Fin N))}
    (hP : P ⊆ defectTails F ell a hN) :
    (layerFromTails N ell a P).card = Nat.choose ell a * P.card := by
  rw [card_layerFromTails (fun C hC ↦
    (defectTails_subset_tailAfter (hP hC)).trans ?_), card_prefix hN.le]
  intro x hx
  simp only [mem_tailAfter] at hx ⊢
  omega

private lemma layerFromTails_subset_defectLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    (hinv : PrefixInvariant F ell) (ha : 0 < a)
    {P : Finset (Finset (Fin N))}
    (hP : P ⊆ defectTails F ell a hN) :
    layerFromTails N ell a P ⊆ defectLayer F ell a hN := by
  rw [defectLayer_eq_layerFromTails hinv ha]
  intro A hA
  rcases mem_layerFromTails.mp hA with
    ⟨C, hCP, B, hBP, hBcard, rfl⟩
  exact mem_layerFromTails.mpr
    ⟨C, hP hCP, B, hBP, hBcard, rfl⟩

private lemma twoIntersecting_central_replacement
    {q ell i : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hinter : TwoIntersecting F) (hleft : LeftCompressed F)
    (hi : 0 < i) (hicentral : 2 * i = ell + 2)
    {P Q : Finset (Finset (Fin (4 * q)))}
    (hP : P = defectTails F ell i (by omega))
    (hQP : Q ⊆ P)
    {z : Fin (4 * q)} (hzQ : ∀ C ∈ Q, z ∈ C) :
    TwoIntersecting
      (replaceDefectLevel F
        (layerFromTails (4 * q) ell i (P \ Q))
        (exchangeFromTails ell i (by omega) Q)) := by
  let hN : ell < 4 * q := by omega
  have hQdef :
      Q ⊆ defectTails F ell i hN := by simpa [hP] using hQP
  have hGsub :
      exchangeFromTails ell i hN Q ⊆ exchangeLayer F ell i hN :=
    exchangeFromTails_subset_exchangeLayer hQdef
  have hRsub :
      layerFromTails (4 * q) ell i (P \ Q) ⊆
        defectLayer F ell i hN := by
    apply layerFromTails_subset_defectLayer hinv hi
    intro C hC
    have hCP : C ∈ P := (mem_sdiff.mp hC).1
    simpa [hP] using hCP
  intro A B hA hB
  rcases mem_union.mp hA with hAF | hAG
  · rcases mem_union.mp hB with hBF | hBG
    · exact hinter (mem_sdiff.mp hAF).1 (mem_sdiff.mp hBF).1
    · rw [inter_comm]
      have hAF' := (mem_sdiff.mp hAF).1
      have hARnot := (mem_sdiff.mp hAF).2
      have hBE := hGsub hBG
      by_cases hAdef : A ∈ defectFamily F ell hN
      · let j := (A ∩ «prefix» (4 * q) ell).card
        have hADj : A ∈ defectLayer F ell j hN :=
          mem_defectLayer.mpr ⟨hAdef, rfl⟩
        by_cases hji : j = i
        · have hADi : A ∈ defectLayer F ell i hN := hji ▸ hADj
          have hAtailP :
              A ∩ tailAfter (4 * q) (ell + 1) ∈ P := by
            rw [hP]
            exact mem_defectTails.mpr ⟨A, hADi, rfl⟩
          have hAtailQ :
              A ∩ tailAfter (4 * q) (ell + 1) ∈ Q := by
            by_contra hnQ
            apply hARnot
            apply mem_layerFromTails.mpr
            refine ⟨A ∩ tailAfter (4 * q) (ell + 1),
              mem_sdiff.mpr ⟨hAtailP, hnQ⟩,
              A ∩ «prefix» (4 * q) ell, inter_subset_right,
              (mem_defectLayer.mp hADi).2, ?_⟩
            rw [← inter_tail_eq_far_of_not_next hN
              (defect_not_mem_next hAdef)]
            exact inter_prefix_union_inter_tailAfter A
          rcases mem_layerFromTails.mp hBG with
            ⟨D, hD, BE, hBEP, hBEcard, rfl⟩
          rcases mem_image.mp hD with ⟨CE, hCEQ, rfl⟩
          have hzA : z ∈ A := inter_subset_left
            (hzQ _ hAtailQ)
          have hzCE : z ∈ CE := hzQ _ hCEQ
          have hzTail := defectTails_subset_tailAfter
            (hQdef hCEQ) hzCE
          have hApreS : A ∩ «prefix» (4 * q) ell ⊆
              «prefix» (4 * q) ell := inter_subset_right
          have hlower := prefix_inter_card_lower_bound
            (N := 4 * q) (ell := ell) (a := i - 1) (b := i)
            (by omega) hBEP hApreS hBEcard
            (mem_defectLayer.mp hADi).2
          have hprePos :
              0 < (BE ∩ (A ∩ «prefix» (4 * q) ell)).card := by
            omega
          obtain ⟨w, hw⟩ := card_pos.mp hprePos
          have hwBE := (mem_inter.mp hw).1
          have hwA := (mem_inter.mp (mem_inter.mp hw).2).1
          have hwPre := (mem_inter.mp (mem_inter.mp hw).2).2
          have hwz : w ≠ z := by
            intro e
            subst w
            have hwlt := mem_prefix.mp hwPre
            have hzge := mem_tailAfter.mp hzTail
            omega
          have hpair :
              ({w, z} : Finset (Fin (4 * q))) ⊆
                ((BE ∪ insert (nextPoint hN) CE) ∩ A) := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact mem_inter.mpr ⟨mem_union_left _
                hwBE, hwA⟩
            · exact mem_inter.mpr ⟨mem_union_right _
                (mem_insert_of_mem hzCE), hzA⟩
          have hc := card_le_card hpair
          simpa [hwz] using hc
        · obtain ⟨X, hXD, x, hxP, hxX, rfl⟩ :=
            exchangeLayer_exists_source hinv hi hBE
          exact two_le_inter_rightExchange_left
            (defect_inter_card_three hell hinv hinter hleft
              hXD hADj (by omega))
      · exact exchange_cross_nondefect hinv hi hinter hBE hAF' hAdef
  · rcases mem_union.mp hB with hBF | hBG
    · have hBF' := (mem_sdiff.mp hBF).1
      have hBRnot := (mem_sdiff.mp hBF).2
      have hAE := hGsub hAG
      by_cases hBdef : B ∈ defectFamily F ell hN
      · let j := (B ∩ «prefix» (4 * q) ell).card
        have hBDj : B ∈ defectLayer F ell j hN :=
          mem_defectLayer.mpr ⟨hBdef, rfl⟩
        by_cases hji : j = i
        · have hBDi : B ∈ defectLayer F ell i hN := hji ▸ hBDj
          have hBtailP :
              B ∩ tailAfter (4 * q) (ell + 1) ∈ P := by
            rw [hP]
            exact mem_defectTails.mpr ⟨B, hBDi, rfl⟩
          have hBtailQ :
              B ∩ tailAfter (4 * q) (ell + 1) ∈ Q := by
            by_contra hnQ
            apply hBRnot
            apply mem_layerFromTails.mpr
            refine ⟨B ∩ tailAfter (4 * q) (ell + 1),
              mem_sdiff.mpr ⟨hBtailP, hnQ⟩,
              B ∩ «prefix» (4 * q) ell, inter_subset_right,
              (mem_defectLayer.mp hBDi).2, ?_⟩
            rw [← inter_tail_eq_far_of_not_next hN
              (defect_not_mem_next hBdef)]
            exact inter_prefix_union_inter_tailAfter B
          rcases mem_layerFromTails.mp hAG with
            ⟨D, hD, BA, hBAP, hBAcard, rfl⟩
          rcases mem_image.mp hD with ⟨CA, hCAQ, rfl⟩
          have hzB : z ∈ B := inter_subset_left
            (hzQ _ hBtailQ)
          have hzCA : z ∈ CA := hzQ _ hCAQ
          have hzTail := defectTails_subset_tailAfter
            (hQdef hCAQ) hzCA
          have hBpreS : B ∩ «prefix» (4 * q) ell ⊆
              «prefix» (4 * q) ell := inter_subset_right
          have hlower := prefix_inter_card_lower_bound
            (N := 4 * q) (ell := ell) (a := i - 1) (b := i)
            (by omega) hBAP hBpreS hBAcard
            (mem_defectLayer.mp hBDi).2
          have hprePos :
              0 < (BA ∩ (B ∩ «prefix» (4 * q) ell)).card := by
            omega
          obtain ⟨w, hw⟩ := card_pos.mp hprePos
          have hwBA := (mem_inter.mp hw).1
          have hwB := (mem_inter.mp (mem_inter.mp hw).2).1
          have hwPre := (mem_inter.mp (mem_inter.mp hw).2).2
          have hwz : w ≠ z := by
            intro e
            subst w
            have hwlt := mem_prefix.mp hwPre
            have hzge := mem_tailAfter.mp hzTail
            omega
          have hpair :
              ({w, z} : Finset (Fin (4 * q))) ⊆
                ((BA ∪ insert (nextPoint hN) CA) ∩ B) := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact mem_inter.mpr ⟨mem_union_left _ hwBA, hwB⟩
            · exact mem_inter.mpr ⟨mem_union_right _
                (mem_insert_of_mem hzCA), hzB⟩
          have hc := card_le_card hpair
          simpa [hwz] using hc
        · obtain ⟨X, hXD, x, hxP, hxX, rfl⟩ :=
            exchangeLayer_exists_source hinv hi hAE
          exact two_le_inter_rightExchange_left
            (defect_inter_card_three hell hinv hinter hleft
              hXD hBDj (by omega))
      · exact exchange_cross_nondefect hinv hi hinter hAE hBF' hBdef
    · rcases mem_layerFromTails.mp hAG with
        ⟨D₁, hD₁, B₁, hB₁P, hB₁card, rfl⟩
      rcases mem_image.mp hD₁ with ⟨C₁, hC₁Q, rfl⟩
      rcases mem_layerFromTails.mp hBG with
        ⟨D₂, hD₂, B₂, hB₂P, hB₂card, rfl⟩
      rcases mem_image.mp hD₂ with ⟨C₂, hC₂Q, rfl⟩
      have hz₁ : z ∈ C₁ := hzQ _ hC₁Q
      have hz₂ : z ∈ C₂ := hzQ _ hC₂Q
      have hzh : z ≠ nextPoint hN := by
        intro e
        subst z
        have hfar := defectTails_subset_tailAfter
          (hQdef hC₁Q) hz₁
        exact nextPoint_not_mem_farTail hN hfar
      have hpair :
          ({nextPoint hN, z} : Finset (Fin (4 * q))) ⊆
            ((B₁ ∪ insert (nextPoint hN) C₁) ∩
              (B₂ ∪ insert (nextPoint hN) C₂)) := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp
        · exact mem_inter.mpr
            ⟨mem_union_right _ (mem_insert_of_mem hz₁),
             mem_union_right _ (mem_insert_of_mem hz₂)⟩
      have hc := card_le_card hpair
      simpa [hzh, Ne.symm hzh] using hc

private lemma central_defectLayer_empty
    {q ell i : ℕ} {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F)
    (hi : 2 ≤ i) (hicentral : 2 * i = ell + 2) :
    defectLayer F ell i (by omega) = ∅ := by
  let hN : ell < 4 * q := by omega
  let P := defectTails F ell i hN
  by_contra hne
  have hDpos : 0 < (defectLayer F ell i hN).card :=
    card_pos.mpr (by simpa only [nonempty_iff_ne_empty] using hne)
  have hPpos : 0 < P.card := by
    rw [card_defectLayer hinv (by omega)] at hDpos
    dsimp only [P]
    exact Nat.pos_of_mul_pos_left hDpos
  have hPsub : ∀ C ∈ P, C ⊆ tailAfter (4 * q) (ell + 1) := by
    intro C hC
    exact defectTails_subset_tailAfter hC
  have hPcard : ∀ C ∈ P, C.card = 2 * q - i := by
    intro C hC
    rcases mem_defectTails.mp hC with ⟨X, hXD, rfl⟩
    have hXdef := (mem_defectLayer.mp hXD).1
    have hXpre := (mem_defectLayer.mp hXD).2
    have hXmem := (mem_defectFamily.mp hXdef).1
    have hsplit :=
      card_inter_prefix_add_card_inter_tailAfter (ell := ell) X
    rw [inter_tail_eq_far_of_not_next hN (defect_not_mem_next hXdef),
      hXpre, hunif hXmem] at hsplit
    omega
  let T := tailAfter (4 * q) (ell + 1)
  have hTcard : T.card = 4 * q - (ell + 1) := by
    dsimp only [T]
    exact card_tailAfter (by omega)
  have hTnonempty : T.Nonempty := by
    apply card_pos.mp
    rw [hTcard]
    omega
  obtain ⟨z, hzT, hzavg⟩ :=
    exists_incidence_ge_average_on T hTnonempty P (2 * q - i)
      hPsub hPcard
  let Q := P.filter fun C ↦ z ∈ C
  have hQP : Q ⊆ P := filter_subset _ _
  have hzQ : ∀ C ∈ Q, z ∈ C := by
    intro C hC
    exact (mem_filter.mp hC).2
  have hzavg' : T.card * Q.card ≥ (2 * q - i) * P.card := by
    simpa only [Q] using hzavg
  let R := layerFromTails (4 * q) ell i (P \ Q)
  let E := exchangeFromTails ell i hN Q
  have hRsubD : R ⊆ defectLayer F ell i hN := by
    apply layerFromTails_subset_defectLayer hinv (by omega)
    intro C hC
    exact (mem_sdiff.mp hC).1
  have hRsubF : R ⊆ F :=
    hRsubD.trans defectLayer_subset_family
  have hEsub : E ⊆ exchangeLayer F ell i hN := by
    exact exchangeFromTails_subset_exchangeLayer hQP
  let H := replaceDefectLevel F R E
  have hHunif : Uniform (2 * q) H := by
    apply uniform_replaceDefectLevel hunif
    intro A hA
    exact uniform_exchangeLayer hinv (by omega) hunif (hEsub hA)
  have hHinter : TwoIntersecting H := by
    exact twoIntersecting_central_replacement hell hinv hinter hleft
      (by omega) hicentral (P := P) (Q := Q) rfl hQP hzQ
  have hEdisj : Disjoint E F :=
    (exchangeLayer_disjoint_family hinv (by omega)).mono_left hEsub
  have hHcard : H.card = F.card - R.card + E.card :=
    card_replaceDefectLevel hRsubF hEdisj
  have hHmax := hmax H hHunif hHinter
  have hRleF : R.card ≤ F.card := card_le_card hRsubF
  have hEleR : E.card ≤ R.card := by
    rw [hHcard] at hHmax
    omega
  have hRcard : R.card = Nat.choose ell i * (P \ Q).card := by
    dsimp only [R]
    exact card_defectLayer_from_tail_subfamily
      (fun C hC ↦ (mem_sdiff.mp hC).1)
  have hEcard : E.card = Nat.choose ell (i - 1) * Q.card := by
    dsimp only [E]
    exact card_exchangeFromTails (fun C hC ↦ hPsub C (hQP hC))
  have hPQcard : (P \ Q).card = P.card - Q.card :=
    card_sdiff_of_subset hQP
  rw [hRcard, hEcard, hPQcard] at hEleR
  have hpascal :
      Nat.choose (ell + 1) i =
        Nat.choose ell (i - 1) + Nat.choose ell i := by
    have hipred : i - 1 + 1 = i := by omega
    simpa only [hipred] using (Nat.choose_succ_succ' ell (i - 1))
  have hcount :
      Nat.choose (ell + 1) i * Q.card ≤
        Nat.choose ell i * P.card := by
    rw [hpascal, add_mul]
    have hQleP : Q.card ≤ P.card := card_le_card hQP
    have hsplit :
        Nat.choose ell i * (P.card - Q.card) +
            Nat.choose ell i * Q.card =
          Nat.choose ell i * P.card := by
      rw [← mul_add, Nat.sub_add_cancel hQleP]
    exact le_trans (Nat.add_le_add_right hEleR _)
      (le_of_eq hsplit)
  have hiell : i ≤ ell := by omega
  have hTvalue : T.card = 2 * (2 * q - i) + 1 := by
    rw [hTcard]
    omega
  have hsmallValue : ell + 1 - i = i - 1 := by omega
  have hlargeValue : ell + 1 = 2 * i - 1 := by omega
  have hcoef :
      T.card * (ell + 1 - i) < (2 * q - i) * (ell + 1) := by
    rw [hTvalue, hsmallValue, hlargeValue]
    have hiq : i ≤ q := by omega
    have hi2q : i ≤ 2 * q := by omega
    have hqi : 2 * q - i + i = 2 * q := Nat.sub_add_cancel hi2q
    have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
    have hlt : i - 1 < 2 * q - i := by omega
    calc
      (2 * (2 * q - i) + 1) * (i - 1) =
          2 * (2 * q - i) * (i - 1) + (i - 1) := by ring
      _ < 2 * (2 * q - i) * (i - 1) + (2 * q - i) :=
        Nat.add_lt_add_left hlt _
      _ = (2 * q - i) * (2 * i - 1) := by
        have hinner : 2 * (i - 1) + 1 = 2 * i - 1 := by omega
        calc
          2 * (2 * q - i) * (i - 1) + (2 * q - i) =
              (2 * q - i) * (2 * (i - 1) + 1) := by ring
          _ = (2 * q - i) * (2 * i - 1) := by rw [hinner]
  have hcoefScaled := Nat.mul_lt_mul_of_pos_right hcoef hPpos
  have havgScaled := Nat.mul_le_mul_right (ell + 1) hzavg'
  have hcross :
      P.card * (ell + 1 - i) < Q.card * (ell + 1) := by
    apply Nat.lt_of_mul_lt_mul_left (a := T.card)
    calc
      T.card * (P.card * (ell + 1 - i)) =
          (T.card * (ell + 1 - i)) * P.card := by ac_rfl
      _ < ((2 * q - i) * (ell + 1)) * P.card := hcoefScaled
      _ = ((2 * q - i) * P.card) * (ell + 1) := by ac_rfl
      _ ≤ (T.card * Q.card) * (ell + 1) := havgScaled
      _ = T.card * (Q.card * (ell + 1)) := by ac_rfl
  have hstrict := choose_succ_left_mul_lt_of_cross_lt hiell hcross
  exact (Nat.not_lt_of_ge hcount) hstrict

private lemma rightExchange_mem_exchangeLayer
    {N ell a : ℕ} {F : Finset (Finset (Fin N))} {hN : ell < N}
    {X : Finset (Fin N)}
    (hXD : X ∈ defectLayer F ell a hN)
    {i : Fin N} (hiP : i ∈ «prefix» N ell) (hiX : i ∈ X) :
    rightExchange (nextPoint hN) i X ∈ exchangeLayer F ell a hN := by
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXcard := (mem_defectLayer.mp hXD).2
  have hhX := defect_not_mem_next hXdef
  apply mem_layerFromTails.mpr
  refine ⟨insert (nextPoint hN) (X ∩ tailAfter N (ell + 1)),
    mem_image.mpr ⟨X ∩ tailAfter N (ell + 1),
      mem_defectTails.mpr ⟨X, hXD, rfl⟩, rfl⟩,
    (X ∩ «prefix» N ell).erase i, ?_, ?_, ?_⟩
  · exact (erase_subset _ _).trans inter_subset_right
  · have hiInter : i ∈ X ∩ «prefix» N ell :=
      mem_inter.mpr ⟨hiX, hiP⟩
    rw [card_erase_of_mem hiInter, hXcard]
  · ext x
    simp only [mem_union, mem_erase, mem_inter, mem_prefix, mem_insert,
      mem_tailAfter, mem_rightExchange]
    constructor
    · rintro (⟨hxi, hxX, hxlt⟩ | rfl | ⟨hxX, hxge⟩)
      · exact Or.inr ⟨hxX, hxi⟩
      · exact Or.inl rfl
      · right
        refine ⟨hxX, ?_⟩
        intro hxi
        subst x
        have := mem_prefix.mp hiP
        omega
    · rintro (rfl | ⟨hxX, hxi⟩)
      · exact Or.inr (Or.inl rfl)
      · by_cases hxlt : x.val < ell
        · exact Or.inl ⟨hxi, hxX, hxlt⟩
        · right
          right
          refine ⟨hxX, ?_⟩
          by_cases hxeq : x.val = ell
          · have hxnext : x = nextPoint hN := Fin.ext hxeq
            exact (hhX (hxnext ▸ hxX)).elim
          · omega

private lemma low_defectLayer_empty
    {q ell : ℕ} {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    defectLayer F ell 1 (by omega) = ∅ := by
  let hN : ell < 4 * q := by omega
  by_contra hne
  obtain ⟨X, hXD⟩ :
      ∃ X, X ∈ defectLayer F ell 1 hN := by
    rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨X, hX⟩
    exact ⟨X, hX⟩
  have hXdef := (mem_defectLayer.mp hXD).1
  have hXF := (mem_defectFamily.mp hXdef).1
  rcases (mem_defectFamily.mp hXdef).2 with
    ⟨i, hiP, hiX, hhX, hiMissing⟩
  let E := rightExchange (nextPoint hN) i X
  have hEexchange : E ∈ exchangeLayer F ell 1 hN := by
    exact rightExchange_mem_exchangeLayer hXD hiP hiX
  have hEcard : E.card = 2 * q := by
    dsimp only [E]
    exact (card_rightExchange hiX hhX).trans (hunif hXF)
  have hEinterF : ∀ {Y}, Y ∈ F → 2 ≤ (E ∩ Y).card := by
    intro Y hYF
    by_cases hYdef : Y ∈ defectFamily F ell hN
    · let j := (Y ∩ «prefix» (4 * q) ell).card
      have hYDj : Y ∈ defectLayer F ell j hN :=
        mem_defectLayer.mpr ⟨hYdef, rfl⟩
      have hjpos : 0 < j := by
        rcases (mem_defectFamily.mp hYdef).2 with
          ⟨w, hwP, hwY, _hwNext, _hwMissing⟩
        exact card_pos.mpr ⟨w, mem_inter.mpr ⟨hwY, hwP⟩⟩
      have hjle : j ≤ ell := by
        have hc := card_le_card
          (inter_subset_right : Y ∩ «prefix» (4 * q) ell ⊆
            «prefix» (4 * q) ell)
        rw [card_prefix (by omega)] at hc
        exact hc
      exact two_le_inter_rightExchange_left
        (defect_inter_card_three hell hinv hinter hleft hXD hYDj
          (by omega))
    · exact exchange_cross_nondefect hinv (by omega) hinter
        hEexchange hYF hYdef
  let H := insert E F
  have hHunif : Uniform (2 * q) H := by
    intro A hA
    rcases mem_insert.mp hA with rfl | hAF
    · exact hEcard
    · exact hunif hAF
  have hHinter : TwoIntersecting H := by
    intro A B hA hB
    rcases mem_insert.mp hA with rfl | hAF
    · rcases mem_insert.mp hB with rfl | hBF
      · simpa [hEcard] using (show 2 ≤ 2 * q by omega)
      · exact hEinterF hBF
    · rcases mem_insert.mp hB with rfl | hBF
      · rw [inter_comm]
        exact hEinterF hAF
      · exact hinter hAF hBF
  have hHmax := hmax H hHunif hHinter
  have hEmissing : E ∉ F := hiMissing
  have hHcard : H.card = F.card + 1 := by
    dsimp only [H]
    rw [card_insert_of_notMem hEmissing]
  rw [hHcard] at hHmax
  omega

private lemma all_defects_empty
    {q ell : ℕ} {F : Finset (Finset (Fin (4 * q)))}
    (hell : ell < 2 * q)
    (hinv : PrefixInvariant F ell)
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    defectFamily F ell (by omega) = ∅ := by
  let hN : ell < 4 * q := by omega
  rw [Finset.eq_empty_iff_forall_notMem]
  intro X hXD
  let a := (X ∩ «prefix» (4 * q) ell).card
  have hXDa : X ∈ defectLayer F ell a hN :=
    mem_defectLayer.mpr ⟨hXD, rfl⟩
  have hapos : 0 < a := by
    rcases (mem_defectFamily.mp hXD).2 with
      ⟨i, hiP, hiX, _hiNext, _hiMissing⟩
    exact card_pos.mpr ⟨i, mem_inter.mpr ⟨hiX, hiP⟩⟩
  have hale : a ≤ ell := by
    have hc := card_le_card
      (inter_subset_right : X ∩ «prefix» (4 * q) ell ⊆
        «prefix» (4 * q) ell)
    rw [card_prefix (by omega)] at hc
    exact hc
  by_cases haone : a = 1
  · have hempty := low_defectLayer_empty hell hinv hunif hinter hmax hleft
    rw [haone, hempty] at hXDa
    exact Finset.notMem_empty X hXDa
  · have hatwo : 2 ≤ a := by omega
    by_cases hcentral : 2 * a = ell + 2
    · have hempty := central_defectLayer_empty hell hinv hunif hinter
        hmax hleft hatwo hcentral
      rw [hempty] at hXDa
      exact Finset.notMem_empty X hXDa
    · have hempty := noncentral_defectLayer_empty hell hinv hunif hinter
        hmax hleft hatwo hale hcentral
      rw [hempty] at hXDa
      exact Finset.notMem_empty X hXDa

private lemma inter_prefix_succ_eq {N ell : ℕ} (hN : ell < N)
    (A : Finset (Fin N)) :
    A ∩ «prefix» N (ell + 1) =
      if nextPoint hN ∈ A then
        insert (nextPoint hN) (A ∩ «prefix» N ell)
      else A ∩ «prefix» N ell := by
  by_cases hhA : nextPoint hN ∈ A
  · rw [if_pos hhA]
    ext x
    simp only [mem_inter, mem_prefix, mem_insert]
    constructor
    · rintro ⟨hxA, hxlt⟩
      by_cases hxeq : x.val = ell
      · exact Or.inl (Fin.ext hxeq)
      · exact Or.inr ⟨hxA, by omega⟩
    · rintro (rfl | ⟨hxA, hxlt⟩)
      · exact ⟨hhA, by simp⟩
      · exact ⟨hxA, by omega⟩
  · rw [if_neg hhA]
    ext x
    simp only [mem_inter, mem_prefix]
    constructor
    · rintro ⟨hxA, hxlt⟩
      refine ⟨hxA, ?_⟩
      by_cases hxeq : x.val = ell
      · have hxnext : x = nextPoint hN := Fin.ext hxeq
        exact (hhA (hxnext ▸ hxA)).elim
      · omega
    · rintro ⟨hxA, hxlt⟩
      exact ⟨hxA, by omega⟩

private lemma inter_tail_eq_at_next {N ell : ℕ} (hN : ell < N)
    (A : Finset (Fin N)) :
    A ∩ tailAfter N ell =
      if nextPoint hN ∈ A then
        insert (nextPoint hN) (A ∩ tailAfter N (ell + 1))
      else A ∩ tailAfter N (ell + 1) := by
  by_cases hhA : nextPoint hN ∈ A
  · rw [if_pos hhA]
    ext x
    simp only [mem_inter, mem_tailAfter, mem_insert]
    constructor
    · rintro ⟨hxA, hxge⟩
      by_cases hxeq : x.val = ell
      · exact Or.inl (Fin.ext hxeq)
      · exact Or.inr ⟨hxA, by omega⟩
    · rintro (rfl | ⟨hxA, hxge⟩)
      · exact ⟨hhA, le_rfl⟩
      · exact ⟨hxA, by omega⟩
  · rw [if_neg hhA]
    exact inter_tail_eq_far_of_not_next hN hhA

private lemma cross_next_membership_iff
    {N ell : ℕ} {F : Finset (Finset (Fin N))} (hN : ell < N)
    (hinv : PrefixInvariant F ell) (hleft : LeftCompressed F)
    (hdef : defectFamily F ell hN = ∅)
    {A B : Finset (Fin N)}
    (hA0 : nextPoint hN ∉ A) (hB1 : nextPoint hN ∈ B)
    (htail : A ∩ tailAfter N (ell + 1) =
      B ∩ tailAfter N (ell + 1))
    (hcard : (A ∩ «prefix» N (ell + 1)).card =
      (B ∩ «prefix» N (ell + 1)).card) :
    (A ∈ F ↔ B ∈ F) := by
  have hpreCard :
      (A ∩ «prefix» N ell).card =
        (B ∩ «prefix» N ell).card + 1 := by
    rw [inter_prefix_succ_eq hN A, if_neg hA0,
      inter_prefix_succ_eq hN B, if_pos hB1] at hcard
    have hhpre : nextPoint hN ∉ B ∩ «prefix» N ell :=
      fun hh ↦ nextPoint_not_mem_prefix hN (mem_inter.mp hh).2
    rw [card_insert_of_notMem hhpre] at hcard
    omega
  have hlt :
      (B ∩ «prefix» N ell).card <
        (A ∩ «prefix» N ell).card := by omega
  obtain ⟨i, hiAP, hiBP⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hiA : i ∈ A := (mem_inter.mp hiAP).1
  have hiP : i ∈ «prefix» N ell := (mem_inter.mp hiAP).2
  have hiB : i ∉ B := by
    intro hi
    exact hiBP (mem_inter.mpr ⟨hi, hiP⟩)
  constructor
  · intro hAF
    let E := rightExchange (nextPoint hN) i A
    have hEnF : E ∈ F := by
      by_contra hmissing
      have hAdef : A ∈ defectFamily F ell hN :=
        mem_defectFamily.mpr
          ⟨hAF, ⟨i, hiP, hiA, hA0, hmissing⟩⟩
      rw [hdef] at hAdef
      exact Finset.notMem_empty A hAdef
    apply (hinv ?_ ?_).mp hEnF
    · rw [rightExchange_inter_tail hN hiP,
        inter_tail_eq_at_next hN B, if_pos hB1, htail]
    · rw [rightExchange_inter_prefix hN,
        card_erase_of_mem hiAP]
      omega
  · intro hBF
    let L := singletonLeftShift i (nextPoint hN) B
    have hilt : i < nextPoint hN := by
      exact Fin.mk_lt_mk.mpr (mem_prefix.mp hiP)
    have hLF : L ∈ F := hleft.shifted_mem hilt hBF
    have hLeq : L = insert i (B.erase (nextPoint hN)) := by
      dsimp only [L]
      rw [singletonLeftShift_eq_transpose ⟨hB1, hiB⟩,
        setTranspose_eq_insert_erase ⟨hB1, hiB⟩]
    apply (hinv ?_ ?_).mp hLF
    · rw [inter_tail_eq_at_next hN A, if_neg hA0]
      ext x
      have hxTail := congrArg (fun S : Finset (Fin N) ↦ x ∈ S) htail
      simp only [mem_inter, mem_tailAfter] at hxTail
      simp only [hLeq, mem_inter, mem_insert, mem_erase, mem_tailAfter]
      constructor
      · rintro ⟨rfl | ⟨hxnext, hxB⟩, hxge⟩
        · have := mem_prefix.mp hiP
          omega
        · have hfar : ell + 1 ≤ x.val := by
            by_cases hxeq : x.val = ell
            · have : x = nextPoint hN := Fin.ext hxeq
              exact (hxnext this).elim
            · omega
          exact hxTail.mpr ⟨hxB, hfar⟩
      · rintro ⟨hxA, hxfar⟩
        have hxB := (hxTail.mp ⟨hxA, hxfar⟩).1
        refine ⟨Or.inr ⟨?_, hxB⟩, by omega⟩
        intro hxeq
        subst x
        have hnextval : (nextPoint hN).val = ell := rfl
        omega
    · have hLpre :
          L ∩ «prefix» N ell =
            insert i (B ∩ «prefix» N ell) := by
        ext x
        simp only [hLeq, mem_inter, mem_insert, mem_erase, mem_prefix]
        constructor
        · rintro ⟨rfl | ⟨hxnext, hxB⟩, hxlt⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxB, hxlt⟩
        · rintro (rfl | ⟨hxB, hxlt⟩)
          · exact ⟨Or.inl rfl, mem_prefix.mp hiP⟩
          · refine ⟨Or.inr ⟨?_, hxB⟩, hxlt⟩
            intro hxeq
            subst x
            simp at hxlt
      rw [hLpre, card_insert_of_notMem hiBP]
      omega

private lemma prefixInvariant_zero {N : ℕ}
    (F : Finset (Finset (Fin N))) : PrefixInvariant F 0 := by
  intro A B htail _hcard
  change A ∩ tailAfter N 0 = B ∩ tailAfter N 0 at htail
  have htailUniv : tailAfter N 0 = (univ : Finset (Fin N)) := by
    ext x
    simp
  rw [htailUniv] at htail
  simp only [inter_univ] at htail
  subst B
  exact Iff.rfl

private lemma prefixInvariant_succ
    {N ell : ℕ} {F : Finset (Finset (Fin N))} (hN : ell < N)
    (hinv : PrefixInvariant F ell) (hleft : LeftCompressed F)
    (hdef : defectFamily F ell hN = ∅) :
    PrefixInvariant F (ell + 1) := by
  intro A B htail hcard
  change A ∩ tailAfter N (ell + 1) =
      B ∩ tailAfter N (ell + 1) at htail
  change (A ∩ «prefix» N (ell + 1)).card =
      (B ∩ «prefix» N (ell + 1)).card at hcard
  by_cases hA : nextPoint hN ∈ A
  · by_cases hB : nextPoint hN ∈ B
    · apply hinv
      · rw [inter_tail_eq_at_next hN A, if_pos hA,
          inter_tail_eq_at_next hN B, if_pos hB, htail]
      · rw [inter_prefix_succ_eq hN A, if_pos hA,
          inter_prefix_succ_eq hN B, if_pos hB] at hcard
        have hhApre : nextPoint hN ∉ A ∩ «prefix» N ell :=
          fun hh ↦ nextPoint_not_mem_prefix hN (mem_inter.mp hh).2
        have hhBpre : nextPoint hN ∉ B ∩ «prefix» N ell :=
          fun hh ↦ nextPoint_not_mem_prefix hN (mem_inter.mp hh).2
        rw [card_insert_of_notMem hhApre,
          card_insert_of_notMem hhBpre] at hcard
        omega
    · exact (cross_next_membership_iff hN hinv hleft hdef hB hA
        htail.symm hcard.symm).symm
  · by_cases hB : nextPoint hN ∈ B
    · exact cross_next_membership_iff hN hinv hleft hdef hA hB
        htail hcard
    · apply hinv
      · rw [inter_tail_eq_at_next hN A, if_neg hA,
          inter_tail_eq_at_next hN B, if_neg hB, htail]
      · rw [inter_prefix_succ_eq hN A, if_neg hA,
          inter_prefix_succ_eq hN B, if_neg hB] at hcard
        exact hcard

private lemma prefixInvariant_upto
    {q : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    ∀ ell, ell ≤ 2 * q → PrefixInvariant F ell := by
  intro ell hell
  induction ell with
  | zero => exact prefixInvariant_zero F
  | succ ell ih =>
      have hell' : ell < 2 * q := by omega
      have hinv : PrefixInvariant F ell := ih (by omega)
      apply prefixInvariant_succ (hN := by omega) hinv hleft
      exact all_defects_empty hell' hinv hunif hinter hmax hleft

/-- A maximum-cardinality left-compressed uniform two-intersecting family of
`2q`-subsets is invariant under all permutations of the first `2q` points,
expressed in the direct prefix-layer form used by the remainder of the proof. -/
theorem prefixInvariant_two_mul {q : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F)
    (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    PrefixInvariant F (2 * q) := by
  exact prefixInvariant_upto hunif hinter hmax hleft (2 * q) le_rfl

end Erdos83
