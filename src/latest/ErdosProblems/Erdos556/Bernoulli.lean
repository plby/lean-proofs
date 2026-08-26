/-
Copyright 2026 The Lean-Proofs Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Elementary finite Bernoulli sampling

This self-contained finite-sum development is adapted from the proved
Bernoulli counting lemmas in `Erdos76/Kahn.lean` and
`Erdos76/FiniteBernoulliLocality.lean`. No local lemma or hypergraph theorem
is imported or assumed.
-/

namespace Erdos556.Bernoulli

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The mass of an event in a finite weighted probability space. -/
def eventMass {Ω : Type*} [Fintype Ω] (mass : Ω → ℝ) (event : Ω → Prop) : ℝ :=
  ∑ x, if event x then mass x else 0

variable {E : Type*} [DecidableEq E]

/-- Product Bernoulli mass of a subset `S` of a finite ground set `U`. -/
def bernoulliMass (U : Finset E) (p : E → ℝ) (S : Finset E) : ℝ :=
  (∏ e ∈ S, p e) * ∏ e ∈ U \ S, (1 - p e)

/-- The explicit Bernoulli masses on the powerset sum to one.  This identity is
purely algebraic and does not require the parameters to lie in `[0,1]`. -/
lemma sum_bernoulliMass (U : Finset E) (p : E → ℝ) :
    ∑ S ∈ U.powerset, bernoulliMass U p S = 1 := by
  simp only [bernoulliMass]
  rw [← prod_add]
  simp

lemma bernoulliMass_nonneg {U S : Finset E} {p : E → ℝ}
    (hS : S ⊆ U) (hp₀ : ∀ e ∈ U, 0 ≤ p e) (hp₁ : ∀ e ∈ U, p e ≤ 1) :
    0 ≤ bernoulliMass U p S := by
  apply mul_nonneg
  · exact prod_nonneg fun e he ↦ hp₀ e (hS he)
  · exact prod_nonneg fun e he ↦ sub_nonneg.mpr (hp₁ e (mem_sdiff.mp he).1)

lemma bernoulliMass_insert {U T : Finset E} {p : E → ℝ} {e : E}
    (heU : e ∈ U) (hT : T ⊆ U.erase e) :
    bernoulliMass U p (insert e T) = p e * bernoulliMass (U.erase e) p T := by
  have heT : e ∉ T := by
    intro he
    exact (mem_erase.mp (hT he)).1 rfl
  have hdiff : U \ insert e T = U.erase e \ T := by
    ext x
    simp only [mem_sdiff, mem_insert, mem_erase]
    tauto
  simp only [bernoulliMass, prod_insert heT, hdiff]
  ring

/-- First Bernoulli moment: the total mass of subsets containing `e` is `p e`. -/
lemma sum_bernoulliMass_filter_mem {U : Finset E} {p : E → ℝ} {e : E} (heU : e ∈ U) :
    ∑ S ∈ U.powerset with e ∈ S, bernoulliMass U p S = p e := by
  have hsets : U.powerset.filter (fun S ↦ e ∈ S) =
      (U.erase e).powerset.image (insert e) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hSU, heS⟩
      refine ⟨S.erase e, ?_, ?_⟩
      · intro x hx
        obtain ⟨hxe, hxS⟩ := mem_erase.mp hx
        exact mem_erase.mpr ⟨hxe, hSU hxS⟩
      · simpa using insert_erase heS
    · rintro ⟨T, hT, rfl⟩
      exact ⟨insert_subset heU (hT.trans (erase_subset _ _)), mem_insert_self _ _⟩
  rw [hsets, sum_image]
  · calc
      ∑ T ∈ (U.erase e).powerset, bernoulliMass U p (insert e T) =
          ∑ T ∈ (U.erase e).powerset, p e * bernoulliMass (U.erase e) p T := by
        apply sum_congr rfl
        intro T hT
        exact bernoulliMass_insert heU (mem_powerset.mp hT)
      _ = p e * ∑ T ∈ (U.erase e).powerset, bernoulliMass (U.erase e) p T := by
        rw [mul_sum]
      _ = p e := by rw [sum_bernoulliMass, mul_one]
  · intro A hA B hB hAB
    have heA : e ∉ A := by
      intro heA
      exact (mem_erase.mp ((mem_powerset.mp hA) heA)).1 rfl
    have heB : e ∉ B := by
      intro heB
      exact (mem_erase.mp ((mem_powerset.mp hB) heB)).1 rfl
    simpa [heA, heB] using congrArg (fun S : Finset E ↦ S.erase e) hAB

/-- Second Bernoulli moment for two distinct coordinates. -/
lemma sum_bernoulliMass_filter_mem_mem {U : Finset E} {p : E → ℝ} {e f : E}
    (heU : e ∈ U) (hfU : f ∈ U) (hef : e ≠ f) :
    ∑ S ∈ U.powerset with e ∈ S ∧ f ∈ S, bernoulliMass U p S = p e * p f := by
  have hsets : U.powerset.filter (fun S ↦ e ∈ S ∧ f ∈ S) =
      ((U.erase e).powerset.filter fun T ↦ f ∈ T).image (insert e) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hSU, heS, hfS⟩
      refine ⟨S.erase e, ?_, ?_⟩
      · refine ⟨?_, mem_erase.mpr ⟨hef.symm, hfS⟩⟩
        intro x hx
        obtain ⟨hxe, hxS⟩ := mem_erase.mp hx
        exact mem_erase.mpr ⟨hxe, hSU hxS⟩
      · simpa using insert_erase heS
    · rintro ⟨T, ⟨hT, hfT⟩, rfl⟩
      exact ⟨insert_subset heU (hT.trans (erase_subset _ _)), mem_insert_self _ _,
        mem_insert_of_mem hfT⟩
  rw [hsets, sum_image]
  · calc
      ∑ T ∈ (U.erase e).powerset with f ∈ T, bernoulliMass U p (insert e T) =
          ∑ T ∈ (U.erase e).powerset with f ∈ T,
            p e * bernoulliMass (U.erase e) p T := by
        apply sum_congr rfl
        intro T hT
        exact bernoulliMass_insert heU (mem_powerset.mp (mem_filter.mp hT).1)
      _ = p e * ∑ T ∈ (U.erase e).powerset with f ∈ T,
          bernoulliMass (U.erase e) p T := by rw [mul_sum]
      _ = p e * p f := by
        rw [sum_bernoulliMass_filter_mem (mem_erase.mpr ⟨hef.symm, hfU⟩)]
  · intro A hA B hB hAB
    have heA : e ∉ A := by
      intro heA
      exact (mem_erase.mp ((mem_powerset.mp (mem_filter.mp hA).1) heA)).1 rfl
    have heB : e ∉ B := by
      intro heB
      exact (mem_erase.mp ((mem_powerset.mp (mem_filter.mp hB).1) heB)).1 rfl
    simpa [heA, heB] using congrArg (fun S : Finset E ↦ S.erase e) hAB

/-- Expected cardinality of the explicit Bernoulli sample. -/
lemma sum_bernoulliMass_mul_card (U : Finset E) (p : E → ℝ) :
    ∑ S ∈ U.powerset, bernoulliMass U p S * (S.card : ℝ) = ∑ e ∈ U, p e := by
  calc
    ∑ S ∈ U.powerset, bernoulliMass U p S * (S.card : ℝ) =
        ∑ S ∈ U.powerset, ∑ e ∈ U, if e ∈ S then bernoulliMass U p S else 0 := by
      apply sum_congr rfl
      intro S hS
      rw [← sum_filter]
      have hfilter : U.filter (fun e ↦ e ∈ S) = S := by
        ext e
        simp only [mem_filter]
        constructor
        · exact fun h ↦ h.2
        · intro heS
          exact ⟨(mem_powerset.mp hS) heS, heS⟩
      rw [hfilter]
      simp [mul_comm]
    _ = ∑ e ∈ U, ∑ S ∈ U.powerset,
          if e ∈ S then bernoulliMass U p S else 0 := by rw [sum_comm]
    _ = ∑ e ∈ U, p e := by
      apply sum_congr rfl
      intro e heU
      rw [← sum_filter, sum_bernoulliMass_filter_mem heU]

/-- Finite probabilistic method: some outcome is at least its expectation under
any nonnegative mass function of total mass one. -/
lemma exists_output_ge_average {Omega : Type*} [Fintype Omega]
    (mass output : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (hsum : ∑ omega, mass omega = 1) :
    ∃ omega, (∑ x, mass x * output x) ≤ output omega := by
  have hne : (univ : Finset Omega).Nonempty := by
    by_contra h
    have hempty : (univ : Finset Omega) = ∅ := not_nonempty_iff_eq_empty.mp h
    simpa [hempty] using hsum
  obtain ⟨omega, _, homega⟩ := exists_max_image univ output hne
  refine ⟨omega, ?_⟩
  calc
    ∑ x, mass x * output x ≤ ∑ x, mass x * output omega := by
      exact sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left (homega x hx) (hmass x)
    _ = (∑ x, mass x) * output omega := by rw [sum_mul]
    _ = output omega := by rw [hsum, one_mul]


variable [Fintype E]

/-- Two outcomes agree on `R` when they select the same coordinates of `R`. -/
def AgreesOn (R S T : Finset E) : Prop := S ∩ R = T ∩ R

/-- An event depends only on the coordinates in `R`. -/
def EventDependsOn (R : Finset E) (event : Finset E → Prop) : Prop :=
  ∀ S T, AgreesOn R S T → (event S ↔ event T)

lemma agreesOn_refl (R S : Finset E) : AgreesOn R S S := rfl

lemma agreesOn_symm {R S T : Finset E} (h : AgreesOn R S T) : AgreesOn R T S := h.symm

lemma agreesOn_trans {R S T V : Finset E}
    (hST : AgreesOn R S T) (hTV : AgreesOn R T V) : AgreesOn R S V :=
  hST.trans hTV

lemma agreesOn_mono {R R' S T : Finset E} (hRR' : R ⊆ R')
    (h : AgreesOn R' S T) : AgreesOn R S T := by
  unfold AgreesOn at h ⊢
  ext e
  have hmem : e ∈ S ∩ R' ↔ e ∈ T ∩ R' := by rw [h]
  simp only [mem_inter] at hmem ⊢
  constructor
  · rintro ⟨heS, heR⟩
    exact ⟨(hmem.mp ⟨heS, hRR' heR⟩).1, heR⟩
  · rintro ⟨heT, heR⟩
    exact ⟨(hmem.mpr ⟨heT, hRR' heR⟩).1, heR⟩

lemma eventDependsOn_mono {R R' : Finset E} {event : Finset E → Prop}
    (hRR' : R ⊆ R') (h : EventDependsOn R event) : EventDependsOn R' event := by
  intro S T hST
  exact h S T (agreesOn_mono hRR' hST)

lemma eventDependsOn_true (R : Finset E) : EventDependsOn R (fun _ ↦ True) := by
  intro S T hST
  simp

lemma eventDependsOn_and {R T : Finset E} {A B : Finset E → Prop}
    (hA : EventDependsOn R A) (hB : EventDependsOn T B) :
    EventDependsOn (R ∪ T) (fun S ↦ A S ∧ B S) := by
  intro S V hSV
  have hR : AgreesOn R S V := agreesOn_mono subset_union_left hSV
  have hT : AgreesOn T S V := agreesOn_mono subset_union_right hSV
  exact and_congr (hA S V hR) (hB S V hT)

/-- The finite type of subsets of `U`. -/
abbrev Subsets (U : Finset E) := {S : Finset E // S ⊆ U}

/-- Identify subsets of `U` with the attached elements of `U.powerset`. -/
def subsetsEquivPowersetAttach (U : Finset E) :
    Subsets U ≃ ↥U.powerset :=
  Equiv.subtypeEquivRight (by intro S; simp)

/-- A subset of the full coordinate set is just an arbitrary finite subset. -/
def subsetsUnivEquiv : Subsets (Finset.univ : Finset E) ≃ Finset E where
  toFun S := S.1
  invFun S := ⟨S, subset_univ S⟩
  left_inv S := Subtype.ext rfl
  right_inv S := rfl

/-- Splitting a subset of a disjoint union into its two coordinate blocks. -/
def disjointSubsetsEquiv {U V : Finset E} (hUV : Disjoint U V) :
    Subsets (U ∪ V) ≃ Subsets U × Subsets V where
  toFun S :=
    (⟨S.1 ∩ U, inter_subset_right⟩, ⟨S.1 ∩ V, inter_subset_right⟩)
  invFun P := ⟨P.1.1 ∪ P.2.1, union_subset_union P.1.2 P.2.2⟩
  left_inv S := by
    apply Subtype.ext
    ext e
    simp only [mem_union, mem_inter]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro heS
      have hsplit : e ∈ U ∨ e ∈ V := by
        simpa only [mem_union] using S.2 heS
      rcases hsplit with heU | heV
      · exact Or.inl ⟨heS, heU⟩
      · exact Or.inr ⟨heS, heV⟩
  right_inv P := by
    rcases P with ⟨A, B⟩
    apply Prod.ext
    · apply Subtype.ext
      ext e
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨heA | heB, heU⟩
        · exact heA
        · exact False.elim ((Finset.disjoint_left.mp hUV) heU (B.2 heB))
      · intro heA
        exact ⟨Or.inl heA, A.2 heA⟩
    · apply Subtype.ext
      ext e
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨heA | heB, heV⟩
        · exact False.elim ((Finset.disjoint_left.mp hUV) (A.2 heA) heV)
        · exact heB
      · intro heB
        exact ⟨Or.inr heB, B.2 heB⟩

/-- Bernoulli mass of an event restricted to coordinates in `U`. -/
def restrictedEventMass (U : Finset E) (p : E → ℝ) (event : Finset E → Prop) : ℝ :=
  ∑ S : Subsets U, if event S.1 then bernoulliMass U p S.1 else 0

lemma sum_restricted_bernoulliMass (U : Finset E) (p : E → ℝ) :
    ∑ S : Subsets U, bernoulliMass U p S.1 = 1 := by
  calc
    (∑ S : Subsets U, bernoulliMass U p S.1) =
        ∑ S : ↥U.powerset, bernoulliMass U p S.1 := by
      apply Fintype.sum_equiv (subsetsEquivPowersetAttach U)
      intro S
      rfl
    _ = ∑ S ∈ U.powerset, bernoulliMass U p S := by
      simpa using
        (Finset.sum_attach U.powerset
          (fun S : Finset E ↦ bernoulliMass U p S))
    _ = 1 := sum_bernoulliMass U p

lemma restrictedEventMass_true (U : Finset E) (p : E → ℝ) :
    restrictedEventMass U p (fun _ ↦ True) = 1 := by
  unfold restrictedEventMass
  simpa using sum_restricted_bernoulliMass U p

/-- The `eventMass` sample space of all finite subsets agrees with the
restricted construction on the full coordinate set. -/
lemma eventMass_eq_restrictedEventMass_univ (p : E → ℝ)
    (event : Finset E → Prop) :
    eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S) event =
      restrictedEventMass Finset.univ p event := by
  unfold eventMass restrictedEventMass
  symm
  apply Fintype.sum_equiv subsetsUnivEquiv
  intro S
  by_cases h : event S.1 <;> simp [h, subsetsUnivEquiv]

lemma bernoulliMass_union_of_disjoint {U V A B : Finset E} {p : E → ℝ}
    (hUV : Disjoint U V) (hA : A ⊆ U) (hB : B ⊆ V) :
    bernoulliMass (U ∪ V) p (A ∪ B) =
      bernoulliMass U p A * bernoulliMass V p B := by
  have hAB : Disjoint A B := hUV.mono hA hB
  have hdiff : (U ∪ V) \ (A ∪ B) = (U \ A) ∪ (V \ B) := by
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨heU | heV, hnot⟩
      · exact Or.inl ⟨heU, fun heA ↦ hnot (Or.inl heA)⟩
      · exact Or.inr ⟨heV, fun heB ↦ hnot (Or.inr heB)⟩
    · rintro (⟨heU, heA⟩ | ⟨heV, heB⟩)
      · refine ⟨Or.inl heU, ?_⟩
        rintro (hAe | hBe)
        · exact heA hAe
        · exact (Finset.disjoint_left.mp hUV) heU (hB hBe)
      · refine ⟨Or.inr heV, ?_⟩
        rintro (hAe | hBe)
        · exact (Finset.disjoint_left.mp hUV) (hA hAe) heV
        · exact heB hBe
  have hdiffDisj : Disjoint (U \ A) (V \ B) :=
    hUV.mono sdiff_subset sdiff_subset
  simp only [bernoulliMass, prod_union hAB, hdiff, prod_union hdiffDisj]
  ring

/-- Exact product factorisation for two local events on disjoint restricted
coordinate spaces. -/
lemma restrictedEventMass_and_of_disjoint {U V : Finset E} {p : E → ℝ}
    {A B : Finset E → Prop} (hUV : Disjoint U V)
    (hA : EventDependsOn U A) (hB : EventDependsOn V B) :
    restrictedEventMass (U ∪ V) p (fun S ↦ A S ∧ B S) =
      restrictedEventMass U p A * restrictedEventMass V p B := by
  let split : Subsets (U ∪ V) ≃ Subsets U × Subsets V :=
    disjointSubsetsEquiv hUV
  let summand : Subsets (U ∪ V) → ℝ := fun S ↦
    if A S.1 ∧ B S.1 then bernoulliMass (U ∪ V) p S.1 else 0
  calc
    restrictedEventMass (U ∪ V) p (fun S ↦ A S ∧ B S) =
        ∑ S : Subsets (U ∪ V), summand S := by
      unfold restrictedEventMass
      apply sum_congr rfl
      intro S _
      by_cases h : A S.1 ∧ B S.1 <;> simp [summand, h]
    _ = ∑ P : Subsets U × Subsets V, summand (split.symm P) := by
      apply Fintype.sum_equiv split
      intro S
      simp only [Equiv.symm_apply_apply]
    _ = ∑ X : Subsets U, ∑ Y : Subsets V, summand (split.symm (X, Y)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ X : Subsets U, ∑ Y : Subsets V,
        (if A X.1 then bernoulliMass U p X.1 else 0) *
          (if B Y.1 then bernoulliMass V p Y.1 else 0) := by
      apply sum_congr rfl
      intro X _
      apply sum_congr rfl
      intro Y _
      have hsplit : (split.symm (X, Y)).1 = X.1 ∪ Y.1 := rfl
      have hAgreeA : AgreesOn U (X.1 ∪ Y.1) X.1 := by
        unfold AgreesOn
        ext e
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨heX | heY, heU⟩
          · exact ⟨heX, X.2 heX⟩
          · exact False.elim ((Finset.disjoint_left.mp hUV) heU (Y.2 heY))
        · rintro ⟨heX, heU⟩
          exact ⟨Or.inl heX, heU⟩
      have hAgreeB : AgreesOn V (X.1 ∪ Y.1) Y.1 := by
        unfold AgreesOn
        ext e
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨heX | heY, heV⟩
          · exact False.elim ((Finset.disjoint_left.mp hUV) (X.2 heX) heV)
          · exact ⟨heY, Y.2 heY⟩
        · rintro ⟨heY, heV⟩
          exact ⟨Or.inr heY, heV⟩
      have hAE : A (X.1 ∪ Y.1) ↔ A X.1 := hA _ _ hAgreeA
      have hBE : B (X.1 ∪ Y.1) ↔ B Y.1 := hB _ _ hAgreeB
      rw [show summand (split.symm (X, Y)) =
          if A (X.1 ∪ Y.1) ∧ B (X.1 ∪ Y.1) then
            bernoulliMass (U ∪ V) p (X.1 ∪ Y.1) else 0 by
              change (if A (split.symm (X, Y)).1 ∧ B (split.symm (X, Y)).1 then
                bernoulliMass (U ∪ V) p (split.symm (X, Y)).1 else 0) = _
              rw [hsplit]]
      rw [bernoulliMass_union_of_disjoint hUV X.2 Y.2]
      by_cases hAX : A X.1 <;> by_cases hBY : B Y.1 <;>
        simp_all
    _ = (∑ X : Subsets U, if A X.1 then bernoulliMass U p X.1 else 0) *
        ∑ Y : Subsets V, if B Y.1 then bernoulliMass V p Y.1 else 0 := by
      rw [sum_mul]
      apply sum_congr rfl
      intro X _
      rw [mul_sum]
    _ = restrictedEventMass U p A * restrictedEventMass V p B := by
      rfl

/-- Marginalising all coordinates outside a local event's support does not
change its Bernoulli mass. -/
lemma eventMass_eq_restrictedEventMass {R : Finset E} {p : E → ℝ}
    {event : Finset E → Prop} (hlocal : EventDependsOn R event) :
    eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S) event =
      restrictedEventMass R p event := by
  calc
    eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S) event =
        restrictedEventMass Finset.univ p event :=
      eventMass_eq_restrictedEventMass_univ p event
    _ = restrictedEventMass R p event := by
      have hfactor := restrictedEventMass_and_of_disjoint
        (p := p) (U := R) (V := Finset.univ \ R)
        (A := event) (B := fun _ ↦ True) Finset.disjoint_sdiff hlocal
        (eventDependsOn_true (Finset.univ \ R))
      have hcover : R ∪ (Finset.univ \ R) = (Finset.univ : Finset E) :=
        union_sdiff_of_subset (subset_univ R)
      rw [hcover] at hfactor
      simpa [restrictedEventMass_true] using hfactor

/-- Events supported on disjoint coordinate sets have exactly factorising
mass in the full finite Bernoulli product space. -/
theorem eventMass_and_of_disjoint {R T : Finset E} {p : E → ℝ}
    {A B : Finset E → Prop} (hRT : Disjoint R T)
    (hA : EventDependsOn R A) (hB : EventDependsOn T B) :
    eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S)
        (fun S ↦ A S ∧ B S) =
      eventMass
          (fun S : Finset E ↦ bernoulliMass Finset.univ p S) A *
        eventMass
          (fun S : Finset E ↦ bernoulliMass Finset.univ p S) B := by
  calc
    eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S)
        (fun S ↦ A S ∧ B S) =
        restrictedEventMass (R ∪ T) p (fun S ↦ A S ∧ B S) :=
      eventMass_eq_restrictedEventMass (eventDependsOn_and hA hB)
    _ = restrictedEventMass R p A * restrictedEventMass T p B :=
      restrictedEventMass_and_of_disjoint hRT hA hB
    _ = eventMass
          (fun S : Finset E ↦ bernoulliMass Finset.univ p S) A *
        eventMass
          (fun S : Finset E ↦ bernoulliMass Finset.univ p S) B := by
      rw [eventMass_eq_restrictedEventMass hA,
        eventMass_eq_restrictedEventMass hB]




#print axioms eventMass_and_of_disjoint

end

end Erdos556.Bernoulli

