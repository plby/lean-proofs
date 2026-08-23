/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 703.
https://www.erdosproblems.com/forum/thread/703

Informal authors:
- Péter Frankl
- Vojtěch Rödl

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos703.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import ErdosProblems.Erdos703.FranklRodl

/-!
# Erdős Problem 703: forbidden intersections

For `n r : ℕ`, `T n r` is the largest size of a family of subsets of
`{0, ..., n - 1}` such that no two members (including a member paired with
itself) have intersection of size `r`.

The main theorem `erdos_703` is the Frankl--Rödl exponential gap: if `r` stays
a positive linear distance from both `0` and `n / 2`, then `T n r` is bounded
by `(2 - δ) ^ n`, where `δ > 0` depends only on that distance.

The mathematical proof and the formalization map are in `tex/703.tex`.
-/

namespace Erdos703

open Nat Finset Real
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Two finite sets have an `r`-intersection when their intersection has size `r`. -/
def HasRIntersection (r : ℕ) (A B : Finset ℕ) : Prop :=
  #(A ∩ B) = r

/-- No two members of `𝓕`, including a member paired with itself, meet in `r` points. -/
def AvoidsRIntersection (r : ℕ) (𝓕 : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, #(A ∩ B) ≠ r

/-- The extremal quantity in Erdős Problem 703. -/
def T (n r : ℕ) : ℕ :=
  (((range n).powerset.powerset).filter (AvoidsRIntersection r)).sup card

lemma mem_admissibleFamilies_iff {n r : ℕ} {𝓕 : Finset (Finset ℕ)} :
    𝓕 ∈ ((range n).powerset.powerset).filter (AvoidsRIntersection r) ↔
      𝓕 ⊆ (range n).powerset ∧ AvoidsRIntersection r 𝓕 := by
  simp only [mem_filter, mem_powerset]

lemma card_le_T {n r : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hsub : 𝓕 ⊆ (range n).powerset) (havoid : AvoidsRIntersection r 𝓕) :
    #𝓕 ≤ T n r := by
  exact le_sup (s := ((range n).powerset.powerset).filter (AvoidsRIntersection r))
    (f := card) (mem_filter.mpr ⟨mem_powerset.mpr hsub, havoid⟩)

lemma T_le_of_forall {n r M : ℕ}
    (h : ∀ 𝓕 : Finset (Finset ℕ), 𝓕 ⊆ (range n).powerset →
      AvoidsRIntersection r 𝓕 → #𝓕 ≤ M) :
    T n r ≤ M := by
  apply Finset.sup_le
  intro 𝓕 h𝓕
  rw [mem_filter, mem_powerset] at h𝓕
  exact h 𝓕 h𝓕.1 h𝓕.2

lemma T_le_pow (n r : ℕ) : T n r ≤ 2 ^ n := by
  apply T_le_of_forall
  intro 𝓕 hsub _
  calc
    #𝓕 ≤ #(range n).powerset := card_le_card hsub
    _ = 2 ^ n := by simp

lemma avoidsRIntersection_self_card_ne {r : ℕ} {𝓕 : Finset (Finset ℕ)}
    (h : AvoidsRIntersection r 𝓕) {A : Finset ℕ} (hA : A ∈ 𝓕) : #A ≠ r := by
  simpa using h A hA A hA

lemma card_lt_pow_of_avoids {n r : ℕ} (hrn : r ≤ n)
    {𝓕 : Finset (Finset ℕ)} (hsub : 𝓕 ⊆ (range n).powerset)
    (havoid : AvoidsRIntersection r 𝓕) : #𝓕 < 2 ^ n := by
  have hproper : 𝓕 ⊂ (range n).powerset := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    have hlayer : ((range n).powersetCard r).Nonempty := by
      apply card_pos.mp
      rw [card_powersetCard, card_range]
      exact Nat.choose_pos hrn
    obtain ⟨A, hA⟩ := hlayer
    have hAdata := mem_powersetCard.mp hA
    have hA : A ∈ 𝓕 := by
      rw [heq, mem_powerset]
      exact hAdata.1
    exact avoidsRIntersection_self_card_ne havoid hA hAdata.2
  simpa using card_lt_card hproper

/-! ## The exact elementary case `r = 0` -/

lemma card_le_of_avoids_zero (n : ℕ) (hn : 1 ≤ n) (𝓕 : Finset (Finset ℕ))
    (hsub : 𝓕 ⊆ (range n).powerset) (havoid : AvoidsRIntersection 0 𝓕) :
    #𝓕 ≤ 2 ^ (n - 1) := by
  let c : Finset ℕ → Finset ℕ := fun A ↦ range n \ A
  have hc_mem : ∀ A ∈ 𝓕, c A ∈ (range n).powerset := by
    intro A hA
    exact mem_powerset.mpr sdiff_subset
  have hc_invol : ∀ A ∈ 𝓕, c (c A) = A := by
    intro A hA
    exact Finset.sdiff_sdiff_eq_self (mem_powerset.mp (hsub hA))
  have hc_notMem : ∀ A ∈ 𝓕, c A ∉ 𝓕 := by
    intro A hA hcA
    have hne := havoid A hA (c A) hcA
    exact hne (by simp [c])
  have hdisj : Disjoint 𝓕 (𝓕.image c) := by
    rw [disjoint_left]
    intro A hA hAc
    rw [mem_image] at hAc
    obtain ⟨B, hB, rfl⟩ := hAc
    exact hc_notMem B hB hA
  have hinj : Set.InjOn c 𝓕 := by
    intro A hA B hB hAB
    have := congrArg c hAB
    simpa [hc_invol A hA, hc_invol B hB] using this
  have hunion : 𝓕 ∪ 𝓕.image c ⊆ (range n).powerset := by
    refine union_subset hsub ?_
    intro A hA
    rw [mem_image] at hA
    obtain ⟨B, hB, rfl⟩ := hA
    exact hc_mem B hB
  have htwo : #𝓕 + #𝓕 ≤ 2 ^ n := by
    calc
      #𝓕 + #𝓕 = #(𝓕 ∪ 𝓕.image c) := by
        rw [card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
      _ ≤ #(range n).powerset := card_le_card hunion
      _ = 2 ^ n := by simp
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Nat.pow_succ']
  omega

/-- The star consisting of all subsets through `0`. -/
def starFamily (n : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter fun A ↦ 0 ∈ A

lemma starFamily_card (n : ℕ) (hn : 1 ≤ n) : #(starFamily n) = 2 ^ (n - 1) := by
  have h0 : 0 ∈ range n := mem_range.mpr hn
  have hcard : #((range n).erase 0) = n - 1 := by simp [h0]
  rw [← hcard, ← card_powerset]
  apply card_nbij' (fun A ↦ A.erase 0) (fun B ↦ insert 0 B)
  · intro A hA
    rw [mem_coe, starFamily, mem_filter, mem_powerset] at hA
    rw [mem_coe, mem_powerset]
    intro x hx
    rw [mem_erase] at hx ⊢
    exact ⟨hx.1, hA.1 hx.2⟩
  · intro B hB
    rw [mem_coe, mem_powerset] at hB
    rw [mem_coe, starFamily, mem_filter, mem_powerset]
    refine ⟨?_, mem_insert_self 0 B⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact h0
    · exact (mem_erase.mp (hB hx)).2
  · intro A hA
    rw [mem_coe, starFamily, mem_filter] at hA
    exact insert_erase hA.2
  · intro B hB
    rw [mem_coe, mem_powerset] at hB
    have h0B : 0 ∉ B := fun h ↦ (mem_erase.mp (hB h)).1 rfl
    exact erase_insert h0B

lemma starFamily_avoids_zero (n : ℕ) : AvoidsRIntersection 0 (starFamily n) := by
  intro A hA B hB
  rw [starFamily, mem_filter] at hA hB
  have h0 : 0 ∈ A ∩ B := mem_inter.mpr ⟨hA.2, hB.2⟩
  exact ne_of_gt (card_pos.mpr ⟨0, h0⟩)

/-- The trivial exact value `T(n,0) = 2^(n-1)`. -/
theorem T_zero (n : ℕ) (hn : 1 ≤ n) : T n 0 = 2 ^ (n - 1) := by
  apply le_antisymm
  · exact T_le_of_forall fun 𝓕 hsub havoid ↦ card_le_of_avoids_zero n hn 𝓕 hsub havoid
  · rw [← starFamily_card n hn]
    exact card_le_T (filter_subset _ _) (starFamily_avoids_zero n)

/-! ## The Frankl--Füredi constructions -/

/-- The fixed-`r` construction when `n + r` is odd. -/
def franklFurediOdd (n r : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter fun A ↦ (n + r) / 2 < #A ∨ #A < r

lemma franklFurediOdd_avoids (n r : ℕ) :
    AvoidsRIntersection r (franklFurediOdd n r) := by
  intro A hA B hB
  rw [franklFurediOdd, mem_filter, mem_powerset] at hA hB
  have hunion : #(A ∪ B) ≤ n := by
    calc
      #(A ∪ B) ≤ #(range n) := card_le_card (union_subset hA.1 hB.1)
      _ = n := card_range n
  have hie := card_union_add_card_inter A B
  have hiA : #(A ∩ B) ≤ #A := card_le_card inter_subset_left
  have hiB : #(A ∩ B) ≤ #B := card_le_card inter_subset_right
  rcases hA.2 with hAl | hAs <;> rcases hB.2 with hBl | hBs <;> omega

lemma franklFurediOdd_card_le_T (n r : ℕ) : #(franklFurediOdd n r) ≤ T n r :=
  card_le_T (filter_subset _ _) (franklFurediOdd_avoids n r)

/-- The fixed-`r` construction when `n + r` is even. -/
def franklFurediEven (n r : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter fun A ↦
    (n + r) / 2 ≤ #(A.filter (· ≠ 0)) ∨ #A < r

lemma franklFurediEven_avoids (n r : ℕ) (hn : 1 ≤ n) (heven : (n + r) % 2 = 0) :
    AvoidsRIntersection r (franklFurediEven n r) := by
  intro A hA B hB
  rw [franklFurediEven, mem_filter, mem_powerset] at hA hB
  let A₀ := A.filter (· ≠ 0)
  let B₀ := B.filter (· ≠ 0)
  have hA₀A : A₀ ⊆ A := filter_subset _ _
  have hB₀B : B₀ ⊆ B := filter_subset _ _
  have hint : #(A₀ ∩ B₀) ≤ #(A ∩ B) :=
    card_le_card (inter_subset_inter hA₀A hB₀B)
  have hground : #((range n).filter (· ≠ 0)) = n - 1 := by
    rw [filter_ne', card_erase_of_mem (mem_range.mpr hn), card_range]
  have hA₀sub : A₀ ⊆ (range n).filter (· ≠ 0) :=
    filter_subset_filter (· ≠ 0) hA.1
  have hB₀sub : B₀ ⊆ (range n).filter (· ≠ 0) :=
    filter_subset_filter (· ≠ 0) hB.1
  have hunion : #(A₀ ∪ B₀) ≤ n - 1 := by
    calc
      #(A₀ ∪ B₀) ≤ #((range n).filter (· ≠ 0)) :=
        card_le_card (union_subset hA₀sub hB₀sub)
      _ = n - 1 := hground
  have hie := card_union_add_card_inter A₀ B₀
  have hhalf : 2 * ((n + r) / 2) = n + r := by omega
  have hiA : #(A ∩ B) ≤ #A := card_le_card inter_subset_left
  have hiB : #(A ∩ B) ≤ #B := card_le_card inter_subset_right
  rcases hA.2 with hAl | hAs
  · rcases hB.2 with hBl | hBs
    · intro heq
      change (n + r) / 2 ≤ #A₀ at hAl
      change (n + r) / 2 ≤ #B₀ at hBl
      have hinter : r + 1 ≤ #(A₀ ∩ B₀) := by omega
      omega
    · omega
  · omega

lemma franklFurediEven_card_le_T (n r : ℕ) (hn : 1 ≤ n) (heven : (n + r) % 2 = 0) :
    #(franklFurediEven n r) ≤ T n r :=
  card_le_T (filter_subset _ _) (franklFurediEven_avoids n r hn heven)

/-! ## Passing between subsets of range n and subsets of Fin n -/

def toFinSet (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ (i : ℕ) ∈ A

@[simp] lemma mem_toFinSet {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFinSet n A ↔ (i : ℕ) ∈ A := by simp [toFinSet]

lemma toFinSet_inter (n : ℕ) (A B : Finset ℕ) :
    toFinSet n (A ∩ B) = toFinSet n A ∩ toFinSet n B := by
  ext i
  simp

lemma card_toFinSet {n : ℕ} {A : Finset ℕ} (hA : A ⊆ range n) :
    #(toFinSet n A) = #A := by
  refine Finset.card_bij (s := toFinSet n A) (t := A)
    (fun i _ ↦ (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simpa using hi
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro x hx
    have hxn : x < n := mem_range.mp (hA hx)
    let i : Fin n := ⟨x, hxn⟩
    exact ⟨i, by simp [i, hx], rfl⟩

lemma toFinSet_injOn {n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range n) (hB : B ⊆ range n)
    (h : toFinSet n A = toFinSet n B) : A = B := by
  ext x
  by_cases hxn : x < n
  · let i : Fin n := ⟨x, hxn⟩
    have hi := Finset.ext_iff.mp h i
    simpa [i] using hi
  · have hxA : x ∉ A := fun hx ↦ hxn (mem_range.mp (hA hx))
    have hxB : x ∉ B := fun hx ↦ hxn (mem_range.mp (hB hx))
    simp [hxA, hxB]

def toFinFamily (n : ℕ) (fam : Finset (Finset ℕ)) :
    Erdos703Iteration.Family n := fam.image (toFinSet n)

lemma card_toFinFamily {n : ℕ} {fam : Finset (Finset ℕ)}
    (hsub : fam ⊆ (range n).powerset) : #(toFinFamily n fam) = #fam := by
  unfold toFinFamily
  apply Finset.card_image_of_injOn
  intro A hA B hB hAB
  exact toFinSet_injOn (mem_powerset.mp (hsub hA)) (mem_powerset.mp (hsub hB)) hAB

lemma toFinFamily_crossAvoids {n r : ℕ} {fam : Finset (Finset ℕ)}
    (hsub : fam ⊆ (range n).powerset) (havoid : AvoidsRIntersection r fam) :
    Erdos703Iteration.CrossAvoids r r (toFinFamily n fam) (toFinFamily n fam) := by
  intro S hS T hT
  rw [toFinFamily, mem_image] at hS hT
  obtain ⟨A, hA, rfl⟩ := hS
  obtain ⟨B, hB, rfl⟩ := hT
  have hAB : A ∩ B ⊆ range n :=
    inter_subset_left.trans (mem_powerset.mp (hsub hA))
  have hne : #(toFinSet n A ∩ toFinSet n B) ≠ r := by
    intro heq
    apply havoid A hA B hB
    rw [← card_toFinSet hAB, toFinSet_inter]
    exact heq
  exact Nat.lt_or_gt_of_ne hne

/-! ## The Frankl--Rödl resolution -/

/-- Erdős Problem 703: forbidden intersections in the linear range have a
uniform exponential gap below the size of the Boolean cube. -/
theorem erdos_703 :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n r : ℕ), ε * n < r → r < (1 / 2 - ε) * n →
        (T n r : ℝ) < (2 - δ) ^ n := by
  intro ε hε
  by_cases hεhalf : ε < 1 / 2
  · obtain ⟨b, hb0, hb1, hfamily⟩ :=
      Erdos703FranklRodl.forbidden_family_density hε hεhalf
    refine ⟨2 - 2 * b, by linarith, ?_⟩
    intro n r hrlow hrhigh
    let admissible := ((range n).powerset.powerset).filter (AvoidsRIntersection r)
    have hadmissible : admissible.Nonempty := by
      refine ⟨∅, ?_⟩
      simp [admissible, AvoidsRIntersection]
    obtain ⟨fam, hfammem, hfammax⟩ :=
      Finset.exists_mem_eq_sup admissible hadmissible card
    have hfamdata : fam ⊆ (range n).powerset ∧ AvoidsRIntersection r fam := by
      simpa [admissible, mem_admissibleFamilies_iff] using hfammem
    have hden := hfamily hrlow hrhigh (toFinFamily n fam)
      (toFinFamily_crossAvoids hfamdata.1 hfamdata.2)
    have hcard := card_toFinFamily hfamdata.1
    change (#(toFinFamily n fam) : ℝ) / (2 : ℝ) ^ n < b ^ n at hden
    rw [hcard] at hden
    have hcardBound : (#fam : ℝ) < (2 * b) ^ n := by
      have hmul :=
        (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mp hden
      rw [mul_comm, ← mul_pow] at hmul
      exact hmul
    have hTeq : T n r = #fam := by
      simpa [T, admissible] using hfammax
    rw [hTeq]
    convert hcardBound using 1 <;> ring
  · refine ⟨1, by norm_num, ?_⟩
    intro n r hrlow hrhigh
    have hcoef : 1 / 2 - ε ≤ 0 := by linarith
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hright : (1 / 2 - ε) * n ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef hn0
    have hr0 : (0 : ℝ) ≤ r := by positivity
    exfalso
    linarith

#print axioms erdos_703

end

end Erdos703
