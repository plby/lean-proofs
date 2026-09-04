/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos49.ExceptionalBasic
import ErdosProblems.Erdos841.BoundedUnits
import ErdosProblems.Erdos841.ClassNumberBound
import ErdosProblems.Erdos841.LinearForms
import ErdosProblems.Erdos841.Threshold

/-!
# Erdős Problem 841: core development

For a positive integer `n`, let `t n` be the least endpoint such that some
subset of the offsets `1, ..., t n`, when added to `n` and multiplied
together with `n`, has square product.  The definition below is uniform:
it also gives `t n = 0` exactly when `n` is square.

This file proves the exact large-prime estimate of Granville and Selfridge,
the finite square-subset and smooth-interval lemmas of
Bui--Pratt--Zaharescu, and their moving-threshold distributional comparison.
The detailed mathematical reconstruction is in `tex/841.tex`.
-/

open scoped BigOperators symmDiff

namespace Erdos841

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `Admissible n T` means that the interval of offsets `1, ..., T`
contains a subset whose translated product, multiplied by `n`, is a square. -/
def Admissible (n T : ℕ) : Prop :=
  ∃ J : Finset ℕ, J ⊆ Finset.Icc 1 T ∧
    IsSquare (n * ∏ j ∈ J, (n + j))

lemma admissible_mono {n T U : ℕ} (hTU : T ≤ U) (hT : Admissible n T) :
    Admissible n U := by
  obtain ⟨J, hJ, hsq⟩ := hT
  exact ⟨J, hJ.trans (Finset.Icc_subset_Icc_right hTU), hsq⟩

lemma admissible_of_isSquare {n : ℕ} (hn : IsSquare n) : Admissible n 0 := by
  refine ⟨∅, by simp, ?_⟩
  simpa using hn

lemma exists_admissible (n : ℕ) : ∃ T, Admissible n T := by
  by_cases hn : IsSquare n
  · exact ⟨0, admissible_of_isSquare hn⟩
  · have hn0 : n ≠ 0 := by
      intro h
      subst n
      exact hn IsSquare.zero
    have hn1 : n ≠ 1 := by
      intro h
      subst n
      exact hn IsSquare.one
    have hn2 : 2 ≤ n := by omega
    have hpow2 : 1 < n ^ 2 := one_lt_pow₀ (by omega) (by decide)
    have hlt : n < n ^ 3 := by
      calc
        n = n * 1 := by simp
        _ < n * n ^ 2 := Nat.mul_lt_mul_of_pos_left hpow2 (by omega)
        _ = n ^ 3 := by ring
    have hle : n ≤ n ^ 3 := hlt.le
    refine ⟨n ^ 3 - n, {n ^ 3 - n}, ?_, ?_⟩
    · simp only [Finset.singleton_subset_iff, Finset.mem_Icc]
      exact ⟨Nat.sub_pos_of_lt hlt, le_rfl⟩
    · simp only [Finset.prod_singleton]
      refine ⟨n ^ 2, ?_⟩
      rw [Nat.add_sub_of_le hle]
      ring

/-- The exact sequence from Problem 841. -/
noncomputable def t (n : ℕ) : ℕ := Nat.find (exists_admissible n)

lemma t_spec (n : ℕ) : Admissible n (t n) := Nat.find_spec (exists_admissible n)

lemma not_admissible_of_lt_t {n T : ℕ} (hT : T < t n) : ¬Admissible n T := by
  exact Nat.find_min (exists_admissible n) hT

lemma t_le_of_admissible {n T : ℕ} (hT : Admissible n T) : t n ≤ T := by
  exact Nat.find_min' (exists_admissible n) hT

theorem t_eq_zero_iff (n : ℕ) : t n = 0 ↔ IsSquare n := by
  constructor
  · intro ht
    obtain ⟨J, hJ, hsq⟩ := t_spec n
    rw [ht] at hJ
    have hJe : J = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have := hJ hj
      simp at this
    subst J
    simpa using hsq
  · intro hn
    exact Nat.eq_zero_of_le_zero (t_le_of_admissible (admissible_of_isSquare hn))

lemma t_pos_of_not_isSquare {n : ℕ} (hn : ¬IsSquare n) : 0 < t n := by
  exact Nat.pos_of_ne_zero fun ht ↦ hn ((t_eq_zero_iff n).mp ht)

/-- A witness at the least positive endpoint necessarily uses that endpoint. -/
lemma exists_minimal_witness_with_endpoint {n : ℕ} (hn : ¬IsSquare n) :
    ∃ J : Finset ℕ, J ⊆ Finset.Icc 1 (t n) ∧ t n ∈ J ∧
      IsSquare (n * ∏ j ∈ J, (n + j)) := by
  obtain ⟨J, hJ, hsq⟩ := t_spec n
  refine ⟨J, hJ, ?_, hsq⟩
  by_contra hend
  have htpos : 0 < t n := t_pos_of_not_isSquare hn
  have hJpred : J ⊆ Finset.Icc 1 (t n - 1) := by
    intro j hj
    have hjI := Finset.mem_Icc.mp (hJ hj)
    have hjne : j ≠ t n := by
      intro h
      exact hend (h ▸ hj)
    exact Finset.mem_Icc.mpr ⟨hjI.1, by omega⟩
  exact not_admissible_of_lt_t (Nat.pred_lt htpos.ne') ⟨J, hJpred, hsq⟩

/-! ## The exact finite square-subset count -/

/-- The offset definition of admissibility is equivalent to a square-product
subset of the value interval containing its left endpoint. -/
lemma admissible_iff_exists_values (n T : ℕ) :
    Admissible n T ↔
      ∃ S : Finset ℕ, n ∈ S ∧ S ⊆ Finset.Icc n (n + T) ∧
        IsSquare (∏ x ∈ S, x) := by
  constructor
  · rintro ⟨J, hJ, hsq⟩
    let f : ℕ → ℕ := fun j ↦ n + j
    let S : Finset ℕ := insert n (J.image f)
    have hnimage : n ∉ J.image f := by
      intro hn
      obtain ⟨j, hj, hjEq⟩ := Finset.mem_image.mp hn
      have hjpos := (Finset.mem_Icc.mp (hJ hj)).1
      dsimp [f] at hjEq
      omega
    refine ⟨S, Finset.mem_insert_self _ _, ?_, ?_⟩
    · intro x hx
      simp only [S, Finset.mem_insert, Finset.mem_image] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩
      · simp
      · have hjI := Finset.mem_Icc.mp (hJ hj)
        simpa only [f] using
          (Finset.mem_Icc.mpr ⟨Nat.le_add_right n j, Nat.add_le_add_left hjI.2 n⟩)
    · have hf : Function.Injective f := by
        intro a b hab
        dsimp [f] at hab
        omega
      rw [show ∏ x ∈ S, x = n * ∏ j ∈ J, (n + j) by
        simp only [S, Finset.prod_insert hnimage, Finset.prod_image hf.injOn, f]]
      exact hsq
  · rintro ⟨S, hnS, hS, hsq⟩
    let R := S.erase n
    let g : ℕ → ℕ := fun x ↦ x - n
    let J := R.image g
    have hRle : ∀ x ∈ R, n ≤ x := by
      intro x hx
      exact (Finset.mem_Icc.mp (hS (Finset.mem_of_mem_erase hx))).1
    have hg : Set.InjOn g R := by
      intro x hx y hy hxy
      have hxle := hRle x hx
      have hyle := hRle y hy
      dsimp [g] at hxy
      omega
    refine ⟨J, ?_, ?_⟩
    · intro j hj
      obtain ⟨x, hxR, rfl⟩ := Finset.mem_image.mp hj
      have hxS := Finset.mem_of_mem_erase hxR
      have hxne : x ≠ n := (Finset.mem_erase.mp hxR).1
      have hxI := Finset.mem_Icc.mp (hS hxS)
      change x - n ∈ Finset.Icc 1 T
      exact Finset.mem_Icc.mpr
        ⟨Nat.sub_pos_of_lt (lt_of_le_of_ne hxI.1 (Ne.symm hxne)),
          Nat.sub_le_iff_le_add.mpr (by simpa [Nat.add_comm] using hxI.2)⟩
    · have hprodJ : ∏ j ∈ J, (n + j) = ∏ x ∈ R, x := by
        rw [show ∏ j ∈ J, (n + j) = ∏ x ∈ R, (n + g x) by
          exact Finset.prod_image hg]
        apply Finset.prod_congr rfl
        intro x hx
        have hxle := hRle x hx
        dsimp [g]
        omega
      rw [hprodJ]
      have hprodS : ∏ x ∈ S, x = n * ∏ x ∈ S.erase n, x := by
        simpa using (Finset.mul_prod_erase S id hnS).symm
      rw [hprodS] at hsq
      simpa [R] using hsq

/-- The product over a symmetric difference, multiplied by the square of the
intersection product, is the product of the two original products. -/
private lemma prod_symmDiff_mul_inter_sq {α M : Type*} [DecidableEq α]
    [CommMonoid M] (s u : Finset α) (f : α → M) :
    (∏ x ∈ s ∆ u, f x) * (∏ x ∈ s ∩ u, f x) ^ 2 =
      (∏ x ∈ s, f x) * (∏ x ∈ u, f x) := by
  rw [Finset.symmDiff_def, Finset.prod_union]
  · have hs := Finset.prod_union (f := f) (Finset.disjoint_sdiff_inter s u)
    rw [Finset.sdiff_union_inter] at hs
    have hu := Finset.prod_union (f := f) (Finset.disjoint_sdiff_inter u s)
    rw [Finset.sdiff_union_inter] at hu
    rw [Finset.inter_comm] at hu
    rw [hs, hu]
    simp only [pow_two]
    ac_rfl
  · exact Finset.disjoint_left.mpr (by aesop)

/-- For nonzero natural factors, square-product subsets are closed under
symmetric difference. -/
private lemma isSquare_prod_symmDiff {s u : Finset ℕ}
    (hs0 : ∀ x ∈ s, x ≠ 0) (_hu0 : ∀ x ∈ u, x ≠ 0)
    (hs : IsSquare (∏ x ∈ s, x)) (hu : IsSquare (∏ x ∈ u, x)) :
    IsSquare (∏ x ∈ s ∆ u, x) := by
  rw [← Rat.isSquare_natCast_iff]
  have hsQ : IsSquare (((∏ x ∈ s, x : ℕ) : ℚ)) :=
    Rat.isSquare_natCast_iff.mpr hs
  have huQ : IsSquare (((∏ x ∈ u, x : ℕ) : ℚ)) :=
    Rat.isSquare_natCast_iff.mpr hu
  have hinter0 : (∏ x ∈ s ∩ u, x) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by aesop)
  have hsqQ := (hsQ.mul huQ).div
    (IsSquare.sq (((∏ x ∈ s ∩ u, x : ℕ) : ℚ)))
  have heq : (((∏ x ∈ s ∆ u, x : ℕ) : ℚ)) =
      (((∏ x ∈ s, x : ℕ) : ℚ) * ((∏ x ∈ u, x : ℕ) : ℚ)) /
        (((∏ x ∈ s ∩ u, x : ℕ) : ℚ)) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 (by exact_mod_cast hinter0))).mpr
    exact_mod_cast prod_symmDiff_mul_inter_sq s u id
  rw [heq]
  exact hsqQ

/-- All subsets of `I` whose element-product is a square. -/
def squareProductSubsets (I : Finset ℕ) : Finset (Finset ℕ) :=
  I.powerset.filter fun S ↦ IsSquare (∏ x ∈ S, x)

@[simp] lemma mem_squareProductSubsets {I S : Finset ℕ} :
    S ∈ squareProductSubsets I ↔ S ⊆ I ∧ IsSquare (∏ x ∈ S, x) := by
  simp [squareProductSubsets]

private lemma squareProductSubsets_symmDiff {I S U : Finset ℕ}
    (hI0 : ∀ x ∈ I, x ≠ 0)
    (hS : S ∈ squareProductSubsets I) (hU : U ∈ squareProductSubsets I) :
    S ∆ U ∈ squareProductSubsets I := by
  rw [mem_squareProductSubsets] at hS hU ⊢
  refine ⟨Finset.symmDiff_subset_union.trans (Finset.union_subset hS.1 hU.1), ?_⟩
  exact isSquare_prod_symmDiff
    (fun x hx ↦ hI0 x (hS.1 hx)) (fun x hx ↦ hI0 x (hU.1 hx)) hS.2 hU.2

private lemma card_squareProductSubsets_toggle {I W : Finset ℕ} {a : ℕ}
    (hI0 : ∀ x ∈ I, x ≠ 0) (hW : W ∈ squareProductSubsets I) (ha : a ∈ W) :
    ((squareProductSubsets I).filter fun S ↦ a ∉ S).card =
      ((squareProductSubsets I).filter fun S ↦ a ∈ S).card := by
  let K₀ := (squareProductSubsets I).filter fun S ↦ a ∉ S
  let K₁ := (squareProductSubsets I).filter fun S ↦ a ∈ S
  refine Finset.card_bij'
    (s := K₀) (t := K₁)
    (fun S _ ↦ S ∆ W) (fun S _ ↦ S ∆ W) ?_ ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨squareProductSubsets_symmDiff hI0 hS.1 hW, ?_⟩
    rw [Finset.mem_symmDiff]
    exact Or.inr ⟨ha, hS.2⟩
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨squareProductSubsets_symmDiff hI0 hS.1 hW, ?_⟩
    simp [Finset.mem_symmDiff, hS.2, ha]
  · intro S _
    simpa using (symmDiff_symmDiff_cancel_right W S)
  · intro S _
    simpa using (symmDiff_symmDiff_cancel_right W S)

/-- Starting points in `(X,E]` whose least witness closes by `E`. -/
def closedStarts (X E : ℕ) : Finset ℕ :=
  (Finset.Ioc X E).filter fun n ↦ n + t n ≤ E

private lemma exists_squareProductSubset_mem_succ_iff {X E : ℕ} (hXE : X < E) :
    (∃ W ∈ squareProductSubsets (Finset.Ioc X E), X + 1 ∈ W) ↔
      X + 1 + t (X + 1) ≤ E := by
  have haE : X + 1 ≤ E := hXE
  constructor
  · rintro ⟨W, hW, haW⟩
    rw [mem_squareProductSubsets] at hW
    have hsub : W ⊆ Finset.Icc (X + 1) E := by
      intro x hx
      have hxI := Finset.mem_Ioc.mp (hW.1 hx)
      exact Finset.mem_Icc.mpr ⟨by omega, hxI.2⟩
    have hadm : Admissible (X + 1) (E - (X + 1)) :=
      (admissible_iff_exists_values (X + 1) (E - (X + 1))).mpr
        ⟨W, haW, by simpa [Nat.add_sub_of_le haE] using hsub, hW.2⟩
    have ht := t_le_of_admissible hadm
    omega
  · intro ht
    have htle : t (X + 1) ≤ E - (X + 1) := by omega
    have hadm := admissible_mono htle (t_spec (X + 1))
    obtain ⟨W, haW, hWsub, hWsq⟩ :=
      (admissible_iff_exists_values (X + 1) (E - (X + 1))).mp hadm
    refine ⟨W, ?_, haW⟩
    rw [mem_squareProductSubsets]
    refine ⟨?_, hWsq⟩
    intro x hx
    have hxI := Finset.mem_Icc.mp (hWsub hx)
    rw [Nat.add_sub_of_le haE] at hxI
    exact Finset.mem_Ioc.mpr ⟨by omega, hxI.2⟩

private lemma filter_squareProductSubsets_not_succ {X E : ℕ} :
    (squareProductSubsets (Finset.Ioc X E)).filter (fun S ↦ X + 1 ∉ S) =
      squareProductSubsets (Finset.Ioc (X + 1) E) := by
  ext S
  simp only [Finset.mem_filter, mem_squareProductSubsets]
  constructor
  · rintro ⟨⟨hS, hsq⟩, haS⟩
    refine ⟨?_, hsq⟩
    intro x hx
    have hxI := Finset.mem_Ioc.mp (hS hx)
    have hxne : x ≠ X + 1 := by
      intro h
      exact haS (h ▸ hx)
    exact Finset.mem_Ioc.mpr ⟨by omega, hxI.2⟩
  · rintro ⟨hS, hsq⟩
    refine ⟨⟨?_, hsq⟩, ?_⟩
    · intro x hx
      have hxI := Finset.mem_Ioc.mp (hS hx)
      exact Finset.mem_Ioc.mpr ⟨by omega, hxI.2⟩
    · intro ha
      exact (Finset.mem_Ioc.mp (hS ha)).1.false

private lemma card_squareProductSubsets_step {X E : ℕ} (hXE : X < E) :
    (squareProductSubsets (Finset.Ioc X E)).card =
      (if X + 1 + t (X + 1) ≤ E then
        2 * (squareProductSubsets (Finset.Ioc (X + 1) E)).card
      else (squareProductSubsets (Finset.Ioc (X + 1) E)).card) := by
  let K := squareProductSubsets (Finset.Ioc X E)
  let K₀ := K.filter fun S ↦ X + 1 ∉ S
  let K₁ := K.filter fun S ↦ X + 1 ∈ S
  have hsplit : K₁.card + K₀.card = K.card := by
    exact Finset.card_filter_add_card_filter_not (s := K) (fun S ↦ X + 1 ∈ S)
  have hK₀ : K₀ = squareProductSubsets (Finset.Ioc (X + 1) E) :=
    filter_squareProductSubsets_not_succ
  split_ifs with helig
  · obtain ⟨W, hWK, haW⟩ := (exists_squareProductSubset_mem_succ_iff hXE).mpr helig
    have hpos : ∀ x ∈ Finset.Ioc X E, x ≠ 0 := by
      intro x hx
      have hx' := (Finset.mem_Ioc.mp hx).1
      omega
    have htoggle := card_squareProductSubsets_toggle hpos hWK haW
    change K₀.card = K₁.card at htoggle
    change K.card = 2 * (squareProductSubsets (Finset.Ioc (X + 1) E)).card
    calc
      K.card = K₁.card + K₀.card := hsplit.symm
      _ = K₀.card + K₀.card := by rw [← htoggle]
      _ = 2 * (squareProductSubsets (Finset.Ioc (X + 1) E)).card := by
        rw [hK₀]
        omega
  · have hK₁ : K₁ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro W hW
      apply helig
      rw [Finset.mem_filter] at hW
      exact (exists_squareProductSubset_mem_succ_iff hXE).mp ⟨W, hW.1, hW.2⟩
    change K.card = (squareProductSubsets (Finset.Ioc (X + 1) E)).card
    calc
      K.card = K₁.card + K₀.card := hsplit.symm
      _ = K₀.card := by rw [hK₁]; simp
      _ = (squareProductSubsets (Finset.Ioc (X + 1) E)).card := congrArg Finset.card hK₀

private lemma closedStarts_step {X E : ℕ} (hXE : X < E) :
    closedStarts X E =
      if X + 1 + t (X + 1) ≤ E then
        insert (X + 1) (closedStarts (X + 1) E)
      else closedStarts (X + 1) E := by
  rw [closedStarts, ← Finset.insert_Ioc_succ_left_eq_Ioc hXE,
    Finset.filter_insert]
  rfl

/-- BPZ Lemma 3.6 in endpoint form: the number of square-product subsets of
`(X,E]` is exactly `2^B`, where `B` counts starting points whose least witness
closes by `E`. -/
theorem card_squareProductSubsets_eq_pow_closedStarts {X E : ℕ} (hXE : X ≤ E) :
    (squareProductSubsets (Finset.Ioc X E)).card = 2 ^ (closedStarts X E).card := by
  refine Nat.decreasingInduction (motive := fun X _ ↦
    (squareProductSubsets (Finset.Ioc X E)).card = 2 ^ (closedStarts X E).card)
    ?_ ?_ hXE
  · intro X hlt ih
    rw [card_squareProductSubsets_step hlt, closedStarts_step hlt]
    split_ifs with helig
    · have hnotmem : X + 1 ∉ closedStarts (X + 1) E := by
        simp [closedStarts]
      rw [Finset.card_insert_of_notMem hnotmem, pow_succ, ih]
      omega
    · exact ih
  · have hsq : squareProductSubsets (Finset.Ioc E E) = {∅} := by
      ext S
      rw [mem_squareProductSubsets, Finset.mem_singleton]
      simp only [Finset.Ioc_self]
      constructor
      · rintro ⟨hS, _⟩
        exact Finset.subset_empty.mp hS
      · rintro rfl
        exact ⟨by simp, IsSquare.one⟩
    rw [hsq]
    simp [closedStarts]

/-- BPZ Lemma 3.6 in the interval-length notation of the paper. -/
theorem bpz_square_subset_count (X Y : ℕ) :
    (squareProductSubsets (Finset.Ioc X (X + Y))).card =
      2 ^ ((Finset.Ioc X (X + Y)).filter
        (fun n ↦ n + t n ≤ X + Y)).card := by
  simpa [closedStarts] using
    (card_squareProductSubsets_eq_pow_closedStarts (X := X) (E := X + Y)
      (Nat.le_add_right X Y))

/-! ## Smooth numbers and parity vectors -/

/-- A nonzero natural number is a square exactly when every exponent in its
prime factorization is even. -/
lemma isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨a, ha⟩ p
    have ha0 : a ≠ 0 := by
      intro haz
      subst a
      simp at ha
      exact hn ha
    rw [ha, Nat.factorization_mul ha0 ha0, Finsupp.add_apply]
    exact ⟨a.factorization p, by omega⟩
  · intro heven
    let factors := n.factorization.mapRange (· / 2) (Nat.zero_div 2)
    let a := factors.prod (· ^ ·)
    have hprime : ∀ p ∈ factors.support, Nat.Prime p := by
      intro p hp
      exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
    have hfac : (a ^ 2).factorization = n.factorization := by
      rw [Nat.factorization_pow]
      unfold a
      rw [Nat.prod_pow_factorization_eq_self hprime]
      ext p
      rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply]
      have htwo : 2 ∣ n.factorization p := by
        obtain ⟨r, hr⟩ := heven p
        exact ⟨r, by omega⟩
      exact Nat.mul_div_cancel' htwo
    have han0 : a ^ 2 ≠ 0 := by simp [a, factors]
    have heq : a ^ 2 = n := by
      apply Nat.eq_of_factorization_eq han0 hn
      intro p
      exact congrArg (fun f : ℕ →₀ ℕ ↦ f p) hfac
    exact ⟨a, by simpa [pow_two] using heq.symm⟩

private lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hval : a.val = 0 ∨ a.val = 1 := by omega
  rcases hval with hval | hval
  · left
    exact (ZMod.val_eq_zero a).mp hval
  · right
    exact (ZMod.val_eq_one (by norm_num) a).mp hval

/-- Subsets of a finite family of `ℝ₂`-vectors whose vector sum is zero. -/
def zeroSumSubsets {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] (v : α → β → ZMod 2) : Finset (Finset α) :=
  Finset.univ.powerset.filter fun S ↦ ∑ a ∈ S, v a = 0

/-- Among `M` vectors in an `r`-coordinate vector space over `ℝ₂`, at
least `2^(M-r)` subsets have zero sum. -/
theorem pow_card_sub_card_le_zeroSumSubsets_card
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] (v : α → β → ZMod 2) :
    2 ^ (Fintype.card α - Fintype.card β) ≤ (zeroSumSubsets v).card := by
  let L : (α → ZMod 2) →ₗ[ZMod 2] (β → ZMod 2) :=
    Fintype.linearCombination (ZMod 2) v
  let : Fintype L.ker := Fintype.ofFinite L.ker
  let supportSet : L.ker → Finset α := fun f ↦
    Finset.univ.filter fun a ↦ f.1 a = 1
  have hsupport_mem : ∀ f : L.ker, supportSet f ∈ zeroSumSubsets v := by
    intro f
    rw [zeroSumSubsets, Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hsum : (∑ a ∈ supportSet f, v a) = ∑ a, f.1 a • v a := by
      simp only [supportSet]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      rcases zmod_two_eq_zero_or_one (f.1 a) with ha | ha
      · simp [ha]
      · simp [ha]
    rw [hsum]
    exact f.2
  have hsupport_inj : Function.Injective supportSet := by
    intro f g hfg
    apply Subtype.ext
    funext a
    have hmem : a ∈ supportSet f ↔ a ∈ supportSet g := by rw [hfg]
    simp only [supportSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rcases zmod_two_eq_zero_or_one (f.1 a) with hf | hf <;>
      rcases zmod_two_eq_zero_or_one (g.1 a) with hg | hg <;> simp_all
  have hker_card_le : Fintype.card L.ker ≤ (zeroSumSubsets v).card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card_of_injOn supportSet
      (fun f _ ↦ hsupport_mem f) hsupport_inj.injOn
  have hrange_le : Module.finrank (ZMod 2) L.range ≤ Fintype.card β := by
    exact L.range.finrank_le.trans_eq (Module.finrank_fintype_fun_eq_card (ZMod 2))
  have hnull := L.finrank_range_add_finrank_ker
  have hker_rank : Fintype.card α - Fintype.card β ≤
      Module.finrank (ZMod 2) L.ker := by
    rw [Module.finrank_fintype_fun_eq_card (ZMod 2)] at hnull
    omega
  calc
    2 ^ (Fintype.card α - Fintype.card β)
        ≤ 2 ^ Module.finrank (ZMod 2) L.ker :=
          Nat.pow_le_pow_right (by omega) hker_rank
    _ = Fintype.card L.ker := by
      simpa using
        (Module.card_eq_pow_finrank (K := ZMod 2) (V := L.ker)).symm
    _ ≤ (zeroSumSubsets v).card := hker_card_le

/-- The `Y`-smooth members of `(X,X+Y]`; Mathlib's convention is strict,
so `Y`-smooth is represented by membership in `smoothNumbers (Y+1)`. -/
def smoothInterval (X Y : ℕ) : Finset ℕ :=
  (Finset.Ioc X (X + Y)).filter fun m ↦ m ∈ (Y + 1).smoothNumbers

/-! ### A finite lower reservoir of smooth numbers -/

/-- Products of `k`-element subsets of a supplied finite prime set. -/
noncomputable def primeSubsetProducts (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (P.powersetCard k).image fun S ↦ ∏ p ∈ S, p

/-- Unique factorization makes the subset-product map injective on a set
of primes, so the reservoir has exactly the expected binomial size. -/
lemma card_primeSubsetProducts (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (primeSubsetProducts P k).card = P.card.choose k := by
  rw [primeSubsetProducts, Finset.card_image_of_injOn]
  · exact Finset.card_powersetCard k P
  · intro A hA B hB hprod
    have hAprime : ∀ p ∈ A, p.Prime := by
      intro p hp
      exact hP p ((Finset.mem_powersetCard.mp hA).1 hp)
    have hBprime : ∀ p ∈ B, p.Prime := by
      intro p hp
      exact hP p ((Finset.mem_powersetCard.mp hB).1 hp)
    have hfac := congrArg Nat.primeFactors hprod
    simpa [Nat.primeFactors_prod hAprime, Nat.primeFactors_prod hBprime] using hfac

/-- If the supplied primes are at most `Y` and `Y^k ≤ X`, all subset
products belong to the finite set of `Y`-smooth integers through `X`. -/
lemma primeSubsetProducts_subset_smoothNumbersUpTo
    {P : Finset ℕ} {k X Y : ℕ}
    (hPprime : ∀ p ∈ P, p.Prime) (hPle : ∀ p ∈ P, p ≤ Y)
    (hpow : Y ^ k ≤ X) :
    primeSubsetProducts P k ⊆ Nat.smoothNumbersUpTo X (Y + 1) := by
  intro m hm
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
  have hScard := (Finset.mem_powersetCard.mp hS).2
  have hSsub := (Finset.mem_powersetCard.mp hS).1
  apply Nat.mem_smoothNumbersUpTo.mpr
  constructor
  · calc
      ∏ p ∈ S, p ≤ ∏ _p ∈ S, Y := by
        exact Finset.prod_le_prod' (fun p hp ↦ hPle p (hSsub hp))
      _ = Y ^ S.card := by simp
      _ = Y ^ k := by rw [hScard]
      _ ≤ X := hpow
  · rw [Nat.mem_smoothNumbers']
    intro q hq hqdiv
    obtain ⟨p, hpS, hqdp⟩ := (hq.prime.dvd_finsetProd_iff id).mp hqdiv
    have hpprime := hPprime p (hSsub hpS)
    have hqp : q = p :=
      (Nat.dvd_prime hpprime).mp hqdp |>.resolve_left hq.ne_one
    rw [hqp]
    exact Nat.lt_succ_iff.mpr (hPle p (hSsub hpS))

/-- Concrete binomial lower bound for the smooth-number counting function. -/
theorem choose_le_smoothNumbersUpTo_card
    {P : Finset ℕ} {k X Y : ℕ}
    (hPprime : ∀ p ∈ P, p.Prime) (hPle : ∀ p ∈ P, p ≤ Y)
    (hpow : Y ^ k ≤ X) :
    P.card.choose k ≤ (Nat.smoothNumbersUpTo X (Y + 1)).card := by
  rw [← card_primeSubsetProducts P k hPprime]
  exact Finset.card_le_card
    (primeSubsetProducts_subset_smoothNumbersUpTo hPprime hPle hpow)

/-- Products from a `k`-element prime subset lie between the corresponding
`k`th powers of any common lower and upper bounds for the primes. -/
lemma primeSubsetProducts_subset_Icc
    {P : Finset ℕ} {k L Y : ℕ}
    (hPlo : ∀ p ∈ P, L ≤ p) (hPhi : ∀ p ∈ P, p ≤ Y) :
    primeSubsetProducts P k ⊆ Finset.Icc (L ^ k) (Y ^ k) := by
  intro m hm
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
  have hScard := (Finset.mem_powersetCard.mp hS).2
  have hSsub := (Finset.mem_powersetCard.mp hS).1
  apply Finset.mem_Icc.mpr
  constructor
  · calc
      L ^ k = L ^ S.card := by rw [hScard]
      _ = ∏ _p ∈ S, L := by simp
      _ ≤ ∏ p ∈ S, p :=
        Finset.prod_le_prod' (fun p hp ↦ hPlo p (hSsub hp))
  · calc
      ∏ p ∈ S, p ≤ ∏ _p ∈ S, Y :=
        Finset.prod_le_prod' (fun p hp ↦ hPhi p (hSsub hp))
      _ = Y ^ S.card := by simp
      _ = Y ^ k := by rw [hScard]

/-- BPZ Lemma 3.7: an interval contains at least as many closed witness
starts as its number of `Y`-smooth members minus the number of primes at most
`Y`.  The latter is `#(Y+1).primesBelow = π(Y)`. -/
theorem bpz_smooth_interval_bound (X Y : ℕ) :
    (smoothInterval X Y).card - (Y + 1).primesBelow.card ≤
      (closedStarts X (X + Y)).card := by
  let A := smoothInterval X Y
  let P := (Y + 1).primesBelow
  let v : A → P → ZMod 2 := fun m p ↦ (m.1.factorization p.1 : ZMod 2)
  have hzero_le_square : (zeroSumSubsets v).card ≤
      (squareProductSubsets (Finset.Ioc X (X + Y))).card := by
    refine Finset.card_le_card_of_injOn (fun U : Finset A ↦ U.image Subtype.val) ?_ ?_
    · intro U hU
      change U ∈ zeroSumSubsets v at hU
      change U.image Subtype.val ∈ squareProductSubsets (Finset.Ioc X (X + Y))
      rw [zeroSumSubsets, Finset.mem_filter] at hU
      rw [mem_squareProductSubsets]
      refine ⟨?_, ?_⟩
      · intro m hm
        obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp hm
        exact (Finset.mem_filter.mp a.2).1
      · have hprod0 : (∏ m ∈ U.image Subtype.val, m) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro m hm
          obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp hm
          have haI := Finset.mem_Ioc.mp (Finset.mem_filter.mp a.2).1
          omega
        rw [isSquare_iff_even_factorization hprod0]
        intro p
        rw [Nat.factorization_prod_apply (fun m hm ↦ by
          obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp hm
          have haI := Finset.mem_Ioc.mp (Finset.mem_filter.mp a.2).1
          omega)]
        by_cases hpP : p ∈ P
        · have hpzero := congrFun hU.2 (⟨p, hpP⟩ : P)
          have hpzero' : (∑ a ∈ U, (a.1.factorization p : ZMod 2)) = 0 := by
            simpa only [Finset.sum_apply, v, Pi.zero_apply] using hpzero
          rw [Finset.sum_image Subtype.val_injective.injOn]
          rw [← ZMod.natCast_eq_zero_iff_even]
          simpa only [Nat.cast_sum] using hpzero'
        · have hsum0 : ∑ m ∈ U.image Subtype.val, m.factorization p = 0 := by
            apply Finset.sum_eq_zero
            intro m hm
            obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp hm
            have hasmooth := (Finset.mem_filter.mp a.2).2
            by_cases hp : p.Prime
            · apply Nat.factorization_eq_zero_of_not_dvd
              intro hpdvd
              have hplt := (Nat.mem_smoothNumbers').mp hasmooth p hp hpdvd
              exact hpP (Nat.mem_primesBelow.mpr ⟨hplt, hp⟩)
            · exact Nat.factorization_eq_zero_of_not_prime _ hp
          rw [hsum0]
          exact Even.zero
    · exact (Finset.image_injective Subtype.val_injective).injOn
  have hlin := pow_card_sub_card_le_zeroSumSubsets_card v
  have hpows : 2 ^ (A.card - P.card) ≤
      2 ^ (closedStarts X (X + Y)).card := by
    simpa [A, P] using hlin.trans hzero_le_square |>.trans_eq
      (card_squareProductSubsets_eq_pow_closedStarts (Nat.le_add_right X Y))
  have hexp := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpows
  simpa [A, P] using hexp

/-- The largest prime factor, with the standard convention `P⁺(0) = P⁺(1) = 1`. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 1

lemma largestPrimeFactor_eq_max' {n : ℕ} (hn : 1 < n) :
    largestPrimeFactor n = n.primeFactors.max' (Nat.nonempty_primeFactors.mpr hn) := by
  simp only [largestPrimeFactor, dif_pos (Nat.nonempty_primeFactors.mpr hn)]

lemma largestPrimeFactor_mem {n : ℕ} (hn : 1 < n) :
    largestPrimeFactor n ∈ n.primeFactors := by
  rw [largestPrimeFactor_eq_max' hn]
  exact Finset.max'_mem _ _

lemma largestPrimeFactor_prime {n : ℕ} (hn : 1 < n) :
    Nat.Prime (largestPrimeFactor n) :=
  Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem hn)

lemma largestPrimeFactor_dvd {n : ℕ} (hn : 1 < n) : largestPrimeFactor n ∣ n :=
  Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem hn)

lemma prime_le_largestPrimeFactor {n q : ℕ} (hn : 1 < n)
    (hq : q.Prime) (hqn : q ∣ n) : q ≤ largestPrimeFactor n := by
  rw [largestPrimeFactor_eq_max' hn]
  exact Finset.le_max' _ q (hq.mem_primeFactors hqn (by omega))

/-! ## The elementary lower bound -/

private lemma prime_dvd_finset_prod {p : ℕ} (hp : p.Prime) {J : Finset ℕ}
    {f : ℕ → ℕ} (h : p ∣ ∏ j ∈ J, f j) : ∃ j ∈ J, p ∣ f j := by
  exact (hp.prime.dvd_finsetProd_iff f).mp h

/-- If `p` divides `n` exactly once (in the weak sense `p² ∤ n`), every
square-product witness has endpoint at least `p`.  This is BPZ Lemma 3.4. -/
lemma prime_le_endpoint_of_admissible {n T p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hp2n : ¬p ^ 2 ∣ n) (hT : Admissible n T) : p ≤ T := by
  obtain ⟨J, hJ, y, hy⟩ := hT
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    exact hp2n (dvd_zero _)
  have hpn' := hpn
  obtain ⟨a, ha⟩ := hpn
  have hpa : ¬p ∣ a := by
    intro hpa
    obtain ⟨b, hb⟩ := hpa
    apply hp2n
    refine ⟨b, ?_⟩
    rw [hb] at ha
    simpa [pow_two, Nat.mul_assoc] using ha
  have hpy : p ∣ y := by
    have hpyy : p ∣ y * y := by
      rw [← hy]
      exact dvd_mul_of_dvd_left hpn' _
    exact (hp.dvd_mul.mp hpyy).elim id id
  obtain ⟨z, hz⟩ := hpy
  have hpam : p ∣ a * ∏ j ∈ J, (n + j) := by
    have hp0 : 0 < p := hp.pos
    have hcancel : p * (a * ∏ j ∈ J, (n + j)) = p * (p * (z * z)) := by
      calc
        p * (a * ∏ j ∈ J, (n + j))
            = n * ∏ j ∈ J, (n + j) := by rw [ha]; ac_rfl
        _ = y * y := hy
        _ = (p * z) * (p * z) := by rw [hz]
        _ = p * (p * (z * z)) := by ring
    exact ⟨z * z, Nat.eq_of_mul_eq_mul_left hp0 hcancel⟩
  have hpm : p ∣ ∏ j ∈ J, (n + j) := (hp.dvd_mul.mp hpam).resolve_left hpa
  obtain ⟨j, hjJ, hpj⟩ := prime_dvd_finset_prod hp hpm
  have hp_offset : p ∣ j := by
    exact (Nat.dvd_add_iff_right hpn').mpr hpj
  have hjpos : 0 < j := (Finset.mem_Icc.mp (hJ hjJ)).1
  exact le_trans (Nat.le_of_dvd hjpos hp_offset) (Finset.mem_Icc.mp (hJ hjJ)).2

lemma prime_le_t {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hp2n : ¬p ^ 2 ∣ n) :
    p ≤ t n :=
  prime_le_endpoint_of_admissible hp hpn hp2n (t_spec n)

lemma largestPrimeFactor_le_t {n : ℕ} (hn : 1 < n)
    (hnotSq : ¬(largestPrimeFactor n) ^ 2 ∣ n) :
    largestPrimeFactor n ≤ t n :=
  prime_le_t (largestPrimeFactor_prime hn) (largestPrimeFactor_dvd hn) hnotSq

/-! ## The Granville--Selfridge six-factor construction -/

private lemma admissible_collision_one (a : ℕ) (ha : 0 < a) :
    Admissible (a * (4 * a + 1)) (4 * a + 1) := by
  let n := a * (4 * a + 1)
  let J : Finset ℕ := {3 * a + 1, 3 * a, 4 * a + 1}
  refine ⟨J, ?_, ?_⟩
  · intro j hj
    simp only [J, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with (rfl | rfl | rfl) <;> simp only [Finset.mem_Icc] <;> omega
  · refine ⟨2 * a * (a + 1) * (4 * a + 1) * (2 * a + 1), ?_⟩
    have h₁ : 3 * a + 1 ≠ 3 * a := by omega
    have h₂ : 3 * a + 1 ≠ 4 * a + 1 := by omega
    have h₃ : 3 * a ≠ 4 * a + 1 := by omega
    have hm₁ : 3 * a + 1 ∉ ({3 * a, 4 * a + 1} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h₁, h₂⟩
    have hm₂ : 3 * a ∉ ({4 * a + 1} : Finset ℕ) := by
      simpa only [Finset.mem_singleton] using h₃
    dsimp only [J]
    rw [Finset.prod_insert hm₁, Finset.prod_insert hm₂, Finset.prod_singleton]
    ring

private lemma admissible_collision_two (a : ℕ) (ha : 0 < a) :
    Admissible (a * (4 * a + 3)) (4 * a + 3) := by
  let n := a * (4 * a + 3)
  let J : Finset ℕ := {a, a + 1, 4 * a + 3}
  refine ⟨J, ?_, ?_⟩
  · intro j hj
    simp only [J, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with (rfl | rfl | rfl) <;> simp only [Finset.mem_Icc] <;> omega
  · refine ⟨2 * a * (a + 1) * (4 * a + 3) * (2 * a + 1), ?_⟩
    have h₁ : a ≠ a + 1 := by omega
    have h₂ : a ≠ 4 * a + 3 := by omega
    have h₃ : a + 1 ≠ 4 * a + 3 := by omega
    have hm₁ : a ∉ ({a + 1, 4 * a + 3} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h₁, h₂⟩
    have hm₂ : a + 1 ∉ ({4 * a + 3} : Finset ℕ) := by
      simpa only [Finset.mem_singleton] using h₃
    dsimp only [J]
    rw [Finset.prod_insert hm₁, Finset.prod_insert hm₂, Finset.prod_singleton]
    ring

private lemma admissible_no_collision (a k : ℕ) (ha : 0 < a) (hak : a < k)
    (hk₁ : k ≠ 2 * a) (hk₂ : k ≠ 2 * a + 1) :
    Admissible (a * (2 * k + 1)) (2 * k + 1) := by
  let n := a * (2 * k + 1)
  let d₁ := a
  let d₂ := k - a
  let d₃ := k + a + 1
  let d₄ := 2 * k - a
  let p := 2 * k + 1
  let J : Finset ℕ := {d₁, d₂, d₃, d₄, p}
  have hd₁₂ : d₁ ≠ d₂ := by simp only [d₁, d₂]; omega
  have hd₁₃ : d₁ ≠ d₃ := by simp only [d₁, d₃]; omega
  have hd₁₄ : d₁ ≠ d₄ := by simp only [d₁, d₄]; omega
  have hd₁p : d₁ ≠ p := by simp only [d₁, p]; omega
  have hd₂₃ : d₂ ≠ d₃ := by simp only [d₂, d₃]; omega
  have hd₂₄ : d₂ ≠ d₄ := by simp only [d₂, d₄]; omega
  have hd₂p : d₂ ≠ p := by simp only [d₂, p]; omega
  have hd₃₄ : d₃ ≠ d₄ := by simp only [d₃, d₄]; omega
  have hd₃p : d₃ ≠ p := by simp only [d₃, p]; omega
  have hd₄p : d₄ ≠ p := by simp only [d₄, p]; omega
  have hterm₁ : n + d₁ = 2 * a * (k + 1) := by simp only [n, d₁]; ring
  have hterm₂ : n + d₂ = (2 * a + 1) * k := by
    simp only [n, d₂]
    have hpoly : (2 * a + 1) * k + a = a * (2 * k + 1) + k := by ring
    omega
  have hterm₃ : n + d₃ = (2 * a + 1) * (k + 1) := by
    simp only [n, d₃]
    ring
  have hterm₄ : n + d₄ = 2 * (a + 1) * k := by
    simp only [n, d₄]
    have hpoly : 2 * (a + 1) * k + a = a * (2 * k + 1) + 2 * k := by ring
    omega
  have htermp : n + p = (a + 1) * (2 * k + 1) := by
    simp only [n, p]
    ring
  have hm₁ : d₁ ∉ ({d₂, d₃, d₄, p} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hd₁₂, hd₁₃, hd₁₄, hd₁p⟩
  have hm₂ : d₂ ∉ ({d₃, d₄, p} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hd₂₃, hd₂₄, hd₂p⟩
  have hm₃ : d₃ ∉ ({d₄, p} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hd₃₄, hd₃p⟩
  have hm₄ : d₄ ∉ ({p} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hd₄p
  refine ⟨J, ?_, ?_⟩
  · intro j hj
    simp only [J, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with (rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Finset.mem_Icc, d₂, d₃, d₄, p] <;> omega
  · refine ⟨2 * a * (a + 1) * (2 * k + 1) * (2 * a + 1) * k * (k + 1), ?_⟩
    dsimp only [J]
    rw [Finset.prod_insert hm₁, Finset.prod_insert hm₂, Finset.prod_insert hm₃,
      Finset.prod_insert hm₄, Finset.prod_singleton]
    rw [hterm₁, hterm₂, hterm₃, hterm₄, htermp]
    ring

/-- The explicit Granville--Selfridge construction in the odd form
`p = 2*k+1`.  The condition `a < k` is exactly `2*a+1 < p`. -/
lemma admissible_two_mul_add_one (a k : ℕ) (ha : 0 < a) (hak : a < k) :
    Admissible (a * (2 * k + 1)) (2 * k + 1) := by
  by_cases hk₁ : k = 2 * a
  · subst k
    convert admissible_collision_one a ha using 1 <;> ring
  by_cases hk₂ : k = 2 * a + 1
  · subst k
    convert admissible_collision_two a ha using 1 <;> ring
  exact admissible_no_collision a k ha hak hk₁ hk₂

lemma t_le_prime_of_large_prime_divisor {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : p ∣ n) (hlarge : 2 * n < (p - 1) ^ 2) : t n ≤ p := by
  have hp2 : p ≠ 2 := by
    intro hp2
    subst p
    norm_num at hlarge
    omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hpk : p = 2 * k + 1 := by omega
  obtain ⟨a, ha⟩ := hpn
  have ha0 : 0 < a := by
    by_contra hnot
    have haZ : a = 0 := Nat.eq_zero_of_not_pos hnot
    subst a
    simp at ha
    omega
  have hak : a < k := by
    by_contra hnot
    have hka : k ≤ a := Nat.le_of_not_gt hnot
    have hmul : k * k ≤ a * k := Nat.mul_le_mul_right k hka
    rw [ha, hpk] at hlarge
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hsub] at hlarge
    nlinarith
  apply t_le_of_admissible
  rw [ha, hpk]
  simpa [Nat.mul_comm] using admissible_two_mul_add_one a k ha0 hak

lemma prime_sq_not_dvd_of_large {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hlarge : 2 * n < (p - 1) ^ 2) : ¬p ^ 2 ∣ n := by
  intro hp2n
  have hp2le : p ^ 2 ≤ n := Nat.le_of_dvd hn hp2n
  have hp1 : 1 ≤ p := hp.one_le
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hlt : (p - 1) ^ 2 < p ^ 2 := by
    nlinarith [hp.pos]
  omega

/-- Granville--Selfridge's exact estimate in an integer-arithmetic form.
The inequality is equivalent to `p > sqrt (2*n) + 1`. -/
theorem t_eq_prime_of_large_prime_divisor {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : p ∣ n) (hlarge : 2 * n < (p - 1) ^ 2) : t n = p := by
  apply Nat.le_antisymm
  · exact t_le_prime_of_large_prime_divisor hn hp hpn hlarge
  · exact prime_le_t hp hpn (prime_sq_not_dvd_of_large hn hp hlarge)

/-- The large-prime-factor resolution of Erdős Problem 841, stated with
the square-root threshold used in the literature. -/
theorem erdos841 {n : ℕ} (hn : 1 < n)
    (hlarge : Real.sqrt (2 * (n : ℝ)) + 1 < (largestPrimeFactor n : ℝ)) :
    t n = largestPrimeFactor n := by
  let p := largestPrimeFactor n
  have hp : p.Prime := largestPrimeFactor_prime hn
  have hp1 : 1 ≤ p := hp.one_le
  have hsqrt : Real.sqrt (2 * (n : ℝ)) < ((p - 1 : ℕ) : ℝ) := by
    change Real.sqrt (2 * (n : ℝ)) + 1 < (p : ℝ) at hlarge
    rw [Nat.cast_sub hp1]
    simp only [Nat.cast_one]
    linarith
  have hsquare : (Real.sqrt (2 * (n : ℝ))) ^ 2 < (((p - 1 : ℕ) : ℝ)) ^ 2 :=
    (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hsqrt
  have hnonneg : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  have hlargeNat : 2 * n < (p - 1) ^ 2 := by
    rw [Real.sq_sqrt hnonneg] at hsquare
    exact_mod_cast hsquare
  exact t_eq_prime_of_large_prime_divisor (by omega) hp
    (largestPrimeFactor_dvd hn) hlargeNat

/-! ## The Granville--Selfridge square-root branch -/

def SquareClassTarget (n T q : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Ioc n (n + T) ∧
    IsSquare ((q : ℚ) * ∏ x ∈ S, (x : ℚ))

lemma squareClassTarget_one (n T : ℕ) : SquareClassTarget n T 1 := by
  refine ⟨∅, by simp, ?_⟩
  simp

lemma squareClassTarget_of_mem {n T q : ℕ}
    (hq : q ∈ Finset.Ioc n (n + T)) : SquareClassTarget n T q := by
  refine ⟨{q}, ?_, ?_⟩
  · simpa only [Finset.singleton_subset_iff] using hq
  simp only [Finset.prod_singleton]
  exact ⟨(q : ℚ), by ring⟩

lemma squareClassTarget_mul_square_iff {n T q k : ℕ} (hk : k ≠ 0) :
    SquareClassTarget n T (q * k ^ 2) ↔ SquareClassTarget n T q := by
  constructor
  · rintro ⟨S, hS, hsq⟩
    refine ⟨S, hS, ?_⟩
    have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    have hkSq : IsSquare ((k : ℚ) ^ 2) := IsSquare.sq _
    have hcast : ((q * k ^ 2 : ℕ) : ℚ) = (q : ℚ) * (k : ℚ) ^ 2 := by norm_num
    rw [hcast, mul_assoc] at hsq
    have h := hsq.div hkSq
    have hcancel :
        (q : ℚ) * ((k : ℚ) ^ 2 * ∏ x ∈ S, (x : ℚ)) / (k : ℚ) ^ 2 =
          (q : ℚ) * ∏ x ∈ S, (x : ℚ) := by
      rw [div_eq_iff (pow_ne_zero 2 hkQ)]
      ring
    rw [hcancel] at h
    exact h
  · rintro ⟨S, hS, hsq⟩
    refine ⟨S, hS, ?_⟩
    have hkSq : IsSquare ((k : ℚ) ^ 2) := IsSquare.sq _
    have h := hsq.mul hkSq
    simpa [mul_assoc, mul_left_comm, mul_comm] using h

private lemma prod_symmDiff_mul_inter_sq_rat (s u : Finset ℕ) :
    (∏ x ∈ s ∆ u, (x : ℚ)) * (∏ x ∈ s ∩ u, (x : ℚ)) ^ 2 =
      (∏ x ∈ s, (x : ℚ)) * (∏ x ∈ u, (x : ℚ)) := by
  rw [Finset.symmDiff_def, Finset.prod_union]
  · have hs := Finset.prod_union (f := fun x : ℕ ↦ (x : ℚ))
      (Finset.disjoint_sdiff_inter s u)
    rw [Finset.sdiff_union_inter] at hs
    have hu := Finset.prod_union (f := fun x : ℕ ↦ (x : ℚ))
      (Finset.disjoint_sdiff_inter u s)
    rw [Finset.sdiff_union_inter] at hu
    rw [Finset.inter_comm] at hu
    rw [hs, hu]
    simp only [pow_two]
    ac_rfl
  · exact Finset.disjoint_left.mpr (by aesop)

lemma squareClassTarget_mul {n T q r : ℕ} (hn : 0 < n)
    (hq : SquareClassTarget n T q) (hr : SquareClassTarget n T r) :
    SquareClassTarget n T (q * r) := by
  rcases hq with ⟨S, hS, hsqS⟩
  rcases hr with ⟨U, hU, hsqU⟩
  refine ⟨S ∆ U, Finset.symmDiff_subset_union.trans (Finset.union_subset hS hU), ?_⟩
  have hinter0 : (∏ x ∈ S ∩ U, (x : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro x hx
    have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
    have hxn : n < x := (Finset.mem_Ioc.mp (hS hxS)).1
    exact_mod_cast (show x ≠ 0 by omega)
  have hprod := hsqS.mul hsqU
  have hinterSq : IsSquare ((∏ x ∈ S ∩ U, (x : ℚ)) ^ 2) := IsSquare.sq _
  have hdiv := hprod.div hinterSq
  have heq := prod_symmDiff_mul_inter_sq_rat S U
  have harg :
      (((q * r : ℕ) : ℚ) * ∏ x ∈ S ∆ U, (x : ℚ)) =
        (((q : ℚ) * ∏ x ∈ S, (x : ℚ)) *
          ((r : ℚ) * ∏ x ∈ U, (x : ℚ))) /
            (∏ x ∈ S ∩ U, (x : ℚ)) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hinter0)).mpr
    rw [Nat.cast_mul]
    calc
      (((q : ℚ) * (r : ℚ)) * ∏ x ∈ S ∆ U, (x : ℚ)) *
          (∏ x ∈ S ∩ U, (x : ℚ)) ^ 2 =
        ((q : ℚ) * (r : ℚ)) *
          ((∏ x ∈ S ∆ U, (x : ℚ)) *
            (∏ x ∈ S ∩ U, (x : ℚ)) ^ 2) := by ring
      _ = ((q : ℚ) * (r : ℚ)) *
          ((∏ x ∈ S, (x : ℚ)) * ∏ x ∈ U, (x : ℚ)) := by rw [heq]
      _ = ((q : ℚ) * ∏ x ∈ S, (x : ℚ)) *
          ((r : ℚ) * ∏ x ∈ U, (x : ℚ)) := by ring
  rw [harg]
  exact hdiv

def gsScale (n : ℕ) : ℕ := (Nat.sqrt n + 1) / 2

def gsEndpoint (n : ℕ) : ℕ := 20 * (Nat.sqrt n + 1)

lemma gsScale_pos {n : ℕ} (hn : 16 ≤ n) : 0 < gsScale n := by
  have hs : 4 ≤ Nat.sqrt n := (Nat.le_sqrt' ).2 (by omega)
  simp only [gsScale]
  omega

lemma sqrt_le_two_mul_gsScale_add_one (n : ℕ) :
    Nat.sqrt n ≤ 2 * gsScale n + 1 := by
  simp only [gsScale]
  omega

lemma n_le_sixteen_mul_gsScale_sq {n : ℕ} (hn : 16 ≤ n) :
    n ≤ 16 * gsScale n ^ 2 := by
  let s := Nat.sqrt n
  let r := gsScale n
  have hr : 0 < r := gsScale_pos hn
  have hnlt : n < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' n
  have hsr : s ≤ 2 * r + 1 := by
    simpa [s, r] using sqrt_le_two_mul_gsScale_add_one n
  have h1 : n ≤ (2 * r + 2) ^ 2 := by nlinarith
  have h2 : (2 * r + 2) ^ 2 ≤ 16 * r ^ 2 := by nlinarith
  exact h1.trans h2

lemma gs_walk_pair_target {n a : ℕ} (hn : 16 ≤ n)
    (ha : a ∈ Finset.Icc (gsScale n) (4 * gsScale n)) :
    SquareClassTarget n (gsEndpoint n) (a * (a + 1)) := by
  let r := gsScale n
  let T := gsEndpoint n
  let b := n / a + 1
  have hr : 0 < r := gsScale_pos hn
  have haBounds : r ≤ a ∧ a ≤ 4 * r := by simpa [r] using Finset.mem_Icc.mp ha
  have ha0 : 0 < a := hr.trans_le haBounds.1
  have hb0 : 0 < b := by simp [b]
  have hnScale : n ≤ 16 * r ^ 2 := by
    simpa [r] using n_le_sixteen_mul_gsScale_sq hn
  have hna : n ≤ 16 * r * a := by
    calc
      n ≤ 16 * r ^ 2 := hnScale
      _ = (16 * r) * r := by ring
      _ ≤ (16 * r) * a := Nat.mul_le_mul_left _ haBounds.1
      _ = 16 * r * a := by ring
  have hdiv : n / a ≤ 16 * r := by
    exact Nat.div_le_of_le_mul (by simpa [mul_comm, mul_left_comm] using hna)
  have habLower : n < a * b := by
    simpa [b] using Nat.lt_mul_div_succ n ha0
  have habUpper : a * b ≤ n + a := by
    dsimp [b]
    calc
      a * (n / a + 1) = a * (n / a) + a := by ring
      _ ≤ n + a := Nat.add_le_add_right (Nat.mul_div_le n a) a
  have hsuccLower : n < (a + 1) * b :=
    habLower.trans_le (Nat.mul_le_mul_right b (Nat.le_succ a))
  have hsuccUpper : (a + 1) * b ≤ n + T := by
    have hraw : (a + 1) * b ≤ n + a + (n / a + 1) := by
      calc
        (a + 1) * b = a * b + b := by ring
        _ ≤ (n + a) + (n / a + 1) := Nat.add_le_add habUpper (by simp [b])
    have hsmall : a + (n / a + 1) ≤ T := by
      dsimp [T, gsEndpoint]
      have hrs : r ≤ Nat.sqrt n := by
        dsimp [r, gsScale]
        omega
      omega
    omega
  have haT : a ≤ T := by
    dsimp [T, gsEndpoint]
    have hrs : r ≤ Nat.sqrt n := by
      dsimp [r, gsScale]
      omega
    omega
  have hne : a * b ≠ (a + 1) * b := by
    exact ne_of_lt (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self a) hb0)
  refine ⟨{a * b, (a + 1) * b}, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_Ioc.mpr
        ⟨habLower, habUpper.trans (Nat.add_le_add_left haT n)⟩
    · exact Finset.mem_Ioc.mpr ⟨hsuccLower, hsuccUpper⟩
  · rw [Finset.prod_insert]
    · rw [Finset.prod_singleton]
      refine ⟨((a * (a + 1) * b : ℕ) : ℚ), ?_⟩
      push_cast
      ring
    · simpa only [Finset.mem_singleton] using hne

lemma gs_walk_target_of_le {n m v : ℕ} (hn : 16 ≤ n)
    (hm : m ∈ Finset.Icc (gsScale n) (4 * gsScale n))
    (hv : v ∈ Finset.Icc (gsScale n) (4 * gsScale n))
    (hmv : m ≤ v) : SquareClassTarget n (gsEndpoint n) (m * v) := by
  let r := gsScale n
  have hr : 0 < r := gsScale_pos hn
  have hmBounds : r ≤ m ∧ m ≤ 4 * r := by simpa [r] using Finset.mem_Icc.mp hm
  have hvBounds : r ≤ v ∧ v ≤ 4 * r := by simpa [r] using Finset.mem_Icc.mp hv
  induction v, hmv using Nat.le_induction with
  | base =>
      refine ⟨∅, by simp, ?_⟩
      simp only [Finset.prod_empty, mul_one]
      refine ⟨(m : ℚ), ?_⟩
      norm_num
  | succ v hmv ih =>
      have hv0 : 0 < v := hr.trans_le (hmBounds.1.trans hmv)
      have hvMem : v ∈ Finset.Icc (gsScale n) (4 * gsScale n) := by
        rw [Finset.mem_Icc]
        exact ⟨hmBounds.1.trans hmv, by
          change v ≤ 4 * r
          omega⟩
      have hp := gs_walk_pair_target hn hvMem
      have hi := ih hvMem ⟨hmBounds.1.trans hmv, by
        omega⟩
      have hmul := squareClassTarget_mul (show 0 < n by omega) hi hp
      have hshape :
          (m * v) * (v * (v + 1)) = (m * (v + 1)) * v ^ 2 := by ring
      rw [hshape] at hmul
      exact (squareClassTarget_mul_square_iff (n := n) (T := gsEndpoint n)
        (q := m * (v + 1)) (k := v) hv0.ne').mp hmul

lemma gs_walk_target_of_ne {n m v : ℕ} (hn : 16 ≤ n)
    (hm : m ∈ Finset.Icc (gsScale n) (4 * gsScale n))
    (hv : v ∈ Finset.Icc (gsScale n) (4 * gsScale n))
    (_hmv : m ≠ v) : SquareClassTarget n (gsEndpoint n) (m * v) := by
  rcases le_total m v with hle | hle
  · exact gs_walk_target_of_le hn hm hv hle
  · simpa [mul_comm] using gs_walk_target_of_le hn hv hm hle

lemma exists_prime_square_multiple_in_gs_interval {r p : ℕ}
    (hr : 0 < r) (hp : p.Prime) (hpUpper : p ≤ 4 * r) :
    ∃ k : ℕ, 0 < k ∧ p * k ^ 2 ∈ Finset.Icc r (4 * r) := by
  by_cases hpr : r ≤ p
  · refine ⟨1, by simp, ?_⟩
    rw [Finset.mem_Icc]
    simpa using ⟨hpr, hpUpper⟩
  · have hplt : p < r := Nat.lt_of_not_ge hpr
    have hex : ∃ k : ℕ, r ≤ p * k ^ 2 := by
      refine ⟨r, ?_⟩
      have hpTwo : 2 ≤ p := hp.two_le
      nlinarith
    let k := Nat.find hex
    have hkSpec : r ≤ p * k ^ 2 := Nat.find_spec hex
    have hk0 : 0 < k := by
      by_contra hk
      have hkz : k = 0 := Nat.eq_zero_of_not_pos hk
      have hz : p * k ^ 2 = 0 := by simp [hkz]
      omega
    have hkTwo : 2 ≤ k := by
      by_contra hk
      have hkOne : k = 1 := by omega
      have hone : p * k ^ 2 = p := by simp [hkOne]
      omega
    have hkPrev : p * (k - 1) ^ 2 < r := by
      have hpred : k - 1 < k := by omega
      exact Nat.lt_of_not_ge (Nat.find_min hex hpred)
    have hkGrow : k ≤ 2 * (k - 1) := by omega
    have hupper : p * k ^ 2 ≤ 4 * r := by
      calc
        p * k ^ 2 ≤ p * (2 * (k - 1)) ^ 2 := by gcongr
        _ = 4 * (p * (k - 1) ^ 2) := by ring
        _ ≤ 4 * r := Nat.mul_le_mul_left 4 hkPrev.le
    exact ⟨k, hk0, Finset.mem_Icc.mpr ⟨hkSpec, hupper⟩⟩

lemma exists_square_in_gs_interval {r : ℕ} (hr : 0 < r) :
    ∃ q : ℕ, 0 < q ∧ q ^ 2 ∈ Finset.Icc r (4 * r) := by
  let q := Nat.sqrt r + 1
  have hq0 : 0 < q := by simp [q]
  have hlower : r ≤ q ^ 2 := by
    have := Nat.lt_succ_sqrt' r
    simpa [q] using this.le
  have hsqrt : Nat.sqrt r ≤ r := Nat.sqrt_le_self r
  have hupper : q ^ 2 ≤ 4 * r := by
    dsimp [q]
    nlinarith [Nat.sqrt_le r]
  exact ⟨q, hq0, Finset.mem_Icc.mpr ⟨hlower, hupper⟩⟩

lemma prime_mul_sq_ne_sq {p k q : ℕ} (hp : p.Prime) (hk : 0 < k) :
    p * k ^ 2 ≠ q ^ 2 := by
  intro heq
  have hvSq : IsSquare (p * k ^ 2) := ⟨q, by simpa [pow_two] using heq⟩
  have hvSqQ : IsSquare (((p * k ^ 2 : ℕ) : ℚ)) :=
    Rat.isSquare_natCast_iff.mpr hvSq
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkSqQ : IsSquare ((k : ℚ) ^ 2) := IsSquare.sq _
  have hpSqQ := hvSqQ.div hkSqQ
  have hcancel : (((p * k ^ 2 : ℕ) : ℚ)) / (k : ℚ) ^ 2 = (p : ℚ) := by
    push_cast
    rw [div_eq_iff (pow_ne_zero 2 hkQ)]
  rw [hcancel] at hpSqQ
  exact hp.not_isSquare (Rat.isSquare_natCast_iff.mp hpSqQ)

lemma gs_prime_target {n p : ℕ} (hn : 16 ≤ n) (hp : p.Prime)
    (hpUpper : p ≤ 4 * gsScale n) :
    SquareClassTarget n (gsEndpoint n) p := by
  let r := gsScale n
  have hr : 0 < r := gsScale_pos hn
  obtain ⟨k, hk0, hv⟩ :=
    exists_prime_square_multiple_in_gs_interval hr hp (by simpa [r] using hpUpper)
  obtain ⟨q, hq0, hw⟩ := exists_square_in_gs_interval hr
  have hv' : p * k ^ 2 ∈ Finset.Icc (gsScale n) (4 * gsScale n) := by
    simpa [r] using hv
  have hw' : q ^ 2 ∈ Finset.Icc (gsScale n) (4 * gsScale n) := by
    simpa [r] using hw
  have hne : p * k ^ 2 ≠ q ^ 2 := prime_mul_sq_ne_sq hp hk0
  have hwalk := gs_walk_target_of_ne hn hv' hw' hne
  have hshape : (p * k ^ 2) * q ^ 2 = p * (k * q) ^ 2 := by ring
  rw [hshape] at hwalk
  exact (squareClassTarget_mul_square_iff (n := n) (T := gsEndpoint n)
    (q := p) (k := k * q) (Nat.mul_ne_zero hk0.ne' hq0.ne')).mp hwalk

lemma sqrt_two_mul_add_one_le_four_gsScale {n : ℕ} (hn : 16 ≤ n) :
    Nat.sqrt (2 * n) + 1 ≤ 4 * gsScale n := by
  let s := Nat.sqrt n
  have hs : 4 ≤ s := by
    dsimp [s]
    exact (Nat.le_sqrt').2 (by omega)
  have hnlt : n < (s + 1) ^ 2 := by
    simpa [s] using Nat.lt_succ_sqrt' n
  have htwo : 2 * n < (2 * s) ^ 2 := by nlinarith
  have hsqrt : Nat.sqrt (2 * n) < 2 * s := (Nat.sqrt_lt').2 htwo
  dsimp [gsScale]
  omega

lemma squareClassTarget_of_prime_divisors {n T m : ℕ} (hn : 0 < n)
    (hm : 0 < m)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ m → SquareClassTarget n T p) :
    SquareClassTarget n T m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm1 : m = 1
      · subst m
        exact squareClassTarget_one n T
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
      let k := m / p
      have hm0 : 0 < m := hm
      have hklt : k < m := by
        dsimp [k]
        exact Nat.div_lt_self hm0 hp.one_lt
      have hk0 : 0 < k := by
        dsimp [k]
        exact Nat.div_pos (Nat.le_of_dvd hm0 hpm) hp.pos
      have hpk : p * k = m := by
        dsimp [k]
        rw [Nat.mul_comm]
        exact Nat.div_mul_cancel hpm
      have hprimeK : ∀ q : ℕ, q.Prime → q ∣ k → SquareClassTarget n T q := by
        intro q hq hqk
        apply hprime q hq
        rw [← hpk]
        exact dvd_mul_of_dvd_right hqk p
      have hkTarget := ih k hklt hk0 hprimeK
      have hpTarget := hprime p hp hpm
      have hmul := squareClassTarget_mul hn hpTarget hkTarget
      simpa [hpk] using hmul

lemma admissible_of_squareClassTarget_self {n T : ℕ} (hn : 0 < n)
    (h : SquareClassTarget n T n) : Admissible n T := by
  rcases h with ⟨S, hS, hsqQ⟩
  have hnS : n ∉ S := by
    intro hmem
    exact (Finset.mem_Ioc.mp (hS hmem)).1.false
  have hcast :
      ((((n * ∏ x ∈ S, x : ℕ) : ℕ) : ℚ)) =
        (n : ℚ) * ∏ x ∈ S, (x : ℚ) := by
    push_cast
    rfl
  have hsqNat : IsSquare (n * ∏ x ∈ S, x) := by
    apply Rat.isSquare_natCast_iff.mp
    rw [hcast]
    exact hsqQ
  apply (admissible_iff_exists_values n T).mpr
  refine ⟨insert n S, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_add_right _ _⟩
    · have hxI := Finset.mem_Ioc.mp (hS hx)
      exact Finset.mem_Icc.mpr ⟨hxI.1.le, hxI.2⟩
  · rw [Finset.prod_insert hnS]
    exact hsqNat

lemma largestPrimeFactor_le_natSqrt_two_add_one_of_real {n : ℕ}
    (h : (largestPrimeFactor n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + 1) :
    largestPrimeFactor n ≤ Nat.sqrt (2 * n) + 1 := by
  have hsqrt : Real.sqrt (2 * (n : ℝ)) <
      ((Nat.sqrt (2 * n) : ℕ) : ℝ) + 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Real.real_sqrt_lt_nat_sqrt_succ (a := 2 * n))
  have hlt : (largestPrimeFactor n : ℝ) <
      ((Nat.sqrt (2 * n) + 2 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hltNat : largestPrimeFactor n < Nat.sqrt (2 * n) + 2 := by
    exact_mod_cast hlt
  omega

theorem t_le_gsEndpoint_of_small_largestPrimeFactor {n : ℕ} (hn : 16 ≤ n)
    (hsmall : (largestPrimeFactor n : ℝ) ≤
      Real.sqrt (2 * (n : ℝ)) + 1) :
    t n ≤ gsEndpoint n := by
  have hn1 : 1 < n := by omega
  have hn0 : 0 < n := by omega
  have hPnat := largestPrimeFactor_le_natSqrt_two_add_one_of_real hsmall
  have hscale : largestPrimeFactor n ≤ 4 * gsScale n :=
    hPnat.trans (sqrt_two_mul_add_one_le_four_gsScale hn)
  have htarget : SquareClassTarget n (gsEndpoint n) n := by
    apply squareClassTarget_of_prime_divisors hn0 hn0
    intro p hp hpn
    apply gs_prime_target hn hp
    exact (prime_le_largestPrimeFactor hn1 hp hpn).trans hscale
  exact t_le_of_admissible (admissible_of_squareClassTarget_self hn0 htarget)

/-- A fully discrete Granville--Selfridge walk gives the uniform square-root
branch (with a deliberately coarse absolute constant). -/
theorem erdos841_selfridge_sqrt_bound {n : ℕ} (hn : 16 ≤ n)
    (hsmall : (largestPrimeFactor n : ℝ) ≤
      Real.sqrt (2 * (n : ℝ)) + 1) :
    (t n : ℝ) ≤ 40 * Real.sqrt (n : ℝ) := by
  have ht := t_le_gsEndpoint_of_small_largestPrimeFactor hn hsmall
  have htR : (t n : ℝ) ≤ (gsEndpoint n : ℝ) := by exact_mod_cast ht
  have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num)]
    · exact_mod_cast (show 1 ≤ n by omega)
    · positivity
  calc
    (t n : ℝ) ≤ (gsEndpoint n : ℝ) := htR
    _ = 20 * ((Nat.sqrt n : ℝ) + 1) := by simp [gsEndpoint]
    _ ≤ 40 * Real.sqrt (n : ℝ) := by nlinarith

lemma admissible_three_mul (n : ℕ) : Admissible n (3 * n) := by
  by_cases hn : n = 0
  · subst n
    exact admissible_of_isSquare IsSquare.zero
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  refine ⟨{3 * n}, ?_, ?_⟩
  · simp only [Finset.singleton_subset_iff, Finset.mem_Icc]
    omega
  · simp only [Finset.prod_singleton]
    refine ⟨2 * n, ?_⟩
    ring

lemma t_le_three_mul (n : ℕ) : t n ≤ 3 * n :=
  t_le_of_admissible (admissible_three_mul n)

/-- The coarse square-root branch holds for every natural number; the
finite initial range is covered by the universal offset `3*n`. -/
theorem erdos841_selfridge_sqrt_bound_all {n : ℕ}
    (hsmall : (largestPrimeFactor n : ℝ) ≤
      Real.sqrt (2 * (n : ℝ)) + 1) :
    (t n : ℝ) ≤ 40 * Real.sqrt (n : ℝ) := by
  by_cases hn16 : 16 ≤ n
  · exact erdos841_selfridge_sqrt_bound hn16 hsmall
  by_cases hn0 : n = 0
  · subst n
    rw [(t_eq_zero_iff 0).2 IsSquare.zero]
    norm_num
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnlt : n < 16 := Nat.lt_of_not_ge hn16
  have ht : (t n : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast t_le_three_mul n
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtLt : Real.sqrt (n : ℝ) < 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    exact_mod_cast hnlt
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
  nlinarith

/-! ## The elementary case of the universal lower-bound argument -/

/-- BPZ Lemma 6.1.  A positive integral point on
`y² = x(x+J)` has `x ≤ J²`.  The proof uses the factorization
`J² = (2x+J-2y)(2x+J+2y)`. -/
theorem two_factor_square_bound {x y J : ℕ} (hx : 0 < x) (hJ : 0 < J)
    (heq : y ^ 2 = x * (x + J)) : x ≤ J ^ 2 := by
  have heqZ : (y : ℤ) ^ 2 = (x : ℤ) * ((x : ℤ) + (J : ℤ)) := by
    exact_mod_cast heq
  let A : ℤ := 2 * x + J
  let B : ℤ := 2 * y
  have hdiff : A ^ 2 - B ^ 2 = (J : ℤ) ^ 2 := by
    dsimp [A, B]
    nlinarith
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hABpos : 0 < A + B := by linarith
  have hAltB : B < A := by
    by_contra h
    have hBA : A ≤ B := le_of_not_gt h
    nlinarith [sq_nonneg (J : ℤ)]
  have hone : (1 : ℤ) ≤ A - B := by omega
  have hfactor : (A - B) * (A + B) = (J : ℤ) ^ 2 := by
    nlinarith
  have hsum : A + B ≤ (J : ℤ) ^ 2 := by
    nlinarith
  have hxZ : (x : ℤ) ≤ (J : ℤ) ^ 2 := by
    dsimp [A, B] at hsum
    omega
  exact_mod_cast hxZ

/-- In a decomposition `m = z² b` with squarefree `b`, every prime
dividing `b` occurs to odd valuation in `m`. -/
lemma odd_factorization_of_sq_mul_squarefree
    {m z b p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hb : Squarefree b) (hdecomp : z ^ 2 * b = m) (hpdiv : p ∣ b) :
    Odd (m.factorization p) := by
  have hprod0 : z ^ 2 * b ≠ 0 := hdecomp.symm ▸ hm.ne'
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    simp at hprod0
  have hb0 : b ≠ 0 := by
    intro hbz
    subst b
    simp at hprod0
  have hbp : b.factorization p = 1 := by
    have hpos := hp.factorization_pos_of_dvd hb0 hpdiv
    have hle := (Nat.squarefree_iff_factorization_le_one hb0).mp hb p
    omega
  have hfac := congrArg (fun F : ℕ →₀ ℕ ↦ F p)
    (Nat.factorization_mul (pow_ne_zero 2 hz0) hb0)
  rw [hdecomp] at hfac
  have hpowfac : (z ^ 2).factorization p = 2 * z.factorization p := by
    simpa using congrArg (fun F : ℕ →₀ ℕ ↦ F p) (Nat.factorization_pow z 2)
  simp only [Finsupp.add_apply] at hfac
  rw [hpowfac, hbp] at hfac
  exact ⟨z.factorization p, by omega⟩

/-- A prime absent from the squarefree factor has even valuation in the
original integer. -/
lemma even_factorization_of_sq_mul_not_dvd
    {m z b p : ℕ} (hm : 0 < m)
    (hdecomp : z ^ 2 * b = m) (hpndiv : ¬p ∣ b) :
    Even (m.factorization p) := by
  have hprod0 : z ^ 2 * b ≠ 0 := hdecomp.symm ▸ hm.ne'
  have hz0 : z ≠ 0 := by
    intro hz
    subst z
    simp at hprod0
  have hb0 : b ≠ 0 := by
    intro hbz
    subst b
    simp at hprod0
  have hbp : b.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpndiv
  have hfac := congrArg (fun F : ℕ →₀ ℕ ↦ F p)
    (Nat.factorization_mul (pow_ne_zero 2 hz0) hb0)
  rw [hdecomp] at hfac
  have hpowfac : (z ^ 2).factorization p = 2 * z.factorization p := by
    simpa using congrArg (fun F : ℕ →₀ ℕ ↦ F p) (Nat.factorization_pow z 2)
  simp only [Finsupp.add_apply] at hfac
  rw [hpowfac, hbp] at hfac
  exact ⟨z.factorization p, by omega⟩

/-- If a product is square, every prime appearing in one squarefree part
appears in another one as well. -/
theorem exists_other_squarefree_factor_dvd
    {I : Finset ℕ} {f z b : ℕ → ℕ} {i p : ℕ}
    (hi : i ∈ I) (hfpos : ∀ j ∈ I, 0 < f j)
    (hbfree : ∀ j ∈ I, Squarefree (b j))
    (hdecomp : ∀ j ∈ I, z j ^ 2 * b j = f j)
    (hsquare : IsSquare (∏ j ∈ I, f j))
    (hp : p.Prime) (hpbi : p ∣ b i) :
    ∃ j ∈ I, j ≠ i ∧ p ∣ b j := by
  by_contra hno
  push Not at hno
  have hprod0 : (∏ j ∈ I, f j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj ↦ (hfpos j hj).ne'
  have hsumEven : Even (∑ j ∈ I, (f j).factorization p) := by
    have hall := (isSquare_iff_even_factorization hprod0).mp hsquare p
    rw [Nat.factorization_prod_apply (fun j hj ↦ (hfpos j hj).ne')] at hall
    exact hall
  have hiOdd : Odd ((f i).factorization p) :=
    odd_factorization_of_sq_mul_squarefree (hfpos i hi) hp (hbfree i hi)
      (hdecomp i hi) hpbi
  have hrestEven : Even (∑ j ∈ I.erase i, (f j).factorization p) := by
    apply Finset.even_sum
    intro j hj
    have hjI := Finset.mem_of_mem_erase hj
    have hji := (Finset.mem_erase.mp hj).1
    exact even_factorization_of_sq_mul_not_dvd (hfpos j hjI) (hdecomp j hjI)
      (hno j hjI hji)
  have hsumOdd : Odd (∑ j ∈ I, (f j).factorization p) := by
    rw [← Finset.sum_erase_add _ _ hi]
    exact hrestEven.add_odd hiOdd
  exact (Nat.not_even_iff_odd.mpr hsumOdd) hsumEven

/-- In BPZ's shifted-product curve, all primes in every squarefree part
are at most the shift bound `J`. -/
theorem prime_le_shift_bound_of_squarefree_factors
    {n J : ℕ} {I : Finset ℕ} {z b : ℕ → ℕ}
    (hn : 0 < n) (hI : I ⊆ Finset.Icc 0 J)
    (hbfree : ∀ j ∈ I, Squarefree (b j))
    (hdecomp : ∀ j ∈ I, z j ^ 2 * b j = n + j)
    (hsquare : IsSquare (∏ j ∈ I, (n + j)))
    {i p : ℕ} (hi : i ∈ I) (hp : p.Prime) (hpbi : p ∣ b i) :
    p ≤ J := by
  obtain ⟨j, hjI, hji, hpbj⟩ := exists_other_squarefree_factor_dvd
    hi (fun j _ ↦ by omega) hbfree hdecomp hsquare hp hpbi
  have hbdiv (u : ℕ) (hu : u ∈ I) : b u ∣ n + u := by
    rw [← hdecomp u hu]
    exact ⟨z u ^ 2, by ac_rfl⟩
  have hpi : p ∣ n + i := hpbi.trans (hbdiv i hi)
  have hpj : p ∣ n + j := hpbj.trans (hbdiv j hjI)
  have hiBound := (Finset.mem_Icc.mp (hI hi)).2
  have hjBound := (Finset.mem_Icc.mp (hI hjI)).2
  rcases lt_or_gt_of_ne hji with hij | hji'
  · have hpdiff : p ∣ i - j := by
      have hd := Nat.dvd_sub hpi hpj
      convert hd using 1 <;> omega
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hpdiff).trans (by omega)
  · have hpdiff : p ∣ j - i := by
      have hd := Nat.dvd_sub hpj hpi
      convert hd using 1 <;> omega
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hji') hpdiff).trans (by omega)

/-- Product of the nonzero distances from one selected shift to all the
other shifts in the ambient witness. -/
def shiftDifferenceProduct (I : Finset ℕ) (i : ℕ) : ℕ :=
  ∏ j ∈ I.erase i, Nat.dist i j

lemma shiftDifferenceProduct_pos {I : Finset ℕ} {i : ℕ} (hi : i ∈ I) :
    0 < shiftDifferenceProduct I i := by
  rw [Nat.pos_iff_ne_zero, shiftDifferenceProduct,
    Finset.prod_ne_zero_iff]
  intro j hj
  exact (Nat.dist_pos_of_ne (Finset.mem_erase.mp hj).1.symm).ne'

/-- The squarefree part at a shift divides the product of all its nonzero
distances to the other shifts.  This retains the full parity information of
the square witness and is stronger than merely saying that its primes are at
most the endpoint. -/
theorem squarefree_factor_dvd_shiftDifferenceProduct
    {n : ℕ} {I : Finset ℕ} {z b : ℕ → ℕ}
    (hn : 0 < n)
    (hbfree : ∀ j ∈ I, Squarefree (b j))
    (hdecomp : ∀ j ∈ I, z j ^ 2 * b j = n + j)
    (hsquare : IsSquare (∏ j ∈ I, (n + j)))
    {i : ℕ} (hi : i ∈ I) :
    b i ∣ shiftDifferenceProduct I i := by
  have hprod : shiftDifferenceProduct I i ≠ 0 :=
    (shiftDifferenceProduct_pos hi).ne'
  rw [← Nat.prod_primeFactors_of_squarefree (hbfree i hi),
    Nat.prod_primeFactors_dvd_iff hprod]
  intro p hpbi
  have hp : p.Prime := (Nat.mem_primeFactors.mp hpbi).1
  have hpdivbi : p ∣ b i := (Nat.mem_primeFactors.mp hpbi).2.1
  obtain ⟨j, hjI, hji, hpdivbj⟩ := exists_other_squarefree_factor_dvd
    hi (fun j _ ↦ by omega) hbfree hdecomp hsquare hp hpdivbi
  have hbdiv (u : ℕ) (hu : u ∈ I) : b u ∣ n + u := by
    rw [← hdecomp u hu]
    exact ⟨z u ^ 2, by ac_rfl⟩
  have hpi : p ∣ n + i := hpdivbi.trans (hbdiv i hi)
  have hpj : p ∣ n + j := hpdivbj.trans (hbdiv j hjI)
  have hpdist : p ∣ Nat.dist i j := by
    rcases lt_or_gt_of_ne hji.symm with hij | hji'
    · rw [Nat.dist_eq_sub_of_le hij.le]
      have hd := Nat.dvd_sub hpj hpi
      convert hd using 1 <;> omega
    · rw [Nat.dist_eq_sub_of_le_right hji'.le]
      have hd := Nat.dvd_sub hpi hpj
      convert hd using 1 <;> omega
  have hjErase : j ∈ I.erase i := Finset.mem_erase.mpr ⟨hji, hjI⟩
  have hpProd : p ∣ shiftDifferenceProduct I i :=
    hpdist.trans (by
      rw [shiftDifferenceProduct]
      exact Finset.dvd_prod_of_mem (fun j ↦ Nat.dist i j) hjErase)
  exact Nat.mem_primeFactors.mpr ⟨hp, hpProd, hprod⟩

/-- Consequently a squarefree part in an interval of endpoint `J` is at
most `J^(I.card-1)`.  In particular, any three chosen factors produce a
degree-eight radical field whose discriminant depends polynomially on this
explicit witness-size majorant. -/
theorem squarefree_factor_le_shiftBound_pow_card_sub_one
    {n J : ℕ} {I : Finset ℕ} {z b : ℕ → ℕ}
    (hn : 0 < n) (hI : I ⊆ Finset.Icc 0 J)
    (hbfree : ∀ j ∈ I, Squarefree (b j))
    (hdecomp : ∀ j ∈ I, z j ^ 2 * b j = n + j)
    (hsquare : IsSquare (∏ j ∈ I, (n + j)))
    {i : ℕ} (hi : i ∈ I) :
    b i ≤ J ^ (I.card - 1) := by
  have hdvd := squarefree_factor_dvd_shiftDifferenceProduct
    hn hbfree hdecomp hsquare hi
  have hpos := shiftDifferenceProduct_pos hi
  calc
    b i ≤ shiftDifferenceProduct I i := Nat.le_of_dvd hpos hdvd
    _ ≤ ∏ _j ∈ I.erase i, J := by
      rw [shiftDifferenceProduct]
      refine Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) ?_
      intro j hj
      have hjI := Finset.mem_of_mem_erase hj
      have hiJ := (Finset.mem_Icc.mp (hI hi)).2
      have hjJ := (Finset.mem_Icc.mp (hI hjI)).2
      unfold Nat.dist
      omega
    _ = J ^ (I.card - 1) := by
      rw [Finset.prod_const, Finset.card_erase_of_mem hi]

/-- The squarefree factors attached to two distinct shifts have gcd at
most the shift bound.  This is the second elementary input to BPZ Lemma
6.4. -/
theorem gcd_squarefree_factors_le_shift_bound
    {n J : ℕ} {I : Finset ℕ} {z b : ℕ → ℕ}
    (hI : I ⊆ Finset.Icc 0 J)
    (hdecomp : ∀ j ∈ I, z j ^ 2 * b j = n + j)
    {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    Nat.gcd (b i) (b j) ≤ J := by
  have hbdiv (u : ℕ) (hu : u ∈ I) : b u ∣ n + u := by
    rw [← hdecomp u hu]
    exact ⟨z u ^ 2, by ac_rfl⟩
  have hgi : Nat.gcd (b i) (b j) ∣ n + i :=
    (Nat.gcd_dvd_left (b i) (b j)).trans (hbdiv i hi)
  have hgj : Nat.gcd (b i) (b j) ∣ n + j :=
    (Nat.gcd_dvd_right (b i) (b j)).trans (hbdiv j hj)
  have hiBound := (Finset.mem_Icc.mp (hI hi)).2
  have hjBound := (Finset.mem_Icc.mp (hI hj)).2
  rcases lt_or_gt_of_ne hij with hij' | hji
  · have hgd : Nat.gcd (b i) (b j) ∣ j - i := by
      have hd := Nat.dvd_sub hgj hgi
      convert hd using 1 <;> omega
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hij') hgd).trans (by omega)
  · have hgd : Nat.gcd (b i) (b j) ∣ i - j := by
      have hd := Nat.dvd_sub hgi hgj
      convert hd using 1 <;> omega
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hji) hgd).trans (by omega)

/-! ### Sparse squarefree supports -/

/-- A Bonferroni-type bound for a finite family of finite sets with
uniformly bounded pairwise intersections.  The deliberately coarse
`I.card ^ 2` term is the form needed in BPZ's sparse-support argument. -/
theorem sum_card_le_biUnion_card_add_sq_mul
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (S : ι → Finset α) (B : ℕ)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ B) :
    (∑ i ∈ I, (S i).card) ≤
      (I.biUnion S).card + I.card ^ 2 * B := by
  classical
  revert hinter
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      intro hinter
      have hinterI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          (S i ∩ S j).card ≤ B := by
        intro i hi j hj hij
        exact hinter i (by simp [hi]) j (by simp [hj]) hij
      have hIH := ih hinterI
      have hcross : (S a ∩ I.biUnion S).card ≤ I.card * B := by
        rw [Finset.inter_biUnion]
        apply Finset.card_biUnion_le_card_mul
        intro j hj
        exact hinter a (by simp) j (by simp [hj]) (by
          intro hja
          subst j
          exact ha hj)
      have hunion := Finset.card_union_add_card_inter (S a) (I.biUnion S)
      simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
        Finset.biUnion_insert] at *
      calc
        (S a).card + ∑ i ∈ I, (S i).card ≤
            (S a).card + ((I.biUnion S).card + I.card ^ 2 * B) :=
          Nat.add_le_add_left hIH _
        _ = ((S a).card + (I.biUnion S).card) + I.card ^ 2 * B := by omega
        _ = (((S a ∪ I.biUnion S).card +
              (S a ∩ I.biUnion S).card) + I.card ^ 2 * B) := by
          rw [hunion]
        _ ≤ (S a ∪ I.biUnion S).card +
              ((I.card + 1) ^ 2 * B) := by
          have hstep : (S a ∩ I.biUnion S).card + I.card ^ 2 * B ≤
              (I.card + 1) ^ 2 * B := by
            calc
              (S a ∩ I.biUnion S).card + I.card ^ 2 * B ≤
                  I.card * B + I.card ^ 2 * B := Nat.add_le_add_right hcross _
              _ ≤ (I.card + 1) ^ 2 * B := by nlinarith
          omega

/-- If the total support size is at most `M`, then three members have
support at most the average with the loss of two exceptional members.
The multiplication form avoids all rounding conventions. -/
theorem exists_three_small_of_sum_card_le
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {I : Finset ι} {S : ι → Finset α} {M : ℕ}
    (hI : 3 ≤ I.card) (hsum : (∑ i ∈ I, (S i).card) ≤ M) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ k ∈ I,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (I.card - 2) * (S i).card ≤ M ∧
      (I.card - 2) * (S j).card ≤ M ∧
      (I.card - 2) * (S k).card ≤ M := by
  classical
  let G := I.filter fun i ↦ (I.card - 2) * (S i).card ≤ M
  have hG : 3 ≤ G.card := by
    by_contra hnot
    have hGle : G.card ≤ 2 := by omega
    let D := I.filter fun i ↦ ¬(I.card - 2) * (S i).card ≤ M
    have hpart := Finset.card_filter_add_card_filter_not
      (s := I) (fun i ↦ (I.card - 2) * (S i).card ≤ M)
    have hDG : D.card + G.card = I.card := by
      simpa [D, G, Nat.add_comm] using hpart
    have hDcard : I.card - 2 ≤ D.card := by omega
    have hDnonempty : D.Nonempty := by
      apply Finset.card_pos.mp
      omega
    have hsumStrict : D.card * M <
        (I.card - 2) * ∑ i ∈ D, (S i).card := by
      calc
        D.card * M = ∑ _i ∈ D, M := by simp
        _ < ∑ i ∈ D, ((I.card - 2) * (S i).card) := by
          apply Finset.sum_lt_sum_of_nonempty hDnonempty
          intro i hi
          exact Nat.lt_of_not_ge (Finset.mem_filter.mp hi).2
        _ = (I.card - 2) * ∑ i ∈ D, (S i).card := by
          rw [Finset.mul_sum]
    have hfactorPos : 0 < I.card - 2 := by omega
    have hMlt : M < ∑ i ∈ D, (S i).card := by
      have hleft : (I.card - 2) * M ≤ D.card * M :=
        Nat.mul_le_mul_right M hDcard
      have hmul : (I.card - 2) * M <
          (I.card - 2) * ∑ i ∈ D, (S i).card := hleft.trans_lt hsumStrict
      exact (Nat.mul_lt_mul_left hfactorPos).mp hmul
    have hDsub : D ⊆ I := Finset.filter_subset _ _
    have hsumD : ∑ i ∈ D, (S i).card ≤ ∑ i ∈ I, (S i).card :=
      Finset.sum_le_sum_of_subset_of_nonneg hDsub (fun _ _ _ ↦ by omega)
    omega
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp (by omega : 2 < G.card)
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  have hk' := Finset.mem_filter.mp hk
  exact ⟨i, hi'.1, j, hj'.1, k, hk'.1, hij, hik, hjk,
    hi'.2, hj'.2, hk'.2⟩

/-- Abstract form of BPZ Lemma 6.4: three supports are sparse when the
ambient union and all pairwise overlaps are bounded. -/
theorem exists_three_sparse_supports
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    {I : Finset ι} {S : ι → Finset α} {N B : ℕ}
    (hI : 3 ≤ I.card)
    (hunion : (I.biUnion S).card ≤ N)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ B) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ k ∈ I,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (I.card - 2) * (S i).card ≤ N + I.card ^ 2 * B ∧
      (I.card - 2) * (S j).card ≤ N + I.card ^ 2 * B ∧
      (I.card - 2) * (S k).card ≤ N + I.card ^ 2 * B := by
  apply exists_three_small_of_sum_card_le hI
  exact (sum_card_le_biUnion_card_add_sq_mul I S B hinter).trans
    (Nat.add_le_add_right hunion _)

lemma primeFactors_card_le_log_two {n : ℕ} (hn : n ≠ 0) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc
    2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
      apply Finset.pow_card_le_prod
      intro p hp
      exact (Nat.mem_primeFactors.mp hp).1.two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- Number-theoretic specialization of the sparse-support lemma.  It is an
exact finite version of BPZ Lemma 6.4, with all constants visible. -/
theorem exists_three_sparse_squarefree_parts
    {ι : Type*} [DecidableEq ι] {I : Finset ι} {b : ι → ℕ} {J : ℕ}
    (hI : 3 ≤ I.card) (hbpos : ∀ i ∈ I, 0 < b i)
    (hprime : ∀ i ∈ I, ∀ p ∈ (b i).primeFactors, p ≤ J)
    (hgcd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.gcd (b i) (b j) ≤ J) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ k ∈ I,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (I.card - 2) * (b i).primeFactors.card ≤
        Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J ∧
      (I.card - 2) * (b j).primeFactors.card ≤
        Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J ∧
      (I.card - 2) * (b k).primeFactors.card ≤
        Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J := by
  have hunion : (I.biUnion fun i ↦ (b i).primeFactors).card ≤
      Nat.primeCounting J := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨i, hi, hpbi⟩ := Finset.mem_biUnion.mp hp
    exact Nat.mem_primesLE.mpr
      ⟨hprime i hi p hpbi, (Nat.mem_primeFactors.mp hpbi).1⟩
  have hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ((b i).primeFactors ∩ (b j).primeFactors).card ≤ Nat.log 2 J := by
    intro i hi j hj hij
    have hbi : b i ≠ 0 := (hbpos i hi).ne'
    have hbj : b j ≠ 0 := (hbpos j hj).ne'
    rw [← Nat.primeFactors_gcd hbi hbj]
    exact (primeFactors_card_le_log_two (Nat.gcd_pos_of_pos_left _ (hbpos i hi)).ne').trans
      (Nat.log_mono_right (hgcd i hi j hj hij))
  exact exists_three_sparse_supports hI hunion hinter

/-- The squarefree factor in a chosen decomposition `m = z² b`. -/
noncomputable def squarefreePart (m : ℕ) : ℕ :=
  Classical.choose (Nat.sq_mul_squarefree m)

/-- The square root factor accompanying `squarefreePart`. -/
noncomputable def squareRootPart (m : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Nat.sq_mul_squarefree m))

lemma squareRootPart_sq_mul_squarefreePart (m : ℕ) :
    squareRootPart m ^ 2 * squarefreePart m = m := by
  exact (Classical.choose_spec
    (Classical.choose_spec (Nat.sq_mul_squarefree m))).1

lemma squarefree_squarefreePart (m : ℕ) : Squarefree (squarefreePart m) := by
  exact (Classical.choose_spec
    (Classical.choose_spec (Nat.sq_mul_squarefree m))).2

lemma squarefreePart_pos {m : ℕ} (hm : 0 < m) : 0 < squarefreePart m := by
  have hdecomp := squareRootPart_sq_mul_squarefreePart m
  by_contra h
  have hz : squarefreePart m = 0 := Nat.eq_zero_of_not_pos h
  rw [hz] at hdecomp
  simp at hdecomp
  omega

lemma squareRootPart_pos {m : ℕ} (hm : 0 < m) : 0 < squareRootPart m := by
  have hdecomp := squareRootPart_sq_mul_squarefreePart m
  by_contra h
  have hz : squareRootPart m = 0 := Nat.eq_zero_of_not_pos h
  rw [hz] at hdecomp
  simp at hdecomp
  omega

/-- A squarefree integer supported on primes at most `J` is bounded by the
corresponding power of `J`.  This is the coefficient-size bridge in the
sparse-support argument. -/
lemma squarefree_le_pow_primeFactors_card {b J : ℕ} (hb : Squarefree b)
    (hprime : ∀ p ∈ b.primeFactors, p ≤ J) :
    b ≤ J ^ b.primeFactors.card := by
  calc
    b = ∏ p ∈ b.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hb).symm
    _ ≤ ∏ _p ∈ b.primeFactors, J := by
      refine Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) ?_
      intro p hp
      exact hprime p hp
    _ = J ^ b.primeFactors.card := by simp

/-- BPZ's three-shift reduction, before forming the auxiliary quartic.
Every sufficiently large shifted square-product witness contains three
distinct shifts whose squarefree parts have explicitly sparse prime
support. -/
theorem exists_three_sparse_shifts_of_square_product
    {n J : ℕ} {I : Finset ℕ} (hn : 0 < n)
    (hI : I ⊆ Finset.Icc 0 J) (hcard : 3 ≤ I.card)
    (hsquare : IsSquare (∏ j ∈ I, (n + j))) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ k ∈ I,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (I.card - 2) * (squarefreePart (n + i)).primeFactors.card ≤
        Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J ∧
      (I.card - 2) * (squarefreePart (n + j)).primeFactors.card ≤
        Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J ∧
      (I.card - 2) * (squarefreePart (n + k)).primeFactors.card ≤
        Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J := by
  let z : ℕ → ℕ := fun j ↦ squareRootPart (n + j)
  let b : ℕ → ℕ := fun j ↦ squarefreePart (n + j)
  have hbpos : ∀ j ∈ I, 0 < b j := by
    intro j hj
    exact squarefreePart_pos (by omega)
  have hbfree : ∀ j ∈ I, Squarefree (b j) := by
    intro j _
    exact squarefree_squarefreePart _
  have hdecomp : ∀ j ∈ I, z j ^ 2 * b j = n + j := by
    intro j _
    exact squareRootPart_sq_mul_squarefreePart _
  have hprime : ∀ i ∈ I, ∀ p ∈ (b i).primeFactors, p ≤ J := by
    intro i hi p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact prime_le_shift_bound_of_squarefree_factors hn hI hbfree hdecomp hsquare
      hi hp'.1 hp'.2.1
  have hgcd : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Nat.gcd (b i) (b j) ≤ J := by
    intro i hi j hj hij
    exact gcd_squarefree_factors_le_shift_bound hI hdecomp hi hj hij
  simpa [b] using
    (exists_three_sparse_squarefree_parts hcard hbpos hprime hgcd)

/-- Multiplicative form of the support-to-size estimate.  It retains the
factor `R` instead of dividing an integer support bound, which is exactly
what is needed when the quartic height is later raised to the `R`th power. -/
lemma squarefree_pow_le_of_mul_primeFactors_card_le
    {b J R E : ℕ} (hb : Squarefree b)
    (hprime : ∀ p ∈ b.primeFactors, p ≤ J)
    (hJ : 1 ≤ J) (hcard : R * b.primeFactors.card ≤ E) :
    b ^ R ≤ J ^ E := by
  have hbJ := squarefree_le_pow_primeFactors_card hb hprime
  calc
    b ^ R ≤ (J ^ b.primeFactors.card) ^ R :=
      Nat.pow_le_pow_left hbJ R
    _ = J ^ (b.primeFactors.card * R) := by rw [pow_mul]
    _ ≤ J ^ E := by
      apply Nat.pow_le_pow_right (by omega)
      simpa [Nat.mul_comm] using hcard

/-- The sparse-shift conclusion with coefficient-size information already
converted into power inequalities.  No rounding or real logarithm occurs in
this finite statement. -/
theorem exists_three_sparse_shifts_with_power_bounds
    {n J : ℕ} {I : Finset ℕ} (hn : 0 < n)
    (hI : I ⊆ Finset.Icc 0 J) (hcard : 3 ≤ I.card)
    (hJ : 1 ≤ J) (hsquare : IsSquare (∏ j ∈ I, (n + j))) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ k ∈ I,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      squarefreePart (n + i) ^ (I.card - 2) ≤
        J ^ (Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J) ∧
      squarefreePart (n + j) ^ (I.card - 2) ≤
        J ^ (Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J) ∧
      squarefreePart (n + k) ^ (I.card - 2) ≤
        J ^ (Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J) := by
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hiCard, hjCard, hkCard⟩ :=
    exists_three_sparse_shifts_of_square_product hn hI hcard hsquare
  let z : ℕ → ℕ := fun a ↦ squareRootPart (n + a)
  let b : ℕ → ℕ := fun a ↦ squarefreePart (n + a)
  have hbfree : ∀ a ∈ I, Squarefree (b a) := by
    intro a _
    exact squarefree_squarefreePart _
  have hdecomp : ∀ a ∈ I, z a ^ 2 * b a = n + a := by
    intro a _
    exact squareRootPart_sq_mul_squarefreePart _
  have hprime : ∀ a ∈ I, ∀ p ∈ (b a).primeFactors, p ≤ J := by
    intro a ha p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact prime_le_shift_bound_of_squarefree_factors hn hI hbfree hdecomp hsquare
      ha hp'.1 hp'.2.1
  refine ⟨i, hi, j, hj, k, hk, hij, hik, hjk, ?_, ?_, ?_⟩
  · exact squarefree_pow_le_of_mul_primeFactors_card_le
      (squarefree_squarefreePart _) (hprime i hi) hJ hiCard
  · exact squarefree_pow_le_of_mul_primeFactors_card_le
      (squarefree_squarefreePart _) (hprime j hj) hJ hjCard
  · exact squarefree_pow_le_of_mul_primeFactors_card_le
      (squarefree_squarefreePart _) (hprime k hk) hJ hkCard

/-- Sparse shifts selected from a prescribed subfamily.  The square-product
hypothesis belongs to the full witness `I`; this is essential because a
subfamily need not itself have square product. -/
theorem exists_three_sparse_shifts_with_power_bounds_subfamily
    {n J : ℕ} {I K : Finset ℕ} (hn : 0 < n)
    (hI : I ⊆ Finset.Icc 0 J) (hK : K ⊆ I) (hcard : 3 ≤ K.card)
    (hJ : 1 ≤ J) (hsquare : IsSquare (∏ j ∈ I, (n + j))) :
    ∃ i ∈ K, ∃ j ∈ K, ∃ k ∈ K,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      squarefreePart (n + i) ^ (K.card - 2) ≤
        J ^ (Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J) ∧
      squarefreePart (n + j) ^ (K.card - 2) ≤
        J ^ (Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J) ∧
      squarefreePart (n + k) ^ (K.card - 2) ≤
        J ^ (Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J) := by
  let z : ℕ → ℕ := fun a ↦ squareRootPart (n + a)
  let b : ℕ → ℕ := fun a ↦ squarefreePart (n + a)
  have hbpos : ∀ a ∈ K, 0 < b a := by
    intro a _
    exact squarefreePart_pos (by omega)
  have hbfreeI : ∀ a ∈ I, Squarefree (b a) := by
    intro a _
    exact squarefree_squarefreePart _
  have hdecompI : ∀ a ∈ I, z a ^ 2 * b a = n + a := by
    intro a _
    exact squareRootPart_sq_mul_squarefreePart _
  have hprime : ∀ a ∈ K, ∀ p ∈ (b a).primeFactors, p ≤ J := by
    intro a ha p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact prime_le_shift_bound_of_squarefree_factors hn hI hbfreeI hdecompI hsquare
      (hK ha) hp'.1 hp'.2.1
  have hgcd : ∀ a ∈ K, ∀ c ∈ K, a ≠ c → Nat.gcd (b a) (b c) ≤ J := by
    intro a ha c hc hac
    exact gcd_squarefree_factors_le_shift_bound hI hdecompI
      (hK ha) (hK hc) hac
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hiCard, hjCard, hkCard⟩ :=
    exists_three_sparse_squarefree_parts hcard hbpos hprime hgcd
  refine ⟨i, hi, j, hj, k, hk, hij, hik, hjk, ?_, ?_, ?_⟩
  · exact squarefree_pow_le_of_mul_primeFactors_card_le
      (squarefree_squarefreePart _) (hprime i hi) hJ hiCard
  · exact squarefree_pow_le_of_mul_primeFactors_card_le
      (squarefree_squarefreePart _) (hprime j hj) hJ hjCard
  · exact squarefree_pow_le_of_mul_primeFactors_card_le
      (squarefree_squarefreePart _) (hprime k hk) hJ hkCard

/-- Algebraic identity which turns three shifted squarefree decompositions
into BPZ's auxiliary quartic integral point.  Integer shifts are used so no
ordering convention is hidden in natural subtraction. -/
theorem three_shift_quartic_identity
    {n i j k zi zj zk bi bj bk : ℕ}
    (hi : zi ^ 2 * bi = n + i)
    (hj : zj ^ 2 * bj = n + j)
    (hk : zk ^ 2 * bk = n + k) :
    ((bj * bk * zj * zk : ℕ) : ℤ) ^ 2 =
      (bj * bk : ℤ) *
        ((bi : ℤ) * (zi : ℤ) ^ 2 + ((j : ℤ) - i)) *
        ((bi : ℤ) * (zi : ℤ) ^ 2 + ((k : ℤ) - i)) := by
  have hiZ : (zi : ℤ) ^ 2 * bi = n + i := by exact_mod_cast hi
  have hjZ : (zj : ℤ) ^ 2 * bj = n + j := by exact_mod_cast hj
  have hkZ : (zk : ℤ) ^ 2 * bk = n + k := by exact_mod_cast hk
  have hfacj : (bi : ℤ) * (zi : ℤ) ^ 2 + ((j : ℤ) - i) =
      (bj : ℤ) * (zj : ℤ) ^ 2 := by
    nlinarith
  have hfack : (bi : ℤ) * (zi : ℤ) ^ 2 + ((k : ℤ) - i) =
      (bk : ℤ) * (zk : ℤ) ^ 2 := by
    nlinarith
  rw [hfacj, hfack]
  push_cast
  ring

/-! ### The simultaneous Pell and decomposable-form bridge

The effective height theorem used below ultimately sends three root
factorizations to a system of two Pell-type equations.  We record that
algebraic bridge explicitly so that the remaining transcendence-theoretic
input is isolated from the BPZ combinatorics. -/

/-- The simultaneous Pell system occurring in Bérczes--Evertse--Győry,
specialized to integral coefficients and integral unknowns. -/
def SimultaneousPellZ
    (γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ) : Prop :=
  γ₁ * x₁ ^ 2 - γ₂ * x₂ ^ 2 = β₁₂ ∧
    γ₁ * x₁ ^ 2 - γ₃ * x₃ ^ 2 = β₁₃

/-- Three shifted squarefree decompositions satisfy the simultaneous Pell
system, with right-hand sides equal to the two shift differences. -/
lemma three_shift_simultaneousPellZ
    {n i j k zi zj zk bi bj bk : ℕ}
    (hi : zi ^ 2 * bi = n + i)
    (hj : zj ^ 2 * bj = n + j)
    (hk : zk ^ 2 * bk = n + k) :
    SimultaneousPellZ (bi : ℤ) (bj : ℤ) (bk : ℤ)
      ((i : ℤ) - j) ((i : ℤ) - k) zi zj zk := by
  have hiZ : (zi : ℤ) ^ 2 * bi = n + i := by exact_mod_cast hi
  have hjZ : (zj : ℤ) ^ 2 * bj = n + j := by exact_mod_cast hj
  have hkZ : (zk : ℤ) ^ 2 * bk = n + k := by exact_mod_cast hk
  dsimp [SimultaneousPellZ]
  constructor <;> nlinarith

/-- Three distinct shifts in a square-product witness furnish an explicit
simultaneous Pell system.  In addition to positivity and nonvanishing, the
three squarefree coefficients are bounded solely in terms of the interval
length and witness cardinality.  This packages the elementary input needed
by the fixed-degree logarithmic-form estimate. -/
theorem exists_three_direct_pell_data
    {n J : ℕ} {I : Finset ℕ}
    (hn : 0 < n) (hnlarge : 4 * J < n)
    (hI : I ⊆ Finset.Icc 0 J) (hcard : 3 ≤ I.card)
    (hsquare : IsSquare (∏ j ∈ I, (n + j))) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ k ∈ I,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      let γ₁ := squarefreePart (n + i)
      let γ₂ := squarefreePart (n + j)
      let γ₃ := squarefreePart (n + k)
      let x₁ := squareRootPart (n + i)
      let x₂ := squareRootPart (n + j)
      let x₃ := squareRootPart (n + k)
      let β₁₂ : ℤ := (i : ℤ) - j
      let β₁₃ : ℤ := (i : ℤ) - k
      SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
          β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ) ∧
        0 < γ₁ ∧ 0 < γ₂ ∧ 0 < γ₃ ∧
        γ₁ ≤ J ^ (I.card - 1) ∧
        γ₂ ≤ J ^ (I.card - 1) ∧
        γ₃ ≤ J ^ (I.card - 1) ∧
        0 < x₁ ∧ 0 < x₂ ∧ 0 < x₃ ∧
        β₁₂ ≠ 0 ∧ β₁₃ ≠ 0 ∧ β₁₃ - β₁₂ ≠ 0 ∧
        β₁₂.natAbs ≤ 2 * J ∧ β₁₃.natAbs ≤ 2 * J ∧
        (β₁₃ - β₁₂).natAbs ≤ 2 * J ∧
        2 * (2 * J) < γ₁ * x₁ ^ 2 := by
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < I.card)
  refine ⟨i, hi, j, hj, k, hk, hij, hik, hjk, ?_⟩
  dsimp only
  have hdi := squareRootPart_sq_mul_squarefreePart (n + i)
  have hdj := squareRootPart_sq_mul_squarefreePart (n + j)
  have hdk := squareRootPart_sq_mul_squarefreePart (n + k)
  have hγi := squarefreePart_pos (by omega : 0 < n + i)
  have hγj := squarefreePart_pos (by omega : 0 < n + j)
  have hγk := squarefreePart_pos (by omega : 0 < n + k)
  have hxi := squareRootPart_pos (by omega : 0 < n + i)
  have hxj := squareRootPart_pos (by omega : 0 < n + j)
  have hxk := squareRootPart_pos (by omega : 0 < n + k)
  have hbfree : ∀ a ∈ I, Squarefree (squarefreePart (n + a)) := by
    intro a _
    exact squarefree_squarefreePart _
  have hdecomp : ∀ a ∈ I,
      squareRootPart (n + a) ^ 2 * squarefreePart (n + a) = n + a := by
    intro a _
    exact squareRootPart_sq_mul_squarefreePart _
  have hγiH := squarefree_factor_le_shiftBound_pow_card_sub_one
    hn hI hbfree hdecomp hsquare hi
  have hγjH := squarefree_factor_le_shiftBound_pow_card_sub_one
    hn hI hbfree hdecomp hsquare hj
  have hγkH := squarefree_factor_le_shiftBound_pow_card_sub_one
    hn hI hbfree hdecomp hsquare hk
  have hPell := three_shift_simultaneousPellZ hdi hdj hdk
  have hiJ := (Finset.mem_Icc.mp (hI hi)).2
  have hjJ := (Finset.mem_Icc.mp (hI hj)).2
  have hkJ := (Finset.mem_Icc.mp (hI hk)).2
  have hβ₁₂ : (i : ℤ) - (j : ℤ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hij)
  have hβ₁₃ : (i : ℤ) - (k : ℤ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hik)
  have hβ₂₃ : ((i : ℤ) - k) - ((i : ℤ) - j) ≠ 0 := by
    have : (j : ℤ) ≠ k := by exact_mod_cast hjk
    omega
  have hJ₁₂ : ((i : ℤ) - j).natAbs ≤ 2 * J := by
    calc
      ((i : ℤ) - j).natAbs ≤ (i : ℤ).natAbs + (j : ℤ).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * J := by simp only [Int.natAbs_natCast]; omega
  have hJ₁₃ : ((i : ℤ) - k).natAbs ≤ 2 * J := by
    calc
      ((i : ℤ) - k).natAbs ≤ (i : ℤ).natAbs + (k : ℤ).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * J := by simp only [Int.natAbs_natCast]; omega
  have hJ₂₃ : (((i : ℤ) - k) - ((i : ℤ) - j)).natAbs ≤ 2 * J := by
    have heq : ((i : ℤ) - k) - ((i : ℤ) - j) = (j : ℤ) - k := by ring
    rw [heq]
    calc
      ((j : ℤ) - k).natAbs ≤ (j : ℤ).natAbs + (k : ℤ).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * J := by simp only [Int.natAbs_natCast]; omega
  have hlarge : 2 * (2 * J) <
      squarefreePart (n + i) * squareRootPart (n + i) ^ 2 := by
    calc
      2 * (2 * J) = 4 * J := by omega
      _ < n + i := by omega
      _ = squareRootPart (n + i) ^ 2 * squarefreePart (n + i) := hdi.symm
      _ = squarefreePart (n + i) * squareRootPart (n + i) ^ 2 :=
        Nat.mul_comm _ _
  exact ⟨hPell, hγi, hγj, hγk, hγiH, hγjH, hγkH,
    hxi, hxj, hxk, hβ₁₂, hβ₁₃, hβ₂₃, hJ₁₂, hJ₁₃, hJ₂₃, hlarge⟩

/-- One quadratic factor of the connected degree-six decomposable form
attached to a simultaneous Pell system. -/
def pellDifferenceZ (γa γb : ℤ) (a b : Fin 3) : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.C γa * MvPolynomial.X a ^ 2 -
    MvPolynomial.C γb * MvPolynomial.X b ^ 2

/-- The degree-six form used in BEG Proposition 3.12.  Over a field
containing the relevant square roots, its three quadratic factors split
into six linear forms. -/
def simultaneousPellFormZ (γ₁ γ₂ γ₃ : ℤ) : MvPolynomial (Fin 3) ℤ :=
  pellDifferenceZ γ₁ γ₂ 0 1 *
    pellDifferenceZ γ₁ γ₃ 0 2 *
    pellDifferenceZ γ₂ γ₃ 1 2

lemma pellDifferenceZ_isHomogeneous (γa γb : ℤ) (a b : Fin 3) :
    (pellDifferenceZ γa γb a b).IsHomogeneous 2 := by
  have ha : (MvPolynomial.C γa * MvPolynomial.X a ^ 2 :
      MvPolynomial (Fin 3) ℤ).IsHomogeneous 2 := by
    simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 3) γa).mul
      ((MvPolynomial.isHomogeneous_X (R := ℤ) a).pow 2)
  have hb : (MvPolynomial.C γb * MvPolynomial.X b ^ 2 :
      MvPolynomial (Fin 3) ℤ).IsHomogeneous 2 := by
    simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 3) γb).mul
      ((MvPolynomial.isHomogeneous_X (R := ℤ) b).pow 2)
  exact ha.sub hb

lemma simultaneousPellFormZ_isHomogeneous (γ₁ γ₂ γ₃ : ℤ) :
    (simultaneousPellFormZ γ₁ γ₂ γ₃).IsHomogeneous 6 := by
  simpa [simultaneousPellFormZ] using
    ((pellDifferenceZ_isHomogeneous γ₁ γ₂ 0 1).mul
      (pellDifferenceZ_isHomogeneous γ₁ γ₃ 0 2)).mul
        (pellDifferenceZ_isHomogeneous γ₂ γ₃ 1 2)

lemma simultaneousPellFormZ_ne_zero {γ₁ γ₂ γ₃ : ℤ}
    (hγ₁ : γ₁ ≠ 0) (hγ₂ : γ₂ ≠ 0) :
    simultaneousPellFormZ γ₁ γ₂ γ₃ ≠ 0 := by
  have h₁₂ : pellDifferenceZ γ₁ γ₂ 0 1 ≠ 0 := by
    intro hzero
    have h := congrArg (MvPolynomial.eval ![(1 : ℤ), 0, 0]) hzero
    apply hγ₁
    simpa [pellDifferenceZ] using h
  have h₁₃ : pellDifferenceZ γ₁ γ₃ 0 2 ≠ 0 := by
    intro hzero
    have h := congrArg (MvPolynomial.eval ![(1 : ℤ), 0, 0]) hzero
    apply hγ₁
    simpa [pellDifferenceZ] using h
  have h₂₃ : pellDifferenceZ γ₂ γ₃ 1 2 ≠ 0 := by
    intro hzero
    have h := congrArg (MvPolynomial.eval ![(0 : ℤ), 1, 0]) hzero
    apply hγ₂
    simpa [pellDifferenceZ] using h
  exact mul_ne_zero (mul_ne_zero h₁₂ h₁₃) h₂₃

lemma simultaneousPellFormZ_totalDegree {γ₁ γ₂ γ₃ : ℤ}
    (hγ₁ : γ₁ ≠ 0) (hγ₂ : γ₂ ≠ 0) :
    (simultaneousPellFormZ γ₁ γ₂ γ₃).totalDegree = 6 :=
  (simultaneousPellFormZ_isHomogeneous γ₁ γ₂ γ₃).totalDegree
    (simultaneousPellFormZ_ne_zero hγ₁ hγ₂)

/-- The minus linear factor `sₐ Xₐ - s_b X_b`. -/
def pellLinearMinus {K : Type*} [CommRing K]
    (sₐ s_b : K) (a b : Fin 3) : MvPolynomial (Fin 3) K :=
  MvPolynomial.C sₐ * MvPolynomial.X a -
    MvPolynomial.C s_b * MvPolynomial.X b

/-- The plus linear factor `sₐ Xₐ + s_b X_b`. -/
def pellLinearPlus {K : Type*} [CommRing K]
    (sₐ s_b : K) (a b : Fin 3) : MvPolynomial (Fin 3) K :=
  MvPolynomial.C sₐ * MvPolynomial.X a +
    MvPolynomial.C s_b * MvPolynomial.X b

/-- The explicit product of the six linear factors of the Pell form. -/
def simultaneousPellLinearProduct {K : Type*} [CommRing K]
    (s₁ s₂ s₃ : K) : MvPolynomial (Fin 3) K :=
  pellLinearMinus s₁ s₂ 0 1 * pellLinearPlus s₁ s₂ 0 1 *
    pellLinearMinus s₁ s₃ 0 2 * pellLinearPlus s₁ s₃ 0 2 *
    pellLinearMinus s₂ s₃ 1 2 * pellLinearPlus s₂ s₃ 1 2

/-- Over any field containing square roots of the three coefficients, the
degree-six Pell form splits into the six displayed linear factors. -/
lemma simultaneousPellFormZ_map_eq_linearProduct
    {K : Type*} [Field K] (γ₁ γ₂ γ₃ : ℤ) (s₁ s₂ s₃ : K)
    (hs₁ : s₁ ^ 2 = (γ₁ : K))
    (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K)) :
    (simultaneousPellFormZ γ₁ γ₂ γ₃).map (Int.castRingHom K) =
      simultaneousPellLinearProduct s₁ s₂ s₃ := by
  simp only [simultaneousPellFormZ, pellDifferenceZ, map_mul, map_sub,
    MvPolynomial.map_C, map_pow, MvPolynomial.map_X,
    simultaneousPellLinearProduct, pellLinearMinus, pellLinearPlus]
  have hs₁' : (Int.castRingHom K) γ₁ = s₁ ^ 2 := by simpa using hs₁.symm
  have hs₂' : (Int.castRingHom K) γ₂ = s₂ ^ 2 := by simpa using hs₂.symm
  have hs₃' : (Int.castRingHom K) γ₃ = s₃ ^ 2 := by simpa using hs₃.symm
  rw [hs₁', hs₂', hs₃']
  simp only [map_pow]
  ring

lemma pellLinearMinus_isHomogeneous {K : Type*} [CommRing K]
    (sₐ s_b : K) (a b : Fin 3) :
    (pellLinearMinus sₐ s_b a b).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sub
  · simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 3) sₐ).mul
      (MvPolynomial.isHomogeneous_X (R := K) a)
  · simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 3) s_b).mul
      (MvPolynomial.isHomogeneous_X (R := K) b)

lemma pellLinearPlus_isHomogeneous {K : Type*} [CommRing K]
    (sₐ s_b : K) (a b : Fin 3) :
    (pellLinearPlus sₐ s_b a b).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.add
  · simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 3) sₐ).mul
      (MvPolynomial.isHomogeneous_X (R := K) a)
  · simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 3) s_b).mul
      (MvPolynomial.isHomogeneous_X (R := K) b)

/-! The next four identities are the triangular connections between the
six factors.  In particular, starting with the two factors on the edges
`0--1` and `1--2`, each factor on `0--2` is obtained by a three-term linear
relation, and conversely the plus factors recover the remaining edge. -/

lemma pellLinearMinus_zero_two_eq_add
    {K : Type*} [CommRing K] (s₁ s₂ s₃ : K) :
    pellLinearMinus s₁ s₃ 0 2 =
      pellLinearMinus s₁ s₂ 0 1 + pellLinearMinus s₂ s₃ 1 2 := by
  simp [pellLinearMinus]

lemma pellLinearPlus_zero_two_eq_add
    {K : Type*} [CommRing K] (s₁ s₂ s₃ : K) :
    pellLinearPlus s₁ s₃ 0 2 =
      pellLinearMinus s₁ s₂ 0 1 + pellLinearPlus s₂ s₃ 1 2 := by
  simp [pellLinearMinus, pellLinearPlus]
  ring

lemma pellLinearPlus_one_two_eq_sub
    {K : Type*} [CommRing K] (s₁ s₂ s₃ : K) :
    pellLinearPlus s₂ s₃ 1 2 =
      pellLinearPlus s₁ s₂ 0 1 - pellLinearMinus s₁ s₃ 0 2 := by
  simp [pellLinearMinus, pellLinearPlus]

lemma pellLinearMinus_one_two_eq_sub
    {K : Type*} [CommRing K] (s₁ s₂ s₃ : K) :
    pellLinearMinus s₂ s₃ 1 2 =
      pellLinearPlus s₁ s₂ 0 1 - pellLinearPlus s₁ s₃ 0 2 := by
  simp [pellLinearMinus, pellLinearPlus]

/-- The two edge factors used to start the triangular chain are linearly
independent.  This coordinate form avoids hiding the required nonvanishing
of the square roots in a dimension computation. -/
lemma pellLinearMinus_edge_relation_eq_zero
    {K : Type*} [Field K] {s₁ s₂ s₃ a b : K}
    (hs₁ : s₁ ≠ 0) (hs₃ : s₃ ≠ 0)
    (h : a • pellLinearMinus s₁ s₂ 0 1 +
        b • pellLinearMinus s₂ s₃ 1 2 = 0) :
    a = 0 ∧ b = 0 := by
  have h₀ := congrArg (MvPolynomial.eval ![(1 : K), 0, 0]) h
  have h₂ := congrArg (MvPolynomial.eval ![(0 : K), 0, 1]) h
  simp [pellLinearMinus] at h₀ h₂
  exact ⟨h₀.resolve_right hs₁, h₂.resolve_right hs₃⟩

/-- Over characteristic zero, three of the Pell factors are linearly
independent.  Since every factor uses only three variables, this proves
that the six-factor system has rank exactly three, as required by the
decomposable-form theorem. -/
lemma pellLinear_rank_three_relation_eq_zero
    {K : Type*} [Field K] [CharZero K] {s₁ s₂ s₃ a b c : K}
    (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0) (hs₃ : s₃ ≠ 0)
    (h : a • pellLinearMinus s₁ s₂ 0 1 +
          b • pellLinearMinus s₂ s₃ 1 2 +
          c • pellLinearPlus s₁ s₂ 0 1 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h₀ := congrArg (MvPolynomial.eval ![(1 : K), 0, 0]) h
  have h₁ := congrArg (MvPolynomial.eval ![(0 : K), 1, 0]) h
  have h₂ := congrArg (MvPolynomial.eval ![(0 : K), 0, 1]) h
  simp [pellLinearMinus, pellLinearPlus] at h₀ h₁ h₂
  have hb : b = 0 := by
    exact h₂.resolve_right hs₃
  have hac : a + c = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hs₁
    linear_combination h₀
  have hdif : -a + c = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hs₂
    rw [hb] at h₁
    linear_combination h₁
  have ha : a = 0 := by
    have htwo : (2 : K) * a = 0 := by
      linear_combination hac - hdif
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hc : c = 0 := by
    rw [ha, zero_add] at hac
    exact hac
  exact ⟨ha, hb, hc⟩

/-- A compact certificate containing exactly the factorization, nonvanishing,
rank-two starting pair, and triangular connections required for the
degree-six decomposable form. -/
def PellSixFactorCertificate {K : Type*} [Field K]
    (γ₁ γ₂ γ₃ : ℤ) : Prop :=
  ∃ s₁ s₂ s₃ : K,
    s₁ ^ 2 = (γ₁ : K) ∧ s₂ ^ 2 = (γ₂ : K) ∧ s₃ ^ 2 = (γ₃ : K) ∧
    s₁ ≠ 0 ∧ s₂ ≠ 0 ∧ s₃ ≠ 0 ∧
    (simultaneousPellFormZ γ₁ γ₂ γ₃).map (Int.castRingHom K) =
      simultaneousPellLinearProduct s₁ s₂ s₃ ∧
    (∀ a b : K,
      a • pellLinearMinus s₁ s₂ 0 1 +
          b • pellLinearMinus s₂ s₃ 1 2 = 0 →
        a = 0 ∧ b = 0) ∧
    (∀ a b c : K,
      a • pellLinearMinus s₁ s₂ 0 1 +
          b • pellLinearMinus s₂ s₃ 1 2 +
          c • pellLinearPlus s₁ s₂ 0 1 = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) ∧
    pellLinearMinus s₁ s₃ 0 2 =
      pellLinearMinus s₁ s₂ 0 1 + pellLinearMinus s₂ s₃ 1 2 ∧
    pellLinearPlus s₁ s₃ 0 2 =
      pellLinearMinus s₁ s₂ 0 1 + pellLinearPlus s₂ s₃ 1 2 ∧
    pellLinearPlus s₂ s₃ 1 2 =
      pellLinearPlus s₁ s₂ 0 1 - pellLinearMinus s₁ s₃ 0 2 ∧
    pellLinearMinus s₂ s₃ 1 2 =
      pellLinearPlus s₁ s₂ 0 1 - pellLinearPlus s₁ s₃ 0 2

/-- In an algebraically closed splitting field the Pell sextic has the full
connected six-factor certificate. -/
theorem simultaneousPellFormZ_connected_certificate
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (γ₁ γ₂ γ₃ : ℤ)
    (hγ₁ : (γ₁ : K) ≠ 0) (hγ₂ : (γ₂ : K) ≠ 0)
    (hγ₃ : (γ₃ : K) ≠ 0) :
    PellSixFactorCertificate (K := K) γ₁ γ₂ γ₃ := by
  obtain ⟨s₁, hs₁⟩ := IsAlgClosed.exists_pow_nat_eq (γ₁ : K) (by norm_num : 0 < 2)
  obtain ⟨s₂, hs₂⟩ := IsAlgClosed.exists_pow_nat_eq (γ₂ : K) (by norm_num : 0 < 2)
  obtain ⟨s₃, hs₃⟩ := IsAlgClosed.exists_pow_nat_eq (γ₃ : K) (by norm_num : 0 < 2)
  have hs₁ne : s₁ ≠ 0 := fun hs ↦ hγ₁ (by simpa [hs] using hs₁.symm)
  have hs₂ne : s₂ ≠ 0 := fun hs ↦ hγ₂ (by simpa [hs] using hs₂.symm)
  have hs₃ne : s₃ ≠ 0 := fun hs ↦ hγ₃ (by simpa [hs] using hs₃.symm)
  exact ⟨s₁, s₂, s₃, hs₁, hs₂, hs₃, hs₁ne, hs₂ne, hs₃ne,
    simultaneousPellFormZ_map_eq_linearProduct γ₁ γ₂ γ₃ s₁ s₂ s₃ hs₁ hs₂ hs₃,
    fun a b h ↦ pellLinearMinus_edge_relation_eq_zero hs₁ne hs₃ne h,
    fun a b c h ↦ pellLinear_rank_three_relation_eq_zero hs₁ne hs₂ne hs₃ne h,
    pellLinearMinus_zero_two_eq_add s₁ s₂ s₃,
    pellLinearPlus_zero_two_eq_add s₁ s₂ s₃,
    pellLinearPlus_one_two_eq_sub s₁ s₂ s₃,
    pellLinearMinus_one_two_eq_sub s₁ s₂ s₃⟩

/-- A chosen square root of an element of the base field is integral. -/
lemma isIntegral_sqRoot
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (s : L) (γ : K) (hs : s ^ 2 = algebraMap K L γ) : IsIntegral K s := by
  let p : Polynomial K := Polynomial.X ^ 2 - Polynomial.C γ
  have hpmonic : p.Monic := by
    simpa [p] using Polynomial.monic_X_pow_sub_C γ (by norm_num : 2 ≠ 0)
  have hproot : Polynomial.aeval s p = 0 := by
    simp [p, hs]
  exact ⟨p, hpmonic, hproot⟩

/-- Adjoining one chosen square root has degree at most two. -/
lemma finrank_adjoin_sqRoot_le_two
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (s : L) (γ : K) (hs : s ^ 2 = algebraMap K L γ) :
    Module.finrank K (IntermediateField.adjoin K ({s} : Set L)) ≤ 2 := by
  let p : Polynomial K := Polynomial.X ^ 2 - Polynomial.C γ
  have hpmonic : p.Monic := by
    simpa [p] using Polynomial.monic_X_pow_sub_C γ (by norm_num : 2 ≠ 0)
  have hproot : Polynomial.aeval s p = 0 := by
    simp [p, hs]
  have hsInt := isIntegral_sqRoot s γ hs
  rw [IntermediateField.adjoin.finrank hsInt]
  apply Polynomial.natDegree_le_of_degree_le
  exact (minpoly.min K s hpmonic hproot).trans (by
    simpa [p] using
      (le_of_eq (Polynomial.degree_X_pow_sub_C (R := K) (by norm_num : 0 < 2) γ)))

/-- The product of the three degrees in the successive square-root tower is
at most eight. -/
lemma finrank_sqRoot_tower_product_le_eight
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (s₁ s₂ s₃ : L) (γ₁ γ₂ γ₃ : K)
    (hs₁ : s₁ ^ 2 = algebraMap K L γ₁)
    (hs₂ : s₂ ^ 2 = algebraMap K L γ₂)
    (hs₃ : s₃ ^ 2 = algebraMap K L γ₃) :
    let K₁ := IntermediateField.adjoin K ({s₁} : Set L)
    let K₂ := IntermediateField.adjoin K₁ ({s₂} : Set L)
    let K₃ := IntermediateField.adjoin K₂ ({s₃} : Set L)
    Module.finrank K K₁ * Module.finrank K₁ K₂ *
      Module.finrank K₂ K₃ ≤ 8 := by
  dsimp only
  let K₁ := IntermediateField.adjoin K ({s₁} : Set L)
  have hs₂' : s₂ ^ 2 = algebraMap K₁ L (algebraMap K K₁ γ₂) := by
    simpa only [IntermediateField.algebraMap_apply,
      IntermediateField.coe_algebraMap_apply] using hs₂
  let K₂ := IntermediateField.adjoin K₁ ({s₂} : Set L)
  have hs₃' : s₃ ^ 2 =
      algebraMap K₂ L (algebraMap K₁ K₂ (algebraMap K K₁ γ₃)) := by
    simpa only [IntermediateField.algebraMap_apply,
      IntermediateField.coe_algebraMap_apply] using hs₃
  let K₃ := IntermediateField.adjoin K₂ ({s₃} : Set L)
  have h₁ : Module.finrank K K₁ ≤ 2 :=
    finrank_adjoin_sqRoot_le_two s₁ γ₁ hs₁
  have h₂ : Module.finrank K₁ K₂ ≤ 2 :=
    finrank_adjoin_sqRoot_le_two s₂ (algebraMap K K₁ γ₂) hs₂'
  have h₃ : Module.finrank K₂ K₃ ≤ 2 :=
    finrank_adjoin_sqRoot_le_two s₃
      (algebraMap K₁ K₂ (algebraMap K K₁ γ₃)) hs₃'
  exact Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃

/-- The field obtained by adjoining all three square roots at once has
degree at most eight over the base field.  This is the direct degree bound
needed by the number-field estimates; it follows from the submultiplicative
degree bound for composita. -/
lemma finrank_adjoin_three_sqRoots_le_eight
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (s₁ s₂ s₃ : L) (γ₁ γ₂ γ₃ : K)
    (hs₁ : s₁ ^ 2 = algebraMap K L γ₁)
    (hs₂ : s₂ ^ 2 = algebraMap K L γ₂)
    (hs₃ : s₃ ^ 2 = algebraMap K L γ₃) :
    Module.finrank K
      (IntermediateField.adjoin K ({s₁, s₂, s₃} : Set L)) ≤ 8 := by
  let K₁ := IntermediateField.adjoin K ({s₁} : Set L)
  let K₂ := IntermediateField.adjoin K ({s₂} : Set L)
  let K₃ := IntermediateField.adjoin K ({s₃} : Set L)
  have h₁ : Module.finrank K K₁ ≤ 2 :=
    finrank_adjoin_sqRoot_le_two s₁ γ₁ hs₁
  have h₂ : Module.finrank K K₂ ≤ 2 :=
    finrank_adjoin_sqRoot_le_two s₂ γ₂ hs₂
  have h₃ : Module.finrank K K₃ ≤ 2 :=
    finrank_adjoin_sqRoot_le_two s₃ γ₃ hs₃
  have hset : ({s₁, s₂, s₃} : Set L) =
      ({s₁} : Set L) ∪ ({s₂} : Set L) ∪ ({s₃} : Set L) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  rw [hset, IntermediateField.adjoin_union, IntermediateField.adjoin_union]
  calc
    Module.finrank K ↥((K₁ ⊔ K₂) ⊔ K₃ : IntermediateField K L) ≤
        Module.finrank K ↥(K₁ ⊔ K₂ : IntermediateField K L) *
          Module.finrank K K₃ :=
      IntermediateField.finrank_sup_le (K₁ ⊔ K₂) K₃
    _ ≤ (Module.finrank K K₁ * Module.finrank K K₂) *
        Module.finrank K K₃ :=
      Nat.mul_le_mul_right _ (IntermediateField.finrank_sup_le K₁ K₂)
    _ ≤ (2 * 2) * 2 := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
    _ = 8 := by norm_num

/-- In a number field, the unnormalised logarithmic height of a rational
integer is the field degree times its ordinary logarithm. -/
lemma numberField_logHeight_natCast
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Height.logHeight₁ (n : K) =
      (Module.finrank ℚ K : ℝ) * Real.log (n : ℝ) := by
  rw [NumberField.logHeight₁_eq]
  have hinf :
      (∑ v : NumberField.InfinitePlace K,
          v.mult * Real.posLog (v (n : K))) =
        (Module.finrank ℚ K : ℝ) * Real.log (n : ℝ) := by
    simp_rw [NumberField.InfinitePlace.map_natCast]
    change (∑ v : NumberField.InfinitePlace K,
        (v.mult : ℝ) * Real.posLog (n : ℝ)) = _
    rw [Real.log_of_nat_eq_posLog]
    rw [← Finset.sum_mul]
    have hsumNat :
        (∑ v : NumberField.InfinitePlace K, v.mult) =
          Module.finrank ℚ K := by
      rw [← NumberField.totalWeight_eq_sum_mult,
        NumberField.totalWeight_eq_finrank]
    rw [show (∑ v : NumberField.InfinitePlace K, (v.mult : ℝ)) =
        (Module.finrank ℚ K : ℝ) by exact_mod_cast hsumNat]
  have hfin :
      ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v (n : K)) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro v
    change Real.posLog (v (n : K)) = 0
    rw [Real.posLog_eq_zero_iff]
    rw [abs_of_nonneg (apply_nonneg v (n : K))]
    exact IsNonarchimedean.apply_natCast_le_one
      (NumberField.FinitePlace.add_le v)
  simpa only [hinf, hfin, add_zero]

/-- A chosen square root of a natural number has logarithmic height exactly
half that of its square, and hence is controlled by the natural coefficient
and the degree of the ambient number field. -/
lemma numberField_logHeight_sqRoot
    (K : Type*) [Field K] [NumberField K]
    (s : K) (γ : ℕ) (hs : s ^ 2 = (γ : K)) :
    2 * Height.logHeight₁ s =
      (Module.finrank ℚ K : ℝ) * Real.log (γ : ℝ) := by
  calc
    2 * Height.logHeight₁ s = Height.logHeight₁ (s ^ 2) := by
      simpa using (Height.logHeight₁_pow s 2).symm
    _ = Height.logHeight₁ (γ : K) := by rw [hs]
    _ = (Module.finrank ℚ K : ℝ) * Real.log (γ : ℝ) :=
      numberField_logHeight_natCast K γ

/-- In a number field of degree at most eight, the logarithmic height of a
chosen square root of a positive integer `γ ≤ H` is at most `4 log H`.
This is the explicit coefficient-height input for the six Pell factors. -/
lemma numberField_logHeight_sqRoot_le
    (K : Type*) [Field K] [NumberField K]
    (s : K) {γ H : ℕ} (hs : s ^ 2 = (γ : K))
    (hdeg : Module.finrank ℚ K ≤ 8) (hγ : 0 < γ) (hγH : γ ≤ H) :
    Height.logHeight₁ s ≤ 4 * Real.log (H : ℝ) := by
  have hH : 0 < H := hγ.trans_le hγH
  have hlogγ : 0 ≤ Real.log (γ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hγ)
  have hlogmono : Real.log (γ : ℝ) ≤ Real.log (H : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by change (0 : ℝ) < (γ : ℝ); exact_mod_cast hγ)
      (by change (0 : ℝ) < (H : ℝ); exact_mod_cast hH)
      (by exact_mod_cast hγH)
  have hdegR : (Module.finrank ℚ K : ℝ) ≤ 8 := by exact_mod_cast hdeg
  have hprod :
      (Module.finrank ℚ K : ℝ) * Real.log (γ : ℝ) ≤
        8 * Real.log (H : ℝ) := by
    exact mul_le_mul hdegR hlogmono hlogγ (by positivity)
  have hsHeight := numberField_logHeight_sqRoot K s γ hs
  nlinarith

/-! ### Values of the six factors and their finite-prime support

The decomposable-form argument ultimately applies unit-equation estimates
to the values, rather than merely to the formal linear factors.  The next
lemmas make that passage explicit for the specialized simultaneous Pell
system. -/

/-- The value of the minus factor `sₐ Xₐ - s_b X_b` at an integral
point. -/
def pellValueMinus {K : Type*} [CommRing K]
    (sₐ s_b : K) (xₐ x_b : ℤ) : K :=
  sₐ * (xₐ : K) - s_b * (x_b : K)

/-- The value of the plus factor `sₐ Xₐ + s_b X_b` at an integral
point. -/
def pellValuePlus {K : Type*} [CommRing K]
    (sₐ s_b : K) (xₐ x_b : ℤ) : K :=
  sₐ * (xₐ : K) + s_b * (x_b : K)

lemma pellValueMinus_zero_two_eq_add
    {K : Type*} [CommRing K] (s₁ s₂ s₃ : K) (x₁ x₂ x₃ : ℤ) :
    pellValueMinus s₁ s₃ x₁ x₃ =
      pellValueMinus s₁ s₂ x₁ x₂ +
        pellValueMinus s₂ s₃ x₂ x₃ := by
  simp [pellValueMinus]

lemma pellValuePlus_zero_two_eq_add
    {K : Type*} [CommRing K] (s₁ s₂ s₃ : K) (x₁ x₂ x₃ : ℤ) :
    pellValuePlus s₁ s₃ x₁ x₃ =
      pellValueMinus s₁ s₂ x₁ x₂ +
        pellValuePlus s₂ s₃ x₂ x₃ := by
  simp [pellValueMinus, pellValuePlus]
  ring

lemma pellValuePlus_one_two_eq_sub
    {K : Type*} [CommRing K] (s₁ s₂ s₃ : K) (x₁ x₂ x₃ : ℤ) :
    pellValuePlus s₂ s₃ x₂ x₃ =
      pellValuePlus s₁ s₂ x₁ x₂ -
        pellValueMinus s₁ s₃ x₁ x₃ := by
  simp [pellValueMinus, pellValuePlus]

lemma pellValueMinus_one_two_eq_sub
    {K : Type*} [CommRing K] (s₁ s₂ s₃ : K) (x₁ x₂ x₃ : ℤ) :
    pellValueMinus s₂ s₃ x₂ x₃ =
      pellValuePlus s₁ s₂ x₁ x₂ -
        pellValuePlus s₁ s₃ x₁ x₃ := by
  simp [pellValueMinus, pellValuePlus]

/-- The first triangular identity in normalized `S`-unit-equation form. -/
lemma pellValue_minus_unitEquation
    {K : Type*} [Field K] (s₁ s₂ s₃ : K) (x₁ x₂ x₃ : ℤ)
    (h₁₃ : pellValueMinus s₁ s₃ x₁ x₃ ≠ 0) :
    pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ +
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ = 1 := by
  rw [← add_div, ← pellValueMinus_zero_two_eq_add]
  exact div_self h₁₃

/-- The two values belonging to one edge multiply to the corresponding
Pell right-hand side. -/
lemma pellValueMinus_mul_plus
    {K : Type*} [Field K] [CharZero K]
    {sₐ s_b : K} {γₐ γ_b β xₐ x_b : ℤ}
    (hsₐ : sₐ ^ 2 = (γₐ : K)) (hs_b : s_b ^ 2 = (γ_b : K))
    (hPell : γₐ * xₐ ^ 2 - γ_b * x_b ^ 2 = β) :
    pellValueMinus sₐ s_b xₐ x_b * pellValuePlus sₐ s_b xₐ x_b =
      (β : K) := by
  calc
    pellValueMinus sₐ s_b xₐ x_b * pellValuePlus sₐ s_b xₐ x_b =
        sₐ ^ 2 * (xₐ : K) ^ 2 - s_b ^ 2 * (x_b : K) ^ 2 := by
      simp only [pellValueMinus, pellValuePlus]
      ring
    _ = ((γₐ * xₐ ^ 2 - γ_b * x_b ^ 2 : ℤ) : K) := by
      rw [hsₐ, hs_b]
      push_cast
      rfl
    _ = (β : K) := by rw [hPell]

/-! ### The distinguished real logarithmic form

At the real embedding sending all three radicals to their positive square
roots, the quotient of two minus factors is extremely close to the rational
number `β₁₂ / β₁₃`.  The following three lemmas isolate the exact
identity, its elementary absolute-value estimate, and the logarithmic form
which is fed into the archimedean linear-forms theorem. -/

/-- Exact cross-ratio identity behind the archimedean step in the
simultaneous-Pell reduction. -/
lemma simultaneousPell_real_normalized_gap_identity
    {A B C β₁₂ β₁₃ : ℝ}
    (h₁₂ : A ^ 2 - B ^ 2 = β₁₂)
    (h₁₃ : A ^ 2 - C ^ 2 = β₁₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hAB : A + B ≠ 0) (hBC : B + C ≠ 0) :
    β₁₃ / β₁₂ * ((A - B) / (A - C)) - 1 =
      (β₁₂ - β₁₃) / ((B + C) * (A + B)) := by
  have hAC : A - C ≠ 0 := by
    intro h
    have : A = C := sub_eq_zero.mp h
    rw [this] at h₁₃
    simp at h₁₃
    exact hβ₁₃ h₁₃.symm
  have hprod₁₂ : (A - B) * (A + B) = β₁₂ := by
    nlinarith
  have hprod₁₃ : (A - C) * (A + C) = β₁₃ := by
    nlinarith
  have hdiff : (C - B) * (B + C) = β₁₂ - β₁₃ := by
    nlinarith
  have hAmB : A - B ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod₁₂
    exact hβ₁₂ hprod₁₂.symm
  rw [← hprod₁₂, ← hprod₁₃]
  field_simp
  ring

/-- Pairwise distinct nonzero Pell right-hand sides make the normalized
real cross-ratio genuinely different from one. -/
lemma simultaneousPell_real_normalized_gap_ne_zero
    {A B C β₁₂ β₁₃ : ℝ}
    (h₁₂ : A ^ 2 - B ^ 2 = β₁₂)
    (h₁₃ : A ^ 2 - C ^ 2 = β₁₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβDiff : β₁₂ - β₁₃ ≠ 0)
    (hAB : A + B ≠ 0) (hBC : B + C ≠ 0) :
    β₁₃ / β₁₂ * ((A - B) / (A - C)) - 1 ≠ 0 := by
  rw [simultaneousPell_real_normalized_gap_identity h₁₂ h₁₃
    hβ₁₂ hβ₁₃ hAB hBC]
  exact div_ne_zero hβDiff (mul_ne_zero hBC hAB)

/-- If both Pell right-hand sides have size at most `J` and the common
positive term has square at least `2J`, the normalized cross ratio is at
most `2J/A²` away from one. -/
lemma simultaneousPell_real_normalized_gap_abs_le
    {A B C β₁₂ β₁₃ J : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h₁₂ : A ^ 2 - B ^ 2 = β₁₂)
    (h₁₃ : A ^ 2 - C ^ 2 = β₁₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hJ : 0 ≤ J) (hβ₁₂J : |β₁₂| ≤ J)
    (hβ₁₃J : |β₁₃| ≤ J)
    (hlarge : 2 * J ≤ A ^ 2) :
    |β₁₃ / β₁₂ * ((A - B) / (A - C)) - 1| ≤
      2 * J / A ^ 2 := by
  have hBsq : A ^ 2 - J ≤ B ^ 2 := by
    have hb : β₁₂ ≤ J := (le_abs_self β₁₂).trans hβ₁₂J
    nlinarith
  have hCsq : A ^ 2 - J ≤ C ^ 2 := by
    have hb : β₁₃ ≤ J := (le_abs_self β₁₃).trans hβ₁₃J
    nlinarith
  have hhalf : A ^ 2 / 2 ≤ A ^ 2 - J := by nlinarith
  have hBhalf : A / 2 ≤ B := by
    by_contra h
    have hlt : B < A / 2 := lt_of_not_ge h
    nlinarith [sq_nonneg (B - A / 2)]
  have hChalf : A / 2 ≤ C := by
    by_contra h
    have hlt : C < A / 2 := lt_of_not_ge h
    nlinarith [sq_nonneg (C - A / 2)]
  have hABpos : 0 < A + B := by positivity
  have hBCpos : 0 < B + C := by nlinarith
  have hden : A ^ 2 ≤ (B + C) * (A + B) := by nlinarith
  have hdiff : |β₁₂ - β₁₃| ≤ 2 * J := by
    calc
      |β₁₂ - β₁₃| ≤ |β₁₂| + |β₁₃| := abs_sub _ _
      _ ≤ J + J := add_le_add hβ₁₂J hβ₁₃J
      _ = 2 * J := by ring
  rw [simultaneousPell_real_normalized_gap_identity h₁₂ h₁₃ hβ₁₂ hβ₁₃
    hABpos.ne' hBCpos.ne']
  rw [abs_div, abs_of_pos (mul_pos hBCpos hABpos)]
  apply div_le_div₀ (mul_nonneg (by norm_num) hJ)
  · exact hdiff
  · positivity
  · exact hden

/-- Logarithmic upper bound for the nonzero normalized Pell cross ratio.
This is the exact elementary half of the eventual Matveev comparison. -/
lemma simultaneousPell_real_normalized_gap_log_le
    {A B C β₁₂ β₁₃ J : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h₁₂ : A ^ 2 - B ^ 2 = β₁₂)
    (h₁₃ : A ^ 2 - C ^ 2 = β₁₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβDiff : β₁₂ - β₁₃ ≠ 0)
    (hJ : 0 < J) (hβ₁₂J : |β₁₂| ≤ J)
    (hβ₁₃J : |β₁₃| ≤ J)
    (hlarge : 2 * J ≤ A ^ 2) :
    Real.log |β₁₃ / β₁₂ * ((A - B) / (A - C)) - 1| ≤
      Real.log (2 * J) - 2 * Real.log A := by
  have hABpos : 0 < A + B := by positivity
  have hBsq : A ^ 2 - J ≤ B ^ 2 := by
    have hb : β₁₂ ≤ J := (le_abs_self β₁₂).trans hβ₁₂J
    nlinarith
  have hhalf : A ^ 2 / 2 ≤ A ^ 2 - J := by nlinarith
  have hBhalf : A / 2 ≤ B := by
    by_contra h
    have hlt : B < A / 2 := lt_of_not_ge h
    nlinarith [sq_nonneg (B - A / 2)]
  have hCsq : A ^ 2 - J ≤ C ^ 2 := by
    have hc : β₁₃ ≤ J := (le_abs_self β₁₃).trans hβ₁₃J
    nlinarith
  have hChalf : A / 2 ≤ C := by
    by_contra h
    have hlt : C < A / 2 := lt_of_not_ge h
    nlinarith [sq_nonneg (C - A / 2)]
  have hBCpos : 0 < B + C := by nlinarith
  have hgapEq := simultaneousPell_real_normalized_gap_identity h₁₂ h₁₃
    hβ₁₂ hβ₁₃ hABpos.ne' hBCpos.ne'
  have hgapNe : β₁₃ / β₁₂ * ((A - B) / (A - C)) - 1 ≠ 0 := by
    rw [hgapEq]
    exact div_ne_zero hβDiff (mul_ne_zero hBCpos.ne' hABpos.ne')
  have hgap := simultaneousPell_real_normalized_gap_abs_le hA hB hC h₁₂ h₁₃
    hβ₁₂ hβ₁₃ hJ.le hβ₁₂J hβ₁₃J hlarge
  calc
    Real.log |β₁₃ / β₁₂ * ((A - B) / (A - C)) - 1| ≤
        Real.log (2 * J / A ^ 2) :=
      Real.log_le_log (abs_pos.mpr hgapNe) hgap
    _ = Real.log (2 * J) - 2 * Real.log A := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
      norm_num

/-- Raising a positive real number which is nontrivially within distance
one of `1` preserves a quantitative logarithmic upper bound.  This is the
elementary power-amplification step needed after the class-number and
bounded-unit indices have been introduced. -/
lemma real_log_abs_pow_sub_one_le
    {z : ℝ} {m : ℕ} (hm : 0 < m)
    (hgap : z - 1 ≠ 0) (hsmall : |z - 1| < 1) :
    Real.log |z ^ m - 1| ≤
      Real.log |z - 1| + Real.log (m : ℝ) +
        (m - 1 : ℕ) * Real.log 2 := by
  have hzpos : 0 < z := by
    have hleft := (abs_lt.mp hsmall).1
    linarith
  have hzle : |z| ≤ 2 := by
    calc
      |z| = |(z - 1) + 1| := by ring_nf
      _ ≤ |z - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hmax : max |z| |(1 : ℝ)| ≤ 2 := by simp [hzle]
  have hmaxpow : max |z| |(1 : ℝ)| ^ (m - 1) ≤
      (2 : ℝ) ^ (m - 1) := by
    exact pow_le_pow_left₀ (by positivity) hmax _
  have hraw := abs_pow_sub_pow_le (a := z) (b := (1 : ℝ)) (n := m)
  have habs : |z ^ m - 1| ≤
      |z - 1| * (m : ℝ) * (2 : ℝ) ^ (m - 1) := by
    simpa only [one_pow] using
      hraw.trans (mul_le_mul_of_nonneg_left hmaxpow (by positivity))
  have hzpow : z ^ m - 1 ≠ 0 := by
    intro h
    have hp : z ^ m = 1 := sub_eq_zero.mp h
    have hz1 : z = 1 :=
      (pow_eq_one_iff_of_nonneg hzpos.le hm.ne').mp hp
    exact hgap (sub_eq_zero.mpr hz1)
  have hprodpos : 0 < |z - 1| * (m : ℝ) * (2 : ℝ) ^ (m - 1) := by
    positivity
  calc
    Real.log |z ^ m - 1| ≤
        Real.log (|z - 1| * (m : ℝ) * (2 : ℝ) ^ (m - 1)) :=
      Real.log_le_log (abs_pos.mpr hzpow) habs
    _ = Real.log |z - 1| + Real.log (m : ℝ) +
          (m - 1 : ℕ) * Real.log 2 := by
      rw [Real.log_mul (mul_ne_zero (abs_ne_zero.mpr hgap)
          (by positivity)) (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
        Real.log_mul (abs_ne_zero.mpr hgap) (by positivity), Real.log_pow]

/-- Convenient transitive form of `real_log_abs_pow_sub_one_le`: an
available logarithmic upper bound for `z - 1` is preserved after taking a
positive natural power, up to the elementary geometric-sum loss. -/
lemma real_log_abs_pow_sub_one_le_of_log_gap
    {z L : ℝ} {m : ℕ} (hm : 0 < m)
    (hgap : z - 1 ≠ 0) (hsmall : |z - 1| < 1)
    (hlog : Real.log |z - 1| ≤ L) :
    Real.log |z ^ m - 1| ≤
      L + Real.log (m : ℝ) + (m - 1 : ℕ) * Real.log 2 := by
  calc
    Real.log |z ^ m - 1| ≤
        Real.log |z - 1| + Real.log (m : ℝ) +
          (m - 1 : ℕ) * Real.log 2 :=
      real_log_abs_pow_sub_one_le hm hgap hsmall
    _ ≤ L + Real.log (m : ℝ) + (m - 1 : ℕ) * Real.log 2 := by
      linarith

/-- A coarse square-root majorant for the real logarithm.  It is used to
absorb the residual `log log` term after applying a logarithmic-form lower
estimate. -/
lemma real_log_le_two_mul_sqrt (X : ℝ) (hX : 0 ≤ X) :
    Real.log X ≤ 2 * Real.sqrt X := by
  have hs := Real.log_le_self (Real.sqrt_nonneg X)
  have hlog := Real.log_sqrt hX
  nlinarith

/-- Elementary absorption for the final Baker comparison: a bound of the
form `X ≤ A(1 + log X)` with `X,A ≥ 1` is already a quadratic bound in
`A`. -/
lemma le_four_mul_sq_of_le_mul_one_add_log
    {X A : ℝ} (hX : 1 ≤ X) (hA : 1 ≤ A)
    (h : X ≤ A * (1 + Real.log X)) :
    X ≤ (4 * A) ^ 2 := by
  by_contra hnot
  have hgt : (4 * A) ^ 2 < X := lt_of_not_ge hnot
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hs2 : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX0
  have hAs0 : 0 ≤ A := le_trans zero_le_one hA
  have hs : 4 * A < Real.sqrt X := by nlinarith
  have hlog := real_log_le_two_mul_sqrt X hX0
  have hupper : A * (1 + Real.log X) ≤
      A * (1 + 2 * Real.sqrt X) := by
    gcongr
  have hstrict : A * (1 + 2 * Real.sqrt X) < X := by
    rw [← hs2]
    nlinarith
  linarith

/-- Near `1`, the multiplicative gap controls the ordinary real logarithm.
This is the elementary bridge from a Baker--Wüstholz lower bound for an
additive logarithmic form to the multiplicative gap constructed from the
Pell factors. -/
lemma abs_real_log_le_two_mul_abs_sub_one
    {z : ℝ} (hz : 0 < z) (hsmall : |z - 1| < 1 / 2) :
    |Real.log z| ≤ 2 * |z - 1| := by
  by_cases hzone : 1 ≤ z
  · rw [abs_of_nonneg (Real.log_nonneg hzone),
      abs_of_nonneg (sub_nonneg.mpr hzone)]
    have hlog := Real.log_le_sub_one_of_pos hz
    linarith
  · have hzlt : z < 1 := lt_of_not_ge hzone
    have hgap : |z - 1| = 1 - z := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hzhalf : 1 / 2 < z := by
      rw [hgap] at hsmall
      linarith
    have hinv : 0 < z⁻¹ := inv_pos.mpr hz
    have hlogInv := Real.log_le_sub_one_of_pos hinv
    have hlogNeg : Real.log z < 0 := Real.log_neg hz hzlt
    rw [Real.log_inv] at hlogInv
    rw [abs_of_neg hlogNeg, hgap]
    have hzinv : z⁻¹ - 1 = (1 - z) / z := by field_simp
    rw [hzinv] at hlogInv
    have hdiv : (1 - z) / z ≤ 2 * (1 - z) := by
      rw [div_le_iff₀ hz]
      have hnonneg : 0 ≤ 1 - z := by linarith
      nlinarith
    linarith

/-- Logarithmic version of `abs_real_log_le_two_mul_abs_sub_one`.  Any
lower bound for the nonzero additive form `log z` loses only `log 2` when
transferred to the multiplicative form `z - 1`. -/
lemma log_abs_sub_one_lower_of_log_form
    {z L : ℝ} (hz : 0 < z) (hz1 : z ≠ 1)
    (hsmall : |z - 1| < 1 / 2)
    (hform : L ≤ Real.log |Real.log z|) :
    L - Real.log 2 ≤ Real.log |z - 1| := by
  have hlogne : Real.log z ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hz hz1
  have hgapne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hbound := abs_real_log_le_two_mul_abs_sub_one hz hsmall
  have hmono : Real.log |Real.log z| ≤
      Real.log (2 * |z - 1|) := by
    apply Real.log_le_log (abs_pos.mpr hlogne)
    exact hbound
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (abs_ne_zero.mpr hgapne)] at hmono
  linarith

/-- For positive real algebraic numbers the principal complex logarithmic
form is exactly the real logarithm of the corresponding product of integer
powers. -/
lemma complex_linear_form_eq_real_log_zpow_product
    {n : ℕ} (α : Fin n → ℝ) (hα : ∀ i, 0 < α i)
    (b : Fin n → ℤ) :
    (∑ i, (b i : ℂ) * Complex.log (α i : ℂ)) =
      (Real.log (∏ i, α i ^ b i) : ℂ) := by
  rw [Real.log_prod]
  · simp_rw [Real.log_zpow]
    push_cast
    simp_rw [Complex.ofReal_log (hα _).le]
  · intro i _
    exact zpow_ne_zero _ (hα i).ne'

/-- Nontriviality of the multiplicative form supplies the nonzero
hypothesis in the additive Baker--Wüstholz statement. -/
lemma complex_linear_form_ne_zero_of_product_ne_one
    {n : ℕ} (α : Fin n → ℝ) (hα : ∀ i, 0 < α i)
    (b : Fin n → ℤ) (hprod : (∏ i, α i ^ b i) ≠ 1) :
    (∑ i, (b i : ℂ) * Complex.log (α i : ℂ)) ≠ 0 := by
  rw [complex_linear_form_eq_real_log_zpow_product α hα b]
  exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one
    (Finset.prod_pos fun i _ ↦ zpow_pos (hα i) _) hprod

namespace BakerWustholz

/-- The explicit constant in the Baker--Wüstholz lower bound for a linear
form in `n` logarithms over a number field of degree `d`. -/
noncomputable def constant (n d : ℕ) : ℝ :=
  18 * (n + 1).factorial * (n : ℝ) ^ (n + 1) *
    (32 * (d : ℝ)) ^ (n + 2) * Real.log (2 * n * d)

/-- The modified height used in the Baker--Wüstholz theorem.  Mathlib's
`logHeight₁` is unnormalised, so division by the field degree produces the
standard absolute height. -/
noncomputable def modifiedHeight
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (α : K) : ℝ :=
  let d : ℝ := Module.finrank ℚ K
  max (Height.logHeight₁ α / d)
    (max (‖Complex.log (φ α)‖ / d) (1 / d))

lemma constant_pos {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    0 < constant n d := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnd : (1 : ℝ) ≤ (n : ℝ) * (d : ℝ) :=
    by simpa using mul_le_mul hn1 hd1 zero_le_one (zero_le_one.trans hn1)
  have harg : (1 : ℝ) < 2 * (n : ℝ) * (d : ℝ) := by
    nlinarith
  rw [constant]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log (2 * (n : ℝ) * (d : ℝ)) := Real.log_pos harg
  positivity

lemma one_div_degree_le_modifiedHeight
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (α : K) :
    1 / (Module.finrank ℚ K : ℝ) ≤ modifiedHeight φ α := by
  rw [modifiedHeight]
  exact le_max_of_le_right (le_max_right _ _)

lemma modifiedHeight_pos
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (α : K) :
    0 < modifiedHeight φ α := by
  have hd : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  exact (div_pos zero_lt_one hd).trans_le
    (one_div_degree_le_modifiedHeight φ α)

lemma normalized_logHeight_le_modifiedHeight
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (α : K) :
    Height.logHeight₁ α / (Module.finrank ℚ K : ℝ) ≤
      modifiedHeight φ α := by
  rw [modifiedHeight]
  exact le_max_left _ _

lemma normalized_log_norm_le_modifiedHeight
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (α : K) :
    ‖Complex.log (φ α)‖ / (Module.finrank ℚ K : ℝ) ≤
      modifiedHeight φ α := by
  rw [modifiedHeight]
  exact le_max_of_le_right (le_max_left _ _)

end BakerWustholz

/-- The elementary one-place Liouville inequality supplied by the product
formula: at any complex embedding, the logarithm of a nonzero algebraic
number cannot lie below minus its unnormalised logarithmic height.  This is
the local lower-bound input for the auxiliary determinants in the
Baker--Wüstholz argument. -/
lemma numberField_neg_logHeight_le_log_norm_embedding
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {x : K} (_hx : x ≠ 0) :
    -Height.logHeight₁ x ≤ Real.log ‖φ x‖ := by
  let w : NumberField.InfinitePlace K :=
    NumberField.InfinitePlace.mk φ
  have harchTerm :
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) ≤
        ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹)) := by
    exact Finset.single_le_sum
      (fun (v : NumberField.InfinitePlace K) _ ↦
        mul_nonneg (Nat.cast_nonneg v.mult)
          (show 0 ≤ Real.posLog (v (x⁻¹)) from Real.posLog_nonneg))
      (Finset.mem_univ w)
  have hnonarch : 0 ≤
      ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v (x⁻¹)) :=
    finsum_nonneg fun v : NumberField.FinitePlace K ↦
      (show 0 ≤ Real.posLog (v (x⁻¹)) from Real.posLog_nonneg)
  have htermHeight :
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) ≤
        Height.logHeight₁ x := by
    calc
      _ ≤ ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹)) := harchTerm
      _ ≤ (∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v (x⁻¹))) +
          ∑ᶠ v : NumberField.FinitePlace K,
            Real.posLog (v (x⁻¹)) := le_add_of_nonneg_right hnonarch
      _ = Height.logHeight₁ (x⁻¹) :=
        (NumberField.logHeight₁_eq (x⁻¹)).symm
      _ = Height.logHeight₁ x := Height.logHeight₁_inv x
  have hwInv : w (x⁻¹) = ‖φ x‖⁻¹ := by
    simp [w]
  have hneglog : -Real.log ‖φ x‖ ≤ Real.posLog (w (x⁻¹)) := by
    rw [hwInv]
    change -Real.log ‖φ x‖ ≤ max 0 (Real.log ‖φ x‖⁻¹)
    rw [Real.log_inv]
    exact le_max_right _ _
  have hmult : Real.posLog (w (x⁻¹)) ≤
      (w.mult : ℝ) * Real.posLog (w (x⁻¹)) := by
    nth_rewrite 1 [← one_mul (Real.posLog (w (x⁻¹)))]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr w.mult_ne_zero)
      Real.posLog_nonneg
  linarith

/-- The complementary one-place upper inequality: the logarithmic norm at
one complex embedding is at most the global unnormalised height. -/
lemma numberField_log_norm_embedding_le_logHeight
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (x : K) :
    Real.log ‖φ x‖ ≤ Height.logHeight₁ x := by
  let w : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk φ
  have harchTerm :
      (w.mult : ℝ) * Real.posLog (w x) ≤
        ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v x) := by
    exact Finset.single_le_sum
      (fun (v : NumberField.InfinitePlace K) _ ↦
        mul_nonneg (Nat.cast_nonneg v.mult)
          (show 0 ≤ Real.posLog (v x) from Real.posLog_nonneg))
      (Finset.mem_univ w)
  have hnonarch : 0 ≤
      ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v x) :=
    finsum_nonneg fun _ ↦ Real.posLog_nonneg
  have htermHeight :
      (w.mult : ℝ) * Real.posLog (w x) ≤ Height.logHeight₁ x := by
    calc
      _ ≤ ∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v x) := harchTerm
      _ ≤ (∑ v : NumberField.InfinitePlace K,
          (v.mult : ℝ) * Real.posLog (v x)) +
          ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v x) :=
        le_add_of_nonneg_right hnonarch
      _ = Height.logHeight₁ x := (NumberField.logHeight₁_eq x).symm
  have hw : w x = ‖φ x‖ := by simp [w]
  have hlog : Real.log ‖φ x‖ ≤ Real.posLog (w x) := by
    rw [hw]
    exact le_max_right _ _
  have hmult : Real.posLog (w x) ≤
      (w.mult : ℝ) * Real.posLog (w x) := by
    nth_rewrite 1 [← one_mul (Real.posLog (w x))]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr w.mult_ne_zero)
      Real.posLog_nonneg
  exact hlog.trans (hmult.trans htermHeight)

/-- At a nonzero algebraic number, the absolute logarithmic norm at any
complex embedding is bounded by its global unnormalised height. -/
lemma numberField_abs_log_norm_embedding_le_logHeight
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {x : K} (hx : x ≠ 0) :
    |Real.log ‖φ x‖| ≤ Height.logHeight₁ x := by
  rw [abs_le]
  exact ⟨numberField_neg_logHeight_le_log_norm_embedding φ hx,
    numberField_log_norm_embedding_le_logHeight φ x⟩

attribute [local instance] Matrix.seminormedAddCommGroup

/-- Quantitative control of the integral trace-coordinate matrix obtained
from a common integral denominator.  The estimate is deliberately coarse:
each trace is bounded by the sum of all complex embeddings. -/
lemma traceConstraintMatrix_norm_le
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype rows] [Fintype cols] [Fintype ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) (Q : ℕ)
    (hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j))
    {H M S : ℝ} (hS : 0 ≤ S) (hM0 : 0 ≤ M)
    (hH : ∀ r j, Height.logHeight₁ (A r j) ≤ H)
    (hM : ∀ i (φ : K →ₐ[ℚ] ℂ), ‖φ (b i)‖ ≤ M)
    (hQ : (Q : ℝ) ≤ S) :
    ‖LinearForms.traceConstraintMatrix b hb A Q hQA‖ ≤
      (Module.finrank ℚ K : ℝ) * S * Real.exp H * M := by
  have hRHS : 0 ≤ (Module.finrank ℚ K : ℝ) * S * Real.exp H * M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hS)
      (Real.exp_pos H).le) hM0
  rw [Matrix.norm_le_iff hRHS]
  intro ri j
  let u : NumberField.RingOfIntegers K :=
    ⟨(Q : K) * A ri.1 j, hQA ri.1 j⟩
  let v : NumberField.RingOfIntegers K := ⟨b ri.2, hb ri.2⟩
  have htrace :
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ) =
        ∑ φ : K →ₐ[ℚ] ℂ, φ (((u * v : NumberField.RingOfIntegers K) : K)) := by
    calc
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ) =
          algebraMap ℚ ℂ
            ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℚ) := by
        norm_num
      _ = algebraMap ℚ ℂ
          (Algebra.trace ℚ K (((u * v : NumberField.RingOfIntegers K) : K))) := by
        rw [Algebra.coe_trace_int]
      _ = ∑ φ : K →ₐ[ℚ] ℂ,
          φ (((u * v : NumberField.RingOfIntegers K) : K)) :=
        trace_eq_sum_embeddings ℂ
  have hAemb : ∀ φ : K →ₐ[ℚ] ℂ, ‖φ (A ri.1 j)‖ ≤ Real.exp H := by
    intro φ
    by_cases hz : A ri.1 j = 0
    · simp [hz, (Real.exp_pos H).le]
    · have hp : 0 < ‖φ (A ri.1 j)‖ := norm_pos_iff.mpr
          ((map_ne_zero_iff φ.toRingHom φ.injective).mpr hz)
      calc
        ‖φ (A ri.1 j)‖ = Real.exp (Real.log ‖φ (A ri.1 j)‖) := by
          rw [Real.exp_log hp]
        _ ≤ Real.exp H := Real.exp_le_exp.mpr
          ((numberField_log_norm_embedding_le_logHeight φ.toRingHom _).trans
            (hH ri.1 j))
  have hterm : ∀ φ : K →ₐ[ℚ] ℂ,
      ‖φ (((u * v : NumberField.RingOfIntegers K) : K))‖ ≤
        S * Real.exp H * M := by
    intro φ
    change ‖φ ((Q : K) * A ri.1 j * b ri.2)‖ ≤ _
    rw [map_mul, map_mul, norm_mul, norm_mul]
    have hQnorm : ‖φ (Q : K)‖ ≤ S := by
      simpa using hQ
    exact mul_le_mul
      (mul_le_mul hQnorm (hAemb φ) (by positivity) hS)
      (hM ri.2 φ) (norm_nonneg _) (mul_nonneg hS (Real.exp_pos H).le)
  change ‖Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v)‖ ≤ _
  have hcastNorm :
      ‖Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v)‖ =
        ‖((Algebra.trace ℤ (NumberField.RingOfIntegers K) (u * v) : ℤ) : ℂ)‖ := by
    norm_num [Int.norm_eq_abs]
  rw [hcastNorm, htrace]
  calc
    ‖∑ φ : K →ₐ[ℚ] ℂ, φ (((u * v : NumberField.RingOfIntegers K) : K))‖ ≤
        ∑ φ : K →ₐ[ℚ] ℂ,
          ‖φ (((u * v : NumberField.RingOfIntegers K) : K))‖ := norm_sum_le _ _
    _ ≤ ∑ _φ : K →ₐ[ℚ] ℂ, (S * Real.exp H * M) := by
      gcongr with φ hφ
      exact hterm φ
    _ = (Module.finrank ℚ K : ℝ) * S * Real.exp H * M := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        AlgHom.card ℚ K ℂ]
      ring

/-- A number-field form of Siegel's lemma.  Taking traces against an
integral rational basis turns each algebraic row into `deg K` integral
rows.  Nondegeneracy of the trace pairing recovers the original kernel. -/
theorem exists_bounded_nonzero_integer_kernel_numberField
    {K rows cols ι : Type*} [Field K] [NumberField K]
    [Fintype rows] [Fintype cols] [Fintype ι]
    [Nonempty rows]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i))
    (A : Matrix rows cols K) {H M : ℝ}
    (hM0 : 0 ≤ M)
    (hH : ∀ r j, Height.logHeight₁ (A r j) ≤ H)
    (hM : ∀ i (φ : K →ₐ[ℚ] ℂ), ‖φ (b i)‖ ≤ M)
    (hcard : Fintype.card rows * Fintype.card ι < Fintype.card cols) :
    ∃ (Q : ℕ) (_hQ0 : Q ≠ 0)
        (hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j))
        (c : cols → ℤ),
      (Q : ℝ) ≤ Real.exp H ^ (Fintype.card rows * Fintype.card cols) ∧
      c ≠ 0 ∧ A.mulVec (fun j ↦ (c j : K)) = 0 ∧
      (∀ j, (c j).natAbs ≤ Nat.ceil
        (((Fintype.card cols : ℝ) *
            max 1 ‖LinearForms.traceConstraintMatrix b hb A Q hQA‖) ^
          (((Fintype.card rows * Fintype.card ι : ℕ) : ℝ) /
            ((Fintype.card cols : ℝ) -
              (Fintype.card rows * Fintype.card ι : ℕ))))) ∧
      ‖LinearForms.traceConstraintMatrix b hb A Q hQA‖ ≤
        (Module.finrank ℚ K : ℝ) *
          (Real.exp H ^ (Fintype.card rows * Fintype.card cols)) *
          Real.exp H * M := by
  classical
  obtain ⟨Q, hQ0, hQbound, hQAflat⟩ :=
    LinearForms.exists_common_integral_scale
      (fun rc : rows × cols ↦ A rc.1 rc.2)
      (fun rc ↦ hH rc.1 rc.2)
  have hQA : ∀ r j, IsIntegral ℤ ((Q : K) * A r j) :=
    fun r j ↦ hQAflat (r, j)
  let T := LinearForms.traceConstraintMatrix b hb A Q hQA
  have hcard' : Fintype.card (rows × ι) < Fintype.card cols := by
    simpa [Fintype.card_prod] using hcard
  let : Nonempty ι := Fintype.card_pos_iff.mp <| by
    rw [← Module.finrank_eq_card_basis b]
    exact Module.finrank_pos
  have hrows' : 0 < Fintype.card (rows × ι) := Fintype.card_pos
  obtain ⟨c, hc0, hkernel, hcbound⟩ :=
    LinearForms.exists_bounded_nonzero_integer_kernel T hcard' hrows'
  have hAker : A.mulVec (fun j ↦ (c j : K)) = 0 :=
    LinearForms.traceConstraintMatrix_kernel b hb A Q hQ0 hQA c hkernel
  have hQbound' :
      (Q : ℝ) ≤ Real.exp H ^ (Fintype.card rows * Fintype.card cols) := by
    simpa [Fintype.card_prod] using hQbound
  have hTnorm : ‖T‖ ≤
      (Module.finrank ℚ K : ℝ) *
        (Real.exp H ^ (Fintype.card rows * Fintype.card cols)) *
        Real.exp H * M := by
    apply traceConstraintMatrix_norm_le b hb A Q hQA
      (by positivity) hM0 hH hM hQbound'
  refine ⟨Q, hQ0, hQA, c, hQbound', hc0, hAker, ?_, hTnorm⟩
  simpa [T, Fintype.card_prod] using hcbound

/-- Siegel's lemma for the algebraic multipoint moment system used in the
fixed-rank logarithmic-form argument.  It returns the exact moments together
with the coefficient and trace-matrix bounds needed by extrapolation. -/
theorem exists_bounded_nonzero_multipoint_moment_coefficients_numberField
    {F kappa iota ι : Type*} [Field F] [NumberField F]
    [Fintype kappa] [Fintype iota] [DecidableEq iota] [Fintype ι]
    (basis : Module.Basis ι ℚ F)
    (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (beta : kappa → F) (a : kappa → ℤ) (r : kappa → iota → ℤ)
    (A T S : ℕ) {H V M : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hS : 0 < S)
    (hV : 1 ≤ V) (hM0 : 0 ≤ M)
    (hbeta : ∀ k, Height.logHeight₁ (beta k) ≤ H)
    (ha : ∀ k, ‖a k‖ ≤ V) (hr : ∀ k i, ‖r k i‖ ≤ V)
    (hM : ∀ i (φ : F →ₐ[ℚ] ℂ), ‖φ (basis i)‖ ≤ M)
    (hcard :
      (A * T * S ^ Fintype.card iota) * Fintype.card ι <
        Fintype.card kappa) :
    let Hentry : ℝ := (A : ℝ) * H +
      ((T + Fintype.card iota * S : ℕ) : ℝ) *
        ((Module.finrank ℚ F : ℝ) * Real.log V)
    ∃ (Q : ℕ) (_hQ0 : Q ≠ 0)
        (hQint : ∀ row k, IsIntegral ℤ
          ((Q : F) * LinearForms.multipointRectangularMomentMatrix
            beta a r A T S row k))
        (c : kappa → ℤ),
      (Q : ℝ) ≤ Real.exp Hentry ^
          ((A * T * S ^ Fintype.card iota) * Fintype.card kappa) ∧
      c ≠ 0 ∧
      (∀ h : Fin A, ∀ q : Fin T, ∀ u : iota → Fin S,
        ∑ k, (c k : F) * beta k ^ (h : ℕ) * (a k : F) ^ (q : ℕ) *
          ∏ i, (r k i : F) ^ (u i : ℕ) = 0) ∧
      (∀ k, (c k).natAbs ≤ Nat.ceil
        (((Fintype.card kappa : ℝ) *
            max 1 ‖LinearForms.traceConstraintMatrix basis hbasis
              (LinearForms.multipointRectangularMomentMatrix beta a r A T S)
              Q hQint‖) ^
          ((((A * T * S ^ Fintype.card iota) * Fintype.card ι : ℕ) : ℝ) /
            ((Fintype.card kappa : ℝ) -
              ((A * T * S ^ Fintype.card iota) * Fintype.card ι : ℕ))))) ∧
      ‖LinearForms.traceConstraintMatrix basis hbasis
          (LinearForms.multipointRectangularMomentMatrix beta a r A T S)
          Q hQint‖ ≤
        (Module.finrank ℚ F : ℝ) *
          (Real.exp Hentry ^
            ((A * T * S ^ Fintype.card iota) * Fintype.card kappa)) *
          Real.exp Hentry * M := by
  dsimp only
  let rows := LinearForms.MultipointRectangularMomentIndex iota A T S
  let : Fintype rows := by
    dsimp [rows, LinearForms.MultipointRectangularMomentIndex,
      LinearForms.RectangularMomentIndex]
    infer_instance
  let matrix : Matrix rows kappa F :=
    LinearForms.multipointRectangularMomentMatrix beta a r A T S
  have hrowsCard : Fintype.card rows =
      A * T * S ^ Fintype.card iota := by
    simp [rows, LinearForms.MultipointRectangularMomentIndex,
      LinearForms.RectangularMomentIndex, Nat.mul_assoc]
  let Hentry : ℝ := (A : ℝ) * H +
      ((T + Fintype.card iota * S : ℕ) : ℝ) *
        ((Module.finrank ℚ F : ℝ) * Real.log V)
  have hheight : ∀ row k, Height.logHeight₁ (matrix row k) ≤ Hentry := by
    intro row k
    exact LinearForms.logHeight₁_multipointRectangularMomentMatrix_le
      beta a r A T S hV hbeta ha hr row k
  have : Nonempty rows := Fintype.card_pos_iff.mp <| by
    rw [hrowsCard]
    positivity
  have hcard' : Fintype.card rows * Fintype.card ι <
      Fintype.card kappa := by
    simpa [hrowsCard] using hcard
  obtain ⟨Q, hQ0, hQint, c, hQ, hc0, hker, hc, hnorm⟩ :=
    exists_bounded_nonzero_integer_kernel_numberField
      basis hbasis matrix hM0 hheight hM hcard'
  have hmom :=
    (LinearForms.multipointRectangularMomentMatrix_kernel_iff
      beta a r A T S c).mp hker
  refine ⟨Q, hQ0, hQint, c, ?_, hc0, hmom, ?_, ?_⟩
  · simpa [Hentry, hrowsCard] using hQ
  · simpa [matrix, Hentry, hrowsCard] using hc
  · simpa [matrix, Hentry, hrowsCard] using hnorm

namespace BakerWustholz

/-- At a positive real embedding, the logarithm term in the modified height
is already bounded by the global height.  Thus only the normalized height
and the degree floor remain. -/
lemma modifiedHeight_positiveReal_le
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {α : K} {ρ : ℝ}
    (hρ : 0 < ρ) (hφ : φ α = (ρ : ℂ)) :
    modifiedHeight φ α ≤
      max (Height.logHeight₁ α / (Module.finrank ℚ K : ℝ))
        (1 / (Module.finrank ℚ K : ℝ)) := by
  have hα : α ≠ 0 := by
    intro h
    subst α
    simp at hφ
    apply hρ.ne'
    exact_mod_cast hφ.symm
  have hlogNorm : ‖Complex.log (φ α)‖ ≤ Height.logHeight₁ α := by
    have habs := numberField_abs_log_norm_embedding_le_logHeight φ hα
    rw [hφ, Complex.norm_real, Real.norm_eq_abs] at habs
    rw [hφ, ← Complex.ofReal_log hρ.le, Complex.norm_real,
      Real.norm_eq_abs]
    simpa [abs_of_pos hρ] using habs
  have hd : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  rw [modifiedHeight]
  apply max_le
  · exact le_max_left _ _
  · apply max_le
    · exact ((div_le_div_iff_of_pos_right hd).2 hlogNorm).trans
        (le_max_left _ _)
    · exact le_max_right _ _

lemma modifiedHeight_positiveReal_eq
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {α : K} {ρ : ℝ}
    (hρ : 0 < ρ) (hφ : φ α = (ρ : ℂ)) :
    modifiedHeight φ α =
      max (Height.logHeight₁ α / (Module.finrank ℚ K : ℝ))
        (1 / (Module.finrank ℚ K : ℝ)) := by
  apply le_antisymm (modifiedHeight_positiveReal_le φ hρ hφ)
  exact max_le (normalized_logHeight_le_modifiedHeight φ α)
    (one_div_degree_le_modifiedHeight φ α)

lemma modifiedHeight_positiveReal_le_of_logHeight_le
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {α : K} {ρ A : ℝ}
    (hρ : 0 < ρ) (hφ : φ α = (ρ : ℂ))
    (hheight : Height.logHeight₁ α ≤ A) :
    modifiedHeight φ α ≤
      max (A / (Module.finrank ℚ K : ℝ))
        (1 / (Module.finrank ℚ K : ℝ)) := by
  rw [modifiedHeight_positiveReal_eq φ hρ hφ]
  apply max_le_max_right
  exact div_le_div_of_nonneg_right hheight (by positivity)

end BakerWustholz

/-- The one-logarithm case of the archimedean transcendence estimate is
already elementary.  If an algebraic number is different from zero and one,
Liouville's inequality applied to `α - 1`, together with
`exp (log α) = α`, gives a completely explicit lower bound for its
principal logarithm.  This is the base case of the linear-forms argument. -/
lemma numberField_log_norm_log_lower
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {α : K} (hα : α ≠ 0) (hα1 : α ≠ 1) :
    -(Height.logHeight₁ α +
        (Module.finrank ℚ K : ℝ) * Real.log 2 + Real.log 2) ≤
      Real.log ‖Complex.log (φ α)‖ := by
  have hφa : φ α ≠ 0 := (map_ne_zero φ).2 hα
  have hφa1 : φ α ≠ 1 := by
    intro h
    apply hα1
    apply φ.injective
    simpa using h
  have hlogne : Complex.log (φ α) ≠ 0 := by
    intro h
    have hexp := congrArg Complex.exp h
    rw [Complex.exp_log hφa, Complex.exp_zero] at hexp
    exact hφa1 hexp
  have hheightNonneg : 0 ≤ Height.logHeight₁ α :=
    Height.zero_le_logHeight₁ _
  have hdNonneg : (0 : ℝ) ≤ Module.finrank ℚ K := by positivity
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hdLogTwo : 0 ≤ (Module.finrank ℚ K : ℝ) * Real.log 2 :=
    mul_nonneg hdNonneg hlogTwo
  by_cases hlarge : 1 ≤ ‖Complex.log (φ α)‖
  · have hlogNonneg : 0 ≤ Real.log ‖Complex.log (φ α)‖ :=
      Real.log_nonneg hlarge
    linarith
  · have hsmall : ‖Complex.log (φ α)‖ ≤ 1 :=
      le_of_lt (lt_of_not_ge hlarge)
    have hexp := Complex.norm_exp_sub_one_le hsmall
    rw [Complex.exp_log hφa] at hexp
    have hsubne : α - 1 ≠ 0 := sub_ne_zero.mpr hα1
    have hφsubne : φ (α - 1) ≠ 0 := (map_ne_zero φ).2 hsubne
    have hgapEq : φ (α - 1) = φ α - 1 := by simp
    have hgapPos : 0 < ‖φ (α - 1)‖ := norm_pos_iff.mpr hφsubne
    have hlogPos : 0 < ‖Complex.log (φ α)‖ := norm_pos_iff.mpr hlogne
    have hmono : Real.log ‖φ (α - 1)‖ ≤
        Real.log (2 * ‖Complex.log (φ α)‖) := by
      apply Real.log_le_log hgapPos
      simpa [hgapEq] using hexp
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogPos.ne'] at hmono
    have hliouville :=
      numberField_neg_logHeight_le_log_norm_embedding φ hsubne
    have hheightSub := Height.logHeight₁_sub_le α (1 : K)
    rw [Height.logHeight₁_one, add_zero,
      NumberField.totalWeight_eq_finrank K] at hheightSub
    linarith

/-- The complete one-logarithm case, including an arbitrary nonzero integer
coefficient.  The coefficient can only increase the norm, so the elementary
Liouville estimate above is absorbed by four times the square of the field
degree and the modified height. -/
lemma numberField_one_logarithm_form_lower
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {α : K} (hα : α ≠ 0)
    {b : ℤ} (hform : (b : ℂ) * Complex.log (φ α) ≠ 0) :
    -(4 * (Module.finrank ℚ K : ℝ) ^ 2 *
        BakerWustholz.modifiedHeight φ α) ≤
      Real.log ‖(b : ℂ) * Complex.log (φ α)‖ := by
  have hb : b ≠ 0 := by
    intro hb
    apply hform
    simp [hb]
  have hlogne : Complex.log (φ α) ≠ 0 := by
    intro h
    exact hform (by simp [h])
  have hα1 : α ≠ 1 := by
    intro h
    subst α
    simp at hform
  let d : ℝ := Module.finrank ℚ K
  let A : ℝ := BakerWustholz.modifiedHeight φ α
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hAone : 1 / d ≤ A := by
    simpa [d, A] using
      BakerWustholz.one_div_degree_le_modifiedHeight φ α
  have hAheight : Height.logHeight₁ α / d ≤ A := by
    simpa [d, A] using
      BakerWustholz.normalized_logHeight_le_modifiedHeight φ α
  have hA : 0 < A := by
    simpa [A] using BakerWustholz.modifiedHeight_pos φ α
  have hone : 1 ≤ d * A := by
    have h := mul_le_mul_of_nonneg_left hAone (by positivity : 0 ≤ d)
    field_simp at h
    exact h
  have hheight : Height.logHeight₁ α ≤ d * A := by
    have h := mul_le_mul_of_nonneg_left hAheight (by positivity : 0 ≤ d)
    field_simp at h
    exact h
  have hlog2 : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_two_lt_d9]
  have hbase : Height.logHeight₁ α + d * Real.log 2 + Real.log 2 ≤
      4 * d ^ 2 * A := by
    have hdA0 : 0 ≤ d * A := by positivity
    have haux : d * Real.log 2 + Real.log 2 ≤ 2 * d := by
      nlinarith
    have hquad : 2 * d ≤ 2 * d ^ 2 * A := by
      nlinarith
    nlinarith [sq_nonneg d]
  have hsingle := numberField_log_norm_log_lower φ hα hα1
  have hbNat : 1 ≤ b.natAbs := Int.natAbs_pos.mpr hb
  have hbNorm : (1 : ℝ) ≤ ‖(b : ℂ)‖ := by
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hbNat
  have hnormLog : ‖Complex.log (φ α)‖ ≤
      ‖(b : ℂ) * Complex.log (φ α)‖ := by
    rw [norm_mul]
    nth_rewrite 1 [← one_mul ‖Complex.log (φ α)‖]
    exact mul_le_mul_of_nonneg_right hbNorm (norm_nonneg _)
  have hmono : Real.log ‖Complex.log (φ α)‖ ≤
      Real.log ‖(b : ℂ) * Complex.log (φ α)‖ := by
    exact Real.log_le_log (norm_pos_iff.mpr hlogne) hnormLog
  dsimp [d, A] at hbase ⊢
  linarith

/-- Liouville's elementary lower bound for the logarithm of an algebraic
product.  Its coefficient dependence is linear in the integer exponents;
the fixed-rank Baker step improves precisely this dependence to a power of
their logarithm. -/
lemma numberField_log_algebraic_product_lower
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {n : ℕ} (α : Fin n → K)
    (hα : ∀ i, α i ≠ 0) (b : Fin n → ℤ)
    (hprod : (∏ i, α i ^ b i) ≠ 1) :
    -((∑ i, (b i).natAbs * Height.logHeight₁ (α i)) +
        (Module.finrank ℚ K : ℝ) * Real.log 2 + Real.log 2) ≤
      Real.log ‖Complex.log (φ (∏ i, α i ^ b i))‖ := by
  let z : K := ∏ i, α i ^ b i
  have hz : z ≠ 0 := by
    dsimp [z]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hα i)
  have hbase :=
    numberField_log_norm_log_lower φ hz (by simpa [z] using hprod)
  have hheight : Height.logHeight₁ z ≤
      ∑ i, (b i).natAbs * Height.logHeight₁ (α i) := by
    calc
      Height.logHeight₁ z ≤
          ∑ i, Height.logHeight₁ (α i ^ b i) := by
        dsimp [z]
        simpa using Height.logHeight₁_prod_le Finset.univ
          (fun i ↦ α i ^ b i)
      _ = ∑ i, (b i).natAbs * Height.logHeight₁ (α i) := by
        simp_rw [Height.logHeight₁_zpow]
  dsimp [z] at hbase ⊢
  linarith

/-- When all chosen algebraic numbers are positive at the distinguished real
embedding, the sum of principal logarithms is exactly the principal
logarithm of their algebraic product. -/
lemma numberField_positive_linear_form_eq_log_product
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {n : ℕ} (α : Fin n → K)
    (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hφ : ∀ i, φ (α i) = (ρ i : ℂ)) (b : Fin n → ℤ) :
    (∑ i, (b i : ℂ) * Complex.log (φ (α i))) =
      Complex.log (φ (∏ i, α i ^ b i)) := by
  simp_rw [hφ]
  rw [complex_linear_form_eq_real_log_zpow_product ρ hρ b]
  have hmap : φ (∏ i, α i ^ b i) =
      ((∏ i, ρ i ^ b i : ℝ) : ℂ) := by
    simp [hφ]
  rw [hmap]
  exact Complex.ofReal_log
    (Finset.prod_pos fun i _ ↦ zpow_pos (hρ i) _).le

/-- The coefficient-linear Liouville baseline for a positive-real
logarithmic form.  This theorem makes the remaining Baker improvement
syntactically exact: replace the displayed weighted sum of heights by a
quantity polynomial in the logarithm of the largest coefficient. -/
lemma numberField_positive_linear_form_liouville_lower
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {n : ℕ} (α : Fin n → K)
    (hα : ∀ i, α i ≠ 0) (ρ : Fin n → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hφ : ∀ i, φ (α i) = (ρ i : ℂ))
    (b : Fin n → ℤ) (hprod : (∏ i, α i ^ b i) ≠ 1) :
    -((∑ i, (b i).natAbs * Height.logHeight₁ (α i)) +
        (Module.finrank ℚ K : ℝ) * Real.log 2 + Real.log 2) ≤
      Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖ := by
  rw [numberField_positive_linear_form_eq_log_product φ α ρ hρ hφ b]
  exact numberField_log_algebraic_product_lower φ α hα b hprod

/-- Baker--Wüstholz for a single logarithm.  In this base case no auxiliary
determinant is needed: the explicit Baker--Wüstholz constant is much larger
than the elementary Liouville coefficient proved above. -/
theorem bakerWustholz_linearForms_logs_one
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α : Fin 1 → K) (hα : ∀ i, α i ≠ 0)
    (b : Fin 1 → ℤ) {B : ℕ} (_hB : 2 ≤ B)
    (_hbB : ∀ i, (b i).natAbs ≤ B)
    (hform : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖ ≥
      -(BakerWustholz.constant 1 (Module.finrank ℚ K) *
          max (Real.log B) (1 / (Module.finrank ℚ K : ℝ)) *
          ∏ i, BakerWustholz.modifiedHeight φ (α i)) := by
  let d : ℝ := Module.finrank ℚ K
  let A : ℝ := BakerWustholz.modifiedHeight φ (α 0)
  have hsum : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) =
      (b 0 : ℂ) * Complex.log (φ (α 0)) := by simp
  rw [hsum] at hform ⊢
  have hbase :=
    numberField_one_logarithm_form_lower φ (hα 0) hform
  have hd : (1 : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hmax : 1 / d ≤ max (Real.log B) (1 / d) := le_max_right _ _
  have hlog : (1 / 2 : ℝ) ≤
      Real.log (2 * (Module.finrank ℚ K : ℕ)) := by
    calc
      (1 / 2 : ℝ) ≤ Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      _ ≤ Real.log (2 * (Module.finrank ℚ K : ℕ)) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast (Nat.mul_le_mul_left 2
          (show 1 ≤ Module.finrank ℚ K from Module.finrank_pos))
  have hconstant : 4 * d ^ 3 ≤
      BakerWustholz.constant 1 (Module.finrank ℚ K) := by
    rw [BakerWustholz.constant]
    norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, one_pow]
    dsimp [d]
    have hd0 : (0 : ℝ) ≤ Module.finrank ℚ K := by positivity
    nlinarith [sq_nonneg ((Module.finrank ℚ K : ℝ) ^ 2)]
  have hcoef : 4 * d ^ 2 ≤
      BakerWustholz.constant 1 (Module.finrank ℚ K) *
        max (Real.log B) (1 / d) := by
    have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
    calc
      4 * d ^ 2 = (4 * d ^ 3) * (1 / d) := by field_simp
      _ ≤ BakerWustholz.constant 1 (Module.finrank ℚ K) *
          (1 / d) := by gcongr
      _ ≤ BakerWustholz.constant 1 (Module.finrank ℚ K) *
          max (Real.log B) (1 / d) := by
        exact mul_le_mul_of_nonneg_left hmax
          (BakerWustholz.constant_pos (by norm_num)
            (Module.finrank_pos : 0 < Module.finrank ℚ K)).le
  have hA : 0 ≤ A :=
    (BakerWustholz.modifiedHeight_pos φ (α 0)).le
  have hmul := mul_le_mul_of_nonneg_right hcoef hA
  simpa [A] using (neg_le_neg hmul).trans hbase

/-- The one-logarithm estimate also handles an arbitrary ambient vector
whose coefficients vanish away from one chosen coordinate. -/
lemma numberField_single_support_logarithmic_form_lower
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) {n : ℕ} (α : Fin n → K)
    (hα : ∀ i, α i ≠ 0) (b : Fin n → ℤ) (j : Fin n)
    (hb : ∀ i, i ≠ j → b i = 0)
    (hform : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    -(4 * (Module.finrank ℚ K : ℝ) ^ 2 *
        BakerWustholz.modifiedHeight φ (α j)) ≤
      Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖ := by
  have hsum : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) =
      (b j : ℂ) * Complex.log (φ (α j)) := by
    rw [← Finset.sum_subset (s₁ := {j}) (s₂ := Finset.univ)]
    · simp
    · simp
    · intro i _hi hij
      simp only [Finset.mem_singleton] at hij
      rw [hb i hij]
      simp
  rw [hsum] at hform ⊢
  exact numberField_one_logarithm_form_lower φ (hα j) hform

/-- A totally real field of degree at most eight has at most seven free
unit generators.  Consequently the bounded-unit product arising from the
three-radical Pell field contributes a fixed number of logarithms. -/
lemma totallyReal_degreeEight_units_rank_le_seven
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) :
    NumberField.Units.rank K ≤ 7 := by
  rw [NumberField.Units.rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero,
    add_zero, ← NumberField.IsTotallyReal.finrank]
  omega

/-- After adjoining the rational and finite-prime factors, the packaged
positive logarithmic form has at most nine terms. -/
lemma totallyReal_degreeEight_packaged_log_count_le_nine
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) :
    NumberField.Units.rank K + 2 ≤ 9 := by
  have hrank := totallyReal_degreeEight_units_rank_le_seven K hdeg
  omega

/-- Every root of unity in a totally real number field is `1` or `-1`.
The proof evaluates it in a real embedding and uses the elementary
classification of finite-order real numbers. -/
theorem totallyReal_torsion_eq_one_or_neg_one
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (x : NumberField.Units.torsion K) :
    (x : (NumberField.RingOfIntegers K)ˣ) = 1 ∨
      (x : (NumberField.RingOfIntegers K)ˣ) = -1 := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  let ρ : K →+* ℝ :=
    (NumberField.IsTotallyReal.complexEmbedding_isReal φ).embedding
  let r : ℝ := ρ ((x.1 : NumberField.RingOfIntegers K) : K)
  obtain ⟨n, hn, hpow⟩ :=
    ((CommGroup.mem_torsion x.1).1 x.2).exists_pow_eq_one
  have hpowK :
      (((x.1 : NumberField.RingOfIntegers K) : K) ^ n) = 1 := by
    simpa using congrArg (fun u : (NumberField.RingOfIntegers K)ˣ ↦
      (((u : NumberField.RingOfIntegers K) : K))) hpow
  have hrpow : r ^ n = 1 := by
    dsimp [r]
    rw [← map_pow, hpowK, map_one]
  have hrfin : IsOfFinOrder r :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hrpow⟩
  by_cases hr : 0 ≤ r
  · left
    have hre : r = 1 := hrfin.eq_one hr
    apply Units.ext
    apply Subtype.ext
    apply ρ.injective
    change ρ ((x.1 : NumberField.RingOfIntegers K) : K) = ρ (1 : K)
    rw [map_one]
    exact hre
  · right
    have hre : r = -1 := hrfin.eq_neg_one (le_of_not_ge hr)
    apply Units.ext
    apply Subtype.ext
    apply ρ.injective
    change ρ ((x.1 : NumberField.RingOfIntegers K) : K) = ρ (-1 : K)
    rw [map_neg, map_one]
    exact hre

/-- Squaring eliminates the torsion factor in every totally real unit
decomposition. -/
lemma totallyReal_torsion_sq_eq_one
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (x : NumberField.Units.torsion K) :
    (x.1 : (NumberField.RingOfIntegers K)ˣ) ^ 2 = 1 := by
  rcases totallyReal_torsion_eq_one_or_neg_one x with h | h
  · rw [h]
    simp
  · rw [h]
    simp

/-- The archimedean logarithmic form specialized all the way to three
shifted squarefree decompositions.  Pairwise-distinct shifts make the
form nonzero, and bounding the shifts by `J` supplies its explicit upper
bound. -/
lemma three_shift_real_normalized_gap_log_le
    {n i j k zᵢ zⱼ zₖ bᵢ bⱼ bₖ J : ℕ}
    (hbᵢ : 0 < bᵢ) (hbⱼ : 0 < bⱼ) (hbₖ : 0 < bₖ)
    (hzᵢ : 0 < zᵢ) (hzⱼ : 0 < zⱼ) (hzₖ : 0 < zₖ)
    (hᵢ : zᵢ ^ 2 * bᵢ = n + i)
    (hⱼ : zⱼ ^ 2 * bⱼ = n + j)
    (hₖ : zₖ ^ 2 * bₖ = n + k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hiJ : i ≤ J) (hjJ : j ≤ J) (hkJ : k ≤ J)
    (hJ : 0 < J) (hlarge : 2 * J ≤ n + i) :
    Real.log (abs
        ((((i : ℤ) - (k : ℤ) : ℤ) : ℝ) /
            (((i : ℤ) - (j : ℤ) : ℤ) : ℝ) *
            ((Real.sqrt bᵢ * zᵢ - Real.sqrt bⱼ * zⱼ) /
              (Real.sqrt bᵢ * zᵢ - Real.sqrt bₖ * zₖ)) - 1)) ≤
      Real.log (2 * (J : ℝ)) -
        2 * Real.log (Real.sqrt bᵢ * zᵢ) := by
  let A : ℝ := Real.sqrt bᵢ * zᵢ
  let B : ℝ := Real.sqrt bⱼ * zⱼ
  let C : ℝ := Real.sqrt bₖ * zₖ
  let β₁₂ : ℝ := (((i : ℤ) - (j : ℤ) : ℤ) : ℝ)
  let β₁₃ : ℝ := (((i : ℤ) - (k : ℤ) : ℤ) : ℝ)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hbᵢ))
      (by exact_mod_cast hzᵢ)
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ C := by positivity
  have hAsq : A ^ 2 = (n + i : ℕ) := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact_mod_cast (by simpa [mul_comm] using hᵢ)
  have hBsq : B ^ 2 = (n + j : ℕ) := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact_mod_cast (by simpa [mul_comm] using hⱼ)
  have hCsq : C ^ 2 = (n + k : ℕ) := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact_mod_cast (by simpa [mul_comm] using hₖ)
  have h₁₂ : A ^ 2 - B ^ 2 = β₁₂ := by
    rw [hAsq, hBsq]
    norm_num [β₁₂]
  have h₁₃ : A ^ 2 - C ^ 2 = β₁₃ := by
    rw [hAsq, hCsq]
    norm_num [β₁₃]
  have hβ₁₂ : β₁₂ ≠ 0 := by
    dsimp [β₁₂]
    exact_mod_cast sub_ne_zero.mpr
      (show (i : ℤ) ≠ (j : ℤ) by exact_mod_cast hij)
  have hβ₁₃ : β₁₃ ≠ 0 := by
    dsimp [β₁₃]
    exact_mod_cast sub_ne_zero.mpr
      (show (i : ℤ) ≠ (k : ℤ) by exact_mod_cast hik)
  have hβDiff : β₁₂ - β₁₃ ≠ 0 := by
    have heq : β₁₂ - β₁₃ =
        (((k : ℤ) - (j : ℤ) : ℤ) : ℝ) := by
      dsimp [β₁₂, β₁₃]
      push_cast
      ring
    rw [heq]
    exact_mod_cast sub_ne_zero.mpr
      (show (k : ℤ) ≠ (j : ℤ) by exact_mod_cast hjk.symm)
  have hβ₁₂J : |β₁₂| ≤ (J : ℝ) := by
    dsimp [β₁₂]
    rw [abs_le]
    constructor
    · exact_mod_cast
        (show -(J : ℤ) ≤ (i : ℤ) - (j : ℤ) by omega)
    · exact_mod_cast
        (show (i : ℤ) - (j : ℤ) ≤ (J : ℤ) by omega)
  have hβ₁₃J : |β₁₃| ≤ (J : ℝ) := by
    dsimp [β₁₃]
    rw [abs_le]
    constructor
    · exact_mod_cast
        (show -(J : ℤ) ≤ (i : ℤ) - (k : ℤ) by omega)
    · exact_mod_cast
        (show (i : ℤ) - (k : ℤ) ≤ (J : ℤ) by omega)
  have hlargeR : 2 * (J : ℝ) ≤ A ^ 2 := by
    rw [hAsq]
    exact_mod_cast hlarge
  simpa [A, B, C, β₁₂, β₁₃] using
    simultaneousPell_real_normalized_gap_log_le hA hB hC h₁₂ h₁₃
      hβ₁₂ hβ₁₃ hβDiff (by exact_mod_cast hJ)
      hβ₁₂J hβ₁₃J hlargeR

/-- A square root of a rational integer is integral over the rational
integers. -/
lemma isIntegral_int_sqRoot
    {K : Type*} [Field K] [CharZero K]
    (s : K) (γ : ℤ) (hs : s ^ 2 = (γ : K)) : IsIntegral ℤ s := by
  let p : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C γ
  have hpmonic : p.Monic := by
    simpa [p] using Polynomial.monic_X_pow_sub_C γ (by norm_num : 2 ≠ 0)
  have hproot : Polynomial.aeval s p = 0 := by
    simp [p, hs]
  exact ⟨p, hpmonic, hproot⟩

/-- Each minus factor value is an algebraic integer. -/
lemma isIntegral_pellValueMinus
    {K : Type*} [Field K] [CharZero K]
    {sₐ s_b : K} {γₐ γ_b xₐ x_b : ℤ}
    (hsₐ : sₐ ^ 2 = (γₐ : K)) (hs_b : s_b ^ 2 = (γ_b : K)) :
    IsIntegral ℤ (pellValueMinus sₐ s_b xₐ x_b) := by
  exact ((isIntegral_int_sqRoot sₐ γₐ hsₐ).mul
      (isIntegral_intCast (R := ℤ) (B := K) xₐ)).sub
    ((isIntegral_int_sqRoot s_b γ_b hs_b).mul
      (isIntegral_intCast (R := ℤ) (B := K) x_b))

/-- Each plus factor value is an algebraic integer. -/
lemma isIntegral_pellValuePlus
    {K : Type*} [Field K] [CharZero K]
    {sₐ s_b : K} {γₐ γ_b xₐ x_b : ℤ}
    (hsₐ : sₐ ^ 2 = (γₐ : K)) (hs_b : s_b ^ 2 = (γ_b : K)) :
    IsIntegral ℤ (pellValuePlus sₐ s_b xₐ x_b) := by
  exact ((isIntegral_int_sqRoot sₐ γₐ hsₐ).mul
      (isIntegral_intCast (R := ℤ) (B := K) xₐ)).add
    ((isIntegral_int_sqRoot s_b γ_b hs_b).mul
      (isIntegral_intCast (R := ℤ) (B := K) x_b))

/-- The finite-prime support of a nonzero number-field element, expressed
using the height-one primes of the ring of integers. -/
def numberFieldPrimeSupport
    {K : Type*} [Field K] [NumberField K] (z : Kˣ) :
    Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {v | v.valuation K z ≠ 1}

/-- The prime support of a nonzero number-field element is finite. -/
lemma numberFieldPrimeSupport_finite
    {K : Type*} [Field K] [NumberField K] (z : Kˣ) :
    (numberFieldPrimeSupport z).Finite := by
  let e := NumberField.FinitePlace.equivHeightOneSpectrum (K := K)
  have hz : ((z : Kˣ) : K) ≠ 0 := Units.ne_zero z
  have hfinite :
      (Function.mulSupport (fun w : NumberField.FinitePlace K ↦
        w ((z : Kˣ) : K))).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hz
  have hsupport_iff
      (v : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K)) :
      (e.symm v) ((z : Kˣ) : K) ≠ 1 ↔ v.valuation K z ≠ 1 := by
    rw [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
      NumberField.FinitePlace.norm_embedding']
    norm_cast
    exact not_congr (WithZeroMulInt.toNNReal_eq_one_iff _
      (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)))
  have heq : numberFieldPrimeSupport z =
      e '' Function.mulSupport (fun w : NumberField.FinitePlace K ↦
        w ((z : Kˣ) : K)) := by
    ext v
    constructor
    · intro hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      exact (hsupport_iff v).mpr hv
    · rintro ⟨w, hw, rfl⟩
      exact (hsupport_iff (e w)).mp (by simpa using hw)
  rw [heq]
  exact hfinite.image e

/-- The rational prime below a height-one prime of the ring of integers
of a number field. -/
def numberFieldPrimeBelow
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) : ℕ :=
  Ideal.absNorm (Ideal.under ℤ v.asIdeal)

lemma numberFieldPrimeBelow_prime
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    (numberFieldPrimeBelow v).Prime := by
  let : NeZero v.asIdeal := ⟨v.ne_bot⟩
  exact Nat.absNorm_under_prime v.asIdeal

/-- The inertia degree of a height-one prime is at most the degree of the
number field.  This is the individual-term consequence of the fundamental
ramification--inertia degree formula. -/
lemma numberFieldPrime_inertiaDeg_le_finrank
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.asIdeal.inertiaDeg ℤ ≤ Module.finrank ℚ K := by
  let p : Ideal ℤ := Ideal.under ℤ v.asIdeal
  let q : p.primesOver (NumberField.RingOfIntegers K) :=
    ⟨v.asIdeal, ⟨v.isPrime, by dsimp only [p]; infer_instance⟩⟩
  have hterm' :
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ ≤
        ∑ q' : p.primesOver (NumberField.RingOfIntegers K),
          q'.1.ramificationIdx ℤ * q'.1.inertiaDeg ℤ := by
    exact Finset.single_le_sum
      (f := fun q' : p.primesOver (NumberField.RingOfIntegers K) ↦
        q'.1.ramificationIdx ℤ * q'.1.inertiaDeg ℤ)
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ q)
  have hterm :
      v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ ≤
        ∑ q' : p.primesOver (NumberField.RingOfIntegers K),
          q'.1.ramificationIdx ℤ * q'.1.inertiaDeg ℤ := by
    simpa only [q] using hterm'
  have hram : 0 < v.asIdeal.ramificationIdx ℤ :=
    Ideal.ramificationIdx_pos v.asIdeal ℤ
  calc
    v.asIdeal.inertiaDeg ℤ ≤
        v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ := by
      exact Nat.le_mul_of_pos_left _ hram
    _ ≤ ∑ q' : p.primesOver (NumberField.RingOfIntegers K),
          q'.1.ramificationIdx ℤ * q'.1.inertiaDeg ℤ := hterm
    _ = Module.finrank ℤ (NumberField.RingOfIntegers K) := by
      exact Ideal.sum_ramification_inertia_eq_finrank p
        (NumberField.RingOfIntegers K)
    _ = Module.finrank ℚ K := NumberField.RingOfIntegers.rank K

/-- The absolute norm of a height-one prime is the inertia-degree power of
the rational prime below it. -/
lemma numberFieldPrime_absNorm_eq_pow_below
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.asIdeal.absNorm =
      numberFieldPrimeBelow v ^ v.asIdeal.inertiaDeg ℤ := by
  symm
  simpa only [numberFieldPrimeBelow] using
    (Ideal.pow_inertiaDeg
      (Ideal.absNorm (Ideal.under ℤ v.asIdeal)) v.asIdeal)

/-- Bounding the rational prime below a height-one prime also bounds the
absolute norm of that prime, with exponent the degree of the field. -/
lemma numberFieldPrime_absNorm_le_pow
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) {B : ℕ}
    (hB : numberFieldPrimeBelow v ≤ B) :
    v.asIdeal.absNorm ≤ B ^ Module.finrank ℚ K := by
  have hBpos : 0 < B :=
    (numberFieldPrimeBelow_prime v).pos.trans_le hB
  rw [numberFieldPrime_absNorm_eq_pow_below]
  calc
    numberFieldPrimeBelow v ^ v.asIdeal.inertiaDeg ℤ ≤
        B ^ v.asIdeal.inertiaDeg ℤ :=
      Nat.pow_le_pow_left hB _
    _ ≤ B ^ Module.finrank ℚ K :=
      Nat.pow_le_pow_right hBpos
        (numberFieldPrime_inertiaDeg_le_finrank v)

/-- Every prime in the finite support of a rational integer lies over a
rational prime dividing that integer. -/
lemma numberFieldPrimeBelow_dvd_natAbs_of_mem_support
    {K : Type*} [Field K] [NumberField K]
    (beta : ℤ) (hbeta : beta ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (hv : v ∈ numberFieldPrimeSupport
      (Units.mk0 (beta : K) (Int.cast_ne_zero.mpr hbeta))) :
    numberFieldPrimeBelow v ∣ beta.natAbs := by
  have hval : v.valuation K
      (algebraMap (NumberField.RingOfIntegers K) K
        (beta : NumberField.RingOfIntegers K)) ≠ 1 := by
    simpa [numberFieldPrimeSupport] using hv
  have hmem : (beta : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
    have hnot : ¬ ((beta : NumberField.RingOfIntegers K) ∉ v.asIdeal) := by
      intro hnmem
      exact hval ((v.valuation_eq_one_iff_notMem (K := K)).mpr hnmem)
    simpa using hnot
  have hdvd : ((numberFieldPrimeBelow v : ℕ) : ℤ) ∣ beta := by
    exact (Int.cast_mem_ideal_iff (I := v.asIdeal)).mp hmem
  exact Int.natCast_dvd.mp hdvd

/-- Every height-one prime supporting a nonzero rational integer has norm
at most the field-degree power of the absolute value of that integer. -/
lemma numberFieldPrime_absNorm_le_natAbs_pow_of_mem_support
    {K : Type*} [Field K] [NumberField K]
    (beta : ℤ) (hbeta : beta ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (hv : v ∈ numberFieldPrimeSupport
      (Units.mk0 (beta : K) (Int.cast_ne_zero.mpr hbeta))) :
    v.asIdeal.absNorm ≤ beta.natAbs ^ Module.finrank ℚ K := by
  apply numberFieldPrime_absNorm_le_pow v
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hbeta)
    (numberFieldPrimeBelow_dvd_natAbs_of_mem_support
      beta hbeta v hv)

/-- Degree-eight specialization of the rational-integer support bound. -/
lemma numberFieldPrime_absNorm_le_eight_of_mem_support
    {K : Type*} [Field K] [NumberField K]
    (beta : ℤ) (hbeta : beta ≠ 0) {J : ℕ}
    (hbetaJ : beta.natAbs ≤ J)
    (hdeg : Module.finrank ℚ K ≤ 8)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (hv : v ∈ numberFieldPrimeSupport
      (Units.mk0 (beta : K) (Int.cast_ne_zero.mpr hbeta))) :
    v.asIdeal.absNorm ≤ J ^ 8 := by
  have hJpos : 0 < J := (Int.natAbs_pos.mpr hbeta).trans_le hbetaJ
  calc
    v.asIdeal.absNorm ≤ beta.natAbs ^ Module.finrank ℚ K :=
      numberFieldPrime_absNorm_le_natAbs_pow_of_mem_support
        beta hbeta v hv
    _ ≤ J ^ Module.finrank ℚ K :=
      Nat.pow_le_pow_left hbetaJ _
    _ ≤ J ^ 8 := Nat.pow_le_pow_right hJpos hdeg

lemma numberFieldPrimeBelow_mem_primeFactors_of_mem_support
    {K : Type*} [Field K] [NumberField K]
    (beta : ℤ) (hbeta : beta ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (hv : v ∈ numberFieldPrimeSupport
      (Units.mk0 (beta : K) (Int.cast_ne_zero.mpr hbeta))) :
    numberFieldPrimeBelow v ∈ beta.natAbs.primeFactors := by
  exact (numberFieldPrimeBelow_prime v).mem_primeFactors
    (numberFieldPrimeBelow_dvd_natAbs_of_mem_support beta hbeta v hv)
    (Int.natAbs_ne_zero.mpr hbeta)

/-- The finite-prime support of a rational integer in a number field has
at most `[K : ℚ]` primes above each rational prime divisor. -/
lemma numberFieldPrimeSupport_card_le
    {K : Type*} [Field K] [NumberField K]
    (beta : ℤ) (hbeta : beta ≠ 0) :
    Nat.card (numberFieldPrimeSupport
        (Units.mk0 (beta : K) (Int.cast_ne_zero.mpr hbeta))) ≤
      Module.finrank ℚ K * beta.natAbs.primeFactors.card := by
  classical
  let S := numberFieldPrimeSupport
    (Units.mk0 (beta : K) (Int.cast_ne_zero.mpr hbeta))
  have hS : S.Finite := numberFieldPrimeSupport_finite _
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card S hS]
  calc
    hS.toFinset.card ≤ Module.finrank ℚ K *
        (hS.toFinset.image numberFieldPrimeBelow).card := by
      apply Finset.card_le_mul_card_image
      intro p hp
      obtain ⟨v, hvS, hvp⟩ := Finset.mem_image.mp hp
      have hpprime : p.Prime := by
        rw [← hvp]
        exact numberFieldPrimeBelow_prime v
      let P : Ideal ℤ := Ideal.span {(p : ℤ)}
      have hP0 : P ≠ ⊥ := by
        simp [P, hpprime.ne_zero]
      let hPprime : P.IsPrime :=
        Ideal.isPrime_span_singleton_of_prime
          ((Nat.prime_iff_prime_int).mp hpprime)
      let hPmax : P.IsMaximal := hPprime.isMaximal hP0
      calc
        (hS.toFinset.filter (fun v ↦ numberFieldPrimeBelow v = p)).card ≤
            (IsDedekindDomain.primesOverFinset P
              (NumberField.RingOfIntegers K)).card := by
          apply Finset.card_le_card_of_injOn
              (fun w ↦ w.asIdeal)
          · intro w hw
            change w ∈ hS.toFinset.filter
              (fun v ↦ numberFieldPrimeBelow v = p) at hw
            rw [Finset.mem_filter] at hw
            apply (IsDedekindDomain.mem_primesOverFinset_iff hP0 _).mpr
            refine ⟨w.isPrime, ?_⟩
            have hnorm : Ideal.absNorm (Ideal.under ℤ w.asIdeal) = p := by
              simpa [numberFieldPrimeBelow] using hw.2
            have hunder : Ideal.under ℤ w.asIdeal = P := by
              calc
                Ideal.under ℤ w.asIdeal =
                    Ideal.span
                      {((Ideal.absNorm (Ideal.under ℤ w.asIdeal) : ℕ) : ℤ)} :=
                  (Int.ideal_span_absNorm_eq_self _).symm
                _ = P := by rw [hnorm]
            exact ⟨hunder.symm⟩
          · intro v₁ _hv₁ v₂ _hv₂ hv
            exact IsDedekindDomain.HeightOneSpectrum.ext hv
        _ ≤ Module.finrank ℚ K := by
          exact Ideal.card_primesOverFinset_le_finrank
            (R := ℤ) (S := NumberField.RingOfIntegers K)
            (K := ℚ) (L := K) hP0
    _ ≤ Module.finrank ℚ K * beta.natAbs.primeFactors.card := by
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      intro p hp
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      exact numberFieldPrimeBelow_mem_primeFactors_of_mem_support
        beta hbeta v (hS.mem_toFinset.mp hv)

/-- Raising a nonzero number-field ideal to the class number makes it
principal.  This supplies the principal prime-power generators used in
the standard construction of generators for an `S`-unit group. -/
lemma numberField_ideal_pow_classNumber_isPrincipal
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    Submodule.IsPrincipal (I ^ NumberField.classNumber K) := by
  rw [← ClassGroup.mk0_eq_one_iff
    (pow_mem (mem_nonZeroDivisors_of_ne_zero hI) (NumberField.classNumber K))]
  change ClassGroup.mk0
    ((⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ :
      nonZeroDivisors (Ideal (NumberField.RingOfIntegers K))) ^
        NumberField.classNumber K) = 1
  rw [map_pow]
  simpa only [NumberField.classNumber, Nat.card_eq_fintype_card] using
    (pow_card_eq_one' (x := ClassGroup.mk0
      ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩))

/-- A nonzero ideal has a nonzero integral generator after it is raised
to the class number. -/
lemma exists_numberField_ideal_pow_classNumber_generator
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧
      I ^ NumberField.classNumber K = Ideal.span {a} := by
  obtain ⟨a, ha⟩ :=
    (numberField_ideal_pow_classNumber_isPrincipal I hI).principal
  refine ⟨a, ?_, ha⟩
  intro ha0
  subst a
  rw [Submodule.span_zero_singleton] at ha
  exact (pow_ne_zero _ hI) ha

/-- A fixed integral generator of the class-number power of a
number-field prime ideal. -/
noncomputable def numberFieldPrimeClassGenerator
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    NumberField.RingOfIntegers K :=
  Classical.choose (exists_numberField_ideal_pow_classNumber_generator
    v.asIdeal v.ne_bot)

lemma numberFieldPrimeClassGenerator_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    numberFieldPrimeClassGenerator v ≠ 0 :=
  (Classical.choose_spec
    (exists_numberField_ideal_pow_classNumber_generator
      v.asIdeal v.ne_bot)).1

lemma numberFieldPrimeClassGenerator_span
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.asIdeal ^ NumberField.classNumber K =
      Ideal.span {numberFieldPrimeClassGenerator v} :=
  (Classical.choose_spec
    (exists_numberField_ideal_pow_classNumber_generator
      v.asIdeal v.ne_bot)).2

/-- A class-number prime-power generator may be multiplied by a global
unit so that its mixed embedding lies in the Dirichlet fundamental cone.
The principal ideal, and hence every finite valuation, is unchanged. -/
theorem exists_numberFieldPrimeClassGenerator_mem_fundamentalCone
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    ∃ a : NumberField.RingOfIntegers K,
      a ≠ 0 ∧
      v.asIdeal ^ NumberField.classNumber K = Ideal.span {a} ∧
      NumberField.mixedEmbedding K (a : K) ∈
        NumberField.mixedEmbedding.fundamentalCone K := by
  let a₀ := numberFieldPrimeClassGenerator v
  have ha₀ : a₀ ≠ 0 := numberFieldPrimeClassGenerator_ne_zero v
  have ha₀emb : NumberField.mixedEmbedding K (a₀ : K) ≠ 0 := by
    simpa only [map_zero] using
      (NumberField.mixedEmbedding_injective K).ne
        (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha₀)
  have hnorm : NumberField.mixedEmbedding.norm
      (NumberField.mixedEmbedding K (a₀ : K)) ≠ 0 := by
    intro h
    exact ha₀emb ((NumberField.mixedEmbedding.norm_eq_zero_iff'
      (x := NumberField.mixedEmbedding K (a₀ : K)) ⟨(a₀ : K), rfl⟩).mp h)
  obtain ⟨u, hu⟩ :=
    NumberField.mixedEmbedding.fundamentalCone.exists_unit_smul_mem hnorm
  refine ⟨u * a₀, ?_, ?_, ?_⟩
  · exact mul_ne_zero (Units.ne_zero u) ha₀
  · calc
      v.asIdeal ^ NumberField.classNumber K = Ideal.span {a₀} :=
        numberFieldPrimeClassGenerator_span v
      _ = Ideal.span {u * a₀} :=
        (Ideal.span_singleton_mul_left_unit u.isUnit a₀).symm
  · simpa only [NumberField.mixedEmbedding.unitSMul_smul, map_mul] using hu

/-- A chosen fundamental-cone-normalized generator of the class-number
power of a number-field prime ideal. -/
noncomputable def numberFieldPrimeClassNormalizedGenerator
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    NumberField.RingOfIntegers K :=
  Classical.choose
    (exists_numberFieldPrimeClassGenerator_mem_fundamentalCone v)

lemma numberFieldPrimeClassNormalizedGenerator_ne_zero
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    numberFieldPrimeClassNormalizedGenerator v ≠ 0 :=
  (Classical.choose_spec
    (exists_numberFieldPrimeClassGenerator_mem_fundamentalCone v)).1

lemma numberFieldPrimeClassNormalizedGenerator_span
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.asIdeal ^ NumberField.classNumber K =
      Ideal.span {numberFieldPrimeClassNormalizedGenerator v} :=
  (Classical.choose_spec
    (exists_numberFieldPrimeClassGenerator_mem_fundamentalCone v)).2.1

lemma numberFieldPrimeClassNormalizedGenerator_mem_fundamentalCone
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    NumberField.mixedEmbedding K
        (numberFieldPrimeClassNormalizedGenerator v : K) ∈
      NumberField.mixedEmbedding.fundamentalCone K :=
  (Classical.choose_spec
    (exists_numberFieldPrimeClassGenerator_mem_fundamentalCone v)).2.2

/-- Membership in the Dirichlet fundamental cone supplies real
coordinates in `[0,1)` on the logarithms of the fixed fundamental units. -/
lemma fundamentalCone_logMap_eq_sum_fundSystem
    {K : Type*} [Field K] [NumberField K]
    {x : NumberField.mixedEmbedding.mixedSpace K}
    (hx : x ∈ NumberField.mixedEmbedding.fundamentalCone K) :
    ∃ c : Fin (NumberField.Units.rank K) → ℝ,
      (∀ i, c i ∈ Set.Ico (0 : ℝ) 1) ∧
      NumberField.mixedEmbedding.logMap x =
        ∑ i, c i • NumberField.Units.logEmbedding K
          (Additive.ofMul (NumberField.Units.fundSystem K i)) := by
  let B := (NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
    (NumberField.Units.unitLattice K)
  let c : Fin (NumberField.Units.rank K) → ℝ := fun i ↦
    B.repr (NumberField.mixedEmbedding.logMap x) i
  refine ⟨c, ?_, ?_⟩
  · have hfd := hx.1
    change NumberField.mixedEmbedding.logMap x ∈
      ZSpan.fundamentalDomain B at hfd
    exact (ZSpan.mem_fundamentalDomain B).mp hfd
  · calc
      NumberField.mixedEmbedding.logMap x =
          ∑ i, c i • B i := (B.sum_repr _).symm
      _ = ∑ i, c i • NumberField.Units.logEmbedding K
          (Additive.ofMul (NumberField.Units.fundSystem K i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hBi : B i = NumberField.Units.logEmbedding K
            (Additive.ofMul (NumberField.Units.fundSystem K i)) := by
          dsimp only [B]
          rw [Module.Basis.ofZLatticeBasis_apply,
            NumberField.Units.logEmbedding_fundSystem]
        rw [hBi]

/-- A linear combination with coefficients in `[0,1]` is bounded in
absolute value by the sum of the absolute values of its terms. -/
lemma abs_sum_mul_le_sum_abs
    {ι : Type*} [Fintype ι] (c z : ι → ℝ)
    (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) :
    |∑ i, c i * z i| ≤ ∑ i, |z i| := by
  calc
    |∑ i, c i * z i| ≤ ∑ i, |c i * z i| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun i ↦ c i * z i) Finset.univ
    _ ≤ ∑ i, |z i| := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul, abs_of_nonneg (hc i).1]
      exact mul_le_of_le_one_left (abs_nonneg (z i)) (hc i).2

/-- The logarithmic embedding of a fundamental-cone representative is
pointwise bounded by the absolute logarithmic embeddings of the fixed
fundamental units. -/
lemma fundamentalCone_abs_logMap_le
    {K : Type*} [Field K] [NumberField K]
    {x : NumberField.mixedEmbedding.mixedSpace K}
    (hx : x ∈ NumberField.mixedEmbedding.fundamentalCone K)
    (w : {w : NumberField.InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    |NumberField.mixedEmbedding.logMap x w| ≤
      ∑ i : Fin (NumberField.Units.rank K),
        |NumberField.Units.logEmbedding K
          (Additive.ofMul (NumberField.Units.fundSystem K i)) w| := by
  obtain ⟨c, hc, hsum⟩ := fundamentalCone_logMap_eq_sum_fundSystem hx
  have hw := congrFun hsum w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw
  rw [hw]
  apply abs_sum_mul_le_sum_abs c
  intro i
  exact ⟨(hc i).1, (hc i).2.le⟩

/-- On an algebraic integer the mixed-embedding norm is the natural
absolute value of its integral algebraic norm. -/
lemma mixedEmbedding_norm_ringOfIntegers
    {K : Type*} [Field K] [NumberField K]
    (a : NumberField.RingOfIntegers K) :
    NumberField.mixedEmbedding.norm
        (NumberField.mixedEmbedding K (a : K)) =
      ((Algebra.norm ℤ a).natAbs : ℝ) := by
  symm
  rw [Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs,
    Algebra.coe_norm_int,
    ← NumberField.mixedEmbedding.norm_eq_norm]

/-- The nonarchimedean terms in the height of an algebraic integer
vanish. -/
lemma numberField_logHeight_ringOfIntegers_eq_sum
    {K : Type*} [Field K] [NumberField K]
    (a : NumberField.RingOfIntegers K) :
    Height.logHeight₁ (a : K) =
      ∑ w : NumberField.InfinitePlace K,
        w.mult * Real.posLog (w (a : K)) := by
  rw [NumberField.logHeight₁_eq]
  have hfin :
      ∑ᶠ v : NumberField.FinitePlace K,
          Real.posLog (v (a : K)) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro v
    rw [Real.posLog_eq_zero_iff,
      abs_of_nonneg (apply_nonneg v (a : K))]
    rw [← NumberField.FinitePlace.norm_embedding_eq v (a : K)]
    exact NumberField.FinitePlace.norm_le_one (K := K) v.maximalIdeal a
  rw [hfin, add_zero]

/-- Positive logarithms commute with multiplication by a positive natural
weight after taking the positive part. -/
lemma natCast_mul_posLog_eq_max_zero
    (m : ℕ) (hm : 0 < m) (x : ℝ) :
    (m : ℝ) * Real.posLog x = max 0 ((m : ℝ) * Real.log x) := by
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by positivity
  rw [Real.posLog_apply, mul_max_of_nonneg 0 (Real.log x) hmR,
    mul_zero]

/-- If a distinguished logarithm and the remaining logarithms sum to a
nonnegative number `N`, the sum of all their positive parts is bounded by
`N` plus twice the absolute mass of the remaining logarithms. -/
lemma max_zero_add_sum_max_zero_le
    {ι : Type*} [Fintype ι] (l₀ N : ℝ) (g : ι → ℝ)
    (hN : 0 ≤ N) (hsum : l₀ + ∑ i, g i = N) :
    max 0 l₀ + ∑ i, max 0 (g i) ≤
      N + 2 * ∑ i, |g i| := by
  have habsSum : |∑ i, g i| ≤ ∑ i, |g i| := by
    simpa using Finset.abs_sum_le_sum_abs g Finset.univ
  have hl₀ : l₀ = N - ∑ i, g i := by linarith
  have hl₀max : max 0 l₀ ≤ N + ∑ i, |g i| := by
    rw [hl₀]
    calc
      max 0 (N - ∑ i, g i) ≤ |N - ∑ i, g i| :=
        max_le (abs_nonneg _) (le_abs_self _)
      _ ≤ |N| + |∑ i, g i| := abs_sub _ _
      _ = N + |∑ i, g i| := by rw [abs_of_nonneg hN]
      _ ≤ N + ∑ i, |g i| := add_le_add (le_refl N) habsSum
  have hrest : ∑ i, max 0 (g i) ≤ ∑ i, |g i| := by
    apply Finset.sum_le_sum
    intro i _hi
    exact max_le (abs_nonneg _) (le_abs_self _)
  linarith

/-- An algebraic integer normalized into the Dirichlet fundamental cone
has height bounded by its norm and the logarithmic size of the fixed
fundamental units.  This is the elementary generator-normalization bound
used before the logarithmic-form estimate. -/
theorem numberField_logHeight_fundamentalCone_le
    {K : Type*} [Field K] [NumberField K]
    (a : NumberField.RingOfIntegers K) (ha : a ≠ 0)
    (hcone : NumberField.mixedEmbedding K (a : K) ∈
      NumberField.mixedEmbedding.fundamentalCone K) :
    Height.logHeight₁ (a : K) ≤
      Real.log ((Algebra.norm ℤ a).natAbs : ℝ) +
        2 * ∑ w : {w : NumberField.InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          ((∑ i : Fin (NumberField.Units.rank K),
              |NumberField.Units.logEmbedding K
                (Additive.ofMul (NumberField.Units.fundSystem K i)) w|) +
            Real.log ((Algebra.norm ℤ a).natAbs : ℝ)) := by
  let w₀ := NumberField.Units.dirichletUnitTheorem.w₀ (K := K)
  let N : ℝ := Real.log ((Algebra.norm ℤ a).natAbs : ℝ)
  let g : {w : NumberField.InfinitePlace K // w ≠ w₀} → ℝ := fun w ↦
    (w.1.mult : ℝ) * Real.log (w.1 (a : K))
  let l₀ : ℝ := (w₀.mult : ℝ) * Real.log (w₀ (a : K))
  have haNorm : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have hnatNorm : 0 < (Algebra.norm ℤ a).natAbs :=
    Int.natAbs_pos.mpr haNorm
  have hN : 0 ≤ N := by
    apply Real.log_nonneg
    exact_mod_cast hnatNorm
  have haK : (a : K) ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hsumAll :=
    NumberField.mixedEmbedding.fundamentalCone.sum_expMap_symm_apply haK
  have hnormQ :
      ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) =
        ((Algebra.norm ℤ a).natAbs : ℝ) := by
    rw [← NumberField.mixedEmbedding.norm_eq_norm]
    exact mixedEmbedding_norm_ringOfIntegers a
  have hlogNorm : Real.log (|Algebra.norm ℚ (a : K)| : ℚ) = N := by
    rw [hnormQ]
  have hsumAll' :
      ∑ w : NumberField.InfinitePlace K,
          (w.mult : ℝ) * Real.log (w (a : K)) = N := by
    simpa only [NumberField.mixedEmbedding.fundamentalCone.expMap_symm_apply,
      NumberField.mixedEmbedding.normAtAllPlaces_mixedEmbedding] using
        hsumAll.trans hlogNorm
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsumAll'
  have hsum : l₀ + ∑ w, g w = N := by
    simpa only [l₀, g] using hsumAll'
  have hheightMax : Height.logHeight₁ (a : K) =
      max 0 l₀ + ∑ w, max 0 (g w) := by
    rw [numberField_logHeight_ringOfIntegers_eq_sum,
      Fintype.sum_eq_add_sum_subtype_ne _ w₀]
    rw [natCast_mul_posLog_eq_max_zero w₀.mult
      NumberField.InfinitePlace.mult_pos]
    apply congrArg (fun z : ℝ ↦ max 0 l₀ + z)
    apply Finset.sum_congr rfl
    intro w _hw
    exact natCast_mul_posLog_eq_max_zero w.1.mult
      NumberField.InfinitePlace.mult_pos _
  have hbase : Height.logHeight₁ (a : K) ≤
      N + 2 * ∑ w, |g w| := by
    rw [hheightMax]
    exact max_zero_add_sum_max_zero_le l₀ N g hN hsum
  have hg (w : {w : NumberField.InfinitePlace K // w ≠ w₀}) :
      |g w| ≤
        |NumberField.mixedEmbedding.logMap
          (NumberField.mixedEmbedding K (a : K)) w| + N := by
    have hnorm : NumberField.mixedEmbedding.norm
        (NumberField.mixedEmbedding K (a : K)) =
        ((Algebra.norm ℤ a).natAbs : ℝ) :=
      mixedEmbedding_norm_ringOfIntegers a
    have hDpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) :=
      Nat.cast_pos.mpr Module.finrank_pos
    have hmDnat : w.1.mult ≤ Module.finrank ℚ K := by
      rw [← NumberField.InfinitePlace.sum_mult_eq]
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ w.1)
    have hmD : (w.1.mult : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast hmDnat
    have hratio : (0 : ℝ) ≤
        (w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ := by positivity
    have hratioOne :
        (w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ ≤ 1 := by
      exact mul_inv_le_one_of_le₀ hmD hDpos.le
    have hdecomp : g w =
        NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w +
          ((w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹) * N := by
      rw [NumberField.mixedEmbedding.logMap_apply,
        NumberField.mixedEmbedding.normAtPlace_apply, hnorm]
      dsimp only [g, N]
      ring
    rw [hdecomp]
    calc
      |NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w +
          ((w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹) * N| ≤
          |NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w| +
            |((w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹) * N| :=
        abs_add_le _ _
      _ = |NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w| +
          ((w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹) * N := by
        rw [abs_of_nonneg (mul_nonneg hratio hN)]
      _ ≤ |NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w| + N := by
        gcongr
        exact mul_le_of_le_one_left hN hratioOne
  calc
    Height.logHeight₁ (a : K) ≤ N + 2 * ∑ w, |g w| := hbase
    _ ≤ N + 2 * ∑ w,
        (|NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w| + N) := by
      gcongr with w
      exact hg w
    _ ≤ N + 2 * ∑ w,
        ((∑ i : Fin (NumberField.Units.rank K),
            |NumberField.Units.logEmbedding K
              (Additive.ofMul (NumberField.Units.fundSystem K i)) w|) + N) := by
      gcongr with w
      exact fundamentalCone_abs_logMap_le hcone w
    _ = Real.log ((Algebra.norm ℤ a).natAbs : ℝ) +
        2 * ∑ w : {w : NumberField.InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          ((∑ i : Fin (NumberField.Units.rank K),
              |NumberField.Units.logEmbedding K
                (Additive.ofMul (NumberField.Units.fundSystem K i)) w|) +
            Real.log ((Algebra.norm ℤ a).natAbs : ℝ)) := rfl

/-- The integral norm of a normalized prime-class generator is the class
number power of the norm of the underlying prime ideal. -/
lemma numberFieldPrimeClassNormalizedGenerator_norm
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    (Algebra.norm ℤ (numberFieldPrimeClassNormalizedGenerator v)).natAbs =
      v.asIdeal.absNorm ^ NumberField.classNumber K := by
  calc
    (Algebra.norm ℤ
        (numberFieldPrimeClassNormalizedGenerator v)).natAbs =
        Ideal.absNorm
          (Ideal.span {numberFieldPrimeClassNormalizedGenerator v}) :=
      (Ideal.absNorm_span_singleton _).symm
    _ = Ideal.absNorm
          (v.asIdeal ^ NumberField.classNumber K) := by
      rw [numberFieldPrimeClassNormalizedGenerator_span]
    _ = v.asIdeal.absNorm ^ NumberField.classNumber K := by
      rw [map_pow]

/-- Explicit height bound for the normalized class-number generator attached
to a height-one prime.  Unlike an arbitrary principal-ideal generator, this
choice has bounded Dirichlet coordinates. -/
theorem numberFieldPrimeClassNormalizedGenerator_logHeight_le
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    Height.logHeight₁
        ((numberFieldPrimeClassNormalizedGenerator v :
          NumberField.RingOfIntegers K) : K) ≤
      Real.log
          ((v.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) +
        2 * ∑ w : {w : NumberField.InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          ((∑ i : Fin (NumberField.Units.rank K),
              |NumberField.Units.logEmbedding K
                (Additive.ofMul (NumberField.Units.fundSystem K i)) w|) +
            Real.log
              ((v.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ)) := by
  have h := numberField_logHeight_fundamentalCone_le
    (numberFieldPrimeClassNormalizedGenerator v)
    (numberFieldPrimeClassNormalizedGenerator_ne_zero v)
    (numberFieldPrimeClassNormalizedGenerator_mem_fundamentalCone v)
  rw [numberFieldPrimeClassNormalizedGenerator_norm] at h
  exact h

/-- At its own prime, the chosen class-number generator has valuation
exactly the negative class number. -/
lemma numberFieldPrimeClassGenerator_valuation_self
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.valuation K (numberFieldPrimeClassGenerator v : K) =
      WithZero.exp (-(NumberField.classNumber K : ℤ)) := by
  rw [v.valuation_of_algebraMap,
    v.intValuation_eq_exp_neg_multiplicity
      (numberFieldPrimeClassGenerator_ne_zero v),
    ← numberFieldPrimeClassGenerator_span]
  rw [multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime v.ne_bot v.isPrime)]

/-- The fundamental-cone-normalized generator has the same finite valuation
at its defining prime as any generator of the same principal ideal. -/
lemma numberFieldPrimeClassNormalizedGenerator_valuation_self
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.valuation K (numberFieldPrimeClassNormalizedGenerator v : K) =
      WithZero.exp (-(NumberField.classNumber K : ℤ)) := by
  rw [v.valuation_of_algebraMap,
    v.intValuation_eq_exp_neg_multiplicity
      (numberFieldPrimeClassNormalizedGenerator_ne_zero v),
    ← numberFieldPrimeClassNormalizedGenerator_span]
  rw [multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime v.ne_bot v.isPrime)]

/-- The chosen prime-power generator, regarded as a nonzero element of
the number field. -/
noncomputable def numberFieldPrimeClassUnit
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) : Kˣ :=
  Units.mk0 (numberFieldPrimeClassNormalizedGenerator v : K)
    (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr
      (numberFieldPrimeClassNormalizedGenerator_ne_zero v))

/-- A class-number prime-power generator is supported only at its own
height-one prime. -/
lemma numberFieldPrimeClassUnit_mem_singleton_supportedUnits
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    numberFieldPrimeClassUnit v ∈ ({v} : Set
      (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K := by
  intro w hw
  change w.valuation K
    ((numberFieldPrimeClassNormalizedGenerator v :
      NumberField.RingOfIntegers K) : K) = 1
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hmem
  have hpowle : v.asIdeal ^ NumberField.classNumber K ≤ w.asIdeal := by
    rw [numberFieldPrimeClassNormalizedGenerator_span]
    exact (Ideal.span_singleton_le_iff_mem w.asIdeal).mpr hmem
  have hvle : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hpowle
  have hideals : v.asIdeal = w.asIdeal :=
    Ideal.IsMaximal.eq_of_le inferInstance w.isPrime.ne_top hvle
  have hvw : v = w := IsDedekindDomain.HeightOneSpectrum.ext hideals
  exact hw (by simpa only [Set.mem_singleton_iff] using hvw.symm)

/-- The prime-power generator at a prime belonging to `S` is an
`S`-unit. -/
lemma numberFieldPrimeClassUnit_mem_supportedUnits
    {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))}
    {v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)} (hv : v ∈ S) :
    numberFieldPrimeClassUnit v ∈ S.unit K := by
  intro w hw
  exact numberFieldPrimeClassUnit_mem_singleton_supportedUnits v w (by
    show w ≠ v
    intro hwv
    exact hw (hwv ▸ hv))

/-- The finite family of class-number prime-power generators inside an
`S`-unit group. -/
noncomputable def numberFieldPrimeClassSupportedUnit
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v : S) : S.unit K :=
  ⟨numberFieldPrimeClassUnit v,
    numberFieldPrimeClassUnit_mem_supportedUnits v.property⟩

/-- If two nonzero algebraic integers multiply to `β`, then each is an
`S`-unit for the finite set of primes supporting `β`. -/
lemma integral_factors_mem_supported_units
    {K : Type*} [Field K] [NumberField K]
    {a b β : K} (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hprod : a * b = β) :
    let au : Kˣ := Units.mk0 a ha0
    let bu : Kˣ := Units.mk0 b hb0
    let βu : Kˣ := Units.mk0 β (hprod ▸ mul_ne_zero ha0 hb0)
    au ∈ (numberFieldPrimeSupport βu).unit K ∧
      bu ∈ (numberFieldPrimeSupport βu).unit K := by
  dsimp only
  let au : Kˣ := Units.mk0 a ha0
  let bu : Kˣ := Units.mk0 b hb0
  let βu : Kˣ := Units.mk0 β (hprod ▸ mul_ne_zero ha0 hb0)
  have habUnits : au * bu = βu := by
    ext
    exact hprod
  have hmem (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
      (hv : v ∉ numberFieldPrimeSupport βu) :
      v.valuation K au = 1 ∧ v.valuation K bu = 1 := by
    have hva : v.valuation K au ≤ 1 := by
      change v.valuation K
        ((⟨a, ha⟩ : NumberField.RingOfIntegers K) : K) ≤ 1
      exact v.valuation_le_one (K := K)
        (⟨a, ha⟩ : NumberField.RingOfIntegers K)
    have hvb : v.valuation K bu ≤ 1 := by
      change v.valuation K
        ((⟨b, hb⟩ : NumberField.RingOfIntegers K) : K) ≤ 1
      exact v.valuation_le_one (K := K)
        (⟨b, hb⟩ : NumberField.RingOfIntegers K)
    have hvβ : v.valuation K βu = 1 := by
      simpa [numberFieldPrimeSupport] using hv
    have hvprod : v.valuation K au * v.valuation K bu = 1 := by
      calc
        v.valuation K au * v.valuation K bu =
            v.valuation K (((au * bu : Kˣ) : K)) := by
          change v.valuation K (au : K) * v.valuation K (bu : K) =
            v.valuation K ((au : K) * (bu : K))
          exact (map_mul (v.valuation K) (au : K) (bu : K)).symm
        _ = v.valuation K βu := by rw [habUnits]
        _ = 1 := hvβ
    exact ⟨eq_one_of_one_le_mul_left hva hvb hvprod.ge,
      eq_one_of_one_le_mul_right hva hvb hvprod.ge⟩
  constructor
  · intro v hv
    exact (hmem v hv).1
  · intro v hv
    exact (hmem v hv).2

/-- A single nondegenerate Pell edge gives two algebraic-integer factor
values, both supported on the finite set of primes dividing its right-hand
side.  This packages the exact input passed to an `S`-unit equation. -/
theorem pell_factor_pair_supported_units
    {K : Type*} [Field K] [NumberField K]
    {sₐ s_b : K} {γₐ γ_b β xₐ x_b : ℤ}
    (hsₐ : sₐ ^ 2 = (γₐ : K)) (hs_b : s_b ^ 2 = (γ_b : K))
    (hPell : γₐ * xₐ ^ 2 - γ_b * x_b ^ 2 = β) (β_ne : β ≠ 0) :
    let m := pellValueMinus sₐ s_b xₐ x_b
    let p := pellValuePlus sₐ s_b xₐ x_b
    let βu : Kˣ := Units.mk0 (β : K) (Int.cast_ne_zero.mpr β_ne)
    ∃ hm : m ≠ 0, ∃ hp : p ≠ 0,
      IsIntegral ℤ m ∧ IsIntegral ℤ p ∧ m * p = (β : K) ∧
      (numberFieldPrimeSupport βu).Finite ∧
      Units.mk0 m hm ∈ (numberFieldPrimeSupport βu).unit K ∧
      Units.mk0 p hp ∈ (numberFieldPrimeSupport βu).unit K := by
  dsimp only
  let m := pellValueMinus sₐ s_b xₐ x_b
  let p := pellValuePlus sₐ s_b xₐ x_b
  have hprod : m * p = (β : K) :=
    pellValueMinus_mul_plus hsₐ hs_b hPell
  have hβK : (β : K) ≠ 0 := Int.cast_ne_zero.mpr β_ne
  have hm : m ≠ 0 := by
    intro hm0
    apply hβK
    rw [← hprod, hm0, zero_mul]
  have hp : p ≠ 0 := by
    intro hp0
    apply hβK
    rw [← hprod, hp0, mul_zero]
  have hmInt : IsIntegral ℤ m := isIntegral_pellValueMinus hsₐ hs_b
  have hpInt : IsIntegral ℤ p := isIntegral_pellValuePlus hsₐ hs_b
  have hmem := integral_factors_mem_supported_units hmInt hpInt hm hp hprod
  refine ⟨hm, hp, hmInt, hpInt, hprod,
    numberFieldPrimeSupport_finite (Units.mk0 (β : K) hβK), ?_, ?_⟩
  · exact hmem.1
  · exact hmem.2

namespace SupportedUnits

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Set (HeightOneSpectrum R)) (F : Type*) [Field F]
  [Algebra R F] [IsFractionRing R F]

/-- The valuation vector of an `S`-unit at the primes belonging to `S`. -/
noncomputable def valuationMap : S.unit F →* (↑S → Multiplicative ℤ) where
  toFun u v := (v : HeightOneSpectrum R).valuationOfNeZero (u : Fˣ)
  map_one' := by ext v; simp
  map_mul' u u' := by ext v; simp

@[simp] lemma valuationMap_apply (u : S.unit F) (v : ↑S) :
    valuationMap S F u v =
      (v : HeightOneSpectrum R).valuationOfNeZero (u : Fˣ) := rfl

/-- At a finite prime, the additive valuation of a nonzero algebraic
integer is the negative of the multiplicity of its principal ideal.  This
is the exact bridge between the supported-unit coordinates used below and
ideal factorization. -/
lemma valuationOfNeZero_toAdd_algebraicInteger
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K) (ha0 : (a : K) ≠ 0) :
    (v.valuationOfNeZero (Units.mk0 (a : K) ha0)).toAdd =
      -(multiplicity v.asIdeal
        (Ideal.span ({a} : Set (NumberField.RingOfIntegers K))) : ℤ) := by
  have ha0' : a ≠ 0 := by
    rw [← NumberField.RingOfIntegers.coe_ne_zero_iff]
    exact ha0
  apply Multiplicative.ofAdd.injective
  rw [ofAdd_toAdd]
  apply WithZero.coe_injective
  rw [v.valuationOfNeZero_eq, ← WithZero.exp_eq_coe_ofAdd]
  change v.valuation K (a : K) =
    WithZero.exp (-(multiplicity v.asIdeal
      (Ideal.span ({a} : Set (NumberField.RingOfIntegers K))) : ℤ))
  rw [v.valuation_of_algebraMap,
    v.intValuation_eq_exp_neg_multiplicity ha0']

/-- If one algebraic integer divides another, every finite-prime
multiplicity of the first principal ideal is bounded by that of the
second. -/
lemma multiplicity_principal_le_of_mul_eq
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a b c : NumberField.RingOfIntegers K) (hc0 : c ≠ 0)
    (hab : a * b = c) :
    multiplicity v.asIdeal
        (Ideal.span ({a} : Set (NumberField.RingOfIntegers K))) ≤
      multiplicity v.asIdeal
        (Ideal.span ({c} : Set (NumberField.RingOfIntegers K))) := by
  apply v.multiplicity_le_of_ideal_ge
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact ⟨b, hab.symm⟩
  · simpa using hc0

/-- The finite-prime valuation of a quotient of nonzero algebraic
integers is bounded by the sum of the two principal-ideal
multiplicities. -/
lemma natAbs_valuationOfNeZero_toAdd_div_algebraicInteger_le
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a b : NumberField.RingOfIntegers K)
    (ha0 : (a : K) ≠ 0) (hb0 : (b : K) ≠ 0) :
    Int.natAbs ((v.valuationOfNeZero
      (Units.mk0 (a : K) ha0 / Units.mk0 (b : K) hb0)).toAdd) ≤
      multiplicity v.asIdeal
          (Ideal.span ({a} : Set (NumberField.RingOfIntegers K))) +
        multiplicity v.asIdeal
          (Ideal.span ({b} : Set (NumberField.RingOfIntegers K))) := by
  rw [map_div, toAdd_div]
  rw [valuationOfNeZero_toAdd_algebraicInteger,
    valuationOfNeZero_toAdd_algebraicInteger]
  simpa only [neg_sub_neg, Int.natAbs_natCast, Nat.add_comm] using
    Int.natAbs_sub_le
      (multiplicity v.asIdeal
        (Ideal.span ({b} : Set (NumberField.RingOfIntegers K))))
      (multiplicity v.asIdeal
        (Ideal.span ({a} : Set (NumberField.RingOfIntegers K))))

/-- The same quotient bound, stated for a supported unit whose ambient
field value is identified with the quotient.  This avoids losing the
finite-prime coordinates when a unit equation is packaged existentially. -/
lemma natAbs_valuationMap_toAdd_le_of_eq_div_algebraicInteger
    {K : Type*} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (u : S.unit K) (v : S)
    (a b : NumberField.RingOfIntegers K)
    (ha0 : (a : K) ≠ 0) (hb0 : (b : K) ≠ 0)
    (hu : (((u : Kˣ) : K)) = (a : K) / (b : K)) :
    Int.natAbs (valuationMap S K u v).toAdd ≤
      multiplicity v.1.asIdeal
          (Ideal.span ({a} : Set (NumberField.RingOfIntegers K))) +
        multiplicity v.1.asIdeal
          (Ideal.span ({b} : Set (NumberField.RingOfIntegers K))) := by
  have huUnits : (u : Kˣ) =
      Units.mk0 (a : K) ha0 / Units.mk0 (b : K) hb0 := by
    ext
    simpa using hu
  rw [valuationMap_apply, huUnits]
  exact natAbs_valuationOfNeZero_toAdd_div_algebraicInteger_le
    v.1 a b ha0 hb0

/-- If the numerator and denominator are integral factors of (possibly
different) rational integers, the finite coordinate of their quotient is
bounded by the corresponding two rational principal-ideal multiplicities. -/
lemma natAbs_valuationMap_toAdd_factor_ratio_le
    {K : Type*} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (u : S.unit K) (v : S)
    (a a' b b' : NumberField.RingOfIntegers K)
    (ha0 : (a : K) ≠ 0) (hb0 : (b : K) ≠ 0)
    (β γ : ℤ) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0)
    (haa' : a * a' = (β : NumberField.RingOfIntegers K))
    (hbb' : b * b' = (γ : NumberField.RingOfIntegers K))
    (hu : (((u : Kˣ) : K)) = (a : K) / (b : K)) :
    Int.natAbs (valuationMap S K u v).toAdd ≤
      multiplicity v.1.asIdeal
          (Ideal.span ({(β : NumberField.RingOfIntegers K)} :
            Set (NumberField.RingOfIntegers K))) +
        multiplicity v.1.asIdeal
          (Ideal.span ({(γ : NumberField.RingOfIntegers K)} :
            Set (NumberField.RingOfIntegers K))) := by
  have hβ0' : (β : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast hβ0
  have hγ0' : (γ : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast hγ0
  exact (natAbs_valuationMap_toAdd_le_of_eq_div_algebraicInteger
    u v a b ha0 hb0 hu).trans (Nat.add_le_add
      (multiplicity_principal_le_of_mul_eq v.1 a a' _ hβ0' haa')
      (multiplicity_principal_le_of_mul_eq v.1 b b' _ hγ0' hbb'))

/-- Combining two degree-eight principal-ideal multiplicity bounds gives
the convenient `J^16` exponential bound for the quotient coordinate. -/
lemma two_pow_le_sixteen_of_le_multiplicity_sum
    {a m n J : ℕ} (ha : a ≤ m + n)
    (hm : 2 ^ m ≤ J ^ 8) (hn : 2 ^ n ≤ J ^ 8) :
    2 ^ a ≤ J ^ 16 := by
  calc
    2 ^ a ≤ 2 ^ (m + n) := Nat.pow_le_pow_right (by omega) ha
    _ = 2 ^ m * 2 ^ n := by rw [pow_add]
    _ ≤ J ^ 8 * J ^ 8 := Nat.mul_le_mul hm hn
    _ = J ^ 16 := by ring

/-- A prime-ideal norm raised to its multiplicity in a nonzero ideal is
bounded by the norm of that ideal. -/
lemma absNorm_pow_multiplicity_le
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    v.asIdeal.absNorm ^ multiplicity v.asIdeal I ≤ I.absNorm := by
  have hdvd : v.asIdeal ^ multiplicity v.asIdeal I ∣ I :=
    pow_multiplicity_dvd v.asIdeal I
  have hnormdvd :
      Ideal.absNorm (v.asIdeal ^ multiplicity v.asIdeal I) ∣
        Ideal.absNorm I := map_dvd Ideal.absNorm hdvd
  rw [map_pow] at hnormdvd
  apply Nat.le_of_dvd
  · rw [Nat.pos_iff_ne_zero, Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors,
      mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot]
    exact hI
  · exact hnormdvd

/-- The norm of the principal ideal generated by a rational integer in a
number field is the absolute value of that integer raised to the degree. -/
lemma absNorm_span_intCast
    {K : Type*} [Field K] [NumberField K] (β : ℤ) :
    Ideal.absNorm (Ideal.span ({(β : NumberField.RingOfIntegers K)} :
      Set (NumberField.RingOfIntegers K))) =
      β.natAbs ^ Module.finrank ℤ (NumberField.RingOfIntegers K) := by
  cases β with
  | ofNat n =>
      simpa using
        (Ideal.absNorm_span_natCast
          (S := NumberField.RingOfIntegers K) n)
  | negSucc n =>
      rw [show ((Int.negSucc n : ℤ) : NumberField.RingOfIntegers K) =
        -((n + 1 : ℕ) : NumberField.RingOfIntegers K) by norm_num,
        Ideal.span_singleton_neg]
      simpa using
        (Ideal.absNorm_span_natCast
          (S := NumberField.RingOfIntegers K) (n + 1))

/-- In degree at most eight, the multiplicity of a finite prime in the
principal ideal of a nonzero rational integer of size at most `J` is
bounded by the elementary inequality `2^m ≤ J^8`. -/
lemma two_pow_multiplicity_span_intCast_le
    {K : Type*} [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (β : ℤ) (β_ne : β ≠ 0) (J : ℕ) (hβJ : β.natAbs ≤ J) :
    2 ^ multiplicity v.asIdeal
        (Ideal.span ({(β : NumberField.RingOfIntegers K)} :
          Set (NumberField.RingOfIntegers K))) ≤ J ^ 8 := by
  let I : Ideal (NumberField.RingOfIntegers K) :=
    Ideal.span ({(β : NumberField.RingOfIntegers K)} :
      Set (NumberField.RingOfIntegers K))
  have hI : I ≠ ⊥ := by
    simp [I, β_ne]
  have hprime : 2 ≤ v.asIdeal.absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hpowprime : 2 ^ multiplicity v.asIdeal I ≤
      v.asIdeal.absNorm ^ multiplicity v.asIdeal I :=
    Nat.pow_le_pow_left hprime _
  have hrank : Module.finrank ℤ (NumberField.RingOfIntegers K) ≤ 8 := by
    rw [NumberField.RingOfIntegers.rank]
    exact hdeg
  have hJpos : 0 < J := lt_of_lt_of_le (Int.natAbs_pos.mpr β_ne) hβJ
  calc
    2 ^ multiplicity v.asIdeal I ≤ I.absNorm :=
      hpowprime.trans (absNorm_pow_multiplicity_le v I hI)
    _ = β.natAbs ^ Module.finrank ℤ
        (NumberField.RingOfIntegers K) := by
      simpa [I] using (absNorm_span_intCast (K := K) β)
    _ ≤ J ^ Module.finrank ℤ (NumberField.RingOfIntegers K) :=
      Nat.pow_le_pow_left hβJ _
    _ ≤ J ^ 8 := Nat.pow_le_pow_right hJpos hrank

/-- When two nonzero algebraic integers multiply to a rational integer,
the finite-prime valuation of their quotient is at most twice the
multiplicity of that rational integer. -/
lemma natAbs_valuationOfNeZero_toAdd_factor_ratio_le
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a b : NumberField.RingOfIntegers K)
    (ha0 : (a : K) ≠ 0) (hb0 : (b : K) ≠ 0)
    (β : ℤ) (β_ne : β ≠ 0)
    (hab : a * b = (β : NumberField.RingOfIntegers K)) :
    Int.natAbs ((v.valuationOfNeZero
      (Units.mk0 (a : K) ha0 / Units.mk0 (b : K) hb0)).toAdd) ≤
      2 * multiplicity v.asIdeal
        (Ideal.span ({(β : NumberField.RingOfIntegers K)} :
          Set (NumberField.RingOfIntegers K))) := by
  let m := multiplicity v.asIdeal
    (Ideal.span ({(β : NumberField.RingOfIntegers K)} :
      Set (NumberField.RingOfIntegers K)))
  have hβ0 : (β : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast β_ne
  have ha_le : multiplicity v.asIdeal
      (Ideal.span ({a} : Set (NumberField.RingOfIntegers K))) ≤ m :=
    multiplicity_principal_le_of_mul_eq v a b _ hβ0 hab
  have hb_le : multiplicity v.asIdeal
      (Ideal.span ({b} : Set (NumberField.RingOfIntegers K))) ≤ m :=
    multiplicity_principal_le_of_mul_eq v b a _ hβ0
      (by simpa [mul_comm] using hab)
  exact (natAbs_valuationOfNeZero_toAdd_div_algebraicInteger_le
    v a b ha0 hb0).trans (by omega)

lemma valuationOfNeZero_eq_one_iff
    (v : HeightOneSpectrum R) (x : Fˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation F (x : F) = 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, WithZero.coe_one]

/-- The valuation vector of the chosen prime-class generator has the
expected class-number entry at its own prime. -/
lemma valuationMap_numberFieldPrimeClassSupportedUnit_self
    {K : Type*} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (v : S) :
    valuationMap S K (numberFieldPrimeClassSupportedUnit S v) v =
      Multiplicative.ofAdd (-(NumberField.classNumber K : ℤ)) := by
  rw [valuationMap_apply]
  apply WithZero.coe_injective
  rw [valuationOfNeZero_eq]
  simpa [numberFieldPrimeClassSupportedUnit, numberFieldPrimeClassUnit,
    WithZero.exp_eq_coe_ofAdd] using
    numberFieldPrimeClassNormalizedGenerator_valuation_self v.1

/-- Away from its own prime, the valuation vector of a prime-class
generator is one. -/
lemma valuationMap_numberFieldPrimeClassSupportedUnit_of_ne
    {K : Type*} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (v w : S) (hvw : w ≠ v) :
    valuationMap S K (numberFieldPrimeClassSupportedUnit S v) w = 1 := by
  rw [valuationMap_apply, valuationOfNeZero_eq_one_iff]
  exact numberFieldPrimeClassUnit_mem_singleton_supportedUnits v.1 w.1 (by
    show w.1 ≠ v.1
    intro h
    exact hvw (Subtype.ext h))

lemma valuationMap_numberFieldPrimeClassSupportedUnit_apply
    {K : Type*} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (v w : S) :
    valuationMap S K (numberFieldPrimeClassSupportedUnit S v) w =
      if w = v then
        Multiplicative.ofAdd (-(NumberField.classNumber K : ℤ))
      else 1 := by
  by_cases h : w = v
  · subst w
    rw [if_pos rfl]
    exact valuationMap_numberFieldPrimeClassSupportedUnit_self S v
  · rw [if_neg h]
    exact valuationMap_numberFieldPrimeClassSupportedUnit_of_ne S v w h

/-- The product of the chosen prime-class generators with a prescribed
integer exponent vector. -/
noncomputable def numberFieldPrimeClassSupportedUnitProduct
    {K : Type*} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    [Fintype S] (e : S → ℤ) : S.unit K :=
  ∏ v : S, numberFieldPrimeClassSupportedUnit S v ^ e v

/-- The valuation vector of the prime-class-generator product is the
prescribed vector multiplied by the negative class number. -/
lemma valuationMap_numberFieldPrimeClassSupportedUnitProduct_apply
    {K : Type*} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    [Fintype S] (e : S → ℤ) (w : S) :
    valuationMap S K
        (numberFieldPrimeClassSupportedUnitProduct S e) w =
      Multiplicative.ofAdd
        (-(NumberField.classNumber K : ℤ) * e w) := by
  rw [numberFieldPrimeClassSupportedUnitProduct, map_prod]
  simp_rw [map_zpow]
  simp only [Finset.prod_apply]
  calc
    ∏ v : S,
        valuationMap S K (numberFieldPrimeClassSupportedUnit S v) w ^ e v =
        valuationMap S K
          (numberFieldPrimeClassSupportedUnit S w) w ^ e w := by
      apply Finset.prod_eq_single_of_mem w (Finset.mem_univ w)
      intro v _hv hvw
      rw [valuationMap_numberFieldPrimeClassSupportedUnit_apply,
        if_neg (Ne.symm hvw), one_zpow]
    _ = Multiplicative.ofAdd
        (-(NumberField.classNumber K : ℤ)) ^ e w := by
      rw [valuationMap_numberFieldPrimeClassSupportedUnit_self]
    _ = Multiplicative.ofAdd
        (-(NumberField.classNumber K : ℤ) * e w) := by
      exact (Int.ofAdd_mul _ _).symm

/-- After raising an `S`-unit to the class number, its finite valuation
vector is supplied by the explicit prime-class generators; the remaining
factor is supported at no finite prime. -/
theorem exists_primeClassProduct_mul_emptySupportedUnit_eq_pow
    {K : Type*} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    [Fintype S] (u : S.unit K) :
    ∃ (e : S → ℤ)
        (q : (∅ : Set
          (HeightOneSpectrum (NumberField.RingOfIntegers K))).unit K),
      (u : Kˣ) ^ NumberField.classNumber K =
          (numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) * (q : Kˣ) ∧
        ∀ v, e v = -(valuationMap S K u v).toAdd := by
  let e : S → ℤ := fun v ↦ -(valuationMap S K u v).toAdd
  let g : S.unit K := numberFieldPrimeClassSupportedUnitProduct S e
  let qS : S.unit K := u ^ NumberField.classNumber K / g
  have hqval : valuationMap S K qS = 1 := by
    ext w
    simp only [qS, map_div, map_pow, Pi.div_apply, Pi.pow_apply,
      Pi.one_apply, g]
    rw [valuationMap_numberFieldPrimeClassSupportedUnitProduct_apply]
    simp only [toAdd_div, Int.toAdd_pow, toAdd_ofAdd, toAdd_one, e]
    ring
  have hqempty : (qS : Kˣ) ∈
      (∅ : Set
        (HeightOneSpectrum (NumberField.RingOfIntegers K))).unit K := by
    intro v _hvEmpty
    by_cases hvS : v ∈ S
    · have hv := congrFun hqval ⟨v, hvS⟩
      rw [valuationMap_apply, Pi.one_apply,
        valuationOfNeZero_eq_one_iff] at hv
      exact hv
    · exact qS.property v hvS
  let q : (∅ : Set
      (HeightOneSpectrum (NumberField.RingOfIntegers K))).unit K :=
    ⟨(qS : Kˣ), hqempty⟩
  have heqS : u ^ NumberField.classNumber K = g * qS := by
    simp [qS]
  refine ⟨e, q, ?_, fun v ↦ rfl⟩
  simpa [g, q] using
    congrArg (fun z : S.unit K ↦ (z : Kˣ)) heqS

/-- Enlarging the allowed prime set enlarges the supported-unit group. -/
lemma mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    S.unit F ≤ T.unit F := by
  intro u hu v hvT
  exact hu v (fun hvS ↦ hvT (hST hvS))

/-- The kernel of the valuation vector consists exactly of units supported
at no finite prime. -/
lemma valuationMap_ker :
    (valuationMap S F).ker =
      ((∅ : Set (HeightOneSpectrum R)).unit F).subgroupOf (S.unit F) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, funext_iff]
  constructor
  · intro h v _
    by_cases hvS : v ∈ S
    · have hv := h ⟨v, hvS⟩
      rw [valuationMap_apply, Pi.one_apply,
        valuationOfNeZero_eq_one_iff] at hv
      exact hv
    · exact u.property v hvS
  · intro h v
    rw [valuationMap_apply, Pi.one_apply,
      valuationOfNeZero_eq_one_iff]
    exact h v (Set.notMem_empty v)

/-- A module is finite when the kernel and range of a linear map out of it
are finite. -/
lemma moduleFinite_of_ker_range
    {A G H : Type*} [Ring A] [AddCommGroup G] [AddCommGroup H]
    [Module A G] [Module A H] (f : G →ₗ[A] H)
    [Module.Finite A (LinearMap.ker f)]
    [Module.Finite A (LinearMap.range f)] : Module.Finite A G := by
  have : Module.Finite A (G ⧸ LinearMap.ker f) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange f).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

/-- A commutative group is finitely generated when the kernel and range of
a homomorphism out of it are finitely generated. -/
lemma groupFG_of_ker_range
    {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H)
    (hk : Group.FG (f.ker : Subgroup G))
    (hr : Group.FG (f.range : Subgroup H)) : Group.FG G := by
  rw [GroupFG.iff_add_fg, ← Module.Finite.iff_addGroup_fg]
  have : Module.Finite ℤ
      (LinearMap.ker (MonoidHom.toAdditive f).toIntLinearMap) := by
    rw [AddMonoidHom.coe_toIntLinearMap_ker, Module.Finite.iff_fg,
      Submodule.fg_iff_addSubgroup_fg,
      AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact (Subgroup.fg_iff_add_fg f.ker).mp
      ((Group.fg_iff_subgroup_fg f.ker).mp hk)
  have : Module.Finite ℤ
      (LinearMap.range (MonoidHom.toAdditive f).toIntLinearMap) := by
    rw [AddMonoidHom.coe_toIntLinearMap_range, Module.Finite.iff_fg,
      Submodule.fg_iff_addSubgroup_fg,
      AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact (Subgroup.fg_iff_add_fg f.range).mp
      ((Group.fg_iff_subgroup_fg f.range).mp hr)
  exact moduleFinite_of_ker_range (MonoidHom.toAdditive f).toIntLinearMap

/-- A subgroup of a finitely generated commutative group is finitely
generated. -/
lemma subgroupFG {G : Type*} [CommGroup G] [Group.FG G]
    (P : Subgroup G) : Group.FG P := by
  have : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (GroupFG.iff_add_fg.mp inferInstance)
  have : IsNoetherian ℤ (Additive G) := inferInstance
  have h : (AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup P)).FG :=
    IsNoetherian.noetherian _
  rw [Submodule.fg_iff_addSubgroup_fg,
    AddSubgroup.toIntSubmodule_toAddSubgroup] at h
  exact (Group.fg_iff_subgroup_fg P).mpr
    ((Subgroup.fg_iff_add_fg P).mpr h)

/-- Supported units are finitely generated whenever `S` is finite and
the units supported nowhere are finitely generated. -/
theorem fg [Finite S]
    (hEmpty : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit F)) :
    Group.FG (S.unit F) := by
  have : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit F) := hEmpty
  have : Group.FG (↑S → Multiplicative ℤ) := by
    rw [GroupFG.iff_add_fg, ← Module.Finite.iff_addGroup_fg]
    exact inferInstanceAs (Module.Finite ℤ (↑S → ℤ))
  apply groupFG_of_ker_range (valuationMap S F)
  · rw [valuationMap_ker]
    exact Group.fg_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe
        (mono (F := F) (S := ∅) (T := S)
          (Set.empty_subset S))).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe
        (mono (F := F) (S := ∅) (T := S)
          (Set.empty_subset S))).symm.surjective
  · exact subgroupFG _

omit [IsDedekindDomain R] in
/-- The valuation-vector codomain has rank equal to the number of allowed
primes. -/
lemma finrank_valuationCodomain [Finite S] :
    Module.finrank ℤ (Additive (↑S → Multiplicative ℤ)) = Nat.card S := by
  let : Fintype ↑S := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_pi ℤ

/-- The valuation-map kernel has the same rank as the units supported at
no finite prime. -/
lemma finrank_valuationKer [Finite S] :
    Module.finrank ℤ
        (LinearMap.ker (MonoidHom.toAdditive (valuationMap S F)).toIntLinearMap) =
      Module.finrank ℤ
        (Additive ((∅ : Set (HeightOneSpectrum R)).unit F)) := by
  rw [AddMonoidHom.coe_toIntLinearMap_ker,
    MonoidHom.coe_toAdditive_ker, valuationMap_ker]
  exact LinearEquiv.finrank_eq
    (AddEquiv.toIntLinearEquiv
      (MulEquiv.toAdditive (Subgroup.subgroupOfEquivOfLe
        (mono (F := F) (S := ∅) (T := S) (Set.empty_subset S)))))

/-- Rank-nullity for the supported-unit valuation map. -/
lemma finrank_eq_add_range [Finite S]
    (hEmpty : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit F)) :
    Module.finrank ℤ (Additive (S.unit F)) =
      Module.finrank ℤ
          (Additive ((∅ : Set (HeightOneSpectrum R)).unit F)) +
        Module.finrank ℤ
          (LinearMap.range
            (MonoidHom.toAdditive (valuationMap S F)).toIntLinearMap) := by
  have : Group.FG (S.unit F) := fg S F hEmpty
  have : Module.Finite ℤ (Additive (S.unit F)) :=
    Module.Finite.iff_addGroup_fg.mpr (GroupFG.iff_add_fg.mp inferInstance)
  have hrn := Submodule.finrank_quotient_add_finrank
    (LinearMap.ker (MonoidHom.toAdditive (valuationMap S F)).toIntLinearMap)
  rw [LinearEquiv.finrank_eq
      (MonoidHom.toAdditive (valuationMap S F)).toIntLinearMap.quotKerEquivRange,
    finrank_valuationKer] at hrn
  omega

/-- The rank of the supported-unit group is at most the ordinary-unit rank
plus the number of allowed finite primes. -/
theorem finrank_le [Finite S]
    (hEmpty : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit F)) :
    Module.finrank ℤ (Additive (S.unit F)) ≤
      Module.finrank ℤ
          (Additive ((∅ : Set (HeightOneSpectrum R)).unit F)) + Nat.card S := by
  rw [finrank_eq_add_range S F hEmpty]
  gcongr
  rw [← finrank_valuationCodomain (S := S)]
  exact Submodule.finrank_le _

/-- Units supported at no prime are the ordinary units of the base
Dedekind domain. -/
private lemma algebraMap_botEquivOfInjective_apply
    (x : (⊥ : Subalgebra R F)) :
    algebraMap R F
        (Algebra.botEquivOfInjective (IsFractionRing.injective R F) x) =
      (x : F) := by
  have h := congrArg Subtype.val
    ((Algebra.botEquivOfInjective
      (IsFractionRing.injective R F)).symm_apply_apply x)
  exact h

noncomputable def emptyEquivUnits :
    (∅ : Set (HeightOneSpectrum R)).unit F ≃* Rˣ :=
  (Set.unitEquivUnitsInteger (∅ : Set (HeightOneSpectrum R)) F).trans
    (Units.mapEquiv
      ((Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R F)).trans
        (Algebra.botEquivOfInjective (IsFractionRing.injective R F))).toRingEquiv.toMulEquiv)

/-- Passing from an everywhere-supported unit to the corresponding
ordinary unit and back to the fraction field preserves its value. -/
@[simp] lemma unitsMap_emptyEquivUnits
    (q : (∅ : Set (HeightOneSpectrum R)).unit F) :
    Units.map (algebraMap R F) (emptyEquivUnits F q) = (q : Fˣ) := by
  ext
  simp [emptyEquivUnits, algebraMap_botEquivOfInjective_apply]

end SupportedUnits

/-- The finite-prime coordinate used in the explicit `S`-unit product is
represented by the fundamental-cone-normalized class generator, so it
inherits the explicit generator-height bound above. -/
theorem numberFieldPrimeClassSupportedUnit_logHeight_le
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v : S) :
    Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) ≤
      Real.log
          ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) +
        2 * ∑ w : {w : NumberField.InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          ((∑ i : Fin (NumberField.Units.rank K),
              |NumberField.Units.logEmbedding K
                (Additive.ofMul (NumberField.Units.fundSystem K i)) w|) +
            Real.log
              ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ)) := by
  simpa [numberFieldPrimeClassSupportedUnit,
    numberFieldPrimeClassUnit] using
    numberFieldPrimeClassNormalizedGenerator_logHeight_le v.1

/-- The total absolute logarithmic mass of the fixed Dirichlet
fundamental system, over the non-distinguished infinite places.  This is
the only field-dependent archimedean term in the normalized prime-class
generator bound. -/
noncomputable def numberFieldFundamentalUnitLogMass
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  ∑ w : {w : NumberField.InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
    ∑ i : Fin (NumberField.Units.rank K),
      |NumberField.Units.logEmbedding K
        (Additive.ofMul (NumberField.Units.fundSystem K i)) w|

/-- Collecting the repeated norm logarithms in the normalized-generator
bound gives one explicit unit-lattice mass and `2 rank K + 1` copies of
the norm logarithm. -/
theorem numberFieldPrimeClassSupportedUnit_logHeight_le_mass
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v : S) :
    Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) ≤
      2 * numberFieldFundamentalUnitLogMass K +
        ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
          Real.log
            ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) := by
  have h := numberFieldPrimeClassSupportedUnit_logHeight_le S v
  have hcard : Fintype.card {w : NumberField.InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      NumberField.Units.rank K := by
    simpa using
      (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  have hunivcard : (Finset.univ : Finset
      {w : NumberField.InfinitePlace K //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}).card =
      NumberField.Units.rank K := by
    simpa using hcard
  calc
    Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) ≤
        Real.log
            ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) +
          2 * ∑ w : {w : NumberField.InfinitePlace K //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
            ((∑ i : Fin (NumberField.Units.rank K),
                |NumberField.Units.logEmbedding K
                  (Additive.ofMul (NumberField.Units.fundSystem K i)) w|) +
              Real.log
                ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ)) := h
    _ = 2 * numberFieldFundamentalUnitLogMass K +
        ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
          Real.log
            ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) := by
      simp only [numberFieldFundamentalUnitLogMass,
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hunivcard,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- A degree-eight norm bound converts, after taking a further natural
power, into the corresponding logarithmic bound. -/
lemma log_nat_pow_le_class_mul_eight_log
    {A J h : ℕ} (hApos : 0 < A) (hA : A ≤ J ^ 8) :
    Real.log (((A ^ h : ℕ) : ℝ)) ≤
      (h : ℝ) * (8 * Real.log (J : ℝ)) := by
  have hJ : 0 < J := by
    by_contra hJ
    have hJ0 : J = 0 := Nat.eq_zero_of_not_pos hJ
    subst J
    norm_num at hA
    omega
  have hlogbase : Real.log (A : ℝ) ≤
      8 * Real.log (J : ℝ) := by
    calc
      Real.log (A : ℝ) ≤ Real.log (((J ^ 8 : ℕ) : ℝ)) := by
        apply Real.strictMonoOn_log.monotoneOn
        · show (0 : ℝ) < (A : ℝ)
          exact_mod_cast hApos
        · show (0 : ℝ) < ((J ^ 8 : ℕ) : ℝ)
          positivity
        · exact_mod_cast hA
      _ = 8 * Real.log (J : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
  rw [Nat.cast_pow, Real.log_pow]
  exact mul_le_mul_of_nonneg_left hlogbase (Nat.cast_nonneg h)

/-- Northcott finiteness gives a uniform positive gap above Mahler measure
one for all integer polynomials of degree at most eight.  The constant is
not optimized; only its positivity and independence of the number field
will be used in the unit-lattice reduction. -/
theorem exists_degree_eight_mahlerMeasure_gap :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ p : Polynomial ℤ,
        1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure →
        p.natDegree ≤ 8 →
        δ ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure - 1 := by
  classical
  let A : Set (Polynomial ℤ) :=
    {p | p.natDegree ≤ 8 ∧
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ (2 : ℝ)}
  have hA : A.Finite := by
    simpa only [A, Set.mem_setOf_eq, NNReal.coe_ofNat] using
      (Polynomial.finite_mahlerMeasure_le (n := 8) (B := (2 : NNReal)))
  let F : Finset (Polynomial ℤ) := hA.toFinset
  let G : Finset ℝ := insert 1
    ((F.filter (fun p ↦
      1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure)).image
        (fun p ↦ (p.map (Int.castRingHom ℂ)).mahlerMeasure - 1))
  have hG : G.Nonempty := by
    exact ⟨1, Finset.mem_insert_self 1 _⟩
  let δ : ℝ := G.min' hG
  have hδmem : δ ∈ G := by
    exact G.min'_mem hG
  have hδpos : 0 < δ := by
    rcases Finset.mem_insert.mp hδmem with hδ | hδ
    · simpa [hδ]
    · obtain ⟨p, hp, hpδ⟩ := Finset.mem_image.mp hδ
      have hpgt : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
        (Finset.mem_filter.mp hp).2
      rw [← hpδ]
      linarith
  have hδone : δ ≤ 1 := by
    exact G.min'_le _ (Finset.mem_insert_self 1 _)
  refine ⟨δ, hδpos, ?_⟩
  intro p hpgt hpdeg
  by_cases hpTwo :
      (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ (2 : ℝ)
  · have hpA : p ∈ A := ⟨hpdeg, hpTwo⟩
    have hpF : p ∈ F := hA.mem_toFinset.mpr hpA
    have hpFilter : p ∈ F.filter (fun q ↦
        1 < (q.map (Int.castRingHom ℂ)).mahlerMeasure) :=
      Finset.mem_filter.mpr ⟨hpF, hpgt⟩
    have hpG : (p.map (Int.castRingHom ℂ)).mahlerMeasure - 1 ∈ G := by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨p, hpFilter, rfl⟩
    exact G.min'_le _ hpG
  · have hpLarge : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure - 1 := by
      push_neg at hpTwo
      linarith
    exact hδone.trans hpLarge.le

/-- A fixed positive lower gap for the Mahler measure of non-cyclotomic
integer polynomials of degree at most eight. -/
noncomputable def degreeEightMahlerGap : ℝ :=
  Classical.choose exists_degree_eight_mahlerMeasure_gap

lemma degreeEightMahlerGap_pos : 0 < degreeEightMahlerGap :=
  (Classical.choose_spec exists_degree_eight_mahlerMeasure_gap).1

lemma degreeEightMahlerGap_le
    (p : Polynomial ℤ)
    (hp : 1 < (p.map (Int.castRingHom ℂ)).mahlerMeasure)
    (hdeg : p.natDegree ≤ 8) :
    degreeEightMahlerGap ≤
      (p.map (Int.castRingHom ℂ)).mahlerMeasure - 1 :=
  (Classical.choose_spec exists_degree_eight_mahlerMeasure_gap).2 p hp hdeg

/-- Kronecker's theorem in the form needed for unit-lattice separation:
the integer minimal polynomial of a non-torsion algebraic unit has Mahler
measure strictly greater than one. -/
theorem unit_minpoly_mahlerMeasure_gt_one
    {K : Type*} [Field K] [NumberField K]
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    1 < (((minpoly ℤ u.1).map
      (Int.castRingHom ℂ)).mahlerMeasure) := by
  classical
  let p : Polynomial ℤ := minpoly ℤ u.1
  have hp0 : p ≠ 0 := by
    exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral u.1)
  have hpOne : 1 ≤ (p.map (Int.castRingHom ℂ)).mahlerMeasure :=
    Polynomial.one_le_mahlerMeasure_of_ne_zero hp0
  exact lt_of_le_of_ne hpOne fun hMeasure ↦ by
    have hMeasureOne :
        (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1 :=
      hMeasure.symm
    let φ : K →+* ℂ := Classical.choice inferInstance
    let ψ : NumberField.RingOfIntegers K →+* ℂ :=
      φ.comp (algebraMap (NumberField.RingOfIntegers K) K)
    have hψinj : Function.Injective ψ :=
      φ.injective.comp
        (NumberField.RingOfIntegers.coe_injective (K := K))
    let z : ℂ := ψ u.1
    have hzaeval : Polynomial.aeval z p = 0 := by
      have hcomp :
          (algebraMap ℤ ℂ).comp (RingHom.id ℤ) =
            ψ.comp (algebraMap ℤ (NumberField.RingOfIntegers K)) := by
        ext m
        simp [ψ, φ]
      have hmap := p.map_aeval_eq_aeval_map hcomp u.1
      calc
        Polynomial.aeval z p =
            ψ (Polynomial.aeval u.1 p) := by
          simpa [z] using hmap.symm
        _ = 0 := by simp [p]
    have hzroot : z ∈ p.aroots ℂ := by
      rw [Polynomial.mem_aroots]
      exact ⟨hp0, hzaeval⟩
    have hz0 : z ≠ 0 := by
      exact (map_ne_zero_iff ψ hψinj).mpr (Units.ne_zero u)
    obtain ⟨n, hn, hzn⟩ :=
      Polynomial.pow_eq_one_of_mahlerMeasure_eq_one
        hMeasureOne hz0 hzroot
    apply hu n hn
    apply hψinj
    simpa [z] using hzn

/-- A non-torsion algebraic unit in a number field of degree at most eight
has Mahler measure separated uniformly from one. -/
theorem degreeEightMahlerGap_le_unit_minpoly
    {K : Type*} [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    degreeEightMahlerGap ≤
      (((minpoly ℤ u.1).map
        (Int.castRingHom ℂ)).mahlerMeasure - 1) := by
  let p : Polynomial ℤ := minpoly ℤ u.1
  have hpdeg : p.natDegree ≤ 8 := by
    calc
      p.natDegree ≤ Module.finrank ℤ (NumberField.RingOfIntegers K) :=
        minpoly.natDegree_le u.1
      _ = Module.finrank ℚ K := NumberField.RingOfIntegers.rank K
      _ ≤ 8 := hdeg
  exact degreeEightMahlerGap_le p
    (by simpa [p] using unit_minpoly_mahlerMeasure_gt_one u hu) hpdeg

/-- The logarithmic separation constant attached to
`degreeEightMahlerGap`.  Division by eight anticipates the maximal degree
of the multiquadratic fields used in the simultaneous-Pell reduction. -/
noncomputable def degreeEightUnitLogGap : ℝ :=
  Real.log (1 + degreeEightMahlerGap) / 8

lemma degreeEightUnitLogGap_pos : 0 < degreeEightUnitLogGap := by
  rw [degreeEightUnitLogGap, div_pos_iff]
  exact Or.inl ⟨Real.log_pos (by linarith [degreeEightMahlerGap_pos]), by norm_num⟩

/-- In a nonempty multiset of real numbers at least one, with at most
eight entries, one entry to the eighth power dominates the product. -/
private lemma exists_mem_prod_le_pow_eight
    (s : Multiset ℝ) (hs : s ≠ 0)
    (hone : ∀ x ∈ s, 1 ≤ x) (hcard : s.card ≤ 8) :
    ∃ x ∈ s, s.prod ≤ x ^ 8 := by
  let F : Finset ℝ := s.toFinset
  have hF : F.Nonempty := by
    simpa [F, Multiset.toFinset_nonempty] using hs
  let x : ℝ := F.max' hF
  have hxmemF : x ∈ F := F.max'_mem hF
  have hxmem : x ∈ s := by
    simpa [F] using hxmemF
  have hxone : 1 ≤ x := hone x hxmem
  have hxnonneg : 0 ≤ x := zero_le_one.trans hxone
  have hprod_le_pow : ∀ t : Multiset ℝ,
      (∀ y ∈ t, 0 ≤ y ∧ y ≤ x) → t.prod ≤ x ^ t.card := by
    intro t ht
    induction t using Multiset.induction_on with
    | empty => simp
    | @cons a t ih =>
        have ha : 0 ≤ a ∧ a ≤ x := ht a (by simp)
        have ht' : ∀ y ∈ t, 0 ≤ y ∧ y ≤ x := by
          intro y hy
          exact ht y (by simp [hy])
        have hit := ih ht'
        have htprod : 0 ≤ t.prod :=
          Multiset.prod_nonneg fun y hy ↦ (ht' y hy).1
        rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
        calc
          a * t.prod ≤ x * t.prod :=
            mul_le_mul_of_nonneg_right ha.2 htprod
          _ ≤ x * x ^ t.card :=
            mul_le_mul_of_nonneg_left hit hxnonneg
          _ = x ^ t.card * x := mul_comm _ _
  have hprod : s.prod ≤ x ^ s.card := by
    apply hprod_le_pow s
    intro y hy
    exact ⟨zero_le_one.trans (hone y hy),
      F.le_max' y (by simpa [F] using hy)⟩
  exact ⟨x, hxmem, hprod.trans (pow_le_pow_right₀ hxone hcard)⟩

/-- Quantitative Kronecker separation at one complex conjugate: a
non-torsion unit in degree at most eight has a conjugate whose logarithmic
absolute value is at least `degreeEightUnitLogGap`. -/
theorem exists_unit_minpoly_root_log_norm_ge
    {K : Type*} [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    ∃ z ∈ (((minpoly ℤ u.1).map (Int.castRingHom ℂ)).roots),
      degreeEightUnitLogGap ≤ Real.log ‖z‖ := by
  classical
  let p : Polynomial ℤ := minpoly ℤ u.1
  let q : Polynomial ℂ := p.map (Int.castRingHom ℂ)
  have hpmonic : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral u.1)
  have hqmonic : q.Monic := hpmonic.map _
  have hpdegpos : 0 < p.natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral u.1)
  have hqdeg : q.natDegree = p.natDegree :=
    hpmonic.natDegree_map (Int.castRingHom ℂ)
  have hqrootsCard : q.roots.card = p.natDegree := by
    rw [← hqdeg]
    exact (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  let s : Multiset ℝ := q.roots.map (fun z ↦ max 1 ‖z‖)
  have hs : s ≠ 0 := by
    intro hs0
    have : s.card = 0 := by simp [hs0]
    simp only [s, Multiset.card_map, hqrootsCard] at this
    omega
  have hsone : ∀ x ∈ s, 1 ≤ x := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    exact le_max_left _ _
  have hscard : s.card ≤ 8 := by
    simp only [s, Multiset.card_map, hqrootsCard]
    exact (minpoly.natDegree_le u.1).trans
      ((NumberField.RingOfIntegers.rank K).le.trans hdeg)
  obtain ⟨R, hRmem, hprod⟩ :=
    exists_mem_prod_le_pow_eight s hs hsone hscard
  obtain ⟨z, hzroot, hzR⟩ := Multiset.mem_map.mp hRmem
  have hMeasureProd : q.mahlerMeasure = s.prod := by
    rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
      hqmonic.leadingCoeff, norm_one, one_mul]
  have hgapMeasure : 1 + degreeEightMahlerGap ≤ q.mahlerMeasure := by
    have hgap := degreeEightMahlerGap_le_unit_minpoly hdeg u hu
    change degreeEightMahlerGap ≤ q.mahlerMeasure - 1 at hgap
    linarith
  have hRpow : 1 + degreeEightMahlerGap ≤ R ^ 8 := by
    rw [hMeasureProd] at hgapMeasure
    exact hgapMeasure.trans hprod
  have hRone : 1 < R := by
    by_contra hR
    have hRle : R ≤ 1 := le_of_not_gt hR
    have : R ^ 8 ≤ 1 := by
      simpa using pow_le_one₀ (by linarith [hsone R hRmem]) hRle
    linarith [degreeEightMahlerGap_pos]
  have hzNorm : R = max 1 ‖z‖ := hzR.symm
  have hzOne : 1 < ‖z‖ := by
    by_contra hz
    have hzle : ‖z‖ ≤ 1 := le_of_not_gt hz
    rw [hzNorm, max_eq_left hzle] at hRone
    exact (lt_irrefl 1) hRone
  refine ⟨z, hzroot, ?_⟩
  have hlog : Real.log (1 + degreeEightMahlerGap) ≤
      Real.log (‖z‖ ^ 8) := by
    apply Real.strictMonoOn_log.monotoneOn
    · show 0 < 1 + degreeEightMahlerGap
      linarith [degreeEightMahlerGap_pos]
    · show 0 < ‖z‖ ^ 8
      exact pow_pos (by linarith [hzOne]) _
    · simpa [hzNorm, max_eq_right hzOne.le] using hRpow
  rw [Real.log_pow] at hlog
  rw [degreeEightUnitLogGap]
  norm_num at hlog ⊢
  linarith

/-- A large root of the integral minimal polynomial is the image of the
unit under an actual complex embedding of the ambient number field. -/
theorem exists_unit_embedding_log_norm_ge
    {K : Type*} [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    ∃ φ : K →+* ℂ,
      degreeEightUnitLogGap ≤ Real.log ‖φ (u.1 : K)‖ := by
  obtain ⟨z, hz, hzlog⟩ :=
    exists_unit_minpoly_root_log_norm_ge hdeg u hu
  have hpzero : (minpoly ℤ u.1).map (Int.castRingHom ℂ) ≠ 0 := by
    exact ((minpoly.monic (Algebra.IsIntegral.isIntegral u.1)).map
      (Int.castRingHom ℂ)).ne_zero
  have hminpoly :
      (minpoly ℚ (u.1 : K)).map (algebraMap ℚ ℂ) =
        (minpoly ℤ u.1).map (Int.castRingHom ℂ) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ u.1.isIntegral_coe,
      NumberField.RingOfIntegers.minpoly_coe, Polynomial.map_map]
    rfl
  have hzQ : z ∈ (minpoly ℚ (u.1 : K)).rootSet ℂ := by
    rw [Polynomial.mem_rootSet']
    constructor
    · rw [hminpoly]
      exact hpzero
    · have hzEval := (Polynomial.mem_roots hpzero).mp hz
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hminpoly]
      exact hzEval
  obtain ⟨φ, hφ⟩ :=
    (NumberField.Embeddings.range_eval_eq_rootSet_minpoly
      K ℂ (u.1 : K)).symm.subset hzQ
  exact ⟨φ, by simpa [hφ] using hzlog⟩

/-- Uniform discreteness of the logarithmic unit lattice in degrees at
most eight.  This is an explicit quantitative strengthening of the
discreteness used in Mathlib's proof of Dirichlet's unit theorem. -/
theorem degreeEightUnitLogGap_div_eight_le_logEmbedding_norm
    {K : Type*} [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    degreeEightUnitLogGap / 8 ≤
      ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ := by
  classical
  obtain ⟨φ, hφ⟩ := exists_unit_embedding_log_norm_ge hdeg u hu
  let w : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk φ
  have hw : degreeEightUnitLogGap ≤
      Real.log (w (u.1 : K)) := by
    simpa [w, NumberField.InfinitePlace.apply] using hφ
  have hlog :=
    NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le
      (x := u)
      (r := ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖)
      (norm_nonneg _) le_rfl w
  have hcard : Fintype.card (NumberField.InfinitePlace K) ≤
      Module.finrank ℚ K := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    calc
      Fintype.card (NumberField.InfinitePlace K) =
          ∑ _w : NumberField.InfinitePlace K, 1 := by simp
      _ ≤ ∑ w : NumberField.InfinitePlace K, w.mult := by
        exact Finset.sum_le_sum fun w _ ↦
          Nat.one_le_iff_ne_zero.mpr NumberField.InfinitePlace.mult_ne_zero
  have hcard8 : (Fintype.card (NumberField.InfinitePlace K) : ℝ) ≤ 8 := by
    exact_mod_cast hcard.trans hdeg
  have hδ : degreeEightUnitLogGap ≤
      (Fintype.card (NumberField.InfinitePlace K) : ℝ) *
        ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ :=
    hw.trans ((le_abs_self _).trans hlog)
  have hnorm : 0 ≤
      ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ := norm_nonneg _
  have hδeight : degreeEightUnitLogGap ≤
      8 * ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ :=
    hδ.trans (mul_le_mul_of_nonneg_right hcard8 hnorm)
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    (by simpa [mul_comm] using hδeight)

/-- The total operator norm of the real coordinate functionals of
Mathlib's fixed unit-lattice basis.  This isolates, as one field-dependent
constant, the conditioning of the chosen ordinary-unit basis. -/
noncomputable def numberFieldFundamentalUnitCoordinateNorm
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  ∑ i : Fin (NumberField.Units.rank K),
    ‖LinearMap.toContinuousLinearMap
      (((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
        (NumberField.Units.unitLattice K)).coord i)‖

lemma numberFieldFundamentalUnitCoordinateNorm_nonneg
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ numberFieldFundamentalUnitCoordinateNorm K := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- Each real coordinate in the fixed unit-lattice basis is bounded by
the coordinate-operator mass times the norm of the logarithmic vector. -/
lemma numberField_fundamentalUnit_basis_coordinate_le
    (K : Type*) [Field K] [NumberField K]
    (x : NumberField.Units.dirichletUnitTheorem.logSpace K)
    (i : Fin (NumberField.Units.rank K)) :
    |((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
        (NumberField.Units.unitLattice K)).repr x i| ≤
      numberFieldFundamentalUnitCoordinateNorm K * ‖x‖ := by
  let b := (NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
    (NumberField.Units.unitLattice K)
  let c := LinearMap.toContinuousLinearMap (b.coord i)
  have hci : ‖c‖ ≤ numberFieldFundamentalUnitCoordinateNorm K := by
    change ‖LinearMap.toContinuousLinearMap (b.coord i)‖ ≤
      ∑ j, ‖LinearMap.toContinuousLinearMap (b.coord j)‖
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin (NumberField.Units.rank K) ↦
        ‖LinearMap.toContinuousLinearMap (b.coord j)‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
  calc
    |b.repr x i| = ‖c x‖ := by simp [b, c, Real.norm_eq_abs]
    _ ≤ ‖c‖ * ‖x‖ := c.le_opNorm x
    _ ≤ numberFieldFundamentalUnitCoordinateNorm K * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right hci (norm_nonneg x)

/-- The exponent of a fundamental unit in Dirichlet's decomposition is
bounded by the norm of the unit's logarithmic embedding. -/
lemma numberField_ordinaryUnit_exponent_abs_le
    (K : Type*) [Field K] [NumberField K]
    {x ζ : (NumberField.RingOfIntegers K)ˣ}
    {f : Fin (NumberField.Units.rank K) → ℤ}
    (hζ : ζ ∈ NumberField.Units.torsion K)
    (h : x = ζ * ∏ i, (NumberField.Units.fundSystem K i) ^ f i)
    (i : Fin (NumberField.Units.rank K)) :
    |(f i : ℝ)| ≤ numberFieldFundamentalUnitCoordinateNorm K *
      ‖NumberField.Units.logEmbedding K (Additive.ofMul x)‖ := by
  let xu : NumberField.Units.unitLattice K :=
    NumberField.Units.logEmbeddingEquiv K
      (Additive.ofMul (QuotientGroup.mk x))
  have hf := NumberField.Units.fun_eq_repr K hζ h
  have hreprZ :
      (NumberField.Units.basisUnitLattice K).repr xu i = f i := by
    rw [hf]
    simp [NumberField.Units.basisUnitLattice, xu]
  have hreprR :=
    (NumberField.Units.basisUnitLattice K).ofZLatticeBasis_repr_apply
      ℝ (NumberField.Units.unitLattice K) xu i
  have hcoord := numberField_fundamentalUnit_basis_coordinate_le K
    (xu : NumberField.Units.dirichletUnitTheorem.logSpace K) i
  rw [hreprR, hreprZ] at hcoord
  simpa [xu, NumberField.Units.logEmbeddingEquiv_apply,
    Real.norm_eq_abs] using hcoord

/-- The logarithmic embedding of an ordinary unit has norm at most twice
its unnormalised logarithmic height. -/
lemma numberField_logEmbedding_norm_le_two_logHeight
    (K : Type*) [Field K] [NumberField K]
    (x : (NumberField.RingOfIntegers K)ˣ) :
    ‖NumberField.Units.logEmbedding K (Additive.ofMul x)‖ ≤
      2 * Height.logHeight₁ (((x : NumberField.RingOfIntegers K) : K)) := by
  have hh : Height.logHeight₁ (((x : NumberField.RingOfIntegers K) : K)) =
      ∑ w : NumberField.InfinitePlace K,
        w.mult * Real.posLog (w (((x : NumberField.RingOfIntegers K) : K))) :=
    numberField_logHeight_ringOfIntegers_eq_sum (x : NumberField.RingOfIntegers K)
  have hhinv : Height.logHeight₁
      ((((x⁻¹ : (NumberField.RingOfIntegers K)ˣ) :
        NumberField.RingOfIntegers K) : K)) =
      Height.logHeight₁ (((x : NumberField.RingOfIntegers K) : K)) := by
    rw [show ((((x⁻¹ : (NumberField.RingOfIntegers K)ˣ) :
      NumberField.RingOfIntegers K) : K)) =
        (((x : NumberField.RingOfIntegers K) : K))⁻¹ by simp,
      Height.logHeight₁_inv]
  have hh_nonneg : 0 ≤ Height.logHeight₁
      (((x : NumberField.RingOfIntegers K) : K)) := Height.zero_le_logHeight₁ _
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hh_nonneg)]
  intro w
  rw [Real.norm_eq_abs,
    NumberField.Units.dirichletUnitTheorem.logEmbedding_component]
  let a := w.1 (((x : NumberField.RingOfIntegers K) : K))
  change |(w.1.mult : ℝ) * Real.log a| ≤
    2 * Height.logHeight₁ (((x : NumberField.RingOfIntegers K) : K))
  have ha : 0 < a := NumberField.InfinitePlace.pos_iff.mpr (by simp)
  have hwpos :
      (w.1.mult : ℝ) * Real.posLog a ≤
        Height.logHeight₁ (((x : NumberField.RingOfIntegers K) : K)) := by
    rw [hh]
    have hterm := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun z : NumberField.InfinitePlace K ↦
        (z.mult : ℝ) * Real.posLog
          (z (((x : NumberField.RingOfIntegers K) : K))))
      (fun z _ ↦ mul_nonneg (Nat.cast_nonneg z.mult)
        (show 0 ≤ Real.posLog
          (z (((x : NumberField.RingOfIntegers K) : K))) from
            Real.posLog_nonneg))
      (Finset.mem_univ w.1)
    simpa [a] using hterm
  have hwinv :
      (w.1.mult : ℝ) * Real.posLog a⁻¹ ≤
        Height.logHeight₁ (((x : NumberField.RingOfIntegers K) : K)) := by
    rw [← hhinv, numberField_logHeight_ringOfIntegers_eq_sum]
    have hterm := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun z : NumberField.InfinitePlace K ↦
        (z.mult : ℝ) * Real.posLog
          (z ((((x⁻¹ : (NumberField.RingOfIntegers K)ˣ) :
            NumberField.RingOfIntegers K) : K))))
      (fun z _ ↦ mul_nonneg (Nat.cast_nonneg z.mult)
        (show 0 ≤ Real.posLog
          (z ((((x⁻¹ : (NumberField.RingOfIntegers K)ˣ) :
            NumberField.RingOfIntegers K) : K))) from Real.posLog_nonneg))
      (Finset.mem_univ w.1)
    simpa [a] using hterm
  rw [← Real.posLog_sub_posLog_inv (x := a)]
  have hpa : 0 ≤ Real.posLog a := Real.posLog_nonneg
  have hpainv : 0 ≤ Real.posLog a⁻¹ := Real.posLog_nonneg
  have hmult : 0 ≤ (w.1.mult : ℝ) := Nat.cast_nonneg _
  calc
    |(w.1.mult : ℝ) * (Real.posLog a - Real.posLog a⁻¹)| =
        |(w.1.mult : ℝ) * Real.posLog a -
          (w.1.mult : ℝ) * Real.posLog a⁻¹| := by ring_nf
    _ ≤ (w.1.mult : ℝ) * Real.posLog a +
        (w.1.mult : ℝ) * Real.posLog a⁻¹ := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith [hpa, hpainv, hmult]
    _ ≤ 2 * Height.logHeight₁
        (((x : NumberField.RingOfIntegers K) : K)) := by linarith

/-- If the prime represented by a finite-prime coordinate has norm at
most `J^8`, its normalized generator height is bounded solely by the
unit-lattice mass, the unit rank, the class number, and `log J`. -/
theorem numberFieldPrimeClassSupportedUnit_logHeight_le_of_absNorm_le_eight
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v : S) {J : ℕ}
    (hvJ : v.1.asIdeal.absNorm ≤ J ^ 8) :
    Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) ≤
      2 * numberFieldFundamentalUnitLogMass K +
        ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
          ((NumberField.classNumber K : ℝ) *
            (8 * Real.log (J : ℝ))) := by
  have hmass := numberFieldPrimeClassSupportedUnit_logHeight_le_mass S v
  have hlog : Real.log
      ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) ≤
        (NumberField.classNumber K : ℝ) *
          (8 * Real.log (J : ℝ)) :=
    log_nat_pow_le_class_mul_eight_log
      (Nat.zero_lt_one.trans
        (NumberField.HeightOneSpectrum.one_lt_absNorm v.1)) hvJ
  have hcoef : 0 ≤ ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  exact hmass.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hlog hcoef))

/-- An `S`-unit raised to the class number has completely explicit
coordinates: one exponent for each finite prime in `S`, a torsion unit,
and one exponent for each member of Dirichlet's fundamental system. -/
theorem numberField_supportedUnit_classNumber_fundSystem_decomposition
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (u : S.unit K) :
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K)
        (ζ : NumberField.Units.torsion K)
        (f : Fin (NumberField.Units.rank K) → ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
            (q : Kˣ) ∧
        SupportedUnits.emptyEquivUnits K q =
          ζ.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ f i ∧
        ∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd := by
  obtain ⟨e, q, hpow, he⟩ :=
    SupportedUnits.exists_primeClassProduct_mul_emptySupportedUnit_eq_pow S u
  obtain ⟨⟨ζ, f⟩, hq, _hunique⟩ :=
    NumberField.Units.exist_unique_eq_mul_prod K
      (SupportedUnits.emptyEquivUnits K q)
  exact ⟨e, q, ζ, f, hpow, hq, he⟩

/-- The class-number decomposition with a quantitative bound for every
ordinary-unit exponent in terms of the height of the residual global
unit and the conditioning constant of the fixed unit-lattice basis. -/
theorem numberField_supportedUnit_classNumber_fundSystem_decomposition_with_exponent_bound
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (u : S.unit K) :
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K)
        (ζ : NumberField.Units.torsion K)
        (f : Fin (NumberField.Units.rank K) → ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
            (q : Kˣ) ∧
        SupportedUnits.emptyEquivUnits K q =
          ζ.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ f i ∧
        (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
        ∀ i,
          |(f i : ℝ)| ≤
            2 * numberFieldFundamentalUnitCoordinateNorm K *
              Height.logHeight₁
                ((((SupportedUnits.emptyEquivUnits K q) :
                  NumberField.RingOfIntegers K) : K)) := by
  obtain ⟨e, q, ζ, f, hpow, hq, he⟩ :=
    numberField_supportedUnit_classNumber_fundSystem_decomposition S u
  refine ⟨e, q, ζ, f, hpow, hq, he, ?_⟩
  intro i
  have hcoord := numberField_ordinaryUnit_exponent_abs_le K ζ.2 hq i
  have hlog := numberField_logEmbedding_norm_le_two_logHeight K
    (SupportedUnits.emptyEquivUnits K q)
  have hC : 0 ≤ numberFieldFundamentalUnitCoordinateNorm K :=
    numberFieldFundamentalUnitCoordinateNorm_nonneg K
  calc
    |(f i : ℝ)| ≤ numberFieldFundamentalUnitCoordinateNorm K *
        ‖NumberField.Units.logEmbedding K
          (Additive.ofMul (SupportedUnits.emptyEquivUnits K q))‖ := hcoord
    _ ≤ numberFieldFundamentalUnitCoordinateNorm K *
        (2 * Height.logHeight₁
          ((((SupportedUnits.emptyEquivUnits K q) :
            NumberField.RingOfIntegers K) : K))) :=
      mul_le_mul_of_nonneg_left hlog hC
    _ = 2 * numberFieldFundamentalUnitCoordinateNorm K *
        Height.logHeight₁
          ((((SupportedUnits.emptyEquivUnits K q) :
            NumberField.RingOfIntegers K) : K)) := by ring

/-- The same class-number decomposition, now written entirely in the
ambient number field as one product of the finite-prime generators,
torsion, and Dirichlet fundamental units. -/
theorem numberField_supportedUnit_classNumber_explicit_product
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (u : S.unit K) :
    ∃ (e : S → ℤ) (ζ : NumberField.Units.torsion K)
        (f : Fin (NumberField.Units.rank K) → ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
        (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
          Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1 *
            ∏ i, (Units.map (algebraMap
              (NumberField.RingOfIntegers K) K).toMonoidHom
              (NumberField.Units.fundSystem K i)) ^ f i ∧
        ∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd := by
  obtain ⟨e, q, ζ, f, hpow, hq, he⟩ :=
    numberField_supportedUnit_classNumber_fundSystem_decomposition S u
  have hqK := congrArg
    (Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom) hq
  have hmap :
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (SupportedUnits.emptyEquivUnits K q) = (q : Kˣ) := by
    exact SupportedUnits.unitsMap_emptyEquivUnits
      (R := NumberField.RingOfIntegers K) K q
  rw [hmap] at hqK
  simp only [map_mul, map_prod, map_zpow] at hqK
  refine ⟨e, ζ, f, ?_, he⟩
  rw [hpow, hqK]
  simp only [mul_assoc]

/-- A number field of degree at most eight has at most seven independent
ordinary units. -/
theorem numberField_units_rank_le_seven
    {K : Type*} [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8) :
    NumberField.Units.rank K ≤ 7 := by
  have hcard : Fintype.card (NumberField.InfinitePlace K) ≤
      Module.finrank ℚ K := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    classical
    calc
      Fintype.card (NumberField.InfinitePlace K) =
          ∑ _w : NumberField.InfinitePlace K, 1 := by simp
      _ ≤ ∑ w : NumberField.InfinitePlace K, w.mult := by
        exact Finset.sum_le_sum fun w _ ↦
          Nat.one_le_iff_ne_zero.mpr NumberField.InfinitePlace.mult_ne_zero
  rw [NumberField.Units.rank]
  omega

/-- The explicit non-torsion coordinate family for an `S`-unit has at
most `|S| + 7` members in a degree-eight number field. -/
theorem numberField_supportedUnit_coordinate_count_le
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (hdeg : Module.finrank ℚ K ≤ 8) :
    Fintype.card S + NumberField.Units.rank K ≤
      Fintype.card S + 7 := by
  exact Nat.add_le_add_left (numberField_units_rank_le_seven hdeg) _

/-- A root of unity contributes zero logarithmic height to the explicit
supported-unit product. -/
theorem numberField_logHeight_torsionUnit_eq_zero
    {K : Type*} [Field K] [NumberField K]
    (ζ : NumberField.Units.torsion K) :
    Height.logHeight₁ (((ζ.1 : NumberField.RingOfIntegers K) : K)) = 0 := by
  obtain ⟨n, hnpos, hn⟩ := isOfFinOrder_iff_pow_eq_one.mp
    ((CommGroup.mem_torsion _).mp ζ.2)
  have hpow : (((ζ.1 : NumberField.RingOfIntegers K) : K)) ^ n = 1 := by
    have hnval := congrArg
      (Units.val : (NumberField.RingOfIntegers K)ˣ →
        NumberField.RingOfIntegers K) hn
    have hnmap := congrArg
      (algebraMap (NumberField.RingOfIntegers K) K) hnval
    simpa using hnmap
  have hh := congrArg Height.logHeight₁ hpow
  rw [Height.logHeight₁_pow, Height.logHeight₁_one] at hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  nlinarith

/-- The finite supported-unit groups produced by the Pell factors are
finitely generated.  This is the Dirichlet `S`-unit finiteness layer in
the precise number field used above. -/
theorem numberFieldPrimeSupport_units_fg
    {K : Type*} [Field K] [NumberField K] (z : Kˣ) :
    Group.FG ((numberFieldPrimeSupport z).unit K) := by
  let : Fintype (numberFieldPrimeSupport z) :=
    (numberFieldPrimeSupport_finite z).fintype
  have hOrd : Group.FG (NumberField.RingOfIntegers K)ˣ :=
    Group.fg_iff_monoid_fg.mpr inferInstance
  have hEmpty : Group.FG
      ((∅ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K) :=
    Group.fg_of_surjective
      (f := (SupportedUnits.emptyEquivUnits
        (R := NumberField.RingOfIntegers K) K).symm.toMonoidHom)
      (SupportedUnits.emptyEquivUnits
        (R := NumberField.RingOfIntegers K) K).symm.surjective
  exact SupportedUnits.fg (numberFieldPrimeSupport z) K hEmpty

/-- In a splitting field of degree at most eight, the supported-unit rank
is at most seven plus the number of finite primes in the support. -/
theorem numberFieldPrimeSupport_units_finrank_le
    {K : Type*} [Field K] [NumberField K] (z : Kˣ)
    (hdeg : Module.finrank ℚ K ≤ 8) :
    Module.finrank ℤ (Additive ((numberFieldPrimeSupport z).unit K)) ≤
      7 + Nat.card (numberFieldPrimeSupport z) := by
  let : Fintype (numberFieldPrimeSupport z) :=
    (numberFieldPrimeSupport_finite z).fintype
  let : Group.FG (NumberField.RingOfIntegers K)ˣ :=
    Group.fg_iff_monoid_fg.mpr inferInstance
  have hEmpty : Group.FG
      ((∅ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K) :=
    Group.fg_of_surjective
      (f := (SupportedUnits.emptyEquivUnits
        (R := NumberField.RingOfIntegers K) K).symm.toMonoidHom)
      (SupportedUnits.emptyEquivUnits
        (R := NumberField.RingOfIntegers K) K).symm.surjective
  have hsRank := SupportedUnits.finrank_le
    (numberFieldPrimeSupport z) K hEmpty
  have hEmptyRank :
      Module.finrank ℤ
          (Additive ((∅ : Set (IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers K))).unit K)) =
        NumberField.Units.rank K := by
    calc
      _ = Module.finrank ℤ
          (Additive (NumberField.RingOfIntegers K)ˣ) :=
        LinearEquiv.finrank_eq
          (AddEquiv.toIntLinearEquiv
            (MulEquiv.toAdditive (SupportedUnits.emptyEquivUnits
              (R := NumberField.RingOfIntegers K) K)))
      _ = NumberField.Units.rank K := NumberField.Units.finrank_eq K
  have hcard : Fintype.card (NumberField.InfinitePlace K) ≤
      Module.finrank ℚ K := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    classical
    calc
      Fintype.card (NumberField.InfinitePlace K) =
          ∑ _w : NumberField.InfinitePlace K, 1 := by simp
      _ ≤ ∑ w : NumberField.InfinitePlace K, w.mult := by
        exact Finset.sum_le_sum fun w _ ↦
          Nat.one_le_iff_ne_zero.mpr NumberField.InfinitePlace.mult_ne_zero
  have hunitRank : NumberField.Units.rank K ≤ 7 := by
    rw [NumberField.Units.rank]
    omega
  rw [hEmptyRank] at hsRank
  omega

/-- In any number field of degree at most eight, the rank of an `S`-unit
group is at most seven plus the cardinality of the finite support `S`. -/
theorem numberField_supported_units_finrank_le
    {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))}
    (hS : S.Finite) (hdeg : Module.finrank ℚ K ≤ 8) :
    Module.finrank ℤ (Additive (S.unit K)) ≤ 7 + Nat.card S := by
  let : Fintype S := hS.fintype
  let : Group.FG (NumberField.RingOfIntegers K)ˣ :=
    Group.fg_iff_monoid_fg.mpr inferInstance
  have hEmpty : Group.FG
      ((∅ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K) :=
    Group.fg_of_surjective
      (f := (SupportedUnits.emptyEquivUnits
        (R := NumberField.RingOfIntegers K) K).symm.toMonoidHom)
      (SupportedUnits.emptyEquivUnits
        (R := NumberField.RingOfIntegers K) K).symm.surjective
  have hsRank := SupportedUnits.finrank_le S K hEmpty
  have hEmptyRank :
      Module.finrank ℤ
          (Additive ((∅ : Set (IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers K))).unit K)) =
        NumberField.Units.rank K := by
    calc
      _ = Module.finrank ℤ
          (Additive (NumberField.RingOfIntegers K)ˣ) :=
        LinearEquiv.finrank_eq
          (AddEquiv.toIntLinearEquiv
            (MulEquiv.toAdditive (SupportedUnits.emptyEquivUnits
              (R := NumberField.RingOfIntegers K) K)))
      _ = NumberField.Units.rank K := NumberField.Units.finrank_eq K
  have hcard : Fintype.card (NumberField.InfinitePlace K) ≤
      Module.finrank ℚ K := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    classical
    calc
      Fintype.card (NumberField.InfinitePlace K) =
          ∑ _w : NumberField.InfinitePlace K, 1 := by simp
      _ ≤ ∑ w : NumberField.InfinitePlace K, w.mult := by
        exact Finset.sum_le_sum fun w _ ↦
          Nat.one_le_iff_ne_zero.mpr NumberField.InfinitePlace.mult_ne_zero
  have hunitRank : NumberField.Units.rank K ≤ 7 := by
    rw [NumberField.Units.rank]
    omega
  rw [hEmptyRank] at hsRank
  omega

/-- A common finite set of primes supporting all six factors of the three
Pell edges. -/
def pellCommonPrimeSupport
    {K : Type*} [Field K] [NumberField K] (z₁₂ z₁₃ z₂₃ : Kˣ) :
    Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :=
  numberFieldPrimeSupport z₁₂ ∪ numberFieldPrimeSupport z₁₃ ∪
    numberFieldPrimeSupport z₂₃

lemma pellCommonPrimeSupport_finite
    {K : Type*} [Field K] [NumberField K] (z₁₂ z₁₃ z₂₃ : Kˣ) :
    (pellCommonPrimeSupport z₁₂ z₁₃ z₂₃).Finite := by
  exact ((numberFieldPrimeSupport_finite z₁₂).union
    (numberFieldPrimeSupport_finite z₁₃)).union
      (numberFieldPrimeSupport_finite z₂₃)

/-- If the three rational right-hand sides are bounded by `J`, every prime
ideal in their common support has norm at most `J^8` in a degree-eight
splitting field. -/
lemma pellCommonPrimeSupport_absNorm_le_eight
    {K : Type*} [Field K] [NumberField K]
    (beta₁₂ beta₁₃ beta₂₃ : ℤ)
    (hbeta₁₂ : beta₁₂ ≠ 0) (hbeta₁₃ : beta₁₃ ≠ 0)
    (hbeta₂₃ : beta₂₃ ≠ 0) {J : ℕ}
    (hbeta₁₂J : beta₁₂.natAbs ≤ J)
    (hbeta₁₃J : beta₁₃.natAbs ≤ J)
    (hbeta₂₃J : beta₂₃.natAbs ≤ J)
    (hdeg : Module.finrank ℚ K ≤ 8)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (hv : v ∈ pellCommonPrimeSupport
      (Units.mk0 (beta₁₂ : K) (Int.cast_ne_zero.mpr hbeta₁₂))
      (Units.mk0 (beta₁₃ : K) (Int.cast_ne_zero.mpr hbeta₁₃))
      (Units.mk0 (beta₂₃ : K) (Int.cast_ne_zero.mpr hbeta₂₃))) :
    v.asIdeal.absNorm ≤ J ^ 8 := by
  rcases hv with (hv | hv) | hv
  · exact numberFieldPrime_absNorm_le_eight_of_mem_support
      beta₁₂ hbeta₁₂ hbeta₁₂J hdeg v hv
  · exact numberFieldPrime_absNorm_le_eight_of_mem_support
      beta₁₃ hbeta₁₃ hbeta₁₃J hdeg v hv
  · exact numberFieldPrime_absNorm_le_eight_of_mem_support
      beta₂₃ hbeta₂₃ hbeta₂₃J hdeg v hv

/-- Every finite-prime coordinate in the common Pell support therefore
has the same explicit height majorant. -/
theorem pellCommonPrimeClassSupportedUnit_logHeight_le
    {K : Type*} [Field K] [NumberField K]
    (beta₁₂ beta₁₃ beta₂₃ : ℤ)
    (hbeta₁₂ : beta₁₂ ≠ 0) (hbeta₁₃ : beta₁₃ ≠ 0)
    (hbeta₂₃ : beta₂₃ ≠ 0) {J : ℕ}
    (hbeta₁₂J : beta₁₂.natAbs ≤ J)
    (hbeta₁₃J : beta₁₃.natAbs ≤ J)
    (hbeta₂₃J : beta₂₃.natAbs ≤ J)
    (hdeg : Module.finrank ℚ K ≤ 8)
    (v : pellCommonPrimeSupport
      (Units.mk0 (beta₁₂ : K) (Int.cast_ne_zero.mpr hbeta₁₂))
      (Units.mk0 (beta₁₃ : K) (Int.cast_ne_zero.mpr hbeta₁₃))
      (Units.mk0 (beta₂₃ : K) (Int.cast_ne_zero.mpr hbeta₂₃))) :
    Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit
          (pellCommonPrimeSupport
            (Units.mk0 (beta₁₂ : K) (Int.cast_ne_zero.mpr hbeta₁₂))
            (Units.mk0 (beta₁₃ : K) (Int.cast_ne_zero.mpr hbeta₁₃))
            (Units.mk0 (beta₂₃ : K) (Int.cast_ne_zero.mpr hbeta₂₃))) v) :
              Kˣ) : K)) ≤
      2 * numberFieldFundamentalUnitLogMass K +
        ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
          ((NumberField.classNumber K : ℝ) *
            (8 * Real.log (J : ℝ))) := by
  apply numberFieldPrimeClassSupportedUnit_logHeight_le_of_absNorm_le_eight
  exact pellCommonPrimeSupport_absNorm_le_eight
    beta₁₂ beta₁₃ beta₂₃ hbeta₁₂ hbeta₁₃ hbeta₂₃
    hbeta₁₂J hbeta₁₃J hbeta₂₃J hdeg v.1 v.2

lemma pellCommonPrimeSupport_card_le_sum
    {K : Type*} [Field K] [NumberField K] (z₁₂ z₁₃ z₂₃ : Kˣ) :
    Nat.card (pellCommonPrimeSupport z₁₂ z₁₃ z₂₃) ≤
      Nat.card (numberFieldPrimeSupport z₁₂) +
        Nat.card (numberFieldPrimeSupport z₁₃) +
          Nat.card (numberFieldPrimeSupport z₂₃) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  calc
    (pellCommonPrimeSupport z₁₂ z₁₃ z₂₃).ncard ≤
        (numberFieldPrimeSupport z₁₂ ∪
          numberFieldPrimeSupport z₁₃).ncard +
          (numberFieldPrimeSupport z₂₃).ncard := by
      exact Set.ncard_union_le _ _
    _ ≤ ((numberFieldPrimeSupport z₁₂).ncard +
          (numberFieldPrimeSupport z₁₃).ncard) +
          (numberFieldPrimeSupport z₂₃).ncard := by
      exact Nat.add_le_add_right (Set.ncard_union_le _ _) _

/-- Explicit support bound for the common support of the three Pell
right-hand sides. -/
lemma pellCommonIntegerPrimeSupport_card_le
    {K : Type*} [Field K] [NumberField K]
    (beta₁₂ beta₁₃ beta₂₃ : ℤ)
    (hbeta₁₂ : beta₁₂ ≠ 0) (hbeta₁₃ : beta₁₃ ≠ 0)
    (hbeta₂₃ : beta₂₃ ≠ 0) :
    Nat.card (pellCommonPrimeSupport
        (Units.mk0 (beta₁₂ : K) (Int.cast_ne_zero.mpr hbeta₁₂))
        (Units.mk0 (beta₁₃ : K) (Int.cast_ne_zero.mpr hbeta₁₃))
        (Units.mk0 (beta₂₃ : K) (Int.cast_ne_zero.mpr hbeta₂₃))) ≤
      Module.finrank ℚ K *
        (beta₁₂.natAbs.primeFactors.card +
          beta₁₃.natAbs.primeFactors.card +
            beta₂₃.natAbs.primeFactors.card) := by
  calc
    Nat.card (pellCommonPrimeSupport
        (Units.mk0 (beta₁₂ : K) (Int.cast_ne_zero.mpr hbeta₁₂))
        (Units.mk0 (beta₁₃ : K) (Int.cast_ne_zero.mpr hbeta₁₃))
        (Units.mk0 (beta₂₃ : K) (Int.cast_ne_zero.mpr hbeta₂₃))) ≤
        Nat.card (numberFieldPrimeSupport
          (Units.mk0 (beta₁₂ : K) (Int.cast_ne_zero.mpr hbeta₁₂))) +
          Nat.card (numberFieldPrimeSupport
            (Units.mk0 (beta₁₃ : K) (Int.cast_ne_zero.mpr hbeta₁₃))) +
          Nat.card (numberFieldPrimeSupport
            (Units.mk0 (beta₂₃ : K) (Int.cast_ne_zero.mpr hbeta₂₃))) :=
      pellCommonPrimeSupport_card_le_sum _ _ _
    _ ≤ Module.finrank ℚ K * beta₁₂.natAbs.primeFactors.card +
          Module.finrank ℚ K * beta₁₃.natAbs.primeFactors.card +
          Module.finrank ℚ K * beta₂₃.natAbs.primeFactors.card := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (numberFieldPrimeSupport_card_le beta₁₂ hbeta₁₂)
          (numberFieldPrimeSupport_card_le beta₁₃ hbeta₁₃))
        (numberFieldPrimeSupport_card_le beta₂₃ hbeta₂₃)
    _ = Module.finrank ℚ K *
        (beta₁₂.natAbs.primeFactors.card +
          beta₁₃.natAbs.primeFactors.card +
            beta₂₃.natAbs.primeFactors.card) := by ring

lemma pellCommonIntegerSupportedUnits_finrank_le
    {K : Type*} [Field K] [NumberField K]
    (beta₁₂ beta₁₃ beta₂₃ : ℤ)
    (hbeta₁₂ : beta₁₂ ≠ 0) (hbeta₁₃ : beta₁₃ ≠ 0)
    (hbeta₂₃ : beta₂₃ ≠ 0)
    (hdeg : Module.finrank ℚ K ≤ 8) :
    Module.finrank ℤ (Additive ((pellCommonPrimeSupport
        (Units.mk0 (beta₁₂ : K) (Int.cast_ne_zero.mpr hbeta₁₂))
        (Units.mk0 (beta₁₃ : K) (Int.cast_ne_zero.mpr hbeta₁₃))
        (Units.mk0 (beta₂₃ : K) (Int.cast_ne_zero.mpr hbeta₂₃))).unit K)) ≤
      7 + 8 *
        (beta₁₂.natAbs.primeFactors.card +
          beta₁₃.natAbs.primeFactors.card +
            beta₂₃.natAbs.primeFactors.card) := by
  let S := pellCommonPrimeSupport
    (Units.mk0 (beta₁₂ : K) (Int.cast_ne_zero.mpr hbeta₁₂))
    (Units.mk0 (beta₁₃ : K) (Int.cast_ne_zero.mpr hbeta₁₃))
    (Units.mk0 (beta₂₃ : K) (Int.cast_ne_zero.mpr hbeta₂₃))
  have hS : S.Finite := pellCommonPrimeSupport_finite _ _ _
  have hrank := numberField_supported_units_finrank_le hS hdeg
  have hcard := pellCommonIntegerPrimeSupport_card_le
    (K := K) beta₁₂ beta₁₃ beta₂₃ hbeta₁₂ hbeta₁₃ hbeta₂₃
  have hcardS : Nat.card S ≤ Module.finrank ℚ K *
      (beta₁₂.natAbs.primeFactors.card +
        beta₁₃.natAbs.primeFactors.card +
          beta₂₃.natAbs.primeFactors.card) := by
    simpa [S] using hcard
  change Module.finrank ℤ (Additive (S.unit K)) ≤ _
  calc
    Module.finrank ℤ (Additive (S.unit K)) ≤ 7 + Nat.card S := hrank
    _ ≤ 7 + Module.finrank ℚ K *
        (beta₁₂.natAbs.primeFactors.card +
          beta₁₃.natAbs.primeFactors.card +
            beta₂₃.natAbs.primeFactors.card) :=
      Nat.add_le_add_left hcardS 7
    _ ≤ 7 + 8 *
        (beta₁₂.natAbs.primeFactors.card +
          beta₁₃.natAbs.primeFactors.card +
            beta₂₃.natAbs.primeFactors.card) := by
      gcongr

/-- For three distinct shifts in `[0,J]`, the common supported-unit rank
is at most `7 + 24 log₂ J`. -/
lemma pellShiftCommonSupportedUnits_finrank_le
    {K : Type*} [Field K] [NumberField K]
    {i j k J : ℕ} (hi : i ≤ J) (hj : j ≤ J) (hk : k ≤ J)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdeg : Module.finrank ℚ K ≤ 8) :
    Module.finrank ℤ (Additive ((pellCommonPrimeSupport
        (Units.mk0 (((i : ℤ) - j : ℤ) : K)
          (Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hij))))
        (Units.mk0 (((i : ℤ) - k : ℤ) : K)
          (Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hik))))
        (Units.mk0 (((j : ℤ) - k : ℤ) : K)
          (Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hjk))))).unit K)) ≤
      7 + 24 * Nat.log 2 J := by
  let beta₁₂ : ℤ := (i : ℤ) - j
  let beta₁₃ : ℤ := (i : ℤ) - k
  let beta₂₃ : ℤ := (j : ℤ) - k
  have hbeta₁₂ : beta₁₂ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
  have hbeta₁₃ : beta₁₃ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hik)
  have hbeta₂₃ : beta₂₃ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjk)
  have hrank := pellCommonIntegerSupportedUnits_finrank_le
    (K := K) beta₁₂ beta₁₃ beta₂₃ hbeta₁₂ hbeta₁₃ hbeta₂₃ hdeg
  have habs₁₂ : beta₁₂.natAbs ≤ J := by
    exact Int.natAbs_coe_sub_coe_le_of_le hi hj
  have habs₁₃ : beta₁₃.natAbs ≤ J := by
    exact Int.natAbs_coe_sub_coe_le_of_le hi hk
  have habs₂₃ : beta₂₃.natAbs ≤ J := by
    exact Int.natAbs_coe_sub_coe_le_of_le hj hk
  have hpf₁₂ : beta₁₂.natAbs.primeFactors.card ≤ Nat.log 2 J :=
    (primeFactors_card_le_log_two (Int.natAbs_ne_zero.mpr hbeta₁₂)).trans
      (Nat.log_mono_right habs₁₂)
  have hpf₁₃ : beta₁₃.natAbs.primeFactors.card ≤ Nat.log 2 J :=
    (primeFactors_card_le_log_two (Int.natAbs_ne_zero.mpr hbeta₁₃)).trans
      (Nat.log_mono_right habs₁₃)
  have hpf₂₃ : beta₂₃.natAbs.primeFactors.card ≤ Nat.log 2 J :=
    (primeFactors_card_le_log_two (Int.natAbs_ne_zero.mpr hbeta₂₃)).trans
      (Nat.log_mono_right habs₂₃)
  simpa only [beta₁₂, beta₁₃, beta₂₃] using hrank.trans (by omega)

lemma left_mem_pellCommon_supportedUnit
    {K : Type*} [Field K] [NumberField K] {z₁₂ z₁₃ z₂₃ u : Kˣ}
    (hu : u ∈ (numberFieldPrimeSupport z₁₂).unit K) :
    u ∈ (pellCommonPrimeSupport z₁₂ z₁₃ z₂₃).unit K :=
  SupportedUnits.mono (F := K)
    (S := numberFieldPrimeSupport z₁₂)
    (T := pellCommonPrimeSupport z₁₂ z₁₃ z₂₃)
    (by intro v hv; exact Or.inl (Or.inl hv)) hu

lemma middle_mem_pellCommon_supportedUnit
    {K : Type*} [Field K] [NumberField K] {z₁₂ z₁₃ z₂₃ u : Kˣ}
    (hu : u ∈ (numberFieldPrimeSupport z₁₃).unit K) :
    u ∈ (pellCommonPrimeSupport z₁₂ z₁₃ z₂₃).unit K :=
  SupportedUnits.mono (F := K)
    (S := numberFieldPrimeSupport z₁₃)
    (T := pellCommonPrimeSupport z₁₂ z₁₃ z₂₃)
    (by intro v hv; exact Or.inl (Or.inr hv)) hu

lemma right_mem_pellCommon_supportedUnit
    {K : Type*} [Field K] [NumberField K] {z₁₂ z₁₃ z₂₃ u : Kˣ}
    (hu : u ∈ (numberFieldPrimeSupport z₂₃).unit K) :
    u ∈ (pellCommonPrimeSupport z₁₂ z₁₃ z₂₃).unit K :=
  SupportedUnits.mono (F := K)
    (S := numberFieldPrimeSupport z₂₃)
    (T := pellCommonPrimeSupport z₁₂ z₁₃ z₂₃)
    (by intro v hv; exact Or.inr hv) hu

/-- Three nonzero minus factors in one supported-unit group give a genuine
two-variable `S`-unit equation `U + V = 1`. -/
theorem pellMinus_unitEquation_in_supportedUnits
    {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))}
    (s₁ s₂ s₃ : K) (x₁ x₂ x₃ : ℤ)
    (h₁₂ : pellValueMinus s₁ s₂ x₁ x₂ ≠ 0)
    (h₁₃ : pellValueMinus s₁ s₃ x₁ x₃ ≠ 0)
    (h₂₃ : pellValueMinus s₂ s₃ x₂ x₃ ≠ 0)
    (hu₁₂ : Units.mk0 (pellValueMinus s₁ s₂ x₁ x₂) h₁₂ ∈
      S.unit K)
    (hu₁₃ : Units.mk0 (pellValueMinus s₁ s₃ x₁ x₃) h₁₃ ∈
      S.unit K)
    (hu₂₃ : Units.mk0 (pellValueMinus s₂ s₃ x₂ x₃) h₂₃ ∈
      S.unit K) :
    ∃ U V : S.unit K,
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ := by
  let u₁₂ : S.unit K :=
    ⟨Units.mk0 (pellValueMinus s₁ s₂ x₁ x₂) h₁₂, hu₁₂⟩
  let u₁₃ : S.unit K :=
    ⟨Units.mk0 (pellValueMinus s₁ s₃ x₁ x₃) h₁₃, hu₁₃⟩
  let u₂₃ : S.unit K :=
    ⟨Units.mk0 (pellValueMinus s₂ s₃ x₂ x₃) h₂₃, hu₂₃⟩
  refine ⟨u₁₂ / u₁₃, u₂₃ / u₁₃, ?_, ?_, ?_⟩
  · simpa [u₁₂, u₁₃, u₂₃] using
      pellValue_minus_unitEquation s₁ s₂ s₃ x₁ x₂ x₃ h₁₃
  · simp [u₁₂, u₁₃]
  · simp [u₂₃, u₁₃]

/-- Every supported-unit group with finite prime support is finitely
generated over a number field. -/
theorem numberField_supported_units_fg
    {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))}
    [Finite S] : Group.FG (S.unit K) := by
  have hOrd : Group.FG (NumberField.RingOfIntegers K)ˣ :=
    Group.fg_iff_monoid_fg.mpr inferInstance
  have hEmpty : Group.FG
      ((∅ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K) :=
    Group.fg_of_surjective
      (f := (SupportedUnits.emptyEquivUnits
        (R := NumberField.RingOfIntegers K) K).symm.toMonoidHom)
      (SupportedUnits.emptyEquivUnits
        (R := NumberField.RingOfIntegers K) K).symm.surjective
  exact SupportedUnits.fg S K hEmpty

/-- A finite prime support admits a finite generating family.  This is the
group-theoretic coordinate system used for the exponents in the
supported-unit equation. -/
theorem supportedUnit_finite_generators
    {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))}
    (hS : S.Finite) :
    ∃ T : Finset (S.unit K),
      Subgroup.closure (T : Set (S.unit K)) = ⊤ := by
  let : Fintype S := hS.fintype
  obtain ⟨_n, T, _hcard, hT⟩ :=
    Group.fg_iff'.mp (numberField_supported_units_fg (K := K) (S := S))
  exact ⟨T, hT⟩

/-- Every pair of supported units has simultaneous integer-exponent
coordinates in one minimum-cardinality generating family. -/
theorem supportedUnit_two_exponent_representation
    {K : Type*} [Field K] [NumberField K]
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))}
    (hS : S.Finite) (U V : S.unit K) :
    ∃ (T : Finset (S.unit K)) (eU eV : T → ℤ),
      U = ∏ g : T, (g.1 : S.unit K) ^ eU g ∧
      V = ∏ g : T, (g.1 : S.unit K) ^ eV g := by
  let : Fintype S := hS.fintype
  obtain ⟨T, hT⟩ := supportedUnit_finite_generators (K := K) hS
  have hUmem : U ∈ Subgroup.closure (T : Set (S.unit K)) := by
    rw [hT]
    exact Subgroup.mem_top U
  have hVmem : V ∈ Subgroup.closure (T : Set (S.unit K)) := by
    rw [hT]
    exact Subgroup.mem_top V
  obtain ⟨eU, hU⟩ :=
    (Subgroup.mem_closure_iff_of_fintype (s := (T : Set (S.unit K)))).mp hUmem
  obtain ⟨eV, hV⟩ :=
    (Subgroup.mem_closure_iff_of_fintype (s := (T : Set (S.unit K)))).mp hVmem
  exact ⟨T, eU, eV, hU, hV⟩

/-- All three edges of a nondegenerate simultaneous Pell solution have
the finite-support factor certificates above. -/
theorem simultaneousPell_supported_factor_pairs
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) :
    (∃ hm hp,
      IsIntegral ℤ (pellValueMinus s₁ s₂ x₁ x₂) ∧
      IsIntegral ℤ (pellValuePlus s₁ s₂ x₁ x₂) ∧
      pellValueMinus s₁ s₂ x₁ x₂ *
          pellValuePlus s₁ s₂ x₁ x₂ = (β₁₂ : K) ∧
      Units.mk0 (pellValueMinus s₁ s₂ x₁ x₂) hm ∈
        (numberFieldPrimeSupport
          (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))).unit K ∧
      Units.mk0 (pellValuePlus s₁ s₂ x₁ x₂) hp ∈
        (numberFieldPrimeSupport
          (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))).unit K) ∧
    (∃ hm hp,
      IsIntegral ℤ (pellValueMinus s₁ s₃ x₁ x₃) ∧
      IsIntegral ℤ (pellValuePlus s₁ s₃ x₁ x₃) ∧
      pellValueMinus s₁ s₃ x₁ x₃ *
          pellValuePlus s₁ s₃ x₁ x₃ = (β₁₃ : K) ∧
      Units.mk0 (pellValueMinus s₁ s₃ x₁ x₃) hm ∈
        (numberFieldPrimeSupport
          (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))).unit K ∧
      Units.mk0 (pellValuePlus s₁ s₃ x₁ x₃) hp ∈
        (numberFieldPrimeSupport
          (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))).unit K) ∧
    (∃ hm hp,
      IsIntegral ℤ (pellValueMinus s₂ s₃ x₂ x₃) ∧
      IsIntegral ℤ (pellValuePlus s₂ s₃ x₂ x₃) ∧
      pellValueMinus s₂ s₃ x₂ x₃ *
          pellValuePlus s₂ s₃ x₂ x₃ = ((β₁₃ - β₁₂ : ℤ) : K) ∧
      Units.mk0 (pellValueMinus s₂ s₃ x₂ x₃) hm ∈
        (numberFieldPrimeSupport
          (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
            (Int.cast_ne_zero.mpr hβ₂₃))).unit K ∧
      Units.mk0 (pellValuePlus s₂ s₃ x₂ x₃) hp ∈
        (numberFieldPrimeSupport
          (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
            (Int.cast_ne_zero.mpr hβ₂₃))).unit K) := by
  rcases hPell with ⟨h₁₂, h₁₃⟩
  have h₂₃ : γ₂ * x₂ ^ 2 - γ₃ * x₃ ^ 2 = β₁₃ - β₁₂ := by
    nlinarith
  have c₁₂ := pell_factor_pair_supported_units hs₁ hs₂ h₁₂ hβ₁₂
  have c₁₃ := pell_factor_pair_supported_units hs₁ hs₃ h₁₃ hβ₁₃
  have c₂₃ := pell_factor_pair_supported_units hs₂ hs₃ h₂₃ hβ₂₃
  rcases c₁₂ with ⟨hm₁₂, hp₁₂, hiM₁₂, hiP₁₂, hpEq₁₂, _hf₁₂, huM₁₂, huP₁₂⟩
  rcases c₁₃ with ⟨hm₁₃, hp₁₃, hiM₁₃, hiP₁₃, hpEq₁₃, _hf₁₃, huM₁₃, huP₁₃⟩
  rcases c₂₃ with ⟨hm₂₃, hp₂₃, hiM₂₃, hiP₂₃, hpEq₂₃, _hf₂₃, huM₂₃, huP₂₃⟩
  exact ⟨⟨hm₁₂, hp₁₂, hiM₁₂, hiP₁₂, hpEq₁₂, huM₁₂, huP₁₂⟩,
    ⟨hm₁₃, hp₁₃, hiM₁₃, hiP₁₃, hpEq₁₃, huM₁₃, huP₁₃⟩,
    ⟨hm₂₃, hp₂₃, hiM₂₃, hiP₂₃, hpEq₂₃, huM₂₃, huP₂₃⟩⟩

/-- A nondegenerate simultaneous Pell solution yields an actual two-term
supported-unit equation in one finite prime support. -/
theorem simultaneousPell_common_supported_unit_equation
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K),
      S.Finite ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ := by
  let z₁₂ : Kˣ :=
    Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂)
  let z₁₃ : Kˣ :=
    Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃)
  let z₂₃ : Kˣ :=
    Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K) (Int.cast_ne_zero.mpr hβ₂₃)
  let S := pellCommonPrimeSupport z₁₂ z₁₃ z₂₃
  rcases simultaneousPell_supported_factor_pairs hs₁ hs₂ hs₃ hPell
      hβ₁₂ hβ₁₃ hβ₂₃ with
    ⟨⟨hm₁₂, _hp₁₂, _hiM₁₂, _hiP₁₂, _hprod₁₂, huM₁₂, _huP₁₂⟩,
      ⟨hm₁₃, _hp₁₃, _hiM₁₃, _hiP₁₃, _hprod₁₃, huM₁₃, _huP₁₃⟩,
      ⟨hm₂₃, _hp₂₃, _hiM₂₃, _hiP₂₃, _hprod₂₃, huM₂₃, _huP₂₃⟩⟩
  have hu₁₂ : Units.mk0 (pellValueMinus s₁ s₂ x₁ x₂) hm₁₂ ∈
      S.unit K := by
    exact left_mem_pellCommon_supportedUnit
      (z₁₂ := z₁₂) (z₁₃ := z₁₃) (z₂₃ := z₂₃) (by simpa [z₁₂] using huM₁₂)
  have hu₁₃ : Units.mk0 (pellValueMinus s₁ s₃ x₁ x₃) hm₁₃ ∈
      S.unit K := by
    exact middle_mem_pellCommon_supportedUnit
      (z₁₂ := z₁₂) (z₁₃ := z₁₃) (z₂₃ := z₂₃) (by simpa [z₁₃] using huM₁₃)
  have hu₂₃ : Units.mk0 (pellValueMinus s₂ s₃ x₂ x₃) hm₂₃ ∈
      S.unit K := by
    exact right_mem_pellCommon_supportedUnit
      (z₁₂ := z₁₂) (z₁₃ := z₁₃) (z₂₃ := z₂₃) (by simpa [z₂₃] using huM₂₃)
  obtain ⟨U, V, hUV, hU, hV⟩ :=
    pellMinus_unitEquation_in_supportedUnits
      (S := S) s₁ s₂ s₃ x₁ x₂ x₃ hm₁₂ hm₁₃ hm₂₃ hu₁₂ hu₁₃ hu₂₃
  exact ⟨S, U, V, pellCommonPrimeSupport_finite z₁₂ z₁₃ z₂₃,
    hUV, hU, hV⟩

/-- The supported-unit reduction with its support fixed explicitly and with
the degree-eight support and rank estimates included.  This is the
quantitative algebraic input to the effective `S`-unit estimate. -/
theorem simultaneousPell_quantitative_common_supported_unit_equation
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) (hdeg : Module.finrank ℚ K ≤ 8) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K),
      S = pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
          (Int.cast_ne_zero.mpr hβ₂₃)) ∧
      S.Finite ∧
      Nat.card S ≤ 8 *
        (β₁₂.natAbs.primeFactors.card +
          β₁₃.natAbs.primeFactors.card +
            (β₁₃ - β₁₂).natAbs.primeFactors.card) ∧
      Module.finrank ℤ (Additive (S.unit K)) ≤ 7 + 8 *
        (β₁₂.natAbs.primeFactors.card +
          β₁₃.natAbs.primeFactors.card +
            (β₁₃ - β₁₂).natAbs.primeFactors.card) ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ := by
  let z₁₂ : Kˣ := Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂)
  let z₁₃ : Kˣ := Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃)
  let z₂₃ : Kˣ := Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
    (Int.cast_ne_zero.mpr hβ₂₃)
  let S := pellCommonPrimeSupport z₁₂ z₁₃ z₂₃
  rcases simultaneousPell_supported_factor_pairs hs₁ hs₂ hs₃ hPell
      hβ₁₂ hβ₁₃ hβ₂₃ with
    ⟨⟨hm₁₂, _hp₁₂, _hiM₁₂, _hiP₁₂, _hprod₁₂, huM₁₂, _huP₁₂⟩,
      ⟨hm₁₃, _hp₁₃, _hiM₁₃, _hiP₁₃, _hprod₁₃, huM₁₃, _huP₁₃⟩,
      ⟨hm₂₃, _hp₂₃, _hiM₂₃, _hiP₂₃, _hprod₂₃, huM₂₃, _huP₂₃⟩⟩
  have hu₁₂ : Units.mk0 (pellValueMinus s₁ s₂ x₁ x₂) hm₁₂ ∈ S.unit K := by
    exact left_mem_pellCommon_supportedUnit
      (z₁₂ := z₁₂) (z₁₃ := z₁₃) (z₂₃ := z₂₃) (by simpa [z₁₂] using huM₁₂)
  have hu₁₃ : Units.mk0 (pellValueMinus s₁ s₃ x₁ x₃) hm₁₃ ∈ S.unit K := by
    exact middle_mem_pellCommon_supportedUnit
      (z₁₂ := z₁₂) (z₁₃ := z₁₃) (z₂₃ := z₂₃) (by simpa [z₁₃] using huM₁₃)
  have hu₂₃ : Units.mk0 (pellValueMinus s₂ s₃ x₂ x₃) hm₂₃ ∈ S.unit K := by
    exact right_mem_pellCommon_supportedUnit
      (z₁₂ := z₁₂) (z₁₃ := z₁₃) (z₂₃ := z₂₃) (by simpa [z₂₃] using huM₂₃)
  obtain ⟨U, V, hUV, hU, hV⟩ :=
    pellMinus_unitEquation_in_supportedUnits
      (S := S) s₁ s₂ s₃ x₁ x₂ x₃ hm₁₂ hm₁₃ hm₂₃ hu₁₂ hu₁₃ hu₂₃
  have hcard := pellCommonIntegerPrimeSupport_card_le
    (K := K) β₁₂ β₁₃ (β₁₃ - β₁₂) hβ₁₂ hβ₁₃ hβ₂₃
  have hrank := pellCommonIntegerSupportedUnits_finrank_le
    (K := K) β₁₂ β₁₃ (β₁₃ - β₁₂) hβ₁₂ hβ₁₃ hβ₂₃ hdeg
  refine ⟨S, U, V, ?_, pellCommonPrimeSupport_finite z₁₂ z₁₃ z₂₃, ?_, ?_,
    hUV, hU, hV⟩
  · simp [S, z₁₂, z₁₃, z₂₃]
  · exact (by simpa [S, z₁₂, z₁₃, z₂₃] using
      (hcard.trans (Nat.mul_le_mul_right
        (β₁₂.natAbs.primeFactors.card + β₁₃.natAbs.primeFactors.card +
          (β₁₃ - β₁₂).natAbs.primeFactors.card) hdeg)))
  · simpa [S, z₁₂, z₁₃, z₂₃] using hrank

/-- The finite-prime coordinates in the quantitative common `S`-unit
equation are not merely supported on the three rational right-hand sides:
their absolute values are bounded by the two relevant principal-ideal
multiplicities.  This is the specialized replacement for any finite-place
linear-forms estimate in the Pell reduction. -/
theorem simultaneousPell_quantitative_common_finite_coordinate_bounds
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) (hdeg : Module.finrank ℚ K ≤ 8) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K),
      S = pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
          (Int.cast_ne_zero.mpr hβ₂₃)) ∧
      S.Finite ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      (∀ v : S,
        Int.natAbs (SupportedUnits.valuationMap S K U v).toAdd ≤
          multiplicity v.1.asIdeal
              (Ideal.span ({(β₁₂ : NumberField.RingOfIntegers K)} :
                Set (NumberField.RingOfIntegers K))) +
            multiplicity v.1.asIdeal
              (Ideal.span ({(β₁₃ : NumberField.RingOfIntegers K)} :
                Set (NumberField.RingOfIntegers K)))) ∧
      (∀ v : S,
        Int.natAbs (SupportedUnits.valuationMap S K V v).toAdd ≤
          multiplicity v.1.asIdeal
              (Ideal.span ({((β₁₃ - β₁₂ : ℤ) :
                NumberField.RingOfIntegers K)} :
                Set (NumberField.RingOfIntegers K))) +
            multiplicity v.1.asIdeal
              (Ideal.span ({(β₁₃ : NumberField.RingOfIntegers K)} :
                Set (NumberField.RingOfIntegers K)))) := by
  obtain ⟨S, U, V, hSdef, hS, _hcard, _hrank, hUV, hU, hV⟩ :=
    simultaneousPell_quantitative_common_supported_unit_equation
      hs₁ hs₂ hs₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg
  rcases simultaneousPell_supported_factor_pairs hs₁ hs₂ hs₃ hPell
      hβ₁₂ hβ₁₃ hβ₂₃ with
    ⟨⟨hm₁₂, hp₁₂, hiM₁₂, hiP₁₂, hprod₁₂, _huM₁₂, _huP₁₂⟩,
      ⟨hm₁₃, hp₁₃, hiM₁₃, hiP₁₃, hprod₁₃, _huM₁₃, _huP₁₃⟩,
      ⟨hm₂₃, hp₂₃, hiM₂₃, hiP₂₃, hprod₂₃, _huM₂₃, _huP₂₃⟩⟩
  let m₁₂ : NumberField.RingOfIntegers K :=
    ⟨pellValueMinus s₁ s₂ x₁ x₂, hiM₁₂⟩
  let p₁₂ : NumberField.RingOfIntegers K :=
    ⟨pellValuePlus s₁ s₂ x₁ x₂, hiP₁₂⟩
  let m₁₃ : NumberField.RingOfIntegers K :=
    ⟨pellValueMinus s₁ s₃ x₁ x₃, hiM₁₃⟩
  let p₁₃ : NumberField.RingOfIntegers K :=
    ⟨pellValuePlus s₁ s₃ x₁ x₃, hiP₁₃⟩
  let m₂₃ : NumberField.RingOfIntegers K :=
    ⟨pellValueMinus s₂ s₃ x₂ x₃, hiM₂₃⟩
  let p₂₃ : NumberField.RingOfIntegers K :=
    ⟨pellValuePlus s₂ s₃ x₂ x₃, hiP₂₃⟩
  have hprod₁₂' : m₁₂ * p₁₂ =
      (β₁₂ : NumberField.RingOfIntegers K) := by
    ext
    exact hprod₁₂
  have hprod₁₃' : m₁₃ * p₁₃ =
      (β₁₃ : NumberField.RingOfIntegers K) := by
    ext
    exact hprod₁₃
  have hprod₂₃' : m₂₃ * p₂₃ =
      ((β₁₃ - β₁₂ : ℤ) : NumberField.RingOfIntegers K) := by
    ext
    change pellValueMinus s₂ s₃ x₂ x₃ *
      pellValuePlus s₂ s₃ x₂ x₃ = ((β₁₃ - β₁₂ : ℤ) : K)
    exact hprod₂₃
  refine ⟨S, U, V, hSdef, hS, hUV, hU, hV, ?_, ?_⟩
  · intro v
    exact SupportedUnits.natAbs_valuationMap_toAdd_factor_ratio_le
      U v m₁₂ p₁₂ m₁₃ p₁₃ hm₁₂ hm₁₃
      β₁₂ β₁₃ hβ₁₂ hβ₁₃ hprod₁₂' hprod₁₃'
      (by
        change (((U : Kˣ) : K)) =
          pellValueMinus s₁ s₂ x₁ x₂ /
            pellValueMinus s₁ s₃ x₁ x₃
        exact hU)
  · intro v
    exact SupportedUnits.natAbs_valuationMap_toAdd_factor_ratio_le
      V v m₂₃ p₂₃ m₁₃ p₁₃ hm₂₃ hm₁₃
      (β₁₃ - β₁₂) β₁₃ hβ₂₃ hβ₁₃ hprod₂₃' hprod₁₃'
      (by
        change (((V : Kˣ) : K)) =
          pellValueMinus s₂ s₃ x₂ x₃ /
            pellValueMinus s₁ s₃ x₁ x₃
        exact hV)

/-- If the three rational right-hand sides have absolute value at most
`J`, every finite-prime coordinate of both common Pell `S`-units has
`2^|e_v| ≤ J^16`. -/
theorem simultaneousPell_quantitative_common_finite_coordinate_pow_le
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) (hdeg : Module.finrank ℚ K ≤ 8)
    (J : ℕ) (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K),
      S = pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
          (Int.cast_ne_zero.mpr hβ₂₃)) ∧
      S.Finite ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      (∀ v : S,
        2 ^ Int.natAbs (SupportedUnits.valuationMap S K U v).toAdd ≤ J ^ 16) ∧
      (∀ v : S,
        2 ^ Int.natAbs (SupportedUnits.valuationMap S K V v).toAdd ≤ J ^ 16) := by
  obtain ⟨S, U, V, hSdef, hS, hUV, hU, hV, hcoordU, hcoordV⟩ :=
    simultaneousPell_quantitative_common_finite_coordinate_bounds
      hs₁ hs₂ hs₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg
  refine ⟨S, U, V, hSdef, hS, hUV, hU, hV, ?_, ?_⟩
  · intro v
    exact SupportedUnits.two_pow_le_sixteen_of_le_multiplicity_sum
      (hcoordU v)
      (SupportedUnits.two_pow_multiplicity_span_intCast_le
        hdeg v.1 β₁₂ hβ₁₂ J hJ₁₂)
      (SupportedUnits.two_pow_multiplicity_span_intCast_le
        hdeg v.1 β₁₃ hβ₁₃ J hJ₁₃)
  · intro v
    exact SupportedUnits.two_pow_le_sixteen_of_le_multiplicity_sum
      (hcoordV v)
      (SupportedUnits.two_pow_multiplicity_span_intCast_le
        hdeg v.1 (β₁₃ - β₁₂) hβ₂₃ J hJ₂₃)
      (SupportedUnits.two_pow_multiplicity_span_intCast_le
        hdeg v.1 β₁₃ hβ₁₃ J hJ₁₃)

/-- The finite-coordinate and prime-norm bounds depend only on the common
support and on the value of the left Pell quotient.  Hence they may be
transported to any independently constructed supported unit with those
same two defining properties. -/
theorem simultaneousPell_common_left_coordinate_pow_le_of_eq
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) (hdeg : Module.finrank ℚ K ≤ 8)
    (J : ℕ) (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (U : S.unit K)
    (hSdef : S = pellCommonPrimeSupport
      (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
      (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
      (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
        (Int.cast_ne_zero.mpr hβ₂₃)))
    (hU : ((U : Kˣ) : K) =
      pellValueMinus s₁ s₂ x₁ x₂ /
        pellValueMinus s₁ s₃ x₁ x₃) :
    (∀ v : S,
      2 ^ Int.natAbs (SupportedUnits.valuationMap S K U v).toAdd ≤ J ^ 16) ∧
    ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8 := by
  subst S
  obtain ⟨S', U', V', hSdef', _hS', _hUV', hU', _hV',
      hcoordU', _hcoordV'⟩ :=
    simultaneousPell_quantitative_common_finite_coordinate_pow_le
      hs₁ hs₂ hs₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg J hJ₁₂ hJ₁₃ hJ₂₃
  subst S'
  have hUU : U' = U := by
    apply Subtype.ext
    apply Units.ext
    exact hU'.trans hU.symm
  subst U'
  refine ⟨hcoordU', ?_⟩
  intro v
  apply pellCommonPrimeSupport_absNorm_le_eight
    β₁₂ β₁₃ (β₁₃ - β₁₂)
    hβ₁₂ hβ₁₃ hβ₂₃ hJ₁₂ hJ₁₃ hJ₂₃ hdeg
  exact v.2

/-- The common supported-unit equation can be placed in one finite
integer-exponent coordinate system. -/
theorem simultaneousPell_common_exponent_equation
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K),
      S.Finite ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ∃ (T : Finset (S.unit K)) (eU eV : T → ℤ),
        U = ∏ g : T, (g.1 : S.unit K) ^ eU g ∧
        V = ∏ g : T, (g.1 : S.unit K) ^ eV g := by
  obtain ⟨S, U, V, hS, hUV, hU, hV⟩ :=
    simultaneousPell_common_supported_unit_equation hs₁ hs₂ hs₃ hPell
      hβ₁₂ hβ₁₃ hβ₂₃
  obtain ⟨T, eU, eV, hUexp, hVexp⟩ :=
    supportedUnit_two_exponent_representation hS U V
  exact ⟨S, U, V, hS, hUV, hU, hV, T, eU, eV, hUexp, hVexp⟩

/-- The full quantitative reduction to a common exponent-coordinate
system.  In addition to `U + V = 1`, it records the degree-eight bounds
for the common prime support and the free rank of its supported-unit
group. -/
theorem simultaneousPell_quantitative_common_exponent_equation
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) (hdeg : Module.finrank ℚ K ≤ 8) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K),
      S.Finite ∧
      Nat.card S ≤ 8 *
        (β₁₂.natAbs.primeFactors.card +
          β₁₃.natAbs.primeFactors.card +
            (β₁₃ - β₁₂).natAbs.primeFactors.card) ∧
      Module.finrank ℤ (Additive (S.unit K)) ≤ 7 + 8 *
        (β₁₂.natAbs.primeFactors.card +
          β₁₃.natAbs.primeFactors.card +
            (β₁₃ - β₁₂).natAbs.primeFactors.card) ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ∃ (T : Finset (S.unit K)) (eU eV : T → ℤ),
        U = ∏ g : T, (g.1 : S.unit K) ^ eU g ∧
        V = ∏ g : T, (g.1 : S.unit K) ^ eV g := by
  obtain ⟨S, U, V, _hSdef, hS, hcard, hrank, hUV, hU, hV⟩ :=
    simultaneousPell_quantitative_common_supported_unit_equation
      hs₁ hs₂ hs₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg
  obtain ⟨T, eU, eV, hUexp, hVexp⟩ :=
    supportedUnit_two_exponent_representation hS U V
  exact ⟨S, U, V, hS, hcard, hrank, hUV, hU, hV,
    T, eU, eV, hUexp, hVexp⟩

/-- The quantitative Pell reduction using the explicit prime-class and
Dirichlet coordinate families.  Both sides of `U + V = 1`, after the
same class-number power, have ambient-field product expansions whose
non-torsion index set has the controlled size `|S| + rank K`. -/
theorem simultaneousPell_quantitative_common_explicit_product
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) (hdeg : Module.finrank ℚ K ≤ 8) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K) (hS : S.Finite),
      Nat.card S ≤ 8 *
        (β₁₂.natAbs.primeFactors.card +
          β₁₃.natAbs.primeFactors.card +
            (β₁₃ - β₁₂).natAbs.primeFactors.card) ∧
      Module.finrank ℤ (Additive (S.unit K)) ≤ 7 + 8 *
        (β₁₂.natAbs.primeFactors.card +
          β₁₃.natAbs.primeFactors.card +
            (β₁₃ - β₁₂).natAbs.primeFactors.card) ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      (letI : Fintype S := hS.fintype
       ∃ (eU eV : S → ℤ)
          (ζU ζV : NumberField.Units.torsion K)
          (fU fV : Fin (NumberField.Units.rank K) → ℤ),
        (U : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S eU : Kˣ) *
            Units.map (algebraMap
              (NumberField.RingOfIntegers K) K).toMonoidHom ζU.1 *
              ∏ i, (Units.map (algebraMap
                (NumberField.RingOfIntegers K) K).toMonoidHom
                  (NumberField.Units.fundSystem K i)) ^ fU i ∧
        (V : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S eV : Kˣ) *
            Units.map (algebraMap
              (NumberField.RingOfIntegers K) K).toMonoidHom ζV.1 *
              ∏ i, (Units.map (algebraMap
                (NumberField.RingOfIntegers K) K).toMonoidHom
                  (NumberField.Units.fundSystem K i)) ^ fV i ∧
        (∀ v, eU v = -(SupportedUnits.valuationMap S K U v).toAdd) ∧
        (∀ v, eV v = -(SupportedUnits.valuationMap S K V v).toAdd) ∧
        Fintype.card S + NumberField.Units.rank K ≤
          Fintype.card S + 7) := by
  obtain ⟨S, U, V, _hSdef, hS, hcard, hrank, hUV, _hU, _hV⟩ :=
    simultaneousPell_quantitative_common_supported_unit_equation
      hs₁ hs₂ hs₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg
  refine ⟨S, U, V, hS, hcard, hrank, hUV, ?_⟩
  let : Fintype S := hS.fintype
  obtain ⟨eU, ζU, fU, hUprod, heU⟩ :=
    numberField_supportedUnit_classNumber_explicit_product S U
  obtain ⟨eV, ζV, fV, hVprod, heV⟩ :=
    numberField_supportedUnit_classNumber_explicit_product S V
  exact ⟨eU, eV, ζU, ζV, fU, fV, hUprod, hVprod, heU, heV,
    numberField_supportedUnit_coordinate_count_le S hdeg⟩

/-- The explicit class-number/Dirichlet decomposition together with the
specialized finite-coordinate bound.  Thus only the ordinary-unit
coordinates remain to be controlled by an archimedean estimate. -/
theorem simultaneousPell_quantitative_common_bounded_explicit_product
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) (hdeg : Module.finrank ℚ K ≤ 8)
    (J : ℕ) (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K) (hS : S.Finite),
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ x₁ x₂ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ x₂ x₃ /
          pellValueMinus s₁ s₃ x₁ x₃ ∧
      (letI : Fintype S := hS.fintype
       ∃ (eU eV : S → ℤ)
          (ζU ζV : NumberField.Units.torsion K)
          (fU fV : Fin (NumberField.Units.rank K) → ℤ),
        (U : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S eU : Kˣ) *
            Units.map (algebraMap
              (NumberField.RingOfIntegers K) K).toMonoidHom ζU.1 *
              ∏ i, (Units.map (algebraMap
                (NumberField.RingOfIntegers K) K).toMonoidHom
                  (NumberField.Units.fundSystem K i)) ^ fU i ∧
        (V : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S eV : Kˣ) *
            Units.map (algebraMap
              (NumberField.RingOfIntegers K) K).toMonoidHom ζV.1 *
              ∏ i, (Units.map (algebraMap
                (NumberField.RingOfIntegers K) K).toMonoidHom
                  (NumberField.Units.fundSystem K i)) ^ fV i ∧
        (∀ v, 2 ^ Int.natAbs (eU v) ≤ J ^ 16) ∧
        (∀ v, 2 ^ Int.natAbs (eV v) ≤ J ^ 16) ∧
        Fintype.card S + NumberField.Units.rank K ≤
          Fintype.card S + 7) := by
  obtain ⟨S, U, V, _hSdef, hS, hUV, hU, hV, hcoordU, hcoordV⟩ :=
    simultaneousPell_quantitative_common_finite_coordinate_pow_le
      hs₁ hs₂ hs₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg J hJ₁₂ hJ₁₃ hJ₂₃
  refine ⟨S, U, V, hS, hUV, hU, hV, ?_⟩
  let : Fintype S := hS.fintype
  obtain ⟨eU, ζU, fU, hUprod, heU⟩ :=
    numberField_supportedUnit_classNumber_explicit_product S U
  obtain ⟨eV, ζV, fV, hVprod, heV⟩ :=
    numberField_supportedUnit_classNumber_explicit_product S V
  refine ⟨eU, eV, ζU, ζV, fU, fV, hUprod, hVprod, ?_, ?_,
    numberField_supportedUnit_coordinate_count_le S hdeg⟩
  · intro v
    simpa [heU v] using hcoordU v
  · intro v
    simpa [heV v] using hcoordV v

/-- Logarithmic height is subadditive on a finite product of integer
powers, with the absolute exponent as coefficient. -/
lemma numberField_logHeight_zpow_prod_le
    (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] (g : ι → K) (e : ι → ℤ) :
    Height.logHeight₁ (∏ i, g i ^ e i) ≤
      ∑ i, (e i).natAbs * Height.logHeight₁ (g i) := by
  calc
    Height.logHeight₁ (∏ i, g i ^ e i) ≤
        ∑ i, Height.logHeight₁ (g i ^ e i) := by
      simpa using Height.logHeight₁_prod_le (K := K) Finset.univ
        (fun i ↦ g i ^ e i)
    _ = ∑ i, (e i).natAbs * Height.logHeight₁ (g i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Height.logHeight₁_zpow (g i) (e i)

/-- The height of the residual ordinary unit in the class-number
decomposition is bounded by the class-number multiple of the original
supported-unit height plus the finite-prime generator contribution. -/
lemma numberField_residualOrdinaryUnit_logHeight_le
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
        (q : Kˣ)) :
    Height.logHeight₁
        ((((SupportedUnits.emptyEquivUnits K q) :
          NumberField.RingOfIntegers K) : K)) ≤
      (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) +
        ∑ v, (e v).natAbs * Height.logHeight₁
          ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) := by
  let g : Kˣ :=
    SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  have hqUnits : (q : Kˣ) = g⁻¹ * (u : Kˣ) ^ NumberField.classNumber K := by
    rw [hpow]
    simp [g]
  have hmap :
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (SupportedUnits.emptyEquivUnits K q) = (q : Kˣ) :=
    SupportedUnits.unitsMap_emptyEquivUnits
      (R := NumberField.RingOfIntegers K) K q
  have hqK := congrArg (fun z : Kˣ ↦ (z : K)) hqUnits
  have hmapK' :
      (((SupportedUnits.emptyEquivUnits K q) :
        NumberField.RingOfIntegers K) : K) = (((q : Kˣ) : K)) := by
    change algebraMap (NumberField.RingOfIntegers K) K
      (((SupportedUnits.emptyEquivUnits K q) :
        (NumberField.RingOfIntegers K)ˣ) : NumberField.RingOfIntegers K) =
          (((q : Kˣ) : K))
    exact congrArg Units.val hmap
  have hqValue :
      (((SupportedUnits.emptyEquivUnits K q) :
        NumberField.RingOfIntegers K) : K) =
        (g : K)⁻¹ * (((u : Kˣ) : K)) ^ NumberField.classNumber K := by
    rw [hmapK']
    simpa using hqK
  rw [hqValue]
  calc
    Height.logHeight₁
        ((g : K)⁻¹ * (((u : Kˣ) : K)) ^ NumberField.classNumber K) ≤
      Height.logHeight₁ ((g : K)⁻¹) +
        Height.logHeight₁
          ((((u : Kˣ) : K)) ^ NumberField.classNumber K) :=
      Height.logHeight₁_mul_le _ _
    _ = Height.logHeight₁ (g : K) +
        (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) := by
      rw [Height.logHeight₁_inv, Height.logHeight₁_pow]
    _ ≤ (∑ v, (e v).natAbs * Height.logHeight₁
          ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))) +
        (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) := by
      gcongr
      simpa [g, SupportedUnits.numberFieldPrimeClassSupportedUnitProduct]
        using numberField_logHeight_zpow_prod_le K
          (fun v : S ↦
            (((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) e
    _ = (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) +
        ∑ v, (e v).natAbs * Height.logHeight₁
          ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) := by
      ring

/-- All ordinary-unit exponents in the class-number decomposition are
bounded by an explicit linear expression in the supported unit's height
and the finite-prime generator heights. -/
theorem numberField_supportedUnit_classNumber_fundSystem_total_exponent_bound
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (u : S.unit K) :
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K)
        (ζ : NumberField.Units.torsion K)
        (f : Fin (NumberField.Units.rank K) → ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
            (q : Kˣ) ∧
        SupportedUnits.emptyEquivUnits K q =
          ζ.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ f i ∧
        (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
        ∀ i,
          |(f i : ℝ)| ≤
            2 * numberFieldFundamentalUnitCoordinateNorm K *
              ((NumberField.classNumber K : ℝ) *
                  Height.logHeight₁ (((u : Kˣ) : K)) +
                ∑ v, (e v).natAbs * Height.logHeight₁
                  ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))) := by
  obtain ⟨e, q, ζ, f, hpow, hq, he, hf⟩ :=
    numberField_supportedUnit_classNumber_fundSystem_decomposition_with_exponent_bound S u
  refine ⟨e, q, ζ, f, hpow, hq, he, ?_⟩
  intro i
  have hres := numberField_residualOrdinaryUnit_logHeight_le S u e q hpow
  have hfactor : 0 ≤ 2 * numberFieldFundamentalUnitCoordinateNorm K :=
    mul_nonneg (by norm_num) (numberFieldFundamentalUnitCoordinateNorm_nonneg K)
  exact (hf i).trans (mul_le_mul_of_nonneg_left hres hfactor)

/-- Every natural number is at most the corresponding power of two.  This
elementary conversion lets the multiplicative finite-coordinate estimate
`2^|e_v| ≤ B` serve directly as an additive exponent estimate. -/
lemma nat_le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by omega)
      omega

lemma natAbs_le_of_two_pow_le {e : ℤ} {B : ℕ}
    (h : 2 ^ e.natAbs ≤ B) : e.natAbs ≤ B :=
  (nat_le_two_pow_self e.natAbs).trans h

/-- Summing bounded integer coordinates costs only the cardinality of the
coordinate set. -/
lemma sum_natAbs_cast_le_card_mul
    {ι : Type*} [Fintype ι] (e : ι → ℤ) {B : ℕ}
    (h : ∀ i, 2 ^ (e i).natAbs ≤ B) :
    ∑ i, (((e i).natAbs : ℕ) : ℝ) ≤
      (Fintype.card ι : ℝ) * B := by
  calc
    ∑ i, (((e i).natAbs : ℕ) : ℝ) ≤ ∑ _i : ι, (B : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact_mod_cast natAbs_le_of_two_pow_le (h i)
    _ = (Fintype.card ι : ℝ) * B := by simp

lemma numberFieldFundamentalUnitLogMass_nonneg
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ numberFieldFundamentalUnitLogMass K := by
  unfold numberFieldFundamentalUnitLogMass
  positivity

/-- If every finite coordinate satisfies `2^|e_v| ≤ J^16` and every
prime in the support has norm at most `J^8`, then the entire finite-prime
part of the residual-unit height has one explicit uniform bound. -/
theorem numberField_finite_generator_sum_le_of_pow_coordinate
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (e : S → ℤ) {J : ℕ} (hJ : 1 ≤ J)
    (hcoord : ∀ v, 2 ^ (e v).natAbs ≤ J ^ 16)
    (hSJ : ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8) :
    ∑ v, (e v).natAbs * Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) ≤
      ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        (2 * numberFieldFundamentalUnitLogMass K +
          ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
            ((NumberField.classNumber K : ℝ) *
              (8 * Real.log (J : ℝ)))) := by
  let C : ℝ := 2 * numberFieldFundamentalUnitLogMass K +
    ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
      ((NumberField.classNumber K : ℝ) * (8 * Real.log (J : ℝ)))
  have hlogJ : 0 ≤ Real.log (J : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hJ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (mul_nonneg (by norm_num)
        (numberFieldFundamentalUnitLogMass_nonneg K))
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (by norm_num) hlogJ)))
  calc
    ∑ v, (e v).natAbs * Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) ≤
      ∑ v, ((e v).natAbs : ℝ) * C := by
        apply Finset.sum_le_sum
        intro v _hv
        exact mul_le_mul_of_nonneg_left
          (numberFieldPrimeClassSupportedUnit_logHeight_le_of_absNorm_le_eight
            S v (hSJ v)) (by positivity)
    _ ≤ ∑ _v : S, (J ^ 16 : ℝ) * C := by
        apply Finset.sum_le_sum
        intro v _hv
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast natAbs_le_of_two_pow_le (hcoord v)) hC
    _ = ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) * C := by
        simp
        ring
    _ = _ := rfl

/-- The same finite-coordinate estimate applied to the complete
prime-class product occurring in the supported-unit decomposition. -/
theorem numberField_primeClassProduct_logHeight_le_of_pow_coordinate
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (e : S → ℤ) {J : ℕ} (hJ : 1 ≤ J)
    (hcoord : ∀ v, 2 ^ (e v).natAbs ≤ J ^ 16)
    (hSJ : ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8) :
    Height.logHeight₁
        (((SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) : K)) ≤
      ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        (2 * numberFieldFundamentalUnitLogMass K +
          ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
            ((NumberField.classNumber K : ℝ) *
              (8 * Real.log (J : ℝ)))) := by
  let p : S → K := fun v ↦
    (((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)
  have hprod := numberField_logHeight_zpow_prod_le K p e
  have hsum := numberField_finite_generator_sum_le_of_pow_coordinate
    S e hJ hcoord hSJ
  have hprod' : Height.logHeight₁
        (((SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) : K)) ≤
      ∑ v, (e v).natAbs * Height.logHeight₁ (p v) := by
    simpa [SupportedUnits.numberFieldPrimeClassSupportedUnitProduct, p]
      using hprod
  exact hprod'.trans hsum

/-- The preceding finite-coordinate estimate inserted into the exact
class-number/Dirichlet decomposition.  Only the supported unit's own
height and field invariants remain on the right-hand side. -/
theorem numberField_supportedUnit_total_exponent_bound_of_pow_coordinate
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) {J : ℕ} (hJ : 1 ≤ J)
    (hcoord : ∀ v,
      2 ^ Int.natAbs (SupportedUnits.valuationMap S K u v).toAdd ≤ J ^ 16)
    (hSJ : ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8) :
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K)
        (ζ : NumberField.Units.torsion K)
        (f : Fin (NumberField.Units.rank K) → ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
            (q : Kˣ) ∧
        SupportedUnits.emptyEquivUnits K q =
          ζ.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ f i ∧
        (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
        ∀ i,
          |(f i : ℝ)| ≤
            2 * numberFieldFundamentalUnitCoordinateNorm K *
              ((NumberField.classNumber K : ℝ) *
                  Height.logHeight₁ (((u : Kˣ) : K)) +
                ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
                  (2 * numberFieldFundamentalUnitLogMass K +
                    ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
                      ((NumberField.classNumber K : ℝ) *
                        (8 * Real.log (J : ℝ))))) := by
  obtain ⟨e, q, ζ, f, hpow, hq, he, hf⟩ :=
    numberField_supportedUnit_classNumber_fundSystem_total_exponent_bound S u
  refine ⟨e, q, ζ, f, hpow, hq, he, ?_⟩
  have hcoordE : ∀ v, 2 ^ (e v).natAbs ≤ J ^ 16 := by
    intro v
    simpa [he v] using hcoord v
  have hfinite := numberField_finite_generator_sum_le_of_pow_coordinate
    S e hJ hcoordE hSJ
  have hfactor : 0 ≤ 2 * numberFieldFundamentalUnitCoordinateNorm K :=
    mul_nonneg (by norm_num) (numberFieldFundamentalUnitCoordinateNorm_nonneg K)
  intro i
  exact (hf i).trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) hfinite) hfactor)

/-- The common numerical majorant for ordinary-unit coordinates once the
height of the supported unit itself is bounded by `B`. -/
noncomputable def supportedUnitDirichletExponentMajorant
    (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (J : ℕ) (B : ℝ) : ℝ :=
  2 * numberFieldFundamentalUnitCoordinateNorm K *
    ((NumberField.classNumber K : ℝ) * B +
      ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        (2 * numberFieldFundamentalUnitLogMass K +
          ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
            ((NumberField.classNumber K : ℝ) *
              (8 * Real.log (J : ℝ)))))

/-- Exact class-number/Dirichlet coordinates together with a uniform bound
for every ordinary-unit exponent. -/
def SupportedUnitBoundedDirichletDecomposition
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (J : ℕ) (B : ℝ) : Prop :=
  ∃ (e : S → ℤ)
      (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K)
      (ζ : NumberField.Units.torsion K)
      (f : Fin (NumberField.Units.rank K) → ℤ),
    (u : Kˣ) ^ NumberField.classNumber K =
        (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
          (q : Kˣ) ∧
      SupportedUnits.emptyEquivUnits K q =
        ζ.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ f i ∧
      (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
      ∀ i, |(f i : ℝ)| ≤
        supportedUnitDirichletExponentMajorant K S J B

/-- A height bound for the supported unit turns the quantitative exact
decomposition into a uniform bound for all ordinary-unit coordinates. -/
theorem supportedUnitBoundedDirichletDecomposition_of_height_le
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) {J : ℕ} {B : ℝ} (hJ : 1 ≤ J)
    (hcoord : ∀ v,
      2 ^ Int.natAbs (SupportedUnits.valuationMap S K u v).toAdd ≤ J ^ 16)
    (hSJ : ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8)
    (hheight : Height.logHeight₁ (((u : Kˣ) : K)) ≤ B) :
    SupportedUnitBoundedDirichletDecomposition S u J B := by
  obtain ⟨e, q, ζ, f, hpow, hq, he, hf⟩ :=
    numberField_supportedUnit_total_exponent_bound_of_pow_coordinate
      S u hJ hcoord hSJ
  refine ⟨e, q, ζ, f, hpow, hq, he, ?_⟩
  have hclass : 0 ≤ (NumberField.classNumber K : ℝ) := Nat.cast_nonneg _
  have hinside :
      (NumberField.classNumber K : ℝ) *
            Height.logHeight₁ (((u : Kˣ) : K)) +
          ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
            (2 * numberFieldFundamentalUnitLogMass K +
              ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
                ((NumberField.classNumber K : ℝ) *
                  (8 * Real.log (J : ℝ)))) ≤
        (NumberField.classNumber K : ℝ) * B +
          ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
            (2 * numberFieldFundamentalUnitLogMass K +
              ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
                ((NumberField.classNumber K : ℝ) *
                  (8 * Real.log (J : ℝ)))) :=
    add_le_add (mul_le_mul_of_nonneg_left hheight hclass) (le_refl _)
  have hfactor : 0 ≤ 2 * numberFieldFundamentalUnitCoordinateNorm K :=
    mul_nonneg (by norm_num) (numberFieldFundamentalUnitCoordinateNorm_nonneg K)
  intro i
  exact (hf i).trans (by
    unfold supportedUnitDirichletExponentMajorant
    exact mul_le_mul_of_nonneg_left hinside hfactor)

/-- Logarithmic height is subadditive on a product of three factors. -/
lemma numberField_logHeight_mul_mul_le
    (K : Type*) [Field K] [NumberField K] (a b c : K) :
    Height.logHeight₁ (a * b * c) ≤
      Height.logHeight₁ a + Height.logHeight₁ b + Height.logHeight₁ c := by
  calc
    Height.logHeight₁ (a * b * c) ≤
        Height.logHeight₁ (a * b) + Height.logHeight₁ c :=
      Height.logHeight₁_mul_le _ _
    _ ≤ (Height.logHeight₁ a + Height.logHeight₁ b) +
        Height.logHeight₁ c := by
      exact add_le_add (Height.logHeight₁_mul_le a b) (le_refl _)

/-- The explicit class-number coordinates give a matching logarithmic
height inequality.  The torsion factor disappears, leaving only the
finite-prime generators and the Dirichlet fundamental units. -/
theorem numberField_supportedUnit_classNumber_logHeight_le
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (u : S.unit K) :
    ∃ (e : S → ℤ) (f : Fin (NumberField.Units.rank K) → ℤ),
      (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) ≤
        ∑ v, (e v).natAbs * Height.logHeight₁
          ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) +
        ∑ i, (f i).natAbs * Height.logHeight₁
          (((NumberField.Units.fundSystem K i :
            NumberField.RingOfIntegers K) : K)) := by
  obtain ⟨e, ζ, f, hprod, _he⟩ :=
    numberField_supportedUnit_classNumber_explicit_product S u
  let p : S → K := fun v ↦
    (((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)
  let z : K := ((ζ.1 : NumberField.RingOfIntegers K) : K)
  let ε : Fin (NumberField.Units.rank K) → K := fun i ↦
    ((NumberField.Units.fundSystem K i :
      NumberField.RingOfIntegers K) : K)
  have hprodK :
      (((u : Kˣ) : K)) ^ NumberField.classNumber K =
        (∏ v, p v ^ e v) * z * ∏ i, ε i ^ f i := by
    have h := congrArg (fun w : Kˣ ↦ (w : K)) hprod
    simpa [p, z, ε,
      SupportedUnits.numberFieldPrimeClassSupportedUnitProduct] using h
  have hp := numberField_logHeight_zpow_prod_le K p e
  have hε := numberField_logHeight_zpow_prod_le K ε f
  have hz : Height.logHeight₁ z = 0 := by
    simpa only [z] using numberField_logHeight_torsionUnit_eq_zero ζ
  have hsplit : Height.logHeight₁
        ((∏ v, p v ^ e v) * z * ∏ i, ε i ^ f i) ≤
      Height.logHeight₁ (∏ v, p v ^ e v) +
        Height.logHeight₁ z + Height.logHeight₁ (∏ i, ε i ^ f i) := by
    exact numberField_logHeight_mul_mul_le K _ _ _
  refine ⟨e, f, ?_⟩
  calc
    (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) =
        Height.logHeight₁
          ((((u : Kˣ) : K)) ^ NumberField.classNumber K) := by
      rw [Height.logHeight₁_pow]
    _ = Height.logHeight₁
          ((∏ v, p v ^ e v) * z * ∏ i, ε i ^ f i) := by rw [hprodK]
    _ ≤ Height.logHeight₁ (∏ v, p v ^ e v) +
          Height.logHeight₁ z + Height.logHeight₁ (∏ i, ε i ^ f i) := by
      exact hsplit
    _ ≤ (∑ v, (e v).natAbs * Height.logHeight₁ (p v)) +
          0 + ∑ i, (f i).natAbs * Height.logHeight₁ (ε i) := by
      exact add_le_add (add_le_add hp hz.le) hε
    _ = ∑ v, (e v).natAbs * Height.logHeight₁
          ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) +
        ∑ i, (f i).natAbs * Height.logHeight₁
          (((NumberField.Units.fundSystem K i :
            NumberField.RingOfIntegers K) : K)) := by simp [p, ε]

/-- Uniformly bounding the norms of the finite primes turns the entire
finite-prime part of an `S`-unit height estimate into the `ℓ¹` mass of its
valuation exponents times one common majorant. -/
theorem numberField_supportedUnit_classNumber_logHeight_le_of_absNorm_le_eight
    {K : Type*} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (u : S.unit K)
    {J : ℕ} (hSJ : ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8) :
    ∃ (e : S → ℤ) (f : Fin (NumberField.Units.rank K) → ℤ),
      (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) ≤
        (∑ v, ((e v).natAbs : ℝ)) *
          (2 * numberFieldFundamentalUnitLogMass K +
            ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
              ((NumberField.classNumber K : ℝ) *
                (8 * Real.log (J : ℝ)))) +
        ∑ i, (f i).natAbs * Height.logHeight₁
          (((NumberField.Units.fundSystem K i :
            NumberField.RingOfIntegers K) : K)) := by
  obtain ⟨e, f, hheight⟩ :=
    numberField_supportedUnit_classNumber_logHeight_le S u
  refine ⟨e, f, hheight.trans ?_⟩
  have hfinite :
    ∑ v, (e v).natAbs * Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) ≤
      (∑ v, ((e v).natAbs : ℝ)) *
        (2 * numberFieldFundamentalUnitLogMass K +
          ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
            ((NumberField.classNumber K : ℝ) *
              (8 * Real.log (J : ℝ)))) := by
    calc
      ∑ v, (e v).natAbs * Height.logHeight₁
          ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K)) ≤
        ∑ v, (e v).natAbs *
          (2 * numberFieldFundamentalUnitLogMass K +
            ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
              ((NumberField.classNumber K : ℝ) *
                (8 * Real.log (J : ℝ)))) := by
        apply Finset.sum_le_sum
        intro v _hv
        exact mul_le_mul_of_nonneg_left
          (numberFieldPrimeClassSupportedUnit_logHeight_le_of_absNorm_le_eight
            S v (hSJ v)) (by positivity)
      _ = (∑ v, ((e v).natAbs : ℝ)) *
          (2 * numberFieldFundamentalUnitLogMass K +
            ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
              ((NumberField.classNumber K : ℝ) *
                (8 * Real.log (J : ℝ)))) := by
        rw [Finset.sum_mul]
  exact add_le_add hfinite (le_refl _)

/-- Multiplying a controlled square root by a positive integral coordinate
costs at most `8 log x` in a number field of degree at most eight. -/
lemma numberField_logHeight_sqRoot_mul_nat_le
    (K : Type*) [Field K] [NumberField K]
    (s : K) {γ H x : ℕ} (hs : s ^ 2 = (γ : K))
    (hdeg : Module.finrank ℚ K ≤ 8) (hγ : 0 < γ) (hγH : γ ≤ H)
    (hx : 0 < x) :
    Height.logHeight₁ (s * (x : K)) ≤
      4 * Real.log (H : ℝ) + 8 * Real.log (x : ℝ) := by
  have hsHeight := numberField_logHeight_sqRoot_le K s hs hdeg hγ hγH
  have hxlog : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx)
  have hdegR : (Module.finrank ℚ K : ℝ) ≤ 8 := by exact_mod_cast hdeg
  calc
    Height.logHeight₁ (s * (x : K)) ≤
        Height.logHeight₁ s + Height.logHeight₁ (x : K) :=
      Height.logHeight₁_mul_le s (x : K)
    _ = Height.logHeight₁ s +
        (Module.finrank ℚ K : ℝ) * Real.log (x : ℝ) := by
      rw [numberField_logHeight_natCast K x]
    _ ≤ 4 * Real.log (H : ℝ) + 8 * Real.log (x : ℝ) :=
      add_le_add hsHeight (mul_le_mul_of_nonneg_right hdegR hxlog)

/-- The height of either signed Pell factor value is controlled explicitly
by the coefficient height and the two integral coordinates. -/
lemma numberField_logHeight_pellValue_le
    (K : Type*) [Field K] [NumberField K]
    (sₐ s_b : K) {γₐ γ_b H xₐ x_b : ℕ}
    (hsₐ : sₐ ^ 2 = (γₐ : K)) (hs_b : s_b ^ 2 = (γ_b : K))
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hγₐ : 0 < γₐ) (hγ_b : 0 < γ_b)
    (hγₐH : γₐ ≤ H) (hγ_bH : γ_b ≤ H)
    (hxₐ : 0 < xₐ) (hx_b : 0 < x_b) :
    Height.logHeight₁
        (pellValueMinus sₐ s_b (xₐ : ℤ) (x_b : ℤ)) ≤
      8 * Real.log 2 + 8 * Real.log (H : ℝ) +
        8 * (Real.log (xₐ : ℝ) + Real.log (x_b : ℝ)) ∧
    Height.logHeight₁
        (pellValuePlus sₐ s_b (xₐ : ℤ) (x_b : ℤ)) ≤
      8 * Real.log 2 + 8 * Real.log (H : ℝ) +
        8 * (Real.log (xₐ : ℝ) + Real.log (x_b : ℝ)) := by
  have htermₐ := numberField_logHeight_sqRoot_mul_nat_le K sₐ hsₐ hdeg
    hγₐ hγₐH hxₐ
  have hterm_b := numberField_logHeight_sqRoot_mul_nat_le K s_b hs_b hdeg
    hγ_b hγ_bH hx_b
  have hweight : (Height.totalWeight K : ℝ) ≤ 8 := by
    rw [NumberField.totalWeight_eq_finrank]
    exact_mod_cast hdeg
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hconst :
      (Height.totalWeight K : ℝ) * Real.log 2 ≤
        8 * Real.log 2 :=
    mul_le_mul_of_nonneg_right hweight hlog2
  have hminus := Height.logHeight₁_sub_le
    (sₐ * (xₐ : K)) (s_b * (x_b : K))
  have hplus := Height.logHeight₁_add_le
    (sₐ * (xₐ : K)) (s_b * (x_b : K))
  have hfinal (hadd : Height.logHeight₁
      (sₐ * (xₐ : K) - s_b * (x_b : K)) ≤
        (Height.totalWeight K : ℝ) * Real.log 2 +
          Height.logHeight₁ (sₐ * (xₐ : K)) +
          Height.logHeight₁ (s_b * (x_b : K))) :
      Height.logHeight₁ (sₐ * (xₐ : K) - s_b * (x_b : K)) ≤
        8 * Real.log 2 + 8 * Real.log (H : ℝ) +
          8 * (Real.log (xₐ : ℝ) + Real.log (x_b : ℝ)) := by
    calc
      _ ≤ (Height.totalWeight K : ℝ) * Real.log 2 +
          Height.logHeight₁ (sₐ * (xₐ : K)) +
          Height.logHeight₁ (s_b * (x_b : K)) := hadd
      _ ≤ 8 * Real.log 2 +
          (4 * Real.log (H : ℝ) + 8 * Real.log (xₐ : ℝ)) +
          (4 * Real.log (H : ℝ) + 8 * Real.log (x_b : ℝ)) :=
        add_le_add (add_le_add hconst htermₐ) hterm_b
      _ = _ := by ring
  constructor
  · simpa [pellValueMinus] using hfinal hminus
  · have hplusFinal : Height.logHeight₁
        (sₐ * (xₐ : K) + s_b * (x_b : K)) ≤
          8 * Real.log 2 + 8 * Real.log (H : ℝ) +
            8 * (Real.log (xₐ : ℝ) + Real.log (x_b : ℝ)) := by
      calc
        _ ≤ (Height.totalWeight K : ℝ) * Real.log 2 +
            Height.logHeight₁ (sₐ * (xₐ : K)) +
            Height.logHeight₁ (s_b * (x_b : K)) := hplus
        _ ≤ 8 * Real.log 2 +
            (4 * Real.log (H : ℝ) + 8 * Real.log (xₐ : ℝ)) +
            (4 * Real.log (H : ℝ) + 8 * Real.log (x_b : ℝ)) :=
          add_le_add (add_le_add hconst htermₐ) hterm_b
        _ = _ := by ring
    simpa [pellValuePlus] using hplusFinal

/-- Division costs the sum of logarithmic heights, since inversion
preserves height. -/
lemma numberField_logHeight_div_le
    (K : Type*) [Field K] [NumberField K] (a b : K) :
    Height.logHeight₁ (a / b) ≤
      Height.logHeight₁ a + Height.logHeight₁ b := by
  rw [div_eq_mul_inv]
  calc
    Height.logHeight₁ (a * b⁻¹) ≤
        Height.logHeight₁ a + Height.logHeight₁ b⁻¹ :=
      Height.logHeight₁_mul_le a b⁻¹
    _ = Height.logHeight₁ a + Height.logHeight₁ b := by
      rw [Height.logHeight₁_inv]

/-- Both ratios occurring in the common Pell `S`-unit equation have a
single height majorant in the three positive integral coordinates. -/
lemma numberField_logHeight_pellRatios_le
    (K : Type*) [Field K] [NumberField K]
    (s₁ s₂ s₃ : K) {γ₁ γ₂ γ₃ H x₁ x₂ x₃ : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃) :
    Height.logHeight₁
        (pellValueMinus s₁ s₂ (x₁ : ℤ) (x₂ : ℤ) /
          pellValueMinus s₁ s₃ (x₁ : ℤ) (x₃ : ℤ)) ≤
      16 * Real.log 2 + 16 * Real.log (H : ℝ) +
        16 * (Real.log (x₁ : ℝ) + Real.log (x₂ : ℝ) +
          Real.log (x₃ : ℝ)) ∧
    Height.logHeight₁
        (pellValueMinus s₂ s₃ (x₂ : ℤ) (x₃ : ℤ) /
          pellValueMinus s₁ s₃ (x₁ : ℤ) (x₃ : ℤ)) ≤
      16 * Real.log 2 + 16 * Real.log (H : ℝ) +
        16 * (Real.log (x₁ : ℝ) + Real.log (x₂ : ℝ) +
          Real.log (x₃ : ℝ)) := by
  obtain ⟨hm₁₂, _hp₁₂⟩ := numberField_logHeight_pellValue_le
    K s₁ s₂ hs₁ hs₂ hdeg hγ₁ hγ₂ hγ₁H hγ₂H hx₁ hx₂
  obtain ⟨hm₁₃, _hp₁₃⟩ := numberField_logHeight_pellValue_le
    K s₁ s₃ hs₁ hs₃ hdeg hγ₁ hγ₃ hγ₁H hγ₃H hx₁ hx₃
  obtain ⟨hm₂₃, _hp₂₃⟩ := numberField_logHeight_pellValue_le
    K s₂ s₃ hs₂ hs₃ hdeg hγ₂ hγ₃ hγ₂H hγ₃H hx₂ hx₃
  have hlog₁ : 0 ≤ Real.log (x₁ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx₁)
  have hlog₂ : 0 ≤ Real.log (x₂ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx₂)
  have hlog₃ : 0 ≤ Real.log (x₃ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx₃)
  constructor
  · exact (numberField_logHeight_div_le K _ _).trans (by nlinarith)
  · exact (numberField_logHeight_div_le K _ _).trans (by nlinarith)

/-- The quantitative common Pell `S`-unit equation, now with every finite
coordinate and every ordinary Dirichlet coordinate explicitly bounded.
The only field-dependent quantities left are the fixed class number and
the two norms attached to Mathlib's chosen fundamental unit system. -/
theorem simultaneousPell_quantitative_common_all_coordinate_bounds
    {K : Type*} [Field K] [NumberField K]
    {s₁ s₂ s₃ : K} {γ₁ γ₂ γ₃ H x₁ x₂ x₃ : ℕ}
    {β₁₂ β₁₃ : ℤ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hdeg : Module.finrank ℚ K ≤ 8)
    (J : ℕ) (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃) :
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K) (hS : S.Finite),
      S = pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
          (Int.cast_ne_zero.mpr hβ₂₃)) ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus s₁ s₂ (x₁ : ℤ) (x₂ : ℤ) /
          pellValueMinus s₁ s₃ (x₁ : ℤ) (x₃ : ℤ) ∧
      ((V : Kˣ) : K) =
        pellValueMinus s₂ s₃ (x₂ : ℤ) (x₃ : ℤ) /
          pellValueMinus s₁ s₃ (x₁ : ℤ) (x₃ : ℤ) ∧
      (letI : Fintype S := hS.fintype
       let B : ℝ := 16 * Real.log 2 + 16 * Real.log (H : ℝ) +
          16 * (Real.log (x₁ : ℝ) + Real.log (x₂ : ℝ) +
            Real.log (x₃ : ℝ))
       SupportedUnitBoundedDirichletDecomposition S U J B ∧
         SupportedUnitBoundedDirichletDecomposition S V J B) := by
  obtain ⟨S, U, V, hSdef, hS, hUV, hU, hV, hcoordU, hcoordV⟩ :=
    simultaneousPell_quantitative_common_finite_coordinate_pow_le
      (by simpa using hs₁) (by simpa using hs₂) (by simpa using hs₃)
      hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg J hJ₁₂ hJ₁₃ hJ₂₃
  refine ⟨S, U, V, hS, hSdef, hUV, hU, hV, ?_⟩
  let : Fintype S := hS.fintype
  let B : ℝ := 16 * Real.log 2 + 16 * Real.log (H : ℝ) +
    16 * (Real.log (x₁ : ℝ) + Real.log (x₂ : ℝ) +
      Real.log (x₃ : ℝ))
  have hJ : 1 ≤ J := by
    have habs : 0 < β₁₂.natAbs := Int.natAbs_pos.mpr hβ₁₂
    omega
  have hSJ : ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8 := by
    intro v
    apply pellCommonPrimeSupport_absNorm_le_eight
      β₁₂ β₁₃ (β₁₃ - β₁₂)
      hβ₁₂ hβ₁₃ hβ₂₃ hJ₁₂ hJ₁₃ hJ₂₃ hdeg
    simpa [hSdef] using v.2
  have hratios := numberField_logHeight_pellRatios_le K s₁ s₂ s₃
    hs₁ hs₂ hs₃ hdeg hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H hx₁ hx₂ hx₃
  have hheightU : Height.logHeight₁ (((U : Kˣ) : K)) ≤ B := by
    rw [hU]
    exact hratios.1
  have hheightV : Height.logHeight₁ (((V : Kˣ) : K)) ≤ B := by
    rw [hV]
    exact hratios.2
  exact ⟨
    supportedUnitBoundedDirichletDecomposition_of_height_le
      S U hJ hcoordU hSJ hheightU,
    supportedUnitBoundedDirichletDecomposition_of_height_le
      S V hJ hcoordV hSJ hheightV⟩

open Module in
/-- Bounding all conjugates of an integral field basis bounds its
discriminant through the determinant of the embedding matrix. -/
lemma algebra_discr_norm_le_of_embedding_norm_le
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ K) (e : ι ≃ (K →ₐ[ℚ] ℂ)) (M : ℝ)
    (hM : ∀ i j, ‖e j (b i)‖ ≤ M) :
    ‖(algebraMap ℚ ℂ) (Algebra.discr ℚ b)‖ ≤
      (((Fintype.card ι).factorial : ℝ) * M ^ Fintype.card ι) ^ 2 := by
  rw [Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ b e,
    norm_pow]
  have hdet : ‖(Algebra.embeddingsMatrixReindex ℚ ℂ b e).det‖ ≤
      ((Fintype.card ι).factorial : ℝ) * M ^ Fintype.card ι := by
    have h := Matrix.det_le
      (abv := NormedField.toAbsoluteValue ℂ)
      (A := Algebra.embeddingsMatrixReindex ℚ ℂ b e) hM
    change ‖(Algebra.embeddingsMatrixReindex ℚ ℂ b e).det‖ ≤
      (Fintype.card ι).factorial • M ^ Fintype.card ι at h
    simpa only [nsmul_eq_mul] using h
  exact pow_le_pow_left₀ (norm_nonneg _) hdet 2

open Module in
/-- The change-of-basis coefficients from an integral field basis to the
number field's integral basis are rational integers. -/
lemma numberField_integral_basis_coordinate_isIntegral
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ K) (hInt : ∀ i, IsIntegral ℤ (b i)) :
    let b₀ : Basis ι ℚ K :=
      (NumberField.integralBasis K).reindex
        (b.indexEquiv (NumberField.integralBasis K)).symm
    ∀ i j, IsIntegral ℤ (b₀.toMatrix b i j) := by
  dsimp only
  intro i j
  rw [Basis.toMatrix_apply]
  apply IsIntegrallyClosed.isIntegral_iff.mpr
  have hmem : b j ∈ Submodule.span ℤ
      (Set.range ((NumberField.integralBasis K).reindex
        (b.indexEquiv (NumberField.integralBasis K)).symm)) := by
    obtain ⟨y, hy⟩ :=
      (IsIntegralClosure.isIntegral_iff
        (A := NumberField.RingOfIntegers K)).mp (hInt j)
    have h := (NumberField.mem_span_integralBasis K).mpr ⟨y, hy⟩
    simpa using h
  exact (((NumberField.integralBasis K).reindex
    (b.indexEquiv (NumberField.integralBasis K)).symm).mem_span_iff_repr_mem
      ℤ (b j)).mp hmem i

open Module in
/-- The absolute field discriminant divides the discriminant of every
integral `ℚ`-basis; in norm form, its absolute value is no larger. -/
lemma numberField_natAbs_discr_le_integral_basis_discr_norm
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ K) (hInt : ∀ i, IsIntegral ℤ (b i)) :
    (NumberField.discr K).natAbs ≤
      ‖(algebraMap ℚ ℂ) (Algebra.discr ℚ b)‖ := by
  let b₀ : Basis ι ℚ K :=
    (NumberField.integralBasis K).reindex
      (b.indexEquiv (NumberField.integralBasis K)).symm
  let P : Matrix ι ι ℚ := b₀.toMatrix b
  have hdisc : Algebra.discr ℚ b =
      P.det ^ 2 * Algebra.discr ℚ b₀ := by
    dsimp only [P]
    convert Algebra.discr_of_matrix_vecMul b₀ (b₀.toMatrix b) using 1
    rw [Basis.toMatrix_map_vecMul]
  have hb₀disc : Algebra.discr ℚ b₀ = (NumberField.discr K : ℚ) := by
    rw [NumberField.coe_discr]
    dsimp only [b₀]
    rw [Basis.coe_reindex, Algebra.discr_reindex]
  have hPInt : IsIntegral ℤ P.det := by
    exact IsIntegral.det (numberField_integral_basis_coordinate_isIntegral b hInt)
  obtain ⟨k : ℤ, hk⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hPInt
  have hPunit : IsUnit P.det := by
    dsimp only [P]
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b₀]
    exact LinearEquiv.isUnit_det (LinearEquiv.refl ℚ K) b b₀
  have hk0 : k ≠ 0 := by
    intro hkzero
    subst k
    simp at hk
    exact hPunit.ne_zero hk.symm
  have hnormeq :
      ‖(algebraMap ℚ ℂ) (Algebra.discr ℚ b)‖ =
        (k.natAbs : ℝ) ^ 2 * (NumberField.discr K).natAbs := by
    rw [hdisc, hb₀disc, ← hk, map_mul, map_pow, norm_mul, norm_pow]
    norm_num [Rat.cast_intCast, Complex.norm_real, abs_of_nonneg]
  rw [hnormeq]
  have hkone : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk0
  have hkoneR : (1 : ℝ) ≤ k.natAbs := by exact_mod_cast hkone
  have hD : 0 ≤ ((NumberField.discr K).natAbs : ℝ) := by positivity
  calc
    ((NumberField.discr K).natAbs : ℝ) = 1 *
        (NumberField.discr K).natAbs := by ring
    _ ≤ (k.natAbs : ℝ) ^ 2 * (NumberField.discr K).natAbs := by
      exact mul_le_mul_of_nonneg_right (by nlinarith) hD

open Module in
/-- A convenient combined discriminant estimate for an integral field basis
whose conjugates all have one common norm bound. -/
lemma numberField_natAbs_discr_le_of_integral_basis_embedding_norm_le
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ K) (e : ι ≃ (K →ₐ[ℚ] ℂ)) (M : ℝ)
    (hInt : ∀ i, IsIntegral ℤ (b i))
    (hM : ∀ i j, ‖e j (b i)‖ ≤ M) :
    ((NumberField.discr K).natAbs : ℝ) ≤
      (((Fintype.card ι).factorial : ℝ) * M ^ Fintype.card ι) ^ 2 := by
  exact (numberField_natAbs_discr_le_integral_basis_discr_norm b hInt).trans
    (algebra_discr_norm_le_of_embedding_norm_le b e M hM)

open Module Function Set Submodule in
/-- Extracting a basis from a finite integral spanning family preserves its
uniform conjugate bound, and hence gives a discriminant estimate expressed
only in the field degree. -/
lemma numberField_natAbs_discr_le_of_finite_spanning_family
    {K : Type*} [Field K] [NumberField K]
    {α : Type*} [Fintype α] (v : α → K) (M : ℝ)
    (hspan : ⊤ ≤ Submodule.span ℚ (Set.range v))
    (hInt : ∀ a, IsIntegral ℤ (v a))
    (hM : ∀ a (w : K →ₐ[ℚ] ℂ), ‖w (v a)‖ ≤ M) :
    ((NumberField.discr K).natAbs : ℝ) ≤
      (((Module.finrank ℚ K).factorial : ℝ) *
        M ^ Module.finrank ℚ K) ^ 2 := by
  let I : Set K :=
    (linearIndepOn_empty ℚ id).extend (empty_subset (Set.range v))
  let b : Basis I ℚ K := Basis.ofSpan hspan
  have hIfin : I.Finite := by
    change ((linearIndepOn_empty ℚ id).extend
      (empty_subset (Set.range v))).Finite
    rw [← Basis.range_ofSpan hspan]
    exact (Set.finite_range v).subset (Basis.ofSpan_subset hspan)
  let : Fintype I := hIfin.fintype
  let : DecidableEq I := Classical.decEq I
  have hcard : Fintype.card I = Module.finrank ℚ K := by
    exact (Module.finrank_eq_card_basis b).symm
  let e : I ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq <| by
    rw [hcard, AlgHom.card]
  have hbInt : ∀ i, IsIntegral ℤ (b i) := by
    intro i
    have hi : b i ∈ Set.range v :=
      Basis.ofSpan_subset hspan (Set.mem_range_self i)
    obtain ⟨a, ha⟩ := hi
    rw [← ha]
    exact hInt a
  have hbM : ∀ i j, ‖e j (b i)‖ ≤ M := by
    intro i j
    have hi : b i ∈ Set.range v :=
      Basis.ofSpan_subset hspan (Set.mem_range_self i)
    obtain ⟨a, ha⟩ := hi
    rw [← ha]
    exact hM a (e j)
  simpa only [hcard] using
    numberField_natAbs_discr_le_of_integral_basis_embedding_norm_le
      b e M hbInt hbM

open Module Function Set Submodule in
/-- Extract an actual rational basis from a finite integral spanning family.
Every extracted basis vector is one of the original vectors, so both
integrality and the common conjugate bound are preserved. -/
theorem exists_integral_basis_of_finite_spanning_family
    {K : Type*} [Field K] [NumberField K]
    {α : Type*} [Fintype α] (v : α → K) (M : ℝ)
    (hspan : ⊤ ≤ Submodule.span ℚ (Set.range v))
    (hInt : ∀ a, IsIntegral ℤ (v a))
    (hM : ∀ a (w : K →ₐ[ℚ] ℂ), ‖w (v a)‖ ≤ M) :
    ∃ I : Set K, I.Finite ∧ ∃ b : Module.Basis I ℚ K,
      (∀ i, IsIntegral ℤ (b i)) ∧
      (∀ i (w : K →ₐ[ℚ] ℂ), ‖w (b i)‖ ≤ M) := by
  let I : Set K :=
    (linearIndepOn_empty ℚ id).extend (empty_subset (Set.range v))
  let b : Basis I ℚ K := Basis.ofSpan hspan
  have hIfin : I.Finite := by
    change ((linearIndepOn_empty ℚ id).extend
      (empty_subset (Set.range v))).Finite
    rw [← Basis.range_ofSpan hspan]
    exact (Set.finite_range v).subset (Basis.ofSpan_subset hspan)
  refine ⟨I, hIfin, b, ?_, ?_⟩
  · intro i
    have hi : b i ∈ Set.range v :=
      Basis.ofSpan_subset hspan (Set.mem_range_self i)
    obtain ⟨a, ha⟩ := hi
    rw [← ha]
    exact hInt a
  · intro i w
    have hi : b i ∈ Set.range v :=
      Basis.ofSpan_subset hspan (Set.mem_range_self i)
    obtain ⟨a, ha⟩ := hi
    rw [← ha]
    exact hM a w

/-- The eight square-root monomials used to span a field generated by three
quadratic radicals.  The `Fin 2` exponents are exactly zero or one. -/
def threeSqRootMonomial {K : Type*} [Field K]
    (s₁ s₂ s₃ : K) (a : Fin 2 × Fin 2 × Fin 2) : K :=
  s₁ ^ (a.1 : ℕ) * s₂ ^ (a.2.1 : ℕ) * s₃ ^ (a.2.2 : ℕ)

/-- Products of the eight square-root monomials reduce, using the three
quadratic equations, to scalar multiples of the same eight monomials. -/
lemma threeSqRootMonomial_span_mul_mem
    {K : Type*} [Field K] [Algebra ℚ K]
    (s₁ s₂ s₃ : K) (γ₁ γ₂ γ₃ : ℚ)
    (hs₁ : s₁ ^ 2 = algebraMap ℚ K γ₁)
    (hs₂ : s₂ ^ 2 = algebraMap ℚ K γ₂)
    (hs₃ : s₃ ^ 2 = algebraMap ℚ K γ₃)
    (a b : Fin 2 × Fin 2 × Fin 2) :
    threeSqRootMonomial s₁ s₂ s₃ a *
      threeSqRootMonomial s₁ s₂ s₃ b ∈
      Submodule.span ℚ (Set.range (threeSqRootMonomial s₁ s₂ s₃)) := by
  let V := Submodule.span ℚ (Set.range (threeSqRootMonomial s₁ s₂ s₃))
  have hv (c : Fin 2 × Fin 2 × Fin 2) :
      threeSqRootMonomial s₁ s₂ s₃ c ∈ V :=
    Submodule.subset_span (Set.mem_range_self c)
  have h000 : (1 : K) ∈ V := by
    simpa [threeSqRootMonomial] using hv (0, 0, 0)
  have h001 : s₃ ∈ V := by
    simpa [threeSqRootMonomial] using hv (0, 0, 1)
  have h010 : s₂ ∈ V := by
    simpa [threeSqRootMonomial] using hv (0, 1, 0)
  have h011 : s₂ * s₃ ∈ V := by
    simpa [threeSqRootMonomial] using hv (0, 1, 1)
  have h100 : s₁ ∈ V := by
    simpa [threeSqRootMonomial] using hv (1, 0, 0)
  have h101 : s₁ * s₃ ∈ V := by
    simpa [threeSqRootMonomial] using hv (1, 0, 1)
  have h110 : s₁ * s₂ ∈ V := by
    simpa [threeSqRootMonomial] using hv (1, 1, 0)
  have h111 : s₁ * s₂ * s₃ ∈ V := by
    simpa [threeSqRootMonomial] using hv (1, 1, 1)
  have heq :
      threeSqRootMonomial s₁ s₂ s₃ a *
          threeSqRootMonomial s₁ s₂ s₃ b =
        algebraMap ℚ K (γ₁ ^ ((a.1 : ℕ) * (b.1 : ℕ))) *
          algebraMap ℚ K (γ₂ ^ ((a.2.1 : ℕ) * (b.2.1 : ℕ))) *
          algebraMap ℚ K (γ₃ ^ ((a.2.2 : ℕ) * (b.2.2 : ℕ))) *
          threeSqRootMonomial s₁ s₂ s₃ (a + b) := by
    rcases a with ⟨a₁, a₂, a₃⟩
    rcases b with ⟨b₁, b₂, b₃⟩
    fin_cases a₁ <;> fin_cases a₂ <;> fin_cases a₃ <;>
      fin_cases b₁ <;> fin_cases b₂ <;> fin_cases b₃ <;>
      simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, mul_one, pow_one, eq_ratCast, mul_zero, pow_zero,
    Rat.cast_one, Prod.mk_add_mk, Fin.reduceAdd, add_zero, zero_add, one_mul] <;> (try ring_nf) <;>
      simp [hs₁, hs₂, hs₃] <;> (try ac_rfl) <;>
      exact Or.inl (mul_comm _ _)
  rw [heq]
  simpa [Algebra.smul_def, mul_assoc] using
    V.smul_mem (γ₁ ^ ((a.1 : ℕ) * (b.1 : ℕ)))
      (V.smul_mem (γ₂ ^ ((a.2.1 : ℕ) * (b.2.1 : ℕ)))
        (V.smul_mem (γ₃ ^ ((a.2.2 : ℕ) * (b.2.2 : ℕ))) (hv (a + b))))

/-- If the three radicals generate the ambient algebra, their eight
zero-one monomials span it as a rational vector space. -/
lemma threeSqRootMonomial_span_eq_top_of_adjoin_eq_top
    {K : Type*} [Field K] [Algebra ℚ K]
    (s₁ s₂ s₃ : K) (γ₁ γ₂ γ₃ : ℚ)
    (hs₁ : s₁ ^ 2 = algebraMap ℚ K γ₁)
    (hs₂ : s₂ ^ 2 = algebraMap ℚ K γ₂)
    (hs₃ : s₃ ^ 2 = algebraMap ℚ K γ₃)
    (hgen : Algebra.adjoin ℚ {s₁, s₂, s₃} = ⊤) :
    Submodule.span ℚ (Set.range (threeSqRootMonomial s₁ s₂ s₃)) = ⊤ := by
  let V := Submodule.span ℚ (Set.range (threeSqRootMonomial s₁ s₂ s₃))
  have hv (c : Fin 2 × Fin 2 × Fin 2) :
      threeSqRootMonomial s₁ s₂ s₃ c ∈ V :=
    Submodule.subset_span (Set.mem_range_self c)
  have h_one : (1 : K) ∈ V := by
    simpa [threeSqRootMonomial] using hv (0, 0, 0)
  have h_mul (x y : K) (hx : x ∈ V) (hy : y ∈ V) : x * y ∈ V := by
    refine Submodule.span_induction₂
      (p := fun x y _ _ ↦ x * y ∈ V) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact threeSqRootMonomial_span_mul_mem s₁ s₂ s₃ γ₁ γ₂ γ₃ hs₁ hs₂ hs₃ a b
    · intro y hy
      simpa using V.zero_mem
    · intro x hx
      simpa using V.zero_mem
    · intro x y z hx hy hz hxz hyz
      simpa [add_mul] using V.add_mem hxz hyz
    · intro x y z hx hy hz hxy hxz
      simpa [mul_add] using V.add_mem hxy hxz
    · intro r x y hx hy hxy
      simpa [Algebra.smul_def, mul_assoc] using V.smul_mem r hxy
    · intro r x y hx hy hxy
      simpa [Algebra.smul_def, mul_left_comm, mul_assoc] using V.smul_mem r hxy
  let A : Subalgebra ℚ K := V.toSubalgebra h_one h_mul
  have hs₁V : s₁ ∈ A := by
    simpa [A, V, threeSqRootMonomial] using hv (1, 0, 0)
  have hs₂V : s₂ ∈ A := by
    simpa [A, V, threeSqRootMonomial] using hv (0, 1, 0)
  have hs₃V : s₃ ∈ A := by
    simpa [A, V, threeSqRootMonomial] using hv (0, 0, 1)
  have hadjoin : Algebra.adjoin ℚ {s₁, s₂, s₃} ≤ A := by
    refine Algebra.adjoin_le ?_
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hs₁V, hs₂V, hs₃V⟩
  have hAtop : A = ⊤ := by
    apply top_unique
    simpa [hgen] using hadjoin
  apply top_unique
  intro x hx
  have : x ∈ A := by simpa [hAtop]
  exact this

/-- A square root of a rational integer is integral over `ℤ`. -/
lemma sqRoot_isIntegral_nat
    {K : Type*} [Field K] [Algebra ℚ K]
    (s : K) {n : ℕ} (hs : s ^ 2 = (n : K)) : IsIntegral ℤ s := by
  apply IsIntegral.of_pow (by norm_num : 0 < 2)
  rw [hs]
  exact isIntegral_natCast (R := ℤ) (B := K) n

/-- Every zero-one monomial in three integral square roots is integral. -/
lemma threeSqRootMonomial_isIntegral
    {K : Type*} [Field K] [Algebra ℚ K]
    (s₁ s₂ s₃ : K) {n₁ n₂ n₃ : ℕ}
    (hs₁ : s₁ ^ 2 = (n₁ : K)) (hs₂ : s₂ ^ 2 = (n₂ : K))
    (hs₃ : s₃ ^ 2 = (n₃ : K)) (a : Fin 2 × Fin 2 × Fin 2) :
    IsIntegral ℤ (threeSqRootMonomial s₁ s₂ s₃ a) := by
  exact (((sqRoot_isIntegral_nat s₁ hs₁).pow _).mul
    ((sqRoot_isIntegral_nat s₂ hs₂).pow _)).mul
      ((sqRoot_isIntegral_nat s₃ hs₃).pow _)

/-- A conjugate of a positive square root whose radicand is at most `H`
has norm at most `H`; this deliberately coarse integral bound avoids real
square-root bookkeeping. -/
lemma sqRoot_embedding_norm_le_nat
    {K : Type*} [Field K] [NumberField K]
    (s : K) {γ H : ℕ} (hs : s ^ 2 = (γ : K))
    (hγ : 0 < γ) (hγH : γ ≤ H) (w : K →ₐ[ℚ] ℂ) :
    ‖w s‖ ≤ (H : ℝ) := by
  have heq : ‖w s‖ ^ 2 = (γ : ℝ) := by
    calc
      ‖w s‖ ^ 2 = ‖(w s) ^ 2‖ := by rw [norm_pow]
      _ = ‖w (s ^ 2)‖ := by rw [map_pow]
      _ = ‖w (γ : K)‖ := by rw [hs]
      _ = (γ : ℝ) := by norm_num
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hγ.trans_le hγH
  have hγHR : (γ : ℝ) ≤ H := by exact_mod_cast hγH
  have hn : 0 ≤ ‖w s‖ := norm_nonneg _
  nlinarith [sq_nonneg ((H : ℝ) - ‖w s‖)]

/-- Every conjugate of an eight-monomial spanning element is bounded by
`H³` when the three positive radicands are at most `H`. -/
lemma threeSqRootMonomial_embedding_norm_le
    {K : Type*} [Field K] [NumberField K]
    (s₁ s₂ s₃ : K) {γ₁ γ₂ γ₃ H : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (a : Fin 2 × Fin 2 × Fin 2) (w : K →ₐ[ℚ] ℂ) :
    ‖w (threeSqRootMonomial s₁ s₂ s₃ a)‖ ≤ (H : ℝ) ^ 3 := by
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hγ₁.trans_le hγ₁H
  have h₁ (i : Fin 2) : ‖w (s₁ ^ (i : ℕ))‖ ≤ (H : ℝ) := by
    fin_cases i
    · simpa using hH
    · simpa using sqRoot_embedding_norm_le_nat s₁ hs₁ hγ₁ hγ₁H w
  have h₂ (i : Fin 2) : ‖w (s₂ ^ (i : ℕ))‖ ≤ (H : ℝ) := by
    fin_cases i
    · simpa using hH
    · simpa using sqRoot_embedding_norm_le_nat s₂ hs₂ hγ₂ hγ₂H w
  have h₃ (i : Fin 2) : ‖w (s₃ ^ (i : ℕ))‖ ≤ (H : ℝ) := by
    fin_cases i
    · simpa using hH
    · simpa using sqRoot_embedding_norm_le_nat s₃ hs₃ hγ₃ hγ₃H w
  rw [threeSqRootMonomial, map_mul, map_mul, norm_mul, norm_mul]
  calc
    ‖w (s₁ ^ (a.1 : ℕ))‖ * ‖w (s₂ ^ (a.2.1 : ℕ))‖ *
        ‖w (s₃ ^ (a.2.2 : ℕ))‖ ≤ (H : ℝ) * H * H := by
      gcongr <;> first | exact h₁ _ | exact h₂ _ | exact h₃ _
    _ = (H : ℝ) ^ 3 := by ring

/-- A generated three-radical field has an integral rational basis selected
from its eight zero-one radical monomials.  Every conjugate of every basis
element is bounded by `H³`. -/
theorem exists_threeSqRoot_integral_basis
    {K : Type*} [Field K] [NumberField K]
    (s₁ s₂ s₃ : K) {γ₁ γ₂ γ₃ H : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hgen : Algebra.adjoin ℚ {s₁, s₂, s₃} = ⊤) :
    ∃ I : Set K, I.Finite ∧ ∃ b : Module.Basis I ℚ K,
      (∀ i, IsIntegral ℤ (b i)) ∧
      (∀ i (w : K →ₐ[ℚ] ℂ), ‖w (b i)‖ ≤ (H : ℝ) ^ 3) := by
  apply exists_integral_basis_of_finite_spanning_family
    (threeSqRootMonomial s₁ s₂ s₃) ((H : ℝ) ^ 3)
  · rw [threeSqRootMonomial_span_eq_top_of_adjoin_eq_top
      s₁ s₂ s₃ (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using hs₁) (by simpa using hs₂) (by simpa using hs₃) hgen]
  · exact threeSqRootMonomial_isIntegral s₁ s₂ s₃ hs₁ hs₂ hs₃
  · exact threeSqRootMonomial_embedding_norm_le s₁ s₂ s₃
      hs₁ hs₂ hs₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H

/-- Explicit discriminant estimate for a number field generated by three
positive square roots of radicands at most `H`. -/
theorem numberField_natAbs_discr_le_three_sqRoots
    {K : Type*} [Field K] [NumberField K]
    (s₁ s₂ s₃ : K) {γ₁ γ₂ γ₃ H : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hgen : Algebra.adjoin ℚ {s₁, s₂, s₃} = ⊤) :
    ((NumberField.discr K).natAbs : ℝ) ≤
      (((Module.finrank ℚ K).factorial : ℝ) *
        ((H : ℝ) ^ 3) ^ Module.finrank ℚ K) ^ 2 := by
  apply numberField_natAbs_discr_le_of_finite_spanning_family
    (threeSqRootMonomial s₁ s₂ s₃) ((H : ℝ) ^ 3)
  · rw [threeSqRootMonomial_span_eq_top_of_adjoin_eq_top
      s₁ s₂ s₃ (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using hs₁) (by simpa using hs₂) (by simpa using hs₃) hgen]
  · exact threeSqRootMonomial_isIntegral s₁ s₂ s₃ hs₁ hs₂ hs₃
  · exact threeSqRootMonomial_embedding_norm_le s₁ s₂ s₃
      hs₁ hs₂ hs₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H

/-- A field generated by three quadratic radicals has rational degree at
most eight, proved here directly from the eight-monomial spanning family. -/
lemma finrank_threeSqRoots_le_eight
    {K : Type*} [Field K] [NumberField K]
    (s₁ s₂ s₃ : K) (γ₁ γ₂ γ₃ : ℚ)
    (hs₁ : s₁ ^ 2 = algebraMap ℚ K γ₁)
    (hs₂ : s₂ ^ 2 = algebraMap ℚ K γ₂)
    (hs₃ : s₃ ^ 2 = algebraMap ℚ K γ₃)
    (hgen : Algebra.adjoin ℚ {s₁, s₂, s₃} = ⊤) :
    Module.finrank ℚ K ≤ 8 := by
  have hspan := threeSqRootMonomial_span_eq_top_of_adjoin_eq_top
    s₁ s₂ s₃ γ₁ γ₂ γ₃ hs₁ hs₂ hs₃ hgen
  let : Fintype (Set.range (threeSqRootMonomial s₁ s₂ s₃)) :=
    (Set.finite_range (threeSqRootMonomial s₁ s₂ s₃)).fintype
  rw [← finrank_top ℚ K, ← hspan]
  calc
    Module.finrank ℚ (Submodule.span ℚ
        (Set.range (threeSqRootMonomial s₁ s₂ s₃))) ≤
        (Set.range (threeSqRootMonomial s₁ s₂ s₃)).toFinset.card :=
      finrank_span_le_card _
    _ = Fintype.card (Set.range (threeSqRootMonomial s₁ s₂ s₃)) := by
      rw [Set.toFinset_card]
    _ ≤ 8 := by
      simpa using Fintype.card_range_le (threeSqRootMonomial s₁ s₂ s₃)

/-- Degree-free version of the preceding discriminant estimate: all
generated fields under consideration satisfy `|D_K| ≤ (40320 H²⁴)²`. -/
theorem numberField_natAbs_discr_le_three_sqRoots_explicit
    {K : Type*} [Field K] [NumberField K]
    (s₁ s₂ s₃ : K) {γ₁ γ₂ γ₃ H : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hgen : Algebra.adjoin ℚ {s₁, s₂, s₃} = ⊤) :
    ((NumberField.discr K).natAbs : ℝ) ≤
      ((40320 : ℝ) * (H : ℝ) ^ 24) ^ 2 := by
  have hraw := numberField_natAbs_discr_le_three_sqRoots s₁ s₂ s₃
    hs₁ hs₂ hs₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H hgen
  have hdeg : Module.finrank ℚ K ≤ 8 :=
    finrank_threeSqRoots_le_eight s₁ s₂ s₃
      (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using hs₁) (by simpa using hs₂) (by simpa using hs₃) hgen
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hγ₁.trans_le hγ₁H
  have hfac : ((Module.finrank ℚ K).factorial : ℝ) ≤ 40320 := by
    exact_mod_cast Nat.factorial_le hdeg
  have hpow : ((H : ℝ) ^ 3) ^ Module.finrank ℚ K ≤ (H : ℝ) ^ 24 := by
    calc
      ((H : ℝ) ^ 3) ^ Module.finrank ℚ K ≤ ((H : ℝ) ^ 3) ^ 8 := by
        exact pow_le_pow_right₀ (one_le_pow₀ hH) hdeg
      _ = (H : ℝ) ^ 24 := by ring
  have hbase :
      ((Module.finrank ℚ K).factorial : ℝ) *
          ((H : ℝ) ^ 3) ^ Module.finrank ℚ K ≤
        (40320 : ℝ) * (H : ℝ) ^ 24 := by
    exact mul_le_mul hfac hpow (by positivity) (by positivity)
  exact hraw.trans (pow_le_pow_left₀ (by positivity) hbase 2)

/-- A complex number whose square is a positive rational integer is real.
This elementary observation is the archimedean input showing that the
three-radical fields used below are totally real. -/
lemma complex_isReal_of_sq_eq_pos_nat
    (z : ℂ) {n : ℕ} (hn : 0 < n) (hz : z ^ 2 = (n : ℂ)) :
    star z = z := by
  apply Complex.ext
  · simp
  · have him : 2 * z.re * z.im = 0 := by
      have h := congrArg Complex.im hz
      simp [pow_two] at h
      nlinarith
    have hre_or_im : z.re = 0 ∨ z.im = 0 := by
      exact mul_eq_zero.mp (by nlinarith : z.re * z.im = 0)
    rcases hre_or_im with hre | him0
    · have hreal := congrArg Complex.re hz
      simp [pow_two, hre] at hreal
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      nlinarith [sq_nonneg z.im]
    · simp [him0]

/-- A number field generated by square roots of positive rational integers
is totally real: every complex embedding sends each generator to a real
root, and the generators span the whole algebra. -/
theorem numberField_isTotallyReal_of_three_positive_sqRoots
    {K : Type*} [Field K] [NumberField K]
    (s₁ s₂ s₃ : K) {γ₁ γ₂ γ₃ : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hgen : Algebra.adjoin ℚ {s₁, s₂, s₃} = ⊤) :
    NumberField.IsTotallyReal K := by
  refine ⟨fun w ↦ ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff,
    NumberField.ComplexEmbedding.isReal_iff]
  let φ := NumberField.InfinitePlace.embedding w
  have heq : (NumberField.ComplexEmbedding.conjugate φ).toRatAlgHom =
      φ.toRatAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with hs | hs | hs
    · subst s
      apply complex_isReal_of_sq_eq_pos_nat (φ s₁) hγ₁
      simpa using congrArg φ hs₁
    · subst s
      apply complex_isReal_of_sq_eq_pos_nat (φ s₂) hγ₂
      simpa using congrArg φ hs₂
    · subst s
      apply complex_isReal_of_sq_eq_pos_nat (φ s₃) hγ₃
      simpa using congrArg φ hs₃
  exact congrArg AlgHom.toRingHom heq

/-- For a totally real number field, the sum of the integral traces of a
unit squared and its inverse squared is the sum of the corresponding
positive squared conjugate norms. -/
lemma trace_sq_unit_add_inv_eq_sum_norm_sq
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ((Algebra.trace ℤ (NumberField.RingOfIntegers K)
          ((u.1 : NumberField.RingOfIntegers K) ^ 2) +
        Algebra.trace ℤ (NumberField.RingOfIntegers K)
          (((u⁻¹).1 : NumberField.RingOfIntegers K) ^ 2) : ℤ) : ℝ) =
      ∑ φ : K →ₐ[ℚ] ℂ,
        (‖φ ((u.1 : NumberField.RingOfIntegers K) : K)‖ ^ 2 +
          ‖φ (((u⁻¹).1 : NumberField.RingOfIntegers K) : K)‖ ^ 2) := by
  let a : NumberField.RingOfIntegers K := u.1
  let b : NumberField.RingOfIntegers K := (u⁻¹).1
  have haC :
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) : ℤ) : ℂ) =
        ∑ φ : K →ₐ[ℚ] ℂ,
          φ ((a ^ 2 : NumberField.RingOfIntegers K) : K) := by
    calc
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) : ℤ) : ℂ) =
          algebraMap ℚ ℂ
            ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) : ℤ) : ℚ) := by
              norm_num
      _ = algebraMap ℚ ℂ
          (Algebra.trace ℚ K ((a ^ 2 : NumberField.RingOfIntegers K) : K)) := by
        rw [Algebra.coe_trace_int]
      _ = ∑ φ : K →ₐ[ℚ] ℂ,
          φ ((a ^ 2 : NumberField.RingOfIntegers K) : K) :=
        trace_eq_sum_embeddings ℂ
  have hbC :
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2) : ℤ) : ℂ) =
        ∑ φ : K →ₐ[ℚ] ℂ,
          φ ((b ^ 2 : NumberField.RingOfIntegers K) : K) := by
    calc
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2) : ℤ) : ℂ) =
          algebraMap ℚ ℂ
            ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2) : ℤ) : ℚ) := by
              norm_num
      _ = algebraMap ℚ ℂ
          (Algebra.trace ℚ K ((b ^ 2 : NumberField.RingOfIntegers K) : K)) := by
        rw [Algebra.coe_trace_int]
      _ = ∑ φ : K →ₐ[ℚ] ℂ,
          φ ((b ^ 2 : NumberField.RingOfIntegers K) : K) :=
        trace_eq_sum_embeddings ℂ
  have hC := congrArg Complex.re (congrArg₂ (· + ·) haC hbC)
  simp only [Complex.add_re, Complex.intCast_re, Complex.re_sum, map_pow] at hC
  have hreal_sq (φ : K →ₐ[ℚ] ℂ)
      (x : NumberField.RingOfIntegers K) :
      ((φ (x : K)) ^ 2).re = ‖φ (x : K)‖ ^ 2 := by
    have hφ := NumberField.IsTotallyReal.complexEmbedding_isReal φ.toRingHom
    have him : (φ (x : K)).im = 0 := by
      rw [← Complex.conj_eq_iff_im]
      exact RingHom.congr_fun hφ (x : K)
    rw [Complex.sq_norm]
    simp [Complex.normSq, pow_two, Complex.mul_re, him]
  change
    ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) +
      Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2) : ℤ) : ℝ) = _
  calc
    ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) +
        Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2) : ℤ) : ℝ) =
        (∑ φ : K →ₐ[ℚ] ℂ, ((φ (a : K)) ^ 2).re) +
          ∑ φ : K →ₐ[ℚ] ℂ, ((φ (b : K)) ^ 2).re := by
      simpa using hC
    _ = (∑ φ : K →ₐ[ℚ] ℂ, ‖φ (a : K)‖ ^ 2) +
        ∑ φ : K →ₐ[ℚ] ℂ, ‖φ (b : K)‖ ^ 2 := by
      congr 1 <;> apply Finset.sum_congr rfl <;>
        intro φ _ <;> exact hreal_sq φ _
    _ = ∑ φ : K →ₐ[ℚ] ℂ,
        (‖φ (a : K)‖ ^ 2 + ‖φ (b : K)‖ ^ 2) := by
      rw [Finset.sum_add_distrib]

/-- The trace sum is an integer strictly greater than twice the degree for
a non-torsion unit.  Strictness comes from one conjugate outside the unit
circle; integrality turns it into a full unit of numerical separation. -/
lemma trace_sq_unit_add_inv_gt_two_finrank
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    (2 * Module.finrank ℚ K : ℤ) <
      Algebra.trace ℤ (NumberField.RingOfIntegers K)
          ((u.1 : NumberField.RingOfIntegers K) ^ 2) +
        Algebra.trace ℤ (NumberField.RingOfIntegers K)
          (((u⁻¹).1 : NumberField.RingOfIntegers K) ^ 2) := by
  let a : NumberField.RingOfIntegers K := u.1
  let b : NumberField.RingOfIntegers K := (u⁻¹).1
  let q : (K →ₐ[ℚ] ℂ) → ℝ := fun φ ↦
    ‖φ (a : K)‖ ^ 2 + ‖φ (b : K)‖ ^ 2
  have hab (φ : K →ₐ[ℚ] ℂ) :
      ‖φ (b : K)‖ = (‖φ (a : K)‖)⁻¹ := by
    simp [a, b, NumberField.RingOfIntegers.coe_eq_algebraMap]
  have hq (φ : K →ₐ[ℚ] ℂ) : 2 ≤ q φ := by
    let r : ℝ := ‖φ (a : K)‖
    have hr : 0 < r := norm_pos_iff.mpr <| by
      exact (map_ne_zero_iff φ.toRingHom φ.injective).mpr (by simp [a])
    change 2 ≤ r ^ 2 + ‖φ (b : K)‖ ^ 2
    rw [hab φ]
    calc
      2 = 2 * r * r⁻¹ := by field_simp
      _ ≤ r ^ 2 + (r⁻¹) ^ 2 := two_mul_le_add_sq r r⁻¹
  obtain ⟨φ₀', hφ₀⟩ := exists_unit_embedding_log_norm_ge hdeg u hu
  let φ₀ : K →ₐ[ℚ] ℂ := φ₀'.toRatAlgHom
  have hlog₀ : 0 < Real.log ‖φ₀ (a : K)‖ := by
    have hgap : 0 < degreeEightUnitLogGap := degreeEightUnitLogGap_pos
    change degreeEightUnitLogGap ≤ Real.log ‖φ₀ (a : K)‖ at hφ₀
    exact hgap.trans_le hφ₀
  have hr₀ : 1 < ‖φ₀ (a : K)‖ :=
    (Real.log_pos_iff (by positivity)).mp hlog₀
  have hq₀ : 2 < q φ₀ := by
    let r : ℝ := ‖φ₀ (a : K)‖
    have hr : 0 < r := lt_trans zero_lt_one hr₀
    have hrne : r ≠ r⁻¹ := by
      intro heq
      have hinvlt : r⁻¹ < 1 := (inv_lt_one₀ hr).2 hr₀
      linarith
    have hsquare : 0 < (r - r⁻¹) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hrne)
    change 2 < r ^ 2 + ‖φ₀ (b : K)‖ ^ 2
    rw [hab φ₀]
    have hmul : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    nlinarith
  have hsum :
      (2 * Module.finrank ℚ K : ℝ) < ∑ φ : K →ₐ[ℚ] ℂ, q φ := by
    have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K :=
      AlgHom.card ℚ K ℂ
    calc
      (2 * Module.finrank ℚ K : ℝ) =
          ∑ _φ : K →ₐ[ℚ] ℂ, (2 : ℝ) := by simp [hcard, mul_comm]
      _ < ∑ φ : K →ₐ[ℚ] ℂ, q φ := by
        exact Finset.sum_lt_sum (fun φ _ ↦ hq φ)
          ⟨φ₀, Finset.mem_univ _, hq₀⟩
  have htrace :
      ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) +
        Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2) : ℤ) : ℝ) =
        ∑ φ : K →ₐ[ℚ] ℂ, q φ := by
    simpa [q, a, b] using trace_sq_unit_add_inv_eq_sum_norm_sq u
  have hcast :
      (((2 : ℤ) * (Module.finrank ℚ K : ℤ) : ℤ) : ℝ) <
        ((Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) +
          Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2) : ℤ) : ℝ) := by
    rw [htrace]
    exact_mod_cast hsum
  have hi : (2 : ℤ) * (Module.finrank ℚ K : ℤ) <
      Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) +
        Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2) := by
    exact_mod_cast hcast
  simpa [a, b] using hi

/-- In a totally real field of degree at most eight, a non-torsion unit has
a conjugate for which either the unit or its inverse has squared norm at
least `17/16`.  The constant follows only from the integral trace and the
degree bound. -/
theorem exists_totallyReal_degreeEight_unit_norm_sq_gap
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    ∃ φ : K →ₐ[ℚ] ℂ,
      (17 / 16 : ℝ) ≤ max
        (‖φ ((u.1 : NumberField.RingOfIntegers K) : K)‖ ^ 2)
        (‖φ (((u⁻¹).1 : NumberField.RingOfIntegers K) : K)‖ ^ 2) := by
  let a : NumberField.RingOfIntegers K := u.1
  let b : NumberField.RingOfIntegers K := (u⁻¹).1
  let q : (K →ₐ[ℚ] ℂ) → ℝ := fun φ ↦
    ‖φ (a : K)‖ ^ 2 + ‖φ (b : K)‖ ^ 2
  let T : ℤ :=
    Algebra.trace ℤ (NumberField.RingOfIntegers K) (a ^ 2) +
      Algebra.trace ℤ (NumberField.RingOfIntegers K) (b ^ 2)
  have hTgt : (2 : ℤ) * (Module.finrank ℚ K : ℤ) < T := by
    simpa [T, a, b] using trace_sq_unit_add_inv_gt_two_finrank hdeg u hu
  have hTle : (2 : ℤ) * (Module.finrank ℚ K : ℤ) + 1 ≤ T := by omega
  have htrace : (T : ℝ) = ∑ φ : K →ₐ[ℚ] ℂ, q φ := by
    simpa [T, q, a, b] using trace_sq_unit_add_inv_eq_sum_norm_sq u
  have hsum :
      (2 * Module.finrank ℚ K + 1 : ℝ) ≤
        ∑ φ : K →ₐ[ℚ] ℂ, q φ := by
    rw [← htrace]
    exact_mod_cast hTle
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K :=
    AlgHom.card ℚ K ℂ
  have hdpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hnotall : ¬ ∀ φ : K →ₐ[ℚ] ℂ, q φ < (17 / 8 : ℝ) := by
    intro hall
    let φ₀ : K →ₐ[ℚ] ℂ :=
      (Classical.choice (inferInstance : Nonempty (K →+* ℂ))).toRatAlgHom
    have hstrict : (∑ φ : K →ₐ[ℚ] ℂ, q φ) <
        ∑ _φ : K →ₐ[ℚ] ℂ, (17 / 8 : ℝ) := by
      exact Finset.sum_lt_sum (fun φ _ ↦ (hall φ).le)
        ⟨φ₀, Finset.mem_univ _, hall φ₀⟩
    have hconst : (∑ _φ : K →ₐ[ℚ] ℂ, (17 / 8 : ℝ)) =
        (Module.finrank ℚ K : ℝ) * (17 / 8 : ℝ) := by
      simp [hcard]
    have hupper : (∑ φ : K →ₐ[ℚ] ℂ, q φ) <
        (Module.finrank ℚ K : ℝ) * (17 / 8 : ℝ) := by
      simpa [hconst] using hstrict
    have hdegR : (Module.finrank ℚ K : ℝ) ≤ 8 := by exact_mod_cast hdeg
    have hbound : (Module.finrank ℚ K : ℝ) * (17 / 8 : ℝ) ≤
        2 * Module.finrank ℚ K + 1 := by
      nlinarith
    linarith
  push Not at hnotall
  obtain ⟨φ, hφ⟩ := hnotall
  refine ⟨φ, ?_⟩
  change (17 / 16 : ℝ) ≤ max
    (‖φ (a : K)‖ ^ 2) (‖φ (b : K)‖ ^ 2)
  have hmaxsum :
      ‖φ (a : K)‖ ^ 2 + ‖φ (b : K)‖ ^ 2 ≤
        2 * max (‖φ (a : K)‖ ^ 2) (‖φ (b : K)‖ ^ 2) := by
    nlinarith [le_max_left (‖φ (a : K)‖ ^ 2) (‖φ (b : K)‖ ^ 2),
      le_max_right (‖φ (a : K)‖ ^ 2) (‖φ (b : K)‖ ^ 2)]
  change (17 / 8 : ℝ) ≤ q φ at hφ
  dsimp [q] at hφ
  nlinarith

/-- A fully numerical logarithmic separation constant for non-torsion
units in the totally real degree-at-most-eight fields used here. -/
noncomputable def totallyRealDegreeEightUnitLogGap : ℝ :=
  Real.log (17 / 16 : ℝ) / 2

lemma totallyRealDegreeEightUnitLogGap_pos :
    0 < totallyRealDegreeEightUnitLogGap := by
  rw [totallyRealDegreeEightUnitLogGap]
  positivity

theorem exists_totallyReal_degreeEight_unit_abs_log_norm_ge
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    ∃ φ : K →ₐ[ℚ] ℂ,
      totallyRealDegreeEightUnitLogGap ≤
        |Real.log ‖φ ((u.1 : NumberField.RingOfIntegers K) : K)‖| := by
  obtain ⟨φ, hφ⟩ := exists_totallyReal_degreeEight_unit_norm_sq_gap hdeg u hu
  refine ⟨φ, ?_⟩
  let r : ℝ := ‖φ ((u.1 : NumberField.RingOfIntegers K) : K)‖
  have hr : 0 < r := norm_pos_iff.mpr <| by
    exact (map_ne_zero_iff φ.toRingHom φ.injective).mpr (by simp)
  have hinv :
      ‖φ (((u⁻¹).1 : NumberField.RingOfIntegers K) : K)‖ = r⁻¹ := by
    simp [r, NumberField.RingOfIntegers.coe_eq_algebraMap]
  rw [hinv] at hφ
  rcases (le_max_iff.mp hφ) with hlarge | hlarge
  · have hlog : Real.log (17 / 16 : ℝ) ≤ Real.log (r ^ 2) := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num) (pow_pos hr 2) hlarge
    rw [Real.log_pow] at hlog
    rw [totallyRealDegreeEightUnitLogGap]
    exact (by nlinarith [le_abs_self (Real.log r)])
  · have hlog : Real.log (17 / 16 : ℝ) ≤ Real.log ((r⁻¹) ^ 2) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by norm_num) (pow_pos (inv_pos.mpr hr) 2) hlarge
    rw [Real.log_pow, Real.log_inv] at hlog
    rw [totallyRealDegreeEightUnitLogGap]
    exact (by nlinarith [neg_le_abs (Real.log r)])

/-- Numerical uniform discreteness of the logarithmic unit lattice in the
totally real degree-at-most-eight case. -/
theorem totallyRealDegreeEightUnitLogGap_div_eight_le_logEmbedding_norm
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1) :
    totallyRealDegreeEightUnitLogGap / 8 ≤
      ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ := by
  classical
  obtain ⟨φ, hφ⟩ :=
    exists_totallyReal_degreeEight_unit_abs_log_norm_ge hdeg u hu
  let w : NumberField.InfinitePlace K :=
    NumberField.InfinitePlace.mk φ.toRingHom
  have hw : totallyRealDegreeEightUnitLogGap ≤
      |Real.log (w (u.1 : K))| := by
    simpa [w, NumberField.InfinitePlace.apply] using hφ
  have hlog :=
    NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le
      (x := u)
      (r := ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖)
      (norm_nonneg _) le_rfl w
  have hcard : Fintype.card (NumberField.InfinitePlace K) ≤
      Module.finrank ℚ K := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    calc
      Fintype.card (NumberField.InfinitePlace K) =
          ∑ _w : NumberField.InfinitePlace K, 1 := by simp
      _ ≤ ∑ w : NumberField.InfinitePlace K, w.mult := by
        exact Finset.sum_le_sum fun w _ ↦
          Nat.one_le_iff_ne_zero.mpr NumberField.InfinitePlace.mult_ne_zero
  have hcard8 : (Fintype.card (NumberField.InfinitePlace K) : ℝ) ≤ 8 := by
    exact_mod_cast hcard.trans hdeg
  have hnorm : 0 ≤
      ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ := norm_nonneg _
  have hδ : totallyRealDegreeEightUnitLogGap ≤
      (Fintype.card (NumberField.InfinitePlace K) : ℝ) *
        ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ :=
    hw.trans hlog
  have hδeight : totallyRealDegreeEightUnitLogGap ≤
      8 * ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ :=
    hδ.trans (mul_le_mul_of_nonneg_right hcard8 hnorm)
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    (by simpa [mul_comm] using hδeight)

/-- A lower bound for a regulator from a uniform lower bound on nonzero
vectors of the logarithmic unit lattice.  The proof is the contrapositive
of Minkowski's convex-body theorem applied to the open sup-norm ball. -/
theorem regulator_lower_of_unitLattice_gap
    {K : Type*} [Field K] [NumberField K]
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ x : NumberField.Units.unitLattice K,
      x ≠ 0 → ε ≤
        ‖(x : NumberField.Units.dirichletUnitTheorem.logSpace K)‖) :
    ε ^ NumberField.Units.rank K ≤ NumberField.Units.regulator K := by
  classical
  let b : Module.Basis (Fin (NumberField.Units.rank K)) ℝ
      (NumberField.Units.dirichletUnitTheorem.logSpace K) :=
    (NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
      (NumberField.Units.unitLattice K)
  have hspan : Submodule.span ℤ (Set.range b) =
      NumberField.Units.unitLattice K := by
    exact (NumberField.Units.basisUnitLattice K).ofZLatticeBasis_span ℝ
  let : Countable (NumberField.Units.unitLattice K) := by
    rw [← hspan]
    infer_instance
  let F : Set (NumberField.Units.dirichletUnitTheorem.logSpace K) :=
    ZSpan.fundamentalDomain b
  have hfund : MeasureTheory.IsAddFundamentalDomain
      (NumberField.Units.unitLattice K) F MeasureTheory.volume := by
    rw [← hspan]
    exact ZSpan.isAddFundamentalDomain b MeasureTheory.volume
  have hcov : NumberField.Units.regulator K =
      MeasureTheory.volume.real F := by
    rw [NumberField.Units.regulator]
    exact ZLattice.covolume_eq_measure_fundamentalDomain
      (NumberField.Units.unitLattice K) MeasureTheory.volume hfund
  by_contra h
  have hlt : NumberField.Units.regulator K <
      ε ^ NumberField.Units.rank K := lt_of_not_ge h
  have hvolFfin : MeasureTheory.volume F ≠ ⊤ := by
    exact (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  have hdim : Module.finrank ℝ
      (NumberField.Units.dirichletUnitTheorem.logSpace K) =
      NumberField.Units.rank K := NumberField.Units.finrank_eq_rank K
  have hcard : Fintype.card {w : NumberField.InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      NumberField.Units.rank K := by
    simpa [Module.finrank_fintype_fun_eq_card] using hdim
  have hmeasure : MeasureTheory.volume F * 2 ^ Module.finrank ℝ
        (NumberField.Units.dirichletUnitTheorem.logSpace K) <
      MeasureTheory.volume (Metric.ball
        (0 : NumberField.Units.dirichletUnitTheorem.logSpace K) ε) := by
    rw [Real.volume_pi_ball
      (0 : NumberField.Units.dirichletUnitTheorem.logSpace K) hε]
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top hvolFfin (by simp)) (by simp)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * ε) ^ _), hdim, hcard]
    change NumberField.Units.regulator K =
      (MeasureTheory.volume F).toReal at hcov
    rw [← hcov]
    have hmul := mul_lt_mul_of_pos_right hlt
      (pow_pos (by norm_num : (0 : ℝ) < 2) (NumberField.Units.rank K))
    calc
      NumberField.Units.regulator K * 2 ^ NumberField.Units.rank K <
          ε ^ NumberField.Units.rank K * 2 ^ NumberField.Units.rank K := hmul
      _ = (2 * ε) ^ NumberField.Units.rank K := by
        rw [mul_pow]
        ring
  obtain ⟨x, hx0, hxball⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := (NumberField.Units.unitLattice K).toAddSubgroup)
      hfund (s := Metric.ball
        (0 : NumberField.Units.dirichletUnitTheorem.logSpace K) ε)
      (by intro x hx; simpa [Metric.mem_ball] using hx)
      (convex_ball
        (0 : NumberField.Units.dirichletUnitTheorem.logSpace K) ε) hmeasure
  have hxlt :
      ‖(x : NumberField.Units.dirichletUnitTheorem.logSpace K)‖ < ε := by
    simpa [Metric.mem_ball] using hxball
  exact (not_lt_of_ge (hgap x hx0)) hxlt

/-- The exact numerical regulator lower bound used for the totally real
degree-at-most-eight splitting fields arising from three positive square
roots. -/
theorem totallyRealDegreeEight_regulator_lower
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) :
    (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K ≤
      NumberField.Units.regulator K := by
  apply regulator_lower_of_unitLattice_gap
    (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num))
  intro x hx
  obtain ⟨a, _ha, hax⟩ := x.property
  let u : (NumberField.RingOfIntegers K)ˣ := a.toMul
  have hlog : NumberField.Units.logEmbedding K (Additive.ofMul u) = x := by
    simpa [NumberField.Units.unitLattice, u] using hax
  have hu : ∀ n : ℕ, 0 < n →
      (u.1 : NumberField.RingOfIntegers K) ^ n ≠ 1 := by
    intro n hn hp
    have hup : u ^ n = 1 := by
      apply Units.ext
      simpa using hp
    have htor : u ∈ NumberField.Units.torsion K := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion]
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hup⟩
    have hz : NumberField.Units.logEmbedding K (Additive.ofMul u) = 0 :=
      NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr htor
    apply hx
    apply Subtype.ext
    rw [← hlog]
    exact hz
  rw [← hlog]
  exact totallyRealDegreeEightUnitLogGap_div_eight_le_logEmbedding_norm hdeg u hu

/-! ### Explicit size control for the bounded fundamental units -/

/-- The finite ideal count used by the quantitative Dirichlet-unit
construction consists of the nonzero ideals in the same norm range, together
with the zero ideal. -/
lemma boundedIdealCount_eq_nonzero_add_one
    (K : Type*) [Field K] [NumberField K] (B : ℕ) :
    BoundedUnits.boundedIdealCount (K := K) B =
      Nat.card {I : Towers.NonzeroIntegersIdeal K //
        Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ B} + 1 := by
  let s : Set (Ideal (NumberField.RingOfIntegers K)) :=
    {I | Ideal.absNorm I ≤ B}
  let hs : s.Finite := Ideal.finite_setOfPred_absNorm_le B
  change hs.toFinset.card = _
  calc
    hs.toFinset.card = s.ncard := (Set.ncard_eq_toFinset_card s hs).symm
    _ = Nat.card s := (Nat.card_coe_set_eq s).symm
    _ = Nat.card {I : Towers.NonzeroIntegersIdeal K //
          Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ B} + 1 := by
      change Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
          Ideal.absNorm I ≤ B} = _
      exact Ideal.card_norm_le_eq_card_norm_le_add_one B

/-- The collision count is bounded by the degree-wise Euler product at
`s = 2`.  This is the bridge between `BoundedUnits` and the explicit ideal
count developed in `ClassNumberBound`. -/
lemma boundedIdealCount_le_zeta
    (K : Type*) [Field K] [NumberField K] (B : ℕ) :
    (BoundedUnits.boundedIdealCount (K := K) B : ℝ) ≤
      (B : ℝ) ^ 2 * Towers.zetaTwoFactor K + 1 := by
  rw [boundedIdealCount_eq_nonzero_add_one]
  push_cast
  let sNat : Set (Towers.NonzeroIntegersIdeal K) :=
    {I | Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ B}
  have hsEq : sNat = Towers.idealsAbsNorm K (B : ℝ) := by
    ext I
    simp only [sNat, Towers.idealsAbsNorm, Set.mem_ofPred_eq]
    exact_mod_cast Iff.rfl
  have hcard : (Nat.card sNat : ℝ) =
      ((Towers.idealsAbsNorm K (B : ℝ)).ncard : ℝ) := by
    rw [Nat.card_coe_set_eq, hsEq]
  change (Nat.card sNat : ℝ) + 1 ≤ _
  rw [hcard]
  have hcount := Towers.ncard_ideals_norm (K := K)
    (B := (B : ℝ)) (by positivity)
  have hzeta := Towers.ideal_zeta_factor (K := K)
  simpa [add_comm] using add_le_add_right
    (hcount.trans (mul_le_mul_of_nonneg_left hzeta (by positivity))) 1

/-- A convenient completely numerical upper bound for the Euler factor. -/
lemma zetaTwoFactor_le_three_pow_finrank
    (K : Type*) [Field K] [NumberField K] :
    Towers.zetaTwoFactor K ≤ (3 : ℝ) ^ Module.finrank ℚ K := by
  have hzetaEq : ‖riemannZeta 2‖ = Real.pi ^ (2 : ℕ) / 6 := by
    rw [riemannZeta_two]
    norm_num [Real.norm_eq_abs, abs_of_pos, Real.pi_pos]
  have hpiSq : Real.pi ^ (2 : ℕ) < 16 := by
    have hprod : 0 < (4 - Real.pi) * (4 + Real.pi) :=
      mul_pos (sub_pos.mpr Real.pi_lt_four) (by positivity)
    nlinarith
  have hzeta : ‖riemannZeta 2‖ ≤ (3 : ℝ) := by
    rw [hzetaEq]
    nlinarith
  unfold Towers.zetaTwoFactor
  exact pow_le_pow_left₀ (norm_nonneg _) hzeta _

lemma zetaTwoFactor_le_degree_eight
    (K : Type*) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8) :
    Towers.zetaTwoFactor K ≤ (6561 : ℝ) := by
  calc
    Towers.zetaTwoFactor K ≤ (3 : ℝ) ^ Module.finrank ℚ K :=
      zetaTwoFactor_le_three_pow_finrank K
    _ ≤ (3 : ℝ) ^ 8 := pow_le_pow_right₀ (by norm_num) hdeg
    _ = 6561 := by norm_num

/-- In degree at most eight there are at most `6561 B² + 1` ideals in
the collision range. -/
lemma boundedIdealCount_le_degree_eight
    (K : Type*) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8) (B : ℕ) :
    BoundedUnits.boundedIdealCount (K := K) B ≤ 6561 * B ^ 2 + 1 := by
  exact_mod_cast (show
    (BoundedUnits.boundedIdealCount (K := K) B : ℝ) ≤
      ((6561 * B ^ 2 + 1 : ℕ) : ℝ) from
    calc
      (BoundedUnits.boundedIdealCount (K := K) B : ℝ) ≤
          (B : ℝ) ^ 2 * Towers.zetaTwoFactor K + 1 :=
        boundedIdealCount_le_zeta K B
      _ ≤ (B : ℝ) ^ 2 * 6561 + 1 := by
        gcongr
        exact zetaTwoFactor_le_degree_eight K hdeg
      _ = ((6561 * B ^ 2 + 1 : ℕ) : ℝ) := by norm_num; ring)

/-- A natural-number Minkowski cutoff obtained by rounding up Mathlib's
explicit discriminant-dependent bound. -/
noncomputable def boundedUnitMinkowskiNatBound (N : ℕ) : ℕ :=
  ⌈(NumberField.hermiteTheorem.boundOfDiscBdd N : ℝ)⌉₊

/-- A polynomially bounded Minkowski cutoff specialized to fields of degree
at most eight.  Unlike the general Hermite-theorem cutoff, its dependence
on the discriminant parameter is immediately explicit. -/
noncomputable def degreeEightMinkowskiNatBound (N : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (N : ℝ) * 256 + 1)

lemma degreeEightMinkowskiNatBound_le (N : ℕ) :
    degreeEightMinkowskiNatBound N ≤ 258 * (N + 1) := by
  rw [degreeEightMinkowskiNatBound, Nat.ceil_le]
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) + 1 := by
    have hsqrt0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    nlinarith [sq_nonneg ((N : ℝ) + 1 - Real.sqrt (N : ℝ))]
  exact_mod_cast (show Real.sqrt (N : ℝ) * 256 + 1 ≤
      (258 : ℝ) * ((N : ℝ) + 1) by nlinarith)

/-- In degree at most eight, the preceding explicit natural cutoff exceeds
the Minkowski bound after multiplication by Mathlib's convex-body factor. -/
lemma minkowskiBound_lt_degreeEightMinkowskiNatBound
    (K : Type*) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K ≤ 8) {N : ℕ}
    (hdisc : |NumberField.discr K| ≤ N) :
    NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K *
        degreeEightMinkowskiNatBound N := by
  have hraw : NumberField.mixedEmbedding.minkowskiBound K 1 ≤
      (NNReal.sqrt N : ENNReal) * (2 : ENNReal) ^ 8 := by
    rw [NumberField.mixedEmbedding.minkowskiBound,
      NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
      Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one,
      ENNReal.ofReal_one, one_mul, NumberField.mixedEmbedding.finrank,
      NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis]
    apply mul_le_mul
    · have hsqrtNN : NNReal.sqrt ‖NumberField.discr K‖₊ ≤ NNReal.sqrt N := by
        rw [NNReal.sqrt_le_sqrt]
        rw [← NNReal.coe_le_coe, coe_nnnorm, Int.norm_eq_abs,
          ← Int.cast_abs, NNReal.coe_natCast, ← Int.cast_natCast, Int.cast_le]
        exact hdisc
      calc
        (2 : ENNReal)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K *
            (NNReal.sqrt ‖NumberField.discr K‖₊ : ENNReal) ≤
            1 * (NNReal.sqrt N : ENNReal) := by
          exact mul_le_mul
            (pow_le_one₀ (by positivity) (by simp))
            (ENNReal.coe_le_coe.mpr hsqrtNN) (by positivity) (by positivity)
        _ = (NNReal.sqrt N : ENNReal) := one_mul _
    · exact pow_le_pow_right₀ (by norm_num) hdeg
    · positivity
    · positivity
  let X : ℝ := Real.sqrt (N : ℝ) * 256 + 1
  let B : ℕ := degreeEightMinkowskiNatBound N
  have hXB : X ≤ (B : ℝ) := by
    dsimp [X, B, degreeEightMinkowskiNatBound]
    exact Nat.le_ceil _
  have hcore : (NNReal.sqrt N : ENNReal) * (2 : ENNReal) ^ 8 <
      (B : ENNReal) := by
    rw [show (2 : ENNReal) ^ 8 = 256 by norm_num]
    apply ENNReal.coe_lt_coe.mpr
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact (show Real.sqrt (N : ℝ) * 256 < (B : ℝ) by
      dsimp [X] at hXB
      linarith)
  calc
    NumberField.mixedEmbedding.minkowskiBound K 1 ≤
        (NNReal.sqrt N : ENNReal) * (2 : ENNReal) ^ 8 := hraw
    _ < (B : ENNReal) := hcore
    _ = 1 * (B : ENNReal) := by rw [one_mul]
    _ ≤ NumberField.mixedEmbedding.convexBodyLTFactor K * (B : ENNReal) := by
      exact mul_le_mul_of_nonneg_right
        (ENNReal.coe_le_coe.mpr
          (NumberField.mixedEmbedding.one_le_convexBodyLTFactor K)) (by positivity)
    _ = _ := by rfl

lemma minkowskiBound_lt_boundedUnitMinkowskiNatBound
    (K : Type*) [Field K] [NumberField K]
    {N : ℕ} (hdisc : |NumberField.discr K| ≤ N) :
    NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K *
        boundedUnitMinkowskiNatBound N := by
  let A := NumberField.hermiteTheorem.boundOfDiscBdd N
  let B := boundedUnitMinkowskiNatBound N
  have hM : NumberField.mixedEmbedding.minkowskiBound K 1 <
      (A : ENNReal) := by
    simpa [A] using
      (NumberField.hermiteTheorem.minkowskiBound_lt_boundOfDiscBdd
        (K := K) hdisc)
  have hceilR : (A : ℝ) ≤ (B : ℝ) := by
    change (A : ℝ) ≤ (⌈(A : ℝ)⌉₊ : ℕ)
    exact Nat.le_ceil (A : ℝ)
  have hceilNN : A ≤ (B : NNReal) := by
    exact_mod_cast hceilR
  have hceilE : (A : ENNReal) ≤ (B : ENNReal) :=
    ENNReal.coe_le_coe.mpr hceilNN
  have hfac : (1 : ENNReal) ≤
      NumberField.mixedEmbedding.convexBodyLTFactor K := by
    exact_mod_cast NumberField.mixedEmbedding.one_le_convexBodyLTFactor K
  calc
    NumberField.mixedEmbedding.minkowskiBound K 1 < (A : ENNReal) := hM
    _ ≤ (B : ENNReal) := hceilE
    _ = 1 * (B : ENNReal) := by rw [one_mul]
    _ ≤ NumberField.mixedEmbedding.convexBodyLTFactor K * (B : ENNReal) := by
      gcongr

/-- The complete bounded-unit package needed in the three-radical fields:
the rounded discriminant cutoff is admissible for the Minkowski collision,
its ideal count is explicit, the generated unit subgroup has bounded finite
index, and every chosen generator has uniformly bounded logarithms at all
infinite places. -/
theorem degreeEight_boundedUnitData
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {N : ℕ}
    (hdisc : |NumberField.discr K| ≤ N) :
    let B := boundedUnitMinkowskiNatBound N
    ∃ hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
        NumberField.mixedEmbedding.convexBodyLTFactor K * B,
      BoundedUnits.boundedIdealCount (K := K) B ≤ 6561 * B ^ 2 + 1 ∧
      (BoundedUnits.boundedUnitSubgroup hB).index ≤
        BoundedUnits.boundedUnitIndexUpper (K := K)
          (totallyRealDegreeEightUnitLogGap / 8) B ∧
      ∀ (i : Fin (NumberField.Units.rank K))
          (w : NumberField.InfinitePlace K),
        |Real.log (w (BoundedUnits.boundedFundSystem hB i))| ≤
          BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
  dsimp only
  let B := boundedUnitMinkowskiNatBound N
  have hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B := by
    simpa [B] using minkowskiBound_lt_boundedUnitMinkowskiNatBound K hdisc
  refine ⟨hB, boundedIdealCount_le_degree_eight K hdeg B, ?_, ?_⟩
  · exact BoundedUnits.boundedUnitSubgroup_index_le hB
      (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num))
      (totallyRealDegreeEight_regulator_lower hdeg)
  · intro i w
    exact BoundedUnits.boundedFundSystem_log_abs_le hB i w

/-- Every generator in the bounded fundamental system has logarithmic
height at most eight times its common conjugate-log bound. -/
theorem boundedFundSystem_logHeight_le_degree_eight
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (i : Fin (NumberField.Units.rank K)) :
    Height.logHeight₁
        (((BoundedUnits.boundedFundSystem hB i :
          (NumberField.RingOfIntegers K)ˣ) :
            NumberField.RingOfIntegers K) : K) ≤
      8 * BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
  rw [numberField_logHeight_ringOfIntegers_eq_sum]
  have hterm : ∀ w : NumberField.InfinitePlace K,
      (w.mult : ℝ) * Real.posLog
          (w (((BoundedUnits.boundedFundSystem hB i :
            (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K)) ≤
        BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
    intro w
    rw [NumberField.IsTotallyReal.mult_eq, Nat.cast_one, one_mul]
    have hpos :
        Real.posLog
            (w (((BoundedUnits.boundedFundSystem hB i :
              (NumberField.RingOfIntegers K)ˣ) :
                NumberField.RingOfIntegers K) : K)) ≤
          |Real.log
            (w (((BoundedUnits.boundedFundSystem hB i :
              (NumberField.RingOfIntegers K)ˣ) :
                NumberField.RingOfIntegers K) : K))| := by
      rw [Real.posLog_def]
      exact max_le (abs_nonneg _) (le_abs_self _)
    exact hpos.trans (BoundedUnits.boundedFundSystem_log_abs_le hB i w)
  calc
    ∑ w : NumberField.InfinitePlace K,
        (w.mult : ℝ) * Real.posLog
          (w (((BoundedUnits.boundedFundSystem hB i :
            (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K)) ≤
        ∑ _w : NumberField.InfinitePlace K,
          BoundedUnits.commonBoundedUnitLogBound (K := K) B :=
      Finset.sum_le_sum fun w _ ↦ hterm w
    _ = (Fintype.card (NumberField.InfinitePlace K) : ℝ) *
        BoundedUnits.commonBoundedUnitLogBound (K := K) B := by simp
    _ ≤ 8 * BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
      apply mul_le_mul_of_nonneg_right
      · have hcard : Fintype.card (NumberField.InfinitePlace K) ≤
            Module.finrank ℚ K := by
          rw [← NumberField.InfinitePlace.sum_mult_eq]
          calc
            Fintype.card (NumberField.InfinitePlace K) =
                ∑ _w : NumberField.InfinitePlace K, 1 := by simp
            _ ≤ ∑ w : NumberField.InfinitePlace K, w.mult :=
              Finset.sum_le_sum fun w _ ↦
                Nat.one_le_iff_ne_zero.mpr
                  NumberField.InfinitePlace.mult_ne_zero
        exact_mod_cast hcard.trans hdeg
      · exact BoundedUnits.commonBoundedUnitLogBound_nonneg hB

/-- In every totally real field of degree at most eight and bounded
discriminant, the finite-index unit decomposition has exponent coordinates
bounded only by explicit functions of the discriminant cutoff and the
logarithmic size of the powered unit. -/
theorem degreeEight_boundedUnitExponentData
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {N : ℕ}
    (hdisc : |NumberField.discr K| ≤ N)
    (q : (NumberField.RingOfIntegers K)ˣ) :
    let B := boundedUnitMinkowskiNatBound N
    ∃ hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
        NumberField.mixedEmbedding.convexBodyLTFactor K * B,
      (BoundedUnits.boundedUnitSubgroup hB).index ≤
          BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B ∧
        ∃ (a : Fin (NumberField.Units.rank K) →₀ ℤ),
          ∀ i,
            |((a i : ℤ) : ℝ)| ≤
              ((NumberField.Units.rank K).factorial *
                (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                  (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
                    ‖NumberField.Units.logEmbedding K
                      (Additive.ofMul q)‖)) ^
                  NumberField.Units.rank K) /
                (totallyRealDegreeEightUnitLogGap / 8) ^
                  NumberField.Units.rank K := by
  dsimp only
  let B := boundedUnitMinkowskiNatBound N
  have hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B := by
    simpa [B] using minkowskiBound_lt_boundedUnitMinkowskiNatBound K hdisc
  refine ⟨hB, ?_, ?_⟩
  · exact BoundedUnits.boundedUnitSubgroup_index_le hB
      (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num))
      (totallyRealDegreeEight_regulator_lower hdeg)
  · exact BoundedUnits.boundedUnit_pow_decomposition_exponent_le_unpowered hB
      (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num))
      (totallyRealDegreeEight_regulator_lower hdeg) q

/-- The degree-eight bounded-unit package with the actual decomposition
identity retained.  This is the form needed when the resulting product is
inserted into an archimedean linear form. -/
theorem degreeEight_boundedUnitDecompositionData
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {N : ℕ}
    (hdisc : |NumberField.discr K| ≤ N)
    (q : (NumberField.RingOfIntegers K)ˣ) :
    let B := boundedUnitMinkowskiNatBound N
    ∃ hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
        NumberField.mixedEmbedding.convexBodyLTFactor K * B,
      (BoundedUnits.boundedUnitSubgroup hB).index ≤
          BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B ∧
        ∃ (ζ : NumberField.Units.torsion K)
            (a : Fin (NumberField.Units.rank K) →₀ ℤ),
          q ^ (BoundedUnits.boundedUnitSubgroup hB).index =
              ζ.1 * a.prod (fun i z ↦
                BoundedUnits.boundedFundSystem hB i ^ z) ∧
            ∀ i,
              |((a i : ℤ) : ℝ)| ≤
                ((NumberField.Units.rank K).factorial *
                  (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                    (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
                      ‖NumberField.Units.logEmbedding K
                        (Additive.ofMul q)‖)) ^
                    NumberField.Units.rank K) /
                  (totallyRealDegreeEightUnitLogGap / 8) ^
                    NumberField.Units.rank K := by
  dsimp only
  let B := boundedUnitMinkowskiNatBound N
  have hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B := by
    simpa [B] using minkowskiBound_lt_boundedUnitMinkowskiNatBound K hdisc
  refine ⟨hB, ?_, ?_⟩
  · exact BoundedUnits.boundedUnitSubgroup_index_le hB
      (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num))
      (totallyRealDegreeEight_regulator_lower hdeg)
  · exact BoundedUnits.boundedUnit_pow_decomposition_with_exponent_le_unpowered hB
      (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num))
      (totallyRealDegreeEight_regulator_lower hdeg) q

/-- The subgroup of field units which come from units of the ring of
integers. -/
def integerUnitSubgroup (K : Type*) [Field K] [NumberField K] :
    Subgroup Kˣ :=
  MonoidHom.range (Units.map
    (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom)

/-- If a positive power of a field unit is an algebraic-integer unit, then
the field unit itself is an algebraic-integer unit. -/
theorem fieldUnit_mem_integerUnitSubgroup_of_pow_mem
    {K : Type*} [Field K] [NumberField K]
    (w : Kˣ) {n : ℕ} (hn : 0 < n)
    (hpow : w ^ n ∈ integerUnitSubgroup K) :
    w ∈ integerUnitSubgroup K := by
  obtain ⟨u, hu⟩ := hpow
  have huK : (u : K) = ((w ^ n : Kˣ) : K) := by
    have h := congrArg (Units.val : Kˣ → K) hu
    simpa using h
  have hwpow : IsIntegral ℤ ((w : K) ^ n) := by
    rw [show (w : K) ^ n = (u : K) by simpa using huK.symm]
    exact u.1.isIntegral_coe
  have hw : IsIntegral ℤ (w : K) :=
    (IsIntegral.pow_iff hn).mp hwpow
  have huinvK : ((u⁻¹ : (NumberField.RingOfIntegers K)ˣ) : K) =
      (((w⁻¹ : Kˣ) : K) ^ n) := by
    calc
      ((u⁻¹ : (NumberField.RingOfIntegers K)ˣ) : K) =
          ((u : K)⁻¹) := by simp
      _ = ((((w ^ n : Kˣ) : K))⁻¹) := congrArg Inv.inv huK
      _ = (((w⁻¹ : Kˣ) : K) ^ n) := by simp
  have hwinvpow : IsIntegral ℤ (((w⁻¹ : Kˣ) : K) ^ n) := by
    rw [← huinvK]
    exact (u⁻¹).1.isIntegral_coe
  have hwinv : IsIntegral ℤ ((w⁻¹ : Kˣ) : K) :=
    (IsIntegral.pow_iff hn).mp hwinvpow
  let a : NumberField.RingOfIntegers K := ⟨(w : K), hw⟩
  let ai : NumberField.RingOfIntegers K :=
    ⟨((w⁻¹ : Kˣ) : K), hwinv⟩
  let q : (NumberField.RingOfIntegers K)ˣ :=
    ⟨a, ai, by
      apply NumberField.RingOfIntegers.coe_injective
      change (w : K) * ((w⁻¹ : Kˣ) : K) = 1
      simp,
      by
        apply NumberField.RingOfIntegers.coe_injective
        change ((w⁻¹ : Kˣ) : K) * (w : K) = 1
        simp⟩
  refine ⟨q, ?_⟩
  apply Units.ext
  change (w : K) = (w : K)
  rfl

/-- A field unit outside the ring-of-integers unit subgroup has infinite
order in the quotient by that subgroup. -/
theorem fieldUnit_quotient_pow_injective_of_not_mem
    {K : Type*} [Field K] [NumberField K]
    (w : Kˣ) (hw : w ∉ integerUnitSubgroup K) :
    Function.Injective
      (fun n : ℕ ↦
        (QuotientGroup.mk' (integerUnitSubgroup K) w) ^ n) := by
  refine (injective_pow_iff_not_isOfFinOrder
    (x := (QuotientGroup.mk' (integerUnitSubgroup K)) w)).2 ?_
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hmap :
      (QuotientGroup.mk' (integerUnitSubgroup K)) (w ^ n) = 1 := by
    simpa using hpow
  have hmem : w ^ n ∈ integerUnitSubgroup K :=
    (QuotientGroup.eq_one_iff (w ^ n)).mp hmap
  exact hw (fieldUnit_mem_integerUnitSubgroup_of_pow_mem w hn hmem)

/-- Adjoining one element of infinite order modulo a subgroup to a family
with injective box monomials preserves injectivity. -/
theorem boxMonomial_finCases_injective_of_quotient
    {G : Type*} [CommGroup G] {r N : ℕ}
    (H : Subgroup G) (W : G) (u : Fin r → G)
    (hu : ∀ i, u i ∈ H)
    (hW : Function.Injective
      (fun n : ℕ ↦ (QuotientGroup.mk' H W) ^ n))
    (htail : Function.Injective
      (fun x : LinearForms.ExponentBox r N ↦
        LinearForms.boxMonomial u x)) :
    Function.Injective
      (fun x : LinearForms.ExponentBox (r + 1) N ↦
        LinearForms.boxMonomial (Fin.cases W u) x) := by
  intro x y hxy
  have hprod : W ^ (x 0 : ℕ) *
        ∏ i : Fin r, u i ^ (x i.succ : ℕ) =
      W ^ (y 0 : ℕ) *
        ∏ i : Fin r, u i ^ (y i.succ : ℕ) := by
    simpa [LinearForms.boxMonomial, Fin.prod_univ_succ] using hxy
  have hheadNat : (x 0 : ℕ) = (y 0 : ℕ) := by
    apply hW
    have hmap := congrArg (QuotientGroup.mk' H) hprod
    rw [map_mul, map_mul, map_pow, map_pow] at hmap
    have htailx : (QuotientGroup.mk' H)
        (∏ i : Fin r, u i ^ (x i.succ : ℕ)) = 1 := by
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i _hi
      rw [map_pow]
      have hui : (QuotientGroup.mk' H) (u i) = 1 :=
        (QuotientGroup.eq_one_iff (u i)).2 (hu i)
      rw [hui, one_pow]
    have htaily : (QuotientGroup.mk' H)
        (∏ i : Fin r, u i ^ (y i.succ : ℕ)) = 1 := by
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i _hi
      rw [map_pow]
      have hui : (QuotientGroup.mk' H) (u i) = 1 :=
        (QuotientGroup.eq_one_iff (u i)).2 (hu i)
      rw [hui, one_pow]
    rw [htailx, htaily, mul_one, mul_one] at hmap
    exact hmap
  have hhead : x 0 = y 0 := Fin.ext hheadNat
  have htailProd :
      LinearForms.boxMonomial u (fun i ↦ x i.succ) =
        LinearForms.boxMonomial u (fun i ↦ y i.succ) := by
    rw [LinearForms.boxMonomial, LinearForms.boxMonomial]
    exact mul_left_cancel (hhead ▸ hprod)
  have htailEq : (fun i : Fin r ↦ x i.succ) =
      (fun i : Fin r ↦ y i.succ) := htail htailProd
  funext i
  refine Fin.cases hhead (fun j ↦ ?_) i
  exact congrFun htailEq j

/-- A maximal-rank unit family has unique finitely supported integer
coordinates.  This is the exact multiplicative independence statement
needed to feed the bounded fundamental system into the auxiliary-function
linear-form estimate. -/
theorem isMaxRank_finsupp_prod_injective
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (u : Fin (NumberField.Units.rank K) →
      (NumberField.RingOfIntegers K)ˣ)
    (hu : NumberField.Units.IsMaxRank u) :
    Function.Injective
      (fun a : Fin (NumberField.Units.rank K) →₀ ℤ ↦
        a.prod (fun i z ↦ u i ^ z)) := by
  intro a b hab
  have hlog := congrArg
    (fun z : (NumberField.RingOfIntegers K)ˣ ↦
      NumberField.Units.logEmbedding K (Additive.ofMul z)) hab
  rw [BoundedUnits.logEmbedding_finsupp_prod,
    BoundedUnits.logEmbedding_finsupp_prod] at hlog
  have hsum :
      ∑ i, ((a i : ℤ) : ℝ) • NumberField.Units.logEmbedding K
          (Additive.ofMul (u i)) =
        ∑ i, ((b i : ℤ) : ℝ) • NumberField.Units.logEmbedding K
          (Additive.ofMul (u i)) := by
    simpa [Finsupp.sum_fintype] using hlog
  apply Finsupp.ext
  intro i
  have hi := Fintype.linearIndependent_iffₛ.mp hu
    (fun i ↦ ((a i : ℤ) : ℝ)) (fun i ↦ ((b i : ℤ) : ℝ)) hsum i
  exact_mod_cast hi

/-- Squaring every member of a maximal-rank unit family gives an
injective monomial map on every nonnegative exponent box. -/
theorem isMaxRank_boxMonomial_sq_injective
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (u : Fin (NumberField.Units.rank K) →
      (NumberField.RingOfIntegers K)ˣ)
    (hu : NumberField.Units.IsMaxRank u) :
    ∀ N, Function.Injective
      (fun x : LinearForms.ExponentBox (NumberField.Units.rank K) N ↦
        LinearForms.boxMonomial
          (fun i ↦ ((((u i) ^ 2 :
            (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K)) x) := by
  intro N x y hxy
  have hunit :
      (∏ i, (u i ^ 2) ^ (x i : ℕ)) =
        ∏ i, (u i ^ 2) ^ (y i : ℕ) := by
    apply NumberField.Units.coe_injective K
    simpa [LinearForms.boxMonomial] using hxy
  have hlog := congrArg
    (fun z : (NumberField.RingOfIntegers K)ˣ ↦
      NumberField.Units.logEmbedding K (Additive.ofMul z)) hunit
  simp only [ofMul_prod, map_sum, ofMul_pow, map_nsmul] at hlog
  simp_rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at hlog
  funext i
  have hi := Fintype.linearIndependent_iffₛ.mp hu
    (fun i ↦ (x i : ℝ) * 2)
    (fun i ↦ (y i : ℝ) * 2) hlog i
  apply Fin.ext
  norm_num at hi ⊢
  exact_mod_cast hi

/-- The bounded fundamental system constructed above therefore has
injective squared monomials on every exponent box. -/
theorem boundedFundSystem_boxMonomial_sq_injective
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    ∀ N, Function.Injective
      (fun x : LinearForms.ExponentBox (NumberField.Units.rank K) N ↦
        LinearForms.boxMonomial
          (fun i ↦ ((((BoundedUnits.boundedFundSystem hB i) ^ 2 :
            (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K)) x) :=
  isMaxRank_boxMonomial_sq_injective
    (BoundedUnits.boundedFundSystem hB)
    (BoundedUnits.boundedFundSystem_isMaxRank hB)

/-- Squaring a finite-support product of integer powers is the full finite
product of the squared bases with the same integer powers. -/
lemma finsupp_prod_zpow_sq
    {G : Type*} [CommGroup G] {r : ℕ}
    (a : Fin r →₀ ℤ) (eps : Fin r → G) :
    (a.prod (fun i z ↦ eps i ^ z)) ^ 2 =
      ∏ i, (eps i ^ 2) ^ (a i) := by
  rw [Finsupp.prod_zpow]
  calc
    (∏ i, eps i ^ a i) ^ 2 =
        ∏ i ∈ (Finset.univ : Finset (Fin r)), (eps i ^ a i) ^ 2 := by
      rw [Finset.prod_pow]
    _ = ∏ i, (eps i ^ 2) ^ a i := by
      apply Finset.prod_congr rfl
      intro i _hi
      calc
        (eps i ^ a i) ^ (2 : ℕ) =
            (eps i ^ a i) ^ (2 : ℤ) :=
          (zpow_natCast (eps i ^ a i) 2).symm
        _ = eps i ^ (a i * (2 : ℤ)) :=
          (zpow_mul (eps i) (a i) (2 : ℤ)).symm
        _ = eps i ^ ((2 : ℤ) * a i) := by rw [mul_comm]
        _ = (eps i ^ (2 : ℤ)) ^ a i :=
          zpow_mul (eps i) (2 : ℤ) (a i)
        _ = (eps i ^ (2 : ℕ)) ^ a i :=
          congrArg (fun z : G ↦ z ^ a i) (zpow_natCast (eps i) 2)

/-- If one extra field unit is not a ring-of-integers unit, adjoining it to
the squared bounded fundamental system still gives injective box
monomials. -/
theorem boundedFundSystem_adjoin_boxMonomial_sq_injective
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (W : Kˣ) (hW : W ∉ integerUnitSubgroup K) :
    ∀ N, Function.Injective
      (fun x : LinearForms.ExponentBox
          (NumberField.Units.rank K + 1) N ↦
        LinearForms.boxMonomial
          (Fin.cases (W : K) (fun i ↦
            (((Units.map
              (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
                (BoundedUnits.boundedFundSystem hB i)) ^ 2 : Kˣ) : K))) x) := by
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  have hepsMem : ∀ i, eps i ^ 2 ∈ integerUnitSubgroup K := by
    intro i
    refine ⟨BoundedUnits.boundedFundSystem hB i ^ 2, ?_⟩
    simp [eps]
  intro N
  have htail : Function.Injective
      (fun x : LinearForms.ExponentBox (NumberField.Units.rank K) N ↦
        LinearForms.boxMonomial (fun i ↦ eps i ^ 2) x) := by
    intro x y hxy
    apply boundedFundSystem_boxMonomial_sq_injective hB N
    have hval := congrArg (Units.val : Kˣ → K) hxy
    simpa [LinearForms.boxMonomial, eps] using hval
  have hunit := boxMonomial_finCases_injective_of_quotient
    (integerUnitSubgroup K) W (fun i ↦ eps i ^ 2) hepsMem
      (fieldUnit_quotient_pow_injective_of_not_mem W hW) htail
  intro x y hxy
  apply hunit
  apply Units.ext
  have hcoe : ∀ i,
      ((Fin.cases W (fun i ↦ eps i ^ 2) i : Kˣ) : K) =
        Fin.cases (W : K) (fun i ↦ ((eps i ^ 2 : Kˣ) : K)) i := by
    intro i
    refine Fin.cases rfl (fun j ↦ ?_) i
    rfl
  change ((∏ i, (Fin.cases W (fun i ↦ eps i ^ 2) i) ^
      (x i : ℕ) : Kˣ) : K) =
    ((∏ i, (Fin.cases W (fun i ↦ eps i ^ 2) i) ^
      (y i : ℕ) : Kˣ) : K)
  push_cast
  simp_rw [hcoe]
  simpa [LinearForms.boxMonomial, eps] using hxy

/-- If the combined non-unit factor is in fact an algebraic-integer unit,
raise the product by twice the bounded subgroup index.  The torsion factor
then disappears and the whole product is expressed using only squares of
the maximal-rank bounded fundamental units. -/
theorem integerUnit_powered_product_eq_bounded_squares
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {B m : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (W z : Kˣ)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hW : W ∈ integerUnitSubgroup K)
    (hprod : z ^ m = W * ∏ i,
      ((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)) ^ 2) ^ (a i)) :
    ∃ c : Fin (NumberField.Units.rank K) →₀ ℤ,
      (z ^ m) ^ (2 * (BoundedUnits.boundedUnitSubgroup hB).index) =
        ∏ i,
          ((Units.map
            (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
              (BoundedUnits.boundedFundSystem hB i)) ^ 2) ^
            (c i +
              ((2 * (BoundedUnits.boundedUnitSubgroup hB).index : ℕ) : ℤ) *
                a i) := by
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  obtain ⟨q, hq⟩ := hW
  obtain ⟨ζ, c, hc⟩ := BoundedUnits.boundedUnit_pow_decomposition hB q
  refine ⟨c, ?_⟩
  have hcK := congrArg
    (Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom) hc
  simp only [map_pow, map_mul, map_finsuppProd, map_zpow] at hcK
  have hqW : Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom q = W := hq
  have hζsq : (Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1) ^ 2 =
        1 := by
    rw [← map_pow, totallyReal_torsion_sq_eq_one ζ, map_one]
  have hWI : W ^ I =
      Units.map
          (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1 *
        c.prod (fun i z ↦ eps i ^ z) := by
    rw [← hqW]
    simpa [I, eps] using hcK
  rw [hprod]
  change (W * ∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) = _
  rw [mul_pow]
  calc
    W ^ (2 * I) * (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) =
        (W ^ I) ^ 2 * (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) := by
      rw [show 2 * I = I * 2 by omega, pow_mul]
    _ = (c.prod (fun i z ↦ eps i ^ z)) ^ 2 *
          (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) := by
      rw [hWI, mul_pow, hζsq, one_mul]
    _ = (∏ i, (eps i ^ 2) ^ (c i)) *
          (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) := by
      rw [finsupp_prod_zpow_sq]
    _ = (∏ i, (eps i ^ 2) ^ (c i)) *
          ∏ i, (eps i ^ 2) ^ (((2 * I : ℕ) : ℤ) * a i) := by
      congr 1
      calc
        (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) =
            ∏ i, ((eps i ^ 2) ^ (a i)) ^ (2 * I) :=
          (Finset.prod_pow Finset.univ (2 * I)
            (fun i ↦ (eps i ^ 2) ^ (a i))).symm
        _ = ∏ i, (eps i ^ 2) ^
            (((2 * I : ℕ) : ℤ) * a i) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [← zpow_natCast, ← zpow_mul]
          congr 1
          ring
    _ = ∏ i, (eps i ^ 2) ^
          (c i + ((2 * I : ℕ) : ℤ) * a i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _hi
      exact (zpow_add (eps i ^ 2) (c i)
        (((2 * I : ℕ) : ℤ) * a i)).symm

/-- The integer-unit absorption identity together with the explicit
degree-eight coordinate bound for the newly introduced unit exponents. -/
theorem integerUnit_powered_product_eq_bounded_squares_with_bound
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {B m : ℕ} {Q : ℝ}
    (hdeg : Module.finrank ℚ K ≤ 8)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (W z : Kˣ)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hW : W ∈ integerUnitSubgroup K)
    (hQ : Height.logHeight₁ (W : K) ≤ Q)
    (hprod : z ^ m = W * ∏ i,
      ((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)) ^ 2) ^ (a i)) :
    ∃ c : Fin (NumberField.Units.rank K) →₀ ℤ,
      (z ^ m) ^ (2 * (BoundedUnits.boundedUnitSubgroup hB).index) =
          ∏ i,
            ((Units.map
              (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
                (BoundedUnits.boundedFundSystem hB i)) ^ 2) ^
              (c i +
                ((2 * (BoundedUnits.boundedUnitSubgroup hB).index : ℕ) : ℤ) *
                  a i) ∧
        ∀ i, |((c i : ℤ) : ℝ)| ≤
          ((NumberField.Units.rank K).factorial *
            (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
              (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) * (2 * Q))) ^
              NumberField.Units.rank K) /
            (totallyRealDegreeEightUnitLogGap / 8) ^
              NumberField.Units.rank K := by
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  obtain ⟨q, hq⟩ := hW
  obtain ⟨ζ, c, hc, hc_bound⟩ :=
    BoundedUnits.boundedUnit_pow_decomposition_with_exponent_le_unpowered hB
      (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num))
      (totallyRealDegreeEight_regulator_lower hdeg) q
  refine ⟨c, ?_, ?_⟩
  · have hcK := congrArg
      (Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom) hc
    simp only [map_pow, map_mul, map_finsuppProd, map_zpow] at hcK
    have hqW : Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom q = W := hq
    have hζsq : (Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1) ^ 2 =
          1 := by
      rw [← map_pow, totallyReal_torsion_sq_eq_one ζ, map_one]
    have hWI : W ^ I =
        Units.map
            (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1 *
          c.prod (fun i z ↦ eps i ^ z) := by
      rw [← hqW]
      simpa [I, eps] using hcK
    rw [hprod]
    change (W * ∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) = _
    rw [mul_pow]
    calc
      W ^ (2 * I) * (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) =
          (W ^ I) ^ 2 * (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) := by
        rw [show 2 * I = I * 2 by omega, pow_mul]
      _ = (c.prod (fun i z ↦ eps i ^ z)) ^ 2 *
            (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) := by
        rw [hWI, mul_pow, hζsq, one_mul]
      _ = (∏ i, (eps i ^ 2) ^ (c i)) *
            (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) := by
        rw [finsupp_prod_zpow_sq]
      _ = (∏ i, (eps i ^ 2) ^ (c i)) *
            ∏ i, (eps i ^ 2) ^ (((2 * I : ℕ) : ℤ) * a i) := by
        congr 1
        calc
          (∏ i, (eps i ^ 2) ^ (a i)) ^ (2 * I) =
              ∏ i, ((eps i ^ 2) ^ (a i)) ^ (2 * I) :=
            (Finset.prod_pow Finset.univ (2 * I)
              (fun i ↦ (eps i ^ 2) ^ (a i))).symm
          _ = ∏ i, (eps i ^ 2) ^
              (((2 * I : ℕ) : ℤ) * a i) := by
            apply Finset.prod_congr rfl
            intro i _hi
            rw [← zpow_natCast, ← zpow_mul]
            congr 1
            ring
      _ = ∏ i, (eps i ^ 2) ^
            (c i + ((2 * I : ℕ) : ℤ) * a i) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _hi
        exact (zpow_add (eps i ^ 2) (c i)
          (((2 * I : ℕ) : ℤ) * a i)).symm
  · intro i
    refine (hc_bound i).trans ?_
    have hqfield : (((q : NumberField.RingOfIntegers K) : K)) = (W : K) := by
      have hv := congrArg (Units.val : Kˣ → K) hq
      simpa using hv
    have hqheight : Height.logHeight₁
        (((q : NumberField.RingOfIntegers K) : K)) ≤ Q := by
      simpa only [hqfield] using hQ
    have hnorm := numberField_logEmbedding_norm_le_two_logHeight K q
    have hnormQ :
        ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖ ≤ 2 * Q :=
      hnorm.trans (mul_le_mul_of_nonneg_left hqheight (by norm_num))
    have hproduct :
        ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
            ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖ ≤
          ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) * (2 * Q) :=
      mul_le_mul_of_nonneg_left hnormQ (Nat.cast_nonneg _)
    have hmax := max_le_max_left
      (BoundedUnits.commonBoundedUnitLogBound (K := K) B) hproduct
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hmax _) (Nat.cast_nonneg _))
      (pow_nonneg (le_of_lt (div_pos totallyRealDegreeEightUnitLogGap_pos
        (by norm_num))) _)

/-- The real coordinate bound introduced when a combined leading factor
is absorbed into the bounded ordinary-unit basis. -/
def integerUnitAbsorptionRealBound
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B0 : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (Q : ℝ) : ℝ :=
  ((NumberField.Units.rank K).factorial *
    (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B0)
      (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) * (2 * Q))) ^
      NumberField.Units.rank K) /
    (totallyRealDegreeEightUnitLogGap / 8) ^
      NumberField.Units.rank K

/-- A natural coefficient box containing both the absorbed coordinates
and the original coordinates multiplied by twice the subgroup index. -/
noncomputable def integerUnitAbsorptionNatBound
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B0 : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (Q : ℝ) (B : ℕ) : ℕ :=
  Nat.ceil (integerUnitAbsorptionRealBound K hB Q) +
    2 * (BoundedUnits.boundedUnitSubgroup hB).index * B

lemma integerUnitAbsorptionCoefficient_natAbs_le
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B0 B : ℕ} {Q : ℝ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (c a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hc : ∀ i, |((c i : ℤ) : ℝ)| ≤
      integerUnitAbsorptionRealBound K hB Q)
    (ha : ∀ i, (a i).natAbs ≤ B) :
    ∀ i,
      (c i +
        ((2 * (BoundedUnits.boundedUnitSubgroup hB).index : ℕ) : ℤ) *
          a i).natAbs ≤ integerUnitAbsorptionNatBound K hB Q B := by
  intro i
  have hcNat : (c i).natAbs ≤
      Nat.ceil (integerUnitAbsorptionRealBound K hB Q) := by
    exact_mod_cast (show (((c i).natAbs : ℕ) : ℝ) ≤
      (Nat.ceil (integerUnitAbsorptionRealBound K hB Q) : ℕ) from
      calc
        (((c i).natAbs : ℕ) : ℝ) = |((c i : ℤ) : ℝ)| := by simp
        _ ≤ integerUnitAbsorptionRealBound K hB Q := hc i
        _ ≤ (Nat.ceil (integerUnitAbsorptionRealBound K hB Q) : ℕ) :=
          Nat.le_ceil _)
  calc
    (c i +
        ((2 * (BoundedUnits.boundedUnitSubgroup hB).index : ℕ) : ℤ) *
          a i).natAbs ≤
        (c i).natAbs +
          (((2 * (BoundedUnits.boundedUnitSubgroup hB).index : ℕ) : ℤ) *
            a i).natAbs := Int.natAbs_add_le _ _
    _ = (c i).natAbs +
          (2 * (BoundedUnits.boundedUnitSubgroup hB).index) *
            (a i).natAbs := by rw [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ Nat.ceil (integerUnitAbsorptionRealBound K hB Q) +
          2 * (BoundedUnits.boundedUnitSubgroup hB).index * B := by
      exact Nat.add_le_add hcNat (Nat.mul_le_mul_left _ (ha i))
    _ = integerUnitAbsorptionNatBound K hB Q B := rfl

/-- A nontrivial absorbed product has a nonzero resulting coefficient
vector, as required by the logarithmic-form lower bound. -/
lemma absorbedCoefficient_ne_zero
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B m : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (z : Kˣ) (a c : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hprod : (z ^ m) ^ (2 * (BoundedUnits.boundedUnitSubgroup hB).index) =
      ∏ i,
        ((Units.map
          (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
            (BoundedUnits.boundedFundSystem hB i)) ^ 2) ^
          (c i +
            ((2 * (BoundedUnits.boundedUnitSubgroup hB).index : ℕ) : ℤ) *
              a i))
    (hne : (z ^ m) ^ (2 * (BoundedUnits.boundedUnitSubgroup hB).index) ≠ 1) :
    (fun i ↦ c i +
      ((2 * (BoundedUnits.boundedUnitSubgroup hB).index : ℕ) : ℤ) *
        a i) ≠ 0 := by
  intro hb
  apply hne
  rw [hprod]
  apply Finset.prod_eq_one
  intro i _hi
  have hi := congrFun hb i
  change
    ((Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)) ^ 2) ^
      (c i +
        ((2 * (BoundedUnits.boundedUnitSubgroup hB).index : ℕ) : ℤ) *
          a i) = 1
  rw [hi]
  simp

/-- The class-number decomposition of a supported unit can use the explicit
bounded fundamental system rather than Mathlib's arbitrary chosen one.
Both the finite-prime exponents and the bounded-unit identity are retained,
ready to be substituted into the Pell supported-unit equation. -/
theorem numberField_supportedUnit_classNumber_boundedUnit_decomposition
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K)
    (hdeg : Module.finrank ℚ K ≤ 8) {N : ℕ}
    (hdisc : |NumberField.discr K| ≤ N) :
    let B := boundedUnitMinkowskiNatBound N
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K)
        (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
          NumberField.mixedEmbedding.convexBodyLTFactor K * B)
        (ζ : NumberField.Units.torsion K)
        (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
            (q : Kˣ) ∧
        (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
        (BoundedUnits.boundedUnitSubgroup hB).index ≤
          BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B ∧
        (SupportedUnits.emptyEquivUnits K q) ^
            (BoundedUnits.boundedUnitSubgroup hB).index =
          ζ.1 * a.prod (fun i z ↦
            BoundedUnits.boundedFundSystem hB i ^ z) ∧
        ∀ i,
          |((a i : ℤ) : ℝ)| ≤
            ((NumberField.Units.rank K).factorial *
              (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
                  ‖NumberField.Units.logEmbedding K
                    (Additive.ofMul
                      (SupportedUnits.emptyEquivUnits K q))‖)) ^
                NumberField.Units.rank K) /
              (totallyRealDegreeEightUnitLogGap / 8) ^
                NumberField.Units.rank K := by
  dsimp only
  obtain ⟨e, q, hpow, he⟩ :=
    SupportedUnits.exists_primeClassProduct_mul_emptySupportedUnit_eq_pow S u
  obtain ⟨hB, hindex, ζ, a, hq, ha⟩ :=
    degreeEight_boundedUnitDecompositionData K hdeg hdisc
      (SupportedUnits.emptyEquivUnits K q)
  exact ⟨e, q, hB, ζ, a, hpow, he, hindex, hq, ha⟩

/-- A height-only form of the bounded-unit exponent estimate.  Both the
subgroup index and the logarithmic norm are replaced by the explicit
discriminant cutoff and a supplied logarithmic-height bound. -/
theorem degreeEight_boundedUnitExponentData_of_logHeight
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {N : ℕ}
    (hdisc : |NumberField.discr K| ≤ N)
    (q : (NumberField.RingOfIntegers K)ˣ) {Q : ℝ}
    (hQ : 0 ≤ Q)
    (hq : Height.logHeight₁
      (((q : NumberField.RingOfIntegers K) : K)) ≤ Q) :
    let B := boundedUnitMinkowskiNatBound N
    ∃ hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
        NumberField.mixedEmbedding.convexBodyLTFactor K * B,
      (BoundedUnits.boundedUnitSubgroup hB).index ≤
          BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B ∧
        ∃ (a : Fin (NumberField.Units.rank K) →₀ ℤ),
          ∀ i,
            |((a i : ℤ) : ℝ)| ≤
              ((NumberField.Units.rank K).factorial *
                (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                  ((BoundedUnits.boundedUnitIndexUpper (K := K)
                      (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
                    (2 * Q))) ^
                  NumberField.Units.rank K) /
                (totallyRealDegreeEightUnitLogGap / 8) ^
                  NumberField.Units.rank K := by
  dsimp only
  obtain ⟨hB, hindex, a, ha⟩ :=
    degreeEight_boundedUnitExponentData K hdeg hdisc q
  refine ⟨hB, hindex, a, fun i ↦ (ha i).trans ?_⟩
  have hlog := numberField_logEmbedding_norm_le_two_logHeight K q
  have hnorm :
      ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖ ≤ 2 * Q :=
    hlog.trans (mul_le_mul_of_nonneg_left hq (by norm_num))
  have hindexR :
      ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) ≤
        BoundedUnits.boundedUnitIndexUpper (K := K)
          (totallyRealDegreeEightUnitLogGap / 8)
          (boundedUnitMinkowskiNatBound N) := by
    exact_mod_cast hindex
  have hproduct :
      ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
          ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖ ≤
        (BoundedUnits.boundedUnitIndexUpper (K := K)
          (totallyRealDegreeEightUnitLogGap / 8)
          (boundedUnitMinkowskiNatBound N) : ℝ) * (2 * Q) :=
    mul_le_mul hindexR hnorm (norm_nonneg _)
      (Nat.cast_nonneg _)
  have hmax :
      max (BoundedUnits.commonBoundedUnitLogBound (K := K)
          (boundedUnitMinkowskiNatBound N))
          (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
            ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖) ≤
        max (BoundedUnits.commonBoundedUnitLogBound (K := K)
          (boundedUnitMinkowskiNatBound N))
          ((BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8)
            (boundedUnitMinkowskiNatBound N) : ℝ) * (2 * Q)) :=
    max_le_max_left _ hproduct
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hmax _) (Nat.cast_nonneg _))
    (pow_nonneg (le_of_lt (div_pos totallyRealDegreeEightUnitLogGap_pos
      (by norm_num))) _)

/-- Height-only bounded-unit data with the product identity retained.
There are no field-dependent constants left in either the generators or
their exponent vector. -/
theorem degreeEight_boundedUnitDecompositionData_of_logHeight
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {N : ℕ}
    (hdisc : |NumberField.discr K| ≤ N)
    (q : (NumberField.RingOfIntegers K)ˣ) {Q : ℝ}
    (hQ : 0 ≤ Q)
    (hq : Height.logHeight₁
      (((q : NumberField.RingOfIntegers K) : K)) ≤ Q) :
    let B := boundedUnitMinkowskiNatBound N
    ∃ hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
        NumberField.mixedEmbedding.convexBodyLTFactor K * B,
      (BoundedUnits.boundedUnitSubgroup hB).index ≤
          BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B ∧
        ∃ (ζ : NumberField.Units.torsion K)
            (a : Fin (NumberField.Units.rank K) →₀ ℤ),
          q ^ (BoundedUnits.boundedUnitSubgroup hB).index =
              ζ.1 * a.prod (fun i z ↦
                BoundedUnits.boundedFundSystem hB i ^ z) ∧
            ∀ i,
              |((a i : ℤ) : ℝ)| ≤
                ((NumberField.Units.rank K).factorial *
                  (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                    ((BoundedUnits.boundedUnitIndexUpper (K := K)
                        (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
                      (2 * Q))) ^
                    NumberField.Units.rank K) /
                  (totallyRealDegreeEightUnitLogGap / 8) ^
                    NumberField.Units.rank K := by
  dsimp only
  obtain ⟨hB, hindex, ζ, a, hdecomp, ha⟩ :=
    degreeEight_boundedUnitDecompositionData K hdeg hdisc q
  refine ⟨hB, hindex, ζ, a, hdecomp, fun i ↦ (ha i).trans ?_⟩
  have hlog := numberField_logEmbedding_norm_le_two_logHeight K q
  have hnorm :
      ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖ ≤ 2 * Q :=
    hlog.trans (mul_le_mul_of_nonneg_left hq (by norm_num))
  have hindexR :
      ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) ≤
        BoundedUnits.boundedUnitIndexUpper (K := K)
          (totallyRealDegreeEightUnitLogGap / 8)
          (boundedUnitMinkowskiNatBound N) := by
    exact_mod_cast hindex
  have hproduct :
      ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
          ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖ ≤
        (BoundedUnits.boundedUnitIndexUpper (K := K)
          (totallyRealDegreeEightUnitLogGap / 8)
          (boundedUnitMinkowskiNatBound N) : ℝ) * (2 * Q) :=
    mul_le_mul hindexR hnorm (norm_nonneg _) (Nat.cast_nonneg _)
  have hmax :
      max (BoundedUnits.commonBoundedUnitLogBound (K := K)
          (boundedUnitMinkowskiNatBound N))
          (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
            ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖) ≤
        max (BoundedUnits.commonBoundedUnitLogBound (K := K)
          (boundedUnitMinkowskiNatBound N))
          ((BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8)
            (boundedUnitMinkowskiNatBound N) : ℝ) * (2 * Q)) :=
    max_le_max_left _ hproduct
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hmax _) (Nat.cast_nonneg _))
    (pow_nonneg (le_of_lt (div_pos totallyRealDegreeEightUnitLogGap_pos
      (by norm_num))) _)

/-- Height-controlled bounded-unit decomposition at any supplied admissible
Minkowski cutoff.  This variant lets the degree-eight Pell field use the
polynomial cutoff `degreeEightMinkowskiNatBound`. -/
theorem degreeEight_boundedUnitDecompositionData_at_of_logHeight
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (q : (NumberField.RingOfIntegers K)ˣ) {Q : ℝ}
    (_hQ : 0 ≤ Q)
    (hq : Height.logHeight₁
      (((q : NumberField.RingOfIntegers K) : K)) ≤ Q) :
    (BoundedUnits.boundedUnitSubgroup hB).index ≤
        BoundedUnits.boundedUnitIndexUpper (K := K)
          (totallyRealDegreeEightUnitLogGap / 8) B ∧
      ∃ (ζ : NumberField.Units.torsion K)
          (a : Fin (NumberField.Units.rank K) →₀ ℤ),
        q ^ (BoundedUnits.boundedUnitSubgroup hB).index =
            ζ.1 * a.prod (fun i z ↦
              BoundedUnits.boundedFundSystem hB i ^ z) ∧
          ∀ i,
            |((a i : ℤ) : ℝ)| ≤
              ((NumberField.Units.rank K).factorial *
                (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                  ((BoundedUnits.boundedUnitIndexUpper (K := K)
                      (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
                    (2 * Q))) ^ NumberField.Units.rank K) /
                (totallyRealDegreeEightUnitLogGap / 8) ^
                  NumberField.Units.rank K := by
  classical
  have hδ : 0 < totallyRealDegreeEightUnitLogGap / 8 :=
    div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num)
  have hreg := totallyRealDegreeEight_regulator_lower hdeg
  have hindex := BoundedUnits.boundedUnitSubgroup_index_le hB hδ hreg
  obtain ⟨ζ, a, hdecomp, ha⟩ :=
    BoundedUnits.boundedUnit_pow_decomposition_with_exponent_le_unpowered
      hB hδ hreg q
  refine ⟨hindex, ζ, a, hdecomp, fun i ↦ (ha i).trans ?_⟩
  have hlog := numberField_logEmbedding_norm_le_two_logHeight K q
  have hnorm :
      ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖ ≤ 2 * Q :=
    hlog.trans (mul_le_mul_of_nonneg_left hq (by norm_num))
  have hindexR :
      ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) ≤
        BoundedUnits.boundedUnitIndexUpper (K := K)
          (totallyRealDegreeEightUnitLogGap / 8) B := by
    exact_mod_cast hindex
  have hproduct :
      ((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
          ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖ ≤
        (BoundedUnits.boundedUnitIndexUpper (K := K)
          (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) * (2 * Q) :=
    mul_le_mul hindexR hnorm (norm_nonneg _) (Nat.cast_nonneg _)
  have hmax :
      max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
          (((BoundedUnits.boundedUnitSubgroup hB).index : ℝ) *
            ‖NumberField.Units.logEmbedding K (Additive.ofMul q)‖) ≤
        max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
          ((BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) * (2 * Q)) :=
    max_le_max_left _ hproduct
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hmax _) (Nat.cast_nonneg _))
    (pow_nonneg hδ.le _)

/-- Full supported-unit decomposition at a supplied admissible degree-eight
cutoff, retaining the finite-prime coordinates and a uniform exponent
majorant for the bounded ordinary-unit basis. -/
theorem numberField_supportedUnit_boundedUnit_decomposition_at
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K)
        (ζ : NumberField.Units.torsion K)
        (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
            (q : Kˣ) ∧
        (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
        (BoundedUnits.boundedUnitSubgroup hB).index ≤
          BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B ∧
        (SupportedUnits.emptyEquivUnits K q) ^
            (BoundedUnits.boundedUnitSubgroup hB).index =
          ζ.1 * a.prod (fun i z ↦
            BoundedUnits.boundedFundSystem hB i ^ z) ∧
        let Q :=
          (NumberField.classNumber K : ℝ) *
              Height.logHeight₁ (((u : Kˣ) : K)) +
            ∑ v, (e v).natAbs * Height.logHeight₁
              ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))
        ∀ i,
          |((a i : ℤ) : ℝ)| ≤
            ((NumberField.Units.rank K).factorial *
              (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                ((BoundedUnits.boundedUnitIndexUpper (K := K)
                    (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
                  (2 * Q))) ^ NumberField.Units.rank K) /
              (totallyRealDegreeEightUnitLogGap / 8) ^
                NumberField.Units.rank K := by
  classical
  obtain ⟨e, q, hpow, he⟩ :=
    SupportedUnits.exists_primeClassProduct_mul_emptySupportedUnit_eq_pow S u
  let Q : ℝ :=
    (NumberField.classNumber K : ℝ) *
        Height.logHeight₁ (((u : Kˣ) : K)) +
      ∑ v, (e v).natAbs * Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Height.zero_le_logHeight₁ _))
      (Finset.sum_nonneg fun v _ ↦
        mul_nonneg (Nat.cast_nonneg _) (Height.zero_le_logHeight₁ _))
  have hqHeight :
      Height.logHeight₁
          ((((SupportedUnits.emptyEquivUnits K q) :
            NumberField.RingOfIntegers K) : K)) ≤ Q :=
    numberField_residualOrdinaryUnit_logHeight_le S u e q hpow
  obtain ⟨hindex, ζ, a, hdecomp, ha⟩ :=
    degreeEight_boundedUnitDecompositionData_at_of_logHeight
      K hdeg hB (SupportedUnits.emptyEquivUnits K q) hQ hqHeight
  exact ⟨e, q, ζ, a, hpow, he, hindex, hdecomp, by simpa [Q] using ha⟩

/-- Full explicit supported-unit decomposition in a totally real
degree-eight field.  The residual ordinary unit is expanded in bounded
generators, and its exponent majorant contains only the original
supported-unit height, finite-prime generator heights, and explicit
discriminant functions. -/
theorem numberField_supportedUnit_boundedUnit_decomposition_explicit
    (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K)
    (hdeg : Module.finrank ℚ K ≤ 8) {N : ℕ}
    (hdisc : |NumberField.discr K| ≤ N) :
    let B := boundedUnitMinkowskiNatBound N
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K)
        (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
          NumberField.mixedEmbedding.convexBodyLTFactor K * B)
        (ζ : NumberField.Units.torsion K)
        (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
          (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
            (q : Kˣ) ∧
        (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
        (BoundedUnits.boundedUnitSubgroup hB).index ≤
          BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B ∧
        (SupportedUnits.emptyEquivUnits K q) ^
            (BoundedUnits.boundedUnitSubgroup hB).index =
          ζ.1 * a.prod (fun i z ↦
            BoundedUnits.boundedFundSystem hB i ^ z) ∧
        let Q :=
          (NumberField.classNumber K : ℝ) *
              Height.logHeight₁ (((u : Kˣ) : K)) +
            ∑ v, (e v).natAbs * Height.logHeight₁
              ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))
        ∀ i,
          |((a i : ℤ) : ℝ)| ≤
            ((NumberField.Units.rank K).factorial *
              (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                ((BoundedUnits.boundedUnitIndexUpper (K := K)
                    (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
                  (2 * Q))) ^
                NumberField.Units.rank K) /
              (totallyRealDegreeEightUnitLogGap / 8) ^
                NumberField.Units.rank K := by
  dsimp only
  obtain ⟨e, q, hpow, he⟩ :=
    SupportedUnits.exists_primeClassProduct_mul_emptySupportedUnit_eq_pow S u
  let Q : ℝ :=
    (NumberField.classNumber K : ℝ) *
        Height.logHeight₁ (((u : Kˣ) : K)) +
      ∑ v, (e v).natAbs * Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Height.zero_le_logHeight₁ _))
      (Finset.sum_nonneg fun v _ ↦
        mul_nonneg (Nat.cast_nonneg _) (Height.zero_le_logHeight₁ _))
  have hqHeight :
      Height.logHeight₁
          ((((SupportedUnits.emptyEquivUnits K q) :
            NumberField.RingOfIntegers K) : K)) ≤ Q := by
    exact numberField_residualOrdinaryUnit_logHeight_le S u e q hpow
  obtain ⟨hB, hindex, ζ, a, hdecomp, ha⟩ :=
    degreeEight_boundedUnitDecompositionData_of_logHeight K hdeg hdisc
      (SupportedUnits.emptyEquivUnits K q) hQ hqHeight
  exact ⟨e, q, hB, ζ, a, hpow, he, hindex, hdecomp, by simpa [Q] using ha⟩

/-- Combining the class-number supported-unit identity with the bounded
ordinary-unit identity gives one ambient-field product for a single
positive power of the original supported unit.  This is the exact
algebraic product to which the archimedean logarithmic-form estimate is
applied. -/
theorem supportedUnit_powered_bounded_product
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
        (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    (u : Kˣ) ^ (NumberField.classNumber K *
        (BoundedUnits.boundedUnitSubgroup hB).index) =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) ^
          (BoundedUnits.boundedUnitSubgroup hB).index *
        Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1 *
        a.prod (fun i z ↦
          (Units.map (algebraMap
            (NumberField.RingOfIntegers K) K).toMonoidHom
              (BoundedUnits.boundedFundSystem hB i)) ^ z) := by
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ :=
    SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  have hqmap :
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (SupportedUnits.emptyEquivUnits K q) = (q : Kˣ) :=
    SupportedUnits.unitsMap_emptyEquivUnits
      (R := NumberField.RingOfIntegers K) K q
  have hdecompK := congrArg
    (Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom) hdecomp
  simp only [map_pow, hqmap, map_mul, map_finsuppProd, map_zpow] at hdecompK
  calc
    (u : Kˣ) ^ (NumberField.classNumber K * I) =
        ((u : Kˣ) ^ NumberField.classNumber K) ^ I := by rw [pow_mul]
    _ = (P * (q : Kˣ)) ^ I := by rw [hpow]
    _ = P ^ I * (q : Kˣ) ^ I := mul_pow _ _ _
    _ = P ^ I *
        (Units.map (algebraMap
          (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1 *
          a.prod (fun i z ↦
            (Units.map (algebraMap
              (NumberField.RingOfIntegers K) K).toMonoidHom
                (BoundedUnits.boundedFundSystem hB i)) ^ z)) := by
      rw [hdecompK]
    _ = _ := by simp [I, P, mul_assoc]

/-- After one further square, the bounded-generator identity has no torsion
factor.  In the three-radical field its right-hand side is therefore one
finite-prime factor followed by at most seven bounded unit factors. -/
theorem supportedUnit_powered_bounded_product_torsion_free
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
        (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    (u : Kˣ) ^ ((NumberField.classNumber K *
        (BoundedUnits.boundedUnitSubgroup hB).index) * 2) =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) ^
          ((BoundedUnits.boundedUnitSubgroup hB).index * 2) *
        (a.prod (fun i z ↦
          (Units.map (algebraMap
            (NumberField.RingOfIntegers K) K).toMonoidHom
              (BoundedUnits.boundedFundSystem hB i)) ^ z)) ^ 2 := by
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ :=
    SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  let Z : Kˣ :=
    Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1
  let G : Kˣ :=
    a.prod (fun i z ↦
      (Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)) ^ z)
  have hbase := supportedUnit_powered_bounded_product
    S u e q B hB ζ a hpow hdecomp
  have hZ : Z ^ 2 = 1 := by
    dsimp [Z]
    rw [← map_pow]
    rw [totallyReal_torsion_sq_eq_one ζ, map_one]
  calc
    (u : Kˣ) ^ ((NumberField.classNumber K * I) * 2) =
        ((u : Kˣ) ^ (NumberField.classNumber K * I)) ^ 2 := by
      rw [pow_mul]
    _ = (P ^ I * Z * G) ^ 2 := by rw [hbase]
    _ = P ^ (I * 2) * G ^ 2 := by
      rw [mul_pow, mul_pow, hZ, mul_one, pow_mul]
    _ = _ := by rfl

/-- The torsion-free powered identity, after also adjoining a rational
factor, is already a product of squares.  All its bases are therefore
positive in every real embedding. -/
lemma two_power_product_identity
    {G : Type*} [CommGroup G] {r h I : ℕ}
    (ratio U P : G) (a : Fin r →₀ ℤ) (eps : Fin r → G)
    (hU : U ^ ((h * I) * 2) =
      P ^ (I * 2) * (a.prod (fun i z ↦ eps i ^ z)) ^ 2) :
    (ratio * U) ^ ((h * I) * 2) =
      (ratio ^ 2) ^ (h * I) *
        ((P ^ 2) ^ I * ∏ i, (eps i ^ 2) ^ (a i)) := by
  rw [mul_pow, hU, finsupp_prod_zpow_sq]
  rw [pow_mul, pow_mul]
  group

/-- The squared rational factor, squared finite-prime factor, and squared
bounded unit generators, arranged as one finite vector. -/
def squaredProductBases
    {G : Type*} [Monoid G] {r : ℕ}
    (ratio P : G) (eps : Fin r → G) : Fin (r + 2) → G :=
  Fin.cases (ratio ^ 2) (Fin.cases (P ^ 2) (fun i ↦ eps i ^ 2))

/-- The coefficient vector corresponding to `squaredProductBases`. -/
def squaredProductCoefficients
    {r : ℕ} (h I : ℕ) (a : Fin r →₀ ℤ) : Fin (r + 2) → ℤ :=
  Fin.cases ((h * I : ℕ) : ℤ) (Fin.cases (I : ℤ) (fun i ↦ a i))

/-- Combine the two possibly nonintegral square bases into the single
element which actually occurs in the powered Pell identity.  This reduces
the logarithmic form to one quotient direction plus the maximal-rank unit
directions. -/
def combinedSquaredProductBases
    {G : Type*} [Monoid G] {r : ℕ}
    (W : G) (eps : Fin r → G) : Fin (r + 1) → G :=
  Fin.cases W (fun i ↦ eps i ^ 2)

/-- Coefficients for the combined product: the combined leading factor has
coefficient one and the bounded-unit squares retain their exponents. -/
def combinedSquaredProductCoefficients
    {r : ℕ} (a : Fin r →₀ ℤ) : Fin (r + 1) → ℤ :=
  Fin.cases 1 (fun i ↦ a i)

lemma prod_combinedSquaredProductBases_zpow
    {G : Type*} [CommGroup G] {r : ℕ}
    (W : G) (eps : Fin r → G) (a : Fin r →₀ ℤ) :
    ∏ i, combinedSquaredProductBases W eps i ^
        combinedSquaredProductCoefficients a i =
      W * ∏ i, (eps i ^ 2) ^ (a i) := by
  rw [Fin.prod_univ_succ]
  simp [combinedSquaredProductBases, combinedSquaredProductCoefficients]

/-- Coercing a combined product identity from field units to the field
preserves the combined bases and coefficients. -/
lemma combinedProduct_units_coe
    {K : Type*} [Field K] {r m : ℕ}
    (W z : Kˣ) (eps : Fin r → Kˣ) (a : Fin r →₀ ℤ)
    (h : z ^ m = ∏ i, combinedSquaredProductBases W eps i ^
      combinedSquaredProductCoefficients a i) :
    (z : K) ^ m = ∏ i,
      combinedSquaredProductBases (W : K) (fun j ↦ (eps j : K)) i ^
        combinedSquaredProductCoefficients a i := by
  have hv := congrArg (Units.val : Kˣ → K) h
  push_cast at hv
  have hcoe : ∀ i,
      ((combinedSquaredProductBases W eps i : Kˣ) : K) =
        combinedSquaredProductBases (W : K) (fun j ↦ (eps j : K)) i := by
    intro i
    refine Fin.cases rfl (fun j ↦ ?_) i
    change ((eps j ^ 2 : Kˣ) : K) = (eps j : K) ^ 2
    rfl
  simpa only [hcoe] using hv

/-- Coercion of a product of squared field units to the ambient field. -/
lemma squaredUnitsProduct_coe
    {K : Type*} [Field K] {r m : ℕ}
    (z : Kˣ) (eps : Fin r → Kˣ) (b : Fin r → ℤ)
    (h : z ^ m = ∏ i, (eps i ^ 2) ^ b i) :
    (z : K) ^ m = ∏ i, ((eps i : K) ^ 2) ^ b i := by
  have hv := congrArg (Units.val : Kˣ → K) h
  push_cast at hv
  exact hv

/-- Logarithmic height of the combined leading factor, in terms of the
two original factors and their natural exponents. -/
lemma combinedLeadingFactor_logHeight_le
    {K : Type*} [Field K] [NumberField K]
    (ratio P : K) (h I : ℕ) {R Q : ℝ}
    (hratio : Height.logHeight₁ ratio ≤ R)
    (hP : Height.logHeight₁ P ≤ Q) :
    Height.logHeight₁
        ((ratio ^ 2) ^ (h * I) * (P ^ 2) ^ I) ≤
      (2 * (h * I) : ℕ) * R + (2 * I : ℕ) * Q := by
  calc
    Height.logHeight₁ ((ratio ^ 2) ^ (h * I) * (P ^ 2) ^ I) ≤
        Height.logHeight₁ ((ratio ^ 2) ^ (h * I)) +
          Height.logHeight₁ ((P ^ 2) ^ I) :=
      Height.logHeight₁_mul_le _ _
    _ = (2 * (h * I) : ℕ) * Height.logHeight₁ ratio +
          (2 * I : ℕ) * Height.logHeight₁ P := by
      rw [← pow_mul, ← pow_mul, Height.logHeight₁_pow, Height.logHeight₁_pow]
    _ ≤ (2 * (h * I) : ℕ) * R + (2 * I : ℕ) * Q := by
      gcongr

/-- The combined leading factor is positive at every real embedding,
because it is built only from even powers of nonzero factors. -/
lemma combinedLeadingFactor_positive
    {K : Type*} [Field K] (ρ : K →+* ℝ)
    (ratio P : K) (h I : ℕ) (hratio : ratio ≠ 0) (hP : P ≠ 0) :
    0 < ρ ((ratio ^ 2) ^ (h * I) * (P ^ 2) ^ I) := by
  rw [map_mul, map_pow, map_pow, map_pow, map_pow]
  exact mul_pos (pow_pos (sq_pos_of_ne_zero ((map_ne_zero ρ).2 hratio)) _)
    (pow_pos (sq_pos_of_ne_zero ((map_ne_zero ρ).2 hP)) _)

lemma combinedSquaredProductBases_positive
    {K : Type*} [Field K] {r : ℕ}
    (ρ : K →+* ℝ) {W : K} (hW : 0 < ρ W)
    (eps : Fin r → K) (heps : ∀ i, eps i ≠ 0) :
    ∀ i, 0 < ρ (combinedSquaredProductBases W eps i) := by
  intro i
  refine Fin.cases hW (fun j ↦ ?_) i
  change 0 < ρ (eps j ^ 2)
  rw [map_pow]
  exact sq_pos_of_ne_zero ((map_ne_zero ρ).2 (heps j))

/-- The principal logarithmic form for the combined package is the real
logarithm of its positive powered product. -/
lemma combined_positive_linear_form_eq_log_power
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (ρ : K →+* ℝ)
    (hφρ : ∀ x, φ x = (ρ x : ℂ))
    {r m : ℕ} (W z : K) (eps : Fin r → K)
    (hW : 0 < ρ W) (heps : ∀ i, eps i ≠ 0)
    (a : Fin r →₀ ℤ)
    (hpack : z ^ m = ∏ i, combinedSquaredProductBases W eps i ^
      combinedSquaredProductCoefficients a i) :
    (∑ i, (combinedSquaredProductCoefficients a i : ℂ) *
        Complex.log (φ (combinedSquaredProductBases W eps i))) =
      (Real.log (ρ (z ^ m)) : ℂ) := by
  let alpha : Fin (r + 1) → K := combinedSquaredProductBases W eps
  let q : Fin (r + 1) → ℝ := fun i ↦ ρ (alpha i)
  have hq : ∀ i, 0 < q i := by
    intro i
    exact combinedSquaredProductBases_positive ρ hW eps heps i
  have hlog := numberField_positive_linear_form_eq_log_product
    φ alpha q hq (fun i ↦ hφρ (alpha i))
      (combinedSquaredProductCoefficients a)
  rw [← hpack] at hlog
  have hzpow : 0 < ρ (z ^ m) := by
    rw [hpack, map_prod]
    exact Finset.prod_pos fun i _hi ↦ by
      simpa using zpow_pos (hq i)
        (combinedSquaredProductCoefficients a i)
  rw [hlog, hφρ, ← Complex.ofReal_log hzpow.le]

lemma units_rank_le_finrank
    (K : Type*) [Field K] [NumberField K] :
    NumberField.Units.rank K ≤ Module.finrank ℚ K := by
  unfold NumberField.Units.rank
  calc
    Fintype.card (NumberField.InfinitePlace K) - 1 ≤
        Fintype.card (NumberField.InfinitePlace K) := Nat.sub_le _ _
    _ ≤ Module.finrank ℚ K := by
      rw [← NumberField.InfinitePlace.sum_mult_eq]
      calc
        Fintype.card (NumberField.InfinitePlace K) =
            ∑ _w : NumberField.InfinitePlace K, 1 := by simp
        _ ≤ ∑ w : NumberField.InfinitePlace K, w.mult :=
          Finset.sum_le_sum fun w _ ↦
            Nat.one_le_iff_ne_zero.mpr
              NumberField.InfinitePlace.mult_ne_zero

/-- Fixed-rank logarithmic-form lower bound for the nonintegral combined
factor case.  The leading coefficient is one, while the remaining bases
are the squared bounded fundamental units. -/
theorem nonintegerUnit_combined_logarithmic_form_lower_bound
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Fintype ι]
    (basis : Module.Basis ι ℚ K) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : K →+* ℂ)
    {B0 B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (W : Kˣ) (hW : W ∉ integerUnitSubgroup K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (M : ℝ) (hd : Module.finrank ℚ K ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : K →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hBone : 1 ≤ B) (ha : ∀ i, (a i).natAbs ≤ B) :
    let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
      ((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
    let alpha := combinedSquaredProductBases (W : K) eps
    let ell : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
      Complex.log (φ (alpha i))
    LinearForms.structuredBoxLogarithmicFormThreshold B
        (LinearForms.structuredBoxMasterL B M alpha ell) M alpha ell ≤
      ‖∑ i, (combinedSquaredProductCoefficients a i : ℂ) * ell i‖ := by
  dsimp only
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  let alpha : Fin (NumberField.Units.rank K + 1) → K :=
    combinedSquaredProductBases (W : K) (fun i ↦ (eps i : K))
  let ell : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
    Complex.log (φ (alpha i))
  apply LinearForms.structured_box_logarithmic_form_lower_bound_at_master
    basis hbasis φ alpha ell (combinedSquaredProductCoefficients a) M
  · exact (units_rank_le_finrank K).trans hd
  · exact hd
  · exact hM
  · exact hMbasis
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [combinedSquaredProductCoefficients] using hBone
    · simpa [combinedSquaredProductCoefficients] using ha j
  · simp [combinedSquaredProductCoefficients]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact W.ne_zero
    · change (eps j : K) ^ 2 ≠ 0
      exact pow_ne_zero _ (Units.ne_zero (eps j))
  · intro N _hN
    exact boundedFundSystem_adjoin_boxMonomial_sq_injective hB W hW N
  · intro N x
    have hexp := LinearForms.exp_boxLinearForm_log
      (fun i ↦ φ (alpha i)) (fun i ↦ (map_ne_zero φ).2
        (by
          refine Fin.cases W.ne_zero (fun j ↦ ?_) i
          change (eps j : K) ^ 2 ≠ 0
          exact pow_ne_zero _ (Units.ne_zero (eps j)))) x
    simpa [ell, alpha, LinearForms.boxMonomial, map_prod, map_pow, eps]
      using hexp

/-- At a compatible real embedding, the noninteger-unit combined lower
bound is exactly a lower bound for the absolute real logarithm of the
powered Pell product. -/
theorem nonintegerUnit_combined_real_log_lower_bound
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Fintype ι]
    (basis : Module.Basis ι ℚ K) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : K →+* ℂ) (ρ : K →+* ℝ) (hφρ : ∀ x, φ x = (ρ x : ℂ))
    {B0 B m : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (W : Kˣ) (hW : W ∉ integerUnitSubgroup K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ) (z : K)
    (M : ℝ) (hd : Module.finrank ℚ K ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : K →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hBone : 1 ≤ B) (ha : ∀ i, (a i).natAbs ≤ B)
    (hWpos : 0 < ρ (W : K))
    (hpack : z ^ m = ∏ i,
      combinedSquaredProductBases (W : K)
          (fun j ↦ ((Units.map
            (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
              (BoundedUnits.boundedFundSystem hB j) : Kˣ) : K)) i ^
        combinedSquaredProductCoefficients a i) :
    let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
      ((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
    let alpha := combinedSquaredProductBases (W : K) eps
    let ell : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
      Complex.log (φ (alpha i))
    LinearForms.structuredBoxLogarithmicFormThreshold B
        (LinearForms.structuredBoxMasterL B M alpha ell) M alpha ell ≤
      |Real.log (ρ (z ^ m))| := by
  dsimp only
  let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
    ((Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
  let alpha := combinedSquaredProductBases (W : K) eps
  let ell : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
    Complex.log (φ (alpha i))
  have hlower := nonintegerUnit_combined_logarithmic_form_lower_bound
    basis hbasis φ hB W hW a M hd hM hMbasis hBone ha
  have hlog := combined_positive_linear_form_eq_log_power
    φ ρ hφρ (W : K) z eps hWpos
      (fun i ↦ Units.ne_zero _) a hpack
  have hlog' :
      (∑ i, (combinedSquaredProductCoefficients a i : ℂ) * ell i) =
        (Real.log (ρ (z ^ m)) : ℂ) := by
    simpa [ell, alpha] using hlog
  dsimp only at hlower
  rw [hlog'] at hlower
  simpa [Real.norm_eq_abs, alpha, ell, eps] using hlower

/-- If the leading combined factor is an algebraic-integer unit, its
controlled powered decomposition leaves a nonzero logarithmic form solely
in the squared bounded fundamental units.  A finite permutation moves a
nonzero coefficient to the distinguished coordinate. -/
theorem integerUnit_bounded_logarithmic_form_lower_bound
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Fintype ι]
    (basis : Module.Basis ι ℚ K) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : K →+* ℂ) {B0 B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (b : Fin (NumberField.Units.rank K) → ℤ)
    (M : ℝ) (hd : Module.finrank ℚ K ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : K →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hb : ∀ i, (b i).natAbs ≤ B) (hbne : b ≠ 0) :
    let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
      ((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
    let alpha : Fin (NumberField.Units.rank K) → K := fun i ↦ eps i ^ 2
    let ell : Fin (NumberField.Units.rank K) → ℂ := fun i ↦
      Complex.log (φ (alpha i))
    ∃ e : Fin (NumberField.Units.rank K - 1 + 1) ≃
        Fin (NumberField.Units.rank K),
      LinearForms.structuredBoxLogarithmicFormThreshold B
          (LinearForms.structuredBoxMasterL B M (fun i ↦ alpha (e i))
            (fun i ↦ ell (e i))) M
          (fun i ↦ alpha (e i)) (fun i ↦ ell (e i)) ≤
        ‖∑ i, (b i : ℂ) * ell i‖ := by
  dsimp only
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  let alpha : Fin (NumberField.Units.rank K) → K := fun i ↦ (eps i : K) ^ 2
  let ell : Fin (NumberField.Units.rank K) → ℂ := fun i ↦
    Complex.log (φ (alpha i))
  have hj : ∃ j, b j ≠ 0 := by
    by_contra h
    apply hbne
    funext i
    exact not_ne_iff.mp (fun hi ↦ h ⟨i, hi⟩)
  obtain ⟨j, hj⟩ := hj
  have hrank : 0 < NumberField.Units.rank K := by
    simpa using Fintype.card_pos_iff.mpr ⟨j⟩
  have heq : NumberField.Units.rank K - 1 + 1 =
      NumberField.Units.rank K := by omega
  let e0 : Fin (NumberField.Units.rank K - 1 + 1) ≃
      Fin (NumberField.Units.rank K) := finCongr heq
  let e : Fin (NumberField.Units.rank K - 1 + 1) ≃
      Fin (NumberField.Units.rank K) := e0.trans (Equiv.swap (e0 0) j)
  have he0 : e 0 = j := by
    simp [e, e0]
  refine ⟨e, ?_⟩
  apply LinearForms.structured_box_logarithmic_form_lower_bound_at_master_reindex
    basis hbasis φ e alpha ell b M
  · have hr := (units_rank_le_finrank K).trans hd
    omega
  · exact hd
  · exact hM
  · exact hMbasis
  · exact hb
  · rwa [he0]
  · intro i
    dsimp [alpha]
    exact pow_ne_zero _ (Units.ne_zero (eps i))
  · intro N _hN
    simpa [alpha, eps] using
      boundedFundSystem_boxMonomial_sq_injective hB N
  · intro N x
    have hexp := LinearForms.exp_boxLinearForm_log
      (fun i ↦ φ (alpha i))
      (fun i ↦ (map_ne_zero φ).2
        (pow_ne_zero _ (Units.ne_zero (eps i)))) x
    simpa [ell, alpha, LinearForms.boxMonomial, map_prod, map_pow, eps]
      using hexp

/-- The integer-unit logarithmic-form estimate at a compatible real
embedding, rewritten as a lower bound for the absolute real logarithm of
the powered product. -/
theorem integerUnit_bounded_real_log_lower_bound
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Fintype ι]
    (basis : Module.Basis ι ℚ K) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : K →+* ℂ) (ρ : K →+* ℝ) (hφρ : ∀ x, φ x = (ρ x : ℂ))
    {B0 B m : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (b : Fin (NumberField.Units.rank K) → ℤ) (z : K)
    (M : ℝ) (hd : Module.finrank ℚ K ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : K →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hb : ∀ i, (b i).natAbs ≤ B) (hbne : b ≠ 0)
    (hpack : z ^ m = ∏ i,
      (((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K) ^ 2) ^ b i) :
    let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
      ((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
    let alpha : Fin (NumberField.Units.rank K) → K := fun i ↦ eps i ^ 2
    let ell : Fin (NumberField.Units.rank K) → ℂ := fun i ↦
      Complex.log (φ (alpha i))
    ∃ e : Fin (NumberField.Units.rank K - 1 + 1) ≃
        Fin (NumberField.Units.rank K),
      LinearForms.structuredBoxLogarithmicFormThreshold B
          (LinearForms.structuredBoxMasterL B M (fun i ↦ alpha (e i))
            (fun i ↦ ell (e i))) M
          (fun i ↦ alpha (e i)) (fun i ↦ ell (e i)) ≤
        |Real.log (ρ (z ^ m))| := by
  dsimp only
  let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
    ((Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
  let alpha : Fin (NumberField.Units.rank K) → K := fun i ↦ eps i ^ 2
  let ell : Fin (NumberField.Units.rank K) → ℂ := fun i ↦
    Complex.log (φ (alpha i))
  have hepspos : ∀ i, 0 < ρ (alpha i) := by
    intro i
    dsimp [alpha, eps]
    rw [map_pow]
    exact sq_pos_of_ne_zero ((map_ne_zero ρ).2
      ((map_ne_zero_iff (algebraMap (NumberField.RingOfIntegers K) K)
        (FaithfulSMul.algebraMap_injective
          (NumberField.RingOfIntegers K) K)).2 (Units.ne_zero _)))
  obtain ⟨e, hlower⟩ := integerUnit_bounded_logarithmic_form_lower_bound
    basis hbasis φ hB b M hd hM hMbasis hb hbne
  have hlog := numberField_positive_linear_form_eq_log_product
    φ alpha (fun i ↦ ρ (alpha i)) hepspos
      (fun i ↦ hφρ (alpha i)) b
  rw [← hpack] at hlog
  have hzpos : 0 < ρ (z ^ m) := by
    rw [hpack, map_prod]
    exact Finset.prod_pos fun i _hi ↦ by
      simpa [alpha, eps, map_pow] using zpow_pos (hepspos i) (b i)
  have hlog' : (∑ i, (b i : ℂ) * ell i) =
      (Real.log (ρ (z ^ m)) : ℂ) := by
    rw [hlog]
    rw [hφρ, ← Complex.ofReal_log hzpos.le]
  refine ⟨e, ?_⟩
  rw [hlog'] at hlower
  simpa [Real.norm_eq_abs] using hlower

/-- Height majorants matching the three blocks of `squaredProductBases`. -/
def squaredProductHeightMajorants
    {r : ℕ} (R P : ℝ) (E : Fin r → ℝ) : Fin (r + 2) → ℝ :=
  Fin.cases (2 * R) (Fin.cases (2 * P) (fun i ↦ 2 * E i))

/-- A componentwise coefficient bound for the packaged product. -/
lemma squaredProductCoefficients_natAbs_le
    {r h I B : ℕ} (a : Fin r →₀ ℤ)
    (hh : h * I ≤ B) (hI : I ≤ B)
    (ha : ∀ i, (a i).natAbs ≤ B) :
    ∀ i, (squaredProductCoefficients h I a i).natAbs ≤ B := by
  intro i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
  · change Int.natAbs ((h * I : ℕ) : ℤ) ≤ B
    rw [Int.natAbs_natCast]
    exact hh
  · change Int.natAbs (I : ℤ) ≤ B
    simpa using hI
  · change (a k).natAbs ≤ B
    exact ha k

/-- Squaring doubles logarithmic height, component by component in the
packaged product. -/
lemma squaredProductBases_logHeight_le
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (ratio P : K) (eps : Fin r → K) {R Q : ℝ} {E : Fin r → ℝ}
    (hratio : Height.logHeight₁ ratio ≤ R)
    (hP : Height.logHeight₁ P ≤ Q)
    (heps : ∀ i, Height.logHeight₁ (eps i) ≤ E i) :
    ∀ i, Height.logHeight₁ (squaredProductBases ratio P eps i) ≤
      squaredProductHeightMajorants R Q E i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
  · change Height.logHeight₁ (ratio ^ 2) ≤ 2 * R
    rw [Height.logHeight₁_pow]
    norm_num
    linarith
  · change Height.logHeight₁ (P ^ 2) ≤ 2 * Q
    rw [Height.logHeight₁_pow]
    norm_num
    linarith
  · change Height.logHeight₁ (eps k ^ 2) ≤ 2 * E k
    rw [Height.logHeight₁_pow]
    norm_num
    linarith [heps k]

lemma prod_squaredProductBases_zpow
    {G : Type*} [CommGroup G] {r h I : ℕ}
    (ratio P : G) (eps : Fin r → G) (a : Fin r →₀ ℤ) :
    ∏ i, squaredProductBases ratio P eps i ^
        squaredProductCoefficients h I a i =
      (ratio ^ 2) ^ (h * I) *
        ((P ^ 2) ^ I * ∏ i, (eps i ^ 2) ^ (a i)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [squaredProductBases, squaredProductCoefficients,
    Fin.cases_zero, Fin.cases_succ, zpow_natCast]

/-- The original two-leading-base package is exactly the combined package
with leading element `(ratio²)^(hI) (P²)^I`. -/
lemma prod_squaredProductBases_eq_combined
    {G : Type*} [CommGroup G] {r h I : ℕ}
    (ratio P : G) (eps : Fin r → G) (a : Fin r →₀ ℤ) :
    ∏ i, squaredProductBases ratio P eps i ^
        squaredProductCoefficients h I a i =
      ∏ i, combinedSquaredProductBases
          ((ratio ^ 2) ^ (h * I) * (P ^ 2) ^ I) eps i ^
        combinedSquaredProductCoefficients a i := by
  rw [prod_squaredProductBases_zpow,
    prod_combinedSquaredProductBases_zpow]
  group

lemma two_power_eq_packaged_product
    {G : Type*} [CommGroup G] {r h I : ℕ}
    (ratio U P : G) (a : Fin r →₀ ℤ) (eps : Fin r → G)
    (hU : U ^ ((h * I) * 2) =
      P ^ (I * 2) * (a.prod (fun i z ↦ eps i ^ z)) ^ 2) :
    (ratio * U) ^ ((h * I) * 2) =
      ∏ i, squaredProductBases ratio P eps i ^
        squaredProductCoefficients h I a i := by
  rw [prod_squaredProductBases_zpow]
  exact two_power_product_identity ratio U P a eps hU

/-- The same torsion-free identity after combining its two leading square
bases into the one element that occurs with coefficient one. -/
lemma two_power_eq_combined_product
    {G : Type*} [CommGroup G] {r h I : ℕ}
    (ratio U P : G) (a : Fin r →₀ ℤ) (eps : Fin r → G)
    (hU : U ^ ((h * I) * 2) =
      P ^ (I * 2) * (a.prod (fun i z ↦ eps i ^ z)) ^ 2) :
    (ratio * U) ^ ((h * I) * 2) =
      ∏ i, combinedSquaredProductBases
          ((ratio ^ 2) ^ (h * I) * (P ^ 2) ^ I) eps i ^
        combinedSquaredProductCoefficients a i := by
  rw [← prod_squaredProductBases_eq_combined]
  exact two_power_eq_packaged_product ratio U P a eps hU

lemma squaredProductBases_ne_zero
    {K : Type*} [Field K] {r : ℕ}
    {ratio P : K} (hratio : ratio ≠ 0) (hP : P ≠ 0)
    (eps : Fin r → K) (heps : ∀ i, eps i ≠ 0) :
    ∀ i, squaredProductBases ratio P eps i ≠ 0 := by
  intro i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
  · exact pow_ne_zero 2 hratio
  · exact pow_ne_zero 2 hP
  · exact pow_ne_zero 2 (heps k)

/-- At a real embedding all the packaged squared bases are strictly
positive, so their principal logarithms add without branch corrections. -/
lemma squaredProductBases_positive
    {K : Type*} [Field K] {r : ℕ}
    (ρ : K →+* ℝ) {ratio P : K}
    (hratio : ratio ≠ 0) (hP : P ≠ 0)
    (eps : Fin r → K) (heps : ∀ i, eps i ≠ 0) :
    ∀ i, 0 < ρ (squaredProductBases ratio P eps i) := by
  intro i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
  · simp only [squaredProductBases, Fin.cases_zero, map_pow]
    exact sq_pos_of_ne_zero ((map_ne_zero ρ).2 hratio)
  · simp only [squaredProductBases, Fin.cases_succ, Fin.cases_zero, map_pow]
    exact sq_pos_of_ne_zero ((map_ne_zero ρ).2 hP)
  · simp only [squaredProductBases, Fin.cases_succ, map_pow]
    exact sq_pos_of_ne_zero ((map_ne_zero ρ).2 (heps k))

/-- Explicit componentwise modified-height bounds for the positive packaged
bases. -/
lemma squaredProductBases_modifiedHeight_le
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (ρ : K →+* ℝ)
    (hφρ : ∀ x, φ x = (ρ x : ℂ))
    {r : ℕ} (ratio P : K) (eps : Fin r → K)
    (hratio : ratio ≠ 0) (hP : P ≠ 0) (heps : ∀ i, eps i ≠ 0)
    {R Q : ℝ} {E : Fin r → ℝ}
    (hratioHeight : Height.logHeight₁ ratio ≤ R)
    (hPHeight : Height.logHeight₁ P ≤ Q)
    (hepsHeight : ∀ i, Height.logHeight₁ (eps i) ≤ E i) :
    ∀ i, BakerWustholz.modifiedHeight φ
        (squaredProductBases ratio P eps i) ≤
      max (squaredProductHeightMajorants R Q E i /
          (Module.finrank ℚ K : ℝ))
        (1 / (Module.finrank ℚ K : ℝ)) := by
  intro i
  apply BakerWustholz.modifiedHeight_positiveReal_le_of_logHeight_le
    φ (squaredProductBases_positive ρ hratio hP eps heps i)
    (hφρ _) (squaredProductBases_logHeight_le ratio P eps
      hratioHeight hPHeight hepsHeight i)

lemma prod_squaredProductBases_modifiedHeight_le
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (ρ : K →+* ℝ)
    (hφρ : ∀ x, φ x = (ρ x : ℂ))
    {r : ℕ} (ratio P : K) (eps : Fin r → K)
    (hratio : ratio ≠ 0) (hP : P ≠ 0) (heps : ∀ i, eps i ≠ 0)
    {R Q : ℝ} {E : Fin r → ℝ}
    (hratioHeight : Height.logHeight₁ ratio ≤ R)
    (hPHeight : Height.logHeight₁ P ≤ Q)
    (hepsHeight : ∀ i, Height.logHeight₁ (eps i) ≤ E i) :
    (∏ i, BakerWustholz.modifiedHeight φ
        (squaredProductBases ratio P eps i)) ≤
      ∏ i, max (squaredProductHeightMajorants R Q E i /
          (Module.finrank ℚ K : ℝ))
        (1 / (Module.finrank ℚ K : ℝ)) := by
  apply Finset.prod_le_prod
  · intro i _hi
    exact (BakerWustholz.modifiedHeight_pos φ _).le
  · intro i _hi
    exact squaredProductBases_modifiedHeight_le φ ρ hφρ ratio P eps
      hratio hP heps hratioHeight hPHeight hepsHeight i

/-- The principal logarithmic form attached to the packaged bases is the
ordinary real logarithm of the corresponding positive powered product. -/
lemma packaged_positive_linear_form_eq_log_power
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (ρ : K →+* ℝ)
    (hφρ : ∀ x, φ x = (ρ x : ℂ))
    {r m : ℕ} (ratio z P : K) (eps : Fin r → K)
    (hratio : ratio ≠ 0) (hP : P ≠ 0) (heps : ∀ i, eps i ≠ 0)
    (b : Fin (r + 2) → ℤ)
    (hpack : z ^ m = ∏ i, squaredProductBases ratio P eps i ^ b i)
    (hzpow : 0 < ρ (z ^ m)) :
    (∑ i, (b i : ℂ) *
        Complex.log (φ (squaredProductBases ratio P eps i))) =
      (Real.log (ρ (z ^ m)) : ℂ) := by
  let α : Fin (r + 2) → K := squaredProductBases ratio P eps
  let q : Fin (r + 2) → ℝ := fun i ↦ ρ (α i)
  have hq : ∀ i, 0 < q i := by
    intro i
    exact squaredProductBases_positive ρ hratio hP eps heps i
  have hlog := numberField_positive_linear_form_eq_log_product
    φ α q hq (fun i ↦ hφρ (α i)) b
  rw [← hpack] at hlog
  rw [hlog, hφρ, ← Complex.ofReal_log hzpow.le]

/-- Positivity of the powered product is automatic from its expression as
a product of squared positive-real bases. -/
lemma packaged_positive_linear_form_eq_log_power_of_pack
    {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (ρ : K →+* ℝ)
    (hφρ : ∀ x, φ x = (ρ x : ℂ))
    {r m : ℕ} (ratio z P : K) (eps : Fin r → K)
    (hratio : ratio ≠ 0) (hP : P ≠ 0) (heps : ∀ i, eps i ≠ 0)
    (b : Fin (r + 2) → ℤ)
    (hpack : z ^ m = ∏ i, squaredProductBases ratio P eps i ^ b i) :
    (∑ i, (b i : ℂ) *
        Complex.log (φ (squaredProductBases ratio P eps i))) =
      (Real.log (ρ (z ^ m)) : ℂ) := by
  have hbase : ∀ i, 0 < ρ (squaredProductBases ratio P eps i) :=
    squaredProductBases_positive ρ hratio hP eps heps
  have hzpow : 0 < ρ (z ^ m) := by
    rw [hpack, map_prod]
    exact Finset.prod_pos fun i _hi ↦ by
      simpa using zpow_pos (hbase i) (b i)
  exact packaged_positive_linear_form_eq_log_power
    φ ρ hφρ ratio z P eps hratio hP heps b hpack hzpow

/-- The complete bounded supported-unit identity with an additional
nonzero factor, packaged as a single fixed-length product of squares. -/
theorem supportedUnit_ratio_two_power_eq_packaged_product
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (ratio : Kˣ) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
        (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let P : Kˣ :=
      SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
    let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)
    (ratio * (u : Kˣ)) ^ ((NumberField.classNumber K * I) * 2) =
      ∏ i, squaredProductBases ratio P eps i ^
        squaredProductCoefficients (NumberField.classNumber K) I a i := by
  dsimp only
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ :=
    SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  have hU := supportedUnit_powered_bounded_product_torsion_free
    S u e q B hB ζ a hpow hdecomp
  exact two_power_eq_packaged_product ratio (u : Kˣ) P a eps
    (by simpa only [I, P, eps] using hU)

/-- Combined-leading-factor form of the complete bounded supported-unit
identity.  It has one quotient direction and the maximal-rank unit
directions. -/
theorem supportedUnit_ratio_two_power_eq_combined_product
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (ratio : Kˣ) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
        (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let P : Kˣ :=
      SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
    let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)
    let W : Kˣ :=
      (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
    (ratio * (u : Kˣ)) ^ ((NumberField.classNumber K * I) * 2) =
      ∏ i, combinedSquaredProductBases W eps i ^
        combinedSquaredProductCoefficients a i := by
  dsimp only
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ :=
    SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  have hU := supportedUnit_powered_bounded_product_torsion_free
    S u e q B hB ζ a hpow hdecomp
  exact two_power_eq_combined_product ratio (u : Kˣ) P a eps
    (by simpa only [I, P, eps] using hU)

/-- Field-valued form of the combined supported-unit identity. -/
theorem supportedUnit_ratio_two_power_eq_combined_product_field
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (ratio : Kˣ) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
        (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let P : Kˣ :=
      SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
    let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)
    let W : Kˣ :=
      (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
    (((ratio * (u : Kˣ) : Kˣ) : K)) ^
        ((NumberField.classNumber K * I) * 2) =
      ∏ i, combinedSquaredProductBases (W : K)
          (fun j ↦ (eps j : K)) i ^
        combinedSquaredProductCoefficients a i := by
  dsimp only
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ :=
    SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  let W : Kˣ :=
    (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
  have h := supportedUnit_ratio_two_power_eq_combined_product
    S u ratio e q B hB ζ a hpow hdecomp
  exact combinedProduct_units_coe W (ratio * (u : Kˣ)) eps a
    (by simpa only [I, P, eps, W] using h)

/-- Complete algebraic and archimedean dichotomy for the combined
supported-unit product.  If the leading factor is not an integer unit, it
supplies the distinguished quotient direction.  If it is an integer unit,
it is absorbed with a controlled coefficient box into the maximal-rank
bounded unit basis. -/
theorem supportedUnit_combined_real_log_lower_dichotomy
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Fintype ι]
    (basis : Module.Basis ι ℚ K) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : K →+* ℂ) (ρ : K →+* ℝ) (hφρ : ∀ x, φ x = (ρ x : ℂ))
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (ratio : Kˣ) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B0 Ba : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
        (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z))
    (QW M : ℝ) (hd : Module.finrank ℚ K ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : K →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hBa : 1 ≤ Ba) (ha : ∀ i, (a i).natAbs ≤ Ba)
    (hWheight : Height.logHeight₁
      ((((ratio ^ 2) ^
          (NumberField.classNumber K *
            (BoundedUnits.boundedUnitSubgroup hB).index) *
        ((SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) ^ 2) ^
          (BoundedUnits.boundedUnitSubgroup hB).index : Kˣ) : K)) ≤ QW)
    (hzne :
      (((ratio * (u : Kˣ)) ^
        ((NumberField.classNumber K *
          (BoundedUnits.boundedUnitSubgroup hB).index) * 2)) ^
        (2 * (BoundedUnits.boundedUnitSubgroup hB).index)) ≠ 1) :
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let P : Kˣ := SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
    let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
      ((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
    let W : Kˣ :=
      (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
    let z : K := ((ratio * (u : Kˣ) : Kˣ) : K)
    let m := (NumberField.classNumber K * I) * 2
    let alphaNon := combinedSquaredProductBases (W : K) eps
    let ellNon : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
      Complex.log (φ (alphaNon i))
    (W ∉ integerUnitSubgroup K ∧
      LinearForms.structuredBoxLogarithmicFormThreshold Ba
          (LinearForms.structuredBoxMasterL Ba M alphaNon ellNon)
          M alphaNon ellNon ≤ |Real.log (ρ (z ^ m))|) ∨
    ∃ (c : Fin (NumberField.Units.rank K) →₀ ℤ)
        (reindex : Fin (NumberField.Units.rank K - 1 + 1) ≃
          Fin (NumberField.Units.rank K)),
      W ∈ integerUnitSubgroup K ∧
      let b : Fin (NumberField.Units.rank K) → ℤ := fun i ↦
        c i + ((2 * I : ℕ) : ℤ) * a i
      let alphaUnit : Fin (NumberField.Units.rank K) → K := fun i ↦ eps i ^ 2
      let ellUnit : Fin (NumberField.Units.rank K) → ℂ := fun i ↦
        Complex.log (φ (alphaUnit i))
      LinearForms.structuredBoxLogarithmicFormThreshold
          (integerUnitAbsorptionNatBound K hB QW Ba)
          (LinearForms.structuredBoxMasterL
            (integerUnitAbsorptionNatBound K hB QW Ba) M
            (fun i ↦ alphaUnit (reindex i))
            (fun i ↦ ellUnit (reindex i))) M
          (fun i ↦ alphaUnit (reindex i))
          (fun i ↦ ellUnit (reindex i)) ≤
        |Real.log (ρ ((z ^ m) ^ (2 * I)))| := by
  dsimp only
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ := SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  let epsU : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  let eps : Fin (NumberField.Units.rank K) → K := fun i ↦ (epsU i : K)
  let W : Kˣ :=
    (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
  let zU : Kˣ := ratio * (u : Kˣ)
  let z : K := (zU : K)
  let m := (NumberField.classNumber K * I) * 2
  have hcombined := supportedUnit_ratio_two_power_eq_combined_product
    S u ratio e q B0 hB ζ a hpow hdecomp
  have hcombined' : zU ^ m = ∏ i,
      combinedSquaredProductBases W epsU i ^
        combinedSquaredProductCoefficients a i := by
    simpa only [I, P, W, epsU, zU, m] using hcombined
  by_cases hW : W ∈ integerUnitSubgroup K
  · right
    have hprod : zU ^ m = W * ∏ i, (epsU i ^ 2) ^ (a i) := by
      rw [hcombined', prod_combinedSquaredProductBases_zpow]
    have hWh : Height.logHeight₁ (W : K) ≤ QW := by
      simpa only [W, I, P] using hWheight
    obtain ⟨c, hcprod, hcbound⟩ :=
      integerUnit_powered_product_eq_bounded_squares_with_bound
        hd hB W zU a hW hWh hprod
    let b : Fin (NumberField.Units.rank K) → ℤ := fun i ↦
      c i + ((2 * I : ℕ) : ℤ) * a i
    have hcbound' : ∀ i, |((c i : ℤ) : ℝ)| ≤
        integerUnitAbsorptionRealBound K hB QW := by
      simpa [integerUnitAbsorptionRealBound] using hcbound
    have hb : ∀ i, (b i).natAbs ≤
        integerUnitAbsorptionNatBound K hB QW Ba := by
      intro i
      exact integerUnitAbsorptionCoefficient_natAbs_le hB c a hcbound' ha i
    have hbne : b ≠ 0 := by
      apply absorbedCoefficient_ne_zero hB zU a c
      · simpa only [I, epsU, b] using hcprod
      · simpa only [I, m, zU] using hzne
    have hfield := squaredUnitsProduct_coe (zU ^ m) epsU b
      (by simpa only [I, epsU, b] using hcprod)
    obtain ⟨reindex, hlower⟩ := integerUnit_bounded_real_log_lower_bound
      basis hbasis φ ρ hφρ hB b (z ^ m) M hd hM hMbasis hb hbne
        (by simpa [z, zU, epsU] using hfield)
    exact ⟨c, reindex, hW, by
      simpa only [b, eps, epsU, I, z, zU, m] using hlower⟩
  · left
    have hfield := supportedUnit_ratio_two_power_eq_combined_product_field
      S u ratio e q B0 hB ζ a hpow hdecomp
    have hWpos : 0 < ρ (W : K) := by
      exact combinedLeadingFactor_positive ρ (ratio : K) (P : K)
        (NumberField.classNumber K) I (Units.ne_zero _) (Units.ne_zero _)
    refine ⟨hW, ?_⟩
    exact nonintegerUnit_combined_real_log_lower_bound
      basis hbasis φ ρ hφρ hB W hW a z M hd hM hMbasis hBa ha hWpos
        (by simpa only [I, P, W, eps, epsU, z, zU, m] using hfield)

/-- Field-valued form of the packaged supported-unit identity.  This is the
exact equality consumed by the logarithmic-form bridge. -/
theorem supportedUnit_ratio_two_power_eq_packaged_product_field
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (ratio : Kˣ) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
        (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let P : Kˣ :=
      SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
    let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)
    ((((ratio * (u : Kˣ)) : K)) ^
        ((NumberField.classNumber K * I) * 2)) =
      ∏ i, (squaredProductBases
          (ratio : K) (P : K) (fun j ↦ (eps j : K)) i) ^
        squaredProductCoefficients (NumberField.classNumber K) I a i := by
  dsimp only
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ :=
    SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  have h := supportedUnit_ratio_two_power_eq_packaged_product
    S u ratio e q B hB ζ a hpow hdecomp
  have hK := congrArg (Units.coeHom K) h
  have hbase : ∀ i,
      (Units.coeHom K) (squaredProductBases ratio P eps i) =
        squaredProductBases (ratio : K) (P : K)
          (fun j ↦ (eps j : K)) i := by
    intro i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
    · change ((ratio ^ 2 : Kˣ) : K) = (ratio : K) ^ 2
      simp
    · change ((P ^ 2 : Kˣ) : K) = (P : K) ^ 2
      simp
    · change ((eps k ^ 2 : Kˣ) : K) = (eps k : K) ^ 2
      simp
  simp only [map_mul, map_pow, map_prod, map_zpow] at hK
  change ((ratio : K) * ((u : Kˣ) : K)) ^
      ((NumberField.classNumber K * I) * 2) =
    ∏ i, ((Units.coeHom K) (squaredProductBases ratio P eps i)) ^
      squaredProductCoefficients (NumberField.classNumber K) I a i at hK
  rw [show (∏ i, ((Units.coeHom K) (squaredProductBases ratio P eps i)) ^
      squaredProductCoefficients (NumberField.classNumber K) I a i) =
      ∏ i, (squaredProductBases (ratio : K) (P : K)
        (fun j ↦ (eps j : K)) i) ^
          squaredProductCoefficients (NumberField.classNumber K) I a i by
    apply Finset.prod_congr rfl
    intro i _hi
    rw [hbase i]] at hK
  exact hK

/-- Combining the generated-field discriminant estimate with the proved
Minkowski--Euler-product class-number bound eliminates the formerly
uncontrolled class-number factor. -/
theorem numberField_classNumber_le_three_sqRoots_explicit
    {K : Type*} [Field K] [NumberField K]
    (s₁ s₂ s₃ : K) {γ₁ γ₂ γ₃ H : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : K)) (hs₂ : s₂ ^ 2 = (γ₂ : K))
    (hs₃ : s₃ ^ 2 = (γ₃ : K))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hgen : Algebra.adjoin ℚ {s₁, s₂, s₃} = ⊤) :
    (NumberField.classNumber K : ℝ) ≤
      (6 : ℝ) ^ 8 * ((40320 : ℝ) * (H : ℝ) ^ 24) ^ 2 := by
  have hdeg : Module.finrank ℚ K ≤ 8 :=
    finrank_threeSqRoots_le_eight s₁ s₂ s₃
      (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using hs₁) (by simpa using hs₂) (by simpa using hs₃) hgen
  have hdisc := numberField_natAbs_discr_le_three_sqRoots_explicit
    s₁ s₂ s₃ hs₁ hs₂ hs₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H hgen
  have hclass := Towers.classNumber_le_six_pow_finrank_mul_absDiscriminant
    (K := K)
  have habs : Towers.absDiscriminant K =
      ((NumberField.discr K).natAbs : ℝ) := by
    simp [Towers.absDiscriminant]
  rw [habs] at hclass
  calc
    (NumberField.classNumber K : ℝ) ≤
        (6 : ℝ) ^ Module.finrank ℚ K *
          ((NumberField.discr K).natAbs : ℝ) := hclass
    _ ≤ (6 : ℝ) ^ 8 * ((40320 : ℝ) * (H : ℝ) ^ 24) ^ 2 := by
      exact mul_le_mul
        (pow_le_pow_right₀ (by norm_num) hdeg) hdisc (by positivity) (by positivity)

/-- If three elements are adjoined inside the algebraic closure, their
canonical lifts generate the resulting intermediate field not only as a
field but already as a rational algebra.  This is the bridge from the
ambient square roots to the concrete number field on which discriminants
and units are computed. -/
lemma algebra_adjoin_three_lifts_eq_top
    (s₁ s₂ s₃ : AlgebraicClosure ℚ) :
    let K := IntermediateField.adjoin ℚ
      ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
    let _ : Algebra ℚ K := K.algebra'
    let r₁ : K := ⟨s₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₂ : K := ⟨s₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₃ : K := ⟨s₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    Algebra.adjoin ℚ {r₁, r₂, r₃} = ⊤ := by
  dsimp only
  let K := IntermediateField.adjoin ℚ
    ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
  let : Algebra ℚ K := K.algebra'
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  let r₁ : K := ⟨s₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₂ : K := ⟨s₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₃ : K := ⟨s₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hIF : IntermediateField.adjoin ℚ {r₁, r₂, r₃} = ⊤ := by
    apply (IntermediateField.map_injective K.val)
    rw [IntermediateField.adjoin_map]
    have himage : K.val '' ({r₁, r₂, r₃} : Set K) =
        ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        rcases hy with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨r₁, by exact Or.inl rfl, rfl⟩
        · exact ⟨r₂, by exact Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨r₃, by exact Or.inr (Or.inr rfl), rfl⟩
    rw [himage]
    ext x
    change x ∈ K ↔ x ∈ K.val '' (⊤ : IntermediateField ℚ K)
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
    · rintro ⟨x, -, rfl⟩
      exact x.2
  apply Algebra.adjoin_eq_top_of_intermediateField
    (fun x _ ↦ IntermediateField.isAlgebraic_iff.mpr
      (Algebra.IsAlgebraic.isAlgebraic (x : AlgebraicClosure ℚ)))
  exact hIF

/-! The positive-real model of the three-radical field

The algebraic-closure model above is convenient for choosing roots without
signs.  For the archimedean estimate we also need one distinguished
embedding at which all three roots are positive.  The following concrete
subfield of `ℝ` supplies exactly that embedding while retaining the same
degree, discriminant, class-number, and bounded-unit estimates. -/

/-- The subfield of `ℝ` generated by the three positive square roots. -/
def realPellField (γ₁ γ₂ γ₃ : ℕ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ
    ({Real.sqrt γ₁, Real.sqrt γ₂, Real.sqrt γ₃} : Set ℝ)

/-- The distinguished inclusion of the positive-real Pell field into `ℝ`. -/
def realPellRealEmbedding (γ₁ γ₂ γ₃ : ℕ) :
    realPellField γ₁ γ₂ γ₃ →+* ℝ :=
  SubsemiringClass.subtype (realPellField γ₁ γ₂ γ₃)

/-- The same distinguished embedding, regarded as a complex embedding. -/
def realPellComplexEmbedding (γ₁ γ₂ γ₃ : ℕ) :
    realPellField γ₁ γ₂ γ₃ →+* ℂ :=
  Complex.ofRealHom.comp (realPellRealEmbedding γ₁ γ₂ γ₃)

@[simp] lemma realPellComplexEmbedding_apply (γ₁ γ₂ γ₃ : ℕ)
    (x : realPellField γ₁ γ₂ γ₃) :
    realPellComplexEmbedding γ₁ γ₂ γ₃ x = ((x : ℝ) : ℂ) := rfl

/-- First distinguished positive radical in `realPellField`. -/
def realPellRootOne (γ₁ γ₂ γ₃ : ℕ) : realPellField γ₁ γ₂ γ₃ :=
  ⟨Real.sqrt γ₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

/-- Second distinguished positive radical in `realPellField`. -/
def realPellRootTwo (γ₁ γ₂ γ₃ : ℕ) : realPellField γ₁ γ₂ γ₃ :=
  ⟨Real.sqrt γ₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

/-- Third distinguished positive radical in `realPellField`. -/
def realPellRootThree (γ₁ γ₂ γ₃ : ℕ) : realPellField γ₁ γ₂ γ₃ :=
  ⟨Real.sqrt γ₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

@[simp] lemma realPellRootOne_val (γ₁ γ₂ γ₃ : ℕ) :
    ((realPellRootOne γ₁ γ₂ γ₃ : realPellField γ₁ γ₂ γ₃) : ℝ) =
      Real.sqrt γ₁ := rfl

@[simp] lemma realPellRootTwo_val (γ₁ γ₂ γ₃ : ℕ) :
    ((realPellRootTwo γ₁ γ₂ γ₃ : realPellField γ₁ γ₂ γ₃) : ℝ) =
      Real.sqrt γ₂ := rfl

@[simp] lemma realPellRootThree_val (γ₁ γ₂ γ₃ : ℕ) :
    ((realPellRootThree γ₁ γ₂ γ₃ : realPellField γ₁ γ₂ γ₃) : ℝ) =
      Real.sqrt γ₃ := rfl

lemma realPellRootOne_sq (γ₁ γ₂ γ₃ : ℕ) :
    realPellRootOne γ₁ γ₂ γ₃ ^ 2 =
      (γ₁ : realPellField γ₁ γ₂ γ₃) := by
  apply Subtype.ext
  simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity)

lemma realPellRootTwo_sq (γ₁ γ₂ γ₃ : ℕ) :
    realPellRootTwo γ₁ γ₂ γ₃ ^ 2 =
      (γ₂ : realPellField γ₁ γ₂ γ₃) := by
  apply Subtype.ext
  simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity)

lemma realPellRootThree_sq (γ₁ γ₂ γ₃ : ℕ) :
    realPellRootThree γ₁ γ₂ γ₃ ^ 2 =
      (γ₃ : realPellField γ₁ γ₂ γ₃) := by
  apply Subtype.ext
  simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity)

lemma real_sqrt_nat_isIntegral (γ : ℕ) :
    IsIntegral ℚ (Real.sqrt γ) := by
  apply IsIntegral.of_pow (by norm_num : 0 < 2)
  rw [Real.sq_sqrt (by positivity)]
  exact isIntegral_natCast (R := ℚ) (B := ℝ) γ

/-- The positive-real three-radical field is a number field. -/
theorem realPellFieldNumberField (γ₁ γ₂ γ₃ : ℕ) :
    NumberField (realPellField γ₁ γ₂ γ₃) := by
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  exact NumberField.of_module_finite ℚ K

/-- The canonical positive-root lifts generate the concrete real Pell
field as a rational algebra. -/
lemma realPellField_adjoin_roots_eq_top (γ₁ γ₂ γ₃ : ℕ) :
    let K := realPellField γ₁ γ₂ γ₃
    let _ : Algebra ℚ K := K.algebra'
    let r₁ : K := ⟨Real.sqrt γ₁,
      IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₂ : K := ⟨Real.sqrt γ₂,
      IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₃ : K := ⟨Real.sqrt γ₃,
      IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    Algebra.adjoin ℚ {r₁, r₂, r₃} = ⊤ := by
  dsimp only
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  let r₁ : K := ⟨Real.sqrt γ₁,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₂ : K := ⟨Real.sqrt γ₂,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₃ : K := ⟨Real.sqrt γ₃,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hIF : IntermediateField.adjoin ℚ {r₁, r₂, r₃} = ⊤ := by
    apply (IntermediateField.map_injective K.val)
    rw [IntermediateField.adjoin_map]
    have himage : K.val '' ({r₁, r₂, r₃} : Set K) =
        ({Real.sqrt γ₁, Real.sqrt γ₂, Real.sqrt γ₃} : Set ℝ) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        rcases hy with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨r₁, by exact Or.inl rfl, rfl⟩
        · exact ⟨r₂, by exact Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨r₃, by exact Or.inr (Or.inr rfl), rfl⟩
    rw [himage]
    ext x
    change x ∈ K ↔ x ∈ K.val '' (⊤ : IntermediateField ℚ K)
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
    · rintro ⟨x, -, rfl⟩
      exact x.2
  apply Algebra.adjoin_eq_top_of_intermediateField
    (fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x)
  exact hIF

/-- All embeddings of the positive-real three-radical field are real. -/
theorem realPellFieldIsTotallyReal
    {γ₁ γ₂ γ₃ : ℕ} (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃) :
    let K := realPellField γ₁ γ₂ γ₃
    let _ : Algebra ℚ K := K.algebra'
    let r₁ : K := ⟨Real.sqrt γ₁,
      IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₂ : K := ⟨Real.sqrt γ₂,
      IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₃ : K := ⟨Real.sqrt γ₃,
      IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let _ : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
    NumberField.IsTotallyReal K := by
  dsimp only
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  let : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  let r₁ : K := ⟨Real.sqrt γ₁,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₂ : K := ⟨Real.sqrt γ₂,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₃ : K := ⟨Real.sqrt γ₃,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := by
    apply Subtype.ext
    simpa [r₁] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity)
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := by
    apply Subtype.ext
    simpa [r₂] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity)
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := by
    apply Subtype.ext
    simpa [r₃] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity)
  exact numberField_isTotallyReal_of_three_positive_sqRoots
    r₁ r₂ r₃ hr₁ hr₂ hr₃ hγ₁ hγ₂ hγ₃
      (realPellField_adjoin_roots_eq_top γ₁ γ₂ γ₃)

/-- Explicit discriminant bound for the concrete positive-real Pell
field. -/
theorem realPellField_natAbs_discr_le
    {γ₁ γ₂ γ₃ H : ℕ}
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H) :
    let K := realPellField γ₁ γ₂ γ₃
    let _ : Algebra ℚ K := K.algebra'
    let _ : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
    ((NumberField.discr K).natAbs : ℝ) ≤
      ((40320 : ℝ) * (H : ℝ) ^ 24) ^ 2 := by
  dsimp only
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  let : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  let r₁ : K := ⟨Real.sqrt γ₁,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₂ : K := ⟨Real.sqrt γ₂,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₃ : K := ⟨Real.sqrt γ₃,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := by
    apply Subtype.ext
    simpa [r₁] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity)
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := by
    apply Subtype.ext
    simpa [r₂] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity)
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := by
    apply Subtype.ext
    simpa [r₃] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity)
  exact numberField_natAbs_discr_le_three_sqRoots_explicit
    r₁ r₂ r₃ hr₁ hr₂ hr₃ hγ₁ hγ₂ hγ₃
      hγ₁H hγ₂H hγ₃H (realPellField_adjoin_roots_eq_top γ₁ γ₂ γ₃)

/-- Explicit class-number bound for the concrete positive-real Pell
field. -/
theorem realPellField_classNumber_le
    {γ₁ γ₂ γ₃ H : ℕ}
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H) :
    let K := realPellField γ₁ γ₂ γ₃
    let _ : Algebra ℚ K := K.algebra'
    let _ : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
    (NumberField.classNumber K : ℝ) ≤
      (6 : ℝ) ^ 8 * ((40320 : ℝ) * (H : ℝ) ^ 24) ^ 2 := by
  dsimp only
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  let : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  let r₁ : K := ⟨Real.sqrt γ₁,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₂ : K := ⟨Real.sqrt γ₂,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₃ : K := ⟨Real.sqrt γ₃,
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := by
    apply Subtype.ext
    simpa [r₁] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity)
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := by
    apply Subtype.ext
    simpa [r₂] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity)
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := by
    apply Subtype.ext
    simpa [r₃] using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity)
  exact numberField_classNumber_le_three_sqRoots_explicit
    r₁ r₂ r₃ hr₁ hr₂ hr₃ hγ₁ hγ₂ hγ₃
      hγ₁H hγ₂H hγ₃H (realPellField_adjoin_roots_eq_top γ₁ γ₂ γ₃)

/-- The common supported-unit equation in the positive-real radical field,
together with the exact distinguished real value of its first unit and the
elementary upper bound for the resulting nonzero logarithmic form.  Thus the
finite-prime/Dirichlet coordinate reduction and the archimedean estimate are
now attached to the same concrete number field. -/
theorem realPell_supportedUnit_log_gap
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlarge : 2 * J ≤ γ₁ * x₁ ^ 2) :
    let K := realPellField γ₁ γ₂ γ₃
    let _ : Algebra ℚ K := K.algebra'
    let _ : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K) (hS : S.Finite),
      S = pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
          (Int.cast_ne_zero.mpr hβ₂₃)) ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      ((U : Kˣ) : K) =
        pellValueMinus (realPellRootOne γ₁ γ₂ γ₃)
            (realPellRootTwo γ₁ γ₂ γ₃) (x₁ : ℤ) (x₂ : ℤ) /
          pellValueMinus (realPellRootOne γ₁ γ₂ γ₃)
            (realPellRootThree γ₁ γ₂ γ₃) (x₁ : ℤ) (x₃ : ℤ) ∧
      ((V : Kˣ) : K) =
        pellValueMinus (realPellRootTwo γ₁ γ₂ γ₃)
            (realPellRootThree γ₁ γ₂ γ₃) (x₂ : ℤ) (x₃ : ℤ) /
          pellValueMinus (realPellRootOne γ₁ γ₂ γ₃)
            (realPellRootThree γ₁ γ₂ γ₃) (x₁ : ℤ) (x₃ : ℤ) ∧
      (letI : Fintype S := hS.fintype
       let B : ℝ := 16 * Real.log 2 + 16 * Real.log (H : ℝ) +
          16 * (Real.log (x₁ : ℝ) + Real.log (x₂ : ℝ) +
            Real.log (x₃ : ℝ))
       SupportedUnitBoundedDirichletDecomposition S U J B ∧
         SupportedUnitBoundedDirichletDecomposition S V J B) ∧
      ((((U : Kˣ) : K) : ℝ)) =
        (Real.sqrt γ₁ * x₁ - Real.sqrt γ₂ * x₂) /
          (Real.sqrt γ₁ * x₁ - Real.sqrt γ₃ * x₃) ∧
      (β₁₃ : ℝ) / (β₁₂ : ℝ) *
          ((((U : Kˣ) : K) : ℝ)) - 1 ≠ 0 ∧
      |(β₁₃ : ℝ) / (β₁₂ : ℝ) *
          ((((U : Kˣ) : K) : ℝ)) - 1| ≤
        2 * (J : ℝ) / (Real.sqrt γ₁ * x₁) ^ 2 ∧
      Real.log |(β₁₃ : ℝ) / (β₁₂ : ℝ) *
          ((((U : Kˣ) : K) : ℝ)) - 1| ≤
        Real.log (2 * (J : ℝ)) -
          2 * Real.log (Real.sqrt γ₁ * x₁) := by
  dsimp only
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  let : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  let r₁ : K := realPellRootOne γ₁ γ₂ γ₃
  let r₂ : K := realPellRootTwo γ₁ γ₂ γ₃
  let r₃ : K := realPellRootThree γ₁ γ₂ γ₃
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := realPellRootOne_sq _ _ _
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := realPellRootTwo_sq _ _ _
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := realPellRootThree_sq _ _ _
  have hdeg : Module.finrank ℚ K ≤ 8 := by
    change Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        ({Real.sqrt γ₁, Real.sqrt γ₂, Real.sqrt γ₃} : Set ℝ)) ≤ 8
    exact finrank_adjoin_three_sqRoots_le_eight
      (Real.sqrt γ₁) (Real.sqrt γ₂) (Real.sqrt γ₃)
      (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity))
  obtain ⟨S, U, V, hS, hSdef, hUV, hU, hV, hdecomp⟩ :=
    simultaneousPell_quantitative_common_all_coordinate_bounds
      hr₁ hr₂ hr₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg J
      hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
      hx₁ hx₂ hx₃
  have hUreal : ((((U : Kˣ) : K) : ℝ)) =
      (Real.sqrt γ₁ * x₁ - Real.sqrt γ₂ * x₂) /
        (Real.sqrt γ₁ * x₁ - Real.sqrt γ₃ * x₃) := by
    have h := congrArg (fun z : K ↦ (z : ℝ)) hU
    simpa [r₁, r₂, r₃, pellValueMinus] using h
  let A : ℝ := Real.sqrt γ₁ * x₁
  let B : ℝ := Real.sqrt γ₂ * x₂
  let C : ℝ := Real.sqrt γ₃ * x₃
  have hA : 0 < A := by
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hγ₁))
      (by exact_mod_cast hx₁)
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ C := by positivity
  have hAsq : A ^ 2 = (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hBsq : B ^ 2 = (γ₂ : ℝ) * (x₂ : ℝ) ^ 2 := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hCsq : C ^ 2 = (γ₃ : ℝ) * (x₃ : ℝ) ^ 2 := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have h₁₂ : A ^ 2 - B ^ 2 = (β₁₂ : ℝ) := by
    rw [hAsq, hBsq]
    exact_mod_cast hPell.1
  have h₁₃ : A ^ 2 - C ^ 2 = (β₁₃ : ℝ) := by
    rw [hAsq, hCsq]
    exact_mod_cast hPell.2
  have hβ₁₂R : (β₁₂ : ℝ) ≠ 0 := by exact_mod_cast hβ₁₂
  have hβ₁₃R : (β₁₃ : ℝ) ≠ 0 := by exact_mod_cast hβ₁₃
  have hβdiffR : (β₁₂ : ℝ) - (β₁₃ : ℝ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (sub_ne_zero.mp hβ₂₃).symm)
  have hJR : (0 : ℝ) < J := by
    exact_mod_cast (lt_of_lt_of_le (Int.natAbs_pos.mpr hβ₁₂) hJ₁₂)
  have hJ₁₂R : |(β₁₂ : ℝ)| ≤ (J : ℝ) := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast hJ₁₂
  have hJ₁₃R : |(β₁₃ : ℝ)| ≤ (J : ℝ) := by
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast hJ₁₃
  have hlargeR : 2 * (J : ℝ) ≤ A ^ 2 := by
    rw [hAsq]
    exact_mod_cast hlarge
  have hABpos : 0 < A + B := by positivity
  have hBCne : B + C ≠ 0 := by
    intro hzero
    have hBzero : B = 0 := by nlinarith
    have hCzero : C = 0 := by nlinarith
    apply hβdiffR
    rw [hBzero] at h₁₂
    rw [hCzero] at h₁₃
    linarith
  have hgapNe := simultaneousPell_real_normalized_gap_ne_zero
    h₁₂ h₁₃ hβ₁₂R hβ₁₃R hβdiffR hABpos.ne' hBCne
  have hgapAbs := simultaneousPell_real_normalized_gap_abs_le
    hA hB hC h₁₂ h₁₃ hβ₁₂R hβ₁₃R hJR.le
      hJ₁₂R hJ₁₃R hlargeR
  have hlog := simultaneousPell_real_normalized_gap_log_le
    hA hB hC h₁₂ h₁₃ hβ₁₂R hβ₁₃R hβdiffR hJR
      hJ₁₂R hJ₁₃R hlargeR
  refine ⟨S, U, V, hS, hSdef, hUV, ?_, ?_, hdecomp, hUreal, ?_, ?_, ?_⟩
  · simpa [r₁, r₂, r₃] using hU
  · simpa [r₁, r₂, r₃] using hV
  · rw [hUreal]
    simpa [A, B, C] using hgapNe
  · rw [hUreal]
    simpa [A, B, C] using hgapAbs
  · rw [hUreal]
    simpa [A, B, C] using hlog

/-- Every supported unit in the positive-real three-radical field admits
the explicit bounded-generator decomposition with a discriminant parameter
depending only on the common radicand height. -/
theorem realPellField_supportedUnit_boundedUnit_decomposition_explicit
    {γ₁ γ₂ γ₃ H : ℕ}
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H) :
    let K := realPellField γ₁ γ₂ γ₃
    let _ : Algebra ℚ K := K.algebra'
    let _ : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
    let _ : NumberField.IsTotallyReal K :=
      realPellFieldIsTotallyReal hγ₁ hγ₂ hγ₃
    ∀ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) [Fintype S] (u : S.unit K),
      let N := (40320 * H ^ 24) ^ 2
      let B := boundedUnitMinkowskiNatBound N
      ∃ (e : S → ℤ)
          (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers K))).unit K)
          (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
            NumberField.mixedEmbedding.convexBodyLTFactor K * B)
          (ζ : NumberField.Units.torsion K)
          (a : Fin (NumberField.Units.rank K) →₀ ℤ),
        (u : Kˣ) ^ NumberField.classNumber K =
            (SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e : Kˣ) *
              (q : Kˣ) ∧
          (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
          (BoundedUnits.boundedUnitSubgroup hB).index ≤
            BoundedUnits.boundedUnitIndexUpper (K := K)
              (totallyRealDegreeEightUnitLogGap / 8) B ∧
          (SupportedUnits.emptyEquivUnits K q) ^
              (BoundedUnits.boundedUnitSubgroup hB).index =
            ζ.1 * a.prod (fun i z ↦
              BoundedUnits.boundedFundSystem hB i ^ z) ∧
          let Q :=
            (NumberField.classNumber K : ℝ) *
                Height.logHeight₁ (((u : Kˣ) : K)) +
              ∑ v, (e v).natAbs * Height.logHeight₁
                ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))
          ∀ i,
            |((a i : ℤ) : ℝ)| ≤
              ((NumberField.Units.rank K).factorial *
                (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                  ((BoundedUnits.boundedUnitIndexUpper (K := K)
                      (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
                    (2 * Q))) ^ NumberField.Units.rank K) /
                (totallyRealDegreeEightUnitLogGap / 8) ^
                  NumberField.Units.rank K := by
  dsimp only
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  let : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  let : NumberField.IsTotallyReal K :=
    realPellFieldIsTotallyReal hγ₁ hγ₂ hγ₃
  intro S _ u
  let r₁ : K := realPellRootOne γ₁ γ₂ γ₃
  let r₂ : K := realPellRootTwo γ₁ γ₂ γ₃
  let r₃ : K := realPellRootThree γ₁ γ₂ γ₃
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := realPellRootOne_sq _ _ _
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := realPellRootTwo_sq _ _ _
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := realPellRootThree_sq _ _ _
  have hdeg : Module.finrank ℚ K ≤ 8 := by
    change Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        ({Real.sqrt γ₁, Real.sqrt γ₂, Real.sqrt γ₃} : Set ℝ)) ≤ 8
    exact finrank_adjoin_three_sqRoots_le_eight
      (Real.sqrt γ₁) (Real.sqrt γ₂) (Real.sqrt γ₃)
      (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity))
  let N : ℕ := (40320 * H ^ 24) ^ 2
  have hdiscR := realPellField_natAbs_discr_le
    hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
  dsimp only at hdiscR
  have hdisc : |NumberField.discr K| ≤ N := by
    rw [Int.abs_eq_natAbs]
    dsimp [N]
    norm_cast at hdiscR
    exact_mod_cast hdiscR
  simpa [N] using
    (numberField_supportedUnit_boundedUnit_decomposition_explicit
      K S u hdeg hdisc)

/-- The concrete supported-unit logarithmic form remains exponentially small
after raising it to any positive power.  This is the archimedean estimate in
the same powered form as `supportedUnit_powered_bounded_product`. -/
theorem realPell_supportedUnit_powered_log_gap
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J m : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlarge : 2 * J < γ₁ * x₁ ^ 2) (hm : 0 < m) :
    let K := realPellField γ₁ γ₂ γ₃
    let _ : Algebra ℚ K := K.algebra'
    let _ : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
    ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U V : S.unit K) (hS : S.Finite),
      S = pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
          (Int.cast_ne_zero.mpr hβ₂₃)) ∧
      (((U : Kˣ) : K) + ((V : Kˣ) : K) = 1) ∧
      (letI : Fintype S := hS.fintype
       let B : ℝ := 16 * Real.log 2 + 16 * Real.log (H : ℝ) +
          16 * (Real.log (x₁ : ℝ) + Real.log (x₂ : ℝ) +
            Real.log (x₃ : ℝ))
       SupportedUnitBoundedDirichletDecomposition S U J B ∧
         SupportedUnitBoundedDirichletDecomposition S V J B) ∧
      ((((U : Kˣ) : K) : ℝ)) =
        (Real.sqrt γ₁ * x₁ - Real.sqrt γ₂ * x₂) /
          (Real.sqrt γ₁ * x₁ - Real.sqrt γ₃ * x₃) ∧
      (β₁₃ : ℝ) / (β₁₂ : ℝ) *
          ((((U : Kˣ) : K) : ℝ)) - 1 ≠ 0 ∧
      Real.log |(((β₁₃ : ℝ) / (β₁₂ : ℝ) *
          ((((U : Kˣ) : K) : ℝ))) ^ m) - 1| ≤
        (Real.log (2 * (J : ℝ)) -
          2 * Real.log (Real.sqrt γ₁ * x₁)) +
          Real.log (m : ℝ) + (m - 1 : ℕ) * Real.log 2 := by
  dsimp only
  obtain ⟨S, U, V, hS, hSdef, hUV, _hU, _hV, hdecomp,
      hUreal, hgapNe, hgapAbs, hlog⟩ :=
    realPell_supportedUnit_log_gap hPell hβ₁₂ hβ₁₃ hβ₂₃
      hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
      hx₁ hx₂ hx₃ hlarge.le
  let z : ℝ := (β₁₃ : ℝ) / (β₁₂ : ℝ) *
    ((((U : (realPellField γ₁ γ₂ γ₃)ˣ) :
      realPellField γ₁ γ₂ γ₃) : ℝ))
  let A : ℝ := Real.sqrt γ₁ * x₁
  have hA : 0 < A := by
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hγ₁))
      (by exact_mod_cast hx₁)
  have hAsq : A ^ 2 = (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hlargeR : 2 * (J : ℝ) < A ^ 2 := by
    rw [hAsq]
    exact_mod_cast hlarge
  have hratio : 2 * (J : ℝ) / A ^ 2 < 1 :=
    (div_lt_one (sq_pos_of_pos hA)).2 hlargeR
  have hsmall : |z - 1| < 1 := by
    exact hgapAbs.trans_lt (by simpa [A, z] using hratio)
  have hpow := real_log_abs_pow_sub_one_le_of_log_gap hm
    (by simpa [z] using hgapNe) hsmall (by simpa [A, z] using hlog)
  exact ⟨S, U, V, hS, hSdef, hUV, hdecomp, hUreal, hgapNe,
    by simpa [z, A] using hpow⟩

/-- The finitely generated field of three elements of the algebraic closure
is a number field.  We name the fully proved instance so later statements can
refer to its discriminant without postulating any field-theoretic structure. -/
theorem pellSplittingFieldNumberField
    (s₁ s₂ s₃ : AlgebraicClosure ℚ) :
    NumberField (IntermediateField.adjoin ℚ
      ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))) := by
  let K := IntermediateField.adjoin ℚ
    ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
  let : Algebra ℚ K := K.algebra'
  let : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    @Algebra.IsAlgebraic.isIntegral ℚ (AlgebraicClosure ℚ) _ _ _
      (AlgebraicClosure.isAlgebraic ℚ)
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      Algebra.IsIntegral.isIntegral x
  exact NumberField.of_module_finite ℚ K

/-- The exact field generated by three chosen square roots of positive
integers is totally real.  This is stronger than the ambient degree-eight
statement and enables explicit real-unit separation below. -/
theorem pellSplittingFieldIsTotallyReal
    (s₁ s₂ s₃ : AlgebraicClosure ℚ) {γ₁ γ₂ γ₃ : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : AlgebraicClosure ℚ))
    (hs₂ : s₂ ^ 2 = (γ₂ : AlgebraicClosure ℚ))
    (hs₃ : s₃ ^ 2 = (γ₃ : AlgebraicClosure ℚ))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃) :
    let K := IntermediateField.adjoin ℚ
      ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
    let _ : Algebra ℚ K := K.algebra'
    let r₁ : K := ⟨s₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₂ : K := ⟨s₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₃ : K := ⟨s₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let _ : NumberField K := pellSplittingFieldNumberField s₁ s₂ s₃
    NumberField.IsTotallyReal K := by
  dsimp only
  let K := IntermediateField.adjoin ℚ
    ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
  let : Algebra ℚ K := K.algebra'
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  let : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    @Algebra.IsAlgebraic.isIntegral ℚ (AlgebraicClosure ℚ) _ _ _
      (AlgebraicClosure.isAlgebraic ℚ)
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      Algebra.IsIntegral.isIntegral x
  let : NumberField K := pellSplittingFieldNumberField s₁ s₂ s₃
  let r₁ : K := ⟨s₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₂ : K := ⟨s₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₃ : K := ⟨s₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := by
    apply Subtype.ext
    simpa [r₁] using hs₁
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := by
    apply Subtype.ext
    simpa [r₂] using hs₂
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := by
    apply Subtype.ext
    simpa [r₃] using hs₃
  exact numberField_isTotallyReal_of_three_positive_sqRoots
    r₁ r₂ r₃ hr₁ hr₂ hr₃ hγ₁ hγ₂ hγ₃
      (algebra_adjoin_three_lifts_eq_top s₁ s₂ s₃)

/-- The exact three-radical field used for the common Pell factorization has
the promised explicit discriminant bound.  In particular, the preceding
abstract estimate is now attached to the generated intermediate field rather
than to an arbitrary overfield. -/
theorem pellSplittingField_natAbs_discr_le
    (s₁ s₂ s₃ : AlgebraicClosure ℚ) {γ₁ γ₂ γ₃ H : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : AlgebraicClosure ℚ))
    (hs₂ : s₂ ^ 2 = (γ₂ : AlgebraicClosure ℚ))
    (hs₃ : s₃ ^ 2 = (γ₃ : AlgebraicClosure ℚ))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H) :
    let K := IntermediateField.adjoin ℚ
      ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
    let _ : Algebra ℚ K := K.algebra'
    let r₁ : K := ⟨s₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₂ : K := ⟨s₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₃ : K := ⟨s₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let _ : NumberField K := pellSplittingFieldNumberField s₁ s₂ s₃
    ((NumberField.discr K).natAbs : ℝ) ≤
      ((40320 : ℝ) * (H : ℝ) ^ 24) ^ 2 := by
  dsimp only
  let K := IntermediateField.adjoin ℚ
    ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
  let : Algebra ℚ K := K.algebra'
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  let : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    @Algebra.IsAlgebraic.isIntegral ℚ (AlgebraicClosure ℚ) _ _ _
      (AlgebraicClosure.isAlgebraic ℚ)
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      Algebra.IsIntegral.isIntegral x
  let : NumberField K := pellSplittingFieldNumberField s₁ s₂ s₃
  let r₁ : K := ⟨s₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₂ : K := ⟨s₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₃ : K := ⟨s₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := by
    apply Subtype.ext
    simpa [r₁] using hs₁
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := by
    apply Subtype.ext
    simpa [r₂] using hs₂
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := by
    apply Subtype.ext
    simpa [r₃] using hs₃
  exact numberField_natAbs_discr_le_three_sqRoots_explicit
    r₁ r₂ r₃ hr₁ hr₂ hr₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
    (algebra_adjoin_three_lifts_eq_top s₁ s₂ s₃)

/-- The class number of the exact three-radical splitting field is bounded
solely in terms of the common radicand height. -/
theorem pellSplittingField_classNumber_le
    (s₁ s₂ s₃ : AlgebraicClosure ℚ) {γ₁ γ₂ γ₃ H : ℕ}
    (hs₁ : s₁ ^ 2 = (γ₁ : AlgebraicClosure ℚ))
    (hs₂ : s₂ ^ 2 = (γ₂ : AlgebraicClosure ℚ))
    (hs₃ : s₃ ^ 2 = (γ₃ : AlgebraicClosure ℚ))
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H) :
    let K := IntermediateField.adjoin ℚ
      ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
    let _ : Algebra ℚ K := K.algebra'
    let r₁ : K := ⟨s₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₂ : K := ⟨s₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let r₃ : K := ⟨s₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let _ : NumberField K := pellSplittingFieldNumberField s₁ s₂ s₃
    (NumberField.classNumber K : ℝ) ≤
      (6 : ℝ) ^ 8 * ((40320 : ℝ) * (H : ℝ) ^ 24) ^ 2 := by
  dsimp only
  let K := IntermediateField.adjoin ℚ
    ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))
  let : Algebra ℚ K := K.algebra'
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  let : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    @Algebra.IsAlgebraic.isIntegral ℚ (AlgebraicClosure ℚ) _ _ _
      (AlgebraicClosure.isAlgebraic ℚ)
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      Algebra.IsIntegral.isIntegral x
  let : NumberField K := pellSplittingFieldNumberField s₁ s₂ s₃
  let r₁ : K := ⟨s₁, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₂ : K := ⟨s₂, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let r₃ : K := ⟨s₃, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := by
    apply Subtype.ext
    simpa [r₁] using hs₁
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := by
    apply Subtype.ext
    simpa [r₂] using hs₂
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := by
    apply Subtype.ext
    simpa [r₃] using hs₃
  exact numberField_classNumber_le_three_sqRoots_explicit
    r₁ r₂ r₃ hr₁ hr₂ hr₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
    (algebra_adjoin_three_lifts_eq_top s₁ s₂ s₃)

/-- The three square roots needed for the factorization may be chosen inside
a finite extension of `ℚ`: take their finitely generated intermediate
field in the algebraic closure.  This is the number-field reduction used
before applying height and unit-equation estimates. -/
theorem exists_finite_pell_splitting_field (γ₁ γ₂ γ₃ : ℤ) :
    ∃ s₁ s₂ s₃ : AlgebraicClosure ℚ,
      s₁ ^ 2 = (γ₁ : AlgebraicClosure ℚ) ∧
      s₂ ^ 2 = (γ₂ : AlgebraicClosure ℚ) ∧
      s₃ ^ 2 = (γ₃ : AlgebraicClosure ℚ) ∧
      (let K₁ := IntermediateField.adjoin ℚ ({s₁} : Set (AlgebraicClosure ℚ))
       let K₂ := IntermediateField.adjoin K₁ ({s₂} : Set (AlgebraicClosure ℚ))
       let K₃ := IntermediateField.adjoin K₂ ({s₃} : Set (AlgebraicClosure ℚ))
       Module.finrank ℚ K₁ * Module.finrank K₁ K₂ *
          Module.finrank K₂ K₃ ≤ 8) ∧
      Module.finrank ℚ
        (IntermediateField.adjoin ℚ
          ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))) ≤ 8 ∧
      Nonempty (FiniteDimensional ℚ
        (IntermediateField.adjoin ℚ ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ)))) := by
  obtain ⟨s₁, hs₁⟩ := IsAlgClosed.exists_pow_nat_eq
    (γ₁ : AlgebraicClosure ℚ) (by norm_num : 0 < 2)
  obtain ⟨s₂, hs₂⟩ := IsAlgClosed.exists_pow_nat_eq
    (γ₂ : AlgebraicClosure ℚ) (by norm_num : 0 < 2)
  obtain ⟨s₃, hs₃⟩ := IsAlgClosed.exists_pow_nat_eq
    (γ₃ : AlgebraicClosure ℚ) (by norm_num : 0 < 2)
  let : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    @Algebra.IsAlgebraic.isIntegral ℚ (AlgebraicClosure ℚ) _ _ _
      (AlgebraicClosure.isAlgebraic ℚ)
  let hfin : FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ
        ({s₁, s₂, s₃} : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦
      Algebra.IsIntegral.isIntegral x
  have htower := finrank_sqRoot_tower_product_le_eight
    s₁ s₂ s₃ (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
    (by simpa using hs₁) (by simpa using hs₂) (by simpa using hs₃)
  have hall := finrank_adjoin_three_sqRoots_le_eight
    s₁ s₂ s₃ (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
    (by simpa using hs₁) (by simpa using hs₂) (by simpa using hs₃)
  exact ⟨s₁, s₂, s₃, hs₁, hs₂, hs₃, htower, hall, ⟨hfin⟩⟩

lemma eval_pellDifferenceZ (γa γb xa xb : ℤ) (a b : Fin 3)
    (v : Fin 3 → ℤ) (ha : v a = xa) (hb : v b = xb) :
    MvPolynomial.eval v (pellDifferenceZ γa γb a b) =
      γa * xa ^ 2 - γb * xb ^ 2 := by
  simp [pellDifferenceZ, ha, hb]

/-- Every simultaneous Pell solution lies on the corresponding connected
decomposable-form equation.  The third factor is the difference of the
two right-hand sides. -/
lemma simultaneousPellZ_eval_form
    {γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃ : ℤ}
    (h : SimultaneousPellZ γ₁ γ₂ γ₃ β₁₂ β₁₃ x₁ x₂ x₃) :
    MvPolynomial.eval ![x₁, x₂, x₃]
        (simultaneousPellFormZ γ₁ γ₂ γ₃) =
      β₁₂ * β₁₃ * (β₁₃ - β₁₂) := by
  rcases h with ⟨h₁₂, h₁₃⟩
  have h₂₃ : γ₂ * x₂ ^ 2 - γ₃ * x₃ ^ 2 = β₁₃ - β₁₂ := by
    nlinarith
  simp only [simultaneousPellFormZ, map_mul]
  rw [eval_pellDifferenceZ γ₁ γ₂ x₁ x₂ 0 1 ![x₁, x₂, x₃] (by simp) (by simp),
    eval_pellDifferenceZ γ₁ γ₃ x₁ x₃ 0 2 ![x₁, x₂, x₃] (by simp) (by simp),
    eval_pellDifferenceZ γ₂ γ₃ x₂ x₃ 1 2 ![x₁, x₂, x₃] (by simp) (by simp),
    h₁₂, h₁₃, h₂₃]

/-- Distinct shifts make the right-hand side of the decomposable-form
equation nonzero, exactly as required in BEG Proposition 3.12. -/
lemma three_shift_pell_rhs_ne_zero {i j k : ℕ}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (((i : ℤ) - j) * ((i : ℤ) - k) *
      (((i : ℤ) - k) - ((i : ℤ) - j))) ≠ 0 := by
  have hijZ : (i : ℤ) - j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij)
  have hikZ : (i : ℤ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hik)
  have hjkZ : ((i : ℤ) - k) - ((i : ℤ) - j) ≠ 0 := by
    intro h
    have hjkCast : (j : ℤ) ≠ k := by exact_mod_cast hjk
    apply hjkCast
    linarith
  exact mul_ne_zero (mul_ne_zero hijZ hikZ) hjkZ

/-- Complete algebraic reduction of three shifted decompositions to a
nonzero value of the homogeneous degree-six Pell form. -/
lemma three_shift_decomposable_form_equation
    {n i j k zi zj zk bi bj bk : ℕ}
    (hi : zi ^ 2 * bi = n + i)
    (hj : zj ^ 2 * bj = n + j)
    (hk : zk ^ 2 * bk = n + k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MvPolynomial.eval ![(zi : ℤ), (zj : ℤ), (zk : ℤ)]
        (simultaneousPellFormZ bi bj bk) =
          ((i : ℤ) - j) * ((i : ℤ) - k) *
            (((i : ℤ) - k) - ((i : ℤ) - j)) ∧
      (((i : ℤ) - j) * ((i : ℤ) - k) *
        (((i : ℤ) - k) - ((i : ℤ) - j))) ≠ 0 := by
  exact ⟨simultaneousPellZ_eval_form
      (three_shift_simultaneousPellZ hi hj hk),
    three_shift_pell_rhs_ne_zero hij hik hjk⟩

/-- A quadratic factor of BPZ's auxiliary quartic. -/
def shiftQuadratic (b : ℕ) (d : ℤ) : Polynomial ℚ :=
  Polynomial.C (b : ℚ) * Polynomial.X ^ 2 + Polynomial.C (d : ℚ)

lemma separable_shiftQuadratic {b : ℕ} {d : ℤ} (hb : 0 < b) (hd : d ≠ 0) :
    (shiftQuadratic b d).Separable := by
  let a : ℚ := -(d : ℚ) / (b : ℚ)
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have ha : a ≠ 0 := by
    dsimp [a]
    exact div_ne_zero (neg_ne_zero.mpr hdQ) hbQ
  have hbase : (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℚ).Separable :=
    Polynomial.separable_X_pow_sub_C a (by norm_num) ha
  have hunit : IsUnit (Polynomial.C (b : ℚ) : Polynomial ℚ) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbQ)
  have hscalar : (d : ℚ) = -(b : ℚ) * a := by
    dsimp [a]
    field_simp
  have hscalar' : (d : ℚ) = -((b : ℚ) * a) := by
    rw [hscalar]
    ring
  have heq : shiftQuadratic b d =
      Polynomial.C (b : ℚ) * (Polynomial.X ^ 2 - Polynomial.C a) := by
    dsimp [shiftQuadratic]
    rw [mul_sub, hscalar', Polynomial.C_neg, Polynomial.C.map_mul]
    ring
  rw [heq]
  exact hbase.unit_mul hunit

lemma isCoprime_shiftQuadratic {b : ℕ} {d e : ℤ} (hde : d ≠ e) :
    IsCoprime (shiftQuadratic b d) (shiftQuadratic b e) := by
  have hdeQ : (d : ℚ) - (e : ℚ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hde)
  have hunit : IsUnit
      (Polynomial.C ((d : ℚ) - (e : ℚ)) : Polynomial ℚ) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hdeQ)
  have hdiff : (Polynomial.C ((d : ℚ) - (e : ℚ)) : Polynomial ℚ) =
      Polynomial.C (d : ℚ) - Polynomial.C (e : ℚ) :=
    Polynomial.C.map_sub (d : ℚ) (e : ℚ)
  have hbase : IsCoprime
      (Polynomial.C ((d : ℚ) - (e : ℚ)) : Polynomial ℚ)
      (shiftQuadratic b e) := by
    simpa using
      ((isCoprime_mul_unit_left_left hunit 1 (shiftQuadratic b e)).mpr
        isCoprime_one_left)
  have hadd := hbase.add_mul_left_left (1 : Polynomial ℚ)
  rw [mul_one, hdiff] at hadd
  have heq :
      (Polynomial.C (d : ℚ) - Polynomial.C (e : ℚ) : Polynomial ℚ) +
          shiftQuadratic b e = shiftQuadratic b d := by
    dsimp [shiftQuadratic]
    abel
  rw [heq] at hadd
  exact hadd

/-- BPZ's fixed-degree auxiliary quartic over `ℚ`. -/
def auxiliaryQuartic (bi bj bk i j k : ℕ) : Polynomial ℚ :=
  Polynomial.C ((bj * bk : ℕ) : ℚ) *
    shiftQuadratic bi ((j : ℤ) - i) *
    shiftQuadratic bi ((k : ℤ) - i)

lemma auxiliaryQuartic_separable
    {bi bj bk i j k : ℕ} (hbi : 0 < bi) (hbj : 0 < bj) (hbk : 0 < bk)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (auxiliaryQuartic bi bj bk i j k).Separable := by
  have hdj : (j : ℤ) - i ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij.symm)
  have hdk : (k : ℤ) - i ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hik.symm)
  have hdjk : (j : ℤ) - i ≠ (k : ℤ) - i := by
    intro h
    apply hjk
    exact_mod_cast sub_left_injective h
  have hprod : (shiftQuadratic bi ((j : ℤ) - i) *
      shiftQuadratic bi ((k : ℤ) - i)).Separable :=
    (separable_shiftQuadratic hbi hdj).mul
      (separable_shiftQuadratic hbi hdk)
      (isCoprime_shiftQuadratic hdjk)
  have hunit : IsUnit (Polynomial.C ((bj * bk : ℕ) : ℚ) : Polynomial ℚ) := by
    apply Polynomial.isUnit_C.mpr
    rw [isUnit_iff_ne_zero]
    exact_mod_cast (Nat.mul_ne_zero hbj.ne' hbk.ne')
  simpa [auxiliaryQuartic, mul_assoc] using hprod.unit_mul hunit

lemma auxiliaryQuartic_integral_point
    {n i j k zi zj zk bi bj bk : ℕ}
    (hi : zi ^ 2 * bi = n + i)
    (hj : zj ^ 2 * bj = n + j)
    (hk : zk ^ 2 * bk = n + k) :
    (((bj * bk * zj * zk : ℕ) : ℚ) ^ 2) =
      (auxiliaryQuartic bi bj bk i j k).eval (zi : ℚ) := by
  have hZ := three_shift_quartic_identity hi hj hk
  have hQ := congrArg (fun z : ℤ ↦ (z : ℚ)) hZ
  simpa [auxiliaryQuartic, shiftQuadratic] using hQ

/-! ### Integral model and explicit coefficient height -/

/-- A coefficient-wise height bound for an integral polynomial. -/
def IntPolynomialCoeffBound (P : Polynomial ℤ) (H : ℕ) : Prop :=
  ∀ r : ℕ, Int.natAbs (P.coeff r) ≤ H

/-- The exact rational-integer specialization of Bérczes--Evertse--Győry,
Theorem 2.2, used by BPZ as Lemma 6.2.  It is kept as a proposition while
its proof is developed, so intermediate reduction lemmas can state their
dependency without adding a primitive or unchecked declaration. -/
def EffectiveHyperellipticHeightBound : Prop :=
  ∀ (P : Polynomial ℤ) (d H x y : ℕ),
    P.natDegree = d → 3 ≤ d →
    (P.map (Int.castRingHom ℚ)).Separable →
    IntPolynomialCoeffBound P H →
    0 < x → 0 < y →
    ((y : ℤ) ^ 2 = P.eval (x : ℤ)) →
    Real.log (x : ℝ) ≤
      (((4 * d : ℕ) : ℝ) ^ (212 * d ^ 4)) *
        ((H : ℝ) ^ (50 * d ^ 4))

/-- Taking one further logarithm in the effective height estimate.  This
elementary interface is reused by both BPZ branches. -/
lemma log_log_le_of_effective_height
    {d H x : ℕ} (hd : 0 < d) (hH : 0 < H) (hx : 1 < x)
    (hbound : Real.log (x : ℝ) ≤
      (((4 * d : ℕ) : ℝ) ^ (212 * d ^ 4)) *
        ((H : ℝ) ^ (50 * d ^ 4))) :
    Real.log (Real.log (x : ℝ)) ≤
      (212 * d ^ 4 : ℕ) * Real.log ((4 * d : ℕ) : ℝ) +
        (50 * d ^ 4 : ℕ) * Real.log (H : ℝ) := by
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hC : (0 : ℝ) < ((4 * d : ℕ) : ℝ) := by positivity
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hRHS : (0 : ℝ) <
      (((4 * d : ℕ) : ℝ) ^ (212 * d ^ 4)) *
        ((H : ℝ) ^ (50 * d ^ 4)) := by positivity
  calc
    Real.log (Real.log (x : ℝ)) ≤
        Real.log
          ((((4 * d : ℕ) : ℝ) ^ (212 * d ^ 4)) *
            ((H : ℝ) ^ (50 * d ^ 4))) := by
      exact Real.strictMonoOn_log.monotoneOn hlogx hRHS hbound
    _ = (212 * d ^ 4 : ℕ) * Real.log ((4 * d : ℕ) : ℝ) +
          (50 * d ^ 4 : ℕ) * Real.log (H : ℝ) := by
      rw [Real.log_mul (pow_ne_zero _ hC.ne') (pow_ne_zero _ hHR.ne'),
        Real.log_pow, Real.log_pow]

/-- Convert a bound for the square-root coordinate of a shifted
squarefree decomposition into a bound for the original `n`. -/
lemma log_log_le_of_squarefactor_height
    {n i z b H C K : ℕ} (hn : 1 < n) (hz : 0 < z) (hb : 0 < b)
    (hH : 0 < H) (hC : 0 < C) (hbH : b ≤ H)
    (hdecomp : z ^ 2 * b = n + i)
    (hroot : Real.log (z : ℝ) ≤
      (C : ℝ) * (H : ℝ) ^ K) :
    Real.log (Real.log (n : ℝ)) ≤
      Real.log ((3 * C : ℕ) : ℝ) +
        (K + 1 : ℕ) * Real.log (H : ℝ) := by
  have hNone : 1 ≤ H := hH
  have hCone : 1 ≤ C := hC
  have hnle : n ≤ z ^ 2 * H := by
    calc
      n ≤ n + i := Nat.le_add_right n i
      _ = z ^ 2 * b := hdecomp.symm
      _ ≤ z ^ 2 * H := Nat.mul_le_mul_left _ hbH
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hprodR : (0 : ℝ) < (z : ℝ) ^ 2 * (H : ℝ) := by positivity
  have hlogn : Real.log (n : ℝ) ≤
      2 * Real.log (z : ℝ) + Real.log (H : ℝ) := by
    calc
      Real.log (n : ℝ) ≤
          Real.log ((z : ℝ) ^ 2 * (H : ℝ)) := by
        apply Real.strictMonoOn_log.monotoneOn hnpos hprodR
        exact_mod_cast hnle
      _ = 2 * Real.log (z : ℝ) + Real.log (H : ℝ) := by
        rw [Real.log_mul (pow_ne_zero _ hzR.ne') hHR.ne', Real.log_pow]
        norm_num
  have hlogHle : Real.log (H : ℝ) ≤ (H : ℝ) := by
    calc
      Real.log (H : ℝ) ≤ (H : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hHR
      _ ≤ (H : ℝ) := by linarith
  have hpowmono : (H : ℝ) ^ K ≤ (H : ℝ) ^ (K + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hNone)
  have hBmono : (C : ℝ) * (H : ℝ) ^ K ≤
      (C : ℝ) * (H : ℝ) ^ (K + 1) := by
    gcongr
  have hHmono : (H : ℝ) ≤
      (C : ℝ) * (H : ℝ) ^ (K + 1) := by
    have hpowone : (1 : ℝ) ≤ (H : ℝ) ^ K :=
      one_le_pow₀ (by exact_mod_cast hNone)
    have hConeR : (1 : ℝ) ≤ C := by exact_mod_cast hCone
    have hCHone : (1 : ℝ) ≤ (C : ℝ) * (H : ℝ) ^ K := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (C : ℝ) * (H : ℝ) ^ K :=
          mul_le_mul hConeR hpowone (by norm_num) (by norm_num)
    calc
      (H : ℝ) = 1 * (H : ℝ) := by ring
      _ ≤ ((C : ℝ) * (H : ℝ) ^ K) * (H : ℝ) := by
        exact mul_le_mul_of_nonneg_right hCHone (by positivity)
      _ = (C : ℝ) * (H : ℝ) ^ (K + 1) := by
        rw [pow_succ]
        ring
  have hlarge : Real.log (n : ℝ) ≤
      3 * (C : ℝ) * (H : ℝ) ^ (K + 1) := by
    calc
      Real.log (n : ℝ) ≤
          2 * Real.log (z : ℝ) + Real.log (H : ℝ) := hlogn
      _ ≤ 2 * ((C : ℝ) * (H : ℝ) ^ K) + (H : ℝ) := by
        gcongr
      _ ≤ 3 * (C : ℝ) * (H : ℝ) ^ (K + 1) := by
        nlinarith
  have hlognpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hbigpos : (0 : ℝ) <
      3 * (C : ℝ) * (H : ℝ) ^ (K + 1) := by positivity
  calc
    Real.log (Real.log (n : ℝ)) ≤
        Real.log (3 * (C : ℝ) * (H : ℝ) ^ (K + 1)) :=
      Real.strictMonoOn_log.monotoneOn hlognpos hbigpos hlarge
    _ = Real.log ((3 * C : ℕ) : ℝ) +
          (K + 1 : ℕ) * Real.log (H : ℝ) := by
      rw [Real.log_mul (mul_ne_zero (by norm_num) (by exact_mod_cast hC.ne'))
        (pow_ne_zero _ hHR.ne'), Real.log_pow]
      norm_num

/-- The integral quadratic factor underlying `shiftQuadratic`. -/
def shiftQuadraticZ (b : ℕ) (d : ℤ) : Polynomial ℤ :=
  Polynomial.C (b : ℤ) * Polynomial.X ^ 2 + Polynomial.C d

/-- The integral model of the auxiliary quartic. -/
def auxiliaryQuarticZ (bi bj bk i j k : ℕ) : Polynomial ℤ :=
  Polynomial.C (bj * bk : ℤ) *
    shiftQuadraticZ bi ((j : ℤ) - i) *
    shiftQuadraticZ bi ((k : ℤ) - i)

lemma auxiliaryQuarticZ_map_rat (bi bj bk i j k : ℕ) :
    (auxiliaryQuarticZ bi bj bk i j k).map (Int.castRingHom ℚ) =
      auxiliaryQuartic bi bj bk i j k := by
  simp [auxiliaryQuarticZ, auxiliaryQuartic, shiftQuadraticZ,
    shiftQuadratic]

lemma auxiliaryQuarticZ_integral_point
    {n i j k zi zj zk bi bj bk : ℕ}
    (hi : zi ^ 2 * bi = n + i)
    (hj : zj ^ 2 * bj = n + j)
    (hk : zk ^ 2 * bk = n + k) :
    ((bj * bk * zj * zk : ℕ) : ℤ) ^ 2 =
      (auxiliaryQuarticZ bi bj bk i j k).eval (zi : ℤ) := by
  have hZ := three_shift_quartic_identity hi hj hk
  simpa [auxiliaryQuarticZ, shiftQuadraticZ] using hZ

/-- The maximum of the three possibly nonzero coefficient magnitudes of
the auxiliary quartic.  Writing it explicitly avoids hiding coefficient
bookkeeping in an asymptotic `O`-term. -/
def auxiliaryQuarticCoeffHeight (bi bj bk i j k : ℕ) : ℕ :=
  max (bj * bk * bi ^ 2)
    (max
      (bj * bk * bi * Int.natAbs (((j : ℤ) - i) + ((k : ℤ) - i)))
      (bj * bk * Int.natAbs (((j : ℤ) - i) * ((k : ℤ) - i))))

lemma auxiliaryQuarticZ_explicit (bi bj bk i j k : ℕ) :
    auxiliaryQuarticZ bi bj bk i j k =
      Polynomial.C ((bj * bk * bi ^ 2 : ℕ) : ℤ) * Polynomial.X ^ 4 +
      Polynomial.C
          (((bj * bk * bi : ℕ) : ℤ) *
            (((j : ℤ) - i) + ((k : ℤ) - i))) * Polynomial.X ^ 2 +
      Polynomial.C
        (((bj * bk : ℕ) : ℤ) * (((j : ℤ) - i) * ((k : ℤ) - i))) := by
  simp only [auxiliaryQuarticZ, shiftQuadraticZ]
  push_cast
  simp only [Polynomial.C.map_add, Polynomial.C.map_mul,
    Polynomial.C.map_pow]
  ring

lemma auxiliaryQuarticZ_eq_trinomial (bi bj bk i j k : ℕ) :
    auxiliaryQuarticZ bi bj bk i j k =
      Polynomial.trinomial 0 2 4
        (((bj * bk : ℕ) : ℤ) * (((j : ℤ) - i) * ((k : ℤ) - i)))
        (((bj * bk * bi : ℕ) : ℤ) *
          (((j : ℤ) - i) + ((k : ℤ) - i)))
        ((bj * bk * bi ^ 2 : ℕ) : ℤ) := by
  rw [auxiliaryQuarticZ_explicit, Polynomial.trinomial_def]
  ring

lemma auxiliaryQuarticZ_coeff_bound (bi bj bk i j k : ℕ) :
    IntPolynomialCoeffBound (auxiliaryQuarticZ bi bj bk i j k)
      (auxiliaryQuarticCoeffHeight bi bj bk i j k) := by
  intro r
  rw [auxiliaryQuarticZ_eq_trinomial]
  by_cases hr0 : r = 0
  · subst r
    rw [Polynomial.trinomial_trailing_coeff' (by omega) (by omega)]
    simp [auxiliaryQuarticCoeffHeight, Int.natAbs_mul]
  by_cases hr2 : r = 2
  · subst r
    rw [Polynomial.trinomial_middle_coeff (by omega) (by omega)]
    simp [auxiliaryQuarticCoeffHeight, Int.natAbs_mul]
  by_cases hr4 : r = 4
  · subst r
    rw [Polynomial.trinomial_leading_coeff' (by omega) (by omega)]
    simp [auxiliaryQuarticCoeffHeight, Int.natAbs_mul]
  · rw [Polynomial.trinomial_def]
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow, if_neg hr0, if_neg hr2, if_neg hr4]
    simp

lemma auxiliaryQuarticZ_natDegree {bi bj bk i j k : ℕ}
    (hbi : 0 < bi) (hbj : 0 < bj) (hbk : 0 < bk) :
    (auxiliaryQuarticZ bi bj bk i j k).natDegree = 4 := by
  rw [auxiliaryQuarticZ_eq_trinomial]
  apply Polynomial.trinomial_natDegree (by omega) (by omega)
  exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero hbj.ne' hbk.ne')
    (pow_ne_zero 2 hbi.ne')

lemma auxiliaryQuarticCoeffHeight_le
    {bi bj bk i j k J Q : ℕ}
    (hi : i ≤ J) (hj : j ≤ J) (hk : k ≤ J)
    (hbi : bi ≤ Q) (hbj : bj ≤ Q) (hbk : bk ≤ Q) :
    auxiliaryQuarticCoeffHeight bi bj bk i j k ≤
      (2 * (J + 1) * (Q + 1)) ^ 4 := by
  let M := 2 * (J + 1) * (Q + 1)
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hJM : J ≤ M := by
    dsimp [M]
    nlinarith
  have hQM : Q ≤ M := by
    dsimp [M]
    nlinarith
  have hbiM : bi ≤ M := hbi.trans hQM
  have hbjM : bj ≤ M := hbj.trans hQM
  have hbkM : bk ≤ M := hbk.trans hQM
  have hdj : Int.natAbs ((j : ℤ) - i) ≤ J :=
    Int.natAbs_coe_sub_coe_le_of_le hj hi
  have hdk : Int.natAbs ((k : ℤ) - i) ≤ J :=
    Int.natAbs_coe_sub_coe_le_of_le hk hi
  have hsum : Int.natAbs (((j : ℤ) - i) + ((k : ℤ) - i)) ≤ M := by
    calc
      Int.natAbs (((j : ℤ) - i) + ((k : ℤ) - i)) ≤
          Int.natAbs ((j : ℤ) - i) + Int.natAbs ((k : ℤ) - i) :=
        Int.natAbs_add_le _ _
      _ ≤ J + J := Nat.add_le_add hdj hdk
      _ ≤ M := by
        dsimp [M]
        nlinarith
  have hprod : Int.natAbs (((j : ℤ) - i) * ((k : ℤ) - i)) ≤ M ^ 2 := by
    rw [Int.natAbs_mul]
    calc
      Int.natAbs ((j : ℤ) - i) * Int.natAbs ((k : ℤ) - i) ≤ J * J :=
        Nat.mul_le_mul hdj hdk
      _ ≤ M ^ 2 := by
        simpa [pow_two] using Nat.mul_self_le_mul_self hJM
  rw [auxiliaryQuarticCoeffHeight, max_le_iff, max_le_iff]
  constructor
  · calc
      bj * bk * bi ^ 2 ≤ M * M * M ^ 2 := by gcongr
      _ = M ^ 4 := by ring
  constructor
  · calc
      bj * bk * bi *
          Int.natAbs (((j : ℤ) - i) + ((k : ℤ) - i)) ≤ M * M * M * M := by
        gcongr
      _ = M ^ 4 := by ring
  · calc
      bj * bk * Int.natAbs (((j : ℤ) - i) * ((k : ℤ) - i)) ≤
          M * M * M ^ 2 := by gcongr
      _ = M ^ 4 := by ring

private lemma max_three_pow_le {a b c R X : ℕ}
    (ha : a ^ R ≤ X) (hb : b ^ R ≤ X) (hc : c ^ R ≤ X) :
    max a (max b c) ^ R ≤ X := by
  by_cases haMax : a ≤ max b c
  · rw [max_eq_right haMax]
    by_cases hbc : b ≤ c
    · rwa [max_eq_right hbc]
    · rw [max_eq_left (Nat.le_of_not_ge hbc)]
      exact hb
  · rw [max_eq_left (Nat.le_of_not_ge haMax)]
    exact ha

/-- Raising the coefficient height to the retained support factor makes the
division-free sparse bounds usable directly.  This is the precise finite
counterpart of `log H = O(E/R + log J)`. -/
lemma auxiliaryQuarticCoeffHeight_pow_le
    {bi bj bk i j k J R E : ℕ}
    (hi : i ≤ J) (hj : j ≤ J) (hk : k ≤ J)
    (hbi : 0 < bi) (hbj : 0 < bj) (hbk : 0 < bk)
    (hbiPow : bi ^ R ≤ J ^ E) (hbjPow : bj ^ R ≤ J ^ E)
    (hbkPow : bk ^ R ≤ J ^ E) :
    auxiliaryQuarticCoeffHeight bi bj bk i j k ^ R ≤
      (4 * (J + 1)) ^ (4 * R) * J ^ (4 * E) := by
  let Q := max bi (max bj bk)
  let M := 2 * (J + 1) * (Q + 1)
  let A := 4 * (J + 1)
  have hbiQ : bi ≤ Q := by
    dsimp [Q]
    exact le_max_left _ _
  have hbjQ : bj ≤ Q := by
    dsimp [Q]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hbkQ : bk ≤ Q := by
    dsimp [Q]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hQpos : 0 < Q := hbi.trans_le hbiQ
  have hQpow : Q ^ R ≤ J ^ E := by
    dsimp [Q]
    exact max_three_pow_le hbiPow hbjPow hbkPow
  have hheight : auxiliaryQuarticCoeffHeight bi bj bk i j k ≤ M ^ 4 := by
    dsimp [M]
    exact auxiliaryQuarticCoeffHeight_le hi hj hk hbiQ hbjQ hbkQ
  have hQplus : Q + 1 ≤ 2 * Q := by omega
  have hMA : M ≤ A * Q := by
    dsimp [M, A]
    calc
      2 * (J + 1) * (Q + 1) ≤ 2 * (J + 1) * (2 * Q) := by gcongr
      _ = 4 * (J + 1) * Q := by ring
  calc
    auxiliaryQuarticCoeffHeight bi bj bk i j k ^ R ≤ (M ^ 4) ^ R :=
      Nat.pow_le_pow_left hheight R
    _ = M ^ (4 * R) := by rw [pow_mul]
    _ ≤ (A * Q) ^ (4 * R) := Nat.pow_le_pow_left hMA _
    _ = A ^ (4 * R) * Q ^ (4 * R) := by rw [mul_pow]
    _ = A ^ (4 * R) * (Q ^ R) ^ 4 := by
      congr 1
      rw [Nat.mul_comm 4 R, ← pow_mul]
    _ ≤ A ^ (4 * R) * (J ^ E) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQpow 4)
    _ = A ^ (4 * R) * J ^ (4 * E) := by
      congr 1
      rw [Nat.mul_comm 4 E, ← pow_mul]

/-- Complete finite auxiliary-curve package for the large-support case:
three distinct shifts, their canonical squarefree decompositions, a separable
quartic, its integral point, and the explicit retained-power height bound. -/
theorem exists_sparse_auxiliary_quartic
    {n J : ℕ} {I : Finset ℕ} (hn : 0 < n)
    (hI : I ⊆ Finset.Icc 0 J) (hcard : 3 ≤ I.card)
    (hJ : 1 ≤ J) (hsquare : IsSquare (∏ a ∈ I, (n + a))) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ k ∈ I,
      ∃ zi zj zk bi bj bk : ℕ,
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        0 < bi ∧ 0 < bj ∧ 0 < bk ∧
        zi ^ 2 * bi = n + i ∧
        zj ^ 2 * bj = n + j ∧
        zk ^ 2 * bk = n + k ∧
        (auxiliaryQuartic bi bj bk i j k).Separable ∧
        (((bj * bk * zj * zk : ℕ) : ℚ) ^ 2) =
          (auxiliaryQuartic bi bj bk i j k).eval (zi : ℚ) ∧
        auxiliaryQuarticCoeffHeight bi bj bk i j k ^ (I.card - 2) ≤
          (4 * (J + 1)) ^ (4 * (I.card - 2)) *
            J ^ (4 * (Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J)) := by
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hiPow, hjPow, hkPow⟩ :=
    exists_three_sparse_shifts_with_power_bounds hn hI hcard hJ hsquare
  let zi := squareRootPart (n + i)
  let zj := squareRootPart (n + j)
  let zk := squareRootPart (n + k)
  let bi := squarefreePart (n + i)
  let bj := squarefreePart (n + j)
  let bk := squarefreePart (n + k)
  have hbi : 0 < bi := squarefreePart_pos (by omega)
  have hbj : 0 < bj := squarefreePart_pos (by omega)
  have hbk : 0 < bk := squarefreePart_pos (by omega)
  have hzi : zi ^ 2 * bi = n + i := squareRootPart_sq_mul_squarefreePart _
  have hzj : zj ^ 2 * bj = n + j := squareRootPart_sq_mul_squarefreePart _
  have hzk : zk ^ 2 * bk = n + k := squareRootPart_sq_mul_squarefreePart _
  have hiJ : i ≤ J := (Finset.mem_Icc.mp (hI hi)).2
  have hjJ : j ≤ J := (Finset.mem_Icc.mp (hI hj)).2
  have hkJ : k ≤ J := (Finset.mem_Icc.mp (hI hk)).2
  have hsep := auxiliaryQuartic_separable hbi hbj hbk hij hik hjk
  have hpoint := auxiliaryQuartic_integral_point hzi hzj hzk
  have hheight := auxiliaryQuarticCoeffHeight_pow_le hiJ hjJ hkJ hbi hbj hbk
    (by simpa [bi] using hiPow) (by simpa [bj] using hjPow)
    (by simpa [bk] using hkPow)
  exact ⟨i, hi, j, hj, k, hk, zi, zj, zk, bi, bj, bk,
    hij, hik, hjk, hbi, hbj, hbk, hzi, hzj, hzk, hsep, hpoint, hheight⟩

/-- The auxiliary-quartic package after restricting a full square-product
witness to a subfamily of a chosen cardinality. -/
theorem exists_sparse_auxiliary_quartic_subfamily
    {n J : ℕ} {I K : Finset ℕ} (hn : 0 < n)
    (hI : I ⊆ Finset.Icc 0 J) (hK : K ⊆ I) (hcard : 3 ≤ K.card)
    (hJ : 1 ≤ J) (hsquare : IsSquare (∏ a ∈ I, (n + a))) :
    ∃ i ∈ K, ∃ j ∈ K, ∃ k ∈ K,
      ∃ zi zj zk bi bj bk : ℕ,
        i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        0 < bi ∧ 0 < bj ∧ 0 < bk ∧
        zi ^ 2 * bi = n + i ∧
        zj ^ 2 * bj = n + j ∧
        zk ^ 2 * bk = n + k ∧
        (auxiliaryQuartic bi bj bk i j k).Separable ∧
        (((bj * bk * zj * zk : ℕ) : ℚ) ^ 2) =
          (auxiliaryQuartic bi bj bk i j k).eval (zi : ℚ) ∧
        auxiliaryQuarticCoeffHeight bi bj bk i j k ^ (K.card - 2) ≤
          (4 * (J + 1)) ^ (4 * (K.card - 2)) *
            J ^ (4 * (Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J)) := by
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, hiPow, hjPow, hkPow⟩ :=
    exists_three_sparse_shifts_with_power_bounds_subfamily
      hn hI hK hcard hJ hsquare
  let zi := squareRootPart (n + i)
  let zj := squareRootPart (n + j)
  let zk := squareRootPart (n + k)
  let bi := squarefreePart (n + i)
  let bj := squarefreePart (n + j)
  let bk := squarefreePart (n + k)
  have hbi : 0 < bi := squarefreePart_pos (by omega)
  have hbj : 0 < bj := squarefreePart_pos (by omega)
  have hbk : 0 < bk := squarefreePart_pos (by omega)
  have hzi : zi ^ 2 * bi = n + i := squareRootPart_sq_mul_squarefreePart _
  have hzj : zj ^ 2 * bj = n + j := squareRootPart_sq_mul_squarefreePart _
  have hzk : zk ^ 2 * bk = n + k := squareRootPart_sq_mul_squarefreePart _
  have hiJ : i ≤ J := (Finset.mem_Icc.mp (hI (hK hi))).2
  have hjJ : j ≤ J := (Finset.mem_Icc.mp (hI (hK hj))).2
  have hkJ : k ≤ J := (Finset.mem_Icc.mp (hI (hK hk))).2
  have hsep := auxiliaryQuartic_separable hbi hbj hbk hij hik hjk
  have hpoint := auxiliaryQuartic_integral_point hzi hzj hzk
  have hheight := auxiliaryQuarticCoeffHeight_pow_le hiJ hjJ hkJ hbi hbj hbk
    (by simpa [bi] using hiPow) (by simpa [bj] using hjPow)
    (by simpa [bk] using hkPow)
  exact ⟨i, hi, j, hj, k, hk, zi, zj, zk, bi, bj, bk,
    hij, hik, hjk, hbi, hbj, hbk, hzi, hzj, hzk, hsep, hpoint, hheight⟩

/-- The large-support branch with the Bérczes--Evertse--Győry estimate
inserted.  Besides the logarithmic bound for the selected square root, the
statement retains BPZ's division-free coefficient-height estimate; this is
the form needed for the subsequent balancing argument. -/
theorem exists_sparse_auxiliary_height_bound
    (heffective : EffectiveHyperellipticHeightBound)
    {n J : ℕ} {I : Finset ℕ} (hn : 0 < n)
    (hI : I ⊆ Finset.Icc 0 J) (hcard : 3 ≤ I.card)
    (hJ : 1 ≤ J) (hsquare : IsSquare (∏ a ∈ I, (n + a))) :
    ∃ i ∈ I, ∃ j ∈ I, ∃ k ∈ I,
      ∃ zi zj zk bi bj bk : ℕ,
        0 < zi ∧ 0 < zj ∧ 0 < zk ∧
        0 < bi ∧ 0 < bj ∧ 0 < bk ∧
        zi ^ 2 * bi = n + i ∧
        zj ^ 2 * bj = n + j ∧
        zk ^ 2 * bk = n + k ∧
        Real.log (zi : ℝ) ≤
          (((4 * 4 : ℕ) : ℝ) ^ (212 * 4 ^ 4)) *
            ((auxiliaryQuarticCoeffHeight bi bj bk i j k : ℝ) ^
              (50 * 4 ^ 4)) ∧
        auxiliaryQuarticCoeffHeight bi bj bk i j k ^ (I.card - 2) ≤
          (4 * (J + 1)) ^ (4 * (I.card - 2)) *
            J ^ (4 * (Nat.primeCounting J + I.card ^ 2 * Nat.log 2 J)) := by
  obtain ⟨i, hi, j, hj, k, hk, zi, zj, zk, bi, bj, bk,
      hij, hik, hjk, hbi, hbj, hbk, hdeci, hdecj, hdeck, hsep, _hpoint,
      hheightPow⟩ :=
    exists_sparse_auxiliary_quartic hn hI hcard hJ hsquare
  have hzi : 0 < zi := by
    by_contra hz
    have hz0 : zi = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz0] at hdeci
    simp at hdeci
    omega
  have hzj : 0 < zj := by
    by_contra hz
    have hz0 : zj = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz0] at hdecj
    simp at hdecj
    omega
  have hzk : 0 < zk := by
    by_contra hz
    have hz0 : zk = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz0] at hdeck
    simp at hdeck
    omega
  have hy : 0 < bj * bk * zj * zk := by positivity
  have hlog := heffective
    (auxiliaryQuarticZ bi bj bk i j k) 4
    (auxiliaryQuarticCoeffHeight bi bj bk i j k) zi
    (bj * bk * zj * zk)
    (auxiliaryQuarticZ_natDegree hbi hbj hbk) (by norm_num) ?_
    (auxiliaryQuarticZ_coeff_bound bi bj bk i j k) hzi hy
    (auxiliaryQuarticZ_integral_point hdeci hdecj hdeck)
  · exact ⟨i, hi, j, hj, k, hk, zi, zj, zk, bi, bj, bk,
      hzi, hzj, hzk, hbi, hbj, hbk, hdeci, hdecj, hdeck, hlog, hheightPow⟩
  · rw [auxiliaryQuarticZ_map_rat]
    exact hsep

/-- Effective-height form of the sparse auxiliary curve for a selected
subfamily of the original minimal witness. -/
theorem exists_sparse_auxiliary_height_bound_subfamily
    (heffective : EffectiveHyperellipticHeightBound)
    {n J : ℕ} {I K : Finset ℕ} (hn : 0 < n)
    (hI : I ⊆ Finset.Icc 0 J) (hK : K ⊆ I) (hcard : 3 ≤ K.card)
    (hJ : 1 ≤ J) (hsquare : IsSquare (∏ a ∈ I, (n + a))) :
    ∃ i ∈ K, ∃ j ∈ K, ∃ k ∈ K,
      ∃ zi zj zk bi bj bk : ℕ,
        0 < zi ∧ 0 < zj ∧ 0 < zk ∧
        0 < bi ∧ 0 < bj ∧ 0 < bk ∧
        zi ^ 2 * bi = n + i ∧
        zj ^ 2 * bj = n + j ∧
        zk ^ 2 * bk = n + k ∧
        Real.log (zi : ℝ) ≤
          (((4 * 4 : ℕ) : ℝ) ^ (212 * 4 ^ 4)) *
            ((auxiliaryQuarticCoeffHeight bi bj bk i j k : ℝ) ^
              (50 * 4 ^ 4)) ∧
        auxiliaryQuarticCoeffHeight bi bj bk i j k ^ (K.card - 2) ≤
          (4 * (J + 1)) ^ (4 * (K.card - 2)) *
            J ^ (4 * (Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J)) := by
  obtain ⟨i, hi, j, hj, k, hk, zi, zj, zk, bi, bj, bk,
      hij, hik, hjk, hbi, hbj, hbk, hdeci, hdecj, hdeck, hsep, _hpoint,
      hheightPow⟩ :=
    exists_sparse_auxiliary_quartic_subfamily hn hI hK hcard hJ hsquare
  have hzi : 0 < zi := by
    by_contra hz
    have hz0 : zi = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz0] at hdeci
    simp at hdeci
    omega
  have hzj : 0 < zj := by
    by_contra hz
    have hz0 : zj = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz0] at hdecj
    simp at hdecj
    omega
  have hzk : 0 < zk := by
    by_contra hz
    have hz0 : zk = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz0] at hdeck
    simp at hdeck
    omega
  have hy : 0 < bj * bk * zj * zk := by positivity
  have hlog := heffective
    (auxiliaryQuarticZ bi bj bk i j k) 4
    (auxiliaryQuarticCoeffHeight bi bj bk i j k) zi
    (bj * bk * zj * zk)
    (auxiliaryQuarticZ_natDegree hbi hbj hbk) (by norm_num) ?_
    (auxiliaryQuarticZ_coeff_bound bi bj bk i j k) hzi hy
    (auxiliaryQuarticZ_integral_point hdeci hdecj hdeck)
  · exact ⟨i, hi, j, hj, k, hk, zi, zj, zk, bi, bj, bk,
      hzi, hzj, hzk, hbi, hbj, hbk, hdeci, hdecj, hdeck, hlog, hheightPow⟩
  · rw [auxiliaryQuarticZ_map_rat]
    exact hsep

/-- Exact retained-factor logarithmic inequality for BPZ's large-support
branch.  It is independent of which three sparse members are selected. -/
theorem sparse_subfamily_loglog_bound
    (heffective : EffectiveHyperellipticHeightBound)
    {n J : ℕ} {I K : Finset ℕ} (hnlarge : 1 < n)
    (hI : I ⊆ Finset.Icc 0 J) (hK : K ⊆ I) (hcard : 3 ≤ K.card)
    (hJ : 1 ≤ J) (hsquare : IsSquare (∏ a ∈ I, (n + a))) :
    ((K.card - 2 : ℕ) : ℝ) * Real.log (Real.log (n : ℝ)) ≤
      ((K.card - 2 : ℕ) : ℝ) *
          Real.log ((3 * (16 ^ (212 * 4 ^ 4)) : ℕ) : ℝ) +
        ((50 * 4 ^ 4 + 1 : ℕ) : ℝ) *
          (((4 * (K.card - 2) : ℕ) : ℝ) *
              Real.log ((4 * (J + 1) : ℕ) : ℝ) +
            ((4 * (Nat.primeCounting J +
                K.card ^ 2 * Nat.log 2 J) : ℕ) : ℝ) *
              Real.log (J : ℝ)) := by
  obtain ⟨i, hi, j, hj, k, hk, zi, zj, zk, bi, bj, bk,
      hzi, hzj, hzk, hbi, hbj, hbk, hdeci, hdecj, hdeck,
      hroot, hheightPow⟩ :=
    exists_sparse_auxiliary_height_bound_subfamily heffective
      (by omega : 0 < n) hI hK hcard hJ hsquare
  let H := auxiliaryQuarticCoeffHeight bi bj bk i j k
  let R := K.card - 2
  let E := Nat.primeCounting J + K.card ^ 2 * Nat.log 2 J
  let A := 4 * (J + 1)
  let C := 16 ^ (212 * 4 ^ 4)
  let L := 50 * 4 ^ 4
  have hR : 0 < R := by dsimp [R]; omega
  have hH : 0 < H := by
    dsimp [H, auxiliaryQuarticCoeffHeight]
    have hlead : 0 < bj * bk * bi ^ 2 := by positivity
    exact hlead.trans_le (le_max_left _ _)
  have hbH : bi ≤ H := by
    have hbiPow : bi ≤ bi ^ 2 := le_self_pow₀ (by omega) (by norm_num)
    have hmul : bi ^ 2 ≤ bj * bk * bi ^ 2 := by
      calc
        bi ^ 2 = 1 * bi ^ 2 := by simp
        _ ≤ (bj * bk) * bi ^ 2 := by
          gcongr
          exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hbj.ne' hbk.ne')
    exact (hbiPow.trans hmul).trans (by
      dsimp [H, auxiliaryQuarticCoeffHeight]
      exact le_max_left _ _)
  have hC : 0 < C := by dsimp [C]; positivity
  have hLL : Real.log (Real.log (n : ℝ)) ≤
      Real.log ((3 * C : ℕ) : ℝ) +
        (L + 1 : ℕ) * Real.log (H : ℝ) := by
    apply log_log_le_of_squarefactor_height hnlarge hzi hbi hH hC hbH hdeci
    have hcastC : (C : ℝ) = (16 : ℝ) ^ (212 * 4 ^ 4) := by
      rw [show C = 16 ^ (212 * 4 ^ 4) by rfl, Nat.cast_pow]
      norm_num
    rw [hcastC]
    have hbase : (((4 * 4 : ℕ) : ℝ)) = 16 := by norm_num
    rw [hbase] at hroot
    simpa only [L, H] using hroot
  have hheightPow' : H ^ R ≤ A ^ (4 * R) * J ^ (4 * E) := by
    simpa [H, R, E, A] using hheightPow
  have hleftPos : (0 : ℝ) < ((H ^ R : ℕ) : ℝ) := by positivity
  have hrightPos : (0 : ℝ) <
      (((A ^ (4 * R) * J ^ (4 * E) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (pow_pos (by dsimp [A]; positivity) _)
      (pow_pos (by omega) _)
  have hpowlog : (R : ℝ) * Real.log (H : ℝ) ≤
      ((4 * R : ℕ) : ℝ) * Real.log (A : ℝ) +
        ((4 * E : ℕ) : ℝ) * Real.log (J : ℝ) := by
    have hlogmono : Real.log ((H ^ R : ℕ) : ℝ) ≤
        Real.log ((A ^ (4 * R) * J ^ (4 * E) : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn hleftPos hrightPos
      exact_mod_cast hheightPow'
    have hAR : (A : ℝ) ≠ 0 := by
      exact_mod_cast (show A ≠ 0 by dsimp [A]; positivity)
    have hJR : (J : ℝ) ≠ 0 := by
      exact_mod_cast (show J ≠ 0 by omega)
    simp only [Nat.cast_pow, Nat.cast_mul] at hlogmono
    rw [Real.log_pow] at hlogmono
    rw [Real.log_mul (pow_ne_zero _ hAR) (pow_ne_zero _ hJR),
      Real.log_pow, Real.log_pow] at hlogmono
    norm_num at hlogmono ⊢
    exact hlogmono
  calc
    (R : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        (R : ℝ) *
          (Real.log ((3 * C : ℕ) : ℝ) +
            (L + 1 : ℕ) * Real.log (H : ℝ)) := by
      gcongr
    _ = (R : ℝ) * Real.log ((3 * C : ℕ) : ℝ) +
          ((L + 1 : ℕ) : ℝ) *
            ((R : ℝ) * Real.log (H : ℝ)) := by ring
    _ ≤ (R : ℝ) * Real.log ((3 * C : ℕ) : ℝ) +
          ((L + 1 : ℕ) : ℝ) *
            (((4 * R : ℕ) : ℝ) * Real.log (A : ℝ) +
              ((4 * E : ℕ) : ℝ) * Real.log (J : ℝ)) := by
      gcongr
    _ = _ := by rfl

/-! ### The direct shifted-product curve for the small-support case -/

/-- Product of the shifted linear factors over the naturals.  Positivity of
its coefficients makes the coefficient-height estimate elementary. -/
def shiftedProductN (I : Finset ℕ) : Polynomial ℕ :=
  ∏ a ∈ I, (Polynomial.X + Polynomial.C a)

/-- Integral model of the shifted-product curve. -/
def shiftedProductZ (I : Finset ℕ) : Polynomial ℤ :=
  (shiftedProductN I).map (Nat.castRingHom ℤ)

/-- Rational model used to express absence of repeated roots. -/
def shiftedProductQ (I : Finset ℕ) : Polynomial ℚ :=
  ∏ a ∈ I, (Polynomial.X + Polynomial.C (a : ℚ))

lemma natPolynomial_coeff_le_eval_one (P : Polynomial ℕ) (r : ℕ) :
    P.coeff r ≤ P.eval 1 := by
  rw [Polynomial.eval_eq_sum]
  simp only [one_pow, mul_one]
  by_cases hr : r ∈ P.support
  · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hr
  · rw [Polynomial.notMem_support_iff.mp hr]
    exact Nat.zero_le _

lemma shiftedProductN_eval_one (I : Finset ℕ) :
    (shiftedProductN I).eval 1 = ∏ a ∈ I, (a + 1) := by
  rw [shiftedProductN, Polynomial.eval_prod]
  simp [Nat.add_comm]

lemma shiftedProduct_coeff_bound {I : Finset ℕ} {J : ℕ}
    (hI : I ⊆ Finset.Icc 0 J) :
    IntPolynomialCoeffBound (shiftedProductZ I) ((J + 1) ^ I.card) := by
  intro r
  have hcoeff : Int.natAbs ((shiftedProductZ I).coeff r) =
      (shiftedProductN I).coeff r := by
    simp [shiftedProductZ]
  rw [hcoeff]
  calc
    (shiftedProductN I).coeff r ≤ (shiftedProductN I).eval 1 :=
      natPolynomial_coeff_le_eval_one _ _
    _ = ∏ a ∈ I, (a + 1) := shiftedProductN_eval_one I
    _ ≤ ∏ _a ∈ I, (J + 1) := by
      refine Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) ?_
      intro a ha
      exact Nat.add_le_add_right (Finset.mem_Icc.mp (hI ha)).2 1
    _ = (J + 1) ^ I.card := by simp

lemma shiftedProductZ_map_rat (I : Finset ℕ) :
    (shiftedProductZ I).map (Int.castRingHom ℚ) = shiftedProductQ I := by
  rw [shiftedProductZ, Polynomial.map_map]
  have hcomp : (Int.castRingHom ℚ).comp (Nat.castRingHom ℤ) =
      Nat.castRingHom ℚ := by
    ext n
    simp
  rw [hcomp]
  rw [shiftedProductN, shiftedProductQ, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro a _
  simp

lemma shiftedProductQ_separable (I : Finset ℕ) :
    (shiftedProductQ I).Separable := by
  have hsep :
      (∏ a ∈ I,
        (Polynomial.X - Polynomial.C (-(a : ℚ)))).Separable := by
    rw [Polynomial.separable_prod_X_sub_C_iff']
    intro a ha b hb hab
    have hcast : (a : ℚ) = b := by linarith
    exact_mod_cast hcast
  simpa [shiftedProductQ, sub_neg_eq_add] using hsep

lemma shiftedProductZ_natDegree (I : Finset ℕ) :
    (shiftedProductZ I).natDegree = I.card := by
  have hmonic : (shiftedProductN I).Monic := by
    rw [shiftedProductN]
    exact Polynomial.monic_prod_of_monic I _
      (fun a _ ↦ Polynomial.monic_X_add_C a)
  rw [shiftedProductZ, hmonic.natDegree_map]
  rw [shiftedProductN, Polynomial.natDegree_prod_of_monic]
  · calc
      ∑ a ∈ I, (Polynomial.X + Polynomial.C a : Polynomial ℕ).natDegree =
          ∑ _a ∈ I, 1 := by
            apply Finset.sum_congr rfl
            intro a _
            exact Polynomial.natDegree_X_add_C a
      _ = I.card := by simp
  · intro a _
    exact Polynomial.monic_X_add_C a

lemma shiftedProductN_eval (I : Finset ℕ) (n : ℕ) :
    (shiftedProductN I).eval n = ∏ a ∈ I, (n + a) := by
  rw [shiftedProductN, Polynomial.eval_prod]
  simp

lemma shiftedProductZ_integral_point {I : Finset ℕ} {n y : ℕ}
    (hy : y ^ 2 = ∏ a ∈ I, (n + a)) :
    ((y : ℤ) ^ 2) = (shiftedProductZ I).eval (n : ℤ) := by
  calc
    ((y : ℤ) ^ 2) = ((y ^ 2 : ℕ) : ℤ) := by norm_num
    _ = (((shiftedProductN I).eval n : ℕ) : ℤ) := by
      rw [shiftedProductN_eval I n]
      exact_mod_cast hy
    _ = (shiftedProductZ I).eval (n : ℤ) := by
      simp [shiftedProductZ]

/-- A nonsquare `n` supplies a minimal shifted-product curve containing
both endpoint shifts `0` and `t n`. -/
theorem exists_minimal_curve_shifts {n : ℕ} (hn : ¬IsSquare n) :
    ∃ I : Finset ℕ, ∃ y : ℕ,
      I ⊆ Finset.Icc 0 (t n) ∧ 0 ∈ I ∧ t n ∈ I ∧ 2 ≤ I.card ∧
      y ^ 2 = ∏ a ∈ I, (n + a) := by
  obtain ⟨J, hJ, htJ, y, hy⟩ := exists_minimal_witness_with_endpoint hn
  have h0J : 0 ∉ J := by
    intro h0
    have := Finset.mem_Icc.mp (hJ h0)
    omega
  let I := insert 0 J
  have hI : I ⊆ Finset.Icc 0 (t n) := by
    intro a ha
    have ha' : a = 0 ∨ a ∈ J := by simpa [I] using ha
    rcases ha' with rfl | haJ
    · exact Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩
    · have haI := Finset.mem_Icc.mp (hJ haJ)
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, haI.2⟩
  have hcardJ : 0 < J.card := Finset.card_pos.mpr ⟨t n, htJ⟩
  have hcardI : 2 ≤ I.card := by
    change 2 ≤ (insert 0 J).card
    rw [Finset.card_insert_of_notMem h0J]
    omega
  have hsq : y ^ 2 = ∏ a ∈ I, (n + a) := by
    change y ^ 2 = ∏ a ∈ insert 0 J, (n + a)
    rw [Finset.prod_insert h0J]
    simpa [pow_two] using hy.symm
  exact ⟨I, y, hI, by simp [I], by simp [I, htJ], hcardI, hsq⟩

/-- The complete direct-curve package extracted from the minimal witness.
When its degree is at least three, it is ready for the effective
hyperelliptic height estimate. -/
theorem exists_minimal_shifted_product_curve {n : ℕ} (hn : ¬IsSquare n) :
    ∃ I : Finset ℕ, ∃ y : ℕ,
      I ⊆ Finset.Icc 0 (t n) ∧ 0 ∈ I ∧ t n ∈ I ∧ 2 ≤ I.card ∧ 0 < y ∧
      (shiftedProductZ I).natDegree = I.card ∧
      (shiftedProductQ I).Separable ∧
      IntPolynomialCoeffBound (shiftedProductZ I) ((t n + 1) ^ I.card) ∧
      ((y : ℤ) ^ 2) = (shiftedProductZ I).eval (n : ℤ) := by
  obtain ⟨I, y, hI, h0, ht, hcard, hsq⟩ := exists_minimal_curve_shifts hn
  have hy : 0 < y := by
    have hn0 : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      exact hn (this ▸ IsSquare.zero)
    have hprod : 0 < ∏ a ∈ I, (n + a) := by
      exact Finset.prod_pos fun a _ ↦ by omega
    nlinarith
  exact ⟨I, y, hI, h0, ht, hcard, hy, shiftedProductZ_natDegree I,
    shiftedProductQ_separable I, shiftedProduct_coeff_bound hI,
    shiftedProductZ_integral_point hsq⟩

/-- The small-support branch after inserting the exact effective-height
input.  The degree-two branch is deliberately left visible: it is handled
by `two_factor_square_bound`, whereas every larger minimal witness receives
the published explicit height bound. -/
theorem exists_minimal_direct_height_bound
    (hheight : EffectiveHyperellipticHeightBound)
    {n : ℕ} (hn : ¬IsSquare n) :
    ∃ I : Finset ℕ, ∃ y : ℕ,
      I ⊆ Finset.Icc 0 (t n) ∧ 0 ∈ I ∧ t n ∈ I ∧ 2 ≤ I.card ∧
      (I.card = 2 ∨
        Real.log (n : ℝ) ≤
          (((4 * I.card : ℕ) : ℝ) ^ (212 * I.card ^ 4)) *
            ((((t n + 1) ^ I.card : ℕ) : ℝ) ^
              (50 * I.card ^ 4))) := by
  obtain ⟨I, y, hI, h0, ht, hcard, hy, hdeg, hsep, hcoeff, hpoint⟩ :=
    exists_minimal_shifted_product_curve hn
  refine ⟨I, y, hI, h0, ht, hcard, ?_⟩
  rcases hcard.eq_or_lt with hcardEq | hcardLt
  · exact Or.inl hcardEq.symm
  · right
    apply hheight (shiftedProductZ I) I.card ((t n + 1) ^ I.card) n y
      hdeg (by omega) ?_ hcoeff ?_ hy hpoint
    · simpa [shiftedProductZ_map_rat] using hsep
    · by_contra hn0
      have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn0
      exact hn (hnZero ▸ IsSquare.zero)

/-- If the minimal shifted-product curve has degree two, its two shifts
are exactly `0` and `t n`, so BPZ's elementary two-factor bound applies. -/
lemma minimal_curve_card_two_bound
    {n : ℕ} (hn : ¬IsSquare n) {I : Finset ℕ} {y : ℕ}
    (h0 : 0 ∈ I) (ht : t n ∈ I) (hcard : I.card = 2)
    (hsq : y ^ 2 = ∏ a ∈ I, (n + a)) :
    n ≤ (t n) ^ 2 := by
  have htpos : 0 < t n := t_pos_of_not_isSquare hn
  have hne : 0 ≠ t n := by omega
  have hpairSub : ({0, t n} : Finset ℕ) ⊆ I := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact h0
    · exact ht
  have hpairCard : ({0, t n} : Finset ℕ).card = 2 := by simp [hne]
  have hEq : ({0, t n} : Finset ℕ) = I := by
    apply Finset.eq_of_subset_of_card_le hpairSub
    omega
  have hsq' : y ^ 2 = n * (n + t n) := by
    rw [← hEq] at hsq
    simpa [hne] using hsq
  exact two_factor_square_bound (by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    exact hn (this ▸ IsSquare.zero)) htpos hsq'

/-- Exact direct-curve dichotomy after taking a second logarithm.  The
degree-two alternative is elementary; every larger degree has the
published effective-height expression with no asymptotic notation. -/
theorem minimal_direct_loglog_dichotomy
    (hheight : EffectiveHyperellipticHeightBound)
    {n : ℕ} (hn : ¬IsSquare n) (hnlarge : 1 < n) :
    n ≤ (t n) ^ 2 ∨
      ∃ D : ℕ, 3 ≤ D ∧ D ≤ t n + 1 ∧
        Real.log (Real.log (n : ℝ)) ≤
          (212 * D ^ 4 : ℕ) * Real.log ((4 * D : ℕ) : ℝ) +
            (50 * D ^ 4 : ℕ) *
              Real.log ((((t n + 1) ^ D : ℕ) : ℝ)) := by
  obtain ⟨I, y, hI, h0, ht, hcard, hy, hdeg, hsep, hcoeff, hpoint⟩ :=
    exists_minimal_shifted_product_curve hn
  by_cases htwo : I.card = 2
  · have hpoint' : ((y ^ 2 : ℕ) : ℤ) =
        (((shiftedProductN I).eval n : ℕ) : ℤ) := by
      simpa [shiftedProductZ] using hpoint
    have hsqN : y ^ 2 = (shiftedProductN I).eval n := by
      exact_mod_cast hpoint'
    rw [shiftedProductN_eval] at hsqN
    exact Or.inl (minimal_curve_card_two_bound hn h0 ht htwo hsqN)
  · right
    have hthree : 3 ≤ I.card := by omega
    have hDle : I.card ≤ t n + 1 := by
      have hc := Finset.card_le_card hI
      simpa using hc
    have hnpos : 0 < n := by omega
    have hraw := hheight (shiftedProductZ I) I.card
      ((t n + 1) ^ I.card) n y hdeg hthree (by
        simpa [shiftedProductZ_map_rat] using hsep) hcoeff hnpos hy hpoint
    exact ⟨I.card, hthree, hDle,
      log_log_le_of_effective_height (by omega) (by positivity) hnlarge hraw⟩

/-- The exact three-way dichotomy used in BPZ's balancing argument, for an
arbitrary integer support cutoff `r`. -/
theorem minimal_balancing_dichotomy
    (hheight : EffectiveHyperellipticHeightBound)
    {n r : ℕ} (hn : ¬IsSquare n) (hnlarge : 1 < n) (hr : 3 ≤ r) :
    n ≤ (t n) ^ 2 ∨
      (∃ D : ℕ, 3 ≤ D ∧ D ≤ r ∧
        Real.log (Real.log (n : ℝ)) ≤
          (212 * D ^ 4 : ℕ) * Real.log ((4 * D : ℕ) : ℝ) +
            (50 * D ^ 4 : ℕ) *
              Real.log ((((t n + 1) ^ D : ℕ) : ℝ))) ∨
      ((r - 2 : ℕ) : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        ((r - 2 : ℕ) : ℝ) *
            Real.log ((3 * (16 ^ (212 * 4 ^ 4)) : ℕ) : ℝ) +
          ((50 * 4 ^ 4 + 1 : ℕ) : ℝ) *
            (((4 * (r - 2) : ℕ) : ℝ) *
                Real.log ((4 * (t n + 1) : ℕ) : ℝ) +
              ((4 * (Nat.primeCounting (t n) +
                  r ^ 2 * Nat.log 2 (t n)) : ℕ) : ℝ) *
                Real.log (t n : ℝ)) := by
  obtain ⟨I, y, hI, h0, ht, hcard, hsq⟩ := exists_minimal_curve_shifts hn
  have htpos : 0 < t n := t_pos_of_not_isSquare hn
  by_cases htwo : I.card = 2
  · exact Or.inl (minimal_curve_card_two_bound hn h0 ht htwo hsq)
  have hthree : 3 ≤ I.card := by omega
  right
  by_cases hsmall : I.card ≤ r
  · left
    have hy : 0 < y := by
      have hprod : 0 < ∏ a ∈ I, (n + a) :=
        Finset.prod_pos fun a _ ↦ by omega
      nlinarith
    have hraw := hheight (shiftedProductZ I) I.card
      ((t n + 1) ^ I.card) n y (shiftedProductZ_natDegree I) hthree
      (by simpa [shiftedProductZ_map_rat] using shiftedProductQ_separable I)
      (shiftedProduct_coeff_bound hI) (by omega) hy
      (shiftedProductZ_integral_point hsq)
    exact ⟨I.card, hthree, hsmall,
      log_log_le_of_effective_height (by omega) (by positivity) hnlarge hraw⟩
  · right
    have hrle : r ≤ I.card := by omega
    obtain ⟨K, hKI, hKcard⟩ := Finset.exists_subset_card_eq hrle
    have hsquare : IsSquare (∏ a ∈ I, (n + a)) :=
      ⟨y, by simpa [pow_two] using hsq.symm⟩
    have hsparse := sparse_subfamily_loglog_bound hheight hnlarge
      hI hKI (by omega : 3 ≤ K.card) (by omega : 1 ≤ t n) hsquare
    simpa only [hKcard] using hsparse

/-! ### The balancing scale and asymptotic inversion -/

/-- The real support scale `(J / log J)^(1/6)`. -/
def lowerBalanceScale (J : ℕ) : ℝ :=
  ((J : ℝ) / Real.log (J : ℝ)) ^ ((1 : ℝ) / 6)

/-- The integer cutoff used to select a subfamily of shifts. -/
def lowerBalanceCutoff (J : ℕ) : ℕ :=
  ⌊lowerBalanceScale J⌋₊

/-- The common order of magnitude of the two balanced branches. -/
def lowerBalanceMagnitude (J : ℕ) : ℝ :=
  lowerBalanceScale J ^ 5 * Real.log (J : ℝ)

/-- The shape occurring in BPZ's final lower bound, written in a form whose
fifth power is exactly `L^6 / log L`. -/
def lowerLogShape (L : ℝ) : ℝ :=
  (L ^ 6 / Real.log L) ^ ((5 : ℝ)⁻¹)

def lowerBoundShape (n : ℕ) : ℝ :=
  lowerLogShape (Real.log (Real.log (n : ℝ)))

/-- A concrete positive constant sufficient for the asymptotic inversion. -/
def lowerBoundConstant : ℝ :=
  1 / (2 * (2000000 : ℝ) ^ 6)

lemma lowerBalanceScale_tendsto_atTop :
    Filter.Tendsto lowerBalanceScale Filter.atTop Filter.atTop := by
  have hzeroR : Filter.Tendsto
      (fun z : ℝ ↦ Real.log z / z) Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_pow_atTop
      (1 : ℝ) (1 : ℝ) (by norm_num)
    simpa [Real.rpow_one] using h
  have hzero : Filter.Tendsto
      (fun J : ℕ ↦ Real.log (J : ℝ) / (J : ℝ))
      Filter.atTop (nhds 0) := hzeroR.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ J : ℕ in Filter.atTop,
      0 < Real.log (J : ℝ) / (J : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with J hJ
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < J by omega)))
      (by positivity)
  have hzeroPos : Filter.Tendsto
      (fun J : ℕ ↦ Real.log (J : ℝ) / (J : ℝ))
      Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_inf.mpr ⟨hzero, Filter.tendsto_principal.mpr hpos⟩
  have hinv := hzeroPos.inv_tendsto_nhdsGT_zero
  have hquot : Filter.Tendsto
      (fun J : ℕ ↦ (J : ℝ) / Real.log (J : ℝ))
      Filter.atTop Filter.atTop := by
    apply hinv.congr'
    filter_upwards [Filter.eventually_ge_atTop 2] with J hJ
    have hJR : (0 : ℝ) < J := by positivity
    have hlog : 0 < Real.log (J : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < J by omega))
    change (Real.log (J : ℝ) / (J : ℝ))⁻¹ =
      (J : ℝ) / Real.log (J : ℝ)
    rw [inv_div]
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp hquot

lemma lowerBalanceCutoff_tendsto_atTop :
    Filter.Tendsto lowerBalanceCutoff Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp lowerBalanceScale_tendsto_atTop

lemma lowerBalanceCutoff_div_scale_tendsto_one :
    Filter.Tendsto
      (fun J : ℕ ↦ (lowerBalanceCutoff J : ℝ) / lowerBalanceScale J)
      Filter.atTop (nhds 1) :=
  tendsto_nat_floor_div_atTop.comp lowerBalanceScale_tendsto_atTop

lemma lowerBalanceMagnitude_tendsto_atTop :
    Filter.Tendsto lowerBalanceMagnitude Filter.atTop Filter.atTop := by
  have hpow : Filter.Tendsto
      (fun J : ℕ ↦ lowerBalanceScale J ^ 5)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp
      lowerBalanceScale_tendsto_atTop
  apply Filter.tendsto_atTop_mono' Filter.atTop ?_ hpow
  have hlogTop : Filter.Tendsto (fun J : ℕ ↦ Real.log (J : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne := hlogTop.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [hlogOne, Filter.eventually_ge_atTop 1] with J hlog hJ
  rw [lowerBalanceMagnitude]
  have hbase : 0 ≤ (J : ℝ) / Real.log (J : ℝ) :=
    div_nonneg (by positivity) (by linarith)
  have hscale : 0 ≤ lowerBalanceScale J := by
    exact Real.rpow_nonneg hbase _
  exact le_mul_of_one_le_right
    (pow_nonneg hscale _) hlog

/-- The integer cutoff is eventually a positive constant fraction of the
real balancing scale. -/
lemma eventually_lowerBalanceCutoff_bounds :
    ∀ᶠ J : ℕ in Filter.atTop,
      3 ≤ lowerBalanceCutoff J ∧
        lowerBalanceScale J / 2 ≤ (lowerBalanceCutoff J : ℝ) ∧
        (lowerBalanceCutoff J : ℝ) ≤ lowerBalanceScale J := by
  have hcutThree := lowerBalanceCutoff_tendsto_atTop.eventually
    (Filter.eventually_ge_atTop 3)
  have hratio := lowerBalanceCutoff_div_scale_tendsto_one.eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hscalePos := lowerBalanceScale_tendsto_atTop.eventually
    (Filter.eventually_gt_atTop 0)
  filter_upwards [hcutThree, hratio, hscalePos] with J hJ hratio hscale
  refine ⟨hJ, ?_, Nat.floor_le hscale.le⟩
  have hdiv : (1 / 2 : ℝ) <
      (lowerBalanceCutoff J : ℝ) / lowerBalanceScale J := hratio
  have := (lt_div_iff₀ hscale).mp hdiv
  nlinarith

/-- The balancing scale was chosen so that its sixth power cancels the
single logarithm. -/
lemma lowerBalanceScale_pow_six_mul_log {J : ℕ} (hJ : 1 < J) :
    lowerBalanceScale J ^ 6 * Real.log (J : ℝ) = J := by
  have hlog : 0 < Real.log (J : ℝ) :=
    Real.log_pos (by exact_mod_cast hJ)
  have hq : 0 ≤ (J : ℝ) / Real.log (J : ℝ) :=
    div_nonneg (by positivity) hlog.le
  rw [lowerBalanceScale, ← Real.rpow_mul_natCast hq ((1 : ℝ) / 6) 6]
  norm_num
  field_simp

lemma lowerBalanceScale_mul_magnitude {J : ℕ} (hJ : 1 < J) :
    lowerBalanceScale J * lowerBalanceMagnitude J = (J : ℝ) := by
  rw [lowerBalanceMagnitude]
  calc
    lowerBalanceScale J * (lowerBalanceScale J ^ 5 * Real.log (J : ℝ)) =
        lowerBalanceScale J ^ 6 * Real.log (J : ℝ) := by ring
    _ = (J : ℝ) := lowerBalanceScale_pow_six_mul_log hJ

lemma lowerBalanceMagnitude_pow_six {J : ℕ} (hJ : 1 < J) :
    lowerBalanceMagnitude J ^ 6 =
      (J : ℝ) ^ 5 * Real.log (J : ℝ) := by
  rw [lowerBalanceMagnitude]
  calc
    (lowerBalanceScale J ^ 5 * Real.log (J : ℝ)) ^ 6 =
        (lowerBalanceScale J ^ 6 * Real.log (J : ℝ)) ^ 5 *
          Real.log (J : ℝ) := by ring
    _ = (J : ℝ) ^ 5 * Real.log (J : ℝ) := by
      rw [lowerBalanceScale_pow_six_mul_log hJ]

lemma lowerLogShape_pow_five {L : ℝ} (hL : 1 < L) :
    lowerLogShape L ^ 5 = L ^ 6 / Real.log L := by
  have hbase : 0 ≤ L ^ 6 / Real.log L :=
    div_nonneg (by positivity) (Real.log_pos hL).le
  rw [lowerLogShape]
  simpa using Real.rpow_inv_natCast_pow hbase (by norm_num : (5 : ℕ) ≠ 0)

lemma lowerLogShape_nonneg {L : ℝ} (hL : 1 < L) :
    0 ≤ lowerLogShape L := by
  rw [lowerLogShape]
  exact Real.rpow_nonneg
    (div_nonneg (by positivity) (Real.log_pos hL).le) _

lemma lowerLogShape_eq {L : ℝ} (hL : 1 < L) :
    lowerLogShape L =
      L ^ ((6 : ℝ) / 5) * (Real.log L) ^ (-((1 : ℝ) / 5)) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog0 : 0 ≤ Real.log L := (Real.log_pos hL).le
  let R := L ^ ((6 : ℝ) / 5) * (Real.log L) ^ (-((1 : ℝ) / 5))
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hlog0 _)
  have hRpow : R ^ 5 = L ^ 6 / Real.log L := by
    dsimp [R]
    rw [mul_pow, ← Real.rpow_mul_natCast hL0 ((6 : ℝ) / 5) 5,
      ← Real.rpow_mul_natCast hlog0 (-((1 : ℝ) / 5)) 5]
    norm_num
    rw [Real.rpow_neg_one]
    rfl
  apply le_antisymm
  · apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) hRnonneg
    rw [lowerLogShape_pow_five hL, hRpow]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0)
      (lowerLogShape_nonneg hL)
    rw [hRpow, lowerLogShape_pow_five hL]

lemma lowerLogShape_le_sq {L : ℝ} (hL : 1 < L)
    (hlogL : 1 ≤ Real.log L) :
    lowerLogShape L ≤ L ^ 2 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) (sq_nonneg L)
  rw [lowerLogShape_pow_five hL]
  have hdiv : L ^ 6 / Real.log L ≤ L ^ 6 := by
    exact div_le_self (by positivity) hlogL
  calc
    L ^ 6 / Real.log L ≤ L ^ 6 := hdiv
    _ ≤ L ^ 10 := by
      exact pow_le_pow_right₀ (by linarith) (by omega : 6 ≤ 10)
    _ = (L ^ 2) ^ 5 := by ring

lemma lowerLogShape_le_of_balance {L J A : ℝ}
    (hL : 1 < L) (hlogL : 1 ≤ Real.log L) (hJ : 1 < J)
    (hJL : J ≤ L ^ 2)
    (hAnonneg : 0 ≤ A) (hbalance : L ≤ 2000000 * A)
    (hmagPow : A ^ 6 = J ^ 5 * Real.log J) :
    lowerBoundConstant * lowerLogShape L ≤ J := by
  have hJpos : 0 < J := by linarith
  have hlogJ : 0 < Real.log J := Real.log_pos hJ
  have hLsix : L ^ 6 ≤
      (2000000 : ℝ) ^ 6 * (J ^ 5 * Real.log J) := by
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ L) hbalance 6
    rw [mul_pow, hmagPow] at hp
    exact hp
  have hlogJLe : Real.log J ≤ 2 * Real.log L := by
    calc
      Real.log J ≤ Real.log (L ^ 2) := Real.log_le_log hJpos hJL
      _ = 2 * Real.log L := by rw [Real.log_pow]; norm_num
  have hLsix' : L ^ 6 ≤
      2 * (2000000 : ℝ) ^ 6 * J ^ 5 * Real.log L := by
    calc
      L ^ 6 ≤ (2000000 : ℝ) ^ 6 * (J ^ 5 * Real.log J) := hLsix
      _ ≤ (2000000 : ℝ) ^ 6 * (J ^ 5 * (2 * Real.log L)) := by
        gcongr
      _ = 2 * (2000000 : ℝ) ^ 6 * J ^ 5 * Real.log L := by ring
  have hcPos : 0 < lowerBoundConstant := by
    norm_num [lowerBoundConstant]
  have hcOne : lowerBoundConstant ≤ 1 := by
    norm_num [lowerBoundConstant]
  have hcCancel : lowerBoundConstant *
      (2 * (2000000 : ℝ) ^ 6) = 1 := by
    norm_num [lowerBoundConstant]
  have hcL : lowerBoundConstant * L ^ 6 ≤ J ^ 5 * Real.log L := by
    calc
      lowerBoundConstant * L ^ 6 ≤ lowerBoundConstant *
          (2 * (2000000 : ℝ) ^ 6 * J ^ 5 * Real.log L) :=
        mul_le_mul_of_nonneg_left hLsix' hcPos.le
      _ = (lowerBoundConstant * (2 * (2000000 : ℝ) ^ 6)) *
          (J ^ 5 * Real.log L) := by ring
      _ = J ^ 5 * Real.log L := by rw [hcCancel, one_mul]
  have hcPow : lowerBoundConstant ^ 5 ≤ lowerBoundConstant := by
    simpa only [pow_one] using
      (pow_le_pow_of_le_one hcPos.le hcOne (by omega : 1 ≤ (5 : ℕ)))
  have hbase : 0 ≤ L ^ 6 / Real.log L :=
    div_nonneg (by positivity) (Real.log_pos hL).le
  have htargetPow : (lowerBoundConstant * lowerLogShape L) ^ 5 ≤ J ^ 5 := by
    rw [mul_pow, lowerLogShape_pow_five hL]
    calc
      lowerBoundConstant ^ 5 * (L ^ 6 / Real.log L) ≤
          lowerBoundConstant * (L ^ 6 / Real.log L) :=
        mul_le_mul_of_nonneg_right hcPow hbase
      _ ≤ J ^ 5 := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ (Real.log_pos hL)).2 (by simpa [mul_assoc] using hcL)
  exact le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) hJpos.le htargetPow

lemma eventually_lowerBoundShape_inputs :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < Real.log (Real.log (n : ℝ)) ∧
        1 ≤ Real.log (Real.log (Real.log (n : ℝ))) ∧
        Real.log (Real.log (n : ℝ)) ^ 4 ≤ (n : ℝ) := by
  have hlogTop : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogTop : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlogTop
  have hlogloglogTop : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (Real.log (n : ℝ))))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hloglogTop
  have hratioR := Real.tendsto_pow_log_div_pow_atTop
    (1 : ℝ) (4 : ℝ) (by norm_num)
  have hratio := hratioR.comp tendsto_natCast_atTop_atTop
  have hratioOne := hratio.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hloglogTop.eventually (Filter.eventually_gt_atTop 1),
    hlogloglogTop.eventually (Filter.eventually_ge_atTop 1), hratioOne,
    Filter.eventually_ge_atTop 2] with n hL hlogL hratioOne hn
  refine ⟨hL, hlogL, ?_⟩
  have hnR : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogFour : Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) := by
    norm_num at hratioOne
    have hlt : Real.log (n : ℝ) ^ 4 / (n : ℝ) < 1 := hratioOne
    simpa using ((div_lt_iff₀ hnR).mp hlt).le
  have hllog : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
    Real.log_le_self hlogn.le
  exact (pow_le_pow_left₀ (by linarith : 0 ≤ Real.log (Real.log (n : ℝ)))
    hllog 4).trans hlogFour

lemma eventually_lowerBalanceScale_le_self :
    ∀ᶠ J : ℕ in Filter.atTop, lowerBalanceScale J ≤ (J : ℝ) := by
  have hlogTop : Filter.Tendsto (fun J : ℕ ↦ Real.log (J : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne := hlogTop.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [hlogOne, Filter.eventually_ge_atTop 2] with J hlogOne hJ
  have hJR : (0 : ℝ) < J := by positivity
  have hlogPos : 0 < Real.log (J : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < J by omega))
  have hlogLe : Real.log (J : ℝ) ≤ (J : ℝ) :=
    Real.log_le_self hJR.le
  have hqOne : (1 : ℝ) ≤ (J : ℝ) / Real.log (J : ℝ) :=
    (le_div_iff₀ hlogPos).2 (by simpa using hlogLe)
  have hqJ : (J : ℝ) / Real.log (J : ℝ) ≤ (J : ℝ) := by
    rw [div_le_iff₀ hlogPos]
    nlinarith
  rw [lowerBalanceScale]
  exact (Real.rpow_le_self_of_one_le hqOne (by norm_num)).trans hqJ

lemma eventually_lowerBalanceCutoff_le_self :
    ∀ᶠ J : ℕ in Filter.atTop, lowerBalanceCutoff J ≤ J := by
  filter_upwards [eventually_lowerBalanceCutoff_bounds,
    eventually_lowerBalanceScale_le_self] with J hcut hscale
  exact_mod_cast hcut.2.2.trans hscale

lemma log_succ_le_two_mul_log {J : ℕ} (hJ : 2 ≤ J) :
    Real.log ((J + 1 : ℕ) : ℝ) ≤ 2 * Real.log (J : ℝ) := by
  have hnat : J + 1 ≤ J ^ 2 := by nlinarith
  have hreal : ((J + 1 : ℕ) : ℝ) ≤ (J : ℝ) ^ 2 := by
    exact_mod_cast hnat
  calc
    Real.log ((J + 1 : ℕ) : ℝ) ≤ Real.log ((J : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hreal
    _ = 2 * Real.log (J : ℝ) := by rw [Real.log_pow]; norm_num

lemma log_four_mul_le_three_mul_log {J : ℕ} (hJ : 2 ≤ J) :
    Real.log ((4 * J : ℕ) : ℝ) ≤ 3 * Real.log (J : ℝ) := by
  have hsq : 4 ≤ J ^ 2 := by
    simpa using Nat.pow_le_pow_left hJ 2
  have hnat : 4 * J ≤ J ^ 3 := by
    calc
      4 * J = J * 4 := by omega
      _ ≤ J * J ^ 2 := Nat.mul_le_mul_left J hsq
      _ = J ^ 3 := by ring
  have hreal : ((4 * J : ℕ) : ℝ) ≤ (J : ℝ) ^ 3 := by
    exact_mod_cast hnat
  calc
    Real.log ((4 * J : ℕ) : ℝ) ≤ Real.log ((J : ℝ) ^ 3) :=
      Real.log_le_log (by positivity) hreal
    _ = 3 * Real.log (J : ℝ) := by rw [Real.log_pow]; norm_num

lemma log_four_mul_succ_le_four_mul_log {J : ℕ} (hJ : 2 ≤ J) :
    Real.log ((4 * (J + 1) : ℕ) : ℝ) ≤ 4 * Real.log (J : ℝ) := by
  have hsq : J + 1 ≤ J ^ 2 := by nlinarith
  have hfour : 4 ≤ J ^ 2 := by
    simpa using Nat.pow_le_pow_left hJ 2
  have hnat : 4 * (J + 1) ≤ J ^ 4 := by
    calc
      4 * (J + 1) ≤ J ^ 2 * J ^ 2 := Nat.mul_le_mul hfour hsq
      _ = J ^ 4 := by ring
  have hreal : ((4 * (J + 1) : ℕ) : ℝ) ≤ (J : ℝ) ^ 4 := by
    exact_mod_cast hnat
  calc
    Real.log ((4 * (J + 1) : ℕ) : ℝ) ≤ Real.log ((J : ℝ) ^ 4) :=
      Real.log_le_log (by positivity) hreal
    _ = 4 * Real.log (J : ℝ) := by rw [Real.log_pow]; norm_num

lemma natLog_two_le_two_mul_log {J : ℕ} (hJ : 2 ≤ J) :
    (Nat.log 2 J : ℝ) ≤ 2 * Real.log (J : ℝ) := by
  have hlogJ : 0 ≤ Real.log (J : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < J by omega))).le
  calc
    (Nat.log 2 J : ℝ) ≤ Real.logb 2 J := Real.natLog_le_logb J 2
    _ = Real.log (J : ℝ) / Real.log 2 := by rw [Real.logb]
    _ ≤ 2 * Real.log (J : ℝ) := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      nlinarith [Real.log_two_gt_d9]

lemma direct_height_expression_le_balance
    {J D : ℕ} (hJ : 2 ≤ J) (hD : 3 ≤ D) (hDJ : D ≤ J)
    (hDscale : (D : ℝ) ≤ lowerBalanceScale J) :
    (212 * D ^ 4 : ℕ) * Real.log ((4 * D : ℕ) : ℝ) +
        (50 * D ^ 4 : ℕ) *
          Real.log ((((J + 1) ^ D : ℕ) : ℝ)) ≤
      736 * lowerBalanceMagnitude J := by
  have hlogJ : 0 ≤ Real.log (J : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < J by omega))).le
  have hfour : (4 * D : ℕ) ≤ 4 * J := Nat.mul_le_mul_left 4 hDJ
  have hlogFourD : Real.log ((4 * D : ℕ) : ℝ) ≤
      3 * Real.log (J : ℝ) := by
    calc
      Real.log ((4 * D : ℕ) : ℝ) ≤ Real.log ((4 * J : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hfour)
      _ ≤ 3 * Real.log (J : ℝ) := log_four_mul_le_three_mul_log hJ
  have hlogPow : Real.log ((((J + 1) ^ D : ℕ) : ℝ)) ≤
      (D : ℝ) * (2 * Real.log (J : ℝ)) := by
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left (log_succ_le_two_mul_log hJ) (by positivity)
  have hDfour : (D : ℝ) ^ 4 ≤ (D : ℝ) ^ 5 := by
    have hDone : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    calc
      (D : ℝ) ^ 4 = (D : ℝ) ^ 4 * 1 := by ring
      _ ≤ (D : ℝ) ^ 4 * (D : ℝ) :=
        mul_le_mul_of_nonneg_left hDone (by positivity)
      _ = (D : ℝ) ^ 5 := by ring
  have hDfive : (D : ℝ) ^ 5 ≤ lowerBalanceScale J ^ 5 := by
    exact pow_le_pow_left₀ (by positivity) hDscale 5
  have hlogFourD' : Real.log (4 * (D : ℝ)) ≤
      3 * Real.log (J : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlogFourD
  have hlogPow' : Real.log (((J : ℝ) + 1) ^ D) ≤
      (D : ℝ) * (2 * Real.log (J : ℝ)) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hlogPow
  push_cast
  calc
    212 * (D : ℝ) ^ 4 * Real.log (4 * (D : ℝ)) +
          50 * (D : ℝ) ^ 4 *
            Real.log (((J : ℝ) + 1) ^ D) ≤
        212 * (D : ℝ) ^ 4 * (3 * Real.log (J : ℝ)) +
          50 * (D : ℝ) ^ 4 *
            ((D : ℝ) * (2 * Real.log (J : ℝ))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlogFourD' (by positivity))
        (mul_le_mul_of_nonneg_left hlogPow' (by positivity))
    _ = (636 * (D : ℝ) ^ 4 + 100 * (D : ℝ) ^ 5) *
          Real.log (J : ℝ) := by ring
    _ ≤ 736 * (D : ℝ) ^ 5 * Real.log (J : ℝ) := by
      gcongr
      nlinarith
    _ ≤ 736 * lowerBalanceScale J ^ 5 * Real.log (J : ℝ) := by
      gcongr
    _ = 736 * lowerBalanceMagnitude J := by
      rw [lowerBalanceMagnitude]
      ring

/-- Eventually one logarithm is at most the square of the balancing scale.
This is the elementary `log(J)^4 = o(J)` estimate used in the sparse
branch. -/
lemma eventually_log_le_lowerBalanceScale_sq :
    ∀ᶠ J : ℕ in Filter.atTop,
      Real.log (J : ℝ) ≤ lowerBalanceScale J ^ 2 := by
  have hratioR := Real.tendsto_pow_log_div_pow_atTop
    (1 : ℝ) (4 : ℝ) (by norm_num)
  have hratio := hratioR.comp tendsto_natCast_atTop_atTop
  have hratioOne := hratio.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hratioOne, Filter.eventually_ge_atTop 2] with J hratioOne hJ
  have hJR : (0 : ℝ) < J := by positivity
  have hlog : 0 < Real.log (J : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < J by omega))
  have hlogFour : Real.log (J : ℝ) ^ 4 ≤ (J : ℝ) := by
    have hlt : Real.log (J : ℝ) ^ (4 : ℝ) / (J : ℝ) ^ (1 : ℝ) < 1 :=
      hratioOne
    norm_num at hlt
    simpa using ((div_lt_iff₀ hJR).mp hlt).le
  have hlogThree : Real.log (J : ℝ) ^ 3 ≤ lowerBalanceScale J ^ 6 := by
    apply le_of_mul_le_mul_right _ hlog
    calc
      Real.log (J : ℝ) ^ 3 * Real.log (J : ℝ) =
          Real.log (J : ℝ) ^ 4 := by ring
      _ ≤ (J : ℝ) := hlogFour
      _ = lowerBalanceScale J ^ 6 * Real.log (J : ℝ) :=
        (lowerBalanceScale_pow_six_mul_log (by omega : 1 < J)).symm
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0)
    (sq_nonneg (lowerBalanceScale J))
  calc
    Real.log (J : ℝ) ^ 3 ≤ lowerBalanceScale J ^ 6 := hlogThree
    _ = (lowerBalanceScale J ^ 2) ^ 3 := by ring

/-! ## Finite distribution comparisons -/

/-- The exceptional members of `(X,X+Y]` for which the largest prime factor
occurs at least twice. -/
def exceptionalInterval (X Y : ℕ) : Finset ℕ :=
  (Finset.Ioc X (X + Y)).filter fun n ↦ largestPrimeFactor n ^ 2 ∣ n

/-- The exact finite reverse comparison underlying BPZ Theorem 3.1.  In one
block, the number of `Y`-smooth integers with `t n > Y` is at most the number
of exceptional integers plus `π(Y)`. -/
theorem smooth_large_t_interval_card_le (X Y : ℕ) :
    ((smoothInterval X Y).filter fun n ↦ Y < t n).card ≤
      (exceptionalInterval X Y).card + (Y + 1).primesBelow.card := by
  let M := smoothInterval X Y
  let G := M.filter fun n ↦ t n ≤ Y
  let E := exceptionalInterval X Y
  let B := closedStarts X (X + Y)
  have hMleB : M.card ≤ B.card + (Y + 1).primesBelow.card := by
    have h := bpz_smooth_interval_bound X Y
    change M.card - (Y + 1).primesBelow.card ≤ B.card at h
    omega
  have hBsub : B ⊆ G ∪ E := by
    intro n hnB
    have hnB' := Finset.mem_filter.mp hnB
    have hnI := hnB'.1
    have htY : t n ≤ Y := by
      have hnlo := (Finset.mem_Ioc.mp hnI).1
      have hnclose := hnB'.2
      omega
    by_cases hnE : largestPrimeFactor n ^ 2 ∣ n
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hnE⟩)
    · have hn1 : 1 < n := by
        have hnpos : 0 < n := by
          have := (Finset.mem_Ioc.mp hnI).1
          omega
        by_contra h
        have hnEq : n = 1 := by omega
        subst n
        exact hnE (by norm_num [largestPrimeFactor])
      have hPle : largestPrimeFactor n ≤ Y :=
        (largestPrimeFactor_le_t hn1 hnE).trans htY
      have hsmooth : n ∈ (Y + 1).smoothNumbers := by
        rw [Nat.mem_smoothNumbers']
        intro p hp hpn
        have hpP := prime_le_largestPrimeFactor hn1 hp hpn
        omega
      apply Finset.mem_union_left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_filter.mpr ⟨hnI, hsmooth⟩, htY⟩
  have hBle : B.card ≤ G.card + E.card := by
    exact (Finset.card_le_card hBsub).trans (Finset.card_union_le G E)
  have hMle : M.card ≤ G.card + E.card + (Y + 1).primesBelow.card := by omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := M) (fun n ↦ t n ≤ Y)
  change G.card + (M.filter fun n ↦ ¬t n ≤ Y).card = M.card at hsplit
  have hbad : (M.filter fun n ↦ ¬t n ≤ Y) = M.filter fun n ↦ Y < t n := by
    ext n
    simp
  rw [hbad] at hsplit
  change (M.filter fun n ↦ Y < t n).card ≤
    E.card + (Y + 1).primesBelow.card
  omega

/-- Positive integers at most `x` with `t n ≤ y`. -/
def smallTUpTo (x y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ t n ≤ y

/-- The exact finite first comparison: every `n ≤ x` with `t n ≤ y` is
either `y`-smooth or belongs to the exceptional largest-prime-square set. -/
theorem smallTUpTo_card_le_smooth_add_exceptional (x y : ℕ) :
    (smallTUpTo x y).card ≤
      (Nat.smoothNumbersUpTo x (y + 1)).card + (exceptionalInterval 0 x).card := by
  have hsub : smallTUpTo x y ⊆
      Nat.smoothNumbersUpTo x (y + 1) ∪ exceptionalInterval 0 x := by
    intro n hn
    have hn' : n ∈ Finset.Icc 1 x ∧ t n ≤ y := by
      simpa [smallTUpTo] using hn
    have hnI : n ∈ Finset.Icc 1 x := hn'.1
    have htn : t n ≤ y := hn'.2
    have hnLower : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnPos : 0 < n := by omega
    by_cases hnE : largestPrimeFactor n ^ 2 ∣ n
    · apply Finset.mem_union_right
      rw [exceptionalInterval, zero_add, Finset.mem_filter]
      exact ⟨Finset.mem_Ioc.mpr ⟨hnPos, (Finset.mem_Icc.mp hnI).2⟩, hnE⟩
    · have hn1 : 1 < n := by
        by_contra h
        have hnEq : n = 1 := by omega
        subst n
        exact hnE (by norm_num [largestPrimeFactor])
      have hPle : largestPrimeFactor n ≤ y :=
        (largestPrimeFactor_le_t hn1 hnE).trans htn
      have hsmooth : n ∈ (y + 1).smoothNumbers := by
        rw [Nat.mem_smoothNumbers']
        intro p hp hpn
        have hpP := prime_le_largestPrimeFactor hn1 hp hpn
        omega
      apply Finset.mem_union_left
      exact Nat.mem_smoothNumbersUpTo.mpr ⟨(Finset.mem_Icc.mp hnI).2, hsmooth⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le (Nat.smoothNumbersUpTo x (y + 1)) (exceptionalInterval 0 x))

/-! ## The exceptional largest-prime-square set has density zero -/

/-- Split the exceptional set at a fixed cutoff `L`.  If the largest prime
factor is at most `L`, the integer is `L`-smooth; otherwise its square is a
large square divisor and hence it lies in the elementary square cover. -/
theorem exceptionalInterval_subset_smooth_union_squareCover (x L : ℕ) :
    exceptionalInterval 0 x ⊆
      Nat.smoothNumbersUpTo x (L + 1) ∪ Erdos49.squareCover x L := by
  intro n hn
  have hn' : n ∈ Finset.Ioc 0 x ∧ largestPrimeFactor n ^ 2 ∣ n := by
    simpa [exceptionalInterval] using hn
  have hnPos : 0 < n := (Finset.mem_Ioc.mp hn'.1).1
  have hnle : n ≤ x := (Finset.mem_Ioc.mp hn'.1).2
  by_cases hnOne : n = 1
  · subst n
    apply Finset.mem_union_left
    apply Nat.mem_smoothNumbersUpTo.mpr
    refine ⟨hnle, ?_⟩
    rw [Nat.mem_smoothNumbers']
    intro p hp hpOne
    have hpOne' : p = 1 := Nat.dvd_one.mp hpOne
    subst p
    exact (Nat.not_prime_one hp).elim
  have hnLarge : 1 < n := by omega
  by_cases hPL : largestPrimeFactor n ≤ L
  · apply Finset.mem_union_left
    apply Nat.mem_smoothNumbersUpTo.mpr
    refine ⟨hnle, ?_⟩
    rw [Nat.mem_smoothNumbers']
    intro p hp hpn
    exact Nat.lt_succ_iff.mpr
      ((prime_le_largestPrimeFactor hnLarge hp hpn).trans hPL)
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨largestPrimeFactor n, ?_, ?_⟩
    · apply Finset.mem_Ioc.mpr
      exact ⟨Nat.lt_of_not_ge hPL,
        (Nat.le_of_dvd hnPos (largestPrimeFactor_dvd hnLarge)).trans hnle⟩
    · exact Erdos49.mem_multiplesUpTo.mpr
        ⟨by omega, hnle, hn'.2⟩

/-- The elementary square-divisor cover has relative size at most `1/L`.
This is the telescoping estimate `∑_{q>L} 1/q² ≤ 1/L`. -/
theorem squareCover_card_real_le (x L : ℕ) (hL : 0 < L) :
    ((Erdos49.squareCover x L).card : ℝ) ≤ (x : ℝ) / L := by
  calc
    ((Erdos49.squareCover x L).card : ℝ) ≤
        ∑ q ∈ Finset.Ioc L x, ((x / q ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast Erdos49.squareCover_card_le x L
    _ ≤ ∑ q ∈ Finset.Ioc L x, (x : ℝ) * ((1 : ℝ) / q ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        ((x / q ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) / (q ^ 2 : ℕ) := Nat.cast_div_le
        _ = (x : ℝ) * ((1 : ℝ) / q ^ 2) := by push_cast; ring
    _ = (x : ℝ) * ∑ q ∈ Finset.Ioc L x, (1 : ℝ) / q ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (x : ℝ) * (1 / L) :=
      mul_le_mul_of_nonneg_left (Erdos49.sum_Ioc_reciprocal_sq_le hL)
        (by positivity)
    _ = (x : ℝ) / L := by ring

/-- A fully explicit finite exceptional-set estimate.  For every positive
cutoff `L`, the exceptional set is bounded by a fixed multiple of `√x`
plus `x/L`. -/
theorem exceptionalInterval_card_real_le (x L : ℕ) (hL : 0 < L) :
    ((exceptionalInterval 0 x).card : ℝ) ≤
      (2 ^ (Nat.primesLE L).card : ℕ) * (x.sqrt : ℝ) + (x : ℝ) / L := by
  have hcover := exceptionalInterval_subset_smooth_union_squareCover x L
  have hsmooth :
      (Nat.smoothNumbersUpTo x (L + 1)).card ≤
        2 ^ (Nat.primesLE L).card * x.sqrt := by
    rw [← Erdos49.smoothUpTo_eq_nat_smoothNumbersUpTo]
    exact Erdos49.smoothUpTo_card_le_sqrt x L
  calc
    ((exceptionalInterval 0 x).card : ℝ) ≤
        ((Nat.smoothNumbersUpTo x (L + 1) ∪ Erdos49.squareCover x L).card : ℕ) := by
      exact_mod_cast Finset.card_le_card hcover
    _ ≤ ((Nat.smoothNumbersUpTo x (L + 1)).card : ℝ) +
          ((Erdos49.squareCover x L).card : ℝ) := by
      exact_mod_cast Finset.card_union_le
        (Nat.smoothNumbersUpTo x (L + 1)) (Erdos49.squareCover x L)
    _ ≤ (2 ^ (Nat.primesLE L).card : ℕ) * (x.sqrt : ℝ) +
          (x : ℝ) / L :=
      add_le_add (by exact_mod_cast hsmooth) (squareCover_card_real_le x L hL)

private lemma natSqrt_cast_le_realSqrt (x : ℕ) :
    (x.sqrt : ℝ) ≤ Real.sqrt x := by
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast Nat.sqrt_le' x

/-- BPZ Lemma 3.5 in the qualitative form needed for the density theorem:
integers whose largest prime factor occurs at least twice have natural
density zero. -/
theorem exceptionalInterval_density_zero :
    Filter.Tendsto
      (fun x : ℕ ↦ ((exceptionalInterval 0 x).card : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hLlarge⟩ := exists_nat_gt (2 / ε)
  have hL : 0 < L := by
    have : (0 : ℝ) < L := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 2 / ε) hLlarge
    exact_mod_cast this
  have hLinv : (1 : ℝ) / L < ε / 2 := by
    have hLprod : (2 : ℝ) < (L : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hLlarge
    rw [div_lt_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)]
    nlinarith
  let C : ℝ := (2 ^ (Nat.primesLE L).card : ℕ)
  have hsqrtDiv : Filter.Tendsto
      (fun x : ℕ ↦ Real.sqrt x / (x : ℝ)) Filter.atTop (nhds 0) := by
    simpa [Real.sqrt_div_self] using tendsto_inv_atTop_nhds_zero_nat.sqrt
  have hmain : Filter.Tendsto
      (fun x : ℕ ↦ C * (Real.sqrt x / (x : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hsqrtDiv
  rw [Metric.tendsto_atTop] at hmain
  obtain ⟨N, hN⟩ := hmain (ε / 2) (by positivity)
  refine ⟨max 1 N, fun x hx ↦ ?_⟩
  have hxPos : 0 < x := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hx)
  have hxN : N ≤ x := (le_max_right 1 N).trans hx
  have hmainx := hN x hxN
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg (by positivity) (div_nonneg (Real.sqrt_nonneg _) (by positivity)))]
    at hmainx
  have hcard := exceptionalInterval_card_real_le x L hL
  have hxReal : (0 : ℝ) < x := by exact_mod_cast hxPos
  have hratio :
      ((exceptionalInterval 0 x).card : ℝ) / (x : ℝ) ≤
        C * ((x.sqrt : ℝ) / (x : ℝ)) + (1 : ℝ) / L := by
    calc
      ((exceptionalInterval 0 x).card : ℝ) / (x : ℝ) ≤
          (C * (x.sqrt : ℝ) + (x : ℝ) / L) / (x : ℝ) := by
        apply div_le_div_of_nonneg_right
        · simpa [C] using hcard
        · exact hxReal.le
      _ = C * ((x.sqrt : ℝ) / (x : ℝ)) + (1 : ℝ) / L := by
        field_simp
  have hsqrtRatio :
      C * ((x.sqrt : ℝ) / (x : ℝ)) ≤
        C * (Real.sqrt x / (x : ℝ)) := by
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (natSqrt_cast_le_realSqrt x) hxReal.le)
      (by positivity)
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hxReal.le)]
  exact lt_of_le_of_lt hratio (by linarith)

/-! ## Global fixed-threshold comparison -/

/-- `y`-smooth integers through `x` for which the required endpoint is
larger than `y`. -/
def smoothFixedFailures (x y : ℕ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo x (y + 1)).filter fun n ↦ y < t n

/-- Summing BPZ Lemma 3.7 over the consecutive blocks of length `y` gives
the exact global reverse comparison.  No asymptotics have been used: the
only losses are one copy of `π(y)` per block and the exceptional set. -/
theorem smoothFixedFailures_card_le (x y : ℕ) (hy : 0 < y) :
    (smoothFixedFailures x y).card ≤
      (x / y + 1) * (y + 1).primesBelow.card +
        (exceptionalInterval 0 ((x / y + 1) * y)).card := by
  let S := smoothFixedFailures x y
  let K := Finset.range (x / y + 1)
  let f : ℕ → ℕ := fun n ↦ (n - 1) / y
  have hmaps : (S : Set ℕ).MapsTo f K := by
    intro n hn
    have hn' : n ∈ Nat.smoothNumbersUpTo x (y + 1) ∧ y < t n := by
      simpa [S, smoothFixedFailures] using hn
    have hnle := (Nat.mem_smoothNumbersUpTo.mp hn'.1).1
    simpa [K, f] using
      Nat.lt_succ_of_le (Nat.div_le_div_right ((Nat.sub_le n 1).trans hnle))
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (k : ℕ) (hk : k ∈ K) :
      ({n ∈ S | f n = k}).card ≤
        (exceptionalInterval (k * y) y).card + (y + 1).primesBelow.card := by
    have hsub : {n ∈ S | f n = k} ⊆
        (smoothInterval (k * y) y).filter fun n ↦ y < t n := by
      intro n hn
      have hnmem := Finset.mem_filter.mp hn
      have hnS : n ∈ Nat.smoothNumbersUpTo x (y + 1) ∧ y < t n := by
        simpa [S, smoothFixedFailures] using hnmem.1
      have hnsmooth := (Nat.mem_smoothNumbersUpTo.mp hnS.1).2
      have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hnsmooth
      have hmod := Nat.mod_lt (n - 1) hy
      have hdecomp := Nat.mod_add_div (n - 1) y
      have hfEq : (n - 1) / y = k := by simpa [f] using hnmem.2
      rw [hfEq] at hdecomp
      have hnPos : 0 < n := Nat.pos_of_ne_zero hn0
      have hdecomp' : (n - 1) % y + k * y = n - 1 := by
        simpa [Nat.mul_comm] using hdecomp
      have hLower : k * y < n := by omega
      have hUpper : n ≤ k * y + y := by omega
      have hnI : n ∈ Finset.Ioc (k * y) (k * y + y) := by
        exact Finset.mem_Ioc.mpr ⟨hLower, hUpper⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hnS.2⟩
      exact Finset.mem_filter.mpr ⟨hnI, hnsmooth⟩
    exact (Finset.card_le_card hsub).trans (smooth_large_t_interval_card_le (k * y) y)
  have hpair : (K : Set ℕ).PairwiseDisjoint
      (fun k ↦ exceptionalInterval (k * y) y) := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro n hni hnj
    have hniI := (Finset.mem_filter.mp hni).1
    have hnjI := (Finset.mem_filter.mp hnj).1
    have hniBounds := Finset.mem_Ioc.mp hniI
    have hnjBounds := Finset.mem_Ioc.mp hnjI
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hblocks : i * y + y ≤ j * y := by
        have := Nat.mul_le_mul_right y (Nat.succ_le_iff.mpr hij)
        simpa [Nat.add_mul] using this
      omega
    · have hblocks : j * y + y ≤ i * y := by
        have := Nat.mul_le_mul_right y (Nat.succ_le_iff.mpr hji)
        simpa [Nat.add_mul] using this
      omega
  have hEsub : K.biUnion (fun k ↦ exceptionalInterval (k * y) y) ⊆
      exceptionalInterval 0 ((x / y + 1) * y) := by
    intro n hn
    obtain ⟨k, hkK, hnk⟩ := Finset.mem_biUnion.mp hn
    have hk : k < x / y + 1 := by simpa [K] using hkK
    have hndata := Finset.mem_filter.mp hnk
    have hnI := Finset.mem_Ioc.mp hndata.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, ?_⟩, hndata.2⟩
    have hmul := Nat.mul_le_mul_right y (Nat.succ_le_iff.mpr hk)
    have hmul' : k * y + y ≤ (x / y + 1) * y := by
      simpa [Nat.add_mul] using hmul
    simpa using hnI.2.trans hmul'
  have hsumE : ∑ k ∈ K, (exceptionalInterval (k * y) y).card ≤
      (exceptionalInterval 0 ((x / y + 1) * y)).card := by
    rw [← Finset.card_biUnion hpair]
    exact Finset.card_le_card hEsub
  rw [hpartition]
  calc
    ∑ k ∈ K, ({n ∈ S | f n = k}).card ≤
        ∑ k ∈ K,
          ((exceptionalInterval (k * y) y).card + (y + 1).primesBelow.card) := by
      exact Finset.sum_le_sum hfiber
    _ = (∑ k ∈ K, (exceptionalInterval (k * y) y).card) +
          K.card * (y + 1).primesBelow.card := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (exceptionalInterval 0 ((x / y + 1) * y)).card +
          K.card * (y + 1).primesBelow.card := Nat.add_le_add_right hsumE _
    _ = (x / y + 1) * (y + 1).primesBelow.card +
          (exceptionalInterval 0 ((x / y + 1) * y)).card := by
      simp [K, Nat.add_comm]

/-- The reverse half of the exact finite fixed-threshold comparison. -/
theorem smooth_card_le_smallT_add_errors (x y : ℕ) (hy : 0 < y) :
    (Nat.smoothNumbersUpTo x (y + 1)).card ≤
      (smallTUpTo x y).card +
        ((x / y + 1) * (y + 1).primesBelow.card +
          (exceptionalInterval 0 ((x / y + 1) * y)).card) := by
  let M := Nat.smoothNumbersUpTo x (y + 1)
  let G := M.filter fun n ↦ t n ≤ y
  let F := smoothFixedFailures x y
  have hGsub : G ⊆ smallTUpTo x y := by
    intro n hn
    have hn' : n ∈ M ∧ t n ≤ y := Finset.mem_filter.mp hn
    have hnM := Nat.mem_smoothNumbersUpTo.mp hn'.1
    have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hnM.2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hnM.1⟩, hn'.2⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := M) (fun n ↦ t n ≤ y)
  have hnot : (M.filter fun n ↦ ¬t n ≤ y) = F := by
    ext n
    simp [F, M, smoothFixedFailures]
  change G.card + (M.filter fun n ↦ ¬t n ≤ y).card = M.card at hsplit
  rw [hnot] at hsplit
  have hF := smoothFixedFailures_card_le x y hy
  change F.card ≤ (x / y + 1) * (y + 1).primesBelow.card +
    (exceptionalInterval 0 ((x / y + 1) * y)).card at hF
  have hG := Finset.card_le_card hGsub
  change M.card ≤ (smallTUpTo x y).card +
    ((x / y + 1) * (y + 1).primesBelow.card +
      (exceptionalInterval 0 ((x / y + 1) * y)).card)
  omega

/-- The elementary consequence of Chebyshev's estimate needed below:
`pi(y) / y` tends to zero. -/
theorem primeCounting_div_self_tendsto_zero :
    Filter.Tendsto (fun y : ℕ ↦ (Nat.primeCounting y : ℝ) / (y : ℝ))
      Filter.atTop (nhds 0) := by
  have hchebR := Chebyshev.eventually_primeCounting_le
    (show (0 : ℝ) < 1 from zero_lt_one)
  have hchebN := (tendsto_natCast_atTop_atTop (R := ℝ)) hchebR
  have hbound : ∀ᶠ y : ℕ in Filter.atTop,
      (Nat.primeCounting y : ℝ) ≤ 4 * (y : ℝ) / Real.log y := by
    filter_upwards [hchebN, Filter.eventually_ge_atTop 3] with y hyC hy3
    change (Nat.primeCounting ⌊(y : ℝ)⌋₊ : ℝ) ≤
      (Real.log 4 + 1) * (y : ℝ) / Real.log y at hyC
    rw [Nat.floor_natCast] at hyC
    have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
    have hlog : 0 < Real.log (y : ℝ) := Real.log_pos hy1
    have hlog4 : Real.log (4 : ℝ) < 3 / 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      nlinarith [Real.log_two_lt_d9]
    calc
      (Nat.primeCounting y : ℝ) ≤
          (Real.log 4 + 1) * (y : ℝ) / Real.log y := hyC
      _ ≤ 4 * (y : ℝ) / Real.log y := by
        apply div_le_div_of_nonneg_right _ hlog.le
        nlinarith
  have hmajorant : Filter.Tendsto (fun y : ℕ ↦ (4 : ℝ) / Real.log y)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ hmajorant
  filter_upwards [hbound, Filter.eventually_ge_atTop 3] with y hyB hy3
  have hyPos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hyPos.le)]
  calc
    (Nat.primeCounting y : ℝ) / (y : ℝ) ≤
        (4 * (y : ℝ) / Real.log y) / (y : ℝ) :=
      div_le_div_of_nonneg_right hyB hyPos.le
    _ = 4 / Real.log y := by field_simp

theorem eventually_primeCounting_le_four_mul_div_log :
    ∀ᶠ y : ℕ in Filter.atTop,
      (Nat.primeCounting y : ℝ) ≤ 4 * (y : ℝ) / Real.log y := by
  have hchebR := Chebyshev.eventually_primeCounting_le
    (show (0 : ℝ) < 1 from zero_lt_one)
  have hchebN := (tendsto_natCast_atTop_atTop (R := ℝ)) hchebR
  filter_upwards [hchebN, Filter.eventually_ge_atTop 3] with y hyC hy3
  change (Nat.primeCounting ⌊(y : ℝ)⌋₊ : ℝ) ≤
    (Real.log 4 + 1) * (y : ℝ) / Real.log y at hyC
  rw [Nat.floor_natCast] at hyC
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos hy1
  have hlog4 : Real.log (4 : ℝ) < 3 / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_lt_d9]
  calc
    (Nat.primeCounting y : ℝ) ≤
        (Real.log 4 + 1) * (y : ℝ) / Real.log y := hyC
    _ ≤ 4 * (y : ℝ) / Real.log y := by
      apply div_le_div_of_nonneg_right _ hlog.le
      nlinarith

/-- The exact sparse-curve expression is eventually bounded by the same
balanced magnitude as the direct branch.  The numerical constant is kept
deliberately generous so that every elementary loss remains visible. -/
lemma sparse_height_expression_le_balance_eventually :
    ∀ᶠ J : ℕ in Filter.atTop, ∀ L : ℝ,
      (((lowerBalanceCutoff J - 2 : ℕ) : ℝ) * L ≤
        ((lowerBalanceCutoff J - 2 : ℕ) : ℝ) *
            Real.log ((3 * (16 ^ (212 * 4 ^ 4)) : ℕ) : ℝ) +
          ((50 * 4 ^ 4 + 1 : ℕ) : ℝ) *
            (((4 * (lowerBalanceCutoff J - 2) : ℕ) : ℝ) *
                Real.log ((4 * (J + 1) : ℕ) : ℝ) +
              ((4 * (Nat.primeCounting J +
                  (lowerBalanceCutoff J) ^ 2 * Nat.log 2 J) : ℕ) : ℝ) *
                Real.log (J : ℝ))) →
        L ≤ 2000000 * lowerBalanceMagnitude J := by
  let C₀ : ℝ := Real.log ((3 * (16 ^ (212 * 4 ^ 4)) : ℕ) : ℝ)
  have hmagC := lowerBalanceMagnitude_tendsto_atTop.eventually
    (Filter.eventually_ge_atTop C₀)
  have hscaleOne := lowerBalanceScale_tendsto_atTop.eventually
    (Filter.eventually_ge_atTop 1)
  have hlogTop : Filter.Tendsto (fun J : ℕ ↦ Real.log (J : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne := hlogTop.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [eventually_lowerBalanceCutoff_bounds,
    eventually_lowerBalanceCutoff_le_self,
    eventually_log_le_lowerBalanceScale_sq,
    eventually_primeCounting_le_four_mul_div_log,
    hmagC, hscaleOne, hlogOne, Filter.eventually_ge_atTop 3] with
      J hcut hcutJ hlogScale hpi hmagC hscaleOne hlogOne hJ
  intro L hSparse
  let r := lowerBalanceCutoff J
  have hr3 : 3 ≤ r := hcut.1
  have hrmPos : (0 : ℝ) < (r - 2 : ℕ) := by
    exact_mod_cast (show 0 < r - 2 by omega)
  have hJR : (0 : ℝ) < J := by positivity
  have hlogPos : 0 < Real.log (J : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < J by omega))
  have hscaleNonneg : 0 ≤ lowerBalanceScale J := hscaleOne.trans' zero_le_one
  have hmagNonneg : 0 ≤ lowerBalanceMagnitude J := by
    rw [lowerBalanceMagnitude]
    positivity
  have hrToScale : (r : ℝ) ≤ lowerBalanceScale J := by
    simpa [r] using hcut.2.2
  have hscaleToR : lowerBalanceScale J ≤ 6 * ((r - 2 : ℕ) : ℝ) := by
    have hlow : lowerBalanceScale J / 2 ≤ (r : ℝ) := by
      simpa [r] using hcut.2.1
    have hrthree : (r : ℝ) ≤ 3 * ((r - 2 : ℕ) : ℝ) := by
      exact_mod_cast (show r ≤ 3 * (r - 2) by omega)
    nlinarith
  have hJbalance : (J : ℝ) ≤
      6 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by
    calc
      (J : ℝ) = lowerBalanceScale J * lowerBalanceMagnitude J :=
        (lowerBalanceScale_mul_magnitude (by omega : 1 < J)).symm
      _ ≤ (6 * ((r - 2 : ℕ) : ℝ)) * lowerBalanceMagnitude J :=
        mul_le_mul_of_nonneg_right hscaleToR hmagNonneg
  have hlogMag : Real.log (J : ℝ) ≤ lowerBalanceMagnitude J := by
    rw [lowerBalanceMagnitude]
    have hpowOne : (1 : ℝ) ≤ lowerBalanceScale J ^ 5 := by
      exact one_le_pow₀ hscaleOne
    nlinarith [mul_le_mul_of_nonneg_right hpowOne hlogPos.le]
  have hpiLog : (Nat.primeCounting J : ℝ) * Real.log (J : ℝ) ≤
      4 * (J : ℝ) := by
    calc
      (Nat.primeCounting J : ℝ) * Real.log (J : ℝ) ≤
          (4 * (J : ℝ) / Real.log (J : ℝ)) * Real.log (J : ℝ) :=
        mul_le_mul_of_nonneg_right hpi hlogPos.le
      _ = 4 * (J : ℝ) := by field_simp
  have hlogSq : Real.log (J : ℝ) ^ 2 ≤ lowerBalanceScale J ^ 4 := by
    calc
      Real.log (J : ℝ) ^ 2 ≤ (lowerBalanceScale J ^ 2) ^ 2 :=
        pow_le_pow_left₀ hlogPos.le hlogScale 2
      _ = lowerBalanceScale J ^ 4 := by ring
  have hrLogSq : (r : ℝ) * Real.log (J : ℝ) ^ 2 ≤
      lowerBalanceScale J ^ 5 := by
    calc
      (r : ℝ) * Real.log (J : ℝ) ^ 2 ≤
          lowerBalanceScale J * lowerBalanceScale J ^ 4 :=
        mul_le_mul hrToScale hlogSq (sq_nonneg _) hscaleNonneg
      _ = lowerBalanceScale J ^ 5 := by ring
  have hrThree : (r : ℝ) ≤ 3 * ((r - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show r ≤ 3 * (r - 2) by omega)
  have hscaleFiveMag : lowerBalanceScale J ^ 5 ≤ lowerBalanceMagnitude J := by
    rw [lowerBalanceMagnitude]
    exact le_mul_of_one_le_right (by positivity) hlogOne
  have hNatLog := natLog_two_le_two_mul_log (show 2 ≤ J by omega)
  have hA :
      (4 * ((r - 2 : ℕ) : ℝ)) *
          Real.log (4 * ((J : ℝ) + 1)) ≤
        16 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by
    have hlogFour : Real.log (4 * ((J : ℝ) + 1)) ≤
        4 * Real.log (J : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
        using log_four_mul_succ_le_four_mul_log (show 2 ≤ J by omega)
    calc
      (4 * ((r - 2 : ℕ) : ℝ)) * Real.log (4 * ((J : ℝ) + 1)) ≤
          (4 * ((r - 2 : ℕ) : ℝ)) * (4 * Real.log (J : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogFour (by positivity)
      _ ≤ 16 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by
        nlinarith [mul_le_mul_of_nonneg_left hlogMag
          (show 0 ≤ 16 * ((r - 2 : ℕ) : ℝ) by positivity)]
  have hB : 4 * (Nat.primeCounting J : ℝ) * Real.log (J : ℝ) ≤
      96 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by
    calc
      4 * (Nat.primeCounting J : ℝ) * Real.log (J : ℝ) ≤
          16 * (J : ℝ) := by nlinarith
      _ ≤ 96 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by
        nlinarith
  have hC : 4 * (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) *
        Real.log (J : ℝ) ≤
      24 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by
    have hcore : (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) *
        Real.log (J : ℝ) ≤
        2 * (r : ℝ) * lowerBalanceScale J ^ 5 := by
      calc
        (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) * Real.log (J : ℝ) ≤
            (r : ℝ) ^ 2 * (2 * Real.log (J : ℝ)) *
              Real.log (J : ℝ) := by
          gcongr
        _ = 2 * (r : ℝ) *
              ((r : ℝ) * Real.log (J : ℝ) ^ 2) := by ring
        _ ≤ 2 * (r : ℝ) * lowerBalanceScale J ^ 5 := by
          gcongr
    calc
      4 * (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) * Real.log (J : ℝ) ≤
          8 * (r : ℝ) * lowerBalanceScale J ^ 5 := by nlinarith
      _ ≤ 24 * ((r - 2 : ℕ) : ℝ) * lowerBalanceScale J ^ 5 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ ≤ 24 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by
        gcongr
  have hInner :
      (4 * ((r - 2 : ℕ) : ℝ)) * Real.log (4 * ((J : ℝ) + 1)) +
          4 * ((Nat.primeCounting J : ℝ) +
            (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ)) * Real.log (J : ℝ) ≤
        136 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by
    calc
      _ = (4 * ((r - 2 : ℕ) : ℝ)) * Real.log (4 * ((J : ℝ) + 1)) +
          (4 * (Nat.primeCounting J : ℝ) * Real.log (J : ℝ)) +
          (4 * (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ) * Real.log (J : ℝ)) := by
            ring
      _ ≤ 16 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J +
          96 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J +
          24 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J :=
        add_le_add (add_le_add hA hB) hC
      _ = 136 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J := by ring
  have hSparse' : ((r - 2 : ℕ) : ℝ) * L ≤
      ((r - 2 : ℕ) : ℝ) * C₀ + 12801 *
        ((4 * ((r - 2 : ℕ) : ℝ)) * Real.log (4 * ((J : ℝ) + 1)) +
          4 * ((Nat.primeCounting J : ℝ) +
            (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ)) * Real.log (J : ℝ)) := by
    have hcoef : (50 * 4 ^ 4 + 1 : ℕ) = 12801 := by norm_num
    rw [hcoef] at hSparse
    simpa only [r, C₀, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ lowerBalanceCutoff J),
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using hSparse
  have hRhs : ((r - 2 : ℕ) : ℝ) * C₀ + 12801 *
        ((4 * ((r - 2 : ℕ) : ℝ)) * Real.log (4 * ((J : ℝ) + 1)) +
          4 * ((Nat.primeCounting J : ℝ) +
            (r : ℝ) ^ 2 * (Nat.log 2 J : ℝ)) * Real.log (J : ℝ)) ≤
      ((r - 2 : ℕ) : ℝ) * (2000000 * lowerBalanceMagnitude J) := by
    have hconst : ((r - 2 : ℕ) : ℝ) * C₀ ≤
        ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J :=
      mul_le_mul_of_nonneg_left hmagC (by positivity)
    calc
      _ ≤ ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J +
          12801 * (136 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J) :=
        add_le_add hconst (mul_le_mul_of_nonneg_left hInner (by positivity))
      _ ≤ ((r - 2 : ℕ) : ℝ) *
          (2000000 * lowerBalanceMagnitude J) := by
        have hcoef : (1 + 12801 * 136 : ℝ) ≤ 2000000 := by norm_num
        have hnonneg : 0 ≤ ((r - 2 : ℕ) : ℝ) *
            lowerBalanceMagnitude J := mul_nonneg (by positivity) hmagNonneg
        calc
          ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J +
              12801 * (136 * ((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J) =
              (1 + 12801 * 136) *
                (((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J) := by ring
          _ ≤ 2000000 *
                (((r - 2 : ℕ) : ℝ) * lowerBalanceMagnitude J) :=
            mul_le_mul_of_nonneg_right hcoef hnonneg
          _ = ((r - 2 : ℕ) : ℝ) *
                (2000000 * lowerBalanceMagnitude J) := by ring
  exact le_of_mul_le_mul_left (hSparse'.trans hRhs) hrmPos

/-- Conditional on the effective integral-point estimate, the direct and
sparse branches combine at the BPZ balancing scale. -/
theorem eventual_minimal_loglog_balance
    (hheight : EffectiveHyperellipticHeightBound) :
    ∀ᶠ J : ℕ in Filter.atTop, ∀ n : ℕ,
      ¬IsSquare n → 1 < n → t n = J →
        n ≤ J ^ 2 ∨
          Real.log (Real.log (n : ℝ)) ≤
            2000000 * lowerBalanceMagnitude J := by
  filter_upwards [eventually_lowerBalanceCutoff_bounds,
    eventually_lowerBalanceCutoff_le_self,
    sparse_height_expression_le_balance_eventually,
    Filter.eventually_ge_atTop 3] with J hcut hcutJ hsparse hJ
  intro n hn hnlarge ht
  have hdich := minimal_balancing_dichotomy hheight hn hnlarge hcut.1
  rcases hdich with hquad | hdirect | hsparseRaw
  · left
    simpa only [ht] using hquad
  · right
    obtain ⟨D, hDthree, hDcut, hraw⟩ := hdirect
    have hDJ : D ≤ J := hDcut.trans hcutJ
    have hDscale : (D : ℝ) ≤ lowerBalanceScale J := by
      exact (Nat.cast_le.mpr hDcut).trans hcut.2.2
    have hbound := direct_height_expression_le_balance (by omega : 2 ≤ J)
      hDthree hDJ hDscale
    rw [ht] at hraw
    have hmag : 0 ≤ lowerBalanceMagnitude J := by
      rw [lowerBalanceMagnitude]
      have hscale : 0 ≤ lowerBalanceScale J := hcut.2.2.trans' (by positivity)
      exact mul_nonneg (pow_nonneg hscale _)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ J by omega)))
    exact hraw.trans (hbound.trans (by nlinarith))
  · right
    rw [ht] at hsparseRaw
    exact hsparse (Real.log (Real.log (n : ℝ))) hsparseRaw

/-- Conditional on the effective height theorem, `t n` tends to infinity
along the nonsquares.  This supplies the eventual cutoff hypotheses needed
to apply the balanced estimate with `J = t n`. -/
theorem eventually_t_ge_of_not_square
    (hheight : EffectiveHyperellipticHeightBound) (B : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n → B ≤ t n := by
  let M := B + 3
  let K : ℝ :=
    ((212 * M ^ 4 : ℕ) : ℝ) * Real.log ((4 * M : ℕ) : ℝ) +
      ((50 * M ^ 4 : ℕ) : ℝ) *
        ((M : ℝ) * Real.log (M : ℝ))
  have hloglogTop : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogLarge := hloglogTop.eventually (Filter.eventually_gt_atTop K)
  filter_upwards [hlogLarge, Filter.eventually_gt_atTop (M ^ 2),
    Filter.eventually_ge_atTop 2] with n hlogLarge hnM hn2
  intro hn
  by_contra hBt
  have htB : t n < B := by omega
  have hMthree : 3 ≤ M := by simp [M]
  have htM : t n + 1 ≤ M := by simp [M]; omega
  rcases minimal_direct_loglog_dichotomy hheight hn (by omega : 1 < n) with
    hquad | ⟨D, hDthree, hDt, hraw⟩
  · have htSq : (t n) ^ 2 < M ^ 2 := by
      exact Nat.pow_lt_pow_left (by omega : t n < M) (by decide)
    omega
  · have hDM : D ≤ M := hDt.trans htM
    have hDfour : (212 * D ^ 4 : ℕ) ≤ 212 * M ^ 4 :=
      Nat.mul_le_mul_left 212 (Nat.pow_le_pow_left hDM 4)
    have hDfifty : (50 * D ^ 4 : ℕ) ≤ 50 * M ^ 4 :=
      Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left hDM 4)
    have hlogFour : Real.log ((4 * D : ℕ) : ℝ) ≤
        Real.log ((4 * M : ℕ) : ℝ) :=
      Real.log_le_log (by positivity)
        (by exact_mod_cast Nat.mul_le_mul_left 4 hDM)
    have hlogM : 0 ≤ Real.log (M : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
    have hlogTM : Real.log ((t n + 1 : ℕ) : ℝ) ≤
        Real.log (M : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast htM)
    have hlogPow : Real.log ((((t n + 1) ^ D : ℕ) : ℝ)) ≤
        (M : ℝ) * Real.log (M : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
      exact mul_le_mul (by exact_mod_cast hDM) hlogTM
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ t n + 1 by omega)))
        (by positivity)
    have hfirst :
        ((212 * D ^ 4 : ℕ) : ℝ) * Real.log ((4 * D : ℕ) : ℝ) ≤
          ((212 * M ^ 4 : ℕ) : ℝ) * Real.log ((4 * M : ℕ) : ℝ) :=
      mul_le_mul (by exact_mod_cast hDfour) hlogFour
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * D by omega))) (by positivity)
    have hsecond :
        ((50 * D ^ 4 : ℕ) : ℝ) *
            Real.log ((((t n + 1) ^ D : ℕ) : ℝ)) ≤
          ((50 * M ^ 4 : ℕ) : ℝ) *
            ((M : ℝ) * Real.log (M : ℝ)) :=
      mul_le_mul (by exact_mod_cast hDfifty) hlogPow
        (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ (t n + 1) ^ D by
            exact one_le_pow₀ (by omega : 1 ≤ t n + 1)))) (by positivity)
    have : Real.log (Real.log (n : ℝ)) ≤ K := by
      exact hraw.trans (by simpa [K] using add_le_add hfirst hsecond)
    exact (not_le_of_gt hlogLarge) this

theorem eventual_minimal_loglog_balance_on_n
    (hheight : EffectiveHyperellipticHeightBound) :
    ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      n ≤ (t n) ^ 2 ∨
        Real.log (Real.log (n : ℝ)) ≤
          2000000 * lowerBalanceMagnitude (t n) := by
  have hbalance := eventual_minimal_loglog_balance hheight
  rw [Filter.eventually_atTop] at hbalance
  obtain ⟨J₀, hJ₀⟩ := hbalance
  filter_upwards [eventually_t_ge_of_not_square hheight J₀,
    Filter.eventually_ge_atTop 2] with n htLarge hn2
  intro hn
  exact hJ₀ (t n) (htLarge hn) n hn (by omega) rfl

/-- BPZ's pointwise lower bound, conditional only on the explicit
effective integral-point theorem isolated above.  The function
`lowerBoundShape` is exactly
`(log log n)^(6/5) / (log log log n)^(1/5)` when the iterated logarithms
are positive. -/
theorem erdos841_lower_bound_of_effective_height
    (hheight : EffectiveHyperellipticHeightBound) :
    ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      lowerBoundConstant * lowerBoundShape n ≤ (t n : ℝ) := by
  filter_upwards [eventual_minimal_loglog_balance_on_n hheight,
    eventually_lowerBoundShape_inputs,
    eventually_t_ge_of_not_square hheight 2] with n hbalance hinput htTwo
  intro hn
  have hbal := hbalance hn
  have ht := htTwo hn
  let L := Real.log (Real.log (n : ℝ))
  have hL : 1 < L := hinput.1
  have hlogL : 1 ≤ Real.log L := by simpa [L] using hinput.2.1
  have hshape : lowerBoundShape n = lowerLogShape L := rfl
  have hshapeSq : lowerLogShape L ≤ L ^ 2 :=
    lowerLogShape_le_sq hL hlogL
  have hcPos : 0 < lowerBoundConstant := by
    norm_num [lowerBoundConstant]
  have hcOne : lowerBoundConstant ≤ 1 := by
    norm_num [lowerBoundConstant]
  have hshapeNonneg : 0 ≤ lowerLogShape L := lowerLogShape_nonneg hL
  have hcrude : lowerBoundConstant * lowerLogShape L ≤ L ^ 2 := by
    exact (mul_le_mul_of_nonneg_right hcOne hshapeNonneg).trans (by simpa using hshapeSq)
  rcases hbal with hquad | hheightBal
  · rw [hshape]
    have hpow : (L ^ 2) ^ 2 ≤ ((t n : ℝ) ^ 2) := by
      calc
        (L ^ 2) ^ 2 = L ^ 4 := by ring
        _ ≤ (n : ℝ) := hinput.2.2
        _ ≤ ((t n : ℝ) ^ 2) := by exact_mod_cast hquad
    have hLsq : L ^ 2 ≤ (t n : ℝ) :=
      le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) hpow
    exact hcrude.trans hLsq
  · rw [hshape]
    by_cases hsmall : (t n : ℝ) ≤ L ^ 2
    · apply lowerLogShape_le_of_balance
          (A := lowerBalanceMagnitude (t n)) hL hlogL
          (by exact_mod_cast (show 1 < t n by omega)) hsmall
      · rw [lowerBalanceMagnitude]
        have hs : 0 ≤ lowerBalanceScale (t n) := by
          rw [lowerBalanceScale]
          apply Real.rpow_nonneg
          exact div_nonneg (by positivity)
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ t n by omega)))
        exact mul_nonneg (pow_nonneg hs _)
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ t n by omega)))
      · exact hheightBal
      · exact lowerBalanceMagnitude_pow_six (by omega : 1 < t n)
    · exact hcrude.trans (lt_of_not_ge hsmall).le

theorem erdos841_lower_bound_explicit_of_effective_height
    (hheight : EffectiveHyperellipticHeightBound) :
    ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      lowerBoundConstant *
          (Real.log (Real.log (n : ℝ)) ^ ((6 : ℝ) / 5) *
            Real.log (Real.log (Real.log (n : ℝ))) ^ (-((1 : ℝ) / 5))) ≤
        (t n : ℝ) := by
  filter_upwards [erdos841_lower_bound_of_effective_height hheight,
    eventually_lowerBoundShape_inputs] with n hbound hinput
  intro hn
  have hb := hbound hn
  rw [lowerBoundShape,
    lowerLogShape_eq hinput.1] at hb
  exact hb

lemma primesBelow_succ_card_eq_primeCounting (y : ℕ) :
    (y + 1).primesBelow.card = Nat.primeCounting y := by
  rw [Nat.primesBelow_card_eq_primeCounting']
  exact (Nat.primeCounting_eq_primeCounting'_succ y).symm

/-- A single natural-number error term dominating both directions of the
fixed-threshold comparison. -/
def fixedThresholdError (x y : ℕ) : ℕ :=
  (exceptionalInterval 0 x).card +
    ((x / y + 1) * (y + 1).primesBelow.card +
      (exceptionalInterval 0 ((x / y + 1) * y)).card)

/-- The normalized finite-comparison error is `o(1)` for every threshold
which tends to infinity and remains at most `x`. -/
theorem fixedThresholdError_density_zero (y : ℕ → ℕ)
    (hyTop : Filter.Tendsto y Filter.atTop Filter.atTop)
    (hyle : ∀ᶠ x : ℕ in Filter.atTop, y x ≤ x) :
    Filter.Tendsto
      (fun x : ℕ ↦ (fixedThresholdError x (y x) : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
  let H : ℕ → ℕ := fun x ↦ (x / y x + 1) * y x
  have hyPos : ∀ᶠ x : ℕ in Filter.atTop, 0 < y x :=
    hyTop.eventually (Filter.eventually_gt_atTop 0)
  have hxPos : ∀ᶠ x : ℕ in Filter.atTop, 0 < x :=
    Filter.eventually_gt_atTop 0
  have hHbounds : ∀ᶠ x : ℕ in Filter.atTop, x ≤ H x ∧ H x ≤ 2 * x := by
    filter_upwards [hyPos, hyle] with x hy hxy
    have hdecomp := Nat.mod_add_div x (y x)
    have hmod := Nat.mod_lt x hy
    have hdiv := Nat.div_mul_le_self x (y x)
    have hdecomp' : x % y x + (x / y x) * y x = x := by
      simpa [Nat.mul_comm] using hdecomp
    change x ≤ (x / y x + 1) * y x ∧ (x / y x + 1) * y x ≤ 2 * x
    constructor
    · have : x < (x / y x + 1) * y x := by
        rw [Nat.add_mul]
        omega
      exact this.le
    · rw [Nat.add_mul]
      omega
  have hHTop : Filter.Tendsto H Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono' Filter.atTop
      (hHbounds.mono fun x hx ↦ hx.1) Filter.tendsto_id
  have hprimeY : Filter.Tendsto
      (fun x : ℕ ↦ (Nat.primeCounting (y x) : ℝ) / (y x : ℝ))
      Filter.atTop (nhds 0) := primeCounting_div_self_tendsto_zero.comp hyTop
  have hprimeMajor : Filter.Tendsto
      (fun x : ℕ ↦ 2 * ((Nat.primeCounting (y x) : ℝ) / (y x : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hprimeY
  have hblocks : Filter.Tendsto
      (fun x : ℕ ↦
        (((x / y x + 1) * (y x + 1).primesBelow.card : ℕ) : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hprimeMajor
    filter_upwards [hyPos, hyle, hxPos] with x hy hxy hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hyR : (0 : ℝ) < y x := by exact_mod_cast hy
    rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hxR.le)]
    rw [primesBelow_succ_card_eq_primeCounting]
    have hceil : (x / y x + 1) * y x ≤ 2 * x := by
      have hdiv := Nat.div_mul_le_self x (y x)
      rw [Nat.add_mul]
      omega
    have hcross :
        ((x / y x + 1) * Nat.primeCounting (y x)) * y x ≤
          2 * Nat.primeCounting (y x) * x := by
      calc
        ((x / y x + 1) * Nat.primeCounting (y x)) * y x =
            Nat.primeCounting (y x) * ((x / y x + 1) * y x) := by ring
        _ ≤ Nat.primeCounting (y x) * (2 * x) :=
          Nat.mul_le_mul_left _ hceil
        _ = 2 * Nat.primeCounting (y x) * x := by ring
    have hreal :
        (((x / y x + 1) * Nat.primeCounting (y x) : ℕ) : ℝ) / x ≤
          (2 * (Nat.primeCounting (y x) : ℝ)) / y x := by
      rw [div_le_div_iff₀ hxR hyR]
      exact_mod_cast hcross
    simpa only [mul_div_assoc] using hreal
  have hEbase := exceptionalInterval_density_zero
  have hEHbase : Filter.Tendsto
      (fun x : ℕ ↦ ((exceptionalInterval 0 (H x)).card : ℝ) / (H x : ℝ))
      Filter.atTop (nhds 0) := hEbase.comp hHTop
  have hEHmajor : Filter.Tendsto
      (fun x : ℕ ↦ 2 *
        (((exceptionalInterval 0 (H x)).card : ℝ) / (H x : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hEHbase
  have hEH : Filter.Tendsto
      (fun x : ℕ ↦ ((exceptionalInterval 0 (H x)).card : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hEHmajor
    filter_upwards [hHbounds, hxPos] with x hHb hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hHR : (0 : ℝ) < H x := by exact_mod_cast hx.trans_le hHb.1
    rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hxR.le)]
    have hcross : (exceptionalInterval 0 (H x)).card * H x ≤
        2 * (exceptionalInterval 0 (H x)).card * x := by
      calc
        (exceptionalInterval 0 (H x)).card * H x ≤
            (exceptionalInterval 0 (H x)).card * (2 * x) :=
          Nat.mul_le_mul_left _ hHb.2
        _ = 2 * (exceptionalInterval 0 (H x)).card * x := by ring
    have hreal : ((exceptionalInterval 0 (H x)).card : ℝ) / x ≤
        (2 * ((exceptionalInterval 0 (H x)).card : ℝ)) / H x := by
      rw [div_le_div_iff₀ hxR hHR]
      exact_mod_cast hcross
    simpa only [mul_div_assoc] using hreal
  have hsum : Filter.Tendsto
      (fun x : ℕ ↦ ((exceptionalInterval 0 x).card : ℝ) / (x : ℝ) +
        ((((x / y x + 1) * (y x + 1).primesBelow.card : ℕ) : ℝ) / (x : ℝ) +
          ((exceptionalInterval 0 (H x)).card : ℝ) / (x : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using hEbase.add (hblocks.add hEH)
  apply hsum.congr'
  filter_upwards [hyPos] with x hy
  simp only [fixedThresholdError, Nat.cast_add]
  change
    ((exceptionalInterval 0 x).card : ℝ) / (x : ℝ) +
      ((((x / y x + 1) * (y x + 1).primesBelow.card : ℕ) : ℝ) / (x : ℝ) +
        ((exceptionalInterval 0 (H x)).card : ℝ) / (x : ℝ)) =
      (((exceptionalInterval 0 x).card : ℝ) +
        ((((x / y x + 1) * (y x + 1).primesBelow.card : ℕ) : ℝ) +
          ((exceptionalInterval 0 (H x)).card : ℝ))) / (x : ℝ)
  simp only [H]
  ring

/-- BPZ Theorem 3.1 in its qualitative, threshold-agnostic form.  Whenever
`y(x) → ∞` and `y(x) ≤ x`, the normalized fixed-threshold counting
functions for `t` and for smooth numbers differ by `o(1)`. -/
theorem fixedThreshold_comparison_tendsto_zero (y : ℕ → ℕ)
    (hyTop : Filter.Tendsto y Filter.atTop Filter.atTop)
    (hyle : ∀ᶠ x : ℕ in Filter.atTop, y x ≤ x) :
    Filter.Tendsto
      (fun x : ℕ ↦
        (((smallTUpTo x (y x)).card : ℝ) -
          ((Nat.smoothNumbersUpTo x (y x + 1)).card : ℝ)) / (x : ℝ))
      Filter.atTop (nhds 0) := by
  have hyPos : ∀ᶠ x : ℕ in Filter.atTop, 0 < y x :=
    hyTop.eventually (Filter.eventually_gt_atTop 0)
  have hxPos : ∀ᶠ x : ℕ in Filter.atTop, 0 < x :=
    Filter.eventually_gt_atTop 0
  apply squeeze_zero_norm' _ (fixedThresholdError_density_zero y hyTop hyle)
  filter_upwards [hyPos, hxPos] with x hy hx
  let A := (smallTUpTo x (y x)).card
  let B := (Nat.smoothNumbersUpTo x (y x + 1)).card
  let R := fixedThresholdError x (y x)
  have hforward := smallTUpTo_card_le_smooth_add_exceptional x (y x)
  have hreverse := smooth_card_le_smallT_add_errors x (y x) hy
  have hAR : A ≤ B + R := by
    change (smallTUpTo x (y x)).card ≤
      (Nat.smoothNumbersUpTo x (y x + 1)).card + fixedThresholdError x (y x)
    exact hforward.trans (Nat.add_le_add_left
      (by simp [fixedThresholdError] :
        (exceptionalInterval 0 x).card ≤ fixedThresholdError x (y x)) _)
  have hBR : B ≤ A + R := by
    change B ≤ A +
      ((x / y x + 1) * (y x + 1).primesBelow.card +
        (exceptionalInterval 0 ((x / y x + 1) * y x)).card) at hreverse
    change B ≤ A + R
    simp only [R, fixedThresholdError]
    omega
  have habs : |(A : ℝ) - (B : ℝ)| ≤ (R : ℝ) := by
    have hARreal : (A : ℝ) ≤ (B : ℝ) + (R : ℝ) := by exact_mod_cast hAR
    have hBRreal : (B : ℝ) ≤ (A : ℝ) + (R : ℝ) := by exact_mod_cast hBR
    rw [abs_le]
    constructor <;> linarith
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  change ‖(((A : ℝ) - (B : ℝ)) / (x : ℝ))‖ ≤ (R : ℝ) / (x : ℝ)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hxR.le]
  exact div_le_div_of_nonneg_right habs hxR.le

/-- The integer threshold representing `x^c`. -/
def powerThreshold (c : ℝ) (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ c⌋₊

lemma powerThreshold_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (powerThreshold c) Filter.atTop Filter.atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop)

lemma eventually_powerThreshold_le_self {c : ℝ} (hc : c ≤ 1) :
    ∀ᶠ x : ℕ in Filter.atTop, powerThreshold c x ≤ x := by
  filter_upwards [Filter.eventually_ge_atTop 1] with x hx
  apply Nat.floor_le_of_le
  change (x : ℝ) ^ c ≤ (x : ℝ)
  calc
    (x : ℝ) ^ c ≤ (x : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx) hc
    _ = (x : ℝ) := Real.rpow_one _

lemma powerThreshold_mono {c : ℝ} (hc : 0 ≤ c) : Monotone (powerThreshold c) := by
  intro m n hmn
  apply Nat.floor_mono
  exact Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmn) hc

lemma powerThreshold_cast_le_rpow (c : ℝ) (x : ℕ) :
    (powerThreshold c x : ℝ) ≤ (x : ℝ) ^ c := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) c)

lemma eventually_half_rpow_le_powerThreshold {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ c / 2 ≤ (powerThreshold c x : ℝ) := by
  have hpowTop : Filter.Tendsto (fun x : ℕ ↦ (x : ℝ) ^ c)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hpowTwo : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ (x : ℝ) ^ c :=
    hpowTop.eventually (Filter.eventually_ge_atTop 2)
  filter_upwards [hpowTwo] with x hx
  have hfloor := Nat.lt_floor_add_one ((x : ℝ) ^ c)
  change (x : ℝ) ^ c < (powerThreshold c x : ℝ) + 1 at hfloor
  nlinarith

/-- The formal fixed-threshold distribution comparison at `x^c`. -/
theorem powerThreshold_comparison_tendsto_zero {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto
      (fun x : ℕ ↦
        (((smallTUpTo x (powerThreshold c x)).card : ℝ) -
          ((Nat.smoothNumbersUpTo x (powerThreshold c x + 1)).card : ℝ)) /
            (x : ℝ))
      Filter.atTop (nhds 0) :=
  fixedThreshold_comparison_tendsto_zero (powerThreshold c)
    (powerThreshold_tendsto_atTop hc0) (eventually_powerThreshold_le_self hc1)

/-! ## BPZ interval bounds with separate length and smoothness cutoffs -/

/-- The `Y`-smooth members of the interval `(X,X+H]`. -/
def smoothIntervalAt (X H Y : ℕ) : Finset ℕ :=
  (Finset.Ioc X (X + H)).filter fun m ↦ m ∈ (Y + 1).smoothNumbers

/-- BPZ Lemma 3.7 with the interval length `H` and smoothness cutoff `Y`
kept separate.  The original published statement is the case `H = Y`. -/
theorem bpz_smooth_interval_bound_general (X H Y : ℕ) :
    (smoothIntervalAt X H Y).card - (Y + 1).primesBelow.card ≤
      (closedStarts X (X + H)).card := by
  let A := smoothIntervalAt X H Y
  let P := (Y + 1).primesBelow
  let v : A → P → ZMod 2 := fun m p ↦ (m.1.factorization p.1 : ZMod 2)
  have hzero_le_square : (zeroSumSubsets v).card ≤
      (squareProductSubsets (Finset.Ioc X (X + H))).card := by
    refine Finset.card_le_card_of_injOn (fun U : Finset A ↦ U.image Subtype.val) ?_ ?_
    · intro U hU
      change U ∈ zeroSumSubsets v at hU
      change U.image Subtype.val ∈ squareProductSubsets (Finset.Ioc X (X + H))
      rw [zeroSumSubsets, Finset.mem_filter] at hU
      rw [mem_squareProductSubsets]
      refine ⟨?_, ?_⟩
      · intro m hm
        obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp hm
        exact (Finset.mem_filter.mp a.2).1
      · have hprod0 : (∏ m ∈ U.image Subtype.val, m) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro m hm
          obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp hm
          have haI := Finset.mem_Ioc.mp (Finset.mem_filter.mp a.2).1
          omega
        rw [isSquare_iff_even_factorization hprod0]
        intro p
        rw [Nat.factorization_prod_apply (fun m hm ↦ by
          obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp hm
          have haI := Finset.mem_Ioc.mp (Finset.mem_filter.mp a.2).1
          omega)]
        by_cases hpP : p ∈ P
        · have hpzero := congrFun hU.2 (⟨p, hpP⟩ : P)
          have hpzero' : (∑ a ∈ U, (a.1.factorization p : ZMod 2)) = 0 := by
            simpa only [Finset.sum_apply, v, Pi.zero_apply] using hpzero
          rw [Finset.sum_image Subtype.val_injective.injOn]
          rw [← ZMod.natCast_eq_zero_iff_even]
          simpa only [Nat.cast_sum] using hpzero'
        · have hsum0 : ∑ m ∈ U.image Subtype.val, m.factorization p = 0 := by
            apply Finset.sum_eq_zero
            intro m hm
            obtain ⟨a, haU, rfl⟩ := Finset.mem_image.mp hm
            have hasmooth := (Finset.mem_filter.mp a.2).2
            by_cases hp : p.Prime
            · apply Nat.factorization_eq_zero_of_not_dvd
              intro hpdvd
              have hplt := (Nat.mem_smoothNumbers').mp hasmooth p hp hpdvd
              exact hpP (Nat.mem_primesBelow.mpr ⟨hplt, hp⟩)
            · exact Nat.factorization_eq_zero_of_not_prime _ hp
          rw [hsum0]
          exact Even.zero
    · exact (Finset.image_injective Subtype.val_injective).injOn
  have hlin := pow_card_sub_card_le_zeroSumSubsets_card v
  have hpows : 2 ^ (A.card - P.card) ≤
      2 ^ (closedStarts X (X + H)).card := by
    simpa [A, P] using hlin.trans hzero_le_square |>.trans_eq
      (card_squareProductSubsets_eq_pow_closedStarts (Nat.le_add_right X H))
  have hexp := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpows
  simpa [A, P] using hexp

/-- BPZ Lemma 4.2, in the exact finite form used for the small-values
argument.  More `Y`-smooth integers than there are primes at most `Y` in
one interval force a starting point in that interval whose least witness
has length at most the interval length. -/
theorem smooth_rich_interval_forces_short_t {X H Y : ℕ}
    (hrich : (Y + 1).primesBelow.card < (smoothIntervalAt X H Y).card) :
    ∃ n ∈ Finset.Ioc X (X + H), t n ≤ H := by
  have hcount := bpz_smooth_interval_bound_general X H Y
  have hclosed : 0 < (closedStarts X (X + H)).card := by
    omega
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hclosed
  have hn' := Finset.mem_filter.mp hn
  refine ⟨n, hn'.1, ?_⟩
  have hnlo := (Finset.mem_Ioc.mp hn'.1).1
  omega

/-- Indices of consecutive length-`H` blocks after `X` which contain more
`Y`-smooth integers than there are primes at most `Y`. -/
def smoothRichBlockIndices (X K H Y : ℕ) : Finset ℕ :=
  (Finset.range K).filter fun k ↦
    (Y + 1).primesBelow.card <
      (smoothIntervalAt (X + k * H) H Y).card

/-- A short-`t` starting point selected from a rich block.  Its value away
from the rich-block index set is irrelevant. -/
noncomputable def smoothRichBlockStart (X K H Y k : ℕ) : ℕ :=
  if hk : k ∈ smoothRichBlockIndices X K H Y then
    Classical.choose
      (smooth_rich_interval_forces_short_t
        ((Finset.mem_filter.mp hk).2))
  else 0

lemma smoothRichBlockStart_spec {X K H Y k : ℕ}
    (hk : k ∈ smoothRichBlockIndices X K H Y) :
    smoothRichBlockStart X K H Y k ∈
        Finset.Ioc (X + k * H) (X + (k + 1) * H) ∧
      t (smoothRichBlockStart X K H Y k) ≤ H := by
  rw [smoothRichBlockStart, dif_pos hk]
  have hspec := Classical.choose_spec
    (smooth_rich_interval_forces_short_t
      ((Finset.mem_filter.mp hk).2))
  simpa [Nat.add_mul, Nat.add_assoc] using hspec

/-- The selected short-`t` starts, one from each rich block. -/
noncomputable def smoothRichBlockStarts (X K H Y : ℕ) : Finset ℕ :=
  (smoothRichBlockIndices X K H Y).image
    (smoothRichBlockStart X K H Y)

lemma smoothRichBlockStart_injOn {X K H Y : ℕ} (_hH : 0 < H) :
    Set.InjOn (smoothRichBlockStart X K H Y)
      (smoothRichBlockIndices X K H Y : Set ℕ) := by
  intro k hk l hl hEq
  by_contra hkl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hkSpec := smoothRichBlockStart_spec hk
    have hlSpec := smoothRichBlockStart_spec hl
    have hmul : (k + 1) * H ≤ l * H :=
      Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hlt)
    have hkUpper := (Finset.mem_Ioc.mp hkSpec.1).2
    have hlLower := (Finset.mem_Ioc.mp hlSpec.1).1
    omega
  · have hkSpec := smoothRichBlockStart_spec hk
    have hlSpec := smoothRichBlockStart_spec hl
    have hmul : (l + 1) * H ≤ k * H :=
      Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hgt)
    have hkLower := (Finset.mem_Ioc.mp hkSpec.1).1
    have hlUpper := (Finset.mem_Ioc.mp hlSpec.1).2
    omega

theorem card_smoothRichBlockStarts {X K H Y : ℕ} (hH : 0 < H) :
    (smoothRichBlockStarts X K H Y).card =
      (smoothRichBlockIndices X K H Y).card := by
  exact Finset.card_image_of_injOn (smoothRichBlockStart_injOn hH)

/-- Every selected rich-block start lies in the union of the `K` blocks
and has `t` at most `H`. -/
theorem smoothRichBlockStarts_subset_short {X K H Y : ℕ} :
    smoothRichBlockStarts X K H Y ⊆
      (Finset.Ioc X (X + K * H)).filter fun n ↦ t n ≤ H := by
  intro n hn
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
  have hkRange := (Finset.mem_filter.mp hk).1
  have hspec := smoothRichBlockStart_spec hk
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hspec.2⟩
  · exact (Nat.le_add_right X (k * H)).trans_lt
      (Finset.mem_Ioc.mp hspec.1).1
  · have hklt : k + 1 ≤ K := by simpa using hkRange
    have hmul : (k + 1) * H ≤ K * H := Nat.mul_le_mul_right H hklt
    exact (Finset.mem_Ioc.mp hspec.1).2.trans (Nat.add_le_add_left hmul X)

/-- Exact finite disjoint-block transfer used in BPZ Theorem 1.2: the
number of short-`t` starts in the covered segment is at least the number of
smooth-rich blocks. -/
theorem smoothRichBlockIndices_card_le_short {X K H Y : ℕ} (hH : 0 < H) :
    (smoothRichBlockIndices X K H Y).card ≤
      ((Finset.Ioc X (X + K * H)).filter fun n ↦ t n ≤ H).card := by
  rw [← card_smoothRichBlockStarts hH]
  exact Finset.card_le_card smoothRichBlockStarts_subset_short

/-- Finite averaging inequality behind the production of many rich blocks.
Any reservoir of `Y`-smooth integers contained in `K` consecutive
length-`H` blocks is bounded by one prime-dimension allowance per block,
plus one full-block allowance for each rich block. -/
theorem reservoir_card_le_rich_blocks
    {R : Finset ℕ} {X K H Y : ℕ} (hH : 0 < H)
    (hRsegment : R ⊆ Finset.Ioc X (X + K * H))
    (hRsmooth : ∀ n ∈ R, n ∈ (Y + 1).smoothNumbers) :
    R.card ≤ K * (Y + 1).primesBelow.card +
      (smoothRichBlockIndices X K H Y).card * H := by
  let KS := Finset.range K
  let f : ℕ → ℕ := fun n ↦ (n - X - 1) / H
  have hmaps : (R : Set ℕ).MapsTo f KS := by
    intro n hn
    have hnI := Finset.mem_Ioc.mp (hRsegment hn)
    have hsub : n - X - 1 < K * H := by omega
    have hdiv : (n - X - 1) / H < K := by
      exact (Nat.div_lt_iff_lt_mul hH).mpr (by simpa [Nat.mul_comm] using hsub)
    simpa [KS, f] using hdiv
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (k : ℕ) (hk : k ∈ KS) :
      ({n ∈ R | f n = k}).card ≤
        (Y + 1).primesBelow.card +
          if k ∈ smoothRichBlockIndices X K H Y then H else 0 := by
    have hsub : {n ∈ R | f n = k} ⊆
        smoothIntervalAt (X + k * H) H Y := by
      intro n hn
      have hnmem := Finset.mem_filter.mp hn
      have hnBase := (Finset.mem_Ioc.mp (hRsegment hnmem.1)).1
      have hmod := Nat.mod_lt (n - X - 1) hH
      have hdecomp := Nat.mod_add_div (n - X - 1) H
      have hfEq : (n - X - 1) / H = k := by simpa [f] using hnmem.2
      rw [hfEq] at hdecomp
      have hdecomp' : (n - X - 1) % H + k * H = n - X - 1 := by
        simpa [Nat.mul_comm] using hdecomp
      have hLower : X + k * H < n := by omega
      have hUpper : n ≤ X + k * H + H := by omega
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hLower, hUpper⟩, hRsmooth n hnmem.1⟩
    by_cases hrich : k ∈ smoothRichBlockIndices X K H Y
    · rw [if_pos hrich]
      have hcardI :
          (Finset.Ioc (X + k * H) (X + k * H + H)).card = H := by simp
      have hSI : smoothIntervalAt (X + k * H) H Y ⊆
          Finset.Ioc (X + k * H) (X + k * H + H) := Finset.filter_subset _ _
      have hle : ({n ∈ R | f n = k}).card ≤ H := by
        calc
          ({n ∈ R | f n = k}).card ≤
              (smoothIntervalAt (X + k * H) H Y).card := Finset.card_le_card hsub
          _ ≤ (Finset.Ioc (X + k * H) (X + k * H + H)).card :=
            Finset.card_le_card hSI
          _ = H := hcardI
      omega
    · rw [if_neg hrich, Nat.add_zero]
      have hnot : (smoothIntervalAt (X + k * H) H Y).card ≤
          (Y + 1).primesBelow.card := by
        exact not_lt.mp fun hlt ↦ hrich
          (Finset.mem_filter.mpr ⟨hk, hlt⟩)
      exact (Finset.card_le_card hsub).trans hnot
  rw [hpartition]
  calc
    ∑ k ∈ KS, ({n ∈ R | f n = k}).card ≤
        ∑ k ∈ KS, ((Y + 1).primesBelow.card +
          if k ∈ smoothRichBlockIndices X K H Y then H else 0) :=
      Finset.sum_le_sum hfiber
    _ = K * (Y + 1).primesBelow.card +
        (smoothRichBlockIndices X K H Y).card * H := by
      rw [Finset.sum_add_distrib]
      have hrichSub : smoothRichBlockIndices X K H Y ⊆ KS :=
        Finset.filter_subset _ _
      rw [← Finset.sum_filter]
      have hfilter : KS.filter
          (fun k ↦ k ∈ smoothRichBlockIndices X K H Y) =
          smoothRichBlockIndices X K H Y := by
        exact Finset.filter_mem_eq_inter.trans
          (Finset.inter_eq_right.mpr hrichSub)
      rw [hfilter]
      simp [KS, Nat.mul_comm]

/-- A directly usable finite many-small-values criterion.  If a smooth
reservoir is larger than the total prime allowance plus `Q` full blocks,
then the segment contains more than `Q` distinct integers with `t ≤ H`. -/
theorem target_lt_short_count_of_smooth_reservoir
    {R : Finset ℕ} {X K H Y Q : ℕ} (hH : 0 < H)
    (hRsegment : R ⊆ Finset.Ioc X (X + K * H))
    (hRsmooth : ∀ n ∈ R, n ∈ (Y + 1).smoothNumbers)
    (hlarge : K * (Y + 1).primesBelow.card + Q * H < R.card) :
    Q < ((Finset.Ioc X (X + K * H)).filter fun n ↦ t n ≤ H).card := by
  have havg := reservoir_card_le_rich_blocks hH hRsegment hRsmooth
  have hmul : Q * H < (smoothRichBlockIndices X K H Y).card * H := by omega
  have hQ : Q < (smoothRichBlockIndices X K H Y).card :=
    (Nat.mul_lt_mul_right hH).mp hmul
  exact hQ.trans_le (smoothRichBlockIndices_card_le_short hH)

/-- Quantitative form of the finite rich-block argument.  After paying one
prime-dimension allowance in each block, every further `H` members of a
smooth reservoir force another distinct start with `t ≤ H`.  This quotient
form is convenient for asymptotic lower bounds because it has no auxiliary
target parameter. -/
theorem smooth_reservoir_excess_div_le_short_count
    {R : Finset ℕ} {X K H Y : ℕ} (hH : 0 < H)
    (hRsegment : R ⊆ Finset.Ioc X (X + K * H))
    (hRsmooth : ∀ n ∈ R, n ∈ (Y + 1).smoothNumbers) :
    (R.card - K * (Y + 1).primesBelow.card) / H ≤
      ((Finset.Ioc X (X + K * H)).filter fun n ↦ t n ≤ H).card := by
  have havg := reservoir_card_le_rich_blocks hH hRsegment hRsmooth
  have hexcess :
      R.card - K * (Y + 1).primesBelow.card ≤
        (smoothRichBlockIndices X K H Y).card * H := by
    rw [Nat.sub_le_iff_le_add]
    simpa [Nat.add_comm, Nat.mul_comm] using havg
  exact (Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hexcess)).trans
    (smoothRichBlockIndices_card_le_short hH)

/-- Fully finite squarefree-product version of the rich-block criterion.
All analytic work in the small-values theorem can therefore be reduced to
choosing parameters which satisfy the displayed elementary inequalities. -/
theorem target_lt_short_count_of_prime_products
    {P : Finset ℕ} {k L X K H Y Q : ℕ}
    (hH : 0 < H) (hPprime : ∀ p ∈ P, p.Prime)
    (hPlo : ∀ p ∈ P, L ≤ p) (hPhi : ∀ p ∈ P, p ≤ Y)
    (hXlo : X < L ^ k) (hYhi : Y ^ k ≤ X + K * H)
    (hlarge : K * (Y + 1).primesBelow.card + Q * H < P.card.choose k) :
    Q < ((Finset.Ioc X (X + K * H)).filter fun n ↦ t n ≤ H).card := by
  let R := primeSubsetProducts P k
  have hRIcc : R ⊆ Finset.Icc (L ^ k) (Y ^ k) :=
    primeSubsetProducts_subset_Icc hPlo hPhi
  have hRsegment : R ⊆ Finset.Ioc X (X + K * H) := by
    intro n hn
    have hnI := Finset.mem_Icc.mp (hRIcc hn)
    exact Finset.mem_Ioc.mpr ⟨hXlo.trans_le hnI.1, hnI.2.trans hYhi⟩
  have hRsmooth : ∀ n ∈ R, n ∈ (Y + 1).smoothNumbers := by
    intro n hn
    have hnUp := primeSubsetProducts_subset_smoothNumbersUpTo
      hPprime hPhi (show Y ^ k ≤ Y ^ k from le_rfl) hn
    exact (Nat.mem_smoothNumbersUpTo.mp hnUp).2
  apply target_lt_short_count_of_smooth_reservoir hH hRsegment hRsmooth
  simpa [R, card_primeSubsetProducts P k hPprime] using hlarge

/-- Explicit lower bound obtained from a reservoir of products of `k`
distinct primes.  It is the parameter-free counterpart of
`target_lt_short_count_of_prime_products`. -/
theorem prime_product_excess_div_le_short_count
    {P : Finset ℕ} {k L X K H Y : ℕ}
    (hH : 0 < H) (hPprime : ∀ p ∈ P, p.Prime)
    (hPlo : ∀ p ∈ P, L ≤ p) (hPhi : ∀ p ∈ P, p ≤ Y)
    (hXlo : X < L ^ k) (hYhi : Y ^ k ≤ X + K * H) :
    (P.card.choose k - K * (Y + 1).primesBelow.card) / H ≤
      ((Finset.Ioc X (X + K * H)).filter fun n ↦ t n ≤ H).card := by
  let R := primeSubsetProducts P k
  have hRIcc : R ⊆ Finset.Icc (L ^ k) (Y ^ k) :=
    primeSubsetProducts_subset_Icc hPlo hPhi
  have hRsegment : R ⊆ Finset.Ioc X (X + K * H) := by
    intro n hn
    have hnI := Finset.mem_Icc.mp (hRIcc hn)
    exact Finset.mem_Ioc.mpr ⟨hXlo.trans_le hnI.1, hnI.2.trans hYhi⟩
  have hRsmooth : ∀ n ∈ R, n ∈ (Y + 1).smoothNumbers := by
    intro n hn
    have hnUp := primeSubsetProducts_subset_smoothNumbersUpTo
      hPprime hPhi (show Y ^ k ≤ Y ^ k from le_rfl) hn
    exact (Nat.mem_smoothNumbersUpTo.mp hnUp).2
  simpa [R, card_primeSubsetProducts P k hPprime] using
    smooth_reservoir_excess_div_le_short_count hH hRsegment hRsmooth

/-- A coarse lower bound for a binomial coefficient tailored to prime
reservoirs.  If `N` contains `m` disjoint blocks of at least `A` elements,
then the number of `m`-subsets is at least `A^m`.  The proof is numerical,
via the standard lower bound `(N+1-m)^m / m! ≤ N.choose m`. -/
theorem pow_le_choose_of_mul_add_le {A m N : ℕ} (hm : 0 < m)
    (hblocks : m * A + m ≤ N + 1) : A ^ m ≤ N.choose m := by
  have hbase : m * A ≤ N + 1 - m := by omega
  have hfac : m.factorial * A ^ m ≤ (m * A) ^ m := by
    rw [Nat.mul_pow]
    exact Nat.mul_le_mul_right (A ^ m) (Nat.factorial_le_pow m)
  have hpow : (m * A) ^ m ≤ (N + 1 - m) ^ m :=
    Nat.pow_le_pow_left hbase m
  have hquot : (A ^ m : ℚ) ≤ ((N + 1 - m : ℕ) ^ m : ℚ) / m.factorial := by
    rw [le_div_iff₀' (by positivity : (0 : ℚ) < m.factorial)]
    exact_mod_cast hfac.trans hpow
  have hchoose := Nat.pow_le_choose (α := ℚ) m N
  exact_mod_cast hquot.trans hchoose

/-- Primes in the closed numerical band `[L,Y]`. -/
def primeBand (L Y : ℕ) : Finset ℕ :=
  (Y + 1).primesBelow.filter fun p ↦ L ≤ p

lemma prime_mem_primeBand {L Y p : ℕ} (hp : p ∈ primeBand L Y) :
    p.Prime ∧ L ≤ p ∧ p ≤ Y := by
  have hp' := Finset.mem_filter.mp hp
  have hpBelow := Nat.mem_primesBelow.mp hp'.1
  exact ⟨hpBelow.2, hp'.2, by omega⟩

/-- At most `L` primes below `Y+1` are lost when the lower cutoff `L` is
imposed.  This deliberately coarse form avoids any estimate for the lower
endpoint of the band. -/
theorem primeCounting_le_primeBand_card_add (L Y : ℕ) :
    Nat.primeCounting Y ≤ (primeBand L Y).card + L := by
  let S := (Y + 1).primesBelow
  let P := S.filter fun p ↦ L ≤ p
  let Q := S.filter fun p ↦ ¬L ≤ p
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun p ↦ L ≤ p)
  have hQsub : Q ⊆ Finset.range L := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_range.mpr (Nat.lt_of_not_ge hp'.2)
  have hQcard : Q.card ≤ L := by
    simpa using Finset.card_le_card hQsub
  have hScard : S.card = Nat.primeCounting Y := by
    simpa [S] using primesBelow_succ_card_eq_primeCounting Y
  change P.card + Q.card = S.card at hsplit
  change Nat.primeCounting Y ≤ P.card + L
  omega

theorem le_primeBand_card_of_add_le_primeCounting {A L Y : ℕ}
    (h : L + A ≤ Nat.primeCounting Y) : A ≤ (primeBand L Y).card := by
  have hband := primeCounting_le_primeBand_card_add L Y
  omega

/-- A deliberately coarse lower Chebyshev bound.  It is enough for the
explicit prime-product reservoir and follows directly from Mathlib's
`Chebyshev.pi_ge`; no prime number theorem or smooth-number asymptotic is
used. -/
theorem eventually_self_div_four_log_le_primeCounting :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) / (4 * Real.log n) ≤ Nat.primeCounting n := by
  have hlogR := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 8 by norm_num)
  have hshift : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hlogN := hshift.eventually hlogR
  filter_upwards [hlogN, Filter.eventually_ge_atTop 2] with n hnlog hn2
  have hnpos : (0 : ℝ) < n := by positivity
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hlogsmall : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) / 4 := by
    have habslog : |Real.log ((n : ℝ) + 1)| = Real.log ((n : ℝ) + 1) := by
      rw [abs_of_nonneg (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ n + 1 by omega)))]
    have hnlog' : |Real.log ((n : ℝ) + 1)| ≤ (1 / 8 : ℝ) * |(n : ℝ) + 1| := by
      simpa [Real.norm_eq_abs] using hnlog
    rw [habslog, abs_of_pos hn1pos] at hnlog'
    nlinarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hnum : (n : ℝ) / 4 ≤
      (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) := by
    nlinarith
  calc
    (n : ℝ) / (4 * Real.log n) = ((n : ℝ) / 4) / Real.log n := by ring
    _ ≤ ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) /
        Real.log n := div_le_div_of_nonneg_right hnum hlogpos.le
    _ ≤ Nat.primeCounting n := by
      simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
        Chebyshev.pi_ge n

/-- A compact finite production theorem: a sufficiently populated prime
band supplies at least `A^k` squarefree products, and any requested target
whose block cost is below this reservoir is attained by distinct starts
with short square witnesses. -/
theorem target_lt_short_count_of_prime_band
    {L Y k A X K H Q : ℕ} (hk : 0 < k) (hH : 0 < H)
    (hband : k * A + k ≤ (primeBand L Y).card + 1)
    (hXlo : X < L ^ k) (hYhi : Y ^ k ≤ X + K * H)
    (hbudget : K * (Y + 1).primesBelow.card + Q * H < A ^ k) :
    Q < ((Finset.Ioc X (X + K * H)).filter fun n ↦ t n ≤ H).card := by
  apply target_lt_short_count_of_prime_products (P := primeBand L Y)
    hH (fun p hp ↦ (prime_mem_primeBand hp).1)
    (fun p hp ↦ (prime_mem_primeBand hp).2.1)
    (fun p hp ↦ (prime_mem_primeBand hp).2.2) hXlo hYhi
  exact hbudget.trans_le (pow_le_choose_of_mul_add_le hk hband)

/-! ### An explicit prime-product family for BPZ's many-small-values result -/

/-- Prime cutoff in the elementary reservoir, parametrized by `m`. -/
def smallValueY (m : ℕ) : ℕ := m ^ m

/-- Lower edge of the prime band.  Its logarithm differs from that of
`smallValueY m` by only `O(log m)`. -/
def smallValueL (m : ℕ) : ℕ := m ^ (m - 7)

/-- The block size used in the binomial lower bound. -/
def smallValueA (m : ℕ) : ℕ := m ^ (m - 6)

lemma smallValueY_tendsto_atTop :
    Filter.Tendsto smallValueY Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono' Filter.atTop
    (f₁ := fun m : ℕ ↦ m) (f₂ := smallValueY)
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact Nat.le_pow hm
  · exact Filter.tendsto_id

/-- Chebyshev's estimate supplies enough primes in the explicit band for
the binomial reservoir. -/
theorem eventually_smallValue_primeBand_supply :
    ∀ᶠ m : ℕ in Filter.atTop,
      m * smallValueA m + m ≤
        (primeBand (smallValueL m) (smallValueY m)).card + 1 := by
  have hpi := smallValueY_tendsto_atTop.eventually
    eventually_self_div_four_log_le_primeCounting
  filter_upwards [hpi, Filter.eventually_ge_atTop 10] with m hpi hm
  have hmpos : 0 < m := by omega
  have hm1 : 1 < m := by omega
  have hpowmono (a b : ℕ) (hab : a ≤ b) : m ^ a ≤ m ^ b :=
    Nat.pow_le_pow_right hmpos hab
  have hLle : smallValueL m ≤ m ^ (m - 5) := by
    exact hpowmono _ _ (by omega)
  have hmA : m * smallValueA m = m ^ (m - 5) := by
    rw [smallValueA, ← pow_succ']
    congr 1
    omega
  have hmle : m ≤ m ^ (m - 5) := by
    apply Nat.le_pow
    omega
  have hsum : smallValueL m + (m * smallValueA m + m) ≤ m ^ (m - 3) := by
    have hthree :
        smallValueL m + (m * smallValueA m + m) ≤
          3 * m ^ (m - 5) := by
      rw [hmA]
      omega
    have hpowstep : 3 * m ^ (m - 5) ≤ m ^ (m - 3) := by
      have h3m : 3 ≤ m ^ 2 := by nlinarith
      have hmul := Nat.mul_le_mul_right (m ^ (m - 5)) h3m
      calc
        3 * m ^ (m - 5) ≤ m ^ 2 * m ^ (m - 5) := hmul
        _ = m ^ (m - 3) := by
          rw [← pow_add]
          congr 1
          omega
    exact hthree.trans hpowstep
  have hlogm : Real.log (m : ℝ) ≤ m := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by positivity)
    linarith
  have hlogY : Real.log (smallValueY m : ℝ) =
      (m : ℝ) * Real.log m := by
    rw [smallValueY, Nat.cast_pow, Real.log_pow]
  have hlogYpos : 0 < Real.log (smallValueY m : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < m ^ m by exact one_lt_pow₀ hm1 hmpos.ne')
  have hden : 4 * Real.log (smallValueY m : ℝ) ≤ (m : ℝ) ^ 3 := by
    rw [hlogY]
    have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (show 4 ≤ m by omega)
    calc
      4 * ((m : ℝ) * Real.log m) ≤ 4 * ((m : ℝ) * m) := by
        gcongr
      _ ≤ (m : ℝ) ^ 3 := by nlinarith
  have hYsplit : m ^ (m - 3) * m ^ 3 = smallValueY m := by
    rw [smallValueY, ← pow_add]
    congr 1
    omega
  have hsumR :
      ((smallValueL m + (m * smallValueA m + m) : ℕ) : ℝ) ≤
        (smallValueY m : ℝ) / ((m : ℝ) ^ 3) := by
    have hcast :
        ((smallValueL m + (m * smallValueA m + m) : ℕ) : ℝ) ≤
          (m ^ (m - 3) : ℕ) := by exact_mod_cast hsum
    calc
      ((smallValueL m + (m * smallValueA m + m) : ℕ) : ℝ) ≤
          (m ^ (m - 3) : ℕ) := hcast
      _ = (smallValueY m : ℝ) / ((m : ℝ) ^ 3) := by
        rw [eq_div_iff (by positivity : (m : ℝ) ^ 3 ≠ 0)]
        exact_mod_cast hYsplit
  have hdiv : (smallValueY m : ℝ) / ((m : ℝ) ^ 3) ≤
      (smallValueY m : ℝ) / (4 * Real.log (smallValueY m : ℝ)) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hnat : smallValueL m + (m * smallValueA m + m) ≤
      Nat.primeCounting (smallValueY m) := by
    exact_mod_cast hsumR.trans (hdiv.trans hpi)
  have hband := le_primeBand_card_of_add_le_primeCounting
    (A := m * smallValueA m + m)
    (L := smallValueL m) (Y := smallValueY m) hnat
  omega

lemma primesBelow_succ_card_le_self (Y : ℕ) :
    (Y + 1).primesBelow.card ≤ Y := by
  have hsub : (Y + 1).primesBelow ⊆ Finset.Icc 1 Y := by
    intro p hp
    have hp' := Nat.mem_primesBelow.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, by omega⟩
  simpa using Finset.card_le_card hsub

/-- Length of the short witnesses in the elementary many-small-values
construction. -/
def smallValueH (m : ℕ) : ℕ := smallValueY m ^ 10

/-- Number of consecutive `smallValueH m` blocks used by the construction. -/
def smallValueK (m : ℕ) : ℕ := smallValueY m ^ (m - 10) + 1

/-- Left endpoint, one below the least prime-product in the reservoir. -/
def smallValueX (m : ℕ) : ℕ := smallValueL m ^ m - 1

/-- Right endpoint of the blocks used in the construction. -/
def smallValueEnd (m : ℕ) : ℕ :=
  smallValueX m + smallValueK m * smallValueH m

/-- Explicit target count in the elementary many-small-values construction. -/
def smallValueQ (m : ℕ) : ℕ := smallValueY m ^ (m - 17)

/-- The actual finite set of starts produced at parameter `m`. -/
def manySmallStarts (m : ℕ) : Finset ℕ :=
  (Finset.Ioc (smallValueX m) (smallValueEnd m)).filter
    fun n ↦ t n ≤ smallValueH m

/-- Exact finite output of the prime-product construction.  This is the
arithmetic core of the `x^{1-o(1)}` assertion and is independent of any
smooth-number asymptotic. -/
theorem eventually_smallValueQ_lt_manySmallStarts_card :
    ∀ᶠ m : ℕ in Filter.atTop,
      smallValueQ m < (manySmallStarts m).card := by
  filter_upwards [eventually_smallValue_primeBand_supply,
    Filter.eventually_ge_atTop 18] with m hband hm
  let Y := smallValueY m
  let L := smallValueL m
  let A := smallValueA m
  let H := smallValueH m
  let K := smallValueK m
  let X := smallValueX m
  let Q := smallValueQ m
  have hmpos : 0 < m := by omega
  have hYpos : 0 < Y := by simp [Y, smallValueY, hmpos]
  have hY4 : 4 ≤ Y := by
    change 4 ≤ m ^ m
    exact (show 4 ≤ m by omega).trans (Nat.le_pow hmpos)
  have hHpos : 0 < H := by
    change 0 < Y ^ 10
    positivity
  have hLpowpos : 0 < L ^ m := by
    have hLpos : 0 < L := by simp [L, smallValueL, hmpos]
    positivity
  have hXlo : X < L ^ m := by
    change L ^ m - 1 < L ^ m
    omega
  have hYfactor : Y ^ (m - 10) * Y ^ 10 = Y ^ m :=
    Nat.pow_sub_mul_pow Y (by omega)
  have hYhi : Y ^ m ≤ X + K * H := by
    change Y ^ m ≤ X + (Y ^ (m - 10) + 1) * Y ^ 10
    calc
      Y ^ m = Y ^ (m - 10) * Y ^ 10 := hYfactor.symm
      _ ≤ (Y ^ (m - 10) + 1) * Y ^ 10 :=
        Nat.mul_le_mul_right (Y ^ 10) (Nat.le_add_right _ _)
      _ ≤ X + (Y ^ (m - 10) + 1) * Y ^ 10 := Nat.le_add_left _ _
  have hpi : (Y + 1).primesBelow.card ≤ Y :=
    primesBelow_succ_card_le_self Y
  have hKpi : K * (Y + 1).primesBelow.card ≤ Y ^ (m - 9) + Y := by
    calc
      K * (Y + 1).primesBelow.card ≤ K * Y := Nat.mul_le_mul_left K hpi
      _ = (Y ^ (m - 10) + 1) * Y := by rfl
      _ = Y ^ (m - 9) + Y := by
        rw [add_mul, one_mul]
        congr 1
        rw [← pow_succ]
        congr 1
        omega
  have hQH : Q * H = Y ^ (m - 7) := by
    dsimp [Q, H, smallValueQ, smallValueH]
    rw [← pow_add]
    congr 1
    omega
  have hpowmono (a b : ℕ) (hab : a ≤ b) : Y ^ a ≤ Y ^ b :=
    Nat.pow_le_pow_right hYpos hab
  have hsmall1 : Y ^ (m - 9) ≤ Y ^ (m - 7) :=
    hpowmono _ _ (by omega)
  have hsmallY : Y ≤ Y ^ (m - 7) := by
    exact Nat.le_pow (by omega)
  have hthree : Y ^ (m - 9) + Y + Y ^ (m - 7) ≤
      3 * Y ^ (m - 7) := by omega
  have hstep : 3 * Y ^ (m - 7) < Y ^ (m - 6) := by
    have hmul : 3 * Y ^ (m - 7) < Y * Y ^ (m - 7) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    calc
      3 * Y ^ (m - 7) < Y * Y ^ (m - 7) := hmul
      _ = Y ^ (m - 6) := by
        rw [← pow_succ']
        congr 1
        omega
  have hbudget : K * (Y + 1).primesBelow.card + Q * H < A ^ m := by
    calc
      K * (Y + 1).primesBelow.card + Q * H ≤
          (Y ^ (m - 9) + Y) + Y ^ (m - 7) := by omega
      _ ≤ 3 * Y ^ (m - 7) := hthree
      _ < Y ^ (m - 6) := hstep
      _ = A ^ m := by
        dsimp [Y, A]
        rw [smallValueY, smallValueA, ← pow_mul, ← pow_mul]
        rw [Nat.mul_comm]
  have hout := target_lt_short_count_of_prime_band
    (L := L) (Y := Y) (k := m) (A := A) (X := X)
    (K := K) (H := H) (Q := Q) hmpos hHpos hband hXlo hYhi hbudget
  simpa [manySmallStarts, smallValueEnd, Y, L, A, H, K, X, Q] using hout

/-- The ambient interval in the explicit construction has the same
logarithmic size as `Y^m`, while its selected subset is bounded below by
`Y^(m-17)`. -/
theorem eventually_manySmallStarts_card_bounds :
    ∀ᶠ m : ℕ in Filter.atTop,
      smallValueQ m < (manySmallStarts m).card ∧
      (manySmallStarts m).card ≤ smallValueEnd m ∧
      smallValueEnd m ≤ 3 * smallValueY m ^ m := by
  filter_upwards [eventually_smallValueQ_lt_manySmallStarts_card,
    Filter.eventually_ge_atTop 18] with m hQ hm
  let Y := smallValueY m
  let L := smallValueL m
  have hmpos : 0 < m := by omega
  have hYpos : 0 < Y := by simp [Y, smallValueY, hmpos]
  have hLleY : L ≤ Y := by
    dsimp [L, Y, smallValueL, smallValueY]
    exact Nat.pow_le_pow_right hmpos (by omega)
  have hXle : smallValueX m ≤ Y ^ m := by
    calc
      smallValueX m = L ^ m - 1 := by rfl
      _ ≤ L ^ m := Nat.sub_le _ _
      _ ≤ Y ^ m := Nat.pow_le_pow_left hLleY m
  have hKH : smallValueK m * smallValueH m =
      Y ^ m + Y ^ 10 := by
    change (Y ^ (m - 10) + 1) * Y ^ 10 = Y ^ m + Y ^ 10
    rw [add_mul, one_mul, Nat.pow_sub_mul_pow Y (by omega)]
  have hHle : Y ^ 10 ≤ Y ^ m :=
    Nat.pow_le_pow_right hYpos (by omega)
  have hend : smallValueEnd m ≤ 3 * Y ^ m := by
    rw [smallValueEnd, hKH]
    omega
  have hcard : (manySmallStarts m).card ≤ smallValueEnd m := by
    calc
      (manySmallStarts m).card ≤
          (Finset.Ioc (smallValueX m) (smallValueEnd m)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ smallValueEnd m := by simp
  exact ⟨hQ, hcard, by simpa [Y] using hend⟩

/-- Literal `x^{1-o(1)}` formulation for the explicit family: the logarithm
of the number of produced starts is asymptotic to the logarithm of the
ambient endpoint. -/
theorem manySmallStarts_log_card_ratio_tendsto_one :
    Filter.Tendsto
      (fun m : ℕ ↦ Real.log ((manySmallStarts m).card : ℝ) /
        Real.log (smallValueEnd m : ℝ))
      Filter.atTop (nhds 1) := by
  have hden : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hseventeen : Filter.Tendsto
      (fun m : ℕ ↦ (17 : ℝ) / ((m : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hmain := tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1
  have hloReal : Filter.Tendsto
      (fun m : ℕ ↦ ((m : ℝ) - 17) / ((m : ℝ) + 1))
      Filter.atTop (nhds 1) := by
    convert hmain.sub hseventeen using 1 <;> simp [sub_div]
  have hlo : Filter.Tendsto
      (fun m : ℕ ↦ ((m - 17 : ℕ) : ℝ) / ((m : ℝ) + 1))
      Filter.atTop (nhds 1) := by
    apply hloReal.congr'
    filter_upwards [Filter.eventually_ge_atTop 17] with m hm
    rw [Nat.cast_sub (by omega : 17 ≤ m)]
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_manySmallStarts_card_bounds,
      Filter.eventually_ge_atTop 18] with m hb hm
    let Y := smallValueY m
    have hmpos : 0 < m := by omega
    have hY4 : 4 ≤ Y := by
      change 4 ≤ m ^ m
      exact (show 4 ≤ m by omega).trans (Nat.le_pow hmpos)
    have hQpos : 0 < smallValueQ m := by
      simp [smallValueQ, Y, smallValueY, hmpos]
    have hcardpos : 0 < (manySmallStarts m).card := hQpos.trans hb.1
    have hendpos : 0 < smallValueEnd m := hcardpos.trans_le hb.2.1
    have hcard2 : 2 ≤ (manySmallStarts m).card := by omega
    have hend2 : 2 ≤ smallValueEnd m := hcard2.trans hb.2.1
    have hlogendpos : 0 < Real.log (smallValueEnd m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < smallValueEnd m by omega))
    have hlogYpos : 0 < Real.log (Y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
    have hlogQ : Real.log (smallValueQ m : ℝ) =
        ((m - 17 : ℕ) : ℝ) * Real.log (Y : ℝ) := by
      change Real.log ((Y ^ (m - 17) : ℕ) : ℝ) = _
      rw [Nat.cast_pow, Real.log_pow]
    have hlogQle : Real.log (smallValueQ m : ℝ) ≤
        Real.log ((manySmallStarts m).card : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < smallValueQ m
        exact_mod_cast hQpos
      · show (0 : ℝ) < (manySmallStarts m).card
        exact_mod_cast hcardpos
      · exact_mod_cast hb.1.le
    have hlogY3 : Real.log (3 : ℝ) ≤ Real.log (Y : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · norm_num
      · show (0 : ℝ) < Y
        exact_mod_cast hY4.trans' (by norm_num : 0 < 4)
      · exact_mod_cast (show 3 ≤ Y by omega)
    have hlogEndUpper : Real.log (smallValueEnd m : ℝ) ≤
        ((m : ℝ) + 1) * Real.log (Y : ℝ) := by
      have hlogmono : Real.log (smallValueEnd m : ℝ) ≤
          Real.log ((3 * Y ^ m : ℕ) : ℝ) := by
        apply Real.strictMonoOn_log.monotoneOn
        · show (0 : ℝ) < smallValueEnd m
          exact_mod_cast hendpos
        · show (0 : ℝ) < (3 * Y ^ m : ℕ)
          exact_mod_cast Nat.mul_pos (by norm_num) (pow_pos (by omega) m)
        · exact_mod_cast hb.2.2
      have hrewrite : Real.log ((3 * Y ^ m : ℕ) : ℝ) =
          Real.log 3 + (m : ℝ) * Real.log (Y : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
          Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      rw [hrewrite] at hlogmono
      nlinarith
    have hnumNonneg : 0 ≤
        ((m - 17 : ℕ) : ℝ) * Real.log (Y : ℝ) := by positivity
    calc
      ((m - 17 : ℕ) : ℝ) / ((m : ℝ) + 1) =
          (((m - 17 : ℕ) : ℝ) * Real.log (Y : ℝ)) /
            (((m : ℝ) + 1) * Real.log (Y : ℝ)) := by
              field_simp
      _ ≤ (((m - 17 : ℕ) : ℝ) * Real.log (Y : ℝ)) /
          Real.log (smallValueEnd m : ℝ) :=
        div_le_div_of_nonneg_left hnumNonneg hlogendpos hlogEndUpper
      _ ≤ Real.log ((manySmallStarts m).card : ℝ) /
          Real.log (smallValueEnd m : ℝ) := by
        apply div_le_div_of_nonneg_right _ hlogendpos.le
        simpa [hlogQ] using hlogQle
  · filter_upwards [eventually_manySmallStarts_card_bounds,
      Filter.eventually_ge_atTop 18] with m hb hm
    have hQpos : 0 < smallValueQ m := by
      simp [smallValueQ, smallValueY, show 0 < m by omega]
    have hcardpos : 0 < (manySmallStarts m).card := hQpos.trans hb.1
    have hendpos : 0 < smallValueEnd m := hcardpos.trans_le hb.2.1
    have hlogendpos : 0 < Real.log (smallValueEnd m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < smallValueEnd m by omega))
    have hlogle : Real.log ((manySmallStarts m).card : ℝ) ≤
        Real.log (smallValueEnd m : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · show (0 : ℝ) < (manySmallStarts m).card
        exact_mod_cast hcardpos
      · show (0 : ℝ) < smallValueEnd m
        exact_mod_cast hendpos
      · exact_mod_cast hb.2.1
    exact (div_le_one hlogendpos).mpr hlogle

/-- Every start in the explicit family has the subexponential witness bound
claimed in the coarse form of BPZ Theorem 1.2.  The numerical constant `20`
is inessential; retaining one explicit constant makes the `O`-statement
fully precise. -/
theorem eventually_manySmallStarts_witness_bound :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ n ∈ manySmallStarts m,
      (t n : ℝ) ≤ Real.exp
        (20 * Real.sqrt (Real.log n * Real.log (Real.log n))) := by
  filter_upwards [Filter.eventually_ge_atTop 18] with m hm
  intro n hn
  let Y := smallValueY m
  let L := smallValueL m
  have hmpos : 0 < m := by omega
  have hmRpos : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm1 : 1 < m := by omega
  have hlogmpos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm1)
  have hlogmone : (1 : ℝ) < Real.log (m : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hmRpos]
    have hm18R : (18 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.exp_one_lt_d9]
  have hn' := Finset.mem_filter.mp hn
  have hnI := Finset.mem_Ioc.mp hn'.1
  have htH : t n ≤ smallValueH m := hn'.2
  have hLpos : 0 < L := by simp [L, smallValueL, hmpos]
  have hLpowpos : 0 < L ^ m := pow_pos hLpos m
  have hnLower : L ^ m ≤ n := by
    have hnlo := hnI.1
    change L ^ m - 1 < n at hnlo
    omega
  have hnpos : 0 < n := hLpowpos.trans_le hnLower
  have hlogL : Real.log (L : ℝ) =
      ((m - 7 : ℕ) : ℝ) * Real.log (m : ℝ) := by
    change Real.log ((m ^ (m - 7) : ℕ) : ℝ) = _
    rw [Nat.cast_pow, Real.log_pow]
  have hlogLpow : Real.log ((L ^ m : ℕ) : ℝ) =
      (m : ℝ) * ((m - 7 : ℕ) : ℝ) * Real.log (m : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow, hlogL]
    ring
  have hlogLower : Real.log ((L ^ m : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < (L ^ m : ℕ) by exact_mod_cast hLpowpos)
    · simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < n by exact_mod_cast hnpos)
    · exact_mod_cast hnLower
  have hcoef : (m : ℝ) ^ 2 / 2 ≤
      (m : ℝ) * ((m - 7 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 7 ≤ m)]
    have hm14R : (14 : ℝ) ≤ m := by
      exact_mod_cast (show 14 ≤ m by omega)
    have hgap : (0 : ℝ) ≤ (m : ℝ) - 14 := by linarith
    nlinarith [mul_nonneg hmRpos.le hgap]
  have hlognLower : ((m : ℝ) ^ 2 / 2) * Real.log (m : ℝ) ≤
      Real.log (n : ℝ) := by
    calc
      ((m : ℝ) ^ 2 / 2) * Real.log (m : ℝ) ≤
          ((m : ℝ) * ((m - 7 : ℕ) : ℝ)) * Real.log (m : ℝ) := by
        gcongr
      _ = Real.log ((L ^ m : ℕ) : ℝ) := hlogLpow.symm
      _ ≤ Real.log (n : ℝ) := hlogLower
  have hlognpos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by
      have : 1 < L ^ m := one_lt_pow₀ (by
        dsimp [L, smallValueL]
        exact one_lt_pow₀ hm1 (by omega)) (by omega)
      omega)
  have hm_le_logn : (m : ℝ) ≤ Real.log (n : ℝ) := by
    calc
      (m : ℝ) ≤ ((m : ℝ) ^ 2 / 2) * Real.log (m : ℝ) := by
        have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
        nlinarith
      _ ≤ Real.log (n : ℝ) := hlognLower
  have hloglog : Real.log (m : ℝ) ≤ Real.log (Real.log (n : ℝ)) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact hmRpos
    · exact hlognpos
    · exact hm_le_logn
  have hlognOne : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    exact hmone.trans hm_le_logn
  have hprod : (((m : ℝ) * Real.log (m : ℝ)) ^ 2) / 4 ≤
      Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
    have hfirst :
        (((m : ℝ) ^ 2 / 2) * Real.log (m : ℝ)) * Real.log (m : ℝ) ≤
          Real.log (n : ℝ) * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_right hlognLower hlogmpos.le
    have hsecond : Real.log (n : ℝ) * Real.log (m : ℝ) ≤
        Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hloglog hlognpos.le
    calc
      (((m : ℝ) * Real.log (m : ℝ)) ^ 2) / 4 ≤
          (((m : ℝ) ^ 2 / 2) * Real.log (m : ℝ)) * Real.log (m : ℝ) := by
        nlinarith [sq_nonneg (Real.log (m : ℝ))]
      _ ≤ Real.log (n : ℝ) * Real.log (m : ℝ) := hfirst
      _ ≤ Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) := hsecond
  have hsqrt : ((m : ℝ) * Real.log (m : ℝ)) / 2 ≤
      Real.sqrt (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))) := by
    apply (Real.le_sqrt (by positivity)
      (mul_nonneg hlognpos.le (Real.log_nonneg hlognOne))).2
    nlinarith
  have hlogH : Real.log (smallValueH m : ℝ) =
      10 * (m : ℝ) * Real.log (m : ℝ) := by
    rw [smallValueH, smallValueY, Nat.cast_pow, Real.log_pow,
      Nat.cast_pow, Real.log_pow]
    ring
  have hlogHle : Real.log (smallValueH m : ℝ) ≤
      20 * Real.sqrt (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))) := by
    rw [hlogH]
    nlinarith
  calc
    (t n : ℝ) ≤ (smallValueH m : ℝ) := by exact_mod_cast htH
    _ = Real.exp (Real.log (smallValueH m : ℝ)) := by
      symm
      apply Real.exp_log
      exact_mod_cast (show 0 < smallValueH m by
        simp [smallValueH, smallValueY, hmpos])
    _ ≤ Real.exp
        (20 * Real.sqrt (Real.log n * Real.log (Real.log n))) :=
      Real.exp_le_exp.mpr hlogHle

lemma smallValueEnd_tendsto_atTop :
    Filter.Tendsto smallValueEnd Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono' Filter.atTop
    (f₁ := smallValueY) (f₂ := smallValueEnd)
    (h₁ := smallValueY_tendsto_atTop)
  filter_upwards [Filter.eventually_ge_atTop 18] with m hm
  let Y := smallValueY m
  have hYpos : 0 < Y := by
    simp [Y, smallValueY, show 0 < m by omega]
  have hpow : Y ≤ Y ^ m := Nat.le_pow (by omega)
  have hfactor : Y ^ (m - 10) * Y ^ 10 = Y ^ m :=
    Nat.pow_sub_mul_pow Y (by omega)
  change Y ≤ smallValueX m +
    (Y ^ (m - 10) + 1) * Y ^ 10
  calc
    Y ≤ Y ^ m := hpow
    _ = Y ^ (m - 10) * Y ^ 10 := hfactor.symm
    _ ≤ (Y ^ (m - 10) + 1) * Y ^ 10 :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    _ ≤ smallValueX m + (Y ^ (m - 10) + 1) * Y ^ 10 :=
      Nat.le_add_left _ _

/-- A monotone-size envelope for the endpoint of the elementary
construction.  Unlike `smallValueEnd`, its closed formula is convenient
for interpolating between consecutive parameter values. -/
def smallValueCeiling (m : ℕ) : ℕ :=
  3 * smallValueY m ^ m

lemma smallValueCeiling_tendsto_atTop :
    Filter.Tendsto smallValueCeiling Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono' Filter.atTop
    (f₁ := smallValueY) (f₂ := smallValueCeiling)
    (h₁ := smallValueY_tendsto_atTop)
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hYpos : 0 < smallValueY m := by
    simp [smallValueY, show 0 < m by omega]
  calc
    smallValueY m ≤ smallValueY m ^ m := Nat.le_pow (by omega)
    _ ≤ 3 * smallValueY m ^ m := by omega

lemma exists_smallValueCeiling_gt (x : ℕ) :
    ∃ m : ℕ, x < smallValueCeiling m := by
  have h : ∀ᶠ m : ℕ in Filter.atTop, x + 1 ≤ smallValueCeiling m :=
    (Filter.tendsto_atTop.1 smallValueCeiling_tendsto_atTop) (x + 1)
  have h' : ∀ᶠ m : ℕ in Filter.atTop, x < smallValueCeiling m := by
    filter_upwards [h] with m hm
    omega
  exact h'.exists

/-- Least parameter whose ceiling is strictly beyond `x`. -/
noncomputable def smallValueIndex (x : ℕ) : ℕ :=
  Nat.find (exists_smallValueCeiling_gt x)

lemma smallValueIndex_spec (x : ℕ) :
    x < smallValueCeiling (smallValueIndex x) :=
  Nat.find_spec (exists_smallValueCeiling_gt x)

lemma smallValueIndex_tendsto_atTop :
    Filter.Tendsto smallValueIndex Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro A
  refine Filter.eventually_atTop.2
    ⟨∑ k ∈ Finset.range A, smallValueCeiling k, ?_⟩
  intro x hx
  by_contra hidx
  have hlt : smallValueIndex x < A := Nat.lt_of_not_ge hidx
  have hmem : smallValueIndex x ∈ Finset.range A := Finset.mem_range.mpr hlt
  have hsingle : smallValueCeiling (smallValueIndex x) ≤
      ∑ k ∈ Finset.range A, smallValueCeiling k := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hmem
  have hspec := smallValueIndex_spec x
  omega

/-- Parameter immediately below the first ceiling which exceeds `x`. -/
def smallValueFloorIndex (x : ℕ) : ℕ :=
  smallValueIndex x - 1

lemma smallValueFloorIndex_tendsto_atTop :
    Filter.Tendsto smallValueFloorIndex Filter.atTop Filter.atTop := by
  exact (Filter.tendsto_sub_atTop_nat 1).comp smallValueIndex_tendsto_atTop

lemma eventually_smallValueFloorIndex_brackets :
    ∀ᶠ x : ℕ in Filter.atTop,
      smallValueCeiling (smallValueFloorIndex x) ≤ x ∧
      x < smallValueCeiling (smallValueFloorIndex x + 1) := by
  have hidx : ∀ᶠ x : ℕ in Filter.atTop, 0 < smallValueIndex x :=
    smallValueIndex_tendsto_atTop.eventually (Filter.eventually_gt_atTop 0)
  filter_upwards [hidx] with x hidx
  let e := exists_smallValueCeiling_gt x
  have hpred : smallValueIndex x - 1 < smallValueIndex x := by omega
  have hnot : ¬x < smallValueCeiling (smallValueIndex x - 1) := by
    simpa [smallValueIndex, e] using Nat.find_min e hpred
  have hsucc : smallValueIndex x - 1 + 1 = smallValueIndex x := by omega
  exact ⟨Nat.le_of_not_gt hnot, by
    rw [smallValueFloorIndex, hsucc]
    exact smallValueIndex_spec x⟩

/-- All positive starts up to `x` which satisfy the explicit absolute
subexponential witness bound used in BPZ Theorem 1.2. -/
def manySmallUpTo (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦
    (t n : ℝ) ≤ Real.exp
      (20 * Real.sqrt (Real.log n * Real.log (Real.log n)))

lemma manySmallUpTo_mono {x z : ℕ} (hxz : x ≤ z) :
    manySmallUpTo x ⊆ manySmallUpTo z := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  exact ⟨Finset.Icc_subset_Icc_right hxz hn'.1, hn'.2⟩

lemma eventually_manySmallStarts_subset_manySmallUpToCeiling :
    ∀ᶠ m : ℕ in Filter.atTop,
      manySmallStarts m ⊆ manySmallUpTo (smallValueCeiling m) := by
  filter_upwards [eventually_manySmallStarts_card_bounds,
    eventually_manySmallStarts_witness_bound,
    Filter.eventually_ge_atTop 18] with m hb hw hm
  intro n hn
  have hnI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
  have hnpos : 0 < n := by omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hnpos, ?_⟩, hw n hn⟩
  exact hnI.2.trans (hb.2.2.trans_eq rfl)

lemma eventually_smallValueQ_floor_lt_manySmallUpTo_card :
    ∀ᶠ x : ℕ in Filter.atTop,
      smallValueQ (smallValueFloorIndex x) < (manySmallUpTo x).card := by
  have hparam : ∀ᶠ x : ℕ in Filter.atTop,
      smallValueQ (smallValueFloorIndex x) <
          (manySmallStarts (smallValueFloorIndex x)).card ∧
        manySmallStarts (smallValueFloorIndex x) ⊆
          manySmallUpTo (smallValueCeiling (smallValueFloorIndex x)) :=
    smallValueFloorIndex_tendsto_atTop.eventually
      (eventually_smallValueQ_lt_manySmallStarts_card.and
        eventually_manySmallStarts_subset_manySmallUpToCeiling)
  filter_upwards [eventually_smallValueFloorIndex_brackets, hparam] with x hx hp
  have hmono := manySmallUpTo_mono hx.1
  have hsub : manySmallStarts (smallValueFloorIndex x) ⊆ manySmallUpTo x :=
    hp.2.trans hmono
  exact hp.1.trans_le (Finset.card_le_card hsub)

lemma log_nat_succ_div_log_tendsto_one :
    Filter.Tendsto
      (fun m : ℕ ↦ Real.log ((m + 1 : ℕ) : ℝ) / Real.log (m : ℝ))
      Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun m : ℕ ↦ Real.log (m : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Filter.Tendsto
      (fun m : ℕ ↦
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          Real.log (m : ℝ))
      Filter.atTop (nhds 0) :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Real.tendsto_log_nat_add_one_sub_log.div_atTop hlog
  have hone : Filter.Tendsto
      (fun m : ℕ ↦ (1 : ℝ) +
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          Real.log (m : ℝ))
      Filter.atTop (nhds 1) :=
    by
      simpa using
        ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ))
          Filter.atTop (nhds 1)).add hzero)
  apply hone.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with m hm
  have hne : Real.log (m : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < m by omega))).ne'
  field_simp [hne]
  ring

lemma log_nat_div_log_succ_tendsto_one :
    Filter.Tendsto
      (fun m : ℕ ↦ Real.log (m : ℝ) / Real.log ((m + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
  have hinv := log_nat_succ_div_log_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa [inv_div] using hinv

lemma smallValue_log_reservoir_ratio_tendsto_one :
    Filter.Tendsto
      (fun m : ℕ ↦ Real.log (smallValueQ m : ℝ) /
        Real.log (smallValueCeiling (m + 1) : ℝ))
      Filter.atTop (nhds 1) := by
  have hfirst : Filter.Tendsto
      (fun m : ℕ ↦ (m : ℝ) / ((m : ℝ) + 1))
      Filter.atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1
  have hden : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hseventeen : Filter.Tendsto
      (fun m : ℕ ↦ (17 : ℝ) / ((m : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hmain := tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1
  have hsecondReal : Filter.Tendsto
      (fun m : ℕ ↦ ((m : ℝ) - 17) / ((m : ℝ) + 1))
      Filter.atTop (nhds 1) := by
    convert hmain.sub hseventeen using 1 <;> simp [sub_div]
  have hsecond : Filter.Tendsto
      (fun m : ℕ ↦ ((m - 17 : ℕ) : ℝ) / ((m : ℝ) + 1))
      Filter.atTop (nhds 1) := by
    apply hsecondReal.congr'
    filter_upwards [Filter.eventually_ge_atTop 17] with m hm
    rw [Nat.cast_sub (by omega : 17 ≤ m)]
    norm_num
  have hADprod := hfirst.mul (hsecond.mul log_nat_div_log_succ_tendsto_one)
  have hADprod' : Filter.Tendsto
      (fun m : ℕ ↦ (m : ℝ) / ((m : ℝ) + 1) *
        (((m - 17 : ℕ) : ℝ) / ((m : ℝ) + 1) *
          (Real.log (m : ℝ) / Real.log ((m + 1 : ℕ) : ℝ))))
      Filter.atTop (nhds 1) := by
    simpa using hADprod
  have hAD : Filter.Tendsto
      (fun m : ℕ ↦
        ((m : ℝ) * ((m - 17 : ℕ) : ℝ) * Real.log (m : ℝ)) /
          ((((m + 1 : ℕ) : ℝ) ^ 2) * Real.log ((m + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 1) := by
    apply hADprod'.congr'
    filter_upwards [Filter.eventually_ge_atTop 18] with m hm
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hlogm : Real.log (m : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < m by omega))).ne'
    have hlogs : Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))).ne'
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp [hm1, hlogm, hlogs]
  have hlogSucc : Filter.Tendsto
      (fun m : ℕ ↦ Real.log ((m + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  have hD : Filter.Tendsto
      (fun m : ℕ ↦ (((m + 1 : ℕ) : ℝ) ^ 2) *
        Real.log ((m + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop ?_ hlogSucc
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hlognonneg : 0 ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega))
    have hbase : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ m + 1 by omega)
    have hsq : (1 : ℝ) ≤ (((m + 1 : ℕ) : ℝ) ^ 2) := by nlinarith
    nlinarith
  have hcorr : Filter.Tendsto
      (fun m : ℕ ↦ Real.log 3 /
        ((((m + 1 : ℕ) : ℝ) ^ 2) * Real.log ((m + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hD
  have hCoverD : Filter.Tendsto
      (fun m : ℕ ↦
        (Real.log 3 + (((m + 1 : ℕ) : ℝ) ^ 2) *
            Real.log ((m + 1 : ℕ) : ℝ)) /
          ((((m + 1 : ℕ) : ℝ) ^ 2) * Real.log ((m + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 1) := by
    have hone : Filter.Tendsto
        (fun m : ℕ ↦ (1 : ℝ) + Real.log 3 /
          ((((m + 1 : ℕ) : ℝ) ^ 2) * Real.log ((m + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 1) := by
      simpa using
        ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ))
          Filter.atTop (nhds 1)).add hcorr)
    apply hone.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hDne : (((m + 1 : ℕ) : ℝ) ^ 2) *
        Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 := by
      apply mul_ne_zero
      · exact pow_ne_zero _ (by positivity)
      · exact (Real.log_pos (by
          exact_mod_cast (show 1 < m + 1 by omega))).ne'
    rw [add_div, div_self hDne]
    ring
  have hDoverC : Filter.Tendsto
      (fun m : ℕ ↦
        ((((m + 1 : ℕ) : ℝ) ^ 2) * Real.log ((m + 1 : ℕ) : ℝ)) /
          (Real.log 3 + (((m + 1 : ℕ) : ℝ) ^ 2) *
            Real.log ((m + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 1) := by
    have hinv := hCoverD.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [inv_div] using hinv
  have hanalytic := hAD.mul hDoverC
  have hanalytic' : Filter.Tendsto
      (fun m : ℕ ↦
        ((m : ℝ) * ((m - 17 : ℕ) : ℝ) * Real.log (m : ℝ)) /
            ((((m + 1 : ℕ) : ℝ) ^ 2) * Real.log ((m + 1 : ℕ) : ℝ)) *
          (((((m + 1 : ℕ) : ℝ) ^ 2) * Real.log ((m + 1 : ℕ) : ℝ)) /
            (Real.log 3 + (((m + 1 : ℕ) : ℝ) ^ 2) *
              Real.log ((m + 1 : ℕ) : ℝ))))
      Filter.atTop (nhds 1) := by
    simpa using hanalytic
  apply hanalytic'.congr'
  filter_upwards [Filter.eventually_ge_atTop 18] with m hm
  have hDne : (((m + 1 : ℕ) : ℝ) ^ 2) *
      Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by positivity)
    · exact (Real.log_pos (by
        exact_mod_cast (show 1 < m + 1 by omega))).ne'
  have hCne : Real.log 3 + (((m + 1 : ℕ) : ℝ) ^ 2) *
      Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 := by
    have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hDpos : (0 : ℝ) < (((m + 1 : ℕ) : ℝ) ^ 2) *
        Real.log ((m + 1 : ℕ) : ℝ) := by positivity
    positivity
  have hlogQ : Real.log (smallValueQ m : ℝ) =
      (m : ℝ) * ((m - 17 : ℕ) : ℝ) * Real.log (m : ℝ) := by
    simp only [smallValueQ, smallValueY, Nat.cast_pow]
    rw [Real.log_pow, Real.log_pow]
    ring
  have hlogC : Real.log (smallValueCeiling (m + 1) : ℝ) =
      Real.log 3 + (((m + 1 : ℕ) : ℝ) ^ 2) *
        Real.log ((m + 1 : ℕ) : ℝ) := by
    simp only [smallValueCeiling, smallValueY, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (pow_ne_zero _ (pow_ne_zero _ (by positivity))),
      Real.log_pow, Real.log_pow]
    ring
  rw [hlogQ, hlogC]
  have hlogsNat : Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))).ne'
  field_simp [hDne, hCne, hlogsNat]

/-- The advertised `x^{1-o(1)}` count for every sufficiently large
ambient bound `x`, rather than only along the explicit cofinal sequence. -/
theorem manySmallUpTo_log_card_ratio_tendsto_one :
    Filter.Tendsto
      (fun x : ℕ ↦ Real.log ((manySmallUpTo x).card : ℝ) /
        Real.log (x : ℝ))
      Filter.atTop (nhds 1) := by
  have hlower : Filter.Tendsto
      (fun x : ℕ ↦
        Real.log (smallValueQ (smallValueFloorIndex x) : ℝ) /
          Real.log
            (smallValueCeiling (smallValueFloorIndex x + 1) : ℝ))
      Filter.atTop (nhds 1) :=
    smallValue_log_reservoir_ratio_tendsto_one.comp
      smallValueFloorIndex_tendsto_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · have hparam : ∀ᶠ x : ℕ in Filter.atTop,
        18 ≤ smallValueFloorIndex x :=
      smallValueFloorIndex_tendsto_atTop.eventually
        (Filter.eventually_ge_atTop 18)
    filter_upwards [eventually_smallValueFloorIndex_brackets,
      eventually_smallValueQ_floor_lt_manySmallUpTo_card, hparam] with x hx hcount hm
    let m := smallValueFloorIndex x
    have hmpos : 0 < m := by omega
    have hcount' : smallValueQ m < (manySmallUpTo x).card := by
      simpa [m] using hcount
    have hxlower : smallValueCeiling m ≤ x := by
      simpa [m] using hx.1
    have hxupper : x < smallValueCeiling (m + 1) := by
      simpa [m] using hx.2
    have hQpos : 0 < smallValueQ m := by
      simp [smallValueQ, smallValueY, hmpos]
    have hcardpos : 0 < (manySmallUpTo x).card := hQpos.trans hcount'
    have hCpos : 0 < smallValueCeiling (m + 1) := by
      simp [smallValueCeiling, smallValueY, show 0 < m + 1 by omega]
    have hxpos : 0 < x := by
      have hCmpos : 0 < smallValueCeiling m := by
        simp [smallValueCeiling, smallValueY, hmpos]
      exact hCmpos.trans_le hxlower
    have hxone : 1 < x := by
      have hCge : 3 ≤ smallValueCeiling m := by
        rw [smallValueCeiling]
        exact Nat.le_mul_of_pos_right 3 (pow_pos (by
          simp [smallValueY, hmpos]) _)
      exact lt_of_lt_of_le (by omega) (hCge.trans hxlower)
    have hCone : 1 < smallValueCeiling (m + 1) := by
      rw [smallValueCeiling]
      have hpowpos : 0 < smallValueY (m + 1) ^ (m + 1) :=
        pow_pos (by simp [smallValueY, hmpos]) _
      omega
    have hlogx : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hxone)
    have hlogC : 0 < Real.log (smallValueCeiling (m + 1) : ℝ) :=
      Real.log_pos (by exact_mod_cast hCone)
    have hlogQnonneg : 0 ≤ Real.log (smallValueQ m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ smallValueQ m by omega))
    have hlogQle : Real.log (smallValueQ m : ℝ) ≤
        Real.log ((manySmallUpTo x).card : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · change (0 : ℝ) < (smallValueQ m : ℝ)
        exact_mod_cast hQpos
      · change (0 : ℝ) < ((manySmallUpTo x).card : ℝ)
        exact_mod_cast hcardpos
      · exact_mod_cast hcount'.le
    have hlogxle : Real.log (x : ℝ) ≤
        Real.log (smallValueCeiling (m + 1) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · change (0 : ℝ) < (x : ℝ)
        exact_mod_cast hxpos
      · change (0 : ℝ) < (smallValueCeiling (m + 1) : ℝ)
        exact_mod_cast hCpos
      · exact_mod_cast hxupper.le
    calc
      Real.log (smallValueQ m : ℝ) /
          Real.log (smallValueCeiling (m + 1) : ℝ) ≤
          Real.log (smallValueQ m : ℝ) / Real.log (x : ℝ) :=
        div_le_div_of_nonneg_left hlogQnonneg hlogx hlogxle
      _ ≤ Real.log ((manySmallUpTo x).card : ℝ) / Real.log (x : ℝ) :=
        div_le_div_of_nonneg_right hlogQle hlogx.le
  · filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    have hxpos : 0 < x := by omega
    have hcard : (manySmallUpTo x).card ≤ x := by
      calc
        (manySmallUpTo x).card ≤ (Finset.Icc 1 x).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ x := by simpa using card_Icc_one x
    have hlogx : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hcardpos : 0 < (manySmallUpTo x).card := by
      have hmem : 1 ∈ manySmallUpTo x := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
        have ht : t 1 = 0 := (t_eq_zero_iff 1).2 ⟨1, by norm_num⟩
        rw [ht]
        norm_num
      exact Finset.card_pos.mpr ⟨1, hmem⟩
    have hlogle : Real.log ((manySmallUpTo x).card : ℝ) ≤
        Real.log (x : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · change (0 : ℝ) < ((manySmallUpTo x).card : ℝ)
        exact_mod_cast hcardpos
      · change (0 : ℝ) < (x : ℝ)
        exact_mod_cast hxpos
      · exact_mod_cast hcard
    exact (div_le_one hlogx).mpr hlogle

/-- Coarse BPZ many-small-values theorem in a completely explicit cofinal
form.  The first limit is the formal meaning of `#S_m = X_m^(1-o(1))`;
the final conjunct gives the advertised
`exp (O (sqrt (log n * log log n)))` bound with an absolute constant. -/
theorem erdos841_many_small_values :
    Filter.Tendsto smallValueEnd Filter.atTop Filter.atTop ∧
    Filter.Tendsto
      (fun m : ℕ ↦ Real.log ((manySmallStarts m).card : ℝ) /
        Real.log (smallValueEnd m : ℝ))
      Filter.atTop (nhds 1) ∧
    ∀ᶠ m : ℕ in Filter.atTop, ∀ n ∈ manySmallStarts m,
      n ≤ smallValueEnd m ∧
      (t n : ℝ) ≤ Real.exp
        (20 * Real.sqrt (Real.log n * Real.log (Real.log n))) := by
  refine ⟨smallValueEnd_tendsto_atTop,
    manySmallStarts_log_card_ratio_tendsto_one, ?_⟩
  filter_upwards [eventually_manySmallStarts_witness_bound] with m hm
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  exact ⟨(Finset.mem_Ioc.mp hn'.1).2, hm n hn⟩

/-- BPZ's `x^{1-o(1)}` many-small-values conclusion for every ambient
bound `x`.  The second conjunct identifies the counted finset with the
set in the published statement, including positivity of the starts. -/
theorem erdos841_many_small_values_global :
    Filter.Tendsto
      (fun x : ℕ ↦ Real.log ((manySmallUpTo x).card : ℝ) /
        Real.log (x : ℝ))
      Filter.atTop (nhds 1) ∧
    ∀ x n : ℕ, n ∈ manySmallUpTo x ↔
      1 ≤ n ∧ n ≤ x ∧
        (t n : ℝ) ≤ Real.exp
          (20 * Real.sqrt (Real.log n * Real.log (Real.log n))) := by
  refine ⟨manySmallUpTo_log_card_ratio_tendsto_one, ?_⟩
  intro x n
  simp only [manySmallUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- In an interval of length `H`, the number of `Y`-smooth starts having
`t n > H` is at most the exceptional count plus `pi(Y)`, provided `H ≤ Y`. -/
theorem smooth_large_t_interval_card_le_general (X H Y : ℕ) (hHY : H ≤ Y) :
    ((smoothIntervalAt X H Y).filter fun n ↦ H < t n).card ≤
      (exceptionalInterval X H).card + (Y + 1).primesBelow.card := by
  let M := smoothIntervalAt X H Y
  let G := M.filter fun n ↦ t n ≤ H
  let E := exceptionalInterval X H
  let B := closedStarts X (X + H)
  have hMleB : M.card ≤ B.card + (Y + 1).primesBelow.card := by
    have h := bpz_smooth_interval_bound_general X H Y
    change M.card - (Y + 1).primesBelow.card ≤ B.card at h
    omega
  have hBsub : B ⊆ G ∪ E := by
    intro n hnB
    have hnB' := Finset.mem_filter.mp hnB
    have hnI := hnB'.1
    have htH : t n ≤ H := by
      have hnlo := (Finset.mem_Ioc.mp hnI).1
      have hnclose := hnB'.2
      omega
    by_cases hnE : largestPrimeFactor n ^ 2 ∣ n
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hnE⟩)
    · have hn1 : 1 < n := by
        have hnpos : 0 < n := by
          have := (Finset.mem_Ioc.mp hnI).1
          omega
        by_contra h
        have hnEq : n = 1 := by omega
        subst n
        exact hnE (by norm_num [largestPrimeFactor])
      have hPle : largestPrimeFactor n ≤ Y :=
        (largestPrimeFactor_le_t hn1 hnE).trans (htH.trans hHY)
      have hsmooth : n ∈ (Y + 1).smoothNumbers := by
        rw [Nat.mem_smoothNumbers']
        intro p hp hpn
        have hpP := prime_le_largestPrimeFactor hn1 hp hpn
        omega
      apply Finset.mem_union_left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_filter.mpr ⟨hnI, hsmooth⟩, htH⟩
  have hBle : B.card ≤ G.card + E.card :=
    (Finset.card_le_card hBsub).trans (Finset.card_union_le G E)
  have hMle : M.card ≤ G.card + E.card + (Y + 1).primesBelow.card := by omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := M) (fun n ↦ t n ≤ H)
  change G.card + (M.filter fun n ↦ ¬t n ≤ H).card = M.card at hsplit
  have hbad : (M.filter fun n ↦ ¬t n ≤ H) = M.filter fun n ↦ H < t n := by
    ext n
    simp
  rw [hbad] at hsplit
  change (M.filter fun n ↦ H < t n).card ≤
    E.card + (Y + 1).primesBelow.card
  omega

/-- `Y`-smooth members of `(X,X+Z]` whose `t`-value exceeds the chosen
block length `H`. -/
def smoothSegmentFailures (X Z H Y : ℕ) : Finset ℕ :=
  (smoothIntervalAt X Z Y).filter fun n ↦ H < t n

/-- Global form of the separated-cutoff interval estimate, obtained by
partitioning `(X,X+Z]` into consecutive blocks of length `H`. -/
theorem smoothSegmentFailures_card_le (X Z H Y : ℕ)
    (hH : 0 < H) (hHY : H ≤ Y) :
    (smoothSegmentFailures X Z H Y).card ≤
      (Z / H + 1) * (Y + 1).primesBelow.card +
        (exceptionalInterval X ((Z / H + 1) * H)).card := by
  let S := smoothSegmentFailures X Z H Y
  let K := Finset.range (Z / H + 1)
  let f : ℕ → ℕ := fun n ↦ (n - X - 1) / H
  have hmaps : (S : Set ℕ).MapsTo f K := by
    intro n hn
    have hn' : n ∈ smoothIntervalAt X Z Y ∧ H < t n := by
      simpa [S, smoothSegmentFailures] using hn
    have hnI := (Finset.mem_filter.mp hn'.1).1
    have hnle := (Finset.mem_Ioc.mp hnI).2
    have hsub : n - X - 1 ≤ Z := by omega
    simpa [K, f] using Nat.lt_succ_of_le (Nat.div_le_div_right hsub)
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (k : ℕ) (hk : k ∈ K) :
      ({n ∈ S | f n = k}).card ≤
        (exceptionalInterval (X + k * H) H).card + (Y + 1).primesBelow.card := by
    have hsub : {n ∈ S | f n = k} ⊆
        (smoothIntervalAt (X + k * H) H Y).filter fun n ↦ H < t n := by
      intro n hn
      have hnmem := Finset.mem_filter.mp hn
      have hnS : n ∈ smoothIntervalAt X Z Y ∧ H < t n := by
        simpa [S, smoothSegmentFailures] using hnmem.1
      have hnA := Finset.mem_filter.mp hnS.1
      have hnBase := (Finset.mem_Ioc.mp hnA.1).1
      have hmod := Nat.mod_lt (n - X - 1) hH
      have hdecomp := Nat.mod_add_div (n - X - 1) H
      have hfEq : (n - X - 1) / H = k := by simpa [f] using hnmem.2
      rw [hfEq] at hdecomp
      have hdecomp' : (n - X - 1) % H + k * H = n - X - 1 := by
        simpa [Nat.mul_comm] using hdecomp
      have hLower : X + k * H < n := by omega
      have hUpper : n ≤ X + k * H + H := by omega
      apply Finset.mem_filter.mpr
      refine ⟨?_, hnS.2⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hLower, hUpper⟩, hnA.2⟩
    exact (Finset.card_le_card hsub).trans
      (smooth_large_t_interval_card_le_general (X + k * H) H Y hHY)
  have hpair : (K : Set ℕ).PairwiseDisjoint
      (fun k ↦ exceptionalInterval (X + k * H) H) := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro n hni hnj
    have hniBounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hni).1
    have hnjBounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hnj).1
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hblocks : X + i * H + H ≤ X + j * H := by
        have := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hij)
        simpa [Nat.add_mul, Nat.add_assoc] using Nat.add_le_add_left this X
      omega
    · have hblocks : X + j * H + H ≤ X + i * H := by
        have := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hji)
        simpa [Nat.add_mul, Nat.add_assoc] using Nat.add_le_add_left this X
      omega
  have hEsub : K.biUnion (fun k ↦ exceptionalInterval (X + k * H) H) ⊆
      exceptionalInterval X ((Z / H + 1) * H) := by
    intro n hn
    obtain ⟨k, hkK, hnk⟩ := Finset.mem_biUnion.mp hn
    have hk : k < Z / H + 1 := by simpa [K] using hkK
    have hndata := Finset.mem_filter.mp hnk
    have hnI := Finset.mem_Ioc.mp hndata.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, ?_⟩, hndata.2⟩
    have hmul := Nat.mul_le_mul_right H (Nat.succ_le_iff.mpr hk)
    have hmul' : X + k * H + H ≤ X + (Z / H + 1) * H := by
      have := Nat.add_le_add_left hmul X
      simpa [Nat.add_mul, Nat.add_assoc] using this
    simpa [Nat.add_assoc] using hnI.2.trans hmul'
  have hsumE : ∑ k ∈ K, (exceptionalInterval (X + k * H) H).card ≤
      (exceptionalInterval X ((Z / H + 1) * H)).card := by
    rw [← Finset.card_biUnion hpair]
    exact Finset.card_le_card hEsub
  rw [hpartition]
  calc
    ∑ k ∈ K, ({n ∈ S | f n = k}).card ≤
        ∑ k ∈ K,
          ((exceptionalInterval (X + k * H) H).card +
            (Y + 1).primesBelow.card) := Finset.sum_le_sum hfiber
    _ = (∑ k ∈ K, (exceptionalInterval (X + k * H) H).card) +
          K.card * (Y + 1).primesBelow.card := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (exceptionalInterval X ((Z / H + 1) * H)).card +
          K.card * (Y + 1).primesBelow.card := Nat.add_le_add_right hsumE _
    _ = (Z / H + 1) * (Y + 1).primesBelow.card +
          (exceptionalInterval X ((Z / H + 1) * H)).card := by
      simp [K, Nat.add_comm]

/-! ## Exact moving-threshold sets -/

/-- Positive integers `n ≤ x` satisfying the original moving inequality
`t n ≤ n^c` (with the real power converted to its natural floor). -/
def movingSmallTUpTo (x : ℕ) (c : ℝ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ t n ≤ powerThreshold c n

/-- Positive integers `n ≤ x` whose largest prime factor is at most
`n^c`. -/
def movingSmoothUpTo (x : ℕ) (c : ℝ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n ↦ largestPrimeFactor n ≤ powerThreshold c n

/-- The easy moving-threshold comparison direction: outside the exceptional
largest-prime-square set, `P⁺(n) ≤ t n`. -/
theorem movingSmallT_card_le_movingSmooth_add_exceptional (x : ℕ) (c : ℝ) :
    (movingSmallTUpTo x c).card ≤
      (movingSmoothUpTo x c).card + (exceptionalInterval 0 x).card := by
  have hsub : movingSmallTUpTo x c ⊆
      movingSmoothUpTo x c ∪ exceptionalInterval 0 x := by
    intro n hn
    have hn' : n ∈ Finset.Icc 1 x ∧ t n ≤ powerThreshold c n := by
      simpa [movingSmallTUpTo] using hn
    have hnLower : 1 ≤ n := (Finset.mem_Icc.mp hn'.1).1
    have hnPos : 0 < n := by omega
    by_cases hnE : largestPrimeFactor n ^ 2 ∣ n
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨by simpa using
        (Finset.mem_Ioc.mpr ⟨hnPos, (Finset.mem_Icc.mp hn'.1).2⟩), hnE⟩
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hn'.1, ?_⟩
      by_cases hnOne : n = 1
      · subst n
        simp [largestPrimeFactor, powerThreshold]
      · exact (largestPrimeFactor_le_t (by omega) hnE).trans hn'.2
  exact (Finset.card_le_card hsub).trans
    (Finset.card_union_le (movingSmoothUpTo x c) (exceptionalInterval 0 x))

/-- Members of the moving smooth set which fail the corresponding moving
`t` inequality. -/
def movingFailures (x : ℕ) (c : ℝ) : Finset ℕ :=
  (movingSmoothUpTo x c).filter fun n ↦ powerThreshold c n < t n

/-- Finite tail comparison for moving thresholds.  On `(D,x]`, suppose all
moving cutoffs lie between `H` and `Y`.  Then the number of moving failures
is bounded by the discarded initial segment, the block-prime loss, and the
exceptional set. -/
theorem movingFailures_card_le_tail_errors (x D H Y : ℕ) (c : ℝ)
    (hD : D ≤ x) (hH : 0 < H) (hHY : H ≤ Y)
    (hLower : ∀ n ∈ Finset.Ioc D x, H ≤ powerThreshold c n)
    (hUpper : ∀ n ∈ Finset.Ioc D x, powerThreshold c n ≤ Y) :
    (movingFailures x c).card ≤ D +
      ((x - D) / H + 1) * (Y + 1).primesBelow.card +
        (exceptionalInterval D (((x - D) / H + 1) * H)).card := by
  have hsub : movingFailures x c ⊆
      Finset.Icc 1 D ∪ smoothSegmentFailures D (x - D) H Y := by
    intro n hn
    have hn' : n ∈ movingSmoothUpTo x c ∧ powerThreshold c n < t n := by
      simpa [movingFailures] using hn
    have hnM : n ∈ Finset.Icc 1 x ∧
        largestPrimeFactor n ≤ powerThreshold c n := by
      simpa [movingSmoothUpTo] using hn'.1
    by_cases hnD : n ≤ D
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hnM.1).1, hnD⟩)
    · apply Finset.mem_union_right
      have hnTail : n ∈ Finset.Ioc D x := Finset.mem_Ioc.mpr
        ⟨Nat.lt_of_not_ge hnD, (Finset.mem_Icc.mp hnM.1).2⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, (hLower n hnTail).trans_lt hn'.2⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · have hxEq : D + (x - D) = x := Nat.add_sub_of_le hD
        simpa [hxEq] using hnTail
      · rw [Nat.mem_smoothNumbers']
        intro p hp hpn
        have hn1 : 1 < n := by
          exact hp.one_lt.trans_le (Nat.le_of_dvd (by omega) hpn)
        have hpP := prime_le_largestPrimeFactor hn1 hp hpn
        exact Nat.lt_succ_iff.mpr
          (hpP.trans (hnM.2.trans (hUpper n hnTail)))
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le (Finset.Icc 1 D)
    (smoothSegmentFailures D (x - D) H Y)
  have hsegment := smoothSegmentFailures_card_le D (x - D) H Y hH hHY
  have hIcc : (Finset.Icc 1 D).card ≤ D := by
    simpa using card_Icc_one D
  omega

/-- The moving smooth count is at most the moving `t` count plus the number
of moving failures. -/
theorem movingSmooth_card_le_movingSmallT_add_failures (x : ℕ) (c : ℝ) :
    (movingSmoothUpTo x c).card ≤
      (movingSmallTUpTo x c).card + (movingFailures x c).card := by
  let M := movingSmoothUpTo x c
  let G := M.filter fun n ↦ t n ≤ powerThreshold c n
  let F := movingFailures x c
  have hGsub : G ⊆ movingSmallTUpTo x c := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnM : n ∈ Finset.Icc 1 x ∧
        largestPrimeFactor n ≤ powerThreshold c n := by
      simpa [M, movingSmoothUpTo] using hn'.1
    exact Finset.mem_filter.mpr ⟨hnM.1, hn'.2⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := M) (fun n ↦ t n ≤ powerThreshold c n)
  have hnot : (M.filter fun n ↦ ¬t n ≤ powerThreshold c n) = F := by
    ext n
    simp [F, M, movingFailures]
  change G.card + (M.filter fun n ↦ ¬t n ≤ powerThreshold c n).card =
    M.card at hsplit
  rw [hnot] at hsplit
  have hG := Finset.card_le_card hGsub
  change M.card ≤ (movingSmallTUpTo x c).card + F.card
  omega

/-- The complete finite error used to compare the two moving-threshold
counting functions after discarding `[1,D]`. -/
def movingTailError (x D H Y : ℕ) : ℕ :=
  (exceptionalInterval 0 x).card + D +
    (((x - D) / H + 1) * (Y + 1).primesBelow.card +
      (exceptionalInterval D (((x - D) / H + 1) * H)).card)

/-- Abstract analytic wrapper for the moving-threshold argument.  Once a
choice of scales `D,H,Y` makes the displayed finite error `o(x)`, the two
moving densities differ by zero. -/
theorem moving_comparison_tendsto_zero_of_tail_scales
    (c : ℝ) (D H Y : ℕ → ℕ)
    (hD : ∀ᶠ x : ℕ in Filter.atTop, D x ≤ x)
    (hH : ∀ᶠ x : ℕ in Filter.atTop, 0 < H x)
    (hHY : ∀ᶠ x : ℕ in Filter.atTop, H x ≤ Y x)
    (hLower : ∀ᶠ x : ℕ in Filter.atTop,
      ∀ n ∈ Finset.Ioc (D x) x, H x ≤ powerThreshold c n)
    (hUpper : ∀ᶠ x : ℕ in Filter.atTop,
      ∀ n ∈ Finset.Ioc (D x) x, powerThreshold c n ≤ Y x)
    (herror : Filter.Tendsto
      (fun x : ℕ ↦ (movingTailError x (D x) (H x) (Y x) : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun x : ℕ ↦
        (((movingSmallTUpTo x c).card : ℝ) -
          ((movingSmoothUpTo x c).card : ℝ)) / (x : ℝ))
      Filter.atTop (nhds 0) := by
  have hxPos : ∀ᶠ x : ℕ in Filter.atTop, 0 < x :=
    Filter.eventually_gt_atTop 0
  apply squeeze_zero_norm' _ herror
  filter_upwards [hD, hH, hHY, hLower, hUpper, hxPos] with
    x hDx hHx hHYx hLowerx hUpperx hx
  let A := (movingSmallTUpTo x c).card
  let B := (movingSmoothUpTo x c).card
  let R := movingTailError x (D x) (H x) (Y x)
  have hforward := movingSmallT_card_le_movingSmooth_add_exceptional x c
  have hfail := movingFailures_card_le_tail_errors x (D x) (H x) (Y x) c
    hDx hHx hHYx hLowerx hUpperx
  have hreverse := movingSmooth_card_le_movingSmallT_add_failures x c
  have hAR : A ≤ B + R := by
    change (movingSmallTUpTo x c).card ≤
      (movingSmoothUpTo x c).card + movingTailError x (D x) (H x) (Y x)
    have hER : (exceptionalInterval 0 x).card ≤
        movingTailError x (D x) (H x) (Y x) := by
      simp only [movingTailError]
      omega
    exact hforward.trans (Nat.add_le_add_left hER _)
  have hBR : B ≤ A + R := by
    change B ≤ A + (movingFailures x c).card at hreverse
    change (movingFailures x c).card ≤ D x +
      ((x - D x) / H x + 1) * (Y x + 1).primesBelow.card +
        (exceptionalInterval (D x) (((x - D x) / H x + 1) * H x)).card at hfail
    change B ≤ A + R
    simp only [R, movingTailError]
    omega
  have hARreal : (A : ℝ) ≤ (B : ℝ) + (R : ℝ) := by exact_mod_cast hAR
  have hBRreal : (B : ℝ) ≤ (A : ℝ) + (R : ℝ) := by exact_mod_cast hBR
  have habs : |(A : ℝ) - (B : ℝ)| ≤ (R : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  change ‖(((A : ℝ) - (B : ℝ)) / (x : ℝ))‖ ≤ (R : ℝ) / (x : ℝ)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hxR.le]
  exact div_le_div_of_nonneg_right habs hxR.le

/-! ## The concrete moving-threshold tail scale -/

/-- The real tail cutoff `x / sqrt(log x)`. -/
def movingTailScale (x : ℕ) : ℝ :=
  (x : ℝ) / Real.sqrt (Real.log (x : ℝ))

/-- The natural tail cutoff used in the BPZ moving-threshold comparison. -/
def movingTailCutoff (x : ℕ) : ℕ :=
  ⌊movingTailScale x⌋₊

lemma movingTailScale_tendsto_atTop :
    Filter.Tendsto movingTailScale Filter.atTop Filter.atTop := by
  have hzeroR : Filter.Tendsto
      (fun z : ℝ ↦ Real.sqrt (Real.log z) / z) Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_pow_atTop
      (1 : ℝ) ((1 : ℝ) / 2) (by norm_num)
    simpa [Real.sqrt_eq_rpow, Real.rpow_one] using h
  have hzero : Filter.Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ)) / (x : ℝ))
      Filter.atTop (nhds 0) := hzeroR.comp tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ x : ℕ in Filter.atTop,
      0 < Real.sqrt (Real.log (x : ℝ)) / (x : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with x hx
    exact div_pos (Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega))))
      (by positivity)
  have hzeroPos : Filter.Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ)) / (x : ℝ))
      Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    Filter.tendsto_inf.mpr ⟨hzero, Filter.tendsto_principal.mpr hpos⟩
  have hinv := hzeroPos.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with x hx
  have hxR : (0 : ℝ) < x := by positivity
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  change (Real.sqrt (Real.log (x : ℝ)) / (x : ℝ))⁻¹ = movingTailScale x
  simp only [movingTailScale]
  field_simp

lemma movingTailCutoff_tendsto_atTop :
    Filter.Tendsto movingTailCutoff Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp movingTailScale_tendsto_atTop

lemma movingTailCutoff_div_scale_tendsto_one :
    Filter.Tendsto
      (fun x : ℕ ↦ (movingTailCutoff x : ℝ) / movingTailScale x)
      Filter.atTop (nhds 1) := by
  exact tendsto_nat_floor_div_atTop.comp movingTailScale_tendsto_atTop

lemma movingTailCutoff_density_zero :
    Filter.Tendsto
      (fun x : ℕ ↦ (movingTailCutoff x : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
  have hlogTop : Filter.Tendsto (fun x : ℕ ↦ Real.log (x : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtTop : Filter.Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_sqrt_atTop.comp hlogTop
  have hinv : Filter.Tendsto
      (fun x : ℕ ↦ (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrtTop
  have hprod := movingTailCutoff_div_scale_tendsto_one.mul hinv
  have hprod0 : Filter.Tendsto
      (fun x : ℕ ↦ (movingTailCutoff x : ℝ) / movingTailScale x *
        (Real.sqrt (Real.log (x : ℝ)))⁻¹)
      Filter.atTop (nhds 0) := by simpa using hprod
  apply hprod0.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with x hx
  have hxR : (0 : ℝ) < x := by positivity
  have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
    Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  simp only [movingTailScale]
  field_simp

lemma eventually_movingTailCutoff_le_self :
    ∀ᶠ x : ℕ in Filter.atTop, movingTailCutoff x ≤ x := by
  have hlogTop : Filter.Tendsto (fun x : ℕ ↦ Real.log (x : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [hlogOne, Filter.eventually_ge_atTop 2] with x hlog hx
  apply Nat.floor_le_of_le
  change movingTailScale x ≤ (x : ℝ)
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
    exact (Real.le_sqrt (by norm_num) (zero_le_one.trans hlog)).2 (by simpa using hlog)
  exact div_le_self (by positivity) hsqrtOne

/-- Once `pi(Y(x))/H(x) → 0`, all four terms in the moving-tail error are
`o(x)`.  The exceptional segment is absorbed into the exceptional set
through `2x`. -/
theorem movingTailError_density_zero_of_prime_ratio
    (D H Y : ℕ → ℕ)
    (hDle : ∀ᶠ x : ℕ in Filter.atTop, D x ≤ x)
    (hHpos : ∀ᶠ x : ℕ in Filter.atTop, 0 < H x)
    (hHle : ∀ᶠ x : ℕ in Filter.atTop, H x ≤ x)
    (hDzero : Filter.Tendsto (fun x : ℕ ↦ (D x : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0))
    (hprime : Filter.Tendsto
      (fun x : ℕ ↦ (Nat.primeCounting (Y x) : ℝ) / (H x : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun x : ℕ ↦ (movingTailError x (D x) (H x) (Y x) : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
  let L : ℕ → ℕ := fun x ↦ ((x - D x) / H x + 1) * H x
  let U : ℕ → ℕ := fun x ↦ D x + L x
  have hxPos : ∀ᶠ x : ℕ in Filter.atTop, 0 < x := Filter.eventually_gt_atTop 0
  have hUbounds : ∀ᶠ x : ℕ in Filter.atTop, x ≤ U x ∧ U x ≤ 2 * x := by
    filter_upwards [hDle, hHpos, hHle] with x hDx hHx hHxx
    have hdecomp := Nat.mod_add_div (x - D x) (H x)
    have hmod := Nat.mod_lt (x - D x) hHx
    have hdiv := Nat.div_mul_le_self (x - D x) (H x)
    have hdecomp' : (x - D x) % H x + ((x - D x) / H x) * H x = x - D x := by
      simpa [Nat.mul_comm] using hdecomp
    change x ≤ D x + (((x - D x) / H x + 1) * H x) ∧
      D x + (((x - D x) / H x + 1) * H x) ≤ 2 * x
    constructor
    · rw [Nat.add_mul]
      omega
    · rw [Nat.add_mul]
      omega
  have hUTop : Filter.Tendsto U Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono' Filter.atTop
      (hUbounds.mono fun x hx ↦ hx.1) Filter.tendsto_id
  have hEUSmall : Filter.Tendsto
      (fun x : ℕ ↦ ((exceptionalInterval 0 (U x)).card : ℝ) / (U x : ℝ))
      Filter.atTop (nhds 0) := exceptionalInterval_density_zero.comp hUTop
  have hEUMajor : Filter.Tendsto
      (fun x : ℕ ↦ 2 *
        (((exceptionalInterval 0 (U x)).card : ℝ) / (U x : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hEUSmall
  have hsegment : Filter.Tendsto
      (fun x : ℕ ↦ ((exceptionalInterval (D x) (L x)).card : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hEUMajor
    filter_upwards [hUbounds, hxPos] with x hUb hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hUR : (0 : ℝ) < U x := by exact_mod_cast hx.trans_le hUb.1
    have hsub : exceptionalInterval (D x) (L x) ⊆ exceptionalInterval 0 (U x) := by
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hnI := Finset.mem_Ioc.mp hn'.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ioc.mpr ⟨by omega, by simpa [U] using hnI.2⟩, hn'.2⟩
    have hcardNat := Finset.card_le_card hsub
    have hcross : (exceptionalInterval (D x) (L x)).card * U x ≤
        2 * (exceptionalInterval 0 (U x)).card * x := by
      calc
        (exceptionalInterval (D x) (L x)).card * U x ≤
            (exceptionalInterval 0 (U x)).card * U x :=
          Nat.mul_le_mul_right _ hcardNat
        _ ≤ (exceptionalInterval 0 (U x)).card * (2 * x) :=
          Nat.mul_le_mul_left _ hUb.2
        _ = 2 * (exceptionalInterval 0 (U x)).card * x := by ring
    rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hxR.le)]
    have hreal : ((exceptionalInterval (D x) (L x)).card : ℝ) / x ≤
        (2 * ((exceptionalInterval 0 (U x)).card : ℝ)) / U x := by
      rw [div_le_div_iff₀ hxR hUR]
      exact_mod_cast hcross
    simpa only [mul_div_assoc] using hreal
  have hprimeMajor : Filter.Tendsto
      (fun x : ℕ ↦ 2 * ((Nat.primeCounting (Y x) : ℝ) / (H x : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hprime
  have hblocks : Filter.Tendsto
      (fun x : ℕ ↦
        ((((x - D x) / H x + 1) * (Y x + 1).primesBelow.card : ℕ) : ℝ) /
          (x : ℝ)) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hprimeMajor
    filter_upwards [hDle, hHpos, hHle, hxPos] with x hDx hHx hHxx hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hHR : (0 : ℝ) < H x := by exact_mod_cast hHx
    rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hxR.le)]
    rw [primesBelow_succ_card_eq_primeCounting]
    have hceil : ((x - D x) / H x + 1) * H x ≤ 2 * x := by
      have hdiv := Nat.div_mul_le_self (x - D x) (H x)
      rw [Nat.add_mul]
      omega
    have hcross :
        (((x - D x) / H x + 1) * Nat.primeCounting (Y x)) * H x ≤
          2 * Nat.primeCounting (Y x) * x := by
      calc
        (((x - D x) / H x + 1) * Nat.primeCounting (Y x)) * H x =
            Nat.primeCounting (Y x) * (((x - D x) / H x + 1) * H x) := by ring
        _ ≤ Nat.primeCounting (Y x) * (2 * x) :=
          Nat.mul_le_mul_left _ hceil
        _ = 2 * Nat.primeCounting (Y x) * x := by ring
    have hreal :
        (((((x - D x) / H x + 1) * Nat.primeCounting (Y x) : ℕ) : ℝ) / x) ≤
          (2 * (Nat.primeCounting (Y x) : ℝ)) / H x := by
      rw [div_le_div_iff₀ hxR hHR]
      exact_mod_cast hcross
    simpa only [mul_div_assoc] using hreal
  have hsum : Filter.Tendsto
      (fun x : ℕ ↦ ((exceptionalInterval 0 x).card : ℝ) / (x : ℝ) +
        ((D x : ℝ) / (x : ℝ) +
          (((((x - D x) / H x + 1) * (Y x + 1).primesBelow.card : ℕ) : ℝ) /
            (x : ℝ) +
            ((exceptionalInterval (D x) (L x)).card : ℝ) / (x : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using exceptionalInterval_density_zero.add (hDzero.add (hblocks.add hsegment))
  apply hsum.congr'
  filter_upwards with x
  simp only [movingTailError, Nat.cast_add, L]
  ring

/-- The quantitative prime loss at the concrete moving scale tends to zero.
This is the analytic heart of replacing `x^c` by `n^c`. -/
theorem moving_prime_loss_tendsto_zero {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto
      (fun x : ℕ ↦
        (Nat.primeCounting (powerThreshold c x) : ℝ) /
          (powerThreshold c (movingTailCutoff x) : ℝ))
      Filter.atTop (nhds 0) := by
  let D : ℕ → ℕ := movingTailCutoff
  let H : ℕ → ℕ := fun x ↦ powerThreshold c (D x)
  let Y : ℕ → ℕ := powerThreshold c
  have hcNonneg : 0 ≤ c := hc0.le
  have hDTop : Filter.Tendsto D Filter.atTop Filter.atTop :=
    movingTailCutoff_tendsto_atTop
  have hHTop : Filter.Tendsto H Filter.atTop Filter.atTop :=
    (powerThreshold_tendsto_atTop hc0).comp hDTop
  have hYTop : Filter.Tendsto Y Filter.atTop Filter.atTop :=
    powerThreshold_tendsto_atTop hc0
  have hDhalf : ∀ᶠ x : ℕ in Filter.atTop,
      movingTailScale x / 2 ≤ (D x : ℝ) := by
    have hnear := movingTailCutoff_div_scale_tendsto_one.eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    have hscalePos : ∀ᶠ x : ℕ in Filter.atTop, 0 < movingTailScale x :=
      movingTailScale_tendsto_atTop.eventually (Filter.eventually_gt_atTop 0)
    filter_upwards [hnear, hscalePos] with x hnear hscale
    have hmul := (lt_div_iff₀ hscale).mp hnear
    nlinarith
  have hHhalf : ∀ᶠ x : ℕ in Filter.atTop,
      (D x : ℝ) ^ c / 2 ≤ (H x : ℝ) := by
    exact hDTop.eventually (by
      simpa [H] using eventually_half_rpow_le_powerThreshold hc0)
  have hYhalf : ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) ^ c / 2 ≤ (Y x : ℝ) := by
    simpa [Y] using eventually_half_rpow_le_powerThreshold hc0
  have hYupper (x : ℕ) : (Y x : ℝ) ≤ (x : ℝ) ^ c := by
    simpa [Y] using powerThreshold_cast_le_rpow c x
  have hcheb : ∀ᶠ x : ℕ in Filter.atTop,
      (Nat.primeCounting (Y x) : ℝ) ≤
        4 * (Y x : ℝ) / Real.log (Y x : ℝ) :=
    hYTop.eventually eventually_primeCounting_le_four_mul_div_log
  have hlogTop : Filter.Tendsto (fun x : ℕ ↦ Real.log (x : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ x : ℕ in Filter.atTop,
      2 * Real.log 2 / c ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (Filter.eventually_ge_atTop (2 * Real.log 2 / c))
  have hsqrtTop : Filter.Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_sqrt_atTop.comp hlogTop
  have hmajor : Filter.Tendsto
      (fun x : ℕ ↦ (32 / c) / Real.sqrt (Real.log (x : ℝ)))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hsqrtTop
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [hDhalf, hHhalf, hYhalf, hcheb, hlogLarge,
    Filter.eventually_ge_atTop 3] with x hDhalfx hHhalfx hYhalfx hchebx hlogLargeX hx3
  have hxPos : (0 : ℝ) < x := by positivity
  have hxOne : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlogPos : 0 < Real.log (x : ℝ) := Real.log_pos hxOne
  have hsqrtPos : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hlogPos
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
    apply (Real.le_sqrt (by norm_num) hlogPos.le).2
    have : (1 : ℝ) ≤ Real.log (x : ℝ) := by
      have hprod := (div_le_iff₀ hc0).mp hlogLargeX
      nlinarith [Real.log_two_gt_d9]
    simpa using this
  have hDpos : (0 : ℝ) < D x := by
    have hscalePos : 0 < movingTailScale x := by
      simp only [movingTailScale]
      exact div_pos hxPos hsqrtPos
    linarith
  have hHpos : (0 : ℝ) < H x := by
    have hDpow : 0 < (D x : ℝ) ^ c := Real.rpow_pos_of_pos hDpos c
    linarith
  have hYpos : (0 : ℝ) < Y x := by
    have hxpow : 0 < (x : ℝ) ^ c := Real.rpow_pos_of_pos hxPos c
    linarith
  have hlogYLower : (c / 2) * Real.log (x : ℝ) ≤ Real.log (Y x : ℝ) := by
    have hbasePos : 0 < (x : ℝ) ^ c / 2 := by positivity
    have hmono := Real.log_le_log hbasePos hYhalfx
    calc
      (c / 2) * Real.log (x : ℝ) ≤
          c * Real.log (x : ℝ) - Real.log 2 := by
        have hprod := (div_le_iff₀ hc0).mp hlogLargeX
        nlinarith
      _ = Real.log ((x : ℝ) ^ c / 2) := by
        rw [Real.log_div (Real.rpow_pos_of_pos hxPos c).ne' (by norm_num),
          Real.log_rpow hxPos]
      _ ≤ Real.log (Y x : ℝ) := hmono
  have hlogYPos : 0 < Real.log (Y x : ℝ) :=
    lt_of_lt_of_le (mul_pos (half_pos hc0) hlogPos) hlogYLower
  have hxDivD : (x : ℝ) / (D x : ℝ) ≤
      2 * Real.sqrt (Real.log (x : ℝ)) := by
    rw [div_le_iff₀ hDpos]
    have hscaleEq : movingTailScale x / 2 =
        (x : ℝ) / (2 * Real.sqrt (Real.log (x : ℝ))) := by
      simp only [movingTailScale]
      field_simp
    rw [hscaleEq] at hDhalfx
    have hmul := (div_le_iff₀ (mul_pos (by norm_num) hsqrtPos)).mp hDhalfx
    nlinarith
  have hpowRatio : (x : ℝ) ^ c / (D x : ℝ) ^ c ≤
      2 * Real.sqrt (Real.log (x : ℝ)) := by
    calc
      (x : ℝ) ^ c / (D x : ℝ) ^ c =
          ((x : ℝ) / (D x : ℝ)) ^ c := by
        rw [Real.div_rpow hxPos.le hDpos.le]
      _ ≤ (2 * Real.sqrt (Real.log (x : ℝ))) ^ c :=
        Real.rpow_le_rpow (by positivity) hxDivD hcNonneg
      _ ≤ (2 * Real.sqrt (Real.log (x : ℝ))) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith) hc1
      _ = 2 * Real.sqrt (Real.log (x : ℝ)) := Real.rpow_one _
  have hYdivH : (Y x : ℝ) / (H x : ℝ) ≤
      4 * Real.sqrt (Real.log (x : ℝ)) := by
    have hden : (D x : ℝ) ^ c / 2 ≤ (H x : ℝ) := hHhalfx
    calc
      (Y x : ℝ) / (H x : ℝ) ≤ (x : ℝ) ^ c / (H x : ℝ) :=
        div_le_div_of_nonneg_right (hYupper x) hHpos.le
      _ ≤ (x : ℝ) ^ c / ((D x : ℝ) ^ c / 2) := by
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hxPos.le c) (by positivity) hden
      _ = 2 * ((x : ℝ) ^ c / (D x : ℝ) ^ c) := by field_simp
      _ ≤ 4 * Real.sqrt (Real.log (x : ℝ)) := by linarith
  rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hHpos.le)]
  calc
    (Nat.primeCounting (Y x) : ℝ) / (H x : ℝ) ≤
        (4 * (Y x : ℝ) / Real.log (Y x : ℝ)) / (H x : ℝ) :=
      div_le_div_of_nonneg_right hchebx hHpos.le
    _ = 4 * ((Y x : ℝ) / (H x : ℝ)) / Real.log (Y x : ℝ) := by field_simp
    _ ≤ 4 * (4 * Real.sqrt (Real.log (x : ℝ))) /
          ((c / 2) * Real.log (x : ℝ)) := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul_of_nonneg_left hYdivH (by norm_num)
      · exact mul_pos (half_pos hc0) hlogPos
      · exact hlogYLower
    _ = (32 / c) / Real.sqrt (Real.log (x : ℝ)) := by
      have hsqrtSq := Real.sq_sqrt hlogPos.le
      field_simp
      nlinarith

/-- The moving-tail error for the concrete choice
`D = floor(x/sqrt(log x))`, `H = floor(D^c)`, `Y = floor(x^c)` is `o(x)`. -/
theorem concrete_movingTailError_density_zero {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto
      (fun x : ℕ ↦
        (movingTailError x (movingTailCutoff x)
          (powerThreshold c (movingTailCutoff x)) (powerThreshold c x) : ℝ) /
            (x : ℝ))
      Filter.atTop (nhds 0) := by
  let D : ℕ → ℕ := movingTailCutoff
  let H : ℕ → ℕ := fun x ↦ powerThreshold c (D x)
  let Y : ℕ → ℕ := powerThreshold c
  have hDle : ∀ᶠ x : ℕ in Filter.atTop, D x ≤ x := by
    simpa [D] using eventually_movingTailCutoff_le_self
  have hHTop : Filter.Tendsto H Filter.atTop Filter.atTop :=
    (powerThreshold_tendsto_atTop hc0).comp movingTailCutoff_tendsto_atTop
  have hHpos : ∀ᶠ x : ℕ in Filter.atTop, 0 < H x :=
    hHTop.eventually (Filter.eventually_gt_atTop 0)
  have hYle : ∀ᶠ x : ℕ in Filter.atTop, Y x ≤ x := by
    simpa [Y] using eventually_powerThreshold_le_self hc1
  have hHY : ∀ᶠ x : ℕ in Filter.atTop, H x ≤ Y x := by
    filter_upwards [hDle] with x hDx
    exact powerThreshold_mono hc0.le hDx
  have hHle : ∀ᶠ x : ℕ in Filter.atTop, H x ≤ x := by
    filter_upwards [hHY, hYle] with x h1 h2
    exact h1.trans h2
  have hprime : Filter.Tendsto
      (fun x : ℕ ↦ (Nat.primeCounting (Y x) : ℝ) / (H x : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [H, Y, D] using moving_prime_loss_tendsto_zero hc0 hc1
  simpa [D, H, Y] using movingTailError_density_zero_of_prime_ratio
    D H Y hDle hHpos hHle movingTailCutoff_density_zero hprime

/-- BPZ Theorem 1.1 at the comparison level: for every fixed `0 < c ≤ 1`,
the normalized difference between the original moving `t_n` count and the
moving largest-prime-factor count tends to zero. -/
theorem movingThreshold_comparison_tendsto_zero {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto
      (fun x : ℕ ↦
        (((movingSmallTUpTo x c).card : ℝ) -
          ((movingSmoothUpTo x c).card : ℝ)) / (x : ℝ))
      Filter.atTop (nhds 0) := by
  let D : ℕ → ℕ := movingTailCutoff
  let H : ℕ → ℕ := fun x ↦ powerThreshold c (D x)
  let Y : ℕ → ℕ := powerThreshold c
  have hDle : ∀ᶠ x : ℕ in Filter.atTop, D x ≤ x := by
    simpa [D] using eventually_movingTailCutoff_le_self
  have hHTop : Filter.Tendsto H Filter.atTop Filter.atTop :=
    (powerThreshold_tendsto_atTop hc0).comp movingTailCutoff_tendsto_atTop
  have hHpos : ∀ᶠ x : ℕ in Filter.atTop, 0 < H x :=
    hHTop.eventually (Filter.eventually_gt_atTop 0)
  have hHY : ∀ᶠ x : ℕ in Filter.atTop, H x ≤ Y x := by
    filter_upwards [hDle] with x hDx
    exact powerThreshold_mono hc0.le hDx
  have hLower : ∀ᶠ x : ℕ in Filter.atTop,
      ∀ n ∈ Finset.Ioc (D x) x, H x ≤ powerThreshold c n := by
    filter_upwards with x
    intro n hn
    exact powerThreshold_mono hc0.le (Finset.mem_Ioc.mp hn).1.le
  have hUpper : ∀ᶠ x : ℕ in Filter.atTop,
      ∀ n ∈ Finset.Ioc (D x) x, powerThreshold c n ≤ Y x := by
    filter_upwards with x
    intro n hn
    exact powerThreshold_mono hc0.le (Finset.mem_Ioc.mp hn).2
  have herror : Filter.Tendsto
      (fun x : ℕ ↦ (movingTailError x (D x) (H x) (Y x) : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [D, H, Y] using concrete_movingTailError_density_zero hc0 hc1
  exact moving_comparison_tendsto_zero_of_tail_scales c D H Y
    hDle hHpos hHY hLower hUpper herror

/-- Consequently either moving density exists exactly when the other does,
and in that case the two limits are equal. -/
theorem movingThreshold_same_limit_iff {c L : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto
        (fun x : ℕ ↦ ((movingSmallTUpTo x c).card : ℝ) / (x : ℝ))
        Filter.atTop (nhds L) ↔
      Filter.Tendsto
        (fun x : ℕ ↦ ((movingSmoothUpTo x c).card : ℝ) / (x : ℝ))
        Filter.atTop (nhds L) := by
  have hdiff0 : Filter.Tendsto
      (fun x : ℕ ↦
        ((movingSmallTUpTo x c).card : ℝ) / (x : ℝ) -
          ((movingSmoothUpTo x c).card : ℝ) / (x : ℝ))
      Filter.atTop (nhds 0) := by
    have h := movingThreshold_comparison_tendsto_zero hc0 hc1
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    field_simp
  constructor
  · intro hsmall
    have h := hsmall.sub hdiff0
    have h' : Filter.Tendsto
        (fun x : ℕ ↦
          ((movingSmallTUpTo x c).card : ℝ) / (x : ℝ) -
            (((movingSmallTUpTo x c).card : ℝ) / (x : ℝ) -
              ((movingSmoothUpTo x c).card : ℝ) / (x : ℝ)))
        Filter.atTop (nhds L) := by simpa using h
    apply h'.congr'
    filter_upwards with x
    ring
  · intro hsmooth
    have h := hdiff0.add hsmooth
    have h' : Filter.Tendsto
        (fun x : ℕ ↦
          (((movingSmallTUpTo x c).card : ℝ) / (x : ℝ) -
            ((movingSmoothUpTo x c).card : ℝ) / (x : ℝ)) +
              ((movingSmoothUpTo x c).card : ℝ) / (x : ℝ))
        Filter.atTop (nhds L) := by simpa using h
    apply h'.congr'
    filter_upwards with x
    ring

/-- The distributional resolution of Problem 841 in a single theorem:
for every fixed `0 < c ≤ 1`, the normalized difference of the two counting
functions tends to zero.  This formulation is meaningful without choosing
or separately constructing the classical smooth-number density; together
with that density theorem it says that both displayed limits in the problem
exist and are equal. -/
theorem erdos841_distributional_resolution :
    ∀ c : ℝ, 0 < c → c ≤ 1 →
      Filter.Tendsto
        (fun x : ℕ ↦
          (((movingSmallTUpTo x c).card : ℝ) -
            ((movingSmoothUpTo x c).card : ℝ)) / (x : ℝ))
        Filter.atTop (nhds 0) := by
  intro c hc0 hc1
  exact movingThreshold_comparison_tendsto_zero hc0 hc1

end

end Erdos841

namespace Erdos841

/-- The exact two-branch conclusion of the fixed-rank logarithmic-form
argument, packaged so the concrete Pell-field construction can retain every
parameter needed for the subsequent explicit estimates. -/
noncomputable def SupportedUnitCombinedRealLogDichotomy
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Fintype ι]
    (basis : Module.Basis ι ℚ K) (φ : K →+* ℂ) (ρ : K →+* ℝ)
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))} [Fintype S]
    (u : S.unit K) (ratio : Kˣ) (e : S → ℤ) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (Ba : ℕ) (QW M : ℝ) : Prop :=
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ := SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
    ((Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
  let W : Kˣ :=
    (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
  let z : K := ((ratio * (u : Kˣ) : Kˣ) : K)
  let m := (NumberField.classNumber K * I) * 2
  let alphaNon := combinedSquaredProductBases (W : K) eps
  let ellNon : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
    Complex.log (φ (alphaNon i))
  (W ∉ integerUnitSubgroup K ∧
    LinearForms.structuredBoxLogarithmicFormThreshold Ba
        (LinearForms.structuredBoxMasterL Ba M alphaNon ellNon)
        M alphaNon ellNon ≤ |Real.log (ρ (z ^ m))|) ∨
  ∃ (c : Fin (NumberField.Units.rank K) →₀ ℤ)
      (reindex : Fin (NumberField.Units.rank K - 1 + 1) ≃
        Fin (NumberField.Units.rank K)),
    W ∈ integerUnitSubgroup K ∧
    let alphaUnit : Fin (NumberField.Units.rank K) → K :=
      fun i ↦ eps i ^ 2
    let ellUnit : Fin (NumberField.Units.rank K) → ℂ := fun i ↦
      Complex.log (φ (alphaUnit i))
    LinearForms.structuredBoxLogarithmicFormThreshold
        (integerUnitAbsorptionNatBound K hB QW Ba)
        (LinearForms.structuredBoxMasterL
          (integerUnitAbsorptionNatBound K hB QW Ba) M
          (fun i ↦ alphaUnit (reindex i))
          (fun i ↦ ellUnit (reindex i))) M
        (fun i ↦ alphaUnit (reindex i))
        (fun i ↦ ellUnit (reindex i)) ≤
      |Real.log (ρ ((z ^ m) ^ (2 * I)))|

/-- All algebraic, finite-prime, height, basis, and archimedean data needed
to apply the fixed-rank logarithmic-form theorem to one simultaneous Pell
triple in the concrete positive-real triquadratic field. -/
noncomputable def RealPellCombinedArchimedeanData
    (γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ) (β₁₂ β₁₃ : ℤ)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) : Prop :=
  let K := realPellField γ₁ γ₂ γ₃
  letI : Algebra ℚ K := K.algebra'
  letI : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  letI : NumberField.IsTotallyReal K :=
    realPellFieldIsTotallyReal hγ₁ hγ₂ hγ₃
  let ratio : Kˣ :=
    Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃) /
      Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂)
  let N := (40320 * H ^ 24) ^ 2
  let B := degreeEightMinkowskiNatBound N
  ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U : S.unit K) (hS : S.Finite)
      (ι : Set K) (hι : ι.Finite) (basis : Module.Basis ι ℚ K)
      (e : S → ℤ)
      (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K)
      (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
        NumberField.mixedEmbedding.convexBodyLTFactor K * B)
      (ζ : NumberField.Units.torsion K)
      (a : Fin (NumberField.Units.rank K) →₀ ℤ),
    letI : Fintype S := hS.fintype
    letI : Fintype ι := hι.fintype
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let P : Kˣ := SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
    let QP : ℝ :=
      ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        (2 * numberFieldFundamentalUnitLogMass K +
          ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
            ((NumberField.classNumber K : ℝ) * (8 * Real.log (J : ℝ))))
    let Qres : ℝ :=
      (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((U : Kˣ) : K)) + QP
    let Acoef : ℝ :=
      ((NumberField.Units.rank K).factorial *
        (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
          ((BoundedUnits.boundedUnitIndexUpper (K := K)
              (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
            (2 * Qres))) ^ NumberField.Units.rank K) /
        (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K
    let Ba := max 1 (Nat.ceil Acoef)
    let QW : ℝ :=
      (2 * (NumberField.classNumber K * I) : ℕ) *
          Height.logHeight₁ (ratio : K) + (2 * I : ℕ) * QP
    S = pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
          (Int.cast_ne_zero.mpr hβ₂₃)) ∧
    ((U : Kˣ) : K) =
      pellValueMinus (realPellRootOne γ₁ γ₂ γ₃)
          (realPellRootTwo γ₁ γ₂ γ₃) (x₁ : ℤ) (x₂ : ℤ) /
        pellValueMinus (realPellRootOne γ₁ γ₂ γ₃)
          (realPellRootThree γ₁ γ₂ γ₃) (x₁ : ℤ) (x₃ : ℤ) ∧
    realPellRealEmbedding γ₁ γ₂ γ₃
        (((ratio * (U : Kˣ) : Kˣ) : K)) - 1 ≠ 0 ∧
    |realPellRealEmbedding γ₁ γ₂ γ₃
        (((ratio * (U : Kˣ) : Kˣ) : K)) - 1| ≤
      2 * (J : ℝ) / (Real.sqrt γ₁ * x₁) ^ 2 ∧
    (U : Kˣ) ^ NumberField.classNumber K = P * (q : Kˣ) ∧
    (∀ v, e v = -(SupportedUnits.valuationMap S K U v).toAdd) ∧
    (∀ v, 2 ^ (e v).natAbs ≤ J ^ 16) ∧
    (∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8) ∧
    (BoundedUnits.boundedUnitSubgroup hB).index ≤
      BoundedUnits.boundedUnitIndexUpper (K := K)
        (totallyRealDegreeEightUnitLogGap / 8) B ∧
    (SupportedUnits.emptyEquivUnits K q) ^ I =
      ζ.1 * a.prod (fun i z ↦ BoundedUnits.boundedFundSystem hB i ^ z) ∧
    (∀ i, (a i).natAbs ≤ Ba) ∧
    Height.logHeight₁ (P : K) ≤ QP ∧
    Height.logHeight₁
      ((((ratio ^ 2) ^ (NumberField.classNumber K * I) *
        (P ^ 2) ^ I : Kˣ) : K)) ≤ QW ∧
    (∀ i, IsIntegral ℤ (basis i)) ∧
    (∀ i (w : K →ₐ[ℚ] ℂ), ‖w (basis i)‖ ≤ (H : ℝ) ^ 3) ∧
    SupportedUnitCombinedRealLogDichotomy basis
      (realPellComplexEmbedding γ₁ γ₂ γ₃)
      (realPellRealEmbedding γ₁ γ₂ γ₃) U ratio e hB a Ba QW ((H : ℝ) ^ 3)

/-- The concrete simultaneous-Pell data satisfy the complete fixed-rank
unit/nonunit logarithmic-form dichotomy.  In particular, this theorem joins
the elementary small archimedean gap to the exact same powered supported
unit product used by the auxiliary-function lower bound. -/
theorem realPell_combined_archimedean_data
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlarge : 2 * J < γ₁ * x₁ ^ 2) :
    RealPellCombinedArchimedeanData γ₁ γ₂ γ₃ H x₁ x₂ x₃ J β₁₂ β₁₃
      hγ₁ hγ₂ hγ₃ hβ₁₂ hβ₁₃ hβ₂₃ := by
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  let : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  let : NumberField.IsTotallyReal K :=
    realPellFieldIsTotallyReal hγ₁ hγ₂ hγ₃
  let ratio : Kˣ :=
    Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃) /
      Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂)
  let r₁ : K := realPellRootOne γ₁ γ₂ γ₃
  let r₂ : K := realPellRootTwo γ₁ γ₂ γ₃
  let r₃ : K := realPellRootThree γ₁ γ₂ γ₃
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := realPellRootOne_sq _ _ _
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := realPellRootTwo_sq _ _ _
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := realPellRootThree_sq _ _ _
  have hdeg : Module.finrank ℚ K ≤ 8 := by
    change Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        ({Real.sqrt γ₁, Real.sqrt γ₂, Real.sqrt γ₃} : Set ℝ)) ≤ 8
    exact finrank_adjoin_three_sqRoots_le_eight
      (Real.sqrt γ₁) (Real.sqrt γ₂) (Real.sqrt γ₃)
      (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity))
  obtain ⟨S, U, V, hS, hSdef, hUV, hU, _hV, _hdecomp0,
      hUreal, hgapNe0, hgapAbs0, _hlog⟩ :=
    realPell_supportedUnit_log_gap hPell hβ₁₂ hβ₁₃ hβ₂₃
      hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
      hx₁ hx₂ hx₃ hlarge.le
  let : Fintype S := hS.fintype
  have hcoordNorm := simultaneousPell_common_left_coordinate_pow_le_of_eq
    hr₁ hr₂ hr₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg J
      hJ₁₂ hJ₁₃ hJ₂₃ S U hSdef (by simpa [r₁, r₂, r₃] using hU)
  rcases hcoordNorm with ⟨hcoordU, hSJ⟩
  let N : ℕ := (40320 * H ^ 24) ^ 2
  let B : ℕ := degreeEightMinkowskiNatBound N
  have hdiscR := realPellField_natAbs_discr_le
    hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
  dsimp only at hdiscR
  have hdisc : |NumberField.discr K| ≤ N := by
    rw [Int.abs_eq_natAbs]
    dsimp [N]
    norm_cast at hdiscR
    exact_mod_cast hdiscR
  have hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B := by
    simpa [B] using
      (minkowskiBound_lt_degreeEightMinkowskiNatBound K hdeg hdisc)
  obtain ⟨e, q, ζ, a, hpow, he, hindex, hdecomp, ha⟩ :=
    numberField_supportedUnit_boundedUnit_decomposition_at K S U hdeg hB
  obtain ⟨ι, hι, basis, hbasis, hMbasis⟩ :=
    exists_threeSqRoot_integral_basis r₁ r₂ r₃ hr₁ hr₂ hr₃
      hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
      (by exact realPellField_adjoin_roots_eq_top γ₁ γ₂ γ₃)
  let : Fintype ι := hι.fintype
  unfold RealPellCombinedArchimedeanData
  dsimp only
  refine ⟨S, U, hS, ι, hι, basis, e, q, hB, ζ, a, ?_⟩
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ := SupportedUnits.numberFieldPrimeClassSupportedUnitProduct S e
  let QP : ℝ :=
    ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
      (2 * numberFieldFundamentalUnitLogMass K +
        ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
          ((NumberField.classNumber K : ℝ) * (8 * Real.log (J : ℝ))))
  let Qactual : ℝ :=
    (NumberField.classNumber K : ℝ) *
        Height.logHeight₁ (((U : Kˣ) : K)) +
      ∑ v, (e v).natAbs * Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))
  let Qres : ℝ :=
    (NumberField.classNumber K : ℝ) *
        Height.logHeight₁ (((U : Kˣ) : K)) + QP
  let Acoef : ℝ :=
    ((NumberField.Units.rank K).factorial *
      (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
        ((BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
          (2 * Qres))) ^ NumberField.Units.rank K) /
      (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K
  let Ba := max 1 (Nat.ceil Acoef)
  let QW : ℝ :=
    (2 * (NumberField.classNumber K * I) : ℕ) *
        Height.logHeight₁ (ratio : K) + (2 * I : ℕ) * QP
  have hJ : 1 ≤ J := by
    exact (Int.natAbs_pos.mpr hβ₁₂).trans_le hJ₁₂
  have hcoordE : ∀ v, 2 ^ (e v).natAbs ≤ J ^ 16 := by
    intro v
    rw [he v, Int.natAbs_neg]
    exact hcoordU v
  have hPheight : Height.logHeight₁ (P : K) ≤ QP := by
    simpa [P, QP] using
      (numberField_primeClassProduct_logHeight_le_of_pow_coordinate
        S e hJ hcoordE hSJ)
  have hsum :
      (∑ v, (e v).natAbs * Height.logHeight₁
        ((((numberFieldPrimeClassSupportedUnit S v) : Kˣ) : K))) ≤ QP := by
    simpa [QP] using
      (numberField_finite_generator_sum_le_of_pow_coordinate
        S e hJ hcoordE hSJ)
  have hQactual : Qactual ≤ Qres := by
    dsimp [Qactual, Qres]
    simpa [add_comm] using
      (add_le_add_left hsum
        ((NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((U : Kˣ) : K))))
  have haAcoef : ∀ i, |((a i : ℤ) : ℝ)| ≤ Acoef := by
    intro i
    refine (ha i).trans ?_
    have hδ : 0 ≤ totallyRealDegreeEightUnitLogGap / 8 :=
      (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num)).le
    have htwice : 2 * Qactual ≤ 2 * Qres :=
      mul_le_mul_of_nonneg_left hQactual (by norm_num)
    have hprod :
        (BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
              (2 * Qactual) ≤
          (BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
              (2 * Qres) :=
      mul_le_mul_of_nonneg_left htwice (Nat.cast_nonneg _)
    have hmax := max_le_max_left
      (BoundedUnits.commonBoundedUnitLogBound (K := K) B) hprod
    have hpow := pow_le_pow_left₀ (by positivity) hmax
      (NumberField.Units.rank K)
    have hnum := mul_le_mul_of_nonneg_left hpow
      (Nat.cast_nonneg (NumberField.Units.rank K).factorial)
    exact div_le_div_of_nonneg_right hnum
      (pow_nonneg hδ (NumberField.Units.rank K))
  have haNat : ∀ i, (a i).natAbs ≤ Ba := by
    intro i
    have hcast : ((a i).natAbs : ℝ) ≤ Acoef := by
      simpa using haAcoef i
    have hceil : (a i).natAbs ≤ Nat.ceil Acoef := by
      exact_mod_cast hcast.trans (Nat.le_ceil Acoef)
    exact hceil.trans (le_max_right _ _)
  have hBa : 1 ≤ Ba := le_max_left _ _
  have hWheight : Height.logHeight₁
      ((((ratio ^ 2) ^ (NumberField.classNumber K * I) *
        (P ^ 2) ^ I : Kˣ) : K)) ≤ QW := by
    simpa [QW] using
      (combinedLeadingFactor_logHeight_le (ratio : K) (P : K)
        (NumberField.classNumber K) I (le_refl _) hPheight)
  have hratioUreal :
      realPellRealEmbedding γ₁ γ₂ γ₃
          (((ratio * (U : Kˣ) : Kˣ) : K)) =
        (β₁₃ : ℝ) / (β₁₂ : ℝ) * ((((U : Kˣ) : K) : ℝ)) := by
    simp [ratio, realPellRealEmbedding]
  have hgapNe : realPellRealEmbedding γ₁ γ₂ γ₃
      (((ratio * (U : Kˣ) : Kˣ) : K)) - 1 ≠ 0 := by
    rw [hratioUreal]
    exact hgapNe0
  have hgapAbs : |realPellRealEmbedding γ₁ γ₂ γ₃
      (((ratio * (U : Kˣ) : Kˣ) : K)) - 1| ≤
        2 * (J : ℝ) / (Real.sqrt γ₁ * x₁) ^ 2 := by
    rw [hratioUreal]
    exact hgapAbs0
  let zreal : ℝ := realPellRealEmbedding γ₁ γ₂ γ₃
    (((ratio * (U : Kˣ) : Kˣ) : K))
  have hAsq : (Real.sqrt γ₁ * (x₁ : ℝ)) ^ 2 =
      (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsmallR : 2 * (J : ℝ) /
      (Real.sqrt γ₁ * x₁) ^ 2 < 1 := by
    rw [hAsq]
    apply (div_lt_one (by positivity)).2
    exact_mod_cast hlarge
  have hzpos : 0 < zreal := by
    have hzabs : |zreal - 1| < 1 := by
      exact hgapAbs.trans_lt hsmallR
    exact sub_pos.mp ((abs_lt.mp hzabs).1 |> fun h ↦ by linarith)
  have hIne : I ≠ 0 := by
    exact BoundedUnits.boundedUnitSubgroup_index_ne_zero hB
  have hmne : (NumberField.classNumber K * I) * 2 ≠ 0 := by
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (NumberField.classNumber_ne_zero K) hIne)
      (by norm_num)
  have htwIne : 2 * I ≠ 0 := Nat.mul_ne_zero (by norm_num) hIne
  have hzne :
      (((ratio * (U : Kˣ)) ^
        ((NumberField.classNumber K * I) * 2)) ^ (2 * I)) ≠ 1 := by
    intro hz
    have hzmap := congrArg (fun w : Kˣ ↦
      realPellRealEmbedding γ₁ γ₂ γ₃ (w : K)) hz
    have hzpow : (zreal ^ ((NumberField.classNumber K * I) * 2)) ^
        (2 * I) = 1 := by
      simpa [zreal, map_pow] using hzmap
    have hzone : zreal ^ ((NumberField.classNumber K * I) * 2) = 1 :=
      (pow_eq_one_iff_of_nonneg (pow_nonneg hzpos.le _)
        htwIne).mp hzpow
    have : zreal = 1 :=
      (pow_eq_one_iff_of_nonneg hzpos.le hmne).mp hzone
    exact hgapNe (sub_eq_zero.mpr this)
  have hM : (1 : ℝ) ≤ (H : ℝ) ^ 3 := by
    exact one_le_pow₀ (by exact_mod_cast hγ₁.trans_le hγ₁H)
  have hdich := supportedUnit_combined_real_log_lower_dichotomy
    basis hbasis (realPellComplexEmbedding γ₁ γ₂ γ₃)
      (realPellRealEmbedding γ₁ γ₂ γ₃) (fun _ ↦ rfl)
      S U ratio e q B Ba hB ζ a hpow hdecomp QW ((H : ℝ) ^ 3)
      hdeg hM hMbasis hBa haNat hWheight (by simpa [I] using hzne)
  refine ⟨hSdef, ?_, hgapNe, hgapAbs, hpow, he, hcoordE, hSJ,
    hindex, hdecomp, haNat, hPheight, hWheight, hbasis, hMbasis, ?_⟩
  · simpa [r₁, r₂, r₃] using hU
  · simpa only [SupportedUnitCombinedRealLogDichotomy]
      using hdich

attribute [local instance] Classical.propDecidable

theorem test_exists_numberFieldPrimeClassGenerator_bounded_logMap
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    ∃ a : NumberField.RingOfIntegers K,
      a ≠ 0 ∧
      v.asIdeal ^ NumberField.classNumber K = Ideal.span {a} ∧
      ∀ w : {w : NumberField.InfinitePlace K //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
        |NumberField.mixedEmbedding.logMap
          (NumberField.mixedEmbedding K (a : K)) w| ≤
          (NumberField.Units.rank K : ℝ) *
            BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
  classical
  let a₀ := numberFieldPrimeClassGenerator v
  have ha₀ : a₀ ≠ 0 := numberFieldPrimeClassGenerator_ne_zero v
  have ha₀emb : NumberField.mixedEmbedding K (a₀ : K) ≠ 0 := by
    simpa only [map_zero] using
      (NumberField.mixedEmbedding_injective K).ne
        (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha₀)
  have hnorm : NumberField.mixedEmbedding.norm
      (NumberField.mixedEmbedding K (a₀ : K)) ≠ 0 := by
    intro h
    exact ha₀emb ((NumberField.mixedEmbedding.norm_eq_zero_iff'
      (x := NumberField.mixedEmbedding K (a₀ : K)) ⟨(a₀ : K), rfl⟩).mp h)
  let b := NumberField.Units.basisOfIsMaxRank
    (BoundedUnits.boundedFundSystem_isMaxRank hB)
  let x := NumberField.mixedEmbedding.logMap
    (NumberField.mixedEmbedding K (a₀ : K))
  let z : Fin (NumberField.Units.rank K) → ℤ := fun i ↦
    -⌊b.repr x i⌋
  let u : (NumberField.RingOfIntegers K)ˣ :=
    ∏ i, BoundedUnits.boundedFundSystem hB i ^ z i
  let a : NumberField.RingOfIntegers K := u * a₀
  refine ⟨a, mul_ne_zero (Units.ne_zero u) ha₀, ?_, ?_⟩
  · calc
      v.asIdeal ^ NumberField.classNumber K = Ideal.span {a₀} :=
        numberFieldPrimeClassGenerator_span v
      _ = Ideal.span {u * a₀} :=
        (Ideal.span_singleton_mul_left_unit u.isUnit a₀).symm
      _ = Ideal.span {a} := rfl
  have hlogu : NumberField.Units.logEmbedding K (Additive.ofMul u) =
      ∑ i, (z i : ℝ) • b i := by
    dsimp only [u]
    rw [ofMul_prod, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ofMul_zpow, map_zsmul]
    rw [NumberField.Units.basisOfIsMaxRank_apply]
    exact (Int.cast_smul_eq_zsmul ℝ (z i)
      (NumberField.Units.logEmbedding K
        (Additive.ofMul (BoundedUnits.boundedFundSystem hB i)))).symm
  have hloga : NumberField.mixedEmbedding.logMap
      (NumberField.mixedEmbedding K (a : K)) = ZSpan.fract b x := by
    have hsmul := NumberField.mixedEmbedding.logMap_unit_smul u hnorm
    have haemb : u • NumberField.mixedEmbedding K (a₀ : K) =
        NumberField.mixedEmbedding K (a : K) := by
      simp [a, NumberField.mixedEmbedding.unitSMul_smul]
    rw [haemb, hlogu] at hsmul
    rw [hsmul]
    apply b.ext_elem
    intro i
    simp only [map_add, Finsupp.coe_add, Pi.add_apply, map_sum,
      LinearEquiv.map_smul,
      b.repr_self, smul_eq_mul, Finsupp.single_apply, z]
    have hsumApply := map_sum (Finsupp.applyAddHom i)
      (fun j : Fin (NumberField.Units.rank K) ↦
        (z j : ℝ) • (Finsupp.single j (1 : ℝ))) Finset.univ
    change (Finsupp.applyAddHom i)
        (∑ j, (z j : ℝ) • (Finsupp.single j (1 : ℝ))) +
      b.repr x i = b.repr (ZSpan.fract b x) i
    rw [hsumApply]
    simp only [Finsupp.applyAddHom_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ i]
    rw [ZSpan.repr_fract_apply]
    dsimp only [z]
    rw [Int.cast_neg, Int.fract]
    rw [if_pos (Finset.mem_univ i)]
    ring
  intro w
  rw [hloga]
  have hrepr := b.sum_repr (ZSpan.fract b x)
  have hw := congrFun hrepr w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hw
  rw [← hw]
  calc
    |∑ i, b.repr (ZSpan.fract b x) i * b i w| ≤
        ∑ i, |b i w| := by
      apply abs_sum_mul_le_sum_abs
      intro i
      have hi := ZSpan.fract_mem_fundamentalDomain b x
      exact ⟨(hi i).1, (hi i).2.le⟩
    _ ≤ ∑ _i : Fin (NumberField.Units.rank K),
        BoundedUnits.commonBoundedUnitLogBound (K := K) B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [NumberField.Units.basisOfIsMaxRank_apply]
      simpa [NumberField.IsTotallyReal.mult_eq] using
        BoundedUnits.boundedFundSystem_log_abs_le hB i w.1
    _ = (NumberField.Units.rank K : ℝ) *
        BoundedUnits.commonBoundedUnitLogBound (K := K) B := by simp

theorem test_numberField_logHeight_le_of_abs_logMap_le
    {K : Type*} [Field K] [NumberField K]
    (a : NumberField.RingOfIntegers K) (ha : a ≠ 0) (C : ℝ)
    (hC : ∀ w : {w : NumberField.InfinitePlace K //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      |NumberField.mixedEmbedding.logMap
        (NumberField.mixedEmbedding K (a : K)) w| ≤ C) :
    Height.logHeight₁ (a : K) ≤
      Real.log ((Algebra.norm ℤ a).natAbs : ℝ) +
        2 * ∑ _w : {w : NumberField.InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          (C + Real.log ((Algebra.norm ℤ a).natAbs : ℝ)) := by
  let w₀ := NumberField.Units.dirichletUnitTheorem.w₀ (K := K)
  let N : ℝ := Real.log ((Algebra.norm ℤ a).natAbs : ℝ)
  let g : {w : NumberField.InfinitePlace K // w ≠ w₀} → ℝ := fun w ↦
    (w.1.mult : ℝ) * Real.log (w.1 (a : K))
  let l₀ : ℝ := (w₀.mult : ℝ) * Real.log (w₀ (a : K))
  have haNorm : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have hnatNorm : 0 < (Algebra.norm ℤ a).natAbs :=
    Int.natAbs_pos.mpr haNorm
  have hN : 0 ≤ N := by
    apply Real.log_nonneg
    exact_mod_cast hnatNorm
  have haK : (a : K) ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hsumAll :=
    NumberField.mixedEmbedding.fundamentalCone.sum_expMap_symm_apply haK
  have hnormQ :
      ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) =
        ((Algebra.norm ℤ a).natAbs : ℝ) := by
    rw [← NumberField.mixedEmbedding.norm_eq_norm]
    exact mixedEmbedding_norm_ringOfIntegers a
  have hlogNorm : Real.log (|Algebra.norm ℚ (a : K)| : ℚ) = N := by
    rw [hnormQ]
  have hsumAll' :
      ∑ w : NumberField.InfinitePlace K,
          (w.mult : ℝ) * Real.log (w (a : K)) = N := by
    simpa only [NumberField.mixedEmbedding.fundamentalCone.expMap_symm_apply,
      NumberField.mixedEmbedding.normAtAllPlaces_mixedEmbedding] using
        hsumAll.trans hlogNorm
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsumAll'
  have hsum : l₀ + ∑ w, g w = N := by
    simpa only [l₀, g] using hsumAll'
  have hheightMax : Height.logHeight₁ (a : K) =
      max 0 l₀ + ∑ w, max 0 (g w) := by
    rw [numberField_logHeight_ringOfIntegers_eq_sum,
      Fintype.sum_eq_add_sum_subtype_ne _ w₀]
    rw [natCast_mul_posLog_eq_max_zero w₀.mult
      NumberField.InfinitePlace.mult_pos]
    apply congrArg (fun z : ℝ ↦ max 0 l₀ + z)
    apply Finset.sum_congr rfl
    intro w _hw
    exact natCast_mul_posLog_eq_max_zero w.1.mult
      NumberField.InfinitePlace.mult_pos _
  have hbase : Height.logHeight₁ (a : K) ≤
      N + 2 * ∑ w, |g w| := by
    rw [hheightMax]
    exact max_zero_add_sum_max_zero_le l₀ N g hN hsum
  have hg (w : {w : NumberField.InfinitePlace K // w ≠ w₀}) :
      |g w| ≤
        |NumberField.mixedEmbedding.logMap
          (NumberField.mixedEmbedding K (a : K)) w| + N := by
    have hnorm : NumberField.mixedEmbedding.norm
        (NumberField.mixedEmbedding K (a : K)) =
        ((Algebra.norm ℤ a).natAbs : ℝ) :=
      mixedEmbedding_norm_ringOfIntegers a
    have hDpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) :=
      Nat.cast_pos.mpr Module.finrank_pos
    have hmDnat : w.1.mult ≤ Module.finrank ℚ K := by
      rw [← NumberField.InfinitePlace.sum_mult_eq]
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ w.1)
    have hmD : (w.1.mult : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast hmDnat
    have hratio : (0 : ℝ) ≤
        (w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ := by positivity
    have hratioOne :
        (w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ ≤ 1 := by
      exact mul_inv_le_one_of_le₀ hmD hDpos.le
    have hdecomp : g w =
        NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w +
          ((w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹) * N := by
      rw [NumberField.mixedEmbedding.logMap_apply,
        NumberField.mixedEmbedding.normAtPlace_apply, hnorm]
      dsimp only [g, N]
      ring
    rw [hdecomp]
    calc
      |NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w +
          ((w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹) * N| ≤
          |NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w| +
            |((w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹) * N| :=
        abs_add_le _ _
      _ = |NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w| +
          ((w.1.mult : ℝ) * (Module.finrank ℚ K : ℝ)⁻¹) * N := by
        rw [abs_of_nonneg (mul_nonneg hratio hN)]
      _ ≤ |NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w| + N := by
        gcongr
        exact mul_le_of_le_one_left hN hratioOne
  calc
    Height.logHeight₁ (a : K) ≤ N + 2 * ∑ w, |g w| := hbase
    _ ≤ N + 2 * ∑ w,
        (|NumberField.mixedEmbedding.logMap
            (NumberField.mixedEmbedding K (a : K)) w| + N) := by
      gcongr with w
      exact hg w
    _ ≤ N + 2 * ∑ _w : {w : NumberField.InfinitePlace K // w ≠ w₀},
        (C + N) := by
      gcongr with w
      exact hC w
    _ = Real.log ((Algebra.norm ℤ a).natAbs : ℝ) +
        2 * ∑ _w : {w : NumberField.InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          (C + Real.log ((Algebra.norm ℤ a).natAbs : ℝ)) := rfl

noncomputable def test_numberFieldPrimeClassBoundedGenerator
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    NumberField.RingOfIntegers K :=
  Classical.choose
    (test_exists_numberFieldPrimeClassGenerator_bounded_logMap hB v)

lemma test_numberFieldPrimeClassBoundedGenerator_ne_zero
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    test_numberFieldPrimeClassBoundedGenerator hB v ≠ 0 :=
  (Classical.choose_spec
    (test_exists_numberFieldPrimeClassGenerator_bounded_logMap hB v)).1

lemma test_numberFieldPrimeClassBoundedGenerator_span
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.asIdeal ^ NumberField.classNumber K =
      Ideal.span {test_numberFieldPrimeClassBoundedGenerator hB v} :=
  (Classical.choose_spec
    (test_exists_numberFieldPrimeClassGenerator_bounded_logMap hB v)).2.1

lemma test_numberFieldPrimeClassBoundedGenerator_logMap_le
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (w : {w : NumberField.InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    |NumberField.mixedEmbedding.logMap
      (NumberField.mixedEmbedding K
        (test_numberFieldPrimeClassBoundedGenerator hB v : K)) w| ≤
      (NumberField.Units.rank K : ℝ) *
        BoundedUnits.commonBoundedUnitLogBound (K := K) B :=
  (Classical.choose_spec
    (test_exists_numberFieldPrimeClassGenerator_bounded_logMap hB v)).2.2 w

lemma test_numberFieldPrimeClassBoundedGenerator_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    (Algebra.norm ℤ
      (test_numberFieldPrimeClassBoundedGenerator hB v)).natAbs =
        v.asIdeal.absNorm ^ NumberField.classNumber K := by
  calc
    (Algebra.norm ℤ
        (test_numberFieldPrimeClassBoundedGenerator hB v)).natAbs =
        Ideal.absNorm
          (Ideal.span {test_numberFieldPrimeClassBoundedGenerator hB v}) :=
      (Ideal.absNorm_span_singleton _).symm
    _ = Ideal.absNorm
          (v.asIdeal ^ NumberField.classNumber K) := by
      rw [test_numberFieldPrimeClassBoundedGenerator_span]
    _ = v.asIdeal.absNorm ^ NumberField.classNumber K := by rw [map_pow]

theorem test_numberFieldPrimeClassBoundedGenerator_logHeight_le
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    Height.logHeight₁
        ((test_numberFieldPrimeClassBoundedGenerator hB v :
          NumberField.RingOfIntegers K) : K) ≤
      2 * (NumberField.Units.rank K : ℝ) ^ 2 *
          BoundedUnits.commonBoundedUnitLogBound (K := K) B +
        ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
          Real.log
            ((v.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) := by
  have h := test_numberField_logHeight_le_of_abs_logMap_le
    (test_numberFieldPrimeClassBoundedGenerator hB v)
    (test_numberFieldPrimeClassBoundedGenerator_ne_zero hB v)
    ((NumberField.Units.rank K : ℝ) *
      BoundedUnits.commonBoundedUnitLogBound (K := K) B)
    (test_numberFieldPrimeClassBoundedGenerator_logMap_le hB v)
  rw [test_numberFieldPrimeClassBoundedGenerator_norm hB v] at h
  have hcard : Fintype.card {w : NumberField.InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      NumberField.Units.rank K := by
    simpa using
      (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  have hunivcard : (Finset.univ : Finset
      {w : NumberField.InfinitePlace K //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}).card =
      NumberField.Units.rank K := by simpa using hcard
  calc
    Height.logHeight₁
        ((test_numberFieldPrimeClassBoundedGenerator hB v :
          NumberField.RingOfIntegers K) : K) ≤
      Real.log
          ((v.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) +
        2 * ∑ _w : {w : NumberField.InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          ((NumberField.Units.rank K : ℝ) *
              BoundedUnits.commonBoundedUnitLogBound (K := K) B +
            Real.log
              ((v.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ)) := h
    _ = 2 * (NumberField.Units.rank K : ℝ) ^ 2 *
          BoundedUnits.commonBoundedUnitLogBound (K := K) B +
        ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
          Real.log
            ((v.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, hunivcard,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring

lemma test_numberFieldPrimeClassBoundedGenerator_valuation_self
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    v.valuation K (test_numberFieldPrimeClassBoundedGenerator hB v : K) =
      WithZero.exp (-(NumberField.classNumber K : ℤ)) := by
  rw [v.valuation_of_algebraMap,
    v.intValuation_eq_exp_neg_multiplicity
      (test_numberFieldPrimeClassBoundedGenerator_ne_zero hB v),
    ← test_numberFieldPrimeClassBoundedGenerator_span hB v]
  rw [multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime v.ne_bot v.isPrime)]

noncomputable def test_numberFieldPrimeClassBoundedUnit
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) : Kˣ :=
  Units.mk0 (test_numberFieldPrimeClassBoundedGenerator hB v : K)
    (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr
      (test_numberFieldPrimeClassBoundedGenerator_ne_zero hB v))

lemma test_numberFieldPrimeClassBoundedUnit_mem_singleton_supportedUnits
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    test_numberFieldPrimeClassBoundedUnit hB v ∈ ({v} : Set
      (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K := by
  intro w hw
  change w.valuation K
    ((test_numberFieldPrimeClassBoundedGenerator hB v :
      NumberField.RingOfIntegers K) : K) = 1
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hmem
  have hpowle : v.asIdeal ^ NumberField.classNumber K ≤ w.asIdeal := by
    rw [test_numberFieldPrimeClassBoundedGenerator_span hB v]
    exact (Ideal.span_singleton_le_iff_mem w.asIdeal).mpr hmem
  have hvle : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hpowle
  have hideals : v.asIdeal = w.asIdeal :=
    Ideal.IsMaximal.eq_of_le inferInstance w.isPrime.ne_top hvle
  have hvw : v = w := IsDedekindDomain.HeightOneSpectrum.ext hideals
  exact hw (by simpa only [Set.mem_singleton_iff] using hvw.symm)

lemma test_numberFieldPrimeClassBoundedUnit_mem_supportedUnits
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))}
    {v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)} (hv : v ∈ S) :
    test_numberFieldPrimeClassBoundedUnit hB v ∈ S.unit K := by
  intro w hw
  exact test_numberFieldPrimeClassBoundedUnit_mem_singleton_supportedUnits
    hB v w (by
      show w ≠ v
      intro hwv
      exact hw (hwv ▸ hv))

noncomputable def test_numberFieldPrimeClassBoundedSupportedUnit
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v : S) : S.unit K :=
  ⟨test_numberFieldPrimeClassBoundedUnit hB v,
    test_numberFieldPrimeClassBoundedUnit_mem_supportedUnits hB v.property⟩

theorem test_numberFieldPrimeClassBoundedSupportedUnit_logHeight_le
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v : S) :
    Height.logHeight₁
        ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K)) ≤
      2 * (NumberField.Units.rank K : ℝ) ^ 2 *
          BoundedUnits.commonBoundedUnitLogBound (K := K) B +
        ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
          Real.log
            ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) := by
  simpa [test_numberFieldPrimeClassBoundedSupportedUnit,
    test_numberFieldPrimeClassBoundedUnit] using
    test_numberFieldPrimeClassBoundedGenerator_logHeight_le hB v.1

lemma test_valuationMap_numberFieldPrimeClassBoundedSupportedUnit_self
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v : S) :
    SupportedUnits.valuationMap S K
        (test_numberFieldPrimeClassBoundedSupportedUnit hB S v) v =
      Multiplicative.ofAdd (-(NumberField.classNumber K : ℤ)) := by
  rw [SupportedUnits.valuationMap_apply]
  apply WithZero.coe_injective
  rw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
  simpa [test_numberFieldPrimeClassBoundedSupportedUnit,
    test_numberFieldPrimeClassBoundedUnit,
    WithZero.exp_eq_coe_ofAdd] using
      test_numberFieldPrimeClassBoundedGenerator_valuation_self hB v.1

lemma test_valuationMap_numberFieldPrimeClassBoundedSupportedUnit_of_ne
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v w : S) (hvw : w ≠ v) :
    SupportedUnits.valuationMap S K
        (test_numberFieldPrimeClassBoundedSupportedUnit hB S v) w = 1 := by
  rw [SupportedUnits.valuationMap_apply,
    SupportedUnits.valuationOfNeZero_eq_one_iff]
  exact test_numberFieldPrimeClassBoundedUnit_mem_singleton_supportedUnits
    hB v.1 w.1 (by
      show w.1 ≠ v.1
      intro h
      exact hvw (Subtype.ext h))

lemma test_valuationMap_numberFieldPrimeClassBoundedSupportedUnit_apply
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v w : S) :
    SupportedUnits.valuationMap S K
        (test_numberFieldPrimeClassBoundedSupportedUnit hB S v) w =
      if w = v then
        Multiplicative.ofAdd (-(NumberField.classNumber K : ℤ)) else 1 := by
  by_cases h : w = v
  · subst w
    rw [if_pos rfl]
    exact test_valuationMap_numberFieldPrimeClassBoundedSupportedUnit_self hB S v
  · rw [if_neg h]
    exact test_valuationMap_numberFieldPrimeClassBoundedSupportedUnit_of_ne
      hB S v w h

noncomputable def test_numberFieldPrimeClassBoundedSupportedUnitProduct
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (e : S → ℤ) : S.unit K :=
  ∏ v : S, test_numberFieldPrimeClassBoundedSupportedUnit hB S v ^ e v

lemma test_valuationMap_numberFieldPrimeClassBoundedSupportedUnitProduct_apply
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (e : S → ℤ) (w : S) :
    SupportedUnits.valuationMap S K
        (test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e) w =
      Multiplicative.ofAdd (-(NumberField.classNumber K : ℤ) * e w) := by
  rw [test_numberFieldPrimeClassBoundedSupportedUnitProduct, map_prod]
  simp_rw [map_zpow]
  simp only [Finset.prod_apply]
  calc
    ∏ v : S,
        SupportedUnits.valuationMap S K
          (test_numberFieldPrimeClassBoundedSupportedUnit hB S v) w ^ e v =
        SupportedUnits.valuationMap S K
          (test_numberFieldPrimeClassBoundedSupportedUnit hB S w) w ^ e w := by
      apply Finset.prod_eq_single_of_mem w (Finset.mem_univ w)
      intro v _hv hvw
      rw [test_valuationMap_numberFieldPrimeClassBoundedSupportedUnit_apply,
        if_neg (Ne.symm hvw), one_zpow]
    _ = Multiplicative.ofAdd (-(NumberField.classNumber K : ℤ)) ^ e w := by
      rw [test_valuationMap_numberFieldPrimeClassBoundedSupportedUnit_self]
    _ = Multiplicative.ofAdd
        (-(NumberField.classNumber K : ℤ) * e w) := by
      exact (Int.ofAdd_mul _ _).symm

theorem test_exists_boundedPrimeClassProduct_mul_emptySupportedUnit_eq_pow
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S] (u : S.unit K) :
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K),
      (u : Kˣ) ^ NumberField.classNumber K =
          (test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e : Kˣ) *
            (q : Kˣ) ∧
        ∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd := by
  let e : S → ℤ := fun v ↦ -(SupportedUnits.valuationMap S K u v).toAdd
  let g : S.unit K :=
    test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e
  let qS : S.unit K := u ^ NumberField.classNumber K / g
  have hqval : SupportedUnits.valuationMap S K qS = 1 := by
    ext w
    simp only [qS, map_div, map_pow, Pi.div_apply, Pi.pow_apply,
      Pi.one_apply, g]
    rw [test_valuationMap_numberFieldPrimeClassBoundedSupportedUnitProduct_apply]
    simp only [toAdd_div, Int.toAdd_pow, toAdd_ofAdd, toAdd_one, e]
    ring
  have hqempty : (qS : Kˣ) ∈
      (∅ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K := by
    intro v _hvEmpty
    by_cases hvS : v ∈ S
    · have hv := congrFun hqval ⟨v, hvS⟩
      rw [SupportedUnits.valuationMap_apply, Pi.one_apply,
        SupportedUnits.valuationOfNeZero_eq_one_iff] at hv
      exact hv
    · exact qS.property v hvS
  let q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K := ⟨(qS : Kˣ), hqempty⟩
  have heqS : u ^ NumberField.classNumber K = g * qS := by simp [qS]
  refine ⟨e, q, ?_, fun v ↦ rfl⟩
  simpa [g, q] using congrArg (fun z : S.unit K ↦ (z : Kˣ)) heqS

noncomputable def test_boundedPrimeClassHeightMajorant
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (B J : ℕ) : ℝ :=
  2 * (NumberField.Units.rank K : ℝ) ^ 2 *
      BoundedUnits.commonBoundedUnitLogBound (K := K) B +
    ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) *
      ((NumberField.classNumber K : ℝ) * (8 * Real.log (J : ℝ)))

lemma test_boundedPrimeClassHeightMajorant_nonneg
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (B : ℕ) {J : ℕ} (hJ : 1 ≤ J)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    0 ≤ test_boundedPrimeClassHeightMajorant K B J := by
  unfold test_boundedPrimeClassHeightMajorant
  have hlogJ : 0 ≤ Real.log (J : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hJ)
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (BoundedUnits.commonBoundedUnitLogBound_nonneg hB))
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hlogJ)))

theorem test_numberFieldPrimeClassBoundedSupportedUnit_logHeight_le_of_absNorm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) (v : S) {J : ℕ}
    (hvJ : v.1.asIdeal.absNorm ≤ J ^ 8) :
    Height.logHeight₁
        ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K)) ≤
      test_boundedPrimeClassHeightMajorant K B J := by
  have hbase := test_numberFieldPrimeClassBoundedSupportedUnit_logHeight_le hB S v
  have hlog : Real.log
      ((v.1.asIdeal.absNorm ^ NumberField.classNumber K : ℕ) : ℝ) ≤
        (NumberField.classNumber K : ℝ) * (8 * Real.log (J : ℝ)) :=
    log_nat_pow_le_class_mul_eight_log
      (Nat.zero_lt_one.trans
        (NumberField.HeightOneSpectrum.one_lt_absNorm v.1)) hvJ
  have hcoef : 0 ≤ ((2 * NumberField.Units.rank K + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  exact hbase.trans (by
    unfold test_boundedPrimeClassHeightMajorant
    exact add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left hlog hcoef))

theorem test_numberField_bounded_finite_generator_sum_le_of_pow_coordinate
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (e : S → ℤ) {J : ℕ} (hJ : 1 ≤ J)
    (hcoord : ∀ v, 2 ^ (e v).natAbs ≤ J ^ 16)
    (hSJ : ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8) :
    ∑ v, (e v).natAbs * Height.logHeight₁
        ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K)) ≤
      ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        test_boundedPrimeClassHeightMajorant K B J := by
  let C := test_boundedPrimeClassHeightMajorant K B J
  have hC : 0 ≤ C :=
    test_boundedPrimeClassHeightMajorant_nonneg K B hJ hB
  calc
    ∑ v, (e v).natAbs * Height.logHeight₁
        ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K)) ≤
      ∑ v, ((e v).natAbs : ℝ) * C := by
        apply Finset.sum_le_sum
        intro v _hv
        exact mul_le_mul_of_nonneg_left
          (test_numberFieldPrimeClassBoundedSupportedUnit_logHeight_le_of_absNorm
            hB S v (hSJ v)) (by positivity)
    _ ≤ ∑ _v : S, (J ^ 16 : ℝ) * C := by
        apply Finset.sum_le_sum
        intro v _hv
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast natAbs_le_of_two_pow_le (hcoord v)) hC
    _ = ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        test_boundedPrimeClassHeightMajorant K B J := by simp [C]; ring

theorem test_numberField_boundedPrimeClassProduct_logHeight_le_of_pow_coordinate
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (e : S → ℤ) {J : ℕ} (hJ : 1 ≤ J)
    (hcoord : ∀ v, 2 ^ (e v).natAbs ≤ J ^ 16)
    (hSJ : ∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8) :
    Height.logHeight₁
        (((test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e : Kˣ) : K)) ≤
      ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        test_boundedPrimeClassHeightMajorant K B J := by
  let p : S → K := fun v ↦
    (((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K)
  have hprod := numberField_logHeight_zpow_prod_le K p e
  have hsum := test_numberField_bounded_finite_generator_sum_le_of_pow_coordinate
    hB S e hJ hcoord hSJ
  have hprod' : Height.logHeight₁
        (((test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e : Kˣ) : K)) ≤
      ∑ v, (e v).natAbs * Height.logHeight₁ (p v) := by
    simpa [test_numberFieldPrimeClassBoundedSupportedUnitProduct, p] using hprod
  exact hprod'.trans hsum

lemma test_numberField_boundedResidualOrdinaryUnit_logHeight_le
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (e : S → ℤ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (hpow : (u : Kˣ) ^ NumberField.classNumber K =
      (test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e : Kˣ) *
        (q : Kˣ)) :
    Height.logHeight₁
        ((((SupportedUnits.emptyEquivUnits K q) :
          NumberField.RingOfIntegers K) : K)) ≤
      (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) +
        ∑ v, (e v).natAbs * Height.logHeight₁
          ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K)) := by
  let g : Kˣ := test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e
  have hqUnits : (q : Kˣ) = g⁻¹ * (u : Kˣ) ^ NumberField.classNumber K := by
    rw [hpow]
    simp [g]
  have hmap : Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom
        (SupportedUnits.emptyEquivUnits K q) = (q : Kˣ) :=
    SupportedUnits.unitsMap_emptyEquivUnits
      (R := NumberField.RingOfIntegers K) K q
  have hqK := congrArg (fun z : Kˣ ↦ (z : K)) hqUnits
  have hmapK' :
      (((SupportedUnits.emptyEquivUnits K q) :
        NumberField.RingOfIntegers K) : K) = (((q : Kˣ) : K)) := by
    change algebraMap (NumberField.RingOfIntegers K) K
      (((SupportedUnits.emptyEquivUnits K q) :
        (NumberField.RingOfIntegers K)ˣ) : NumberField.RingOfIntegers K) =
          (((q : Kˣ) : K))
    exact congrArg Units.val hmap
  have hqValue :
      (((SupportedUnits.emptyEquivUnits K q) :
        NumberField.RingOfIntegers K) : K) =
        (g : K)⁻¹ * (((u : Kˣ) : K)) ^ NumberField.classNumber K := by
    rw [hmapK']
    simpa using hqK
  rw [hqValue]
  calc
    Height.logHeight₁
        ((g : K)⁻¹ * (((u : Kˣ) : K)) ^ NumberField.classNumber K) ≤
      Height.logHeight₁ ((g : K)⁻¹) +
        Height.logHeight₁
          ((((u : Kˣ) : K)) ^ NumberField.classNumber K) :=
      Height.logHeight₁_mul_le _ _
    _ = Height.logHeight₁ (g : K) +
        (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) := by
      rw [Height.logHeight₁_inv, Height.logHeight₁_pow]
    _ ≤ (∑ v, (e v).natAbs * Height.logHeight₁
          ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K))) +
        (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) := by
      gcongr
      simpa [g, test_numberFieldPrimeClassBoundedSupportedUnitProduct] using
        numberField_logHeight_zpow_prod_le K
          (fun v : S ↦
            (((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K)) e
    _ = (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((u : Kˣ) : K)) +
        ∑ v, (e v).natAbs * Height.logHeight₁
          ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K)) := by
      ring

theorem test_numberField_supportedUnit_controlled_decomposition_at
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))) [Fintype S]
    (u : S.unit K) (hdeg : Module.finrank ℚ K ≤ 8) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B) :
    ∃ (e : S → ℤ)
        (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K))).unit K)
        (ζ : NumberField.Units.torsion K)
        (a : Fin (NumberField.Units.rank K) →₀ ℤ),
      (u : Kˣ) ^ NumberField.classNumber K =
          (test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e : Kˣ) *
            (q : Kˣ) ∧
        (∀ v, e v = -(SupportedUnits.valuationMap S K u v).toAdd) ∧
        (BoundedUnits.boundedUnitSubgroup hB).index ≤
          BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B ∧
        (SupportedUnits.emptyEquivUnits K q) ^
            (BoundedUnits.boundedUnitSubgroup hB).index =
          ζ.1 * a.prod (fun i z ↦ BoundedUnits.boundedFundSystem hB i ^ z) ∧
        let Q :=
          (NumberField.classNumber K : ℝ) *
              Height.logHeight₁ (((u : Kˣ) : K)) +
            ∑ v, (e v).natAbs * Height.logHeight₁
              ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K))
        ∀ i,
          |((a i : ℤ) : ℝ)| ≤
            ((NumberField.Units.rank K).factorial *
              (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
                ((BoundedUnits.boundedUnitIndexUpper (K := K)
                    (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
                  (2 * Q))) ^ NumberField.Units.rank K) /
              (totallyRealDegreeEightUnitLogGap / 8) ^
                NumberField.Units.rank K := by
  classical
  obtain ⟨e, q, hpow, he⟩ :=
    test_exists_boundedPrimeClassProduct_mul_emptySupportedUnit_eq_pow hB S u
  let Q : ℝ :=
    (NumberField.classNumber K : ℝ) *
        Height.logHeight₁ (((u : Kˣ) : K)) +
      ∑ v, (e v).natAbs * Height.logHeight₁
        ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K))
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Height.zero_le_logHeight₁ _))
      (Finset.sum_nonneg fun v _ ↦
        mul_nonneg (Nat.cast_nonneg _) (Height.zero_le_logHeight₁ _))
  have hqHeight : Height.logHeight₁
      ((((SupportedUnits.emptyEquivUnits K q) :
        NumberField.RingOfIntegers K) : K)) ≤ Q :=
    test_numberField_boundedResidualOrdinaryUnit_logHeight_le hB S u e q hpow
  obtain ⟨hindex, ζ, a, hdecomp, ha⟩ :=
    degreeEight_boundedUnitDecompositionData_at_of_logHeight
      K hdeg hB (SupportedUnits.emptyEquivUnits K q) hQ hqHeight
  exact ⟨e, q, ζ, a, hpow, he, hindex, hdecomp, by simpa [Q] using ha⟩

theorem supportedUnit_powered_bounded_product_of_hpow
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (u P : Kˣ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : u ^ NumberField.classNumber K = P * (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    u ^ (NumberField.classNumber K *
        (BoundedUnits.boundedUnitSubgroup hB).index) =
      P ^ (BoundedUnits.boundedUnitSubgroup hB).index *
        Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1 *
        a.prod (fun i z ↦
          (Units.map (algebraMap
            (NumberField.RingOfIntegers K) K).toMonoidHom
              (BoundedUnits.boundedFundSystem hB i)) ^ z) := by
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  have hqmap :
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (SupportedUnits.emptyEquivUnits K q) = (q : Kˣ) :=
    SupportedUnits.unitsMap_emptyEquivUnits
      (R := NumberField.RingOfIntegers K) K q
  have hdecompK := congrArg
    (Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom) hdecomp
  simp only [map_pow, hqmap, map_mul, map_finsuppProd, map_zpow] at hdecompK
  calc
    u ^ (NumberField.classNumber K * I) =
        (u ^ NumberField.classNumber K) ^ I := by rw [pow_mul]
    _ = (P * (q : Kˣ)) ^ I := by rw [hpow]
    _ = P ^ I * (q : Kˣ) ^ I := mul_pow _ _ _
    _ = P ^ I *
        (Units.map (algebraMap
          (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1 *
          a.prod (fun i z ↦
            (Units.map (algebraMap
              (NumberField.RingOfIntegers K) K).toMonoidHom
                (BoundedUnits.boundedFundSystem hB i)) ^ z)) := by
      rw [hdecompK]
    _ = _ := by simp [I, mul_assoc]

theorem supportedUnit_powered_bounded_product_torsion_free_of_hpow
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (u P : Kˣ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : u ^ NumberField.classNumber K = P * (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    u ^ ((NumberField.classNumber K *
        (BoundedUnits.boundedUnitSubgroup hB).index) * 2) =
      P ^ ((BoundedUnits.boundedUnitSubgroup hB).index * 2) *
        (a.prod (fun i z ↦
          (Units.map (algebraMap
            (NumberField.RingOfIntegers K) K).toMonoidHom
              (BoundedUnits.boundedFundSystem hB i)) ^ z)) ^ 2 := by
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let Z : Kˣ :=
    Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom ζ.1
  let G : Kˣ :=
    a.prod (fun i z ↦
      (Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)) ^ z)
  have hbase := supportedUnit_powered_bounded_product_of_hpow
    u P q B hB ζ a hpow hdecomp
  have hZ : Z ^ 2 = 1 := by
    dsimp [Z]
    rw [← map_pow]
    rw [totallyReal_torsion_sq_eq_one ζ, map_one]
  calc
    u ^ ((NumberField.classNumber K * I) * 2) =
        (u ^ (NumberField.classNumber K * I)) ^ 2 := by rw [pow_mul]
    _ = (P ^ I * Z * G) ^ 2 := by rw [hbase]
    _ = P ^ (I * 2) * G ^ 2 := by
      rw [mul_pow, mul_pow, hZ, mul_one, pow_mul]
    _ = _ := by rfl

theorem supportedUnit_ratio_two_power_eq_combined_product_of_hpow
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (u ratio P : Kˣ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : u ^ NumberField.classNumber K = P * (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)
    let W : Kˣ :=
      (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
    (ratio * u) ^ ((NumberField.classNumber K * I) * 2) =
      ∏ i, combinedSquaredProductBases W eps i ^
        combinedSquaredProductCoefficients a i := by
  dsimp only
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  have hU := supportedUnit_powered_bounded_product_torsion_free_of_hpow
    u P q B hB ζ a hpow hdecomp
  exact two_power_eq_combined_product ratio u P a eps
    (by simpa only [I, eps] using hU)

theorem supportedUnit_ratio_two_power_eq_combined_product_field_of_hpow
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (u ratio P : Kˣ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : u ^ NumberField.classNumber K = P * (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z)) :
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
      Units.map (algebraMap
        (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i)
    let W : Kˣ :=
      (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
    (((ratio * u : Kˣ) : K)) ^
        ((NumberField.classNumber K * I) * 2) =
      ∏ i, combinedSquaredProductBases (W : K)
          (fun j ↦ (eps j : K)) i ^
        combinedSquaredProductCoefficients a i := by
  dsimp only
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let eps : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map (algebraMap
      (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  let W : Kˣ :=
    (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
  have h := supportedUnit_ratio_two_power_eq_combined_product_of_hpow
    u ratio P q B hB ζ a hpow hdecomp
  exact combinedProduct_units_coe W (ratio * u) eps a
    (by simpa only [I, eps, W] using h)

theorem supportedUnit_combined_real_log_lower_dichotomy_of_hpow
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Fintype ι]
    (basis : Module.Basis ι ℚ K) (hbasis : ∀ i, IsIntegral ℤ (basis i))
    (φ : K →+* ℂ) (ρ : K →+* ℝ) (hφρ : ∀ x, φ x = (ρ x : ℂ))
    (u ratio P : Kˣ)
    (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))).unit K)
    (B0 Ba : ℕ)
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B0)
    (ζ : NumberField.Units.torsion K)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (hpow : u ^ NumberField.classNumber K = P * (q : Kˣ))
    (hdecomp : (SupportedUnits.emptyEquivUnits K q) ^
          (BoundedUnits.boundedUnitSubgroup hB).index =
        ζ.1 * a.prod (fun i z ↦
          BoundedUnits.boundedFundSystem hB i ^ z))
    (QW M : ℝ) (hd : Module.finrank ℚ K ≤ 8) (hM : 1 ≤ M)
    (hMbasis : ∀ i (ψ : K →ₐ[ℚ] ℂ), ‖ψ (basis i)‖ ≤ M)
    (hBa : 1 ≤ Ba) (ha : ∀ i, (a i).natAbs ≤ Ba)
    (hWheight : Height.logHeight₁
      ((((ratio ^ 2) ^
          (NumberField.classNumber K *
            (BoundedUnits.boundedUnitSubgroup hB).index) *
        (P ^ 2) ^
          (BoundedUnits.boundedUnitSubgroup hB).index : Kˣ) : K)) ≤ QW)
    (hzne :
      (((ratio * u) ^
        ((NumberField.classNumber K *
          (BoundedUnits.boundedUnitSubgroup hB).index) * 2)) ^
        (2 * (BoundedUnits.boundedUnitSubgroup hB).index)) ≠ 1) :
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
      ((Units.map
        (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
          (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
    let W : Kˣ :=
      (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
    let z : K := ((ratio * u : Kˣ) : K)
    let m := (NumberField.classNumber K * I) * 2
    let alphaNon := combinedSquaredProductBases (W : K) eps
    let ellNon : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
      Complex.log (φ (alphaNon i))
    (W ∉ integerUnitSubgroup K ∧
      LinearForms.structuredBoxLogarithmicFormThreshold Ba
          (LinearForms.structuredBoxMasterL Ba M alphaNon ellNon)
          M alphaNon ellNon ≤ |Real.log (ρ (z ^ m))|) ∨
    ∃ (c : Fin (NumberField.Units.rank K) →₀ ℤ)
        (reindex : Fin (NumberField.Units.rank K - 1 + 1) ≃
          Fin (NumberField.Units.rank K)),
      W ∈ integerUnitSubgroup K ∧
      let b : Fin (NumberField.Units.rank K) → ℤ := fun i ↦
        c i + ((2 * I : ℕ) : ℤ) * a i
      let alphaUnit : Fin (NumberField.Units.rank K) → K := fun i ↦ eps i ^ 2
      let ellUnit : Fin (NumberField.Units.rank K) → ℂ := fun i ↦
        Complex.log (φ (alphaUnit i))
      LinearForms.structuredBoxLogarithmicFormThreshold
          (integerUnitAbsorptionNatBound K hB QW Ba)
          (LinearForms.structuredBoxMasterL
            (integerUnitAbsorptionNatBound K hB QW Ba) M
            (fun i ↦ alphaUnit (reindex i))
            (fun i ↦ ellUnit (reindex i))) M
          (fun i ↦ alphaUnit (reindex i))
          (fun i ↦ ellUnit (reindex i)) ≤
        |Real.log (ρ ((z ^ m) ^ (2 * I)))| := by
  dsimp only
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let epsU : Fin (NumberField.Units.rank K) → Kˣ := fun i ↦
    Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i)
  let eps : Fin (NumberField.Units.rank K) → K := fun i ↦ (epsU i : K)
  let W : Kˣ :=
    (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
  let zU : Kˣ := ratio * u
  let z : K := (zU : K)
  let m := (NumberField.classNumber K * I) * 2
  have hcombined := supportedUnit_ratio_two_power_eq_combined_product_of_hpow
    u ratio P q B0 hB ζ a hpow hdecomp
  have hcombined' : zU ^ m = ∏ i,
      combinedSquaredProductBases W epsU i ^
        combinedSquaredProductCoefficients a i := by
    simpa only [I, W, epsU, zU, m] using hcombined
  by_cases hW : W ∈ integerUnitSubgroup K
  · right
    have hprod : zU ^ m = W * ∏ i, (epsU i ^ 2) ^ (a i) := by
      rw [hcombined', prod_combinedSquaredProductBases_zpow]
    have hWh : Height.logHeight₁ (W : K) ≤ QW := by
      simpa only [W, I] using hWheight
    obtain ⟨c, hcprod, hcbound⟩ :=
      integerUnit_powered_product_eq_bounded_squares_with_bound
        hd hB W zU a hW hWh hprod
    let b : Fin (NumberField.Units.rank K) → ℤ := fun i ↦
      c i + ((2 * I : ℕ) : ℤ) * a i
    have hcbound' : ∀ i, |((c i : ℤ) : ℝ)| ≤
        integerUnitAbsorptionRealBound K hB QW := by
      simpa [integerUnitAbsorptionRealBound] using hcbound
    have hb : ∀ i, (b i).natAbs ≤
        integerUnitAbsorptionNatBound K hB QW Ba := by
      intro i
      exact integerUnitAbsorptionCoefficient_natAbs_le hB c a hcbound' ha i
    have hbne : b ≠ 0 := by
      apply absorbedCoefficient_ne_zero hB zU a c
      · simpa only [I, epsU, b] using hcprod
      · simpa only [I, m, zU] using hzne
    have hfield := squaredUnitsProduct_coe (zU ^ m) epsU b
      (by simpa only [I, epsU, b] using hcprod)
    obtain ⟨reindex, hlower⟩ := integerUnit_bounded_real_log_lower_bound
      basis hbasis φ ρ hφρ hB b (z ^ m) M hd hM hMbasis hb hbne
        (by simpa [z, zU, epsU] using hfield)
    exact ⟨c, reindex, hW, by
      simpa only [b, eps, epsU, I, z, zU, m] using hlower⟩
  · left
    have hfield := supportedUnit_ratio_two_power_eq_combined_product_field_of_hpow
      u ratio P q B0 hB ζ a hpow hdecomp
    have hWpos : 0 < ρ (W : K) := by
      exact combinedLeadingFactor_positive ρ (ratio : K) (P : K)
        (NumberField.classNumber K) I (Units.ne_zero _) (Units.ne_zero _)
    refine ⟨hW, ?_⟩
    exact nonintegerUnit_combined_real_log_lower_bound
      basis hbasis φ ρ hφρ hB W hW a z M hd hM hMbasis hBa ha hWpos
        (by simpa only [I, W, eps, epsU, z, zU, m] using hfield)

/-- The exact two-branch conclusion of the fixed-rank logarithmic-form
argument, packaged so the concrete Pell-field construction can retain every
parameter needed for the subsequent explicit estimates. -/
noncomputable def SupportedUnitControlledCombinedRealLogDichotomy
    {K ι : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Fintype ι]
    (basis : Module.Basis ι ℚ K) (φ : K →+* ℂ) (ρ : K →+* ℝ)
    {S : Set (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))} [Fintype S]
    (u : S.unit K) (ratio P : Kˣ) {B : ℕ}
    (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B)
    (a : Fin (NumberField.Units.rank K) →₀ ℤ)
    (Ba : ℕ) (QW M : ℝ) : Prop :=
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let eps : Fin (NumberField.Units.rank K) → K := fun i ↦
    ((Units.map
      (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom
        (BoundedUnits.boundedFundSystem hB i) : Kˣ) : K)
  let W : Kˣ :=
    (ratio ^ 2) ^ (NumberField.classNumber K * I) * (P ^ 2) ^ I
  let z : K := ((ratio * (u : Kˣ) : Kˣ) : K)
  let m := (NumberField.classNumber K * I) * 2
  let alphaNon := combinedSquaredProductBases (W : K) eps
  let ellNon : Fin (NumberField.Units.rank K + 1) → ℂ := fun i ↦
    Complex.log (φ (alphaNon i))
  (W ∉ integerUnitSubgroup K ∧
    LinearForms.structuredBoxLogarithmicFormThreshold Ba
        (LinearForms.structuredBoxMasterL Ba M alphaNon ellNon)
        M alphaNon ellNon ≤ |Real.log (ρ (z ^ m))|) ∨
  ∃ (c : Fin (NumberField.Units.rank K) →₀ ℤ)
      (reindex : Fin (NumberField.Units.rank K - 1 + 1) ≃
        Fin (NumberField.Units.rank K)),
    W ∈ integerUnitSubgroup K ∧
    let alphaUnit : Fin (NumberField.Units.rank K) → K :=
      fun i ↦ eps i ^ 2
    let ellUnit : Fin (NumberField.Units.rank K) → ℂ := fun i ↦
      Complex.log (φ (alphaUnit i))
    LinearForms.structuredBoxLogarithmicFormThreshold
        (integerUnitAbsorptionNatBound K hB QW Ba)
        (LinearForms.structuredBoxMasterL
          (integerUnitAbsorptionNatBound K hB QW Ba) M
          (fun i ↦ alphaUnit (reindex i))
          (fun i ↦ ellUnit (reindex i))) M
        (fun i ↦ alphaUnit (reindex i))
        (fun i ↦ ellUnit (reindex i)) ≤
      |Real.log (ρ ((z ^ m) ^ (2 * I)))|

/-- All algebraic, finite-prime, height, basis, and archimedean data needed
to apply the fixed-rank logarithmic-form theorem to one simultaneous Pell
triple in the concrete positive-real triquadratic field. -/
noncomputable def RealPellControlledArchimedeanData
    (γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ) (β₁₂ β₁₃ : ℤ)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0) : Prop :=
  let K := realPellField γ₁ γ₂ γ₃
  letI : Algebra ℚ K := K.algebra'
  letI : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  letI : NumberField.IsTotallyReal K :=
    realPellFieldIsTotallyReal hγ₁ hγ₂ hγ₃
  let ratio : Kˣ :=
    Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃) /
      Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂)
  let N := (40320 * H ^ 24) ^ 2
  let B := degreeEightMinkowskiNatBound N
  ∃ (S : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))) (U : S.unit K) (hS : S.Finite)
      (ι : Set K) (hι : ι.Finite) (basis : Module.Basis ι ℚ K)
      (e : S → ℤ)
      (q : (∅ : Set (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))).unit K)
      (hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
        NumberField.mixedEmbedding.convexBodyLTFactor K * B)
      (ζ : NumberField.Units.torsion K)
      (a : Fin (NumberField.Units.rank K) →₀ ℤ),
    letI : Fintype S := hS.fintype
    letI : Fintype ι := hι.fintype
    let I := (BoundedUnits.boundedUnitSubgroup hB).index
    let P : Kˣ :=
      test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e
    let QP : ℝ :=
      ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
        test_boundedPrimeClassHeightMajorant K B J
    let Qres : ℝ :=
      (NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((U : Kˣ) : K)) + QP
    let Acoef : ℝ :=
      ((NumberField.Units.rank K).factorial *
        (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
          ((BoundedUnits.boundedUnitIndexUpper (K := K)
              (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
            (2 * Qres))) ^ NumberField.Units.rank K) /
        (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K
    let Ba := max 1 (Nat.ceil Acoef)
    let QW : ℝ :=
      (2 * (NumberField.classNumber K * I) : ℕ) *
          Height.logHeight₁ (ratio : K) + (2 * I : ℕ) * QP
    S = pellCommonPrimeSupport
        (Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂))
        (Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃))
        (Units.mk0 ((β₁₃ - β₁₂ : ℤ) : K)
          (Int.cast_ne_zero.mpr hβ₂₃)) ∧
    ((U : Kˣ) : K) =
      pellValueMinus (realPellRootOne γ₁ γ₂ γ₃)
          (realPellRootTwo γ₁ γ₂ γ₃) (x₁ : ℤ) (x₂ : ℤ) /
        pellValueMinus (realPellRootOne γ₁ γ₂ γ₃)
          (realPellRootThree γ₁ γ₂ γ₃) (x₁ : ℤ) (x₃ : ℤ) ∧
    realPellRealEmbedding γ₁ γ₂ γ₃
        (((ratio * (U : Kˣ) : Kˣ) : K)) - 1 ≠ 0 ∧
    |realPellRealEmbedding γ₁ γ₂ γ₃
        (((ratio * (U : Kˣ) : Kˣ) : K)) - 1| ≤
      2 * (J : ℝ) / (Real.sqrt γ₁ * x₁) ^ 2 ∧
    (U : Kˣ) ^ NumberField.classNumber K = P * (q : Kˣ) ∧
    (∀ v, e v = -(SupportedUnits.valuationMap S K U v).toAdd) ∧
    (∀ v, 2 ^ (e v).natAbs ≤ J ^ 16) ∧
    (∀ v : S, v.1.asIdeal.absNorm ≤ J ^ 8) ∧
    (BoundedUnits.boundedUnitSubgroup hB).index ≤
      BoundedUnits.boundedUnitIndexUpper (K := K)
        (totallyRealDegreeEightUnitLogGap / 8) B ∧
    (SupportedUnits.emptyEquivUnits K q) ^ I =
      ζ.1 * a.prod (fun i z ↦ BoundedUnits.boundedFundSystem hB i ^ z) ∧
    (∀ i, (a i).natAbs ≤ Ba) ∧
    Height.logHeight₁ (P : K) ≤ QP ∧
    Height.logHeight₁
      ((((ratio ^ 2) ^ (NumberField.classNumber K * I) *
        (P ^ 2) ^ I : Kˣ) : K)) ≤ QW ∧
    (∀ i, IsIntegral ℤ (basis i)) ∧
    (∀ i (w : K →ₐ[ℚ] ℂ), ‖w (basis i)‖ ≤ (H : ℝ) ^ 3) ∧
    SupportedUnitControlledCombinedRealLogDichotomy basis
      (realPellComplexEmbedding γ₁ γ₂ γ₃)
      (realPellRealEmbedding γ₁ γ₂ γ₃) U ratio P hB a Ba QW ((H : ℝ) ^ 3)

/-- The concrete simultaneous-Pell data satisfy the complete fixed-rank
unit/nonunit logarithmic-form dichotomy.  In particular, this theorem joins
the elementary small archimedean gap to the exact same powered supported
unit product used by the auxiliary-function lower bound. -/
theorem realPell_controlled_archimedean_data
    {γ₁ γ₂ γ₃ H x₁ x₂ x₃ J : ℕ} {β₁₂ β₁₃ : ℤ}
    (hPell : SimultaneousPellZ (γ₁ : ℤ) (γ₂ : ℤ) (γ₃ : ℤ)
      β₁₂ β₁₃ (x₁ : ℤ) (x₂ : ℤ) (x₃ : ℤ))
    (hβ₁₂ : β₁₂ ≠ 0) (hβ₁₃ : β₁₃ ≠ 0)
    (hβ₂₃ : β₁₃ - β₁₂ ≠ 0)
    (hJ₁₂ : β₁₂.natAbs ≤ J) (hJ₁₃ : β₁₃.natAbs ≤ J)
    (hJ₂₃ : (β₁₃ - β₁₂).natAbs ≤ J)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ₃ : 0 < γ₃)
    (hγ₁H : γ₁ ≤ H) (hγ₂H : γ₂ ≤ H) (hγ₃H : γ₃ ≤ H)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hx₃ : 0 < x₃)
    (hlarge : 2 * J < γ₁ * x₁ ^ 2) :
    RealPellControlledArchimedeanData γ₁ γ₂ γ₃ H x₁ x₂ x₃ J β₁₂ β₁₃
      hγ₁ hγ₂ hγ₃ hβ₁₂ hβ₁₃ hβ₂₃ := by
  let K := realPellField γ₁ γ₂ γ₃
  let : Algebra ℚ K := K.algebra'
  let : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact real_sqrt_nat_isIntegral γ₁
      · exact real_sqrt_nat_isIntegral γ₂
      · exact real_sqrt_nat_isIntegral γ₃
  let : NumberField K := realPellFieldNumberField γ₁ γ₂ γ₃
  let : NumberField.IsTotallyReal K :=
    realPellFieldIsTotallyReal hγ₁ hγ₂ hγ₃
  let ratio : Kˣ :=
    Units.mk0 (β₁₃ : K) (Int.cast_ne_zero.mpr hβ₁₃) /
      Units.mk0 (β₁₂ : K) (Int.cast_ne_zero.mpr hβ₁₂)
  let r₁ : K := realPellRootOne γ₁ γ₂ γ₃
  let r₂ : K := realPellRootTwo γ₁ γ₂ γ₃
  let r₃ : K := realPellRootThree γ₁ γ₂ γ₃
  have hr₁ : r₁ ^ 2 = (γ₁ : K) := realPellRootOne_sq _ _ _
  have hr₂ : r₂ ^ 2 = (γ₂ : K) := realPellRootTwo_sq _ _ _
  have hr₃ : r₃ ^ 2 = (γ₃ : K) := realPellRootThree_sq _ _ _
  have hdeg : Module.finrank ℚ K ≤ 8 := by
    change Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        ({Real.sqrt γ₁, Real.sqrt γ₂, Real.sqrt γ₃} : Set ℝ)) ≤ 8
    exact finrank_adjoin_three_sqRoots_le_eight
      (Real.sqrt γ₁) (Real.sqrt γ₂) (Real.sqrt γ₃)
      (γ₁ : ℚ) (γ₂ : ℚ) (γ₃ : ℚ)
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₁ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₂ by positivity))
      (by simpa using Real.sq_sqrt (show (0 : ℝ) ≤ γ₃ by positivity))
  obtain ⟨S, U, V, hS, hSdef, hUV, hU, _hV, _hdecomp0,
      hUreal, hgapNe0, hgapAbs0, _hlog⟩ :=
    realPell_supportedUnit_log_gap hPell hβ₁₂ hβ₁₃ hβ₂₃
      hJ₁₂ hJ₁₃ hJ₂₃ hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
      hx₁ hx₂ hx₃ hlarge.le
  let : Fintype S := hS.fintype
  have hcoordNorm := simultaneousPell_common_left_coordinate_pow_le_of_eq
    hr₁ hr₂ hr₃ hPell hβ₁₂ hβ₁₃ hβ₂₃ hdeg J
      hJ₁₂ hJ₁₃ hJ₂₃ S U hSdef (by simpa [r₁, r₂, r₃] using hU)
  rcases hcoordNorm with ⟨hcoordU, hSJ⟩
  let N : ℕ := (40320 * H ^ 24) ^ 2
  let B : ℕ := degreeEightMinkowskiNatBound N
  have hdiscR := realPellField_natAbs_discr_le
    hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
  dsimp only at hdiscR
  have hdisc : |NumberField.discr K| ≤ N := by
    rw [Int.abs_eq_natAbs]
    dsimp [N]
    norm_cast at hdiscR
    exact_mod_cast hdiscR
  have hB : NumberField.mixedEmbedding.minkowskiBound K 1 <
      NumberField.mixedEmbedding.convexBodyLTFactor K * B := by
    simpa [B] using
      (minkowskiBound_lt_degreeEightMinkowskiNatBound K hdeg hdisc)
  obtain ⟨e, q, ζ, a, hpow, he, hindex, hdecomp, ha⟩ :=
    test_numberField_supportedUnit_controlled_decomposition_at K S U hdeg hB
  obtain ⟨ι, hι, basis, hbasis, hMbasis⟩ :=
    exists_threeSqRoot_integral_basis r₁ r₂ r₃ hr₁ hr₂ hr₃
      hγ₁ hγ₂ hγ₃ hγ₁H hγ₂H hγ₃H
      (by exact realPellField_adjoin_roots_eq_top γ₁ γ₂ γ₃)
  let : Fintype ι := hι.fintype
  unfold RealPellControlledArchimedeanData
  dsimp only
  refine ⟨S, U, hS, ι, hι, basis, e, q, hB, ζ, a, ?_⟩
  let I := (BoundedUnits.boundedUnitSubgroup hB).index
  let P : Kˣ :=
    test_numberFieldPrimeClassBoundedSupportedUnitProduct hB S e
  let QP : ℝ :=
    ((Fintype.card S : ℝ) * (J ^ 16 : ℝ)) *
      test_boundedPrimeClassHeightMajorant K B J
  let Qactual : ℝ :=
    (NumberField.classNumber K : ℝ) *
      Height.logHeight₁ (((U : Kˣ) : K)) +
      ∑ v, (e v).natAbs * Height.logHeight₁
        ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K))
  let Qres : ℝ :=
    (NumberField.classNumber K : ℝ) *
        Height.logHeight₁ (((U : Kˣ) : K)) + QP
  let Acoef : ℝ :=
    ((NumberField.Units.rank K).factorial *
      (max (BoundedUnits.commonBoundedUnitLogBound (K := K) B)
        ((BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
          (2 * Qres))) ^ NumberField.Units.rank K) /
      (totallyRealDegreeEightUnitLogGap / 8) ^ NumberField.Units.rank K
  let Ba := max 1 (Nat.ceil Acoef)
  let QW : ℝ :=
    (2 * (NumberField.classNumber K * I) : ℕ) *
        Height.logHeight₁ (ratio : K) + (2 * I : ℕ) * QP
  have hJ : 1 ≤ J := by
    exact (Int.natAbs_pos.mpr hβ₁₂).trans_le hJ₁₂
  have hcoordE : ∀ v, 2 ^ (e v).natAbs ≤ J ^ 16 := by
    intro v
    rw [he v, Int.natAbs_neg]
    exact hcoordU v
  have hPheight : Height.logHeight₁ (P : K) ≤ QP := by
    simpa [P, QP] using
      (test_numberField_boundedPrimeClassProduct_logHeight_le_of_pow_coordinate
        hB S e hJ hcoordE hSJ)
  have hsum :
      (∑ v, (e v).natAbs * Height.logHeight₁
        ((((test_numberFieldPrimeClassBoundedSupportedUnit hB S v) : Kˣ) : K))) ≤ QP := by
    simpa [QP] using
      (test_numberField_bounded_finite_generator_sum_le_of_pow_coordinate
        hB S e hJ hcoordE hSJ)
  have hQactual : Qactual ≤ Qres := by
    dsimp [Qactual, Qres]
    simpa [add_comm] using
      (add_le_add_left hsum
        ((NumberField.classNumber K : ℝ) *
          Height.logHeight₁ (((U : Kˣ) : K))))
  have haAcoef : ∀ i, |((a i : ℤ) : ℝ)| ≤ Acoef := by
    intro i
    refine (ha i).trans ?_
    have hδ : 0 ≤ totallyRealDegreeEightUnitLogGap / 8 :=
      (div_pos totallyRealDegreeEightUnitLogGap_pos (by norm_num)).le
    have htwice : 2 * Qactual ≤ 2 * Qres :=
      mul_le_mul_of_nonneg_left hQactual (by norm_num)
    have hprod :
        (BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
              (2 * Qactual) ≤
          (BoundedUnits.boundedUnitIndexUpper (K := K)
            (totallyRealDegreeEightUnitLogGap / 8) B : ℝ) *
              (2 * Qres) :=
      mul_le_mul_of_nonneg_left htwice (Nat.cast_nonneg _)
    have hmax := max_le_max_left
      (BoundedUnits.commonBoundedUnitLogBound (K := K) B) hprod
    have hpow := pow_le_pow_left₀ (by positivity) hmax
      (NumberField.Units.rank K)
    have hnum := mul_le_mul_of_nonneg_left hpow
      (Nat.cast_nonneg (NumberField.Units.rank K).factorial)
    exact div_le_div_of_nonneg_right hnum
      (pow_nonneg hδ (NumberField.Units.rank K))
  have haNat : ∀ i, (a i).natAbs ≤ Ba := by
    intro i
    have hcast : ((a i).natAbs : ℝ) ≤ Acoef := by
      simpa using haAcoef i
    have hceil : (a i).natAbs ≤ Nat.ceil Acoef := by
      exact_mod_cast hcast.trans (Nat.le_ceil Acoef)
    exact hceil.trans (le_max_right _ _)
  have hBa : 1 ≤ Ba := le_max_left _ _
  have hWheight : Height.logHeight₁
      ((((ratio ^ 2) ^ (NumberField.classNumber K * I) *
        (P ^ 2) ^ I : Kˣ) : K)) ≤ QW := by
    simpa [QW] using
      (combinedLeadingFactor_logHeight_le (ratio : K) (P : K)
        (NumberField.classNumber K) I (le_refl _) hPheight)
  have hratioUreal :
      realPellRealEmbedding γ₁ γ₂ γ₃
          (((ratio * (U : Kˣ) : Kˣ) : K)) =
        (β₁₃ : ℝ) / (β₁₂ : ℝ) * ((((U : Kˣ) : K) : ℝ)) := by
    simp [ratio, realPellRealEmbedding]
  have hgapNe : realPellRealEmbedding γ₁ γ₂ γ₃
      (((ratio * (U : Kˣ) : Kˣ) : K)) - 1 ≠ 0 := by
    rw [hratioUreal]
    exact hgapNe0
  have hgapAbs : |realPellRealEmbedding γ₁ γ₂ γ₃
      (((ratio * (U : Kˣ) : Kˣ) : K)) - 1| ≤
        2 * (J : ℝ) / (Real.sqrt γ₁ * x₁) ^ 2 := by
    rw [hratioUreal]
    exact hgapAbs0
  let zreal : ℝ := realPellRealEmbedding γ₁ γ₂ γ₃
    (((ratio * (U : Kˣ) : Kˣ) : K))
  have hAsq : (Real.sqrt γ₁ * (x₁ : ℝ)) ^ 2 =
      (γ₁ : ℝ) * (x₁ : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsmallR : 2 * (J : ℝ) /
      (Real.sqrt γ₁ * x₁) ^ 2 < 1 := by
    rw [hAsq]
    apply (div_lt_one (by positivity)).2
    exact_mod_cast hlarge
  have hzpos : 0 < zreal := by
    have hzabs : |zreal - 1| < 1 := by
      exact hgapAbs.trans_lt hsmallR
    exact sub_pos.mp ((abs_lt.mp hzabs).1 |> fun h ↦ by linarith)
  have hIne : I ≠ 0 := by
    exact BoundedUnits.boundedUnitSubgroup_index_ne_zero hB
  have hmne : (NumberField.classNumber K * I) * 2 ≠ 0 := by
    exact Nat.mul_ne_zero
      (Nat.mul_ne_zero (NumberField.classNumber_ne_zero K) hIne)
      (by norm_num)
  have htwIne : 2 * I ≠ 0 := Nat.mul_ne_zero (by norm_num) hIne
  have hzne :
      (((ratio * (U : Kˣ)) ^
        ((NumberField.classNumber K * I) * 2)) ^ (2 * I)) ≠ 1 := by
    intro hz
    have hzmap := congrArg (fun w : Kˣ ↦
      realPellRealEmbedding γ₁ γ₂ γ₃ (w : K)) hz
    have hzpow : (zreal ^ ((NumberField.classNumber K * I) * 2)) ^
        (2 * I) = 1 := by
      simpa [zreal, map_pow] using hzmap
    have hzone : zreal ^ ((NumberField.classNumber K * I) * 2) = 1 :=
      (pow_eq_one_iff_of_nonneg (pow_nonneg hzpos.le _)
        htwIne).mp hzpow
    have : zreal = 1 :=
      (pow_eq_one_iff_of_nonneg hzpos.le hmne).mp hzone
    exact hgapNe (sub_eq_zero.mpr this)
  have hM : (1 : ℝ) ≤ (H : ℝ) ^ 3 := by
    exact one_le_pow₀ (by exact_mod_cast hγ₁.trans_le hγ₁H)
  have hdich := supportedUnit_combined_real_log_lower_dichotomy_of_hpow
    basis hbasis (realPellComplexEmbedding γ₁ γ₂ γ₃)
      (realPellRealEmbedding γ₁ γ₂ γ₃) (fun _ ↦ rfl)
      U ratio P q B Ba hB ζ a hpow hdecomp QW ((H : ℝ) ^ 3)
      hdeg hM hMbasis hBa haNat hWheight (by simpa [I] using hzne)
  refine ⟨hSdef, ?_, hgapNe, hgapAbs, hpow, he, hcoordE, hSJ,
    hindex, hdecomp, haNat, hPheight, hWheight, hbasis, hMbasis, ?_⟩
  · simpa [r₁, r₂, r₃] using hU
  · simpa only [SupportedUnitControlledCombinedRealLogDichotomy]
      using hdich



end Erdos841

#print axioms Erdos841.erdos841_distributional_resolution
#print axioms Erdos841.erdos841_selfridge_sqrt_bound_all
#print axioms Erdos841.BoundedUnits.boundedUnit_pow_decomposition_with_exponent_le_unpowered
#print axioms Erdos841.numberField_supportedUnit_boundedUnit_decomposition_explicit
#print axioms Erdos841.bakerWustholz_linearForms_logs_one
