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

import ErdosProblems.Erdos721.AlmostPeriodicity
import ErdosProblems.Erdos721.MarcinkiewiczZygmund
import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Finite Croot--Sisask sampling in a cyclic group

This file specializes the finite Marcinkiewicz--Zygmund inequality to
sampling translates of a function from a finite subset of `ZMod N`.  All
averages are written as explicit finite sums, so the result can be fed into
the later cardinality and density-increment arguments without measure-theory
interfaces.
-/

namespace Erdos721

open Finset Fintype
open scoped BigOperators Pointwise

namespace CyclicCrootSisask

variable {N k m : ℕ} [NeZero N]

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

/-! ## The large-shifts double count -/

section LargeShifts

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {A S : Finset G} {r : ℕ}

lemma bigShifts_step_one (L : Finset (Fin r → G)) (hr : r ≠ 0) :
    ∑ x ∈ L + S.piDiag (Fin r), ∑ l ∈ L, ∑ s ∈ S.piDiag (Fin r),
        (if l + s = x then 1 else 0) = L.card * S.card := by
  simp only [@Finset.sum_comm _ _ _ _ (L + _), Finset.sum_ite_eq]
  rw [Finset.sum_const_nat]
  intro l hl
  have := Fin.pos_iff_nonempty.1 (pos_iff_ne_zero.2 hr)
  rw [Finset.sum_const_nat, mul_one, Finset.card_piDiag]
  exact fun s hs ↦ if_pos (Finset.add_mem_add hl hs)

lemma reindex_shift_count (L : Finset (Fin r → G)) (hr : r ≠ 0)
    (hL : L.Nonempty) (l₁ : Fin r → G) :
    ∑ l₂ ∈ L, ite (l₁ - l₂ ∈ (Finset.univ : Finset G).piDiag (Fin r)) 1 0 =
      ((Finset.univ : Finset G).filter fun t ↦ (l₁ - fun _ ↦ t) ∈ L).card := by
  calc
    _ = ∑ l₂ ∈ L, ∑ t : G, ite ((l₁ - fun _ ↦ t) = l₂) 1 0 := by
      refine Finset.sum_congr rfl fun l₂ _hl₂ ↦ ?_
      rw [Fintype.sum_ite_eq_ite_exists]
      · simp only [Finset.mem_piDiag, Finset.mem_univ, eq_sub_iff_add_eq, true_and,
          sub_eq_iff_eq_add', @eq_comm _ l₁]
        rfl
      rintro i j hij rfl
      cases r
      · simp at hr
      · simpa using congr_fun hij 0
    _ = ((Finset.univ : Finset G).filter fun t ↦ (l₁ - fun _ ↦ t) ∈ L).card := by
      simp only [Finset.sum_comm, Finset.sum_ite_eq, Finset.card_eq_sum_ones,
        Finset.sum_filter]

lemma bigShifts_step_two (L : Finset (Fin r → G)) (hr : r ≠ 0) :
    (∑ x ∈ L + S.piDiag (Fin r), ∑ l ∈ L, ∑ s ∈ S.piDiag (Fin r),
        ite (l + s = x) (1 : ℝ) 0) ^ 2 ≤
      ((L + S.piDiag (Fin r)).card : ℝ) * (S.card : ℝ) *
        ∑ l₁ ∈ L, ∑ l₂ ∈ L,
          ite (l₁ - l₂ ∈ (Finset.univ : Finset G).piDiag (Fin r)) (1 : ℝ) 0 := by
  refine sq_sum_le_card_mul_sum_sq.trans ?_
  simp_rw [sq, Finset.sum_mul, @Finset.sum_comm _ _ _ _ (L + S.piDiag (Fin r)),
    boole_mul, Finset.sum_ite_eq, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have erase_membership : ∀ f : (Fin r → G) → (Fin r → G) → ℝ,
      ∑ x ∈ L, ∑ y ∈ S.piDiag (Fin r),
          (if x + y ∈ L + S.piDiag (Fin r) then f x y else 0) =
        ∑ x ∈ L, ∑ y ∈ S.piDiag (Fin r), f x y := by
    refine fun f ↦ Finset.sum_congr rfl fun x hx ↦ ?_
    exact Finset.sum_congr rfl fun y hy ↦ if_pos (Finset.add_mem_add hx hy)
  rw [erase_membership]
  have count_identity (x y : Fin r → G) :
      ∑ s₁ ∈ S.piDiag (Fin r), ∑ s₂ ∈ S.piDiag (Fin r),
          ite (y + s₂ = x + s₁) (1 : ℝ) 0 =
        ite (x - y ∈ (Finset.univ : Finset G).piDiag (Fin r)) 1 0 *
          ∑ s₁ ∈ S.piDiag (Fin r), ∑ s₂ ∈ S.piDiag (Fin r),
            ite (s₂ = x + s₁ - y) 1 0 := by
    simp_rw [mul_sum, boole_mul, ← ite_and]
    refine Finset.sum_congr rfl fun s₁ hs₁ ↦ ?_
    refine Finset.sum_congr rfl fun s₂ hs₂ ↦ ?_
    refine if_congr ?_ rfl rfl
    rw [eq_sub_iff_add_eq', and_iff_right_of_imp]
    intro h
    simp only [Finset.mem_piDiag] at hs₁ hs₂
    have hxy : x - y = s₂ - s₁ := by
      rw [sub_eq_sub_iff_add_eq_add, ← h, add_comm]
    rw [hxy]
    obtain ⟨i, -, rfl⟩ := hs₁
    obtain ⟨j, -, rfl⟩ := hs₂
    exact Finset.mem_image.2 ⟨j - i, Finset.mem_univ _, rfl⟩
  simp_rw [@Finset.sum_comm _ _ _ _ (S.piDiag (Fin r)) L, count_identity,
    Finset.sum_ite_eq']
  have hbound :
      ∑ x ∈ L, ∑ y ∈ L,
          ite (x - y ∈ (Finset.univ : Finset G).piDiag (Fin r)) (1 : ℝ) 0 *
            ∑ z ∈ S.piDiag (Fin r), ite (x + z - y ∈ S.piDiag (Fin r)) 1 0 ≤
        ∑ x ∈ L, ∑ y ∈ L,
          ite (x - y ∈ (Finset.univ : Finset G).piDiag (Fin r)) (1 : ℝ) 0 *
            (S.card : ℝ) := by
    refine Finset.sum_le_sum fun l₁ _ ↦ Finset.sum_le_sum fun l₂ _ ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> norm_num)
    refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans_eq ?_
    · intro z _
      split_ifs <;> norm_num
    have := Fin.pos_iff_nonempty.1 (pos_iff_ne_zero.2 hr)
    rw [Finset.card_piDiag]
    simp only [nsmul_one]
  refine hbound.trans ?_
  simp_rw [← Finset.sum_mul, mul_comm]
  rfl

/-- If `L` is a nonempty family of `r`-samples from `A`, some sample `a ∈ L`
has many common diagonal shifts with `L`. -/
theorem bigShifts (A S : Finset G) (L : Finset (Fin r → G)) (hr : r ≠ 0)
    (hLne : L.Nonempty) (hL : L ⊆ A ^^ r) :
    ∃ a : Fin r → G, a ∈ L ∧
      L.card * S.card ≤ (A + S).card ^ r *
        ((Finset.univ : Finset G).filter fun t ↦ (a - fun _ ↦ t) ∈ L).card := by
  rcases S.eq_empty_or_nonempty with (rfl | hSne)
  · simpa [Finset.Nonempty, Set.Nonempty] using hLne
  have hSpos : 0 < S.card := by rwa [Finset.card_pos]
  have hsumcard : (L + S.piDiag (Fin r)).card ≤ (A + S).card ^ r := by
    refine (Finset.card_le_card (Finset.add_subset_add_right hL)).trans ?_
    rw [← Fintype.card_piFinset_const]
    refine Finset.card_le_card fun i hi ↦ ?_
    simp only [Finset.mem_add, Finset.mem_piDiag, Fintype.mem_piFinset,
      exists_exists_and_eq_and] at hi ⊢
    obtain ⟨y, hy, a, ha, rfl⟩ := hi
    intro j
    exact ⟨y j, hy _, a, ha, rfl⟩
  rsuffices ⟨a, ha, h⟩ : ∃ a ∈ L,
      L.card * S.card ≤ (L + S.piDiag (Fin r)).card *
        ((Finset.univ : Finset G).filter fun t ↦ (a - fun _ ↦ t) ∈ L).card
  · exact ⟨a, ha, h.trans (Nat.mul_le_mul_right _ hsumcard)⟩
  clear! A
  have hsquare : L.card ^ 2 * S.card ≤
      (L + S.piDiag (Fin r)).card *
        ∑ l₁ ∈ L, ∑ l₂ ∈ L,
          ite (l₁ - l₂ ∈ (Finset.univ : Finset G).piDiag (Fin r)) 1 0 := by
    refine Nat.le_of_mul_le_mul_left ?_ hSpos
    rw [mul_comm, mul_assoc, ← sq, ← mul_pow, mul_left_comm, ← mul_assoc,
      ← bigShifts_step_one L hr]
    exact_mod_cast @bigShifts_step_two G _ _ _ _ _ L hr
  simp only [reindex_shift_count L hr hLne] at hsquare
  rw [sq, mul_assoc, ← smul_eq_mul, mul_sum] at hsquare
  rw [← Finset.sum_const] at hsquare
  exact Finset.exists_le_of_sum_le hLne hsquare

end LargeShifts

/-- The average of `f (x - a)` over `a ∈ A`. -/
noncomputable def setAverageTranslate
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x : ZMod N) : ℝ :=
  (∑ a ∈ A, f (x - a)) / A.card

/-- The translate sample, centered at its exact average over `A`. -/
noncomputable def centeredTranslate
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x a : ZMod N) : ℝ :=
  f (x - a) - setAverageTranslate A f x

/-- The discrepancy between a `k`-sample of translates and `k` times their
exact average. -/
noncomputable def sampleDeviation
    (A : Finset (ZMod N)) (f : ZMod N → ℝ)
    (a : Fin k → ZMod N) (x : ZMod N) : ℝ :=
  ∑ i, centeredTranslate A f x (a i)

lemma sum_centeredTranslate_eq_zero
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ) (x : ZMod N) :
    ∑ a ∈ A, centeredTranslate A f x a = 0 := by
  have hcard : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hA
  unfold centeredTranslate setAverageTranslate
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

/-- For each fixed group point, Marcinkiewicz--Zygmund controls the moment of
the discrepancy of all samples. -/
theorem pointwise_sampleDeviation_moment
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    (hm : m ≠ 0) (x : ZMod N) :
    ∑ a ∈ A ^^ k, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
  let g : ZMod N → ℝ := centeredTranslate A f x
  have hg : ∀ i, ∑ a ∈ A ^^ k, g (a i) = 0 := by
    intro i
    rw [Fintype.sum_piFinset_apply]
    rw [show ∑ b ∈ A, g b = 0 by
      simpa [g] using sum_centeredTranslate_eq_zero hA f x]
    simp
  have h := Erdos721.CyclicMZ.RCLike.marcinkiewicz_zygmund
    (A := A) (n := k) hm g hg
  simpa only [Real.norm_eq_abs, sampleDeviation, g] using h

/-- Summing the pointwise sampling estimate gives an exact global moment
bound. -/
theorem global_sampleDeviation_moment
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    (hm : m ≠ 0) :
    ∑ a ∈ A ^^ k, ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
  rw [Finset.sum_comm]
  calc
    ∑ x : ZMod N, ∑ a ∈ A ^^ k, |sampleDeviation A f a x| ^ (2 * m) ≤
        ∑ x : ZMod N, (8 * m) ^ m * k ^ (m - 1) *
          ∑ a ∈ A ^^ k, ∑ i,
            |centeredTranslate A f x (a i)| ^ (2 * m) := by
      exact Finset.sum_le_sum fun x _ ↦ pointwise_sampleDeviation_moment hA f hm x
    _ = (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

/-- A finite-set translate average of a uniformly bounded function has the
same bound. -/
lemma abs_setAverageTranslate_le
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (x : ZMod N) :
    |setAverageTranslate A f x| ≤ M := by
  have hcard : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hsum : ∑ a ∈ A, |f (x - a)| ≤ ∑ _a ∈ A, M := by
    exact Finset.sum_le_sum fun a _ ↦ hf (x - a)
  unfold setAverageTranslate
  calc
    |(∑ a ∈ A, f (x - a)) / (A.card : ℝ)| =
        |∑ a ∈ A, f (x - a)| / (A.card : ℝ) := by
      rw [abs_div, abs_of_pos hcard]
    _ ≤ (∑ a ∈ A, |f (x - a)|) / (A.card : ℝ) := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ (∑ _a ∈ A, M) / (A.card : ℝ) := by gcongr
    _ = M := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- Centering costs at most a factor two in the pointwise bound. -/
lemma abs_centeredTranslate_le
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (x a : ZMod N) :
    |centeredTranslate A f x a| ≤ 2 * M := by
  unfold centeredTranslate
  calc
    |f (x - a) - setAverageTranslate A f x| ≤
        |f (x - a)| + |setAverageTranslate A f x| := abs_sub _ _
    _ ≤ M + M := add_le_add (hf (x - a))
      (abs_setAverageTranslate_le hA f hM hf x)
    _ = 2 * M := by ring

/-- The global sample discrepancy bound for a uniformly bounded function,
with every finite cardinality made explicit. -/
theorem global_sampleDeviation_moment_of_bounded
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (hm : m ≠ 0) :
    ∑ a ∈ A ^^ k, ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        (A.card : ℝ) ^ k * N * k * (2 * M) ^ (2 * m) := by
  refine (global_sampleDeviation_moment (k := k) hA f hm).trans ?_
  calc
    (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ x : ZMod N, ∑ i,
          |centeredTranslate A f x (a i)| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ _x : ZMod N, ∑ _i : Fin k,
          (2 * M) ^ (2 * m) := by
      apply mul_le_mul_of_nonneg_left
      · refine Finset.sum_le_sum fun a _ha ↦ ?_
        refine Finset.sum_le_sum fun x _hx ↦ ?_
        refine Finset.sum_le_sum fun i _hi ↦ ?_
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_centeredTranslate_le hA f hM hf x (a i)) _
      · positivity
    _ = (8 * m) ^ m * k ^ (m - 1) *
        (A.card : ℝ) ^ k * N * k * (2 * M) ^ (2 * m) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin, Fintype.card_piFinset_const, ZMod.card, Nat.cast_pow]
      ring_nf

/-! ## Many samples are good -/

/-- A finite Markov inequality in the form needed below. -/
lemma markov_card_good
    {ι : Type*} {S : Finset ι} {g : ι → ℝ} {c ε : ℝ}
    (hc : 0 < c) (hg : ∀ a ∈ S, 0 ≤ g a)
    (h : ∑ a ∈ S, g a ≤ ε * c * S.card) :
    (1 - ε) * S.card ≤ (S.filter fun a ↦ g a ≤ c).card := by
  classical
  have hbad := h.trans'
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun a ↦ ¬g a ≤ c) S) fun i hi _ ↦ hg i hi)
  have hcount :=
    (Finset.card_nsmul_le_sum (S.filter fun a ↦ ¬g a ≤ c) g c
      (by simp +contextual [le_of_lt])).trans hbad
  rw [nsmul_eq_mul, mul_right_comm] at hcount
  have hcount' := le_of_mul_le_mul_right hcount hc
  rw [Finset.filter_not, Finset.cast_card_sdiff (Finset.filter_subset _ _)] at hcount'
  linarith

/-- Samples whose global `2m`-moment discrepancy is at most `C`. -/
noncomputable def goodSamples
    (A : Finset (ZMod N)) (f : ZMod N → ℝ) (k m : ℕ) (C : ℝ) :
    Finset (Fin k → ZMod N) :=
  (A ^^ k).filter fun a ↦
    (∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m)) ≤ C

lemma mem_goodSamples
    {A : Finset (ZMod N)} {f : ZMod N → ℝ} {C : ℝ}
    {a : Fin k → ZMod N} :
    a ∈ goodSamples A f k m C ↔
      a ∈ A ^^ k ∧
        (∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m)) ≤ C := by
  simp [goodSamples]

/-- At least half of all samples obey the explicit global moment bound. -/
theorem half_samples_are_good
    {A : Finset (ZMod N)} (hA : A.Nonempty) (f : ZMod N → ℝ)
    {M : ℝ} (hM : 0 < M) (hf : ∀ x, |f x| ≤ M)
    (hm : m ≠ 0) (hk : k ≠ 0) :
    (A.card : ℝ) ^ k / 2 ≤
      (goodSamples A f k m
        (2 * ((8 * m) ^ m * k ^ (m - 1) * N * k *
          (2 * M) ^ (2 * m)))).card := by
  let Q : ℝ := (8 * m) ^ m * k ^ (m - 1) * N * k * (2 * M) ^ (2 * m)
  let C : ℝ := 2 * Q
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hQ : 0 < Q := by
    dsimp only [Q]
    positivity
  have htotal := global_sampleDeviation_moment_of_bounded
    (k := k) hA f hM.le hf hm
  have htotal' :
      ∑ a ∈ A ^^ k, ∑ x : ZMod N,
          |sampleDeviation A f a x| ^ (2 * m) ≤
        (1 / 2 : ℝ) * C * (A ^^ k).card := by
    calc
      _ ≤ (8 * m) ^ m * k ^ (m - 1) *
          (A.card : ℝ) ^ k * N * k * (2 * M) ^ (2 * m) := htotal
      _ = (1 / 2 : ℝ) * C * (A ^^ k).card := by
        simp only [C, Q, Fintype.card_piFinset_const, Nat.cast_pow]
        ring
  have hmarkov := markov_card_good (S := A ^^ k)
    (g := fun a ↦ ∑ x : ZMod N,
      |sampleDeviation A f a x| ^ (2 * m))
    (c := C) (ε := (1 / 2 : ℝ)) (by positivity)
    (fun a _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity) htotal'
  norm_num at hmarkov
  rw [div_eq_mul_inv, mul_comm ((A.card : ℝ) ^ k) (2 : ℝ)⁻¹]
  simpa [goodSamples, C, Q, Fintype.card_piFinset_const, Nat.cast_pow] using hmarkov

/-! ## Two good samples give an almost period -/

lemma sampleDeviation_sub_const_identity
    (A : Finset (ZMod N)) (f : ZMod N → ℝ)
    (a : Fin k → ZMod N) (t x : ZMod N) :
    sampleDeviation A f (a - fun _ ↦ t) x -
        sampleDeviation A f a (x + t) =
      (k : ℝ) *
        (setAverageTranslate A f (x + t) - setAverageTranslate A f x) := by
  unfold sampleDeviation centeredTranslate
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  have harg (i : Fin k) : x - (a i - t) = x + t - a i := by abel
  simp_rw [harg]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

/-- If a sample and its diagonal translate are both good, the exact translate
average has a controlled global `2m`-moment under that shift. -/
theorem goodSamples_give_almost_period
    {A : Finset (ZMod N)} {f : ZMod N → ℝ} {C : ℝ}
    {a : Fin k → ZMod N} {t : ZMod N}
    (ha : a ∈ goodSamples A f k m C)
    (hat : (a - fun _ ↦ t) ∈ goodSamples A f k m C) :
    (k : ℝ) ^ (2 * m) *
        ∑ x : ZMod N,
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
      2 ^ (2 * m) * C := by
  have haMoment := (mem_goodSamples (N := N) (k := k) (m := m)).1 ha |>.2
  have hatMoment := (mem_goodSamples (N := N) (k := k) (m := m)).1 hat |>.2
  have hshift :
      (∑ x : ZMod N, |sampleDeviation A f a (x + t)| ^ (2 * m)) =
        ∑ x : ZMod N, |sampleDeviation A f a x| ^ (2 * m) := by
    exact Fintype.sum_equiv (Equiv.addRight t) _ _ fun _ ↦ rfl
  by_cases hm : m = 0
  · subst m
    simpa using haMoment
  have hpne : 2 * m ≠ 0 := mul_ne_zero two_ne_zero hm
  calc
    (k : ℝ) ^ (2 * m) *
        ∑ x : ZMod N,
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) =
      ∑ x : ZMod N,
        ((k : ℝ) ^ (2 * m) *
          |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m)) := by
      rw [Finset.mul_sum]
    _ = ∑ x : ZMod N,
        |sampleDeviation A f (a - fun _ ↦ t) x -
          sampleDeviation A f a (x + t)| ^ (2 * m) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [← mul_pow]
      have hkabs : |(k : ℝ)| = k := abs_of_nonneg (Nat.cast_nonneg k)
      rw [← hkabs, ← abs_mul, ← sampleDeviation_sub_const_identity]
    _ ≤ ∑ x : ZMod N, 2 ^ (2 * m - 1) *
        (|sampleDeviation A f (a - fun _ ↦ t) x| ^ (2 * m) +
          |sampleDeviation A f a (x + t)| ^ (2 * m)) := by
      refine Finset.sum_le_sum fun x _ ↦ ?_
      calc
        |sampleDeviation A f (a - fun _ ↦ t) x -
            sampleDeviation A f a (x + t)| ^ (2 * m) ≤
          (|sampleDeviation A f (a - fun _ ↦ t) x| +
            |sampleDeviation A f a (x + t)|) ^ (2 * m) := by
          exact pow_le_pow_left₀ (abs_nonneg _)
            (abs_sub _ _)
            _
        _ ≤ _ := add_pow_le (abs_nonneg _) (abs_nonneg _) _
    _ = 2 ^ (2 * m - 1) *
        ((∑ x : ZMod N,
            |sampleDeviation A f (a - fun _ ↦ t) x| ^ (2 * m)) +
          ∑ x : ZMod N, |sampleDeviation A f a (x + t)| ^ (2 * m)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 ^ (2 * m - 1) * (C + C) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hatMoment (by rwa [hshift])
      · positivity
    _ = 2 ^ (2 * m) * C := by
      conv_rhs => rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_add, pow_one]
      ring

/-- The Croot--Sisask sampling conclusion before simplifying its cardinality
bound: there is one good base sample and a diagonal-shift set `T` satisfying
the exact large-shifts count, and every `t ∈ T` is an almost period. -/
theorem exists_large_almostPeriod_set
    {A : Finset (ZMod N)} (hA : A.Nonempty) (S : Finset (ZMod N))
    (f : ZMod N → ℝ) {M : ℝ} (hM : 0 < M) (hf : ∀ x, |f x| ≤ M)
    (hm : m ≠ 0) (hk : k ≠ 0) :
    ∃ (a : Fin k → ZMod N) (T : Finset (ZMod N)),
      a ∈ goodSamples A f k m
        (2 * ((8 * m) ^ m * k ^ (m - 1) * N * k *
          (2 * M) ^ (2 * m))) ∧
      T = ((Finset.univ : Finset (ZMod N)).filter fun t ↦
        (a - fun _ ↦ t) ∈ goodSamples A f k m
          (2 * ((8 * m) ^ m * k ^ (m - 1) * N * k *
            (2 * M) ^ (2 * m)))) ∧
      (goodSamples A f k m
          (2 * ((8 * m) ^ m * k ^ (m - 1) * N * k *
            (2 * M) ^ (2 * m)))).card * S.card ≤
        (A + S).card ^ k * T.card ∧
      (∀ t ∈ T,
        (k : ℝ) ^ (2 * m) *
            ∑ x : ZMod N,
              |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
          2 ^ (2 * m) *
            (2 * ((8 * m) ^ m * k ^ (m - 1) * N * k *
              (2 * M) ^ (2 * m)))) ∧
      T ⊆ A - A := by
  let C : ℝ := 2 * ((8 * m) ^ m * k ^ (m - 1) * N * k *
    (2 * M) ^ (2 * m))
  let L := goodSamples A f k m C
  have hhalf := half_samples_are_good (N := N) (k := k) (m := m)
    hA f hM hf hm hk
  have hLpos : (0 : ℝ) < L.card := by
    refine (show 0 < (A.card : ℝ) ^ k / 2 by positivity).trans_le ?_
    simpa only [L, C] using hhalf
  have hLne : L.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hLpos
  have hLsub : L ⊆ A ^^ k := by
    exact (Finset.filter_subset _ _)
  obtain ⟨a, ha, hcount⟩ := bigShifts A S L hk hLne hLsub
  let T : Finset (ZMod N) :=
    (Finset.univ : Finset (ZMod N)).filter fun t ↦
      (a - fun _ ↦ t) ∈ L
  refine ⟨a, T, ?_, rfl, ?_, ?_, ?_⟩
  · simpa only [L, C] using ha
  · simpa only [T] using hcount
  · intro t ht
    have hat : (a - fun _ ↦ t) ∈ L := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    have halmost := goodSamples_give_almost_period (N := N) (k := k) (m := m)
      (C := C) ha hat
    simpa only [C] using halmost
  · intro t ht
    have haA : a ∈ A ^^ k := (Finset.filter_subset _ _) ha
    have hat : (a - fun _ ↦ t) ∈ L := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    have hatA : (a - fun _ ↦ t) ∈ A ^^ k :=
      (Finset.filter_subset _ _) hat
    let i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
    let b : Fin k → ZMod N := a - fun _ ↦ t
    rw [Finset.mem_sub]
    refine ⟨a i, Fintype.mem_piFinset.mp haA i,
      b i, Fintype.mem_piFinset.mp hatA i, ?_⟩
    simp [b]

/-- Algebraic form of the large-shifts cardinality calculation. -/
lemma card_shiftSet_lower_bound
    {A S : Finset (ZMod N)} {L : Finset (Fin k → ZMod N)}
    {T : Finset (ZMod N)} {K : ℝ}
    (hA : A.Nonempty) (hK : 0 < K)
    (hhalf : (A.card : ℝ) ^ k / 2 ≤ L.card)
    (hcount : L.card * S.card ≤ (A + S).card ^ k * T.card)
    (hdoubling : ((A + S).card : ℝ) ≤ K * A.card) :
    (S.card : ℝ) / (2 * K ^ k) ≤ T.card := by
  have hAcard : (0 : ℝ) < A.card := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hApow : (0 : ℝ) < (A.card : ℝ) ^ k := pow_pos hAcard _
  have hKpow : (0 : ℝ) < K ^ k := pow_pos hK _
  have hcountR : (L.card : ℝ) * S.card ≤
      ((A + S).card : ℝ) ^ k * T.card := by
    exact_mod_cast hcount
  have hpow : ((A + S).card : ℝ) ^ k ≤ (K * A.card) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hdoubling _
  have hchain : ((A.card : ℝ) ^ k / 2) * S.card ≤
      (K * A.card) ^ k * T.card := by
    calc
      ((A.card : ℝ) ^ k / 2) * S.card ≤ (L.card : ℝ) * S.card := by
        exact mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)
      _ ≤ ((A + S).card : ℝ) ^ k * T.card := hcountR
      _ ≤ (K * A.card) ^ k * T.card := by
        exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hcancel : (S.card : ℝ) / 2 ≤ K ^ k * T.card := by
    apply le_of_mul_le_mul_left (a := (A.card : ℝ) ^ k) _ hApow
    calc
      (A.card : ℝ) ^ k * ((S.card : ℝ) / 2) =
          ((A.card : ℝ) ^ k / 2) * S.card := by ring
      _ ≤ (K * A.card) ^ k * T.card := hchain
      _ = (A.card : ℝ) ^ k * (K ^ k * T.card) := by
        rw [mul_pow]
        ring
  calc
    (S.card : ℝ) / (2 * K ^ k) = ((S.card : ℝ) / 2) / K ^ k := by ring
    _ ≤ (K ^ k * T.card) / K ^ k := by
      exact div_le_div_of_nonneg_right hcancel hKpow.le
    _ = T.card := by field_simp

/-- Standard small-doubling form of finite Croot--Sisask: if
`|A + S| ≤ K |A|`, there is an almost-period set of relative size at least
`1 / (2 K^k)` inside the ambient shift set `S`. -/
theorem exists_many_almostPeriods_of_smallDoubling
    {A : Finset (ZMod N)} (hA : A.Nonempty) (S : Finset (ZMod N))
    (f : ZMod N → ℝ) {M K : ℝ} (hM : 0 < M) (hf : ∀ x, |f x| ≤ M)
    (hK : 0 < K) (hdoubling : ((A + S).card : ℝ) ≤ K * A.card)
    (hm : m ≠ 0) (hk : k ≠ 0) :
    ∃ T : Finset (ZMod N),
      (S.card : ℝ) / (2 * K ^ k) ≤ T.card ∧
      (∀ t ∈ T,
        (k : ℝ) ^ (2 * m) *
            ∑ x : ZMod N,
              |setAverageTranslate A f (x + t) - setAverageTranslate A f x| ^ (2 * m) ≤
          2 ^ (2 * m) *
            (2 * ((8 * m) ^ m * k ^ (m - 1) * N * k *
              (2 * M) ^ (2 * m)))) ∧
      T ⊆ A - A := by
  obtain ⟨a, T, ha, hT, hcount, halmost, hTsub⟩ :=
    exists_large_almostPeriod_set (N := N) (k := k) (m := m)
      hA S f hM hf hm hk
  have hhalf := half_samples_are_good (N := N) (k := k) (m := m)
    hA f hM hf hm hk
  refine ⟨T, ?_, halmost, hTsub⟩
  exact card_shiftSet_lower_bound hA hK hhalf hcount hdoubling

end CyclicCrootSisask
end Erdos721
