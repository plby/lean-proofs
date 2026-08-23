/- leanprover/lean4:v4.33.0 -/
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

import ErdosProblems.Erdos721.CrootSisask
import APAP.Physics.AlmostPeriodicity

/-!
# Croot--Sisask almost periods inside a difference set

The APAP Croot--Sisask theorem records the size and approximation properties
of its shift set, but its public interface discards the elementary fact that
the constructed shifts lie in `A - A`.  The local Chang--Sanders argument
needs precisely that fact.  This file repeats the final quantitative
large-shifts assembly while retaining the containment, then carries it
through the `L^p`-to-`L^∞` and boosting arguments.
-/

open Finset Real
open scoped BigOperators Pointwise NNReal ENNReal Indicator translate mu
  Combinatorics.Additive

namespace AlmostPeriodicity

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]
variable {A S : Finset G} {f : G → ℂ} {epsilon K : ℝ} {k m : ℕ}

local notation "𝒫" x => 1 + Real.log (min 1 x)⁻¹
local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

private lemma contained_T_bound (hK₂ : 2 ≤ K) (Lc Sc Ac ASc Tc : ℕ)
    (hk : k = ⌈(64 : ℝ) * m / (epsilon / 2) ^ 2⌉₊)
    (h₁ : Lc * Sc ≤ ASc ^ k * Tc) (h₂ : (Ac : ℝ) ^ k / 2 ≤ Lc)
    (h₃ : (ASc : ℝ) ≤ K * Ac) (hAc : 0 < Ac)
    (hepsilon : 0 < epsilon) (hepsilon' : epsilon ≤ 1) (hm : 1 ≤ m) :
    K ^ (-512 * m / epsilon ^ 2 : ℝ) * Sc ≤ Tc := by
  have hk' : k = ⌈(256 : ℝ) * m / epsilon ^ 2⌉₊ := by
    rw [hk, div_pow, div_div_eq_mul_div, mul_right_comm]
    congr 3
    norm_num
  have hK₀ : 0 < K := by positivity
  have : (0 : ℝ) < Ac ^ k := by positivity
  refine le_of_mul_le_mul_left ?_ this
  rw [neg_mul, neg_div, Real.rpow_neg hK₀.le, mul_left_comm,
    inv_mul_le_iff₀ (by positivity)]
  calc
    (Ac ^ k * Sc : ℝ) = 2 * (Ac ^ k / 2) * Sc := by ring
    _ ≤ K * Lc * Sc := by gcongr
    _ = K * ↑(Lc * Sc) := by push_cast; ring
    _ ≤ K * ↑(ASc ^ k * Tc) := by gcongr
    _ = K * ASc ^ k * Tc := by push_cast; ring
    _ ≤ K * (K * Ac) ^ k * Tc := by gcongr
    _ = K ^ (k + 1 : ℝ) * Ac ^ k * Tc := by norm_cast; push_cast; ring
    _ ≤ K ^ (512 * m / epsilon ^ 2) * Ac ^ k * Tc := by
      gcongr
      · linarith
      rw [← le_sub_iff_add_le, hk', mul_div_assoc, mul_div_assoc]
      have h₄ := Nat.ceil_lt_add_one (a := 256 * (m / epsilon ^ 2))
        (by positivity)
      have h₅ : (1 : ℝ) ≤ 128 * (m / epsilon ^ 2) := by
        rw [div_eq_mul_one_div]
        bound
      linear_combination h₄ + 2 * h₅
    _ = K ^ (512 * m / epsilon ^ 2) * (Ac ^ k * Tc) := by ring

/-- The elementary large-fibre form of the Croot--Sisask double count.  In
contrast to the diagonal-difference set used by APAP's public interface, the
set `T` produced here is literally a subset of the supplied shift set `S`.
Two elements of the same fibre translate one good sample to another. -/
private theorem exists_large_base_shift_fiber
    {r : ℕ} (hr : r ≠ 0) (hA : A.Nonempty) (hS : S.Nonempty)
    (L : Finset (Fin r → G)) (hL : L.Nonempty) (hLA : L ⊆ A ^^ r) :
    ∃ (y : Fin r → G) (T : Finset G),
      T ⊆ S ∧ T.Nonempty ∧
      L.card * S.card ≤ (A + S).card ^ r * T.card ∧
      ∀ t ∈ T, ∃ a ∈ L, a + (fun _ ↦ t) = y := by
  let P : Finset ((Fin r → G) × G) := L.product S
  let Y : Finset (Fin r → G) := (A + S) ^^ r
  let shift : ((Fin r → G) × G) → (Fin r → G) :=
    fun p ↦ p.1 + fun _ ↦ p.2
  have hmap : Set.MapsTo shift (P : Set ((Fin r → G) × G)) (Y : Set (Fin r → G)) := by
    intro p hp
    change p ∈ L.product S at hp
    have hp' : p.1 ∈ L ∧ p.2 ∈ S := Finset.mem_product.mp hp
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_add.mpr
      ⟨p.1 i, Fintype.mem_piFinset.mp (hLA hp'.1) i, p.2, hp'.2, rfl⟩
  have hY : Y.Nonempty := by
    have hAS : (A + S).Nonempty := hA.add hS
    exact Fintype.piFinset_nonempty.mpr fun _ ↦ hAS
  have hsum : P.card = ∑ y ∈ Y, (P.filter fun p ↦ shift p = y).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have haverage :
      ∑ _y ∈ Y, (P.card : ℕ) ≤
        ∑ y ∈ Y, (Y.card : ℕ) *
          (P.filter fun p ↦ shift p = y).card := by
    calc
      ∑ _y ∈ Y, (P.card : ℕ) = Y.card * P.card := by simp
      _ = Y.card * ∑ y ∈ Y,
          (P.filter fun p ↦ shift p = y).card := by rw [hsum]
      _ ≤ ∑ y ∈ Y, Y.card *
          (P.filter fun p ↦ shift p = y).card := by
        rw [Finset.mul_sum]
  obtain ⟨y, hyY, hy⟩ : ∃ y ∈ Y,
      (P.card : ℕ) ≤ (Y.card : ℕ) *
        (P.filter fun p ↦ shift p = y).card :=
    Finset.exists_le_of_sum_le (M := ℕ) hY haverage
  let fiber : Finset ((Fin r → G) × G) :=
    P.filter fun p ↦ shift p = y
  let T : Finset G := fiber.image Prod.snd
  have hsnd : Set.InjOn Prod.snd (fiber : Set ((Fin r → G) × G)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    apply Prod.ext
    · funext i
      have hshift := hp.2.trans hq.2.symm
      change p.1 + (fun _ ↦ p.2) = q.1 + (fun _ ↦ q.2) at hshift
      have hi := congrFun hshift i
      simp only [Pi.add_apply] at hi
      rw [hpq] at hi
      exact add_right_cancel hi
    · exact hpq
  have hTcard : T.card = fiber.card := by
    exact Finset.card_image_of_injOn hsnd
  have hTsub : T ⊆ S := by
    intro t ht
    change t ∈ fiber.image Prod.snd at ht
    rw [Finset.mem_image] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    exact (Finset.mem_product.mp (Finset.filter_subset _ _ hp)).2
  have hfiber : fiber.Nonempty := by
    have hP : P.Nonempty := hL.product hS
    have hPpos : 0 < P.card := Finset.card_pos.mpr hP
    have hprodpos : 0 < Y.card * fiber.card :=
      hPpos.trans_le (by simpa only [fiber] using hy)
    exact Finset.card_pos.mp (Nat.pos_of_mul_pos_left hprodpos)
  refine ⟨y, T, hTsub, ?_, ?_, ?_⟩
  · exact hfiber.image _
  · calc
      L.card * S.card = P.card := by simp [P]
      _ ≤ Y.card * fiber.card := by simpa only [fiber] using hy
      _ = (A + S).card ^ r * T.card := by
        rw [← hTcard]
        simp [Y]
  · intro t ht
    change t ∈ fiber.image Prod.snd at ht
    rw [Finset.mem_image] at ht
    obtain ⟨p, hp, hpt⟩ := ht
    have hpP := Finset.filter_subset _ _ hp
    have hpEq := (Finset.mem_filter.mp hp).2
    refine ⟨p.1, (Finset.mem_product.mp hpP).1, ?_⟩
    simpa only [shift, hpt] using hpEq

/-- The base-set form of Croot--Sisask: `T` is contained in the requested
shift set, and every difference of two elements of `T` is an almost period.
This is the form used in the published local Chang--Sanders bootstrapping. -/
theorem almost_periodicity_base_contained
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon' : epsilon ≤ 1)
    (m : ℕ) (hm : m ≠ 0) (f : G → ℂ)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K) :
    ∃ T : Finset G,
      K ^ (-512 * m / epsilon ^ 2 : ℝ) * #S ≤ #T ∧
      T ⊆ S ∧ T.Nonempty ∧
      ∀ t ∈ T, ∀ t' ∈ T,
        ‖τ (t - t') (μ A ∗ᵈ f) - μ A ∗ᵈ f‖_[2 * m] ≤
          epsilon * ‖f‖_[2 * m] := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let sampleCount := ⌈(64 : ℝ) * m / (epsilon / 2) ^ 2⌉₊
  have hsampleCount : sampleCount ≠ 0 := by positivity
  let L := l sampleCount m (epsilon / 2) f A
  have hLcard : (#A ^ sampleCount : ℝ) / 2 ≤ #L :=
    lemma28 (half_pos hepsilon) hmpos
      (Nat.le_ceil (64 * m / (epsilon / 2) ^ 2))
  have hL : L.Nonempty := by
    have : (0 : ℝ) < #L := hLcard.trans_lt' (by positivity)
    simpa [Finset.card_pos] using this
  obtain ⟨y, T, hTsub, hT, hlarge, hfiber⟩ :=
    exists_large_base_shift_fiber hsampleCount hA hS L hL
      (Finset.filter_subset _ _)
  refine ⟨T, ?_, hTsub, hT, ?_⟩
  · exact contained_T_bound hK₂ #L #S #A #(A + S) #T rfl
      hlarge hLcard
      (by rw [← Finset.cast_addConst_mul_card]; gcongr)
      hA.card_pos hepsilon hepsilon' hmpos
  · intro t ht t' ht'
    obtain ⟨a, ha, hat⟩ := hfiber t ht
    obtain ⟨a', ha', hat'⟩ := hfiber t' ht'
    have haa : a' + (fun _ ↦ t' - t) = a := by
      funext i
      have hi := congrFun (hat'.trans hat.symm) i
      simp only [Pi.add_apply] at hi ⊢
      calc
        a' i + (t' - t) = (a' i + t') - t := by abel
        _ = (a i + t) - t := by rw [hi]
        _ = a i := by abel
    have hasecond : a' + (fun _ ↦ t' - t) ∈ L := by
      rw [haa]
      exact ha
    have htriangle := just_the_triangle_inequality ha' hasecond
      (Nat.pos_of_ne_zero hsampleCount) hmpos
    have hneg : -(t' - t) = t - t' := by abel
    rw [hneg] at htriangle
    exact htriangle.trans_eq (by ring)

/-- Quantitative Croot--Sisask almost-periodicity, retaining the fact that
the shift set is contained in `A - A`. -/
theorem almost_periodicity_contained
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon' : epsilon ≤ 1)
    (m : ℕ) (hm : m ≠ 0) (f : G → ℂ)
    (hA : A.Nonempty) (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K) :
    ∃ T : Finset G,
      K ^ (-512 * m / epsilon ^ 2 : ℝ) * #S ≤ #T ∧
      T ⊆ A - A ∧
      ∀ t ∈ T,
        ‖τ t (μ A ∗ᵈ f) - μ A ∗ᵈ f‖_[2 * m] ≤
          epsilon * ‖f‖_[2 * m] := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let sampleCount := ⌈(64 : ℝ) * m / (epsilon / 2) ^ 2⌉₊
  have hsampleCount : sampleCount ≠ 0 := by positivity
  let L := l sampleCount m (epsilon / 2) f A
  have hLcard : (#A ^ sampleCount : ℝ) / 2 ≤ #L :=
    lemma28 (half_pos hepsilon) hmpos
      (Nat.le_ceil (64 * m / (epsilon / 2) ^ 2))
  have hL : L.Nonempty := by
    have : (0 : ℝ) < #L := hLcard.trans_lt' (by positivity)
    simpa [Finset.card_pos] using this
  obtain ⟨a, ha, hlarge⟩ :=
    Erdos721.CyclicCrootSisask.bigShifts A S L hsampleCount hL
      (Finset.filter_subset _ _)
  let T : Finset G := {t | (a - fun _ ↦ t) ∈ L}
  refine ⟨T, ?_, ?_, ?_⟩
  · exact contained_T_bound hK₂ #L #S #A #(A + S) #T rfl
      (by simpa only [T] using hlarge) hLcard
      (by rw [← Finset.cast_addConst_mul_card]; gcongr)
      hA.card_pos hepsilon hepsilon' hmpos
  · intro t ht
    have haA : a ∈ A ^^ sampleCount := (Finset.filter_subset _ _) ha
    have hatL : (a - fun _ ↦ t) ∈ L := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    have hatA : (a - fun _ ↦ t) ∈ A ^^ sampleCount :=
      (Finset.filter_subset _ _) hatL
    let i : Fin sampleCount := ⟨0, Nat.pos_of_ne_zero hsampleCount⟩
    let b : Fin sampleCount → G := a - fun _ ↦ t
    rw [Finset.mem_sub]
    refine ⟨a i, Fintype.mem_piFinset.mp haA i,
      b i, Fintype.mem_piFinset.mp hatA i, ?_⟩
    simp [b]
  · intro t ht
    have hatSub : (a - fun _ ↦ t) ∈ L := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    have hat : (a + fun _ ↦ -t) ∈ L := by
      rw [show (a - fun _ ↦ t) = a + fun _ ↦ -t by
        ext x
        exact sub_eq_add_neg (a x) t] at hatSub
      exact hatSub
    have htriangle := just_the_triangle_inequality (t := -t) ha hat
      (Nat.pos_of_ne_zero hsampleCount) hmpos
    simpa only [neg_neg] using (htriangle.trans_eq (by ring))

/-- The contained Croot--Sisask set in the `L^∞` form used before
boosting. -/
theorem linfty_almost_periodicity_contained
    (epsilon : ℝ) (hepsilon₀ : 0 < epsilon) (hepsilon₁ : epsilon ≤ 1)
    (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    ∃ T : Finset G,
      K ^ (-4096 * ⌈𝒫 (#C / #B)⌉ / epsilon ^ 2) * #S ≤ #T ∧
      T ⊆ A - A ∧
      ∀ t ∈ T,
        ‖τ t (μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) -
            μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C‖_[∞] ≤ epsilon := by
  let r : ℝ := min 1 (#C / #B)
  set moment : ℝ := 𝒫 (#C / #B)
  have hmoment₀ : 0 < moment := by
    have hBcard : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
    have hCcard : (0 : ℝ) < #C := by exact_mod_cast hC.card_pos
    have : 0 ≤ Real.log (min 1 (#C / #B))⁻¹ := by bound
    positivity
  have hmoment₁ : 1 ≤ ⌈moment⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨T, hKT, hTsub, hT⟩ := almost_periodicity_contained
    (epsilon / Real.exp 1) (by positivity)
    (div_le_one_of_le₀ (hepsilon₁.trans (one_le_exp zero_le_one))
      (by positivity)) ⌈moment⌉₊ (by positivity) (𝟭_[B])
      hA hK₂ hK
  norm_cast at hT
  set M : ℕ := 2 * ⌈moment⌉₊
  have hM₀ : (M : ℝ≥0) ≠ 0 := by positivity
  have hM₁ : 1 < (M : ℝ≥0) := by
    norm_cast
    simp [← Nat.succ_le_iff, M]
    linarith
  have hM : (M : ℝ≥0).HolderConjugate _ :=
    NNReal.HolderConjugate.conjExponent hM₁
  have : (M : ℝ≥0∞).HolderConjugate _ := hM.coe_ennreal
  refine ⟨T, ?_, hTsub, fun t ht ↦ ?_⟩
  · calc
      _ = K ^ (-(512 * 8) / epsilon ^ 2 * ⌈moment⌉₊) * #S := by
        rw [mul_div_right_comm, natCast_ceil_eq_intCast_ceil hmoment₀.le]
        norm_num
      _ ≤ K ^ (-(512 * Real.exp 1 ^ 2) / epsilon ^ 2 * ⌈moment⌉₊) * #S := by
        gcongr
        · exact one_le_two.trans hK₂
        calc
          _ ≤ (2.7182818286 : ℝ) ^ 2 := by
            gcongr
            exact exp_one_lt_d9.le
          _ ≤ _ := by norm_num
      _ = _ := by
        simp [div_div_eq_mul_div, ← mul_div_right_comm, mul_right_comm, div_pow]
      _ ≤ _ := hKT
  set F : G → ℂ := τ t (μ A ∗ᵈ 𝟭_[B]) - μ A ∗ᵈ 𝟭_[B]
  have hpoint (x : G) :=
    calc
      (τ t (μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) -
          μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C : G → ℂ) x =
          (F ∗ᵈ μ C) x := by simp [sub_ddconv, F]
      _ = ∑ y, F y * μ C (x - y) := ddconv_eq_sum_sub' ..
      _ = ∑ y, F y * μ (x +ᵥ -C) y := by simp [neg_add_eq_sub]
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ ?_
  calc
    ‖(τ t (μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) -
        μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C : G → ℂ) x‖ =
        ‖∑ y, F y * μ (x +ᵥ -C) y‖ := by rw [hpoint]
    _ ≤ ∑ y, ‖F y * μ (x +ᵥ -C) y‖ := norm_sum_le _ _
    _ = ‖F * μ (x +ᵥ -C)‖_[1] := by
      rw [MeasureTheory.dL1Norm_eq_sum_norm]
      rfl
    _ ≤ ‖F‖_[M] * ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] :=
      MeasureTheory.dLpNorm_mul_le _ _
    _ ≤ epsilon / exp 1 * #B ^ (M : ℝ)⁻¹ *
        ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
      gcongr
      simpa [← ENNReal.coe_natCast,
        MeasureTheory.dLpNorm_indicator_one hM₀, F] using hT t ht
    _ = epsilon * ((#C / #B) ^ (-(M : ℝ)⁻¹) / exp 1) := by
      rw [← mul_comm_div, MeasureTheory.dLpNorm_mu hM.symm.lt.le hC.neg.vadd_finset,
        card_vadd_finset, card_neg, hM.symm.coe.inv_sub_one, div_rpow, mul_assoc]
      any_goals positivity
      push_cast
      rw [rpow_neg, rpow_neg, ← div_eq_mul_inv, inv_div_inv]
      all_goals positivity
    _ ≤ epsilon := mul_le_of_le_one_right (by positivity) <|
      (div_le_one (by positivity)).2 <| by
        calc
          (#C / #B : ℝ) ^ (-(M : ℝ)⁻¹) ≤
              r ^ (-(M : ℝ)⁻¹) :=
            rpow_le_rpow_of_nonpos (by positivity) inf_le_right <|
              neg_nonpos.2 (by positivity)
          _ ≤ r ^ (-(1 + log r⁻¹)⁻¹) :=
            rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left <|
              neg_le_neg <| inv_anti₀ (by positivity) <|
                (Nat.le_ceil _).trans (by
                  have hrmoment : 1 + log r⁻¹ = moment := rfl
                  rw [hrmoment]
                  exact_mod_cast
                    Nat.le_mul_of_pos_left ⌈moment⌉₊ (by norm_num : 0 < 2))
          _ ≤ r ^ (-(0 + log r⁻¹)⁻¹) := by
            obtain hr | hr : r = 1 ∨ r < 1 := inf_le_left.eq_or_lt
            · simp [hr]
            have : 0 < log r⁻¹ := log_pos ((one_lt_inv₀ (by positivity)).2 hr)
            exact rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left
              (by gcongr; exact zero_le_one)
          _ = r ^ (log r)⁻¹ := by simp [inv_neg]
          _ ≤ exp 1 := rpow_inv_log_le_exp_one

/-- `L^∞` almost-periodicity on all pair differences of a dense base set
`T ⊆ S`.  This is the exact input to the translation-and-boosting step in
Schoen--Sisask and Bloom--Sisask. -/
theorem linfty_almost_periodicity_base_contained
    (epsilon : ℝ) (hepsilon₀ : 0 < epsilon) (hepsilon₁ : epsilon ≤ 1)
    (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    ∃ T : Finset G,
      K ^ (-4096 * ⌈𝒫 (#C / #B)⌉ / epsilon ^ 2) * #S ≤ #T ∧
      T ⊆ S ∧ T.Nonempty ∧
      ∀ t ∈ T, ∀ t' ∈ T,
        ‖τ (t - t') (μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) -
            μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C‖_[∞] ≤ epsilon := by
  let r : ℝ := min 1 (#C / #B)
  set moment : ℝ := 𝒫 (#C / #B)
  have hmoment₀ : 0 < moment := by
    have hBcard : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
    have hCcard : (0 : ℝ) < #C := by exact_mod_cast hC.card_pos
    have : 0 ≤ Real.log (min 1 (#C / #B))⁻¹ := by bound
    positivity
  have hmoment₁ : 1 ≤ ⌈moment⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨T, hKT, hTsub, hTne, hT⟩ := almost_periodicity_base_contained
    (epsilon / Real.exp 1) (by positivity)
    (div_le_one_of_le₀ (hepsilon₁.trans (one_le_exp zero_le_one))
      (by positivity)) ⌈moment⌉₊ (by positivity) (𝟭_[B])
      hA hS hK₂ hK
  norm_cast at hT
  set M : ℕ := 2 * ⌈moment⌉₊
  have hM₀ : (M : ℝ≥0) ≠ 0 := by positivity
  have hM₁ : 1 < (M : ℝ≥0) := by
    norm_cast
    simp [← Nat.succ_le_iff, M]
    linarith
  have hM : (M : ℝ≥0).HolderConjugate _ :=
    NNReal.HolderConjugate.conjExponent hM₁
  have : (M : ℝ≥0∞).HolderConjugate _ := hM.coe_ennreal
  refine ⟨T, ?_, hTsub, hTne, fun t ht t' ht' ↦ ?_⟩
  · calc
      _ = K ^ (-(512 * 8) / epsilon ^ 2 * ⌈moment⌉₊) * #S := by
        rw [mul_div_right_comm, natCast_ceil_eq_intCast_ceil hmoment₀.le]
        norm_num
      _ ≤ K ^ (-(512 * Real.exp 1 ^ 2) / epsilon ^ 2 * ⌈moment⌉₊) * #S := by
        gcongr
        · exact one_le_two.trans hK₂
        calc
          _ ≤ (2.7182818286 : ℝ) ^ 2 := by
            gcongr
            exact exp_one_lt_d9.le
          _ ≤ _ := by norm_num
      _ = _ := by
        simp [div_div_eq_mul_div, ← mul_div_right_comm, mul_right_comm, div_pow]
      _ ≤ _ := hKT
  let shift : G := t - t'
  set F : G → ℂ := τ shift (μ A ∗ᵈ 𝟭_[B]) - μ A ∗ᵈ 𝟭_[B]
  have hpoint (x : G) :=
    calc
      (τ shift (μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) -
          μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C : G → ℂ) x =
          (F ∗ᵈ μ C) x := by simp [sub_ddconv, F]
      _ = ∑ y, F y * μ C (x - y) := ddconv_eq_sum_sub' ..
      _ = ∑ y, F y * μ (x +ᵥ -C) y := by simp [neg_add_eq_sub]
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ ?_
  calc
    ‖(τ shift (μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) -
        μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C : G → ℂ) x‖ =
        ‖∑ y, F y * μ (x +ᵥ -C) y‖ := by rw [hpoint]
    _ ≤ ∑ y, ‖F y * μ (x +ᵥ -C) y‖ := norm_sum_le _ _
    _ = ‖F * μ (x +ᵥ -C)‖_[1] := by
      rw [MeasureTheory.dL1Norm_eq_sum_norm]
      rfl
    _ ≤ ‖F‖_[M] * ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] :=
      MeasureTheory.dLpNorm_mul_le _ _
    _ ≤ epsilon / exp 1 * #B ^ (M : ℝ)⁻¹ *
        ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
      gcongr
      simpa [← ENNReal.coe_natCast,
        MeasureTheory.dLpNorm_indicator_one hM₀, F, shift] using hT t ht t' ht'
    _ = epsilon * ((#C / #B) ^ (-(M : ℝ)⁻¹) / exp 1) := by
      rw [← mul_comm_div, MeasureTheory.dLpNorm_mu hM.symm.lt.le hC.neg.vadd_finset,
        card_vadd_finset, card_neg, hM.symm.coe.inv_sub_one, div_rpow, mul_assoc]
      any_goals positivity
      push_cast
      rw [rpow_neg, rpow_neg, ← div_eq_mul_inv, inv_div_inv]
      all_goals positivity
    _ ≤ epsilon := mul_le_of_le_one_right (by positivity) <|
      (div_le_one (by positivity)).2 <| by
        calc
          (#C / #B : ℝ) ^ (-(M : ℝ)⁻¹) ≤
              r ^ (-(M : ℝ)⁻¹) :=
            rpow_le_rpow_of_nonpos (by positivity) inf_le_right <|
              neg_nonpos.2 (by positivity)
          _ ≤ r ^ (-(1 + log r⁻¹)⁻¹) :=
            rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left <|
              neg_le_neg <| inv_anti₀ (by positivity) <|
                (Nat.le_ceil _).trans (by
                  have hrmoment : 1 + log r⁻¹ = moment := rfl
                  rw [hrmoment]
                  exact_mod_cast
                    Nat.le_mul_of_pos_left ⌈moment⌉₊ (by norm_num : 0 < 2))
          _ ≤ r ^ (-(0 + log r⁻¹)⁻¹) := by
            obtain hr | hr : r = 1 ∨ r < 1 := inf_le_left.eq_or_lt
            · simp [hr]
            have : 0 < log r⁻¹ := log_pos ((one_lt_inv₀ (by positivity)).2 hr)
            exact rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left
              (by gcongr; exact zero_le_one)
          _ = r ^ (log r)⁻¹ := by simp [inv_neg]
          _ ≤ exp 1 := rpow_inv_log_le_exp_one

/-- Boost the pair-difference almost periods of a dense base set.  The
convolution set is the translate `X = -z + T`; the untranslated set `T`
remains inside `S` and has the same cardinality and Fourier magnitudes. -/
theorem linfty_almost_periodicity_boosted_base_contained
    (epsilon : ℝ) (hepsilon₀ : 0 < epsilon) (hepsilon₁ : epsilon ≤ 1)
    (boost : ℕ) (hboost : boost ≠ 0)
    (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    ∃ (T : Finset G) (z : G) (X : Finset G),
      K ^ (-4096 * ⌈𝒫 (#C / #B)⌉ * boost ^ 2 / epsilon ^ 2) * #S ≤ #T ∧
      T ⊆ S ∧ z ∈ T ∧ X = (-z) +ᵥ T ∧
      ‖μ X ∗ᵈ^ boost ∗ᵈ (μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) -
          μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C‖_[∞] ≤ epsilon := by
  obtain ⟨T, hKT, hTsub, hTne, hT⟩ :=
    linfty_almost_periodicity_base_contained
      (epsilon / boost) (by positivity)
      (div_le_one_of_le₀
        (hepsilon₁.trans (mod_cast Nat.one_le_iff_ne_zero.2 hboost))
        (by positivity)) hK₂ hK hA hS B C hB hC
  let z := hTne.choose
  have hz : z ∈ T := hTne.choose_spec
  let X : Finset G := (-z) +ᵥ T
  have hX : X.Nonempty := by
    refine ⟨(-z) +ᵥ z, ?_⟩
    exact Finset.vadd_mem_vadd_finset hz
  refine ⟨T, z, X, ?_, hTsub, hz, rfl, ?_⟩
  · simpa only [div_pow, div_div_eq_mul_div] using hKT
  set F := μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C
  calc
    (‖μ X ∗ᵈ^ boost ∗ᵈ F - F‖_[∞] : ℝ) =
        ‖𝔼 a ∈ X ^^ boost, (τ (∑ i, a i) F - F)‖_[∞] := by
      rw [mu_iterConv_ddconv, expect_sub_distrib,
        expect_const hX.piFinset_const]
    _ ≤ 𝔼 a ∈ X ^^ boost, ‖τ (∑ i, a i) F - F‖_[∞] :=
      MeasureTheory.dLpNorm_expect_le le_top
    _ ≤ 𝔼 _a ∈ X ^^ boost, epsilon := by
      refine expect_le_expect fun a ha ↦ ?_
      calc
        (‖τ (∑ i, a i) F - F‖_[∞] : ℝ) ≤
            ∑ i, ‖τ (a i) F - F‖_[∞] :=
          MeasureTheory.dLpNorm_translate_sum_sub_le le_top _ _ _
        _ ≤ ∑ _i, epsilon / boost := by
          gcongr with i
          have hai : a i ∈ X := Fintype.mem_piFinset.mp ha i
          obtain ⟨t, ht, hti⟩ := Finset.mem_vadd_finset.mp hai
          have hpair := hT t ht z hz
          rw [← hti]
          simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hpair
        _ = epsilon := by
          simp only [sum_const, card_fin, nsmul_eq_mul]
          rw [mul_div_cancel₀]
          positivity
    _ = epsilon := by rw [expect_const hX.piFinset_const]

/-- Boosting a contained Croot--Sisask set preserves its difference-set
containment. -/
theorem linfty_almost_periodicity_boosted_contained
    (epsilon : ℝ) (hepsilon₀ : 0 < epsilon) (hepsilon₁ : epsilon ≤ 1)
    (boost : ℕ) (hboost : boost ≠ 0)
    (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    ∃ T : Finset G,
      K ^ (-4096 * ⌈𝒫 (#C / #B)⌉ * boost ^ 2 / epsilon ^ 2) * #S ≤ #T ∧
      T ⊆ A - A ∧
      ‖μ T ∗ᵈ^ boost ∗ᵈ (μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) -
          μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C‖_[∞] ≤ epsilon := by
  obtain ⟨T, hKT, hTsub, hT⟩ := linfty_almost_periodicity_contained
    (epsilon / boost) (by positivity)
    (div_le_one_of_le₀
      (hepsilon₁.trans (mod_cast Nat.one_le_iff_ne_zero.2 hboost))
      (by positivity)) hK₂ hK hA hS B C hB hC
  refine ⟨T, by simpa only [div_pow, div_div_eq_mul_div] using hKT,
    hTsub, ?_⟩
  set F := μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C
  have hTne : T.Nonempty := by
    have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK₂
    have : (0 : ℝ) < #T := hKT.trans_lt' (by positivity)
    simpa [Finset.card_pos] using this
  calc
    (‖μ T ∗ᵈ^ boost ∗ᵈ F - F‖_[∞] : ℝ) =
        ‖𝔼 a ∈ T ^^ boost, (τ (∑ i, a i) F - F)‖_[∞] := by
      rw [mu_iterConv_ddconv, expect_sub_distrib,
        expect_const hTne.piFinset_const]
    _ ≤ 𝔼 a ∈ T ^^ boost, ‖τ (∑ i, a i) F - F‖_[∞] :=
      MeasureTheory.dLpNorm_expect_le le_top
    _ ≤ 𝔼 _a ∈ T ^^ boost, epsilon := by
      refine expect_le_expect fun x hx ↦ ?_
      calc
        (‖τ (∑ i, x i) F - F‖_[∞] : ℝ) ≤
            ∑ i, ‖τ (x i) F - F‖_[∞] :=
          MeasureTheory.dLpNorm_translate_sum_sub_le le_top _ _ _
        _ ≤ ∑ _i, epsilon / boost := by
          gcongr
          exact hT _ (Fintype.mem_piFinset.1 hx _)
        _ = epsilon := by
          simp only [sum_const, card_fin, nsmul_eq_mul]
          rw [mul_div_cancel₀]
          positivity
    _ = epsilon := by rw [expect_const hTne.piFinset_const]

end AlmostPeriodicity
