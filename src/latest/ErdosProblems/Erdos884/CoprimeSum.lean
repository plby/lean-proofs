/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.Energy

open Finset

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — Lemma B.3: lower bound for the weighted sum over squarefree numbers
coprime to `m`.

Exports `Erdos884.coprime_squarefree_sum_lower`:
`∃ c₀ > 0, ∃ w₀, ∀ w ≥ w₀, ∀ m ≥ 1 with m ≤ (log w)³,`
`  c₀ · (φ(m)/m)² · (log w)² ≤ Σ_{ℓ ≤ w, squarefree, coprime to m} 2^ω(ℓ)/ℓ`.
-/

namespace Erdos884

/-! ## Counting integers coprime to `m` in intervals -/

/-- A general "sum over an injection" helper. -/
lemma cs_sum_le_sum_inj {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    (e : α → β) (f : α → ℝ) (g : β → ℝ)
    (hmaps : ∀ a ∈ s, e a ∈ t) (hinj : Set.InjOn e ↑s)
    (hval : ∀ a ∈ s, f a ≤ g (e a)) (hg : ∀ b ∈ t, 0 ≤ g b) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, g b := by
  calc ∑ a ∈ s, f a ≤ ∑ a ∈ s, g (e a) := Finset.sum_le_sum hval
    _ = ∑ b ∈ s.image e, g b := (Finset.sum_image hinj).symm
    _ ≤ ∑ b ∈ t, g b := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr hmaps) (fun b hb _ => hg b hb)

/-- Exact count of integers coprime to `m` in a run of `q` full blocks of length `m`. -/
lemma cs_cnt_blocks (m n q : ℕ) :
    ((Finset.Ico n (n + q * m)).filter (fun a => Nat.Coprime a m)).card = q * m.totient := by
  induction q with
  | zero => simp
  | succ k ih =>
    have hblock : ((Finset.Ico (n + k * m) (n + k * m + m)).filter
        (fun a => Nat.Coprime a m)).card = m.totient := by
      rw [show (Finset.filter (fun a => Nat.Coprime a m)
            (Finset.Ico (n + k * m) (n + k * m + m)))
          = (Finset.filter (fun x => Nat.Coprime m x)
            (Finset.Ico (n + k * m) (n + k * m + m))) from
        Finset.filter_congr (fun x _ => Nat.coprime_comm)]
      exact Nat.filter_coprime_Ico_eq_totient m (n + k * m)
    have hkey : n + (k + 1) * m = (n + k * m) + m := by ring
    rw [hkey, ← Finset.Ico_union_Ico_eq_Ico (a := n) (b := n + k * m) (c := n + k * m + m)
        (by omega) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, hblock]
    ring

/-- Upper bound for the number of integers coprime to `m` in any interval of length `L`. -/
lemma cs_cnt_upper (m : ℕ) (hm : 0 < m) (n L : ℕ) :
    ((Finset.Ico n (n + L)).filter (fun a => Nat.Coprime a m)).card
      ≤ (L / m + 1) * m.totient := by
  have hL : L < (L / m + 1) * m := by
    have h1 := Nat.div_add_mod L m
    have h2 : L % m < m := Nat.mod_lt L hm
    calc L = m * (L / m) + L % m := h1.symm
      _ < m * (L / m) + m := by omega
      _ = (L / m + 1) * m := by ring
  have hsub : Finset.Ico n (n + L) ⊆ Finset.Ico n (n + (L / m + 1) * m) :=
    Finset.Ico_subset_Ico le_rfl (by omega)
  exact le_of_le_of_eq (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
    (cs_cnt_blocks m n (L / m + 1))

/-- Lower bound for the number of integers coprime to `m` in the block `(v, 2v]`. -/
lemma cs_cnt_lower (m v : ℕ) :
    (v / m) * m.totient ≤ ((Finset.Ioc v (2 * v)).filter (fun a => Nat.Coprime a m)).card := by
  have hsub : Finset.Ico (v + 1) (v + 1 + (v / m) * m) ⊆ Finset.Ioc v (2 * v) := by
    intro a ha
    simp only [Finset.mem_Ico] at ha
    simp only [Finset.mem_Ioc]
    have := Nat.div_mul_le_self v m
    omega
  calc (v / m) * m.totient
      = ((Finset.Ico (v + 1) (v + 1 + (v / m) * m)).filter (fun a => Nat.Coprime a m)).card :=
        (cs_cnt_blocks m (v + 1) (v / m)).symm
    _ ≤ _ := Finset.card_le_card (Finset.filter_subset_filter _ hsub)

lemma cs_two_mul_div_le (A c : ℕ) (hc : 0 < c) : 2 * A / c ≤ 2 * (A / c) + 1 := by
  rw [two_mul, Nat.add_div hc]
  split <;> omega

/-- Count of multiples of `c = p²` coprime to `m` in the block `(v, 2v]`. -/
lemma cs_cnt_sq_dvd (m : ℕ) (hm : 0 < m) (v p : ℕ) (hp : 0 < p) :
    ((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card
      ≤ (v / (p * p) / m + 2) * m.totient := by
  set c := p * p with hcdef
  have hc0 : 0 < c := Nat.mul_pos hp hp
  have hle : v / c ≤ 2 * v / c := Nat.div_le_div_right (by omega)
  -- Step 1: inject `a ↦ a / c` into the coprime elements of `Ioc (v/c) (2v/c)`.
  have hcard : ((Finset.Ioc v (2 * v)).filter (fun a => c ∣ a ∧ Nat.Coprime a m)).card
      ≤ ((Finset.Ioc (v / c) (2 * v / c)).filter (fun b => Nat.Coprime b m)).card := by
    apply Finset.card_le_card_of_injOn (fun a => a / c)
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at ha ⊢
      obtain ⟨⟨hva, ha2v⟩, hdvd, hcop⟩ := ha
      refine ⟨⟨?_, Nat.div_le_div_right ha2v⟩, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hc0, Nat.div_mul_cancel hdvd]
        exact hva
      · exact Nat.Coprime.coprime_dvd_left ⟨c, (Nat.div_mul_cancel hdvd).symm⟩ hcop
    · intro a₁ h₁ a₂ h₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at h₁ h₂
      have e₁ : c * (a₁ / c) = a₁ := Nat.mul_div_cancel' h₁.2.1
      have e₂ : c * (a₂ / c) = a₂ := Nat.mul_div_cancel' h₂.2.1
      simp only at heq
      rw [← e₁, ← e₂, heq]
  -- Step 2: bound the target cardinality.
  have hIoc : Finset.Ioc (v / c) (2 * v / c)
      = Finset.Ico (v / c + 1) ((v / c + 1) + (2 * v / c - v / c)) := by
    ext y
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have h2 : ((Finset.Ioc (v / c) (2 * v / c)).filter (fun b => Nat.Coprime b m)).card
      ≤ ((2 * v / c - v / c) / m + 1) * m.totient := by
    rw [hIoc]
    exact cs_cnt_upper m hm _ _
  have h3 : (2 * v / c - v / c) / m + 1 ≤ v / c / m + 2 := by
    have hlen : 2 * v / c - v / c ≤ v / c + 1 := by
      have := cs_two_mul_div_le v c hc0
      omega
    have : (2 * v / c - v / c) / m ≤ (v / c + 1) / m := Nat.div_le_div_right hlen
    have h4 : (v / c + 1) / m ≤ (v / c + m) / m := Nat.div_le_div_right (by omega)
    rw [Nat.add_div_right _ hm] at h4
    omega
  calc ((Finset.Ioc v (2 * v)).filter (fun a => c ∣ a ∧ Nat.Coprime a m)).card
      ≤ ((2 * v / c - v / c) / m + 1) * m.totient := le_trans hcard h2
    _ ≤ (v / c / m + 2) * m.totient := Nat.mul_le_mul_right _ h3

/-! ## Inverse-square sums via telescoping -/

lemma cs_telescope_le (B : ℕ) (f : ℕ → ℝ) (hfB : 0 ≤ f B) :
    ∑ i ∈ Finset.range B, (f i - f (i + 1)) ≤ f 0 := by
  rw [Finset.sum_range_sub' f B]
  linarith

lemma cs_real_ineq1 (x : ℝ) (hx : 0 ≤ x) :
    1 / ((x + 3) * (x + 3)) ≤ 1 / (x + 2) - 1 / (x + 1 + 2) := by
  have h1 : (0:ℝ) < x + 2 := by linarith
  have h2 : (0:ℝ) < x + 3 := by linarith
  have key : 1 / (x + 2) - 1 / (x + 1 + 2) = 1 / ((x + 2) * (x + 3)) := by
    rw [show x + 1 + 2 = x + 3 by ring]
    field_simp
    ring
  rw [key]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

lemma cs_real_ineq2 (x : ℝ) (hx : 0 ≤ x) :
    1 / ((2 * x + 3) * (2 * x + 3)) ≤ 1 / (4 * (x + 1)) - 1 / (4 * (x + 1 + 1)) := by
  have key : 1 / (4 * (x + 1)) - 1 / (4 * (x + 1 + 1)) = 1 / (4 * ((x + 1) * (x + 2))) := by
    rw [show x + 1 + 1 = x + 2 by ring]
    field_simp
    ring
  rw [key]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

/-- Sum of `1/g²` over a finite set of naturals all `≥ 3` is at most `1/2`. -/
lemma cs_inv_sq_sum_ge3 (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 3 ≤ g) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 1 / 2 := by
  set B := Q.sup id + 1 with hB
  set F : ℕ → ℝ := fun i => (1:ℝ) / ((i:ℝ) + 2) with hF
  have hchain : ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g)
      ≤ ∑ i ∈ Finset.range B, (F i - F (i + 1)) := by
    apply cs_sum_le_sum_inj (fun g => g - 3)
    · intro g hg
      simp only [Finset.mem_range]
      have := Finset.le_sup (f := id) hg
      simp only [id_eq] at this
      omega
    · intro g₁ h₁ g₂ h₂ heq
      simp only [Finset.mem_coe] at h₁ h₂
      have := hQ g₁ h₁
      have := hQ g₂ h₂
      simp only at heq
      omega
    · intro g hg
      obtain ⟨d, rfl⟩ : ∃ d, g = d + 3 := ⟨g - 3, by have := hQ g hg; omega⟩
      simp only [Nat.add_sub_cancel, hF]
      push_cast
      exact cs_real_ineq1 (d:ℝ) (Nat.cast_nonneg d)
    · intro b _
      simp only [hF, sub_nonneg]
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast
        linarith
  have hend : ∑ i ∈ Finset.range B, (F i - F (i + 1)) ≤ F 0 :=
    cs_telescope_le B F (by simp only [hF]; positivity)
  have hF0 : F 0 = 1/2 := by simp only [hF]; norm_num
  exact hchain.trans (hend.trans hF0.le)

/-- Sum of `1/g²` over a finite set of odd naturals all `≥ 3` is at most `1/4`. -/
lemma cs_inv_sq_sum_odd (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 3 ≤ g ∧ g % 2 = 1) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 1 / 4 := by
  set B := Q.sup id + 1 with hB
  set F : ℕ → ℝ := fun i => (1:ℝ) / (4 * ((i:ℝ) + 1)) with hF
  have hchain : ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g)
      ≤ ∑ i ∈ Finset.range B, (F i - F (i + 1)) := by
    apply cs_sum_le_sum_inj (fun g => (g - 3) / 2)
    · intro g hg
      simp only [Finset.mem_range]
      have := Finset.le_sup (f := id) hg
      simp only [id_eq] at this
      omega
    · intro g₁ h₁ g₂ h₂ heq
      simp only [Finset.mem_coe] at h₁ h₂
      have := hQ g₁ h₁
      have := hQ g₂ h₂
      simp only at heq
      omega
    · intro g hg
      obtain ⟨d, rfl⟩ : ∃ d, g = 2 * d + 3 :=
        ⟨(g - 3) / 2, by have := hQ g hg; omega⟩
      have hidx : (2 * d + 3 - 3) / 2 = d := by omega
      rw [hidx]
      simp only [hF]
      push_cast
      exact cs_real_ineq2 (d:ℝ) (Nat.cast_nonneg d)
    · intro b _
      simp only [hF, sub_nonneg]
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast
        linarith
  have hend : ∑ i ∈ Finset.range B, (F i - F (i + 1)) ≤ F 0 :=
    cs_telescope_le B F (by simp only [hF]; positivity)
  have hF0 : F 0 = 1/4 := by simp only [hF]; norm_num
  exact hchain.trans (hend.trans hF0.le)

/-- Sum of `1/p²` over a finite set of primes is at most `1/2`. -/
lemma cs_prime_inv_sq_sum (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * p) ≤ 1 / 2 := by
  have hodd : ∀ p ∈ P.erase 2, 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp
    obtain ⟨hne, hp'⟩ := Finset.mem_erase.mp hp
    have hprime := hP p hp'
    have h1 : p % 2 = 1 := Nat.odd_iff.mp (hprime.odd_of_ne_two hne)
    have h2 := hprime.two_le
    omega
  by_cases h2 : 2 ∈ P
  · rw [← Finset.sum_erase_add P _ h2]
    have herase := cs_inv_sq_sum_odd _ hodd
    have hval : (1:ℝ) / (((2:ℕ):ℝ) * ((2:ℕ):ℝ)) = 1/4 := by norm_num
    rw [hval]
    linarith
  · have hall : ∀ p ∈ P, 3 ≤ p ∧ p % 2 = 1 := fun p hp =>
      hodd p (Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ hp), hp⟩)
    have := cs_inv_sq_sum_odd P hall
    linarith

/-- Sum of `1/g²` over a finite set of naturals all `≥ 2` is at most `3/4`. -/
lemma cs_inv_sq_sum_ge2 (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 2 ≤ g) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 3 / 4 := by
  have hge3 : ∀ g ∈ Q.erase 2, 3 ≤ g := by
    intro g hg
    obtain ⟨hne, hg'⟩ := Finset.mem_erase.mp hg
    have := hQ g hg'
    omega
  by_cases h2 : 2 ∈ Q
  · rw [← Finset.sum_erase_add Q _ h2]
    have herase := cs_inv_sq_sum_ge3 _ hge3
    have hval : (1:ℝ) / (((2:ℕ):ℝ) * ((2:ℕ):ℝ)) = 1/4 := by norm_num
    rw [hval]
    linarith
  · have hall : ∀ g ∈ Q, 3 ≤ g := fun g hg =>
      hge3 g (Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ hg), hg⟩)
    have := cs_inv_sq_sum_ge3 Q hall
    linarith

/-! ## Squarefree numbers coprime to `m` in dyadic blocks -/

/-- Non-squarefree coprime elements of `(v, 2v]` are covered by multiples of `p²`, `p ≤ √(2v)`. -/
lemma cs_nonsq_subset (m v : ℕ) :
    (Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m) ⊆
      ((Finset.Icc 2 (Nat.sqrt (2 * v))).filter Nat.Prime).biUnion
        (fun p => (Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)) := by
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
  obtain ⟨⟨hva, ha2v⟩, hnsq, hcop⟩ := ha
  rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push Not at hnsq
  obtain ⟨p, hp, hpd⟩ := hnsq
  have hpa : p * p ≤ a := Nat.le_of_dvd (by omega) hpd
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  exact ⟨p, ⟨⟨hp.two_le, Nat.le_sqrt.mpr (by omega)⟩, hp⟩, ⟨hva, ha2v⟩, hpd, hcop⟩

/-- Real bound on the number of non-squarefree coprime elements of `(v, 2v]`. -/
lemma cs_nonsq_card (m v : ℕ) (hm : 0 < m) :
    (((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      ≤ (v : ℝ) * m.totient / (2 * m) + 2 * (Nat.sqrt (2 * v) : ℝ) * m.totient := by
  set P := (Finset.Icc 2 (Nat.sqrt (2 * v))).filter Nat.Prime with hPdef
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hcards : ((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card
      ≤ ∑ p ∈ P, ((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card :=
    le_trans (Finset.card_le_card (cs_nonsq_subset m v)) Finset.card_biUnion_le
  have hterm : ∀ p ∈ P,
      (((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient := by
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp0 : 0 < p := hprime.pos
    have hpR : (0:ℝ) < p := by exact_mod_cast hp0
    have h1 := cs_cnt_sq_dvd m hm v p hp0
    have h1R : (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (((v / (p * p) / m : ℕ) : ℝ) + 2) * (m.totient : ℝ) := by
      exact_mod_cast h1
    have h2 : ((v / (p * p) / m : ℕ) : ℝ) ≤ (v:ℝ) / ((p:ℝ) * p * m) := by
      rw [Nat.div_div_eq_div_mul]
      calc ((v / (p * p * m) : ℕ) : ℝ) ≤ (v:ℝ) / ((p * p * m : ℕ) : ℝ) := Nat.cast_div_le
        _ = (v:ℝ) / ((p:ℝ) * p * m) := by push_cast; ring
    calc (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (((v / (p * p) / m : ℕ) : ℝ) + 2) * (m.totient : ℝ) := h1R
      _ ≤ ((v:ℝ) / ((p:ℝ) * p * m) + 2) * (m.totient : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient := by
          field_simp
  have hPcard : (P.card : ℝ) ≤ (Nat.sqrt (2 * v) : ℝ) := by
    have h1 : P.card ≤ (Finset.Icc 2 (Nat.sqrt (2 * v))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Nat.card_Icc] at h1
    have : P.card ≤ Nat.sqrt (2 * v) := by omega
    exact_mod_cast this
  have hsum := cs_prime_inv_sq_sum P (fun p hp => (Finset.mem_filter.mp hp).2)
  calc (((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      ≤ ∑ p ∈ P, (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ) := by exact_mod_cast hcards
    _ ≤ ∑ p ∈ P, ((v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient) :=
        Finset.sum_le_sum hterm
    _ = (v:ℝ) * m.totient / m * (∑ p ∈ P, 1 / ((p:ℝ) * p)) + P.card * (2 * m.totient) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (v:ℝ) * m.totient / m * (1/2) + (Nat.sqrt (2 * v) : ℝ) * (2 * m.totient) := by
        have hnn : (0:ℝ) ≤ (v:ℝ) * m.totient / m := by positivity
        have h1 := mul_le_mul_of_nonneg_left hsum hnn
        have h2 := mul_le_mul_of_nonneg_right hPcard
          (show (0:ℝ) ≤ 2 * m.totient by positivity)
        linarith
    _ = (v : ℝ) * m.totient / (2 * m) + 2 * (Nat.sqrt (2 * v) : ℝ) * m.totient := by ring

/-- The pure real-arithmetic core of the block-count bound. -/
lemma cs_real_block_core (mR vR D s : ℝ) (hm : 1 ≤ mR)
    (hv : 256 * mR^2 ≤ vR) (hD : vR - mR ≤ D * mR) (hs : s ≤ Real.sqrt 2 * Real.sqrt vR) :
    vR/(4*mR) + vR/(2*mR) + 2*s ≤ D := by
  have hm0 : (0:ℝ) < mR := by linarith
  have hv0 : (0:ℝ) ≤ vR := by nlinarith
  set x := Real.sqrt vR with hx
  have hxnn : (0:ℝ) ≤ x := Real.sqrt_nonneg vR
  have hxx : x * x = vR := Real.mul_self_sqrt hv0
  have hx16 : 16 * mR ≤ x := by
    rw [hx]
    rw [show vR = vR from rfl]
    refine (Real.le_sqrt (by positivity) hv0).mpr ?_
    nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs' : s ≤ (3/2) * x := by
    calc s ≤ Real.sqrt 2 * x := hs
      _ ≤ (3/2) * x := mul_le_mul_of_nonneg_right hsqrt2 hxnn
  set u := vR / (4 * mR) with hu
  have h4x : 4 * x ≤ u := by
    rw [hu, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx16) hxnn]
  have hx1 : (1:ℝ) ≤ x := by nlinarith
  have e2 : vR / (2 * mR) = 2 * u := by
    rw [hu]; field_simp; ring
  have hDm : 4 * u - 1 ≤ D := by
    have h5 : (vR - mR) / mR ≤ D := (div_le_iff₀ hm0).mpr hD
    have e4 : (vR - mR) / mR = 4 * u - 1 := by
      rw [hu]; field_simp
    linarith [e4 ▸ h5]
  have hkey : 1 + 2 * s ≤ u := by
    calc 1 + 2*s ≤ 1 + 3*x := by linarith
      _ ≤ 4*x := by linarith
      _ ≤ u := h4x
  linarith

/-- Core counting bound: the block `(v, 2v]` contains at least `v·φ(m)/(4m)` squarefree
numbers coprime to `m`, provided `v ≥ 256·m²`. -/
lemma cs_block_count (m v : ℕ) (hm : 1 ≤ m) (hv : 256 * m^2 ≤ v) :
    (v : ℝ) * m.totient / (4 * m)
      ≤ (((Finset.Ioc v (2 * v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ) := by
  have hm0 : 0 < m := hm
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hφ : 0 < m.totient := Nat.totient_pos.mpr hm0
  have hφR : (0:ℝ) < (m.totient : ℝ) := by exact_mod_cast hφ
  -- partition of the coprime elements into squarefree / non-squarefree
  have e1 : (Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).filter Squarefree := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => and_comm)
  have e2 : (Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).filter
          (fun a => ¬ Squarefree a) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => and_comm)
  have hpart : ((Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card
      + ((Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card := by
    rw [e1, e2]
    exact Finset.card_filter_add_card_filter_not _
  have hcast : (((Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      = (((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card : ℝ)
        - (((Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hpart
    push_cast at h
    linarith
  -- lower bound for the coprime count
  have hDR : ((v / m : ℕ) : ℝ) * (m.totient : ℝ)
      ≤ (((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card : ℝ) := by
    exact_mod_cast cs_cnt_lower m v
  -- upper bound for the non-squarefree coprime count
  have hNS := cs_nonsq_card m v hm0
  -- the real core
  have hD' : (v:ℝ) - m ≤ ((v / m : ℕ) : ℝ) * m := by
    have h1 := Nat.div_add_mod v m
    have h2 : v % m < m := Nat.mod_lt v hm0
    have h3 : (m:ℝ) * ((v / m : ℕ) : ℝ) + ((v % m : ℕ) : ℝ) = (v:ℝ) := by exact_mod_cast h1
    have h4 : ((v % m : ℕ) : ℝ) < m := by exact_mod_cast h2
    nlinarith [mul_comm ((v / m : ℕ) : ℝ) ((m:ℕ) : ℝ)]
  have hs' : ((Nat.sqrt (2 * v) : ℕ) : ℝ) ≤ Real.sqrt 2 * Real.sqrt v := by
    have h1 : (Nat.sqrt (2 * v))^2 ≤ 2 * v := Nat.sqrt_le' (2 * v)
    have h2 : ((Nat.sqrt (2 * v) : ℕ) : ℝ) ≤ Real.sqrt ((2 * v : ℕ) : ℝ) := by
      refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
      exact_mod_cast h1
    have h3 : Real.sqrt ((2 * v : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt v := by
      rw [show ((2 * v : ℕ) : ℝ) = 2 * (v:ℝ) by push_cast; ring]
      exact Real.sqrt_mul (by norm_num) _
    linarith [h3 ▸ h2]
  have hvR : 256 * (m:ℝ)^2 ≤ (v:ℝ) := by exact_mod_cast hv
  have hcore := cs_real_block_core (m:ℝ) (v:ℝ) ((v / m : ℕ) : ℝ)
    ((Nat.sqrt (2 * v) : ℕ) : ℝ) hmR hvR hD' hs'
  -- combine everything
  have hmul := mul_le_mul_of_nonneg_right hcore hφR.le
  have r1 : ((v:ℝ)/(4*(m:ℝ)) + (v:ℝ)/(2*(m:ℝ)) + 2*((Nat.sqrt (2 * v) : ℕ) : ℝ))
        * (m.totient : ℝ)
      = (v:ℝ) * m.totient / (4*m) + (v:ℝ) * m.totient / (2*m)
        + 2 * ((Nat.sqrt (2 * v) : ℕ) : ℝ) * m.totient := by ring
  linarith [hmul, r1, hcast, hDR, hNS]

/-! ## The dyadic harmonic sum -/

/-- Each dyadic block `(2^j, 2^{j+1}]` with `2^j ≥ 256·m²` contributes at least
`φ(m)/(8m)` to the harmonic sum over squarefree numbers coprime to `m`. -/
lemma cs_block_harmonic (m j : ℕ) (hm : 1 ≤ m) (hv : 256 * m^2 ≤ 2^j) :
    (m.totient : ℝ) / (8 * m)
      ≤ ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
          (1:ℝ)/a := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hpow : (2:ℕ)^(j+1) = 2 * 2^j := by rw [pow_succ]; ring
  have hcount := cs_block_count m (2^j) hm hv
  rw [show (2:ℕ) * 2^j = 2^(j+1) from hpow.symm] at hcount
  have hterm : ∀ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
      (fun a => Squarefree a ∧ Nat.Coprime a m),
      (1:ℝ)/((2^(j+1) : ℕ) : ℝ) ≤ (1:ℝ)/(a : ℝ) := by
    intro a ha
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hmem
    have ha0 : 0 < a := by
      have := pow_pos (show 0 < 2 by norm_num) j
      omega
    apply one_div_le_one_div_of_le
    · exact_mod_cast ha0
    · exact_mod_cast h2
  have h5 : ((((Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ)) * (1/((2^(j+1) : ℕ) : ℝ))
      ≤ ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hterm
  have heq : ((2^j : ℕ) : ℝ) * m.totient / (4 * m) * (1/((2^(j+1) : ℕ) : ℝ))
      = (m.totient : ℝ) / (8 * m) := by
    have c1 : ((2^j : ℕ) : ℝ) = (2:ℝ)^j := by push_cast; ring
    have c2 : ((2^(j+1) : ℕ) : ℝ) = 2 * (2:ℝ)^j := by
      rw [hpow]; push_cast; ring
    rw [c1, c2]
    have hne : ((2:ℝ))^j ≠ 0 := by positivity
    have hmne : ((m:ℕ) : ℝ) ≠ 0 := ne_of_gt hmR
    field_simp
    ring
  have h6 := mul_le_mul_of_nonneg_right hcount
    (show (0:ℝ) ≤ 1/((2^(j+1) : ℕ) : ℝ) by positivity)
  calc (m.totient : ℝ)/(8*m)
      = ((2^j : ℕ) : ℝ) * m.totient / (4 * m) * (1/((2^(j+1) : ℕ) : ℝ)) := heq.symm
    _ ≤ _ := h6
    _ ≤ _ := h5

/-- Dyadic decomposition: `j₁ - j₀ + 1` disjoint blocks each contribute `φ(m)/(8m)`. -/
lemma cs_dyadic (m x : ℕ) (hm : 1 ≤ m) (j₀ j₁ : ℕ) (hj : j₀ ≤ j₁)
    (h₀ : 256 * m^2 ≤ 2^j₀) (h₁ : 2^(j₁+1) ≤ x) :
    ((j₁ - j₀ + 1 : ℕ) : ℝ) * m.totient / (8 * m)
      ≤ ∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
  have hdisj : (↑(Finset.Icc j₀ j₁) : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m)) := by
    have key : ∀ i' j' : ℕ, i' < j' → Disjoint
        ((Finset.Ioc (2^i') (2^(i'+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m))
        ((Finset.Ioc (2^j') (2^(j'+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) := by
      intro i' j' hij
      apply Finset.disjoint_filter_filter
      rw [Finset.Ioc_disjoint_Ioc]
      calc min (2^(i'+1)) (2^(j'+1)) ≤ 2^(i'+1) := min_le_left _ _
        _ ≤ 2^j' := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ max (2^i') (2^j') := le_max_right _ _
    intro i _ j _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hsub : (Finset.Icc j₀ j₁).biUnion
      (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m))
      ⊆ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) := by
    intro a ha
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at ha ⊢
    obtain ⟨j, ⟨_, hjj1⟩, ⟨hja, haj⟩, hprops⟩ := ha
    refine ⟨⟨?_, ?_⟩, hprops⟩
    · have := pow_pos (show 0 < 2 by norm_num) j
      omega
    · calc a ≤ 2^(j+1) := haj
        _ ≤ 2^(j₁+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ x := h₁
  calc ((j₁ - j₀ + 1 : ℕ) : ℝ) * m.totient / (8 * m)
      = ∑ _j ∈ Finset.Icc j₀ j₁, (m.totient : ℝ) / (8 * m) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
          show j₁ + 1 - j₀ = j₁ - j₀ + 1 from by omega]
        ring
    _ ≤ ∑ j ∈ Finset.Icc j₀ j₁, ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
        apply Finset.sum_le_sum
        intro j hjmem
        have hj0 : j₀ ≤ j := (Finset.mem_Icc.mp hjmem).1
        exact cs_block_harmonic m j hm
          (le_trans h₀ (Nat.pow_le_pow_right (by norm_num) hj0))
    _ = ∑ a ∈ (Finset.Icc j₀ j₁).biUnion (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m)), (1:ℝ)/a :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro a _ _
        positivity

/-! ## From coprime pairs to the weighted sum over products -/

/-- The sum of `1/(ab)` over coprime pairs of squarefree numbers `≤ x` coprime to `m` is
dominated by the sum of `2^ω(ℓ)/ℓ` over squarefree `ℓ ≤ w` coprime to `m`, when `x² ≤ w`. -/
lemma cs_pairs_to_sum (m x w : ℕ) (hxx : x * x ≤ w) :
    ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
          ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
          (fun q => Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m),
          (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set Q := (T ×ˢ T).filter (fun q : ℕ × ℕ => Nat.Coprime q.1 q.2) with hQ
  have hmem : ∀ q ∈ Q, (1 ≤ q.1 ∧ q.1 ≤ x ∧ Squarefree q.1 ∧ Nat.Coprime q.1 m) ∧
      (1 ≤ q.2 ∧ q.2 ≤ x ∧ Squarefree q.2 ∧ Nat.Coprime q.2 m) ∧ Nat.Coprime q.1 q.2 := by
    intro q hq
    simp only [hQ, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
    tauto
  have himg : Q.image (fun q : ℕ × ℕ => q.1 * q.2)
      ⊆ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m) := by
    intro ℓ hℓ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
    obtain ⟨⟨h11, h1x, h1sq, h1m⟩, ⟨h21, h2x, h2sq, h2m⟩, h12⟩ := hmem q hq
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact le_trans (Nat.mul_le_mul h1x h2x) hxx
    · exact (Nat.squarefree_mul h12).mpr ⟨h1sq, h2sq⟩
    · exact Nat.Coprime.mul_left h1m h2m
  have hfiber : ∀ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2),
      ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ)
        ≤ (2:ℝ)^(ℓ.primeFactors.card) := by
    intro ℓ hℓ
    have hℓ0 : ℓ ≠ 0 := by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
      obtain ⟨⟨h11, _, _, _⟩, ⟨h21, _, _, _⟩, _⟩ := hmem q hq
      exact Nat.mul_ne_zero (by omega) (by omega)
    have hcard : (Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card
        ≤ (ℓ.primeFactors.powerset).card := by
      apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => q.1.primeFactors)
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter] at hq
        obtain ⟨hqQ, hqℓ⟩ := hq
        simp only [Finset.mem_coe, Finset.mem_powerset]
        exact Nat.primeFactors_mono ⟨q.2, hqℓ.symm⟩ hℓ0
      · intro q hq q' hq' heq
        simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
        obtain ⟨hqQ, hqℓ⟩ := hq
        obtain ⟨hq'Q, hq'ℓ⟩ := hq'
        obtain ⟨⟨h11, _, h1sq, _⟩, ⟨h21, _, _, _⟩, _⟩ := hmem q hqQ
        obtain ⟨⟨h11', _, h1sq', _⟩, ⟨h21', _, _, _⟩, _⟩ := hmem q' hq'Q
        have e1 : q.1 = q'.1 := by
          have p1 := Nat.prod_primeFactors_of_squarefree h1sq
          have p2 := Nat.prod_primeFactors_of_squarefree h1sq'
          rw [← p1, ← p2]
          exact Finset.prod_congr heq (fun _ _ => rfl)
        have e2 : q.2 = q'.2 := by
          have h := hqℓ.trans hq'ℓ.symm
          rw [e1] at h
          exact Nat.eq_of_mul_eq_mul_left (by omega) h
        exact Prod.ext e1 e2
    rw [Finset.card_powerset] at hcard
    calc ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ)
        ≤ ((2^(ℓ.primeFactors.card) : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (2:ℝ)^(ℓ.primeFactors.card) := by push_cast; ring
  calc ∑ q ∈ Q, (1:ℝ)/((q.1 : ℝ) * q.2)
      = ∑ q ∈ Q, (fun ℓ : ℕ => (1:ℝ)/(ℓ:ℝ)) (q.1 * q.2) := by
        apply Finset.sum_congr rfl
        intro q _
        push_cast
        ring
    _ = ∑ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2),
          (Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card • ((1:ℝ)/(ℓ:ℝ)) :=
        Finset.sum_comp (fun ℓ : ℕ => (1:ℝ)/(ℓ:ℝ)) (fun q : ℕ × ℕ => q.1 * q.2)
    _ ≤ ∑ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2), (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        rw [nsmul_eq_mul]
        have h1 := hfiber ℓ hℓ
        have h2 : (0:ℝ) ≤ 1/(ℓ:ℝ) := by positivity
        calc ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ) * ((1:ℝ)/(ℓ:ℝ))
            ≤ (2:ℝ)^(ℓ.primeFactors.card) * ((1:ℝ)/(ℓ:ℝ)) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by rw [mul_one_div]
    _ ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m),
          (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himg
        intro ℓ _ _
        positivity

/-- Pairs with a common factor contribute at most `(3/4)·S²`. -/
lemma cs_noncop_bound (m x : ℕ) :
    ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
          ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
          (fun q => ¬ Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ 3/4 * ((∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
            (1:ℝ)/a)
          * (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
            (1:ℝ)/a)) := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set S := ∑ a ∈ T, (1:ℝ)/a with hS
  have hbound : ∑ q ∈ (T ×ˢ T).filter (fun q : ℕ × ℕ => ¬ Nat.Coprime q.1 q.2),
        (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ))) := by
    apply cs_sum_le_sum_inj (fun q : ℕ × ℕ =>
      (Nat.gcd q.1 q.2, (q.1 / Nat.gcd q.1 q.2, q.2 / Nat.gcd q.1 q.2)))
    · -- maps to
      intro q hq
      simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      obtain ⟨⟨⟨⟨h11, h1x⟩, h1sq, h1m⟩, ⟨h21, h2x⟩, h2sq, h2m⟩, hncop⟩ := hq
      have hd0 : 0 < Nat.gcd q.1 q.2 := by
        rcases Nat.eq_zero_or_pos (Nat.gcd q.1 q.2) with h | h
        · rw [Nat.gcd_eq_zero_iff] at h
          omega
        · exact h
      have hd2 : 2 ≤ Nat.gcd q.1 q.2 := by
        rcases Nat.lt_or_ge (Nat.gcd q.1 q.2) 2 with h | h
        · have h1 : Nat.gcd q.1 q.2 = 1 := by omega
          exact absurd h1 hncop
        · exact h
      have hdx : Nat.gcd q.1 q.2 ≤ x :=
        le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) h1x
      have ha1 : q.1 / Nat.gcd q.1 q.2 ∣ q.1 :=
        ⟨Nat.gcd q.1 q.2, (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm⟩
      have hb1 : q.2 / Nat.gcd q.1 q.2 ∣ q.2 :=
        ⟨Nat.gcd q.1 q.2, (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm⟩
      simp only [hT, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hd2, hdx⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hd0
      · exact le_trans (Nat.div_le_self _ _) h1x
      · exact Squarefree.squarefree_of_dvd ha1 h1sq
      · exact Nat.Coprime.coprime_dvd_left ha1 h1m
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hd0
      · exact le_trans (Nat.div_le_self _ _) h2x
      · exact Squarefree.squarefree_of_dvd hb1 h2sq
      · exact Nat.Coprime.coprime_dvd_left hb1 h2m
    · -- injective
      intro q hq q' hq' heq
      simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc] at hq hq'
      obtain ⟨⟨⟨⟨h11, _⟩, _, _⟩, ⟨h21, _⟩, _, _⟩, _⟩ := hq
      obtain ⟨⟨⟨⟨h11', _⟩, _, _⟩, ⟨h21', _⟩, _, _⟩, _⟩ := hq'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hd, h1, h2⟩ := heq
      have a1 : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have a2 : Nat.gcd q'.1 q'.2 * (q'.1 / Nat.gcd q'.1 q'.2) = q'.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have b1 : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have b2 : Nat.gcd q'.1 q'.2 * (q'.2 / Nat.gcd q'.1 q'.2) = q'.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have e1 : q.1 = q'.1 := by
        calc q.1 = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := a1.symm
          _ = Nat.gcd q'.1 q'.2 * (q'.1 / Nat.gcd q'.1 q'.2) := by rw [h1, hd]
          _ = q'.1 := a2
      have e2 : q.2 = q'.2 := by
        calc q.2 = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := b1.symm
          _ = Nat.gcd q'.1 q'.2 * (q'.2 / Nat.gcd q'.1 q'.2) := by rw [h2, hd]
          _ = q'.2 := b2
      exact Prod.ext e1 e2
    · -- value inequality (in fact equality)
      intro q hq
      simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      obtain ⟨⟨⟨⟨h11, _⟩, _, _⟩, ⟨h21, _⟩, _, _⟩, _⟩ := hq
      have hd0 : 0 < Nat.gcd q.1 q.2 := by
        rcases Nat.eq_zero_or_pos (Nat.gcd q.1 q.2) with h | h
        · rw [Nat.gcd_eq_zero_iff] at h
          omega
        · exact h
      have ha : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hb : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have ha0 : 0 < q.1 / Nat.gcd q.1 q.2 :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hd0
      have hb0 : 0 < q.2 / Nat.gcd q.1 q.2 :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hd0
      have haR : (q.1 : ℝ) = (Nat.gcd q.1 q.2 : ℝ) * ((q.1 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by
        exact_mod_cast ha.symm
      have hbR : (q.2 : ℝ) = (Nat.gcd q.1 q.2 : ℝ) * ((q.2 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by
        exact_mod_cast hb.symm
      have hdR : (0:ℝ) < (Nat.gcd q.1 q.2 : ℝ) := by exact_mod_cast hd0
      have haR0 : (0:ℝ) < ((q.1 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by exact_mod_cast ha0
      have hbR0 : (0:ℝ) < ((q.2 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by exact_mod_cast hb0
      apply le_of_eq
      rw [haR, hbR]
      field_simp
    · -- nonnegativity on the target
      intro r _
      positivity
  have hinner : ∑ p ∈ T ×ˢ T, ((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ)) = S * S := by
    calc ∑ p ∈ T ×ˢ T, ((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ))
        = ∑ a ∈ T, ∑ b ∈ T, ((1:ℝ)/(a:ℝ)) * ((1:ℝ)/(b:ℝ)) := Finset.sum_product _ _ _
      _ = S * S := (Finset.sum_mul_sum T T (fun a => (1:ℝ)/(a:ℝ)) (fun b => (1:ℝ)/(b:ℝ))).symm
  have hteval : ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
        (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ)))
      = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) := by
    calc ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ)))
        = ∑ d ∈ Finset.Icc 2 x, ∑ p ∈ T ×ˢ T,
            (1:ℝ)/((d:ℝ) * d) * (((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ))) := Finset.sum_product _ _ _
      _ = ∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ) * d) * (S * S) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [← Finset.mul_sum, hinner]
      _ = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) :=
          (Finset.sum_mul (Finset.Icc 2 x) (fun d => (1:ℝ)/((d:ℝ)*d)) (S * S)).symm
  have hd34 := cs_inv_sq_sum_ge2 (Finset.Icc 2 x) (fun d hd => (Finset.mem_Icc.mp hd).1)
  have hSS : (0:ℝ) ≤ S * S := mul_self_nonneg S
  calc ∑ q ∈ (T ×ˢ T).filter (fun q : ℕ × ℕ => ¬ Nat.Coprime q.1 q.2),
        (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ))) := hbound
    _ = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) := hteval
    _ ≤ 3/4 * (S * S) := mul_le_mul_of_nonneg_right hd34 hSS

/-- The coprime-pair sum is at least a quarter of the squared harmonic sum. -/
lemma cs_coprime_pairs_lower (m x : ℕ) :
    (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a)
    * (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a) / 4
      ≤ ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
            ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
            (fun q => Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2) := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set S := ∑ a ∈ T, (1:ℝ)/a with hS
  have htotal : ∑ q ∈ T ×ˢ T, (1:ℝ)/((q.1:ℝ) * q.2) = S * S := by
    calc ∑ q ∈ T ×ˢ T, (1:ℝ)/((q.1:ℝ) * q.2)
        = ∑ a ∈ T, ∑ b ∈ T, (1:ℝ)/((a:ℝ) * b) := Finset.sum_product _ _ _
      _ = ∑ a ∈ T, ∑ b ∈ T, ((1:ℝ)/(a:ℝ)) * ((1:ℝ)/(b:ℝ)) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [div_mul_div_comm, one_mul]
      _ = S * S := (Finset.sum_mul_sum T T (fun a => (1:ℝ)/(a:ℝ)) (fun b => (1:ℝ)/(b:ℝ))).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (T ×ˢ T)
    (fun q : ℕ × ℕ => Nat.Coprime q.1 q.2) (fun q : ℕ × ℕ => (1:ℝ)/((q.1:ℝ) * q.2))
  have hnon := cs_noncop_bound m x
  rw [← hT, ← hS] at hnon
  linarith [hsplit, htotal, hnon]

/-! ## Choice of dyadic parameters -/

/-- `log y ≤ 2√y - 2` for positive `y`. -/
lemma cs_log_le_two_sqrt (y : ℝ) (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y - 2 := by
  have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
  have h2 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy.le
  linarith

/-- For `w ≥ 2^15000` and `1 ≤ m ≤ (log w)³` there is a long run of dyadic blocks
between `256·m²` and `√w`. -/
lemma cs_params (w m : ℕ) (hw : 2^15000 ≤ w) (hm : 1 ≤ m)
    (hmw : (m:ℝ) ≤ (Real.log w)^3) :
    ∃ j₀ j₁ : ℕ, j₀ ≤ j₁ ∧ 256 * m^2 ≤ 2^j₀ ∧ 2^(j₁+1) ≤ Nat.sqrt w ∧
      Real.log w / 8 ≤ ((j₁ - j₀ + 1 : ℕ) : ℝ) := by
  set x := Nat.sqrt w with hxdef
  set a := Nat.log 2 (256 * m^2) with hadef
  set b := Nat.log 2 x with hbdef
  set L := Real.log w with hLdef
  have hw1 : 1 ≤ w := le_trans Nat.one_le_two_pow hw
  have hwR : (1:ℝ) ≤ (w:ℝ) := by exact_mod_cast hw1
  have hwR0 : (0:ℝ) < (w:ℝ) := by linarith
  have hx1 : 1 ≤ x := by
    rw [hxdef]
    exact Nat.le_sqrt.mpr (by omega)
  have hxR0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx1
  have hmR1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hlog2pos : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h256 : 0 < 256 * m^2 := Nat.mul_pos (by norm_num) (pow_pos hm 2)
  -- `L` is large
  have hL : 10397 ≤ L := by
    have h1 : ((2:ℝ))^(15000:ℕ) ≤ (w:ℝ) := by exact_mod_cast hw
    have h2 : Real.log ((2:ℝ)^(15000:ℕ)) ≤ L := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith [Real.log_two_gt_d9]
  have hL0 : (0:ℝ) < L := by linarith
  -- `log x > L/2 - log 2`
  have hXlow : L/2 - Real.log 2 < Real.log x := by
    have h1 := Nat.lt_succ_sqrt w
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hxdef] at h1
    have hxx : w < 4*(x*x) := by
      calc w < (x+1)*(x+1) := h1
        _ ≤ (2*x)*(2*x) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4*(x*x) := by ring
    have hcast : (w:ℝ) < 4*((x:ℝ)*(x:ℝ)) := by exact_mod_cast hxx
    have hxne : (x:ℝ) ≠ 0 := ne_of_gt hxR0
    have h3 : L < Real.log (4*((x:ℝ)*(x:ℝ))) := Real.log_lt_log hwR0 hcast
    rw [Real.log_mul (by norm_num) (mul_ne_zero hxne hxne), Real.log_mul hxne hxne] at h3
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^(2:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  -- upper bound on `a·log 2`
  have haR : (a:ℝ) * Real.log 2 ≤ 8 * Real.log 2 + 6 * Real.log L := by
    have h1 : (2:ℕ)^(Nat.log 2 (256 * m^2)) ≤ 256 * m^2 := Nat.pow_log_le_self 2 h256.ne'
    rw [← hadef] at h1
    have h2 : ((2:ℝ))^a ≤ ((256 * m^2 : ℕ):ℝ) := by exact_mod_cast h1
    have h3 : Real.log ((2:ℝ)^a) ≤ Real.log ((256*m^2 : ℕ):ℝ) :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have hmne : (m:ℝ) ≠ 0 := by linarith
    have h4 : Real.log ((256*m^2 : ℕ):ℝ) = 8*Real.log 2 + 2*Real.log m := by
      have hc : ((256*m^2 : ℕ):ℝ) = 256 * (m:ℝ)^2 := by push_cast; ring
      rw [hc, Real.log_mul (by norm_num) (pow_ne_zero 2 hmne), Real.log_pow,
        show (256:ℝ) = 2^(8:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have h5 : Real.log (m:ℝ) ≤ 3 * Real.log L := by
      have h6 : Real.log (m:ℝ) ≤ Real.log (L^(3:ℕ)) :=
        Real.log_le_log (by linarith) hmw
      rwa [Real.log_pow, show ((3:ℕ):ℝ) = 3 by norm_num] at h6
    linarith
  -- lower bound on `b·log 2`
  have hbR : Real.log x < (b:ℝ) * Real.log 2 + Real.log 2 := by
    have h1 := Nat.lt_pow_succ_log_self (show (1:ℕ) < 2 by norm_num) x
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hbdef] at h1
    have h2 : (x:ℝ) < (2:ℝ)^(b+1) := by exact_mod_cast h1
    have h3 : Real.log x < Real.log ((2:ℝ)^(b+1)) := Real.log_lt_log hxR0 h2
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  -- `√L` bounds
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hsq101 : (101:ℝ) ≤ Real.sqrt L := by
    refine (Real.le_sqrt (by norm_num) hL0.le).mpr ?_
    norm_num
    linarith
  have hsqL : Real.sqrt L ≤ L / 101 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hsq, hsq101, Real.sqrt_nonneg L]
  have hlogL : Real.log L ≤ 2 * Real.sqrt L - 2 := cs_log_le_two_sqrt L hL0
  have hLlog2 : L * Real.log 2 ≤ 0.6931471808 * L := by
    have := mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) hL0.le
    linarith
  -- `b - a` is large
  have hba : (a:ℝ) + 3 < (b:ℝ) := by
    by_contra hcon
    push Not at hcon
    have h1 : (b:ℝ) * Real.log 2 ≤ ((a:ℝ) + 3) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hcon hlog2pos.le
    have h2 : ((a:ℝ)+3) * Real.log 2 = (a:ℝ)*Real.log 2 + 3*Real.log 2 := by ring
    linarith [Real.log_two_lt_d9]
  have hban : a + 3 < b := by exact_mod_cast hba
  -- the block count is large
  have hcnt : L/8 + 1 ≤ (b:ℝ) - a := by
    by_contra hcon
    push Not at hcon
    have h1 : ((b:ℝ) - a) * Real.log 2 ≤ (L/8 + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hcon) hlog2pos.le
    have h2 : ((b:ℝ) - a) * Real.log 2 = (b:ℝ)*Real.log 2 - (a:ℝ)*Real.log 2 := by ring
    have h3 : (L/8 + 1) * Real.log 2 = L*Real.log 2/8 + Real.log 2 := by ring
    linarith [Real.log_two_lt_d9]
  refine ⟨a + 1, b - 1, by omega, ?_, ?_, ?_⟩
  · have h1 := Nat.lt_pow_succ_log_self (show (1:ℕ) < 2 by norm_num) (256*m^2)
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hadef] at h1
    exact h1.le
  · rw [show b - 1 + 1 = b from by omega, hbdef]
    exact Nat.pow_log_le_self 2 (by omega)
  · rw [show (b - 1) - (a + 1) + 1 = b - a - 1 from by omega]
    have hc : ((b - a - 1 : ℕ):ℝ) = (b:ℝ) - a - 1 := by
      rw [show b - a - 1 = b - (a + 1) from by omega,
        Nat.cast_sub (by omega : a + 1 ≤ b)]
      push_cast
      ring
    rw [hc]
    linarith

/-! ## The exported theorem -/

/-- **Lemma B.3** (blueprint): for all large `w` and all `1 ≤ m ≤ (log w)³`,
`Σ_{ℓ ≤ w, squarefree, coprime to m} 2^ω(ℓ)/ℓ ≥ c₀·(φ(m)/m)²·(log w)²`. -/
theorem coprime_squarefree_sum_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w → ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ (Real.log w)^3 →
      c₀ * ((Nat.totient m : ℝ)/m)^2 * (Real.log w)^2
        ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime m),
            (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
  refine ⟨1/16384, by norm_num, 2^15000, ?_⟩
  intro w hw m hm hmw
  obtain ⟨j₀, j₁, hj, h0, h1, hcount⟩ := cs_params w m hw hm hmw
  have hxx : Nat.sqrt w * Nat.sqrt w ≤ w := by
    have := Nat.sqrt_le' w
    rwa [pow_two] at this
  have hS := cs_dyadic m (Nat.sqrt w) hm j₀ j₁ hj h0 h1
  have hpair := cs_coprime_pairs_lower m (Nat.sqrt w)
  have hsum := cs_pairs_to_sum m (Nat.sqrt w) w hxx
  set S := ∑ a ∈ (Finset.Icc 1 (Nat.sqrt w)).filter
      (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a with hSdef
  set L := Real.log w with hLdef
  set φ := (m.totient : ℝ) with hφdef
  set M := (m : ℝ) with hMdef
  have hM1 : (1:ℝ) ≤ M := by
    rw [hMdef]
    exact_mod_cast hm
  have hM0 : (0:ℝ) < M := by linarith
  have hMne : M ≠ 0 := ne_of_gt hM0
  have hφ0 : (0:ℝ) < φ := by
    rw [hφdef]
    exact_mod_cast Nat.totient_pos.mpr hm
  have hL0 : (0:ℝ) ≤ L := by
    rw [hLdef]
    apply Real.log_nonneg
    have hw1 : 1 ≤ w := le_trans Nat.one_le_two_pow hw
    exact_mod_cast hw1
  have hS0 : (0:ℝ) ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun a _ => by positivity)
  have hφM : (0:ℝ) ≤ φ/(8*M) := div_nonneg hφ0.le (by linarith)
  -- S is large
  have hc1 : L/8 * (φ/(8*M)) ≤ ((j₁ - j₀ + 1 : ℕ):ℝ) * (φ/(8*M)) :=
    mul_le_mul_of_nonneg_right hcount hφM
  have he : ((j₁ - j₀ + 1 : ℕ):ℝ) * (φ/(8*M)) = ((j₁ - j₀ + 1 : ℕ):ℝ) * φ/(8*M) := by
    ring
  have hSlow : L/8 * (φ/(8*M)) ≤ S := by linarith [hS, hc1, he]
  have hSlow0 : (0:ℝ) ≤ L/8 * (φ/(8*M)) :=
    mul_nonneg (div_nonneg hL0 (by norm_num)) hφM
  have hsq := mul_self_le_mul_self hSlow0 hSlow
  have heq : 1/16384 * (φ/M)^2 * L^2
      = (L/8 * (φ/(8*M))) * (L/8 * (φ/(8*M))) / 4 := by
    field_simp
    ring
  calc 1/16384 * (φ/M)^2 * L^2
      = (L/8 * (φ/(8*M))) * (L/8 * (φ/(8*M))) / 4 := heq
    _ ≤ S * S / 4 := by linarith [hsq]
    _ ≤ _ := hpair
    _ ≤ _ := hsum

end Erdos884
