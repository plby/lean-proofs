/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Selecting distinct seed lists while retaining prescribed seeds.
Informal source: Sections 6.3, 6.4, and 7 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameInteger
import Mathlib.Data.Finset.Sort

namespace Erdos1189

open Finset

lemma exists_injective_list_between {A B : Finset ℕ} {k : ℕ} (hAB : A ⊆ B)
    (hAk : A.card ≤ k) (hkB : k ≤ B.card) :
    ∃ f : Fin k → ℕ, Function.Injective f ∧ (∀ i, f i ∈ B) ∧
      ∀ d ∈ A, ∃ i, f i = d := by
  obtain ⟨S, hAS, hSB, hcard⟩ := exists_subsuperset_card_eq hAB hAk hkB
  refine ⟨S.orderEmbOfFin hcard, (S.orderEmbOfFin hcard).injective,
    (fun i => hSB (orderEmbOfFin_mem S hcard i)), ?_⟩
  intro d hd
  refine ⟨(S.orderIsoOfFin hcard).symm ⟨d, hAS hd⟩, ?_⟩
  exact congrArg Subtype.val ((S.orderIsoOfFin hcard).apply_symm_apply ⟨d, hAS hd⟩)

lemma squarefree_below_subset_smallSeeds {q C : ℕ} (hC : 0 < C) :
    squarefreeUpto (q - 1) ⊆ smallSquarefreeSeeds q (C * q) := by
  intro d hd
  obtain ⟨hdI, hdSF⟩ := mem_filter.mp hd
  obtain ⟨hd0, hdq⟩ := mem_Ioc.mp hdI
  have hq0 : 0 < q := by omega
  have hdN : d ≤ C * q := hdq.trans ((Nat.sub_le q 1).trans (Nat.le_mul_of_pos_left q hC))
  refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hd0, hdN⟩, hdSF⟩, ?_⟩
  intro p hp
  have hpd := Nat.le_of_dvd hd0 (Nat.dvd_of_mem_primeFactors hp)
  omega

lemma exists_small_seed_list {q C : ℕ} (hC : 0 < C)
    (hcount : q - 1 ≤ (smallSquarefreeSeeds q (C * q)).card) :
    ∃ f : Fin (q - 1) → ℕ, Function.Injective f ∧
      (∀ i, f i ∈ smallSquarefreeSeeds q (C * q)) ∧
      ∀ d ∈ squarefreeUpto (q - 1), ∃ i, f i = d := by
  apply exists_injective_list_between (squarefree_below_subset_smallSeeds hC) _ hcount
  have hcard := card_le_card (filter_subset (s := Ioc 0 (q - 1)) (p := Squarefree))
  simpa [squarefreeUpto] using hcard

def prescribedTerminalSeeds (P : ℕ) (D : Finset ℕ) : Finset ℕ :=
  ((Nat.primesLE P).erase P).image (fun q => q ^ (frameInteger P D).factorization q)

lemma prescribedTerminalSeeds_card_le (P : ℕ) (D : Finset ℕ) :
    (prescribedTerminalSeeds P D).card ≤ P - 1 := by
  have hsub : Nat.primesLE P ⊆ Icc 2 P := by
    intro q hq
    exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hq).two_le, Nat.le_of_mem_primesLE hq⟩
  calc
    _ ≤ ((Nat.primesLE P).erase P).card := card_image_le
    _ ≤ (Nat.primesLE P).card := card_le_card (erase_subset _ _)
    _ ≤ (Icc 2 P).card := card_le_card hsub
    _ = P - 1 := by simp

lemma prescribedTerminalSeeds_properties {P B : ℕ} {D : Finset ℕ}
    (hB : B < P) (hD : D ⊆ Nat.primesLE B) {d : ℕ} (hd : d ∈ prescribedTerminalSeeds P D) :
    1 < d ∧ d ≤ max (16 * P) (B ^ 2) ∧ d ∣ frameInteger P D ∧
      ∀ p ∈ d.primeFactors, p < P := by
  have hDP : D ⊆ Nat.primesLE P := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE (hD hq)).trans hB.le, Nat.prime_of_mem_primesLE (hD hq)⟩
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hd
  obtain ⟨hqP, hq⟩ := mem_erase.mp hq
  have hqPr := Nat.prime_of_mem_primesLE hq
  have hqle := Nat.le_of_mem_primesLE hq
  have he : 0 < (frameInteger P D).factorization q := by
    rw [frameInteger_factorization hDP, if_pos hq]
    omega
  refine ⟨one_lt_pow₀ hqPr.one_lt he.ne', ?_, ?_, ?_⟩
  · exact (frameInteger_prime_power_bound hB.le hD hq).trans
      (max_le_max (by omega) le_rfl)
  · exact (hqPr.pow_dvd_iff_le_factorization (frameInteger_ne_zero hDP)).mpr le_rfl
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpq := Nat.prime_eq_prime_of_dvd_pow hpp hqPr (Nat.dvd_of_mem_primeFactors hp)
    omega

lemma terminal_stock_properties {P B : ℕ} {D : Finset ℕ}
    (hB : B ≤ P) (hD : D ⊆ Nat.primesLE B) {d : ℕ}
    (hd : d ∈ (smallSquarefreeSeeds P (16 * P)).erase 1) :
    1 < d ∧ d ≤ max (16 * P) (B ^ 2) ∧ d ∣ frameInteger P D ∧
      ∀ p ∈ d.primeFactors, p < P := by
  obtain ⟨hd1, hd⟩ := mem_erase.mp hd
  obtain ⟨hdSF, hsmall⟩ := mem_filter.mp hd
  obtain ⟨hdI, hdSF⟩ := mem_filter.mp hdSF
  obtain ⟨hd0, hdN⟩ := mem_Ioc.mp hdI
  have hDP : D ⊆ Nat.primesLE P := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE (hD hq)).trans hB, Nat.prime_of_mem_primesLE (hD hq)⟩
  exact ⟨by omega, hdN.trans (le_max_left _ _),
    squarefree_seed_dvd_frameInteger hDP hdSF (fun p hp => (hsmall p hp).le), hsmall⟩

theorem exists_terminal_seed_list {P B : ℕ} {D : Finset ℕ} (hP : P.Prime)
    (hB : B < P) (hD : D ⊆ Nat.primesLE B)
    (hstock : 3 * P ≤ (smallSquarefreeSeeds P (16 * P)).card) :
    ∃ f : Fin (P - 1) → ℕ, Function.Injective f ∧
      (∀ i, 1 < f i ∧ f i ≤ max (16 * P) (B ^ 2) ∧ f i ∣ frameInteger P D ∧
        ∀ p ∈ (f i).primeFactors, p < P) ∧
      ∀ p ∈ Nat.primesLE P, p ≠ P → ∃ i, f i = p ^ (frameInteger P D).factorization p := by
  let A := prescribedTerminalSeeds P D
  let S := (smallSquarefreeSeeds P (16 * P)).erase 1
  have hone : 1 ∈ smallSquarefreeSeeds P (16 * P) := by
    have hp := hP.two_le
    simp [smallSquarefreeSeeds, squarefreeUpto]
    omega
  have hS : P - 1 ≤ S.card := by
    have he := card_erase_add_one hone
    dsimp [S]
    omega
  have hsize : P - 1 ≤ (A ∪ S).card := hS.trans (card_le_card subset_union_right)
  obtain ⟨f, hf, hfin, hpres⟩ := exists_injective_list_between
    (subset_union_left : A ⊆ A ∪ S) (prescribedTerminalSeeds_card_le P D) hsize
  refine ⟨f, hf, ?_, ?_⟩
  · intro i
    rcases mem_union.mp (hfin i) with hi | hi
    · exact prescribedTerminalSeeds_properties hB hD hi
    · exact terminal_stock_properties hB.le hD hi
  · intro p hp hpP
    exact hpres _ (mem_image.mpr ⟨p, mem_erase.mpr ⟨hpP, hp⟩, rfl⟩)

end Erdos1189
