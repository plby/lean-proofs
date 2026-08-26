/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Ordered arithmetic frames with distinct moduli.
Informal source: Section 5 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameCoverage
import ErdosProblems.Erdos1189.FrameCriterion

namespace Erdos1189

open Finset

def primeSlotToArithmetic {N : ℕ} (s : PrimeSlot N) : ArithmeticSlot :=
  ⟨s.1.1.val, (s.1.2.val, s.2.val)⟩

lemma primeSlotToArithmetic_injective (N : ℕ) :
    Function.Injective (@primeSlotToArithmetic N) := by
  rintro ⟨⟨⟨p, hp⟩, ⟨e, he⟩⟩, ⟨a, ha⟩⟩ ⟨⟨⟨q, hq⟩, ⟨f, hf⟩⟩, ⟨b, hb⟩⟩ h
  have hpq : p = q := congrArg Sigma.fst h
  subst q
  have hef : (e, a) = (f, b) := congrArg (fun s : ArithmeticSlot => s.2) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hef
  rfl

lemma card_primeSlot (N : ℕ) : Fintype.card (PrimeSlot N) = simpsonWeight N := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_coordinateSize N

lemma card_frameModuli {N : ℕ} {m : PrimeSlot N → ℕ} (hinj : Function.Injective m) :
    (frameModuli m).card = simpsonWeight N := by
  rw [frameModuli, card_image_of_injective _ hinj, card_univ, card_primeSlot]

noncomputable def frameAllocation {N : ℕ} (m : PrimeSlot N → ℕ) : ℕ → ArithmeticSlot :=
  Function.extend m primeSlotToArithmetic (fun _ => ⟨0, (0, 0)⟩)

lemma frameAllocation_apply {N : ℕ} {m : PrimeSlot N → ℕ} (hinj : Function.Injective m)
    (s : PrimeSlot N) : frameAllocation m (m s) = primeSlotToArithmetic s :=
  hinj.extend_apply _ _ _

lemma frameAllocation_injective {N : ℕ} {m : PrimeSlot N → ℕ} (hinj : Function.Injective m) :
    Set.InjOn (frameAllocation m) (frameModuli m) := by
  intro d hd d' hd' heq
  obtain ⟨s, rfl⟩ := mem_frameModuli.mp hd
  obtain ⟨s', rfl⟩ := mem_frameModuli.mp hd'
  rw [frameAllocation_apply hinj, frameAllocation_apply hinj] at heq
  exact congrArg m (primeSlotToArithmetic_injective N heq)

lemma validTag_primeSlot {N : ℕ} (s : PrimeSlot N) {d : ℕ}
    (hd : s.1.1.val ^ (s.1.2.val + 1) ∣ d) : ValidTag (primeSlotToArithmetic s) d :=
  ⟨Nat.prime_of_mem_primeFactors s.1.1.2, s.2.isLt, hd⟩

lemma frame_modulus_nontrivial {N : ℕ} (hN : N ≠ 0) (m : PrimeSlot N → ℕ)
    (hdiv : ∀ s, m s ∣ N) (hown : ∀ s, s.1.1.val ^ (s.1.2.val + 1) ∣ m s) :
    ∀ s, 1 < m s := by
  intro s
  have hp := Nat.prime_of_mem_primeFactors s.1.1.2
  have hpow : 1 < s.1.1.val ^ (s.1.2.val + 1) :=
    one_lt_pow₀ hp.one_lt (by omega)
  exact hpow.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero hN (hdiv s))) (hown s))

/-- A full-center arithmetic frame is irreducible, with exactly `F(N)+1` moduli. -/
theorem full_digit_frame {N : ℕ} (hN : 1 < N)
    (m : PrimeSlot N → ℕ) (rank : PrimeCoordinate N → ℕ)
    (hdiv : ∀ s, m s ∣ N) (hinj : Function.Injective m)
    (hown : ∀ s, s.1.1.val ^ (s.1.2.val + 1) ∣ m s)
    (hcenter : N ∉ frameModuli m)
    (horder : ∀ s i, (i.2 : ℕ) < (m s).factorization i.1 →
      i = s.1 ∨ rank i < rank s.1) :
    IsIrreducibleCoveringSet (insert N (frameModuli m)) ∧
      (insert N (frameModuli m)).card = simpsonWeight N + 1 := by
  have hN0 : N ≠ 0 := by omega
  have hcover := digit_frame_covers hN0 hN dvd_rfl m rank
    (frame_modulus_nontrivial hN0 m hdiv hown) hdiv hinj hcenter horder
  refine ⟨?_, by rw [card_insert_of_notMem hcenter, card_frameModuli hinj]⟩
  apply full_center_irreducible (frameAllocation m) hcover
  · intro d hd
    obtain ⟨s, rfl⟩ := mem_frameModuli.mp hd
    exact hdiv s
  · exact card_frameModuli hinj
  · intro d hd
    obtain ⟨s, rfl⟩ := mem_frameModuli.mp hd
    rw [frameAllocation_apply hinj]
    exact validTag_primeSlot s (hown s)
  · exact frameAllocation_injective hinj

/-- The truncated-center form, with explicit coverage and the terminal lcm condition. -/
theorem truncated_digit_frame {N P : ℕ} (hN : N ≠ 0) (hP : 1 < P) (hPN : P ∣ N)
    (m : PrimeSlot N → ℕ) (rank : PrimeCoordinate N → ℕ)
    (hdiv : ∀ s, m s ∣ N) (hinj : Function.Injective m)
    (hown : ∀ s, s.1.1.val ^ (s.1.2.val + 1) ∣ m s)
    (hcenter : P ∉ frameModuli m) (hPexp : N.factorization P = 1)
    (horder : ∀ s i, (i.2 : ℕ) < (m s).factorization i.1 →
      i = s.1 ∨ rank i < rank s.1)
    (hterminal : N ∣ (terminalTags (frameModuli m) (frameAllocation m) P).lcm id) :
    IsIrreducibleCoveringSet (insert P (frameModuli m)) ∧
      (insert P (frameModuli m)).card = simpsonWeight N + 1 := by
  have hcover := digit_frame_covers hN hP hPN m rank
    (frame_modulus_nontrivial hN m hdiv hown) hdiv hinj hcenter horder
  refine ⟨?_, by rw [card_insert_of_notMem hcenter, card_frameModuli hinj]⟩
  apply truncated_center_irreducible (frameAllocation m) hcover hN hPN
  · intro d hd
    obtain ⟨s, rfl⟩ := mem_frameModuli.mp hd
    exact hdiv s
  · exact card_frameModuli hinj
  · exact hPexp
  · intro d hd
    obtain ⟨s, rfl⟩ := mem_frameModuli.mp hd
    rw [frameAllocation_apply hinj]
    exact validTag_primeSlot s (hown s)
  · exact frameAllocation_injective hinj
  · exact hterminal

end Erdos1189
