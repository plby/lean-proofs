/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Unordered choices of distinct arithmetic-frame moduli.
Informal source: Section 8.3 of Pickhardt and Omniscience Research Agent,
and arithmetic frames in Balister--Bollobás--Morris--Sahasrabudhe--Tiba.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.DigitFrame
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

namespace Erdos1189

open Finset

/-- A tag modulus fixes its own digit, fixes only preceding other digits,
divides the common period, and differs from the center. -/
def admissibleFrameModuli {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (c : PrimeCoordinate N) : Finset ℕ :=
  N.divisors.filter fun d => d ≠ N ∧ c.1.val ^ (c.2.val + 1) ∣ d ∧
    ∀ i : PrimeCoordinate N, i.2.val < d.factorization i.1 →
      i = c ∨ rank i < rank c

lemma mem_admissibleFrameModuli {N d : ℕ} {rank : PrimeCoordinate N → ℕ}
    {c : PrimeCoordinate N} : d ∈ admissibleFrameModuli rank c ↔
      d ∣ N ∧ N ≠ 0 ∧ d ≠ N ∧ c.1.val ^ (c.2.val + 1) ∣ d ∧
        ∀ i : PrimeCoordinate N, i.2.val < d.factorization i.1 →
          i = c ∨ rank i < rank c := by
  simp only [admissibleFrameModuli, mem_filter, Nat.mem_divisors]
  tauto

lemma admissibleFrameModuli_disjoint {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    {c e : PrimeCoordinate N} (hce : c ≠ e) :
    Disjoint (admissibleFrameModuli rank c) (admissibleFrameModuli rank e) := by
  apply disjoint_left.mpr
  intro d hdc hde
  obtain ⟨hdN, hN, _, hcd, hco⟩ := mem_admissibleFrameModuli.mp hdc
  obtain ⟨_, _, _, hed, heo⟩ := mem_admissibleFrameModuli.mp hde
  have hd0 := ne_zero_of_dvd_ne_zero hN hdN
  have hcfix : c.2.val < d.factorization c.1 := by
    have h := (Nat.prime_of_mem_primeFactors c.1.2).pow_dvd_iff_le_factorization hd0 |>.mp hcd
    omega
  have hefix : e.2.val < d.factorization e.1 := by
    have h := (Nat.prime_of_mem_primeFactors e.1.2).pow_dvd_iff_le_factorization hd0 |>.mp hed
    omega
  have h1 := (hco e hefix).resolve_left hce.symm
  have h2 := (heo c hcfix).resolve_left hce
  omega

abbrev FrameChoice {N : ℕ} (rank : PrimeCoordinate N → ℕ) :=
  (c : PrimeCoordinate N) →
    (admissibleFrameModuli rank c).powersetCard (coordinateSize c - 1)

lemma FrameChoice.subset {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) (c : PrimeCoordinate N) :
    (F c).val ⊆ admissibleFrameModuli rank c :=
  (mem_powersetCard.mp (F c).property).1

lemma FrameChoice.card {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) (c : PrimeCoordinate N) :
    (F c).val.card = coordinateSize c - 1 :=
  (mem_powersetCard.mp (F c).property).2

noncomputable def FrameChoice.modulus {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) (s : PrimeSlot N) : ℕ :=
  (F s.1).val.orderEmbOfFin (F.card s.1) s.2

lemma FrameChoice.modulus_mem {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) (s : PrimeSlot N) : F.modulus s ∈ (F s.1).val :=
  orderEmbOfFin_mem _ _ _

lemma FrameChoice.modulus_admissible {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) (s : PrimeSlot N) :
    F.modulus s ∈ admissibleFrameModuli rank s.1 :=
  F.subset s.1 (F.modulus_mem s)

lemma FrameChoice.modulus_injective {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) : Function.Injective F.modulus := by
  intro s t h
  have hst : s.1 = t.1 := by
    by_contra hne
    exact disjoint_left.mp (admissibleFrameModuli_disjoint rank hne)
      (F.modulus_admissible s) (h ▸ F.modulus_admissible t)
  cases s with
  | mk c a =>
      cases t with
      | mk e b =>
          dsimp at hst
          subst e
          have hab := ((F c).val.orderEmbOfFin (F.card c)).injective h
          change a = b at hab
          subst b
          rfl

def FrameChoice.moduli {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) : Finset ℕ :=
  insert N (univ.biUnion fun c => (F c).val)

lemma FrameChoice.frameModuli_eq {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) :
    frameModuli F.modulus = univ.biUnion fun c => (F c).val := by
  ext d
  simp only [mem_frameModuli, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.1, F.modulus_mem s⟩
  · rintro ⟨c, hd⟩
    have him := image_orderEmbOfFin_univ (F c).val (F.card c)
    rw [← him] at hd
    obtain ⟨a, _, ha⟩ := mem_image.mp hd
    exact ⟨⟨c, a⟩, ha⟩

theorem FrameChoice.irreducible {N : ℕ} (hN : 1 < N)
    {rank : PrimeCoordinate N → ℕ} (F : FrameChoice rank) :
    IsIrreducibleCoveringSet F.moduli ∧ F.moduli.card = simpsonWeight N + 1 := by
  have hm := fun s => mem_admissibleFrameModuli.mp (F.modulus_admissible s)
  have hc : N ∉ frameModuli F.modulus := by
    rintro h
    obtain ⟨s, hs⟩ := mem_frameModuli.mp h
    exact (hm s).2.2.1 hs
  have h := full_digit_frame hN F.modulus rank (fun s => (hm s).1)
    F.modulus_injective (fun s => (hm s).2.2.2.1) hc (fun s => (hm s).2.2.2.2)
  simpa only [FrameChoice.moduli, F.frameModuli_eq] using h

lemma FrameChoice.recover {N : ℕ} {rank : PrimeCoordinate N → ℕ}
    (F : FrameChoice rank) (c : PrimeCoordinate N) :
    F.moduli.filter (fun d => d ∈ admissibleFrameModuli rank c) = (F c).val := by
  ext d
  simp only [mem_filter, FrameChoice.moduli, mem_insert, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨hd | ⟨e, he⟩, hdc⟩
    · exact ((mem_admissibleFrameModuli.mp hdc).2.2.1 hd).elim
    · by_cases hec : e = c
      · subst e
        exact he
      · exact (disjoint_left.mp (admissibleFrameModuli_disjoint rank hec)
          (F.subset e he) hdc).elim
  · intro hd
    exact ⟨Or.inr ⟨c, hd⟩, F.subset c hd⟩

theorem FrameChoice.moduli_injective {N : ℕ} (rank : PrimeCoordinate N → ℕ) :
    Function.Injective (@FrameChoice.moduli N rank) := by
  intro F G h
  funext c
  apply Subtype.ext
  rw [← F.recover c, ← G.recover c, h]

lemma card_frameChoice {N : ℕ} (rank : PrimeCoordinate N → ℕ) :
    Fintype.card (FrameChoice rank) =
      ∏ c : PrimeCoordinate N,
        (admissibleFrameModuli rank c).card.choose (coordinateSize c - 1) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_coe, card_powersetCard]

end Erdos1189
