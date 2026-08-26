/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An injective one-member extension of every irreducible covering set.
Informal argument: cover the even integers by 2 and pull an arbitrary covering
assignment back along the opposite parity fibre to prove irreducibility.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Core

namespace Erdos1189

open Finset

def doublingExtension (D : Finset ℕ) : Finset ℕ := insert 2 (D.image (2 * ·))

lemma modEq_doubling_pullback {d : ℕ} {t a c : ℤ}
    (h : 2 * t + c ≡ a [ZMOD (2 * d : ℕ)]) : t ≡ (a - c) / 2 [ZMOD d] := by
  obtain ⟨v, hv⟩ := h.dvd
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hv
  apply Int.modEq_iff_dvd.mpr
  refine ⟨v, ?_⟩
  have hv' : a - c = 2 * (t + (d : ℤ) * v) := by nlinarith [hv]
  rw [hv']
  omega

/-- An even distinguished modulus can cover no point of the opposite parity fibre. -/
lemma Covers.parity_pullback {E : Finset ℕ} {a : ℕ → ℤ} {n : ℕ}
    (hn : 2 ∣ n) (h : Covers (insert n (E.image (2 * ·))) a) :
    Covers E (fun d => (a (2 * d) - (a n + 1)) / 2) := by
  intro t
  obtain ⟨m, hm, ht⟩ := h (2 * t + (a n + 1))
  rcases mem_insert.mp hm with hmn | hm
  · subst m
    have h2 := ht.of_dvd (show (2 : ℤ) ∣ n by exact_mod_cast hn)
    change (2 * t + (a n + 1)) % 2 = a n % 2 at h2
    omega
  · obtain ⟨d, hd, rfl⟩ := mem_image.mp hm
    exact ⟨d, hd, modEq_doubling_pullback ht⟩

lemma IsCoveringSet.doublingExtension {D : Finset ℕ} (hD : IsCoveringSet D) :
    IsCoveringSet (doublingExtension D) := by
  obtain ⟨a, ha⟩ := hD.2
  refine ⟨?_, (fun n => if n = 2 then 0 else 2 * a (n / 2) + 1), ?_⟩
  · intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · norm_num
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp hn
      have := hD.1 d hd
      omega
  · intro z
    by_cases hz : z % 2 = 0
    · refine ⟨2, mem_insert_self _ _, ?_⟩
      simpa only [ite_true, Int.ModEq, Nat.cast_ofNat, Int.zero_emod] using hz
    · have hodd : z = 2 * (z / 2) + 1 := by omega
      obtain ⟨d, hd, ht⟩ := ha (z / 2)
      have hd2 : 2 * d ≠ 2 := by have := hD.1 d hd; omega
      have hdiv : 2 * d / 2 = d := by omega
      refine ⟨2 * d, mem_insert_of_mem (mem_image.mpr ⟨d, hd, rfl⟩), ?_⟩
      dsimp only
      rw [if_neg hd2, hdiv, hodd]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (ht.mul_left' (c := 2)).add_right 1

lemma IsIrreducibleCoveringSet.doublingExtension {D : Finset ℕ}
    (hD : IsIrreducibleCoveringSet D) : IsIrreducibleCoveringSet (doublingExtension D) := by
  apply (isIrreducibleCoveringSet_iff_erase _).mpr
  refine ⟨hD.1.doublingExtension, ?_⟩
  intro m hm hcover
  obtain ⟨a, ha⟩ := hcover.2
  rcases mem_insert.mp hm with rfl | hm
  · obtain ⟨d, hd⟩ := hD.1.nonempty
    have hsub : (Erdos1189.doublingExtension D).erase 2 ⊆
        insert (2 * d) ((D.erase d).image (2 * ·)) := by
      intro n hn
      obtain ⟨hne, hn⟩ := mem_erase.mp hn
      rcases mem_insert.mp hn with hn | hn
      · exact False.elim (hne hn)
      · obtain ⟨e, he, rfl⟩ := mem_image.mp hn
        by_cases hed : e = d
        · subst e
          exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_image.mpr ⟨e, mem_erase.mpr ⟨hed, he⟩, rfl⟩)
    have hpull := (ha.mono hsub).parity_pullback (dvd_mul_right 2 d)
    exact hD.2 _ (erase_ssubset hd) ⟨fun e he => hD.1.1 e (mem_of_mem_erase he), _, hpull⟩
  · obtain ⟨d, hd, rfl⟩ := mem_image.mp hm
    have hsub : (Erdos1189.doublingExtension D).erase (2 * d) ⊆
        insert 2 ((D.erase d).image (2 * ·)) := by
      intro n hn
      obtain ⟨hne, hn⟩ := mem_erase.mp hn
      rcases mem_insert.mp hn with rfl | hn
      · exact mem_insert_self _ _
      · obtain ⟨e, he, rfl⟩ := mem_image.mp hn
        have hed : e ≠ d := by intro h; exact hne (congrArg (2 * ·) h)
        exact mem_insert_of_mem (mem_image.mpr ⟨e, mem_erase.mpr ⟨hed, he⟩, rfl⟩)
    have hpull := (ha.mono hsub).parity_pullback (dvd_refl 2)
    exact hD.2 _ (erase_ssubset hd) ⟨fun e he => hD.1.1 e (mem_of_mem_erase he), _, hpull⟩

lemma doublingExtension_card {D : Finset ℕ} (hD : ∀ d ∈ D, 1 < d) :
    (doublingExtension D).card = D.card + 1 := by
  have h2 : 2 ∉ D.image (2 * ·) := by
    intro h
    obtain ⟨d, hd, h⟩ := mem_image.mp h
    have := hD d hd
    omega
  rw [doublingExtension, card_insert_of_notMem h2, card_image_of_injective]
  intro a b h
  dsimp only at h
  omega

lemma doublingExtension_inj {D E : Finset ℕ} (hD : ∀ d ∈ D, 1 < d)
    (hE : ∀ e ∈ E, 1 < e) (h : doublingExtension D = doublingExtension E) : D = E := by
  have hsub : ∀ {A B : Finset ℕ}, (∀ d ∈ A, 1 < d) →
      doublingExtension A = doublingExtension B → A ⊆ B := by
    intro A B hA hAB d hd
    have hmem : 2 * d ∈ doublingExtension B := by
      rw [← hAB]
      exact mem_insert_of_mem (mem_image.mpr ⟨d, hd, rfl⟩)
    rcases mem_insert.mp hmem with h2 | hmem
    · have := hA d hd
      omega
    · obtain ⟨e, he, heq⟩ := mem_image.mp hmem
      have : e = d := by omega
      simpa only [this] using he
  exact subset_antisymm (hsub hD h) (hsub hE h.symm)

end Erdos1189
