/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Irreducibility of full-center and truncated-center digit frames.
Informal source: Section 5 and Lemma 5.2 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ArithmeticSlots

namespace Erdos1189

open Finset

lemma lcm_eq_of_subset_insert {D T : Finset ℕ} {N : ℕ}
    (hdiv : ∀ d ∈ D, d ∣ N) (hT : T ⊆ insert N D) (hNT : N ∈ T) : T.lcm id = N := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro d hd
    rcases mem_insert.mp (hT hd) with rfl | hdD
    · exact dvd_rfl
    · exact hdiv d hdD
  · exact dvd_lcm hNT

theorem full_center_irreducible {D : Finset ℕ} {N : ℕ}
    (tag : ℕ → ArithmeticSlot) (hcover : IsCoveringSet (insert N D))
    (hdiv : ∀ d ∈ D, d ∣ N) (hcard : D.card = simpsonWeight N)
    (htags : ∀ d ∈ D, ValidTag (tag d) d) (hinj : Set.InjOn tag D) :
    IsIrreducibleCoveringSet (insert N D) := by
  apply irreducible_of_simpson_obstruction hcover
  intro T hT
  by_cases hNT : N ∈ T
  · rw [lcm_eq_of_subset_insert hdiv hT.subset hNT]
    have hlt := card_lt_card hT
    have hle := card_insert_le N D
    omega
  · have hTD : T ⊆ D := by
      intro d hd
      rcases mem_insert.mp (hT.subset hd) with rfl | hdD
      · exact (hNT hd).elim
      · exact hdD
    exact tag_capacity tag
      (fun d hd => lt_trans Nat.zero_lt_one (hcover.1 d (hT.subset hd)))
      (fun d hd => htags d (hTD hd)) (hinj.mono hTD)

/-- The terminal tags are identified by their prime coordinate. -/
def terminalTags (D : Finset ℕ) (tag : ℕ → ArithmeticSlot) (P : ℕ) : Finset ℕ :=
  D.filter fun d => (tag d).1 = P

/-- Lemma 5.2. The final coordinate has exponent one; the terminal tags
together contain the whole lcm. Every proper subset satisfies the Simpson
obstruction, even if all its residues are reassigned. -/
theorem truncated_center_irreducible {D : Finset ℕ} {N P : ℕ}
    (tag : ℕ → ArithmeticSlot) (hcover : IsCoveringSet (insert P D))
    (hN : N ≠ 0) (hP : P ∣ N) (hdiv : ∀ d ∈ D, d ∣ N)
    (hcard : D.card = simpsonWeight N) (hPexp : N.factorization P = 1)
    (htags : ∀ d ∈ D, ValidTag (tag d) d) (hinj : Set.InjOn tag D)
    (hterminal : N ∣ (terminalTags D tag P).lcm id) :
    IsIrreducibleCoveringSet (insert P D) := by
  have hpos : ∀ d ∈ insert P D, 0 < d :=
    fun d hd => lt_trans Nat.zero_lt_one (hcover.1 d hd)
  apply irreducible_of_simpson_obstruction hcover
  intro T hT
  have hTN : T.lcm id ∣ N := by
    apply Finset.lcm_dvd
    intro d hd
    rcases mem_insert.mp (hT.subset hd) with rfl | hdD
    · exact hP
    · exact hdiv d hdD
  have hT0 : T.lcm id ≠ 0 := ne_zero_of_dvd_ne_zero hN hTN
  by_cases hPT : P ∈ T
  · by_cases hfull : terminalTags D tag P ⊆ T
    · have heq : T.lcm id = N := by
        apply Nat.dvd_antisymm hTN
        exact hterminal.trans (Finset.lcm_dvd (fun _ hd => dvd_lcm (hfull hd)))
      rw [heq]
      have hlt := card_lt_card hT
      have hle := card_insert_le P D
      omega
    · obtain ⟨d₀, hd₀, hd₀T⟩ := not_subset.mp hfull
      obtain ⟨hd₀D, hd₀P⟩ := mem_filter.mp hd₀
      have hV : T.erase P ⊆ D := by
        intro d hd
        rcases mem_insert.mp (hT.subset (mem_of_mem_erase hd)) with rfl | hdD
        · exact (ne_of_mem_erase hd rfl).elim
        · exact hdD
      have hsN := (htags d₀ hd₀D).mem_arithmeticSlots hN (hdiv d₀ hd₀D)
      have he : (tag d₀).2.1 = 0 := by
        have he' := (mem_arithmeticSlots.mp hsN).2.1
        rw [hd₀P, hPexp] at he'
        omega
      have hsP : ValidTag (tag d₀) P := by
        refine ⟨(htags d₀ hd₀D).1, (htags d₀ hd₀D).2.1, ?_⟩
        simp [he, hd₀P]
      have hcap := tag_capacity_with_free_slot tag hT0
        (fun d (hd : d ∈ T.erase P) => dvd_lcm (mem_of_mem_erase hd))
        (fun d hd => htags d (hV hd)) (hinj.mono hV)
        (hsP.mem_arithmeticSlots hT0 (dvd_lcm hPT))
        (by
          intro d hd heq
          have hdd : d = d₀ := hinj (hV hd) hd₀D heq
          exact hd₀T (hdd ▸ mem_of_mem_erase hd))
      rwa [card_erase_add_one hPT] at hcap
  · have hTD : T ⊆ D := by
      intro d hd
      rcases mem_insert.mp (hT.subset hd) with rfl | hdD
      · exact (hPT hd).elim
      · exact hdD
    exact tag_capacity tag (fun d hd => hpos d (hT.subset hd))
      (fun d hd => htags d (hTD hd)) (hinj.mono hTD)

end Erdos1189
