import ErdosProblems.Erdos336.KneserTheorem

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Exact Kneser equality in the small-sumset regime. -/
theorem add_kneser_eq_of_card_le {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hsmall : (A + B).card ≤ A.card + B.card - 1) :
    (A + (A + B).addStab).card + (B + (A + B).addStab).card =
      (A + B).card + (A + B).addStab.card := by
  let H : Finset G := (A + B).addStab
  have hAB : (A + B).Nonempty := hA.add hB
  have hH : H.Nonempty := hAB.addStab
  have hzero : 0 ∈ H := Finset.zero_mem_addStab.mpr hAB
  have hAsub : A ⊆ A + H := by
    intro a ha
    exact Finset.mem_add.mpr ⟨a, ha, 0, hzero, by simp⟩
  have hBsub : B ⊆ B + H := by
    intro b hb
    exact Finset.mem_add.mpr ⟨b, hb, 0, hzero, by simp⟩
  let X := (A + H).card + (B + H).card
  let c := (A + B).card
  let h := H.card
  have hk : X ≤ c + h := by
    simpa [X, c, h, H] using Finset.add_kneser A B
  have hcsmall : c + 1 ≤ A.card + B.card := by
    have hApos := hA.card_pos
    have hBpos := hB.card_pos
    dsimp [c]
    omega
  have hcX : c < X := by
    have hAc : A.card ≤ (A + H).card := Finset.card_le_card hAsub
    have hBc : B.card ≤ (B + H).card := Finset.card_le_card hBsub
    dsimp [X]
    omega
  have hdvdA : h ∣ (A + H).card := by
    simpa [h, H] using Finset.card_addStab_dvd_card_add_addStab A (A + B)
  have hdvdB : h ∣ (B + H).card := by
    simpa [h, H] using Finset.card_addStab_dvd_card_add_addStab B (A + B)
  have hdvdX : h ∣ X := by
    dsimp [X]
    exact Nat.dvd_add hdvdA hdvdB
  have hdvdc : h ∣ c := by
    simpa [h, c, H] using Finset.card_addStab_dvd_card (A + B)
  have hdvdd : h ∣ X - c := Nat.dvd_sub hdvdX hdvdc
  have hdpos : 0 < X - c := Nat.sub_pos_of_lt hcX
  have hle : h ≤ X - c := Nat.le_of_dvd hdpos hdvdd
  have hge : X - c ≤ h := by omega
  have heq : X - c = h := Nat.le_antisymm hge hle
  have hXeq : X = c + h := by omega
  simpa [X, c, h, H] using hXeq

/-- Olson's asymmetric half-growth lemma, in denominator-free cardinal form:
unless `B` is contained in one coset of the stabilizer of `A+B`,
`2|A+B| ≥ 2|A|+|B|`. -/
theorem olson_half_growth {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    2 * A.card + B.card ≤ 2 * (A + B).card ∨
      ∃ b : G, B ⊆ b +ᵥ (A + B).addStab := by
  let H : Finset G := (A + B).addStab
  by_cases hcoset : ∃ b : G, B ⊆ b +ᵥ H
  · exact Or.inr hcoset
  · apply Or.inl
    have hAB : (A + B).Nonempty := hA.add hB
    have hH : H.Nonempty := hAB.addStab
    have hzero : 0 ∈ H := Finset.zero_mem_addStab.mpr hAB
    obtain ⟨b, hb⟩ := hB
    have hbHsub : b +ᵥ H ⊆ B + H := by
      intro x hx
      obtain ⟨y, hyH, hyx⟩ := Finset.mem_vadd_finset.mp hx
      exact Finset.mem_add.mpr ⟨b, hb, y, hyH, hyx⟩
    have hcard_bH : (b +ᵥ H).card = H.card := Finset.card_vadd_finset _ _
    have hssub : b +ᵥ H ⊂ B + H := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hbHsub, ?_⟩
      intro heq
      apply hcoset
      refine ⟨b, ?_⟩
      intro x hx
      rw [heq]
      exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
    have hstrict : H.card < (B + H).card := by
      rw [← hcard_bH]
      exact Finset.card_lt_card hssub
    have hdvd : H.card ∣ (B + H).card := by
      simpa [H] using Finset.card_addStab_dvd_card_add_addStab B (A + B)
    obtain ⟨k, hk⟩ := hdvd
    have hHpos : 0 < H.card := hH.card_pos
    have hk2 : 2 ≤ k := by
      rw [hk] at hstrict
      nlinarith
    have h2H : 2 * H.card ≤ (B + H).card := by
      rw [hk]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left H.card hk2
    have hBsub : B ⊆ B + H := by
      intro x hx
      exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
    have hBcard : B.card ≤ (B + H).card := Finset.card_le_card hBsub
    have hKneser := Finset.add_kneser A B
    have hAsub : A ⊆ A + H := by
      intro x hx
      exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
    have hAcard : A.card ≤ (A + H).card := Finset.card_le_card hAsub
    dsimp [H] at h2H hBcard hKneser hAcard ⊢
    omega

end Erdos336
