import Mathlib
import ErdosProblems.Erdos336.KneserConsequences

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A finite set whose saturation by a nonempty stabilizer has one-fibre
cardinality is contained in a single stabilizer coset. -/
lemma subset_vadd_of_card_add_eq_card {A H : Finset G}
    (hA : A.Nonempty) (hzero : 0 ∈ H)
    (hcard : (A + H).card = H.card) :
    ∃ a : G, A ⊆ a +ᵥ H := by
  obtain ⟨a, ha⟩ := hA
  have haHsub : a +ᵥ H ⊆ A + H := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
    exact Finset.mem_add.mpr ⟨a, ha, y, hy, hyx⟩
  have hcarda : (a +ᵥ H).card = (A + H).card := by
    rw [Finset.card_vadd_finset, hcard]
  have heq : a +ᵥ H = A + H :=
    Finset.Subset.antisymm haHsub
      (Finset.eq_of_subset_of_card_le haHsub (by omega)).symm.subset
  refine ⟨a, ?_⟩
  intro x hx
  rw [heq]
  exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩

/-- The density/coset conclusion used in Lev's Corollary 5.3. -/
theorem dense_stabilizer_coset_of_asymmetric_small_sum
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : 2 * (A + B).card < 2 * A.card + B.card)
    (hcard : A.card ≤ B.card) :
    let H := (A + B).addStab
    (∃ b : G, B ⊆ b +ᵥ H) ∧ 2 * H.card < 3 * B.card := by
  let H := (A + B).addStab
  have holson := olson_half_growth hA hB
  rcases holson with hgrowth | hcoset
  · omega
  · refine ⟨hcoset, ?_⟩
    have hstab : H.card ≤ (A + B).card := by
      simpa [H] using (Finset.card_addStab_le_card (s := A + B))
    change 2 * H.card < 3 * B.card
    omega

/-- Lev's very-small-sum Lemma 5.4, in integral form.  If the sumset is
smaller than both `2|B|` and `3|A|/2`, then both summands and their sum
occupy one coset of the sumset stabilizer, with the stated fibre densities. -/
theorem very_small_sum_is_one_stabilizer_coset
    {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (hBsmall : (A + B).card < 2 * B.card)
    (hAsmall : 2 * (A + B).card < 3 * A.card) :
    let H := (A + B).addStab
    (∃ a : G, A ⊆ a +ᵥ H) ∧
    (∃ b : G, B ⊆ b +ᵥ H) ∧
    (∃ s : G, A + B = s +ᵥ H) ∧
    2 * H.card < 3 * A.card ∧ H.card < 2 * B.card := by
  let H := (A + B).addStab
  have hAB : (A + B).Nonempty := hA.add hB
  have hH : H.Nonempty := hAB.addStab
  have hzero : 0 ∈ H := Finset.zero_mem_addStab.mpr hAB
  have hsmall : (A + B).card ≤ A.card + B.card - 1 := by
    have hApos := hA.card_pos
    have hBpos := hB.card_pos
    omega
  have heq := add_kneser_eq_of_card_le hA hB hsmall
  let XA := (A + H).card
  let XB := (B + H).card
  let c := (A + B).card
  let e := H.card
  have heq' : XA + XB = c + e := by simpa [XA, XB, c, e, H] using heq
  have hdvdA : e ∣ XA := by
    simpa [e, XA, H] using
      Finset.card_addStab_dvd_card_add_addStab A (A + B)
  have hdvdB : e ∣ XB := by
    simpa [e, XB, H] using
      Finset.card_addStab_dvd_card_add_addStab B (A + B)
  obtain ⟨α, hα⟩ := hdvdA
  obtain ⟨β, hβ⟩ := hdvdB
  have hepos : 0 < e := by simpa [e] using hH.card_pos
  have hAsub : A ⊆ A + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hBsub : B ⊆ B + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hAcard : A.card ≤ XA := by
    simpa [XA] using Finset.card_le_card hAsub
  have hBcard : B.card ≤ XB := by
    simpa [XB] using Finset.card_le_card hBsub
  have hαpos : 0 < α := by
    rw [hα] at hAcard
    have := hA.card_pos
    nlinarith
  have hβpos : 0 < β := by
    rw [hβ] at hBcard
    have := hB.card_pos
    nlinarith
  have hαβ : α ≤ β := by
    by_contra hn
    have hstep : β + 1 ≤ α := by omega
    have hmul := Nat.mul_le_mul_left e hstep
    have hXstep : XB + e ≤ XA := by
      calc
        XB + e = e * (β + 1) := by rw [hβ]; ring
        _ ≤ e * α := hmul
        _ = XA := hα.symm
    have hBsmall' : c < 2 * B.card := by simpa [c] using hBsmall
    omega
  have h2βα : 2 * β ≤ α + 1 := by
    by_contra hn
    have hstep : α + 2 ≤ 2 * β := by omega
    have hmul := Nat.mul_le_mul_left e hstep
    have hXstep : XA + 2 * e ≤ 2 * XB := by
      calc
        XA + 2 * e = e * (α + 2) := by rw [hα]; ring
        _ ≤ e * (2 * β) := hmul
        _ = 2 * XB := by rw [hβ]; ring
    have hAsmall' : 2 * c < 3 * A.card := by simpa [c] using hAsmall
    omega
  have hαone : α = 1 := by omega
  have hβone : β = 1 := by omega
  have hXA : XA = e := by rw [hα, hαone]; simp
  have hXB : XB = e := by rw [hβ, hβone]; simp
  have hc : c = e := by omega
  have hAc : (A + H).card = H.card := by simpa [XA, e] using hXA
  have hBc : (B + H).card = H.card := by simpa [XB, e] using hXB
  obtain ⟨a, ha⟩ := subset_vadd_of_card_add_eq_card hA hzero hAc
  obtain ⟨b, hb⟩ := subset_vadd_of_card_add_eq_card hB hzero hBc
  obtain ⟨s, hs⟩ := hAB
  have hsHsub : s +ᵥ H ⊆ A + B := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
    have hstable : (A + B) + H = A + B := by
      simpa [H] using Finset.add_addStab (A + B)
    rw [← hstable]
    exact Finset.mem_add.mpr ⟨s, hs, y, hy, hyx⟩
  have hcardsH : (s +ᵥ H).card = (A + B).card := by
    rw [Finset.card_vadd_finset]
    simpa [c, e] using hc.symm
  have hsumcoset : A + B = s +ᵥ H := by
    exact (Finset.Subset.antisymm hsHsub
      (Finset.eq_of_subset_of_card_le hsHsub (by omega)).symm.subset).symm
  have hc' : (A + B).card = H.card := by simpa [c, e] using hc
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨s, hsumcoset⟩, ?_, ?_⟩
  · change 2 * H.card < 3 * A.card
    omega
  · change H.card < 2 * B.card
    omega

end Erdos336
