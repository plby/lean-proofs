import ErdosProblems.Erdos336.MinimalV3PartialRectification
import ErdosProblems.Erdos336.QuotientFiberProduct
import ErdosProblems.Erdos336.TwoMinusOneContainment
import ErdosProblems.Erdos336.FailedGrowthQuotient
import ErdosProblems.Erdos336.HighPowerSmallSupport

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- In a putative sparse V3 counterexample, every subset occupying more than
four fifths of a high power already has `2B-B` containing the whole power.
The proof uses Kneser in the stabilizer quotient; if containment failed, that
quotient would have at most fourteen points and force the forbidden density
alternative. -/
theorem highPower_subset_two_sub_of_not_stableV3
    (C : Set (ZMod N)) (t : ℕ) (ht : 14 ≤ t)
    (hzero : 0 ∈ C)
    (hprimitive : ∃ u : ℕ, ExactPower C u = Set.univ)
    (hnot : ¬ StableHighPowerCertificateV3 C t)
    (hcard : 2 ≤ (ExactPower C t).ncard)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hself : 2 * (ExactPower C t).ncard ≤
      (ExactPower C (2 * t)).ncard + 1)
    (B : Finset (ZMod N))
    (hBA : B ⊆ exactPowerFinset C t)
    (hdenseB : 4 * (ExactPower C t).ncard < 5 * B.card) :
    exactPowerFinset C t ⊆ (B + B) - B := by
  let A : Finset (ZMod N) := exactPowerFinset C t
  have hcardA : A.card = (ExactPower C t).ncard := card_exactPowerFinset C t
  have hsumA : A + A = exactPowerFinset C (2 * t) :=
    exactPowerFinset_add_self C t
  have hcardAA : (A + A).card = (ExactPower C (2 * t)).ncard := by
    rw [hsumA, card_exactPowerFinset]
  have hA2 : 2 ≤ A.card := by simpa [hcardA] using hcard
  have hB : B.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hB0
    rw [hB0] at hdenseB
    simp at hdenseB
  intro x hxA
  by_contra hxnot
  have hdisjointCard : B.card + (B + B).card ≤ (A + A).card :=
    card_add_card_double_le_of_not_mem_two_sub hBA hxA hxnot
  let H : Finset (ZMod N) := (B + B).addStab
  let K : AddSubgroup (ZMod N) :=
    AddAction.stabilizer (ZMod N) (↑(B + B) : Set (ZMod N))
  have hBB : (B + B).Nonempty := hB.add hB
  have hKH : addSubgroupFinset K = H := by
    ext y
    simp only [mem_addSubgroupFinset, H]
    change (y ∈ (K : Set (ZMod N))) ↔ y ∈ ((B + B).addStab : Set (ZMod N))
    rw [Finset.coe_addStab hBB]
  let m : ℕ := Nat.card (ZMod N ⧸ K)
  have hm : 0 < m := Nat.card_pos
  letI : NeZero m := ⟨hm.ne'⟩
  let f : ZMod N →+ ZMod m := cyclicQuotientHom K
  have hf : Function.Surjective f := cyclicQuotientHom_surjective K
  let r : ℕ := (B.image f).card
  let q : ℕ := (A.image f).card
  let h : ℕ := H.card
  let e : ℕ := (B + B).card
  let d : ℕ := (A + A).card
  have hhpos : 0 < h := by
    have hHne : H.Nonempty := by
      rw [← hKH]
      exact ⟨0, by simp [addSubgroupFinset]⟩
    simpa [h] using hHne.card_pos
  have hrpos : 0 < r := by
    have := hB.image f
    simpa [r] using this.card_pos
  have hBsat : (B + H).card = r * h := by
    have hs := card_add_subgroup_eq_cyclicQuotient_image_mul K B
    simpa [f, r, h, hKH] using hs
  have hkneser : 2 * (r * h) ≤ e + h := by
    have hk := Finset.add_kneser B B
    simpa [H, e, h, hBsat, two_mul] using hk
  have hstabLower : (2 * r - 1) * h ≤ e := by
    have hsub : 2 * (r * h) - h ≤ e := by
      apply Nat.sub_le_of_le_add
      simpa [Nat.add_comm] using hkneser
    have hid : (2 * r - 1) * h = 2 * (r * h) - h := by
      rw [Nat.sub_mul]
      ring
    rwa [hid]
  have hBsaturation : B.card ≤ r * h := by
    have hsub : B ⊆ B + H := by
      have hzH : 0 ∈ H := by
        simpa [H] using (Finset.zero_mem_addStab.mpr hBB)
      intro b hb
      exact Finset.mem_add.mpr ⟨b, hb, 0, hzH, by simp⟩
    have hc := Finset.card_le_card hsub
    rw [hBsat] at hc
    exact hc
  have hre : e ≤ d := by
    dsimp [e, d]
    exact Finset.card_le_card (Finset.add_subset_add hBA hBA)
  have hrdense : B.card + e ≤ d := by
    simpa [e, d] using hdisjointCard
  have hrle : r ≤ 5 := by
    by_contra hrnot
    have hr6 : 6 ≤ r := by omega
    have hcoeff : 29 * r ≤ 16 * (2 * r - 1) := by omega
    have h29 : 29 * B.card ≤ 16 * e := by
      calc
        29 * B.card ≤ 29 * (r * h) := Nat.mul_le_mul_left 29 hBsaturation
        _ = (29 * r) * h := by ring
        _ ≤ (16 * (2 * r - 1)) * h := Nat.mul_le_mul_right h hcoeff
        _ = 16 * ((2 * r - 1) * h) := by ring
        _ ≤ 16 * e := Nat.mul_le_mul_left 16 hstabLower
    have h45 : 45 * B.card ≤ 16 * d := by
      calc
        45 * B.card = 16 * B.card + 29 * B.card := by ring
        _ ≤ 16 * B.card + 16 * e := Nat.add_le_add_left h29 _
        _ = 16 * (B.card + e) := by ring
        _ ≤ 16 * d := Nat.mul_le_mul_left 16 hrdense
    have hdenseB' : 4 * A.card < 5 * B.card := by
      simpa [hcardA] using hdenseB
    have hdoub' : 4 * d < 9 * A.card := by
      simpa [d, hcardA, hcardAA] using hdoub
    omega
  have himageProduct : q * B.card ≤ r * d := by
    have hp := card_image_mul_card_le_card_image_mul_card_add f A B hB
    have hABsub : A + B ⊆ A + A :=
      Finset.add_subset_add (Finset.Subset.rfl) hBA
    have hABcard : (A + B).card ≤ d := by
      simpa [d] using Finset.card_le_card hABsub
    calc
      q * B.card ≤ r * (A + B).card := by simpa [q, r] using hp
      _ ≤ r * d := Nat.mul_le_mul_left r hABcard
  have hq_lt : q < 3 * r := by
    by_contra hqnot
    have h3r : 3 * r ≤ q := by omega
    have h3 : 3 * B.card ≤ d := by
      have hmul : (3 * r) * B.card ≤ r * d :=
        le_trans (Nat.mul_le_mul_right B.card h3r) himageProduct
      have hrewrite : (3 * r) * B.card = r * (3 * B.card) := by ring
      rw [hrewrite] at hmul
      exact Nat.le_of_mul_le_mul_left hmul hrpos
    have hdenseB' : 4 * A.card < 5 * B.card := by
      simpa [hcardA] using hdenseB
    have hdoub' : 4 * d < 9 * A.card := by
      simpa [d, hcardA, hcardAA] using hdoub
    omega
  have hq14 : q ≤ 14 := by omega
  have hqt : q ≤ t := le_trans hq14 ht
  let D : Set (ZMod m) := f '' C
  have hzD : 0 ∈ D := by
    refine ⟨0, hzero, ?_⟩
    simp [D]
  have hpD : ∃ u : ℕ, ExactPower D u = Set.univ := by
    exact exactPower_univ_image_of_surjective f hf hprimitive
  have himageA : A.image f = exactPowerFinset D t := by
    simpa [A, D] using image_exactPowerFinset f C t
  have hsmallD : (ExactPower D t).ncard ≤ q := by
    rw [← card_exactPowerFinset, ← himageA]
  have hmleq : m ≤ q := by
    have hc := card_le_of_highPower_ncard_le hzD hpD hqt hsmallD
    simpa [ZMod.card] using hc
  have hGcard : Fintype.card (ZMod N) =
      m * (addSubgroupFinset K).card := by
    letI : Fintype K := Fintype.ofFinite K
    rw [← Nat.card_eq_fintype_card,
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
    congr 1
    simpa [addSubgroupFinset] using (Nat.card_eq_fintype_card (α := K))
  have hNcard : N = m * h := by
    rw [ZMod.card] at hGcard
    simpa [h, hKH] using hGcard
  have hNle : N ≤ 3 * d := by
    calc
      N = m * h := hNcard
      _ ≤ q * h := Nat.mul_le_mul_right h hmleq
      _ ≤ (3 * r) * h := Nat.mul_le_mul_right h (Nat.le_of_lt hq_lt)
      _ = 3 * (r * h) := by ring
      _ ≤ 3 * ((2 * r - 1) * h) := by
        apply Nat.mul_le_mul_left 3
        apply Nat.mul_le_mul_right h
        omega
      _ ≤ 3 * e := Nat.mul_le_mul_left 3 hstabLower
      _ ≤ 3 * d := Nat.mul_le_mul_left 3 hre
  have hN7 : N < 7 * A.card := by
    have hdoub' : 4 * d < 9 * A.card := by
      simpa [d, hcardA, hcardAA] using hdoub
    omega
  let S : Set (ZMod N) := ExactPower C t
  have hzS : 0 ∈ S := by
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hpower : ExactPower S 2 = ExactPower C (2 * t) := by
    simpa [S] using exactPower_exactPower C t 2
  have hweight : stableWeight S = d - 1 := by
    rw [stableWeight_eq_double_sub_one hzS, hpower]
    rw [← card_exactPowerFinset, ← hsumA]
  have haweight : A.card ≤ stableWeight S := by
    rw [hweight]
    have hs : 2 * A.card ≤ d + 1 := by
      simpa [d, hcardA, hcardAA] using hself
    omega
  have hK7 : 7 ≤ 10000000 * Nat.factorial 36 := by
    norm_num [Nat.factorial]
  have hForbiddenDensity : N <
      (10000000 * Nat.factorial 36) * stableWeight S := by
    calc
      N < 7 * A.card := hN7
      _ ≤ (10000000 * Nat.factorial 36) * A.card :=
        Nat.mul_le_mul_right A.card hK7
      _ ≤ (10000000 * Nat.factorial 36) * stableWeight S :=
        Nat.mul_le_mul_left _ haweight
  apply hnot
  change Fintype.card (ZMod N) = 1 ∨
    Fintype.card (ZMod N) < (10000000 * Nat.factorial 36) * stableWeight S ∨
    RankExceptionalCertificate S
  right
  left
  simpa [ZMod.card] using hForbiddenDensity

end Erdos336
