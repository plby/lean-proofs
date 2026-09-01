import Mathlib

namespace Erdos83

open Finset

/-- The first block of `2 * q` points in a ground set of size `4 * q`. -/
def firstHalf (q : ℕ) : Finset (Fin (4 * q)) :=
  Finset.univ.filter fun i ↦ i.1 < 2 * q

/-- The complementary block of `2 * q` points. -/
def secondHalf (q : ℕ) : Finset (Fin (4 * q)) :=
  (firstHalf q)ᶜ

/-- The uniform layer consisting of all `2 * q`-subsets of a `4 * q`-set. -/
def uniformFamily (q : ℕ) : Finset (Finset (Fin (4 * q))) :=
  (Finset.univ : Finset (Fin (4 * q))).powersetCard (2 * q)

/-- The sublayer having exactly `a` points in the first block. -/
def uniformLayer (q a : ℕ) : Finset (Finset (Fin (4 * q))) :=
  (uniformFamily q).filter fun A ↦ (A ∩ firstHalf q).card = a

/-- The standard extremal family: more than half of a member lies in the first block. -/
def majorityFamily (q : ℕ) : Finset (Finset (Fin (4 * q))) :=
  (uniformFamily q).filter fun A ↦ q + 1 ≤ (A ∩ firstHalf q).card

/-- The family paired with `majorityFamily` by complementation. -/
def minorityFamily (q : ℕ) : Finset (Finset (Fin (4 * q))) :=
  (uniformFamily q).filter fun A ↦ (A ∩ firstHalf q).card < q

theorem card_firstHalf (q : ℕ) : (firstHalf q).card = 2 * q := by
  classical
  calc
    (firstHalf q).card = (Finset.univ : Finset (Fin (2 * q))).card := by
      apply Finset.card_bij
          (fun i (hi : i ∈ firstHalf q) ↦
            (⟨i.1, (Finset.mem_filter.mp hi).2⟩ : Fin (2 * q)))
      · intro i hi
        simp
      · intro i hi j hj hij
        apply Fin.ext
        exact congrArg (fun x : Fin (2 * q) ↦ x.1) hij
      · intro j hj
        let i : Fin (4 * q) := ⟨j.1, by omega⟩
        refine ⟨i, ?_, ?_⟩
        · simp [firstHalf, i]
        · exact Fin.ext rfl
    _ = 2 * q := by simp

theorem card_secondHalf (q : ℕ) : (secondHalf q).card = 2 * q := by
  classical
  rw [secondHalf, Finset.card_compl, card_firstHalf]
  simp only [Fintype.card_fin]
  omega

theorem card_uniformFamily (q : ℕ) :
    (uniformFamily q).card = Nat.choose (4 * q) (2 * q) := by
  simp [uniformFamily, Finset.card_powersetCard]

theorem mem_uniformFamily {q : ℕ} {A : Finset (Fin (4 * q))} :
    A ∈ uniformFamily q ↔ A.card = 2 * q := by
  simp [uniformFamily]

theorem mem_uniformLayer {q a : ℕ} {A : Finset (Fin (4 * q))} :
    A ∈ uniformLayer q a ↔ A.card = 2 * q ∧ (A ∩ firstHalf q).card = a := by
  simp [uniformLayer, mem_uniformFamily]

theorem mem_majorityFamily {q : ℕ} {A : Finset (Fin (4 * q))} :
    A ∈ majorityFamily q ↔
      A.card = 2 * q ∧ q + 1 ≤ (A ∩ firstHalf q).card := by
  simp [majorityFamily, mem_uniformFamily]

theorem mem_minorityFamily {q : ℕ} {A : Finset (Fin (4 * q))} :
    A ∈ minorityFamily q ↔
      A.card = 2 * q ∧ (A ∩ firstHalf q).card < q := by
  simp [minorityFamily, mem_uniformFamily]

/-- Count a layer by independently choosing its points in the two equal blocks. -/
theorem card_uniformLayer (q a : ℕ) :
    (uniformLayer q a).card =
      Nat.choose (2 * q) a * Nat.choose (2 * q) (2 * q - a) := by
  classical
  calc
    (uniformLayer q a).card =
        ((firstHalf q).powersetCard a ×ˢ
          (secondHalf q).powersetCard (2 * q - a)).card := by
      apply Finset.card_bij
          (fun A (_ : A ∈ uniformLayer q a) ↦
            (A ∩ firstHalf q, A ∩ secondHalf q))
      · intro A hA
        rw [Finset.mem_product]
        have h := mem_uniformLayer.mp hA
        constructor
        · exact Finset.mem_powersetCard.mpr
            ⟨Finset.inter_subset_right, h.2⟩
        · apply Finset.mem_powersetCard.mpr
          constructor
          · exact Finset.inter_subset_right
          · have hdecomp :
                (A ∩ firstHalf q).card + (A ∩ secondHalf q).card = A.card := by
                rw [secondHalf]
                have hsdiff : A ∩ (firstHalf q)ᶜ = A \ firstHalf q := by
                  ext x
                  simp
                rw [hsdiff]
                exact Finset.card_inter_add_card_sdiff A (firstHalf q)
            have ha : a ≤ 2 * q := by
              rw [← h.2, ← h.1]
              exact Finset.card_le_card Finset.inter_subset_left
            have hsum :
                a + (A ∩ secondHalf q).card = 2 * q := by
              calc
                a + (A ∩ secondHalf q).card =
                    (A ∩ firstHalf q).card + (A ∩ secondHalf q).card := by
                      rw [h.2]
                _ = A.card := hdecomp
                _ = 2 * q := h.1
            exact Nat.eq_sub_of_add_eq' hsum
      · intro A hA B hB hEq
        have hfirst : A ∩ firstHalf q = B ∩ firstHalf q :=
          congrArg Prod.fst hEq
        have hsecond : A ∩ secondHalf q = B ∩ secondHalf q :=
          congrArg Prod.snd hEq
        ext x
        have hsplitA : x ∈ A ↔
            x ∈ A ∩ firstHalf q ∨ x ∈ A ∩ secondHalf q := by
          by_cases hx : x ∈ firstHalf q <;> simp [secondHalf, hx]
        have hsplitB : x ∈ B ↔
            x ∈ B ∩ firstHalf q ∨ x ∈ B ∩ secondHalf q := by
          by_cases hx : x ∈ firstHalf q <;> simp [secondHalf, hx]
        rw [hsplitA, hsplitB, hfirst, hsecond]
      · intro P hP
        rw [Finset.mem_product] at hP
        obtain ⟨hP₁, hP₂⟩ := hP
        have hP₁' := Finset.mem_powersetCard.mp hP₁
        have hP₂' := Finset.mem_powersetCard.mp hP₂
        let A := P.1 ∪ P.2
        have hdisj : Disjoint P.1 P.2 := by
          rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          have hxfirst := hP₁'.1 hx₁
          have hxsecond := hP₂'.1 hx₂
          have hxnotfirst : x ∉ firstHalf q := by
            simpa [secondHalf] using hxsecond
          exact hxnotfirst hxfirst
        have hAcard : A.card = 2 * q := by
          change (P.1 ∪ P.2).card = 2 * q
          rw [Finset.card_union_of_disjoint hdisj, hP₁'.2, hP₂'.2]
          have ha : a ≤ 2 * q := by
            rw [← hP₁'.2, ← card_firstHalf q]
            exact Finset.card_le_card hP₁'.1
          omega
        have hAfirst : A ∩ firstHalf q = P.1 := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hx₁ | hx₂
            · exact hx₁
            · have hxsecond := hP₂'.1 hx₂
              have hxfirst := (Finset.mem_inter.mp hx).2
              have hxnotfirst : x ∉ firstHalf q := by
                simpa [secondHalf] using hxsecond
              exact (hxnotfirst hxfirst).elim
          · intro hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hx, hP₁'.1 hx⟩
        have hAsecond : A ∩ secondHalf q = P.2 := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hx₁ | hx₂
            · have hxfirst := hP₁'.1 hx₁
              have hxsecond := (Finset.mem_inter.mp hx).2
              have hxnotfirst : x ∉ firstHalf q := by
                simpa [secondHalf] using hxsecond
              exact (hxnotfirst hxfirst).elim
            · exact hx₂
          · intro hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hx, hP₂'.1 hx⟩
        refine ⟨A, ?_, ?_⟩
        · apply mem_uniformLayer.mpr
          refine ⟨hAcard, ?_⟩
          rw [hAfirst]
          exact hP₁'.2
        · exact Prod.ext hAfirst hAsecond
    _ = Nat.choose (2 * q) a * Nat.choose (2 * q) (2 * q - a) := by
      rw [Finset.card_product, Finset.card_powersetCard,
        Finset.card_powersetCard, card_firstHalf, card_secondHalf]

/-- Any two members of the majority construction meet in at least two points. -/
theorem majorityFamily_two_intersecting {q : ℕ} {A B : Finset (Fin (4 * q))}
    (hA : A ∈ majorityFamily q) (hB : B ∈ majorityFamily q) :
    2 ≤ (A ∩ B).card := by
  classical
  have hA' := (mem_majorityFamily.mp hA).2
  have hB' := (mem_majorityFamily.mp hB).2
  have hunion :
      ((A ∩ firstHalf q) ∪ (B ∩ firstHalf q)).card ≤ 2 * q := by
    rw [← card_firstHalf q]
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hx).2
  have hcard := Finset.card_union_add_card_inter
    (A ∩ firstHalf q) (B ∩ firstHalf q)
  have hinter : 2 ≤ ((A ∩ firstHalf q) ∩ (B ∩ firstHalf q)).card := by
    omega
  apply le_trans hinter
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_inter] at hx ⊢
  exact ⟨hx.1.1, hx.2.1⟩

private theorem card_majority_eq_card_minority (q : ℕ) :
    (majorityFamily q).card = (minorityFamily q).card := by
  classical
  apply Finset.card_bij (fun A (_ : A ∈ majorityFamily q) ↦ Aᶜ)
  · intro A hA
    have hA' := mem_majorityFamily.mp hA
    apply mem_minorityFamily.mpr
    constructor
    · rw [Finset.card_compl]
      simp only [Fintype.card_fin]
      omega
    · have hblock : Aᶜ ∩ firstHalf q = firstHalf q \ A := by
        ext x
        simp [and_comm]
      rw [hblock, Finset.card_sdiff, card_firstHalf]
      have hinter : (A ∩ firstHalf q).card ≤ 2 * q := by
        rw [← card_firstHalf q]
        exact Finset.card_le_card Finset.inter_subset_right
      omega
  · intro A hA B hB hEq
    have := congrArg (fun S : Finset (Fin (4 * q)) ↦ Sᶜ) hEq
    simpa using this
  · intro B hB
    refine ⟨Bᶜ, ?_, ?_⟩
    · have hB' := mem_minorityFamily.mp hB
      apply mem_majorityFamily.mpr
      constructor
      · rw [Finset.card_compl]
        simp only [Fintype.card_fin]
        omega
      · have hblock : Bᶜ ∩ firstHalf q = firstHalf q \ B := by
          ext x
          simp [and_comm]
        rw [hblock, Finset.card_sdiff, card_firstHalf]
        have hinter : (B ∩ firstHalf q).card ≤ 2 * q := by
          rw [← card_firstHalf q]
          exact Finset.card_le_card Finset.inter_subset_right
        omega
    · simp

/-- Exact size of the standard construction, including the degenerate case `q = 0`. -/
theorem card_majorityFamily (q : ℕ) :
    (majorityFamily q).card =
      (Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2) / 2 := by
  classical
  have hdecomp :
      uniformFamily q =
        (majorityFamily q ∪ uniformLayer q q) ∪ minorityFamily q := by
    ext A
    simp only [mem_uniformFamily, Finset.mem_union, mem_majorityFamily,
      mem_uniformLayer, mem_minorityFamily]
    constructor
    · intro hA
      refine Or.elim (lt_trichotomy (A ∩ firstHalf q).card q) ?_ ?_
      · intro hlt
        exact Or.inr ⟨hA, hlt⟩
      · intro hrest
        rcases hrest with heq | hgt
        · exact Or.inl (Or.inr ⟨hA, heq⟩)
        · exact Or.inl (Or.inl ⟨hA, by omega⟩)
    · rintro ((hA | hA) | hA) <;> exact hA.1
  have hdisj₁ : Disjoint (majorityFamily q) (uniformLayer q q) := by
    rw [Finset.disjoint_left]
    intro A hmaj hmid
    have hmaj' := (mem_majorityFamily.mp hmaj).2
    have hmid' := (mem_uniformLayer.mp hmid).2
    omega
  have hdisj₂ : Disjoint (majorityFamily q ∪ uniformLayer q q) (minorityFamily q) := by
    rw [Finset.disjoint_left]
    intro A hhigh hlow
    rcases Finset.mem_union.mp hhigh with hmaj | hmid
    · have hmaj' := (mem_majorityFamily.mp hmaj).2
      have hlow' := (mem_minorityFamily.mp hlow).2
      omega
    · have hmid' := (mem_uniformLayer.mp hmid).2
      have hlow' := (mem_minorityFamily.mp hlow).2
      omega
  have hcount :
      (uniformFamily q).card =
        (majorityFamily q).card + (uniformLayer q q).card +
          (minorityFamily q).card := by
    rw [hdecomp, Finset.card_union_of_disjoint hdisj₂,
      Finset.card_union_of_disjoint hdisj₁]
  rw [card_uniformFamily, card_uniformLayer, ← card_majority_eq_card_minority] at hcount
  have hsymm : Nat.choose (2 * q) (2 * q - q) = Nat.choose (2 * q) q := by
    rw [Nat.choose_symm]
    omega
  rw [hsymm] at hcount
  have hsquare : Nat.choose (2 * q) q * Nat.choose (2 * q) q =
      Nat.choose (2 * q) q ^ 2 := by ring
  rw [hsquare] at hcount
  have hdiff :
      Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2 =
        2 * (majorityFamily q).card := by
    omega
  rw [hdiff]
  omega

end Erdos83
