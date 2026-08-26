import Mathlib

/-!
# Consecutive blocks for Erdős Problem 421

Elementary ingredients of Przemek Chojecki's gap-greedy construction, as
reconstructed in Rob Sneiderman's July 20, 2026 note.
-/

namespace Erdos421

/-- A nonempty consecutive block in the increasing ordering of a finite set. -/
structure IsBlock (A B : Finset ℕ) : Prop where
  nonempty : B.Nonempty
  subset : B ⊆ A
  convex : ∀ ⦃a b x⦄, a ∈ B → b ∈ B → x ∈ A → a ≤ x → x ≤ b → x ∈ B

/-- Distinct nonempty consecutive blocks have distinct products. -/
def CollisionFree (A : Finset ℕ) : Prop :=
  ∀ B C, IsBlock A B → IsBlock A C → B.prod id = C.prod id → B = C

theorem two_le_prod {A : Finset ℕ} (hA : A.Nonempty)
    (h : ∀ a ∈ A, 2 ≤ a) : 2 ≤ A.prod id := by
  obtain ⟨a, ha⟩ := hA
  calc
    2 ≤ a := h a ha
    _ = ({a} : Finset ℕ).prod id := by simp
    _ ≤ A.prod id := Finset.prod_le_prod_of_subset_of_one_le'
      (Finset.singleton_subset_iff.mpr ha) (by intro x hx _; exact (h x hx).trans' (by decide))

theorem eq_of_subset_of_prod_eq {A B : Finset ℕ} (hAB : A ⊆ B)
    (hB : ∀ b ∈ B, 2 ≤ b) (hprod : A.prod id = B.prod id) : A = B := by
  have hpos : 0 < A.prod id := Finset.prod_pos fun a ha ↦ by
    have := hB a (hAB ha)
    exact Nat.zero_lt_of_lt this
  have hmul := Finset.prod_sdiff (f := id) hAB
  rw [← hprod] at hmul
  have hone : (B \ A).prod id = 1 := by nlinarith
  apply Finset.Subset.antisymm hAB
  intro b hb
  by_contra hba
  have htwo := two_le_prod ⟨b, Finset.mem_sdiff.mpr ⟨hb, hba⟩⟩
    (fun x hx ↦ hB x (Finset.mem_sdiff.mp hx).1)
  omega

theorem prime_not_dvd_prod {p : ℕ} (hp : p.Prime) {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a ∧ a < p) : ¬ p ∣ A.prod id := by
  intro h
  obtain ⟨a, ha, hpa⟩ := (hp.prime.dvd_finsetProd_iff id).mp h
  exact (not_le_of_gt (hA a ha).2) (Nat.le_of_dvd (hA a ha).1 hpa)

theorem IsBlock.restrict {A B C : Finset ℕ} (h : IsBlock A B)
    (hC : C ⊆ A) (hBC : B ⊆ C) : IsBlock C B :=
  ⟨h.nonempty, hBC, fun _ _ _ ha hb hx hax hxb ↦ h.convex ha hb (hC hx) hax hxb⟩

theorem IsBlock.subset_or_subset_of_common_max {A B C : Finset ℕ} {q : ℕ}
    (hB : IsBlock A B) (hC : IsBlock A C)
    (hmax : ∀ a ∈ A, a ≤ q) (hqB : q ∈ B) (hqC : q ∈ C) :
    B ⊆ C ∨ C ⊆ B := by
  by_cases hBC : B ⊆ C
  · exact Or.inl hBC
  · right
    obtain ⟨b, hb, hbc⟩ := Finset.not_subset.mp hBC
    intro c hc
    have hbc' : b < c := by
      by_contra h
      exact hbc (hC.convex hc hqC (hB.subset hb) (by omega) (hmax b (hB.subset hb)))
    exact hB.convex hb hqB (hC.subset hc) hbc'.le (hmax c (hC.subset hc))

/-- Appending a new prime to a certified prefix cannot create a collision. -/
theorem CollisionFree.insert_prime {A : Finset ℕ} {q : ℕ}
    (hA : CollisionFree A) (hq : q.Prime)
    (hbound : ∀ a ∈ A, 2 ≤ a ∧ a < q) : CollisionFree (insert q A) := by
  have htwo : ∀ a ∈ insert q A, 2 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hq.two_le
    · exact (hbound a ha).1
  have hmax : ∀ a ∈ insert q A, a ≤ q := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    · exact (hbound a ha).2.le
  have hsubset : ∀ B : Finset ℕ, B ⊆ insert q A → q ∉ B → B ⊆ A := by
    intro B hB hqB b hb
    rcases Finset.mem_insert.mp (hB hb) with rfl | h
    · exact False.elim (hqB hb)
    · exact h
  have hnot : ∀ B : Finset ℕ, B ⊆ A → ¬ q ∣ B.prod id := by
    intro B hB
    apply prime_not_dvd_prod hq
    intro b hb
    exact ⟨by have := (hbound b (hB hb)).1; omega, (hbound b (hB hb)).2⟩
  intro B C hB hC hprod
  by_cases hqB : q ∈ B <;> by_cases hqC : q ∈ C
  · rcases hB.subset_or_subset_of_common_max hC hmax hqB hqC with h | h
    · exact eq_of_subset_of_prod_eq h (fun b hb ↦ htwo b (hC.subset hb)) hprod
    · exact (eq_of_subset_of_prod_eq h (fun b hb ↦ htwo b (hB.subset hb)) hprod.symm).symm
  · exfalso
    apply hnot C (hsubset C hC.subset hqC)
    rw [← hprod]
    exact Finset.dvd_prod_of_mem id hqB
  · exfalso
    apply hnot B (hsubset B hB.subset hqB)
    rw [hprod]
    exact Finset.dvd_prod_of_mem id hqC
  · exact hA B C
      (hB.restrict (Finset.subset_insert q A) (hsubset B hB.subset hqB))
      (hC.restrict (Finset.subset_insert q A) (hsubset C hC.subset hqC)) hprod

/-- Cancellation of a common part of two products of positive integers. -/
theorem prod_sdiff_eq_of_prod_eq {E R : Finset ℕ}
    (hpos : ∀ a ∈ E, 0 < a) (hprod : E.prod id = R.prod id) :
    (E \ R).prod id = (R \ E).prod id := by
  have hp : (E ∩ R).prod id ≠ 0 :=
    (Finset.prod_pos fun a ha ↦ hpos a (Finset.mem_inter.mp ha).1).ne'
  apply mul_left_cancel₀ hp
  rw [Finset.prod_inter_mul_prod_sdiff, Finset.inter_comm,
    Finset.prod_inter_mul_prod_sdiff]
  exact hprod

/-- An equality of separated products cannot put a prime in its later block. -/
theorem not_prime_mem_later {E R : Finset ℕ}
    (hpos : ∀ a ∈ E, 0 < a)
    (hsep : ∀ e ∈ E, ∀ r ∈ R, e < r)
    (hprod : E.prod id = R.prod id) {p : ℕ} (hpR : p ∈ R) : ¬ p.Prime := by
  intro hp
  apply prime_not_dvd_prod hp (fun a ha ↦ ⟨hpos a ha, hsep a ha p hpR⟩)
  rw [hprod]
  exact Finset.dvd_prod_of_mem id hpR

/-- Equal products in separated nonempty blocks force more earlier factors. -/
theorem earlier_card_gt {E R : Finset ℕ} (hE : E.Nonempty) (hR : R.Nonempty)
    (hpos : ∀ a ∈ E, 0 < a)
    (hsep : ∀ e ∈ E, ∀ r ∈ R, e < r)
    (hprod : E.prod id = R.prod id) : R.card < E.card := by
  by_contra h
  have hcard : E.card ≤ R.card := by omega
  have hmaxmin : E.max' hE < R.min' hR :=
    hsep _ (E.max'_mem hE) _ (R.min'_mem hR)
  have hminpos : 0 < R.min' hR :=
    (hpos _ (E.max'_mem hE)).trans hmaxmin
  have hlt : E.prod id < R.prod id := calc
    E.prod id ≤ (E.max' hE) ^ E.card :=
      Finset.prod_le_pow_card E id _ (fun x hx ↦ E.le_max' x hx)
    _ < (R.min' hR) ^ E.card := Nat.pow_lt_pow_left hmaxmin hE.card_pos.ne'
    _ ≤ (R.min' hR) ^ R.card := Nat.pow_le_pow_right hminpos hcard
    _ ≤ R.prod id := Finset.pow_card_le_prod R id _ (fun x hx ↦ R.min'_le x hx)
  exact hlt.ne hprod

/-- The version of a consecutive block used for an infinite set. -/
structure IsSetBlock (A : Set ℕ) (B : Finset ℕ) : Prop where
  nonempty : B.Nonempty
  subset : ∀ b ∈ B, b ∈ A
  convex : ∀ ⦃a b x⦄, a ∈ B → b ∈ B → x ∈ A → a ≤ x → x ≤ b → x ∈ B

def SetCollisionFree (A : Set ℕ) : Prop :=
  ∀ B C, IsSetBlock A B → IsSetBlock A C → B.prod id = C.prod id → B = C

theorem IsSetBlock.restrict {A : Set ℕ} {B C : Finset ℕ}
    (h : IsSetBlock A B) (hC : ∀ c ∈ C, c ∈ A) (hBC : B ⊆ C) : IsBlock C B :=
  ⟨h.nonempty, hBC, fun _ _ _ ha hb hx hax hxb ↦ h.convex ha hb (hC _ hx) hax hxb⟩

theorem image_Icc_isSetBlock {d : ℕ → ℕ} (hd : StrictMono d) {u v : ℕ}
    (huv : u ≤ v) : IsSetBlock (Set.range d) ((Finset.Icc u v).image d) := by
  refine ⟨⟨d u, Finset.mem_image.mpr ⟨u, Finset.mem_Icc.mpr ⟨le_rfl, huv⟩, rfl⟩⟩,
    ?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i, rfl⟩
  · intro a b x ha hb hx hax hxb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, rfl⟩ := hx
    refine Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · exact (Finset.mem_Icc.mp hi).1.trans (hd.le_iff_le.mp hax)
    · exact (hd.le_iff_le.mp hxb).trans (Finset.mem_Icc.mp hj).2

/-- The finite-set formulation implies exactly the original index-interval injectivity. -/
theorem blockProducts_injective {d : ℕ → ℕ} (hd : StrictMono d)
    (hD : SetCollisionFree (Set.range d)) :
    {uv : ℕ × ℕ | uv.1 ≤ uv.2}.InjOn
      (fun uv ↦ ∏ i ∈ Finset.Icc uv.1 uv.2, d i) := by
  rintro ⟨u, v⟩ huv ⟨w, z⟩ hwz heq
  have hblocks : (Finset.Icc u v).image d = (Finset.Icc w z).image d := by
    apply hD _ _ (image_Icc_isSetBlock hd huv) (image_Icc_isSetBlock hd hwz)
    simpa only [Finset.prod_image hd.injective.injOn, id_eq] using heq
  have hmem : ∀ i, i ∈ Finset.Icc u v ↔ i ∈ Finset.Icc w z := by
    intro i
    have hi : d i ∈ (Finset.Icc u v).image d ↔ d i ∈ (Finset.Icc w z).image d := by
      rw [hblocks]
    simpa only [Finset.mem_image, hd.injective.eq_iff, exists_eq_right] using hi
  have hu := (hmem u).mp (Finset.mem_Icc.mpr ⟨le_rfl, huv⟩)
  have hv := (hmem v).mp (Finset.mem_Icc.mpr ⟨huv, le_rfl⟩)
  have hw := (hmem w).mpr (Finset.mem_Icc.mpr ⟨le_rfl, hwz⟩)
  have hz := (hmem z).mpr (Finset.mem_Icc.mpr ⟨hwz, le_rfl⟩)
  simp only [Finset.mem_Icc] at hu hv hw hz
  congr 1 <;> omega

end Erdos421
