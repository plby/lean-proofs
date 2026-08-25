import ErdosProblems.Erdos157.FiniteFiberCounts
import ErdosProblems.Erdos157.Parabola

/-! Triple-product counts from uniform one-variable fibers. -/

namespace Erdos157.Elementary.GroupTripleCounts

open FiniteFiberCounts

variable {A G : Type*} [Fintype A] [Group G] [Fintype G]

def tripleProduct (x : A → G) (t : A × A × A) : G := x t.1 * x t.2.1 * x t.2.2

def tripleFiberEquiv (x : A → G) (u : G) :
    {t : A × A × A // tripleProduct x t = u} ≃
      (Σ ab : A × A, {c : A // x c = (x ab.1 * x ab.2)⁻¹ * u}) where
  toFun t := ⟨(t.1.1, t.1.2.1), t.1.2.2, by
    simpa only [tripleProduct, inv_mul_cancel_left] using
      congrArg (fun v => (x t.1.1 * x t.1.2.1)⁻¹ * v) t.2⟩
  invFun t := ⟨(t.1.1, t.1.2, t.2.1), by
    change (x t.1.1 * x t.1.2) * x t.2.1 = u
    rw [t.2.2, mul_inv_cancel_left]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem triple_fiber_lower (x : A → G) (u : G) (L : ℝ)
    (hlower : ∀ b, L ≤ fiberCard x b) :
    (Fintype.card A : ℝ) ^ 2 * L ≤ fiberCard (tripleProduct x) u := by
  classical
  have hcard : fiberCard (tripleProduct x) u =
      ∑ ab : A × A, fiberCard x ((x ab.1 * x ab.2)⁻¹ * u) := by
    rw [fiberCard, Nat.card_congr (tripleFiberEquiv x u), Nat.card_sigma]
    rfl
  rw [hcard, Nat.cast_sum]
  calc
    _ = ∑ _ab : A × A, L := by simp [pow_two]
    _ ≤ _ := Finset.sum_le_sum (fun ab _ => hlower _)

theorem triple_fiber_lower_uniform (x : A → G) (u : G) (L : ℝ) (hL : 0 ≤ L)
    (hlower : ∀ b, L ≤ fiberCard x b) :
    (Fintype.card G : ℝ) ^ 2 * L ^ 3 ≤ fiberCard (tripleProduct x) u := by
  have hA := card_le_of_fiber_lower x L hlower
  calc
    _ = ((Fintype.card G : ℝ) * L) ^ 2 * L := by ring
    _ ≤ (Fintype.card A : ℝ) ^ 2 * L := by gcongr
    _ ≤ _ := triple_fiber_lower x u L hlower

def Distinct (t : A × A × A) : Prop := t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

theorem support_card_of_distinct [DecidableEq A] {t : A × A × A} (ht : Distinct t) :
    (Parabola.support t).card = 3 := by
  rcases t with ⟨a, b, c⟩
  rcases ht with ⟨hab, hac, hbc⟩
  simp [Parabola.support, hab, hac, hbc]

theorem support_prod_of_distinct {B : Type*} [CommMonoid B] [DecidableEq A]
    (x : A → B) {t : A × A × A} (ht : Distinct t) :
    (∏ a ∈ Parabola.support t, x a) = x t.1 * x t.2.1 * x t.2.2 := by
  rcases t with ⟨a, b, c⟩
  rcases ht with ⟨hab, hac, hbc⟩
  simp [Parabola.support, hab, hac, hbc, mul_assoc]

noncomputable def repeatedTriples : Finset (A × A × A) := by
  classical
  exact Finset.univ.filter (fun t => ¬Distinct t)

theorem repeatedTriples_card_le : (repeatedTriples (A := A)).card ≤ 3 * Fintype.card A ^ 2 := by
  classical
  let s : Finset (A × A) := Finset.univ
  let s1 := s.image (fun ab => (ab.1, ab.1, ab.2))
  let s2 := s.image (fun ab => (ab.1, ab.2, ab.1))
  let s3 := s.image (fun ab => (ab.1, ab.2, ab.2))
  have hsub : repeatedTriples (A := A) ⊆ s1 ∪ s2 ∪ s3 := by
    rintro ⟨a, b, c⟩ ht
    have h : a = b ∨ a = c ∨ b = c := by
      have h' := (Finset.mem_filter.mp ht).2
      simpa only [Distinct, not_and_or, not_not] using h'
    rcases h with rfl | rfl | rfl
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(a, c), Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩
  calc
    _ ≤ (s1 ∪ s2 ∪ s3).card := Finset.card_le_card hsub
    _ ≤ (s1.card + s2.card) + s3.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (s.card + s.card) + s.card := by
      exact Nat.add_le_add (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))
        (Finset.card_image_le)
    _ = _ := by simp only [s, Finset.card_univ, Fintype.card_prod]; ring

noncomputable def productTriples (x : A → G) (u : G) : Finset (A × A × A) := by
  classical
  exact Finset.univ.filter (fun t => tripleProduct x t = u)

noncomputable def distinctTriples (x : A → G) (u : G) : Finset (A × A × A) := by
  classical
  exact (productTriples x u).filter Distinct

theorem mem_distinctTriples (x : A → G) (u : G) (t : A × A × A) :
    t ∈ distinctTriples x u ↔ tripleProduct x t = u ∧ Distinct t := by
  classical
  simp only [distinctTriples, productTriples, Finset.mem_filter, Finset.mem_univ, true_and]

theorem productTriples_card (x : A → G) (u : G) :
    (productTriples x u).card = fiberCard (tripleProduct x) u := by
  classical
  simp only [productTriples, fiberCard, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem distinctTriples_card_lower (x : A → G) (u : G) (L : ℝ) (hL : 6 ≤ L)
    (hlower : ∀ b, L ≤ fiberCard x b) :
    (Fintype.card G : ℝ) ^ 2 * L ^ 3 / 2 ≤ (distinctTriples x u).card := by
  classical
  have hA := card_le_of_fiber_lower x L hlower
  have htotal := triple_fiber_lower x u L hlower
  have hsplit := Finset.card_filter_add_card_filter_not (s := productTriples x u) Distinct
  have hbad : ((productTriples x u).filter (fun t => ¬Distinct t)).card ≤ 3 * Fintype.card A ^ 2 := by
    apply le_trans (Finset.card_le_card (show (productTriples x u).filter (fun t => ¬Distinct t) ⊆
        repeatedTriples from fun t ht => by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩))
    exact repeatedTriples_card_le
  have hsplit' : ((distinctTriples x u).card : ℝ) +
      (((productTriples x u).filter (fun t => ¬Distinct t)).card : ℝ) =
        fiberCard (tripleProduct x) u := by
    rw [← productTriples_card]
    exact_mod_cast hsplit
  have hbad' : (((productTriples x u).filter (fun t => ¬Distinct t)).card : ℝ) ≤
      3 * (Fintype.card A : ℝ) ^ 2 := by exact_mod_cast hbad
  have hhalf : (Fintype.card A : ℝ) ^ 2 * L / 2 ≤ (distinctTriples x u).card := by
    nlinarith [sq_nonneg (Fintype.card A : ℝ)]
  have hsq : ((Fintype.card G : ℝ) * L) ^ 2 ≤ (Fintype.card A : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hA
  nlinarith

theorem support_image_card_lower [DecidableEq A] (x : A → G) (u : G) (L : ℝ) (hL : 6 ≤ L)
    (hlower : ∀ b, L ≤ fiberCard x b) :
    (Fintype.card G : ℝ) ^ 2 * L ^ 3 / 54 ≤
      ((distinctTriples x u).image Parabola.support).card := by
  classical
  have hlow := distinctTriples_card_lower x u L hL hlower
  have hhigh := Parabola.card_le_twentyseven_mul_card_support_image (distinctTriples x u)
  have hc : ((distinctTriples x u).card : ℝ) ≤
      27 * (((distinctTriples x u).image Parabola.support).card : ℝ) := by exact_mod_cast hhigh
  linarith

end Erdos157.Elementary.GroupTripleCounts
