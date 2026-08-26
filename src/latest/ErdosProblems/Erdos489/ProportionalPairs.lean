import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Two positive proportional real pairs with the same nonzero absolute
difference are equal. -/
theorem eq_of_pos_proportional_of_abs_sub_eq
    (x₁ y₁ x₂ y₂ : ℝ)
    (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (hprop : x₁ * y₂ = y₁ * x₂)
    (hdiff : 0 < |x₁ - y₁|)
    (habs : |x₁ - y₁| = |x₂ - y₂|) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  let lam : ℝ := x₂ / x₁
  have hlam : 0 < lam := div_pos hx₂ hx₁
  have hxscale : lam * x₁ = x₂ := by
    dsimp [lam]
    field_simp
  have hyscale : lam * y₁ = y₂ := by
    dsimp [lam]
    field_simp [hx₁.ne']
    nlinarith [hprop]
  have habscale : |x₂ - y₂| = lam * |x₁ - y₁| := by
    rw [← hxscale, ← hyscale, ← mul_sub, abs_mul, abs_of_pos hlam]
  have hlam1 : lam = 1 := by
    rw [habscale] at habs
    nlinarith
  constructor <;> nlinarith [hxscale, hyscale]

/-- Natural-number form: positive proportional pairs with the same positive
`Nat.dist` are identical. -/
theorem nat_pair_eq_of_proportional_of_dist_eq
    (x₁ y₁ x₂ y₂ : ℕ)
    (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (hprop : x₁ * y₂ = y₁ * x₂)
    (hdpos : 0 < Nat.dist x₁ y₁)
    (hdist : Nat.dist x₁ y₁ = Nat.dist x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have cast_natDist : ∀ x y : ℕ,
      ((Nat.dist x y : ℕ) : ℝ) = |(x : ℝ) - (y : ℝ)| := by
    intro x y
    rcases le_total x y with hxy | hyx
    · rw [Nat.dist_eq_sub_of_le hxy, Nat.cast_sub hxy,
        abs_of_nonpos (by
          have hxyR : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
          linarith)]
      ring
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx, Nat.cast_sub hyx,
        abs_of_nonneg (by
          have hyxR : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyx
          linarith)]
  have hpropR : (x₁ : ℝ) * (y₂ : ℝ) = (y₁ : ℝ) * (x₂ : ℝ) := by
    exact_mod_cast hprop
  have hdiffR : 0 < |(x₁ : ℝ) - (y₁ : ℝ)| := by
    rw [← cast_natDist]
    exact_mod_cast hdpos
  have habsR : |(x₁ : ℝ) - (y₁ : ℝ)| = |(x₂ : ℝ) - (y₂ : ℝ)| := by
    rw [← cast_natDist, ← cast_natDist]
    exact_mod_cast hdist
  have h := eq_of_pos_proportional_of_abs_sub_eq
    (x₁ : ℝ) (y₁ : ℝ) (x₂ : ℝ) (y₂ : ℝ)
    (by exact_mod_cast hx₁) (by exact_mod_cast hy₁)
    (by exact_mod_cast hx₂) (by exact_mod_cast hy₂)
    hpropR hdiffR habsR
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- A family of distinct positive covered-number columns that are pairwise
proportional and whose within-column distance lies in `[1,D]` has at most `D`
members.  Thus the determinant-zero alternative from F-018 has bounded
multiplicity when the selected witness pair has bounded physical separation. -/
theorem card_le_of_pairwise_proportional_bounded_dist
    {α : Type*} [DecidableEq α] (S : Finset α)
    (x y : α → ℕ) (D : ℕ)
    (hpairinj : Set.InjOn (fun i => (x i, y i)) (S : Set α))
    (hxpos : ∀ i ∈ S, 0 < x i) (hypos : ∀ i ∈ S, 0 < y i)
    (hprop : ∀ i ∈ S, ∀ j ∈ S, x i * y j = y i * x j)
    (hdpos : ∀ i ∈ S, 0 < Nat.dist (x i) (y i))
    (hdle : ∀ i ∈ S, Nat.dist (x i) (y i) ≤ D) :
    S.card ≤ D := by
  let delta : α → ℕ := fun i => Nat.dist (x i) (y i)
  have hdinj : Set.InjOn delta (S : Set α) := by
    intro i hi j hj hij
    apply hpairinj hi hj
    have hp := nat_pair_eq_of_proportional_of_dist_eq
      (x i) (y i) (x j) (y j)
      (hxpos i hi) (hypos i hi) (hxpos j hj) (hypos j hj)
      (hprop i hi j hj) (hdpos i hi) hij
    exact Prod.ext hp.1 hp.2
  have hcard : (S.image delta).card = S.card :=
    Finset.card_image_iff.mpr hdinj
  have himage : S.image delta ⊆ Finset.Icc 1 D := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨i, hi, rfl⟩
    exact Finset.mem_Icc.mpr ⟨hdpos i hi, hdle i hi⟩
  rw [← hcard]
  calc
    (S.image delta).card ≤ (Finset.Icc 1 D).card := Finset.card_le_card himage
    _ ≤ D := by simp

end Erdos489
