/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ConvexPools

/-!
# Dense pools of coefficients bounded away from zero

The coefficient-ordered alternating split gives each side positive total
mass.  Since every coefficient is capped, a fixed lower threshold retains a
`delta`-dense subpool on each side.  These are the inputs to CFP in the
source proof of Lemma 14.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The part of a finite weighted pool whose coefficients exceed `theta`. -/
def largeCoefficientPool {α : Type*} [DecidableEq α]
    (S : Finset α) (q : α → ℝ) (theta : ℝ) : Finset α :=
  S.filter fun x ↦ theta ≤ q x

theorem largeCoefficientPool_subset {α : Type*} [DecidableEq α]
    (S : Finset α) (q : α → ℝ) (theta : ℝ) :
    largeCoefficientPool S q theta ⊆ S :=
  Finset.filter_subset _ _

theorem coefficient_lower_of_mem_largeCoefficientPool
    {α : Type*} [DecidableEq α] {S : Finset α} {q : α → ℝ}
    {theta : ℝ} {x : α} (hx : x ∈ largeCoefficientPool S q theta) :
    theta ≤ q x :=
  (Finset.mem_filter.mp hx).2

/-- A side with mass `massLower` has at least `delta*N` above-threshold
points whenever the displayed elementary budget is strict. -/
theorem card_largeCoefficientPool_of_mass
    {α : Type*} [DecidableEq α]
    (S : Finset α) (q : α → ℝ)
    (N : ℕ) (theta cap delta massLower : ℝ)
    (hS : S.card ≤ N)
    (htheta : 0 ≤ theta) (hcap : 0 < cap) (hdelta : 0 ≤ delta)
    (hq : ∀ x ∈ S, 0 ≤ q x ∧ q x ≤ cap)
    (hmass : massLower ≤ ∑ x ∈ S, q x)
    (hbudget : (N : ℝ) * theta + delta * (N : ℝ) * cap < massLower) :
    delta * (N : ℝ) ≤ ((largeCoefficientPool S q theta).card : ℝ) := by
  by_contra! hsmall
  let H := largeCoefficientPool S q theta
  let L := S \ H
  have hsplit : H ∪ L = S := by
    exact Finset.union_sdiff_of_subset (largeCoefficientPool_subset S q theta)
  have hdisj : Disjoint H L := Finset.disjoint_sdiff
  have hlow : ∀ x ∈ L, q x < theta := by
    intro x hx
    have hxS := (Finset.mem_sdiff.mp hx).1
    have hxH := (Finset.mem_sdiff.mp hx).2
    have hnot : ¬(x ∈ S ∧ theta ≤ q x) := by
      simpa [H, largeCoefficientPool] using hxH
    exact lt_of_not_ge fun h ↦ hnot ⟨hxS, h⟩
  have hsumLow : (∑ x ∈ L, q x) ≤ (N : ℝ) * theta := by
    calc
      (∑ x ∈ L, q x) ≤ ∑ _x ∈ L, theta := by
        exact Finset.sum_le_sum fun x hx ↦ (hlow x hx).le
      _ = (L.card : ℝ) * theta := by simp
      _ ≤ (N : ℝ) * theta := by
        apply mul_le_mul_of_nonneg_right _ htheta
        exact_mod_cast ((Finset.card_le_card Finset.sdiff_subset).trans hS)
  have hsumHigh : (∑ x ∈ H, q x) < delta * (N : ℝ) * cap := by
    calc
      (∑ x ∈ H, q x) ≤ ∑ _x ∈ H, cap := by
        apply Finset.sum_le_sum
        intro x hx
        exact (hq x (largeCoefficientPool_subset S q theta hx)).2
      _ = (H.card : ℝ) * cap := by simp
      _ < (delta * (N : ℝ)) * cap :=
        mul_lt_mul_of_pos_right hsmall hcap
      _ = delta * (N : ℝ) * cap := rfl
  have htotal : (∑ x ∈ S, q x) =
      (∑ x ∈ H, q x) + ∑ x ∈ L, q x := by
    rw [← Finset.sum_union hdisj, hsplit]
  rw [htotal] at hmass
  linarith

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- The high-coefficient part of the forward alternating pool. -/
def largeA₁ (D : ConvexPoolsData A a₀ c mu) (theta : ℝ) :
    Finset (LatticePoint d) :=
  largeCoefficientPool D.A₁ (pullCoefficient A c) theta

/-- The high-coefficient part of the reverse alternating pool. -/
def largeA₂ (D : ConvexPoolsData A a₀ c mu) (theta : ℝ) :
    Finset (LatticePoint d) :=
  largeCoefficientPool D.A₂ (pullCoefficient A c) theta

theorem largeA₁_subset (D : ConvexPoolsData A a₀ c mu) (theta : ℝ) :
    D.largeA₁ theta ⊆ D.A₁ :=
  largeCoefficientPool_subset _ _ _

theorem largeA₂_subset (D : ConvexPoolsData A a₀ c mu) (theta : ℝ) :
    D.largeA₂ theta ⊆ D.A₂ :=
  largeCoefficientPool_subset _ _ _

theorem coefficient_lower_largeA₁
    (D : ConvexPoolsData A a₀ c mu) {theta : ℝ}
    {x : LatticePoint d} (hx : x ∈ D.largeA₁ theta) :
    theta ≤ pullCoefficient A c x :=
  coefficient_lower_of_mem_largeCoefficientPool hx

theorem coefficient_lower_largeA₂
    (D : ConvexPoolsData A a₀ c mu) {theta : ℝ}
    {x : LatticePoint d} (hx : x ∈ D.largeA₂ theta) :
    theta ≤ pullCoefficient A c x :=
  coefficient_lower_of_mem_largeCoefficientPool hx

/-- Alternating selection retains at least `(1-2 cap)/2` coefficient mass
on the forward side, where `cap = (mu*|A|)⁻¹`. -/
theorem coefficient_mass_lower_uniform_A₁
    (D : ConvexPoolsData A a₀ c mu) :
    (1 - 2 * (mu * A.card)⁻¹) / 2 ≤
      ∑ x ∈ D.A₁, pullCoefficient A c x := by
  have haCap := (D.coefficient_bounds D.a D.a_mem).2
  have hmass := D.coefficient_mass_lower_A₁
  linarith

/-- The symmetric retained-mass estimate for the reverse side. -/
theorem coefficient_mass_lower_uniform_A₂
    (D : ConvexPoolsData A a₀ c mu) :
    (1 - 2 * (mu * A.card)⁻¹) / 2 ≤
      ∑ x ∈ D.A₂, pullCoefficient A c x := by
  have haCap := (D.coefficient_bounds D.a D.a_mem).2
  have hmass := D.coefficient_mass_lower_A₂
  linarith

/-- The elementary source budget which makes the forward high-coefficient
pool `delta`-dense in the original population. -/
theorem card_largeA₁_of_budget
    (D : ConvexPoolsData A a₀ c mu) (N : ℕ) (theta delta : ℝ)
    (hAcard : A.card ≤ N) (htheta : 0 ≤ theta)
    (hcap : 0 < (mu * A.card)⁻¹) (hdelta : 0 ≤ delta)
    (hbudget :
      (N : ℝ) * theta + delta * (N : ℝ) * (mu * A.card)⁻¹ <
        (1 - 2 * (mu * A.card)⁻¹) / 2) :
    delta * (N : ℝ) ≤ (D.largeA₁ theta).card := by
  apply card_largeCoefficientPool_of_mass D.A₁ (pullCoefficient A c)
    N theta (mu * A.card)⁻¹ delta
      ((1 - 2 * (mu * A.card)⁻¹) / 2)
  · exact (Finset.card_le_card
      (D.A₁_subset_erase.trans (Finset.erase_subset _ _))).trans hAcard
  · exact htheta
  · exact hcap
  · exact hdelta
  · intro x hx
    exact D.coefficient_bounds_A₁ hx
  · exact D.coefficient_mass_lower_uniform_A₁
  · exact hbudget

/-- Reverse-side version of `card_largeA₁_of_budget`. -/
theorem card_largeA₂_of_budget
    (D : ConvexPoolsData A a₀ c mu) (N : ℕ) (theta delta : ℝ)
    (hAcard : A.card ≤ N) (htheta : 0 ≤ theta)
    (hcap : 0 < (mu * A.card)⁻¹) (hdelta : 0 ≤ delta)
    (hbudget :
      (N : ℝ) * theta + delta * (N : ℝ) * (mu * A.card)⁻¹ <
        (1 - 2 * (mu * A.card)⁻¹) / 2) :
    delta * (N : ℝ) ≤ (D.largeA₂ theta).card := by
  apply card_largeCoefficientPool_of_mass D.A₂ (pullCoefficient A c)
    N theta (mu * A.card)⁻¹ delta
      ((1 - 2 * (mu * A.card)⁻¹) / 2)
  · exact (Finset.card_le_card
      (D.A₂_subset_erase.trans (Finset.erase_subset _ _))).trans hAcard
  · exact htheta
  · exact hcap
  · exact hdelta
  · intro x hx
    exact D.coefficient_bounds_A₂ hx
  · exact D.coefficient_mass_lower_uniform_A₂
  · exact hbudget

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
