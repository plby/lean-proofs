import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Finite
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Normals.Axes
import Mathlib.Data.Set.Card

/-! Finiteness of actual support normals with a uniform positive face length. -/

open Set
open scoped BigOperators

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

theorem supporting_normals_finset_weight_le_box {K : Set Plane}
    (hK : Convex ℝ K) {δ : ℝ} (s : Finset (ℝ × ℝ))
    (hs : (s : Set (ℝ × ℝ)) ⊆ supportingNormalsAtLeast K δ)
    {l r bottom top : ℝ} (hlr : l ≤ r) (hbt : bottom ≤ top)
    (hbox : ∀ p ∈ K,
      (l ≤ p 0 ∧ p 0 ≤ r) ∧ (bottom ≤ p 1 ∧ p 1 ≤ top)) :
    (s.card : ℝ) * δ ≤ 2 * ((r - l) + (top - bottom)) := by
  classical
  have hw (i : s) : ∃ a b : Plane,
      SupportsSegment K i.val.1 i.val.2 a b ∧ δ ≤ dist a b := (hs i.property).2
  choose a b hface hlength using hw
  have hnorm (i : s) : i.val.1 ^ 2 + i.val.2 ^ 2 = 1 := (hs i.property).1
  have hinj : Function.Injective (fun i : s => (i.val.1, i.val.2)) := by
    intro i j hij
    exact Subtype.ext hij
  have hsum := sum_supporting_segment_lengths_le_box hK
    (fun i : s => i.val.1) (fun i : s => i.val.2) a b hface hnorm hinj hlr hbt hbox
  have hlower : (s.card : ℝ) * δ ≤ ∑ i : s, dist (a i) (b i) := by
    calc
      (s.card : ℝ) * δ = ∑ _i : s, δ := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hlength i
  exact hlower.trans hsum

/-- A bounded convex set has only finitely many outward unit normal
directions with supporting segments above a fixed positive length. -/
theorem supportingNormalsAtLeast_finite {K : Set Plane} (hK : Convex ℝ K)
    {δ : ℝ} (hδ : 0 < δ) {l r bottom top : ℝ}
    (hlr : l ≤ r) (hbt : bottom ≤ top)
    (hbox : ∀ p ∈ K,
      (l ≤ p 0 ∧ p 0 ≤ r) ∧ (bottom ≤ p 1 ∧ p 1 ≤ top)) :
    (supportingNormalsAtLeast K δ).Finite := by
  classical
  by_contra hinfinite
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ((r - l) + (top - bottom)) / δ)
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite N
  have hbound := supporting_normals_finset_weight_le_box hK s hs hlr hbt hbox
  rw [hcard] at hbound
  have hstrict := (div_lt_iff₀ hδ).mp hN
  linarith

/-- In a strict-height substrip of the square, the entire collection of
outward unit normals with unit supporting segments is finite and has at
most three elements. -/
theorem unitSupportingNormals_finite_and_ncard_le_three {K : Set Plane}
    (hK : Convex ℝ K) (hSquare : K ⊆ unitSquare)
    {l h : ℝ} (hlh : l ≤ h) (hheight : h - l < 1)
    (hstrip : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ h) :
    (unitSupportingNormals K).Finite ∧ (unitSupportingNormals K).ncard ≤ 3 := by
  classical
  have hbox (p : Plane) (hp : p ∈ K) :
      ((0 : ℝ) ≤ p 0 ∧ p 0 ≤ 1) ∧ (l ≤ p 1 ∧ p 1 ≤ h) :=
    ⟨(hSquare hp).1, hstrip p hp⟩
  have hfinite : (unitSupportingNormals K).Finite :=
    supportingNormalsAtLeast_finite hK (by norm_num) (by norm_num) hlh hbox
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  have hbound := supporting_normals_finset_weight_le_box hK (δ := 1) hfinite.toFinset
    (by simp) (show (0 : ℝ) ≤ 1 by norm_num) hlh hbox
  have hlt : (hfinite.toFinset.card : ℝ) < 4 := by nlinarith
  have hnat : hfinite.toFinset.card < 4 := by exact_mod_cast hlt
  omega

end Puzzling139335.N4MiddleInvolutions.FaceBounds
