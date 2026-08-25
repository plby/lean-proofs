import Mathlib

/-!
# The two incoming-aligned N5 contradictions

The reflected placement is excluded by its actual endpoint coordinate.
The translated placement is excluded by the mismatch between its support
contact sets.  The latter lemma is stated for arbitrary coordinate maps,
so it applies to any chosen model of the Euclidean plane.
-/

namespace Puzzling139335.N5Facet

theorem aligned_reflection_endpoint_impossible {c s h k L : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1) (hs : 0 < s)
    (hz : 0 < c * k - s * h) (hd : c * h + s * k = L)
    (hendpoint : 0 ≤ h - L * c) : False := by
  have hscaled := congrArg (fun x : ℝ => h * x) hunit
  have hpositive := mul_pos hs hz
  rw [← hd] at hendpoint
  nlinarith only [hscaled, hpositive, hendpoint]

/-- Diagonal symmetry cannot exchange a singleton minimum-coordinate
contact set with two minimum-coordinate points having different coordinates. -/
theorem diagonal_support_contact_mismatch {α : Type*}
    (V : Set α) (x y : α → ℝ) (swap : α → α)
    (hstable : ∀ p ∈ V, swap p ∈ V)
    (hxswap : ∀ p, x (swap p) = y p)
    (hyswap : ∀ p, y (swap p) = x p)
    {mx my : ℝ}
    (hminx : ∀ p ∈ V, mx ≤ x p) (hminy : ∀ p ∈ V, my ≤ y p)
    {r a b : α} (hr : r ∈ V) (ha : a ∈ V) (hb : b ∈ V)
    (hxr : x r = mx) (hya : y a = my) (hyb : y b = my)
    (hunique : ∀ p ∈ V, x p = mx → p = r)
    (hdistinct : x a ≠ x b) : False := by
  have hmxmy := hminx (swap a) (hstable a ha)
  rw [hxswap, hya] at hmxmy
  have hmymx := hminy (swap r) (hstable r hr)
  rw [hyswap, hxr] at hmymx
  have hmm : mx = my := le_antisymm hmxmy hmymx
  have har : swap a = r := hunique (swap a) (hstable a ha) (by
    rw [hxswap, hya, hmm])
  have hbr : swap b = r := hunique (swap b) (hstable b hb) (by
    rw [hxswap, hyb, hmm])
  apply hdistinct
  calc
    x a = y (swap a) := (hyswap a).symm
    _ = y r := congrArg y har
    _ = y (swap b) := (congrArg y hbr).symm
    _ = x b := hyswap b

/-- The diagonal and vertical symmetries determine the lower vertical
support value from the upper horizontal support value. -/
theorem reflected_symmetries_minimum {α : Type*}
    (V : Set α) (x y : α → ℝ) (swap reflect : α → α) (b : ℝ)
    (hswap : ∀ p ∈ V, swap p ∈ V) (hreflect : ∀ p ∈ V, reflect p ∈ V)
    (hxswap : ∀ p, x (swap p) = y p) (hyswap : ∀ p, y (swap p) = x p)
    (hxreflect : ∀ p, x (reflect p) = 1 + b - x p)
    (hupper : ∀ p ∈ V, x p ≤ 1)
    {r : α} (hr : r ∈ V) (hxr : x r = 1) :
    (∀ p ∈ V, b ≤ y p) ∧ ∃ p ∈ V, y p = b := by
  constructor
  · intro p hp
    have h := hupper (reflect (swap p)) (hreflect (swap p) (hswap p hp))
    rw [hxreflect, hxswap] at h
    linarith
  · refine ⟨swap (reflect r), hswap (reflect r) (hreflect r hr), ?_⟩
    rw [hyswap, hxreflect, hxr]
    ring

/-- Complete reflected aligned contradiction after supplying the two
symmetries and the minimum-height formula of the displayed affine copy. -/
theorem reflected_aligned_impossible {α : Type*}
    (V : Set α) (x y : α → ℝ) (swap reflect : α → α)
    {b c s h k L : ℝ}
    (hswap : ∀ p ∈ V, swap p ∈ V) (hreflect : ∀ p ∈ V, reflect p ∈ V)
    (hxswap : ∀ p, x (swap p) = y p) (hyswap : ∀ p, y (swap p) = x p)
    (hxreflect : ∀ p, x (reflect p) = 1 + b - x p)
    (hupper : ∀ p ∈ V, x p ≤ 1)
    {r a : α} (hr : r ∈ V) (hxr : x r = 1) (ha : a ∈ V)
    (hminimum : ∀ p ∈ V, 1 - (c * h + s * k) ≤ y p)
    (hya : y a = 1 - (c * h + s * k))
    (hunit : c ^ 2 + s ^ 2 = 1) (hs : 0 < s)
    (hz : 0 < c * k - s * h) (hL : L = 1 - b)
    (hendpoint : 0 ≤ h - L * c) : False := by
  obtain ⟨hlower, q, hq, hyq⟩ := reflected_symmetries_minimum V x y swap reflect b
    hswap hreflect hxswap hyswap hxreflect hupper hr hxr
  have hba := hlower a ha
  rw [hya] at hba
  have hqb := hminimum q hq
  rw [hyq] at hqb
  have hd : c * h + s * k = L := by linarith
  exact aligned_reflection_endpoint_impossible hunit hs hz hd hendpoint

end Puzzling139335.N5Facet
