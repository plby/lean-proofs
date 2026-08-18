import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Erdős problem 186: the elementary convex-geometry interface

Pham--Zakharov call a finite set `X ⊆ ℝ^d` *in `δ`-convex position* when every
`a ∈ X` belongs to a closed half-space containing at most `δ |X|` points of `X`.
This file records that definition without any general-position assumptions and proves the
finite half-space consequences used before the genuinely quantitative density-increment
lemma.

The formulation is slightly more general than the paper: it works in every real normed
space.  A closed half-space is represented by a continuous linear functional `ℓ` and a
threshold `c`, with the convention `c ≤ ℓ x`.
-/

open Set

namespace Erdos186
namespace ConvexGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed affine half-space on the upper side of the level `c` of `ℓ`. -/
def closedHalfspace (ℓ : E →L[ℝ] ℝ) (c : ℝ) : Set E :=
  {x | c ≤ ℓ x}

/-- The open half-space strictly opposite `closedHalfspace ℓ c`. -/
def strictLowerHalfspace (ℓ : E →L[ℝ] ℝ) (c : ℝ) : Set E :=
  {x | ℓ x < c}

@[simp] theorem mem_closedHalfspace {x : E} {ℓ : E →L[ℝ] ℝ} {c : ℝ} :
    x ∈ closedHalfspace ℓ c ↔ c ≤ ℓ x := Iff.rfl

@[simp] theorem mem_strictLowerHalfspace {x : E} {ℓ : E →L[ℝ] ℝ} {c : ℝ} :
    x ∈ strictLowerHalfspace ℓ c ↔ ℓ x < c := Iff.rfl

theorem convex_closedHalfspace (ℓ : E →L[ℝ] ℝ) (c : ℝ) :
    Convex ℝ (closedHalfspace ℓ c) :=
  convex_halfSpace_ge ℓ.isLinear c

theorem convex_strictLowerHalfspace (ℓ : E →L[ℝ] ℝ) (c : ℝ) :
    Convex ℝ (strictLowerHalfspace ℓ c) :=
  convex_halfSpace_lt ℓ.isLinear c

/-- The number of points of `X` in a specified closed half-space. -/
noncomputable def halfspaceCount (X : Finset E) (ℓ : E →L[ℝ] ℝ) (c : ℝ) : ℕ := by
  classical
  exact (X.filter fun x ↦ c ≤ ℓ x).card

theorem halfspaceCount_eq_card_filter (X : Finset E) (ℓ : E →L[ℝ] ℝ) (c : ℝ) :
    halfspaceCount X ℓ c = (X.filter fun x ↦ c ≤ ℓ x).card := by
  classical
  rfl

/--
The exact `δ`-convex-position definition of Pham--Zakharov.

No bound on `δ` is built into the definition.  Their density lemma subsequently assumes
`0 < δ < δ₀`; keeping the definition unbundled makes monotonicity in `δ` literal.
-/
def IsDeltaConvexPosition (δ : ℝ) (X : Finset E) : Prop :=
  ∀ a ∈ X, ∃ (ℓ : E →L[ℝ] ℝ) (c : ℝ),
    c ≤ ℓ a ∧ (halfspaceCount X ℓ c : ℝ) ≤ δ * X.card

/-- A short alias useful in declarations that already mention position. -/
abbrev IsDeltaConvex (δ : ℝ) (X : Finset E) : Prop := IsDeltaConvexPosition δ X

theorem isDeltaConvexPosition_empty (δ : ℝ) :
    IsDeltaConvexPosition δ (∅ : Finset E) := by
  simp [IsDeltaConvexPosition]

/-- Every finite set is `δ`-convex once `δ ≥ 1`; the whole space is a witness. -/
theorem isDeltaConvexPosition_of_one_le {X : Finset E} {δ : ℝ} (hδ : 1 ≤ δ) :
    IsDeltaConvexPosition δ X := by
  classical
  intro a ha
  refine ⟨0, 0, by simp, ?_⟩
  rw [halfspaceCount_eq_card_filter]
  simpa using (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg X.card))

/-- `δ`-convex position is monotone in its permitted density. -/
theorem IsDeltaConvexPosition.mono {X : Finset E} {δ δ' : ℝ}
    (hX : IsDeltaConvexPosition δ X) (hδ : δ ≤ δ') :
    IsDeltaConvexPosition δ' X := by
  intro a ha
  obtain ⟨ℓ, c, hac, hcount⟩ := hX a ha
  exact ⟨ℓ, c, hac, hcount.trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg X.card))⟩

/--
One may always translate the boundary of a witnessing half-space until it passes through
the distinguished point.  This only shrinks the half-space and is the normalization used
implicitly in the box-separation argument.
-/
theorem isDeltaConvexPosition_iff_supporting_through_point {X : Finset E} {δ : ℝ} :
    IsDeltaConvexPosition δ X ↔
      ∀ a ∈ X, ∃ ℓ : E →L[ℝ] ℝ,
        (halfspaceCount X ℓ (ℓ a) : ℝ) ≤ δ * X.card := by
  classical
  constructor
  · intro hX a ha
    obtain ⟨ℓ, c, hac, hcount⟩ := hX a ha
    refine ⟨ℓ, ?_⟩
    have hsub : (X.filter fun x ↦ ℓ a ≤ ℓ x) ⊆ (X.filter fun x ↦ c ≤ ℓ x) := by
      intro x hx
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hx).1,
        hac.trans (Finset.mem_filter.1 hx).2⟩
    have hcard : halfspaceCount X ℓ (ℓ a) ≤ halfspaceCount X ℓ c := by
      simpa only [halfspaceCount_eq_card_filter] using Finset.card_le_card hsub
    have hcard' : (halfspaceCount X ℓ (ℓ a) : ℝ) ≤ halfspaceCount X ℓ c := by
      exact_mod_cast hcard
    exact hcard'.trans hcount
  · intro hX a ha
    obtain ⟨ℓ, hcount⟩ := hX a ha
    exact ⟨ℓ, ℓ a, le_rfl, hcount⟩

/--
A subset whose size is larger than the permitted cap must cross the supporting hyperplane.
This is the exact finite counting step used on every occupied box in the paper.
-/
theorem IsDeltaConvexPosition.exists_support_crossing
    {X Y : Finset E} {δ : ℝ} (hX : IsDeltaConvexPosition δ X)
    {a : E} (ha : a ∈ X) (hYX : Y ⊆ X)
    (hY : δ * X.card < Y.card) :
    ∃ (ℓ : E →L[ℝ] ℝ) (c : ℝ),
      c ≤ ℓ a ∧
      (halfspaceCount X ℓ c : ℝ) ≤ δ * X.card ∧
      ∃ y ∈ Y, ℓ y < c := by
  classical
  obtain ⟨ℓ, c, hac, hcount⟩ := hX a ha
  refine ⟨ℓ, c, hac, hcount, ?_⟩
  by_contra h
  have hall : ∀ y ∈ Y, c ≤ ℓ y := by
    intro y hy
    exact le_of_not_gt (fun hyc ↦ h ⟨y, hy, hyc⟩)
  have hsub : Y ⊆ X.filter fun x ↦ c ≤ ℓ x := by
    intro y hy
    exact Finset.mem_filter.2 ⟨hYX hy, hall y hy⟩
  have hcard : (Y.card : ℝ) ≤ halfspaceCount X ℓ c := by
    exact_mod_cast Finset.card_le_card hsub
  linarith

/-- A convenient separation-only corollary of `exists_support_crossing`. -/
theorem IsDeltaConvexPosition.exists_strictly_lower_mem
    {X Y : Finset E} {δ : ℝ} (hX : IsDeltaConvexPosition δ X)
    {a : E} (ha : a ∈ X) (hYX : Y ⊆ X)
    (hY : δ * X.card < Y.card) :
    ∃ (ℓ : E →L[ℝ] ℝ) (y : E), y ∈ Y ∧ ℓ y < ℓ a := by
  obtain ⟨ℓ, c, hac, _hcount, y, hy, hyl⟩ :=
    hX.exists_support_crossing ha hYX hY
  exact ⟨ℓ, y, hy, hyl.trans_le hac⟩

/-- For `δ < 1`, the supporting functional at every point of a nonempty set is nonzero. -/
theorem IsDeltaConvexPosition.exists_nonzero_supportingFunctional
    {X : Finset E} {δ : ℝ} (hX : IsDeltaConvexPosition δ X)
    (hδ : δ < 1) {a : E} (ha : a ∈ X) :
    ∃ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 ∧
      ∃ y ∈ X, ℓ y < ℓ a := by
  have hcardpos : (0 : ℝ) < X.card := by
    exact_mod_cast (Finset.card_pos.2 ⟨a, ha⟩)
  have hheavy : δ * X.card < X.card := by
    nlinarith
  obtain ⟨ℓ, y, hy, hyl⟩ := hX.exists_strictly_lower_mem ha (Finset.Subset.rfl) hheavy
  refine ⟨ℓ, ?_, y, hy, hyl⟩
  rintro rfl
  simp at hyl

/-- Every nonempty `δ`-convex set necessarily has `δ |X| ≥ 1`. -/
theorem IsDeltaConvexPosition.one_le_mul_card
    {X : Finset E} {δ : ℝ} (hX : IsDeltaConvexPosition δ X)
    (hXne : X.Nonempty) :
    1 ≤ δ * X.card := by
  classical
  obtain ⟨a, ha⟩ := hXne
  obtain ⟨ℓ, c, hac, hcount⟩ := hX a ha
  have hmem : a ∈ X.filter fun x ↦ c ≤ ℓ x := Finset.mem_filter.2 ⟨ha, hac⟩
  have hone : 1 ≤ halfspaceCount X ℓ c := by
    rw [halfspaceCount_eq_card_filter]
    exact Finset.one_le_card.2 ⟨a, hmem⟩
  have hone' : (1 : ℝ) ≤ halfspaceCount X ℓ c := by exact_mod_cast hone
  exact hone'.trans hcount

/--
If the permitted cap has real size strictly below `2`, the witness half-space contains no
point of `X` other than its distinguished point.
-/
theorem IsDeltaConvexPosition.exists_strict_exposing_halfspace
    {X : Finset E} {δ : ℝ} (hX : IsDeltaConvexPosition δ X)
    (hmass : δ * X.card < 2) {a : E} (ha : a ∈ X) :
    ∃ (ℓ : E →L[ℝ] ℝ) (c : ℝ),
      c ≤ ℓ a ∧ ∀ x ∈ X, x ≠ a → ℓ x < c := by
  classical
  obtain ⟨ℓ, c, hac, hcount⟩ := hX a ha
  refine ⟨ℓ, c, hac, ?_⟩
  intro x hx hxa
  by_contra hxc
  have ha' : a ∈ X.filter fun z ↦ c ≤ ℓ z := Finset.mem_filter.2 ⟨ha, hac⟩
  have hx' : x ∈ X.filter fun z ↦ c ≤ ℓ z :=
    Finset.mem_filter.2 ⟨hx, not_lt.1 hxc⟩
  have htwo : 2 ≤ halfspaceCount X ℓ c := by
    rw [halfspaceCount_eq_card_filter]
    have hpair : ({a, x} : Finset E) ⊆ X.filter fun z ↦ c ≤ ℓ z := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ha'
      · exact hx'
    have hp := Finset.card_le_card hpair
    simpa [hxa, hxa.symm] using hp
  have htwo' : (2 : ℝ) ≤ halfspaceCount X ℓ c := by exact_mod_cast htwo
  exact (not_lt_of_ge htwo') (hcount.trans_lt hmass)

/-- The usual finite-set definition of (ordinary) convex position. -/
def IsConvexPosition (X : Finset E) : Prop :=
  ∀ a ∈ X, a ∉ convexHull ℝ ((X : Set E) \ {a})

/-- `IsConvexPosition` agrees with Mathlib's convex-independence predicate. -/
theorem isConvexPosition_iff_convexIndependent {X : Finset E} :
    IsConvexPosition X ↔
      ConvexIndependent ℝ (fun x : (X : Set E) ↦ (x : E)) := by
  simpa [IsConvexPosition] using
    (convexIndependent_set_iff_notMem_convexHull_sdiff (s := (X : Set E))).symm

/-- A `δ`-convex set with cap smaller than two points is in ordinary convex position. -/
theorem IsDeltaConvexPosition.isConvexPosition_of_mul_card_lt_two
    {X : Finset E} {δ : ℝ} (hX : IsDeltaConvexPosition δ X)
    (hmass : δ * X.card < 2) : IsConvexPosition X := by
  classical
  intro a ha
  obtain ⟨ℓ, c, hac, hstrict⟩ := hX.exists_strict_exposing_halfspace hmass ha
  have herase : ((X : Set E) \ {a}) ⊆ strictLowerHalfspace ℓ c := by
    intro x hx
    simp only [mem_sdiff, Finset.mem_coe, mem_singleton_iff] at hx
    exact hstrict x hx.1 hx.2
  have hhull : convexHull ℝ ((X : Set E) \ {a}) ⊆ strictLowerHalfspace ℓ c :=
    convexHull_min herase (convex_strictLowerHalfspace ℓ c)
  intro hahull
  exact (not_lt_of_ge hac) (hhull hahull)

/--
Conversely, Hahn--Banach strictly exposes every point of a finite set in ordinary convex
position.  Thus such a set is `δ`-convex as soon as the permitted cap is at least one point.
-/
theorem IsConvexPosition.isDeltaConvexPosition
    [LocallyConvexSpace ℝ E]
    {X : Finset E} (hX : IsConvexPosition X) {δ : ℝ}
    (hmass : 1 ≤ δ * X.card) : IsDeltaConvexPosition δ X := by
  classical
  intro a ha
  let S : Set E := (X : Set E) \ {a}
  have hSfinite : S.Finite := X.finite_toSet.sdiff
  have hSconvex : Convex ℝ (convexHull ℝ S) := convex_convexHull ℝ S
  have hSclosed : IsClosed (convexHull ℝ S) := hSfinite.isClosed_convexHull ℝ
  have haS : a ∉ convexHull ℝ S := hX a ha
  obtain ⟨ℓ, u, hbelow, hua⟩ :=
    geometric_hahn_banach_closed_point hSconvex hSclosed haS
  refine ⟨ℓ, ℓ a, le_rfl, ?_⟩
  have hfilter : X.filter (fun x ↦ ℓ a ≤ ℓ x) = {a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxX, hax⟩
      by_contra hxa
      have hxS : x ∈ S := ⟨hxX, by simpa using hxa⟩
      have hxHull : x ∈ convexHull ℝ S := subset_convexHull ℝ S hxS
      have hxu : ℓ x < u := hbelow x hxHull
      linarith
    · rintro rfl
      exact ⟨ha, le_rfl⟩
  rw [halfspaceCount_eq_card_filter, hfilter]
  simpa using hmass

/--
In the range in which a cap may contain one point but not two, `δ`-convex position is
exactly ordinary convex position.
-/
theorem isDeltaConvexPosition_iff_isConvexPosition_of_cap_range
    [LocallyConvexSpace ℝ E]
    {X : Finset E} {δ : ℝ} (hone : 1 ≤ δ * X.card) (htwo : δ * X.card < 2) :
    IsDeltaConvexPosition δ X ↔ IsConvexPosition X := by
  exact ⟨fun h ↦ h.isConvexPosition_of_mul_card_lt_two htwo,
    fun h ↦ h.isDeltaConvexPosition hone⟩

end ConvexGeometry
end Erdos186
