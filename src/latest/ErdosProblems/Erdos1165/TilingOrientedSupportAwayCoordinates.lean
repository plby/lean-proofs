/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingCappedMarginalization

/-!
# A literal support set as the away-coordinate carrier

For a fixed retained tiling word, let `S` be a finite set of represented
domino bases.  Taking the distinguished bases to be the represented bases
outside `S` makes the away-domino subtype exactly `S`.  This is the finite
reindexing needed by the source-correct candidate product: it does not turn
an arbitrary visited base into an insertion coordinate, and therefore keeps
the genuinely path-dependent support condition as an explicit hypothesis.
-/

open scoped BigOperators

namespace Erdos1165.TilingOrientedSupportAwayCoordinates

open TilingSpatialInsertionFiber TilingCappedMarginalization

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Distinguished bases complementary to `S` inside the bases represented
by the retained word. -/
def supportComplementDistinguished {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (S : Finset Point) : Finset Point :=
  tilingExternalDominoBases t x r \ S

theorem away_mem_support_iff {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (S : Finset Point)
    (b : TilingExternalDomino t x r) :
    b.1 ∉ supportComplementDistinguished t x r S ↔ b.1 ∈ S := by
  classical
  rw [supportComplementDistinguished, Finset.mem_sdiff]
  simp only [b.2, true_and, not_not]

/-- If every member of `S` is represented by the retained word, its literal
point subtype is equivalent to the away-domino coordinate carrier. -/
noncomputable def supportAwayEquiv {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (S : Finset Point)
    (hS : S ⊆ tilingExternalDominoBases t x r) :
    TilingAwayDomino t x r (supportComplementDistinguished t x r S) ≃
      {y : Point // y ∈ S} where
  toFun b := ⟨b.1.1, (away_mem_support_iff t x r S b.1).1 b.2⟩
  invFun y := ⟨⟨y.1, hS y.2⟩,
    (away_mem_support_iff t x r S ⟨y.1, hS y.2⟩).2 y.2⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

@[simp] theorem supportAwayEquiv_apply {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (S : Finset Point)
    (hS : S ⊆ tilingExternalDominoBases t x r)
    (b : TilingAwayDomino t x r
      (supportComplementDistinguished t x r S)) :
    (supportAwayEquiv t x r S hS b).1 = b.1.1 := rfl

@[simp] theorem supportAwayEquiv_symm_apply {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (S : Finset Point)
    (hS : S ⊆ tilingExternalDominoBases t x r) (y : {y : Point // y ∈ S}) :
    ((supportAwayEquiv t x r S hS).symm y).1.1 = y.1 := rfl

theorem card_supportAwayDomino {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (S : Finset Point)
    (hS : S ⊆ tilingExternalDominoBases t x r) :
    Fintype.card
        (TilingAwayDomino t x r
          (supportComplementDistinguished t x r S)) =
      S.card := by
  classical
  rw [Fintype.card_congr (supportAwayEquiv t x r S hS)]
  exact Fintype.card_coe S

/-- The away coordinate canonically selected by a literal supported point. -/
noncomputable def supportAwayChosen {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (S : Finset Point)
    (hS : S ⊆ tilingExternalDominoBases t x r) (y : Point) (hy : y ∈ S) :
    TilingAwayDomino t x r (supportComplementDistinguished t x r S) :=
  (supportAwayEquiv t x r S hS).symm ⟨y, hy⟩

@[simp] theorem supportAwayChosen_base {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (S : Finset Point)
    (hS : S ⊆ tilingExternalDominoBases t x r) (y : Point) (hy : y ∈ S) :
    (supportAwayChosen t x r S hS y hy).1.1 = y := rfl

theorem support_subset_away_base_image {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (S : Finset Point)
    (hS : S ⊆ tilingExternalDominoBases t x r) :
    S ⊆ (Finset.univ.image fun b : TilingAwayDomino t x r
      (supportComplementDistinguished t x r S) ↦ b.1.1) := by
  classical
  intro y hy
  rw [Finset.mem_image]
  exact ⟨supportAwayChosen t x r S hS y hy, Finset.mem_univ _,
    supportAwayChosen_base t x r S hS y hy⟩

end

end Erdos1165.TilingOrientedSupportAwayCoordinates
