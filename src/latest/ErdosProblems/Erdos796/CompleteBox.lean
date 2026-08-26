import ErdosProblems.Erdos796.KST

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The tripartite complete-box estimate

This file formalizes the finite combinatorial core of the manuscript's
unbalanced `K^{(3)}_{2,2,2}` estimate.  A tripartite hypergraph is represented
by a finite set of triples.  The main ingredients are:

* every common link of two vertices in one part is `C₄`-free;
* an exact double count identifies the sum of the common-link sizes with the
  sum of the pair-codegrees;
* the bipartite Kővári--Sós--Turán inequality from `Erdos796.KST` bounds that
  sum.
-/

namespace Erdos796

namespace Tripartite

open scoped BigOperators

variable {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- A finite tripartite `3`-uniform hypergraph contains no nondegenerate
`2 × 2 × 2` box. -/
def K222Free (H : Finset (X × Y × Z)) : Prop :=
  ∀ ⦃x₁ x₂ : X⦄ ⦃y₁ y₂ : Y⦄ ⦃z₁ z₂ : Z⦄,
    (x₁, y₁, z₁) ∈ H →
    (x₁, y₁, z₂) ∈ H →
    (x₁, y₂, z₁) ∈ H →
    (x₁, y₂, z₂) ∈ H →
    (x₂, y₁, z₁) ∈ H →
    (x₂, y₁, z₂) ∈ H →
    (x₂, y₂, z₁) ∈ H →
    (x₂, y₂, z₂) ∈ H →
    x₁ = x₂ ∨ y₁ = y₂ ∨ z₁ = z₂

/-- The number of neighbours in `L` of a pair `(y,z)`. -/
def codegree (H : Finset (X × Y × Z)) (L : Finset X) (y : Y) (z : Z) : ℕ :=
  (L.filter fun x => (x, y, z) ∈ H).card

/-- The common link in `Y × Z` of all vertices of `s`. -/
def commonLink (H : Finset (X × Y × Z)) (M : Finset Y) (R : Finset Z)
    (s : Finset X) : Finset (Y × Z) :=
  (M ×ˢ R).filter fun yz => ∀ x ∈ s, (x, yz.1, yz.2) ∈ H

/-- The number of displayed hyperedges, counted through their `(y,z)`
codegrees. -/
def edgeCount (H : Finset (X × Y × Z)) (L : Finset X)
    (M : Finset Y) (R : Finset Z) : ℕ :=
  ∑ y ∈ M, ∑ z ∈ R, codegree H L y z

/-- The pair-codegree mass appearing in the second moment identity. -/
def pairCodegreeMass (H : Finset (X × Y × Z)) (L : Finset X)
    (M : Finset Y) (R : Finset Z) : ℕ :=
  ∑ y ∈ M, ∑ z ∈ R, Nat.choose (codegree H L y z) 2

@[simp]
theorem mem_commonLink {H : Finset (X × Y × Z)} {M : Finset Y}
    {R : Finset Z} {s : Finset X} {y : Y} {z : Z} :
    (y, z) ∈ commonLink H M R s ↔
      y ∈ M ∧ z ∈ R ∧ ∀ x ∈ s, (x, y, z) ∈ H := by
  simp [commonLink, and_assoc]

/-- The common link of two distinct first-part vertices is `C₄`-free. -/
theorem commonLink_c4Free {H : Finset (X × Y × Z)} (hH : K222Free H)
    (M : Finset Y) (R : Finset Z) {s : Finset X} (hs : s.card = 2) :
    Bipartite.C4Free (commonLink H M R s) := by
  rcases Finset.card_eq_two.mp hs with ⟨x₁, x₂, hxx, rfl⟩
  intro y₁ y₂ z₁ z₂ hyz₁₁ hyz₁₂ hyz₂₁ hyz₂₂
  simp only [mem_commonLink] at hyz₁₁ hyz₁₂ hyz₂₁ hyz₂₂
  have hbox := hH
    (hyz₁₁.2.2 x₁ (by simp)) (hyz₁₂.2.2 x₁ (by simp))
    (hyz₂₁.2.2 x₁ (by simp)) (hyz₂₂.2.2 x₁ (by simp))
    (hyz₁₁.2.2 x₂ (by simp)) (hyz₁₂.2.2 x₂ (by simp))
    (hyz₂₁.2.2 x₂ (by simp)) (hyz₂₂.2.2 x₂ (by simp))
  exact (hbox.resolve_left hxx).imp id id

/-- Since a common link is already supported on `M × R`, its bipartite edge
count is its cardinality. -/
theorem commonLink_edgeCount_eq_card (H : Finset (X × Y × Z))
    (M : Finset Y) (R : Finset Z) (s : Finset X) :
    Bipartite.edgeCount (commonLink H M R s) M R =
      (commonLink H M R s).card := by
  classical
  have hmap : Set.MapsTo Prod.snd
      (commonLink H M R s : Set (Y × Z)) (R : Set Z) := by
    intro yz hyz
    exact (mem_commonLink.mp hyz).2.1
  have hfiber (z : Z) (hz : z ∈ R) :
      ((commonLink H M R s).filter fun yz => yz.2 = z).card =
        Bipartite.leftDegree (commonLink H M R s) M z := by
    rw [Bipartite.leftDegree]
    refine Finset.card_bij (fun yz _ => yz.1) ?_ ?_ ?_
    · intro yz hyz
      have hyzLink := (Finset.mem_filter.mp hyz).1
      have hyzEq := (Finset.mem_filter.mp hyz).2
      have hyzMem := mem_commonLink.mp hyzLink
      exact Finset.mem_filter.mpr
        ⟨hyzMem.1, by simpa [← hyzEq] using! hyzLink⟩
    · intro yz₁ h₁ yz₂ h₂ hfst
      apply Prod.ext hfst
      exact (Finset.mem_filter.mp h₁).2.trans
        (Finset.mem_filter.mp h₂).2.symm
    · intro y hy
      have hyM := (Finset.mem_filter.mp hy).1
      have hyzLink := (Finset.mem_filter.mp hy).2
      exact ⟨(y, z), Finset.mem_filter.mpr ⟨hyzLink, rfl⟩, rfl⟩
  calc
    Bipartite.edgeCount (commonLink H M R s) M R =
        ∑ z ∈ R,
          ((commonLink H M R s).filter fun yz => yz.2 = z).card := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (hfiber z hz).symm
    _ = (commonLink H M R s).card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise hmap

/-- Exact double count: choosing two first-part neighbours of `(y,z)` is
the same as choosing a two-element first-part set and then an edge in its
common link. -/
theorem pairCodegreeMass_eq_sum_commonLink_card
    (H : Finset (X × Y × Z)) (L : Finset X)
    (M : Finset Y) (R : Finset Z) :
    pairCodegreeMass H L M R =
      ∑ s ∈ L.powersetCard 2, (commonLink H M R s).card := by
  classical
  let rel : Finset X → (Y × Z) → Prop :=
    fun s yz => ∀ x ∈ s, (x, yz.1, yz.2) ∈ H
  have habove (s : Finset X) :
      (M ×ˢ R).bipartiteAbove rel s = commonLink H M R s := by
    ext yz
    simp [rel, commonLink]
  have hbelow (yz : Y × Z) :
      (L.powersetCard 2).bipartiteBelow rel yz =
        (L.filter fun x => (x, yz.1, yz.2) ∈ H).powersetCard 2 := by
    ext s
    simp only [Finset.mem_bipartiteBelow, Finset.mem_powersetCard, rel]
    constructor
    · rintro ⟨⟨hsL, hscard⟩, hsH⟩
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hsL hx, hsH x hx⟩, hscard⟩
    · rintro ⟨hs, hscard⟩
      exact ⟨⟨fun x hx => (Finset.mem_filter.mp (hs hx)).1, hscard⟩,
        fun x hx => (Finset.mem_filter.mp (hs hx)).2⟩
  calc
    pairCodegreeMass H L M R =
        ∑ yz ∈ M ×ˢ R, Nat.choose (codegree H L yz.1 yz.2) 2 := by
          simp [pairCodegreeMass, Finset.sum_product]
    _ = ∑ yz ∈ M ×ˢ R,
        ((L.powersetCard 2).bipartiteBelow rel yz).card := by
          apply Finset.sum_congr rfl
          intro yz hyz
          rw [hbelow, Finset.card_powersetCard]
          rfl
    _ = ∑ s ∈ L.powersetCard 2,
        ((M ×ˢ R).bipartiteAbove rel s).card := by
          exact
            (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
              (r := rel) (s := L.powersetCard 2) (t := M ×ˢ R)).symm
    _ = ∑ s ∈ L.powersetCard 2, (commonLink H M R s).card := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [habove]

/-- Iterated `C₄` estimate for the sum of pair-codegrees.  This is the exact
finite form of the first inequality in the complete-box argument. -/
theorem pairCodegreeMass_le_kst {H : Finset (X × Y × Z)}
    (hH : K222Free H) (L : Finset X) (M : Finset Y) (R : Finset Z) :
    (pairCodegreeMass H L M R : ℝ) ≤
      (Nat.choose L.card 2 : ℝ) *
        ((R.card : ℝ) +
          Real.sqrt (2 * (R.card : ℝ) * (Nat.choose M.card 2 : ℝ))) := by
  rw [pairCodegreeMass_eq_sum_commonLink_card]
  simp only [Nat.cast_sum]
  calc
    (∑ s ∈ L.powersetCard 2, ((commonLink H M R s).card : ℝ)) ≤
        ∑ _s ∈ L.powersetCard 2,
          ((R.card : ℝ) +
            Real.sqrt (2 * (R.card : ℝ) *
              (Nat.choose M.card 2 : ℝ))) := by
          apply Finset.sum_le_sum
          intro s hs
          have hcard := (Finset.mem_powersetCard.mp hs).2
          have hk := Bipartite.edgeCount_le_card_add_sqrt
            (commonLink_c4Free hH M R hcard) M R
          rw [commonLink_edgeCount_eq_card] at hk
          exact hk
    _ = (Nat.choose L.card 2 : ℝ) *
        ((R.card : ℝ) +
          Real.sqrt (2 * (R.card : ℝ) *
            (Nat.choose M.card 2 : ℝ))) := by
          rw [Finset.sum_const, Finset.card_powersetCard]
          ring

/-- The displayed edge count is a single sum over the product `M × R`. -/
theorem edgeCount_eq_sum_product (H : Finset (X × Y × Z))
    (L : Finset X) (M : Finset Y) (R : Finset Z) :
    edgeCount H L M R =
      ∑ yz ∈ M ×ˢ R, codegree H L yz.1 yz.2 := by
  simp [edgeCount, Finset.sum_product]

/-- Exact second-moment identity for tripartite codegrees. -/
theorem sum_sq_codegree_eq
    (H : Finset (X × Y × Z)) (L : Finset X)
    (M : Finset Y) (R : Finset Z) :
    (∑ yz ∈ M ×ˢ R, (codegree H L yz.1 yz.2 : ℝ) ^ 2) =
      (edgeCount H L M R : ℝ) +
        2 * (pairCodegreeMass H L M R : ℝ) := by
  have hterm (d : ℕ) :
      (d : ℝ) ^ 2 = (d : ℝ) + 2 * (Nat.choose d 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    ring
  have hpairs :
      (∑ yz ∈ M ×ˢ R,
        (Nat.choose (codegree H L yz.1 yz.2) 2 : ℝ)) =
        (pairCodegreeMass H L M R : ℝ) := by
    rw [pairCodegreeMass]
    push_cast
    rw [Finset.sum_product]
  calc
    (∑ yz ∈ M ×ˢ R, (codegree H L yz.1 yz.2 : ℝ) ^ 2) =
        ∑ yz ∈ M ×ˢ R,
          ((codegree H L yz.1 yz.2 : ℝ) +
            2 * (Nat.choose (codegree H L yz.1 yz.2) 2 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro yz hyz
          exact hterm (codegree H L yz.1 yz.2)
    _ = (edgeCount H L M R : ℝ) +
        2 * (pairCodegreeMass H L M R : ℝ) := by
          simp only [Finset.sum_add_distrib]
          rw [edgeCount_eq_sum_product]
          simp only [Nat.cast_sum]
          rw [← Finset.mul_sum]
          rw [hpairs]

end Tripartite

end Erdos796
