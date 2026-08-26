import ErdosProblems.Erdos593.TripleSystem.TriangleHostRamsey

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Homogeneous pair-colouring interfaces

This module isolates the finite interface between a homogeneous set for a
pair-colouring and the existing `PairRamseyTriangle` interface. It proves no
partition theorem and introduces no axioms.
-/

namespace Erdos593

universe u v

namespace TripleSystem
namespace TriangleHost

/-- All pair-faces contained in `H` have the same `c`-colour. -/
def PairHomogeneous {kappa : Type u} (c : Pair kappa → ℕ) (H : Set kappa) : Prop :=
  ∀ p q : Pair kappa, (p.1 : Set kappa) ⊆ H → (q.1 : Set kappa) ⊆ H → c p = c q

/-- An infinite homogeneous vertex set yields the exact triangle-host Ramsey
interface by extracting a three-element finite subset. -/
theorem pairRamseyTriangle_of_infinite_pair_homogeneous
    {kappa : Type u} [DecidableEq kappa]
    (h : ∀ c : Pair kappa → ℕ, ∃ H : Set kappa, H.Infinite ∧ PairHomogeneous c H) :
    PairRamseyTriangle kappa := by
  intro c
  obtain ⟨H, hHinf, hHmono⟩ := h c
  obtain ⟨t, htH, htcard⟩ := hHinf.exists_subset_card_eq 3
  refine ⟨⟨t, htcard⟩, ?_⟩
  intro p q hp hq
  have hp' : (p.1 : Set kappa) ⊆ t := Finset.coe_subset.2 hp
  have hq' : (q.1 : Set kappa) ⊆ t := Finset.coe_subset.2 hq
  exact hHmono p q (hp'.trans htH) (hq'.trans htH)

/-- Every `C`-colouring of two-element subsets admits three distinct points
whose contained pair-faces have a common colour. -/
def HomogeneousThreePointPairColoring
    (kappa : Type u) [DecidableEq kappa] (C : Type v) : Prop :=
  ∀ c : Pair kappa → C, ∃ a b d : kappa,
    a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      ∀ p q : Pair kappa,
        p.1 ⊆ ({a, b, d} : Finset kappa) →
        q.1 ⊆ ({a, b, d} : Finset kappa) →
        c p = c q

/-- The homogeneous-three-point interface, specialized to natural colours,
implies the existing triangle-host Ramsey interface. -/
theorem pairRamseyTriangle_of_homogeneousThreePoint
    (kappa : Type u) [DecidableEq kappa]
    (h : HomogeneousThreePointPairColoring kappa ℕ) :
    PairRamseyTriangle kappa := by
  intro c
  obtain ⟨a, b, d, hab, had, hbd, hc⟩ := h c
  refine ⟨⟨{a, b, d}, by simp [hab, had, hbd]⟩, ?_⟩
  intro p q hp hq
  exact hc p q hp hq

/-- The two finite forms of the natural-colour interface are equivalent. -/
theorem homogeneousThreePoint_of_pairRamseyTriangle
    (kappa : Type u) [DecidableEq kappa]
    (h : PairRamseyTriangle kappa) :
    HomogeneousThreePointPairColoring kappa ℕ := by
  intro c
  obtain ⟨t, ht⟩ := h c
  rcases Finset.card_eq_three.mp t.2 with ⟨a, b, d, hab, had, hbd, htd⟩
  refine ⟨a, b, d, hab, had, hbd, ?_⟩
  intro p q hp hq
  apply ht p q
  · rw [htd]
    exact hp
  · rw [htd]
    exact hq

theorem homogeneousThreePointPairColoring_iff_pairRamseyTriangle
    (kappa : Type u) [DecidableEq kappa] :
    HomogeneousThreePointPairColoring kappa ℕ ↔ PairRamseyTriangle kappa := by
  constructor
  · exact pairRamseyTriangle_of_homogeneousThreePoint kappa
  · exact homogeneousThreePoint_of_pairRamseyTriangle kappa

end TriangleHost
end TripleSystem
end Erdos593
