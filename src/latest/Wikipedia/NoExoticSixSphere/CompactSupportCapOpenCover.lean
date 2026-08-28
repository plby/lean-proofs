import Wikipedia.NoExoticSixSphere.CompactSupportCapMayerVietoris
import Wikipedia.NoExoticSixSphere.CompactSupportMayerVietorisZero
import Mathlib.Algebra.FiveLemma

/-!
# Gluing bijectivity of the actual compact-support cap map

The five lemma applies to the original Mayer--Vietoris sequences and
the proved cap comparison squares. The homological degree-zero endpoint
uses the original surjection and vanishing of the next overlap
cohomology group. This proves the two-open-set gluing step; it does not
assume or assert the still-required arbitrary-cover duality theorem.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportCapMayerVietoris

open CompactSupportCapMap CompactSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U V : Set M) [ChartedSpace E U] [ChartedSpace E V]
  [ChartedSpace E (U ∩ V : Set M)]
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover

/-- The actual cap is bijective in positive homology degree if it is so on all three pieces. -/
theorem bijective_of_cover_positive (p q : ℕ) (h : p + q + 1 = n + 3)
    (hDU : ∀ a b (hab : a + b = n + 3),
      Function.Bijective (dualityMap (E := E) n U a b hab))
    (hDV : ∀ a b (hab : a + b = n + 3),
      Function.Bijective (dualityMap (E := E) n V a b hab))
    (hDI : ∀ a b (hab : a + b = n + 3),
      Function.Bijective (dualityMap (E := E) n (U ∩ V : Set M) a b hab)) :
    Function.Bijective (dualityMap (E := E) n M p (q + 1)
      ((Nat.add_assoc p q 1).symm.trans h)) := by
  let h₁ : p + (q + 1) = n + 3 := (Nat.add_assoc p q 1).symm.trans h
  let h₂ : (p + 1) + q = n + 3 := (Nat.add_right_comm p 1 q).trans h
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (CompactSupportMayerVietoris.firstMap U V hU hV p)
    (CompactSupportMayerVietoris.differenceMap U V hU hV p)
    (CompactSupportMayerVietoris.connecting U V hU hV p hcover)
    (CompactSupportMayerVietoris.firstMap U V hU hV (p + 1))
    (ModTwoMayerVietoris.firstMap U V (q + 1))
    (ModTwoMayerVietoris.secondMap U V (q + 1))
    (ModTwoMayerVietoris.connecting U V hU hV hcover q)
    (ModTwoMayerVietoris.firstMap U V q)
    (dualityMap (E := E) n (U ∩ V : Set M) p (q + 1) h₁)
    (productMap (E := E) n U V p (q + 1) h₁)
    (dualityMap (E := E) n M p (q + 1) h₁)
    (dualityMap (E := E) n (U ∩ V : Set M) (p + 1) q h₂)
    (productMap (E := E) n U V (p + 1) q h₂)
    (first_square (E := E) n U V hU hV p (q + 1) h₁)
    (second_square (E := E) n U V hU hV p (q + 1) h₁)
    (connecting_square (E := E) n U V hU hV hcover p q h)
    (first_square (E := E) n U V hU hV (p + 1) q h₂)
    (LinearMap.exact_iff.mpr (CompactSupportMayerVietoris.exact_middle
      U V hU hV hcover p).symm)
    (LinearMap.exact_iff.mpr (CompactSupportMayerVietoris.exact_right
      U V hU hV hcover p).symm)
    (LinearMap.exact_iff.mpr (CompactSupportMayerVietoris.exact_left
      U V hU hV hcover p).symm)
    (LinearMap.exact_iff.mpr (ModTwoMayerVietoris.exact_middle
      U V hU hV hcover (q + 1)).symm)
    (LinearMap.exact_iff.mpr (ModTwoMayerVietoris.exact_right U V hU hV hcover q).symm)
    (LinearMap.exact_iff.mpr (ModTwoMayerVietoris.exact_left U V hU hV hcover q).symm)
    (hDI p (q + 1) h₁).2
    (productMap_bijective (E := E) n U V p (q + 1) h₁ (hDU _ _ _) (hDV _ _ _))
    (hDI (p + 1) q h₂)
    (productMap_bijective (E := E) n U V (p + 1) q h₂ (hDU _ _ _) (hDV _ _ _)).1

/-- The actual degree-zero homological endpoint glues by the original right-exact sequences. -/
theorem bijective_of_cover_zero (p : ℕ) (h : p + 0 = n + 3)
    (hDU : Function.Bijective (dualityMap (E := E) n U p 0 h))
    (hDV : Function.Bijective (dualityMap (E := E) n V p 0 h))
    (hDI : Function.Surjective (dualityMap (E := E) n (U ∩ V : Set M) p 0 h))
    [Subsingleton (Cohomology (U ∩ V : Set M) (p + 1))] :
    Function.Bijective (dualityMap (E := E) n M p 0 h) := by
  have hc : Function.Surjective (CompactSupportMayerVietoris.differenceMap U V hU hV p) := by
    intro a
    exact (CompactSupportMayerVietoris.exact_right U V hU hV hcover p).ge
      (show CompactSupportMayerVietoris.connecting U V hU hV p hcover a = 0 from
        Subsingleton.elim _ _)
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (CompactSupportMayerVietoris.firstMap U V hU hV p)
    (CompactSupportMayerVietoris.differenceMap U V hU hV p)
    (ModTwoMayerVietoris.firstMap U V 0) (ModTwoMayerVietoris.secondMap U V 0)
    (dualityMap (E := E) n (U ∩ V : Set M) p 0 h)
    (productMap (E := E) n U V p 0 h) (dualityMap (E := E) n M p 0 h)
    (first_square (E := E) n U V hU hV p 0 h)
    (second_square (E := E) n U V hU hV p 0 h)
    (LinearMap.exact_iff.mpr (CompactSupportMayerVietoris.exact_middle
      U V hU hV hcover p).symm)
    (LinearMap.exact_iff.mpr (ModTwoMayerVietoris.exact_middle U V hU hV hcover 0).symm)
    hDI (productMap_bijective (E := E) n U V p 0 h hDU hDV) hc
    (ModTwoMayerVietoris.secondMap_zero_surjective U V hU hV hcover)

/-- The two-open-set gluing step for the original cap in every complementary degree. -/
theorem bijective_of_cover
    (hDU : ∀ a b (hab : a + b = n + 3),
      Function.Bijective (dualityMap (E := E) n U a b hab))
    (hDV : ∀ a b (hab : a + b = n + 3),
      Function.Bijective (dualityMap (E := E) n V a b hab))
    (hDI : ∀ a b (hab : a + b = n + 3),
      Function.Bijective (dualityMap (E := E) n (U ∩ V : Set M) a b hab))
    (hI : Subsingleton (Cohomology (U ∩ V : Set M) (n + 4)))
    (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (dualityMap (E := E) n M p q h) := by
  cases q with
  | zero =>
    have hp : p + 1 = n + 4 := by omega
    let : Subsingleton (Cohomology (U ∩ V : Set M) (p + 1)) := hp ▸ hI
    exact bijective_of_cover_zero (E := E) n U V hU hV hcover p h
      (hDU p 0 h) (hDV p 0 h) (hDI p 0 h).2
  | succ q =>
    exact bijective_of_cover_positive (E := E) n U V hU hV hcover p q
      ((Nat.add_assoc p q 1).trans h) hDU hDV hDI

end NoExoticSixSphere.CompactSupportCapMayerVietoris
