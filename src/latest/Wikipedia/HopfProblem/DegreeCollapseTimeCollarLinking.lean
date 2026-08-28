import Wikipedia.HopfProblem.DegreeCollapseTimeCollarSplitting
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenLinkingVanishing
import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenLinkingSymmetry

/-!
# Nondegenerate linking on the actual half of a collared closed seven-manifold

The half pairing is the restriction of the original closed integral cap
and torsion pairing. The actual interior homotopy equivalence and open
duality give cross-half vanishing. The original half-inclusion sum then
proves nondegeneracy. No reflected-double presentation is required.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open SingularMayerVietoris PeriodTorusHigherHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 7)]
  {M B : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]
  [TopologicalSpace B] {t : M → ℝ} (C : TimeCollar t B)

def halfLinking (_C : TimeCollar t B) :
    SingularHomology (NonnegativeHalf t) 3 →ₗ[ℤ]
      (SingularHomology (NonnegativeHalf t) 3 →ₗ[ℤ] RationalResidue.Value) := by
  let H := singularHomologyMap (halfInclusion t) 3
  let L := IntegralSevenLinking.linking (E := E) M
  let F : SingularHomology (NonnegativeHalf t) 3 →+
      (SingularHomology (NonnegativeHalf t) 3 →ₗ[ℤ] RationalResidue.Value) :=
    { toFun := fun x ↦ (L (H x)).comp H
      map_zero' := by
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, map_zero, LinearMap.zero_apply]
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply] }
  exact ConstantSheafSingularComparison.addHomToIntLinearMap F

theorem halfLinking_apply (x y : SingularHomology (NonnegativeHalf t) 3) :
    C.halfLinking (E := E) x y = IntegralSevenLinking.linking (E := E) M
      (singularHomologyMap (halfInclusion t) 3 x) (singularHomologyMap (halfInclusion t) 3 y) := rfl

theorem halfLinking_symmetry (x y : SingularHomology (NonnegativeHalf t) 3) :
    C.halfLinking (E := E) x y = C.halfLinking (E := E) y x :=
  IntegralSevenLinking.linking_symmetry (E := E) M
    (singularHomologyMap (halfInclusion t) 3 x) (singularHomologyMap (halfInclusion t) 3 y)

variable [Subsingleton (SingularHomology B 3)] [Subsingleton (SingularHomology B 4)]

include C in
theorem linking_cross_half (x : SingularHomology (NonnegativeHalf t) 3)
    (y : SingularHomology (NonnegativeHalf (fun p ↦ -t p)) 3) :
    IntegralSevenLinking.linking (E := E) M
      (singularHomologyMap (halfInclusion t) 3 x)
      (singularHomologyMap (halfInclusion (fun p ↦ -t p)) 3 y) = 0 := by
  let : Finite (SingularHomology (NonnegativeHalf (fun p ↦ -t p)) 3) :=
    C.negative_homology_finite 3
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := E) M
  let : Subsingleton (SingularHomology (NonnegativeHalf (fun p ↦ -t p)) 4) :=
    C.negative_homology_subsingleton 4
  obtain ⟨a, rfl⟩ := (C.interiorToHalf_homology_bijective 3).2 x
  have hi := LinearMap.congr_fun (singularHomologyMap_comp C.interiorToHalf (halfInclusion t) 3) a
  rw [C.interiorToHalf_inclusion, LinearMap.comp_apply] at hi
  rw [← hi]
  apply IntegralSevenLinking.linking_open_away_zero (E := E) M C.positiveInterior
    (halfInclusion (fun p ↦ -t p)) _ a y
  intro p hp
  change 0 < t p.val at hp
  have hn : 0 ≤ -t p.val := p.property
  linarith

variable [Subsingleton (SingularHomology B 2)]

theorem halfLinking_left_nondegenerate (x : SingularHomology (NonnegativeHalf t) 3)
    (hx : ∀ y, C.halfLinking (E := E) x y = 0) : x = 0 := by
  apply C.halfInclusion_homology_injective 3
  rw [map_zero]
  apply IntegralSevenLinking.linking_left_nondegenerate (E := E) M
  intro z
  obtain ⟨⟨u, v⟩, hz⟩ := (C.halvesHomologySum_bijective 2).2 z
  rw [← hz, halvesHomologySum_apply, map_add, C.linking_cross_half, add_zero]
  exact hx u

theorem halfLinking_right_nondegenerate (y : SingularHomology (NonnegativeHalf t) 3)
    (hy : ∀ x, C.halfLinking (E := E) x y = 0) : y = 0 := by
  apply C.halfLinking_left_nondegenerate (E := E)
  intro x
  rw [C.halfLinking_symmetry]
  exact hy x

theorem half_add_self_eq_zero_of_zero_diagonal
    (hd : ∀ x : SingularHomology (NonnegativeHalf t) 3, C.halfLinking (E := E) x x = 0)
    (a : SingularHomology (NonnegativeHalf t) 3) : a + a = 0 := by
  apply C.halfLinking_left_nondegenerate (E := E)
  intro z
  rw [map_add, LinearMap.add_apply]
  have he := hd (a + z)
  simp only [map_add, LinearMap.add_apply, hd a, hd z, zero_add, add_zero] at he
  rw [C.halfLinking_symmetry (E := E) z a] at he
  exact he

theorem halfLinking_diagonal_dichotomy :
    (∃ x : SingularHomology (NonnegativeHalf t) 3, C.halfLinking (E := E) x x ≠ 0) ∨
      ∀ x : SingularHomology (NonnegativeHalf t) 3, x + x = 0 := by
  classical
  by_cases hd : ∀ x : SingularHomology (NonnegativeHalf t) 3, C.halfLinking (E := E) x x = 0
  · exact Or.inr (C.half_add_self_eq_zero_of_zero_diagonal (E := E) hd)
  · exact Or.inl (not_forall.mp hd)

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
