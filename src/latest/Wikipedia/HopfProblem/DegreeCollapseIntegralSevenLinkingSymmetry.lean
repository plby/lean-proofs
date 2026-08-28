import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenCapOriginal
import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenLinking

/-!
# Symmetry of the original closed seven-manifold torsion pairing

Both arguments use the original cap map and the same constructed
fundamental cycle. The integral cup-one identity therefore proves
symmetry of the already defined pairing, not a replacement pairing.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking

open SingularMayerVietoris

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 7)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)] [Finite (SingularHomology M 3)]

theorem linking_symmetry (x y : SingularHomology M 3) :
    linking (E := E) M x y = linking (E := E) M y x := by
  let : Subsingleton (SingularHomology M 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := E) M
  obtain ⟨a, rfl⟩ := (IntegralCompactSupportCap.absoluteDualityMap_bijective
    (E := E) 4 M 4 3 rfl).2 x
  obtain ⟨b, rfl⟩ := (IntegralCompactSupportCap.absoluteDualityMap_bijective
    (E := E) 4 M 4 3 rfl).2 y
  rw [linking_original_cap, linking_original_cap]
  obtain ⟨Ω, hΩ⟩ := IntegralManifoldFundamentalClass.exists_fundamental_cycle (E := E) 4 M
  obtain ⟨α, hα, hcapα⟩ := exists_absoluteDualityMap_cycle (E := E) M a Ω hΩ
  obtain ⟨β, hβ, hcapβ⟩ := exists_absoluteDualityMap_cycle (E := E) M b Ω hΩ
  rw [hcapβ, hcapα, ← hα, ← hβ]
  exact torsionEvaluation_capSevenCycle_symmetry α β Ω

theorem linking_right_nondegenerate (b : SingularHomology M 3)
    (hb : ∀ a, linking (E := E) M a b = 0) : b = 0 := by
  apply linking_left_nondegenerate (E := E) M b
  intro a
  rw [linking_symmetry]
  exact hb a

theorem add_self_eq_zero_of_zero_diagonal
    (hd : ∀ a : SingularHomology M 3, linking (E := E) M a a = 0)
    (a : SingularHomology M 3) : a + a = 0 := by
  apply linking_left_nondegenerate (E := E) M (a + a)
  intro b
  rw [map_add, LinearMap.add_apply]
  have he := hd (a + b)
  simp only [map_add, LinearMap.add_apply, hd a, hd b, zero_add, add_zero] at he
  rw [linking_symmetry (E := E) M b a] at he
  exact he

theorem linking_diagonal_dichotomy :
    (∃ a : SingularHomology M 3, linking (E := E) M a a ≠ 0) ∨
      ∀ a : SingularHomology M 3, a + a = 0 := by
  classical
  by_cases h : ∀ a : SingularHomology M 3, linking (E := E) M a a = 0
  · exact Or.inr (add_self_eq_zero_of_zero_diagonal (E := E) M h)
  · exact Or.inl (not_forall.mp h)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking
