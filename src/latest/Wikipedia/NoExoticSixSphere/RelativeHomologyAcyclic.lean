import Wikipedia.NoExoticSixSphere.RelativeSingularHomology

/-!
# Relative acyclicity from the actual inclusion maps

The long exact sequence of the actual singular-chain pair shows that
surjectivity in degree `d + 1` and injectivity in degree `d` annihilate
relative homology in degree `d + 1`. Degree zero uses the terminal
surjection in that same sequence. No homotopy conclusion is asserted.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem inclusion_surjective_of_relative_subsingleton (d : ℕ)
    [Subsingleton (Homology U d)] :
    Function.Surjective (singularHomologyMap (subtypeInclusion U) d) := by
  intro a
  have ha : a ∈ LinearMap.ker (toRelative U d) := Subsingleton.elim _ _
  rw [← exact_at_ambient] at ha
  exact ha

theorem inclusion_injective_of_relative_subsingleton (d : ℕ)
    [Subsingleton (Homology U (d + 1))] :
    Function.Injective (singularHomologyMap (subtypeInclusion U) d) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← exact_at_subspace]
  apply LinearMap.range_eq_bot.mpr
  ext a
  exact (congrArg (connecting U d) (Subsingleton.elim a 0)).trans (map_zero _)

theorem toRelative_eq_zero_of_surjective (d : ℕ)
    (h : Function.Surjective (singularHomologyMap (subtypeInclusion U) d))
    (a : SingularHomology X d) : toRelative U d a = 0 := by
  have ha : a ∈ LinearMap.range (singularHomologyMap (subtypeInclusion U) d) := h a
  exact (exact_at_ambient U d).le ha

theorem connecting_eq_zero_of_injective (d : ℕ)
    (h : Function.Injective (singularHomologyMap (subtypeInclusion U) d))
    (a : Homology U (d + 1)) : connecting U d a = 0 := by
  have ha : connecting U d a ∈
      LinearMap.ker (singularHomologyMap (subtypeInclusion U) d) :=
    (exact_at_subspace U d).le ⟨a, rfl⟩
  exact h (ha.trans (singularHomologyMap (subtypeInclusion U) d).map_zero.symm)

theorem homologyZero_subsingleton_of_surjective
    (h : Function.Surjective (singularHomologyMap (subtypeInclusion U) 0)) :
    Subsingleton (Homology U 0) := by
  have hz (a : Homology U 0) : a = 0 := by
    obtain ⟨b, rfl⟩ := toRelative_zero_surjective U a
    exact toRelative_eq_zero_of_surjective U 0 h b
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

theorem homologySucc_subsingleton_of_maps (d : ℕ)
    (hi : Function.Injective (singularHomologyMap (subtypeInclusion U) d))
    (hs : Function.Surjective (singularHomologyMap (subtypeInclusion U) (d + 1))) :
    Subsingleton (Homology U (d + 1)) := by
  have hz (a : Homology U (d + 1)) : a = 0 := by
    have ha : a ∈ LinearMap.ker (connecting U d) :=
      connecting_eq_zero_of_injective U d hi a
    rw [← exact_at_relative] at ha
    obtain ⟨b, rfl⟩ := ha
    exact toRelative_eq_zero_of_surjective U (d + 1) hs b
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

theorem subsingleton_of_inclusion_bijective
    (h : ∀ d, Function.Bijective (singularHomologyMap (subtypeInclusion U) d)) (d : ℕ) :
    Subsingleton (Homology U d) := by
  cases d with
  | zero => exact homologyZero_subsingleton_of_surjective U (h 0).surjective
  | succ d => exact homologySucc_subsingleton_of_maps U d (h d).injective (h (d + 1)).surjective

end NoExoticSixSphere.RelativeSingularHomology
