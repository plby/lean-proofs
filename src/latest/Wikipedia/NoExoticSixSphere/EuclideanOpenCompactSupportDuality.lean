import Wikipedia.NoExoticSixSphere.ConvexOpenCompactSupportDuality
import Wikipedia.NoExoticSixSphere.CompactSupportDualityBasicUnion

/-!
# Actual compact-support cap duality on all Euclidean open subsets

Bounded convex open subsets form an intersection-stable collection.
Every Euclidean open set is their actual union, since it contains a
small open ball around each of its points. The proved finite-union and
directed-union cap theorems assemble the original cap-duality property.
-/

noncomputable section

open TopologicalSpace Metric Bornology

namespace NoExoticSixSphere.CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Every actual Euclidean open subset has original compact-support cap duality. -/
theorem euclidean_open_duality (U : Opens E) : Duality (E := E) n U := by
  let B (V : Opens E) : Prop := Convex ℝ (V : Set E) ∧ IsBounded (V : Set E)
  have hB (V : Opens E) (hV : B V) : Duality (E := E) n V := by
    let : ChartedSpace E (V : Set E) := inferInstanceAs (ChartedSpace E V)
    exact bounded_convex_open_duality (E := E) n (V : Set E) V.isOpen hV.1 hV.2
  have hBI (V W : Opens E) (hV : B V) (hW : B W) : B (V ⊓ W) :=
    ⟨hV.1.inter hW.1, hV.2.subset Set.inter_subset_left⟩
  let I := {V : Opens E // V ≤ U ∧ B V}
  let F : I → Opens E := fun V => V.val
  have he : (⨆ i, F i) = U := by
    apply le_antisymm
    · exact iSup_le fun i => i.property.1
    · intro x hx
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
      let V : Opens E := ⟨ball x r, isOpen_ball⟩
      let i : I := ⟨V, hball, convex_ball x r, isBounded_ball⟩
      exact Opens.mem_iSup.mpr ⟨i, mem_ball_self hr⟩
  exact (congrArg (fun V : Opens E => Duality (E := E) n V) he).mp
    (duality_iSup_of_basic_family (E := E) n B hB hBI F (fun i => i.property.2))

end NoExoticSixSphere.CompactSupportCapMap
