import Wikipedia.HopfProblem.DegreeCollapseConstructedKinkInsertion
import Wikipedia.HopfProblem.DegreeCollapseTripleFreeSphereRepresentative

/-!
# Actual embedded sphere representatives without a parity hypothesis

Generic approximation and finite Whitney reduction leave zero or one
unordered double point. In the latter case the constructed native kink
adds one, and the checked even-pair reduction removes the resulting pair.
The endpoint is an actual smooth closed embedding in the original homotopy
class. Normal framing of that embedding remains a separate invariant.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TripleParameters

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding SphereSelfIntersections DoublePointCounting

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [T2Space M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_embedded_sphere_representative (f : C(Sphere 3, M)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧ IsClosedEmbedding g := by
  obtain ⟨F, hF, HF, hi, ht, hd, hsmall⟩ := exists_at_most_one_double_representative e r f
  by_cases hzero : Nat.card (Unordered F) = 0
  · have hinj := injective_of_unordered_card_zero (finite_pairs hF ht hi) hzero
    exact ⟨F, hF, HF, hi, F.continuous.isClosedEmbedding hinj⟩
  · have hone : Nat.card (Unordered F) = 1 := by omega
    obtain ⟨G, hG, HG, hGi, hGt, hGd, hcount⟩ :=
      ImmersedSource.exists_insertion_increasing_unordered F hF hi ht hd
    have heven : unorderedParity G = 0 := by
      unfold unorderedParity
      rw [hcount, hone]
      change ((2 : ℕ) : ZMod 2) = 0
      exact ZMod.natCast_self 2
    obtain ⟨g, hg, H, hgi, hge⟩ :=
      ImmersedSource.exists_embedded_representative_of_even_double_points G hG hGi hGt hGd heven
    exact ⟨g, hg, HF.trans (HG.trans H), hgi, hge⟩

omit r in
theorem exists_embedded_representative_of_normalFrame
    (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (f : C(Sphere 3, M)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧ IsClosedEmbedding g := by
  let x : Sphere 3 := Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
  let : Nonempty M := ⟨f x⟩
  obtain ⟨r⟩ := e.nonempty_tubularRetraction a
  exact exists_embedded_sphere_representative e r f

end Wikipedia.HopfProblem.DegreeCollapse.TripleParameters
