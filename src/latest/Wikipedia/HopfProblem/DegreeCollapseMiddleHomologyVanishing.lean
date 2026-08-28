import Wikipedia.SmoothSixDPoincare.OrderedMorseHomologyVanishing

/-!
# Propagate actual ambient homology vanishing through the Morse chain

Only vanishing of the specified integral homology group is required.
The last upper sublevel is the actual original manifold; its last handle
has index six. The actual sphere and handle sequences propagate vanishing
below that handle and then backward through nonmatching later indices.
There is no homotopy-sphere assumption, so this applies to H2-zero
six-manifolds with nonzero middle homology.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.HomologyVanishing

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

include hf

theorem lastLower_homology_subsingleton (hdim : Module.finrank ℝ E = 6)
    (h : 0 < S.count) (k : ℕ) (hk : 0 < k) (hk5 : k < 5)
    [Subsingleton (SingularHomology M k)] :
    Subsingleton (SingularHomology {x : M // f x ≤ S.lower (S.last h)} k) := by
  let d := S.data (S.last h)
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1 :=
    (S.last_index_dimension hf h).trans hdim
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1) := ⟨hindex⟩
  let : Subsingleton (SingularHomology {x : M // f x ≤ f (S.last h) + d.radius ^ 2} k) :=
    (homeomorphHomologyEquiv (S.lastUpperHomeomorph hf h) k).injective.subsingleton
  let : Subsingleton (SingularHomology (Hemisphere.Sphere 5) k) :=
    unitSphere_homology_subsingleton 4 k hk.ne' (by omega)
  let : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) k) :=
    (homeomorphHomologyEquiv
      (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 5).symm.toHomeomorph
        k).injective.subsingleton
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf.continuous k hk.ne'

theorem upper_homology_subsingleton_of_later_indices
    (hdim : Module.finrank ℝ E = 6)
    (j : Fin S.count) (hj : j.val + 1 < S.count)
    (k : ℕ) (hk : 0 < k) (hk5 : k < 5)
    [Subsingleton (SingularHomology M k)]
    (hindex : ∀ i : Fin S.count, j.val < i.val → i.val + 1 < S.count →
      2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton (SingularHomology {x : M // f x ≤ S.upper (S.point j)} k) := by
  have hcount : 0 < S.count := by omega
  let P : ℕ → Prop := fun i => ∀ hi : i < S.count,
    Subsingleton (SingularHomology {x : M // f x ≤ S.lower (S.point ⟨i, hi⟩)} k)
  have hlow : P (j.val + 1) := by
    apply Nat.decreasingInduction' (P := P) (m := j.val + 1) (n := S.count - 1)
    · intro i hi hji ih hi'
      have hs : i + 1 < S.count := by omega
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ f (S.point ⟨i + 1, hs⟩) -
            (S.data (S.point ⟨i + 1, hs⟩)).radius ^ 2} k) := ih hs
      obtain ⟨T, _, hT, _⟩ :=
        S.exists_consecutiveBandBridge hf ⟨i, hi'⟩ ⟨i + 1, hs⟩ rfl
      let H := (S.data (S.point ⟨i, hi'⟩)).bandSublevelHomeomorph
        (S.data (S.point ⟨i + 1, hs⟩)) T.toHomeomorph hT
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ f (S.point ⟨i, hi'⟩) +
            (S.data (S.point ⟨i, hi'⟩)).radius ^ 2} k) :=
        (homeomorphHomologyEquiv H k).injective.subsingleton
      obtain ⟨hlo, hne⟩ := hindex ⟨i, hi'⟩ (by change j.val < i; omega) hs
      exact (S.data (S.point ⟨i, hi'⟩)).lowerHomology_subsingleton_of_upper_and_index
        hf.continuous k hk.ne' hlo hne
    · omega
    · intro hi
      exact lastLower_homology_subsingleton S hf hdim hcount k hk hk5
  let : Subsingleton (SingularHomology
      {x : M // f x ≤ f (S.point ⟨j.val + 1, hj⟩) -
        (S.data (S.point ⟨j.val + 1, hj⟩)).radius ^ 2} k) := hlow hj
  obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf j ⟨j.val + 1, hj⟩ rfl
  let H := (S.data (S.point j)).bandSublevelHomeomorph
    (S.data (S.point ⟨j.val + 1, hj⟩)) T.toHomeomorph hT
  exact (homeomorphHomologyEquiv H k).injective.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.HomologyVanishing
