import Wikipedia.SmoothSixDPoincare.MorseCellHomologySequence
import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints
import Wikipedia.SmoothSixDPoincare.HomotopySphereHomology

/-!
# Homology below the last actual Morse surgery of a homotopy six-sphere

The final upper sublevel is the original manifold, and the final index is
six. Its attaching sphere is therefore an actual five-sphere. The proved
Morse homology sequence and the original homotopy equivalence force the
first four positive homology groups of the actual final lower sublevel to
vanish. No homological property of that sublevel is assumed.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology
  Wikipedia.HopfProblem.SphereHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

namespace SurgeryWindows

variable (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

def lastUpperHomeomorph (h : 0 < S.count) :
    {x : M // f x ≤ S.upper (S.last h)} ≃ₜ M :=
  (Homeomorph.setCongr (S.last_upper_univ hf h)).trans (Homeomorph.Set.univ M)

include hf in
omit [FiniteDimensional ℝ E] in
open Classical in
/-- The actual sublevel before the last surgery has zero integral homology
in degrees one to four. -/
theorem lastLower_homology_subsingleton (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) (h : 0 < S.count) (k : ℕ) (hk : 0 < k) (hk5 : k < 5) :
    Subsingleton (SingularHomology {x : M // f x ≤ S.lower (S.last h)} k) := by
  let d := S.data (S.last h)
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1 :=
    (S.last_index_dimension hf h).trans hdim
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1) := ⟨hindex⟩
  let : Subsingleton (SingularHomology M k) :=
    homotopySixSphere_homology_subsingleton hM k hk.ne' (by omega)
  let : Subsingleton (SingularHomology {x : M // f x ≤ f (S.last h) + d.radius ^ 2} k) :=
    (homeomorphHomologyEquiv (S.lastUpperHomeomorph hf h) k).injective.subsingleton
  let : Subsingleton (SingularHomology (Hemisphere.Sphere 5) k) :=
    unitSphere_homology_subsingleton 4 k hk.ne' (by omega)
  let : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) k) :=
    (homeomorphHomologyEquiv
      (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 5).symm.toHomeomorph
        k).injective.subsingleton
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf.continuous k hk.ne'

end SurgeryWindows

/-- The original smooth homotopy-six-sphere data constructs a finite surgery system whose
actual final lower sublevel has the required low-degree homology vanishing. -/
theorem exists_surgeryWindows_with_terminal_homology (hdim : Module.finrank ℝ E = 6)
    (hM : M ≃ₕ SixSphere) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ S : SurgeryWindows E f, ∃ h : 0 < S.count,
        ∀ k : ℕ, 0 < k → k < 5 →
          Subsingleton (SingularHomology {x : M // f x ≤ S.lower (S.last h)} k) := by
  let : Nonempty M := ⟨hM.invFun (basePoint 6)⟩
  obtain ⟨f, hf, hm, ⟨S⟩⟩ := exists_morse_function_with_surgeryWindows E M
  refine ⟨f, hf, hm, S, S.count_pos hf, ?_⟩
  exact S.lastLower_homology_subsingleton hf hdim hM (S.count_pos hf)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
