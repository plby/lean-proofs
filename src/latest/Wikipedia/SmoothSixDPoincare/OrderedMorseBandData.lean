import Wikipedia.SmoothSixDPoincare.MorseBandHomology
import Wikipedia.SmoothSixDPoincare.OrderedMorseSurgeries

/-!
# Retained actual band maps for coherent finite homology coordinates

Choose each bridge once from the constructed ambient regular-band
diffeomorphism. Its sublevel restriction and induced homology equivalence
are then shared by every consecutive basis or attaching-column comparison.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f)

structure BandData (i j : Fin S.count) where
  ambient : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞
  level : (S.data (S.point i)).UpperLevel ≃ₜ (S.data (S.point j)).LowerLevel
  sublevel_image : ambient '' {x : M | f x ≤ S.upper (S.point i)} =
    {x : M | f x ≤ S.lower (S.point j)}
  level_coe : ∀ x : (S.data (S.point i)).UpperLevel, (level x : M) = ambient x

theorem nonempty_consecutiveBandData
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) : Nonempty (S.BandData i j) := by
  let _ := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
  obtain ⟨D, b, hD, hb⟩ := S.exists_consecutiveBandBridge hf i j hij
  exact ⟨⟨D, b.toHomeomorph, hD, hb⟩⟩

def consecutiveBandData (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) : S.BandData i j :=
  Classical.choice (S.nonempty_consecutiveBandData hf i j hij)

namespace BandData

variable {S} {i j : Fin S.count} (D : S.BandData i j)

def sublevelHomeomorph : {x : M // f x ≤ S.upper (S.point i)} ≃ₜ
    {x : M // f x ≤ S.lower (S.point j)} :=
  (S.data (S.point i)).bandSublevelHomeomorph (S.data (S.point j))
    D.ambient.toHomeomorph D.sublevel_image

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem sublevelHomeomorph_coe (x : {x : M // f x ≤ S.upper (S.point i)}) :
    (D.sublevelHomeomorph x : M) = D.ambient x := rfl

def homologyEquiv (k : ℕ) :
    SingularHomology {x : M // f x ≤ S.upper (S.point i)} k ≃ₗ[ℤ]
      SingularHomology {x : M // f x ≤ S.lower (S.point j)} k :=
  homeomorphHomologyEquiv D.sublevelHomeomorph k

end BandData

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
