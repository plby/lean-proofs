import Wikipedia.NoExoticSixSphere.CellChartCoordinates
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Constructed coordinate approximation and supported cell cutoffs

The continuous coordinate extension on the larger closed core has a
global smooth approximation. A cutoff is one on the smaller core and
has its entire topological support inside the larger open core. These
are constructed from the original cell and map, not assumed smoothing
or support data.
-/

noncomputable section

open Set Metric TopologicalSpace
open scoped ContDiff

namespace NoExoticSixSphere.CellChart

theorem exists_supported_cutoff {D : Type} [TopologicalSpace D] [NormalSpace D]
    (K V : Set D) (hK : IsClosed K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ β : C(D, ℝ), EqOn β 1 K ∧ tsupport β ⊆ V ∧ ∀ z, β z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨W, hW, hKW, hWV⟩ := normal_exists_closure_subset hK hV hKV
  have hd : Disjoint Wᶜ K := Set.disjoint_left.mpr (fun _ h hK ↦ h (hKW hK))
  obtain ⟨β, hβ0, hβ1, hβ⟩ := exists_continuous_zero_one_of_isClosed hW.isClosed_compl hK hd
  have hs : Function.support β ⊆ W := by
    intro z hz
    by_contra hn
    exact hz (hβ0 hn)
  exact ⟨β, hβ1, (closure_mono hs).trans hWV, hβ⟩

variable {X D : Type} [TopologicalSpace X] [T2Space X]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  (n : ℕ) (U : Opens X) (e : (Fin n → ℝ) ≃ₜ U)

theorem exists_core_cutoff (f : C(D, X)) (r : ℝ) (hr : 0 < r) :
    ∃ β : C(D, ℝ), EqOn β 1 (f ⁻¹' core n U e (2 * r)) ∧
      tsupport β ⊆ f ⁻¹' openCore n U e (3 * r) ∧ ∀ z, β z ∈ Icc (0 : ℝ) 1 :=
  exists_supported_cutoff (f ⁻¹' core n U e (2 * r)) (f ⁻¹' openCore n U e (3 * r))
    ((isClosed_core n U e (2 * r)).preimage f.continuous)
    ((isOpen_openCore n U e (3 * r)).preimage f.continuous)
    (preimage_mono (core_subset_openCore n U e (by linarith)))

theorem exists_smooth_coordinate_approximation (f : C(D, X)) (r ε : ℝ) (hε : 0 < ε) :
    ∃ f₀ : C(D, (Fin n → ℝ)), ∃ g : D → (Fin n → ℝ), ContDiff ℝ ∞ g ∧
      (∀ z, dist (g z) (f₀ z) < ε) ∧
      ∀ z, f z ∈ core n U e r → encode n U e (f₀ z) = f z := by
  obtain ⟨f₀, hf₀⟩ := exists_coordinate_extension n U e f r
  obtain ⟨g, hg, hgf, _⟩ := f₀.continuous.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ ↦ ε) continuous_const (fun _ ↦ hε)
  exact ⟨f₀, g, hg, hgf, hf₀⟩

end NoExoticSixSphere.CellChart
