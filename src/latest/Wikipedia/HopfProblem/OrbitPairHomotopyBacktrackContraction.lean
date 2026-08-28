import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionRelative
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Jointly continuous contraction of a homotopy followed by its reverse

The contraction is assembled from the explicit interval formula used by
the native path backtracking homotopy. Its dependence on the spatial
parameter is proved continuous before currying into the path space.
-/

noncomputable section

universe u v

open unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

variable {B : Type u} {Z : Type v} [TopologicalSpace B] [TopologicalSpace Z]
    {f₀ f₁ : C(B, Z)}

def backtrackContraction (H : f₀.Homotopy f₁) : C(I × B, C(I, Z)) :=
  (⟨fun p : (I × B) × I ↦
      (Path.Homotopy.reflTransSymm (H.evalAt p.1.2)) (σ p.1.1, p.2), by
    change Continuous (fun p : (I × B) × I ↦
      H (⟨Path.Homotopy.reflTransSymmAux (σ p.1.1, p.2),
        Path.Homotopy.reflTransSymmAux_mem_I _⟩, p.1.2))
    exact H.continuous.comp
      ((Path.Homotopy.continuous_reflTransSymmAux.comp
        ((continuous_symm.comp continuous_fst.fst).prodMk continuous_snd)).subtype_mk _ |>.prodMk
          continuous_fst.snd)⟩ : C((I × B) × I, Z)).curry

theorem backtrackContraction_initial (H : f₀.Homotopy f₁) (b : B) (t : I) :
    backtrackContraction H (0, b) t = (H.trans H.symm) (t, b) := by
  change (Path.Homotopy.reflTransSymm (H.evalAt b)) (σ 0, t) = _
  rw [symm_zero]
  exact (Path.Homotopy.reflTransSymm (H.evalAt b)).map_one_left t

theorem backtrackContraction_final (H : f₀.Homotopy f₁) (b : B) (t : I) :
    backtrackContraction H (1, b) t = f₀ b := by
  change (Path.Homotopy.reflTransSymm (H.evalAt b)) (σ 1, t) = _
  rw [symm_one]
  exact (Path.Homotopy.reflTransSymm (H.evalAt b)).map_zero_left t

theorem backtrackContraction_zero (H : f₀.Homotopy f₁) (s : I) (b : B) :
    backtrackContraction H (s, b) 0 = f₀ b := by
  change H (⟨Path.Homotopy.reflTransSymmAux (σ s, 0), _⟩, b) = _
  have h : (⟨Path.Homotopy.reflTransSymmAux (σ s, 0),
      Path.Homotopy.reflTransSymmAux_mem_I _⟩ : I) = 0 := by
    apply Subtype.ext
    simp [Path.Homotopy.reflTransSymmAux]
  rw [h]
  exact H.map_zero_left b

theorem backtrackContraction_one (H : f₀.Homotopy f₁) (s : I) (b : B) :
    backtrackContraction H (s, b) 1 = f₀ b := by
  change H (⟨Path.Homotopy.reflTransSymmAux (σ s, 1), _⟩, b) = _
  have h : (⟨Path.Homotopy.reflTransSymmAux (σ s, 1),
      Path.Homotopy.reflTransSymmAux_mem_I _⟩ : I) = 0 := by
    apply Subtype.ext
    norm_num [Path.Homotopy.reflTransSymmAux]
  rw [h]
  exact H.map_zero_left b

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
