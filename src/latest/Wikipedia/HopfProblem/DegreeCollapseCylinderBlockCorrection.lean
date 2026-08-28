import Wikipedia.HopfProblem.DegreeCollapseTransverseCorrectionTransport
import Wikipedia.HopfProblem.DegreeCollapseTransverseProjectedEquiv

/-!
# A supported cylinder-label correction from actual endpoint transversality

The projected equivalence, nonlinear reduction, shears, and both global
conjugations are constructed. The resulting one supported correction
retains the unique relative plane intersection on the whole original
domain and has the exact diagonal transition germ.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B Z : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

open Classical in
theorem exists_cylinder_block_correction
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0)
    (hQzero : Q 0 = 0) (hPzero : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (htrans : NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B)
      (fun x : A => H (x, 0)) (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ H.source → ((H (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (L₁ : A ≃L[ℝ] A) (L₂ : B ≃L[ℝ] B)
      (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (K : Set Z),
      IsCompact K ∧ K ⊆ Q.target ∩ P.target ∧
      Nonempty (SupportedRelativeIsotopy D K {(0 : Z)}) ∧ D 0 = 0 ∧
      (∀ z ∈ H.source, D (Q z) ∈ P.target) ∧
      (∀ x : A, (x, (0 : B)) ∈ H.source →
        ((P.symm (D (Q (x, 0)))).1 = 0 ↔ x = 0)) ∧
      (fun z => D (Q z)) =ᶠ[𝓝 (0 : A × B)] (fun z => P (L₁ z.1, L₂ z.2)) := by
  obtain ⟨L₁, _, L₂, Dₛ, Dₜ, Kₛ, Kₜ, hKₛ, hKs, hKₜ, hKt, ⟨Iₛ⟩, ⟨Iₜ⟩,
      hDₛ, hDₜ, huniq, hgerm⟩ :=
    exists_block_reduction_of_native_transverse H h0 hH0 htrans hunique
  have hP0 : (0 : A × B) ∈ P.source := by
    have hh := hHt (H.map_source' h0)
    rwa [hH0] at hh
  obtain ⟨D, K, hK, _, hKU, hI, hD0, hformula⟩ :=
    exists_transported_transition_correction Q P H (hHs h0) hP0 hQzero hPzero
      hHs hHt hdiagram Dₛ Dₜ hKₛ hKₜ hKs hKt
      (show (0 : A × B) ∈ {p : A × B | p.2 = 0} from rfl)
      (show (0 : A × B) ∈ ({(0 : A × B)} : Set (A × B)) from rfl) Iₛ Iₜ
  have hPt (z : A × B) (hz : z ∈ H.source) : Dₜ (H (Dₛ z)) ∈ P.source :=
    hHt (hDₜ (H.map_source' (hDₛ hz)))
  have hinverse (z : A × B) (hz : z ∈ H.source) :
      P.symm (D (Q z)) = Dₜ (H (Dₛ z)) := by
    rw [hformula z hz]
    exact P.left_inv' (hPt z hz)
  refine ⟨L₁, L₂, D, K, hK, hKU, hI, hD0, ?_, ?_, ?_⟩
  · intro z hz
    rw [hformula z hz]
    exact P.map_source' (hPt z hz)
  · intro x hx
    rw [hinverse (x, 0) hx]
    exact huniq x hx
  · filter_upwards [H.open_source.mem_nhds h0, hgerm] with z hz hg
    rw [hformula z hz, hg]

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
