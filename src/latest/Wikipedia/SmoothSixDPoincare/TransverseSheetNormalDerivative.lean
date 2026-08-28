import Wikipedia.SmoothSixDPoincare.SheetNormalCoordinates

/-!
# Invertible normal derivative of an actual transverse native sheet

The derivative is computed from the inverse of a genuine clean ambient sheet
chart. Transversality of the original native sheet maps makes the second
sheet's normal derivative surjective; the complementary dimension makes it
bijective. The statement also holds after any genuine source parametrization.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D B E M A Z N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace A N]
  [TopologicalSpace P] [ChartedSpace Z P]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞)

/-- Normal coordinates differentiate to an isomorphism on the complementary transverse sheet. -/
theorem bijective_normalDerivative_transverse_sheet {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ range F ↔ q.2 = 0)
    {x : N} {y : P} (hx : F x ∈ Φ.target) (hxy : G y = F x)
    (ht : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Bijective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y) := by
  let Q : E →L[ℝ] B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)
  let DF : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x
  let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y
  have hQ : Surjective Q := surjective_mfderiv_normalCoordinate Φ hx
  have hQA : Q.comp DF = 0 := normalDerivative_comp_sheet_eq_zero Φ hF hclean hx
  have hb : Bijective (Q.comp DG) := bijective_normal_comp Q DF DG hQ ht hQA hdim
  have hy : G y ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hderiv : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y = Q.comp DG := by
    rw [mfderiv_comp y (hnormal.mdifferentiableAt (by simp))
      (hG.mdifferentiableAt (by simp)), hxy]
    rfl
  rw [hderiv]
  exact hb

variable {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z']

/-- Reparametrization through a genuine native chart retains the invertible normal derivative. -/
theorem bijective_normalDerivative_transverse_parametrization {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ range F ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) {z : Z'} (hz : z ∈ c.source)
    {x : N} (hx : F x ∈ Φ.target) (hxy : G (c z) = F x)
    (ht : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c z))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Bijective (fderiv ℝ ((normalCoordinate Φ ∘ G) ∘ c) z) := by
  have hb := bijective_normalDerivative_transverse_sheet Φ hF hG hclean hx hxy ht hdim
  have hy : G (c z) ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, B) ∞ (normalCoordinate Φ ∘ G) (c z) :=
    hnormal.comp (c z) hG.contMDiffAt
  rw [← mfderiv_eq_fderiv, mfderiv_comp z (hg.mdifferentiableAt (by simp))
    (c.mdifferentiableAt (by simp) hz)]
  exact hb.comp (PartialChart.bijective_mfderiv c hz)

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates
