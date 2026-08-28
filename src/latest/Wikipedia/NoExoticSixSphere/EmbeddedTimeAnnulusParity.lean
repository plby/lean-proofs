import Wikipedia.NoExoticSixSphere.EmbeddedTimeBoundaryGermCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldFourAnnulusBoundaryHomotopy
import Wikipedia.NoExoticSixSphere.AnnulusDoublePointParity

/-!
# Actual induced-boundary parity agrees across a proper generic annulus

At the inner sphere use the positive-time graph and outward normal;
at the outer sphere use the negative-time graph and the reflected inward
normal coordinates. The literal radius-two source dilation is retained.
The original annulus operator homotopy therefore compares the two actual
outward-frame parities, even when the zero boundary is disconnected.
Construction of a suitable annulus from homology data remains separate.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization Stiefel DiskBoundary SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (6 + 1)) M]
  [IsManifold (𝓡 (6 + 1)) ∞ M] (e : EuclideanEmbedding (6 + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 (6 + 1)) e.normalProjection e.NormalModel) (m : M)

theorem sphereParity_eq_of_even_generic_annulus
    (f₀ f₁ : C(Sphere 3, {x : M // t x = 0})) (g : Vector 4 → M)
    (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ g x)
    (hb₀ : ∀ s : Sphere 3, g s.val = (f₀ s).val)
    (hb₁ : ∀ s : Sphere 3, g ((2 : ℝ) • s.val) = (f₁ s).val)
    (P : GenericFourAnnulus.ParityBallSystem g)
    (heven : Even (AnnulusDoublePoints.singularSet g).ncard)
    (hheight₀ : ∀ s : Sphere 3, 0 < fderiv ℝ (t ∘ g) s.val s.val)
    (hheight₁ : ∀ s : Sphere 3,
      fderiv ℝ (t ∘ g) ((2 : ℝ) • s.val) ((2 : ℝ) • s.val) < 0) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₀) (hi₀ : Injective f₀)
      (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f₀ s))
      (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₁) (hi₁ : Injective f₁)
      (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f₁ s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f₀ hf₀ hi₀ hd₀ =
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f₁ hf₁ hi₁ hd₁ := by
  let := zeroAtlas t ht hreg
  intro hf₀ hi₀ hd₀ hf₁ hi₁ hd₁
  let P₀ := (e.puncturedFourAnnulusOperatorMap a g hg P).comp P.innerBoundary
  let P₁ := (e.puncturedFourAnnulusOperatorMap a g hg P).comp P.outerBoundary
  have hg₀ (s : Sphere 3) : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g s.val := by
    apply hg s.val
    change 1 ≤ ‖s.val‖ ∧ ‖s.val‖ ≤ 2
    rw [ClosedHemisphere.unit_norm]
    norm_num
  have hg₁ (s : Sphere 3) : ContMDiffAt (𝓡 4) (𝓡 7) ∞ g ((2 : ℝ) • s.val) := by
    apply hg ((2 : ℝ) • s.val)
    change 1 ≤ ‖(2 : ℝ) • s.val‖ ∧ ‖(2 : ℝ) • s.val‖ ≤ 2
    rw [norm_smul, ClosedHemisphere.unit_norm]
    norm_num
  let R : Vector 4 ≃L[ℝ] Vector 4 :=
    (LinearEquiv.smulOfNeZero ℝ (Vector 4) 2 (by norm_num)).toContinuousLinearEquiv
  have hcrit₀ := sphereParity_zero_iff_signed_germOperator_extends e r t ht hreg a m
    true f₀ g hg₀ hb₀ P₀ (fun _ ↦ rfl) hheight₀ hf₀ hi₀ hd₀
  have hcrit₁ := sphereParity_zero_iff_signed_reparametrized_germOperator_extends
    e r t ht hreg a m false R f₁ g hg₁ hb₁ P₁ (fun _ ↦ rfl)
      (fun s ↦ neg_pos.mpr (hheight₁ s)) hf₁ hi₁ hd₁
  have hhom : P₁.Homotopic P₀ :=
    e.puncturedFourAnnulusOperatorMap_outer_homotopic_inner a g hg P heven
  exact zmodTwo_eq_of_zero_iff _ _
    (hcrit₀.trans ((extends_homotopic_iff hhom).symm.trans hcrit₁.symm))

theorem sphereParity_eq_of_proper_generic_annulus
    (f₀ f₁ : C(Sphere 3, {x : M // t x = 0})) (g : Vector 4 → M)
    (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ g x)
    (hb₀ : ∀ s : Sphere 3, g s.val = (f₀ s).val)
    (hb₁ : ∀ s : Sphere 3, g ((2 : ℝ) • s.val) = (f₁ s).val)
    (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
    (himmersive : ∀ x ∈ domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
      Injective (fderiv ℝ (e.toFun ∘ g) x))
    (charts : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
    (hcov : ∀ y : M, ∃ c ∈ charts, y ∈ c.source)
    (hgen : ∀ c ∈ charts, OperatorRank.RegularFourSevenOn
      (fun x ↦ fderiv ℝ (c ∘ g) x) {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source})
    (hinside : closure (AnnulusDoublePoints.points g) ⊆ openDomain 3 ×ˢ openDomain 3)
    (hdouble : CompactRetractionAffineFamily.RegularDoublePointsOn
      g (openDomain 3) (openDomain 3) charts)
    (hheight₀ : ∀ s : Sphere 3, 0 < fderiv ℝ (t ∘ g) s.val s.val)
    (hheight₁ : ∀ s : Sphere 3,
      fderiv ℝ (t ∘ g) ((2 : ℝ) • s.val) ((2 : ℝ) • s.val) < 0) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₀) (hi₀ : Injective f₀)
      (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f₀ s))
      (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₁) (hi₁ : Injective f₁)
      (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f₁ s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f₀ hf₀ hi₀ hd₀ =
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f₁ hf₁ hi₁ hd₁ := by
  let := zeroAtlas t ht hreg
  intro hf₀ hi₀ hd₀ hf₁ hi₁ hd₁
  obtain ⟨P, -⟩ := GenericFourAnnulus.exists_parityBallSystem e g hg r₀ r₁ hr₀ hr₁
    himmersive charts hcov hgen
  have heven := (AnnulusDoublePoints.finite_even_singularSet e g hg r₀ r₁ hr₀ hr₁
    himmersive charts hcov hgen hinside hdouble).2
  exact sphereParity_eq_of_even_generic_annulus e r t ht hreg a m f₀ f₁ g hg hb₀ hb₁ P
    heven hheight₀ hheight₁ hf₀ hi₀ hd₀ hf₁ hi₁ hd₁

end NoExoticSixSphere.EmbeddedTime
