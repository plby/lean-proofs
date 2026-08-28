import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourier
import Mathlib.Analysis.Complex.Liouville

/-!
# Ambient representatives of the original local inverse Fourier modes

For a period family whose base is an actual open subset of the complex
plane, extend each inverse mode by zero outside that original base. The
extension agrees literally with the native inverse on the base and is
holomorphic wherever the previously proved common-neighborhood estimate
holds. No regularity outside that neighborhood is used.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

open Set Topology TopologicalSpace Metric PeriodTorusLineBundleClassification

variable {U₀ : Opens ℂ} (P : HolomorphicPeriodMap ℂ U₀)

/-- Zero extension only supplies an ambient function for ordinary complex
derivative notation; its restriction is the original inverse mode. -/
def ambientInverse (p₀ : PeriodDomain) (k : Fin 4 → ℤ) : ℂ → ℂ :=
  (Subtype.val : U₀ → ℂ).extend
    (fun b => denominatorInverse p₀ (P.point b) (integerFrequency k)) 0

@[simp] theorem ambientInverse_apply (p₀ : PeriodDomain) (k : Fin 4 → ℤ) (b : U₀) :
    ambientInverse P p₀ k b = denominatorInverse p₀ (P.point b) (integerFrequency k) :=
  Subtype.val_injective.extend_apply _ _ b

/-- The ambient representative has the same holomorphic germ as the actual
inverse mode, using the unchanged inherited atlas on the original base. -/
theorem ambientInverse_holomorphicAt (p₀ : PeriodDomain) (k : Fin 4 → ℤ)
    (W : Set U₀) (hW : IsOpen W)
    (hhol : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun b => denominatorInverse p₀ (P.point b) (integerFrequency k)) W)
    (b : U₀) (hb : b ∈ W) :
    ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (ambientInverse P p₀ k) (b : ℂ) := by
  apply (contMDiffAt_subtype_iff (I := modelWithCornersSelf ℂ ℂ)
    (I' := modelWithCornersSelf ℂ ℂ) (x := b)).mp
  simpa only [ambientInverse_apply] using hhol.contMDiffAt (hW.mem_nhds hb)

/-- Native holomorphicity becomes ordinary complex differentiability on
the actual image open in the complex plane. -/
theorem ambientInverse_differentiableOn_image (p₀ : PeriodDomain) (k : Fin 4 → ℤ)
    (W : Set U₀) (hW : IsOpen W)
    (hhol : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun b => denominatorInverse p₀ (P.point b) (integerFrequency k)) W) :
    DifferentiableOn ℂ (ambientInverse P p₀ k) ((Subtype.val : U₀ → ℂ) '' W) := by
  rintro z ⟨b, hb, rfl⟩
  exact ((ambientInverse_holomorphicAt P p₀ k W hW hhol b hb).contDiffAt.differentiableAt
    (by simp)).differentiableWithinAt

/-- Every original base point has a genuine ambient open neighborhood on
which all actual inverse modes are holomorphic and uniformly bounded. -/
theorem exists_open_ambient_uniform_inverse (b₀ : U₀) :
    ∃ (W : Set ℂ) (c : ℝ), IsOpen W ∧ (b₀ : ℂ) ∈ W ∧ W ⊆ U₀ ∧ 0 < c ∧
      (∀ k : Fin 4 → ℤ, DifferentiableOn ℂ (ambientInverse P (P.point b₀) k) W) ∧
      (∀ b ∈ W, ∀ k : Fin 4 → ℤ,
        ‖ambientInverse P (P.point b₀) k b‖ ≤ c⁻¹ * ‖k‖⁻¹) := by
  obtain ⟨W, c, hW, hb₀, hc, _, hhol, hbound⟩ :=
    exists_open_uniform_holomorphic_inverse P b₀
  refine ⟨(Subtype.val : U₀ → ℂ) '' W, c, U₀.isOpen.isOpenMap_subtype_val _ hW,
    ⟨b₀, hb₀, rfl⟩, ?_, hc, ?_, ?_⟩
  · rintro z ⟨b, _, rfl⟩
    exact b.property
  · intro k
    exact ambientInverse_differentiableOn_image P (P.point b₀) k W hW
      (hhol (integerFrequency k))
  · rintro z ⟨b, hb, rfl⟩ k
    simpa only [ambientInverse_apply] using hbound b hb k

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier
