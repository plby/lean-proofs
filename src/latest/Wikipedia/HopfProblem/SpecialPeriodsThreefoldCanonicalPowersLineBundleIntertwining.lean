import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleSections
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleTensorFibresGauges

/-!
# Native section powers are actual tensor powers

The polynomial section-power construction is identified with the pure
tensor power in the full algebraic tensor product of the original fibre.
Powering a genuine holomorphic bundle comparison commutes with this
native polynomial map, not merely with its transition-character formula.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]

namespace Powers

/-- A section power is the pure tensor power of the actual original
fibre vector under the full tensor-fibre equivalence. -/
theorem sectionPower_eq_tensor (A : TransitionData M ι) (n : ℕ)
    (s : ∀ x, A.core.Fiber x) (x : M) :
    sectionPower A n s x = fiberTensorPowerEquiv A x n (purePower (s x) n) :=
  (fiberTensorPowerEquiv_purePower A x n (s x)).symm

/-- The native total-space polynomial map is the actual pure tensor
operation followed by the full tensor-fibre identification. -/
theorem powerMap_eq_tensor (A : TransitionData M ι) (n : ℕ) (p : A.core.TotalSpace) :
    powerMap A n p =
      ⟨p.proj, fiberTensorPowerEquiv A p.proj n (purePower p.2 n)⟩ := by
  cases p with
  | mk x v =>
    exact congrArg (fun w : (A.power n).core.Fiber x =>
      (⟨x, w⟩ : (A.power n).core.TotalSpace))
      (fiberTensorPowerEquiv_purePower A x n v).symm

section Holomorphic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  (A : TransitionData M ι) [A.IsHolomorphic I]

/-- The same intrinsic tensor statement for bundled holomorphic sections. -/
theorem holomorphicSectionPower_eq_tensor (n : ℕ)
    (s : ContMDiffSection I ℂ ω A.core.Fiber) (x : M) :
    holomorphicSectionPower A n I s x =
      fiberTensorPowerEquiv A x n (purePower (s x) n) :=
  sectionPower_eq_tensor A n s x

end Holomorphic

end Powers

namespace CrossGauge

open Powers

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
  {A : TransitionData M ι} {B : TransitionData M κ} (G : CrossGauge I A B)

/-- The actual powered fibre comparison carries a section power to the
power of the corresponding original fibre image. -/
theorem power_fiberEquiv_sectionPower (n : ℕ) (s : ∀ x, A.core.Fiber x) (x : M) :
    (G.power n).fiberEquiv x (sectionPower A n s x) =
      sectionPower B n (fun y => G.fiberEquiv y (s y)) x :=
  G.power_fiberEquiv_pow n x (s x)

variable [A.IsHolomorphic I] [B.IsHolomorphic I]

/-- Functoriality for the genuine holomorphic maps of original total
spaces, with every point and native fibre retained. -/
theorem power_diffeomorph_powerMap (n : ℕ) (p : A.core.TotalSpace) :
    (G.power n).diffeomorph (powerMap A n p) = powerMap B n (G.diffeomorph p) := by
  cases p with
  | mk x v =>
    exact congrArg (fun w : (B.power n).core.Fiber x =>
      (⟨x, w⟩ : (B.power n).core.TotalSpace)) (G.power_fiberEquiv_pow n x v)

end CrossGauge

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
