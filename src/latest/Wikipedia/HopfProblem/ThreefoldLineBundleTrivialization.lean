import Wikipedia.HopfProblem.ThreefoldLineBundleTrivializationRepresentative
import Wikipedia.HopfProblem.HolomorphicPicardContinuousPrimitives
import Wikipedia.HopfProblem.HolomorphicPicardContinuousCore
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRealManifold

/-!
# Continuous triviality of every original holomorphic line bundle on X

This constructs a genuine fibrewise complex-linear homeomorphism from
the original total space of any native holomorphic line bundle to
`X × ℂ`.  The original bundle is first presented by an actual exponential
cocycle.  A genuine smooth partition of unity supplies additive
primitives, whose exponentials give continuous nonzero coordinates for
the original glued bundle topology.  The independently proved analytic
bundle isomorphism then returns the trivialization to the original bundle.

No classification by first Chern classes is assumed.  This is continuous,
not holomorphic, triviality, and no numerical holomorphic-cohomology
computation or smooth sphere-recognition hypothesis enters the proof.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleTrivialization

open HolomorphicExponentialSheaf HolomorphicPicard HolomorphicPicardNative

universe u

attribute [local instance] chartedSpace space_compact space_t2Space space_isSmoothRealManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

variable (V : Space → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IF]

/-- Every original native holomorphic line bundle on the actual glued
threefold admits a genuine continuous fibre-linear trivialization. -/
theorem native_continuously_trivial : Nonempty (ContinuousTrivialization V) := by
  obtain ⟨U, hU, c, ⟨e⟩⟩ := exists_exponential_cocycle_iso V
  obtain ⟨a, hne, hcompat⟩ := ContinuousSmooth.exists_exponential_coordinates Space U hU c
  exact ⟨ContinuousTrivialization.ofAnalyticBundleIso e.symm
    (ContinuousCore.trivialization IF Space U hU
      (Cech.mapCocycle (exponential IF Space) c) a hne hcompat)⟩

/-- Choose the actual trivialization whose existence was just proved. -/
def continuousTrivialization : ContinuousTrivialization V :=
  Classical.choice (native_continuously_trivial V)

/-- The actual homeomorphism preserves the original base projection. -/
theorem continuousTrivialization_preserves_base (v : TotalSpace ℂ V) :
    ((continuousTrivialization V).homeomorph v).1 = v.proj :=
  (continuousTrivialization V).preserves_base v

/-- The original fibre map is an actual complex-linear equivalence. -/
theorem continuousTrivialization_map_fiber (x : Space) (v : V x) :
    (continuousTrivialization V).homeomorph ⟨x, v⟩ =
      (x, (continuousTrivialization V).fiberEquiv x v) :=
  (continuousTrivialization V).map_fiber x v

/-- An actual section of the original bundle, obtained from the constant
one section of the product using the constructed inverse fibre map. -/
def nonvanishingSection (x : Space) : V x :=
  ((continuousTrivialization V).fiberEquiv x).symm 1

theorem nonvanishingSection_ne_zero (x : Space) : nonvanishingSection V x ≠ 0 := by
  intro h
  have he := congrArg ((continuousTrivialization V).fiberEquiv x) h
  exact one_ne_zero (by simpa only [nonvanishingSection, LinearEquiv.apply_symm_apply,
    map_zero] using he)

/-- Continuity is in the original native total-space topology. -/
theorem nonvanishingSection_continuous :
    Continuous (fun x : Space => (⟨x, nonvanishingSection V x⟩ : TotalSpace ℂ V)) := by
  have h := (continuousTrivialization V).homeomorph.symm.continuous.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Space => (1 : ℂ))))
  simpa only [Function.comp_def, id_eq, ContinuousTrivialization.symm_map_fiber,
    nonvanishingSection] using h

/-- The bundled original line-bundle statement, with its original native
fibre family and topology unchanged. -/
theorem continuously_trivial (L : LineBundle.{u} IF Space) :
    Nonempty (ContinuousTrivialization L.Fiber) :=
  native_continuously_trivial L.Fiber

/-- Actual nonzero continuous sections exist for every original bundle. -/
theorem exists_nonvanishing_continuous_section :
    ∃ s : ∀ x : Space, V x,
      Continuous (fun x => (⟨x, s x⟩ : TotalSpace ℂ V)) ∧ ∀ x, s x ≠ 0 :=
  ⟨nonvanishingSection V, nonvanishingSection_continuous V, nonvanishingSection_ne_zero V⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleTrivialization
