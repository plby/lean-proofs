import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria

/-!
# Descent from actual cycles to actual homology in every degree

The canonical module-homology isomorphism identifies the categorical homology
object with cycles modulo boundaries. A linear map on cycles annihilating all
actual boundaries therefore induces a unique map from that homology object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- The actual boundaries, regarded as a submodule of the actual cycle kernel. -/
abbrev homologyBoundaries : Submodule ℤ (Cycle K n) :=
  FirstHurewicz.ChainHomology.ShortBoundaries (K.sc n)

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Maps from categorical homology are determined by their values on cycle classes. -/
theorem homologyLinearMap_ext {f g : K.homology n →ₗ[ℤ] M}
    (h : ∀ c : Cycle K n, f (cycleClass K n c) = g (cycleClass K n c)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := cycleClass_surjective K n x
  exact h c

variable (f : Cycle K n →ₗ[ℤ] M)
  (hf : ∀ b : K.X (n + 1), f (boundaryCycle K n b) = 0)

include hf in
/-- Annihilating the ordinary incoming boundaries kills the canonical boundary submodule. -/
theorem homologyBoundaries_le_ker : homologyBoundaries K n ≤ LinearMap.ker f := by
  rintro c ⟨b, hb⟩
  have hc : cycleClass K n c = 0 :=
    (FirstHurewicz.ChainHomology.shortCycleClass_eq_zero_iff (K.sc n) c).mpr
      ⟨b, congrArg Subtype.val hb⟩
  obtain ⟨b', hb'⟩ := (cycleClass_eq_zero_iff K n c).mp hc
  have he : boundaryCycle K n b' = c := Subtype.ext hb'
  exact (congrArg f he).symm.trans (hf b')

/-- Canonical descent to Mathlib's actual categorical homology, in arbitrary degree. -/
def homologyDesc : K.homology n →ₗ[ℤ] M :=
  ((homologyBoundaries K n).liftQ f (homologyBoundaries_le_ker K n f hf)).comp
    (K.sc n).moduleCatHomologyIso.hom.hom

@[simp] theorem homologyDesc_cycleClass (c : Cycle K n) :
    homologyDesc K n f hf (cycleClass K n c) = f c := by
  have h := congrArg (fun q => q.hom (Submodule.Quotient.mk c))
    (K.sc n).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((homologyBoundaries K n).liftQ f (homologyBoundaries_le_ker K n f hf)) h

/-- The descended map composed with the genuine cycle-class map is the original map. -/
theorem homologyDesc_comp_cycleClass :
    (homologyDesc K n f hf).comp (cycleClass K n) = f := by
  apply LinearMap.ext
  intro c
  exact homologyDesc_cycleClass K n f hf c

/-- The universal property uniquely specifies the descended homology map. -/
theorem homologyDesc_unique (g : K.homology n →ₗ[ℤ] M)
    (hg : ∀ c : Cycle K n, g (cycleClass K n c) = f c) :
    g = homologyDesc K n f hf := by
  apply homologyLinearMap_ext K n
  intro c
  rw [hg, homologyDesc_cycleClass]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
