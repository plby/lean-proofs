import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria

/-!
# Canonical evaluation of a closed integral functional on actual homology

A closed functional on the actual chain module vanishes on the actual
incoming boundary image.  It therefore descends to chains modulo
boundaries and restricts to Mathlib's actual homology object.  The
construction has no projectivity or freeness hypothesis.  Its literal
evaluation on every cycle proves naturality and annihilation of actual
coboundaries, independently of choices of representatives.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree

open SingularMayerVietoris.ModuleHomology
open FirstHurewicz.ChainHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortOpchainsModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- Being closed means annihilating the literal incoming boundary map. -/
def IsClosedFunctional (φ : K.X n →ₗ[ℤ] ℤ) : Prop :=
  ∀ b : K.X (n + 1), φ ((K.d (n + 1) n).hom b) = 0

/-- A closed functional kills the incoming boundary submodule used by the actual homology object. -/
theorem closedFunctional_range_le_ker (φ : K.X n →ₗ[ℤ] ℤ)
    (hφ : IsClosedFunctional K n φ) :
    LinearMap.range (K.sc n).f.hom ≤ LinearMap.ker φ := by
  change LinearMap.range (K.d ((ComplexShape.down ℕ).prev n) n).hom ≤ LinearMap.ker φ
  rw [ChainComplex.prev]
  rintro x ⟨b, rfl⟩
  exact hφ b

/-- Evaluation on actual homology, by restricting the descended chain functional. -/
def evaluationOfClosed (φ : K.X n →ₗ[ℤ] ℤ) (hφ : IsClosedFunctional K n φ) :
    K.homology n →ₗ[ℤ] ℤ :=
  ((LinearMap.range (K.sc n).f.hom).liftQ φ
    (closedFunctional_range_le_ker K n φ hφ)).comp (shortHomologyToChainClass (K.sc n))

/-- Evaluation on every actual cycle is literally evaluation on its chain representative. -/
@[simp] theorem evaluationOfClosed_cycleClass (φ : K.X n →ₗ[ℤ] ℤ)
    (hφ : IsClosedFunctional K n φ) (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    evaluationOfClosed K n φ hφ
      (SingularMayerVietoris.ModuleHomology.cycleClass K n c) = φ c.1 := by
  exact congrArg ((LinearMap.range (K.sc n).f.hom).liftQ φ
    (closedFunctional_range_le_ker K n φ hφ))
    (shortHomologyToChainClass_cycleClass (K.sc n) c)

/-- Actual cycle classes determine evaluation uniquely. -/
theorem evaluationOfClosed_unique (φ : K.X n →ₗ[ℤ] ℤ)
    (hφ : IsClosedFunctional K n φ) (e : K.homology n →ₗ[ℤ] ℤ)
    (he : ∀ c : SingularMayerVietoris.ModuleHomology.Cycle K n,
      e (SingularMayerVietoris.ModuleHomology.cycleClass K n c) = φ c.1) :
    e = evaluationOfClosed K n φ hφ := by
  ext a
  obtain ⟨c, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n a
  rw [he, evaluationOfClosed_cycleClass]

/-- A literal coboundary is closed by the chain-complex differential identity. -/
theorem coboundary_isClosed (ψ : K.X (n - 1) →ₗ[ℤ] ℤ) :
    IsClosedFunctional K n (ψ.comp (K.d n (n - 1)).hom) := by
  intro b
  have h := congrArg (fun f : K.X (n + 1) ⟶ K.X (n - 1) => f.hom b)
    (K.d_comp_d (n + 1) n (n - 1))
  change (K.d n (n - 1)).hom ((K.d (n + 1) n).hom b) = 0 at h
  change ψ ((K.d n (n - 1)).hom ((K.d (n + 1) n).hom b)) = 0
  rw [h, map_zero]

/-- Every literal coboundary evaluates to zero on actual homology. -/
theorem evaluationOfClosed_coboundary (ψ : K.X (n - 1) →ₗ[ℤ] ℤ)
    (hψ : IsClosedFunctional K n (ψ.comp (K.d n (n - 1)).hom)) :
    evaluationOfClosed K n (ψ.comp (K.d n (n - 1)).hom) hψ = 0 := by
  ext a
  obtain ⟨c, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n a
  rw [evaluationOfClosed_cycleClass]
  change ψ ((K.d n (n - 1)).hom c.1) = 0
  rw [cycle_condition, map_zero]

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Pullback along an actual chain map preserves the literal cocycle equation. -/
theorem isClosedFunctional_pullback (f : K ⟶ L) (n : ℕ)
    (φ : L.X n →ₗ[ℤ] ℤ) (hφ : IsClosedFunctional L n φ) :
    IsClosedFunctional K n (φ.comp (f.f n).hom) := by
  intro b
  have h := congrArg (fun g : K.X (n + 1) ⟶ L.X n => g.hom b)
    (f.comm (n + 1) n)
  change φ ((f.f n).hom ((K.d (n + 1) n).hom b)) = 0
  exact (congrArg φ h.symm).trans (hφ ((f.f (n + 1)).hom b))

/-- Canonical evaluation is natural for every actual chain map, without any freeness assumption. -/
theorem evaluationOfClosed_naturality (f : K ⟶ L) (n : ℕ)
    (φ : L.X n →ₗ[ℤ] ℤ) (hφ : IsClosedFunctional L n φ)
    (hpull : IsClosedFunctional K n (φ.comp (f.f n).hom)) (a : K.homology n) :
    evaluationOfClosed K n (φ.comp (f.f n).hom) hpull a =
      evaluationOfClosed L n φ hφ ((HomologicalComplex.homologyMap f n).hom a) := by
  obtain ⟨c, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n a
  rw [evaluationOfClosed_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    evaluationOfClosed_cycleClass, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  rfl

end Wikipedia.HopfProblem.SingularCohomologyFree
