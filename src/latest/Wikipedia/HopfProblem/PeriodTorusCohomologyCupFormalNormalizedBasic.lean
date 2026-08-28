import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalBasic

/-!
# Normalized evaluations on ordered formal chains

A normalized cochain vanishes when two consecutive vertices coincide.
Contraction by an initial vertex preserves this property. These elementary
identities discard the degenerate cones in the original coned cross
product before any finite numerical expansion.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open SingularMayerVietoris

variable {V : Type*}

def IsNormalizedFormalCochain {n : ℕ} (f : (Fin (n + 2) → V) → ℤ) : Prop :=
  ∀ (v : Fin (n + 2) → V) (i : Fin (n + 1)),
    v i.castSucc = v i.succ → f v = 0

theorem IsNormalizedFormalCochain.first_repeat {n : ℕ}
    {f : (Fin (n + 2) → V) → ℤ} (hf : IsNormalizedFormalCochain f)
    (v : Fin (n + 1) → V) : f (Fin.cons (v 0) v) = 0 := by
  apply hf _ 0
  rfl

theorem IsNormalizedFormalCochain.cone {n : ℕ}
    {f : (Fin (n + 3) → V) → ℤ} (hf : IsNormalizedFormalCochain f) (a : V) :
    IsNormalizedFormalCochain (fun v : Fin (n + 2) → V => f (Fin.cons a v)) := by
  intro v i hi
  apply hf _ i.succ
  change v i.castSucc = v i.succ
  exact hi

/-- Coning a chain precomposes its evaluation with prepending one vertex. -/
theorem formalLift_cone_apply {n : ℕ} (f : (Fin (n + 1) → V) → ℤ)
    (a : V) (c : FormalChains V n) :
    formalLift f (formalCone a n c) =
      formalLift (fun v : Fin n → V => f (Fin.cons a v)) c := by
  have h : (formalLift f).comp (formalCone a n) =
      formalLift (fun v : Fin n → V => f (Fin.cons a v)) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalCone_simplex, formalLift_simplex]
  exact LinearMap.congr_fun h c

/-- A twice-repeated cone is killed by every normalized cochain. -/
theorem formalLift_doubleCone_eq_zero {n : ℕ}
    {f : (Fin (n + 2) → V) → ℤ} (hf : IsNormalizedFormalCochain f)
    (a : V) (c : FormalChains V n) :
    formalLift f (formalCone a (n + 1) (formalCone a n c)) = 0 := by
  have h : (formalLift f).comp ((formalCone a (n + 1)).comp (formalCone a n)) = 0 := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalCone_simplex, formalLift_simplex,
      LinearMap.zero_apply]
    apply hf _ 0
    rfl
  exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
