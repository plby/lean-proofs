import Wikipedia.HopfProblem.SingularCohomologyCupCochainsDifferential
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# The actual integral cap operation and its evaluation identity

Use the original singular simplex generators with their front and back
faces, retaining integer coefficients. Evaluation against every integral
cochain identifies cap with the already constructed Alexander--Whitney
cup product. The actual simplex basis makes these evaluations separate
chains, allowing the signed differential identity to be proved by duality.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCap

open FirstHurewicz SingularCohomologyCup

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def capInDegree {p q n : ℕ} (h : p + q = n) (α : Cochain X p) :
    Chains X n →ₗ[ℤ] Chains X q :=
  chainLift X n fun σ ↦
    α (simplexChain X p (σ.comp (windowFace 0 p n (by omega)))) •
      simplexChain X q (σ.comp (windowFace p q n (by omega)))

theorem capInDegree_simplex {p q n : ℕ} (h : p + q = n) (α : Cochain X p)
    (σ : SingularSimplex X n) :
    capInDegree h α (simplexChain X n σ) =
      α (simplexChain X p (σ.comp (windowFace 0 p n (by omega)))) •
        simplexChain X q (σ.comp (windowFace p q n (by omega))) :=
  chainLift_simplex X n _ σ

theorem capInDegree_zero {p q n : ℕ} (h : p + q = n) :
    capInDegree (X := X) h (0 : Cochain X p) = 0 := by
  apply chainMap_ext X n
  intro σ
  simp only [capInDegree_simplex, LinearMap.zero_apply, zero_smul]

theorem capInDegree_add {p q n : ℕ} (h : p + q = n) (α β : Cochain X p) :
    capInDegree h (α + β) = capInDegree h α + capInDegree h β := by
  apply chainMap_ext X n
  intro σ
  simp only [capInDegree_simplex, LinearMap.add_apply, add_zsmul]

/-- This equality evaluates the original chains and the actual cup cochain. -/
theorem evaluate_cap {p q n : ℕ} (h : p + q = n) (α : Cochain X p) (β : Cochain X q)
    (c : Chains X n) : β (capInDegree h α c) = cupInDegree h α β c := by
  have he : β.comp (capInDegree h α) = cupInDegree h α β := by
    apply chainMap_ext X n
    intro σ
    rw [LinearMap.comp_apply, capInDegree_simplex, cupInDegree_simplex, map_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id]
  exact LinearMap.congr_fun he c

theorem chain_eq_of_evaluation (n : ℕ) (c d : Chains X n)
    (h : ∀ α : Cochain X n, α c = α d) : c = d := by
  apply (chainBasis X n).repr.injective
  ext σ
  exact h ((chainBasis X n).coord σ)

/-- The actual cap operation respects the actual singular chain map. -/
theorem naturality {p q n : ℕ} (h : p + q = n) (f : C(X, Y)) (α : Cochain Y p)
    (c : Chains X n) :
    inducedChain f q (capInDegree h (pullback f p α) c) = capInDegree h α (inducedChain f n c) := by
  have he : (inducedChain f q).comp (capInDegree h (pullback f p α)) =
      (capInDegree h α).comp (inducedChain f n) := by
    apply chainMap_ext X n
    intro σ
    simp only [LinearMap.comp_apply, capInDegree_simplex, inducedChain_simplex,
      pullback_simplex, map_zsmul, ContinuousMap.comp_assoc]
  exact LinearMap.congr_fun he c

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCap
