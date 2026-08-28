import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsAlgebra

/-!
# Actual integral homology of finite products of circles

The actual circle-product Mayer--Vietoris equivalence is iterated along
the coordinate product homeomorphisms. It gives actual integral homology
equivalences with `Fin (r.choose n) → ℤ` in every degree. These coordinates
are recursively specified by projection and the signed connecting map.

This file computes groups and their recursive coordinates. It does not
identify them with the exterior-power marking or assert its naturality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

/-- The actual singular homology of an `r`-fold product of circles is free
of binomial rank. The equivalence is constructed recursively from the
proved circle-product Mayer--Vietoris equivalence. -/
def productTorusHomologyEquiv : (r n : ℕ) →
    SingularHomology (ProductTorus r) n ≃ₗ[ℤ] binomialModule r n
  | r, 0 =>
      (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r)
  | 0, n + 1 => by
      letI := totallyDisconnected_homology_subsingleton PUnit (n + 1) (Nat.succ_ne_zero n)
      exact (homeomorphHomologyEquiv productTorusZeroHomeomorph (n + 1)).trans
        (LinearEquiv.ofSubsingleton (SingularHomology PUnit (n + 1))
          (binomialModule 0 (n + 1)))
  | r + 1, n + 1 =>
      ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
        ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
          (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
            (productTorusHomologyEquiv r n).toAddEquiv).trans
              (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv

/-- Degree zero is identified by the actual augmentation. -/
@[simp] theorem productTorusHomologyEquiv_zero (r : ℕ) :
    productTorusHomologyEquiv r 0 =
      (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r) := by
  cases r <;> rfl

/-- The recursive equivalence uses the actual coordinate homeomorphism and
the actual circle-product homology equivalence, in that order. -/
theorem productTorusHomologyEquiv_succ (r n : ℕ) :
    productTorusHomologyEquiv (r + 1) (n + 1) =
      ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
        ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
          (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
            (productTorusHomologyEquiv r n).toAddEquiv).trans
              (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv := rfl

/-- The two recursively ordered blocks are exactly the projection and
signed connecting coordinates of the proved Mayer--Vietoris sequence. -/
theorem productTorusHomologyEquiv_succ_apply (r n : ℕ)
    (a : SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      (productTorusHomologyEquiv r (n + 1)
          (circleProjectionHomology (ProductTorus r) (n + 1)
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)),
        productTorusHomologyEquiv r n
          (circleBoundary (ProductTorus r) n
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a))) := by
  rw [productTorusHomologyEquiv_succ]
  change binomialModuleSuccEquiv r n ((binomialModuleSuccEquiv r n).symm
      (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
        (productTorusHomologyEquiv r n).toAddEquiv)
          (circleProductHomologyEquiv (ProductTorus r) n
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)))) = _
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_apply]
  rfl

theorem productTorus_homology_free (r n : ℕ) :
    Module.Free ℤ (SingularHomology (ProductTorus r) n) :=
  Module.Free.of_equiv (productTorusHomologyEquiv r n).symm

theorem productTorus_homology_finite (r n : ℕ) :
    Module.Finite ℤ (SingularHomology (ProductTorus r) n) :=
  Module.Finite.of_surjective (productTorusHomologyEquiv r n).symm.toLinearMap
    (productTorusHomologyEquiv r n).symm.surjective

/-- The actual integral Betti number of the finite product torus. -/
theorem productTorus_homology_finrank (r n : ℕ) :
    Module.finrank ℤ (SingularHomology (ProductTorus r) n) = r.choose n := by
  rw [(productTorusHomologyEquiv r n).finrank_eq]
  exact binomialModule_finrank r n

theorem productTorus_homology_torsionFree (r n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (ProductTorus r) n) := by
  let := productTorus_homology_free r n
  infer_instance

/-- Actual singular homology vanishes above the number of circle factors. -/
theorem productTorus_homology_subsingleton_of_lt {r n : ℕ} (h : r < n) :
    Subsingleton (SingularHomology (ProductTorus r) n) := by
  let := binomialModule_subsingleton_of_lt h
  exact (productTorusHomologyEquiv r n).injective.subsingleton

theorem productTorus_homology_isZero_of_lt {r n : ℕ} (h : r < n) :
    IsZero (SingularHomology (ProductTorus r) n) := by
  let := productTorus_homology_subsingleton_of_lt h
  exact ModuleCat.isZero_of_subsingleton _

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
