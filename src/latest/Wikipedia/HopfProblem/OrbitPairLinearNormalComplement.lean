import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# An actual finite-dimensional normal complement

An injective operator admits complementary Euclidean columns of the
specified codimension. The columns are constructed from a complement of
its actual range. No inner product on the target model is required.
-/

noncomputable section

open Set Function Module

namespace Wikipedia.HopfProblem.OrbitPair.LinearNormal

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem exists_complement (A : E →L[ℝ] G) (hi : Injective A) (n : ℕ)
    (hdim : finrank ℝ E + n = finrank ℝ G) :
    ∃ B : EuclideanSpace ℝ (Fin n) →L[ℝ] G, Bijective (A.coprod B) := by
  obtain ⟨C, hC⟩ := A.range.exists_isCompl
  have hA : finrank ℝ A.range = finrank ℝ E := LinearMap.finrank_range_of_inj hi
  have hdimC : finrank ℝ C = n := by
    have hh := Submodule.finrank_add_eq_of_isCompl hC
    omega
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] C :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hdimC.symm)
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] G := C.subtypeL.comp e.toContinuousLinearMap
  have hsurj : Surjective (A.coprod B) := by
    intro w
    have hw : w ∈ A.range ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ⟨u, hu⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hw
    refine ⟨(u, e.symm ⟨b, hb⟩), ?_⟩
    change A u + (e (e.symm ⟨b, hb⟩) : G) = w
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change A u + b = w
    have hu' : A u = a := hu
    rw [hu']
    exact hab
  have htotal : finrank ℝ (E × EuclideanSpace ℝ (Fin n)) = finrank ℝ G := by
    rw [finrank_prod, finrank_euclideanSpace_fin]
    exact hdim
  exact ⟨B, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank htotal).mpr hsurj, hsurj⟩

end Wikipedia.HopfProblem.OrbitPair.LinearNormal
