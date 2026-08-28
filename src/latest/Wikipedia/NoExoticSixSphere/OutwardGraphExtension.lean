import Wikipedia.NoExoticSixSphere.OutwardGraphStabilization

/-!
# The outward boundary operator has exactly the original extension obstruction

Combine the explicit six-axis stabilization with the two continuous
injective-operator homotopies. The resulting equivalence holds in both
directions for the actual operator maps. It does not assume that an
immersed disk or an extension of the outward normal exists.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.OutwardGraphFrame

open GLOrthonormalization Stiefel CollaredDiskFrame DiskBoundary

variable {N k : ℕ}

theorem coprod_injective_of_operator (P : Monomorphism.Space N (k + 4))
    (A : Vector k →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] Vector N)
    (hP : P.val = OperatorSum.operator A D) : Injective (A.coprod D) := by
  intro u v huv
  apply (EuclideanSpace.finAddEquivProd (n := k) (m := 4)).symm.injective
  apply P.property
  rw [hP]
  change (A.coprod D) (EuclideanSpace.finAddEquivProd
      (EuclideanSpace.finAddEquivProd.symm u)) =
    (A.coprod D) (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm v))
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using huv

theorem extends_outward_iff (hN : N = 3 + (k + 4))
    (A : C(Sphere 3, Vector k →L[ℝ] Vector N))
    (D : C(Sphere 3, Vector 4 →L[ℝ] Vector N))
    (ν : C(Sphere 3, Vector N)) (ξ : C(Sphere 3, Vector N →L[ℝ] ℝ))
    (P : C(Sphere 3, Monomorphism.Space N (k + 4)))
    (G : C(Sphere 3, Monomorphism.Space (N + 6) (((k + 1) + 5) + 4)))
    (hP : ∀ s, (P s).val = OperatorSum.operator (A s) (D s))
    (hG : ∀ s, (G s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp
        (OrthogonalFrameAppend.operator (A s) (ν s))) (graph (D s) (ξ s)))
    (hA : ∀ s u, ξ s (A s u) = 0) (hν : ∀ s, ξ s (ν s) < 0) :
    Extends G ↔ Extends P := by
  have hAD : ∀ s, Injective ((A s).coprod (D s)) :=
    fun s ↦ coprod_injective_of_operator (P s) (A s) (D s) (hP s)
  have H := homotopic_plain_to_outward A D ν ξ hAD hA hν
    (plainStabilization.comp P) G
    (fun s ↦ plainStabilization_operator (P s) (A s) (D s) (ν s) (hP s)) hG
  exact (extends_homotopic_iff H).symm.trans (extends_plainStabilization_iff hN P)

end NoExoticSixSphere.OutwardGraphFrame
