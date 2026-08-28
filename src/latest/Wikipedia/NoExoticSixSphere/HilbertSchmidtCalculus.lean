import Wikipedia.NoExoticSixSphere.HilbertSchmidt

/-!
# Differentiating the Hilbert--Schmidt form

The differentiation rules concern actual operator-valued curves and are proved
by applying the derivative to orthonormal basis vectors and summing.
-/

namespace NoExoticSixSphere.HilbertSchmidt

open GLOrthonormalization

variable {n : ℕ} {f g : ℝ → Vector n →L[ℝ] Vector n}
  {A B : Vector n →L[ℝ] Vector n} {t : ℝ}

theorem hasDerivAt_apply (hf : HasDerivAt f A t) (v : Vector n) :
    HasDerivAt (fun s ↦ f s v) (A v) t := by
  simpa only [map_zero, add_zero] using! hf.clm_apply (hasDerivAt_const t v)

theorem hasDerivAt_innerForm (hf : HasDerivAt f A t) (hg : HasDerivAt g B t) :
    HasDerivAt (fun s ↦ innerForm (f s) (g s))
      (innerForm (f t) B + innerForm A (g t)) t := by
  have hi (i : Fin n) :
      HasDerivAt (fun s ↦ inner ℝ (f s (EuclideanSpace.basisFun (Fin n) ℝ i))
        (g s (EuclideanSpace.basisFun (Fin n) ℝ i)))
        (inner ℝ (f t (EuclideanSpace.basisFun (Fin n) ℝ i))
          (B (EuclideanSpace.basisFun (Fin n) ℝ i)) +
        inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
          (g t (EuclideanSpace.basisFun (Fin n) ℝ i))) t :=
    (hasDerivAt_apply hf _).inner ℝ (hasDerivAt_apply hg _)
  simpa only [innerForm, Finset.sum_add_distrib] using!
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i))

theorem hasDerivAt_squareNorm (hf : HasDerivAt f A t) :
    HasDerivAt (fun s ↦ squareNorm (f s)) (2 * innerForm (f t) A) t := by
  have h := hasDerivAt_innerForm hf hf
  rw [innerForm_comm A (f t)] at h
  convert! h using 1
  ring

end NoExoticSixSphere.HilbertSchmidt
