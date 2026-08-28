import Wikipedia.NoExoticSixSphere.OrthogonalExponentialCoordinates

/-!
# A smooth local logarithm on the orthogonal group

The verified local inverse in Cayley coordinates is transferred back to the
original orthogonal manifold. The resulting inverse is local: no global or
continuously chosen logarithm of arbitrary orthogonal families is asserted.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere

open GLOrthonormalization CayleyTransform CayleyAtlas OrthogonalPaths

namespace CayleyAtlas

variable {n : ℕ}

theorem atOperator_target (a : OrthogonalOperators n) : (atOperator a).target = univ := by
  ext K
  change (K ∈ univ ∧ orthogonal K ∈ univ) ↔ K ∈ univ
  simp only [mem_univ, and_self]

/-- The same Cayley chart, with its verified smooth maps, as a partial diffeomorphism. -/
noncomputable def partialChart (a : OrthogonalOperators n) :
    PartialDiffeomorph 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, SkewOperators n)
      (OrthogonalOperators n) (SkewOperators n) ∞ where
  toPartialEquiv := (atOperator a).toPartialEquiv
  open_source := (atOperator a).open_source
  open_target := (atOperator a).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

theorem partialChart_one_apply (a : OrthogonalOperators n) :
    partialChart (1 : OrthogonalOperators n) a = CayleyTransform.chart a := by
  change coordinates (mul (inverse (identity n)) a) = coordinates a
  rw [inverse_identity, identity_mul]

end CayleyAtlas

namespace OrthogonalExponential

variable {n : ℕ}

/-- The actual exponential is a local diffeomorphism at zero. -/
theorem isLocalDiffeomorphAt_exp_zero :
    IsLocalDiffeomorphAt 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, SkewOperators n) ∞
      (exp (n := n)) 0 := by
  obtain ⟨d, hd0, hdU, hdf⟩ := exists_coordinatePartialDiffeomorph (n := n)
  let c := partialChart (1 : OrthogonalOperators n)
  refine ⟨d.trans c.symm, ?_, ?_⟩
  · refine ⟨hd0, ?_⟩
    change d 0 ∈ (atOperator (1 : OrthogonalOperators n)).target
    rw [atOperator_target]
    exact mem_univ _
  · intro K hK
    have hKU := hdU hK.1
    have hce : c (exp K) = d K := by
      rw [hdf]
      exact (partialChart_one_apply (exp K)).trans (inCoordinates_eq_chart K hKU).symm
    have hsource : exp K ∈ c.source := by
      change exp K ∈ (atOperator (1 : OrthogonalOperators n)).source
      rw [atOperator_source]
      change mul (inverse (identity n)) (exp K) ∈ domain
      rw [inverse_identity, identity_mul]
      exact hKU
    change exp K = c.symm (d K)
    rw [← hce]
    exact (c.left_inv' hsource).symm

/-- A native smooth partial logarithm, defined on a neighborhood of the identity. -/
noncomputable def logarithmChart (n : ℕ) :
    PartialDiffeomorph 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, SkewOperators n)
      (OrthogonalOperators n) (SkewOperators n) ∞ :=
  (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse

theorem one_mem_logarithmChart_source (n : ℕ) :
    1 ∈ (logarithmChart n).source := by
  have h : exp (0 : SkewOperators n) ∈ (logarithmChart n).source :=
    (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse_mem_source
  rwa [exp_zero] at h

theorem zero_mem_logarithmChart_target (n : ℕ) :
    0 ∈ (logarithmChart n).target :=
  (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse_mem_target

theorem exp_logarithmChart (a : OrthogonalOperators n) (ha : a ∈ (logarithmChart n).source) :
    exp (logarithmChart n a) = a :=
  (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse_right_inv ha

theorem logarithmChart_exp (K : SkewOperators n) (hK : K ∈ (logarithmChart n).target) :
    logarithmChart n (exp K) = K :=
  (isLocalDiffeomorphAt_exp_zero (n := n)).localInverse_left_inv hK

theorem logarithmChart_one (n : ℕ) : logarithmChart n 1 = 0 := by
  simpa only [exp_zero] using logarithmChart_exp (0 : SkewOperators n)
    (zero_mem_logarithmChart_target n)

end OrthogonalExponential

end NoExoticSixSphere
