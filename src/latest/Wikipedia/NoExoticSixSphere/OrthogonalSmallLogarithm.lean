import Wikipedia.NoExoticSixSphere.OrthogonalExponentialSubdivision

/-!
# Uniformly small logarithms on a compact path subdivision

The actual local logarithm tends to zero at the identity. Subdivision can
therefore ensure any prescribed positive bound on every logarithmic prefix,
uniformly over the compact parameter space. In particular one can arrange
the short-generator hypothesis used in the energy comparison.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalExponential

open GLOrthonormalization CayleyTransform

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem smallLogarithm_mem_nhds {ε : ℝ} (hε : 0 < ε) :
    {a : OrthogonalOperators n | a ∈ (logarithmChart n).source ∧
      ‖logarithmChart n a‖ < ε} ∈ nhds (1 : OrthogonalOperators n) := by
  have hs := (logarithmChart n).open_source.mem_nhds (one_mem_logarithmChart_source n)
  have hc : ContinuousAt (logarithmChart n) (1 : OrthogonalOperators n) :=
    (logarithmChart n).contMDiffOn_toFun.continuousOn.continuousAt hs
  have hn : ‖logarithmChart n (1 : OrthogonalOperators n)‖ < ε := by
    rw [logarithmChart_one, norm_zero]
    exact hε
  have he := Filter.Tendsto.eventually hc.norm (gt_mem_nhds hn)
  filter_upwards [hs, he] with a ha hnorm
  exact ⟨ha, hnorm⟩

theorem exists_smallLogarithmSubdivision [CompactSpace X]
    (H : C(I × X, OrthogonalOperators n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ i ≥ N, t i = 1) ∧
      ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
        (H (t i, x))⁻¹ * H (u, x) ∈ (logarithmChart n).source ∧
          ‖logarithmChart n ((H (t i, x))⁻¹ * H (u, x))‖ < ε :=
  exists_incrementSubdivision H _ (smallLogarithm_mem_nhds hε)

end NoExoticSixSphere.OrthogonalExponential
