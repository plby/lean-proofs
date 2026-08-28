import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRegular
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRamification
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovableFilters

/-!
# Actual elliptic growth of descended differential coefficients

The finite source coordinate has its proved branching orders three and
four. Its inverse logarithmic derivative therefore tends to zero at
either elliptic centre. Applying the exact punctured-neighbourhood image
theorem transfers this limit to the genuine descended coefficients.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle
open TriangleHolomorphicDifferentialsRemovable

/-- The genuine coefficient of a descended `p`-fold differential on the
regular finite base. Its two exceptional values are not prescribed here. -/
def differentialDescent (p : ℕ) (A : ℍ → ℂ) : ℂ → ℂ :=
  regularScalarDescent (fun z => A z / scalarDeriv specialSourceCoordinate z ^ p)

theorem differentialDescent_projection {p : ℕ} {A : ℍ → ℂ}
    (hA : IsInvariantDifferential p A) {z : ℍ} (hz : z ∈ triangleRegularLocus) :
    differentialDescent p A (specialSourceCoordinate z) =
      A z / scalarDeriv specialSourceCoordinate z ^ p :=
  regularScalarDescent_projection _ (fun g w _ => differentialRatio_invariant hA g w) hz

theorem differentialDescent_analytic {p : ℕ} {A : ℍ → ℂ}
    (hInv : IsInvariantDifferential p A) (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A)
    {t : ℂ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    AnalyticAt ℂ (differentialDescent p A) t :=
  regularScalarDescent_analytic _ (fun g w _ => differentialRatio_invariant hInv g w)
    (differentialRatio_holomorphic hA) ht0 ht1

theorem specialSourceCoordinate_complex_analyticAt (a : ℍ) :
    AnalyticAt ℂ (specialSourceCoordinate ∘ ofComplex) (a : ℂ) :=
  MuTorsor.SourceOrders.finiteProjection_analyticAt triangleSphereUniformization
    triangleSphereUniformization_cusp a

/-- The actual normalized finite coordinate has the computed elliptic
branching order, including the normalization of its central value. -/
theorem specialSourceCoordinate_centered_order (j : Elliptic.Kind) :
    analyticOrderAt (fun w : ℂ => specialSourceCoordinate (ofComplex w) -
      specialSourceCoordinate (ellipticCenter j)) (ellipticCenter j : ℂ) =
        (j.order : ℕ∞) :=
  MuTorsor.SourceOrders.finiteProjection_centered_order_center
    triangleSphereUniformization triangleSphereUniformization_cusp j

theorem specialSourceCoordinate_centered_order_ne_top (j : Elliptic.Kind) :
    analyticOrderAt (fun w : ℂ =>
      (specialSourceCoordinate ∘ ofComplex) w -
        (specialSourceCoordinate ∘ ofComplex) (ellipticCenter j : ℂ))
      (ellipticCenter j : ℂ) ≠ ⊤ := by
  simp only [Function.comp_apply, ofComplex_apply, specialSourceCoordinate_centered_order]
  exact ENat.natCast_ne_top _

/-- The actual branched source coordinate maps punctured neighbourhoods
exactly onto punctured neighbourhoods of the indicated marked value. -/
theorem specialSourceCoordinate_map_nhdsNE_elliptic (j : Elliptic.Kind) :
    Filter.map (specialSourceCoordinate ∘ ofComplex) (𝓝[≠] (ellipticCenter j : ℂ)) =
      𝓝[≠] (specialSourceCoordinate (ellipticCenter j)) := by
  simpa only [Function.comp_apply, ofComplex_apply] using
    map_nhdsNE_eq_of_finite_order
      (specialSourceCoordinate_complex_analyticAt (ellipticCenter j))
      (specialSourceCoordinate_centered_order_ne_top j)

/-- Away from the centre, a sufficiently small actual elliptic
neighbourhood lies in the regular locus. -/
theorem eventually_regular_near_elliptic (j : Elliptic.Kind) :
    ∀ᶠ w : ℂ in 𝓝[≠] (ellipticCenter j : ℂ),
      ofComplex w ∈ triangleRegularLocus := by
  have htarget : ∀ᶠ t : ℂ in 𝓝[≠] (specialSourceCoordinate (ellipticCenter j)),
      t ≠ 0 ∧ t ≠ 1 := by
    cases j with
    | three =>
      simp only [ellipticCenter, specialSourceCoordinate_centerOne]
      filter_upwards [self_mem_nhdsWithin,
        eventually_ne_nhdsWithin (by norm_num : (0 : ℂ) ≠ 1)] with t ht0 ht1
      exact ⟨ht0, ht1⟩
    | four =>
      simp only [ellipticCenter, specialSourceCoordinate_centerTwo]
      filter_upwards [self_mem_nhdsWithin,
        eventually_ne_nhdsWithin (by norm_num : (1 : ℂ) ≠ 0)] with t ht1 ht0
      exact ⟨ht0, ht1⟩
  rw [← specialSourceCoordinate_map_nhdsNE_elliptic j] at htarget
  filter_upwards [htarget] with w hw
  exact (specialSourceCoordinate_regular_iff (ofComplex w)).mpr hw

theorem specialSourceCoordinate_ramificationRatio_tendsto_zero (j : Elliptic.Kind) :
    Tendsto (fun w : ℂ =>
      (specialSourceCoordinate (ofComplex w) - specialSourceCoordinate (ellipticCenter j)) /
        deriv (specialSourceCoordinate ∘ ofComplex) w)
      (𝓝[≠] (ellipticCenter j : ℂ)) (𝓝 0) := by
  have ho : analyticOrderAt (fun w : ℂ =>
      (specialSourceCoordinate ∘ ofComplex) w -
        (specialSourceCoordinate ∘ ofComplex) (ellipticCenter j : ℂ))
      (ellipticCenter j : ℂ) = (j.order : ℕ∞) := by
    simpa only [Function.comp_apply, ofComplex_apply] using
      specialSourceCoordinate_centered_order j
  simpa only [Function.comp_apply, ofComplex_apply] using
    ramificationRatio_tendsto_zero
      (specialSourceCoordinate_complex_analyticAt (ellipticCenter j)) j.order_pos ho

/-- An invariant `p`-fold holomorphic differential has downstairs growth
strictly smaller than a pole of order `p` at either actual elliptic value.
The limit is derived through the actual branched coordinate. -/
theorem differentialDescent_elliptic_growth {p : ℕ} {A : ℍ → ℂ}
    (hp : 0 < p) (hInv : IsInvariantDifferential p A)
    (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A) (j : Elliptic.Kind) :
    Tendsto (fun t : ℂ =>
      (t - specialSourceCoordinate (ellipticCenter j)) ^ p * differentialDescent p A t)
      (𝓝[≠] (specialSourceCoordinate (ellipticCenter j))) (𝓝 0) := by
  let a : ℍ := ellipticCenter j
  let P : ℂ → ℂ := specialSourceCoordinate ∘ ofComplex
  have hA' : AnalyticAt ℂ (A ∘ ofComplex) (a : ℂ) :=
    ((hA (ofComplex (a : ℂ))).comp (a : ℂ)
      (contMDiffAt_ofComplex a.im_pos)).contDiffAt.analyticAt
  have htA : Tendsto (A ∘ ofComplex) (𝓝[≠] (a : ℂ)) (𝓝 (A a)) := by
    simpa only [Function.comp_apply, ofComplex_apply] using
      hA'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := ((specialSourceCoordinate_ramificationRatio_tendsto_zero j).pow p).mul htA
  have hzero : (0 : ℂ) ^ p * A a = 0 := by simp [Nat.ne_of_gt hp]
  rw [hzero] at ht
  have he : (fun w : ℂ =>
      (P w - specialSourceCoordinate a) ^ p * differentialDescent p A (P w)) =ᶠ[𝓝[≠] (a : ℂ)]
        (fun w : ℂ =>
          ((P w - specialSourceCoordinate a) / deriv P w) ^ p * A (ofComplex w)) := by
    filter_upwards [eventually_regular_near_elliptic j,
      (eventuallyEq_coe_comp_ofComplex a.im_pos).filter_mono nhdsWithin_le_nhds] with w hw hcoe
    change (specialSourceCoordinate (ofComplex w) - specialSourceCoordinate a) ^ p *
      differentialDescent p A (specialSourceCoordinate (ofComplex w)) = _
    rw [differentialDescent_projection hInv hw]
    have hd : scalarDeriv specialSourceCoordinate (ofComplex w) = deriv P w := by
      change deriv P ((ofComplex w : ℍ) : ℂ) = deriv P w
      exact congrArg (deriv P) hcoe
    rw [hd]
    dsimp only [P, Function.comp_apply]
    rw [div_pow]
    ring
  have hcomp : Tendsto (fun w : ℂ =>
      (P w - specialSourceCoordinate a) ^ p * differentialDescent p A (P w))
      (𝓝[≠] (a : ℂ)) (𝓝 0) := ht.congr' he.symm
  have hmap : Tendsto (fun t : ℂ =>
      (t - specialSourceCoordinate a) ^ p * differentialDescent p A t)
      (Filter.map P (𝓝[≠] (a : ℂ))) (𝓝 0) := by
    simpa only [Filter.Tendsto, Filter.map_map, Function.comp_def] using hcomp
  rw [specialSourceCoordinate_map_nhdsNE_elliptic j] at hmap
  exact hmap

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
