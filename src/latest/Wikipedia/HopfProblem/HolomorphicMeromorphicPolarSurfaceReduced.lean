import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarSurfaceReducedIsolation
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarReduced

/-!
# Reduced pairs in original holomorphic surface stalks

The actual centered chart equivalence transports the analytic reduced-pair
theorem into the original categorical holomorphic stalk. Its cancellation
law and representative-independent isolated common zero are both retained.
In particular, the neighborhood conclusion concerns arbitrary native local
holomorphic representatives and the original manifold topology.
-/

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSurfaceReduced

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- Every fraction pair in an original complex-surface holomorphic stalk has
a reduced pair whose arbitrary native representatives have isolated common
zero at the base point. -/
theorem exists_reduced_pair (e : (ℂ × ℂ) ≃L[ℂ] E) (x : M)
    (p q : HolomorphicStalk I M x) (hq : q ≠ 0) :
    ∃ a b : HolomorphicStalk I M x, b ≠ 0 ∧ p * b = q * a ∧
      (∀ h : HolomorphicStalk I M x, b ∣ h * a ↔ b ∣ h) ∧
      NativeIsolatedCommonZero I M x a b := by
  let T := PolarStalk.surfaceStalkEquiv I M e x
  obtain ⟨a, b, hb, hpq, hcancel, hisolated⟩ :=
    PolarReduced.exists_reduced_pair_data (T p) (T q) (T.map_ne_zero_iff.mpr hq)
  obtain ⟨hb', hpq', hcancel'⟩ :=
    PolarReduced.reduced_pair_relations_transport T p q a b hb hpq hcancel
  refine ⟨T.symm a, T.symm b, hb', hpq', hcancel', ?_⟩
  apply nativeIsolatedCommonZero_of_surfaceStalkEquiv I M e x
  change PolarReduced.IsolatedCommonZero (T (T.symm a)) (T (T.symm b))
  simpa only [RingEquiv.apply_symm_apply] using hisolated

/-- The same result with the conclusion for every native local representative
displayed explicitly, with no coherence or neighborhood-reduction premise. -/
theorem exists_reduced_pair_explicit (e : (ℂ × ℂ) ≃L[ℂ] E) (x : M)
    (p q : HolomorphicStalk I M x) (hq : q ≠ 0) :
    ∃ a b : HolomorphicStalk I M x, b ≠ 0 ∧ p * b = q * a ∧
      (∀ h : HolomorphicStalk I M x, b ∣ h * a ↔ b ∣ h) ∧
      ∀ (U : Opens M) (hx : x ∈ U) (A B : HolomorphicFunctionSheaf.Section I M U),
        (HolomorphicFunctionSheaf.presheaf I M).germ U x hx A = a →
        (HolomorphicFunctionSheaf.presheaf I M).germ U x hx B = b →
        ∀ᶠ y in 𝓝 x,
          HolomorphicFunctionSheaf.extendManifoldSection I U A y = 0 →
          HolomorphicFunctionSheaf.extendManifoldSection I U B y = 0 → y = x :=
  exists_reduced_pair I M e x p q hq

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSurfaceReduced
