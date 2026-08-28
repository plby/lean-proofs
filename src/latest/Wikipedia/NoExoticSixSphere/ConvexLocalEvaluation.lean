import Wikipedia.NoExoticSixSphere.ConvexExteriorHomology
import Wikipedia.NoExoticSixSphere.SupportedEvaluationTransport
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual point evaluation on compact convex supports

The constructed complement homotopy proves the evaluation isomorphism for
a bounded convex support containing zero. Translating the actual support
then proves bijectivity at every point of any compact convex subset. The
map is the original restriction to singleton support, in every degree.
-/

noncomputable section

open CategoryTheory Metric
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.ConvexLocalHomology

open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem point_mapsTo (K : Set E) (x : E) (hx : x ∈ K) :
    Set.MapsTo (ContinuousMap.id E) Kᶜ ({x}ᶜ : Set E) := by
  intro y hy
  change y ≠ x
  exact fun he => hy (he.symm ▸ hx)

omit [NormedSpace ℝ E] in
theorem restrictedPointMap_eq (K : Set E) (x : E) (hx : x ∈ K) :
    RelativeSingularHomology.restrictedMap (ContinuousMap.id E) (point_mapsTo K x hx) =
      ConvexExterior.toPointPuncture K x hx := by
  ext y
  rfl

/-- The original integral evaluation is a quasi-isomorphism. -/
theorem evaluationChain_zero_mem_quasiIso (K : Set E) (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (r : ℝ) (hr : 0 < r) (hB : ∀ y ∈ K, ‖y‖ < r) (x : E) (hx : x ∈ K) :
    QuasiIso (RelativeSingularHomology.mapChain (ContinuousMap.id E) (point_mapsTo K x hx)) := by
  have h₁ : QuasiIso (singularChainMap
      (RelativeSingularHomology.restrictedMap (ContinuousMap.id E) (point_mapsTo K x hx))) := by
    rw [restrictedPointMap_eq K x hx]
    exact ConvexExterior.toPointPuncture_quasiIso K hK h0 r hr hB x hx
  have h₂ : QuasiIso (singularChainMap (ContinuousMap.id E)) := by
    rw [RelativeSingularHomology.chainMap_id]
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (RelativeSingularHomology.sequenceMap (ContinuousMap.id E) (point_mapsTo K x hx))
    (RelativeSingularHomology.sequence_shortExact Kᶜ)
    (RelativeSingularHomology.sequence_shortExact ({x}ᶜ : Set E)) h₁ h₂

theorem restrictChain_zero_mem_quasiIso (p : ℕ) (hp : p ≠ 0) (K : Set E) (hK : Convex ℝ K)
    (h0 : (0 : E) ∈ K) (r : ℝ) (hr : 0 < r) (hB : ∀ y ∈ K, ‖y‖ < r) (x : E) (hx : x ∈ K) :
    QuasiIso (restrictChain (ModuleCat.of ℤ (ZMod p)) (Set.singleton_subset_iff.mpr hx)) :=
  RelativeCoefficients.mapChain_mod_quasiIso_of_integral p hp (ContinuousMap.id E)
    (point_mapsTo K x hx) (evaluationChain_zero_mem_quasiIso K hK h0 r hr hB x hx)

theorem evaluate_zero_mem_bijective (p : ℕ) (hp : p ≠ 0) (K : Set E) (hK : Convex ℝ K)
    (h0 : (0 : E) ∈ K) (r : ℝ) (hr : 0 < r) (hB : ∀ y ∈ K, ‖y‖ < r)
    (x : E) (hx : x ∈ K) (n : ℕ) :
    Function.Bijective (evaluate (ModuleCat.of ℤ (ZMod p)) K x hx n) := by
  let := restrictChain_zero_mem_quasiIso p hp K hK h0 r hr hB x hx
  exact (isoOfQuasiIsoAt (restrictChain (ModuleCat.of ℤ (ZMod p))
    (Set.singleton_subset_iff.mpr hx)) n).toLinearEquiv.bijective

/-- Every evaluation on a compact convex support is bijective, including at boundary points. -/
theorem evaluate_bijective (p : ℕ) (hp : p ≠ 0) (K : Set E) (hK : IsCompact K)
    (hC : Convex ℝ K) (x : E) (hx : x ∈ K) (n : ℕ) :
    Function.Bijective (evaluate (ModuleCat.of ℤ (ZMod p)) K x hx n) := by
  let h := Homeomorph.subRight x
  let L := h '' K
  have hL : IsCompact L := hK.image h.continuous
  have hLC : Convex ℝ L := by
    change Convex ℝ ((fun y : E => y - x) '' K)
    simpa only [sub_eq_add_neg, add_comm] using hC.translate (-x)
  have hL0 : (0 : E) ∈ L := ⟨x, hx, sub_self x⟩
  have hKL : ∀ y, y ∈ K ↔ h y ∈ L := by
    intro y
    constructor
    · exact fun hy => ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, he⟩
      exact h.injective he ▸ hz
  obtain ⟨r, hr, hB⟩ := hL.isBounded.exists_pos_norm_lt
  exact (evaluate_bijective_iff_homeomorph (ModuleCat.of ℤ (ZMod p)) h hKL x hx n).mp
    (evaluate_zero_mem_bijective p hp L hLC hL0 r hr hB (h x) ((hKL x).mp hx) n)

/-- The actual compact-support evaluation map, bundled as a linear equivalence. -/
def evaluateEquiv (p : ℕ) (hp : p ≠ 0) (K : Set E) (hK : IsCompact K) (hC : Convex ℝ K)
    (x : E) (hx : x ∈ K) (n : ℕ) :
    Homology (ModuleCat.of ℤ (ZMod p)) K n ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p ({x}ᶜ : Set E) n :=
  LinearEquiv.ofBijective (evaluate (ModuleCat.of ℤ (ZMod p)) K x hx n)
    (evaluate_bijective p hp K hK hC x hx n)

theorem evaluateEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (K : Set E) (hK : IsCompact K)
    (hC : Convex ℝ K) (x : E) (hx : x ∈ K) (n : ℕ) :
    (evaluateEquiv p hp K hK hC x hx n).toLinearMap =
      evaluate (ModuleCat.of ℤ (ZMod p)) K x hx n := rfl

end NoExoticSixSphere.ConvexLocalHomology
