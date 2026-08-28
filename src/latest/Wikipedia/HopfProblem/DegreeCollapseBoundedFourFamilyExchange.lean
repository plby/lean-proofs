import Wikipedia.HopfProblem.DegreeCollapseBoundedCommonCutExchange
import Wikipedia.HopfProblem.DegreeCollapseFourNoConnections
import Wikipedia.HopfProblem.DegreeCollapseFourCommonCutFamily

/-!
# Bounded value exchange retaining the original four-handle family and matrix

The full original basin section excludes a connecting orbit. The actual
exchange fixes both outer germs and retains the identical complete flow.
Identity on the common native cut retains every source parameter, full
basin image, and matrix entry in the literally transported integral basis.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_bounded_four_family_value_exchange
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {a b : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    {r n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (hvalues : ∀ j, a < f (p j) ∧ f (p j) < b)
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (γ : Fin n → C(S₃, {y : M // f y = a}))
    (hγ : IsNativeFourBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Surjective (canonicalFourMatrix B γ).mulVec)
    (i j : Fin n) (hij : f (p i) < f (p j))
    (hconsecutive : ∀ z : criticalPoints E f, ¬(f (p i) < f z ∧ f z < f (p j))) :
    ∃ g : M → ℝ, ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
      IsMorse E g ∧ ∃ hcrit : criticalPoints E g = criticalPoints E f,
        InjOn g (criticalPoints E g) ∧ g (p i) = f (p j) ∧ g (p j) = f (p i) ∧
        (∀ z ∈ criticalPoints E f, z ≠ (p i).val → z ≠ (p j).val → g =ᶠ[𝓝 z] f) ∧
        (∀ z ∈ criticalPoints E f, nativeMorseIndex E g z = nativeMorseIndex E f z) ∧
        (∀ k, nativeMorseCount E g k = nativeMorseCount E f k) ∧
        ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
        (∀ y, g y < b ↔ f y < b) ∧ (∀ y, g y = b ↔ f y = b) ∧
        (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧ (∀ y, b ≤ f y → g =ᶠ[𝓝 y] f) ∧
        ∃ hga : ∀ y, g y = a → y ∉ criticalPoints E g,
        ∃ _hgb : ∀ y, g y = b → y ∉ criticalPoints E g,
        ∃ T : AdaptedSurgeryWindows E g, T.field = S.field ∧ T.flow = S.flow ∧
          let p' : Fin n → criticalPoints E g :=
            fun k => ⟨(p k).val, hcrit.symm ▸ (p k).property⟩
          let B' := B.trans (equalFourCutHomologyEquiv hsub)
          let γ' := fun k => equalFourCutSection hlevel (γ k)
          (∀ k, nativeMorseIndex E g (p' k) = 4) ∧
          (∀ k, a < T.toSurgeryWindows.lower (p' k)) ∧
          (∀ k, T.toSurgeryWindows.upper (p' k) < b) ∧
          IsNativeFourBasinFamily T hg hga p' (fun k => γ' k) ∧
          (∀ k x, (γ' k x).val = (γ k x).val) ∧
          canonicalFourMatrix B' γ' = canonicalFourMatrix B γ ∧
          Surjective (canonicalFourMatrix B' γ').mulVec := by
  have hnoconnection := S.no_connection_above_four_basin_cut hf (p i) (p j) hij
    (hp j) ha (hvalues i).1 (γ j) (hγ.2.2.2.2 j)
  obtain ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, hindices, hcounts,
      hsub, hlevel, hstrict, hlevelB, hlowgerm, huppergerm, hga, hgb,
      T, hfield, hflow, _, haboveA, hbelowB, _⟩ :=
    S.exists_bounded_common_cut_value_exchange hf hm ha hb (p i) (p j)
      (hvalues i).1 hij (hvalues j).2 hconsecutive hnoconnection
  have hinside (k : Fin n) : a < g (p k) ∧ g (p k) < b := by
    refine ⟨lt_of_not_ge (fun h => (hvalues k).1.not_ge ((hsub (p k)).mp h)), ?_⟩
    exact (hstrict (p k)).mpr (hvalues k).2
  have hmatrix := canonicalFourMatrix_equalCut hsub hlevel B γ
  refine ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, hindices, hcounts,
    hsub, hlevel, hstrict, hlevelB, hlowgerm, huppergerm, hga, hgb,
    T, hfield, hflow, ?_, ?_, ?_, ?_, ?_, hmatrix, ?_⟩
  · intro k
    exact (hindices (p k) (p k).property).trans (hp k)
  · intro k
    exact haboveA ⟨(p k).val, hcrit.symm ▸ (p k).property⟩ (hinside k).1
  · intro k
    exact hbelowB ⟨(p k).val, hcrit.symm ▸ (p k).property⟩ (hinside k).2
  · exact nativeFourBasinFamily_equalCut S T hf hg ha hga hcrit hlevel hflow p γ hγ
  · intro k x
    rfl
  · rw [hmatrix]
    exact hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
