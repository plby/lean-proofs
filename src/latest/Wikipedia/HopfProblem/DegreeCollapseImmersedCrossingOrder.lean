import Wikipedia.HopfProblem.DegreeCollapseImmersedCornerOrientation
import Wikipedia.HopfProblem.OrbitPairOddSheetSwapDeterminant

/-!
# Choose the original three-dimensional branch ordering before joining arcs

Interchanging the two original source preimages reverses the ordered
crossing sign in dimension three. Thus a selected transverse crossing can
be ordered with either prescribed sign. This choice precedes construction
of the source arcs, patches, strips, and the embedded bigon; none of those
geometric objects is silently reordered afterward.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner

open OrbitPair.DeterminantSignCover

variable {G E M N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, G) N))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (K : (G × G) ≃L[ℝ] E)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, G) ∞ N] in
theorem originalJointFrame_det_swap (hdim : Module.finrank ℝ G = 3)
    (F : N → M) (x y : N) :
    (originalJointFrame K F y x).det = -(originalJointFrame K F x y).det := by
  let DX : G →L[ℝ] E := mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x
  let DY : G →L[ℝ] E := mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y
  change (K.symm.toContinuousLinearMap.comp (DX.coprod DY)).det =
    -(K.symm.toContinuousLinearMap.comp (DY.coprod DX)).det
  have he := OrbitPair.SheetOrder.det_coprod_swap (E := G) (V := E) DY DX K
  have hp : (-1 : ℝ) ^ 3 = -1 := by norm_num
  rw [hdim, hp, neg_one_mul] at he
  exact he

theorem intersectionSign_swap (hdim : Module.finrank ℝ G = 3)
    {F : N → M} {x y : N} (hxy : F x = F y)
    (ht : Surjective ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y).coprod
      (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))) :
    intersectionSign oN oM K F y x = !(intersectionSign oN oM K F x y) := by
  unfold intersectionSign intersectionBit
  rw [originalJointFrame_det_swap K hdim, ← hxy,
    Bool.xor_comm (oN.rawSign x) (oN.rawSign y),
    action_neg _ (originalJointFrame_det_ne_zero K ht)]

theorem exists_ordering_with_sign (hdim : Module.finrank ℝ G = 3)
    {F : N → M} {x y : N} (hxy : F x = F y)
    (ht : Surjective ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y).coprod
      (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))) (desired : Bool) :
    ∃ u v : N, ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∧
      intersectionSign oN oM K F u v = desired := by
  by_cases hs : intersectionSign oN oM K F x y = desired
  · exact ⟨x, y, Or.inl ⟨rfl, rfl⟩, hs⟩
  · refine ⟨y, x, Or.inr ⟨rfl, rfl⟩, ?_⟩
    rw [intersectionSign_swap oN oM K hdim hxy ht]
    cases hh : intersectionSign oN oM K F x y <;> cases desired <;> simp_all

theorem exists_ordering_with_opposite_sign (hdim : Module.finrank ℝ G = 3)
    {F : N → M} (x₀ y₀ : N) {x₁ y₁ : N} (hxy : F x₁ = F y₁)
    (ht : Surjective ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y₁).coprod
      (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x₁))) :
    ∃ u v : N, ((u = x₁ ∧ v = y₁) ∨ (u = y₁ ∧ v = x₁)) ∧
      intersectionSign oN oM K F x₀ y₀ ≠ intersectionSign oN oM K F u v := by
  obtain ⟨u, v, huv, hs⟩ := exists_ordering_with_sign oN oM K hdim hxy ht
    (!(intersectionSign oN oM K F x₀ y₀))
  refine ⟨u, v, huv, ?_⟩
  rw [hs]
  cases intersectionSign oN oM K F x₀ y₀ <;> decide

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner
