import Wikipedia.SmoothSixDPoincare.NativeTransversalityStability

/-!
# Transversality through a native partial diffeomorphism

The actual derivative is a linear equivalence between the original native
tangent spaces. Thus postcomposition preserves and reflects the tangent
sum condition at an actual crossing, with neither manifold replaced by a
vector-space model.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B Z E HA HB HZ HE X Y N M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace HA] [TopologicalSpace HB] [TopologicalSpace HZ] [TopologicalSpace HE]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  {J : ModelWithCorners ℝ Z HZ} {J' : ModelWithCorners ℝ E HE}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
  [TopologicalSpace N] [ChartedSpace HZ N] [TopologicalSpace M] [ChartedSpace HE M]

theorem native_transversality_partial_diffeomorph_iff
    (P : PartialDiffeomorph J J' N M ∞) {f : X → N} {g : Y → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hxy : g y = f x) (hx : f x ∈ P.source) :
    NativeTransversality.At I I' J f g x y ↔
      NativeTransversality.At I I' J' (P ∘ f) (P ∘ g) x y := by
  let L : A →L[ℝ] Z := mfderiv I J f x
  let R : B →L[ℝ] Z := mfderiv I' J g y
  let C : Z →L[ℝ] E := mfderiv J J' P (f x)
  have hy : g y ∈ P.source := hxy ▸ hx
  have hL : (mfderiv I J' (P ∘ f) x : A →L[ℝ] E) = C.comp L :=
    mfderiv_comp x (P.mdifferentiableAt (by simp) hx) hf
  have hR : (mfderiv I' J' (P ∘ g) y : B →L[ℝ] E) = C.comp R := by
    rw [mfderiv_comp y (P.mdifferentiableAt (by simp) hy) hg, hxy]
    rfl
  have hC : Bijective C := PartialChart.bijective_mfderiv P hx
  constructor
  · intro ht _
    have hsum : Surjective (L.coprod R) := ht hxy
    rw [hL, hR]
    intro w
    obtain ⟨z, hz⟩ := hC.surjective w
    obtain ⟨v, hv⟩ := hsum z
    refine ⟨v, ?_⟩
    change C (L v.1) + C (R v.2) = w
    rw [← C.map_add]
    exact (congrArg C hv).trans hz
  · intro ht _
    have hsum := ht (show (P ∘ g) y = (P ∘ f) x from congrArg P hxy)
    rw [hL, hR] at hsum
    intro w
    obtain ⟨v, hv⟩ := hsum (C w)
    refine ⟨v, hC.injective ?_⟩
    change C (L v.1 + R v.2) = C w
    rw [C.map_add]
    exact hv

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
