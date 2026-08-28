import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Interior coordinates for a model with boundary

The model map restricted over an open subset of its range is a genuine
partial diffeomorphism. A smooth ball compression, followed by a linear
equivalence, embeds a full Euclidean model into the interior of any
equal-dimensional model with corners. This supplies a common chart model
for the interior and boundary pieces of a slab.
-/

open scoped Manifold ContDiff
open Set Metric

namespace NoExoticSixSphere

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  (I : ModelWithCorners ℝ B H)

noncomputable def modelInteriorPartialDiffeomorph (W : Set B) (hW : IsOpen W)
    (hWI : W ⊆ range I) : PartialDiffeomorph I 𝓘(ℝ, B) H B ∞ where
  toFun := I
  invFun := I.symm
  source := I ⁻¹' W
  target := W
  map_source' _ hx := hx
  map_target' y hy := by
    change I (I.symm y) ∈ W
    rwa [I.right_inv (hWI hy)]
  left_inv' x _ := I.left_inv x
  right_inv' _ hy := I.right_inv (hWI hy)
  open_source := hW.preimage I.continuous
  open_target := hW
  contMDiffOn_toFun := I.contMDiff.contMDiffOn
  contMDiffOn_invFun := I.contMDiffOn_symm.mono hWI

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem exists_fullSource_modelPartialDiffeomorph (L : K ≃L[ℝ] B) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, K) I K H ∞,
      Φ.source = univ ∧ ∀ y ∈ Φ.target, I y ∈ interior (range I) := by
  obtain ⟨y, hy⟩ := I.nonempty_interior
  have hW : IsOpen (L ⁻¹' interior (range I)) := isOpen_interior.preimage L.continuous
  have hx : L.symm y ∈ L ⁻¹' interior (range I) := by
    simpa only [mem_preimage, L.apply_symm_apply] using hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW (L.symm y) hx
  let q₀ := OpenPartialHomeomorph.univBall (L.symm y) r
  let q : PartialDiffeomorph 𝓘(ℝ, K) 𝓘(ℝ, K) K K ∞ :=
    { toPartialEquiv := q₀.toPartialEquiv
      open_source := q₀.open_source
      open_target := q₀.open_target
      contMDiffOn_toFun := OpenPartialHomeomorph.contDiff_univBall.contMDiff.contMDiffOn
      contMDiffOn_invFun := by
        change ContMDiffOn 𝓘(ℝ, K) 𝓘(ℝ, K) ∞ q₀.symm q₀.target
        rw [OpenPartialHomeomorph.univBall_target _ hr]
        exact OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn }
  let c := (modelInteriorPartialDiffeomorph I (interior (range I))
    isOpen_interior interior_subset).symm
  refine ⟨(q.trans L.toDiffeomorph.toPartialDiffeomorph).trans c, ?_, ?_⟩
  · apply eq_univ_of_forall
    intro z
    have hz : z ∈ q.source := by
      change z ∈ q₀.source
      rw [OpenPartialHomeomorph.univBall_source]
      trivial
    refine ⟨⟨hz, mem_univ _⟩, ?_⟩
    apply hball
    have hq := q.map_source' hz
    change q₀ z ∈ q₀.target at hq
    rwa [OpenPartialHomeomorph.univBall_target _ hr] at hq
  · intro z hz
    exact hz.1

end NoExoticSixSphere
