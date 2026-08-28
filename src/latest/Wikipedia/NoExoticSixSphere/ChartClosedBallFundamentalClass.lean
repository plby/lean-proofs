import Wikipedia.NoExoticSixSphere.CenteredBallLocalEvaluation
import Wikipedia.NoExoticSixSphere.SupportedFundamentalClass

/-!
# Constructed fundamental classes on closed balls in actual manifold charts

For a closed Euclidean ball lying in the target of a chart, its inverse
image is a compact support in the original manifold. Native excision and
the actual source-target homeomorphism show that all original point
evaluations are bijective. This constructs the unique mod-two relative
fundamental class on that whole support, including its boundary.
-/

noncomputable section

open Metric

namespace NoExoticSixSphere.ChartClosedBall

variable {E M : Type} [NormedAddCommGroup E] [TopologicalSpace M]

/-- The actual subset obtained by taking the inverse image of the closed ball in the chart. -/
def support (e : OpenPartialHomeomorph M E) (a : E) (R : ℝ) : Set M :=
  e.symm '' closedBall a R

theorem support_subset_source (e : OpenPartialHomeomorph M E) (a : E) (R : ℝ)
    (hB : closedBall a R ⊆ e.target) : support e a R ⊆ e.source := by
  rintro x ⟨y, hy, rfl⟩
  exact e.map_target (hB hy)

theorem mem_support_iff (e : OpenPartialHomeomorph M E) (a : E) (R : ℝ)
    (hB : closedBall a R ⊆ e.target) (x : M) (hx : x ∈ e.source) :
    x ∈ support e a R ↔ e x ∈ closedBall a R := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [e.right_inv (hB hy)] using hy
  · intro hy
    exact ⟨e x, hy, e.left_inv hx⟩

theorem support_nonempty (e : OpenPartialHomeomorph M E) (a : E) (R : ℝ) (hR : 0 ≤ R) :
    (support e a R).Nonempty :=
  ⟨e.symm a, a, mem_closedBall_self hR, rfl⟩

variable [ProperSpace E]

/-- Compactness is proved from the original chart's continuity on its target. -/
theorem support_isCompact (e : OpenPartialHomeomorph M E) (a : E) (R : ℝ)
    (hB : closedBall a R ⊆ e.target) : IsCompact (support e a R) :=
  (isCompact_closedBall a R).image_of_continuousOn (e.symm.continuousOn.mono hB)

variable [T2Space M]

theorem support_isClosed (e : OpenPartialHomeomorph M E) (a : E) (R : ℝ)
    (hB : closedBall a R ⊆ e.target) : IsClosed (support e a R) :=
  (support_isCompact e a R hB).isClosed

variable [NormedSpace ℝ E]

/-- Evaluation of the original supported relative class at every point is bijective. -/
theorem evaluate_bijective (p : ℕ) (hp : p ≠ 0) (e : OpenPartialHomeomorph M E)
    (a : E) (R : ℝ) (hR : 0 ≤ R) (hB : closedBall a R ⊆ e.target)
    (x : M) (hx : x ∈ support e a R) (k : ℕ) :
    Function.Bijective (SupportedRelativeHomology.evaluate (ModuleCat.of ℤ (ZMod p))
      (support e a R) x hx k) := by
  exact (SupportedRelativeHomology.evaluate_bijective_iff_partialHomeomorph p hp e
    (support_isClosed e a R hB) isClosed_closedBall (support_subset_source e a R hB) hB
    (mem_support_iff e a R hB) x hx k).mpr
    (ClosedBallLocalHomology.evaluate_centered_bijective p hp a R hR (e x)
      ((mem_support_iff e a R hB x (support_subset_source e a R hB hx)).mp hx) k)

end NoExoticSixSphere.ChartClosedBall

namespace NoExoticSixSphere.ChartClosedBall

open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- A closed ball in any actual manifold chart has a unique relative mod-two fundamental class. -/
theorem existsUnique_fundamentalClass (e : OpenPartialHomeomorph M E) (a : E) (R : ℝ)
    (hR : 0 ≤ R) (hB : closedBall a R ⊆ e.target) :
    ∃! c : Homology (ModuleCat.of ℤ (ZMod 2)) (support e a R) (n + 3),
      IsFundamentalOn (E := E) n (support e a R) c :=
  existsUnique_fundamentalClass_of_evaluate_bijective (E := E) n (support e a R)
    (support_nonempty e a R hR) (fun x hx => evaluate_bijective 2 (by decide) e a R hR hB x hx _)

end NoExoticSixSphere.ChartClosedBall
