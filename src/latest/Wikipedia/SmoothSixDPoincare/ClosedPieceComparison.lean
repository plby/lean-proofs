import Wikipedia.SmoothSixDPoincare.ClosedCoverHomeomorph

/-!
# Comparing spaces built from two actual closed embedded pieces

Keep the common exterior parameter space and change the other piece by a
homeomorphism preserving its exact incidence with the exterior. Closed-cover
gluing constructs a homeomorphism of the total spaces, including when those
spaces are noncompact handle complements.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.ClosedCover

variable {R P Q X Y : Type*}
  [TopologicalSpace R] [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Actual embedded pieces, their covers, and their exact incidences determine the comparison. -/
def homeomorphOfClosedPieces
    (r₀ : R → X) (r₁ : R → Y) (p₀ : P → X) (p₁ : Q → Y)
    (hr₀ : IsClosedEmbedding r₀) (hr₁ : IsClosedEmbedding r₁)
    (hp₀ : IsClosedEmbedding p₀) (hp₁ : IsClosedEmbedding p₁)
    (hcover₀ : range r₀ ∪ range p₀ = univ) (hcover₁ : range r₁ ∪ range p₁ = univ)
    (e : P ≃ₜ Q)
    (hincidence : ∀ r p, r₀ r = p₀ p ↔ r₁ r = p₁ (e p)) : X ≃ₜ Y := by
  let a₀ := hr₀.isEmbedding.toHomeomorph
  let a₁ := hr₁.isEmbedding.toHomeomorph
  let b₀ := hp₀.isEmbedding.toHomeomorph
  let b₁ := hp₁.isEmbedding.toHomeomorph
  let a : range r₀ ≃ₜ range r₁ := a₀.symm.trans a₁
  let b : range p₀ ≃ₜ range p₁ := b₀.symm.trans (e.trans b₁)
  apply homeomorph hcover₀ hcover₁ hr₀.isClosed_range hp₀.isClosed_range
    hr₁.isClosed_range hp₁.isClosed_range a b
  intro x y
  have hx : r₀ (a₀.symm x) = (x : X) := by
    exact congrArg Subtype.val (a₀.apply_symm_apply x)
  have hy : p₀ (b₀.symm y) = (y : X) := by
    exact congrArg Subtype.val (b₀.apply_symm_apply y)
  change r₁ (a₀.symm x) = p₁ (e (b₀.symm y)) ↔ (x : X) = (y : X)
  rw [← hincidence, hx, hy]

variable (r₀ : R → X) (r₁ : R → Y) (p₀ : P → X) (p₁ : Q → Y)
  (hr₀ : IsClosedEmbedding r₀) (hr₁ : IsClosedEmbedding r₁)
  (hp₀ : IsClosedEmbedding p₀) (hp₁ : IsClosedEmbedding p₁)
  (hcover₀ : range r₀ ∪ range p₀ = univ) (hcover₁ : range r₁ ∪ range p₁ = univ)
  (e : P ≃ₜ Q)
  (hincidence : ∀ r p, r₀ r = p₀ p ↔ r₁ r = p₁ (e p))

theorem homeomorphOfClosedPieces_left (r : R) :
    homeomorphOfClosedPieces r₀ r₁ p₀ p₁ hr₀ hr₁ hp₀ hp₁ hcover₀ hcover₁ e hincidence (r₀ r) =
      r₁ r := by
  let a₀ := hr₀.isEmbedding.toHomeomorph
  let b₀ := hp₀.isEmbedding.toHomeomorph
  change glue hcover₀ (fun x : range r₀ => r₁ (a₀.symm x))
    (fun x : range p₀ => p₁ (e (b₀.symm x))) (r₀ r) = r₁ r
  have hleft := glue_left hcover₀ (fun x : range r₀ => r₁ (a₀.symm x))
    (fun x : range p₀ => p₁ (e (b₀.symm x))) ⟨r₀ r, mem_range_self r⟩
  exact hleft.trans (congrArg r₁ (a₀.symm_apply_apply r))

theorem homeomorphOfClosedPieces_right (p : P) :
    homeomorphOfClosedPieces r₀ r₁ p₀ p₁ hr₀ hr₁ hp₀ hp₁ hcover₀ hcover₁ e hincidence (p₀ p) =
      p₁ (e p) := by
  let a₀ := hr₀.isEmbedding.toHomeomorph
  let b₀ := hp₀.isEmbedding.toHomeomorph
  have hagree : ∀ x : range r₀, ∀ y : range p₀, (x : X) = y →
      r₁ (a₀.symm x) = p₁ (e (b₀.symm y)) := by
    intro x y hxy
    apply (hincidence (a₀.symm x) (b₀.symm y)).mp
    exact (congrArg Subtype.val (a₀.apply_symm_apply x)).trans
      (hxy.trans (congrArg Subtype.val (b₀.apply_symm_apply y)).symm)
  change glue hcover₀ (fun x : range r₀ => r₁ (a₀.symm x))
    (fun x : range p₀ => p₁ (e (b₀.symm x))) (p₀ p) = p₁ (e p)
  have hright := glue_right hcover₀ (fun x : range r₀ => r₁ (a₀.symm x))
    (fun x : range p₀ => p₁ (e (b₀.symm x))) hagree ⟨p₀ p, mem_range_self p⟩
  exact hright.trans (congrArg (fun x => p₁ (e x)) (b₀.symm_apply_apply p))

end Wikipedia.SmoothSixDPoincare.ClosedCover
