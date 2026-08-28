import Wikipedia.HopfProblem.DegreeCollapseIntegralBallOrientation

/-!
# The actual oriented integral fundamental class supported on a closed ball

Lift the chosen primitive local class at zero through the original
evaluation equivalence. The exterior-shift homotopy identifies every
localization with the translated chosen generator, with the same sign.
The construction includes boundary points and radius zero.
-/

noncomputable section

open Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralBallOrientation

open NoExoticSixSphere

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]

/-- The chosen integral orientation at x is the translated primitive class at zero. -/
def pointClass (x : E) : RelativeSingularHomology.LocalHomology x (n + 2) :=
  (RelativeSingularHomology.translateLocalEquiv E x (n + 2)).symm
    (RelativeSingularHomology.localTopClass E n)

theorem translate_pointClass (x : E) :
    RelativeSingularHomology.translateLocalEquiv E x (n + 2) (pointClass E n x) =
      RelativeSingularHomology.localTopClass E n :=
  (RelativeSingularHomology.translateLocalEquiv E x (n + 2)).apply_symm_apply _

theorem pointClass_ne_zero (x : E) : pointClass E n x ≠ 0 := by
  intro he
  have h := translate_pointClass E n x
  rw [he, map_zero] at h
  exact RelativeSingularHomology.localTopClass_ne_zero E n h.symm

/-- A class in the genuine integral relative group of the original ball exterior. -/
def fundamentalClass (R : ℝ) (hR : 0 ≤ R) :
    RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ (n + 2) :=
  (evaluationEquiv R hR 0 (mem_closedBall_self hR) (n + 2)).symm
    (RelativeSingularHomology.localTopClass E n)

theorem fundamentalClass_evaluate_center (R : ℝ) (hR : 0 ≤ R) :
    evaluation R (0 : E) (mem_closedBall_self hR) (n + 2) (fundamentalClass E n R hR) =
      RelativeSingularHomology.localTopClass E n :=
  (evaluationEquiv R hR 0 (mem_closedBall_self hR) (n + 2)).apply_symm_apply _

/-- Every actual localization has the prescribed integral sign, including at the boundary. -/
theorem fundamentalClass_evaluate (R : ℝ) (hR : 0 ≤ R) (x : E)
    (hx : x ∈ closedBall (0 : E) R) :
    evaluation R x hx (n + 2) (fundamentalClass E n R hR) = pointClass E n x := by
  apply (RelativeSingularHomology.translateLocalEquiv E x (n + 2)).injective
  rw [translate_pointClass]
  exact (translated_evaluation R hR x hx (n + 1) (Nat.succ_ne_zero n)
    (fundamentalClass E n R hR)).trans (fundamentalClass_evaluate_center E n R hR)

theorem fundamentalClass_ne_zero (R : ℝ) (hR : 0 ≤ R) : fundamentalClass E n R hR ≠ 0 := by
  intro he
  have h := fundamentalClass_evaluate_center E n R hR
  rw [he, map_zero] at h
  exact RelativeSingularHomology.localTopClass_ne_zero E n h.symm

/-- The constructed class is primitive in the actual integral supported homology. -/
theorem fundamentalClass_generates (R : ℝ) (hR : 0 ≤ R)
    (a : RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ (n + 2)) :
    ∃ k : ℤ, k • fundamentalClass E n R hR = a := by
  obtain ⟨k, hk⟩ := RelativeSingularHomology.localTopClass_generates E n
    (evaluation R (0 : E) (mem_closedBall_self hR) (n + 2) a)
  refine ⟨k, (evaluationEquiv R hR 0 (mem_closedBall_self hR) (n + 2)).injective ?_⟩
  change evaluation R (0 : E) (mem_closedBall_self hR) (n + 2)
    (k • fundamentalClass E n R hR) = _
  rw [map_zsmul, fundamentalClass_evaluate_center]
  exact hk

theorem fundamentalClass_unique (R : ℝ) (hR : 0 ≤ R)
    (a : RelativeSingularHomology.Homology (closedBall (0 : E) R)ᶜ (n + 2))
    (ha : ∀ (x : E) (hx : x ∈ closedBall (0 : E) R),
      evaluation R x hx (n + 2) a = pointClass E n x) :
    a = fundamentalClass E n R hR := by
  apply (evaluationEquiv R hR 0 (mem_closedBall_self hR) (n + 2)).injective
  exact (ha 0 (mem_closedBall_self hR)).trans
    (fundamentalClass_evaluate E n R hR 0 (mem_closedBall_self hR)).symm

/-- The same oriented class is retained under every inclusion of centered closed balls. -/
theorem restrict_fundamentalClass (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S) (hRS : R ≤ S) :
    SupportedRelativeHomology.restrict (ModuleCat.of ℤ ℤ)
        (closedBall_subset_closedBall hRS : closedBall (0 : E) R ⊆ closedBall (0 : E) S)
        (n + 2) (fundamentalClass E n S hS) = fundamentalClass E n R hR := by
  apply fundamentalClass_unique E n R hR
  intro x hx
  have he := LinearMap.congr_fun
    (SupportedRelativeHomology.evaluate_restrict (ModuleCat.of ℤ ℤ)
      (closedBall_subset_closedBall hRS : closedBall (0 : E) R ⊆ closedBall (0 : E) S)
      x hx (n + 2)) (fundamentalClass E n S hS)
  exact he.trans (fundamentalClass_evaluate E n S hS x (closedBall_subset_closedBall hRS hx))

end Wikipedia.HopfProblem.DegreeCollapse.IntegralBallOrientation
