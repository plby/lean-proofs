import Wikipedia.NoExoticSixSphere.ClosedBallLocalEvaluation
import Wikipedia.NoExoticSixSphere.ModTwoLocalClassUniqueness

/-!
# A constructed relative mod-two fundamental class on a closed ball

The actual local evaluation isomorphism at the center constructs a class
in `H(E, E \ closedBall 0 R; ℤ/2)`. Evaluation is an isomorphism at every
point of the ball, so that class has the canonical nonzero value everywhere.
This proves existence and uniqueness on the whole closed ball, including
its boundary. No fundamental class is supplied as a hypothesis.
-/

noncomputable section

open Metric

namespace NoExoticSixSphere.ClosedBallLocalHomology

open SupportedRelativeHomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- The actual class obtained by lifting the canonical center class through evaluation. -/
def fundamentalClass (R : ℝ) (hR : 0 ≤ R) :
    Homology (ModuleCat.of ℤ (ZMod 2)) (closedBall (0 : E) R) (n + 3) :=
  (evaluateEquiv 2 (by decide) R hR (0 : E) (mem_closedBall_self hR) (n + 3)).symm
    (ModTwoLocalClass.manifoldClass (E := E) n (0 : E))

theorem fundamentalClass_evaluate_center (R : ℝ) (hR : 0 ≤ R) :
    evaluate (ModuleCat.of ℤ (ZMod 2)) (closedBall (0 : E) R) 0 (mem_closedBall_self hR)
        (n + 3) (fundamentalClass E n R hR) =
      ModTwoLocalClass.manifoldClass (E := E) n (0 : E) :=
  (evaluateEquiv 2 (by decide) R hR (0 : E) (mem_closedBall_self hR) (n + 3)).apply_symm_apply _

theorem fundamentalClass_ne_zero (R : ℝ) (hR : 0 ≤ R) : fundamentalClass E n R hR ≠ 0 := by
  intro h
  have he := fundamentalClass_evaluate_center E n R hR
  rw [h, map_zero] at he
  exact ModTwoLocalClass.manifoldClass_ne_zero (E := E) n (0 : E) he.symm

/-- Every original local evaluation is the canonical nonzero class, including at boundary points. -/
theorem fundamentalClass_isFundamentalOn (R : ℝ) (hR : 0 ≤ R) :
    IsFundamentalOn (E := E) n (closedBall (0 : E) R) (fundamentalClass E n R hR) := by
  intro x hx
  apply ModTwoLocalClass.eq_manifoldClass_of_ne_zero (E := E) n x
  intro hz
  let F := evaluateEquiv 2 (by decide) R hR x hx (n + 3)
  have he : F (fundamentalClass E n R hR) = F 0 := hz.trans F.map_zero.symm
  exact fundamentalClass_ne_zero E n R hR (F.injective he)

/-- Any actual class with those local values is the constructed class. -/
theorem fundamentalClass_unique (R : ℝ) (hR : 0 ≤ R)
    (c : Homology (ModuleCat.of ℤ (ZMod 2)) (closedBall (0 : E) R) (n + 3))
    (hc : IsFundamentalOn (E := E) n (closedBall (0 : E) R) c) :
    c = fundamentalClass E n R hR := by
  apply (evaluateEquiv 2 (by decide) R hR (0 : E) (mem_closedBall_self hR) (n + 3)).injective
  exact (hc 0 (mem_closedBall_self hR)).trans (fundamentalClass_evaluate_center E n R hR).symm

/-- A closed ball of nonnegative radius has a unique actual relative mod-two fundamental class. -/
theorem existsUnique_fundamentalClass (R : ℝ) (hR : 0 ≤ R) :
    ∃! c : Homology (ModuleCat.of ℤ (ZMod 2)) (closedBall (0 : E) R) (n + 3),
      IsFundamentalOn (E := E) n (closedBall (0 : E) R) c :=
  ⟨fundamentalClass E n R hR, fundamentalClass_isFundamentalOn E n R hR,
    fun c hc => fundamentalClass_unique E n R hR c hc⟩

end NoExoticSixSphere.ClosedBallLocalHomology
