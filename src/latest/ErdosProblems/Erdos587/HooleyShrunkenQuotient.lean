import ErdosProblems.Erdos587.HooleyBodyDilate
import ErdosProblems.Erdos587.HooleyConvexQuotient

/-! # A shrunken primitive quotient with exact inner containment -/

namespace Erdos587.GeneralizedAP

noncomputable def deltaShrunkenQuotient (X : ConvexProgression)
    {n : ℕ} (u a : Fin X.rank → ℤ) (hua : dotLinear a u = 1)
    (b : Module.Basis (Fin n) ℤ (LinearMap.ker (dotLinear a)))
    (η : ℝ) (hη : η < 1)
    (hround : ∀ x : Fin n → ℝ, ∃ v : Fin n → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) (bodyDilate (1 - η)
        (intLinearMapRealExtension (primitiveQuotientProjection u a hua b) '' X.body))) :
    ConvexProgression :=
  deltaDilatedConvexProgression (X.primitiveQuotient u a hua b) (1 - η)
    (sub_pos.mpr hη) hround

theorem deltaShrunkenQuotient_carrier_subset (X : ConvexProgression)
    {n : ℕ} (u a : Fin X.rank → ℤ) (hua : dotLinear a u = 1)
    (b : Module.Basis (Fin n) ℤ (LinearMap.ker (dotLinear a))) (hn : n + 1 = X.rank)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (hround)
    (hu : intCastVec u ∈ bodyDilate η X.body) (heval : X.eval u = 0) :
    (deltaShrunkenQuotient X u a hua b η hη1 hround).carrier ⊆ X.carrier :=
  delta_shrunken_quotient_eval_subset X u a hua b hn hη0 hη1.le hu heval

theorem deltaShrunkenQuotient_homogeneous (X : ConvexProgression)
    {n : ℕ} (u a : Fin X.rank → ℤ) (hua : dotLinear a u = 1)
    (b : Module.Basis (Fin n) ℤ (LinearMap.ker (dotLinear a)))
    (η : ℝ) (hη1 : η < 1) (hround) (heval : X.eval u = 0)
    (hbase : ∃ c, X.eval c = X.base) :
    ∃ c, (deltaShrunkenQuotient X u a hua b η hη1 hround).eval c =
      (deltaShrunkenQuotient X u a hua b η hη1 hround).base := by
  obtain ⟨c, hc⟩ := hbase
  refine ⟨primitiveQuotientProjection u a hua b c, ?_⟩
  change primitiveQuotientEval X.eval b (primitiveQuotientProjection u a hua b c) = X.base
  rw [primitiveQuotientEval_projection X.eval u a hua heval b, hc]

theorem delta_primitiveQuotient_injOn_of_eval (X : ConvexProgression)
    {n : ℕ} (u a : Fin X.rank → ℤ) (hua : dotLinear a u = 1)
    (b : Module.Basis (Fin n) ℤ (LinearMap.ker (dotLinear a)))
    (heval : X.eval u = 0) {U : Set (Fin X.rank → ℤ)} (hU : Set.InjOn X.eval U) :
    Set.InjOn (primitiveQuotientProjection u a hua b) U := by
  intro x hx y hy hxy
  apply hU hx hy
  have hh := congrArg (primitiveQuotientEval X.eval b) hxy
  simpa only [primitiveQuotientEval_projection X.eval u a hua heval b] using hh

end Erdos587.GeneralizedAP
