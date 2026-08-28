import Wikipedia.HopfProblem.FundamentalGroupVanKampenPushout

/-!
# Surjectivity after a genuine two-open-set attachment

If the overlap already generates the fundamental group of the second
open set, the actual inclusion of the first open set generates the
fundamental group of the union.  This is a consequence of the proved
topological van Kampen isomorphism, with no assumption that either
inclusion is injective.
-/

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen.TwoOpenCover

variable {X : Type*} [TopologicalSpace X] (D : TwoOpenCover X)

/-- Attaching an open set whose group comes from the overlap adds no
new fundamental-group generators. -/
theorem inclusionHomU_surjective_of_overlapHomV_surjective
    (hV : Function.Surjective D.overlapHomV) :
    Function.Surjective D.inclusionHomU := by
  intro γ
  obtain ⟨q, rfl⟩ := D.pushoutEquiv.surjective γ
  induction q using Monoid.PushoutI.induction_on with
  | of i g =>
    cases i with
    | false => exact ⟨g, (D.pushoutEquiv_of false g).symm⟩
    | true =>
      obtain ⟨a, rfl⟩ := hV g
      exact ⟨D.overlapHomU a,
        (DFunLike.congr_fun D.inclusionHom_compatible a).trans
          (D.pushoutEquiv_of true (D.overlapHomV a)).symm⟩
  | base a =>
    refine ⟨D.overlapHomU a, ?_⟩
    exact (D.pushoutEquiv_of false (D.overlapHomU a)).symm.trans
      (congrArg D.pushoutEquiv
        (Monoid.PushoutI.of_apply_eq_base D.overlapHom false a))
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩

end Wikipedia.HopfProblem.FundamentalGroupVanKampen.TwoOpenCover
