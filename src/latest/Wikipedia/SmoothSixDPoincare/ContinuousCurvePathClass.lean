import Wikipedia.SmoothSixDPoincare.EndpointDetourPath
import Mathlib.Topology.Order.OrderClosed

/-!
# Continuous endpoint-germ joining in the prescribed original path class

Paste the explicit detour path to the prescribed real curves outside the
unit interval. Its initial and terminal formulas retain whole endpoint
neighborhoods, and its based path is homotopic to the original input path.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CurveImmersion

variable {N : Type*} [TopologicalSpace N]

theorem exists_continuous_curve_with_endpoint_germs_pathClass (a b : C(ℝ, N))
    (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N), EqOn f a (Iic (1 / 8 : ℝ)) ∧ EqOn f b (Ici (7 / 8 : ℝ)) ∧
      ∃ (h0 : f 0 = a 0) (h1 : f 1 = b 1),
        ((intervalPath f).cast h0.symm h1.symm).Homotopic γ := by
  classical
  let δ := endpointDetourPath a b γ
  let right : ℝ → N := fun t => if t ≤ 1 then δ.extend t else b t
  have hr : Continuous right := δ.continuous_extend.if_le b.continuous
    continuous_id continuous_const (by intro t ht; subst t; exact δ.extend_one)
  let raw : ℝ → N := fun t => if t ≤ 0 then a t else right t
  have hraw : Continuous raw := a.continuous.if_le hr continuous_id continuous_const (by
    intro t ht
    subst t
    change a 0 = if (0 : ℝ) ≤ 1 then δ.extend 0 else b 0
    rw [if_pos zero_le_one]
    exact δ.extend_zero.symm)
  let f : C(ℝ, N) := ⟨raw, hraw⟩
  have h0 : f 0 = a 0 := by change (if (0 : ℝ) ≤ 0 then a 0 else right 0) = _; simp
  have h1 : f 1 = b 1 := by
    change (if (1 : ℝ) ≤ 0 then a 1 else if (1 : ℝ) ≤ 1 then δ.extend 1 else b 1) = b 1
    rw [if_neg (by norm_num), if_pos le_rfl, δ.extend_one]
  have hleft : EqOn f a (Iic (1 / 8 : ℝ)) := by
    intro t ht
    change (if t ≤ 0 then a t else if t ≤ 1 then δ.extend t else b t) = a t
    by_cases ht0 : t ≤ 0
    · exact if_pos ht0
    · have ht1 : t ≤ 1 := by change t ≤ 1 / 8 at ht; linarith
      rw [if_neg ht0, if_pos ht1]
      calc
        δ.extend t = δ ⟨t, (not_le.mp ht0).le, ht1⟩ :=
          δ.extend_extends' ⟨t, (not_le.mp ht0).le, ht1⟩
        _ = a t := endpointDetourPath_left a b γ _ (by change t ≤ 1 / 8 at ht; linarith)
  have hright : EqOn f b (Ici (7 / 8 : ℝ)) := by
    intro t ht
    have ht0 : ¬ t ≤ 0 := by change 7 / 8 ≤ t at ht; linarith
    change (if t ≤ 0 then a t else if t ≤ 1 then δ.extend t else b t) = b t
    rw [if_neg ht0]
    by_cases ht1 : t ≤ 1
    · rw [if_pos ht1]
      calc
        δ.extend t = δ ⟨t, (not_le.mp ht0).le, ht1⟩ :=
          δ.extend_extends' ⟨t, (not_le.mp ht0).le, ht1⟩
        _ = b t := endpointDetourPath_right a b γ _ (by change 7 / 8 ≤ t at ht; linarith)
    · exact if_neg ht1
  have hpath : (intervalPath f).cast h0.symm h1.symm = δ := by
    ext t
    change f (t : ℝ) = δ t
    by_cases ht0 : (t : ℝ) ≤ 0
    · have ht : t = 0 := Subtype.ext (le_antisymm ht0 t.property.1)
      subst t
      exact h0.trans δ.source.symm
    · change (if (t : ℝ) ≤ 0 then a t else
        if (t : ℝ) ≤ 1 then δ.extend t else b t) = δ t
      rw [if_neg ht0, if_pos t.property.2]
      exact δ.extend_extends' t
  refine ⟨f, hleft, hright, h0, h1, ?_⟩
  rw [hpath]
  exact endpointDetourPath_homotopic a b γ

end Wikipedia.SmoothSixDPoincare.CurveImmersion
