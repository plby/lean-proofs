import Wikipedia.HopfProblem.DegreeCollapseExcursionInterval
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Dynamics.Flow
import Mathlib.Tactic.Ring

/-!
# No-return survives a field perturbation supported in the inner neighborhood

An excursion outside the outer neighborhood is isolated between the last
and first encounters with the closed perturbation region. On that open
interval the perturbed curve solves the original ODE. Native uniqueness
and continuity at both endpoints identify the entire closed segment with
an original orbit, contradicting its no-return property.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {V V' : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A native integral curve agrees with the given flow on a closed time interval. -/
theorem native_curve_eq_flow_on_closed_interval
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {γ : ℝ → M} (hγcont : Continuous γ) {a b c : ℝ} (hc : c ∈ Ioo a b)
    (hγ : IsMIntegralCurveOn γ V (Ioo a b)) :
    ∀ t ∈ Icc a b, γ t = F (t - c) (γ c) := by
  have hF : IsMIntegralCurve (fun t => F (t - c) (γ c)) V := by
    have he : (fun t => F (t - c) (γ c)) =
        ((fun t => F t (γ c)) ∘ (· + -c)) := by
      funext t
      simp only [comp_apply, sub_eq_add_neg]
    rw [he]
    exact (hcurve (γ c)).comp_add (-c)
  have heq : EqOn γ (fun t => F (t - c) (γ c)) (Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hc hV hγ
      (hF.isMIntegralCurveOn _) (by simp)
  have heqclosed := heq.closure hγcont hF.continuous
  rw [closure_Ioo (lt_trans hc.1 hc.2).ne] at heqclosed
  exact heqclosed

/-- Every perturbed orbit segment with endpoints in `N` stays in `U`. -/
theorem native_no_return_of_supported_perturbation
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {K N U : Set M} (hK : IsClosed K) (hKN : K ⊆ N) (hNU : N ⊆ U)
    (hoff : ∀ x ∉ K, V' x = V x)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N →
      ∀ s ∈ Icc (0 : ℝ) t, F s x ∈ U)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V')
    {a b : ℝ} (ha : γ a ∈ N) (hb : γ b ∈ N) :
    ∀ t ∈ Icc a b, γ t ∈ U := by
  intro t ht
  by_contra hout
  obtain ⟨s, u, -, hst, htu, -, hsN, huN, havoid⟩ :=
    exists_excursion_interval hγ.continuous hK hKN ht ha hb (fun hh => hout (hNU hh))
  have hold : IsMIntegralCurveOn γ V (Ioo s u) := by
    intro r hr
    have hd := (hγ r).hasMFDerivWithinAt (s := Ioo s u)
    rw [hoff (γ r) (havoid r hr)] at hd
    exact hd
  have heq := native_curve_eq_flow_on_closed_interval hV F hcurve hγ.continuous
    (show t ∈ Ioo s u from ⟨hst, htu⟩) hold
  have hs : γ s = F (s - t) (γ t) := heq s ⟨le_rfl, (lt_trans hst htu).le⟩
  have hu : γ u = F (u - t) (γ t) := heq u ⟨(lt_trans hst htu).le, le_rfl⟩
  have hend : F (u - s) (γ s) = γ u := by
    rw [hs, ← F.map_add, show u - s + (s - t) = u - t by ring, ← hu]
  have hmid : F (t - s) (γ s) = γ t := by
    rw [hs, ← F.map_add, show t - s + (s - t) = 0 by ring, F.map_zero_apply]
  have hh := hnoreturn (γ s) hsN (u - s) (sub_nonneg.mpr (lt_trans hst htu).le)
    (hend ▸ huN) (t - s) ⟨sub_nonneg.mpr hst.le, sub_le_sub_right htu.le s⟩
  exact hout (hmid ▸ hh)

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
