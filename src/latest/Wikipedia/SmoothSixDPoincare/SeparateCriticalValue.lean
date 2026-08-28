import Wikipedia.SmoothSixDPoincare.ConstantMorsePerturbation
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.Separation.Basic

/-!
# Separating one critical value without moving any critical point

A genuine smooth bump is constant one near the chosen critical point and
zero near every other critical point. A small parameter outside a finite
forbidden set makes the chosen value unique. Compact regular stability
ensures that no critical points are added or removed.
-/

noncomputable section

open Set Metric Filter Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Move one critical value away from every other critical value, leaving every critical point
and all other critical values unchanged. -/
theorem exists_separating_critical_value {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (p : M) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧
      (∀ x ∈ criticalPoints E f, x ≠ p → g x = f x) ∧
      ∀ x ∈ criticalPoints E f, g x = g p → x = p := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hclosed : IsClosed (K \ {p}) := (hK.subset sdiff_subset).isClosed
  have hp : p ∈ (K \ {p})ᶜ := by simp
  obtain ⟨ψ, _, hψsub⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
    (hclosed.isOpen_compl.mem_nhds hp)
  have hψone : (ψ : M → ℝ) =ᶠ[𝓝 p] fun _ => 1 := ψ.eventuallyEq_one
  have hψzero (x : M) (hx : x ∈ K) (hxp : x ≠ p) :
      (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ => 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    exact hψsub h ⟨hx, by simpa only [mem_singleton_iff] using hxp⟩
  have hconstant : ∀ x ∈ criticalPoints E f, ∃ b : ℝ, (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ => b := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      exact ⟨1, hψone⟩
    · exact ⟨0, hψzero x hx hxp⟩
  have hstable := eventually_constantPerturb_morse_criticalPoints hf hm ψ.contMDiff hconstant
  let T : Set ℝ := (fun x => f x - f p) '' (K \ {p})
  have hT : T.Finite := (hK.subset sdiff_subset).image _
  have hdense : Dense Tᶜ := by
    have heq : (univ : Set ℝ) \ T = Tᶜ := by
      ext a
      exact and_iff_right (mem_univ a)
    rw [← heq]
    exact dense_univ.sdiff_finite hT
  obtain ⟨U, hUstable, hU, hzeroU⟩ := _root_.mem_nhds_iff.mp hstable
  obtain ⟨a, haT, haU⟩ := hdense.exists_mem_open hU ⟨0, hzeroU⟩
  let g := constantPerturb f ψ a
  have hvalues (x : M) (hx : x ∈ K) (hxp : x ≠ p) : g x = f x := by
    have hxzero : ψ x = 0 := (hψzero x hx hxp).eq_of_nhds
    simp only [g, constantPerturb, hxzero, mul_zero, add_zero]
  have hpvalue : g p = f p + a := by
    have hpone : ψ p = 1 := hψone.eq_of_nhds
    simp only [g, constantPerturb, hpone, mul_one]
  refine ⟨g, (contMDiff_constantPerturb hf ψ.contMDiff).comp
    (contMDiff_const.prodMk contMDiff_id), (hUstable haU).1, (hUstable haU).2, hvalues, ?_⟩
  intro x hx heq
  by_contra hxp
  have hax : f x - f p = a := by rw [hvalues x hx hxp, hpvalue] at heq; linarith
  exact haT ⟨x, ⟨hx, by simpa only [mem_singleton_iff] using hxp⟩, hax⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
