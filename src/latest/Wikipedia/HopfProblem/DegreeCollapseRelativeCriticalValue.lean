import Wikipedia.SmoothSixDPoincare.SeparateCriticalValue

/-!
# Separate one critical value within a prescribed open region

The genuine constant bump perturbation fixes every other critical value
and preserves the entire native critical set. Its closed support lies in
the allowed open region, and a parameter in a prescribed small interval
gives a uniform value bound. Outside that region the function is unchanged.
-/

noncomputable section

open Set Metric Filter Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse

open Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem constantPerturb_close (f : M → ℝ) {p : M}
    (ψ : SmoothBumpFunction 𝓘(ℝ, E) p) (a ε : ℝ) (ha : |a| < ε) (x : M) :
    |constantPerturb f ψ a x - f x| < ε := by
  calc
    |constantPerturb f ψ a x - f x| = |a * ψ x| := by
      unfold constantPerturb
      congr 1
      ring
    _ = |a| * ψ x := by rw [abs_mul, abs_of_nonneg ψ.nonneg]
    _ ≤ |a| := mul_le_of_le_one_right (abs_nonneg a) ψ.le_one
    _ < ε := ha

theorem exists_separating_critical_value_relative {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (O : Set M) (hO : IsOpen O) (p : M) (hpO : p ∈ O) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧
      (∀ x ∈ criticalPoints E f, x ≠ p → g x = f x) ∧
      (∀ x ∈ criticalPoints E f, g x = g p → x = p) ∧
      (∀ x : M, |g x - f x| < ε) ∧ EqOn g f Oᶜ := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hclosed : IsClosed (K \ {p}) := (hK.subset sdiff_subset).isClosed
  have hp : p ∈ (K \ {p})ᶜ ∩ O := ⟨by simp, hpO⟩
  obtain ⟨ψ, _, hψsub⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p
    ).mem_iff.mp ((hclosed.isOpen_compl.inter hO).mem_nhds hp)
  have hψone : (ψ : M → ℝ) =ᶠ[𝓝 p] fun _ ↦ 1 := ψ.eventuallyEq_one
  have hψzero (x : M) (hx : x ∈ K) (hxp : x ≠ p) :
      (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ ↦ 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    exact (hψsub h).1 ⟨hx, by simpa only [mem_singleton_iff] using hxp⟩
  have hconstant : ∀ x ∈ criticalPoints E f, ∃ b : ℝ,
      (ψ : M → ℝ) =ᶠ[𝓝 x] fun _ ↦ b := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      exact ⟨1, hψone⟩
    · exact ⟨0, hψzero x hx hxp⟩
  have hstable := eventually_constantPerturb_morse_criticalPoints hf hm ψ.contMDiff hconstant
  let T : Set ℝ := (fun x ↦ f x - f p) '' (K \ {p})
  have hT : T.Finite := (hK.subset sdiff_subset).image _
  have hdense : Dense Tᶜ := by
    have heq : (univ : Set ℝ) \ T = Tᶜ := by
      ext a
      exact and_iff_right (mem_univ a)
    rw [← heq]
    exact dense_univ.sdiff_finite hT
  obtain ⟨U, hUstable, hU, hzeroU⟩ := _root_.mem_nhds_iff.mp hstable
  obtain ⟨a, haT, haU, haε⟩ := hdense.exists_mem_open (hU.inter isOpen_ball)
    ⟨0, hzeroU, mem_ball_self hε⟩
  let g := constantPerturb f ψ a
  have hvalues (x : M) (hx : x ∈ K) (hxp : x ≠ p) : g x = f x := by
    have hxzero : ψ x = 0 := (hψzero x hx hxp).eq_of_nhds
    simp only [g, constantPerturb, hxzero, mul_zero, add_zero]
  have hpvalue : g p = f p + a := by
    have hpone : ψ p = 1 := hψone.eq_of_nhds
    simp only [g, constantPerturb, hpone, mul_one]
  refine ⟨g, (contMDiff_constantPerturb hf ψ.contMDiff).comp
    (contMDiff_const.prodMk contMDiff_id), (hUstable haU).1, (hUstable haU).2,
    hvalues, ?_, ?_, ?_⟩
  · intro x hx heq
    by_contra hxp
    have hax : f x - f p = a := by rw [hvalues x hx hxp, hpvalue] at heq; linarith
    exact haT ⟨x, ⟨hx, by simpa only [mem_singleton_iff] using hxp⟩, hax⟩
  · intro x
    exact constantPerturb_close f ψ a ε
      (by simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using haε) x
  · intro x hx
    have hψx : ψ x = 0 := by
      by_contra hn
      exact hx (hψsub (subset_closure hn)).2
    simp only [g, constantPerturb, hψx, mul_zero, add_zero]

end Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse
