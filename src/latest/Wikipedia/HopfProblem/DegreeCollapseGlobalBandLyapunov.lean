import Wikipedia.HopfProblem.DegreeCollapseBandHeightGerms

/-!
# The global smooth Lyapunov replacement after finite passage

The band height agrees with the original function on whole neighborhoods
of both boundary levels. Piecewise replacement is consequently smooth
in the original atlas, is strictly descending on the entire closed band,
and retains every original germ outside the open band.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

def bandReplacement (f g : X → ℝ) (c d : ℝ) (x : X) : ℝ := by
  classical
  exact if f x ∈ Ioo c d then g x else f x

theorem bandReplacement_germ_boundary {f g : X → ℝ} {c d : ℝ} {x : X}
    (heq : g =ᶠ[𝓝 x] f) :
    bandReplacement f g c d =ᶠ[𝓝 x] f ∧ bandReplacement f g c d =ᶠ[𝓝 x] g := by
  have hh : bandReplacement f g c d =ᶠ[𝓝 x] f := by
    filter_upwards [heq] with y hy
    simp only [bandReplacement, hy, ite_self]
  exact ⟨hh, hh.trans heq.symm⟩

theorem bandReplacement_germ_interior {f g : X → ℝ} {c d : ℝ}
    (hf : Continuous f) {x : X} (hx : f x ∈ Ioo c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] g := by
  filter_upwards [(isOpen_Ioo.preimage hf).mem_nhds hx] with y hy
  exact if_pos hy

theorem bandReplacement_germ_exterior {f g : X → ℝ} {c d : ℝ}
    (hf : Continuous f) {x : X} (hx : f x ∉ Icc c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] f := by
  filter_upwards [((isClosed_Icc.preimage hf).isOpen_compl).mem_nhds hx] with y hy
  exact if_neg (fun h => hy ⟨h.1.le, h.2.le⟩)

theorem bandReplacement_germ_on_closed {f g : X → ℝ} {c d : ℝ}
    (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∈ Icc c d) : bandReplacement f g c d =ᶠ[𝓝 x] g := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).2
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).2
  exact bandReplacement_germ_interior hf
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hc), lt_of_le_of_ne hx.2 hd⟩

theorem bandReplacement_germ_off_open {f g : X → ℝ} {c d : ℝ}
    (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∉ Ioo c d) : bandReplacement f g c d =ᶠ[𝓝 x] f := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).1
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).1
  apply bandReplacement_germ_exterior hf
  intro h
  exact hx ⟨lt_of_le_of_ne h.1 (Ne.symm hc), lt_of_le_of_ne h.2 hd⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Native smooth gluing across both boundary levels uses complete function germs. -/
theorem contMDiff_bandReplacement {f g : M → ℝ} {c d : ℝ} {U : Set M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (hU : IsOpen U)
    (hband : f ⁻¹' Icc c d ⊆ U)
    (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (bandReplacement f g c d) := by
  intro x
  by_cases hx : f x ∈ Icc c d
  · exact ((hg x (hband hx)).contMDiffAt (hU.mem_nhds (hband hx))).congr_of_eventuallyEq
      (bandReplacement_germ_on_closed hf.continuous hboundary hx)
  · exact hf.contMDiffAt.congr_of_eventuallyEq (bandReplacement_germ_exterior hf.continuous hx)

/-- Equality of scalar germs retains their actual vector-valued manifold derivatives. -/
theorem mvfderiv_eq_of_germ {f g : M → ℝ} {x : M} (heq : f =ᶠ[𝓝 x] g) :
    mvfderiv 𝓘(ℝ, E) f x (V x) = mvfderiv 𝓘(ℝ, E) g x (V x) := by
  unfold mvfderiv
  rw [heq.mfderiv_eq, heq.eq_of_nhds]

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- Actual directed finite passage and negative boundary derivatives construct
a global native smooth replacement, strictly descending throughout the band
and retaining all exterior germs. -/
theorem exists_global_band_lyapunov {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧
      ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ b : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ x, f x ∈ Icc c d → mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
      ∀ x, f x ∉ Ioo c d → b =ᶠ[𝓝 x] f := by
  obtain ⟨U, g, hU, hband, hg, hgneg, hgerm⟩ :=
    exists_smooth_band_height_germs hf hV F hcurve hcd hc hd hcross
  refine ⟨bandReplacement f g c d, contMDiff_bandReplacement hf hg hU hband hgerm, ?_, ?_⟩
  · intro x hx
    rw [mvfderiv_eq_of_germ (V := V) (bandReplacement_germ_on_closed hf.continuous hgerm hx)]
    exact hgneg x (hband hx)
  · intro x hx
    exact bandReplacement_germ_off_open hf.continuous hgerm hx

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
