import Wikipedia.HopfProblem.DegreeCollapseDisjointReturnArc
import Wikipedia.HopfProblem.DegreeCollapsePeriodicJoinedArc
import Wikipedia.HopfProblem.DegreeCollapsePeriodicCircle
import Wikipedia.SmoothSixDPoincare.OpenSubmanifoldDerivative

/-!
# An embedded native circle containing a prescribed short arc

An actual return path in an open set is sufficient. The return curve is
smoothed, embedded, and separated from the short arc with its continuation
germs fixed. The two pieces then give an immersed embedded standard circle.
Outside the prescribed short arc its entire image stays in the open set.
-/

noncomputable section

open Set Function Filter ContinuousMap TopologicalSpace
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold J ∞ N] [T2Space N]

theorem exists_embedded_circle_through_arc (S : Opens N)
    {α : ℝ → N} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Ioo (-R) R))
    (hinj : InjOn α (Icc (-R) R))
    (hderiv : ∀ s ∈ Ioo (-R) R, Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hplus : α r ∈ S) (hminus : α (-r) ∈ S)
    (η : Path (⟨α r, hplus⟩ : S) (⟨α (-r), hminus⟩ : S))
    (hdim : 3 ≤ Module.finrank ℝ G) :
    ∃ γ : C(Circle, N), ContMDiff (𝓡 1) J ∞ γ ∧ Injective γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) J γ z)) ∧
      (∀ s ∈ Icc (-r) r, γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) = α s) ∧
      range γ ⊆ α '' Icc (-r) r ∪ (S : Set N) := by
  obtain ⟨b, hb, hb0, hb1, hemb, hbd, havoid⟩ :=
    exists_disjoint_embedded_return_arc S hr hrR hα hinj hderiv hplus hminus η hdim
  let β : ℝ → N := Subtype.val ∘ b
  have hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β := contMDiff_subtype_val.comp hb
  have hβi : InjOn β (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hbx : b x = b y := Subtype.ext hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hbx)
  have hβd : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J β t) := by
    intro t ht
    rw [show β = Subtype.val ∘ b from rfl, mfderiv_comp t
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (hb.mdifferentiableAt (by simp))]
    exact (NativeOpenSubmanifold.injective_mfderiv_subtype_val S (b t)).comp (hbd t ht)
  have h0 : β 0 = α r := by simpa only [zero_add] using hb0.eq_of_nhds
  have h1 : β 1 = α (-r) := by
    simpa only [show (1 : ℝ) + (-1 - r) = -r by ring] using hb1.eq_of_nhds
  let F := CircleGluing.joinedLoop hr α β
  have hF : ContMDiff 𝓘(ℝ, ℝ) J ∞ F :=
    CircleGluing.joinedLoop_contMDiff hr hrR hα hβ hb0 hb1
  have hFd : ∀ t, Injective (mfderiv 𝓘(ℝ, ℝ) J F t) :=
    CircleGluing.joinedLoop_derivative_injective hr hrR hα hβ hb0 hb1 hderiv hβd
  have hsub : Icc (-r) r ⊆ Icc (-R) R := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hαi : InjOn α (Icc (-r) r) := hinj.mono hsub
  have hFi : InjOn F (Ico (0 : ℝ) (2 * r + 1)) :=
    CircleGluing.joinedLoop_injOn hr hαi hβi havoid
  have hT : 0 < 2 * r + 1 := by linarith
  have hper : Periodic F (2 * r + 1) := CircleGluing.joinedLoop_periodic hr α β
  let Γ := CircleGluing.periodicCircle hT.ne' hper
  have hΓ : ContMDiff (𝓡 1) J ∞ Γ := CircleGluing.periodicCircle_contMDiff hT.ne' hper hF
  refine ⟨⟨Γ, hΓ.continuous⟩, hΓ, CircleGluing.periodicCircle_injective hT hper hFi,
    CircleGluing.periodicCircle_derivative_injective hT.ne' hper hF hFd, ?_, ?_⟩
  · intro s hs
    exact (CircleGluing.periodicCircle_exp hT.ne' hper (s + r)).trans
      (CircleGluing.joinedLoop_left hr α β hs)
  · intro z hz
    change z ∈ range Γ at hz
    rw [CircleGluing.periodicCircle_range, CircleGluing.joinedLoop_range hr h0 h1] at hz
    rcases hz with hz | ⟨t, -, rfl⟩
    · exact Or.inl hz
    · exact Or.inr (b t).property

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
