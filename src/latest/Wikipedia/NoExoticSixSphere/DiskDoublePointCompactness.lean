import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The actual compact closure of disk double points

The two source points lie in the open unit ball. Their closure lies in
the product of the closed balls, hence is compact in finite dimension.
Continuity is required only on the original closed disk, not outside it.
An injective outer collar and separation of interior from boundary images
exclude all boundary ends of this actual closure.
-/

open Set Function Metric

namespace NoExoticSixSphere.DiskDoublePoints

variable {E Y : Type*} [NormedAddCommGroup E]

def points (g : E → Y) : Set (E × E) :=
  {p | p.1 ∈ ball 0 1 ∧ p.2 ∈ ball 0 1 ∧ p.1 ≠ p.2 ∧ g p.1 = g p.2}

theorem closure_subset_closedBall (g : E → Y) :
    closure (points g) ⊆ closedBall 0 1 ×ˢ closedBall 0 1 := by
  apply closure_minimal _ (isClosed_closedBall.prod isClosed_closedBall)
  intro p hp
  exact ⟨ball_subset_closedBall hp.1, ball_subset_closedBall hp.2.1⟩

theorem isCompact_closure [NormedSpace ℝ E] [FiniteDimensional ℝ E] (g : E → Y) :
    IsCompact (closure (points g)) :=
  ((isCompact_closedBall (0 : E) 1).prod (isCompact_closedBall (0 : E) 1)).of_isClosed_subset
    isClosed_closure (closure_subset_closedBall g)

theorem closure_subset_not_both_outer (g : E → Y) (ρ : ℝ)
    (hi : InjOn g (closedBall 0 1 ∩ {x | ρ ≤ ‖x‖})) :
    closure (points g) ⊆ {p : E × E | ‖p.1‖ ≤ ρ ∨ ‖p.2‖ ≤ ρ} := by
  have hc : IsClosed {p : E × E | ‖p.1‖ ≤ ρ ∨ ‖p.2‖ ≤ ρ} :=
    (isClosed_le continuous_fst.norm continuous_const).union
      (isClosed_le continuous_snd.norm continuous_const)
  apply closure_minimal _ hc
  intro p hp
  by_contra hn
  have hleft : ρ < ‖p.1‖ := lt_of_not_ge (fun h ↦ hn (Or.inl h))
  have hright : ρ < ‖p.2‖ := lt_of_not_ge (fun h ↦ hn (Or.inr h))
  exact hp.2.2.1 (hi ⟨ball_subset_closedBall hp.1, hleft.le⟩
    ⟨ball_subset_closedBall hp.2.1, hright.le⟩ hp.2.2.2)

variable [TopologicalSpace Y] [T2Space Y]

theorem closure_equal_image (g : E → Y) (hg : ContinuousOn g (closedBall 0 1))
    {p : E × E} (hp : p ∈ closure (points g)) : g p.1 = g p.2 := by
  have hleft : ContinuousOn (fun q : E × E ↦ g q.1) (closedBall 0 1 ×ˢ closedBall 0 1) :=
    hg.comp continuous_fst.continuousOn (fun _ hq ↦ hq.1)
  have hright : ContinuousOn (fun q : E × E ↦ g q.2) (closedBall 0 1 ×ˢ closedBall 0 1) :=
    hg.comp continuous_snd.continuousOn (fun _ hq ↦ hq.2)
  have hc : IsClosed ((closedBall 0 1 ×ˢ closedBall 0 1) ∩
      {q : E × E | g q.1 = g q.2}) :=
    (hleft.prodMk hright).preimage_isClosed_of_isClosed
      (isClosed_closedBall.prod isClosed_closedBall)
      (isClosed_eq continuous_fst continuous_snd)
  have hs : points g ⊆ (closedBall 0 1 ×ˢ closedBall 0 1) ∩
      {q : E × E | g q.1 = g q.2} := fun q hq ↦
    ⟨⟨ball_subset_closedBall hq.1, ball_subset_closedBall hq.2.1⟩, hq.2.2.2⟩
  exact (closure_minimal hs hc hp).2

theorem closure_subset_interior (g : E → Y) (hg : ContinuousOn g (closedBall 0 1))
    (ρ : ℝ) (hρ : ρ < 1) (hi : InjOn g (closedBall 0 1 ∩ {x | ρ ≤ ‖x‖}))
    (hsep : ∀ x ∈ ball 0 1, ∀ y ∈ sphere 0 1, g x ≠ g y) :
    closure (points g) ⊆ ball 0 1 ×ˢ ball 0 1 := by
  intro p hp
  have hK := closure_subset_closedBall g hp
  have heq := closure_equal_image g hg hp
  have hinner := closure_subset_not_both_outer g ρ hi hp
  have hleft : ‖p.1‖ ≤ 1 := mem_closedBall_zero_iff.mp hK.1
  have hright : ‖p.2‖ ≤ 1 := mem_closedBall_zero_iff.mp hK.2
  constructor
  · apply mem_ball_zero_iff.mpr
    by_contra hn
    have he : ‖p.1‖ = 1 := le_antisymm hleft (le_of_not_gt hn)
    have hy : ‖p.2‖ < 1 := by
      rcases hinner with hx | hy
      · rw [he] at hx
        exact (not_le_of_gt hρ hx).elim
      · exact hy.trans_lt hρ
    exact hsep p.2 (mem_ball_zero_iff.mpr hy) p.1 (mem_sphere_zero_iff_norm.mpr he) heq.symm
  · apply mem_ball_zero_iff.mpr
    by_contra hn
    have he : ‖p.2‖ = 1 := le_antisymm hright (le_of_not_gt hn)
    have hx : ‖p.1‖ < 1 := by
      rcases hinner with hx | hy
      · exact hx.trans_lt hρ
      · rw [he] at hy
        exact (not_le_of_gt hρ hy).elim
    exact hsep p.1 (mem_ball_zero_iff.mpr hx) p.2 (mem_sphere_zero_iff_norm.mpr he) heq

end NoExoticSixSphere.DiskDoublePoints
