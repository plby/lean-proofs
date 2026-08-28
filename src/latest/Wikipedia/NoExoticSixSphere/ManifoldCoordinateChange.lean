import Wikipedia.NoExoticSixSphere.ManifoldChartDerivative

/-!
# The actual derivative formula under overlapping manifold charts

The change-of-coordinates identity holds as an equality of germs. Its
derivative therefore uses the actual source and target chart transitions,
without assuming a global equality outside the chart domains.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldCoordinates

open GLOrthonormalization

def transition {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (c d : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (Vector n) (Vector n) ∞ := c.symm.trans d

theorem mem_transition_source {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (c d : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (x : M) (hc : x ∈ c.source) (hd : x ∈ d.source) :
    c x ∈ (transition c d).source := by
  have hleft : c.symm (c x) = x := c.left_inv hc
  change c x ∈ c.target ∧ c.symm (c x) ∈ d.source
  rw [hleft]
  exact ⟨c.map_source hc, hd⟩

theorem transition_apply {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (c d : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (x : M) (hc : x ∈ c.source) : transition c d (c x) = d x := by
  have hleft : c.symm (c x) = x := c.left_inv hc
  change d (c.symm (c x)) = d x
  rw [hleft]

theorem fderiv_change_charts {k n : ℕ} {X M : Type*}
    [TopologicalSpace X] [ChartedSpace (Vector k) X]
    [TopologicalSpace M] [ChartedSpace (Vector n) M]
    (g : X → M) (x : X) (hg : MDifferentiableAt (𝓡 k) (𝓡 n) g x)
    (s t : PartialDiffeomorph (𝓡 k) (𝓡 k) X (Vector k) ∞)
    (c d : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (hs : x ∈ s.source) (ht : x ∈ t.source)
    (hc : g x ∈ c.source) (hd : g x ∈ d.source) :
    fderiv ℝ (fun z ↦ d (g (t.symm z))) (t x) =
      (fderiv ℝ (transition c d) (c (g x))).comp
        ((fderiv ℝ (fun z ↦ c (g (s.symm z))) (s x)).comp
          (fderiv ℝ (transition t s) (t x))) := by
  let A := transition c d
  let B := transition t s
  let F : Vector k → Vector n := fun z ↦ c (g (s.symm z))
  let G : Vector k → Vector n := fun z ↦ d (g (t.symm z))
  have hsleft : s.symm (s x) = x := s.left_inv hs
  have htleft : t.symm (t x) = x := t.left_inv ht
  have hsI : MDifferentiableAt (𝓡 k) (𝓡 k) s.symm (s x) :=
    (s.contMDiffOn_invFun.contMDiffAt
      (s.open_target.mem_nhds (s.map_source hs))).mdifferentiableAt (by simp)
  have htI : MDifferentiableAt (𝓡 k) (𝓡 k) t.symm (t x) :=
    (t.contMDiffOn_invFun.contMDiffAt
      (t.open_target.mem_nhds (t.map_source ht))).mdifferentiableAt (by simp)
  have hgS : MDifferentiableAt (𝓡 k) (𝓡 n) g (s.symm (s x)) := by
    rw [hsleft]
    exact hg
  have hgT : MDifferentiableAt (𝓡 k) (𝓡 n) g (t.symm (t x)) := by
    rw [htleft]
    exact hg
  have hcS : MDifferentiableAt (𝓡 n) (𝓡 n) c (g (s.symm (s x))) := by
    rw [hsleft]
    exact (c.contMDiffOn_toFun.contMDiffAt
      (c.open_source.mem_nhds hc)).mdifferentiableAt (by simp)
  have hF : DifferentiableAt ℝ F (s x) :=
    (hcS.comp (s x) (hgS.comp (s x) hsI)).differentiableAt
  have hB : DifferentiableAt ℝ B (t x) :=
    (B.contMDiffOn_toFun.contDiffOn.contDiffAt
      (B.open_source.mem_nhds (mem_transition_source t s x ht hs))).differentiableAt (by simp)
  have hA : DifferentiableAt ℝ A (c (g x)) :=
    (A.contMDiffOn_toFun.contDiffOn.contDiffAt
      (A.open_source.mem_nhds (mem_transition_source c d (g x) hc hd))).differentiableAt (by simp)
  have hB0 : B (t x) = s x := transition_apply t s x ht
  have hF0 : F (s x) = c (g x) := by change c (g (s.symm (s x))) = _; rw [hsleft]
  have hNs : ∀ᶠ z in 𝓝 (t x), t.symm z ∈ s.source :=
    htI.continuousAt.preimage_mem_nhds
      (s.open_source.mem_nhds (show t.symm (t x) ∈ s.source from htleft.symm ▸ hs))
  have hNc : ∀ᶠ z in 𝓝 (t x), g (t.symm z) ∈ c.source :=
    (hgT.continuousAt.comp htI.continuousAt).preimage_mem_nhds
      (c.open_source.mem_nhds (show g (t.symm (t x)) ∈ c.source from htleft.symm ▸ hc))
  have he : G =ᶠ[𝓝 (t x)] A ∘ (F ∘ B) := by
    filter_upwards [hNs, hNc] with z hzs hzc
    have hs' : s.symm (s (t.symm z)) = t.symm z := s.left_inv hzs
    have hc' : c.symm (c (g (t.symm z))) = g (t.symm z) := c.left_inv hzc
    change d (g (t.symm z)) = d (c.symm (c (g (s.symm (s (t.symm z))))))
    rw [hs', hc']
  have hF' : DifferentiableAt ℝ F (B (t x)) := by rw [hB0]; exact hF
  have hA' : DifferentiableAt ℝ A (F (B (t x))) := by rw [hB0, hF0]; exact hA
  change fderiv ℝ G (t x) = (fderiv ℝ A (c (g x))).comp
    ((fderiv ℝ F (s x)).comp (fderiv ℝ B (t x)))
  rw [he.fderiv_eq, fderiv_comp (t x) hA' (hF'.comp (t x) hB),
    fderiv_comp (t x) hF' hB, Function.comp_apply, hB0, hF0]

end NoExoticSixSphere.ManifoldCoordinates
