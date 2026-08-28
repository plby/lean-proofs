import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseBirth
import Wikipedia.HopfProblem.DegreeCollapseRegularBandReplacement

/-!
# A supported indexed birth below an untouched upper cut

The actual two new critical values stay inside the original regular
band. Compact-band control retains the literal strict sublevel of any
upper cut above that band, as well as the entire original upper germ.
All old critical germs and the exact indexed-count changes are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_indexed_birth_below_cut
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) {l u b : ℝ} (hub : u ≤ b)
    (hband : ∀ y, f y ∈ Icc l u → y ∉ criticalPoints E f)
    {x : M} (hx : f x ∈ Ioo l u) {k : ℕ} (hk : k < Module.finrank ℝ E) :
    ∃ (g : M → ℝ) (p q : M), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧ f p ∈ Ioo l u ∧ f q ∈ Ioo l u ∧
      nativeMorseIndex E g p = k ∧ nativeMorseIndex E g q = k + 1 ∧
      g p < g q ∧ g p ∈ Ioo l u ∧ g q ∈ Ioo l u ∧
      (criticalPoints E g).ncard = (criticalPoints E f).ncard + 2 ∧
      (∀ y, y ∈ criticalPoints E g ↔ y ∈ criticalPoints E f ∨ y = p ∨ y = q) ∧
      (∀ y, f y ∉ Ioo l u → g =ᶠ[𝓝 y] f) ∧
      (∀ y ∈ criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
      (∀ y, b ≤ f y → g =ᶠ[𝓝 y] f) ∧ (∀ y, g y < b ↔ f y < b) ∧
      nativeMorseCount E g k = nativeMorseCount E f k + 1 ∧
      nativeMorseCount E g (k + 1) = nativeMorseCount E f (k + 1) + 1 ∧
      ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  let U : Set M := f ⁻¹' Ioo l u
  have hU : IsOpen U := isOpen_Ioo.preimage hf.continuous
  obtain ⟨g, p, q, hg, hmg, hinjg, hpU, hqU, hip, hiq, hpq, hpval, hqval,
      hcount, hcrit, hexterior, hkeep, hcountk, hcountk', hother⟩ :=
    exists_excellent_indexed_morse_birth hf hm hinj
      (fun y hy => hband y ⟨hy.1.le, hy.2.le⟩) hx hk hU hx
  have hvalues (y : M) (hy : f y ∈ Icc l u) (hcy : y ∈ criticalPoints E g) :
      g y ∈ Ioo l u := by
    rcases (hcrit y).mp hcy with hold | rfl | rfl
    · exact (hband y hy hold).elim
    · exact hpval
    · exact hqval
  refine ⟨g, p, q, hg, hmg, hinjg, hpU, hqU, hip, hiq, hpq, hpval, hqval,
    hcount, hcrit, hexterior, hkeep, ?_, ?_, hcountk, hcountk', hother⟩
  · intro y hy
    apply hexterior y
    intro h
    exact (not_lt_of_ge hy) (h.2.trans_le hub)
  · intro y
    by_cases hy : f y ∈ Ioo l u
    · have hgy := RegularBandReplacement.mem_open_band_of_critical_values hf hg
        (fun z hz => (hexterior z hz).self_of_nhds) hvalues hy
      exact iff_of_true (hgy.2.trans_le hub) (hy.2.trans_le hub)
    · rw [(hexterior y hy).self_of_nhds]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
