import Wikipedia.HopfProblem.DegreeCollapseNativeMorseBirth

/-!
# A birth in a regular value band preserves excellence

The new cubic critical values lie strictly between the original heights
of the two inserted points, and hence in the prescribed regular value
band. They are distinct and cannot equal an old critical value. All old
critical values are retained by their actual function germs.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem injOn_of_two_new_values {X : Type*} {f g : X → ℝ} {C : Set X} {p q : X}
    (hinj : InjOn f C) (hkeep : ∀ y ∈ C, g y = f y)
    (hp : g p ∉ f '' C) (hq : g q ∉ f '' C) (hpq : g p ≠ g q) :
    InjOn g {y | y ∈ C ∨ y = p ∨ y = q} := by
  intro y hy z hz heq
  rcases hy with hy | rfl | rfl
  · rcases hz with hz | rfl | rfl
    · exact hinj hy hz ((hkeep y hy).symm.trans (heq.trans (hkeep z hz)))
    · exact False.elim (hp ⟨y, hy, (hkeep y hy).symm.trans heq⟩)
    · exact False.elim (hq ⟨y, hy, (hkeep y hy).symm.trans heq⟩)
  · rcases hz with hz | rfl | rfl
    · exact False.elim (hp ⟨z, hz, (hkeep z hz).symm.trans heq.symm⟩)
    · rfl
    · exact False.elim (hpq heq)
  · rcases hz with hz | rfl | rfl
    · exact False.elim (hq ⟨z, hz, (hkeep z hz).symm.trans heq.symm⟩)
    · exact False.elim (hpq heq.symm)
    · rfl

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_excellent_native_morse_birth {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    {l u : ℝ} (hband : ∀ y, f y ∈ Ioo l u → y ∉ criticalPoints E f)
    {x : M} (hx : f x ∈ Ioo l u) {m : ℕ}
    (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a δ : ℝ, 0 < a ∧ 0 < δ ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
        (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧ (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ.target ⊆ U ∧
        ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
          InjOn g (criticalPoints E g) ∧
          (criticalPoints E g).ncard = (criticalPoints E f).ncard + 2 ∧
          (∀ y, y ∈ criticalPoints E g ↔
            y ∈ criticalPoints E f ∨ y = Φ (a, 0) ∨ y = Φ (-a, 0)) ∧
          (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
          (∀ y ∈ criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
          g (Φ (a, 0)) < g (Φ (-a, 0)) ∧
          g (Φ (a, 0)) ∈ Ioo l u ∧ g (Φ (-a, 0)) ∈ Ioo l u ∧
          (g ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => f x + δ * cubic σ (-(a ^ 2)) z) ∧
          (g ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z => f x + δ * cubic σ (-(a ^ 2)) z) := by
  obtain ⟨a, δ, ha, hδ, Φ, hp, hq, hΦ, hmodel, g, hg, hmg, hcount, hcrit,
      hexterior, hkeep, hgp, hgq⟩ := exists_native_morse_birth hf hm (hband x hx) hdim σ hσ
    (hU.inter (isOpen_Ioo.preimage hf.continuous)) ⟨hxU, hx⟩
  have hpa : f (Φ (a, 0)) = f x + δ * (4 * a ^ 3 / 3) := by
    rw [hmodel (a, 0) hp]
    simp only [cubic, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), mul_zero,
      Finset.sum_const_zero, add_zero]
    ring
  have hqa : f (Φ (-a, 0)) = f x - δ * (4 * a ^ 3 / 3) := by
    rw [hmodel (-a, 0) hq]
    simp only [cubic, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), mul_zero,
      Finset.sum_const_zero, add_zero]
    ring
  have hpval : g (Φ (a, 0)) = f x - δ * (2 * a ^ 3 / 3) := by
    have hh := hgp.self_of_nhds
    change g (Φ (a, 0)) = f x + δ * cubic σ (-(a ^ 2)) (a, 0) at hh
    rw [(cubic_critical_values σ a).1] at hh
    exact hh.trans (by ring)
  have hqval : g (Φ (-a, 0)) = f x + δ * (2 * a ^ 3 / 3) := by
    have hh := hgq.self_of_nhds
    change g (Φ (-a, 0)) = f x + δ * cubic σ (-(a ^ 2)) (-a, 0) at hh
    rw [(cubic_critical_values σ a).2] at hh
    exact hh
  have hpos : 0 < δ * (2 * a ^ 3 / 3) := by positivity
  have hpq : g (Φ (a, 0)) < g (Φ (-a, 0)) := by rw [hpval, hqval]; linarith
  have hpband : g (Φ (a, 0)) ∈ Ioo l u := by
    have hb := (hΦ (Φ.map_source' hq)).2
    change f (Φ (-a, 0)) ∈ Ioo l u at hb
    rw [hqa] at hb
    rw [hpval]
    constructor <;> nlinarith [hb.1, hx.2]
  have hqband : g (Φ (-a, 0)) ∈ Ioo l u := by
    have hb := (hΦ (Φ.map_source' hp)).2
    change f (Φ (a, 0)) ∈ Ioo l u at hb
    rw [hpa] at hb
    rw [hqval]
    constructor <;> nlinarith [hx.1, hb.2]
  have hnot (v : ℝ) (hv : v ∈ Ioo l u) : v ∉ f '' criticalPoints E f := by
    rintro ⟨y, hy, rfl⟩
    exact hband y hv hy
  have hinjg : InjOn g (criticalPoints E g) := by
    have hh := injOn_of_two_new_values hinj (fun y hy => (hkeep y hy).self_of_nhds)
      (hnot _ hpband) (hnot _ hqband) hpq.ne
    intro y hy z hz heq
    exact hh ((hcrit y).mp hy) ((hcrit z).mp hz) heq
  refine ⟨a, δ, ha, hδ, Φ, hp, hq, fun _ hy => (hΦ hy).1,
    g, hg, hmg, hinjg, hcount, hcrit, ?_, hkeep, hpq, hpband, hqband, hgp, hgq⟩
  intro y hy
  exact hexterior y (fun hh => hy hh.1)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
