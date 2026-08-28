import Wikipedia.HopfProblem.DegreeCollapseExcellentMorseBirth
import Wikipedia.HopfProblem.DegreeCollapseCubicBirthIndices
import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseCancellation
import Mathlib.Data.Fintype.Fin

/-!
# An excellent native birth with prescribed adjacent intrinsic indices

Choose exactly `k` negative transverse coordinates. The constructed native
birth has lower index `k` and upper index `k+1`, both new values in the
regular band, and every old critical germ retained. The actual critical
count rises by two. This supplies the two/three creation move in dimension
six, without claiming the later geometric trade with an existing one-handle.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem exists_transverse_signs_of_count {m k : ℕ} (hk : k ≤ m) :
    ∃ σ : Fin m → ℝ, (∀ i, σ i = -1 ∨ σ i = 1) ∧
      {i | σ i = -1}.ncard = k := by
  classical
  let σ : Fin m → ℝ := fun i => if i.val < k then -1 else 1
  refine ⟨σ, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < k
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · have heq : {i : Fin m | σ i = -1} = {i : Fin m | i.val < k} := by
      ext i
      by_cases hi : i.val < k <;> norm_num [σ, hi]
    rw [heq, ← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
    simp only [mem_setOf_eq]
    rw [Fin.card_filter_val_lt, min_eq_right hk]

theorem exists_excellent_indexed_morse_birth {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    {l u : ℝ} (hband : ∀ y, f y ∈ Ioo l u → y ∉ criticalPoints E f)
    {x : M} (hx : f x ∈ Ioo l u) {k : ℕ} (hk : k < Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (g : M → ℝ) (p q : M), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧ p ∈ U ∧ q ∈ U ∧
      nativeMorseIndex E g p = k ∧ nativeMorseIndex E g q = k + 1 ∧
      g p < g q ∧ g p ∈ Ioo l u ∧ g q ∈ Ioo l u ∧
      (criticalPoints E g).ncard = (criticalPoints E f).ncard + 2 ∧
      (∀ y, y ∈ criticalPoints E g ↔ y ∈ criticalPoints E f ∨ y = p ∨ y = q) ∧
      (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
      (∀ y ∈ criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
      nativeMorseCount E g k = nativeMorseCount E f k + 1 ∧
      nativeMorseCount E g (k + 1) = nativeMorseCount E f (k + 1) + 1 ∧
      ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  classical
  let m := Module.finrank ℝ E - 1
  have hdim : 1 + m = Module.finrank ℝ E := by dsimp [m]; omega
  have hkm : k ≤ m := by dsimp [m]; omega
  obtain ⟨σ, hσ, hcard⟩ := exists_transverse_signs_of_count hkm
  have hσne (i : Fin m) : σ i ≠ 0 := by rcases hσ i with h | h <;> rw [h] <;> norm_num
  obtain ⟨a, δ, ha, hδ, Φ, hp, hq, hΦ, g, hg, hmg, hinjg, hcount, hcrit,
      hexterior, hkeep, hpq, hpband, hqband, hgp, hgq⟩ :=
    exists_excellent_native_morse_birth hf hm hinj hband hx hdim σ hσne hU hxU
  obtain ⟨hip, hiq⟩ := native_indices_of_cubic_birth_germs Φ hdim σ hσ ha hδ hp hq hgp hgq
  have hc : Fintype.card {i // σ i = -1} = k := (Set.fintypeCard_eq_ncard _).trans hcard
  rw [hc] at hip hiq
  have hpnot : Φ (a, 0) ∉ criticalPoints E f := by
    intro h
    have hv : g (Φ (a, 0)) = f (Φ (a, 0)) := (hkeep _ h).self_of_nhds
    exact hband _ (hv ▸ hpband) h
  have hqnot : Φ (-a, 0) ∉ criticalPoints E f := by
    intro h
    have hv : g (Φ (-a, 0)) = f (Φ (-a, 0)) := (hkeep _ h).self_of_nhds
    exact hband _ (hv ▸ hqband) h
  have hreverse (y : M) : y ∈ criticalPoints E f ↔
      y ∈ criticalPoints E g ∧ y ≠ Φ (a, 0) ∧ y ≠ Φ (-a, 0) := by
    rw [hcrit]
    constructor
    · intro hy
      exact ⟨Or.inl hy, fun h => hpnot (h ▸ hy), fun h => hqnot (h ▸ hy)⟩
    · rintro ⟨hy | hp' | hq', hnp, hnq⟩
      · exact hy
      · exact False.elim (hnp hp')
      · exact False.elim (hnq hq')
  have hpcrit := (hcrit (Φ (a, 0))).mpr (Or.inr (Or.inl rfl))
  have hqcrit := (hcrit (Φ (-a, 0))).mpr (Or.inr (Or.inr rfl))
  have hneq : Φ (a, 0) ≠ Φ (-a, 0) := fun h => hpq.ne (congrArg g h)
  obtain ⟨hck, hck', hcothers⟩ := nativeMorseCount_adjacent_pair
    (finite_criticalPoints hg hmg) hpcrit hqcrit hneq hreverse (fun y hy => (hkeep y hy).symm) hip hiq
  exact ⟨g, Φ (a, 0), Φ (-a, 0), hg, hmg, hinjg, hΦ (Φ.map_source' hp),
    hΦ (Φ.map_source' hq), hip, hiq, hpq, hpband, hqband, hcount, hcrit, hexterior, hkeep,
    hck.symm, hck'.symm, fun j hj hj' => (hcothers j hj hj').symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
