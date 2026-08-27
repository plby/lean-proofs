import ErdosProblems.Erdos4.FGKMTUniformResidueLaw

/-! Freeze one initial sieve with small survivor and exceptional-survivor counts. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical RandomResidueSieve

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def initialSurvivors (Y : ℕ) (targets : Finset ℕ)
    (a : ∀ l, ZMod (ell l)) : Finset targets :=
  Finset.univ.filter (fun q : targets => Survives ell a {q.val + Y})

noncomputable def initialBadSurvivors (Y : ℕ) (targets : Finset ℕ) (bad : Finset targets)
    (E : (∀ l, ZMod (ell l)) → targets → Prop) (a : ∀ l, ZMod (ell l)) : Finset targets :=
  Finset.univ.filter (fun q : targets => Survives ell a {q.val + Y} ∧ (q ∈ bad ∨ E a q))

theorem mean_initialSurvivors (Y : ℕ) (targets : Finset ℕ) :
    (uniformResidueLaw ell).mean (fun a => ((initialSurvivors ell Y targets a).card : ℝ)) =
      UnitFourier.unitDensity ell * targets.card := by
  unfold initialSurvivors
  rw [FiniteLaw.mean_filter_card]
  simp only [uniformResidueLaw_singleton, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_comm]

theorem mean_initialBadSurvivors_le (Y : ℕ) (targets : Finset ℕ) (bad : Finset targets)
    (E : (∀ l, ZMod (ell l)) → targets → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ q : targets, q ∉ bad →
      (conditionalResidueLaw ell (q.val + Y)).prob (fun a => E a q) ≤ ε) :
    (uniformResidueLaw ell).mean (fun a => ((initialBadSurvivors ell Y targets bad E a).card : ℝ)) ≤
      UnitFourier.unitDensity ell * ((bad.card : ℝ) + ε * targets.card) := by
  unfold initialBadSurvivors
  rw [(uniformResidueLaw ell).mean_filter_card
    (fun a (q : targets) => Survives ell a {q.val + Y} ∧ (q ∈ bad ∨ E a q))]
  simp_rw [uniform_surviving_event_eq]
  calc
    _ ≤ ∑ q : targets, UnitFourier.unitDensity ell * ((if q ∈ bad then 1 else 0) + ε) := by
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (UnitFourier.unitDensity_pos ell).le
      by_cases hq : q ∈ bad
      · have hp := (conditionalResidueLaw ell (q.val + Y)).prob_le_one (fun a => q ∈ bad ∨ E a q)
        simp only [if_pos hq]
        linarith
      · simpa only [hq, false_or, if_false, zero_add] using hbad q hq
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      have hb : (Finset.univ.filter (fun q : targets => q ∈ bad)) = bad := by
        ext q
        simp
      rw [Finset.sum_boole, hb]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, mul_comm ε]

theorem exists_initial_sieve_good_vertices (Y : ℕ) (targets : Finset ℕ) (bad : Finset targets)
    (E : (∀ l, ZMod (ell l)) → targets → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ q : targets, q ∉ bad →
      (conditionalResidueLaw ell (q.val + Y)).prob (fun a => E a q) ≤ ε) :
    ∃ (a : ∀ l, ZMod (ell l)) (V : Finset targets),
      V ⊆ initialSurvivors ell Y targets a ∧
      (∀ q ∈ V, q ∉ bad ∧ ¬ E a q) ∧
      (V.card : ℝ) ≤ 2 * (UnitFourier.unitDensity ell * targets.card + 1) ∧
      ((initialSurvivors ell Y targets a \ V).card : ℝ) ≤
        2 * (UnitFourier.unitDensity ell * ((bad.card : ℝ) + ε * targets.card) + 1) := by
  let σ := UnitFourier.unitDensity ell
  have hσ : 0 < σ := UnitFourier.unitDensity_pos ell
  let f := fun a => ((initialSurvivors ell Y targets a).card : ℝ)
  let g := fun a => ((initialBadSurvivors ell Y targets bad E a).card : ℝ)
  have hf0 : ∀ a, 0 ≤ f a := fun a => Nat.cast_nonneg _
  have hg0 : ∀ a, 0 ≤ g a := fun a => Nat.cast_nonneg _
  have hA : 0 < σ * targets.card + 1 := by positivity
  have hB : 0 < σ * ((bad.card : ℝ) + ε * targets.card) + 1 := by positivity
  have hf : (uniformResidueLaw ell).mean f ≤ σ * targets.card + 1 := by
    rw [show (uniformResidueLaw ell).mean f = σ * targets.card from mean_initialSurvivors ell Y targets]
    linarith
  have hg : (uniformResidueLaw ell).mean g ≤ σ * ((bad.card : ℝ) + ε * targets.card) + 1 := by
    have hh := mean_initialBadSurvivors_le ell Y targets bad E hε hbad
    change (uniformResidueLaw ell).mean g ≤ σ * ((bad.card : ℝ) + ε * targets.card) at hh
    linarith
  obtain ⟨a, _, hfa, hga⟩ := (uniformResidueLaw ell).exists_two_mean_bounds f g hf0 hg0 hA hB hf hg
  let V := initialSurvivors ell Y targets a \ initialBadSurvivors ell Y targets bad E a
  have hsub : V ⊆ initialSurvivors ell Y targets a := Finset.sdiff_subset
  refine ⟨a, V, hsub, ?_, ?_, ?_⟩
  · intro q hq
    have hqs := (Finset.mem_sdiff.mp hq).1
    have hnot := (Finset.mem_sdiff.mp hq).2
    have hS := (Finset.mem_filter.mp hqs).2
    have hh : ¬ (q ∈ bad ∨ E a q) := by
      intro hb
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hS, hb⟩)
    exact not_or.mp hh
  · have hh : (V.card : ℝ) ≤ f a := by
      dsimp only [f]
      exact_mod_cast Finset.card_le_card hsub
    exact hh.trans hfa
  · have hc : initialSurvivors ell Y targets a \ V ⊆ initialBadSurvivors ell Y targets bad E a := by
      intro q hq
      have hs := (Finset.mem_sdiff.mp hq).1
      have hv := (Finset.mem_sdiff.mp hq).2
      by_contra hb
      exact hv (Finset.mem_sdiff.mpr ⟨hs, hb⟩)
    have hh : ((initialSurvivors ell Y targets a \ V).card : ℝ) ≤ g a := by
      dsimp only [g]
      exact_mod_cast Finset.card_le_card hc
    exact hh.trans hga

end Erdos4.FGKMT
