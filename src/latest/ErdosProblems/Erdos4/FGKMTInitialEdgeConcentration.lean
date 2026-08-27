import ErdosProblems.Erdos4.FGKMTFullTupleRetainedTail
import ErdosProblems.Erdos4.FGKMTInitialRetainedDegree
import ErdosProblems.Erdos4.FGKMTInitialTargetEdges

/-! Conditional degree concentration for the actual laws of clipped translated edges. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical AffineTuples TupleCollisionMass ConditionalTupleMoments TupleSurvivalBounds
  RandomResidueSieve

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] {k Y : ℕ}

noncomputable def translatedInitialEdgeLaw (h : Fin k → ℕ) (hY : 1 ≤ Y)
    (targets : Finset ℕ) (μ : FiniteLaw (TranslatedCenter Y)) (p : ℕ)
    (a : ∀ l, ZMod (ell l)) : FiniteLaw (Finset targets) :=
  initialEdgeLaw μ (fun n => Survives ell a (translatedSites h p n.val))
    (fun n => initialTargetEdge h p Y targets n.val)
    (UnitFourier.unitDensity ell) k (firstTranslatedCenter hY)

theorem translated_initial_degree_lower_tail (hk : 1 ≤ k)
    (h : Fin k → ℕ) (hh : Function.Injective h) (hY : 1 ≤ Y)
    (sources targets : Finset ℕ) (B : ℕ)
    (μ : ℕ → FiniteLaw (TranslatedCenter Y)) (w : ℕ → ℕ → ℝ)
    (hw : ∀ p ∈ sources, ∀ n : TranslatedCenter Y, (μ p).weight n = w p n.val)
    (q : targets) {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hacc : Accurate ell B (3 * k) ε)
    (hs : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p)
    (hpoints : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 (2 * Y), ∀ t ∈ tuple h p n, t ≤ B)
    (hatom : ∀ p ∈ sources, ∀ n : TranslatedCenter Y, (μ p).weight n ≤ α)
    (hβ : 0 < ∑ p : sources, hitMass h p (2 * Y) (w p) (q.val + Y)) :
    let σ := UnitFourier.unitDensity ell
    let β := ∑ p : sources, hitMass h p (2 * Y) (w p) (q.val + Y)
    (conditionalResidueLaw ell (q.val + Y)).prob (fun a =>
      (∑ p : sources,
        (translatedInitialEdgeLaw ell h hY targets (μ p) p a).prob (fun e => q ∈ e)) <
          β / (6 * σ)) ≤
      76 * ε + 4 * (k : ℝ) * α / (σ ^ (2 * k - 2) * β) +
        80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k - 1) := by
  let σ := UnitFourier.unitDensity ell
  let β := ∑ p : sources, hitMass h p (2 * Y) (w p) (q.val + Y)
  have hσ : 0 < σ := UnitFourier.unitDensity_pos ell
  have hw0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 (2 * Y), 0 ≤ w p n := by
    intro p hp n hn
    exact (hw p hp ⟨n, hn⟩) ▸ (μ p).nonneg ⟨n, hn⟩
  have hwsum : ∀ p ∈ sources, ∑ n ∈ Finset.Icc 1 (2 * Y), w p n = 1 := by
    intro p hp
    calc
      _ = ∑ n : TranslatedCenter Y, w p n.val :=
        (Finset.sum_coe_sort (Finset.Icc 1 (2 * Y)) (w p)).symm
      _ = ∑ n : TranslatedCenter Y, (μ p).weight n := by
        apply Finset.sum_congr rfl
        intro n _
        exact (hw p hp n).symm
      _ = 1 := (μ p).total
  have hwα : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 (2 * Y), w p n ≤ α := by
    intro p hp n hn
    exact (hw p hp ⟨n, hn⟩) ▸ hatom p hp ⟨n, hn⟩
  have ht := full_tuple_retained_lower_tail ell hk h hh sources (2 * Y) B w (q.val + Y)
    hε0 hε1 hα hacc hs hpoints hw0 hwsum hwα hβ
  apply le_trans _ ht
  apply (conditionalResidueLaw ell (q.val + Y)).prob_mono
  intro a ha
  by_contra hret
  have hret' := le_of_not_gt hret
  let E : sources → TranslatedCenter Y → Prop :=
    fun p n => Survives ell a (translatedSites h p n.val)
  let edge : sources → TranslatedCenter Y → Finset targets :=
    fun p n => initialTargetEdge h p Y targets n.val
  have hX : ∀ p : sources, initialCenterNormalizer (μ p) (E p) σ k =
      tupleMass ell h p (2 * Y) (w p) a / σ ^ k := by
    intro p
    unfold initialCenterNormalizer
    rw [center_survival_prob_eq_tupleMass ell h p Y (μ p) (w p) (hw p p.property)]
  have hZ : ∀ p : sources, initialPinnedIncidence (μ p) (E p) (edge p) σ k q =
      hittingMass ell h p (2 * Y) (w p) (q.val + Y) a / σ ^ (k - 1) := by
    intro p
    unfold initialPinnedIncidence
    rw [center_pinned_prob_eq_hittingMass ell h p Y targets (μ p) (w p) (hw p p.property)]
  have hdegree := initial_degree_lower_of_retained (fun p : sources => μ p) E edge hσ hk
    (fun _ => firstTranslatedCenter hY) q (β := β) (by
      simp_rw [hX, hZ]
      rw [← Finset.sum_div]
      exact hret')
  exact (not_lt_of_ge hdegree) ha

end Erdos4.FGKMT
