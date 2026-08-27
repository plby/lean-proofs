import ErdosProblems.Erdos4.FGKMTTranslatedMomentLaw
import ErdosProblems.Erdos4.FGKMTFullTupleMomentBounds

/-! Finite target edges, their residue classes, and exact full-tuple survival probabilities. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical AffineTuples ConditionalTupleMoments RandomResidueSieve

variable {k : ℕ}

noncomputable def initialTargetEdge (h : Fin k → ℕ) (p Y : ℕ) (targets : Finset ℕ) (n : ℕ) :
    Finset targets := Finset.univ.filter (fun q : targets => q.val + Y ∈ translatedSites h p n)

theorem mem_initialTargetEdge (h : Fin k → ℕ) (p Y : ℕ) (targets : Finset ℕ)
    (n : ℕ) (q : targets) :
    q ∈ initialTargetEdge h p Y targets n ↔ q.val + Y ∈ translatedSites h p n := by
  simp only [initialTargetEdge, Finset.mem_filter, Finset.mem_univ, true_and]

theorem initialTargetEdge_card_le (h : Fin k → ℕ) (p Y : ℕ) (targets : Finset ℕ) (n : ℕ) :
    (initialTargetEdge h p Y targets n).card ≤ k := by
  have hi : Function.Injective (fun q : targets => q.val + Y) := by
    intro q r hqr
    exact Subtype.ext (Nat.add_right_cancel hqr)
  have hsub : (initialTargetEdge h p Y targets n).image (fun q : targets => q.val + Y) ⊆
      translatedSites h p n := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact (mem_initialTargetEdge h p Y targets n q).mp hq
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hi] at hh
  exact hh.trans (translatedSites_card_le h p n)

theorem initialTargetEdge_residue (h : Fin k → ℕ) (p Y : ℕ) (targets : Finset ℕ)
    (n : ℕ) (q : targets) (hq : q ∈ initialTargetEdge h p Y targets n) :
    (q.val : ZMod p) = (n : ZMod p) - (Y : ZMod p) := by
  obtain ⟨i, hi⟩ := (mem_translatedSites h p n (q.val + Y)).mp
    ((mem_initialTargetEdge h p Y targets n q).mp hq)
  apply (eq_sub_iff_add_eq).mpr
  have hh := congrArg (fun t : ℕ => (t : ZMod p)) hi
  simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero] using hh.symm

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem initialTargetEdge_survives (h : Fin k → ℕ) (p Y : ℕ) (targets : Finset ℕ)
    (n : ℕ) (a : ∀ l, ZMod (ell l)) (hS : Survives ell a (translatedSites h p n))
    (q : targets) (hq : q ∈ initialTargetEdge h p Y targets n) :
    Survives ell a {q.val + Y} := by
  have hpoint := (mem_initialTargetEdge h p Y targets n q).mp hq
  have hsub : ({q.val + Y} : Finset ℕ) ⊆ translatedSites h p n := Finset.singleton_subset_iff.mpr hpoint
  intro l hl
  exact hS l ((Finset.image_subset_image hsub) hl)

theorem center_survival_prob_eq_tupleMass (h : Fin k → ℕ) (p Y : ℕ)
    (μ : FiniteLaw (TranslatedCenter Y)) (w : ℕ → ℝ)
    (hw : ∀ n : TranslatedCenter Y, μ.weight n = w n.val) (a : ∀ l, ZMod (ell l)) :
    μ.prob (fun n => Survives ell a (translatedSites h p n.val)) =
      tupleMass ell h p (2 * Y) w a := by
  rw [FiniteLaw.prob_eq_mean]
  unfold FiniteLaw.mean tupleMass
  calc
    _ = ∑ n : TranslatedCenter Y, w n.val * indicator ell a (tuple h p n.val) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hw n]
      rfl
    _ = _ := Finset.sum_coe_sort (Finset.Icc 1 (2 * Y))
      (fun n : ℕ => w n * indicator ell a (tuple h p n))

theorem center_pinned_prob_eq_hittingMass (h : Fin k → ℕ) (p Y : ℕ) (targets : Finset ℕ)
    (μ : FiniteLaw (TranslatedCenter Y)) (w : ℕ → ℝ)
    (hw : ∀ n : TranslatedCenter Y, μ.weight n = w n.val)
    (a : ∀ l, ZMod (ell l)) (q : targets) :
    μ.prob (fun n => Survives ell a (translatedSites h p n.val) ∧
      q ∈ initialTargetEdge h p Y targets n.val) =
      hittingMass ell h p (2 * Y) w (q.val + Y) a := by
  rw [FiniteLaw.prob_eq_mean]
  unfold FiniteLaw.mean hittingMass
  calc
    _ = ∑ n : TranslatedCenter Y,
        (if q.val + Y ∈ tuple h p n.val then w n.val else 0) *
          indicator ell a (tuple h p n.val) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hw n]
      simp only [mem_initialTargetEdge]
      change w n.val * (if Survives ell a (tuple h p n.val) ∧ q.val + Y ∈ tuple h p n.val then 1 else 0) = _
      by_cases hS : Survives ell a (tuple h p n.val) <;>
        by_cases hq : q.val + Y ∈ tuple h p n.val <;> simp [indicator, hS, hq]
    _ = _ := Finset.sum_coe_sort (Finset.Icc 1 (2 * Y))
      (fun n : ℕ => (if q.val + Y ∈ tuple h p n then w n else 0) * indicator ell a (tuple h p n))

end Erdos4.FGKMT
