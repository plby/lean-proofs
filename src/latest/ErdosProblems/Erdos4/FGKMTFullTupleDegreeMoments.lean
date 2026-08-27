import ErdosProblems.Erdos4.FGKMTFullTupleMomentBounds
import ErdosProblems.Erdos4.FGKMTFullTranslatedTuples
import ErdosProblems.Erdos4.FGKMTCombinedPrimeFamily

/-! Aggregate pinned-target moments for arbitrary bounded injective shifts. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical AffineTuples TupleCollisionMass ConditionalTupleMoments TupleSurvivalBounds
open AggregatedTupleMoments

theorem full_tuple_intersection_eq_singleton {k : ℕ} (h : Fin k → ℕ)
    {p p' n n' q : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p' ≠ p)
    (hinj : Function.Injective (fun i => (h i : ZMod p)))
    (hq : q ∈ tuple h p n) (hq' : q ∈ tuple h p' n') :
    tuple h p n ∩ tuple h p' n' = {q} := by
  ext r
  constructor
  · intro hr
    have hrr := Finset.mem_inter.mp hr
    apply Finset.mem_singleton.mpr
    exact (translatedSites_common_point_unique h hp hp' hne hinj hq hrr.1 hq' hrr.2).symm
  · intro hr
    rw [Finset.mem_singleton.mp hr]
    exact Finset.mem_inter.mpr ⟨hq, hq'⟩

theorem full_tuple_anchored_union_card {k : ℕ} (h : Fin k → ℕ)
    (hh : Function.Injective h) {p p' n n' q : ℕ}
    (hp : p.Prime) (hp' : p'.Prime) (hne : p' ≠ p)
    (hinj : Function.Injective (fun i => (h i : ZMod p)))
    (hq : q ∈ tuple h p n) (hq' : q ∈ tuple h p' n') :
    (tuple h p n ∪ tuple h p' n').card = 2 * k - 1 := by
  have hc := Finset.card_union_add_card_inter (tuple h p n) (tuple h p' n')
  rw [full_tuple_intersection_eq_singleton h hp hp' hne hinj hq hq', Finset.card_singleton,
    card_tuple h hh hp.pos n, card_tuple h hh hp'.pos n'] at hc
  omega

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] {k : ℕ}

theorem full_tuple_total_moment_bounds (h : Fin k → ℕ) (hh : Function.Injective h)
    (sources : Finset ℕ) (Y B : ℕ) (μ : ℕ → ℕ → ℝ) (q : ℕ)
    {ε α : ℝ} (hε : 0 ≤ ε) (hα : 0 ≤ α)
    (hacc : Accurate ell B (3 * k) ε)
    (hs : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p)
    (hpoints : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, ∀ t ∈ tuple h p n, t ≤ B)
    (hμ0 : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, μ p n ≤ α) :
    let σ := UnitFourier.unitDensity ell
    let β := ∑ p : sources, hitMass h p Y (μ p) q
    (1 - ε) * σ ^ (k - 1) * β ≤
      mean ell q (fun a => ∑ p : sources, hittingMass ell h p Y (μ p) q a) ∧
    mean ell q (fun a => (∑ p : sources, hittingMass ell h p Y (μ p) q a) ^ 2) ≤
      (1 + ε) * σ ^ (2 * k - 2) * β ^ 2 + (k : ℝ) * α * β := by
  dsimp only
  have hσ := UnitFourier.unitDensity_pos ell
  constructor
  · apply firstMoment_lower ell h sources Y μ q hμ0
    intro p hp n hn hqn
    have hc := card_tuple h hh (hs p hp).1.pos n
    have hb := (conditional_bounds ell hacc _ (by rw [hc]; omega)
      (hpoints p hp n hn) q hqn).1
    simpa only [hc] using hb
  · apply secondMoment_le ell h sources Y μ q hα (by positivity) hμ0 hμ
    intro p hp p' hp' hne n hn m hm hqn hqm
    letI : Fact p.Prime := ⟨(hs p hp).1⟩
    have hinj := natCast_shifts_injective h hh (hs p hp).2
    have hc := full_tuple_anchored_union_card h hh (hs p hp).1 (hs p' hp').1
      (Ne.symm hne) hinj hqn hqm
    have hb := (conditional_bounds ell hacc _ (by rw [hc]; omega)
      (union_points_bound (hpoints p hp n hn) (hpoints p' hp' m hm))
      q (Finset.mem_union_left _ hqn)).2
    simpa only [hc, Nat.sub_sub, Nat.reduceAdd] using hb

end Erdos4.FGKMT
