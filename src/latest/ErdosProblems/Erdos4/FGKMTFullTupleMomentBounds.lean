import ErdosProblems.Erdos4.FGKMTConditionalTripleMoments
import ErdosProblems.Erdos4.TupleSurvivalBounds
import ErdosProblems.Erdos4.FGKMTFiniteLaw

/-! Joint survival accuracy supplies the three weighted moments for full-tuple conditioning. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical RandomResidueSieve AffineTuples TupleCollisionMass
open ConditionalTupleMoments TupleSurvivalBounds

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] {k : ℕ}

noncomputable def conditionalResidueLaw (q : ℕ) : FiniteLaw (∀ l, ZMod (ell l)) where
  weight := conditionalWeight ell q
  nonneg := conditionalWeight_nonneg ell q
  total := sum_conditionalWeight ell q

theorem conditionalResidueLaw_mean (q : ℕ) (f : (∀ l, ZMod (ell l)) → ℝ) :
    (conditionalResidueLaw ell q).mean f = mean ell q f := rfl

theorem full_tuple_mixed_moment_bounds (h : Fin k → ℕ) (hh : Function.Injective h)
    {p : ℕ} (hp : 0 < p) (Y B : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hacc : Accurate ell B (3 * k) ε)
    (hpoints : ∀ n ∈ Finset.Icc 1 Y, ∀ t ∈ tuple h p n, t ≤ B)
    (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n)
    (hμsum : ∑ n ∈ Finset.Icc 1 Y, μ n = 1)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) :
    let σ := UnitFourier.unitDensity ell
    let β := hitMass h p Y μ q
    mean ell q (hittingMass ell h p Y μ q) ≤ (1 + ε) * σ ^ (k - 1) * β ∧
    ((1 - ε) * σ ^ (2 * k - 1) * (1 - (k : ℝ) ^ 2 * α)) * β ≤
      mean ell q (fun a => tupleMass ell h p Y μ a * hittingMass ell h p Y μ q a) ∧
    mean ell q (fun a => tupleMass ell h p Y μ a ^ 2 * hittingMass ell h p Y μ q a) ≤
      ((1 + ε) * σ ^ (3 * k - 1) + 3 * (k : ℝ) ^ 2 * α) * β := by
  dsimp only
  have hσ : 0 < UnitFourier.unitDensity ell := UnitFourier.unitDensity_pos ell
  have hfirst := firstMoment_bounds ell h p Y μ q hμ0
    (L := (1 - ε) * UnitFourier.unitDensity ell ^ (k - 1))
    (U := (1 + ε) * UnitFourier.unitDensity ell ^ (k - 1))
    (fun n hn hqn => by
      have hc := card_tuple h hh hp n
      have hb := conditional_bounds ell hacc (tuple h p n) (by rw [hc]; omega)
        (hpoints n hn) q hqn
      simpa only [hc] using hb)
  refine ⟨hfirst.2, ?_, ?_⟩
  · apply mixed_product_lower ell h hh hp Y μ q hμ0 hμsum hα
      (mul_nonneg (sub_nonneg.mpr hε1) (pow_nonneg hσ.le _)) hμ
    intro n hn m hm hqm hd
    have hc : (tuple h p n ∪ tuple h p m).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hd, card_tuple h hh hp n, card_tuple h hh hp m]
      omega
    have hb := (conditional_bounds ell hacc _ (by rw [hc]; omega)
      (union_points_bound (hpoints n hn) (hpoints m hm)) q (Finset.mem_union_right _ hqm)).1
    simpa only [hc] using hb
  · apply mixed_square_product_upper ell h hh hp Y μ q hμ0 hμsum hα (by positivity) hμ
    intro m hm hqm n hn hnm r hr hrnm
    have hc : (tuple h p r ∪ (tuple h p n ∪ tuple h p m)).card = 3 * k := by
      rw [Finset.card_union_of_disjoint hrnm, Finset.card_union_of_disjoint hnm,
        card_tuple h hh hp r, card_tuple h hh hp n, card_tuple h hh hp m]
      omega
    have hb := (conditional_bounds ell hacc _ (by rw [hc])
      (union_points_bound (hpoints r hr) (union_points_bound (hpoints n hn) (hpoints m hm)))
      q (Finset.mem_union_right _ (Finset.mem_union_right _ hqm))).2
    simpa only [hc] using hb

end Erdos4.FGKMT
