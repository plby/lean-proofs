import ErdosProblems.Erdos4.ConditionalTupleMoments

/-!
# Exact product moments and the mixed collision error

Products of tuple masses are expanded into joint survival of unions.
For one source, disjoint tuple pairs contribute the expected main scale;
all intersecting pairs are bounded by the proved small-atom collision
mass. No independence assumption is made for intersecting tuples.
-/

open scoped BigOperators

namespace Erdos4.ConditionalProductMoments

open RandomResidueSieve AffineTuples TupleCollisionMass ConditionalTupleMoments

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem mean_indicator_le_one (q : ℕ) (T : Finset ℕ) :
    mean ell q (fun a => indicator ell a T) ≤ 1 :=
  (mean_mono ell q _ (fun _ => 1) (fun a => indicator_le_one ell a T)).trans_eq
    (mean_const ell q 1)

theorem mean_product_expansions {I J : Type*} (s : Finset I) (t : Finset J)
    (q : ℕ) (c : I → ℝ) (d : J → ℝ) (T : I → Finset ℕ) (U : J → Finset ℕ) :
    mean ell q (fun a => (∑ i ∈ s, c i * indicator ell a (T i)) *
      ∑ j ∈ t, d j * indicator ell a (U j)) =
      ∑ i ∈ s, ∑ j ∈ t, (c i * d j) * mean ell q (fun a => indicator ell a (T i ∪ U j)) := by
  have hpoint (a : ∀ l, ZMod (ell l)) :
      (∑ i ∈ s, c i * indicator ell a (T i)) * (∑ j ∈ t, d j * indicator ell a (U j)) =
        ∑ i ∈ s, ∑ j ∈ t, (c i * d j) * indicator ell a (T i ∪ U j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [← indicator_mul]
    ring
  simp_rw [hpoint, mean_sum, mean_const_mul]

variable {k : ℕ}

theorem mean_hitting_product (h : Fin k → ℕ) (p p' Y : ℕ)
    (μ ν : ℕ → ℝ) (q : ℕ) :
    mean ell q (fun a => hittingMass ell h p Y μ q a * hittingMass ell h p' Y ν q a) =
      ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 Y,
        ((if q ∈ tuple h p n then μ n else 0) * (if q ∈ tuple h p' m then ν m else 0)) *
          mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p' m)) :=
  mean_product_expansions ell (Finset.Icc 1 Y) (Finset.Icc 1 Y) q _ _ _ _

theorem mean_mixed_product (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ) :
    mean ell q (fun a => tupleMass ell h p Y μ a * hittingMass ell h p Y μ q a) =
      ∑ m ∈ Finset.Icc 1 Y, (if q ∈ tuple h p m then μ m else 0) *
        ∑ n ∈ Finset.Icc 1 Y, μ n * mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p m)) := by
  rw [show (fun a => tupleMass ell h p Y μ a * hittingMass ell h p Y μ q a) =
      (fun a => (∑ n ∈ Finset.Icc 1 Y, μ n * indicator ell a (tuple h p n)) *
        ∑ m ∈ Finset.Icc 1 Y, (if q ∈ tuple h p m then μ m else 0) *
          indicator ell a (tuple h p m)) from rfl,
    mean_product_expansions, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n _hn => by ring)

theorem off_diagonal_product_le (h : Fin k → ℕ) (p p' Y : ℕ)
    (μ ν : ℕ → ℝ) (q : ℕ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (hν : ∀ m ∈ Finset.Icc 1 Y, 0 ≤ ν m)
    {L : ℝ}
    (hlocal : ∀ n ∈ Finset.Icc 1 Y, ∀ m ∈ Finset.Icc 1 Y,
      q ∈ tuple h p n → q ∈ tuple h p' m →
        mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p' m)) ≤ L) :
    mean ell q (fun a => hittingMass ell h p Y μ q a * hittingMass ell h p' Y ν q a) ≤
      L * hitMass h p Y μ q * hitMass h p' Y ν q := by
  rw [mean_hitting_product]
  have hpoint : ∀ n ∈ Finset.Icc 1 Y, ∀ m ∈ Finset.Icc 1 Y,
      ((if q ∈ tuple h p n then μ n else 0) * (if q ∈ tuple h p' m then ν m else 0)) *
        mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p' m)) ≤
      L * (if q ∈ tuple h p n then μ n else 0) * (if q ∈ tuple h p' m then ν m else 0) := by
    intro n hn m hm
    by_cases hqn : q ∈ tuple h p n <;> by_cases hqm : q ∈ tuple h p' m
    · simp only [if_pos hqn, if_pos hqm]
      exact (mul_le_mul_of_nonneg_left (hlocal n hn m hm hqn hqm)
        (mul_nonneg (hμ n hn) (hν m hm))).trans_eq (by ring)
    all_goals simp [hqn, hqm]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 Y,
        L * (if q ∈ tuple h p n then μ n else 0) * (if q ∈ tuple h p' m then ν m else 0) :=
      Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun m hm => hpoint n hn m hm))
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul, hitMass]

theorem mixed_product_le (h : Fin k → ℕ) (hh : Function.Injective h)
    {p : ℕ} (hp : 0 < p) (Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (hμsum : ∑ n ∈ Finset.Icc 1 Y, μ n = 1)
    {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α)
    (hlocal : ∀ n ∈ Finset.Icc 1 Y, ∀ m ∈ Finset.Icc 1 Y, q ∈ tuple h p m →
      Disjoint (tuple h p n) (tuple h p m) →
        mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p m)) ≤ L) :
    mean ell q (fun a => tupleMass ell h p Y μ a * hittingMass ell h p Y μ q a) ≤
      (L + (k : ℝ) ^ 2 * α) * hitMass h p Y μ q := by
  have hinner : ∀ m ∈ Finset.Icc 1 Y, q ∈ tuple h p m →
      (∑ n ∈ Finset.Icc 1 Y, μ n * mean ell q
        (fun a => indicator ell a (tuple h p n ∪ tuple h p m))) ≤ L + (k : ℝ) ^ 2 * α := by
    intro m hm hqm
    have hpoint : ∀ n ∈ Finset.Icc 1 Y,
        mean ell q (fun a => indicator ell a (tuple h p n ∪ tuple h p m)) ≤
          L + if ¬Disjoint (tuple h p n) (tuple h p m) then 1 else 0 := by
      intro n hn
      by_cases hd : Disjoint (tuple h p n) (tuple h p m)
      · simpa only [not_false_eq_true, not_true_eq_false, hd, if_false, add_zero] using hlocal n hn m hm hqm hd
      · rw [if_pos hd]
        exact (mean_indicator_le_one ell q _).trans (by linarith)
    have hcollision := meeting_mass_le h p Y (tuple h p m) μ hα hμ
    rw [card_tuple h hh hp m] at hcollision
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 Y, μ n * (L + if ¬Disjoint (tuple h p n) (tuple h p m) then 1 else 0) :=
        Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hpoint n hn) (hμ0 n hn))
      _ = L + ∑ n ∈ Finset.Icc 1 Y, if ¬Disjoint (tuple h p n) (tuple h p m) then μ n else 0 := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hμsum, one_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro n _hn
        split_ifs <;> simp
      _ ≤ _ := add_le_add le_rfl (hcollision.trans_eq (by ring))
  rw [mean_mixed_product]
  unfold hitMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  by_cases hqm : q ∈ tuple h p m
  · simp only [if_pos hqm]
    exact (mul_le_mul_of_nonneg_left (hinner m hm hqm) (hμ0 m hm)).trans_eq (by ring)
  · simp [hqm]

end Erdos4.ConditionalProductMoments
