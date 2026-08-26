/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Basic

namespace Erdos254

open Filter Set
open scoped Topology

/-- An unbounded sequence of naturals is unbounded on every tail. -/
lemma unbounded_tail {a : ℕ → ℕ} (ha : ∀ M, ∃ n, M < a n) (N M : ℕ) :
    ∃ n, N ≤ n ∧ M < a n := by
  obtain ⟨n, hn⟩ := ha (max M ((Finset.range N).sup a))
  refine ⟨n, ?_, (le_max_left _ _).trans_lt hn⟩
  by_contra h
  have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have := (Finset.le_sup (f := a) hmem).trans (le_max_right M _)
  omega

private lemma phase_sub_le (u v : ℝ) :
    distToNearestInt (u - v) ≤ distToNearestInt u + distToNearestInt v := by
  simpa only [distToNearestInt, AddCircle.coe_sub] using
    norm_sub_le (u : UnitAddCircle) (v : UnitAddCircle)

/-- On a small-phase tail, one nearest integer determines the real phase.
This is the separation argument in Fan's Lemma 3.1, using rounding instead
of a packing bound on the circle. -/
lemma small_phase_tail_inj {a : ℕ → ℕ} {L ε : ℝ}
    (ha : ∀ M, ∃ n, M < a n) (hL : 1 < L)
    (hratio : ∀ n, (a (n + 1) : ℝ) ≤ L * a n)
    (hsmall : 4 * L * ε < 1) (N : ℕ) :
    Set.InjOn (fun θ : ℝ ↦ round ((a N : ℝ) * θ))
      {θ : ℝ | ∀ n, N ≤ n → distToNearestInt ((a n : ℝ) * θ) ≤ ε} := by
  intro x hx y hy hxy
  dsimp only at hxy
  have hLpos : 0 < L := by linarith
  have hbound : ∀ n, N ≤ n → (a n : ℝ) * |x - y| ≤ 2 * ε := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have htriangle := abs_sub_le ((a N : ℝ) * x)
          (round ((a N : ℝ) * x)) ((a N : ℝ) * y)
        rw [abs_sub_comm (round ((a N : ℝ) * x) : ℝ) ((a N : ℝ) * y)] at htriangle
        have hxN := hx N le_rfl
        have hyN := hy N le_rfl
        rw [distToNearestInt_eq] at hxN hyN
        rw [← hxy] at hyN
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at htriangle
        linarith
    | succ n hn ih =>
        have hmul : (a (n + 1) : ℝ) * |x - y| ≤ 2 * L * ε := by
          calc
            (a (n + 1) : ℝ) * |x - y| ≤ (L * a n) * |x - y| :=
              mul_le_mul_of_nonneg_right (hratio n) (abs_nonneg _)
            _ = L * ((a n : ℝ) * |x - y|) := by ring
            _ ≤ L * (2 * ε) := mul_le_mul_of_nonneg_left ih hLpos.le
            _ = 2 * L * ε := by ring
        have habs : |(a (n + 1) : ℝ) * (x - y)| ≤ |(1 : ℝ)| / 2 := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_one]
          nlinarith
        have heq : distToNearestInt ((a (n + 1) : ℝ) * (x - y)) =
            (a (n + 1) : ℝ) * |x - y| := by
          rw [distToNearestInt, (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr habs,
            abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        have ht := phase_sub_le ((a (n + 1) : ℝ) * x) ((a (n + 1) : ℝ) * y)
        rw [← mul_sub, heq] at ht
        have hx' := hx (n + 1) (by omega)
        have hy' := hy (n + 1) (by omega)
        linarith
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * ε / |x - y|)
  obtain ⟨n, hn, hMn⟩ := unbounded_tail ha N M
  have hreal : (M : ℝ) < a n := by exact_mod_cast hMn
  have := (div_lt_iff₀ hpos).mp (hM.trans hreal)
  linarith [hbound n hn]

/-- Fan, Lemma 3.1: bounded ratios imply countably many vanishing phases.
We state the result on `ℝ`; passing to the circle only removes integer translates. -/
theorem countable_vanishing_phases {a : ℕ → ℕ} {L : ℝ}
    (ha : ∀ M, ∃ n, M < a n) (hL : 1 < L)
    (hratio : ∀ n, (a (n + 1) : ℝ) ≤ L * a n) :
    {θ : ℝ | Tendsto (fun n ↦ distToNearestInt ((a n : ℝ) * θ)) atTop (𝓝 0)}.Countable := by
  let ε : ℝ := 1 / (8 * L)
  have hLpos : 0 < L := by linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : 4 * L * ε < 1 := by
    dsimp [ε]
    field_simp
    nlinarith
  let E : ℕ → Set ℝ := fun N ↦
    {θ | ∀ n, N ≤ n → distToNearestInt ((a n : ℝ) * θ) ≤ ε}
  have hcount : ∀ N, (E N).Countable := by
    intro N
    exact countable_of_injective_of_countable_image
      (small_phase_tail_inj ha hL hratio hsmall N) (to_countable _)
  apply (countable_iUnion hcount).mono
  intro θ hθ
  have hevent : ∀ᶠ n in atTop, distToNearestInt ((a n : ℝ) * θ) < ε :=
    hθ.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact mem_iUnion.mpr ⟨N, fun n hn ↦ (hN n hn).le⟩

/-- The exceptional summability phases form a countable set. -/
theorem countable_summable_phases {a : ℕ → ℕ} {L : ℝ}
    (ha : ∀ M, ∃ n, M < a n) (hL : 1 < L)
    (hratio : ∀ n, (a (n + 1) : ℝ) ≤ L * a n) :
    {θ : ℝ | Summable (fun n ↦ distToNearestInt ((a n : ℝ) * θ))}.Countable := by
  exact (countable_vanishing_phases ha hL hratio).mono
    (fun _ hθ ↦ hθ.tendsto_atTop_zero)

/-- The circle-valued form used for the partition in Fan's Theorem 4.1. -/
theorem countable_summable_circle_phases {a : ℕ → ℕ} {L : ℝ}
    (ha : ∀ M, ∃ n, M < a n) (hL : 1 < L)
    (hratio : ∀ n, (a (n + 1) : ℝ) ≤ L * a n) :
    {θ : UnitAddCircle | Summable (fun n ↦ ‖a n • θ‖)}.Countable := by
  apply ((countable_summable_phases ha hL hratio).image
    (fun θ : ℝ ↦ (θ : UnitAddCircle))).mono
  intro θ hθ
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
  refine ⟨x, ?_, rfl⟩
  simpa only [Set.mem_ofPred_eq, distToNearestInt, ← AddCircle.coe_nsmul,
    nsmul_eq_mul] using hθ

end Erdos254
