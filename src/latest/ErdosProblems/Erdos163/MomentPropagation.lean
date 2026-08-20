/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Propagation

/-!
# The neutralized defect-moment recurrence

This file lifts the pointwise product estimate through the finite
random-greedy expectation.  It is the formal form of the branching step in
Lee's Lemma 4.5.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace RandomGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β] [DecidableEq ι]

noncomputable def branchCoefficient (C : ℝ) (q : ℕ) : ℝ :=
  ((((q : ℝ) * C ^ q) ^ 2 + 1) / 2)

theorem branchCoefficient_mono {C : ℝ} (hC : 1 ≤ C) {q D : ℕ} (hqD : q ≤ D) :
    branchCoefficient C q ≤ branchCoefficient C D := by
  have hq : (q : ℝ) ≤ D := by exact_mod_cast hqD
  have hpow : C ^ q ≤ C ^ D := pow_le_pow_right₀ hC hqD
  have hmul : (q : ℝ) * C ^ q ≤ (D : ℝ) * C ^ D := by
    exact mul_le_mul hq hpow (pow_nonneg (zero_le_one.trans hC) _) (by positivity)
  unfold branchCoefficient
  gcongr

theorem changeSet_union_forward (I : Finset α)
    (H : SimpleGraph α) [DecidableRel H.Adj] (x : α) :
    changeSet I (I ∪ forwardNeighbors H x) = forwardNeighbors H x \ I := by
  ext y
  simp only [changeSet, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hyI | hyF, hyNotI⟩
    · exact (hyNotI hyI).elim
    · exact ⟨hyF, hyNotI⟩
  · rintro ⟨hyF, hyNotI⟩
    exact ⟨Or.inr hyF, hyNotI⟩

/-- One branching step of the propagated-moment argument. -/
theorem neutralAverage_observed_le_branch
    (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : α → ℕ)
    (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold x)
    (D : ℕ) (hforward : ∀ x, (forwardNeighbors H x).card ≤ D)
    (x : α)
    (hJ : (forwardNeighbors H x \ I).Nonempty) :
    neutralAverage I G H host part threshold (2 * D) default
        (fun final => final.observed x) ≤
      branchCoefficient (2 * γ) (forwardNeighbors H x \ I).card *
          neutralAverage (I ∪ forwardNeighbors H x) G H host part threshold
            (2 * D) default (fun final => (final.observed x) ^ 2) +
        (∑ y ∈ forwardNeighbors H x \ I,
            neutralAverage (I ∪ forwardNeighbors H x) G H host part threshold
              (2 * D) default (fun final => final.observed y)) /
          (2 * ((forwardNeighbors H x \ I).card : ℝ) ^ 2) := by
  let J := forwardNeighbors H x \ I
  let I' := I ∪ forwardNeighbors H x
  let C : ℝ := 2 * γ
  let A : ℝ := branchCoefficient C J.card
  have hII' : I ⊆ I' := by
    intro y hy
    exact Finset.mem_union_left _ hy
  have hchange : changeSet I I' = J := by
    exact changeSet_union_forward I H x
  have hnonnegI :
      neutralAverage I G H host part threshold (2 * D) default
          (fun final => final.observed x) =
        neutralAverage I G H host part threshold (2 * D) default
          (fun final => max 0 (final.observed x)) := by
    apply Process.stateAverage_congr
    intro final hrun
    have hobs := final_observed_nonneg I G H host part threshold (2 * D)
      default hrun x
    exact (max_eq_right hobs).symm
  rw [hnonnegI]
  calc
    neutralAverage I G H host part threshold (2 * D) default
        (fun final => max 0 (final.observed x)) ≤
      neutralAverage I' G H host part threshold (2 * D) default
        (fun final => max 0 (final.observed x) * costProduct J order final) := by
          simpa [hchange] using
            neutralAverage_le_costProduct hII' G H host hhost part threshold
              (2 * D) default (fun final => max 0 (final.observed x))
              (fun final => le_max_left _ _)
    _ ≤ neutralAverage I' G H host part threshold (2 * D) default
        (fun final =>
          A * (final.observed x) ^ 2 +
            (∑ y ∈ J, final.observed y) / (2 * (J.card : ℝ) ^ 2)) := by
      apply Process.stateAverage_mono
      intro final hrun
      have hobs0 := final_observed_nonneg I' G H host part threshold (2 * D)
        default hrun x
      have hcost := costProduct_order_le I' J G H host part threshold (2 * D)
        default hγ hsize hrun
      have hmul :
          max 0 (final.observed x) * costProduct J order final ≤
            C ^ J.card * final.observed x *
              ∏ y ∈ J, max 1 (final.defectSeen y) := by
        rw [max_eq_right hobs0]
        calc
          final.observed x * costProduct J order final ≤
              final.observed x *
                ((2 * γ) ^ J.card *
                  ∏ y ∈ J, max 1 (final.defectSeen y)) :=
            mul_le_mul_of_nonneg_left hcost hobs0
          _ = C ^ J.card * final.observed x *
                ∏ y ∈ J, max 1 (final.defectSeen y) := by
            simp only [C]
            ring
      have hJcard : J.card ≤ D := by
        exact (Finset.card_le_card Finset.sdiff_subset).trans (hforward x)
      have htwoJ : 2 * J.card ≤ 2 * D := Nat.mul_le_mul_left 2 hJcard
      have hJpos : 0 < 2 * J.card := Nat.mul_pos (by norm_num) hJ.card_pos
      have hroot := root_mul_product_le_root_sq_add_children hJ
        (fun y => final.defectSeen y) (fun y => final.observed y) C
        (final.observed x)
        (final_observed_zero_or_one_le I' G H host part threshold (2 * D)
          default hrun x)
        (fun y hy => final_observed_nonneg I' G H host part threshold (2 * D)
          default hrun y)
        (fun y hy => final_defect_pow_le_observed I' G H host part threshold
          (2 * D) default hrun hJpos htwoJ y)
      exact hmul.trans (by simpa [A, C, branchCoefficient] using hroot)
    _ = A * neutralAverage I' G H host part threshold (2 * D) default
          (fun final => (final.observed x) ^ 2) +
        (∑ y ∈ J,
            neutralAverage I' G H host part threshold (2 * D) default
              (fun final => final.observed y)) /
          (2 * (J.card : ℝ) ^ 2) := by
      unfold neutralAverage
      rw [Process.stateAverage_add]
      rw [Process.stateAverage_const_mul]
      rw [Process.stateAverage_div]
      rw [Process.stateAverage_sum]
    _ = branchCoefficient (2 * γ) (forwardNeighbors H x \ I).card *
          neutralAverage (I ∪ forwardNeighbors H x) G H host part threshold
            (2 * D) default (fun final => (final.observed x) ^ 2) +
        (∑ y ∈ forwardNeighbors H x \ I,
            neutralAverage (I ∪ forwardNeighbors H x) G H host part threshold
              (2 * D) default (fun final => final.observed y)) /
          (2 * ((forwardNeighbors H x \ I).card : ℝ) ^ 2) := by
      rfl

/-! ## Finite propagation on the forward-neighbor DAG -/

def higherCount (x : α) : ℕ :=
  (Finset.univ.filter fun y => x < y).card

theorem higherCount_lt_of_lt {x y : α} (hxy : x < y) :
    higherCount y < higherCount x := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    simp only [higherCount, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hxy.trans hz
  · intro heq
    have hyx : y ∈ (Finset.univ.filter fun z => x < z) := by
      simp [hxy]
    have hyy : y ∉ (Finset.univ.filter fun z => y < z) := by simp
    exact hyy (heq ▸ hyx)

/-- Lee's propagated-moment bound from a terminal square-moment estimate.
The hypotheses on `A` isolate the harmless numerical maximization of the
branch coefficients from the finite probabilistic argument. -/
theorem neutralAverage_observed_le_of_terminal
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : α → ℕ)
    (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold x)
    (D : ℕ) (hforward : ∀ x, (forwardNeighbors H x).card ≤ D)
    (μ A : ℝ) (hμ : 0 ≤ μ) (hA : 1 / 2 ≤ A)
    (hcoefficient : ∀ q : ℕ, q ≤ D → branchCoefficient (2 * γ) q ≤ A)
    (hterminal : ∀ (I : Finset α) (x : α), forwardNeighbors H x ⊆ I →
      neutralAverage I G H host part threshold (2 * D) default
        (fun final => (final.observed x) ^ 2) ≤ μ) :
    ∀ (I : Finset α) (x : α),
      neutralAverage I G H host part threshold (2 * D) default
        (fun final => final.observed x) ≤ 2 * A * μ := by
  let B : ℝ := 2 * A * μ
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  let P : ℕ → Prop := fun k =>
    ∀ x : α, higherCount x = k → ∀ I : Finset α,
      neutralAverage I G H host part threshold (2 * D) default
        (fun final => final.observed x) ≤ B
  have hP : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hxrank I
      let J := forwardNeighbors H x \ I
      by_cases hJ : J.Nonempty
      · let I' := I ∪ forwardNeighbors H x
        have hstep := neutralAverage_observed_le_branch I G H host hhost part
          threshold default hγ hsize D hforward x hJ
        have hroot :
            neutralAverage I' G H host part threshold (2 * D) default
              (fun final => (final.observed x) ^ 2) ≤ μ := by
          apply hterminal
          exact Finset.subset_union_right
        have hroot0 : 0 ≤
            neutralAverage I' G H host part threshold (2 * D) default
              (fun final => (final.observed x) ^ 2) := by
          apply Process.stateAverage_nonneg
          intro final hrun
          exact sq_nonneg _
        have hJcard : J.card ≤ D := by
          exact (Finset.card_le_card Finset.sdiff_subset).trans (hforward x)
        have hcoeff := hcoefficient J.card hJcard
        have hcoeff0 : 0 ≤ branchCoefficient (2 * γ) J.card := by
          unfold branchCoefficient
          positivity
        have hrootTerm :
            branchCoefficient (2 * γ) J.card *
                neutralAverage I' G H host part threshold (2 * D) default
                  (fun final => (final.observed x) ^ 2) ≤ A * μ := by
          exact mul_le_mul hcoeff hroot hroot0 hA0
        have hchildren :
            ∑ y ∈ J,
                neutralAverage I' G H host part threshold (2 * D) default
                  (fun final => final.observed y) ≤ (J.card : ℝ) * B := by
          calc
            _ ≤ ∑ _y ∈ J, B := by
              apply Finset.sum_le_sum
              intro y hy
              have hyForward : y ∈ forwardNeighbors H x := (Finset.mem_sdiff.mp hy).1
              have hxy : x < y := by
                exact (Finset.mem_filter.mp hyForward).2.2
              have hyrank : higherCount y < k := by
                rw [← hxrank]
                exact higherCount_lt_of_lt hxy
              exact ih (higherCount y) hyrank y rfl I'
            _ = (J.card : ℝ) * B := by simp
        have hdenom : 0 < (2 * (J.card : ℝ) ^ 2) := by
          have : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
          positivity
        have hquotient :
            (∑ y ∈ J,
                neutralAverage I' G H host part threshold (2 * D) default
                  (fun final => final.observed y)) /
                  (2 * (J.card : ℝ) ^ 2) ≤ B / 2 := by
          calc
            _ ≤ ((J.card : ℝ) * B) / (2 * (J.card : ℝ) ^ 2) :=
              div_le_div_of_nonneg_right hchildren hdenom.le
            _ = B / (2 * (J.card : ℝ)) := by
              have hcardne : (J.card : ℝ) ≠ 0 := by
                exact_mod_cast hJ.card_ne_zero
              field_simp
            _ ≤ B / 2 := by
              apply div_le_div_of_nonneg_left hB0 (by norm_num)
              have hqone : (1 : ℝ) ≤ J.card := by exact_mod_cast hJ.card_pos
              nlinarith
        calc
          neutralAverage I G H host part threshold (2 * D) default
              (fun final => final.observed x) ≤
              branchCoefficient (2 * γ) J.card *
                  neutralAverage I' G H host part threshold (2 * D) default
                    (fun final => (final.observed x) ^ 2) +
                (∑ y ∈ J,
                    neutralAverage I' G H host part threshold (2 * D) default
                      (fun final => final.observed y)) /
                    (2 * (J.card : ℝ) ^ 2) := by
                simpa [J, I'] using hstep
          _ ≤ A * μ + B / 2 := add_le_add hrootTerm hquotient
          _ = B := by simp [B]; ring
      · have hsubset : forwardNeighbors H x ⊆ I := by
          exact Finset.sdiff_eq_empty_iff_subset.mp
            (Finset.not_nonempty_iff_eq_empty.mp hJ)
        have hlinear :
            neutralAverage I G H host part threshold (2 * D) default
                (fun final => final.observed x) ≤
              neutralAverage I G H host part threshold (2 * D) default
                (fun final => (final.observed x) ^ 2) := by
          apply Process.stateAverage_mono
          intro final hrun
          rcases final_observed_zero_or_one_le I G H host part threshold (2 * D)
            default hrun x with hzero | hone
          · simp [hzero]
          · nlinarith [sq_nonneg (final.observed x)]
        calc
          neutralAverage I G H host part threshold (2 * D) default
              (fun final => final.observed x) ≤
              neutralAverage I G H host part threshold (2 * D) default
                (fun final => (final.observed x) ^ 2) := hlinear
          _ ≤ μ := hterminal I x hsubset
          _ ≤ B := by
            dsimp [B]
            nlinarith
  intro I x
  exact hP (higherCount x) x rfl I

theorem average_observed_le_of_terminal
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : α → ℕ)
    (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold x)
    (D : ℕ) (hforward : ∀ x, (forwardNeighbors H x).card ≤ D)
    (μ A : ℝ) (hμ : 0 ≤ μ) (hA : 1 / 2 ≤ A)
    (hcoefficient : ∀ q : ℕ, q ≤ D → branchCoefficient (2 * γ) q ≤ A)
    (hterminal : ∀ (I : Finset α) (x : α), forwardNeighbors H x ⊆ I →
      neutralAverage I G H host part threshold (2 * D) default
        (fun final => (final.observed x) ^ 2) ≤ μ) (x : α) :
    average G H host part threshold (2 * D) default
        (fun final => final.observed x) ≤ 2 * A * μ := by
  have h := neutralAverage_observed_le_of_terminal G H host hhost part threshold
    default hγ hsize D hforward μ A hμ hA hcoefficient hterminal
      (∅ : Finset α) x
  have hempty : maskedChoices (∅ : Finset α) G H host part default =
      fun x state => choices G H host part default state x := by
    funext x state
    simp [maskedChoices]
  unfold neutralAverage at h
  unfold average
  rw [hempty] at h
  exact h

/-- Complete random-greedy embedding theorem with the terminal moments left
as the host-side input. -/
theorem hasCopy_of_terminal_moments
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (default : β)
    (hhostNonempty : ∀ i, (host i).Nonempty)
    (hhostDisjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (hthreshold : ∀ x, 0 < threshold x)
    (hpartSize : ∀ x, 2 * (partVertices part x).card ≤ threshold x)
    {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold x)
    (D : ℕ) (hforward : ∀ x, (forwardNeighbors H x).card ≤ D)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hterminal : ∀ (I : Finset α) (x : α), forwardNeighbors H x ⊆ I →
      neutralAverage I G H host part threshold (2 * D) default
        (fun final => (final.observed x) ^ 2) ≤ μ)
    (htotal : (Fintype.card α : ℝ) *
      (2 * branchCoefficient (2 * γ) D * μ) < 1) :
    HasCopy H G := by
  let A := branchCoefficient (2 * γ) D
  have hC : (1 : ℝ) ≤ 2 * γ := by linarith
  have hA : (1 / 2 : ℝ) ≤ A := by
    dsimp [A, branchCoefficient]
    nlinarith [sq_nonneg ((D : ℝ) * (2 * γ) ^ D)]
  have hcoeff : ∀ q : ℕ, q ≤ D → branchCoefficient (2 * γ) q ≤ A := by
    intro q hq
    exact branchCoefficient_mono hC hq
  apply hasCopy_of_observed_bounds G H host part threshold (2 * D) default
    hhostNonempty hhostDisjoint hpart hthreshold hpartSize
    (B := 2 * A * μ)
  · intro x
    exact average_observed_le_of_terminal G H host hhostNonempty part threshold
      default hγ hsize D hforward μ A hμ hA hcoeff hterminal x
  · simpa [A] using htotal

end RandomGreedy
end Erdos163
