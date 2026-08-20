/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.HostPartition
import ErdosProblems.Erdos163.AdaptiveTerminal

/-!
# From an all-direction host to a target copy

This module combines the target-dependent random partition with the checked
adaptive random-greedy theorem.  All analytic/numerical requirements remain
explicit parameters, so the final file only has to instantiate inequalities.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace HostEmbedding

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {X : Type u} {P : Type v}
  [Fintype X] [DecidableEq X] [LinearOrder X]
  [Fintype P] [DecidableEq P] [LinearOrder P]

theorem unionExcept_nonempty_of_cards
    {N r τ : ℕ} (hr : 2 ≤ r) (hτ : 0 < τ)
    (A : Fin r → Finset (Fin N)) (hA : ∀ j, τ ≤ (A j).card)
    (j : Fin r) : (HostDirections.unionExcept A j).Nonempty := by
  classical
  by_cases hj0 : j.1 = 0
  · let k : Fin r := ⟨1, hr⟩
    have hkj : k ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp [k, hj0] at hv
    have hk : (A k).Nonempty :=
      Finset.card_pos.mp (hτ.trans_le (hA k))
    exact hk.mono (HostDirections.subset_unionExcept A hkj)
  · let k : Fin r := ⟨0, by omega⟩
    have hkj : k ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp [k] at hv
      exact hj0 hv.symm
    have hk : (A k).Nonempty :=
      Finset.card_pos.mp (hτ.trans_le (hA k))
    exact hk.mono (HostDirections.subset_unionExcept A hkj)

/-- The complete target-dependent host reduction.  The base host family has
one all-direction moment estimate per target colour; after random labelling,
the resulting disjoint buckets satisfy the literal family moments required
by `AdaptiveGreedy.hasCopy_of_family_moments`. -/
theorem hasCopy_of_all_direction_parameters
    {N r τ D Ksel Kbase : ℕ} {ε γ μ : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (part : X → P) (color : P → Fin r) (threshold : P → ℕ)
    (A : Fin r → Finset (Fin N)) (q : P → ℝ)
    (defaultTarget : X) (defaultHost : Fin N)
    (hr : 2 ≤ r) (hτ : 0 < τ) (hD : 0 < D)
    (hAcard : ∀ j, τ ≤ (A j).card)
    (hAmoment : ∀ j,
      FiniteDefect.moment G τ (4 * D)
        (fun _ : Fin D => HostDirections.unionExcept A j) (A j) ≤ ε)
    (hcommonPos : ∀ x (g : RandomGreedy.forwardNeighbors H x → Fin N),
      g ∈ FiniteDefect.familyTuples
          (fun y : RandomGreedy.forwardNeighbors H x => A (color (part y))) →
        0 < (FiniteDefect.commonNeighbors G g (A (color (part x)))).card)
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (hcolor : ∀ ⦃a b⦄, H.Adj a b → color (part a) ≠ color (part b))
    (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (hthreshold : ∀ p, 0 < threshold p)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    (hqpos : ∀ p, 0 < q p) (hqsum : ∑ p, q p ≤ 1)
    (hthresholdSample : ∀ p,
      (threshold p : ℝ) ≤ q p * τ / 2)
    (hKsel : ∀ p, (2 : ℝ) ≤ Ksel * q p)
    (hKbase : N ≤ Kbase * τ)
    (hγ : 1 ≤ γ)
    (hsize : ∀ p, (N : ℝ) ≤ γ * threshold p)
    (hmomentNumeric : ∀ x,
      (Ksel : ℝ) ^ Fintype.card (RandomGreedy.forwardNeighbors H x) *
        ((Kbase : ℝ) ^ Fintype.card (RandomGreedy.forwardNeighbors H x) * ε)
        ≤ μ)
    (hμ : 0 ≤ μ)
    (htotal :
      ∑ x : X, (2 / (threshold (part x) : ℝ)) *
        (2 * RandomGreedy.branchCoefficient (2 * γ) D * μ) < 1)
    (hfail :
      let coord : X → Type u := fun x : X =>
        ↑(RandomGreedy.forwardNeighbors H x)
      let base := fun x : X =>
        fun y : RandomGreedy.forwardNeighbors H x => A (color (part y))
      let active : HostPartition.SamplingTest (P := P) X coord base →
          Fin N → Prop
        | Sum.inl p => fun v => v ∈ A (color p)
        | Sum.inr z => fun v => v ∈
            FiniteDefect.commonNeighbors G z.2.1 (A (color (part z.1)))
      let which : HostPartition.SamplingTest (P := P) X coord base → P
        | Sum.inl p => p
        | Sum.inr z => part z.1
      ∑ k, Real.exp
        (-2 * (q (which k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ)) < 1) :
    HasCopy H G := by
  let base := fun x : X =>
    fun y : RandomGreedy.forwardNeighbors H x => A (color (part y))
  obtain ⟨label, hlower, hcommon⟩ :=
    HostPartition.exists_labeling_good
      (P := P) (X := X) (fun x : X => ↑(RandomGreedy.forwardNeighbors H x))
      G A color part base q (fun p => (hqpos p).le) hqsum
      (by simpa [base] using hfail)
  let host : P → Finset (Fin N) := HostPartition.bucket A color label
  have hhostSubset : ∀ p, host p ⊆ A (color p) := by
    intro p
    exact HostPartition.bucket_subset A color label p
  have hhostNonempty : ∀ p, (host p).Nonempty := by
    intro p
    have hApos : (0 : ℝ) < (A (color p)).card := by
      exact_mod_cast hτ.trans_le (hAcard (color p))
    have hlhs : 0 < q p * ((A (color p)).card : ℝ) / 2 := by positivity
    have hcardR : (0 : ℝ) < (host p).card := hlhs.trans (hlower p)
    exact Finset.card_pos.mp (by exact_mod_cast hcardR)
  have hhostDisjoint : ∀ ⦃p p'⦄, p ≠ p' → Disjoint (host p) (host p') := by
    intro p p' hpp'
    exact HostPartition.bucket_disjoint A color label hpp'
  have hselectedCard : ∀ p, (A (color p)).card ≤ Ksel * (host p).card := by
    intro p
    have hl := hlower p
    have hA0 : (0 : ℝ) ≤ (A (color p)).card := by positivity
    have hK0 : (0 : ℝ) ≤ Ksel := by positivity
    have hreal : ((A (color p)).card : ℝ) ≤
        Ksel * ((host p).card : ℝ) := by
      have hfac := hKsel p
      nlinarith
    exact_mod_cast hreal
  have hhostSize : ∀ x, ((host (part x)).card : ℝ) ≤
      γ * threshold (part x) := by
    intro x
    calc
      ((host (part x)).card : ℝ) ≤ N := by
        exact_mod_cast Finset.card_le_univ (host (part x))
      _ ≤ γ * threshold (part x) := hsize (part x)
  have hmoment : ∀ x,
      FiniteDefect.familyMoment G (threshold (part x)) s
        (fun y : RandomGreedy.forwardNeighbors H x => host (part y))
        (host (part x)) ≤ μ := by
    intro x
    let I := RandomGreedy.forwardNeighbors H x
    have hbaseNonempty : ∀ y : I, (base x y).Nonempty := by
      intro y
      exact Finset.card_pos.mp (hτ.trans_le (hAcard (color (part y))))
    have hselectedNonempty : ∀ y : I, (host (part y)).Nonempty :=
      fun y => hhostNonempty (part y)
    have hselectedSubset : ∀ y : I, host (part y) ⊆ base x y := by
      intro y
      exact hhostSubset (part y)
    have hselectedRatio : ∀ y : I,
        (base x y).card ≤ Ksel * (host (part y)).card := by
      intro y
      exact hselectedCard (part y)
    have hretain : ∀ g ∈ FiniteDefect.familyTuples
        (fun y : I => host (part y)),
        q (part x) *
            ((FiniteDefect.commonNeighbors G g (A (color (part x)))).card : ℝ) / 2 <
          ((FiniteDefect.commonNeighbors G g (host (part x))).card : ℝ) := by
      intro g hg
      have hgbase : g ∈ FiniteDefect.familyTuples (base x) := by
        rw [FiniteDefect.mem_familyTuples] at hg ⊢
        intro y
        exact hselectedSubset y (hg y)
      exact hcommon x g hgbase
    have holdPositive : ∀ g ∈ FiniteDefect.familyTuples
        (fun y : I => host (part y)),
        0 < (FiniteDefect.commonNeighbors G g (A (color (part x)))).card := by
      intro g hg
      apply hcommonPos x g
      rw [FiniteDefect.mem_familyTuples] at hg ⊢
      intro y
      exact hselectedSubset y (hg y)
    have hrestrict := HostPartition.familyMoment_restrict_proportional_le
      (s := 4 * D) G
      hselectedNonempty hselectedSubset hselectedRatio
      (A (color (part x))) (host (part x)) (q (part x)) (hqpos (part x))
      (hthresholdSample (part x)) holdPositive hretain
    have hbaseSubset : ∀ y : I,
        base x y ⊆ HostDirections.unionExcept A (color (part x)) := by
      intro y
      have hy := (Finset.mem_filter.mp y.property).2.1
      exact HostDirections.subset_unionExcept A (hcolor hy).symm
    have hbaseRatio : ∀ y : I,
        (HostDirections.unionExcept A (color (part x))).card ≤
          Kbase * (base x y).card := by
      intro y
      calc
        (HostDirections.unionExcept A (color (part x))).card ≤ N :=
          HostDirections.card_unionExcept_le A _
        _ ≤ Kbase * τ := hKbase
        _ ≤ Kbase * (base x y).card :=
          Nat.mul_le_mul_left Kbase (hAcard (color (part y)))
    have hcoord := HostTools.familyMoment_le_pow_mul_of_subset G τ (4 * D) Kbase
      hbaseNonempty hbaseSubset hbaseRatio (A (color (part x)))
    have hunionNonempty := unionExcept_nonempty_of_cards hr hτ A hAcard
      (color (part x))
    have hdim : Fintype.card I ≤ D := by
      simpa [I] using hforward x
    have hconst : FiniteDefect.familyMoment G τ (4 * D)
        (fun _ : I => HostDirections.unionExcept A (color (part x)))
        (A (color (part x))) =
      FiniteDefect.moment G τ (4 * D)
        (fun _ : Fin (Fintype.card I) =>
          HostDirections.unionExcept A (color (part x)))
        (A (color (part x))) :=
      HostPartition.familyMoment_const_eq_moment_card G _ _
    have hdimMoment := HostTools.moment_mono_dimension G hunionNonempty
      (A (color (part x))) τ (4 * D) hdim
    have hold : FiniteDefect.familyMoment G τ (4 * D) (base x)
        (A (color (part x))) ≤
      (Kbase : ℝ) ^ Fintype.card I * ε := by
      calc
        FiniteDefect.familyMoment G τ s (base x) (A (color (part x))) ≤
            (Kbase : ℝ) ^ Fintype.card I *
              FiniteDefect.familyMoment G τ (4 * D)
                (fun _ : I => HostDirections.unionExcept A (color (part x)))
                (A (color (part x))) := hcoord
        _ = (Kbase : ℝ) ^ Fintype.card I *
              FiniteDefect.moment G τ (4 * D)
                (fun _ : Fin (Fintype.card I) =>
                  HostDirections.unionExcept A (color (part x)))
                (A (color (part x))) := by rw [hconst]
        _ ≤ (Kbase : ℝ) ^ Fintype.card I *
              FiniteDefect.moment G τ (4 * D)
                (fun _ : Fin D => HostDirections.unionExcept A (color (part x)))
                (A (color (part x))) :=
          mul_le_mul_of_nonneg_left hdimMoment (by positivity)
        _ ≤ (Kbase : ℝ) ^ Fintype.card I * ε :=
          mul_le_mul_of_nonneg_left (hAmoment (color (part x))) (by positivity)
    exact hrestrict.trans <| (mul_le_mul_of_nonneg_left hold (by positivity)).trans
      (hmomentNumeric x)
  apply AdaptiveGreedy.hasCopy_of_family_moments G H host part threshold
    defaultTarget defaultHost hhostNonempty hhostDisjoint hpart horder hthreshold
    hpartSize hγ hhostSize D hD hforward μ hμ hmoment htotal

end
end HostEmbedding
end Erdos163
