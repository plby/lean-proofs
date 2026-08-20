/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.PartitionConcentration
import ErdosProblems.Erdos163.AdaptiveTerminal

/-!
# Target embedding from concentrated raw defect sums

This is the P1/P2 host-partition reduction in Lee's proof.  P1 retains
bucket sizes and common neighbourhoods.  P2 bounds the unnormalised defect
sum, so the product of label probabilities cancels against the product of
the selected bucket sizes.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace ConcentratedEmbedding

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {X : Type u} {P : Type v}
  [Fintype X] [DecidableEq X] [LinearOrder X]
  [Fintype P] [DecidableEq P] [LinearOrder P]

theorem hasCopy_of_concentrated_parameters
    {N r τ D : ℕ} {γ μ : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (part : X → P) (color : P → Fin r) (threshold : P → ℕ)
    (A : Fin r → Finset (Fin N)) (q : P → ℝ)
    (bound : X → Fin N → ℝ) (tail meanBound : X → ℝ)
    (sizeTail : P → ℝ)
    (defaultTarget : X) (defaultHost : Fin N)
    (hD : 0 < D) (hτ : 0 < τ)
    (hAcard : ∀ j, τ ≤ (A j).card)
    (hcommonPos : ∀ x (g : RandomGreedy.forwardNeighbors H x → Fin N),
      g ∈ FiniteDefect.familyTuples
          (fun y : RandomGreedy.forwardNeighbors H x => A (color (part y))) →
        0 < (FiniteDefect.commonNeighbors G g (A (color (part x)))).card)
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (hthreshold : ∀ p, 0 < threshold p)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (hqpos : ∀ p, 0 < q p) (hqsum : ∑ p, q p ≤ 1)
    (hthresholdSample : ∀ p,
      (threshold p : ℝ) ≤ q p * τ / 2)
    (hbound : ∀ x i, 0 ≤ bound x i)
    (hincident : ∀ x i,
      PartitionConcentration.incident
        (FiniteDefect.familyTuples
          (fun y : RandomGreedy.forwardNeighbors H x => A (color (part y))))
        (fun g => FiniteDefect.defectPower G τ g (A (color (part x))) (4 * D)) i ≤
      bound x i)
    (htail : ∀ x, 0 ≤ tail x)
    (hmean : ∀ x,
      Erdos136.McDiarmid.weightedMean
        (fun _ : Fin N => HostPartition.labelWeight q)
        (PartitionConcentration.rawStatistic
          (FiniteDefect.familyTuples
            (fun y : RandomGreedy.forwardNeighbors H x => A (color (part y))))
          (fun y => part y)
          (fun g => FiniteDefect.defectPower G τ g
            (A (color (part x))) (4 * D))) ≤ meanBound x)
    (hμ : 0 ≤ μ)
    (hnormalized : ∀ x,
      meanBound x + tail x ≤ μ *
        ∏ y : RandomGreedy.forwardNeighbors H x,
          (q (part y) * ((A (color (part y))).card : ℝ) / 2))
    (hγ : 1 ≤ γ)
    (hsizeTail : ∀ p, 0 ≤ sizeTail p)
    (hsize : ∀ p,
      q p * ((A (color p)).card : ℝ) + sizeTail p ≤
        γ * threshold p)
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
      (∑ k, Real.exp
        (-2 * (q (which k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ))) +
      (∑ p : P, Real.exp
        (-2 * (sizeTail p) ^ 2 / (N : ℝ))) +
      ∑ x : X, Real.exp
        (-2 * (tail x) ^ 2 / ∑ i : Fin N, (bound x i) ^ 2) < 1) :
    HasCopy H G := by
  let coord : X → Type u := fun x : X =>
    ↑(RandomGreedy.forwardNeighbors H x)
  let base := fun x : X =>
    fun y : RandomGreedy.forwardNeighbors H x => A (color (part y))
  let oldWeight : ∀ x, (coord x → Fin N) → ℝ := fun x g =>
    FiniteDefect.defectPower G τ g (A (color (part x))) (4 * D)
  obtain ⟨label, hlower, hcommon, hsizeUpper, hrawUpper⟩ :=
    PartitionConcentration.exists_labeling_good_with_raw_and_size
      (P := P) coord G A color part (fun x y => part y) base oldWeight
      q bound tail sizeTail (fun p => (hqpos p).le) hqsum
      (fun x g hg => FiniteDefect.defectPower_nonneg G τ g
        (A (color (part x))) (4 * D))
      hbound (by simpa [coord, base, oldWeight] using hincident) htail
      hsizeTail
      (by simpa [coord, base] using hfail)
  let host : P → Finset (Fin N) := HostPartition.bucket A color label
  have hhostNonempty : ∀ p, (host p).Nonempty := by
    intro p
    have hApos : (0 : ℝ) < (A (color p)).card := by
      exact_mod_cast hτ.trans_le (hAcard (color p))
    have hlhs : 0 < q p * ((A (color p)).card : ℝ) / 2 :=
      div_pos (mul_pos (hqpos p) hApos) (by norm_num)
    have hcardR : (0 : ℝ) < (host p).card := hlhs.trans (hlower p)
    exact Finset.card_pos.mp (by exact_mod_cast hcardR)
  have hhostDisjoint : ∀ ⦃p p'⦄, p ≠ p' → Disjoint (host p) (host p') := by
    intro p p' hpp'
    exact HostPartition.bucket_disjoint A color label hpp'
  have hhostSize : ∀ x, ((host (part x)).card : ℝ) ≤
      γ * threshold (part x) := by
    intro x
    exact (hsizeUpper (part x)).le.trans (hsize (part x))
  have hmoment : ∀ x,
      FiniteDefect.familyMoment G (threshold (part x)) (4 * D)
        (fun y : RandomGreedy.forwardNeighbors H x => host (part y))
        (host (part x)) ≤ μ := by
    intro x
    let I := RandomGreedy.forwardNeighbors H x
    let selected : I → Finset (Fin N) := fun y => host (part y)
    let S := FiniteDefect.familyTuples (base x)
    have hselected_eq : selected =
        PartitionConcentration.selectedCoordinates (base x)
          (fun y : I => part y) label := by
      funext y
      rfl
    have hnewOld : ∀ g ∈ FiniteDefect.familyTuples selected,
        FiniteDefect.defectPower G (threshold (part x)) g
            (host (part x)) (4 * D) ≤ oldWeight x g := by
      intro g hg
      have hgbase : g ∈ FiniteDefect.familyTuples (base x) := by
        rw [FiniteDefect.mem_familyTuples] at hg ⊢
        intro y
        exact HostPartition.bucket_subset A color label (part y) (hg y)
      exact HostPartition.defectPower_restrict_le_of_proportional G g
        (A (color (part x))) (host (part x)) (q (part x))
        (hqpos (part x)) (hcommonPos x g hgbase)
        (hthresholdSample (part x)) (hcommon x g hgbase)
    have hrawSelected : HostTools.rawFamilyMoment G (threshold (part x)) (4 * D)
          selected (host (part x)) ≤
        PartitionConcentration.rawStatistic S (fun y : I => part y)
          (oldWeight x) label := by
      unfold HostTools.rawFamilyMoment PartitionConcentration.rawStatistic
      have hsub : FiniteDefect.familyTuples selected ⊆ S := by
        intro g hg
        rw [FiniteDefect.mem_familyTuples] at hg ⊢
        intro y
        exact HostPartition.bucket_subset A color label (part y) (hg y)
      calc
        (∑ g ∈ FiniteDefect.familyTuples selected,
            FiniteDefect.defectPower G (threshold (part x)) g
              (host (part x)) (4 * D)) ≤
          ∑ g ∈ FiniteDefect.familyTuples selected, oldWeight x g := by
            exact Finset.sum_le_sum fun g hg => hnewOld g hg
        _ = ∑ g ∈ FiniteDefect.familyTuples selected,
            (if HostPartition.cylinder g (fun y : I => part y) label then
              oldWeight x g else 0) := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [if_pos]
          intro y
          rw [FiniteDefect.mem_familyTuples] at hg
          have hy := hg y
          exact (Finset.mem_filter.mp hy).2
        _ ≤ ∑ g ∈ S,
            (if HostPartition.cylinder g (fun y : I => part y) label then
              oldWeight x g else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro g hg hnot
          split
          · exact FiniteDefect.defectPower_nonneg G τ g
              (A (color (part x))) (4 * D)
          · exact le_rfl
    have hactual : PartitionConcentration.rawStatistic S
        (fun y : I => part y) (oldWeight x) label < meanBound x + tail x := by
      exact (hrawUpper x).trans_le (add_le_add (hmean x) le_rfl)
    have hprod :
        (∏ y : I, q (part y) * ((A (color (part y))).card : ℝ) / 2) ≤
          ∏ y : I, ((host (part y)).card : ℝ) := by
      apply Finset.prod_le_prod
      · intro y hy
        exact div_nonneg (mul_nonneg (hqpos (part y)).le (by positivity))
          (by norm_num)
      · intro y hy
        exact (hlower (part y)).le
    have hrawLt : HostTools.rawFamilyMoment G (threshold (part x)) (4 * D)
          selected (host (part x)) <
        μ * ∏ y : I, ((host (part y)).card : ℝ) := by
      calc
        HostTools.rawFamilyMoment G (threshold (part x)) (4 * D)
            selected (host (part x)) ≤
          PartitionConcentration.rawStatistic S (fun y : I => part y)
            (oldWeight x) label := hrawSelected
        _ < meanBound x + tail x := hactual
        _ ≤ μ * (∏ y : I,
            q (part y) * ((A (color (part y))).card : ℝ) / 2) :=
          hnormalized x
        _ ≤ μ * ∏ y : I, ((host (part y)).card : ℝ) :=
          mul_le_mul_of_nonneg_left hprod hμ
    have hcardEq : (FiniteDefect.familyTuples selected).card =
        ∏ y : I, (host (part y)).card := by
      simp [selected, FiniteDefect.card_familyTuples]
    have hcardPos : (0 : ℝ) < (FiniteDefect.familyTuples selected).card := by
      exact_mod_cast Finset.card_pos.mpr <| by
        rw [FiniteDefect.familyTuples]
        exact Fintype.piFinset_nonempty.mpr fun y => hhostNonempty (part y)
    have hcardEqR : ((FiniteDefect.familyTuples selected).card : ℝ) =
        ∏ y : I, ((host (part y)).card : ℝ) := by
      exact_mod_cast hcardEq
    rw [HostTools.rawFamilyMoment_eq_card_mul_moment] at hrawLt
    rw [← hcardEqR] at hrawLt
    have hmomentSelected : FiniteDefect.familyMoment G (threshold (part x)) (4 * D)
        selected (host (part x)) ≤ μ := by
      nlinarith
    simpa [selected] using hmomentSelected
  apply AdaptiveGreedy.hasCopy_of_family_moments G H host part threshold
    defaultTarget defaultHost hhostNonempty hhostDisjoint hpart horder hthreshold
    hpartSize hγ hhostSize D hD hforward μ hμ hmoment htotal

end
end ConcentratedEmbedding
end Erdos163
