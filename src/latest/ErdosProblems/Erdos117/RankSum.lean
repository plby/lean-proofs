import ErdosProblems.Erdos117.SelectedStages
import Mathlib.Data.Finset.Sort

/-!
# The branch rank sum

An arbitrary positive cutoff separates cheap stages from expensive stages.
The selected-stage credit estimate and the interaction-product inequality
control the expensive stages together, rather than one at a time.
-/

namespace Erdos117

open scoped BigOperators

namespace CentralBranch

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {D : CentralChain G p} (B : CentralBranch D)

/-- The total interaction budget for a selection of expensive stages. -/
theorem selected_interaction_mul_le
    (hG : commutator G ≤ Subgroup.center G) {n R : ℕ}
    (hn : NoncommutingBound G n) (hR : 0 < R)
    (hcut : 128 * n * Nat.clog p ((2 * n) ^ 2) ≤ scalarCreditRate p * R * R)
    {M : ℕ} (e : Fin M → Fin B.length) (he : StrictMono e)
    (hm : ∀ k, R ≤ B.halfRank (e k)) :
    (∑ k, B.selectedInteractionSum e k) * (scalarCreditRate p * R) ≤
      M * M * (4 * n) := by
  have hpair (k : Fin M) (i : Fin k.val) :
      B.interactionRank (selectedPrevious e k i) (e k) *
        (scalarCreditRate p * R) ≤ 4 * n := by
    have hik : selectedPrevious e k i < e k := he i.2
    have hexp := B.expensive_interaction hG hn hik (hR.trans_le (hm k))
      (hcut.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (hm k)) (hm k)))
    exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hm k))).trans hexp
  have hlevel (k : Fin M) :
      B.selectedInteractionSum e k * (scalarCreditRate p * R) ≤ M * (4 * n) := by
    calc
      _ = ∑ i : Fin k.val, B.interactionRank (selectedPrevious e k i) (e k) *
          (scalarCreditRate p * R) := by rw [selectedInteractionSum, Finset.sum_mul]
      _ ≤ ∑ _i : Fin k.val, 4 * n := Finset.sum_le_sum (fun i _ => hpair k i)
      _ = k.val * (4 * n) := by simp
      _ ≤ M * (4 * n) := Nat.mul_le_mul_right _ (Nat.le_of_lt k.2)
  calc
    _ = ∑ k, B.selectedInteractionSum e k * (scalarCreditRate p * R) :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ _k : Fin M, M * (4 * n) := Finset.sum_le_sum (fun k _ => hlevel k)
    _ = M * M * (4 * n) := by simp [Nat.mul_assoc]

/-- A division-free cutoff estimate, uniform in the prime. Here the branch
length measures the size of the central series, not the order of the group. -/
theorem rank_sum_cutoff
    (hG : commutator G ≤ Subgroup.center G) {n R : ℕ}
    (hn : NoncommutingBound G n) (hR : 0 < R)
    (hcut : 128 * n * Nat.clog p ((2 * n) ^ 2) ≤ scalarCreditRate p * R * R) :
    scalarCreditRate p * R * (∑ k, B.halfRank k) ≤
      R * (n + B.length * scalarDefect p) +
      scalarCreditRate p * B.length * R * R + 4 * n * B.length * B.length +
      scalarCreditRate p * R * B.length * B.length * Nat.clog p ((2 * n) ^ 2) := by
  classical
  let E : Finset (Fin B.length) := Finset.univ.filter (fun k => R ≤ B.halfRank k)
  let e : Fin E.card ↪o Fin B.length := E.orderEmbOfFin rfl
  have hm (k : Fin E.card) : R ≤ B.halfRank (e k) := by
    have hk := E.orderEmbOfFin_mem rfl k
    exact (Finset.mem_filter.mp hk).2
  have hcard : E.card ≤ B.length := by
    simpa using Finset.card_le_card (Finset.filter_subset (fun k => R ≤ B.halfRank k)
      (Finset.univ : Finset (Fin B.length)))
  have hsum : (∑ k : Fin E.card, B.halfRank (e k)) = ∑ k ∈ E, B.halfRank k := by
    calc
      _ = ∑ k ∈ Finset.univ.map e.toEmbedding, B.halfRank k := by rw [Finset.sum_map]; rfl
      _ = _ := by rw [show Finset.univ.map e.toEmbedding = E from E.map_orderEmbOfFin_univ rfl]
  have hselected := B.selected_stage_credit_bound hG hn e e.strictMono
  rw [hsum] at hselected
  have hint := B.selected_interaction_mul_le hG hn hR hcut e e.strictMono hm
  have hexpensive : scalarCreditRate p * R * (∑ k ∈ E, B.halfRank k) ≤
      R * (n + B.length * scalarDefect p) + 4 * n * B.length * B.length +
        scalarCreditRate p * R * B.length * B.length * Nat.clog p ((2 * n) ^ 2) := by
    have hscaled := Nat.mul_le_mul_left R hselected
    have hbase : R * (n - 1 + E.card * scalarDefect p) ≤
        R * (n + B.length * scalarDefect p) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_right _ hcard))
    have hsize : E.card * E.card ≤ B.length * B.length := Nat.mul_le_mul hcard hcard
    have hint' : (∑ k, B.selectedInteractionSum e k) * (scalarCreditRate p * R) ≤
        4 * n * B.length * B.length :=
      hint.trans (by nlinarith [Nat.mul_le_mul_right (4 * n) hsize])
    have hlevels : scalarCreditRate p * R * E.card * E.card * Nat.clog p ((2 * n) ^ 2) ≤
        scalarCreditRate p * R * B.length * B.length * Nat.clog p ((2 * n) ^ 2) := by
      nlinarith [Nat.mul_le_mul_left (scalarCreditRate p * R * Nat.clog p ((2 * n) ^ 2)) hsize]
    nlinarith
  have hcheap : (∑ k ∈ Eᶜ, B.halfRank k) ≤ B.length * R := by
    calc
      _ ≤ ∑ _k ∈ Eᶜ, R := by
        apply Finset.sum_le_sum
        intro k hk
        have hnot : ¬ R ≤ B.halfRank k := by
          simpa only [E, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] using hk
        omega
      _ = Eᶜ.card * R := by simp
      _ ≤ B.length * R := Nat.mul_le_mul_right _ (by simpa using Eᶜ.card_le_univ)
  have htotal := Finset.sum_add_sum_compl E B.halfRank
  have hcheap' := Nat.mul_le_mul_left (scalarCreditRate p * R) hcheap
  rw [← htotal, Nat.mul_add]
  nlinarith only [hexpensive, hcheap']

end CentralBranch

end Erdos117
