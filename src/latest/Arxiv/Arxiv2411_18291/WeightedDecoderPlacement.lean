import Arxiv.Arxiv2411_18291.WeightedCliquePlacement
import Arxiv.Arxiv2411_18291.WeightedDecoderRoots

/-! # Constructed decoder regions with bounded variable capacities

The original sparse generator supplies both the weighted root budget and
the increment bound. Under the displayed finite inequalities, the regions,
their graph bound, and their capacity bound are all constructed. No uniform
constant bound on the generator's edge multiplicities is assumed.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem exists_weighted_decoder_placement_of_weight_bound (hqr : r + 1 ≤ q)
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) {θD θB c C : ℝ}
    (hD : IsCliqueFamilyBounded r D θD) (hB : IsGraphBounded B θB)
    (hθD : 0 ≤ θD) (hθB : 0 ≤ θB) (hc : 0 < c) (hC : 0 < C)
    (hweight : ∀ e : Block V (r + 1), (decoderRootWeight D e : ℝ) ≤ C)
    (hn : 4 * (q + (r + 1)) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : (q + (r + 1)).choose (r + 1) *
      (θB + (q + (r + 1)).choose (r + 1) *
        ((1 + c) * (2 * (r + 1).factorial * (θB + θD)))) ≤ 1 / 4)
    (hfailure : (q + (r + 1)).choose (r + 1) * Fintype.card (Block V r) *
      Real.exp (-(2 * (r + 1).factorial * (θB + θD) * Fintype.card V * c ^ 2 /
        ((2 + c) * C))) < 1) :
    let L : ℝ := (1 + c) * (2 * (r + 1).factorial * (θB + θD))
    let K : ℕ := (q + (r + 1)).choose (r + 1)
    ∃ Z : B → Block V (q + (r + 1)),
      IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z ∧
      IsWeightedFamilyBounded r Z (fun e => decoderRootWeight D e.val) (K * L) ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Z) (θB + K * L) ∧
      IsCliqueCapacityBounded r (D ∪ cliqueRefinement q (univ.image Z))
        (edgewiseDecoderCapacity D Z)
        ((2 ^ q * (r + 1).factorial : ℕ) *
          (θD + (q + 1).choose (q - r) * (K * L))) := by
  classical
  let s := q + (r + 1)
  let L : ℝ := (1 + c) * (2 * (r + 1).factorial * (θB + θD))
  let K : ℕ := s.choose (r + 1)
  change ∃ Z : B → Block V s,
    IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z ∧
    IsWeightedFamilyBounded r Z (fun e => decoderRootWeight D e.val) (K * L) ∧
    IsGraphBounded (cliqueCoverGraph (r := r) Z) (θB + K * L) ∧
    IsCliqueCapacityBounded r (D ∪ cliqueRefinement q (univ.image Z))
      (edgewiseDecoderCapacity D Z)
      ((2 ^ q * (r + 1).factorial : ℕ) * (θD + (q + 1).choose (q - r) * (K * L)))
  have hrs : r + 1 ≤ s := by dsimp only [s]; omega
  obtain ⟨f, _, hf⟩ := exists_subset_card_eq (s := (univ : Finset (Fin s)))
    (by simpa only [card_univ, Fintype.card_fin] using hrs)
  let F₀ : Block (Fin s) (r + 1) := ⟨f, hf⟩
  have hsV : s ≤ Fintype.card V := by
    have hp := Nat.le_self_pow (by decide : 2 ≠ 0) s
    change 4 * s ^ 2 ≤ Fintype.card V at hn
    omega
  obtain ⟨a, _, ha⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (by simpa only [card_univ] using hrs.trans hsV)
  let e₀ : Block V (r + 1) := ⟨a, ha⟩
  let enum : Fin B.card ≃ B := B.equivFin.symm
  let E : ℕ → Block V (r + 1) :=
    fun i => if hi : i < B.card then (enum ⟨i, hi⟩).val else e₀
  let w : ℕ → ℕ := fun i => decoderRootWeight D (E i)
  have hE (i : Fin B.card) : E i = (enum i).val := by
    dsimp only [E]
    rw [dif_pos i.isLt]
  have hEmem (i : Fin B.card) : E i ∈ B := hE i ▸ (enum i).property
  have hEinj : Function.Injective (fun i : Fin B.card => E i) := by
    intro i j hij
    apply enum.injective
    apply Subtype.ext
    simpa only [hE] using hij
  have hroot : IsWeightedFamilyBounded r (fun i : Fin B.card => E i)
      (fun i => w i) (θB + θD) := by
    intro S
    simp only [w, hE]
    rw [weightedFamilyDegree_reindex enum (fun e : B => e.val)
      (fun e => decoderRootWeight D e.val) S.val]
    exact decoderRootWeight_bounded hD hB S
  obtain ⟨Q, hQ, hwQ, hgQ⟩ := exists_indexed_weighted_clique_placement F₀
    (Fintype.card_fin s) B.card E w B hB hθB (add_nonneg hθB hθD)
    hC hc hn hnpos hsmall
    (fun i _ => decoderRootWeight_pos D (E i))
    (fun i _ => hweight (E i)) hEinj
    (fun i hi => hEmem ⟨i, hi⟩) hroot hfailure
  let Z : B → Block V s := fun e => Q (enum.symm e)
  have hwZ : IsWeightedFamilyBounded r Z (fun e => decoderRootWeight D e.val) (K * L) := by
    intro S
    have hweights : (fun e : B => decoderRootWeight D e.val) = (fun e => w (enum.symm e)) := by
      funext e
      simp only [w, hE, Equiv.apply_symm_apply]
    rw [hweights]
    change (weightedFamilyDegree (fun e => Q (enum.symm e)) (fun e => w (enum.symm e))
      S.val : ℝ) < _
    rw [weightedFamilyDegree_reindex enum.symm Q (fun i => w i) S.val]
    exact hwQ S
  refine ⟨Z, ?_, hwZ, ?_, decoderRootWeight_capacity_bounded hqr Z hD hwZ⟩
  · constructor
    · intro e
      have heq : E (enum.symm e) = e.val := by rw [hE, Equiv.apply_symm_apply]
      simpa only [Z, heq] using hQ.punctured (enum.symm e)
    · intro e f hef
      exact hQ.disjoint (fun h => hef (enum.symm.injective h))
  · change IsGraphBounded (cliqueCoverGraph (r := r) (fun e => Q (enum.symm e))) _
    rw [cliqueCoverGraph_reindex]
    exact hgQ

theorem exists_weighted_decoder_placement (hqr : r + 1 ≤ q)
    (D : Finset (Block V q)) (B : Hypergraph V (r + 1)) {θD θB c : ℝ}
    (hD : IsCliqueFamilyBounded r D θD) (hB : IsGraphBounded B θB)
    (hθD : 0 ≤ θD) (hθB : 0 ≤ θB) (hc : 0 < c)
    (hn : 4 * (q + (r + 1)) ^ 2 ≤ Fintype.card V) (hnpos : 0 < Fintype.card V)
    (hsmall : (q + (r + 1)).choose (r + 1) *
      (θB + (q + (r + 1)).choose (r + 1) *
        ((1 + c) * (2 * (r + 1).factorial * (θB + θD)))) ≤ 1 / 4)
    (hfailure : (q + (r + 1)).choose (r + 1) * Fintype.card (Block V r) *
      Real.exp (-(2 * (r + 1).factorial * (θB + θD) * Fintype.card V * c ^ 2 /
        ((2 + c) * (1 + θD * Fintype.card V)))) < 1) :
    let L : ℝ := (1 + c) * (2 * (r + 1).factorial * (θB + θD))
    let K : ℕ := (q + (r + 1)).choose (r + 1)
    ∃ Z : B → Block V (q + (r + 1)),
      IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z ∧
      IsWeightedFamilyBounded r Z (fun e => decoderRootWeight D e.val) (K * L) ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Z) (θB + K * L) ∧
      IsCliqueCapacityBounded r (D ∪ cliqueRefinement q (univ.image Z))
        (edgewiseDecoderCapacity D Z)
        ((2 ^ q * (r + 1).factorial : ℕ) *
          (θD + (q + 1).choose (q - r) * (K * L))) := by
  exact exists_weighted_decoder_placement_of_weight_bound hqr D B hD hB hθD hθB hc
    (by positivity : (0 : ℝ) < 1 + θD * Fintype.card V)
    (fun e => (decoderRootWeight_lt hD e).le) hn hnpos hsmall hfailure

end Arxiv2411_18291
