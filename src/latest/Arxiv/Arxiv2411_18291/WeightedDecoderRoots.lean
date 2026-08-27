import Arxiv.Arxiv2411_18291.WeightedDecoderDegrees

/-! # Positive decoder weights controlled by the original sparse boundary

The extra unit covers the unweighted occupied graph, including edges with
zero multiplicity. The total weighted root degree is bounded by the sum of
the source graph degree and the original clique-boundary degree.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def decoderRootWeight (D : Finset (Block V q)) (e : Block V (r + 1)) : ℕ :=
  1 + (D.filter fun P => e.val ⊆ P.val).card

omit [Fintype V] in
theorem decoderRootWeight_pos (D : Finset (Block V q)) (e : Block V (r + 1)) :
    1 ≤ decoderRootWeight D e := Nat.le_add_right 1 _

theorem decoderRootWeight_degree_le (D : Finset (Block V q))
    (B : Hypergraph V (r + 1)) (S : Finset V) :
    (weightedFamilyDegree (fun i : B => i.val) (fun i => decoderRootWeight D i.val) S : ℤ) ≤
      degree (indicator B) S + degree (boundary (r + 1) (indicator D)) S := by
  classical
  rw [weightedFamilyDegree,
    Finset.sum_coe_sort B (fun e => if S ⊆ e.val then decoderRootWeight D e else 0),
    Nat.cast_sum]
  have hterm (e : Block V (r + 1)) :
      ((if S ⊆ e.val then decoderRootWeight D e else 0 : ℕ) : ℤ) =
        (if S ⊆ e.val then 1 else 0) +
          (if S ⊆ e.val then boundary (r + 1) (indicator D) e else 0) := by
    rw [boundary_indicator]
    by_cases hS : S ⊆ e.val <;> simp only [hS, if_true, if_false,
      decoderRootWeight, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  simp only [hterm, sum_add_distrib]
  have hcount : (∑ e ∈ B, if S ⊆ e.val then (1 : ℤ) else 0) = degree (indicator B) S := by
    rw [degree_indicator, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rw [hcount]
  apply add_le_add le_rfl
  apply sum_le_sum_of_subset_of_nonneg (subset_univ B)
  intro e _ _
  split_ifs
  · rw [boundary_indicator]
    exact Nat.cast_nonneg _
  · exact le_rfl

theorem decoderRootWeight_bounded {D : Finset (Block V q)}
    {B : Hypergraph V (r + 1)} {θD θB : ℝ}
    (hD : IsCliqueFamilyBounded r D θD) (hB : IsGraphBounded B θB) :
    IsWeightedFamilyBounded r (fun i : B => i.val)
      (fun i => decoderRootWeight D i.val) (θB + θD) := by
  intro S
  have hle : (weightedFamilyDegree (fun i : B => i.val)
      (fun i => decoderRootWeight D i.val) S.val : ℝ) ≤
        ((degree (indicator B) S.val : ℤ) : ℝ) +
          ((degree (boundary (r + 1) (indicator D)) S.val : ℤ) : ℝ) := by
    exact_mod_cast decoderRootWeight_degree_le D B S.val
  have hgraph : ((degree (indicator B) S.val : ℤ) : ℝ) < θB * Fintype.card V := by
    simpa only [degree_indicator, Int.cast_natCast] using hB S
  exact hle.trans_lt (by simpa only [add_mul] using add_lt_add hgraph (hD S))

theorem decoderRootWeight_lt {D : Finset (Block V q)} {θD : ℝ}
    (hD : IsCliqueFamilyBounded r D θD) (e : Block V (r + 1)) :
    (decoderRootWeight D e : ℝ) < 1 + θD * Fintype.card V := by
  have hh := hD.multiplicity_lt e
  simp only [decoderRootWeight, Nat.cast_add, Nat.cast_one]
  linarith only [hh]

theorem decoderRootWeight_capacity_bounded (hqr : r + 1 ≤ q)
    {D : Finset (Block V q)} {B : Hypergraph V (r + 1)}
    (Z : B → Block V (q + (r + 1))) {θD θZ : ℝ}
    (hD : IsCliqueFamilyBounded r D θD)
    (hZ : IsWeightedFamilyBounded r Z (fun i => decoderRootWeight D i.val) θZ) :
    IsCliqueCapacityBounded r (D ∪ cliqueRefinement q (univ.image Z))
      (edgewiseDecoderCapacity D Z)
      ((2 ^ q * (r + 1).factorial : ℕ) * (θD + (q + 1).choose (q - r) * θZ)) := by
  apply edgewiseDecoderCapacity_bounded hqr Z hD
  intro S
  have hle : (weightedFamilyDegree Z
      (fun i => (D.filter fun P => i.val.val ⊆ P.val).card) S.val : ℝ) ≤
        weightedFamilyDegree Z (fun i => decoderRootWeight D i.val) S.val := by
    exact_mod_cast weightedFamilyDegree_mono Z
      (w := fun i => (D.filter fun P => i.val.val ⊆ P.val).card)
      (w' := fun i => decoderRootWeight D i.val)
      (fun i => by unfold decoderRootWeight; omega) S.val
  exact hle.trans_lt (hZ S)

end Arxiv2411_18291
