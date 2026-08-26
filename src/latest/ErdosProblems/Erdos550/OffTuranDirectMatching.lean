import Mathlib
import ErdosProblems.Erdos550.OffTuranConstants
import ErdosProblems.Erdos550.OffTuranDirectBounds
import ErdosProblems.Erdos550.OffTuranMatchingSupply
import ErdosProblems.Erdos550.OffTuranReducedPipeline

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Heavy heads and matching supply for the direct off--Turán proof

The threshold `B = ⌈ηℓ/2⌉` is large enough for the reduced independence
estimate and small enough that the uncovered clusters cost at most `2ηN`.
-/

open Finset SimpleGraph Finpartition SzemerediRegularity

namespace Erdos550

open Classical

set_option maxHeartbeats 2000000 in
theorem OffTuranReducedDegreeData.exists_direct_heads_matching_supply
    {W : Type} [Fintype W] (F : SimpleGraph W)
    {A : Type} [Fintype A]
    (q : ℕ) (hq : 2 ≤ q)
    (ε₀ : ℝ) (m₀ : ℕ)
    {f : ℕ} {δ εCap : ℝ}
    (c : OffTuranConstants q f m₀ δ εCap)
    (hcap : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
      ∀ (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      ∀ (P : Finpartition (univ : Finset V)), P.IsUniform G ε →
      ∀ (A : Finset {C // C ∈ P.parts}),
        4 * q ^ 2 ≤ A.card →
        ((P.parts.card : ℝ) ^ 2 * ε <
          (A.card : ℝ) ^ 2 / (4 * q)) →
        (∀ C ∈ A, m₀ ≤ C.1.card) →
        ∃ C ∈ A, ∃ E ∈ A, C ≠ E ∧ G.IsUniform ε C.1 E.1 ∧
          c.η ≤ (G.edgeDensity C.1 E.1 : ℝ))
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : OffTuranReducedDegreeData G c.ε c.η
      (Fintype.card A) c.η m₀)
    (hF : ¬ (F ⊑ Gᶜ))
    (hεcap : c.ε ≤ ε₀)
    (hellEta :
      (D.P.parts.card : ℝ) ≤ c.η * Fintype.card V) :
    ∃ X Y : {C // C ∈ D.P.parts},
      (offTuranReducedGraph G D.P c.ε c.η).Adj X Y ∧
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
        (cL cR : κ → {C // C ∈ D.P.parts}),
        (∀ k, (offTuranReducedGraph G D.P c.ε c.η).Adj
          (cL k) (cR k)) ∧
        Function.Injective (Sum.elim cL cR) ∧
        (∀ k, cL k ≠ X ∧ cL k ≠ Y ∧
          cR k ≠ X ∧ cR k ≠ Y) ∧
        (Fintype.card A : ℝ) + 78 * c.η * Fintype.card V ≤
          ∑ k, hpHeadMatchingWeight G
            (offTuranReducedGraph G D.P c.ε c.η)
            (fun i : {C // C ∈ D.P.parts} => i.1)
            X cL cR k ∧
        (Fintype.card A : ℝ) + 78 * c.η * Fintype.card V ≤
          ∑ k, hpHeadMatchingWeight G
            (offTuranReducedGraph G D.P c.ε c.η)
            (fun i : {C // C ∈ D.P.parts} => i.1)
            Y cL cR k := by
  let ell : ℝ := D.P.parts.card
  let N : ℝ := Fintype.card V
  let B : ℕ := ⌈c.η * ell / 2⌉₊
  have hη0 : 0 < c.η := c.eta_pos
  have hε0 : 0 < c.ε := c.eps_pos
  have hq0 : (0 : ℝ) < q := by positivity
  have hell0 : 0 < ell := by
    dsimp [ell]
    exact_mod_cast D.parts_pos c.eps_pos
  have hclusterNat :
      ⌈8 * (q : ℝ) ^ 2 / c.η⌉₊ ≤ D.P.parts.card := by
    calc
      _ ≤ max m₀ ⌈8 * (q : ℝ) ^ 2 / c.η⌉₊ :=
        le_max_right _ _
      _ ≤ ⌈4 / c.ε⌉₊ := c.cluster_count_strong
      _ ≤ D.P.parts.card := D.lower_parts
  have hcluster :
      8 * (q : ℝ) ^ 2 ≤ c.η * ell := by
    have hceil :
        8 * (q : ℝ) ^ 2 / c.η ≤
          (⌈8 * (q : ℝ) ^ 2 / c.η⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hcast :
        (⌈8 * (q : ℝ) ^ 2 / c.η⌉₊ : ℝ) ≤ ell := by
      simpa [ell] using! (show
        (⌈8 * (q : ℝ) ^ 2 / c.η⌉₊ : ℝ) ≤
          D.P.parts.card by exact_mod_cast hclusterNat)
    have := hceil.trans hcast
    rw [div_le_iff₀ hη0] at this
    nlinarith
  have hBLower : c.η * ell / 2 ≤ (B : ℝ) := by
    dsimp [B]
    exact Nat.le_ceil _
  have hBUpper : (B : ℝ) < c.η * ell / 2 + 1 := by
    dsimp [B]
    exact Nat.ceil_lt_add_one (by positivity)
  have hBbig : 4 * q ^ 2 ≤ B := by
    exact_mod_cast (show
      (4 * (q : ℝ) ^ 2 : ℝ) ≤ (B : ℝ) by
        nlinarith [hcluster])
  have hBirregular :
      (D.P.parts.card : ℝ) ^ 2 * c.ε <
        (B : ℝ) ^ 2 / (4 * q) := by
    have heps :
        32 * (q : ℝ) * c.ε < c.η ^ 2 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using!
        (lt_div_iff₀ (by positivity :
          (0 : ℝ) < 32 * q)).mp c.eps_square_q_strong
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * q)]
    dsimp [ell] at hBLower
    nlinarith [sq_nonneg ((D.P.parts.card : ℝ) * c.η),
      sq_nonneg (B : ℝ),
      mul_pos hη0 (show (0 : ℝ) < D.P.parts.card by
        exact_mod_cast D.parts_pos c.eps_pos)]
  have hBfit :
      (B : ℝ) ≤ (20 * c.η) * D.P.parts.card := by
    dsimp [ell] at hcluster hBUpper
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [sq_nonneg (q : ℝ)]
  have hNpos : 0 < Fintype.card V := Fintype.card_pos
  have hbase :
      0 ≤ (Fintype.card A : ℝ) +
        80 * c.η * Fintype.card V := by positivity
  obtain ⟨X, Y, hX, hY, hXY, κ, instκ, decκ, cL, cR, U,
      hmatch, hinj, haway, hUsmall, hU, _huncovered⟩ :=
    D.exists_heavy_head_and_matching
      F q (by omega) c.η ε₀ m₀ B hcap hF
      c.eps_pos.le hεcap hBbig hBirregular hBfit hNpos hbase
  have hpartsScale :
      (D.P.parts.card : ℝ) * (D.scale : ℝ) ≤
        Fintype.card V + D.P.parts.card := by
    exact_mod_cast D.parts_mul_scale_le
  have hBplus :
      ((B + 2 : ℕ) : ℝ) ≤
        c.η * D.P.parts.card := by
    dsimp [ell] at hcluster hBUpper
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    nlinarith [sq_nonneg (q : ℝ)]
  have hloss :
      ((B + 2 : ℕ) : ℝ) * (D.scale : ℝ) ≤
        2 * c.η * Fintype.card V := by
    have hmul := mul_le_mul_of_nonneg_right hBplus
      (show (0 : ℝ) ≤ D.scale by positivity)
    have hell := hellEta
    have hη1 : c.η ≤ 1 := c.eta_small.le.trans (by norm_num)
    have hηN : 0 ≤ c.η * (Fintype.card V : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpartsScale c.eta_pos.le,
      mul_le_mul_of_nonneg_left hell c.eta_pos.le]
  have hSX :=
    heavy_head_matchingWeight_lower
      D X Y cL cR U hX hinj hUsmall hU hloss
  have hSY :=
    heavy_head_matchingWeight_lower
      D Y X cL cR U hY hinj hUsmall
        (fun a => by
          rw [hU a]
          aesop)
      hloss
  exact ⟨X, Y, hXY, κ, instκ, decκ, cL, cR,
    hmatch, hinj, haway, hSX, hSY⟩

end Erdos550
