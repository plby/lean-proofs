import Mathlib
import ErdosProblems.Erdos550.OffTuranRegularityData
import ErdosProblems.Erdos550.OffTuranMatchingSelection

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact reduced-graph assembly for the direct off--Turán route

The regularity/blow-up cap is monotone in the tested cluster family.  Once its
two scalar lower bounds have been verified at a fixed natural threshold `B`,
every family of at least `B` clusters contains an edge of the exact reduced
graph.  This is precisely the independence hypothesis consumed by the
heavy-head and maximum-matching selector.
-/

open Finset SimpleGraph Finpartition

namespace Erdos550

open Classical

/-- A regular-pair cap checked at the threshold `B` gives the
independence bound for every larger cluster family. -/
theorem offTuran_alphaQ_of_cap
    {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hq : 1 ≤ q) (d ε₀ : ℝ) (m₀ B : ℕ)
    (hcap : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
      ∀ (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      ∀ (P : Finpartition (univ : Finset V)), P.IsUniform G ε →
      ∀ (A : Finset {C // C ∈ P.parts}),
        4 * q ^ 2 ≤ A.card →
        ((P.parts.card : ℝ) ^ 2 * ε <
          (A.card : ℝ) ^ 2 / (4 * q)) →
        (∀ C ∈ A, m₀ ≤ C.1.card) →
        ∃ C ∈ A, ∃ D ∈ A, C ≠ D ∧ G.IsUniform ε C.1 D.1 ∧
          d ≤ (G.edgeDensity C.1 D.1 : ℝ))
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hF : ¬ (F ⊑ Gᶜ))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hεcap : ε ≤ ε₀)
    (P : Finpartition (univ : Finset V)) (hP : P.IsUniform G ε)
    (hBbig : 4 * q ^ 2 ≤ B)
    (hBirregular :
      (P.parts.card : ℝ) ^ 2 * ε <
        (B : ℝ) ^ 2 / (4 * q))
    (hsize : ∀ C : {C // C ∈ P.parts}, m₀ ≤ C.1.card) :
    ∀ A : Finset {C // C ∈ P.parts}, B ≤ A.card →
      ∃ C ∈ A, ∃ D ∈ A,
        (offTuranReducedGraph G P ε d).Adj C D := by
  intro A hBA
  have hbig : 4 * q ^ 2 ≤ A.card := hBbig.trans hBA
  have hBAreal : (B : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hBA
  have hsq : (B : ℝ) ^ 2 ≤ (A.card : ℝ) ^ 2 := by
    nlinarith [hBAreal, (show (0 : ℝ) ≤ B by positivity)]
  have hqNat : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hq0 : (0 : ℝ) < 4 * q := by positivity
  have hirr :
      (P.parts.card : ℝ) ^ 2 * ε <
        (A.card : ℝ) ^ 2 / (4 * q) :=
    hBirregular.trans_le (div_le_div_of_nonneg_right hsq hq0.le)
  obtain ⟨C, hCA, D, hDA, hCD, huni, hdens⟩ :=
    hcap G hF ε hε0 hεcap P hP A hbig hirr
      (fun C _ => hsize C)
  exact ⟨C, hCA, D, hDA, hCD, huni, hdens⟩

/-- The exact reduced independence estimate, cleaned average
degree, and threshold fit produce heavy adjacent heads and a maximum matching
away from them, together with its exact uncovered-family bound. -/
theorem exists_offTuran_heavy_head_and_matching
    {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hq : 1 ≤ q) (d ε₀ : ℝ) (m₀ B : ℕ)
    (hcap : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
      ∀ (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      ∀ (P : Finpartition (univ : Finset V)), P.IsUniform G ε →
      ∀ (A : Finset {C // C ∈ P.parts}),
        4 * q ^ 2 ≤ A.card →
        ((P.parts.card : ℝ) ^ 2 * ε <
          (A.card : ℝ) ^ 2 / (4 * q)) →
        (∀ C ∈ A, m₀ ≤ C.1.card) →
        ∃ C ∈ A, ∃ D ∈ A, C ≠ D ∧ G.IsUniform ε C.1 D.1 ∧
          d ≤ (G.edgeDensity C.1 D.1 : ℝ))
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hF : ¬ (F ⊑ Gᶜ))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hεcap : ε ≤ ε₀)
    (P : Finpartition (univ : Finset V)) (hP : P.IsUniform G ε)
    (hBbig : 4 * q ^ 2 ≤ B)
    (hBirregular :
      (P.parts.card : ℝ) ^ 2 * ε <
        (B : ℝ) ^ 2 / (4 * q))
    (hsize : ∀ C : {C // C ∈ P.parts}, m₀ ≤ C.1.card)
    (S : Finset {C // C ∈ P.parts}) (D : {C // C ∈ P.parts} → ℝ)
    (base η N : ℝ)
    (hN : 0 < N) (hbase : 0 ≤ base + 80 * η * N)
    (hup : ∀ i ∈ S, D i ≤ N)
    (havg :
      (base + 100 * η * N) * (S.card : ℝ) ≤ ∑ i ∈ S, D i)
    (hBfit : (B : ℝ) ≤ (20 * η) * (S.card : ℝ)) :
    ∃ X Y : {C // C ∈ P.parts},
      X ∈ heavyClusterFamily S D base η N ∧
      Y ∈ heavyClusterFamily S D base η N ∧
      (offTuranReducedGraph G P ε d).Adj X Y ∧
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
        (cL cR : κ → {C // C ∈ P.parts})
        (U : Finset {C // C ∈ P.parts}),
        (∀ k, (offTuranReducedGraph G P ε d).Adj (cL k) (cR k)) ∧
        Function.Injective (Sum.elim cL cR) ∧
        (∀ k, cL k ≠ X ∧ cL k ≠ Y ∧
          cR k ≠ X ∧ cR k ≠ Y) ∧
        U.card < B ∧
        (∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
          a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR) ∧
        (Finset.univ \
          (Finset.univ.image cL ∪ Finset.univ.image cR)).card < B + 2 := by
  apply exists_heavy_head_and_matching_coverage
    (offTuranReducedGraph G P ε d) S D base η N B
    hN hbase hup havg hBfit
  exact offTuran_alphaQ_of_cap F q hq d ε₀ m₀ B hcap
    G hF ε hε0 hεcap P hP hBbig hBirregular hsize

end Erdos550
