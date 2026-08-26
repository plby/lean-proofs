import ErdosProblems.Erdos327.Assembly
import ErdosProblems.Erdos327.AsymptoticReduction
import ErdosProblems.Erdos327.SourceFilter

/-!
# Assembly from quantitative analytic estimates

This file packages the final finite-set bookkeeping.  It turns the three
analytic estimates used in the paper—source density, source-conflict loss,
and mixed-conflict loss—into `EvenEndpointConclusion`, and hence isolates
the remaining analytic obligations from the already formalized
combinatorial construction.
-/

namespace Erdos327

/-- Source vertices deleted by the score-oriented conflict filter. -/
noncomputable def rankBad
    (U S : Finset ℕ) (score : ℕ → ℕ) : Finset ℕ := by
  classical
  exact S.filter fun b ↦
    ∃ d ∈ U, d ≠ b ∧ score d ≤ score b ∧ ConflictTwo b d

@[simp] theorem mem_rankBad
    {U S : Finset ℕ} {score : ℕ → ℕ} {b : ℕ} :
    b ∈ rankBad U S score ↔
      b ∈ S ∧
        ∃ d ∈ U, d ≠ b ∧ score d ≤ score b ∧ ConflictTwo b d := by
  classical
  simp [rankBad]

/-- The retained source is exactly the original source minus its
score-oriented bad vertices. -/
theorem rankFilteredSource_eq_sdiff_rankBad
    (U S : Finset ℕ) (score : ℕ → ℕ) :
    rankFilteredSource U S score = S \ rankBad U S score := by
  classical
  ext b
  simp only [mem_rankFilteredSource, Finset.mem_sdiff, mem_rankBad]
  constructor
  · rintro ⟨hbS, hgood⟩
    refine ⟨hbS, ?_⟩
    rintro ⟨_, d, hdU, hdb, hscore, hconflict⟩
    exact hgood d hdU hdb hscore hconflict
  · rintro ⟨hbS, hnotbad⟩
    refine ⟨hbS, ?_⟩
    intro d hdU hdb hscore hconflict
    exact hnotbad ⟨hbS, d, hdU, hdb, hscore, hconflict⟩

theorem rankBad_subset
    (U S : Finset ℕ) (score : ℕ → ℕ) :
    rankBad U S score ⊆ S := by
  intro b hb
  exact (mem_rankBad.mp hb).1

/-- Exact source-cardinality accounting. -/
theorem card_rankFilteredSource_add_rankBad
    (U S : Finset ℕ) (score : ℕ → ℕ) :
    (rankFilteredSource U S score).card +
        (rankBad U S score).card =
      S.card := by
  rw [rankFilteredSource_eq_sdiff_rankBad,
    Finset.card_sdiff_of_subset (rankBad_subset U S score)]
  exact Nat.sub_add_cancel
    (Finset.card_le_card (rankBad_subset U S score))

/-- Real-valued lower bound after deleting score-oriented source
conflicts. -/
theorem rankFilteredSource_card_lower
    {U S : Finset ℕ} {score : ℕ → ℕ} {sLoss sSize : ℝ}
    (hsize : sSize ≤ (S.card : ℝ))
    (hloss : ((rankBad U S score).card : ℝ) ≤ sLoss) :
    sSize - sLoss ≤ (rankFilteredSource U S score).card := by
  have hcardNat := card_rankFilteredSource_add_rankBad U S score
  have hcardReal :
      ((rankFilteredSource U S score).card : ℝ) +
          ((rankBad U S score).card : ℝ) =
        (S.card : ℝ) := by
    exact_mod_cast hcardNat
  linarith

/-- A source of density `ρ/4` with at most `ρ/8` score-oriented losses
already proves the positive-density conclusion for the second question.
This is the formal version of Sawin's orientation construction. -/
theorem erdos327SecondConclusion_of_analytic_source
    {ρ : ℝ} (hρ : 0 < ρ) {N₀ : ℕ}
    (hwit :
      ∀ N ≥ N₀, ∃ S : Finset ℕ,
        S ⊆ upto N ∧
        (N : ℝ) * ρ / 4 ≤ (S.card : ℝ) ∧
        ((rankBad (upto N) S
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * ρ / 8) :
    Erdos327SecondConclusion := by
  refine ⟨ρ / 8, by positivity, N₀, ?_⟩
  intro N hN
  rcases hwit N hN with ⟨S, hS, hScard, hSourceBad⟩
  let B :=
    rankFilteredSource (upto N) S
      ArithmeticFunction.cardFactors
  have hBsubsetS : B ⊆ S :=
    rankFilteredSource_subset (upto N) S
      ArithmeticFunction.cardFactors
  have hBsubset : B ⊆ upto N := hBsubsetS.trans hS
  have hBadm : TwoAdmissible B :=
    twoAdmissible_rankFilteredSource hS
  have hBcard :
      (N : ℝ) * ρ / 8 ≤ (B.card : ℝ) := by
    dsimp [B]
    have h := rankFilteredSource_card_lower
      (U := upto N) (S := S)
      (score := ArithmeticFunction.cardFactors)
      hScard hSourceBad
    linarith
  refine ⟨B, hBsubset, hBadm, ?_⟩
  convert hBcard using 1 <;> ring

/-- The exact analytic interface for the paper's construction.

For each sufficiently large `N`, the source `S` has density `ρ/4`;
at most `ρ/8` is lost to centered source conflicts; the odd host loses
at most `ρ/32`; and at most another `ρ/32` odd vertices meet the
retained doubled source. -/
theorem evenEndpointConclusion_of_analytic_sets
    {ρ : ℝ} (hρ : 0 < ρ) {N₀ : ℕ}
    (hwit :
      ∀ N ≥ N₀, ∃ S O : Finset ℕ,
        S ⊆ upto N ∧
        O ⊆ upto (2 * N) ∧
        (∀ a ∈ O, Odd a) ∧
        (N : ℝ) * ρ / 4 ≤ (S.card : ℝ) ∧
        ((rankBad (upto N) S
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * ρ / 8 ∧
        (N : ℝ) - (N : ℝ) * ρ / 32 ≤ (O.card : ℝ) ∧
        ((mixedBad O
          (rankFilteredSource (upto N) S
            ArithmeticFunction.cardFactors)).card : ℝ) ≤
              (N : ℝ) * ρ / 32) :
    EvenEndpointConclusion := by
  apply evenEndpointConclusion_of_witnesses hρ
  intro N hN
  rcases hwit N hN with
    ⟨S, O, hS, hO, hodd, hScard, hSourceBad, hOcard, hMixed⟩
  let B :=
    rankFilteredSource (upto N) S
      ArithmeticFunction.cardFactors
  have hBsubsetS : B ⊆ S :=
    rankFilteredSource_subset (upto N) S
      ArithmeticFunction.cardFactors
  have hBsubset : B ⊆ upto N := hBsubsetS.trans hS
  have hBadm : TwoAdmissible B :=
    twoAdmissible_rankFilteredSource hS
  have hBcard :
      (N : ℝ) * ρ / 8 ≤ (B.card : ℝ) := by
    dsimp [B]
    have h := rankFilteredSource_card_lower
      (U := upto N) (S := S)
      (score := ArithmeticFunction.cardFactors)
      hScard hSourceBad
    linarith
  exact ⟨O, B, hO, hBsubset, hodd, hBadm,
    hOcard, hMixed, hBcard⟩

/-- Fully reduced interface for the original Erdős 327 conclusion. -/
theorem erdos327Conclusion_of_analytic_sets
    {ρ : ℝ} (hρ : 0 < ρ) {N₀ : ℕ}
    (hwit :
      ∀ N ≥ N₀, ∃ S O : Finset ℕ,
        S ⊆ upto N ∧
        O ⊆ upto (2 * N) ∧
        (∀ a ∈ O, Odd a) ∧
        (N : ℝ) * ρ / 4 ≤ (S.card : ℝ) ∧
        ((rankBad (upto N) S
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * ρ / 8 ∧
        (N : ℝ) - (N : ℝ) * ρ / 32 ≤ (O.card : ℝ) ∧
        ((mixedBad O
          (rankFilteredSource (upto N) S
            ArithmeticFunction.cardFactors)).card : ℝ) ≤
              (N : ℝ) * ρ / 32) :
    Erdos327Conclusion :=
  erdos327Conclusion_of_evenEndpoint
    (evenEndpointConclusion_of_analytic_sets hρ hwit)

/-- The same analytic witnesses prove both questions in Erdős Problem 327:
the first through the odd/even assembly, and the second directly through
the score-oriented source filter. -/
theorem erdos327FullConclusion_of_analytic_sets
    {ρ : ℝ} (hρ : 0 < ρ) {N₀ : ℕ}
    (hwit :
      ∀ N ≥ N₀, ∃ S O : Finset ℕ,
        S ⊆ upto N ∧
        O ⊆ upto (2 * N) ∧
        (∀ a ∈ O, Odd a) ∧
        (N : ℝ) * ρ / 4 ≤ (S.card : ℝ) ∧
        ((rankBad (upto N) S
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * ρ / 8 ∧
        (N : ℝ) - (N : ℝ) * ρ / 32 ≤ (O.card : ℝ) ∧
        ((mixedBad O
          (rankFilteredSource (upto N) S
            ArithmeticFunction.cardFactors)).card : ℝ) ≤
              (N : ℝ) * ρ / 32) :
    Erdos327FullConclusion := by
  refine ⟨erdos327Conclusion_of_analytic_sets hρ hwit, ?_⟩
  apply erdos327SecondConclusion_of_analytic_source hρ
  intro N hN
  rcases hwit N hN with
    ⟨S, O, hS, _hO, _hodd, hScard, hSourceBad,
      _hOcard, _hMixed⟩
  exact ⟨S, hS, hScard, hSourceBad⟩

end Erdos327
