/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite arithmetic orders refining the optimal BBMST coordinate score.
Informal source: BBMST Definition 5.4. Ties are resolved by a finite enumeration.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeProfiles
import ErdosProblems.Erdos1189.Tau
import Mathlib.Data.Prod.Lex

namespace Erdos1189

lemma exists_rank_refining_score {α : Type*} [Finite α] (score : α → ℝ) :
    ∃ rank : α → ℕ, Function.Injective rank ∧
      ∀ a b, score a < score b → rank a < rank b := by
  classical
  let := Fintype.ofFinite α
  let key : α → ℝ ×ₗ Fin (Fintype.card α) :=
    fun a => toLex (score a, Fintype.equivFin α a)
  have hkey : Function.Injective key := by
    intro a b h
    exact (Fintype.equivFin α).injective (congrArg (fun x => (ofLex x).2) h)
  let : LinearOrder α := LinearOrder.lift' key hkey
  let E : α ≃o Fin (Fintype.card α) := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨fun a => (E a).val, ?_, ?_⟩
  · intro a b hab
    exact E.injective (Fin.ext hab)
  · intro a b hab
    apply E.strictMono
    exact Prod.Lex.left _ _ hab

noncomputable def coordinateScore (p e : ℕ) : ℝ := ((p : ℝ) - 1) / logIncrement e

lemma coordinateScore_pos {p : ℕ} (hp : p.Prime) (e : ℕ) : 0 < coordinateScore p e := by
  apply div_pos
  · exact sub_pos.mpr (by exact_mod_cast hp.one_lt)
  · exact logIncrement_pos e

lemma coordinateScore_strictMono {p : ℕ} (hp : p.Prime) : StrictMono (coordinateScore p) := by
  intro e f hef
  apply (div_lt_div_iff_of_pos_left
    (show (0 : ℝ) < (p : ℝ) - 1 by
      have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith)
    (logIncrement_pos e) (logIncrement_pos f)).mpr
  exact logIncrement_strictAnti hef

lemma first_prime_score_lt {p q : ℕ} (hp : p.Prime) (hqp : q < p) (e : ℕ) :
    coordinateScore q 0 < coordinateScore p e := by
  have hfirst : coordinateScore q 0 < coordinateScore p 0 := by
    apply (div_lt_div_iff_of_pos_right (logIncrement_pos 0)).mpr
    exact sub_lt_sub_right (by exact_mod_cast hqp) 1
  exact hfirst.trans_le ((coordinateScore_strictMono hp).monotone (Nat.zero_le e))

theorem exists_optimal_frame_rank (N : ℕ) :
    ∃ rank : PrimeCoordinate N → ℕ, Function.Injective rank ∧ IsArithmeticRank rank ∧
      ∀ c i, coordinateScore c.1 c.2 < coordinateScore i.1 i.2 → rank c < rank i := by
  obtain ⟨rank, hinj, href⟩ := exists_rank_refining_score
    (fun c : PrimeCoordinate N => coordinateScore c.1 c.2)
  refine ⟨rank, hinj, ?_, href⟩
  intro p e f hef
  exact href _ _ (coordinateScore_strictMono (Nat.prime_of_mem_primeFactors p.2) hef)

end Erdos1189
