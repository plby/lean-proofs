import ErdosProblems.Erdos1038.OneCutSoftBoxSound

/-!
# Finite exact cover of the soft edge
-/

namespace Erdos1038

noncomputable section

namespace SoftBox

def PositiveCoverCertified (terms : Nat) (finish : Rat) :
    Rat → List SoftBox → Prop
  | _, [] => False
  | start, [B] =>
      B.q.lo ≤ start ∧ B.PositiveCertified terms ∧ finish ≤ B.q.hi
  | start, B :: B' :: Bs =>
      B.q.lo ≤ start ∧ B.PositiveCertified terms ∧
        PositiveCoverCertified terms finish B.q.hi (B' :: Bs)

instance instDecidablePositiveCoverCertified (terms : Nat)
    (finish start : Rat) (boxes : List SoftBox) :
    Decidable (PositiveCoverCertified terms finish start boxes) := by
  induction boxes generalizing start with
  | nil => unfold PositiveCoverCertified; infer_instance
  | cons B Bs ih =>
      cases Bs with
      | nil => unfold PositiveCoverCertified; infer_instance
      | cons B' Bs =>
          unfold PositiveCoverCertified
          letI := ih B.q.hi
          infer_instance

theorem derivative_positive_of_cover {terms : Nat}
    {finish start : Rat} {boxes : List SoftBox}
    (hterms : 0 < terms)
    (hcover : PositiveCoverCertified terms finish start boxes)
    {q : ℝ} (hq : (start : ℝ) ≤ q ∧ q ≤ (finish : ℝ))
    (hqs : q < qSoft) :
    0 < LambdaDerivativeFormula q := by
  induction boxes generalizing start with
  | nil =>
      simp only [PositiveCoverCertified] at hcover
  | cons B Bs ih =>
      cases Bs with
      | nil =>
        simp only [PositiveCoverCertified] at hcover
        apply B.lambdaDerivativeFormula_pos_of_certified hterms hcover.2.1
        · constructor
          · have hlo : (B.q.lo : ℝ) ≤ (start : ℝ) := by
              exact_mod_cast hcover.1
            exact hlo.trans hq.1
          · exact hq.2.trans (by exact_mod_cast hcover.2.2)
        · exact hqs
      | cons B' Bs =>
        simp only [PositiveCoverCertified] at hcover
        by_cases hqhi : q ≤ (B.q.hi : ℝ)
        · apply B.lambdaDerivativeFormula_pos_of_certified hterms hcover.2.1
          · constructor
            · have hlo : (B.q.lo : ℝ) ≤ (start : ℝ) := by
                exact_mod_cast hcover.1
              exact hlo.trans hq.1
            · exact hqhi
          · exact hqs
        · exact ih hcover.2.2 ⟨(lt_of_not_ge hqhi).le, hq.2⟩

end SoftBox

end

end Erdos1038
