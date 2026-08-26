import ErdosProblems.Erdos1038.OneCutTailQBox

/-!
# Finite exact covers in the stable tail chart

The boxes may choose their logarithm shifts independently.  The recursive
certificate checks every box and checks that adjacent parameter intervals
leave no gap.
-/

namespace Erdos1038

noncomputable section

namespace OneCutTailCertificate
namespace TailQBox

def NegativeCoverCertified (terms : Nat) (finish : Rat) :
    Rat → List TailQBox → Prop
  | _, [] => False
  | start, [B] =>
      B.q.lo ≤ start ∧ B.NegativeCertified terms ∧ finish ≤ B.q.hi
  | start, B :: B' :: Bs =>
      B.q.lo ≤ start ∧ B.NegativeCertified terms ∧
        NegativeCoverCertified terms finish B.q.hi (B' :: Bs)

def PositiveCoverCertified (terms : Nat) (finish : Rat) :
    Rat → List TailQBox → Prop
  | _, [] => False
  | start, [B] =>
      B.q.lo ≤ start ∧ B.PositiveCertified terms ∧ finish ≤ B.q.hi
  | start, B :: B' :: Bs =>
      B.q.lo ≤ start ∧ B.PositiveCertified terms ∧
        PositiveCoverCertified terms finish B.q.hi (B' :: Bs)

instance instDecidableNegativeCoverCertified (terms : Nat)
    (finish start : Rat) (boxes : List TailQBox) :
    Decidable (NegativeCoverCertified terms finish start boxes) := by
  induction boxes generalizing start with
  | nil => unfold NegativeCoverCertified; infer_instance
  | cons B Bs ih =>
      cases Bs with
      | nil => unfold NegativeCoverCertified; infer_instance
      | cons B' Bs =>
          unfold NegativeCoverCertified
          letI := ih B.q.hi
          infer_instance

instance instDecidablePositiveCoverCertified (terms : Nat)
    (finish start : Rat) (boxes : List TailQBox) :
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

theorem derivative_negative_of_cover {terms : Nat}
    {finish start : Rat} {boxes : List TailQBox}
    (hcover : NegativeCoverCertified terms finish start boxes)
    {q : ℝ} (hq : (start : ℝ) ≤ q ∧ q ≤ (finish : ℝ)) :
    LambdaDerivativeFormula q < 0 := by
  induction boxes generalizing start with
  | nil =>
      simp only [NegativeCoverCertified] at hcover
  | cons B Bs ih =>
      cases Bs with
      | nil =>
        simp only [NegativeCoverCertified] at hcover
        apply B.lambdaDerivativeFormula_neg_of_certified hcover.2.1
        constructor
        · have hlo : (B.q.lo : ℝ) ≤ (start : ℝ) := by
            exact_mod_cast hcover.1
          exact hlo.trans hq.1
        · exact hq.2.trans (by exact_mod_cast hcover.2.2)
      | cons B' Bs =>
        simp only [NegativeCoverCertified] at hcover
        by_cases hqhi : q ≤ (B.q.hi : ℝ)
        · apply B.lambdaDerivativeFormula_neg_of_certified hcover.2.1
          constructor
          · have hlo : (B.q.lo : ℝ) ≤ (start : ℝ) := by
              exact_mod_cast hcover.1
            exact hlo.trans hq.1
          · exact hqhi
        · exact ih hcover.2.2 ⟨(lt_of_not_ge hqhi).le, hq.2⟩

theorem derivative_positive_of_cover {terms : Nat}
    {finish start : Rat} {boxes : List TailQBox}
    (hcover : PositiveCoverCertified terms finish start boxes)
    {q : ℝ} (hq : (start : ℝ) ≤ q ∧ q ≤ (finish : ℝ)) :
    0 < LambdaDerivativeFormula q := by
  induction boxes generalizing start with
  | nil =>
      simp only [PositiveCoverCertified] at hcover
  | cons B Bs ih =>
      cases Bs with
      | nil =>
        simp only [PositiveCoverCertified] at hcover
        apply B.lambdaDerivativeFormula_pos_of_certified hcover.2.1
        constructor
        · have hlo : (B.q.lo : ℝ) ≤ (start : ℝ) := by
            exact_mod_cast hcover.1
          exact hlo.trans hq.1
        · exact hq.2.trans (by exact_mod_cast hcover.2.2)
      | cons B' Bs =>
        simp only [PositiveCoverCertified] at hcover
        by_cases hqhi : q ≤ (B.q.hi : ℝ)
        · apply B.lambdaDerivativeFormula_pos_of_certified hcover.2.1
          constructor
          · have hlo : (B.q.lo : ℝ) ≤ (start : ℝ) := by
              exact_mod_cast hcover.1
            exact hlo.trans hq.1
          · exact hqhi
        · exact ih hcover.2.2 ⟨(lt_of_not_ge hqhi).le, hq.2⟩

end TailQBox
end OneCutTailCertificate

end

end Erdos1038
