import ErdosProblems.Erdos336.WideRankDenseEndgame
import ErdosProblems.Erdos336.LevCertificatePointwise
import ErdosProblems.Erdos336.StableHighPowerCertificateV3

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

lemma rankDenseCertificate_to_wide
    {C : Set (ZMod N)} {t : ℕ}
    (h : RankDenseCertificate C t) :
    WideRankDenseCertificate C t := by
  rcases h with hdense | hrank
  · left
    have hK : 30000 ≤ 30000000 * Nat.factorial 36 := by
      norm_num [Nat.factorial]
    exact lt_of_lt_of_le hdense
      (Nat.mul_le_mul_right (ExactPower C t).ncard hK)
  · exact Or.inr hrank

/-- V3's wide-density/rank/exception output implies the corresponding wide
rank-or-dense endgame certificate under strict `9/4`. -/
theorem wideRankDenseCertificate_of_stableV3
    (C : Set (ZMod N)) (t : ℕ) (ht : 15 ≤ t) (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hstable : StableHighPowerCertificateV3 C t) :
    WideRankDenseCertificate C t := by
  let S : Set (ZMod N) := ExactPower C t
  have hzS : 0 ∈ S := by
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hSpos : 0 < S.ncard := by
    rw [Set.ncard_pos]
    exact ⟨0, hzS⟩
  have hSle : S.ncard ≤ (ExactPower S 2).ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro x hx
    rw [exactPower_eq_nsmul, two_nsmul]
    exact ⟨x, hx, 0, hzS, by simp⟩
  have hpower : ExactPower S 2 = ExactPower C (2 * t) := by
    simpa [S] using exactPower_exactPower C t 2
  have hdoubS : 4 * (ExactPower S 2).ncard < 9 * S.ncard := by
    rw [hpower]
    simpa [S] using hdoub
  rcases hstable with hone | hdense | hstruct
  · left
    change Fintype.card (ZMod N) <
      (30000000 * Nat.factorial 36) * S.ncard
    have hK : 2 ≤ 30000000 * Nat.factorial 36 := by
      norm_num [Nat.factorial]
    have hSone : 1 ≤ S.ncard := by omega
    have hprod : 2 * 1 ≤ (30000000 * Nat.factorial 36) * S.ncard :=
      Nat.mul_le_mul hK hSone
    rw [hone]
    omega
  · left
    change Fintype.card (ZMod N) <
      (30000000 * Nat.factorial 36) * S.ncard
    change Fintype.card (ZMod N) <
      (10000000 * Nat.factorial 36) * stableWeight S at hdense
    have hweight : stableWeight S < 3 * S.ncard := by
      unfold stableWeight
      omega
    have hKpos : 0 < 10000000 * Nat.factorial 36 := by
      positivity
    calc
      Fintype.card (ZMod N) <
          (10000000 * Nat.factorial 36) * stableWeight S := hdense
      _ < (10000000 * Nat.factorial 36) * (3 * S.ncard) :=
        (Nat.mul_lt_mul_left hKpos).2 hweight
      _ = (30000000 * Nat.factorial 36) * S.ncard := by ring
  · have hlev : LevHighPowerCertificate C t := Or.inr hstruct
    exact rankDenseCertificate_to_wide
      (rankDenseCertificate_of_levCertificate C t ht hzero
        hprimitive hdoub hlev)

end Erdos336
