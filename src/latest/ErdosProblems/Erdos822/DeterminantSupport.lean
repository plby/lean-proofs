/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CollisionAdmissibility
import ErdosProblems.Erdos822.ReducedTotientDet

/-!
# Arithmetic support of the reduced determinant

For a nonempty collision fiber, the common shifted coefficient divides the
totient difference.  Consequently the reduced determinant, which is the
quotient by that common coefficient, is itself a divisor of the difference.
This is the exact bridge needed to average the small-range singular factor:
every prime charged by that factor forces a totient-difference congruence.
-/

namespace Erdos822

/-- On the support of a collision fiber, the reduced determinant divides
the absolute totient difference. -/
theorem reducedTotientDet_dvd_totientNatAbs_of_nonempty
    {x m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ p ∈ outerPrimes x m, m < p)
    (hlarge' : ∀ p ∈ outerPrimes x m', m' < p)
    (hne : (outerCollisionPairs x m m').Nonempty) :
    reducedTotientDet m m' ∣
      ((Nat.totient m : ℤ) - Nat.totient m').natAbs := by
  unfold reducedTotientDet
  exact Nat.div_dvd_of_dvd
    (shiftedCoefficientGcd_dvd_totientNatAbs_of_nonempty
      hm hm' hlarge hlarge' hne)

/-- Every prime divisor seen by the reduced-determinant singular factor
therefore divides the absolute totient difference. -/
theorem prime_dvd_totientNatAbs_of_dvd_reducedTotientDet
    {x m m' p : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ q ∈ outerPrimes x m, m < q)
    (hlarge' : ∀ q ∈ outerPrimes x m', m' < q)
    (hne : (outerCollisionPairs x m m').Nonempty)
    (hp : p ∣ reducedTotientDet m m') :
    p ∣ ((Nat.totient m : ℤ) - Nat.totient m').natAbs :=
  hp.trans (reducedTotientDet_dvd_totientNatAbs_of_nonempty
    hm hm' hlarge hlarge' hne)

/-- Integer-congruence form of the preceding divisibility statement. -/
theorem totients_intModEq_of_dvd_reducedTotientDet
    {x m m' p : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ q ∈ outerPrimes x m, m < q)
    (hlarge' : ∀ q ∈ outerPrimes x m', m' < q)
    (hne : (outerCollisionPairs x m m').Nonempty)
    (hp : p ∣ reducedTotientDet m m') :
    (Nat.totient m : ℤ) ≡ (Nat.totient m' : ℤ) [ZMOD p] := by
  rw [Int.modEq_iff_dvd]
  have hsub : (p : ℤ) ∣
      (Nat.totient m : ℤ) - Nat.totient m' := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa using prime_dvd_totientNatAbs_of_dvd_reducedTotientDet
      hm hm' hlarge hlarge' hne hp
  have hneg := dvd_neg.mpr hsub
  simpa using hneg

/-- Natural-number congruence form, convenient for the structured totient
factorization in the small-divisor argument. -/
theorem totients_modEq_of_dvd_reducedTotientDet
    {x m m' p : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hlarge : ∀ q ∈ outerPrimes x m, m < q)
    (hlarge' : ∀ q ∈ outerPrimes x m', m' < q)
    (hne : (outerCollisionPairs x m m').Nonempty)
    (hp : p ∣ reducedTotientDet m m') :
    Nat.totient m ≡ Nat.totient m' [MOD p] := by
  rw [Nat.modEq_iff_dvd]
  exact (totients_intModEq_of_dvd_reducedTotientDet
    hm hm' hlarge hlarge' hne hp).dvd

end Erdos822
