import Wikipedia.SzemeredisTheorem.ArithmeticProgression.CountExtraction
import Wikipedia.GreenTao.ArithmeticProgression.ShortIntervalLift
import Wikipedia.GreenTao.Primes.WTrick

/-!
# Extracting a prime progression from positive W-tricked mass

This module joins the elementary end of the proof.  Once transference gives
positive off-diagonal mass for the W-tricked prime weight, no further
analytic input is needed: positivity identifies prime-supported terms,
short support unwraps the cyclic progression, and the affine W-trick lifts
it to an ordinary progression of natural primes.
-/

namespace Wikipedia.SzemeredisTheorem

theorem containsAP_primes_of_wTricked_offDiagMass_pos
    {k N : ℕ} [NeZero N] (hk : 2 ≤ k)
    {α : ℝ} (hα : 0 < α)
    {W : ℕ} (hW : 0 < W) (b : ℕ)
    (hmass :
      0 <
        cyclicAPOffDiagMass k N
          (wTrickedPrimeWeight α W b)) :
    ContainsAP {p : ℕ | Nat.Prime p} k := by
  have hf :
      ∀ x : ZMod N, 0 ≤ wTrickedPrimeWeight α W b x :=
    wTrickedPrimeWeight_nonneg hα.le W b
  obtain ⟨a, d, hd, hpositive⟩ :=
    exists_cyclicAP_of_offDiagMass_pos hf hmass
  have hpreimage :
      ContainsAP
        {n : ℕ | Nat.Prime (W * n + b)} k := by
    apply containsAP_of_cyclicAPVal_shortInterval
      a d hd hk
      ((N / 64 : ℕ) : ℤ) ((N / 4 : ℕ) : ℤ)
    · intro j hj
      let jf : Fin k := ⟨j, hj⟩
      have hjpos := hpositive jf
      have hsupport :=
        (wTrickedPrimeWeight_pos_iff hα hW b
          (cyclicAPTerm a d jf)).mp hjpos
      have hb := mem_greenTaoInterval.mp hsupport.1
      have hbInt :
          ((N / 64 : ℕ) : ℤ) ≤
              ((cyclicAPTerm a d jf).val : ℤ) ∧
            ((cyclicAPTerm a d jf).val : ℤ) ≤
              ((N / 4 : ℕ) : ℤ) := by
        exact_mod_cast hb
      change
        ((N / 64 : ℕ) : ℤ) ≤ cyclicAPVal a d j ∧
          (cyclicAPVal a d j : ℤ) ≤ ((N / 4 : ℕ) : ℤ)
      simpa only [cyclicAPVal, cyclicAPTerm, jf] using hbInt
    · exact greenTaoInterval_twice_width_lt (NeZero.pos N)
    · intro j hj
      let jf : Fin k := ⟨j, hj⟩
      have hjpos := hpositive jf
      have hprime :=
        ((wTrickedPrimeWeight_pos_iff hα hW b
          (cyclicAPTerm a d jf)).mp hjpos).2
      simpa [wTrickedValue, cyclicAPVal, cyclicAPTerm, jf] using hprime
  exact hpreimage.affine hW

end Wikipedia.SzemeredisTheorem
