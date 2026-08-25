import Util.MaynardTao.BFT.ProgressionModulus
import BoundedGaps.Maynard.MaynardYTransform

/-! # Invariance of the divisor weights under a fixed progression modulus -/

namespace MaynardBFT

open BoundedGaps.Maynard

theorem isMaynardDivisorTuple_mul_primorial_iff
    {q D : ℕ} (hq : 0 < q) (hD : q ≤ D)
    (H : Finset ℕ) (R : ℕ) (d : H → ℕ) :
    IsMaynardDivisorTuple H R (q * primorial D) d ↔
      IsMaynardDivisorTuple H R (primorial D) d := by
  simp only [IsMaynardDivisorTuple, coprime_mul_primorial_iff hq hD]

theorem maynardDivisorTupleSupport_mul_primorial
    {q D : ℕ} (hq : 0 < q) (hD : q ≤ D)
    (H : Finset ℕ) (R : ℕ) :
    maynardDivisorTupleSupport H R (q * primorial D) =
      maynardDivisorTupleSupport H R (primorial D) := by
  ext d
  simp only [mem_maynardDivisorTupleSupport_iff,
    isMaynardDivisorTuple_mul_primorial_iff hq hD]

theorem maynardYValue_mul_primorial
    {q D : ℕ} (hq : 0 < q) (hD : q ≤ D)
    (H : Finset ℕ) (R : ℕ) (F : (H → ℝ) → ℝ) :
    maynardYValue H R (q * primorial D) F =
      maynardYValue H R (primorial D) F := by
  funext d
  simp only [maynardYValue, coprime_mul_primorial_iff hq hD]

theorem maynardCoefficient_mul_primorial
    {q D : ℕ} (hq : 0 < q) (hD : q ≤ D)
    (H : Finset ℕ) (R : ℕ) (F : (H → ℝ) → ℝ) :
    maynardCoefficient H R (q * primorial D) F =
      maynardCoefficient H R (primorial D) F := by
  funext d
  simp only [maynardCoefficient, coprime_mul_primorial_iff hq hD]

end MaynardBFT
