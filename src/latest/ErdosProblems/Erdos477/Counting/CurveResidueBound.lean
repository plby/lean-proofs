/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A uniform bound for the number of curve points in one smooth residue class.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveAuxiliary
import ErdosProblems.Erdos477.Geometry.IntegerPlaneBezout

namespace Erdos477.Counting

variable {K : Type*} [Field K] [CharZero K]

/-- A smooth class modulo `q >= B^(1/d+ε)` contains only a bounded number
of integer points. All auxiliary construction and intersection inputs are proved. -/
theorem card_curve_residue_class_le (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1))
    (B : ℝ) (hB : 1 ≤ B) (hlarge : 2 * Real.log (d * n : ℕ) < Real.log B)
    (q : ℕ) (hq : 0 < q) (hqB : (1 / (d : ℝ) + ε) * Real.log B ≤ Real.log q)
    (P : MvPolynomial (Fin 2) ℤ) (hPdegree : P.degreeOf 0 = d)
    (hP : Irreducible (MvPolynomial.map (Int.castRingHom K) P))
    (a : Fin 2 → ℤ) (S : Finset (Fin 2 → ℤ))
    (hcop : IsCoprime (q : ℤ) (MvPolynomial.eval a (MvPolynomial.pderiv 0 P)))
    (hroot : ∀ z ∈ S, MvPolynomial.eval z P = 0)
    (hclass : ∀ z ∈ S, ∀ k, (q : ℤ) ∣ z k - a k)
    (hheight : ∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) :
    S.card ≤ P.totalDegree * (d + n - 2) := by
  obtain ⟨Q, hQ, hQdeg, hQtotal, _, hzero⟩ := exists_curve_auxiliary_of_congruence
    d n hd hn ε hε hεn B hB hlarge q hq hqB P hPdegree a S hcop hroot hclass hheight
  exact (Geometry.card_integer_plane_common_zeroes_le_of_degreeOf (K := K) d hd P Q
    hP hPdegree hQ hQdeg S (fun z hz => ⟨hroot z hz, hzero z hz⟩)).trans
      (Nat.mul_le_mul_left _ hQtotal)

#print axioms card_curve_residue_class_le
-- 'Erdos477.Counting.card_curve_residue_class_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
