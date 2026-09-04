import Util.Bernays.SplitResidues
import Util.Bernays.AffineLatticeBox

/-!
# The residue-constrained lattice points avoid both primes above each selected prime
-/

namespace Bernays

theorem quadraticEval_affineBoxPoint {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    (μ Q L q : ℕ) (r : ZMod Q × ZMod Q) (i j : Fin L)
    (s : ZMod q) (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hq : q ∣ Q) :
    quadraticEval d b q s hs (affineBoxPoint c μ Q L r i j) =
      (c.re : ZMod q) + (μ : ZMod q) * (r.1.val : ZMod q) +
        ((c.im : ZMod q) + (μ : ZMod q) * (r.2.val : ZMod q)) * s := by
  have hQ : (Q : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff Q q).mpr hq
  simp [quadraticEval, affineBoxPoint, hQ]

theorem affineBoxPoint_not_mem_splitPrime {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (S : Finset (SplitPrime d b)) (c : QuadraticAlgebra ℤ d b) (μ L : ℕ)
    (r : AffineAllowedResiduePairs S c (μ : ℤ)) (i j : Fin L) (s : {s // s ∈ S}) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    affineBoxPoint c μ (splitSieveModulus S) L r.1 i j ∉
      (s.1.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)) := by
  let := quadraticOrderIsDomain hD
  have hdiv : s.1.1 ∣ splitSieveModulus S := Finset.dvd_prod_of_mem (fun s => s.1) s.2
  change quadraticEval d b s.1.1 (s.1.orientedRoot ε) (s.1.orientedRoot_sq ε)
    (affineBoxPoint c μ (splitSieveModulus S) L r.1 i j) ≠ 0
  rw [quadraticEval_affineBoxPoint _ _ _ _ _ _ _ _ _ _ hdiv]
  cases ε
  · simpa only [SplitPrime.orientedRoot, Bool.false_eq_true, if_false,
      splitResiduePairEquivPi_apply, Int.cast_natCast] using (r.2 s).1
  · simpa only [SplitPrime.orientedRoot, if_true,
      splitResiduePairEquivPi_apply, Int.cast_natCast] using (r.2 s).2

theorem factor_isCoprime_of_generator_not_mem {R : Type*} [CommRing R]
    (I J P : Ideal R) (hP : P.IsMaximal) {x : R}
    (hIJ : I * J = Ideal.span {x}) (hx : x ∉ P) : IsCoprime J P := by
  have hJnot : ¬ J ≤ P := by
    intro h
    apply hx
    have hmem : x ∈ I * J := by rw [hIJ]; exact Ideal.mem_span_singleton_self x
    exact h (Ideal.mul_le_right hmem)
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  exact hJnot (le_sup_left.trans_eq (hP.eq_of_le htop le_sup_right).symm)

end Bernays
