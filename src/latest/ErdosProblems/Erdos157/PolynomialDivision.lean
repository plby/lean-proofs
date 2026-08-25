import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-! Generic long-division coordinates, shared by the character argument. -/

namespace Erdos157.PolynomialDivision

variable (K : Type*) [Field K]

/-- Reconstruct a monic degree-`n` polynomial from its remainder modulo a
monic degree-`m` polynomial and a monic quotient of degree `n-m`. -/
noncomputable def monicDegreeEqOfRemainderQuotient
    {m n : ℕ} (g r : Polynomial K) (hg : g.Monic)
    (hgdeg : g.natDegree = m) (hrdeg : r.degree < (m : WithBot ℕ))
    (hmn : m ≤ n) (H : Polynomial.MonicDegreeEq K (n - m)) :
    Polynomial.MonicDegreeEq K n := by
  have hp : (g * H.1).Monic := hg.mul H.monic
  have hprodNat : (g * H.1).natDegree = n := by
    rw [hg.natDegree_mul H.monic, hgdeg, H.natDegree]
    omega
  have hprodDegree : (g * H.1).degree = ((n : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hprodNat]
  have hrlt : r.degree < (g * H.1).degree := by
    rw [hprodDegree]
    exact hrdeg.trans_le (WithBot.coe_le_coe.mpr hmn)
  have hdegree : (r + g * H.1).degree = ((n : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_add_eq_right_of_degree_lt hrlt, hprodDegree]
  have hnat : (r + g * H.1).natDegree = n :=
    Polynomial.natDegree_eq_of_degree_eq_some hdegree
  apply Polynomial.MonicDegreeEq.mk (r + g * H.1) _ hnat
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hnat,
    Polynomial.coeff_add,
    Polynomial.coeff_eq_zero_of_degree_lt (hrlt.trans_eq hprodDegree),
    zero_add]
  change (g * H.1).coeff n = 1
  simpa only [hprodNat] using hp.coeff_natDegree

theorem monicDegreeEqOfRemainderQuotient_modByMonic
    {m n : ℕ} (g r : Polynomial K) (hg : g.Monic)
    (hgdeg : g.natDegree = m) (hrdeg : r.degree < (m : WithBot ℕ))
    (hmn : m ≤ n) (H : Polynomial.MonicDegreeEq K (n - m)) :
    (monicDegreeEqOfRemainderQuotient K g r hg hgdeg hrdeg hmn H).1 %ₘ g = r := by
  rw [show
    (monicDegreeEqOfRemainderQuotient K g r hg hgdeg hrdeg hmn H).1 =
      r + g * H.1 by rfl]
  rw [Polynomial.add_modByMonic]
  rw [(Polynomial.modByMonic_eq_self_iff hg).2 (by
    rw [Polynomial.degree_eq_natDegree hg.ne_zero, hgdeg]
    exact hrdeg)]
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd hg).2 (dvd_mul_right g H.1)]
  simp

theorem monicDegreeEqOfRemainderQuotient_divByMonic
    {m n : ℕ} (g r : Polynomial K) (hg : g.Monic)
    (hgdeg : g.natDegree = m) (hrdeg : r.degree < (m : WithBot ℕ))
    (hmn : m ≤ n) (H : Polynomial.MonicDegreeEq K (n - m)) :
    (monicDegreeEqOfRemainderQuotient K g r hg hgdeg hrdeg hmn H).1 /ₘ g = H.1 := by
  exact (Polynomial.div_modByMonic_unique H.1 r hg ⟨rfl, by
    rw [Polynomial.degree_eq_natDegree hg.ne_zero, hgdeg]
    exact hrdeg⟩).1

/-- Euclidean division gives the free monic quotient coordinate. -/
noncomputable def monicQuotientOfDegree
    {m n : ℕ} (g : Polynomial K) (hg : g.Monic)
    (hgdeg : g.natDegree = m) (hmn : m ≤ n)
    (F : Polynomial.MonicDegreeEq K n) :
    Polynomial.MonicDegreeEq K (n - m) := by
  have hdegree : g.degree ≤ F.1.degree := by
    rw [Polynomial.degree_eq_natDegree hg.ne_zero,
      Polynomial.degree_eq_natDegree F.monic.ne_zero, hgdeg, F.natDegree]
    exact WithBot.coe_le_coe.mpr hmn
  apply Polynomial.MonicDegreeEq.mk (F.1 /ₘ g)
  · rw [Polynomial.Monic.def,
      Polynomial.leadingCoeff_divByMonic_of_monic hg hdegree]
    exact F.monic.leadingCoeff
  · rw [Polynomial.natDegree_divByMonic F.1 hg,
      F.natDegree, hgdeg]

theorem monicDegreeEq_reconstruct
    {m n : ℕ} (g : Polynomial K) (hg : g.Monic)
    (hgdeg : g.natDegree = m) (hmn : m ≤ n)
    (F : Polynomial.MonicDegreeEq K n) :
    monicDegreeEqOfRemainderQuotient K g (F.1 %ₘ g) hg hgdeg
        (by
          have hd := Polynomial.degree_modByMonic_lt F.1 hg
          rw [Polynomial.degree_eq_natDegree hg.ne_zero, hgdeg] at hd
          exact hd) hmn
        (monicQuotientOfDegree K g hg hgdeg hmn F) = F := by
  apply Subtype.ext
  exact Polynomial.modByMonic_add_div F.1 g

/-- Long division gives product coordinates: a monic polynomial of degree `n` is exactly its degree-`<m`
remainder and a monic quotient of degree `n-m`. -/
noncomputable def monicRemainderQuotientEquiv
    {m n : ℕ} (g : Polynomial K) (hg : g.Monic)
    (hgdeg : g.natDegree = m) (hmn : m ≤ n) :
    Polynomial.MonicDegreeEq K n ≃
      {r : Polynomial K // r.degree < (m : WithBot ℕ)} ×
        Polynomial.MonicDegreeEq K (n - m) where
  toFun F :=
    (⟨F.1 %ₘ g, by
      have hd := Polynomial.degree_modByMonic_lt F.1 hg
      rw [Polynomial.degree_eq_natDegree hg.ne_zero, hgdeg] at hd
      exact hd⟩,
      monicQuotientOfDegree K g hg hgdeg hmn F)
  invFun x :=
    monicDegreeEqOfRemainderQuotient K g x.1.1 hg hgdeg x.1.2 hmn x.2
  left_inv F := monicDegreeEq_reconstruct K g hg hgdeg hmn F
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      exact monicDegreeEqOfRemainderQuotient_modByMonic K
        g x.1.1 hg hgdeg x.1.2 hmn x.2
    · exact Subtype.ext (monicDegreeEqOfRemainderQuotient_divByMonic K
        g x.1.1 hg hgdeg x.1.2 hmn x.2)

end Erdos157.PolynomialDivision
