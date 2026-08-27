import Arxiv.Arxiv2411_18291.RationalIncidence

/-!
# Degree divisibility on `q+r` vertices

The first assertion of Remark `rem:div` in arXiv:2411.18291: the usual local
degree-divisibility conditions characterize the integer image of the
clique-to-edge incidence operator on `q+r` vertices. `GlobalDivisibility`
extends this to every ambient size `n ≥ q+r` by induction.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

/-- The standard divisibility conditions, including all subset sizes `0 ≤ i ≤ r`. -/
def DegreeDivisible (q : ℕ) (J : Block V r → ℤ) : Prop :=
  ∀ I : Finset V, I.card ≤ r →
    ((q - I.card).choose (r - I.card) : ℤ) ∣ degree J I

theorem IntegrallyDecomposable.degreeDivisible {J : Block V r → ℤ}
    (h : IntegrallyDecomposable q J) : DegreeDivisible q J := h.degree_dvd

/-- On `q+r` vertices, degree divisibility makes every coefficient of the
rational solution integral, by inclusion–exclusion. -/
theorem integrallyDecomposable_of_degreeDivisible (hn : Fintype.card V = q + r)
    (hqr : r ≤ q) {J : Block V r → ℤ} (hdiv : DegreeDivisible q J) :
    IntegrallyDecomposable q J := by
  obtain ⟨Φ, hΦ⟩ := boundary_surjective_rat hn hqr (fun e => (J e : ℚ))
  have hdeg (I : Finset V) (hIr : I.card ≤ r) : ∃ z : ℤ, degree Φ I = (z : ℚ) := by
    obtain ⟨z, hz⟩ := hdiv I hIr
    have h := degree_boundary Φ I hIr
    rw [hΦ] at h
    have hm := degree_map (Int.castAddHom ℚ) J I
    simp only [Int.coe_castAddHom] at hm
    rw [hm, hz] at h
    push_cast at h
    have hpos : 0 < (q - I.card).choose (r - I.card) :=
      Nat.choose_pos (Nat.sub_le_sub_right hqr I.card)
    have hc : ((q - I.card).choose (r - I.card) : ℚ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact ⟨z, mul_left_cancel₀ hc h.symm⟩
  let z (I : Finset V) : ℤ :=
    if hI : I.card ≤ r then Classical.choose (hdeg I hI) else 0
  have hz (I : Finset V) (hI : I.card ≤ r) : degree Φ I = (z I : ℚ) := by
    simp only [z, dif_pos hI]
    exact Classical.choose_spec (hdeg I hI)
  let Ψ (Q : Block V q) : ℤ :=
    ∑ I ∈ Q.valᶜ.powerset, (-1 : ℤ) ^ I.card * z I
  have hΨ (Q : Block V q) : (Ψ Q : ℚ) = Φ Q := by
    dsimp only [Ψ]
    rw [← coefficient_from_degrees Φ Q]
    push_cast
    apply sum_congr rfl
    intro I hI
    have hcard : Q.valᶜ.card = r := by
      rw [card_compl, hn, Q.property]
      omega
    rw [hz I (by simpa only [hcard] using card_le_card (mem_powerset.mp hI))]
  refine ⟨Ψ, ?_⟩
  have hm := boundary_map (r := r) (Int.castAddHom ℚ) Ψ
  simp only [Int.coe_castAddHom] at hm
  have hΨfun : (fun Q => (Ψ Q : ℚ)) = Φ := funext hΨ
  rw [hΨfun, hΦ] at hm
  funext e
  exact_mod_cast (congrFun hm e).symm

/-- The local degree-divisibility criterion of Remark `rem:div`. -/
theorem integrallyDecomposable_iff_degreeDivisible (hn : Fintype.card V = q + r)
    (hqr : r ≤ q) (J : Block V r → ℤ) :
    IntegrallyDecomposable q J ↔ DegreeDivisible q J :=
  ⟨IntegrallyDecomposable.degreeDivisible,
    integrallyDecomposable_of_degreeDivisible hn hqr⟩

end Arxiv2411_18291
