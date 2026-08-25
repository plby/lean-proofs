import Util.Bernays.GoodIdealGeneratorBall

/-!
# Decomposing coprime generators into lattice cosets
-/

open scoped Classical

namespace Bernays

theorem coprimeQuadraticBall_eq_sum_cosets {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I F : Ideal (QuadraticAlgebra ℤ d b)) (hIF : IsCoprime I F)
    [Fintype (QuadraticAlgebra ℤ d b ⧸ F)ˣ]
    (c : (QuadraticAlgebra ℤ d b ⧸ F)ˣ → I)
    (hc : ∀ u, Ideal.Quotient.mk F (c u : QuadraticAlgebra ℤ d b) = u) (T : ℕ) :
    Nat.card (CoprimeQuadraticBall I F T) =
      ∑ u : (QuadraticAlgebra ℤ d b ⧸ F)ˣ,
        Nat.card (quadraticIdealCosetBall (F * I) (c u) T) := by
  let O := QuadraticAlgebra ℤ d b
  let X := Σ u : (O ⧸ F)ˣ, quadraticIdealCosetBall (F * I) (c u) T
  let Y := CoprimeQuadraticBall I F T
  have hmem (u : (O ⧸ F)ˣ) (w : quadraticIdealCosetBall (F * I) (c u) T) :
      (c u : O) + (w.1 : O) ∈ I := I.add_mem (c u).2 (Ideal.mul_le_right w.1.2)
  have hres (u : (O ⧸ F)ˣ) (w : quadraticIdealCosetBall (F * I) (c u) T) :
      Ideal.Quotient.mk F ((c u : O) + (w.1 : O)) = u := by
    rw [map_add, hc, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_left w.1.2), add_zero]
  let f : X → Y := fun x => ⟨(c x.1 : O) + (x.2.1 : O), hmem x.1 x.2,
    x.2.2, (hres x.1 x.2).symm ▸ x.1.isUnit⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, x⟩ ⟨v, y⟩ hxy
      have hval : (c u : O) + (x.1 : O) = (c v : O) + (y.1 : O) :=
        congrArg (fun t : Y => t.1) hxy
      have huv : u = v := by
        apply Units.ext
        have hq := congrArg (Ideal.Quotient.mk F) hval
        rwa [hres u x, hres v y] at hq
      subst v
      have hxy' : x = y := Subtype.ext (Subtype.ext (add_left_cancel hval))
      subst y
      rfl
    · intro y
      let u : (O ⧸ F)ˣ := y.2.2.2.unit
      have hu : Ideal.Quotient.mk F y.1 = u := y.2.2.2.unit_spec.symm
      have hdiff : y.1 - (c u : O) ∈ F * I :=
        (quotient_eq_iff_sub_mem_product I F hIF ⟨y.1, y.2.1⟩ (c u)).mp (hu.trans (hc u).symm)
      have hsum : (c u : O) + (y.1 - (c u : O)) = y.1 := by abel
      let w : quadraticIdealCosetBall (F * I) (c u) T :=
        ⟨⟨y.1 - (c u : O), hdiff⟩, by
          change ((c u : O) + (y.1 - (c u : O))).norm.natAbs ≤ T
          rw [hsum]
          exact y.2.2.1⟩
      refine ⟨⟨u, w⟩, ?_⟩
      apply Subtype.ext
      change (c u : O) + (y.1 - (c u : O)) = y.1
      abel
  letI (u : (O ⧸ F)ˣ) : Finite (quadraticIdealCosetBall (F * I) (c u) T) :=
    finite_quadraticIdealCosetBall hD (F * I) (c u) T
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sigma]

end Bernays
