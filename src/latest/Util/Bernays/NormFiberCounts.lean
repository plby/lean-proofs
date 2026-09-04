import Util.Bernays.QuadraticClassBalls
import Util.Bernays.LatticeClassCounting
import Mathlib.Data.Set.Card

/-!
# Counting norm fibers and bounded ideal sets
-/

open scoped Classical

namespace Bernays

theorem natCard_bounded_eq_sum_fibers {X : Type*} (f : X → ℕ)
    (hf : ∀ x, 0 < f x) (N : ℕ) [Finite {x : X // f x ≤ N}] :
    Nat.card {x : X // f x ≤ N} =
      ∑ n ∈ Finset.Icc 1 N, Nat.card {x : X // f x = n} := by
  classical
  let S := {n : ℕ // n ∈ Finset.Icc 1 N}
  let : Fintype S := by dsimp only [S]; infer_instance
  let e : {x : X // f x ≤ N} ≃ Σ n : S, {x : X // f x = n.1} :=
    { toFun := fun x => ⟨⟨f x.1, Finset.mem_Icc.mpr ⟨hf x.1, x.2⟩⟩, ⟨x.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, x.2.2.le.trans (Finset.mem_Icc.mp x.1.2).2⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨n, hn⟩, ⟨x, hx⟩⟩
        change f x = n at hx
        subst n
        rfl }
  let (n : S) : Finite {x : X // f x = n.1} := by
    let g : {x : X // f x = n.1} → {x : X // f x ≤ N} :=
      fun x => ⟨x.1, x.2.le.trans (Finset.mem_Icc.mp n.2).2⟩
    exact Finite.of_injective g (fun x y h =>
      Subtype.ext (congrArg (fun t : {x : X // f x ≤ N} => t.1) h))
  rw [Nat.card_congr e, Nat.card_sigma]
  exact Finset.sum_coe_sort (Finset.Icc 1 N) (fun n => Nat.card {x : X // f x = n})

abbrev CoprimeIdealsInClass (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) (F : Ideal R) :=
  {I : InvertibleIdeal R // I.idealClass = C ∧ IsCoprime (I : Ideal R) F}

noncomputable def idealClassNormCount {R : Type*} [CommRing R] [IsDomain R]
    (C : ClassGroup R) (F : Ideal R) (n : ℕ) : ℕ :=
  Nat.card {I : CoprimeIdealsInClass R C F // (I.1 : Ideal R).cardQuot = n}

def boundedCoprimeClassEquiv {R : Type*} [CommRing R] [IsDomain R]
    (C : ClassGroup R) (F : Ideal R) (N : ℕ) :
    {I : CoprimeIdealsInClass R C F // (I.1 : Ideal R).cardQuot ≤ N} ≃
      RestrictedIdealClassBall R C N (fun J => IsCoprime (J : Ideal R) F) where
  toFun I := ⟨⟨I.1.1, I.1.2.1, I.2⟩, I.1.2.2⟩
  invFun I := ⟨⟨I.1.1, I.1.2.1, I.2⟩, I.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem idealClassNormCount_cumsum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (F : Ideal (QuadraticAlgebra ℤ d b)) (N : ℕ),
      (∑ n ∈ Finset.Icc 1 N, idealClassNormCount C F n) =
        Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
          (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) := by
  let := quadraticOrderIsDomain hD
  intro C F N
  let O := QuadraticAlgebra ℤ d b
  let := finite_idealClassBall hD C N
  let : Finite (RestrictedIdealClassBall O C N (fun J => IsCoprime (J : Ideal O) F)) := by
    dsimp only [RestrictedIdealClassBall]
    infer_instance
  let : Finite {I : CoprimeIdealsInClass O C F // (I.1 : Ideal O).cardQuot ≤ N} :=
    Finite.of_equiv _ (boundedCoprimeClassEquiv C F N).symm
  exact (natCard_bounded_eq_sum_fibers
    (fun I : CoprimeIdealsInClass O C F => (I.1 : Ideal O).cardQuot)
    (fun I => I.1.cardQuot_pos) N).symm.trans (Nat.card_congr (boundedCoprimeClassEquiv C F N))

end Bernays
