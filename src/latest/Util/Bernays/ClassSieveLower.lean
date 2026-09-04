import Util.Bernays.SieveLatticePoints
import Util.Bernays.LatticeClassCounting
import Util.Bernays.IdealGenerators

/-!
# A uniform lower sieve bound in every quadratic ideal class
-/

namespace Bernays

def ClassSievePredicate {d b : ℤ} [IsDomain (QuadraticAlgebra ℤ d b)]
    (M : ℕ) (S : Finset (SplitPrime d b)) (J : InvertibleIdeal (QuadraticAlgebra ℤ d b)) : Prop :=
  IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) (Ideal.span {(M : QuadraticAlgebra ℤ d b)}) ∧
    ∀ s ∈ S, ∀ ε : Bool, IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b))
      (rootIdeal d b s.1 (s.orientedRoot ε) (s.orientedRoot_sq ε))

def ClassSieveBall {d b : ℤ} [IsDomain (QuadraticAlgebra ℤ d b)]
    (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N M : ℕ) (S : Finset (SplitPrime d b)) :=
  RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N (ClassSievePredicate M S)

noncomputable def classSieveMultiplier {R : Type*} [CommRing R] [IsDomain R] (I : InvertibleIdeal R) (M : ℕ) : ℕ :=
  M * (I : Ideal R).cardQuot

def classSieveScale (d b : ℤ) (μ : ℕ) : ℕ :=
  (1 + b.natAbs + d.natAbs) * (2 * μ + 1) ^ 2

theorem affineBoxPoint_sub_mem_ideal {d b : ℤ} [IsDomain (QuadraticAlgebra ℤ d b)]
    (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (M Q L : ℕ)
    (c : (I : Ideal (QuadraticAlgebra ℤ d b))) (r : ZMod Q × ZMod Q) (i j : Fin L) :
    affineBoxPoint (c : QuadraticAlgebra ℤ d b) (classSieveMultiplier I M) Q L r i j - c ∈
      Ideal.span {(M : QuadraticAlgebra ℤ d b)} * (I : Ideal (QuadraticAlgebra ℤ d b)) := by
  have hm : ((I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot : QuadraticAlgebra ℤ d b) ∈
      (I : Ideal (QuadraticAlgebra ℤ d b)) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  rw [affineBoxPoint_sub_base, classSieveMultiplier, Nat.cast_mul, mul_assoc]
  exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
    ((I : Ideal (QuadraticAlgebra ℤ d b)).mul_mem_right _ hm)

theorem classSieve_lower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (I : InvertibleIdeal (QuadraticAlgebra ℤ d b)) (M : ℕ), 0 < M →
      ∀ c : (I : Ideal (QuadraticAlgebra ℤ d b)),
      (I : Ideal (QuadraticAlgebra ℤ d b)) = Ideal.span {(c : QuadraticAlgebra ℤ d b)} +
        Ideal.span {(M : QuadraticAlgebra ℤ d b)} * (I : Ideal (QuadraticAlgebra ℤ d b)) →
      ∀ S : Finset (SplitPrime d b),
      (∀ s ∈ S, ¬s.1 ∣ classSieveMultiplier I M) →
      ∀ L : ℕ, (c : QuadraticAlgebra ℤ d b).re.natAbs < L →
        (c : QuadraticAlgebra ℤ d b).im.natAbs < L →
        (∏ s ∈ S, (s.1 - 1) ^ 2) * L ^ 2 ≤ Nat.card (QuadraticAlgebra ℤ d b)ˣ *
          Nat.card (ClassSieveBall I.idealClass⁻¹
            (classSieveScale d b (classSieveMultiplier I M) * (splitSieveModulus S) ^ 2 * L ^ 2) M S) := by
  let := quadraticOrderIsDomain hD
  intro I M hM c hc S hS L hrL hiL
  let O := QuadraticAlgebra ℤ d b
  let μ := classSieveMultiplier I M
  let Q := splitSieveModulus S
  let N := classSieveScale d b μ * Q ^ 2 * L ^ 2
  have hμ : 0 < μ := Nat.mul_pos hM I.cardQuot_pos
  have hQ : 0 < Q := splitSieveModulus_pos S
  let : NeZero Q := ⟨hQ.ne'⟩
  let X := AffineAllowedResiduePairs S (c : O) (μ : ℤ) × Fin L × Fin L
  let : Finite X := by
    dsimp only [X, AffineAllowedResiduePairs]
    infer_instance
  let z : X → O := fun x => affineBoxPoint (c : O) μ Q L x.1.1 x.2.1 x.2.2
  have hcoord : Function.Injective (fun x : X => (x.1.1, x.2)) := by
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (congrArg (fun t : (ZMod Q × ZMod Q) × (Fin L × Fin L) => t.2) h)
  have hz : Function.Injective z := (affineBoxPoint_injective (c : O) hμ hQ).comp hcoord
  have hz₀ (x : X) : z x ≠ 0 := affineBoxPoint_ne_zero (c : O) hμ hQ hrL _ _ _
  have hdiff (x : X) : z x - c ∈ Ideal.span {(M : O)} * (I : Ideal O) :=
    affineBoxPoint_sub_mem_ideal I M Q L c x.1.1 x.2.1 x.2.2
  have hzI (x : X) : z x ∈ (I : Ideal O) := by
    have h := (I : Ideal O).add_mem (Ideal.mul_le_right (hdiff x)) c.2
    simpa only [sub_add_cancel] using h
  have hzN (x : X) : (z x).norm.natAbs ≤ N :=
    affineBoxPoint_norm_le (c : O) hQ hrL hiL x.1.1 x.2.1 x.2.2
  have hA (x : X) (J : InvertibleIdeal O) (hIJ : (I : Ideal O) * J = Ideal.span {z x}) :
      ClassSievePredicate M S J := by
    constructor
    · exact InvertibleIdeal.factor_coprime_of_generator_mod I J (Ideal.span {(M : O)})
        (hz₀ x) (InvertibleIdeal.ext hIJ)
        (InvertibleIdeal.generator_mod_of_sub_mem I _ c hc (hdiff x))
    · intro s hs ε
      exact factor_isCoprime_of_generator_not_mem (I : Ideal O) (J : Ideal O)
        (s.ideal hD ε : Ideal O) (s.ideal_isMaximal hD ε) hIJ
        (affineBoxPoint_not_mem_splitPrime hD S (c : O) μ L x.1 x.2.1 x.2.2 ⟨s, hs⟩ ε)
  have hcount := lattice_family_class_count hD I N (ClassSievePredicate M S) z hz hz₀ hzI hzN hA
  have hμmod : ∀ s ∈ S, ((μ : ℤ) : ZMod s.1) ≠ 0 := by
    intro s hs
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff μ s.1).not.mpr (hS s hs)
  have hcard : Nat.card X = (∏ s ∈ S, (s.1 - 1) ^ 2) * L ^ 2 := by
    rw [show X = (AffineAllowedResiduePairs S (c : O) (μ : ℤ) × Fin L × Fin L) from rfl,
      Nat.card_prod, Nat.card_prod, Nat.card_fin, natCard_affineAllowedResiduePairs S (c : O) (μ : ℤ) hμmod]
    ring
  rw [hcard] at hcount
  exact hcount

end Bernays
