import Util.Bernays.ClassSieveLower
import Util.Bernays.ClassPrimeFactors
import Util.Bernays.DivisibleClassBalls

/-!
# Upper sieve bounds from prime-ideal divisors
-/

namespace Bernays

theorem natCard_classSieveBall_le_sum_divisible {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N M : ℕ)
      (S T : Finset (SplitPrime d b)),
      (∀ I : ClassSieveBall C N M S, ∃ s ∈ T, ∃ ε : Bool,
        (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) ≤ (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b))) →
      Nat.card (ClassSieveBall C N M S) ≤
        ∑ s ∈ T, ∑ ε : Bool,
          Nat.card (DivisibleIdealClassBall (QuadraticAlgebra ℤ d b) C N (s.ideal hD ε)) := by
  classical
  let := quadraticOrderIsDomain hD
  intro C N M S T hcover
  let O := QuadraticAlgebra ℤ d b
  choose s hs ε hle using hcover
  let Y := Σ t : {s // s ∈ T}, Σ e : Bool, DivisibleIdealClassBall O C N (t.1.ideal hD e)
  let f : ClassSieveBall C N M S → Y := fun I => ⟨⟨s I, hs I⟩, ε I, ⟨I.1, hle I⟩⟩
  have hf : Function.Injective f := by
    intro I J h
    exact Subtype.ext (congrArg (fun y : Y => y.2.2.1) h)
  let := finite_idealClassBall hD C N
  let (t : {s // s ∈ T}) (e : Bool) :
      Finite (DivisibleIdealClassBall O C N (t.1.ideal hD e)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card (ClassSieveBall C N M S) ≤ Nat.card Y := Nat.card_le_card_of_injective f hf
    _ = ∑ t : {s // s ∈ T}, ∑ e : Bool,
        Nat.card (DivisibleIdealClassBall O C N (t.1.ideal hD e)) := by
      dsimp only [Y]
      rw [Nat.card_sigma]
      exact Finset.sum_congr rfl (fun _ _ => Nat.card_sigma)
    _ = _ := by
      simpa only [Finset.attach_eq_univ] using T.sum_attach
        (fun s => ∑ e : Bool, Nat.card (DivisibleIdealClassBall O C N (s.ideal hD e)))

theorem classSieve_upper_of_cover {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ B : ℕ,
      (∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∀ N : ℕ,
        Nat.card (IdealClassBall (QuadraticAlgebra ℤ d b) C N) ≤ B * N) →
      ∀ (C : ClassGroup (QuadraticAlgebra ℤ d b)) (N M : ℕ) (S T : Finset (SplitPrime d b)),
      (∀ I : ClassSieveBall C N M S, ∃ s ∈ T, ∃ ε : Bool,
        (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) ≤ (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b))) →
      (Nat.card (ClassSieveBall C N M S) : ℝ) ≤
        2 * (B : ℝ) * N * ∑ s ∈ T, (s.1 : ℝ)⁻¹ := by
  let := quadraticOrderIsDomain hD
  intro B hB C N M S T hcover
  have hdiv (s : SplitPrime d b) (ε : Bool) :
      Nat.card (DivisibleIdealClassBall (QuadraticAlgebra ℤ d b) C N (s.ideal hD ε)) ≤
        B * (N / s.1) := by
    simpa only [s.ideal_cardQuot hD ε] using
      natCard_divisibleIdealClassBall_le hD B hB C N (s.ideal hD ε)
  have hnat := (natCard_classSieveBall_le_sum_divisible hD C N M S T hcover).trans
    (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun ε _ => hdiv s ε)
  have hreal : (Nat.card (ClassSieveBall C N M S) : ℝ) ≤
      ∑ s ∈ T, ∑ _ : Bool, ((B * (N / s.1) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hterm (s : SplitPrime d b) : ((B * (N / s.1) : ℕ) : ℝ) ≤
      (B : ℝ) * N * (s.1 : ℝ)⁻¹ := by
    rw [Nat.cast_mul, mul_assoc, ← div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left Nat.cast_div_le (Nat.cast_nonneg B)
  calc
    _ ≤ ∑ s ∈ T, ∑ _ : Bool, ((B : ℝ) * N * (s.1 : ℝ)⁻¹) :=
      hreal.trans (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun _ _ => hterm s)
    _ = _ := by
      simp only [Fintype.sum_bool]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem SplitPrime.natCast_mem_ideal {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    (s.1 : QuadraticAlgebra ℤ d b) ∈ (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)) := by
  let := quadraticOrderIsDomain hD
  change quadraticEval d b s.1 (s.orientedRoot ε) (s.orientedRoot_sq ε) (s.1 : _) = 0
  rw [map_natCast]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_refl _)

theorem not_dvd_scalar_of_coprime_le {R : Type*} [CommRing R]
    (I P : Ideal R) (hP : P.IsMaximal) (M q : ℕ)
    (hc : IsCoprime I (Ideal.span {(M : R)})) (hIP : I ≤ P) (hq : (q : R) ∈ P) :
    ¬ q ∣ M := by
  rintro ⟨k, hk⟩
  have hMP : Ideal.span {(M : R)} ≤ P := by
    apply (Ideal.span_singleton_le_iff_mem P).mpr
    rw [hk, Nat.cast_mul]
    exact P.mul_mem_right _ hq
  apply hP.ne_top
  apply top_unique
  rw [← hc.sup_eq]
  exact sup_le hIP hMP

theorem coprime_scalar_of_dvd {R : Type*} [CommRing R] (I : Ideal R) {M K : ℕ}
    (h : IsCoprime I (Ideal.span {(M : R)})) (hKM : K ∣ M) :
    IsCoprime I (Ideal.span {(K : R)}) := by
  rcases hKM with ⟨k, hk⟩
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  rw [← h.sup_eq]
  apply sup_le_sup_left
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  rw [hk, Nat.cast_mul]
  exact (Ideal.span {(K : R)}).mul_mem_right _ (Ideal.mem_span_singleton_self _)

noncomputable def boundedSplitPrimes (d b : ℤ) (N : ℕ) : Finset (SplitPrime d b) := by
  classical
  let e : {s : SplitPrime d b // s.1 ≤ N} ↪ Fin (N + 1) :=
    ⟨fun s => ⟨s.1.1, Nat.lt_succ_of_le s.2⟩, fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg Fin.val h))⟩
  letI : Finite {s : SplitPrime d b // s.1 ≤ N} := Finite.of_injective e e.injective
  letI : Fintype {s : SplitPrime d b // s.1 ≤ N} := Fintype.ofFinite _
  exact Finset.univ.image (fun s : {s : SplitPrime d b // s.1 ≤ N} => s.1)

theorem mem_boundedSplitPrimes {d b : ℤ} {N : ℕ} (s : SplitPrime d b) :
    s ∈ boundedSplitPrimes d b N ↔ s.1 ≤ N := by
  classical
  unfold boundedSplitPrimes
  simp

theorem classSieve_cover {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ (H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)))
      (C : ClassGroup (QuadraticAlgebra ℤ d b)), C ∉ H →
      ∀ N M μ : ℕ, discriminantLevel (b ^ 2 + 4 * d) ∣ M →
      (∀ q : ℕ, q.Prime → q ∣ μ → q ∣ M) →
      ∀ S : Finset (SplitPrime d b), ∀ I : ClassSieveBall C N M S,
      ∃ s : SplitPrime d b, s.1 ≤ N ∧ s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ ∧ s ∉ S ∧
        ∃ ε : Bool, (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) ≤
          (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)) := by
  let := quadraticOrderIsDomain hD
  intro H C hC N M μ hDM hμ S I
  have hIF : IsCoprime (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) :=
    coprime_scalar_of_dvd _ I.2.1 hDM
  obtain ⟨s, hsH, hsn, ε, J, hIJ⟩ := exists_splitPrime_factor_outside hD H I.1.1 hIF
    (by simpa only [I.1.2.1] using hC)
  have hle : (I.1.1 : Ideal (QuadraticAlgebra ℤ d b)) ≤
      (s.ideal hD ε : Ideal (QuadraticAlgebra ℤ d b)) := by
    rw [← hIJ, InvertibleIdeal.coe_mul]
    exact Ideal.mul_le_left
  have hsM := not_dvd_scalar_of_coprime_le _ _ (s.ideal_isMaximal hD ε) M s.1
    I.2.1 hle (s.natCast_mem_ideal hD ε)
  refine ⟨s, hsn.trans I.1.2.2, hsH, fun h => hsM (hμ _ s.2.1 h), ?_, ε, hle⟩
  intro hsS
  have hcop := I.2.2 s hsS ε
  apply (s.ideal_isMaximal hD ε).ne_top
  exact (sup_eq_right.mpr hle).symm.trans hcop.sup_eq

end Bernays
