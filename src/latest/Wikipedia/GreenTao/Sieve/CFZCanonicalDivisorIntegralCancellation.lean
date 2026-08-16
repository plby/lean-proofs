import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorRankinTruncation

/-!
# Full-space cancellation of the canonical divisor truncation error

Fourier inversion sees the unrestricted primewise divisor expansion as a
finite sum over squarefree paired divisor families.  Terms whose left or
right divisor has crossed the coordinatewise cutoff have zero full-space
integral, because the smooth cutoff is supported in `(-∞, 1)`.  Thus the
unrestricted integral is exactly the coordinatewise-truncated integral.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

theorem divisorMultiplicativePhase_finsetProd
    {α : Type*} [DecidableEq α]
    (R : ℕ) (s : Finset α) (d : α → ℕ)
    (hd : ∀ a ∈ s, 0 < d a) (t : ℝ) :
    divisorMultiplicativePhase R (∏ a ∈ s, d a) t =
      ∏ a ∈ s, divisorMultiplicativePhase R (d a) t := by
  induction s using Finset.induction_on with
  | empty =>
      simp [divisorMultiplicativePhase, cutoffMultiplicativePhase]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [divisorMultiplicativePhase_mul]
      · rw [ih]
        intro b hb
        exact hd b (Finset.mem_insert_of_mem hb)
      · exact hd a (Finset.mem_insert_self a s)
      · exact Finset.prod_pos fun b hb =>
          hd b (Finset.mem_insert_of_mem hb)

theorem moebius_finsetProd_primes
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℕ)
    (hp : ∀ a ∈ s, (p a).Prime)
    (hinj : Set.InjOn p s) :
    (ArithmeticFunction.moebius (∏ a ∈ s, p a) : ℂ) =
      (-1 : ℂ) ^ s.card := by
  have hsquare :
      Squarefree (∏ a ∈ s, p a) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro a ha b hb hab
      change IsRelPrime (p a) (p b)
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hp a ha) (hp b hb)).mpr
        (fun hpab => hab (hinj ha hb hpab))
    · intro a ha
      exact (hp a ha).squarefree
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsquare]
  push_cast
  congr 1
  have hprod :
      ArithmeticFunction.cardFactors (∏ a ∈ s, p a) =
        ∑ a ∈ s, ArithmeticFunction.cardFactors (p a) := by
    simpa using
      ArithmeticFunction.cardFactors_multiset_prod
        (s := s.1.map p)
        (by
          rw [show (s.1.map p).prod = ∏ a ∈ s, p a by simp]
          exact Finset.prod_ne_zero_iff.mpr fun a ha =>
            (hp a ha).ne_zero)
  rw [hprod]
  calc
    (∑ a ∈ s, ArithmeticFunction.cardFactors (p a)) =
        ∑ _a ∈ s, 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact ArithmeticFunction.cardFactors_apply_prime (hp a ha)
    _ = s.card := by simp

end SmoothSieveCutoff

/-! ## The three paired states at every active prime/form incidence -/

/-- For every incidence `q ∈ support p`, choose whether `p` occurs in the
left divisor, the right divisor, or both. -/
abbrev FixedFamilyPairedPrimeStateAssignment
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :=
  (p : {p // p ∈ P}) →
    ({q // q ∈ support p} → Fin 3)

/-- The phase contributed by one of the three nonempty paired states. -/
noncomputable def pairedFourierPrimeStateTerm
    (R p : ℕ) (t u : ℝ) (state : Fin 3) : ℂ :=
  if state = 0 then
    -SmoothSieveCutoff.divisorMultiplicativePhase R p t
  else if state = 1 then
    -SmoothSieveCutoff.divisorMultiplicativePhase R p u
  else
    SmoothSieveCutoff.divisorMultiplicativePhase R p t *
      SmoothSieveCutoff.divisorMultiplicativePhase R p u

theorem sum_pairedFourierPrimeStateTerm
    (R p : ℕ) (t u : ℝ) :
    (∑ state : Fin 3,
        pairedFourierPrimeStateTerm R p t u state) =
      -pairedFourierPrimeCoefficient R p t u := by
  rw [Fin.sum_univ_three]
  simp [pairedFourierPrimeStateTerm,
    pairedFourierPrimeCoefficient]
  ring

/-- Product of all state phases belonging to one assignment. -/
noncomputable def fixedFamilyPairedPrimeStateTerm
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) : ℂ :=
  ∏ p : {p // p ∈ P},
    ∏ q : {q // q ∈ support p},
      pairedFourierPrimeStateTerm
        R (p : ℕ) (t q) (u q) (A p q)

/-- One local collapsed coefficient is the sum of its three-state
refinements. -/
theorem fixedFamilyPrimeLocalCoefficient_eq_sum_states
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (t u : κ → ℝ)
    (p : Nat.Primes) (s : Finset κ) :
    fixedFamilyPrimeLocalCoefficient R t u p s =
      ∑ A : ({q // q ∈ s} → Fin 3),
        ∏ q : {q // q ∈ s},
          pairedFourierPrimeStateTerm
            R (p : ℕ) (t q) (u q) (A q) := by
  classical
  unfold fixedFamilyPrimeLocalCoefficient
  calc
    (-1 : ℂ) ^ s.card *
          ∏ q ∈ s,
            pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q) =
        ∏ q ∈ s,
          -pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q) := by
      rw [Finset.prod_neg]
    _ =
        ∏ q : {q // q ∈ s},
          -pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q) := by
      exact
        (Finset.prod_coe_sort s
          (fun q =>
            -pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q))).symm
    _ =
        ∏ q : {q // q ∈ s},
          ∑ state : Fin 3,
            pairedFourierPrimeStateTerm
              R (p : ℕ) (t q) (u q) state := by
      apply Finset.prod_congr rfl
      intro q _hq
      rw [sum_pairedFourierPrimeStateTerm]
    _ = _ := Fintype.prod_sum _

/-- The full support coefficient is the finite sum over independent
three-state assignments at all active prime/form incidences. -/
theorem fixedFamilyPrimeSupportCoefficient_eq_sum_states
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    fixedFamilyPrimeSupportCoefficient R t u support =
      ∑ A : FixedFamilyPairedPrimeStateAssignment support,
        fixedFamilyPairedPrimeStateTerm R t u support A := by
  classical
  unfold fixedFamilyPrimeSupportCoefficient
    fixedFamilyPairedPrimeStateTerm
  simp_rw [fixedFamilyPrimeLocalCoefficient_eq_sum_states]
  exact Fintype.prod_sum _

/-! ## The squarefree divisor family encoded by a state assignment -/

noncomputable def fixedFamilyPairedPrimeStateLeftPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) : Finset {p // p ∈ P} := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1

noncomputable def fixedFamilyPairedPrimeStateRightPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) : Finset {p // p ∈ P} := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0

@[simp]
theorem mem_fixedFamilyPairedPrimeStateLeftPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1 := by
  classical
  simp [fixedFamilyPairedPrimeStateLeftPrimes]

@[simp]
theorem mem_fixedFamilyPairedPrimeStateRightPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0 := by
  classical
  simp [fixedFamilyPairedPrimeStateRightPrimes]

/-- Multiply the selected distinct primes in the left and right
occurrences of every form. -/
noncomputable def fixedFamilyPairedPrimeStateDivisorFamily
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    κ → ℕ × ℕ :=
  fun q =>
    (∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
        (p : ℕ),
      ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
        (p : ℕ))

theorem pairedFourierPrimeStateTerm_eq_side_mul
    (R p : ℕ) (t u : ℝ) (state : Fin 3) :
    pairedFourierPrimeStateTerm R p t u state =
      (if state ≠ 1 then
          -SmoothSieveCutoff.divisorMultiplicativePhase R p t
        else 1) *
      (if state ≠ 0 then
          -SmoothSieveCutoff.divisorMultiplicativePhase R p u
        else 1) := by
  fin_cases state <;>
    simp [pairedFourierPrimeStateTerm]

theorem fintype_prod_prod_mul
    {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    {M : Type*} [CommMonoid M]
    (f g : ∀ i, α i → M) :
    (∏ i, ∏ a, f i a * g i a) =
      (∏ i, ∏ a, f i a) * ∏ i, ∏ a, g i a := by
  simp_rw [Finset.prod_mul_distrib]

theorem fintype_prod_subtype_eq_prod_dite
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ∀ i, i ∈ s → M) :
    (∏ i : {i // i ∈ s}, f i i.2) =
      ∏ i : ι, if hi : i ∈ s then f i hi else 1 := by
  classical
  let g : ι → M := fun i =>
    if hi : i ∈ s then f i hi else 1
  calc
    (∏ i : {i // i ∈ s}, f i i.2) =
        ∏ i : {i // i ∈ s}, g i := by
      apply Finset.prod_congr rfl
      intro i _hi
      simp [g, i.2]
    _ = ∏ i ∈ s, g i :=
      Finset.prod_coe_sort s g
    _ = ∏ i : ι, g i := by
      symm
      calc
        (∏ i : ι, g i) =
            ∏ i : ι, if i ∈ s then g i else 1 := by
          apply Finset.prod_congr rfl
          intro i _hi
          by_cases hi : i ∈ s <;> simp [g, hi]
        _ = ∏ i ∈ s, g i :=
          Fintype.prod_ite_mem s g
    _ = _ := rfl

/-- The state product can be regrouped by form and by side. -/
theorem fixedFamilyPairedPrimeStateTerm_eq_sideProducts
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    fixedFamilyPairedPrimeStateTerm R t u support A =
      (∏ q : κ,
          ((-1 : ℂ) ^
              (fixedFamilyPairedPrimeStateLeftPrimes
                support A q).card *
            (∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
              SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (t q)))) *
        (∏ q : κ,
          ((-1 : ℂ) ^
              (fixedFamilyPairedPrimeStateRightPrimes
                support A q).card *
            (∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
              SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (u q)))) := by
  classical
  unfold fixedFamilyPairedPrimeStateTerm
  simp_rw [pairedFourierPrimeStateTerm_eq_side_mul]
  rw [fintype_prod_prod_mul]
  congr 1
  · calc
      (∏ p : {p // p ∈ P},
          ∏ q : {q // q ∈ support p},
            if A p q ≠ 1 then
              -SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (t q)
            else 1) =
          ∏ p : {p // p ∈ P},
            ∏ q : κ,
              if hq : q ∈ support p then
                if A p ⟨q, hq⟩ ≠ 1 then
                  -SmoothSieveCutoff.divisorMultiplicativePhase
                    R (p : ℕ) (t q)
                else 1
              else 1 := by
        apply Finset.prod_congr rfl
        intro p _hp
        exact
          fintype_prod_subtype_eq_prod_dite
            (support p)
            (fun q hq =>
              if A p ⟨q, hq⟩ ≠ 1 then
                -SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (t q)
              else 1)
      _ =
          ∏ q : κ,
            ∏ p : {p // p ∈ P},
              if hq : q ∈ support p then
                if A p ⟨q, hq⟩ ≠ 1 then
                  -SmoothSieveCutoff.divisorMultiplicativePhase
                    R (p : ℕ) (t q)
                else 1
              else 1 := by
        rw [Finset.prod_comm]
      _ =
          ∏ q : κ,
            ∏ p ∈
                fixedFamilyPairedPrimeStateLeftPrimes support A q,
              -SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (t q) := by
        apply Finset.prod_congr rfl
        intro q _hq
        conv_rhs =>
          rw [← Fintype.prod_ite_mem]
        apply Finset.prod_congr rfl
        intro p _hp
        by_cases hmem :
            p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q
        · obtain ⟨hqp, hstate⟩ :=
            (mem_fixedFamilyPairedPrimeStateLeftPrimes
              support A q p).mp hmem
          simp [hqp, hstate, hmem]
        · have hnot :
              ¬∃ hqp : q ∈ support p, A p ⟨q, hqp⟩ ≠ 1 := by
            simpa using hmem
          by_cases hqp : q ∈ support p
          · have hstate : A p ⟨q, hqp⟩ = 1 := by
              by_contra hne
              exact hnot ⟨hqp, hne⟩
            simp [hqp, hstate, hmem]
          · simp [hqp, hmem]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro q _hq
        rw [Finset.prod_neg]
  · calc
      (∏ p : {p // p ∈ P},
          ∏ q : {q // q ∈ support p},
            if A p q ≠ 0 then
              -SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (u q)
            else 1) =
          ∏ p : {p // p ∈ P},
            ∏ q : κ,
              if hq : q ∈ support p then
                if A p ⟨q, hq⟩ ≠ 0 then
                  -SmoothSieveCutoff.divisorMultiplicativePhase
                    R (p : ℕ) (u q)
                else 1
              else 1 := by
        apply Finset.prod_congr rfl
        intro p _hp
        exact
          fintype_prod_subtype_eq_prod_dite
            (support p)
            (fun q hq =>
              if A p ⟨q, hq⟩ ≠ 0 then
                -SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (u q)
              else 1)
      _ =
          ∏ q : κ,
            ∏ p : {p // p ∈ P},
              if hq : q ∈ support p then
                if A p ⟨q, hq⟩ ≠ 0 then
                  -SmoothSieveCutoff.divisorMultiplicativePhase
                    R (p : ℕ) (u q)
                else 1
              else 1 := by
        rw [Finset.prod_comm]
      _ =
          ∏ q : κ,
            ∏ p ∈
                fixedFamilyPairedPrimeStateRightPrimes support A q,
              -SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (u q) := by
        apply Finset.prod_congr rfl
        intro q _hq
        conv_rhs =>
          rw [← Fintype.prod_ite_mem]
        apply Finset.prod_congr rfl
        intro p _hp
        by_cases hmem :
            p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q
        · obtain ⟨hqp, hstate⟩ :=
            (mem_fixedFamilyPairedPrimeStateRightPrimes
              support A q p).mp hmem
          simp [hqp, hstate, hmem]
        · have hnot :
              ¬∃ hqp : q ∈ support p, A p ⟨q, hqp⟩ ≠ 0 := by
            simpa using hmem
          by_cases hqp : q ∈ support p
          · have hstate : A p ⟨q, hqp⟩ = 0 := by
              by_contra hne
              exact hnot ⟨hqp, hne⟩
            simp [hqp, hstate, hmem]
          · simp [hqp, hmem]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro q _hq
        rw [Finset.prod_neg]

theorem moebius_fixedFamilyPairedPrimeStateDivisorFamily_left
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) :
    (ArithmeticFunction.moebius
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 : ℂ) =
      (-1 : ℂ) ^
        (fixedFamilyPairedPrimeStateLeftPrimes support A q).card := by
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  apply SmoothSieveCutoff.moebius_finsetProd_primes
  · intro p _hp
    exact p.1.prop
  · intro p _hp r _hr hpr
    apply Subtype.ext
    apply Subtype.ext
    exact hpr

theorem moebius_fixedFamilyPairedPrimeStateDivisorFamily_right
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) :
    (ArithmeticFunction.moebius
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 : ℂ) =
      (-1 : ℂ) ^
        (fixedFamilyPairedPrimeStateRightPrimes support A q).card := by
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  apply SmoothSieveCutoff.moebius_finsetProd_primes
  · intro p _hp
    exact p.1.prop
  · intro p _hp r _hr hpr
    apply Subtype.ext
    apply Subtype.ext
    exact hpr

theorem divisorMultiplicativePhase_fixedFamilyPairedPrimeStateDivisorFamily_left
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (t : ℝ) :
    SmoothSieveCutoff.divisorMultiplicativePhase R
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 t =
      ∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
        SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) t := by
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  exact SmoothSieveCutoff.divisorMultiplicativePhase_finsetProd
    R
    (fixedFamilyPairedPrimeStateLeftPrimes support A q)
    (fun p => (p : ℕ))
    (fun p _hp => p.1.prop.pos)
    t

theorem divisorMultiplicativePhase_fixedFamilyPairedPrimeStateDivisorFamily_right
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (u : ℝ) :
    SmoothSieveCutoff.divisorMultiplicativePhase R
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 u =
      ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
        SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) u := by
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  exact SmoothSieveCutoff.divisorMultiplicativePhase_finsetProd
    R
    (fixedFamilyPairedPrimeStateRightPrimes support A q)
    (fun p => (p : ℕ))
    (fun p _hp => p.1.prop.pos)
    u

/-- Each state summand, after restoring the common Fourier envelope, is
literally the transformed paired-divisor family encoded by that state
assignment. -/
theorem pairedCutoffFourierEnvelope_mul_fixedFamilyPairedPrimeStateTerm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    pairedCutoffFourierEnvelope χ t u *
        fixedFamilyPairedPrimeStateTerm R t u support A =
      χ.transformedPairedDivisorFamily R
        (fixedFamilyPairedPrimeStateDivisorFamily support A) (t, u) := by
  classical
  rw [fixedFamilyPairedPrimeStateTerm_eq_sideProducts]
  unfold pairedCutoffFourierEnvelope
    SmoothSieveCutoff.transformedPairedDivisorFamily
    SmoothSieveCutoff.transformedDivisorFamilySide
  simp_rw [
    moebius_fixedFamilyPairedPrimeStateDivisorFamily_left,
    moebius_fixedFamilyPairedPrimeStateDivisorFamily_right,
    divisorMultiplicativePhase_fixedFamilyPairedPrimeStateDivisorFamily_left,
    divisorMultiplicativePhase_fixedFamilyPairedPrimeStateDivisorFamily_right]
  calc
    ((∏ q, χ.cutoffFourierTransform (t q)) *
          ∏ q, χ.cutoffFourierTransform (u q)) *
        ((∏ q,
            (-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateLeftPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (t q)) *
          ∏ q,
            (-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateRightPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (u q)) =
        ((∏ q, χ.cutoffFourierTransform (t q)) *
          ∏ q,
            ((-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateLeftPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (t q))) *
        ((∏ q, χ.cutoffFourierTransform (u q)) *
          ∏ q,
            ((-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateRightPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (u q))) := by
      ring
    _ =
        (∏ q,
          χ.cutoffFourierTransform (t q) *
            ((-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateLeftPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (t q))) *
        ∏ q,
          χ.cutoffFourierTransform (u q) *
            ((-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateRightPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (u q)) := by
      congr 1 <;>
        exact (Finset.prod_mul_distrib).symm
    _ = _ := by
      congr 1 <;>
        apply Finset.prod_congr rfl <;>
        intro q _hq <;>
        ring

theorem prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem
    {P : Finset Nat.Primes}
    (s : Finset {p // p ∈ P}) (p : {p // p ∈ P}) :
    (p : ℕ) ∣ ∏ r ∈ s, (r : ℕ) ↔ p ∈ s := by
  constructor
  · intro hp
    obtain ⟨r, hr, hpr⟩ :=
      (p.1.prop.prime.dvd_finsetProd_iff
        (fun r : {p // p ∈ P} => (r : ℕ))).mp hp
    have heqNat : (r : ℕ) = (p : ℕ) :=
      (r.1.prop.dvd_iff_eq p.1.prop.ne_one).mp hpr
    have heq : r = p := by
      apply Subtype.ext
      apply Subtype.ext
      exact heqNat
    simpa [heq] using hr
  · intro hp
    exact Finset.dvd_prod_of_mem
      (fun r : {p // p ∈ P} => (r : ℕ)) hp

theorem prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    (p : ℕ) ∣
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1 := by
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  rw [
    prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem,
    mem_fixedFamilyPairedPrimeStateLeftPrimes]

theorem prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    (p : ℕ) ∣
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0 := by
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  rw [
    prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem,
    mem_fixedFamilyPairedPrimeStateRightPrimes]

theorem fixedFamilyPrimeSupportAssignmentOf_stateDivisorFamily
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    fixedFamilyPrimeSupportAssignmentOf P
        (fixedFamilyPairedPrimeStateDivisorFamily support A) =
      support := by
  funext p
  ext q
  simp only [fixedFamilyPrimeSupportAssignmentOf,
    mem_pairedPrimeSupport, pairedLocalModulus,
    p.1.prop.dvd_lcm,
    prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff,
    prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff]
  constructor
  · rintro (⟨hq, _hstate⟩ | ⟨hq, _hstate⟩)
    · exact hq
    · exact hq
  · intro hq
    by_cases hleft : A p ⟨q, hq⟩ = 1
    · right
      exact ⟨hq, by omega⟩
    · left
      exact ⟨hq, hleft⟩

theorem squarefree_fixedFamilyPairedPrimeStateDivisorFamily
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    SquarefreePairedDivisorChoice
      (fixedFamilyPairedPrimeStateDivisorFamily support A) := by
  intro q
  constructor <;>
    unfold fixedFamilyPairedPrimeStateDivisorFamily <;>
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p _hp r _hr hpr
    change IsRelPrime (p : ℕ) (r : ℕ)
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes p.1.prop r.1.prop).mpr
      (fun heq =>
        hpr (by
          apply Subtype.ext
          apply Subtype.ext
          exact heq))
  · intro p _hp
    exact p.1.prop.squarefree
  · intro p _hp r _hr hpr
    change IsRelPrime (p : ℕ) (r : ℕ)
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes p.1.prop r.1.prop).mpr
      (fun heq =>
        hpr (by
          apply Subtype.ext
          apply Subtype.ext
          exact heq))
  · intro p _hp
    exact p.1.prop.squarefree

theorem fixedFamilyPairedPrimeStateDivisorFamily_injective
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    Function.Injective
      (fixedFamilyPairedPrimeStateDivisorFamily support) := by
  intro A B hAB
  funext p q
  have hzq :
      fixedFamilyPairedPrimeStateDivisorFamily support A q.1 =
        fixedFamilyPairedPrimeStateDivisorFamily support B q.1 :=
    congrFun hAB q.1
  have hleft :
      (A p q ≠ 1) ↔ (B p q ≠ 1) := by
    have hdiv :
        ((p : ℕ) ∣
            (fixedFamilyPairedPrimeStateDivisorFamily
              support A q.1).1) ↔
          ((p : ℕ) ∣
            (fixedFamilyPairedPrimeStateDivisorFamily
              support B q.1).1) := by
      rw [hzq]
    rw [
      prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff,
      prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff] at hdiv
    simpa only [q.2, exists_true_left,
      Subtype.coe_eta, proof_irrel_heq] using hdiv
  have hright :
      (A p q ≠ 0) ↔ (B p q ≠ 0) := by
    have hdiv :
        ((p : ℕ) ∣
            (fixedFamilyPairedPrimeStateDivisorFamily
              support A q.1).2) ↔
          ((p : ℕ) ∣
            (fixedFamilyPairedPrimeStateDivisorFamily
              support B q.1).2) := by
      rw [hzq]
    rw [
      prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff,
      prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff] at hdiv
    simpa only [q.2, exists_true_left,
      Subtype.coe_eta, proof_irrel_heq] using hdiv
  generalize ha : A p q = a at hleft hright
  generalize hb : B p q = b at hleft hright ⊢
  fin_cases a <;> fin_cases b <;> simp_all

/-- Recover the three-state assignment of a paired divisor family from
prime divisibility.  On a support fiber every active incidence has at
least one of the two divisibilities. -/
noncomputable def fixedFamilyPairedPrimeStateAssignmentOf
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (z : κ → ℕ × ℕ) :
    FixedFamilyPairedPrimeStateAssignment support :=
  fun p q =>
    if (p : ℕ) ∣ (z q).1 then
      if (p : ℕ) ∣ (z q).2 then 2 else 0
    else 1

theorem fixedFamilyPairedPrimeStateAssignmentOf_ne_one_iff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (z : κ → ℕ × ℕ)
    (p : {p // p ∈ P}) (q : {q // q ∈ support p}) :
    fixedFamilyPairedPrimeStateAssignmentOf support z p q ≠ 1 ↔
      (p : ℕ) ∣ (z q).1 := by
  unfold fixedFamilyPairedPrimeStateAssignmentOf
  by_cases hleft : (p : ℕ) ∣ (z q).1 <;>
    by_cases hright : (p : ℕ) ∣ (z q).2 <;>
    simp [hleft, hright]

theorem fixedFamilyPairedPrimeStateAssignmentOf_ne_zero_iff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (z : κ → ℕ × ℕ)
    (hSupport :
      fixedFamilyPrimeSupportAssignmentOf P z = support)
    (p : {p // p ∈ P}) (q : {q // q ∈ support p}) :
    fixedFamilyPairedPrimeStateAssignmentOf support z p q ≠ 0 ↔
      (p : ℕ) ∣ (z q).2 := by
  have hactive :
      (p : ℕ) ∣ Nat.lcm (z q).1 (z q).2 := by
    have hmem : q.1 ∈
        fixedFamilyPrimeSupportAssignmentOf P z p := by
      rw [hSupport]
      exact q.2
    simpa [fixedFamilyPrimeSupportAssignmentOf,
      mem_pairedPrimeSupport, pairedLocalModulus] using hmem
  have hor :
      (p : ℕ) ∣ (z q).1 ∨ (p : ℕ) ∣ (z q).2 :=
    p.1.prop.dvd_lcm.mp hactive
  unfold fixedFamilyPairedPrimeStateAssignmentOf
  by_cases hleft : (p : ℕ) ∣ (z q).1
  · by_cases hright : (p : ℕ) ∣ (z q).2 <;>
      simp [hleft, hright]
  · have hright : (p : ℕ) ∣ (z q).2 := hor.resolve_left hleft
    simp [hleft, hright]

def fixedFamilyPrimeSubtypeNatEmbedding
    (P : Finset Nat.Primes) :
    {p // p ∈ P} ↪ ℕ where
  toFun p := (p : ℕ)
  inj' := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    exact hpq

theorem fixedFamilyPairedPrimeStateDivisorFamily_assignmentOf_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ}
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R))
    (z : κ → ℕ × ℕ)
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (hzSquarefree : SquarefreePairedDivisorChoice z)
    (hSupport :
      fixedFamilyPrimeSupportAssignmentOf
          (primesLEAsPrimes R) z =
        support) :
    fixedFamilyPairedPrimeStateDivisorFamily support
        (fixedFamilyPairedPrimeStateAssignmentOf support z) =
      z := by
  funext q
  apply Prod.ext
  · let A :=
      fixedFamilyPairedPrimeStateAssignmentOf support z
    let s :=
      fixedFamilyPairedPrimeStateLeftPrimes support A q
    let e :=
      fixedFamilyPrimeSubtypeNatEmbedding (primesLEAsPrimes R)
    have hzq := Fintype.mem_piFinset.mp hzR q
    have hleftMem :=
      (Finset.mem_product.mp hzq).1
    have hleftPos : 0 < (z q).1 :=
      (Finset.mem_Icc.mp hleftMem).1
    have hleftLe : (z q).1 ≤ R :=
      (Finset.mem_Icc.mp hleftMem).2
    have hmap :
        s.map e = (z q).1.primeFactors := by
      ext r
      constructor
      · intro hr
        obtain ⟨p, hpS, hpr⟩ := Finset.mem_map.mp hr
        have hpDiv :
            (p : ℕ) ∣ (z q).1 := by
          rw [mem_fixedFamilyPairedPrimeStateLeftPrimes] at hpS
          obtain ⟨hq, hstate⟩ := hpS
          exact
            (fixedFamilyPairedPrimeStateAssignmentOf_ne_one_iff
              support z p ⟨q, hq⟩).mp
              (by simpa using hstate)
        have hrPrime : r.Prime := by
          rw [← hpr]
          exact p.1.prop
        have hrDiv : r ∣ (z q).1 := by
          rw [← hpr]
          exact hpDiv
        exact Nat.mem_primeFactors.mpr
          ⟨hrPrime, hrDiv, hleftPos.ne'⟩
      · intro hr
        have hrData := Nat.mem_primeFactors.mp hr
        have hrPrime : r.Prime := hrData.1
        have hrDiv : r ∣ (z q).1 := hrData.2.1
        have hrLe : r ≤ R :=
          (Nat.le_of_dvd hleftPos hrDiv).trans hleftLe
        let rp : Nat.Primes := ⟨r, hrPrime⟩
        have hrpMem : rp ∈ primesLEAsPrimes R :=
          (mem_primesLEAsPrimes_iff R rp).2 hrLe
        let p : {p // p ∈ primesLEAsPrimes R} := ⟨rp, hrpMem⟩
        have hpSupport :
            q ∈ support p := by
          rw [← hSupport]
          rw [fixedFamilyPrimeSupportAssignmentOf,
            mem_pairedPrimeSupport, pairedLocalModulus,
            p.1.prop.dvd_lcm]
          exact Or.inl (by simpa [p, rp] using hrDiv)
        have hpState :
            A p ⟨q, hpSupport⟩ ≠ 1 := by
          exact
            (fixedFamilyPairedPrimeStateAssignmentOf_ne_one_iff
              support z p ⟨q, hpSupport⟩).2
              (by simpa [p, rp] using hrDiv)
        have hpS : p ∈ s := by
          exact
            (mem_fixedFamilyPairedPrimeStateLeftPrimes
              support A q p).2 ⟨hpSupport, hpState⟩
        exact Finset.mem_map.mpr
          ⟨p, hpS, rfl⟩
    unfold fixedFamilyPairedPrimeStateDivisorFamily
    calc
      (∏ p ∈ s, (p : ℕ)) =
          ∏ r ∈ s.map e, r := by
        symm
        exact Finset.prod_map s e (fun r : ℕ => r)
      _ = ∏ r ∈ (z q).1.primeFactors, r := by
        rw [hmap]
      _ = (z q).1 :=
        Nat.prod_primeFactors_of_squarefree (hzSquarefree q).1
  · let A :=
      fixedFamilyPairedPrimeStateAssignmentOf support z
    let s :=
      fixedFamilyPairedPrimeStateRightPrimes support A q
    let e :=
      fixedFamilyPrimeSubtypeNatEmbedding (primesLEAsPrimes R)
    have hzq := Fintype.mem_piFinset.mp hzR q
    have hrightMem :=
      (Finset.mem_product.mp hzq).2
    have hrightPos : 0 < (z q).2 :=
      (Finset.mem_Icc.mp hrightMem).1
    have hrightLe : (z q).2 ≤ R :=
      (Finset.mem_Icc.mp hrightMem).2
    have hmap :
        s.map e = (z q).2.primeFactors := by
      ext r
      constructor
      · intro hr
        obtain ⟨p, hpS, hpr⟩ := Finset.mem_map.mp hr
        have hpSupport :
            q ∈ support p := by
          have hpSel :
              p ∈ fixedFamilyPairedPrimeStateRightPrimes
                support A q := hpS
          rw [mem_fixedFamilyPairedPrimeStateRightPrimes] at hpSel
          exact hpSel.choose
        have hpState :
            A p ⟨q, hpSupport⟩ ≠ 0 := by
          have hpSel :
              p ∈ fixedFamilyPairedPrimeStateRightPrimes
                support A q := hpS
          rw [mem_fixedFamilyPairedPrimeStateRightPrimes] at hpSel
          simpa using hpSel.choose_spec
        have hpDiv :
            (p : ℕ) ∣ (z q).2 :=
          (fixedFamilyPairedPrimeStateAssignmentOf_ne_zero_iff
            support z hSupport p ⟨q, hpSupport⟩).mp hpState
        have hrPrime : r.Prime := by
          rw [← hpr]
          exact p.1.prop
        have hrDiv : r ∣ (z q).2 := by
          rw [← hpr]
          exact hpDiv
        exact Nat.mem_primeFactors.mpr
          ⟨hrPrime, hrDiv, hrightPos.ne'⟩
      · intro hr
        have hrData := Nat.mem_primeFactors.mp hr
        have hrPrime : r.Prime := hrData.1
        have hrDiv : r ∣ (z q).2 := hrData.2.1
        have hrLe : r ≤ R :=
          (Nat.le_of_dvd hrightPos hrDiv).trans hrightLe
        let rp : Nat.Primes := ⟨r, hrPrime⟩
        have hrpMem : rp ∈ primesLEAsPrimes R :=
          (mem_primesLEAsPrimes_iff R rp).2 hrLe
        let p : {p // p ∈ primesLEAsPrimes R} := ⟨rp, hrpMem⟩
        have hpSupport :
            q ∈ support p := by
          rw [← hSupport]
          rw [fixedFamilyPrimeSupportAssignmentOf,
            mem_pairedPrimeSupport, pairedLocalModulus,
            p.1.prop.dvd_lcm]
          exact Or.inr (by simpa [p, rp] using hrDiv)
        have hpState :
            A p ⟨q, hpSupport⟩ ≠ 0 :=
          (fixedFamilyPairedPrimeStateAssignmentOf_ne_zero_iff
            support z hSupport p ⟨q, hpSupport⟩).2
            (by simpa [p, rp] using hrDiv)
        have hpS : p ∈ s :=
          (mem_fixedFamilyPairedPrimeStateRightPrimes
            support A q p).2 ⟨hpSupport, hpState⟩
        exact Finset.mem_map.mpr
          ⟨p, hpS, rfl⟩
    unfold fixedFamilyPairedPrimeStateDivisorFamily
    calc
      (∏ p ∈ s, (p : ℕ)) =
          ∏ r ∈ s.map e, r := by
        symm
        exact Finset.prod_map s e (fun r : ℕ => r)
      _ = ∏ r ∈ (z q).2.primeFactors, r := by
        rw [hmap]
      _ = (z q).2 :=
        Nat.prod_primeFactors_of_squarefree (hzSquarefree q).2

theorem fixedFamilyPairedPrimeStateDivisorFamily_pos
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) :
    0 <
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 ∧
      0 <
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 := by
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  constructor <;>
    exact Finset.prod_pos fun p _hp => p.1.prop.pos

theorem SmoothSieveCutoff.smoothDivisorFamilyCoefficient_eq_zero_of_not_mem
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (z : κ → ℕ × ℕ)
    (hzPos : ∀ q, 0 < (z q).1 ∧ 0 < (z q).2)
    (hzNot : z ∉ smoothDivisorFamilyChoices κ R) :
    smoothDivisorFamilyCoefficient χ.toFun R z = 0 := by
  have hexists :
      ∃ q : κ, z q ∉ smoothDivisorPairChoices R := by
    by_contra h
    apply hzNot
    apply Fintype.mem_piFinset.mpr
    intro q
    exact Classical.byContradiction fun hq => h ⟨q, hq⟩
  obtain ⟨q, hq⟩ := hexists
  have hpair :
      (z q).1 ∉ smoothDivisorChoices R ∨
        (z q).2 ∉ smoothDivisorChoices R := by
    by_cases hleft : (z q).1 ∈ smoothDivisorChoices R
    · right
      intro hright
      exact hq (Finset.mem_product.mpr ⟨hleft, hright⟩)
    · exact Or.inl hleft
  unfold smoothDivisorFamilyCoefficient
  apply Finset.prod_eq_zero (Finset.mem_univ q)
  rcases hpair with hleft | hright
  · have hgt : R < (z q).1 := by
      have hnotle : ¬(z q).1 ≤ R := by
        intro hle
        exact hleft
          (Finset.mem_Icc.mpr ⟨(hzPos q).1, hle⟩)
      omega
    rw [smoothDivisorSummand_eq_zero_of_lt
      χ.toFun hR hgt χ.zero_of_one_le, zero_mul]
  · have hgt : R < (z q).2 := by
      have hnotle : ¬(z q).2 ≤ R := by
        intro hle
        exact hright
          (Finset.mem_Icc.mpr ⟨(hzPos q).2, hle⟩)
      omega
    rw [smoothDivisorSummand_eq_zero_of_lt
      χ.toFun hR hgt χ.zero_of_one_le, mul_zero]

noncomputable def coordinatewiseAdmissiblePairedPrimeStateAssignments
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ)
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)) :
    Finset (FixedFamilyPairedPrimeStateAssignment support) :=
  Finset.univ.filter fun A =>
    fixedFamilyPairedPrimeStateDivisorFamily support A ∈
      smoothDivisorFamilyChoices κ R

@[simp]
theorem mem_coordinatewiseAdmissiblePairedPrimeStateAssignments
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ}
    {support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)}
    {A : FixedFamilyPairedPrimeStateAssignment support} :
    A ∈ coordinatewiseAdmissiblePairedPrimeStateAssignments R support ↔
      fixedFamilyPairedPrimeStateDivisorFamily support A ∈
        smoothDivisorFamilyChoices κ R := by
  classical
  simp [coordinatewiseAdmissiblePairedPrimeStateAssignments]

theorem stateDivisorFamily_mem_coordinatewiseTruncatedSupportFiber_iff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ}
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R))
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    fixedFamilyPairedPrimeStateDivisorFamily support A ∈
        coordinatewiseTruncatedSupportFiber
          R (primesLEAsPrimes R) support ↔
      fixedFamilyPairedPrimeStateDivisorFamily support A ∈
        smoothDivisorFamilyChoices κ R := by
  rw [mem_coordinatewiseTruncatedSupportFiber,
    SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices]
  simp [
    squarefree_fixedFamilyPairedPrimeStateDivisorFamily,
    fixedFamilyPrimeSupportAssignmentOf_stateDivisorFamily]

theorem sum_admissible_stateCoefficients_eq_sum_coordinatewiseFiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)) :
    (∑ A ∈ coordinatewiseAdmissiblePairedPrimeStateAssignments R support,
        (smoothDivisorFamilyCoefficient χ.toFun R
          (fixedFamilyPairedPrimeStateDivisorFamily support A) : ℂ)) =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber
          R (primesLEAsPrimes R) support,
        (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) := by
  classical
  apply Finset.sum_bij
    (fun A _hA =>
      fixedFamilyPairedPrimeStateDivisorFamily support A)
  · intro A hA
    exact
      (stateDivisorFamily_mem_coordinatewiseTruncatedSupportFiber_iff
        support A).2
        (mem_coordinatewiseAdmissiblePairedPrimeStateAssignments.mp hA)
  · intro A _hA B _hB hAB
    exact fixedFamilyPairedPrimeStateDivisorFamily_injective support hAB
  · intro z hz
    have hzData :=
      (mem_coordinatewiseTruncatedSupportFiber.mp hz)
    have hzSquarefreeData :=
      SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices.mp
        hzData.1
    let A :=
      fixedFamilyPairedPrimeStateAssignmentOf support z
    have hencode :
        fixedFamilyPairedPrimeStateDivisorFamily support A = z :=
      fixedFamilyPairedPrimeStateDivisorFamily_assignmentOf_eq
        support z hzSquarefreeData.1 hzSquarefreeData.2 hzData.2
    refine ⟨A, ?_, hencode⟩
    rw [mem_coordinatewiseAdmissiblePairedPrimeStateAssignments,
      hencode]
    exact hzSquarefreeData.1
  · intro A _hA
    rfl

theorem sum_all_stateCoefficients_eq_sum_admissible
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)) :
    (∑ A : FixedFamilyPairedPrimeStateAssignment support,
        (smoothDivisorFamilyCoefficient χ.toFun R
          (fixedFamilyPairedPrimeStateDivisorFamily support A) : ℂ)) =
      ∑ A ∈ coordinatewiseAdmissiblePairedPrimeStateAssignments R support,
        (smoothDivisorFamilyCoefficient χ.toFun R
          (fixedFamilyPairedPrimeStateDivisorFamily support A) : ℂ) := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro A _hA hAadmissible
  have hnot :
      fixedFamilyPairedPrimeStateDivisorFamily support A ∉
        smoothDivisorFamilyChoices κ R := by
    simpa [coordinatewiseAdmissiblePairedPrimeStateAssignments] using
      hAadmissible
  rw [χ.smoothDivisorFamilyCoefficient_eq_zero_of_not_mem
    hR
    (fixedFamilyPairedPrimeStateDivisorFamily support A)
    (fixedFamilyPairedPrimeStateDivisorFamily_pos support A)
    hnot]
  exact_mod_cast (show (0 : ℝ) = 0 by rfl)

/-! ## Fourier integration of one support fiber -/

theorem pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient_eq_sum_states
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    pairedCutoffFourierEnvelope χ t u *
        fixedFamilyPrimeSupportCoefficient R t u support =
      ∑ A : FixedFamilyPairedPrimeStateAssignment support,
        χ.transformedPairedDivisorFamily R
          (fixedFamilyPairedPrimeStateDivisorFamily support A) (t, u) := by
  rw [fixedFamilyPrimeSupportCoefficient_eq_sum_states,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  exact
    pairedCutoffFourierEnvelope_mul_fixedFamilyPairedPrimeStateTerm
      χ R t u support A

theorem integrable_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          fixedFamilyPrimeSupportCoefficient R tu.1 tu.2 support)
      (volume.prod volume) := by
  have hsum :
      Integrable
        (fun tu : (κ → ℝ) × (κ → ℝ) =>
          ∑ A : FixedFamilyPairedPrimeStateAssignment support,
            χ.transformedPairedDivisorFamily R
              (fixedFamilyPairedPrimeStateDivisorFamily support A) tu)
        (volume.prod volume) := by
    apply integrable_finsetSum
    intro A _hA
    exact χ.integrable_transformedPairedDivisorFamily R _
  apply hsum.congr
  exact ae_of_all _ fun tu =>
    (pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient_eq_sum_states
      χ R tu.1 tu.2 support).symm

theorem integral_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient_eq_sum_states
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          fixedFamilyPrimeSupportCoefficient R tu.1 tu.2 support
        ∂(volume.prod volume)) =
      ∑ A : FixedFamilyPairedPrimeStateAssignment support,
        (smoothDivisorFamilyCoefficient χ.toFun R
          (fixedFamilyPairedPrimeStateDivisorFamily support A) : ℂ) := by
  calc
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          fixedFamilyPrimeSupportCoefficient R tu.1 tu.2 support
        ∂(volume.prod volume)) =
        ∫ tu : (κ → ℝ) × (κ → ℝ),
          ∑ A : FixedFamilyPairedPrimeStateAssignment support,
            χ.transformedPairedDivisorFamily R
              (fixedFamilyPairedPrimeStateDivisorFamily support A) tu
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact ae_of_all _ fun tu =>
        pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient_eq_sum_states
          χ R tu.1 tu.2 support
    _ = _ := by
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro A _hA
        exact
          (χ.smoothDivisorFamilyCoefficient_eq_integral R
            (fixedFamilyPairedPrimeStateDivisorFamily support A)).symm
      · intro A _hA
        exact χ.integrable_transformedPairedDivisorFamily R _

theorem integrable_coordinatewiseTruncatedSupportCoefficient
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        coordinatewiseTruncatedSupportCoefficient
          χ R P tu.1 tu.2 support)
      (volume.prod volume) := by
  apply integrable_finsetSum
  intro z _hz
  exact χ.integrable_transformedPairedDivisorFamily R z

theorem integral_coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        coordinatewiseTruncatedSupportCoefficient
          χ R P tu.1 tu.2 support
        ∂(volume.prod volume)) =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) := by
  calc
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        coordinatewiseTruncatedSupportCoefficient
          χ R P tu.1 tu.2 support
        ∂(volume.prod volume)) =
        ∫ tu : (κ → ℝ) × (κ → ℝ),
          ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
            χ.transformedPairedDivisorFamily R z tu
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact ae_of_all _ fun tu =>
        coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
          χ R P tu.1 tu.2 support
    _ = _ := by
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro z _hz
        exact
          (χ.smoothDivisorFamilyCoefficient_eq_integral R z).symm
      · intro z _hz
        exact χ.integrable_transformedPairedDivisorFamily R z

theorem integral_coordinatewiseTruncationSupportDiscrepancy_eq_zero
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        coordinatewiseTruncationSupportDiscrepancy
          χ R (primesLEAsPrimes R) tu.1 tu.2 support
        ∂(volume.prod volume)) = 0 := by
  have htruncated :
      (∫ tu : (κ → ℝ) × (κ → ℝ),
          coordinatewiseTruncatedSupportCoefficient
            χ R (primesLEAsPrimes R) tu.1 tu.2 support
          ∂(volume.prod volume)) =
        ∑ z ∈ coordinatewiseTruncatedSupportFiber
            R (primesLEAsPrimes R) support,
          (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) :=
    integral_coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
      χ R (primesLEAsPrimes R) support
  have hunrestricted :
      (∫ tu : (κ → ℝ) × (κ → ℝ),
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            fixedFamilyPrimeSupportCoefficient
              R tu.1 tu.2 support
          ∂(volume.prod volume)) =
        ∑ z ∈ coordinatewiseTruncatedSupportFiber
            R (primesLEAsPrimes R) support,
          (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) := by
    rw [
      integral_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient_eq_sum_states,
      sum_all_stateCoefficients_eq_sum_admissible χ hR support,
      sum_admissible_stateCoefficients_eq_sum_coordinatewiseFiber]
  unfold coordinatewiseTruncationSupportDiscrepancy
  rw [integral_sub
    (integrable_coordinatewiseTruncatedSupportCoefficient
      χ R (primesLEAsPrimes R) support)
    (integrable_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient
      χ R support),
    htruncated, hunrestricted, sub_self]

theorem integrable_coordinatewiseTruncationSupportDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        coordinatewiseTruncationSupportDiscrepancy
          χ R P tu.1 tu.2 support)
      (volume.prod volume) :=
  (integrable_coordinatewiseTruncatedSupportCoefficient
      χ R P support).sub
    (integrable_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient
      χ R support)

/-- Full-space Fourier inversion cancels the complete carry-weighted
coordinatewise truncation discrepancy.  No arithmetic hypothesis on the
canonical affine families is needed. -/
theorem integral_cfzCanonicalCarryTruncationDiscrepancy_eq_zero
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (forms : κ → CFZFormIndex k) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R forms tu.1 tu.2
        ∂(volume.prod volume)) = 0 := by
  classical
  unfold cfzCanonicalCarryTruncationDiscrepancy
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro carry _hcarry
    rw [integral_const_mul]
    apply mul_eq_zero_of_right
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro support _hsupport
      rw [integral_mul_const,
        integral_coordinatewiseTruncationSupportDiscrepancy_eq_zero
          χ (by omega : 1 < R) support,
        zero_mul]
    · intro support _hsupport
      exact
        (integrable_coordinatewiseTruncationSupportDiscrepancy
          χ R (primesLEAsPrimes R) support).mul_const
          (cfzCanonicalCarryPrimeSupportDensity
            N W b forms carry support)
  · intro carry _hcarry
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro support _hsupport
    exact
      (integrable_coordinatewiseTruncationSupportDiscrepancy
        χ R (primesLEAsPrimes R) support).mul_const
        (cfzCanonicalCarryPrimeSupportDensity
          N W b forms carry support)

end Wikipedia.SzemeredisTheorem
