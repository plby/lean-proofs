import ErdosProblems.Erdos796.Model
import ErdosProblems.Erdos796.Extremal
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lifting the cofactor model

For a compatible cofactor family `U`, the manuscript associates the set

`{q * u | sqrt n < q ≤ n, q prime, u ∈ U (n / q)}`.

This file defines that set as the image of its finite parameter space and
proves the elementary arithmetic facts behind the lift.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

/-- The primes in the interval `(sqrt n, n]`. -/
def largePrimes (n : ℕ) : Finset ℕ :=
  (Finset.Ioc n.sqrt n).filter Nat.Prime

@[simp] theorem mem_largePrimes {n q : ℕ} :
    q ∈ largePrimes n ↔ n.sqrt < q ∧ q ≤ n ∧ q.Prime := by
  simp [largePrimes, and_assoc]

/-- The finite parameter space `(q,u)` used in the lift. -/
def liftParameters (n : ℕ) (U : ℕ → Finset ℕ) : Finset (Σ _q : ℕ, ℕ) :=
  (largePrimes n).sigma fun q => U (n / q)

@[simp] theorem mk_mem_liftParameters {n q u : ℕ} {U : ℕ → Finset ℕ} :
    (⟨q, u⟩ : Σ _q : ℕ, ℕ) ∈ liftParameters n U ↔
      q ∈ largePrimes n ∧ u ∈ U (n / q) := by
  simp [liftParameters]

/-- The integer represented by a lift parameter. -/
def liftValue (qu : Σ _q : ℕ, ℕ) : ℕ := qu.1 * qu.2

/-- The lifted set `A_n(U)` from the manuscript. -/
def liftedSet (n : ℕ) (U : ℕ → Finset ℕ) : Finset ℕ :=
  (liftParameters n U).image liftValue

/-- Membership in the lift, in the literal form used in the manuscript. -/
theorem mem_liftedSet {n a : ℕ} {U : ℕ → Finset ℕ} :
    a ∈ liftedSet n U ↔
      ∃ q u : ℕ, q ∈ largePrimes n ∧ u ∈ U (n / q) ∧ q * u = a := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨⟨q, u⟩, hqu, rfl⟩
    exact ⟨q, u, (mk_mem_liftParameters.mp hqu).1,
      (mk_mem_liftParameters.mp hqu).2, rfl⟩
  · rintro ⟨q, u, hq, hu, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨q, u⟩, mk_mem_liftParameters.mpr ⟨hq, hu⟩, rfl⟩

/-- Division by a number strictly larger than `sqrt n` is at most `sqrt n`. -/
theorem div_le_sqrt_of_sqrt_lt {n q : ℕ} (hq : n.sqrt < q) :
    n / q ≤ n.sqrt := by
  by_contra h
  have hdiv : n.sqrt < n / q := Nat.lt_of_not_ge h
  have hleft : (n.sqrt + 1) * (n.sqrt + 1) ≤ q * (n / q) :=
    Nat.mul_le_mul (Nat.succ_le_iff.mpr hq) (Nat.succ_le_iff.mpr hdiv)
  have hright : q * (n / q) ≤ n := by
    simpa [Nat.mul_comm] using! Nat.div_mul_le_self n q
  exact (Nat.not_lt_of_ge (hleft.trans hright)) (Nat.lt_succ_sqrt n)

/-- The quotient indexing any large prime belongs to the finite index interval
used by `modelScore`. -/
theorem quotient_mem_modelRange {n q : ℕ} (hq : q ∈ largePrimes n) :
    n / q ∈ Finset.Icc 1 n.sqrt := by
  rw [Finset.mem_Icc]
  have hq' := mem_largePrimes.mp hq
  have hqpos : 0 < q := hq'.2.2.pos
  constructor
  · exact (Nat.le_div_iff_mul_le hqpos).mpr (by simpa using! hq'.2.1)
  · exact div_le_sqrt_of_sqrt_lt hq'.1

/-- Every cofactor occurring in a compatible lift lies in `[1,sqrt n]`. -/
theorem lift_cofactor_bounds {n q u : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) (hq : q ∈ largePrimes n) (hu : u ∈ U (n / q)) :
    1 ≤ u ∧ u ≤ n.sqrt := by
  have hu' := hU.1 (n / q) hu
  rw [mem_positiveIcc] at hu'
  exact ⟨hu'.1, hu'.2.trans (div_le_sqrt_of_sqrt_lt (mem_largePrimes.mp hq).1)⟩

/-- The parametrization `(q,u) ↦ q*u` of a compatible lift is injective. -/
theorem lift_parameter_injective {n q u Q v : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U)
    (hq : q ∈ largePrimes n) (_hu : u ∈ U (n / q))
    (hQ : Q ∈ largePrimes n) (hv : v ∈ U (n / Q))
    (heq : q * u = Q * v) : q = Q ∧ u = v := by
  have hqp := (mem_largePrimes.mp hq).2.2
  have hQp := (mem_largePrimes.mp hQ).2.2
  have hvb := lift_cofactor_bounds hU hQ hv
  have hqdvd : q ∣ Q * v := by
    rw [← heq]
    exact ⟨u, rfl⟩
  have hqQ : q ∣ Q := by
    rcases hqp.dvd_mul.mp hqdvd with hqQ | hqv
    · exact hqQ
    · have hqle : q ≤ v := Nat.le_of_dvd (Nat.zero_lt_of_lt hvb.1) hqv
      exact False.elim ((not_lt_of_ge (hqle.trans hvb.2)) (mem_largePrimes.mp hq).1)
  have hqeq : q = Q := (Nat.prime_dvd_prime_iff_eq hqp hQp).mp hqQ
  subst Q
  exact ⟨rfl, Nat.mul_left_cancel hqp.pos heq⟩

/-- No large prime can divide a cofactor occurring in the lift. -/
theorem largePrime_not_dvd_cofactor {n q r x : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) (hq : q ∈ largePrimes n)
    (hr : r ∈ largePrimes n) (hx : x ∈ U (n / r)) : ¬ q ∣ x := by
  intro hqx
  have hxb := lift_cofactor_bounds hU hr hx
  have hqle : q ≤ x := Nat.le_of_dvd (Nat.zero_lt_of_lt hxb.1) hqx
  exact (Nat.not_lt_of_ge (hqle.trans hxb.2)) (mem_largePrimes.mp hq).1

/-- If a large prime divides a product of two lifted integers, it is one of
their two distinguished large primes. -/
theorem largePrime_dvd_two_lifts {n q r x s y : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) (hq : q ∈ largePrimes n)
    (hr : r ∈ largePrimes n) (hx : x ∈ U (n / r))
    (hs : s ∈ largePrimes n) (hy : y ∈ U (n / s))
    (hdiv : q ∣ (r * x) * (s * y)) : q = r ∨ q = s := by
  have hqp := (mem_largePrimes.mp hq).2.2
  rcases hqp.dvd_mul.mp hdiv with hleft | hright
  · rcases hqp.dvd_mul.mp hleft with hqr | hqx
    · exact Or.inl <| (Nat.prime_dvd_prime_iff_eq hqp
        (mem_largePrimes.mp hr).2.2).mp hqr
    · exact False.elim <| largePrime_not_dvd_cofactor hU hq hr hx hqx
  · rcases hqp.dvd_mul.mp hright with hqs | hqy
    · exact Or.inr <| (Nat.prime_dvd_prime_iff_eq hqp
        (mem_largePrimes.mp hs).2.2).mp hqs
    · exact False.elim <| largePrime_not_dvd_cofactor hU hq hs hy hqy

/-- With distinct large primes on the left, equality of represented products
recovers the unordered pair of large primes on the right. -/
theorem distinct_lift_prime_pairs {n q u Q v r x s y : ℕ}
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (hq : q ∈ largePrimes n) (_hu : u ∈ U (n / q))
    (hQ : Q ∈ largePrimes n) (_hv : v ∈ U (n / Q))
    (hr : r ∈ largePrimes n) (hx : x ∈ U (n / r))
    (hs : s ∈ largePrimes n) (hy : y ∈ U (n / s))
    (hne : q ≠ Q) (hprod : (q * u) * (Q * v) = (r * x) * (s * y)) :
    (q = r ∧ Q = s) ∨ (q = s ∧ Q = r) := by
  have hqdvd : q ∣ (r * x) * (s * y) := by
    rw [← hprod]
    exact ⟨u * (Q * v), by ac_rfl⟩
  have hQdvd : Q ∣ (r * x) * (s * y) := by
    rw [← hprod]
    exact ⟨v * (q * u), by ac_rfl⟩
  rcases largePrime_dvd_two_lifts hU hq hr hx hs hy hqdvd with hqr | hqs
  · rcases largePrime_dvd_two_lifts hU hQ hr hx hs hy hQdvd with hQr | hQs
    · exact False.elim <| hne (hqr.trans hQr.symm)
    · exact Or.inl ⟨hqr, hQs⟩
  · rcases largePrime_dvd_two_lifts hU hQ hr hx hs hy hQdvd with hQr | hQs
    · exact Or.inr ⟨hqs, hQr⟩
    · exact False.elim <| hne (hqs.trans hQs.symm)

/-- After cancelling one repeated large prime, the other large prime is still
recoverable because neither remaining cofactor is divisible by it. -/
theorem remaining_large_prime {n q u v s x y : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U)
    (hq : q ∈ largePrimes n) (_hu : u ∈ U (n / q)) (_hv : v ∈ U (n / q))
    (hs : s ∈ largePrimes n) (hx : x ∈ U (n / q)) (hy : y ∈ U (n / s))
    (hprod : (q * u) * (q * v) = (q * x) * (s * y)) : q = s := by
  have hqp := (mem_largePrimes.mp hq).2.2
  have hcancel : u * (q * v) = x * (s * y) := by
    apply Nat.mul_left_cancel hqp.pos
    calc
      q * (u * (q * v)) = (q * u) * (q * v) := by ac_rfl
      _ = (q * x) * (s * y) := hprod
      _ = q * (x * (s * y)) := by ac_rfl
  have hdiv : q ∣ x * (s * y) := by
    rw [← hcancel]
    exact ⟨u * v, by ac_rfl⟩
  rcases hqp.dvd_mul.mp hdiv with hqx | hqsy
  · exact False.elim <| largePrime_not_dvd_cofactor hU hq hq hx hqx
  · rcases hqp.dvd_mul.mp hqsy with hqs | hqy
    · exact (Nat.prime_dvd_prime_iff_eq hqp (mem_largePrimes.mp hs).2.2).mp hqs
    · exact False.elim <| largePrime_not_dvd_cofactor hU hq hs hy hqy

/-- If the two distinguished primes in one representation coincide, both
distinguished primes in every equal product coincide with them. -/
theorem repeated_lift_prime_pair {n q u v r x s y : ℕ}
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (hq : q ∈ largePrimes n) (hu : u ∈ U (n / q)) (hv : v ∈ U (n / q))
    (hr : r ∈ largePrimes n) (hx : x ∈ U (n / r))
    (hs : s ∈ largePrimes n) (hy : y ∈ U (n / s))
    (hprod : (q * u) * (q * v) = (r * x) * (s * y)) :
    r = q ∧ s = q := by
  have hqdvd : q ∣ (r * x) * (s * y) := by
    rw [← hprod]
    exact ⟨u * (q * v), by ac_rfl⟩
  rcases largePrime_dvd_two_lifts hU hq hr hx hs hy hqdvd with hqr | hqs
  · subst r
    have hlast := remaining_large_prime hU hq hu hv hs hx hy hprod
    exact ⟨rfl, hlast.symm⟩
  · subst s
    have hprod' : (q * u) * (q * v) = (q * y) * (r * x) := by
      calc
        (q * u) * (q * v) = (r * x) * (q * y) := hprod
        _ = (q * y) * (r * x) := by ac_rfl
    have hlast := remaining_large_prime hU hq hu hv hr hy hx hprod'
    exact ⟨hlast.symm, rfl⟩

/-- Once the ordered large primes agree, equality of lifted products is
equivalent to equality of the cofactor products. -/
theorem cofactor_product_eq {q Q u v x y : ℕ}
    (hq : 0 < q) (hQ : 0 < Q)
    (hprod : (q * u) * (Q * v) = (q * x) * (Q * y)) : u * v = x * y := by
  apply Nat.mul_left_cancel (Nat.mul_pos hq hQ)
  calc
    (q * Q) * (u * v) = (q * u) * (Q * v) := by ac_rfl
    _ = (q * x) * (Q * y) := hprod
    _ = (q * Q) * (x * y) := by ac_rfl

/-- Cofactor-product cancellation when the two large primes are swapped. -/
theorem cofactor_product_eq_swap {q Q u v x y : ℕ}
    (hq : 0 < q) (hQ : 0 < Q)
    (hprod : (q * u) * (Q * v) = (Q * x) * (q * y)) : u * v = y * x := by
  apply Nat.mul_left_cancel (Nat.mul_pos hq hQ)
  calc
    (q * Q) * (u * v) = (q * u) * (Q * v) := by ac_rfl
    _ = (Q * x) * (q * y) := hprod
    _ = (q * Q) * (y * x) := by ac_rfl

/-- A lifted integer together with its proof of membership. -/
abbrev LiftElement (n : ℕ) (U : ℕ → Finset ℕ) :=
  {a : ℕ // a ∈ liftedSet n U}

/-- The unique lift parameter of a lifted integer.  Uniqueness is proved by
`lift_parameter_injective`; the definition chooses the witness supplied by
membership in the image. -/
noncomputable def liftParameterOf (n : ℕ) (U : ℕ → Finset ℕ)
    (a : LiftElement n U) : Σ _q : ℕ, ℕ :=
  Classical.choose (Finset.mem_image.mp a.property)

theorem liftParameterOf_mem (n : ℕ) (U : ℕ → Finset ℕ)
    (a : LiftElement n U) : liftParameterOf n U a ∈ liftParameters n U :=
  (Classical.choose_spec (Finset.mem_image.mp a.property)).1

theorem liftParameterOf_value (n : ℕ) (U : ℕ → Finset ℕ)
    (a : LiftElement n U) : liftValue (liftParameterOf n U a) = a :=
  (Classical.choose_spec (Finset.mem_image.mp a.property)).2

/-- The finite set counted by `strictProductRepCount` for the lifted set. -/
def liftRepresentationFinset (n : ℕ) (U : ℕ → Finset ℕ) (m : ℕ) :
    Finset (ℕ × ℕ) :=
  ((liftedSet n U ×ˢ liftedSet n U).filter fun ab =>
    ab.1 < ab.2 ∧ ab.1 * ab.2 = m)

/-- A representation in the lifted set, carrying its membership proof. -/
abbrev LiftRepresentation (n : ℕ) (U : ℕ → Finset ℕ) (m : ℕ) :=
  {ab : ℕ × ℕ // ab ∈ liftRepresentationFinset n U m}

theorem liftRepresentation_left_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) : r.1.1 ∈ liftedSet n U := by
  exact (Finset.mem_product.mp (Finset.mem_filter.mp r.property).1).1

theorem liftRepresentation_right_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) : r.1.2 ∈ liftedSet n U := by
  exact (Finset.mem_product.mp (Finset.mem_filter.mp r.property).1).2

theorem liftRepresentation_lt {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) : r.1.1 < r.1.2 :=
  (Finset.mem_filter.mp r.property).2.1

theorem liftRepresentation_product {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) : r.1.1 * r.1.2 = m :=
  (Finset.mem_filter.mp r.property).2.2

/-- The lift parameter of the left member of a representation. -/
noncomputable def leftLiftParameter {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) : Σ _q : ℕ, ℕ :=
  liftParameterOf n U ⟨r.1.1, liftRepresentation_left_mem r⟩

/-- The lift parameter of the right member of a representation. -/
noncomputable def rightLiftParameter {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) : Σ _q : ℕ, ℕ :=
  liftParameterOf n U ⟨r.1.2, liftRepresentation_right_mem r⟩

theorem leftLiftParameter_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    leftLiftParameter r ∈ liftParameters n U :=
  liftParameterOf_mem n U _

theorem rightLiftParameter_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    rightLiftParameter r ∈ liftParameters n U :=
  liftParameterOf_mem n U _

theorem leftLiftPrime_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    (leftLiftParameter r).1 ∈ largePrimes n :=
  (mk_mem_liftParameters.mp (leftLiftParameter_mem r)).1

theorem leftLiftCofactor_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    (leftLiftParameter r).2 ∈ U (n / (leftLiftParameter r).1) :=
  (mk_mem_liftParameters.mp (leftLiftParameter_mem r)).2

theorem rightLiftPrime_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    (rightLiftParameter r).1 ∈ largePrimes n :=
  (mk_mem_liftParameters.mp (rightLiftParameter_mem r)).1

theorem rightLiftCofactor_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    (rightLiftParameter r).2 ∈ U (n / (rightLiftParameter r).1) :=
  (mk_mem_liftParameters.mp (rightLiftParameter_mem r)).2

theorem leftLiftParameter_value {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    liftValue (leftLiftParameter r) = r.1.1 :=
  liftParameterOf_value n U _

theorem rightLiftParameter_value {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    liftValue (rightLiftParameter r) = r.1.2 :=
  liftParameterOf_value n U _

theorem liftRepresentation_parameter_product {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    liftValue (leftLiftParameter r) * liftValue (rightLiftParameter r) = m := by
  rw [leftLiftParameter_value, rightLiftParameter_value]
  exact liftRepresentation_product r

/-- Cofactors in a representation, oriented so that the first one belongs to
the distinguished prime `q`. -/
noncomputable def orientedCofactors {n m : ℕ} {U : ℕ → Finset ℕ}
    (q : ℕ) (r : LiftRepresentation n U m) : ℕ × ℕ :=
  if (leftLiftParameter r).1 = q then
    ((leftLiftParameter r).2, (rightLiftParameter r).2)
  else
    ((rightLiftParameter r).2, (leftLiftParameter r).2)

/-- Relative to a base representation with two distinct large primes, every
other representation has either the same or the swapped prime orientation. -/
theorem liftRepresentation_prime_orientation {n m : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) (b r : LiftRepresentation n U m)
    (hne : (leftLiftParameter b).1 ≠ (rightLiftParameter b).1) :
    ((leftLiftParameter r).1 = (leftLiftParameter b).1 ∧
      (rightLiftParameter r).1 = (rightLiftParameter b).1) ∨
    ((leftLiftParameter r).1 = (rightLiftParameter b).1 ∧
      (rightLiftParameter r).1 = (leftLiftParameter b).1) := by
  have hbL := mk_mem_liftParameters.mp (leftLiftParameter_mem b)
  have hbR := mk_mem_liftParameters.mp (rightLiftParameter_mem b)
  have hrL := mk_mem_liftParameters.mp (leftLiftParameter_mem r)
  have hrR := mk_mem_liftParameters.mp (rightLiftParameter_mem r)
  have hprod :
      ((leftLiftParameter b).1 * (leftLiftParameter b).2) *
          ((rightLiftParameter b).1 * (rightLiftParameter b).2) =
        ((leftLiftParameter r).1 * (leftLiftParameter r).2) *
          ((rightLiftParameter r).1 * (rightLiftParameter r).2) := by
    exact (liftRepresentation_parameter_product b).trans
      (liftRepresentation_parameter_product r).symm
  rcases distinct_lift_prime_pairs hU
      hbL.1 hbL.2 hbR.1 hbR.2 hrL.1 hrL.2 hrR.1 hrR.2 hne hprod with
    hsame | hswap
  · exact Or.inl ⟨hsame.1.symm, hsame.2.symm⟩
  · exact Or.inr ⟨hswap.2.symm, hswap.1.symm⟩

/-- The oriented cofactor pair of every representation lies in the single
cofactor-product fibre selected by a base representation. -/
theorem orientedCofactors_mem {n m : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) (b r : LiftRepresentation n U m)
    (hne : (leftLiftParameter b).1 ≠ (rightLiftParameter b).1) :
    orientedCofactors (leftLiftParameter b).1 r ∈
      ((U (n / (leftLiftParameter b).1) ×ˢ
          U (n / (rightLiftParameter b).1)).filter fun uv =>
        uv.1 * uv.2 = (leftLiftParameter b).2 * (rightLiftParameter b).2) := by
  have hbL := mk_mem_liftParameters.mp (leftLiftParameter_mem b)
  have hbR := mk_mem_liftParameters.mp (rightLiftParameter_mem b)
  have hrL := mk_mem_liftParameters.mp (leftLiftParameter_mem r)
  have hrR := mk_mem_liftParameters.mp (rightLiftParameter_mem r)
  have hprod :
      ((leftLiftParameter b).1 * (leftLiftParameter b).2) *
          ((rightLiftParameter b).1 * (rightLiftParameter b).2) =
        ((leftLiftParameter r).1 * (leftLiftParameter r).2) *
          ((rightLiftParameter r).1 * (rightLiftParameter r).2) := by
    exact (liftRepresentation_parameter_product b).trans
      (liftRepresentation_parameter_product r).symm
  have horient := liftRepresentation_prime_orientation hU b r hne
  by_cases hleft : (leftLiftParameter r).1 = (leftLiftParameter b).1
  · rw [orientedCofactors, if_pos hleft]
    rcases horient with hsame | hswap
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · have hmem := leftLiftCofactor_mem r
          rw [hleft] at hmem
          exact hmem
        · have hmem := rightLiftCofactor_mem r
          rw [hsame.2] at hmem
          exact hmem
      · apply (cofactor_product_eq
          (mem_largePrimes.mp hbL.1).2.2.pos
          (mem_largePrimes.mp hbR.1).2.2.pos ?_).symm
        simpa [hleft, hsame.2] using! hprod
    · exact False.elim <| hne (hleft.symm.trans hswap.1)
  · rw [orientedCofactors, if_neg hleft]
    rcases horient with hsame | hswap
    · exact False.elim <| hleft hsame.1
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · have hmem := rightLiftCofactor_mem r
          rw [hswap.2] at hmem
          exact hmem
        · have hmem := leftLiftCofactor_mem r
          rw [hswap.1] at hmem
          exact hmem
      · apply (cofactor_product_eq_swap
          (mem_largePrimes.mp hbL.1).2.2.pos
          (mem_largePrimes.mp hbR.1).2.2.pos ?_).symm
        simpa [hswap.1, hswap.2] using! hprod

theorem liftRepresentation_primes_of_left_eq {n m : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) (b r : LiftRepresentation n U m)
    (hne : (leftLiftParameter b).1 ≠ (rightLiftParameter b).1)
    (hleft : (leftLiftParameter r).1 = (leftLiftParameter b).1) :
    (leftLiftParameter r).1 = (leftLiftParameter b).1 ∧
      (rightLiftParameter r).1 = (rightLiftParameter b).1 := by
  refine ⟨hleft, ?_⟩
  rcases liftRepresentation_prime_orientation hU b r hne with hsame | hswap
  · exact hsame.2
  · exact False.elim <| hne (hleft.symm.trans hswap.1)

theorem liftRepresentation_primes_of_left_ne {n m : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) (b r : LiftRepresentation n U m)
    (hne : (leftLiftParameter b).1 ≠ (rightLiftParameter b).1)
    (hleft : (leftLiftParameter r).1 ≠ (leftLiftParameter b).1) :
    (leftLiftParameter r).1 = (rightLiftParameter b).1 ∧
      (rightLiftParameter r).1 = (leftLiftParameter b).1 := by
  rcases liftRepresentation_prime_orientation hU b r hne with hsame | hswap
  · exact False.elim <| hleft hsame.1
  · exact hswap

theorem liftRepresentation_left_eq_mul {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    r.1.1 = (leftLiftParameter r).1 * (leftLiftParameter r).2 := by
  calc
    r.1.1 = liftValue (leftLiftParameter r) := (leftLiftParameter_value r).symm
    _ = (leftLiftParameter r).1 * (leftLiftParameter r).2 := rfl

theorem liftRepresentation_right_eq_mul {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) :
    r.1.2 = (rightLiftParameter r).1 * (rightLiftParameter r).2 := by
  calc
    r.1.2 = liftValue (rightLiftParameter r) := (rightLiftParameter_value r).symm
    _ = (rightLiftParameter r).1 * (rightLiftParameter r).2 := rfl

/-- For distinct base primes, the oriented cofactor code is injective on all
strict representations. -/
theorem orientedCofactors_injective {n m : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) (b : LiftRepresentation n U m)
    (hne : (leftLiftParameter b).1 ≠ (rightLiftParameter b).1) :
    Function.Injective (fun r : LiftRepresentation n U m =>
      orientedCofactors (n := n) (m := m) (U := U) (leftLiftParameter b).1 r) := by
  intro r s hcode
  by_cases hr : (leftLiftParameter r).1 = (leftLiftParameter b).1
  · have hrp := liftRepresentation_primes_of_left_eq hU b r hne hr
    by_cases hs : (leftLiftParameter s).1 = (leftLiftParameter b).1
    · have hsp := liftRepresentation_primes_of_left_eq hU b s hne hs
      have hc1 := congrArg Prod.fst hcode
      have hc2 := congrArg Prod.snd hcode
      simp only [orientedCofactors, if_pos hr, if_pos hs] at hc1 hc2
      apply Subtype.ext
      apply Prod.ext
      · calc
          r.1.1 = (leftLiftParameter r).1 * (leftLiftParameter r).2 :=
            liftRepresentation_left_eq_mul r
          _ = (leftLiftParameter b).1 * (leftLiftParameter r).2 := by rw [hrp.1]
          _ = (leftLiftParameter b).1 * (leftLiftParameter s).2 := by rw [hc1]
          _ = (leftLiftParameter s).1 * (leftLiftParameter s).2 := by rw [hsp.1]
          _ = s.1.1 := (liftRepresentation_left_eq_mul s).symm
      · calc
          r.1.2 = (rightLiftParameter r).1 * (rightLiftParameter r).2 :=
            liftRepresentation_right_eq_mul r
          _ = (rightLiftParameter b).1 * (rightLiftParameter r).2 := by rw [hrp.2]
          _ = (rightLiftParameter b).1 * (rightLiftParameter s).2 := by rw [hc2]
          _ = (rightLiftParameter s).1 * (rightLiftParameter s).2 := by rw [hsp.2]
          _ = s.1.2 := (liftRepresentation_right_eq_mul s).symm
    · have hsp := liftRepresentation_primes_of_left_ne hU b s hne hs
      have hc1 := congrArg Prod.fst hcode
      have hc2 := congrArg Prod.snd hcode
      simp only [orientedCofactors, if_pos hr, if_neg hs] at hc1 hc2
      have hcross1 : r.1.1 = s.1.2 := by
        calc
          r.1.1 = (leftLiftParameter r).1 * (leftLiftParameter r).2 :=
            liftRepresentation_left_eq_mul r
          _ = (leftLiftParameter b).1 * (leftLiftParameter r).2 := by rw [hrp.1]
          _ = (leftLiftParameter b).1 * (rightLiftParameter s).2 := by rw [hc1]
          _ = (rightLiftParameter s).1 * (rightLiftParameter s).2 := by rw [hsp.2]
          _ = s.1.2 := (liftRepresentation_right_eq_mul s).symm
      have hcross2 : r.1.2 = s.1.1 := by
        calc
          r.1.2 = (rightLiftParameter r).1 * (rightLiftParameter r).2 :=
            liftRepresentation_right_eq_mul r
          _ = (rightLiftParameter b).1 * (rightLiftParameter r).2 := by rw [hrp.2]
          _ = (rightLiftParameter b).1 * (leftLiftParameter s).2 := by rw [hc2]
          _ = (leftLiftParameter s).1 * (leftLiftParameter s).2 := by rw [hsp.1]
          _ = s.1.1 := (liftRepresentation_left_eq_mul s).symm
      have hrlt := liftRepresentation_lt r
      have hslt := liftRepresentation_lt s
      omega
  · have hrp := liftRepresentation_primes_of_left_ne hU b r hne hr
    by_cases hs : (leftLiftParameter s).1 = (leftLiftParameter b).1
    · have hsp := liftRepresentation_primes_of_left_eq hU b s hne hs
      have hc1 := congrArg Prod.fst hcode
      have hc2 := congrArg Prod.snd hcode
      simp only [orientedCofactors, if_neg hr, if_pos hs] at hc1 hc2
      have hcross1 : r.1.2 = s.1.1 := by
        calc
          r.1.2 = (rightLiftParameter r).1 * (rightLiftParameter r).2 :=
            liftRepresentation_right_eq_mul r
          _ = (leftLiftParameter b).1 * (rightLiftParameter r).2 := by rw [hrp.2]
          _ = (leftLiftParameter b).1 * (leftLiftParameter s).2 := by rw [hc1]
          _ = (leftLiftParameter s).1 * (leftLiftParameter s).2 := by rw [hsp.1]
          _ = s.1.1 := (liftRepresentation_left_eq_mul s).symm
      have hcross2 : r.1.1 = s.1.2 := by
        calc
          r.1.1 = (leftLiftParameter r).1 * (leftLiftParameter r).2 :=
            liftRepresentation_left_eq_mul r
          _ = (rightLiftParameter b).1 * (leftLiftParameter r).2 := by rw [hrp.1]
          _ = (rightLiftParameter b).1 * (rightLiftParameter s).2 := by rw [hc2]
          _ = (rightLiftParameter s).1 * (rightLiftParameter s).2 := by rw [hsp.2]
          _ = s.1.2 := (liftRepresentation_right_eq_mul s).symm
      have hrlt := liftRepresentation_lt r
      have hslt := liftRepresentation_lt s
      omega
    · have hsp := liftRepresentation_primes_of_left_ne hU b s hne hs
      have hc1 := congrArg Prod.fst hcode
      have hc2 := congrArg Prod.snd hcode
      simp only [orientedCofactors, if_neg hr, if_neg hs] at hc1 hc2
      apply Subtype.ext
      apply Prod.ext
      · calc
          r.1.1 = (leftLiftParameter r).1 * (leftLiftParameter r).2 :=
            liftRepresentation_left_eq_mul r
          _ = (rightLiftParameter b).1 * (leftLiftParameter r).2 := by rw [hrp.1]
          _ = (rightLiftParameter b).1 * (leftLiftParameter s).2 := by rw [hc2]
          _ = (leftLiftParameter s).1 * (leftLiftParameter s).2 := by rw [hsp.1]
          _ = s.1.1 := (liftRepresentation_left_eq_mul s).symm
      · calc
          r.1.2 = (rightLiftParameter r).1 * (rightLiftParameter r).2 :=
            liftRepresentation_right_eq_mul r
          _ = (leftLiftParameter b).1 * (rightLiftParameter r).2 := by rw [hrp.2]
          _ = (leftLiftParameter b).1 * (rightLiftParameter s).2 := by rw [hc1]
          _ = (rightLiftParameter s).1 * (rightLiftParameter s).2 := by rw [hsp.2]
          _ = s.1.2 := (liftRepresentation_right_eq_mul s).symm

/-- If one representation uses two distinct large primes, all strict
representations inject into one compatibility fibre. -/
theorem liftRepresentation_card_le_two_of_distinct {n m : ℕ}
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (b : LiftRepresentation n U m)
    (hne : (leftLiftParameter b).1 ≠ (rightLiftParameter b).1) :
    (liftRepresentationFinset n U m).card ≤ 2 := by
  classical
  let target : Finset (ℕ × ℕ) :=
    ((U (n / (leftLiftParameter b).1) ×ˢ
        U (n / (rightLiftParameter b).1)).filter fun uv =>
      uv.1 * uv.2 = (leftLiftParameter b).2 * (rightLiftParameter b).2)
  let code : LiftRepresentation n U m → {uv : ℕ × ℕ // uv ∈ target} :=
    fun r => ⟨orientedCofactors (leftLiftParameter b).1 r, by
      simpa [target] using! orientedCofactors_mem hU b r hne⟩
  have hcode : Function.Injective code := by
    intro r s hrs
    apply orientedCofactors_injective hU b hne
    exact congrArg Subtype.val hrs
  have hcard := Fintype.card_le_of_injective code hcode
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  calc
    (liftRepresentationFinset n U m).card ≤ target.card := hcard
    _ = productRepCount
        (U (n / (leftLiftParameter b).1))
        (U (n / (rightLiftParameter b).1))
        ((leftLiftParameter b).2 * (rightLiftParameter b).2) := by
          rfl
    _ ≤ 2 := hU.2 _ _ _

/-- The un-oriented cofactor pair of a strict representation. -/
noncomputable def representationCofactors {n m : ℕ} {U : ℕ → Finset ℕ}
    (r : LiftRepresentation n U m) : ℕ × ℕ :=
  ((leftLiftParameter r).2, (rightLiftParameter r).2)

/-- If the base representation has a repeated distinguished prime, every
representation has that same distinguished prime in both factors. -/
theorem liftRepresentation_primes_of_repeated {n m : ℕ}
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (b r : LiftRepresentation n U m)
    (heq : (leftLiftParameter b).1 = (rightLiftParameter b).1) :
    (leftLiftParameter r).1 = (leftLiftParameter b).1 ∧
      (rightLiftParameter r).1 = (leftLiftParameter b).1 := by
  have hbRv := rightLiftCofactor_mem b
  rw [← heq] at hbRv
  have hprod :
      ((leftLiftParameter b).1 * (leftLiftParameter b).2) *
          ((leftLiftParameter b).1 * (rightLiftParameter b).2) =
        ((leftLiftParameter r).1 * (leftLiftParameter r).2) *
          ((rightLiftParameter r).1 * (rightLiftParameter r).2) := by
    have h := (liftRepresentation_parameter_product b).trans
      (liftRepresentation_parameter_product r).symm
    change
      ((leftLiftParameter b).1 * (leftLiftParameter b).2) *
          ((rightLiftParameter b).1 * (rightLiftParameter b).2) =
        ((leftLiftParameter r).1 * (leftLiftParameter r).2) *
          ((rightLiftParameter r).1 * (rightLiftParameter r).2) at h
    rw [← heq] at h
    exact h
  exact repeated_lift_prime_pair hU
    (leftLiftPrime_mem b) (leftLiftCofactor_mem b) hbRv
    (leftLiftPrime_mem r) (leftLiftCofactor_mem r)
    (rightLiftPrime_mem r) (rightLiftCofactor_mem r) hprod

/-- In the repeated-prime case, every cofactor pair lies in the corresponding
diagonal compatibility fibre. -/
theorem representationCofactors_mem_repeated {n m : ℕ}
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (b r : LiftRepresentation n U m)
    (heq : (leftLiftParameter b).1 = (rightLiftParameter b).1) :
    representationCofactors r ∈
      ((U (n / (leftLiftParameter b).1) ×ˢ
          U (n / (leftLiftParameter b).1)).filter fun uv =>
        uv.1 * uv.2 = (leftLiftParameter b).2 * (rightLiftParameter b).2) := by
  have hrp := liftRepresentation_primes_of_repeated hU b r heq
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · have hmem := leftLiftCofactor_mem r
      rw [hrp.1] at hmem
      exact hmem
    · have hmem := rightLiftCofactor_mem r
      rw [hrp.2] at hmem
      exact hmem
  · have hprod :
        ((leftLiftParameter b).1 * (leftLiftParameter b).2) *
            ((leftLiftParameter b).1 * (rightLiftParameter b).2) =
          ((leftLiftParameter b).1 * (leftLiftParameter r).2) *
            ((leftLiftParameter b).1 * (rightLiftParameter r).2) := by
      have h := (liftRepresentation_parameter_product b).trans
        (liftRepresentation_parameter_product r).symm
      change
        ((leftLiftParameter b).1 * (leftLiftParameter b).2) *
            ((rightLiftParameter b).1 * (rightLiftParameter b).2) =
          ((leftLiftParameter r).1 * (leftLiftParameter r).2) *
            ((rightLiftParameter r).1 * (rightLiftParameter r).2) at h
      rw [← heq, hrp.1, hrp.2] at h
      exact h
    exact (cofactor_product_eq
      (mem_largePrimes.mp (leftLiftPrime_mem b)).2.2.pos
      (mem_largePrimes.mp (leftLiftPrime_mem b)).2.2.pos hprod).symm

/-- The cofactor code is injective in the repeated-prime case as well. -/
theorem representationCofactors_injective_repeated {n m : ℕ}
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (b : LiftRepresentation n U m)
    (heq : (leftLiftParameter b).1 = (rightLiftParameter b).1) :
    Function.Injective (fun r : LiftRepresentation n U m => representationCofactors r) := by
  intro r s hcode
  have hrp := liftRepresentation_primes_of_repeated hU b r heq
  have hsp := liftRepresentation_primes_of_repeated hU b s heq
  have hc1 := congrArg Prod.fst hcode
  have hc2 := congrArg Prod.snd hcode
  simp only [representationCofactors] at hc1 hc2
  apply Subtype.ext
  apply Prod.ext
  · calc
      r.1.1 = (leftLiftParameter r).1 * (leftLiftParameter r).2 :=
        liftRepresentation_left_eq_mul r
      _ = (leftLiftParameter b).1 * (leftLiftParameter r).2 := by rw [hrp.1]
      _ = (leftLiftParameter b).1 * (leftLiftParameter s).2 := by rw [hc1]
      _ = (leftLiftParameter s).1 * (leftLiftParameter s).2 := by rw [hsp.1]
      _ = s.1.1 := (liftRepresentation_left_eq_mul s).symm
  · calc
      r.1.2 = (rightLiftParameter r).1 * (rightLiftParameter r).2 :=
        liftRepresentation_right_eq_mul r
      _ = (leftLiftParameter b).1 * (rightLiftParameter r).2 := by rw [hrp.2]
      _ = (leftLiftParameter b).1 * (rightLiftParameter s).2 := by rw [hc2]
      _ = (rightLiftParameter s).1 * (rightLiftParameter s).2 := by rw [hsp.2]
      _ = s.1.2 := (liftRepresentation_right_eq_mul s).symm

/-- The repeated-prime branch also has at most two strict representations. -/
theorem liftRepresentation_card_le_two_of_repeated {n m : ℕ}
    {U : ℕ → Finset ℕ} (hU : Compatible U)
    (b : LiftRepresentation n U m)
    (heq : (leftLiftParameter b).1 = (rightLiftParameter b).1) :
    (liftRepresentationFinset n U m).card ≤ 2 := by
  classical
  let target : Finset (ℕ × ℕ) :=
    ((U (n / (leftLiftParameter b).1) ×ˢ
        U (n / (leftLiftParameter b).1)).filter fun uv =>
      uv.1 * uv.2 = (leftLiftParameter b).2 * (rightLiftParameter b).2)
  let code : LiftRepresentation n U m → {uv : ℕ × ℕ // uv ∈ target} :=
    fun r => ⟨representationCofactors r, by
      simpa [target] using! representationCofactors_mem_repeated hU b r heq⟩
  have hcode : Function.Injective code := by
    intro r s hrs
    apply representationCofactors_injective_repeated hU b heq
    exact congrArg Subtype.val hrs
  have hcard := Fintype.card_le_of_injective code hcode
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  calc
    (liftRepresentationFinset n U m).card ≤ target.card := hcard
    _ = productRepCount
        (U (n / (leftLiftParameter b).1))
        (U (n / (leftLiftParameter b).1))
        ((leftLiftParameter b).2 * (rightLiftParameter b).2) := by
          rfl
    _ ≤ 2 := hU.2 _ _ _

/-- The lifted set is contained in `[1,n]`. -/
theorem liftedSet_subset_positiveIcc {n : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) : liftedSet n U ⊆ positiveIcc n := by
  intro a ha
  rcases mem_liftedSet.mp ha with ⟨q, u, hq, hu, rfl⟩
  rw [mem_positiveIcc]
  have hub := (mem_positiveIcc.mp (hU.1 (n / q) hu))
  have hqpos : 0 < q := (mem_largePrimes.mp hq).2.2.pos
  constructor
  · exact Nat.mul_pos hqpos hub.1
  · have : u * q ≤ n := (Nat.le_div_iff_mul_le hqpos).mp hub.2
    simpa [Nat.mul_comm] using! this

/-- `liftValue` is injective on the finite lift parameter space. -/
theorem liftValue_injOn {n : ℕ} {U : ℕ → Finset ℕ} (hU : Compatible U) :
    Set.InjOn liftValue (liftParameters n U) := by
  rintro ⟨q, u⟩ hqu ⟨Q, v⟩ hQv heq
  have h := lift_parameter_injective hU
    (mk_mem_liftParameters.mp hqu).1 (mk_mem_liftParameters.mp hqu).2
    (mk_mem_liftParameters.mp hQv).1 (mk_mem_liftParameters.mp hQv).2 heq
  cases h.1
  cases h.2
  rfl

/-- The cardinality of the lift is the sum of its fibre cardinalities over
large primes. -/
theorem card_liftedSet_eq_sum_primes {n : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) :
    (liftedSet n U).card = ∑ q ∈ largePrimes n, (U (n / q)).card := by
  classical
  rw [liftedSet, Finset.card_image_iff.mpr (liftValue_injOn hU)]
  exact Finset.card_sigma _ _

/-- The bucket definition of `modelScore` is the fibrewise regrouping of the
sum over large primes. -/
theorem sum_primes_eq_modelScore (n : ℕ) (U : ℕ → Finset ℕ) :
    (∑ q ∈ largePrimes n, (U (n / q)).card) = modelScore n U := by
  classical
  let indices := Finset.Icc 1 n.sqrt
  have hmaps : ∀ q ∈ largePrimes n, n / q ∈ indices := by
    intro q hq
    simpa [indices] using! quotient_mem_modelRange hq
  calc
    ∑ q ∈ largePrimes n, (U (n / q)).card =
        ∑ j ∈ indices,
          ∑ q ∈ largePrimes n with n / q = j, (U j).card := by
            symm
            exact Finset.sum_fiberwise_of_maps_to' hmaps (fun j => (U j).card)
    _ = ∑ j ∈ indices, bucketCount n j * (U j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_const_nat (m := (U j).card) (fun _ _ => rfl)]
      congr 1
      simp only [bucketCount, largePrimes]
      congr 1
      ext q
      simp [and_assoc, and_left_comm, and_comm]
    _ = modelScore n U := by
      simp [modelScore, indices]

/-- The lift has exactly the finite-model score. -/
theorem card_liftedSet_eq_modelScore {n : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) :
    (liftedSet n U).card = modelScore n U := by
  rw [card_liftedSet_eq_sum_primes hU, sum_primes_eq_modelScore]

/-- Every product has at most two strict representations in a compatible
lift. -/
theorem liftRepresentation_card_le_two {n m : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) : (liftRepresentationFinset n U m).card ≤ 2 := by
  classical
  by_cases hempty : liftRepresentationFinset n U m = ∅
  · simp [hempty]
  · obtain ⟨ab, hab⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let b : LiftRepresentation n U m := ⟨ab, hab⟩
    by_cases hne : (leftLiftParameter b).1 ≠ (rightLiftParameter b).1
    · exact liftRepresentation_card_le_two_of_distinct hU b hne
    · exact liftRepresentation_card_le_two_of_repeated hU b (not_ne_iff.mp hne)

/-- The manuscript's lift of every compatible cofactor family is admissible. -/
theorem lift_admissible {n : ℕ} {U : ℕ → Finset ℕ} (hU : Compatible U) :
    Admissible n (liftedSet n U) := by
  constructor
  · exact liftedSet_subset_positiveIcc hU
  · intro m
    change (liftRepresentationFinset n U m).card ≤ 2
    exact liftRepresentation_card_le_two hU

/-- Every compatible model score is realized by an admissible set of exactly
that cardinality. -/
theorem modelScore_le_g3_of_compatible {n : ℕ} {U : ℕ → Finset ℕ}
    (hU : Compatible U) : modelScore n U ≤ g3 n := by
  calc
    modelScore n U = (liftedSet n U).card := (card_liftedSet_eq_modelScore hU).symm
    _ ≤ g3 n := card_le_g3 (lift_admissible hU)

/-- The finite cofactor model is a genuine lower bound for the extremal
problem. -/
theorem model_lower (n : ℕ) : G n ≤ g3 n := by
  obtain ⟨U, hU, hscore⟩ := G_attained n
  calc
    G n = modelScore n U := hscore.symm
    _ ≤ g3 n := modelScore_le_g3_of_compatible hU

alias G_le_g3 := model_lower

end Erdos796
