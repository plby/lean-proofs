import ErdosProblems.Erdos538.LayerUnionLower

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- Positive integers up to `N`. -/
def positiveIntegers (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- Positive squarefree integers up to `N`. -/
def positiveSquarefree (N : ℕ) : Finset ℕ :=
  (positiveIntegers N).filter Squarefree

/-- Exact nonnegative-rational harmonic mass up to `N`. -/
def harmonicMassNN (N : ℕ) : ℚ≥0 := reciprocalMassNN (positiveIntegers N)

/-- The elementary finite bound `sum_{1≤b≤N} 1/b² ≤ 2`. -/
theorem sum_inv_sq_positiveIntegers_le_two (N : ℕ) :
    (∑ b ∈ positiveIntegers N, ((b : ℚ≥0) ^ 2)⁻¹) ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℚ) 0 (N + 1)
  have hsets : Finset.Ioo 0 (N + 1) = positiveIntegers N := by
    ext b
    simp [positiveIntegers]
    omega
  rw [hsets] at h
  norm_num at h
  apply (NNRat.coe_le_coe).mp
  change NNRat.coeHom (∑ b ∈ positiveIntegers N,
    ((b : ℚ≥0) ^ 2)⁻¹) ≤ NNRat.coeHom 2
  rw [map_sum]
  simpa [NNRat.coe_inv, NNRat.coe_pow, NNRat.coe_natCast] using h

/-- Every positive integer occurs as `b²*a` for a positive squarefree `a`,
with both factors still at most `N`. -/
theorem positiveIntegers_subset_squarefree_square_image (N : ℕ) :
    positiveIntegers N ⊆
      ((positiveSquarefree N).product (positiveIntegers N)).image
        (fun ab => ab.2 ^ 2 * ab.1) := by
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  obtain ⟨a, b, ha, hb, hab, hsq⟩ :=
    Nat.sq_mul_squarefree_of_pos (show 0 < n by omega)
  apply Finset.mem_image.mpr
  refine ⟨(a, b), Finset.mem_product.mpr ⟨?_, ?_⟩, hab⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨ha, ?_⟩, hsq⟩
    calc
      a ≤ b ^ 2 * a := le_mul_of_one_le_left (Nat.zero_le a) (by nlinarith)
      _ = n := hab
      _ ≤ N := hnN
  · apply Finset.mem_Icc.mpr
    refine ⟨hb, ?_⟩
    calc
      b ≤ b ^ 2 := by nlinarith
      _ ≤ b ^ 2 * a := le_mul_of_one_le_right' ha
      _ = n := hab
      _ ≤ N := hnN

/-- Squarefree integers carry at least half of the full harmonic mass.  The
constant is deliberately elementary rather than sharp. -/
theorem harmonicMassNN_le_two_mul_squarefree (N : ℕ) :
    harmonicMassNN N ≤ 2 * reciprocalMassNN (positiveSquarefree N) := by
  classical
  let pairs := (positiveSquarefree N).product (positiveIntegers N)
  let g : ℕ × ℕ → ℕ := fun ab => ab.2 ^ 2 * ab.1
  have hsubset : positiveIntegers N ⊆ pairs.image g := by
    simpa [pairs, g] using positiveIntegers_subset_squarefree_square_image N
  calc
    harmonicMassNN N = ∑ n ∈ positiveIntegers N, (1 : ℚ≥0) / n := by
      rfl
    _ ≤ ∑ n ∈ pairs.image g, (1 : ℚ≥0) / n :=
      Finset.sum_le_sum_of_subset hsubset
    _ ≤ ∑ ab ∈ pairs, (1 : ℚ≥0) / g ab := by
      exact Finset.sum_image_le_of_nonneg (fun _ _ => bot_le)
    _ = ∑ a ∈ positiveSquarefree N, ∑ b ∈ positiveIntegers N,
        (1 : ℚ≥0) / (b ^ 2 * a) := by
      simpa only [pairs, g, Finset.product_eq_sprod, Nat.cast_mul,
        Nat.cast_pow] using
        (Finset.sum_product' (positiveSquarefree N) (positiveIntegers N)
          (fun a b => (1 : ℚ≥0) / (b ^ 2 * a)))
    _ = ∑ a ∈ positiveSquarefree N, ∑ b ∈ positiveIntegers N,
        ((1 : ℚ≥0) / a) * ((b : ℚ≥0) ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have ha0 : (a : ℚ≥0) ≠ 0 := by
        exact_mod_cast (show a ≠ 0 by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
          omega)
      have hb0 : (b : ℚ≥0) ≠ 0 := by
        exact_mod_cast (show b ≠ 0 by
          have := (Finset.mem_Icc.mp hb).1
          omega)
      field_simp
    _ = (∑ a ∈ positiveSquarefree N, (1 : ℚ≥0) / a) *
        (∑ b ∈ positiveIntegers N, ((b : ℚ≥0) ^ 2)⁻¹) := by
      rw [Finset.sum_mul_sum]
    _ ≤ (∑ a ∈ positiveSquarefree N, (1 : ℚ≥0) / a) * 2 :=
      mul_le_mul_right (sum_inv_sq_positiveIntegers_le_two N) _
    _ = 2 * reciprocalMassNN (positiveSquarefree N) := by
      simp [reciprocalMassNN, mul_comm]

/-- Primes in `{1,…,N}`. -/
def primeIntegers (N : ℕ) : Finset ℕ :=
  (positiveIntegers N).filter Nat.Prime

/-- Reciprocal sum of primes up to `N`. -/
def primeHarmonicNN (N : ℕ) : ℚ≥0 :=
  reciprocalMassNN (primeIntegers N)

/-- Weighted first moment of the number of distinct prime factors on the
positive squarefree integers up to `N`. -/
def squarefreePrimeFactorMomentNN (N : ℕ) : ℚ≥0 :=
  ∑ n ∈ positiveSquarefree N,
    n.primeFactors.card • ((1 : ℚ≥0) / n)

/-- Prime factors of an integer in `{1,…,N}` belong to `primeIntegers N`. -/
theorem primeFactors_subset_primeIntegers {N n : ℕ}
    (hn : n ∈ positiveIntegers N) : n.primeFactors ⊆ primeIntegers N := by
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_le, ?_⟩,
    Nat.prime_of_mem_primeFactors hp⟩
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : 0 < n := by omega
  exact (Nat.le_of_dvd hnpos (Nat.dvd_of_mem_primeFactors hp)).trans
    (Finset.mem_Icc.mp hn).2

/-- Incidences `(n,p)` with squarefree `n≤N` and `p∣n`. -/
def primeFactorIncidences (N : ℕ) : Finset (ℕ × ℕ) :=
  ((positiveSquarefree N).product (primeIntegers N)).filter
    fun np => np.2 ∈ np.1.primeFactors

/-- Expanding the cardinality writes the first moment as the reciprocal sum
over prime-factor incidences. -/
theorem squarefreePrimeFactorMomentNN_eq_incidence_sum (N : ℕ) :
    squarefreePrimeFactorMomentNN N =
      ∑ np ∈ primeFactorIncidences N, (1 : ℚ≥0) / np.1 := by
  classical
  unfold squarefreePrimeFactorMomentNN primeFactorIncidences
  rw [Finset.sum_filter]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  have hpf : (primeIntegers N).filter (fun p => p ∈ n.primeFactors) =
      n.primeFactors := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp => hp.2
    · intro hp
      exact ⟨primeFactors_subset_primeIntegers
        (Finset.mem_filter.mp hn).1 hp, hp⟩
  rw [← Finset.sum_filter, hpf]
  simp [nsmul_eq_mul]

/-- The incidence map `(n,p) ↦ (p,n/p)` is injective and lands in the full
prime-by-integer rectangle. -/
theorem primeFactorIncidence_sum_le_rectangle (N : ℕ) :
    (∑ np ∈ primeFactorIncidences N, (1 : ℚ≥0) / np.1) ≤
      ∑ pm ∈ (primeIntegers N).product (positiveIntegers N),
        ((1 : ℚ≥0) / pm.1) * ((1 : ℚ≥0) / pm.2) := by
  classical
  let e : ℕ × ℕ → ℕ × ℕ := fun np => (np.2, np.1 / np.2)
  let rectangle := (primeIntegers N).product (positiveIntegers N)
  have hinj : Set.InjOn e (primeFactorIncidences N) := by
    intro x hx y hy hxy
    have hxp : x.2 ∈ x.1.primeFactors :=
      (Finset.mem_filter.mp hx).2
    have hyp : y.2 ∈ y.1.primeFactors :=
      (Finset.mem_filter.mp hy).2
    have hp : x.2 = y.2 := congrArg Prod.fst hxy
    have hq : x.1 / x.2 = y.1 / y.2 := congrArg Prod.snd hxy
    apply Prod.ext
    · calc
        x.1 = x.2 * (x.1 / x.2) :=
          (Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hxp)).symm
        _ = y.2 * (y.1 / y.2) := congrArg₂ (· * ·) hp hq
        _ = y.1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hyp)
    · exact hp
  have hmaps : Set.MapsTo e (primeFactorIncidences N : Set (ℕ × ℕ))
      (rectangle : Set (ℕ × ℕ)) := by
    intro np hnp
    have hprod := (Finset.mem_filter.mp hnp).1
    have hfactor := (Finset.mem_filter.mp hnp).2
    have hnSF : np.1 ∈ positiveSquarefree N :=
      (Finset.mem_product.mp hprod).1
    have hpP : np.2 ∈ primeIntegers N :=
      (Finset.mem_product.mp hprod).2
    apply Finset.mem_product.mpr
    refine ⟨hpP, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact (Nat.one_le_div_iff
        (Nat.prime_of_mem_primeFactors hfactor).pos).2
        (Nat.le_of_dvd (by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnSF).1).1
          omega) (Nat.dvd_of_mem_primeFactors hfactor))
    · exact (Nat.div_le_self _ _).trans
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hnSF).1).2
  have hterm : ∀ np ∈ primeFactorIncidences N,
      (1 : ℚ≥0) / np.1 =
        ((1 : ℚ≥0) / (e np).1) * ((1 : ℚ≥0) / (e np).2) := by
    intro np hnp
    have hfactor := (Finset.mem_filter.mp hnp).2
    have hpdvd := Nat.dvd_of_mem_primeFactors hfactor
    have hp0 : (np.2 : ℚ≥0) ≠ 0 := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hfactor).ne_zero
    have hq0 : ((np.1 / np.2 : ℕ) : ℚ≥0) ≠ 0 := by
      have hprod := (Finset.mem_filter.mp hnp).1
      have hnSF := (Finset.mem_product.mp hprod).1
      have hnpos : 0 < np.1 := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnSF).1).1
        omega
      have hqpos : 0 < np.1 / np.2 := Nat.div_pos
        (Nat.le_of_dvd hnpos hpdvd)
        (Nat.prime_of_mem_primeFactors hfactor).pos
      exact_mod_cast (Nat.ne_of_gt hqpos)
    change (1 : ℚ≥0) / np.1 =
      ((1 : ℚ≥0) / np.2) * ((1 : ℚ≥0) / (np.1 / np.2 : ℕ))
    have hcast : (np.1 : ℚ≥0) =
        (np.2 : ℚ≥0) * ((np.1 / np.2 : ℕ) : ℚ≥0) := by
      exact_mod_cast (Nat.mul_div_cancel' hpdvd).symm
    rw [hcast]
    field_simp
  have himage : (primeFactorIncidences N).image e ⊆ rectangle := by
    intro pm hpm
    obtain ⟨np, hnp, rfl⟩ := Finset.mem_image.mp hpm
    exact hmaps hnp
  calc
    (∑ np ∈ primeFactorIncidences N, (1 : ℚ≥0) / np.1) =
        ∑ np ∈ primeFactorIncidences N,
          ((1 : ℚ≥0) / (e np).1) * ((1 : ℚ≥0) / (e np).2) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ∑ pm ∈ (primeFactorIncidences N).image e,
          ((1 : ℚ≥0) / pm.1) * ((1 : ℚ≥0) / pm.2) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ pm ∈ rectangle,
          ((1 : ℚ≥0) / pm.1) * ((1 : ℚ≥0) / pm.2) :=
      Finset.sum_le_sum_of_subset himage
    _ = _ := by rfl

/-- Elementary first-moment bound in terms of the prime reciprocal sum. -/
theorem squarefreePrimeFactorMomentNN_le (N : ℕ) :
    squarefreePrimeFactorMomentNN N ≤
      primeHarmonicNN N * harmonicMassNN N := by
  rw [squarefreePrimeFactorMomentNN_eq_incidence_sum]
  calc
    (∑ np ∈ primeFactorIncidences N, (1 : ℚ≥0) / np.1) ≤
        ∑ pm ∈ (primeIntegers N).product (positiveIntegers N),
          ((1 : ℚ≥0) / pm.1) * ((1 : ℚ≥0) / pm.2) :=
      primeFactorIncidence_sum_le_rectangle N
    _ = primeHarmonicNN N * harmonicMassNN N := by
      rw [Finset.product_eq_sprod, Finset.sum_product]
      simp only [primeHarmonicNN, harmonicMassNN, reciprocalMassNN]
      rw [Finset.sum_mul_sum]

end Erdos538
