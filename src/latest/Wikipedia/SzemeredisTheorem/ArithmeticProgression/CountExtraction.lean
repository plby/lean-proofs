import Wikipedia.SzemeredisTheorem.ArithmeticProgression.Count

/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The unnormalized mass of all cyclic `k`-term progressions. -/
noncomputable def cyclicAPMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, ∑ d : ZMod N, cyclicAPProduct k N f a d

/-- The unnormalized contribution from constant cyclic progressions. -/
noncomputable def cyclicAPDiagonalMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, cyclicAPProduct k N f a 0

/-- The unnormalized mass of cyclic progressions with nonzero common
difference.  This is zero, rather than ill-defined, if no nonzero difference
exists. -/
noncomputable def cyclicAPOffDiagMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N,
    ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
      cyclicAPProduct k N f a d

@[simp]
theorem cyclicAPProduct_zero_difference
    (k N : ℕ) (f : ZMod N → ℝ) (a : ZMod N) :
    cyclicAPProduct k N f a 0 = f a ^ k := by
  simp [cyclicAPProduct, cyclicAPTerm]

theorem cyclicAPDiagonalMass_eq_sum_pow
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPDiagonalMass k N f = ∑ a : ZMod N, f a ^ k := by
  simp [cyclicAPDiagonalMass]

/-- A pointwise bound `0 ≤ x ≤ B` controls its `k`th power by one copy of
`x` and `k - 1` copies of `B`. -/
theorem pow_le_pow_pred_mul
    {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B)
    {k : ℕ} (hk : 1 ≤ k) :
    x ^ k ≤ B ^ (k - 1) * x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hB0 : 0 ≤ B := hx0.trans hxB
  have hpow : x ^ m ≤ B ^ m :=
    pow_le_pow_left₀ hx0 hxB m
  simpa [Nat.add_comm, pow_succ', Nat.add_sub_cancel, mul_comm] using
    (mul_le_mul_of_nonneg_right hpow hx0)

/-- The diagonal mass is bounded by the pointwise height to the power
`k-1`, times `N` times the mean.  This is the form used to show that
diagonal progressions are negligible for the W-tricked prime weight. -/
theorem cyclicAPDiagonalMass_le
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B) :
    cyclicAPDiagonalMass k N f ≤
      B ^ (k - 1) * (N : ℝ) * mean f := by
  rw [cyclicAPDiagonalMass_eq_sum_pow]
  calc
    ∑ a : ZMod N, f a ^ k ≤
        ∑ a : ZMod N, B ^ (k - 1) * f a := by
      exact Finset.sum_le_sum fun a _ =>
        pow_le_pow_pred_mul (hf0 a) (hfB a) hk
    _ = B ^ (k - 1) * ∑ a : ZMod N, f a := by
      rw [Finset.mul_sum]
    _ = B ^ (k - 1) * ((N : ℝ) * mean f) := by
      rw [← Fintype.card_mul_expect]
      simp [mean, ZMod.card]
    _ = B ^ (k - 1) * (N : ℝ) * mean f := by ring

/-- The full unnormalized mass splits into its diagonal and off-diagonal
parts. -/
theorem cyclicAPMass_eq_diagonal_add_offDiagMass
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      cyclicAPDiagonalMass k N f + cyclicAPOffDiagMass k N f := by
  classical
  rw [cyclicAPMass, cyclicAPDiagonalMass, cyclicAPOffDiagMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hdiagonal :
      ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d = 0),
        cyclicAPProduct k N f a d =
          cyclicAPProduct k N f a 0 := by
    apply Finset.sum_eq_single 0
    · intro d hd hd0
      exact (hd0 (Finset.mem_filter.mp hd).2).elim
    · simp
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun d : ZMod N => d = 0)
    (f := fun d => cyclicAPProduct k N f a d)]
  rw [hdiagonal]

/-- If the full mass strictly exceeds its diagonal contribution, the
off-diagonal mass is positive. -/
theorem cyclicAPOffDiagMass_pos_of_diagonal_lt_mass
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ)
    (h :
      cyclicAPDiagonalMass k N f <
        cyclicAPMass k N f) :
    0 < cyclicAPOffDiagMass k N f := by
  rw [cyclicAPMass_eq_diagonal_add_offDiagMass] at h
  linarith

/-- The normalized count is the full mass divided once for each cyclic
parameter. -/
theorem cyclicAPCount_eq_mass_div_div
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPCount k N f =
      cyclicAPMass k N f / (N : ℝ) / (N : ℝ) := by
  simp [cyclicAPCount, cyclicAPMass, mean₂, mean,
    Fintype.expect_eq_sum_div_card, ZMod.card, Finset.sum_div]

/-- Clearing the two nonzero normalization factors recovers the full
unnormalized mass. -/
theorem cyclicAPMass_eq_mul_mul_count
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      (N : ℝ) * (N : ℝ) * cyclicAPCount k N f := by
  rw [cyclicAPCount_eq_mass_div_div]
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  field_simp

/-- Consequently the normalized count is the normalized sum of the diagonal
and off-diagonal masses. -/
theorem cyclicAPCount_eq_diagonal_add_offDiagMass_div_div
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPCount k N f =
      (cyclicAPDiagonalMass k N f + cyclicAPOffDiagMass k N f) /
        (N : ℝ) / (N : ℝ) := by
  rw [cyclicAPCount_eq_mass_div_div,
    cyclicAPMass_eq_diagonal_add_offDiagMass]

theorem cyclicAPOffDiagMass_nonneg
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cyclicAPOffDiagMass k N f := by
  classical
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro d _
  exact cyclicAPProduct_nonneg hf a d

/-- A normalized count which dominates the normalized diagonal-height bound
already forces positive off-diagonal mass. -/
theorem cyclicAPOffDiagMass_pos_of_count
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B)
    (hcount :
      B ^ (k - 1) * mean f <
        (N : ℝ) * cyclicAPCount k N f) :
    0 < cyclicAPOffDiagMass k N f := by
  apply cyclicAPOffDiagMass_pos_of_diagonal_lt_mass
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast NeZero.pos N
  calc
    cyclicAPDiagonalMass k N f ≤
        B ^ (k - 1) * (N : ℝ) * mean f :=
      cyclicAPDiagonalMass_le hk hf0 hfB
    _ = (N : ℝ) * (B ^ (k - 1) * mean f) := by ring
    _ < (N : ℝ) *
        ((N : ℝ) * cyclicAPCount k N f) :=
      mul_lt_mul_of_pos_left hcount hN
    _ = cyclicAPMass k N f := by
      rw [cyclicAPMass_eq_mul_mul_count]
      ring

/-- For nonnegative weights, a cyclic progression has positive product
exactly when each of its factors is positive. -/
theorem cyclicAPProduct_pos_iff_of_nonneg
    {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 < cyclicAPProduct k N f a d ↔
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by
  constructor
  · intro hprod j
    have hprod_ne :
        (∏ i : Fin k, f (cyclicAPTerm a d i)) ≠ 0 := by
      simpa only [cyclicAPProduct] using ne_of_gt hprod
    have hfactor_ne : f (cyclicAPTerm a d j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp hprod_ne j (Finset.mem_univ j)
    exact lt_of_le_of_ne (hf _) (Ne.symm hfactor_ne)
  · intro hfactor
    rw [cyclicAPProduct]
    exact Finset.prod_pos fun j _ => hfactor j

/-- Positive off-diagonal mass extracts a nonconstant cyclic progression on
which every factor of the nonnegative weight is strictly positive. -/
theorem exists_cyclicAP_of_offDiagMass_pos
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hmass : 0 < cyclicAPOffDiagMass k N f) :
    ∃ a d : ZMod N, d ≠ 0 ∧
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by
  classical
  rw [cyclicAPOffDiagMass] at hmass
  have houter_nonneg :
      ∀ a ∈ (Finset.univ : Finset (ZMod N)),
        0 ≤
          ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
            cyclicAPProduct k N f a d := by
    intro a _
    exact Finset.sum_nonneg fun d _ => cyclicAPProduct_nonneg hf a d
  obtain ⟨a, _, ha⟩ :=
    (Finset.sum_pos_iff_of_nonneg houter_nonneg).mp hmass
  have hinner_nonneg :
      ∀ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
        0 ≤ cyclicAPProduct k N f a d := by
    intro d _
    exact cyclicAPProduct_nonneg hf a d
  obtain ⟨d, hdmem, hdpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hinner_nonneg).mp ha
  refine ⟨a, d, (Finset.mem_filter.mp hdmem).2, ?_⟩
  exact (cyclicAPProduct_pos_iff_of_nonneg hf a d).mp hdpos

end Wikipedia.SzemeredisTheorem
