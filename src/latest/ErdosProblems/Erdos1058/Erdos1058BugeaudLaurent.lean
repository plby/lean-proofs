import Mathlib

/-!
# The rational `2`-adic interpolation determinant used in Erdős problem 1058

This file contains the algebraic core of the specialization of the
Bugeaud--Laurent interpolation-determinant argument needed by
`ErdosProblems.Erdos1058`.  Keeping this material in a separate file makes
the trust boundary explicit: every divisibility assertion below is a theorem
about integer matrices checked by Lean's kernel.
-/

namespace Erdos1058.BugeaudLaurent

open scoped BigOperators
open scoped fwdDiff

noncomputable section

/-- Rectangular Cauchy--Binet in the form used by the interpolation
determinant.  It is proved directly from the Leibniz expansion, so no rank or
field hypotheses are needed. -/
theorem det_mul_eq_sum_functions
    {R ι μ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (C : Matrix ι μ R) (V : Matrix μ ι R) :
    (C * V).det =
      ∑ f : ι → μ, (∏ i, C i (f i)) * (V.submatrix f id).det := by
  rw [← Matrix.det_transpose]
  rw [Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [← Matrix.det_transpose]
  rw [Matrix.det_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  simp only [mul_smul_comm]

/-- A repeated row kills the minor attached to a non-injective choice of
columns in `det_mul_eq_sum_functions`. -/
theorem det_submatrix_eq_zero_of_not_injective
    {R ι μ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (V : Matrix μ ι R) (f : ι → μ) (hf : ¬ Function.Injective f) :
    (V.submatrix f id).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_row_eq hne
  funext k
  simp [hij]

/-- Among `N` distinct natural-number indices, the least possible sum is
`0 + ... + (N-1)`.  This is the numerical core of the sharp Schur-determinant
exponent. -/
theorem sum_fin_injective_lower {N M : ℕ}
    (f : Fin N → Fin M) (hf : Function.Injective f) :
    (∑ i : Fin N, i.val) ≤ ∑ i : Fin N, (f i).val := by
  let g : Fin N → ℤ := fun i => (f i).val
  have hg : Function.Injective g := by
    intro i j hij
    apply hf
    apply Fin.ext
    change ((f i).val : ℤ) = (f j).val at hij
    exact_mod_cast hij
  let s : Finset ℤ := Finset.univ.image g
  have hs : ∑ n ∈ Finset.range s.card, ((0 : ℤ) + n) ≤ ∑ x ∈ s, x :=
    Finset.sum_range_le_sum (by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      simp [g])
  have hcard : s.card = N := by
    simp [s, Finset.card_image_of_injective _ hg]
  rw [hcard] at hs
  simp only [zero_add] at hs
  have himage : (∑ x ∈ s, x) = ∑ i : Fin N, g i := by
    simp [s, Finset.sum_image, hg]
  rw [himage] at hs
  have hs' : (∑ n ∈ Finset.range N, (n : ℤ)) ≤
      ∑ i : Fin N, ((f i).val : ℤ) := by
    simpa [g] using hs
  have hsnat : (∑ n ∈ Finset.range N, n) ≤
      ∑ i : Fin N, (f i).val := by
    have hs'' : ((∑ n ∈ Finset.range N, n : ℕ) : ℤ) ≤
        ((∑ i : Fin N, (f i).val : ℕ) : ℤ) := by
      simpa only [Nat.cast_sum] using hs'
    exact_mod_cast hs''
  have hleft : (∑ i : Fin N, i.val) = ∑ n ∈ Finset.range N, n := by
    exact Fin.sum_univ_eq_sum_range (fun n => n) N
  rw [hleft]
  exact hsnat

/-- Sharp determinant divisibility after a finite-difference factorization.
The `m-k` divisibility of the coefficient matrix and the least-sum property
of injective column choices combine through Cauchy--Binet. -/
theorem det_mul_pow_dvd
    {N M E : ℕ} (base : ℤ) (rowDegree : Fin N → ℕ)
    (hbase : E + (∑ i : Fin N, rowDegree i) ≤ ∑ i : Fin N, i.val)
    (C : Matrix (Fin N) (Fin M) ℤ) (V : Matrix (Fin M) (Fin N) ℤ)
    (hC : ∀ i m, base ^ (m.val - rowDegree i) ∣ C i m) :
    base ^ E ∣ (C * V).det := by
  rw [det_mul_eq_sum_functions]
  apply Finset.dvd_sum
  intro f _
  by_cases hf : Function.Injective f
  · have hsumf := sum_fin_injective_lower f hf
    have hpoint : ∀ i : Fin N,
        (f i).val ≤ rowDegree i + ((f i).val - rowDegree i) := by
      intro i
      omega
    have hsums : (∑ i : Fin N, (f i).val) ≤
        (∑ i : Fin N, rowDegree i) +
          ∑ i : Fin N, ((f i).val - rowDegree i) := by
      calc
        _ ≤ ∑ i : Fin N,
            (rowDegree i + ((f i).val - rowDegree i)) :=
          Finset.sum_le_sum fun i _ => hpoint i
        _ = _ := by rw [Finset.sum_add_distrib]
    have hE : E ≤ ∑ i : Fin N, ((f i).val - rowDegree i) := by
      omega
    have hprod : base ^ (∑ i : Fin N,
        ((f i).val - rowDegree i)) ∣ ∏ i : Fin N, C i (f i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hC i (f i)
    have hpow : base ^ E ∣
        base ^ (∑ i : Fin N, ((f i).val - rowDegree i)) :=
      pow_dvd_pow base hE
    exact dvd_mul_of_dvd_left (hpow.trans hprod) _
  · rw [det_submatrix_eq_zero_of_not_injective V f hf, mul_zero]
    exact dvd_zero _

/-- Cauchy--Binet divisibility with an arbitrary entrywise exponent.  The
only combinatorial input needed is a lower bound for the exponent sum along
every injective choice of coefficient columns. -/
theorem det_mul_pow_dvd_of_injective_sum
    {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ]
    (base : ℤ) (E : ℕ) (exponent : ι → μ → ℕ)
    (C : Matrix ι μ ℤ) (V : Matrix μ ι ℤ)
    (hsum : ∀ f : ι → μ, Function.Injective f →
      E ≤ ∑ i, exponent i (f i))
    (hC : ∀ i m, base ^ exponent i m ∣ C i m) :
    base ^ E ∣ (C * V).det := by
  rw [det_mul_eq_sum_functions]
  apply Finset.dvd_sum
  intro f _
  by_cases hf : Function.Injective f
  · have hprod : base ^ (∑ i, exponent i (f i)) ∣ ∏ i, C i (f i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => hC i (f i)
    exact dvd_mul_of_dvd_left ((pow_dvd_pow base (hsum f hf)).trans hprod) _
  · rw [det_submatrix_eq_zero_of_not_injective V f hf, mul_zero]
    exact dvd_zero _

/-- The binomial-exponential functions used as the rows of the Schur
interpolation determinant. -/
def binomialExponential (d : ℤ) (k x : ℕ) : ℤ :=
  (x.choose k : ℤ) * d ^ x

lemma fwdDiff_binomialExponential_zero (d : ℤ) :
    Δ_[1] (binomialExponential d 0) =
      (d - 1) • binomialExponential d 0 := by
  funext x
  simp [fwdDiff, binomialExponential, pow_succ]
  ring

lemma fwdDiff_binomialExponential_succ (d : ℤ) (k : ℕ) :
    Δ_[1] (binomialExponential d (k + 1)) =
      (d - 1) • binomialExponential d (k + 1) +
        d • binomialExponential d k := by
  funext x
  simp only [fwdDiff, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    binomialExponential, pow_succ]
  rw [Nat.choose_succ_succ']
  push_cast
  ring

/-- The `m`-th Newton coefficient of `choose x k * d^x` contains the
factor `(d-1)^(m-k)`.  This recurrence is the integral form of the Schur
polynomial gain responsible for the sharp p-adic constant. -/
theorem pow_sub_dvd_fwdDiff_iter_binomialExponential
    (d : ℤ) (m k x : ℕ) :
    (d - 1) ^ (m - k) ∣ Δ_[1] ^[m] (binomialExponential d k) x := by
  induction m generalizing k x with
  | zero => simp
  | succ m ih =>
      by_cases hkm : k ≤ m
      · cases k with
        | zero =>
            rw [Function.iterate_succ_apply, fwdDiff_binomialExponential_zero]
            rw [fwdDiff_iter_const_smul]
            simp only [Pi.smul_apply, smul_eq_mul, Nat.sub_zero, pow_succ]
            simpa [mul_comm] using mul_dvd_mul_left (d - 1) (ih 0 x)
        | succ k =>
            rw [Function.iterate_succ_apply, fwdDiff_binomialExponential_succ]
            rw [fwdDiff_iter_add, fwdDiff_iter_const_smul,
              fwdDiff_iter_const_smul]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have hk : k ≤ m := by omega
            have hfirst : (d - 1) ^ (m - k) ∣
                (d - 1) * Δ_[1] ^[m]
                  (binomialExponential d (k + 1)) x := by
              have hi := ih (k + 1) x
              have heq : m - k = (m - (k + 1)) + 1 := by omega
              rw [heq, pow_succ]
              simpa [mul_comm] using mul_dvd_mul_left (d - 1) hi
            have hsecond : (d - 1) ^ (m - k) ∣
                d * Δ_[1] ^[m] (binomialExponential d k) x :=
              dvd_mul_of_dvd_right (ih k x) d
            simpa only [Nat.succ_sub_succ_eq_sub] using hfirst.add hsecond
      · have hzero : m + 1 - k = 0 := by omega
        rw [hzero, pow_zero]
        exact one_dvd _

/-- If `d` is congruent to one modulo `2^v`, then the same Newton
coefficient contains `2^(v*(m-k))`. -/
theorem two_pow_mul_sub_dvd_fwdDiff_iter_binomialExponential
    (d : ℤ) (v m k x : ℕ) (hd : (2 : ℤ) ^ v ∣ d - 1) :
    (2 : ℤ) ^ (v * (m - k)) ∣
      Δ_[1] ^[m] (binomialExponential d k) x := by
  have hpow : ((2 : ℤ) ^ v) ^ (m - k) ∣ (d - 1) ^ (m - k) :=
    pow_dvd_pow_of_dvd hd _
  rw [← pow_mul] at hpow
  exact hpow.trans (pow_sub_dvd_fwdDiff_iter_binomialExponential d m k x)

/-- Finite Gregory--Newton expansion, with the coefficient sum padded to
the ambient finite interval. -/
theorem newton_sum_fin {M : ℕ} (f : ℕ → ℤ) (x : Fin M) :
    f x.val = ∑ m : Fin M,
      (x.val.choose m.val : ℤ) * Δ_[1] ^[m.val] f 0 := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) f x.val 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h
  rw [Fin.sum_univ_eq_sum_range
    (fun m : ℕ => (x.val.choose m : ℤ) * Δ_[1] ^[m] f 0) M]
  calc
    f x.val = ∑ m ∈ Finset.range (x.val + 1),
        (x.val.choose m : ℤ) * Δ_[1] ^[m] f 0 := h
    _ = ∑ m ∈ Finset.range M,
        (x.val.choose m : ℤ) * Δ_[1] ^[m] f 0 := by
      apply Finset.sum_subset
        (Finset.range_mono (Nat.succ_le_iff.mpr x.isLt))
      intro m _ hmx
      simp only [Finset.mem_range, not_lt] at hmx
      have hchoose : x.val.choose m = 0 := Nat.choose_eq_zero_of_lt hmx
      simp [hchoose]

/-- Determinant form of the sharp Schur/Newton divisibility.  Each row may
have its own exponential base, provided every base is one modulo the same
power of two. -/
theorem two_pow_mul_dvd_det_binomialExponential
    {N M E v : ℕ} (rowDegree : Fin N → ℕ)
    (hbase : E + (∑ i : Fin N, rowDegree i) ≤ ∑ i : Fin N, i.val)
    (d : Fin N → ℤ) (hd : ∀ i, (2 : ℤ) ^ v ∣ d i - 1)
    (x : Fin N → Fin M) :
    (2 : ℤ) ^ (v * E) ∣
      (Matrix.of fun i j => binomialExponential (d i) (rowDegree i) (x j)).det := by
  let C : Matrix (Fin N) (Fin M) ℤ := fun i m =>
    Δ_[1] ^[m.val] (binomialExponential (d i) (rowDegree i)) 0
  let V : Matrix (Fin M) (Fin N) ℤ := fun m j => (x j).val.choose m.val
  have hmatrix : Matrix.of (fun i j =>
      binomialExponential (d i) (rowDegree i) (x j)) = C * V := by
    ext i j
    rw [Matrix.mul_apply]
    have hnewton := newton_sum_fin
      (binomialExponential (d i) (rowDegree i)) (x j)
    simp only [C, V]
    simpa [mul_comm] using hnewton
  rw [hmatrix]
  have hdiv : ((2 : ℤ) ^ v) ^ E ∣ (C * V).det := by
    apply det_mul_pow_dvd ((2 : ℤ) ^ v) rowDegree hbase C V
    intro i m
    have hi := two_pow_mul_sub_dvd_fwdDiff_iter_binomialExponential
      (d i) v m.val (rowDegree i) 0 (hd i)
    simpa [C, pow_mul] using hi
  simpa [pow_mul] using hdiv

/-- A finite set of distinct natural numbers has sum at least
`0 + ⋯ + (s.card - 1)`. -/
theorem sum_range_card_le_sum_of_injOn
    {α : Type*} [DecidableEq α] (s : Finset α) (g : α → ℕ)
    (hg : Set.InjOn g s) :
    (∑ n ∈ Finset.range s.card, n) ≤ ∑ a ∈ s, g a := by
  let h : α → ℤ := fun a => g a
  have hh : Set.InjOn h s := by
    intro a ha b hb hab
    apply hg ha hb
    dsimp only [h] at hab
    exact Int.ofNat_inj.mp hab
  let t : Finset ℤ := s.image h
  have ht : ∑ n ∈ Finset.range t.card, ((0 : ℤ) + n) ≤ ∑ z ∈ t, z :=
    Finset.sum_range_le_sum (by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨a, _, rfl⟩ := hz
      simp [h])
  have hcard : t.card = s.card := Finset.card_image_of_injOn hh
  rw [hcard] at ht
  simp only [zero_add] at ht
  have himage : (∑ z ∈ t, z) = ∑ a ∈ s, h a := by
    exact Finset.sum_image hh
  rw [himage] at ht
  have ht' : (((∑ n ∈ Finset.range s.card, n) : ℕ) : ℤ) ≤
      (((∑ a ∈ s, g a) : ℕ) : ℤ) := by
    simpa only [Nat.cast_sum, h] using ht
  exact_mod_cast ht'

/-- Indices of columns at which the structured interpolation formula is
replaced by an arbitrary error column. -/
abbrev InterpolationErrorIndex {N : ℕ} (structured : Finset (Fin N)) :=
  {j : Fin N // j ∉ structured}

/-- An injective Cauchy--Binet selection has at least `structured.card`
Newton-coefficient indices: there are only as many error indices as
unstructured columns. -/
theorem structured_card_le_left_rows
    {N M : ℕ} (structured : Finset (Fin N))
    (f : Fin N → Sum (Fin M) (InterpolationErrorIndex structured))
    (hf : Function.Injective f) :
    structured.card ≤
      (Finset.univ.filter fun r => (f r).isLeft).card := by
  classical
  let left : Finset (Fin N) :=
    Finset.univ.filter fun r => (f r).isLeft
  let right : Finset (Fin N) :=
    Finset.univ.filter fun r => (f r).isRight
  let g : {r // r ∈ right} → InterpolationErrorIndex structured := fun r => by
    have hr : r.val ∈ Finset.univ.filter (fun r => (f r).isRight) := by
      simpa only [right] using r.property
    exact (f r.val).getRight (Finset.mem_filter.mp hr).2
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hf
    have ha : f a.val = Sum.inr (g a) :=
      Sum.eq_right_iff_getRight_eq.mpr ⟨_, rfl⟩
    have hb : f b.val = Sum.inr (g b) :=
      Sum.eq_right_iff_getRight_eq.mpr ⟨_, rfl⟩
    rw [ha, hb, hab]
  have hright : right.card ≤ N - structured.card := by
    have hc := Fintype.card_le_of_injective g hg
    have hc' : right.card ≤
        Fintype.card (InterpolationErrorIndex structured) := by
      simpa only [Fintype.card_coe] using hc
    have herror : Fintype.card (InterpolationErrorIndex structured) =
        N - structured.card := by
      simpa [InterpolationErrorIndex] using
        (Fintype.card_subtype_compl (fun j : Fin N => j ∈ structured))
    rw [herror] at hc'
    exact hc'
  have hpartition : left.card + right.card = N := by
    simpa [left, right] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin N)))
        (fun r => (f r).isLeft))
  have hstructured : structured.card ≤ N := by
    simpa using Finset.card_le_univ structured
  change structured.card ≤ left.card
  omega

/-- The total Newton exponent along an injective mixed-column choice is
bounded below by the sharp triangular-number exponent. -/
theorem mixed_exponent_sum
    {N M E : ℕ} (structured : Finset (Fin N))
    (rowDegree : Fin N → ℕ)
    (hbase : E + 3 * (∑ r : Fin N, rowDegree r) ≤
      3 * (∑ t : Fin structured.card, t.val))
    (f : Fin N → Sum (Fin M) (InterpolationErrorIndex structured))
    (hf : Function.Injective f) :
    E ≤ ∑ r : Fin N, match f r with
      | Sum.inl m => 3 * (m.val - rowDegree r)
      | Sum.inr _ => 0 := by
  classical
  let left : Finset (Fin N) :=
    Finset.univ.filter fun r => (f r).isLeft
  let degree : Fin N → ℕ := fun r => match f r with
    | Sum.inl m => m.val
    | Sum.inr _ => 0
  let remainder : Fin N → ℕ := fun r => match f r with
    | Sum.inl m => m.val - rowDegree r
    | Sum.inr _ => 0
  have hleftcard : structured.card ≤ left.card := by
    simpa only [left] using structured_card_le_left_rows structured f hf
  have hdegreeinj : Set.InjOn degree left := by
    intro a ha b hb hab
    rcases hfa : f a with m | e
    · rcases hfb : f b with m' | e'
      · apply hf
        have hmm : m = m' := by
          apply Fin.ext
          simpa [degree, hfa, hfb] using hab
        simp [hfa, hfb, hmm]
      · have hb' := hb
        simp [left, hfb] at hb'
    · have ha' := ha
      simp [left, hfa] at ha'
  have hdistinct := sum_range_card_le_sum_of_injOn left degree hdegreeinj
  have htriangular :
      (∑ n ∈ Finset.range structured.card, n) ≤
        ∑ n ∈ Finset.range left.card, n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hleftcard)
    intro n _ _
    omega
  have hfin : (∑ t : Fin structured.card, t.val) ≤
      ∑ r ∈ left, degree r := by
    rw [Fin.sum_univ_eq_sum_range (fun n => n) structured.card]
    exact htriangular.trans hdistinct
  have hsumdegree : (∑ r : Fin N, degree r) =
      ∑ r ∈ left, degree r := by
    symm
    dsimp only [left]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    rcases hfr : f r with m | e <;> simp [degree, hfr]
  have hpoint : ∀ r : Fin N,
      degree r ≤ rowDegree r + remainder r := by
    intro r
    rcases hfr : f r with m | e <;> simp [degree, remainder, hfr]
    omega
  have hsums : (∑ r : Fin N, degree r) ≤
      (∑ r : Fin N, rowDegree r) + ∑ r : Fin N, remainder r := by
    calc
      _ ≤ ∑ r : Fin N, (rowDegree r + remainder r) :=
        Finset.sum_le_sum fun r _ => hpoint r
      _ = _ := by rw [Finset.sum_add_distrib]
  have hcentral : E ≤ 3 * (∑ r : Fin N, remainder r) := by
    rw [hsumdegree] at hsums
    omega
  calc
    E ≤ ∑ r : Fin N, 3 * remainder r := by
      simpa only [Finset.mul_sum] using hcentral
    _ = ∑ r : Fin N, match f r with
        | Sum.inl m => 3 * (m.val - rowDegree r)
        | Sum.inr _ => 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rcases hfr : f r with m | e <;> simp [remainder, hfr]

def mixedCoefficient {N M : ℕ} (structured : Finset (Fin N))
    (rowDegree : Fin N → ℕ) (d : Fin N → ℤ)
    (H : Matrix (Fin N) (Fin N) ℤ) :
    Matrix (Fin N) (Sum (Fin M) (InterpolationErrorIndex structured)) ℤ :=
  fun i m => match m with
    | Sum.inl m => Δ_[1] ^[m.val]
        (binomialExponential (d i) (rowDegree i)) 0
    | Sum.inr j => H i j.val

def mixedEvaluation {N M : ℕ} (structured : Finset (Fin N))
    (x : Fin N → Fin M) :
    Matrix (Sum (Fin M) (InterpolationErrorIndex structured)) (Fin N) ℤ :=
  fun m j => match m with
    | Sum.inl m => if j ∈ structured then (x j).val.choose m.val else 0
    | Sum.inr a => if a.val = j then 1 else 0

noncomputable def mixedProduct {N M : ℕ} (structured : Finset (Fin N))
    (rowDegree : Fin N → ℕ) (d : Fin N → ℤ) (x : Fin N → Fin M)
    (H : Matrix (Fin N) (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ := by
  classical
  exact fun i j =>
    ∑ m : Sum (Fin M) (InterpolationErrorIndex structured),
      mixedCoefficient (M := M) structured rowDegree d H i m *
        mixedEvaluation structured x m j

theorem mixed_factorization
    {N M : ℕ} (structured : Finset (Fin N))
    (rowDegree : Fin N → ℕ) (d : Fin N → ℤ) (x : Fin N → Fin M)
    (H : Matrix (Fin N) (Fin N) ℤ) :
    Matrix.of (fun i j => if j ∈ structured then
      binomialExponential (d i) (rowDegree i) (x j) else H i j) =
        mixedProduct structured rowDegree d x H := by
  classical
  ext i j
  simp only [Matrix.of_apply, mixedProduct, mixedCoefficient, mixedEvaluation]
  simp only [Fintype.sum_sum_type]
  by_cases hj : j ∈ structured
  · simp only [hj, ↓reduceIte]
    rw [newton_sum_fin (binomialExponential (d i) (rowDegree i)) (x j)]
    simp only [mul_comm]
    have herr : (∑ a : InterpolationErrorIndex structured,
        H i a.val * if a.val = j then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have hne : a.val ≠ j := by
        intro heq
        exact a.property (heq ▸ hj)
      simp [hne]
    rw [herr, add_zero]
  · simp only [hj, ↓reduceIte, mul_zero, Finset.sum_const_zero, zero_add]
    symm
    rw [Fintype.sum_eq_single
      (⟨j, hj⟩ : InterpolationErrorIndex structured)]
    · simp
    · intro a hane
      have hne : a.val ≠ j := by
        intro heq
        apply hane
        exact Subtype.ext heq
      simp [hne]

/-- The mixed-column form of the sharp Schur determinant divisibility.
Structured columns are binomial-exponential evaluations; all remaining
columns may be arbitrary. -/
theorem two_pow_dvd_det_mixed
    {N M E : ℕ} (structured : Finset (Fin N))
    (rowDegree : Fin N → ℕ)
    (hbase : E + 3 * (∑ r : Fin N, rowDegree r) ≤
      3 * (∑ t : Fin structured.card, t.val))
    (d : Fin N → ℤ) (hd : ∀ r, (2 : ℤ) ^ 3 ∣ d r - 1)
    (x : Fin N → Fin M) (H : Matrix (Fin N) (Fin N) ℤ) :
    (2 : ℤ) ^ E ∣
      (Matrix.of fun r j => if j ∈ structured then
        binomialExponential (d r) (rowDegree r) (x j) else H r j).det := by
  classical
  rw [mixed_factorization]
  change (2 : ℤ) ^ E ∣
    (mixedCoefficient (M := M) structured rowDegree d H *
      mixedEvaluation structured x).det
  apply det_mul_pow_dvd_of_injective_sum (2 : ℤ) E
    (fun r m => match m with
      | Sum.inl m => 3 * (m.val - rowDegree r)
      | Sum.inr _ => 0)
  · intro f hf
    exact mixed_exponent_sum structured rowDegree hbase f hf
  · intro r m
    rcases m with m | e
    · simpa [mixedCoefficient] using
        (two_pow_mul_sub_dvd_fwdDiff_iter_binomialExponential
          (d r) 3 m.val (rowDegree r) 0 (hd r))
    · simp [mixedCoefficient]

/-- Row-scaled mixed-column divisibility.  The odd row factors used to clear
the denominators in the rational interpolation determinant do not affect the
Newton exponent; in fact no parity assumption on the scale is needed. -/
theorem two_pow_dvd_det_mixed_scaled
    {N M E : ℕ} (structured : Finset (Fin N))
    (rowDegree : Fin N → ℕ)
    (hbase : E + 3 * (∑ r : Fin N, rowDegree r) ≤
      3 * (∑ t : Fin structured.card, t.val))
    (d scale : Fin N → ℤ) (hd : ∀ r, (2 : ℤ) ^ 3 ∣ d r - 1)
    (x : Fin N → Fin M) (H : Matrix (Fin N) (Fin N) ℤ) :
    (2 : ℤ) ^ E ∣
      (Matrix.of fun r j => if j ∈ structured then
        scale r * binomialExponential (d r) (rowDegree r) (x j)
        else H r j).det := by
  classical
  let C : Matrix (Fin N)
      (Sum (Fin M) (InterpolationErrorIndex structured)) ℤ := fun r m =>
    match m with
    | Sum.inl m => scale r * Δ_[1] ^[m.val]
        (binomialExponential (d r) (rowDegree r)) 0
    | Sum.inr j => H r j.val
  let V : Matrix (Sum (Fin M) (InterpolationErrorIndex structured))
      (Fin N) ℤ := fun m j =>
    match m with
    | Sum.inl m => if j ∈ structured then (x j).val.choose m.val else 0
    | Sum.inr a => if a.val = j then 1 else 0
  have hmatrix : Matrix.of (fun r j => if j ∈ structured then
      scale r * binomialExponential (d r) (rowDegree r) (x j)
      else H r j) = C * V := by
    ext r j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [Fintype.sum_sum_type]
    simp only [C, V]
    by_cases hj : j ∈ structured
    · simp only [hj, ↓reduceIte]
      rw [newton_sum_fin (binomialExponential (d r) (rowDegree r)) (x j)]
      rw [Finset.mul_sum]
      have herr : (∑ a : InterpolationErrorIndex structured,
          H r a.val * if a.val = j then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        have hne : a.val ≠ j := by
          intro heq
          exact a.property (heq ▸ hj)
        simp [hne]
      rw [herr, add_zero]
      apply Finset.sum_congr rfl
      intro m _
      ring
    · simp only [hj, ↓reduceIte, mul_zero, Finset.sum_const_zero, zero_add]
      symm
      rw [Fintype.sum_eq_single
        (⟨j, hj⟩ : InterpolationErrorIndex structured)]
      · simp
      · intro a hane
        have hne : a.val ≠ j := by
          intro heq
          apply hane
          exact Subtype.ext heq
        simp [hne]
  rw [hmatrix]
  apply det_mul_pow_dvd_of_injective_sum (2 : ℤ) E
    (fun r m => match m with
      | Sum.inl m => 3 * (m.val - rowDegree r)
      | Sum.inr _ => 0)
  · intro f hf
    exact mixed_exponent_sum structured rowDegree hbase f hf
  · intro r m
    rcases m with m | e
    · exact dvd_mul_of_dvd_right
        (two_pow_mul_sub_dvd_fwdDiff_iter_binomialExponential
          (d r) 3 m.val (rowDegree r) 0 (hd r)) (scale r)
    · simp [C]

/-- Replace the columns in `s` by columns of `B`, and all remaining columns
by columns of `H`. -/
def selectColumns {N : ℕ} (s : Finset (Fin N))
    (B H : Matrix (Fin N) (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => if j ∈ s then B i j else H i j

/-- Column-wise multilinearity of the determinant, with the common scalar on
the error columns collected as an exact power. -/
theorem det_add_smul_eq_sum_finset {N : ℕ}
    (z : ℤ) (B H : Matrix (Fin N) (Fin N) ℤ) :
    (B + z • H).det = ∑ s : Finset (Fin N),
      z ^ (N - s.card) * (selectColumns s B H).det := by
  classical
  rw [← Matrix.det_transpose]
  rw [Matrix.transpose_add, Matrix.transpose_smul]
  have h := (Matrix.detRowAlternating (n := Fin N) (R := ℤ)).map_add_univ
    B.transpose (z • H.transpose)
  change (B.transpose + z • H.transpose).det = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro s _
  let c : Fin N → ℤ := fun j => if j ∈ s then 1 else z
  let M : Matrix (Fin N) (Fin N) ℤ := fun j i =>
    if j ∈ s then B.transpose j i else H.transpose j i
  have hpw : ∏ j : Fin N, c j = z ^ (N - s.card) := by
    simp only [c]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul,
      Finset.prod_const]
    have hcompl : (Finset.univ.filter fun j : Fin N => j ∉ s) = sᶜ := by
      ext j
      simp
    rw [hcompl, Finset.card_compl, Fintype.card_fin]
  have hpiece : s.piecewise B.transpose (z • H.transpose) =
      fun j => c j • M j := by
    funext j i
    simp only [Finset.piecewise]
    by_cases hj : j ∈ s
    · simp [c, M, hj]
    · simp [c, M, hj]
  rw [hpiece]
  rw [(Matrix.detRowAlternating (n := Fin N) (R := ℤ)).map_smul_univ]
  change (∏ j : Fin N, c j) * M.det = _
  rw [hpw]
  congr 1
  calc
    M.det = M.transpose.det := (Matrix.det_transpose M).symm
    _ = (selectColumns s B H).det := by
      congr 1

/-- Perturbation form of the Schur/Newton determinant estimate.  The first
alternative in `hbudget` pays for a term entirely with its congruence
factor.  The second combines the remaining factor with the mixed-column
Schur exponent. -/
theorem two_pow_dvd_det_perturbed_mixed_scaled
    {N M E T : ℕ} (rowDegree : Fin N → ℕ)
    (d scale : Fin N → ℤ) (hd : ∀ r, (2 : ℤ) ^ 3 ∣ d r - 1)
    (x : Fin N → Fin M) (H : Matrix (Fin N) (Fin N) ℤ)
    (hbudget : ∀ structured : Finset (Fin N),
      E ≤ T * (N - structured.card) ∨
        E - T * (N - structured.card) +
          3 * (∑ r : Fin N, rowDegree r) ≤
            3 * (∑ t : Fin structured.card, t.val)) :
    (2 : ℤ) ^ E ∣
      (Matrix.of (fun r j =>
        scale r * binomialExponential (d r) (rowDegree r) (x j)) +
          (2 : ℤ) ^ T • H).det := by
  classical
  rw [det_add_smul_eq_sum_finset]
  apply Finset.dvd_sum
  intro structured _
  rw [← pow_mul]
  by_cases hcoeff : E ≤ T * (N - structured.card)
  · exact dvd_mul_of_dvd_left (pow_dvd_pow 2 hcoeff) _
  · have hbase := (hbudget structured).resolve_left hcoeff
    have hmixed := two_pow_dvd_det_mixed_scaled structured rowDegree
      hbase d scale hd x H
    have hmixed' : (2 : ℤ) ^ (E - T * (N - structured.card)) ∣
        (selectColumns structured
          (Matrix.of fun r j =>
            scale r * binomialExponential (d r) (rowDegree r) (x j)) H).det := by
      change (2 : ℤ) ^ (E - T * (N - structured.card)) ∣
        (Matrix.of fun r j => if j ∈ structured then
          scale r * binomialExponential (d r) (rowDegree r) (x j)
          else H r j).det
      exact hmixed
    have hcoeffle : T * (N - structured.card) ≤ E := by omega
    have hmul := mul_dvd_mul_left
      ((2 : ℤ) ^ (T * (N - structured.card))) hmixed'
    rw [← pow_add, Nat.add_sub_of_le hcoeffle] at hmul
    exact hmul

/-- If every entry in row `i` of an integer matrix contains the factor
`2 ^ e i`, then the determinant contains the product of all those factors,
hence `2` to the sum of the row exponents.  This is the elementary
factor-extraction step used after the interpolation determinant has been put
in finite-difference form. -/
theorem two_pow_sum_dvd_det_of_row_factors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (e : ι → ℕ)
    (hA : ∀ i j, (2 : ℤ) ^ e i ∣ A i j) :
    (2 : ℤ) ^ (∑ i, e i) ∣ A.det := by
  let B : Matrix ι ι ℤ := fun i j => A i j / (2 : ℤ) ^ e i
  have hentry : ∀ i j, A i j = (2 : ℤ) ^ e i * B i j := by
    intro i j
    exact (Int.ediv_mul_cancel (hA i j)).symm.trans (mul_comm _ _)
  have hmatrix : A = Matrix.of fun i j => (2 : ℤ) ^ e i * B i j := by
    ext i j
    exact hentry i j
  rw [hmatrix, Matrix.det_mul_column]
  refine ⟨B.det, ?_⟩
  rw [Finset.prod_pow_eq_pow_sum]

/-- A matrix whose reduction modulo `m` has zero determinant has determinant
divisible by `m`.  In the interpolation argument this packages the passage
from a rank drop modulo `2 ^ t` back to an integral divisibility statement. -/
theorem dvd_det_of_zmod_det_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (A : Matrix ι ι ℤ)
    (hdet : (A.map (Int.castRingHom (ZMod m))).det = 0) :
    (m : ℤ) ∣ A.det := by
  have hcast : ((A.det : ℤ) : ZMod m) = 0 := by
    change (Int.castRingHom (ZMod m)) A.det = 0
    rw [RingHom.map_det]
    exact hdet
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd A.det m).mp hcast

/-- The preceding reduction lemma at the powers of two used by the
`2`-adic determinant. -/
theorem two_pow_dvd_det_of_zmod_det_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (A : Matrix ι ι ℤ)
    (hdet : (A.map (Int.castRingHom (ZMod (2 ^ t)))).det = 0) :
    (2 : ℤ) ^ t ∣ A.det := by
  simpa using dvd_det_of_zmod_det_eq_zero (2 ^ t) A hdet

/-- A nonzero integer containing `2 ^ t` has ordinary absolute value at
least `2 ^ t`.  This is the elementary product-formula input for the rational
specialization. -/
theorem two_pow_le_natAbs_of_dvd {t : ℕ} {z : ℤ}
    (hz : z ≠ 0) (hdiv : (2 : ℤ) ^ t ∣ z) :
    2 ^ t ≤ z.natAbs := by
  obtain ⟨c, rfl⟩ := hdiv
  have hc : c ≠ 0 := by
    intro hc
    simp [hc] at hz
  rw [Int.natAbs_mul, Int.natAbs_pow]
  norm_num
  exact Int.natAbs_pos.mpr hc

/-- Logarithmic form of `two_pow_le_natAbs_of_dvd`. -/
theorem mul_log_two_le_log_natAbs_of_dvd {t : ℕ} {z : ℤ}
    (hz : z ≠ 0) (hdiv : (2 : ℤ) ^ t ∣ z) :
    (t : ℝ) * Real.log 2 ≤ Real.log z.natAbs := by
  have hnat := two_pow_le_natAbs_of_dvd hz hdiv
  have hreal : ((2 : ℝ) ^ t) ≤ (z.natAbs : ℝ) := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < 2 ^ t := by positivity
  have hlog := Real.log_le_log hpos hreal
  simpa [Real.log_pow] using hlog

end

end Erdos1058.BugeaudLaurent
