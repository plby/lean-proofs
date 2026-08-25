import Mathlib

/-! Basic definitions and elementary lemmas for Erdős problem 490.
Extracted from the existing formalization; no custom analytic axioms are imported. -/

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false

noncomputable section

namespace Erdos490

/-- Primes up to x -/
def primesUpTo (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime

def γ : ℝ := Real.eulerMascheroniConstant

/-- ψ(x) = Chebyshev's second function = ∑_{n ≤ x} Λ(n) -/
def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt n

open Finset BigOperators Nat Real

/-- S[p] = {s ∈ S : p ∣ s} -/
def sdiv (S : Finset ℕ) (p : ℕ) : Finset ℕ := S.filter (p ∣ ·)

/-- p⁻¹S[p] = {s/p : s ∈ S, p ∣ s} -/
def sinv (S : Finset ℕ) (p : ℕ) : Finset ℕ := (sdiv S p).image (· / p)

/-- A pair (A,B) is n-admissible if A,B ⊆ [n] and (a,b) ↦ ab is injective on A × B -/
def ProductAdmissible (n : ℕ) (A B : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ B ⊆ Finset.Icc 1 n ∧
  ∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
    a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂

/-- Y_{λ,k} = 2λ^k -/
def Y_val (lam : ℝ) (k : ℕ) : ℝ := 2 * lam ^ k

/-- Primes in [Y_{λ,k}, Y_{λ,k+1}), as a Finset. -/
def I_layer (lam : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.Ico ⌈Y_val lam k⌉₊ ⌈Y_val lam (k + 1)⌉₊).filter Nat.Prime

/-- N_{λ,k} = |I_{λ,k}| -/
def N_layer (lam : ℝ) (k : ℕ) : ℕ := (I_layer lam k).card

/-- M_{λ,k} = ∏_{p ≤ Y_{λ,k+1}} (1 - 1/p) -/
def M_layer (lam : ℝ) (k : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo (Y_val lam (k + 1)), (1 - 1 / (p : ℝ))

/-- E_{λ,k}(r) = max over T ⊆ I_{λ,k} with |T| ≤ r of ∏_{p∈T} (1-1/p)⁻¹ -/
def E_val (lam : ℝ) (k : ℕ) (r : ℕ) : ℝ :=
  ((I_layer lam k).powerset.filter (·.card ≤ r)).sup'
    ⟨∅, by simp [Finset.mem_filter, Finset.mem_powerset]⟩
    (fun T => ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹)

/-- D_{λ,m} = ∏_k E_{λ,k}(m_k) defined as exp(∑' log E_k(m_k)) -/
def D_val (lam : ℝ) (m : ℕ → ℕ) : ℝ :=
  Real.exp (∑' k, Real.log (E_val lam k (m k)))

/-- F_f(X) = ∑_{m ≤ X} f(m), for f : ℕ → ℝ -/
def F_count (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m

/-- H_f(X) = ∑_{m ≤ X} f(m)/m -/
def H_count (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m / (m : ℝ)

/-- L_f(X) = ∑_{m ≤ X} f(m) · log(m) -/
def L_count (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m * Real.log (m : ℝ)

/-- f is completely multiplicative with values in {0,1} -/
def CompMult01 (f : ℕ → ℝ) : Prop :=
  (∀ m, f m = 0 ∨ f m = 1) ∧
  f 1 = 1 ∧
  (∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f (a * b) = f a * f b)

/-- L_{λ,k}(A,B) = primes in I_{λ,k} dividing some element of both A and B -/
def L_common (lam : ℝ) (k : ℕ) (A B : Finset ℕ) : Finset ℕ :=
  (I_layer lam k).filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)

/-- P_S(n,λ,k) = primes p with Y_{λ,k+1} < p ≤ n/Y_{λ,k} and S[p] = ∅ -/
def P_sieve (n : ℕ) (lam : ℝ) (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  ((Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime).filter
    (fun p => ¬(sdiv S p).Nonempty)

/-- Π_S(n,λ,k) = ∏_{p ∈ P_S(n,λ,k)} (1 - 1/p) -/
def Pi_sieve (n : ℕ) (lam : ℝ) (k : ℕ) (S : Finset ℕ) : ℝ :=
  ∏ p ∈ P_sieve n lam k S, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 800000 in
-- The finite supremum estimate needs extra heartbeats for generated simplification.

/-- E_val is always ≥ 1 (achieved by the empty subset) -/
lemma E_val_ge_one (lam : ℝ) (k : ℕ) (r : ℕ) : 1 ≤ E_val lam k r := by
  refine le_trans ?_ ( Finset.le_sup' _ <| show ∅ ∈ _ from ?_ ) <;> norm_num

/-- A product over a subset T ⊆ I_k with |T| ≤ r is bounded by E_val -/
lemma prod_le_E_val (lam : ℝ) (k : ℕ) (r : ℕ) (T : Finset ℕ)
    (hT : T ⊆ I_layer lam k) (hcard : T.card ≤ r) :
    ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹ ≤ E_val lam k r := by
  refine le_trans ?_ ( Finset.le_sup' _ <| show T ∈ Finset.filter ( fun T => #T ≤ r ) ( Finset.powerset ( I_layer lam k ) ) from ?_ ) <;> simp_all +decide [ Finset.subset_iff ]

/-
Finite partial product (over a Finset) is bounded by D_val
-/
lemma partial_prod_le_D_val (lam : ℝ) (m : ℕ → ℕ)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
    (S : Finset ℕ) :
    ∏ j ∈ S, E_val lam j (m j) ≤ D_val lam m := by
  have hsum :
      ∑ j ∈ S, Real.log (E_val lam j (m j)) ≤
        ∑' k, Real.log (E_val lam k (m k)) := by
    exact Summable.sum_le_tsum _ (fun _ _ => Real.log_nonneg <| E_val_ge_one _ _ _) hsumm
  calc
    ∏ j ∈ S, E_val lam j (m j)
        = Real.exp (∑ j ∈ S, Real.log (E_val lam j (m j))) := by
          rw [Real.exp_sum]
          exact Finset.prod_congr rfl fun _ _ =>
            (Real.exp_log (lt_of_lt_of_le zero_lt_one (E_val_ge_one _ _ _))).symm
    _ ≤ Real.exp (∑' k, Real.log (E_val lam k (m k))) :=
          Real.exp_le_exp.mpr hsum
    _ = D_val lam m := rfl

/-
The primes in (Y_{k+1}, n] that are common to A,B can be decomposed by layer
-/
lemma layer_decomp_common_primes (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (n : ℕ)
    (A B : Finset ℕ) :
    let P := ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ n).filter Nat.Prime).filter
        (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)
    ∀ p ∈ P, ∃ j, k < j ∧ p ∈ I_layer lam j := by
  intro P p hpP
  obtain ⟨j, hj⟩ : ∃ j, Y_val lam j ≤ p ∧ p < Y_val lam (j + 1) := by
    have h_exists_j : ∃ j, Y_val lam j ≤ p ∧ p < Y_val lam (j + 1) := by
      have h_unbounded : ∀ M : ℝ, ∃ j, Y_val lam j > M := by
        exact fun M => by rcases pow_unbounded_of_one_lt ( M / 2 ) hlam with ⟨ j, hj ⟩ ; exact ⟨ j, by rw [ Y_val ] ; linarith ⟩ ;
      contrapose! h_unbounded;
      use p;
      intro j; induction j <;> simp_all +decide [ Y_val ] ;
      exact Nat.Prime.two_le ( Finset.mem_filter.mp ( Finset.mem_filter.mp hpP |>.1 ) |>.2 );
    exact h_exists_j;
  have hj_gt_k : j > k := by
    simp +zetaDelta at *;
    contrapose! hpP;
    intro h₁ h₂; rw [ Nat.floor_lt ] at h₁ <;> linarith [ show ( Y_val lam ( k + 1 ) :ℝ ) ≥ Y_val lam ( j + 1 ) from mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ hlam.le ( by linarith ) ) zero_le_two ] ;
  use j;
  simp +zetaDelta at *;
  exact ⟨ hj_gt_k, Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ Nat.ceil_le.mpr hj.1, Nat.lt_ceil.mpr hj.2 ⟩, hpP.1.2 ⟩ ⟩

/-
Key product inequality for small_interval_case:
    ∏_{p∈P_A} · ∏_{p∈P_B} ≤ ∏_{p∈P_A∪P_B}
-/
lemma prod_union_le_of_le_one {P_A P_B : Finset ℕ}
    (hA : ∀ p ∈ P_A, Nat.Prime p) (hB : ∀ p ∈ P_B, Nat.Prime p) :
    (∏ p ∈ P_A, (1 - 1 / (p : ℝ))) * (∏ p ∈ P_B, (1 - 1 / (p : ℝ))) ≤
    ∏ p ∈ P_A ∪ P_B, (1 - 1 / (p : ℝ)) := by
  have h_prod_union_inter : (∏ p ∈ P_A, (1 - 1 / (p : ℝ))) * (∏ p ∈ P_B, (1 - 1 / (p : ℝ))) = (∏ p ∈ P_A ∪ P_B, (1 - 1 / (p : ℝ))) * (∏ p ∈ P_A ∩ P_B, (1 - 1 / (p : ℝ))) := by
    rw [ ← Finset.prod_union_inter ];
  exact h_prod_union_inter ▸ mul_le_of_le_one_right ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) ( Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => sub_le_self _ <| by positivity )

/-
Elements of sinv S p are ≤ n/p when S ⊆ Icc 1 n
-/
lemma sinv_le_div {S : Finset ℕ} {p n : ℕ} (hS : S ⊆ Finset.Icc 1 n) (_hp : Nat.Prime p)
    {x : ℕ} (hx : x ∈ sinv S p) : x ≤ n / p := by
  obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hx;
  exact Nat.div_le_div_right ( Finset.mem_Icc.mp ( hS ( Finset.mem_filter.mp hs |>.1 ) ) |>.2 )

/-
Elements of sinv S p are ≥ 1 when S ⊆ Icc 1 n
-/
lemma sinv_pos {S : Finset ℕ} {n p : ℕ} (hS : S ⊆ Finset.Icc 1 n) (hp : Nat.Prime p)
    {x : ℕ} (hx : x ∈ sinv S p) : 1 ≤ x := by
  obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hx;
  exact Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp ( hS ( Finset.mem_filter.mp hs |>.1 ) ) |>.1 ) ( Finset.mem_filter.mp hs |>.2 ) ) hp.pos

/-
If p ∈ I_layer lam k and r ∈ P_sieve n lam k S (so r > Y_{k+1} > p),
    then r does not divide any element of sinv S p.
-/
lemma sieve_prime_not_dvd_sinv {S : Finset ℕ} {n : ℕ} {lam : ℝ} {k : ℕ}
    (_hS : S ⊆ Finset.Icc 1 n) (_hlam : 1 < lam)
    {p : ℕ} (_hp : p ∈ I_layer lam k) (_hp_sdiv : (sdiv S p).Nonempty)
    {r : ℕ} (hr : r ∈ P_sieve n lam k S)
    {x : ℕ} (hx : x ∈ sinv S p) : ¬(r ∣ x) := by
  unfold sinv at hx; simp_all +decide [ Finset.subset_iff ] ;
  obtain ⟨ a, ha, rfl ⟩ := hx; simp_all +decide [ sdiv, P_sieve ] ;
  exact fun h => hr.2 ha.1 ( dvd_of_mul_left_dvd h )

/-
M_layer identity: M_k · ∏_{Y_{k+1} < p ≤ X, prime} (1-1/p) = ∏_{p ≤ X, prime} (1-1/p)
    when the interval (Y_{k+1}, X] contains all primes in that range
-/
lemma M_layer_prod_eq {lam : ℝ} {k : ℕ} {X : ℕ}
    (hX : ⌊Y_val lam (k + 1)⌋₊ ≤ X) :
    M_layer lam k * ∏ p ∈ (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ X).filter Nat.Prime,
      (1 - 1 / (p : ℝ)) =
    ∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ)) := by
  unfold M_layer primesUpTo;
  norm_num [ Finset.prod_filter ];
  rw [ ← Finset.prod_union ];
  · rcongr x ; norm_num;
    exact ⟨ fun h => h.elim ( fun h => h.trans hX ) fun h => h.2, fun h => or_iff_not_imp_left.mpr fun h' => ⟨ not_le.mp h', h ⟩ ⟩;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp hx₁, Finset.mem_Ioc.mp hx₂ ] ;

/-
The union ⋃_{p∈L} p⁻¹S[p] is contained in the sifted set for sieve_bound application
-/
lemma biUnion_sinv_subset_sifted {S : Finset ℕ} {n : ℕ} {lam : ℝ} {k : ℕ}
    (hS : S ⊆ Finset.Icc 1 n) (hlam : 1 < lam)
    {L : Finset ℕ} (hL : L ⊆ (I_layer lam k).filter (fun p => (sdiv S p).Nonempty)) :
    L.biUnion (sinv S ·) ⊆
      (Finset.range (⌊(n : ℝ) / Y_val lam k⌋₊ + 1)).filter
        (fun m => m ≥ 1 ∧ ∀ r ∈ P_sieve n lam k S, ¬(r ∣ m)) := by
  intro m hm;
  simp +zetaDelta at *;
  refine ⟨ ?_, ?_, ?_ ⟩;
  · obtain ⟨ p, hp₁, hp₂ ⟩ := hm;
    have h_div : m ≤ n / p := by
      apply sinv_le_div hS (by
      exact Finset.mem_filter.mp ( hL hp₁ |> Finset.mem_filter.mp |>.1 ) |>.2) hp₂;
    refine le_trans h_div ( Nat.le_floor ?_ );
    rw [ le_div_iff₀ ] <;> norm_cast;
    · have h_div : (p : ℝ) ≥ Y_val lam k := by
        have := hL hp₁; simp_all +decide [ I_layer ] ;
      exact le_trans ( mul_le_mul_of_nonneg_left h_div <| Nat.cast_nonneg _ ) <| by norm_cast; nlinarith [ Nat.div_mul_le_self n p ] ;
    · exact mul_pos zero_lt_two ( pow_pos ( zero_lt_one.trans hlam ) _ );
  · obtain ⟨ p, hp₁, hp₂ ⟩ := hm;
    exact sinv_pos hS ( Finset.mem_filter.mp ( hL hp₁ ) |>.1 |> Finset.mem_filter.mp |>.2 ) hp₂;
  · obtain ⟨ p, hp, hm ⟩ := hm;
    intro r hr; exact sieve_prime_not_dvd_sinv hS hlam ( hL hp |> Finset.mem_filter.mp |>.1 ) ( hL hp |> Finset.mem_filter.mp |>.2 ) hr hm;

lemma M_layer_nonneg (lam : ℝ) (k : ℕ) : 0 ≤ M_layer lam k := by
  exact Finset.prod_nonneg fun p hp => sub_nonneg_of_le <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2

/-! ## Euler-Mascheroni constant bound -/

set_option maxHeartbeats 200000000 in
-- The rational harmonic-number bound needs extra heartbeats for `norm_num`.
/-- γ < 579/1000. Proved using eulerMascheroniSeq'(500) with norm_num for harmonic(500). -/
lemma gamma_lt_tight : γ < 579/1000 := by
  unfold γ
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 500
  simp only [Real.eulerMascheroniSeq', show (500 : ℕ) ≠ 0 from by omega, ↓reduceIte] at h
  -- Bound harmonic(500) from above
  have h2 : ((↑(harmonic 500 : ℚ) : ℝ)) < 6793/1000 := by
    rw [show (6793/1000 : ℝ) = ((↑(6793/1000 : ℚ) : ℝ)) from by push_cast; norm_num]
    exact Rat.cast_lt.mpr (by norm_num [harmonic, Finset.sum_range_succ])
  -- Bound Real.log(500) from below: show exp(6214/1000) < 500
  have h3 : Real.log (500 : ℝ) > 6214/1000 := by
    rw [show (6214 : ℝ)/1000 = Real.log (Real.exp (6214/1000)) from (Real.log_exp _).symm]
    exact Real.log_lt_log (Real.exp_pos _) (by
      -- exp(6.214) = exp(1)^6 * exp(0.214)
      have h1 : Real.exp (6214/1000 : ℝ) = Real.exp 1 ^ 6 * Real.exp (214/1000 : ℝ) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      rw [h1]
      have hx : |(214/1000 : ℝ)| ≤ 1 := by norm_num
      have hb := Real.exp_bound hx (n := 8) (by norm_num)
      rw [abs_le] at hb
      calc Real.exp 1 ^ 6 * Real.exp (214/1000 : ℝ)
          ≤ (2.7182818286 : ℝ)^6 * (∑ m ∈ Finset.range 8, (214/1000 : ℝ) ^ m / ↑m.factorial +
            |(214/1000 : ℝ)| ^ 8 * (↑(8 : ℕ).succ / (↑(8 : ℕ).factorial * ↑(8 : ℕ)))) := by
              apply mul_le_mul
              · exact pow_le_pow_left₀ (by positivity) (le_of_lt Real.exp_one_lt_d9) _
              · linarith [hb.2]
              · exact le_of_lt (Real.exp_pos _)
              · positivity
          _ < 500 := by simp [Finset.sum_range_succ]; norm_num)
  have h4 : Real.log ((500 : ℕ) : ℝ) = Real.log (500 : ℝ) := by push_cast; ring
  linarith [h4]

/-
Division Lemma
-/
theorem division_lemma (S : Finset ℕ) (p : ℕ) (_hp : Nat.Prime p) :
    (sinv S p).card = (sdiv S p).card := by
  exact Finset.card_image_of_injOn fun x hx y hy hxy => by
    nlinarith [Nat.div_mul_cancel (Finset.mem_filter.mp hx |>.2),
               Nat.div_mul_cancel (Finset.mem_filter.mp hy |>.2)]

/-
Collision Lemma
-/
theorem collision_lemma (n : ℕ) (A B : Finset ℕ) (p q : ℕ)
    (hadm : ProductAdmissible n A B) (_hp : Nat.Prime p) (_hq : Nat.Prime q) (hpq : p ≠ q)
    (hinter : (sinv A p ∩ sinv A q).Nonempty) :
    sinv B p ∩ sinv B q = ∅ := by
  obtain ⟨x, hx⟩ := hinter
  by_contra h_contra
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr h_contra
  obtain ⟨a1, ha1, ha1_eq⟩ : ∃ a1 ∈ A, a1 = p * x := by
    simp_all +decide [sinv]
    obtain ⟨a, ha, rfl⟩ := hx.1
    exact Finset.mem_filter.mp ha |>.1 |> fun h => by
      simpa [Nat.mul_div_cancel' (Finset.mem_filter.mp ha |>.2)] using h
  obtain ⟨a2, ha2, ha2_eq⟩ : ∃ a2 ∈ A, a2 = q * x := by
    simp_all +decide [sinv]
    obtain ⟨a, ha, rfl⟩ := hx.2
    exact Finset.mem_filter.mp ha |>.1 |> fun h => by
      convert h using 1
      nlinarith [Nat.div_mul_cancel (show q ∣ a from Finset.mem_filter.mp ha |>.2)]
  obtain ⟨b1, hb1, hb1_eq⟩ : ∃ b1 ∈ B, b1 = p * y := by
    simp_all +decide [sinv]
    obtain ⟨a, ha, rfl⟩ := hy.1
    exact Finset.mem_filter.mp ha |>.1 |> fun h => by
      simpa [Nat.mul_div_cancel' (Finset.mem_filter.mp ha |>.2)] using h
  obtain ⟨b2, hb2, hb2_eq⟩ : ∃ b2 ∈ B, b2 = q * y := by
    simp_all +decide [sinv]
    obtain ⟨a, ha, rfl⟩ := hy.2
    exact Finset.mem_filter.mp ha |>.1 |> fun h => by
      convert h using 1
      nlinarith [Nat.div_mul_cancel (show q ∣ a from Finset.mem_filter.mp ha |>.2)]
  have := hadm.2.2 a1 ha1 b2 hb2 a2 ha2 b1 hb1
  simp_all +decide [mul_comm, mul_left_comm]
  have := hadm.1 ha1; aesop

/-
Admissibility is inherited by subsets
-/
theorem admissible_subset {n : ℕ} {A B A' B' : Finset ℕ}
    (hadm : ProductAdmissible n A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    ProductAdmissible n A' B' := by
  exact ⟨hA.trans hadm.1, hB.trans hadm.2.1,
    fun a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ h =>
      hadm.2.2 a₁ (hA ha₁) b₁ (hB hb₁) a₂ (hA ha₂) b₂ (hB hb₂) h⟩

lemma sdiv_subset (S : Finset ℕ) (p : ℕ) : sdiv S p ⊆ S :=
  Finset.filter_subset _ _

lemma sdiv_sdiff_self_empty (S : Finset ℕ) (p : ℕ) : sdiv (S \ sdiv S p) p = ∅ := by
  ext x; simp [sdiv]; tauto

lemma card_sdiff_sdiv_lt (S : Finset ℕ) (p : ℕ) (h : (sdiv S p).Nonempty) :
    (S \ sdiv S p).card < S.card := by
  exact Finset.card_lt_card (Finset.sdiff_ssubset (sdiv_subset S p) h)

lemma sdiv_sdiff_subset (S : Finset ℕ) (p q : ℕ) :
    (sdiv (S \ sdiv S p) q).Nonempty → (sdiv S q).Nonempty := by
  exact fun h => h.imp fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Finset.mem_filter.mp hx |>.2 ⟩

end Erdos490
