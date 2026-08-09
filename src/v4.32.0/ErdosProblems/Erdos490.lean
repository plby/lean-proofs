/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 490.
https://www.erdosproblems.com/forum/thread/490

Formalization status:
- Conditional on: dusart_mertens_product
- Conditional on: dusart_pi_lower
- Conditional on: dusart_pi_upper
- Conditional on: dusart_chebyshev

Informal authors:
- Endre Szemerédi
- ChatGPT 5.5 Pro

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/490#post-6497
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem490.lean
-/
/-
Solving Erdős Problem #490 (https://www.erdosproblems.com/490), Szemerédi proved
that there exists an absolute constant C such if A, B ⊆ {1,...,n} has all
products ab distinct, then |A|·|B| < Cn²/log n for all n > 1. Below you can find
a formalization of this result, which obtains an explicit constant C = 60 for
sufficiently large n. For this we need various explicit estimates on primes of
Dusart that are recorded at the start of the file.

Dusart, P. Explicit estimates of some functions over primes. Ramanujan J. 45,
227–251 (2018).

The proof is an improved version of Szeméredi's original argument, which was
written down by ChatGPT 5.5 Pro.

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) did the formalization.

-/

import Mathlib
import ErdosProblems.Axioms

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

/-- ℓ_k(r) = log E_{λ,k}(r) -/
def ell_val (lam : ℝ) (k : ℕ) (r : ℕ) : ℝ := Real.log (E_val lam k r)

/-- D_{λ,m} = ∏_k E_{λ,k}(m_k) defined as exp(∑' log E_k(m_k)) -/
def D_val (lam : ℝ) (m : ℕ → ℕ) : ℝ :=
  Real.exp (∑' k, Real.log (E_val lam k (m k)))

/-- s_k(r) = N_k / (Y_k · M_k · √(r+1)) if r < N_k, else 0 -/
def s_val (lam : ℝ) (k : ℕ) (r : ℕ) : ℝ :=
  if r < N_layer lam k then
    (N_layer lam k : ℝ) / (Y_val lam k * M_layer lam k * Real.sqrt ((r : ℝ) + 1))
  else 0

/-- Ω_{λ,m,g} = ∑_{k : m_k < N_k} g_k · N_k / (Y_k · M_k · √(m_k+1)) -/
def Omega_val (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑' k, g k * s_val lam k (m k)

/-- A triple (λ,m,g) is admissible if D < ∞, Ω < 1, g_k ≥ 1, and g_k → ∞ -/
def AdmissibleTriple (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ) : Prop :=
  1 < lam ∧
  (∀ k, m k ≤ N_layer lam k) ∧
  Summable (fun k => Real.log (E_val lam k (m k))) ∧
  Summable (fun k => g k * s_val lam k (m k)) ∧
  Omega_val lam m g < 1 ∧
  (∀ k, 1 ≤ g k) ∧
  Filter.Tendsto g Filter.atTop Filter.atTop

/-- Layer weight c_k = g_k / (Y_k · M_k · √(m_k+1)) if m_k < N_k, else 0 -/
def layerWeight (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  if m k < N_layer lam k then
    g k / (Y_val lam k * M_layer lam k * Real.sqrt ((m k : ℝ) + 1))
  else 0

/-- A set S is (λ,m,g)-regular if for every prime p in layer k with
    layerWeight k > 0 and S[p] ≠ ∅, we have |S[p]| > layerWeight k · |S| -/
def Regular (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ) (S : Finset ℕ) : Prop :=
  ∀ k, ∀ p ∈ I_layer lam k,
    layerWeight lam m g k > 0 → (sdiv S p).Nonempty →
    ((sdiv S p).card : ℝ) > layerWeight lam m g k * S.card

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

/-- λ₀ = 1931/1000 -/
def lam0 : ℝ := 1931 / 1000

/-- μ₀ = 29607/20000 -/
def mu0 : ℝ := 29607 / 20000

/-- m_k = N_layer(k) for k ≤ 24, ⌊μ₀ · Y_k^{2/3}⌋ for k ≥ 25.
    Using N_layer for the finite layers ensures s_val = 0 for k ≤ 24,
    at the cost of a larger ell_val contribution, simplifying the proof. -/
def mSeq (k : ℕ) : ℕ :=
  if k ≤ 24 then N_layer lam0 k
  else ⌊mu0 * (Y_val lam0 k) ^ ((2 : ℝ) / 3)⌋₊

/-- g_k = 1 for k ≤ 150, (k-149)² for k > 150 -/
def gSeq (k : ℕ) : ℝ :=
  if k ≤ 150 then 1 else ((k : ℝ) - 149) ^ 2

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

/-! ## Real.log(lam0) bounds -/

lemma log_lam0_gt : Real.log lam0 > 658/1000 := by
  rw [show (658 : ℝ)/1000 = Real.log (exp (658/1000)) from (Real.log_exp _).symm]
  exact Real.log_lt_log (exp_pos _) (by
    have hb := Real.exp_bound (show |(658/1000 : ℝ)| ≤ 1 from by norm_num) (n := 10) (by norm_num)
    rw [abs_le] at hb
    have : ∑ m ∈ Finset.range 10, (658/1000 : ℝ) ^ m / ↑m.factorial +
      |(658/1000 : ℝ)| ^ 10 * (↑(10 : ℕ).succ / (↑(10 : ℕ).factorial * ↑(10 : ℕ))) < lam0 := by
      simp [Finset.sum_range_succ, lam0]; norm_num
    linarith [hb.2])

lemma log_lam0_lt : Real.log lam0 < 659/1000 := by
  rw [show (659 : ℝ)/1000 = Real.log (exp (659/1000)) from (Real.log_exp _).symm]
  exact Real.log_lt_log (by norm_num [lam0] : (0:ℝ) < lam0) (by
    have hb := Real.exp_bound (show |(659/1000 : ℝ)| ≤ 1 from by norm_num) (n := 10) (by norm_num)
    rw [abs_le] at hb
    have : lam0 < ∑ m ∈ Finset.range 10, (659/1000 : ℝ) ^ m / ↑m.factorial -
      |(659/1000 : ℝ)| ^ 10 * (↑(10 : ℕ).succ / (↑(10 : ℕ).factorial * ↑(10 : ℕ))) := by
      simp [Finset.sum_range_succ, lam0]; norm_num
    linarith [hb.1])

/-! ## Y_val positivity and bounds -/

lemma Y_val_pos' (k : ℕ) : 0 < Y_val lam0 k :=
  mul_pos two_pos (pow_pos (by norm_num [lam0]) k)

lemma Y_val_ge_88789 (k : ℕ) (hk : 25 ≤ k) : Y_val lam0 k ≥ 88789 := by
  unfold Y_val lam0
  nlinarith [pow_le_pow_right₀ (show (1 : ℝ) ≤ 1931/1000 from by norm_num) hk,
             show (1931/1000 : ℝ)^25 ≥ 44395 from by norm_num]

lemma Y_val_succ_ge_2278382 (k : ℕ) (hk : 25 ≤ k) : Y_val lam0 (k+1) ≥ 2278382 := by
  unfold Y_val lam0
  nlinarith [pow_le_pow_right₀ (show (1 : ℝ) ≤ 1931/1000 from by norm_num) (show 26 ≤ k + 1 from by omega),
             show (1931/1000 : ℝ)^26 ≥ 1139191 from by norm_num]

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

/-- Total weight of "relevant" primes for S: primes with positive weight
    that divide some element of S. -/
noncomputable def mu_val (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑' k, (layerWeight lam m g k) *
    ((I_layer lam k).filter (fun p => (sdiv S p).Nonempty)).card

lemma sdiv_subset (S : Finset ℕ) (p : ℕ) : sdiv S p ⊆ S :=
  Finset.filter_subset _ _

lemma sdiv_sdiff_self_empty (S : Finset ℕ) (p : ℕ) : sdiv (S \ sdiv S p) p = ∅ := by
  ext x; simp [sdiv]; tauto

lemma card_sdiff_sdiv_lt (S : Finset ℕ) (p : ℕ) (h : (sdiv S p).Nonempty) :
    (S \ sdiv S p).card < S.card := by
  exact Finset.card_lt_card (Finset.sdiff_ssubset (sdiv_subset S p) h)

lemma not_regular_exists_bad (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ) (S : Finset ℕ)
    (h : ¬ Regular lam m g S) :
    ∃ k, ∃ p ∈ I_layer lam k,
      layerWeight lam m g k > 0 ∧ (sdiv S p).Nonempty ∧
      ((sdiv S p).card : ℝ) ≤ layerWeight lam m g k * S.card := by
  simp only [Regular, not_forall] at h
  obtain ⟨k, p, hp, hw, hne, hle⟩ := h
  exact ⟨k, p, hp, hw, hne, le_of_not_gt hle⟩

lemma layerWeight_nonneg (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g) (k : ℕ) :
    0 ≤ layerWeight lam m g k := by
  unfold layerWeight;
  split_ifs <;> norm_num [ hadm ];
  apply_rules [ div_nonneg, mul_nonneg, Real.sqrt_nonneg ];
  · exact le_trans zero_le_one ( hadm.2.2.2.2.2.1 k );
  · norm_num;
  · exact pow_nonneg ( by linarith [ hadm.1 ] ) _;
  · exact Finset.prod_nonneg fun p hp => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2

lemma sdiv_sdiff_subset (S : Finset ℕ) (p q : ℕ) :
    (sdiv (S \ sdiv S p) q).Nonempty → (sdiv S q).Nonempty := by
  exact fun h => h.imp fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Finset.mem_filter.mp hx |>.2 ⟩

lemma omega_summable (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g) :
    Summable (fun k => g k * s_val lam k (m k)) :=
  hadm.2.2.2.1

lemma mu_term_le_omega_term (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g) (S : Finset ℕ) (k : ℕ) :
    layerWeight lam m g k *
      ((I_layer lam k).filter (fun q => (sdiv S q).Nonempty)).card ≤
    g k * s_val lam k (m k) := by
  unfold layerWeight s_val;
  split_ifs <;> ring_nf <;> norm_num;
  gcongr;
  · refine mul_nonneg ( mul_nonneg ( mul_nonneg ?_ ?_ ) ?_ ) ?_ <;> norm_num [ Y_val, M_layer ];
    · exact le_trans zero_le_one ( hadm.2.2.2.2.2.1 k );
    · exact pow_nonneg ( by linarith [ hadm.1 ] ) _;
    · exact Finset.prod_nonneg fun x hx => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by unfold primesUpTo at hx; aesop;
  · exact Finset.card_filter_le _ _

lemma mu_val_summable (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g) (S : Finset ℕ) :
    Summable (fun k => layerWeight lam m g k *
      ((I_layer lam k).filter (fun q => (sdiv S q).Nonempty)).card) :=
  (omega_summable lam m g hadm).of_nonneg_of_le
    (fun k => mul_nonneg (layerWeight_nonneg lam m g hadm k) (Nat.cast_nonneg _))
    (mu_term_le_omega_term lam m g hadm S)

/-
Monotonicity of mu_val: removing sdiv S p decreases mu_val by at least
    layerWeight k (when p ∈ I_layer k with positive weight).
-/
lemma mu_val_sdiff_le (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g)
    (S : Finset ℕ) (k : ℕ) (p : ℕ)
    (hp : p ∈ I_layer lam k) (hw : layerWeight lam m g k > 0)
    (hne : (sdiv S p).Nonempty) :
    mu_val lam m g (S \ sdiv S p) + layerWeight lam m g k ≤ mu_val lam m g S := by
  have h_term_le : ∀ j, layerWeight lam m g j * ((I_layer lam j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card + (if j = k then layerWeight lam m g k else 0) ≤ layerWeight lam m g j * ((I_layer lam j).filter (fun q => (sdiv S q).Nonempty)).card := by
    intro j
    by_cases hj : j = k;
    · have h_card_filter : ((I_layer lam k).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card + 1 ≤ ((I_layer lam k).filter (fun q => (sdiv S q).Nonempty)).card := by
        refine Finset.card_lt_card ?_;
        simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        exact ⟨ fun x hx hx' => sdiv_sdiff_subset _ _ _ hx', p, hp, hne, sdiv_sdiff_self_empty _ _ ⟩;
      rw [ hj ] ; rw [ if_pos rfl ] ; nlinarith [ show ( # ( { q ∈ I_layer lam k | ( sdiv ( S \ sdiv S p ) q ).Nonempty } ) : ℝ ) + 1 ≤ # ( { q ∈ I_layer lam k | ( sdiv S q ).Nonempty } ) from mod_cast h_card_filter ] ;
    · simp [hj];
      gcongr;
      · grind +suggestions;
      · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Finset.mem_filter.mp hx |>.2 ⟩;
  have hsumm_sdiff :
      Summable (fun j => layerWeight lam m g j *
        ((I_layer lam j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card) := by
    convert mu_val_summable lam m g hadm (S \ sdiv S p) using 1
  have hsumm_single :
      Summable (fun j : ℕ => if j = k then layerWeight lam m g k else 0) :=
    ⟨_, hasSum_single k <| by aesop⟩
  have hsumm_left : Summable (fun j => layerWeight lam m g j * ((I_layer lam j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card + (if j = k then layerWeight lam m g k else 0)) := by
    refine Summable.add ?_ ?_;
    · exact hsumm_sdiff
    · exact hsumm_single
  have hleft :
      (∑' j, (layerWeight lam m g j *
          ((I_layer lam j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card +
          (if j = k then layerWeight lam m g k else 0))) =
        mu_val lam m g (S \ sdiv S p) + layerWeight lam m g k := by
    rw [Summable.tsum_add hsumm_sdiff hsumm_single]
    change
      (∑' j, layerWeight lam m g j *
          ((I_layer lam j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card) +
        (∑' j : ℕ, if j = k then layerWeight lam m g k else 0) =
      (∑' j, layerWeight lam m g j *
          ((I_layer lam j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card) +
        layerWeight lam m g k
    congr 1
    rw [tsum_eq_single k]
    · simp
    · intro j hj
      simp [hj]
  have hright : Summable (fun j => layerWeight lam m g j *
      ((I_layer lam j).filter (fun q => (sdiv S q).Nonempty)).card) := by
    convert mu_val_summable lam m g hadm S using 1
  calc
    mu_val lam m g (S \ sdiv S p) + layerWeight lam m g k
        = ∑' j, (layerWeight lam m g j *
            ((I_layer lam j).filter (fun q => (sdiv (S \ sdiv S p) q).Nonempty)).card +
            (if j = k then layerWeight lam m g k else 0)) := hleft.symm
    _ ≤ ∑' j, layerWeight lam m g j *
            ((I_layer lam j).filter (fun q => (sdiv S q).Nonempty)).card :=
          Summable.tsum_le_tsum h_term_le hsumm_left hright
    _ = mu_val lam m g S := rfl

lemma mu_val_nonneg (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g) (S : Finset ℕ) :
    0 ≤ mu_val lam m g S := by
  refine tsum_nonneg ?_
  intro k; unfold layerWeight; split_ifs <;> norm_num
  unfold Y_val M_layer; norm_num
  exact mul_nonneg ( div_nonneg ( by linarith [ hadm.2.2.2.2.2.1 k ] ) ( mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_two ( pow_nonneg ( by linarith [ hadm.1 ] ) _ ) ) ( Finset.prod_nonneg fun x hx => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by unfold primesUpTo at hx; aesop ) ) <| Real.sqrt_nonneg _ ) ) <| Nat.cast_nonneg _

lemma mu_val_le_omega (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ) (S : Finset ℕ)
    (hadm : AdmissibleTriple lam m g) :
    mu_val lam m g S ≤ Omega_val lam m g := by
  exact Summable.tsum_le_tsum (mu_term_le_omega_term lam m g hadm S)
    (mu_val_summable lam m g hadm S) (omega_summable lam m g hadm)

/-- Given an admissible triple (λ,m,g) and a finite nonempty set S,
    there exists a (λ,m,g)-regular subset S* ⊆ S with |S*| ≥ (1-Ω)|S|. -/
theorem weighted_deletion (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g)
    (S : Finset ℕ) :
    ∃ S' ⊆ S, Regular lam m g S' ∧
      ((S'.card : ℝ) ≥ (1 - Omega_val lam m g) * S.card) := by
  -- We prove the stronger statement: ∃ S' ⊆ S regular with
  -- |S| - |S'| ≤ mu_val S · |S| (where mu_val S ≤ Ω).
  suffices h : ∀ n : ℕ, ∀ T : Finset ℕ, T.card = n →
      ∃ S' ⊆ T, Regular lam m g S' ∧
        ((T.card : ℝ) - S'.card ≤ mu_val lam m g T * T.card) by
    obtain ⟨S', hS', hreg, hbound⟩ := h S.card S rfl
    exact ⟨S', hS', hreg, by nlinarith [mu_val_le_omega lam m g S hadm]⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro T hT
    by_cases hreg : Regular lam m g T
    · refine ⟨T, Subset.refl T, hreg, ?_⟩
      simp
      exact mul_nonneg (mu_val_nonneg lam m g hadm T) (Nat.cast_nonneg T.card)
    · obtain ⟨k, p, hp, hw, hne, hbound⟩ := not_regular_exists_bad lam m g T hreg
      set T₁ := T \ sdiv T p
      have hlt : T₁.card < T.card := card_sdiff_sdiv_lt T p hne
      obtain ⟨S', hS', hreg', hbound'⟩ := ih T₁.card (hT ▸ hlt) T₁ rfl
      refine ⟨S', hS'.trans (Finset.sdiff_subset), hreg', ?_⟩
      have hcard : (T.card : ℝ) - T₁.card = (sdiv T p).card := by
        have h1 : T₁.card + (sdiv T p).card = T.card := by
          have h := Finset.card_sdiff_add_card_inter T (sdiv T p)
          have heq : T ∩ sdiv T p = sdiv T p := Finset.inter_eq_right.mpr (sdiv_subset T p)
          simp only [T₁, heq] at h ⊢; omega
        have h2 : (T₁.card : ℝ) + (sdiv T p).card = T.card := by exact_mod_cast h1
        linarith
      have hmu : mu_val lam m g T₁ + layerWeight lam m g k ≤ mu_val lam m g T :=
        mu_val_sdiff_le lam m g hadm T k p hp hw hne
      calc (T.card : ℝ) - S'.card
          = ((sdiv T p).card : ℝ) + ((T₁.card : ℝ) - S'.card) := by
            rw [← hcard]; ring
        _ ≤ layerWeight lam m g k * T.card + mu_val lam m g T₁ * T₁.card := by linarith
        _ ≤ layerWeight lam m g k * T.card + mu_val lam m g T₁ * T.card := by
            have h1 := mu_val_nonneg lam m g hadm T₁
            have h2 : (T₁.card : ℝ) ≤ T.card := Nat.cast_le.mpr (le_of_lt (hT ▸ hlt))
            have h3 : mu_val lam m g T₁ * T₁.card ≤ mu_val lam m g T₁ * T.card :=
              mul_le_mul_of_nonneg_left h2 h1
            linarith
        _ = (layerWeight lam m g k + mu_val lam m g T₁) * T.card := by ring
        _ ≤ mu_val lam m g T * T.card := by nlinarith [hmu]

/-
Weighted Regular Reduction
-/
theorem weighted_regular_reduction (n : ℕ) (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadmT : AdmissibleTriple lam m g) (A B : Finset ℕ)
    (hadm : ProductAdmissible n A B) :
    ∃ A' B' : Finset ℕ, A' ⊆ A ∧ B' ⊆ B ∧
      ProductAdmissible n A' B' ∧ Regular lam m g A' ∧ Regular lam m g B' ∧
      ((A'.card : ℝ) * B'.card ≥
        (1 - Omega_val lam m g) ^ 2 * (A.card * B.card)) := by
  rcases lt_or_ge ( 1 - Omega_val lam m g ) 0 with h | h
  · exact absurd h ( not_lt_of_ge ( sub_nonneg_of_le hadmT.2.2.2.2.1.le ) )
  · obtain ⟨A', hA'⟩ := weighted_deletion lam m g hadmT A
    obtain ⟨B', hB'⟩ := weighted_deletion lam m g hadmT B;
    refine ⟨ A', B', hA'.1, hB'.1, admissible_subset hadm hA'.1 hB'.1, hA'.2.1, hB'.2.1, ?_ ⟩;
    nlinarith [ mul_le_mul_of_nonneg_left hA'.2.2 h, mul_le_mul_of_nonneg_left hB'.2.2 h ]

set_option maxHeartbeats 800000
-- The Mertens-product setup needs extra heartbeats for generated product bounds.

/-
As x → ∞, ∏_{p≤x}(1-1/p) = (e^{-γ} + o(1))/log x.
-/
theorem mertens_product_estimate (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ x : ℝ, x ≥ X₀ →
      |∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) -
        Real.exp (-γ) / Real.log x| ≤ ε / Real.log x := by
  -- By Dusart's theorem, we have for x ≥ 2278382:
  have h_dusart : ∀ x : ℝ, x ≥ 2278382 → |∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) - Real.exp (-γ) / Real.log x| ≤ 1 / (5 * Real.exp γ * Real.log x ^ 4) := by
    intro x hx
    have h0 : |∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) -
        1 / (Real.exp γ * Real.log x)| ≤
        1 / (5 * Real.exp γ * Real.log x ^ 4) := by
      simpa [primesUpTo, γ] using dusart_mertens_product x hx
    convert h0 using 2
    norm_num [ Real.exp_neg ]
    ring
  -- Since 1/(5 e^γ log⁴ x) = o(1/log x), for large enough x this is ≤ ε/log x.
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ x ≥ X₀, 1 / (5 * Real.exp γ * Real.log x ^ 4) ≤ ε / Real.log x := by
    -- We can choose $X₀$ such that for all $x ≥ X₀$, $\frac{1}{5e^\gamma \log^3 x} ≤ \epsilon$.
    obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ x ≥ X₀, 1 / (5 * Real.exp γ * Real.log x ^ 3) ≤ ε := by
      have h_lim : Filter.Tendsto (fun x : ℝ => 1 / (5 * Real.exp γ * Real.log x ^ 3)) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( Filter.Tendsto.const_mul_atTop ( by positivity ) ( Filter.Tendsto.comp ( Filter.tendsto_pow_atTop ( by positivity ) ) ( Real.tendsto_log_atTop ) ) );
      simpa using h_lim.eventually ( ge_mem_nhds hε );
    exact ⟨ Max.max X₀ 2, fun x hx => by
      have hx0 := hX₀ x (le_trans (le_max_left _ _) hx)
      have hloginv : 0 ≤ (Real.log x)⁻¹ :=
        inv_nonneg.mpr (Real.log_nonneg (by linarith [le_max_right X₀ 2]))
      have hmul := mul_le_mul_of_nonneg_right hx0 hloginv
      simpa [div_eq_mul_inv, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul ⟩;
  exact ⟨ Max.max X₀ 2278382, fun x hx => le_trans ( h_dusart x ( le_trans ( le_max_right _ _ ) hx ) ) ( hX₀ x ( le_trans ( le_max_left _ _ ) hx ) ) ⟩

/-
For completely multiplicative f : ℕ → {0,1},
    L_f(X) ≤ ∑_{a ≤ X} f(a) · ψ(X/a).
-/
theorem log_convolution_bound (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (_hX : X ≥ 1) :
    L_count f X ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1),
      f a * chebyshevPsi (X / (a : ℝ)) := by
  unfold L_count chebyshevPsi;
  have h_log_convolution : ∀ m ∈ Finset.range (⌊X⌋₊ + 1), m ≠ 0 → f m * Real.log m ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1), ArithmeticFunction.vonMangoldt n * (if n * a = m then 1 else 0) := by
    intro m hm hm_ne_zero
    have h_log_convolution_step : f m * Real.log m ≤ ∑ a ∈ Nat.divisors m, f a * ArithmeticFunction.vonMangoldt (m / a) := by
      have h_log_convolution_step : Real.log m = ∑ a ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt (m / a) := by
        have h_log_convolution_step : Real.log m = ∑ a ∈ Nat.divisors m, ArithmeticFunction.vonMangoldt a := by
          rw [ ArithmeticFunction.vonMangoldt_sum ];
        rw [ h_log_convolution_step, ← Nat.sum_div_divisors ];
      rw [ h_log_convolution_step, Finset.mul_sum _ _ _ ];
      refine Finset.sum_le_sum fun i hi => ?_;
      have h_f_mul : f m = f i * f (m / i) := by
        rw [ ← hf.2.2 i ( m / i ) ( Nat.pos_of_mem_divisors hi ) ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hm_ne_zero ) ( Nat.dvd_of_mem_divisors hi ) ) ( Nat.pos_of_mem_divisors hi ) ), Nat.mul_div_cancel' ( Nat.dvd_of_mem_divisors hi ) ];
      cases hf.1 i <;> cases hf.1 ( m / i ) <;> simp_all +decide;
    refine le_trans h_log_convolution_step ?_;
    rw [ ← Finset.sum_subset ( show m.divisors ⊆ Finset.range ( ⌊X⌋₊ + 1 ) from fun x hx => Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_trans ( Nat.divisor_le hx ) <| Finset.mem_range_succ_iff.mp hm ) ];
    · gcongr;
      · cases hf.1 ‹_› <;> aesop;
      · rw [ Finset.sum_eq_single ( m / ‹_› ) ] <;> norm_num;
        · rw [ if_pos ( Nat.div_mul_cancel ( Nat.dvd_of_mem_divisors ‹_› ) ) ];
        · aesop;
        · intro h₁ h₂; contrapose! h₁; simp_all +decide [ Nat.floor_div_natCast ] ;
          exact Nat.div_le_div_right hm;
    · simp +zetaDelta at *;
      exact fun x hx hx' => Or.inr <| Finset.sum_eq_zero fun y hy => if_neg <| by intro H; exact hm_ne_zero <| hx' <| dvd_of_mul_left_eq _ H;
  have h_log_convolution_sum : ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m * Real.log m ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1), ArithmeticFunction.vonMangoldt n * ∑ m ∈ Finset.range (⌊X⌋₊ + 1), (if n * a = m then 1 else 0) := by
    have hsum :
        ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m * Real.log m ≤
          ∑ m ∈ Finset.range (⌊X⌋₊ + 1),
            ∑ a ∈ Finset.range (⌊X⌋₊ + 1),
              f a * ∑ n ∈ Finset.range (⌊X / a⌋₊ + 1),
                ArithmeticFunction.vonMangoldt n * (if n * a = m then 1 else 0) := by
      refine Finset.sum_le_sum fun m hm => ?_
      by_cases hm0 : m = 0
      · subst m
        simp
        refine Finset.sum_nonneg fun i hi => mul_nonneg ?_ ?_
        · cases hf.1 i <;> linarith
        · exact Finset.sum_nonneg fun _ _ => by
            split_ifs <;> simp +decide [ArithmeticFunction.vonMangoldt_nonneg]
      · exact h_log_convolution m hm hm0
    refine hsum.trans_eq ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n hn => by
      rw [← Finset.mul_sum]
  refine le_trans h_log_convolution_sum <| Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ <| ?_;
  · gcongr;
    aesop;
  · cases hf.1 a <;> linarith

/-
Let A > log 2, C_A = ψ(e^A), δ_A = 1.66/A².
    If f is completely multiplicative {0,1}-valued and X > e^{A+C_A}, then
    F_f(X) - F_f(X·e^{-A}) ≤ (1+δ_A)·X·H_f(X)/(log X - A - C_A).
-/
theorem block_estimate (A : ℝ) (hA : A > Real.log 2) (f : ℕ → ℝ)
    (hf : CompMult01 f) (X : ℝ)
    (hX : X > Real.exp (A + chebyshevPsi (Real.exp A))) :
    F_count f X - F_count f (X * Real.exp (-A)) ≤
      (1 + 1.66 / A ^ 2) * X * H_count f X /
        (Real.log X - A - chebyshevPsi (Real.exp A)) := by
  -- By log_convolution_bound, L_f(X) ≤ ∑_{a≤X} f(a)·ψ(X/a).
  have h_log_conv : L_count f X ≤ ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) := by
    apply log_convolution_bound f hf X (by
    exact le_trans ( Real.one_le_exp ( by linarith [ Real.log_nonneg one_le_two, show 0 ≤ chebyshevPsi ( Real.exp A ) from Finset.sum_nonneg fun _ _ => by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg ] ) ) hX.le);
  -- Split the sum at a = X·e^{-A}:
  have h_split_sum : ∑ a ∈ Finset.range (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ (1 + 1.66 / A^2) * X * H_count f (X * Real.exp (-A)) + chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
    have h_split_sum : ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ (1 + 1.66 / A^2) * X * H_count f (X * Real.exp (-A)) := by
      have h_split_sum : ∀ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1), a ≠ 0 → f a * chebyshevPsi (X / a) ≤ (1 + 1.66 / A^2) * X * (f a / a) := by
        intros a ha ha_ne_zero
        have h_chebyshev : chebyshevPsi (X / a) ≤ (1 + 1.66 / A^2) * (X / a) := by
          have h_chebyshev : ∀ x : ℝ, x ≥ Real.exp A → chebyshevPsi x ≤ (1 + 1.66 / A^2) * x := by
            intros x hx
            have h_chebyshev : |chebyshevPsi x - x| < 1.66 * x / (Real.log x)^2 := by
              apply dusart_chebyshev;
              exact le_trans ( by rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ] ; linarith ) hx;
            have h_log_bound : Real.log x ≥ A := by
              exact Real.log_exp A ▸ Real.log_le_log ( by positivity ) hx;
            have h_log_bound : 1.66 * x / (Real.log x)^2 ≤ 1.66 * x / A^2 := by
              gcongr;
              · exact mul_nonneg ( by norm_num ) ( le_trans ( by positivity ) hx );
              · exact sq_pos_of_pos ( lt_trans ( Real.log_pos one_lt_two ) hA );
              · linarith [ Real.log_nonneg one_le_two ];
            ring_nf at *; linarith [ abs_lt.mp h_chebyshev ] ;
          apply h_chebyshev;
          rw [ ge_iff_le, le_div_iff₀ ] <;> norm_num at *;
          · rw [ Nat.le_floor_iff ( mul_nonneg ( le_of_lt ( show 0 < X by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) ) ( Real.exp_nonneg _ ) ) ] at ha;
            rw [ Real.exp_neg ] at ha ; nlinarith [ Real.exp_pos A, mul_inv_cancel_left₀ ( ne_of_gt ( Real.exp_pos A ) ) X ];
          · positivity;
        calc
          f a * chebyshevPsi (X / a) ≤
              f a * ((1 + 1.66 / A ^ 2) * (X / a)) :=
            mul_le_mul_of_nonneg_left h_chebyshev
              (show 0 ≤ f a by cases hf.1 a <;> linarith)
          _ = (1 + 1.66 / A ^ 2) * X * (f a / a) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      have hsum :
          ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1),
              f a * chebyshevPsi (X / a) ≤
            ∑ a ∈ Finset.range (⌊X * Real.exp (-A)⌋₊ + 1),
              (1 + 1.66 / A^2) * X * (f a / a) := by
        refine Finset.sum_le_sum fun a ha => ?_
        by_cases ha0 : a = 0
        · subst a
          unfold chebyshevPsi
          norm_num
        · exact h_split_sum a ha ha0
      refine hsum.trans_eq ?_
      rw [H_count, ← Finset.mul_sum]
    have h_split_sum : ∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
      have h_split_sum : ∀ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a * chebyshevPsi (X / a) ≤ f a * chebyshevPsi (Real.exp A) := by
        intros a ha
        have h_chebyshevPsi_le : chebyshevPsi (X / a) ≤ chebyshevPsi (Real.exp A) := by
          have h_chebyshevPsi_le : X / a ≤ Real.exp A := by
            rw [ div_le_iff₀ ] <;> norm_num at *;
            · have := Nat.lt_of_floor_lt ha.1;
              rw [ Real.exp_neg ] at this ; nlinarith [ Real.exp_pos A, mul_inv_cancel_left₀ ( ne_of_gt ( Real.exp_pos A ) ) X ];
            · grind;
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_;
          · exact Finset.range_mono ( Nat.succ_le_succ <| Nat.floor_mono h_chebyshevPsi_le );
          · exact fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg;
        exact mul_le_mul_of_nonneg_left h_chebyshevPsi_le <| by cases hf.1 a <;> linarith;
      refine (Finset.sum_le_sum h_split_sum).trans_eq ?_
      calc
        (∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1),
            f a * chebyshevPsi (Real.exp A))
            = chebyshevPsi (Real.exp A) *
                ∑ a ∈ Finset.Ico (⌊X * Real.exp (-A)⌋₊ + 1) (⌊X⌋₊ + 1), f a := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by ring
        _ = chebyshevPsi (Real.exp A) * (F_count f X - F_count f (X * Real.exp (-A))) := by
              congr 1
              rw [Finset.sum_Ico_eq_sub _] <;> norm_num [Finset.sum_range_succ, F_count]
              exact Nat.floor_mono <|
                mul_le_of_le_one_right
                  (by linarith [Real.exp_pos (A + chebyshevPsi (Real.exp A))])
                  (Real.exp_le_one_iff.mpr <| by linarith [Real.log_nonneg one_le_two])
    rw [ ← Finset.sum_range_add_sum_Ico _ ( show ⌊X * Real.exp ( -A ) ⌋₊ + 1 ≤ ⌊X⌋₊ + 1 from Nat.succ_le_succ <| Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] ) ] ; linarith;
  -- By log_convolution_bound, L_f(X) ≥ (F_f(X) - F_f(X·e^{-A})) · (log X - A).
  have h_log_conv_lower : L_count f X ≥ (F_count f X - F_count f (X * Real.exp (-A))) * (Real.log X - A) := by
    -- Every integer counted by $D$ is larger than $X \cdot e^{-A}$, so $D \cdot (\log X - A) \leq L_f(X)$.
    have h_log_conv_lower : ∑ a ∈ Finset.Icc (⌊X * Real.exp (-A)⌋₊ + 1) ⌊X⌋₊, f a * Real.log a ≥ (F_count f X - F_count f (X * Real.exp (-A))) * (Real.log X - A) := by
      have h_log_conv_lower : ∀ a ∈ Finset.Icc (⌊X * Real.exp (-A)⌋₊ + 1) ⌊X⌋₊, f a * Real.log a ≥ f a * (Real.log X - A) := by
        intros a ha
        have h_log_a : Real.log a ≥ Real.log X - A := by
          have h_log_a : Real.log a ≥ Real.log (X * Real.exp (-A)) := by
            exact Real.log_le_log ( mul_pos ( lt_trans ( by positivity ) hX ) ( Real.exp_pos _ ) ) ( Nat.lt_of_floor_lt ( Finset.mem_Icc.mp ha |>.1 ) |> le_of_lt );
          rw [ Real.log_mul ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) ( by positivity ), Real.log_exp ] at h_log_a ; linarith;
        exact mul_le_mul_of_nonneg_left h_log_a <| by cases hf.1 a <;> linarith;
      refine le_trans ?_ ( Finset.sum_le_sum h_log_conv_lower );
      erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, F_count ];
      · norm_num [ ← Finset.sum_mul _ _ _ ] ; ring_nf ; norm_num;
      · exact Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] ;
    refine le_trans h_log_conv_lower ?_;
    refine le_trans
      ( Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range ( ⌊X⌋₊ + 1 )) ?_ ?_ ) ?_;
    · exact fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx ] );
    · exact fun i hi₁ hi₂ => mul_nonneg ( by cases hf.1 i <;> linarith ) ( by positivity );
    · exact Finset.sum_le_sum fun _ _ => by aesop;
  rw [ le_div_iff₀ ];
  · -- Since $H_f(X) \geq H_f(X \cdot e^{-A})$, we can replace $H_f(X \cdot e^{-A})$ with $H_f(X)$ in the inequality.
    have h_H_ge : H_count f X ≥ H_count f (X * Real.exp (-A)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_;
      · exact Finset.range_mono ( Nat.succ_le_succ <| Nat.floor_mono <| mul_le_of_le_one_right ( by linarith [ Real.exp_pos ( A + chebyshevPsi ( Real.exp A ) ) ] ) <| Real.exp_le_one_iff.mpr <| by linarith [ Real.log_nonneg one_le_two ] );
      · exact fun i hi₁ hi₂ => div_nonneg ( by cases hf.1 i <;> linarith ) ( Nat.cast_nonneg _ );
    nlinarith [ show 0 ≤ ( 1 + 1.66 / A ^ 2 ) * X by exact mul_nonneg ( add_nonneg zero_le_one <| div_nonneg ( by norm_num ) <| sq_nonneg _ ) <| le_of_lt <| lt_trans ( by positivity ) hX ];
  · linarith [ Real.log_exp ( A + chebyshevPsi ( Real.exp A ) ), Real.log_lt_log ( by positivity ) hX ]

/-
Trivial bound: F_f(X) ≤ 1 + X · H_f(X)
-/
lemma F_le_one_add_X_H (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) :
    F_count f X ≤ 1 + X * H_count f X := by
  -- Apply the trivial bound to each term in the sum.
  have h_sum_bound : ∑ m ∈ Finset.range (⌊X⌋₊ + 1), f m ≤ ∑ m ∈ Finset.range (⌊X⌋₊ + 1), (if m = 0 then 1 else X * f m / m) := by
    -- For each term in the sum, if m is not zero, then f(m) ≤ X * f(m) / m. This follows from the fact that m ≤ X.
    have h_term_bound : ∀ m ∈ Finset.range (⌊X⌋₊ + 1), m ≠ 0 → f m ≤ X * f m / m := by
      intro m hm hm'; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hm' ) ] ; nlinarith [ show ( m : ℝ ) ≤ X by exact le_trans ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp hm ) <| Nat.floor_le <| by positivity, show ( f m : ℝ ) ≥ 0 by cases hf.1 m <;> linarith ] ;
    gcongr;
    split_ifs <;> simp_all +decide;
    cases hf.1 0 <;> linarith;
  simp_all +decide [ Finset.sum_range_succ', F_count, H_count ];
  simpa only [ mul_div_assoc, Finset.mul_sum _ _ _, add_comm ] using h_sum_bound

/-
H_f is monotone: H_f(Y) ≤ H_f(X) for Y ≤ X
-/
lemma H_count_mono (f : ℕ → ℝ) (hf : CompMult01 f) (X Y : ℝ) (hY : Y ≤ X) :
    H_count f Y ≤ H_count f X := by
  apply Finset.sum_le_sum_of_subset_of_nonneg;
  · exact Finset.range_mono ( Nat.succ_le_succ ( Nat.floor_mono hY ) );
  · exact fun i hi₁ hi₂ => div_nonneg ( by cases hf.1 i <;> linarith ) ( Nat.cast_nonneg _ )

lemma H_count_ge_one (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) :
    1 ≤ H_count f X := by
  unfold H_count
  have h1 : (1 : ℕ) ∈ Finset.range (⌊X⌋₊ + 1) := by
    simp only [Finset.mem_range]; have : ⌊X⌋₊ ≥ 1 := Nat.floor_pos.mpr hX; omega
  have h2 : ∀ i ∈ Finset.range (⌊X⌋₊ + 1), 0 ≤ f i / (i : ℝ) := by
    intro m _; rcases hf.1 m with h | h <;> simp [h, Nat.cast_nonneg]
  have h3 := Finset.single_le_sum h2 h1
  simp [hf.2.1] at h3; linarith

lemma H_count_nonneg (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) :
    0 ≤ H_count f X := by
  unfold H_count
  exact Finset.sum_nonneg fun m _ => by
    rcases hf.1 m with h | h <;> simp [h, Nat.cast_nonneg]

/-
Block estimate iterated J times with uniform denominator bound L
-/
lemma block_estimate_iter (A : ℝ) (hA : A > Real.log 2) (f : ℕ → ℝ)
    (hf : CompMult01 f) (X : ℝ) (J : ℕ)
    (hXj : ∀ j : ℕ, j < J → X * Real.exp (-(j : ℝ) * A) >
      Real.exp (A + chebyshevPsi (Real.exp A)))
    (hXpos : X > 0) (L : ℝ) (hLpos : L > 0)
    (hLbound : ∀ j : ℕ, j < J → Real.log (X * Real.exp (-(j : ℝ) * A)) -
      A - chebyshevPsi (Real.exp A) ≥ L) :
    F_count f X ≤ F_count f (X * Real.exp (-(J : ℝ) * A)) +
      (1 + 1.66 / A ^ 2) * X * H_count f X / L *
        ∑ j ∈ Finset.range J, Real.exp (-(j : ℝ) * A) := by
  induction J with
  | zero => norm_num;
  | succ J ih =>
    have h_block :
        F_count f (X * Real.exp (-J * A)) -
            F_count f (X * Real.exp (-(J + 1) * A)) ≤
          (1 + 1.66 / A ^ 2) * X * Real.exp (-J * A) *
              H_count f (X * Real.exp (-J * A)) / L := by
      have hbe :=
        block_estimate A hA f hf (X * Real.exp (-(J : ℝ) * A))
          (hXj J (Nat.lt_succ_self J))
      have hden :
          L ≤
            Real.log (X * Real.exp (-(J : ℝ) * A)) - A -
              chebyshevPsi (Real.exp A) :=
        hLbound J (Nat.lt_succ_self J)
      have hnum_nonneg :
          0 ≤
            (1 + 1.66 / A ^ 2) * (X * Real.exp (-(J : ℝ) * A)) *
              H_count f (X * Real.exp (-(J : ℝ) * A)) := by
        refine mul_nonneg (mul_nonneg ?_ ?_) (H_count_nonneg f hf _)
        · positivity
        · exact mul_nonneg hXpos.le (Real.exp_nonneg _)
      have hden_step :
          (1 + 1.66 / A ^ 2) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) /
              (Real.log (X * Real.exp (-(J : ℝ) * A)) - A -
                chebyshevPsi (Real.exp A)) ≤
            (1 + 1.66 / A ^ 2) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) / L := by
        exact div_le_div_of_nonneg_left hnum_nonneg hLpos hden
      have hstep := le_trans hbe hden_step
      have hxexp :
          X * Real.exp (-(J + 1 : ℝ) * A) =
            X * Real.exp (-(J : ℝ) * A) * Real.exp (-A) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        norm_num
        ring
      have hxexp_norm :
          X * Real.exp ((-1 + -(J : ℝ)) * A) =
            X * Real.exp (-(J : ℝ) * A) * Real.exp (-A) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      have hxexp_norm' :
          X * Real.exp (-A + -(J : ℝ) * A) =
            X * Real.exp (-(J : ℝ) * A) * Real.exp (-A) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      have hdiv_norm :
          (X * Real.exp (-(J : ℝ) * A) * H_count f (X * Real.exp (-(J : ℝ) * A)) +
              1.66 / A ^ 2 * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A))) / L =
            (X * Real.exp (-(J : ℝ) * A) * H_count f (X * Real.exp (-(J : ℝ) * A)) +
              1.66 / A ^ 2 * X * Real.exp (-(J : ℝ) * A) *
                H_count f (X * Real.exp (-(J : ℝ) * A))) / L := by
        ring
      have hrhs :
          (1 + 1.66 / A ^ 2) * (X * Real.exp (-(J : ℝ) * A)) *
                H_count f (X * Real.exp (-(J : ℝ) * A)) / L =
            (1 + 1.66 / A ^ 2) * X * Real.exp (-J * A) *
                H_count f (X * Real.exp (-J * A)) / L := by
        ring
      rw [hxexp]
      rw [← hrhs]
      exact hstep
    have h_monotone : H_count f (X * Real.exp (-J * A)) ≤ H_count f X := by
      apply H_count_mono;
      · exact hf;
      · exact mul_le_of_le_one_right hXpos.le ( Real.exp_le_one_iff.mpr <| by nlinarith [ Real.log_nonneg one_le_two ] );
    have h_combined : F_count f X ≤ F_count f (X * Real.exp (-(J + 1) * A)) + (1 + 1.66 / A ^ 2) * X * H_count f X / L * (∑ j ∈ Finset.range J, Real.exp (-j * A)) + (1 + 1.66 / A ^ 2) * X * Real.exp (-J * A) * H_count f X / L := by
      have h_combined : F_count f X ≤ F_count f (X * Real.exp (-J * A)) + (1 + 1.66 / A ^ 2) * X * H_count f X / L * (∑ j ∈ Finset.range J, Real.exp (-j * A)) := by
        exact ih ( fun j hj => hXj j ( Nat.lt_succ_of_lt hj ) ) ( fun j hj => hLbound j ( Nat.lt_succ_of_lt hj ) );
      have h_combined : (1 + 1.66 / A ^ 2) * X * Real.exp (-J * A) * H_count f (X * Real.exp (-J * A)) / L ≤ (1 + 1.66 / A ^ 2) * X * Real.exp (-J * A) * H_count f X / L := by
        gcongr;
      grind;
    convert h_combined using 1 ; push_cast [ Finset.sum_range_succ ] ; ring

lemma geom_sum_le (A : ℝ) (hA : A > 0) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.exp (-(j : ℝ) * A) ≤ 1 / (1 - Real.exp (-A)) := by
  have h_geo_series : ∑ j ∈ Finset.range J, (Real.exp (-A)) ^ j ≤ 1 / (1 - Real.exp (-A)) := by
    rw [ le_div_iff₀ ] <;> nlinarith [ Real.exp_pos ( -A ), Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ), pow_pos ( Real.exp_pos ( -A ) ) J, geom_sum_mul ( Real.exp ( -A ) ) J ];
  convert h_geo_series using 2 ; norm_num [ ← Real.exp_nat_mul ]

lemma delta_limit :
    Filter.Tendsto (fun A : ℝ => (1 + 1.66 / A ^ 2) / (1 - Real.exp (-A)))
      Filter.atTop (nhds 1) := by
  exact le_trans ( Filter.Tendsto.div ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| by norm_num ) ( tendsto_const_nhds.sub <| Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot ) <| by norm_num ) <| by norm_num;

lemma choose_A (ε : ℝ) (hε : ε > 0) :
    ∃ A : ℝ, A > Real.log 2 ∧ A > 0 ∧
      (1 + 1.66 / A ^ 2) / (1 - Real.exp (-A)) < 1 + ε := by
  have := delta_limit;
  exact Filter.eventually_atTop.mp ( this.eventually ( gt_mem_nhds <| show 1 < 1 + ε by linarith ) ) |> fun ⟨ A, hA ⟩ ↦ ⟨ Max.max A ( Real.log 2 + 1 ), by linarith [ le_max_left A ( Real.log 2 + 1 ), le_max_right A ( Real.log 2 + 1 ) ], by linarith [ le_max_left A ( Real.log 2 + 1 ), le_max_right A ( Real.log 2 + 1 ), Real.log_nonneg one_le_two ], hA _ <| le_max_left _ _ ⟩

lemma log_div_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
  -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
  suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
    exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
  norm_num;
  exact tendsto_nhdsWithin_of_tendsto_nhds ( by
    have h := Real.continuous_mul_log.tendsto 0
    simpa using h.neg )

/-
For large X, the denominator in the block estimate is close to log X.
-/
lemma mean_L_improved (A : ℝ) (hA : A > 0) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ X₀ : ℝ, X₀ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₀ →
      ∀ J : ℕ, (J : ℝ) ≤ 2 * Real.log (Real.log X) / A + 1 →
        ∀ j : ℕ, j < J →
          Real.log (X * Real.exp (-(j : ℝ) * A)) - A - chebyshevPsi (Real.exp A) ≥
            (1 - ε₁) * Real.log X := by
  -- We need to ensure that $2 \log(\log X) + A + \psi(e^A) \leq \epsilon_1 \log X$ for sufficiently large $X$.
  have h_log_log : Filter.Tendsto (fun X : ℝ => (2 * Real.log (Real.log X) + A + chebyshevPsi (Real.exp A)) / Real.log X) Filter.atTop (nhds 0) := by
    ring_nf;
    -- We'll use the fact that $\frac{\log(\log X)}{\log X}$ tends to $0$ as $X$ tends to infinity.
    have h_log_log : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X) / Real.log X) Filter.atTop (nhds 0) := by
      refine (log_div_tendsto_zero.comp Real.tendsto_log_atTop).congr' ?_
      exact Filter.Eventually.of_forall fun X => by rfl
    have h_inv_log :
        Filter.Tendsto (fun X : ℝ => (Real.log X)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hAterm :
        Filter.Tendsto (fun X : ℝ => A * (Real.log X)⁻¹) Filter.atTop (nhds 0) :=
      by simpa using tendsto_const_nhds.mul h_inv_log
    have hPterm :
        Filter.Tendsto
          (fun X : ℝ => chebyshevPsi (Real.exp A) * (Real.log X)⁻¹)
          Filter.atTop (nhds 0) :=
      by simpa using tendsto_const_nhds.mul h_inv_log
    have hsum :
        Filter.Tendsto
          (fun X : ℝ =>
            2 * (Real.log (Real.log X) / Real.log X) +
              A * (Real.log X)⁻¹ +
              chebyshevPsi (Real.exp A) * (Real.log X)⁻¹)
          Filter.atTop (nhds 0) :=
      by simpa [add_assoc] using (h_log_log.const_mul 2).add (hAterm.add hPterm)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, add_assoc] using hsum
  -- By the definition of limit, there exists an X₀ such that for all X ≥ X₀, (2 * log(log X) + A + ψ(e^A)) / log X < ε₁.
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ X ≥ X₀, (2 * Real.log (Real.log X) + A + chebyshevPsi (Real.exp A)) / Real.log X < ε₁ := by
    simpa using h_log_log.eventually ( gt_mem_nhds hε₁ );
  refine ⟨ Max.max X₀ 2, le_max_right _ _, fun X hX J hJ j hj => ?_ ⟩ ; specialize hX₀ X ( le_trans ( le_max_left _ _ ) hX ) ; rw [ div_lt_iff₀ ] at hX₀ <;> norm_num at *;
  · rw [ Real.log_mul ( by linarith ) ( by positivity ), Real.log_exp ];
    rw [ div_add_one, le_div_iff₀ ] at hJ <;> nlinarith [ show ( j : ℝ ) + 1 ≤ J by norm_cast ];
  · exact Real.log_pos <| by linarith

/-
For large X, the tail F_f(X·e^{-JA}) + 1 is bounded by ε * X/log X * H_f(X).
-/
set_option maxHeartbeats 1600000 in
-- The tail estimate combines several asymptotic bounds through generated arithmetic.
lemma mean_tail_small (A : ℝ) (hA : A > Real.log 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, X₀ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      ∀ J : ℕ, (J : ℝ) * A ≥ 2 * Real.log (Real.log X) →
        F_count f (X * Real.exp (-(J : ℝ) * A)) + 1 ≤
          ε * X / Real.log X * H_count f X := by
  -- By definition of $F_count$, we know that $F_count f (X * Real.exp (-J * A)) \leq 1 + X * Real.exp (-J * A) * H_count f X$.
  have hF_count_bound : ∀ (f : ℕ → ℝ) (hf : CompMult01 f) (X : ℝ) (hX : X ≥ 1) (J : ℕ), F_count f (X * Real.exp (-J * A)) ≤ 1 + X * Real.exp (-J * A) * H_count f X := by
    intros f hf X hX J
    have hF_count_bound : F_count f (X * Real.exp (-J * A)) ≤ 1 + (X * Real.exp (-J * A)) * H_count f (X * Real.exp (-J * A)) := by
      by_cases hX' : X * Real.exp ( -J * A ) ≥ 1;
      · convert F_le_one_add_X_H f hf ( X * Real.exp ( -J * A ) ) hX' using 1;
      · unfold F_count H_count; norm_num [ Nat.floor_eq_zero.mpr ( not_le.mp hX' ) ] ;
        norm_num [ show ⌊X * Real.exp ( - ( J * A ) ) ⌋₊ = 0 by exact Nat.floor_eq_zero.mpr <| by simpa using hX' ];
        cases hf.1 0 <;> linarith;
    refine le_trans hF_count_bound ?_;
    gcongr;
    exact H_count_mono f hf X _ ( mul_le_of_le_one_right ( by positivity ) ( Real.exp_le_one_iff.mpr ( by nlinarith [ Real.log_pos one_lt_two ] ) ) );
  -- For large X, X·e^{-JA} ≤ X/(log X)².
  have h_exp_bound : ∃ X₀ ≥ 2, ∀ X ≥ X₀, ∀ J : ℕ, J * A ≥ 2 * Real.log (Real.log X) → X * Real.exp (-J * A) ≤ X / (Real.log X) ^ 2 := by
    refine ⟨ Real.exp 2, ?_, ?_ ⟩ <;> norm_num;
    · linarith [ Real.add_one_le_exp 2 ];
    · intro X hX J hJ; rw [ div_eq_mul_inv ] ; rw [ ← Real.log_le_log_iff ( by exact mul_pos ( by linarith [ Real.exp_pos 2 ] ) ( Real.exp_pos _ ) ) ( by exact mul_pos ( by linarith [ Real.exp_pos 2 ] ) ( inv_pos.mpr ( sq_pos_of_pos ( Real.log_pos ( by linarith [ Real.add_one_le_exp 2 ] ) ) ) ) ), Real.log_mul ( by linarith [ Real.exp_pos 2 ] ) ( by positivity ), Real.log_exp ] ; ring_nf;
      rw [ Real.log_mul ( by linarith [ Real.exp_pos 2 ] ) ( by exact ne_of_gt ( sq_pos_of_pos ( inv_pos.mpr ( Real.log_pos ( by linarith [ Real.add_one_le_exp 2 ] ) ) ) ) ), Real.log_pow, Real.log_inv ] ; norm_num ; linarith [ Real.log_pos ( show 1 < X by linarith [ Real.add_one_le_exp 2 ] ) ];
  -- By combining the results from hF_count_bound and h_exp_bound, we can derive the desired inequality.
  obtain ⟨X₀, hX₀_ge_2, hX₀_bound⟩ := h_exp_bound;
  have h_combined_bound : ∃ X₁ ≥ X₀, ∀ X ≥ X₁, ∀ f : ℕ → ℝ, CompMult01 f → ∀ J : ℕ, J * A ≥ 2 * Real.log (Real.log X) → 2 + X * Real.exp (-J * A) * H_count f X ≤ ε * X / Real.log X * H_count f X := by
    have h_combined_bound : ∃ X₁ ≥ X₀, ∀ X ≥ X₁, 2 + X / (Real.log X) ^ 2 ≤ ε * X / Real.log X := by
      have h_combined_bound : Filter.Tendsto (fun X : ℝ => (2 + X / (Real.log X) ^ 2) / (X / Real.log X)) Filter.atTop (nhds 0) := by
        -- Simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun X : ℝ => 2 * Real.log X / X + 1 / Real.log X) Filter.atTop (nhds 0) by
          refine h_simplify.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with X hX;
          grind;
        -- We'll use the fact that $\frac{\log X}{X}$ tends to $0$ as $X$ tends to infinity.
        have h_log_div_X : Filter.Tendsto (fun X : ℝ => Real.log X / X) Filter.atTop (nhds 0) := by
          grind +suggestions;
        simpa [ mul_div_assoc ] using Filter.Tendsto.add ( h_log_div_X.const_mul 2 ) ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) );
      have := h_combined_bound.eventually ( gt_mem_nhds <| show 0 < ε by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₁, hX₁ ⟩ ; exact ⟨ Max.max X₀ X₁, le_max_left _ _, fun X hX => by have := hX₁ X ( le_trans ( le_max_right _ _ ) hX ) ; rw [ div_lt_iff₀ ( div_pos ( by linarith [ le_max_left X₀ X₁, le_max_right X₀ X₁ ] ) ( Real.log_pos ( by linarith [ le_max_left X₀ X₁, le_max_right X₀ X₁ ] ) ) ) ] at this; ring_nf at *; linarith ⟩ ;
    obtain ⟨ X₁, hX₁₁, hX₁₂ ⟩ := h_combined_bound;
    use X₁, hX₁₁;
    intros X hX f hf J hJ;
    refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( hX₁₂ X hX ) ( H_count_nonneg f hf X ) );
    rw [ add_mul ];
    gcongr;
    · exact le_mul_of_one_le_right ( by norm_num ) ( H_count_ge_one f hf X ( by linarith ) );
    · exact H_count_nonneg f hf X;
    · exact hX₀_bound X ( by linarith ) J hJ;
  obtain ⟨ X₁, hX₁₁, hX₁₂ ⟩ := h_combined_bound; exact ⟨ X₁, by linarith, fun X hX f hf J hJ => by linarith [ hF_count_bound f hf X ( by linarith ) J, hX₁₂ X hX f hf J hJ ] ⟩ ;

set_option maxHeartbeats 6400000 in
-- The fixed-A mean estimate contains the largest generated block estimate.
lemma mean_estimate_fixed_A (A : ℝ) (hA : A > Real.log 2) (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      F_count f X ≤ ((1 + 1.66 / A ^ 2) / (1 - Real.exp (-A)) + ε) *
        X / Real.log X * H_count f X := by
  -- Choose ε₁ ∈ (0,1) small enough that (1+1.66/A²)/((1-ε₁)·(1-e^{-A})) ≤ (1+1.66/A²)/(1-e^{-A}) + ε/2.
  obtain ⟨ε₁, hε₁_pos, hε₁_small⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ < 1 ∧ (1 + 1.66 / A ^ 2) / ((1 - ε₁) * (1 - Real.exp (-A))) ≤ (1 + 1.66 / A ^ 2) / (1 - Real.exp (-A)) + ε / 2 := by
    have h_lim : Filter.Tendsto (fun ε₁ : ℝ => (1 + 1.66 / A ^ 2) / ((1 - ε₁) * (1 - Real.exp (-A)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 + 1.66 / A ^ 2) / (1 - Real.exp (-A)))) := by
      have hlim0 :
          Filter.Tendsto
            ((fun _ : ℝ => 1 + 1.66 / A ^ 2) /
              fun ε₁ : ℝ => (1 - ε₁) * (1 - Real.exp (-A)))
            (nhds 0) (nhds ((1 + 1.66 / A ^ 2) / (1 - Real.exp (-A)))) :=
        tendsto_const_nhds.div
          (by
            simpa using
              Continuous.tendsto
                (show Continuous fun ε₁ : ℝ =>
                  (1 - ε₁) * (1 - Real.exp (-A)) by continuity)
                0)
          (show 1 - Real.exp (-A) ≠ 0 by
            exact sub_ne_zero_of_ne
              (Ne.symm
                (by
                  norm_num
                  linarith [Real.log_pos one_lt_two])))
      exact tendsto_nhdsWithin_of_tendsto_nhds
        (hlim0.congr' <| Filter.Eventually.of_forall fun ε₁ => by rfl)
    have := h_lim.eventually ( ge_mem_nhds <| show ( 1 + 1.66 / A ^ 2 ) / ( 1 - Real.exp ( -A ) ) < ( 1 + 1.66 / A ^ 2 ) / ( 1 - Real.exp ( -A ) ) + ε / 2 by linarith ) ; have := this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ; obtain ⟨ ε₁, hε₁₁, hε₁₂ ⟩ := this.exists ; exact ⟨ ε₁, hε₁₂.1, hε₁₂.2, hε₁₁ ⟩ ;
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₁ → ∀ J : ℕ, (J : ℝ) ≤ 2 * Real.log (Real.log X) / A + 1 → ∀ j : ℕ, j < J → Real.log (X * Real.exp (-(j : ℝ) * A)) - A - chebyshevPsi (Real.exp A) ≥ (1 - ε₁) * Real.log X := by
    apply mean_L_improved A (by linarith [Real.log_pos one_lt_two]) ε₁ hε₁_pos;
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : ℝ, X₂ ≥ 2 ∧ ∀ X : ℝ, X ≥ X₂ → ∀ f : ℕ → ℝ, CompMult01 f → ∀ J : ℕ, (J : ℝ) * A ≥ 2 * Real.log (Real.log X) → F_count f (X * Real.exp (-(J : ℝ) * A)) + 1 ≤ ε / 2 * X / Real.log X * H_count f X := by
    convert mean_tail_small A hA ( ε / 2 ) ( half_pos hε ) using 1;
  refine ⟨ Max.max X₁ X₂, fun X hX f hf => ?_ ⟩;
  by_cases hX_pos : 0 < X;
  · by_cases h_log_pos : 0 < Real.log X;
    · have h_block : F_count f X ≤ F_count f (X * Real.exp (-(Nat.ceil (2 * Real.log (Real.log X) / A) : ℝ) * A)) + (1 + 1.66 / A ^ 2) * X * H_count f X / ((1 - ε₁) * Real.log X) * (∑ j ∈ Finset.range (Nat.ceil (2 * Real.log (Real.log X) / A)), Real.exp (-(j : ℝ) * A)) := by
        apply block_estimate_iter;
        all_goals norm_num [ hA, hε₁_pos, hε₁_small, hX_pos, h_log_pos ];
        · exact hf;
        · intro j hj;
          have := hX₁.2 X ( le_trans ( le_max_left _ _ ) hX ) ( Nat.ceil ( 2 * Real.log ( Real.log X ) / A ) ) ( by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ 2 * Real.log ( Real.log X ) / A by exact div_nonneg ( mul_nonneg zero_le_two ( Real.log_nonneg ( show 1 ≤ Real.log X from by
                                                                                                                                                                                                                                                                contrapose! hj;
                                                                                                                                                                                                                                                                rw [ Nat.ceil_eq_zero.mpr ] <;> norm_num;
                                                                                                                                                                                                                                                                exact div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos zero_le_two ( Real.log_nonpos h_log_pos.le hj.le ) ) ( by linarith [ Real.log_pos one_lt_two ] ) ) ) ) ( by linarith [ Real.log_pos one_lt_two ] ) ) ] ) j hj;
          rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] at this;
          rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ];
          norm_num; nlinarith [ Real.log_pos one_lt_two ];
        · simp +zetaDelta at *;
          exact fun j hj => hX₁.2 X hX.1 _ ( by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ 2 * Real.log ( Real.log X ) / A by exact div_nonneg ( mul_nonneg zero_le_two ( Real.log_nonneg ( show 1 ≤ Real.log X from by
                                                                                                                                                                                            contrapose! hj;
                                                                                                                                                                                            rw [ Nat.ceil_eq_zero.mpr ] <;> norm_num;
                                                                                                                                                                                            exact div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonneg_of_nonpos zero_le_two ( Real.log_nonpos h_log_pos.le hj.le ) ) ( by linarith [ Real.log_nonneg one_le_two ] ) ) ) ) ( by linarith [ Real.log_nonneg one_le_two ] ) ) ] ) _ hj;
      have h_tail : F_count f (X * Real.exp (-(Nat.ceil (2 * Real.log (Real.log X) / A) : ℝ) * A)) + 1 ≤ ε / 2 * X / Real.log X * H_count f X := by
        apply hX₂.right X (by
        exact le_trans ( le_max_right _ _ ) hX) f hf (Nat.ceil (2 * Real.log (Real.log X) / A)) (by
        nlinarith [ Nat.le_ceil ( 2 * Real.log ( Real.log X ) / A ), show 0 < A by linarith [ Real.log_pos one_lt_two ], mul_div_cancel₀ ( 2 * Real.log ( Real.log X ) ) ( show A ≠ 0 by linarith [ Real.log_pos one_lt_two ] ) ]);
      have h_geom_sum : ∑ j ∈ Finset.range (Nat.ceil (2 * Real.log (Real.log X) / A)), Real.exp (-(j : ℝ) * A) ≤ 1 / (1 - Real.exp (-A)) := by
        convert geom_sum_le A ( show 0 < A by linarith [ Real.log_pos one_lt_two ] ) ⌈2 * Real.log ( Real.log X ) / A⌉₊ using 1;
      have h_combined : F_count f X ≤ (ε / 2 * X / Real.log X * H_count f X - 1) + (1 + 1.66 / A ^ 2) * X * H_count f X / ((1 - ε₁) * Real.log X) * (1 / (1 - Real.exp (-A))) := by
        refine le_trans h_block ?_;
        refine add_le_add ?_ ?_;
        · linarith;
        · exact mul_le_mul_of_nonneg_left h_geom_sum <| div_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) <| by positivity ) <| H_count_nonneg f hf X ) <| mul_nonneg ( by linarith ) <| by positivity;
      have h_combined : F_count f X ≤ (ε / 2 * X / Real.log X * H_count f X - 1) + ((1 + 1.66 / A ^ 2) / (1 - Real.exp (-A)) + ε / 2) * X / Real.log X * H_count f X := by
        refine le_trans h_combined ?_;
        norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] at *;
        exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( by nlinarith [ inv_pos.mpr h_log_pos ] ) ( H_count_nonneg f hf X ) ) hX_pos.le;
      grind;
    · exact False.elim <| h_log_pos <| Real.log_pos <| by linarith [ le_max_left X₁ X₂, le_max_right X₁ X₂ ] ;
  · linarith [ le_max_left X₁ X₂, le_max_right X₁ X₂ ]

set_option maxHeartbeats 3200000 in
-- The final mean estimate depends on the fixed-A estimate and coefficient comparison.
theorem mean_estimate (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ → ∀ f : ℕ → ℝ, CompMult01 f →
      F_count f X ≤ (1 + ε) * X / Real.log X * H_count f X := by
  obtain ⟨A, hA_log2, hA_pos, hA_bound⟩ := choose_A (ε / 2) (by linarith)
  obtain ⟨X₀, hX₀⟩ := mean_estimate_fixed_A A hA_log2 (ε / 2) (by linarith)
  refine ⟨max X₀ 1, fun X hX f hf => le_trans (hX₀ X (le_of_max_le_left hX) f hf) ?_⟩
  have hcoeff : (1 + 1.66 / A ^ 2) / (1 - Real.exp (-A)) + ε / 2 ≤ 1 + ε := by linarith
  have hH := H_count_nonneg f hf X
  have hX1 : (1 : ℝ) ≤ X := le_of_max_le_right hX
  have hlog := Real.log_nonneg hX1
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by linarith)) hlog) hH

/-! ## Asymptotic upper-bound sieve -/

/-
Let X → ∞ and P ⊆ primes ∩ [X]. Then
    |{m ∈ [X] : p ∤ m ∀ p ∈ P}| ≤ (e^γ + o(1)) · X · ∏_{p∈P}(1-1/p).
-/
theorem sieve_bound (ε : ℝ) (hε : ε > 0) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X ≥ X₀ →
      ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ (p : ℝ) ≤ X) →
        (((Finset.range (⌊X⌋₊ + 1)).filter
          (fun m => m ≥ 1 ∧ ∀ p ∈ P, ¬(p ∣ m))).card : ℝ) ≤
          (Real.exp γ + ε) * X * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  obtain ⟨ X₁, hX₁ ⟩ := mean_estimate ( ε / 2 / ( Real.exp γ + ε ) ) ( by positivity );
  -- By Mertens' product theorem, there exists $X₂$ such that for all $X ≥ X₂$, $\prod_{p ≤ X} (1 - 1/p)^{-1} ≤ (e^γ + ε/2) \log X$.
  obtain ⟨ X₂, hX₂ ⟩ : ∃ X₂ : ℝ, ∀ X ≥ X₂, (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) ≤ (Real.exp γ + ε / 2) * Real.log X := by
    have h_mertens : Filter.Tendsto (fun X : ℝ => (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))) * Real.log X) Filter.atTop (nhds (Real.exp (-γ))) := by
      have := mertens_product_estimate;
      rw [ Metric.tendsto_nhds ];
      intro ε hε; rcases this ( ε / 2 ) ( half_pos hε ) with ⟨ X₀, HX₀ ⟩ ; filter_upwards [ Filter.eventually_ge_atTop X₀, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂; specialize HX₀ x hx₁; rw [ dist_eq_norm ] ; rw [ Real.norm_eq_abs ] ; rw [ abs_lt ] ; constructor <;> nlinarith [ abs_le.mp HX₀, Real.log_pos hx₂, mul_div_cancel₀ ( ε / 2 ) ( ne_of_gt ( Real.log_pos hx₂ ) ), mul_div_cancel₀ ( Real.exp ( -γ ) ) ( ne_of_gt ( Real.log_pos hx₂ ) ) ] ;
    have h_mertens_inv : Filter.Tendsto (fun X : ℝ => (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) / Real.log X) Filter.atTop (nhds (Real.exp γ)) := by
      have := h_mertens.inv₀ ; simp_all +decide [ Real.exp_neg ];
      simpa only [ div_eq_inv_mul ] using this;
    have := h_mertens_inv.eventually ( gt_mem_nhds <| show Real.exp γ < Real.exp γ + ε / 2 by linarith );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X₂, hX₂ ⟩ ; exact ⟨ Max.max X₂ 2, fun X hX => by have := hX₂ X ( le_trans ( le_max_left _ _ ) hX ) ; rw [ div_lt_iff₀ ( Real.log_pos <| by linarith [ le_max_right X₂ 2 ] ) ] at this; linarith ⟩ ;
  refine ⟨ Max.max X₁ ( Max.max X₂ 2 ), fun X hX P hP => ?_ ⟩ ; specialize hX₁ X ( le_trans ( le_max_left ?_ ?_ ) hX ) ( fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0 ) ?_
  focus
    simp_all +decide [ F_count, H_count ]
  · constructor <;> norm_num;
    · exact fun m => Classical.or_iff_not_imp_left.2 fun h => by push Not at h; exact h;
    · constructor;
      · exact fun h => Nat.not_prime_one ( hP _ h |>.1 );
      · intro a b ha hb; split_ifs <;> simp_all +decide [ Nat.Prime.dvd_mul ] ;
  · -- By Euler product bound, we have $H_f(X) \leq \prod_{p \leq X, p \notin P} (1 - 1/p)^{-1}$.
    have h_euler : H_count (fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0) X ≤ (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) := by
      have h_euler : H_count (fun m => if ∀ p ∈ P, ¬p ∣ m then 1 else 0) X ≤ ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) := by
        unfold H_count; simp +decide ;
        erw [ Finset.sum_filter, Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
        exact Finset.sum_le_sum fun _ _ => by split_ifs <;> ring_nf <;> norm_num;
      -- The sum $\sum_{m \leq X, \forall p \in P, \neg p \mid m} \frac{1}{m}$ is bounded above by the product $\prod_{p \leq X, p \notin P} (1 - 1/p)^{-1}$.
      have h_sum_bound : ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) ≤ ∏ p ∈ primesUpTo X \ P, (∑ k ∈ Finset.range (Nat.log p ⌊X⌋₊ + 1), (1 / (p ^ k : ℝ))) := by
        have h_sum_bound : ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (1 / (m : ℝ)) ≤ ∑ m ∈ Finset.filter (fun m => ∀ p ∈ P, ¬p ∣ m) (Finset.Icc 1 ⌊X⌋₊), (∏ p ∈ primesUpTo X \ P, (1 / (p ^ (Nat.factorization m p) : ℝ))) := by
          refine Finset.sum_le_sum fun m hm => ?_;
          have h_factorization : m = ∏ p ∈ primesUpTo X \ P, p ^ (Nat.factorization m p) := by
            conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) ] : m ≠ 0 ) ] ;
            rw [ Finsupp.prod_of_support_subset ] <;> simp_all +decide [ Finset.subset_iff ];
            exact fun p pp dp _ => ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_dvd hm.1.1 dp ) hm.1.2 ) ), pp ⟩, fun hp => hm.2 p hp dp ⟩;
          rw [ h_factorization, Nat.cast_prod ];
          norm_num [ ← h_factorization ];
        refine le_trans h_sum_bound ?_;
        rw [ Finset.prod_sum ];
        refine le_trans ?_
          ( Finset.sum_le_sum_of_subset_of_nonneg
            (s := Finset.image ( fun m => fun p hp => Nat.factorization m p )
              ( Finset.filter ( fun m => ∀ p ∈ P, ¬p ∣ m ) ( Finset.Icc 1 ⌊X⌋₊ ) ))
            ?_ fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity );
        rotate_left;
        · simp +decide [ Finset.subset_iff ];
          rintro x m hm₁ hm₂ hm₃ rfl p hp hq; exact Nat.le_log_of_pow_le ( Nat.Prime.one_lt ( by unfold primesUpTo at hp; aesop ) ) ( Nat.le_trans ( Nat.le_of_dvd hm₁ ( Nat.ordProj_dvd _ _ ) ) hm₂ ) ;
        · rw [ Finset.sum_image ];
          · exact Finset.sum_le_sum fun x hx => by rw [ ← Finset.prod_attach ] ;
          · intro m hm m' hm' h_eq; simp_all +decide [ funext_iff ] ;
            rw [ ← Nat.prod_factorization_pow_eq_self ( by linarith : m ≠ 0 ), ← Nat.prod_factorization_pow_eq_self ( by linarith : m' ≠ 0 ) ];
            congr! 1;
            ext p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ≤ ⌊X⌋₊ <;> simp_all +decide [ primesUpTo ] ;
            · by_cases hp'' : p ∈ P <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
            · rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => by have := Nat.le_of_dvd ( by linarith ) h; linarith ), Nat.factorization_eq_zero_of_not_dvd ( fun h => by have := Nat.le_of_dvd ( by linarith ) h; linarith ) ];
      refine le_trans h_euler <| h_sum_bound.trans ?_;
      gcongr;
      rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by unfold primesUpTo at *; aesop ) ];
      simpa using Summable.sum_le_tsum ( Finset.range ( Nat.log _ ⌊X⌋₊ + 1 ) ) ( fun _ _ => by positivity ) ( summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by unfold primesUpTo at *; aesop ) ) ) ) );
    -- By Mertens' product theorem, we have $\prod_{p \leq X, p \notin P} (1 - 1/p)^{-1} \leq (e^γ + ε/2) \log X \prod_{p \in P} (1 - 1/p)$.
    have h_mertens : (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) ≤ (Real.exp γ + ε / 2) * Real.log X * (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
      have h_mertens : (∏ p ∈ primesUpTo X \ P, (1 - 1 / (p : ℝ))⁻¹) = (∏ p ∈ primesUpTo X, (1 - 1 / (p : ℝ))⁻¹) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
        rw [ ← Finset.prod_sdiff <| show P ⊆ primesUpTo X from fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| Nat.lt_succ_of_le <| Nat.le_floor <| hP p hp |>.2, hP p hp |>.1 ⟩ ];
        simp +decide ;
        rw [ mul_assoc, inv_mul_cancel₀ ( Finset.prod_ne_zero_iff.mpr fun p hp => sub_ne_zero_of_ne <| by norm_num; linarith [ Nat.Prime.one_lt ( hP p hp |>.1 ) ] ), mul_one ];
      exact h_mertens.symm ▸ mul_le_mul_of_nonneg_right ( hX₂ X ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hX ) ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop );
    refine le_trans ?_ ( hX₁.trans ?_ );
    · unfold F_count; simp +decide ;
      exact Finset.card_mono fun x hx => by aesop;
    · refine le_trans ( mul_le_mul_of_nonneg_left ( h_euler.trans h_mertens ) ?_ ) ?_;
      · exact div_nonneg ( mul_nonneg ( add_nonneg zero_le_one ( div_nonneg ( by positivity ) ( by positivity ) ) ) ( by linarith [ le_max_right X₁ ( max X₂ 2 ), le_max_right X₂ 2 ] ) ) ( Real.log_nonneg ( by linarith [ le_max_right X₁ ( max X₂ 2 ), le_max_right X₂ 2 ] ) );
      · field_simp;
        rw [ div_le_iff₀ ( Real.log_pos <| by linarith [ le_max_right X₁ ( max X₂ 2 ), le_max_right X₂ 2 ] ) ] ; ring_nf;
        gcongr;
        · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( by linarith [ le_max_right X₁ ( max X₂ 2 ), le_max_right X₂ 2 ] ) ) ( Real.log_nonneg ( by linarith [ le_max_right X₁ ( max X₂ 2 ), le_max_right X₂ 2 ] ) ) ) ( Finset.prod_nonneg fun p hp => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| hP p hp |>.1 );
        · norm_num

/-! ## Sifted bounds -/

/-
|S| ≤ (e^γ + o(1)) · n · Π_S(n,λ,k) and union bound for p⁻¹S[p].
-/
theorem sifted_bound_set (ε : ℝ) (hε : ε > 0) (lam : ℝ) (hlam : 1 < lam) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n →
      ((S.card : ℝ) ≤ (Real.exp γ + ε) * n * Pi_sieve n lam k S) := by
  obtain ⟨ N₀, hN₀ ⟩ := sieve_bound ε hε;
  refine ⟨ ⌈N₀⌉₊, fun n hn k S hS =>
    le_trans ?_ ( hN₀ n ( Nat.le_of_ceil_le hn ) (P_sieve n lam k S) ?_ ) ⟩;
  · refine mod_cast Finset.card_le_card ?_;
    intro m hm; specialize hS hm; simp_all +decide [ P_sieve ] ;
    intro p hp₁ hp₂ hp₃ hp₄; rw [ Finset.ext_iff ] at hp₄; specialize hp₄ m; simp_all +decide [ sdiv ] ;
  · simp +zetaDelta at *;
    intro p hp;
    refine ⟨ ?_, ?_ ⟩;
    · exact Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
    · refine le_trans ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.1 ) |>.2 ) ?_;
      exact Nat.floor_le_of_le ( div_le_self ( Nat.cast_nonneg _ ) ( by exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( one_le_pow₀ hlam.le ) zero_le_two ) ) )

theorem sifted_bound_union (ε : ℝ) (hε : ε > 0) (lam : ℝ) (hlam : 1 < lam) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n →
      ∀ L ⊆ (I_layer lam k).filter (fun p => (sdiv S p).Nonempty),
        (((L.biUnion (sinv S ·)).card : ℝ) ≤
          (Real.exp γ + ε) * n / Y_val lam k * Pi_sieve n lam k S) := by
  obtain ⟨ X₀, hX₀ ⟩ := sieve_bound ε hε;
  refine ⟨ ⌈X₀ ^ 2 / lam⌉₊ + 1, fun n hn k S hS L hL => ?_ ⟩;
  by_cases hP : P_sieve n lam k S = ∅;
  · have h_card : (L.biUnion (sinv S ·)).card ≤ n / Y_val lam k := by
      have h_card : (L.biUnion (sinv S ·)).card ≤ Finset.card (Finset.Icc 1 (Nat.floor (n / Y_val lam k))) := by
        refine Finset.card_le_card ?_;
        intro x hx; simp_all +decide [ Finset.subset_iff ] ;
        obtain ⟨ a, ha₁, ha₂ ⟩ := hx; specialize hL ha₁; simp_all +decide [ sinv ] ;
        obtain ⟨ y, hy₁, hy₂ ⟩ := ha₂; have := hS ( Finset.mem_filter.mp hy₁ |>.1 ) ; simp_all +decide [ sdiv ] ;
        have h_div : a ≥ Y_val lam k := by
          exact Nat.le_of_ceil_le ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hL.1 |>.1 ) |>.1 );
        exact ⟨ hy₂ ▸ Nat.div_pos ( Nat.le_of_dvd ( hS hy₁.1 |>.1 ) hy₁.2 ) ( Nat.pos_of_dvd_of_pos hy₁.2 ( hS hy₁.1 |>.1 ) ), Nat.le_floor <| by rw [ le_div_iff₀ <| by exact mul_pos zero_lt_two <| pow_pos ( by positivity ) _ ] ; nlinarith [ show ( y : ℝ ) ≤ n by exact_mod_cast hS hy₁.1 |>.2, show ( a : ℝ ) ≥ Y_val lam k by exact_mod_cast h_div, Nat.div_mul_le_self y a, show ( y : ℝ ) = a * x by exact_mod_cast by nlinarith [ Nat.div_mul_cancel hy₁.2 ] ] ⟩;
      exact le_trans ( Nat.cast_le.mpr h_card ) ( by simpa using Nat.floor_le ( show 0 ≤ ( n : ℝ ) / Y_val lam k by exact div_nonneg ( Nat.cast_nonneg _ ) ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ) );
    refine le_trans h_card ?_;
    rw [ show Pi_sieve n lam k S = 1 from _ ];
    · rw [ mul_one ] ; gcongr;
      · exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ );
      · refine le_mul_of_one_le_left ( Nat.cast_nonneg _ ) ?_;
        refine le_add_of_le_of_nonneg ?_ hε.le;
        refine Real.one_le_exp ?_;
        refine le_of_tendsto_of_tendsto tendsto_const_nhds ( Real.tendsto_eulerMascheroniSeq ) ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
        simp +decide [ eulerMascheroniSeq ];
        induction hn <;> simp_all +decide [ harmonic ];
        · exact le_trans ( Real.log_le_sub_one_of_pos ( by norm_num ) ) ( by norm_num );
        · rw [ Finset.sum_range_succ, Real.log_le_iff_le_exp ( by positivity ) ] at *;
          rw [ Real.exp_add ];
          nlinarith [ Real.add_one_le_exp ( ( ↑‹ℕ› : ℝ ) + 1 ) ⁻¹, Real.exp_pos ( ( ↑‹ℕ› : ℝ ) + 1 ) ⁻¹, mul_inv_cancel₀ ( by positivity : ( ( ↑‹ℕ› : ℝ ) + 1 ) ≠ 0 ) ];
    · unfold Pi_sieve; aesop;
  · have h_n_Yk_ge_X₀ : (n : ℝ) / Y_val lam k ≥ X₀ := by
      have h_n_Yk_ge_X₀ : (n : ℝ) ≥ X₀^2 / lam ∧ (n : ℝ) / Y_val lam k ≥ Y_val lam (k + 1) := by
        have h_n_Yk_ge_X₀ : (n : ℝ) ≥ X₀^2 / lam := by
          exact le_of_lt ( Nat.lt_of_ceil_lt hn );
        obtain ⟨ p, hp ⟩ := Finset.nonempty_of_ne_empty hP;
        simp_all +decide [ P_sieve ];
        exact le_trans ( Nat.lt_of_floor_lt hp.1.1.1 |> le_of_lt ) ( Nat.floor_le ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ) |> le_trans ( Nat.cast_le.mpr hp.1.1.2 ) );
      unfold Y_val at *;
      field_simp at *;
      ring_nf at *;
      norm_num [ pow_mul ] at *;
      nlinarith [ show ( lam : ℝ ) ^ k ≥ 1 by exact one_le_pow₀ hlam.le, show ( lam : ℝ ) ^ k * lam ≥ 1 by exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ hlam.le ) hlam.le ];
    have h_card_sifted :
        ((L.biUnion (sinv S ·)).card : ℝ) ≤
          ((Finset.range (⌊(n : ℝ) / Y_val lam k⌋₊ + 1)).filter
            (fun m => m ≥ 1 ∧ ∀ r ∈ P_sieve n lam k S, ¬r ∣ m)).card := by
      exact_mod_cast Finset.card_le_card (biUnion_sinv_subset_sifted hS hlam hL)
    have hP_bound :
        ∀ p ∈ P_sieve n lam k S, Nat.Prime p ∧ (p : ℝ) ≤ (n : ℝ) / Y_val lam k := by
      intro p hp
      exact
        ⟨Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.2,
          by
            exact le_trans
              (Nat.cast_le.mpr <|
                Finset.mem_Ioc.mp
                  (Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.1) |>.2)
              (Nat.floor_le <|
                by
                  exact div_nonneg (Nat.cast_nonneg _) <|
                    by exact mul_nonneg zero_le_two <| pow_nonneg (by positivity) _)⟩
    refine le_trans h_card_sifted ?_
    simpa [Pi_sieve, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hX₀ ((n : ℝ) / Y_val lam k) h_n_Yk_ge_X₀ (P_sieve n lam k S) hP_bound

/-
Weighted interval product
-/
lemma wip_finitely_many (lam : ℝ) (hlam : 1 < lam)
    (g : ℕ → ℝ) (hg1 : ∀ k, 1 ≤ g k)
    (ε : ℝ) (hε : ε > 0) (K : ℕ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, k ≤ K →
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ k ≤ K, ∀ n ≥ N₁, M_layer lam k / g k * (∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
    have h_case1 : ∀ k ≤ K, ∃ N₁ : ℕ, ∀ n ≥ N₁, M_layer lam k * (∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
      intro k hk
      obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, n ≥ N₁ → (∏ p ∈ primesUpTo (⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε / 2) / Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) := by
        have := mertens_product_estimate ( ε / 4 ) ( by positivity );
        obtain ⟨ X₀, hX₀ ⟩ := this;
        -- Choose N₁ such that for all n ≥ N₁, ⌊n/Y_k⌋ ≥ X₀.
        obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ⌊(n : ℝ) / Y_val lam k⌋₊ ≥ X₀ := by
          have h_floor : Filter.Tendsto (fun n : ℕ => ⌊(n : ℝ) / Y_val lam k⌋₊ : ℕ → ℝ) Filter.atTop Filter.atTop := by
            exact tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop.comp <| Filter.Tendsto.atTop_div_const ( show 0 < Y_val lam k from mul_pos zero_lt_two <| pow_pos ( by positivity ) _ ) <| tendsto_natCast_atTop_atTop;
          exact Filter.eventually_atTop.mp ( h_floor.eventually_ge_atTop X₀ );
        use N₁ + 2; intros n hn; specialize hX₀ ⌊ ( n : ℝ ) / Y_val lam k⌋₊ ( hN₁ n ( by linarith ) ) ; rw [ abs_le ] at hX₀; ring_nf at *; linarith;
      use N₁ + ⌈Y_val lam (k + 1) * Y_val lam k⌉₊ + 1;
      intro n hn
      have h_prod : M_layer lam k * (∏ p ∈ (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))) = (∏ p ∈ primesUpTo (⌊(n : ℝ) / Y_val lam k⌋₊), (1 - 1 / (p : ℝ))) := by
        apply M_layer_prod_eq;
        refine Nat.le_floor ?_;
        rw [ le_div_iff₀ ] <;> norm_num [ Y_val ] at *;
        · nlinarith [ Nat.floor_le ( show 0 ≤ 2 * lam ^ ( k + 1 ) by positivity ), Nat.le_ceil ( 2 * lam ^ ( k + 1 ) * ( 2 * lam ^ k ) ), show ( n : ℝ ) ≥ N₁ + ⌈2 * lam ^ ( k + 1 ) * ( 2 * lam ^ k ) ⌉₊ + 1 by exact_mod_cast hn, pow_pos ( zero_lt_one.trans hlam ) k, pow_succ' lam k ];
        · positivity;
      exact h_prod.symm ▸ hN₁ n ( by linarith );
    choose! N₁ hN₁ using h_case1;
    use Finset.sup (Finset.range (K + 1)) N₁;
    intro k hk n hn; specialize hN₁ k hk n ( le_trans ( Finset.le_sup ( f := N₁ ) ( Finset.mem_range.mpr ( Nat.lt_succ_of_le hk ) ) ) hn ) ; simp_all +decide [ div_mul_eq_mul_div ] ;
    exact le_trans ( div_le_self ( mul_nonneg ( M_layer_nonneg _ _ ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop ) ) <| hg1 _ ) hN₁;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ k ≤ K, ∀ n ≥ N₂, Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) ≥ (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) * Real.log n := by
    have h_log_floor : ∀ k ≤ K, Filter.Tendsto (fun n : ℕ => Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log n) Filter.atTop (nhds 1) := by
      intro k hk
      have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => Real.log (n / Y_val lam k) / Real.log n) Filter.atTop (nhds 1) := by
        have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => (Real.log n - Real.log (Y_val lam k)) / Real.log n) Filter.atTop (nhds 1) := by
          ring_nf;
          exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( mod_cast hx ) ) ) ] ) ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) ) ) ( by norm_num );
        refine h_log_floor_aux.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt ( show 0 < Y_val lam k from mul_pos zero_lt_two ( pow_pos ( by positivity ) _ ) ) ) ] );
      have h_log_floor_aux : Filter.Tendsto (fun n : ℕ => Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log (n / Y_val lam k)) Filter.atTop (nhds 1) := by
        have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => Real.log (⌊x⌋₊) / Real.log x) Filter.atTop (nhds 1) := by
          have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => Real.log (x - 1) / Real.log x) Filter.atTop (nhds 1) := by
            have h_log_floor_aux : Filter.Tendsto (fun x : ℝ => (Real.log x + Real.log (1 - 1 / x)) / Real.log x) Filter.atTop (nhds 1) := by
              ring_nf;
              exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num );
            refine h_log_floor_aux.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_sub_div ( by linarith ) ] ; rw [ Real.log_div ] <;> ring_nf <;> linarith );
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_log_floor_aux tendsto_const_nhds ?_ ?_;
          · filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx using div_le_div_of_nonneg_right ( Real.log_le_log ( by linarith ) ( by linarith [ Nat.lt_floor_add_one x ] ) ) ( Real.log_nonneg ( by linarith ) );
          · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using div_le_one_of_le₀ ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by linarith ) <| Real.log_nonneg <| by linarith;
        exact h_log_floor_aux.comp <| tendsto_natCast_atTop_atTop.atTop_div_const <| show 0 < Y_val lam k from mul_pos zero_lt_two <| pow_pos ( by positivity ) _;
      have := h_log_floor_aux.mul ‹Filter.Tendsto ( fun n : ℕ => Real.log ( n / Y_val lam k ) / Real.log n ) Filter.atTop ( nhds 1 ) ›;
      simp_all +decide ;
      refine this.congr' ( by filter_upwards [ ‹Filter.Tendsto ( fun n : ℕ => Real.log ( n / Y_val lam k ) / Real.log n ) Filter.atTop ( nhds 1 ) ›.eventually_ne one_ne_zero ] with n hn using by rw [ div_mul_div_cancel₀ ( by aesop ) ] );
    have h_log_floor : ∀ k ≤ K, ∃ N₂ : ℕ, ∀ n ≥ N₂, Real.log (⌊(n : ℝ) / Y_val lam k⌋₊) / Real.log n ≥ (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) := by
      exact fun k hk => by rcases Metric.tendsto_atTop.mp ( h_log_floor k hk ) ( 1 - ( Real.exp ( -γ ) + ε / 2 ) / ( Real.exp ( -γ ) + ε ) ) ( sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ Real.exp_pos ( -γ ) ] ) with ⟨ N₂, hN₂ ⟩ ; exact ⟨ N₂, fun n hn => by linarith [ abs_lt.mp ( hN₂ n hn ) ] ⟩ ;
    choose! N₂ hN₂ using h_log_floor;
    exact ⟨ Finset.sup ( Finset.Iic K ) N₂ + 2, fun k hk n hn => by have := hN₂ k hk n ( by linarith [ Finset.le_sup ( f := N₂ ) ( Finset.mem_Iic.mpr hk ) ] ) ; rwa [ ge_iff_le, le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Finset.le_sup ( f := N₂ ) ( Finset.mem_Iic.mpr hk ) ] ) ] at this ⟩;
  use Max.max N₁ N₂ + 2;
  intro n hn k hk; specialize hN₁ k hk n ( by linarith [ Nat.le_max_left N₁ N₂ ] ) ; specialize hN₂ k hk n ( by linarith [ Nat.le_max_right N₁ N₂ ] ) ;
  refine le_trans hN₁ ?_;
  rw [ div_le_div_iff₀ ];
  · rw [ div_mul_eq_mul_div, ge_iff_le, div_le_iff₀ ] at hN₂ <;> first | positivity | linarith;
  · refine lt_of_lt_of_le ?_ hN₂;
    exact mul_pos ( div_pos ( by positivity ) ( by positivity ) ) ( Real.log_pos ( by norm_cast; linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) );
  · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ;

/-
M_k * product ≤ (e^{-γ}+δ)/log(max(Y_{k+1}, n/Y_k)). Combined with log(max(...))≥ log(n)/2, this gives
M_k * product ≤ 2(e^{-γ}+δ)/log n.
-/
lemma wip_mertens_bound (lam : ℝ) (hlam : 1 < lam)
    (δ : ℝ) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ,
      M_layer lam k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        2 * (Real.exp (-γ) + δ) / Real.log n := by
  have := @mertens_product_estimate;
  obtain ⟨ X₀, hX₀ ⟩ := this ( δ / 2 ) ( half_pos hδ );
  refine ⟨ ⌈X₀⌉₊ ^ 2 + ⌈lam ^ 2⌉₊ ^ 2 + 2, fun n hn k => ?_ ⟩;
  -- Let $x = \max(Y_{k+1}, n/Y_k)$.
  set x := max (Y_val lam (k + 1)) (n / Y_val lam k) with hx;
  -- By definition of $x$, we have $M_k * \prod_{Y_{k+1}<p\le n/Y_k}(1-1/p) \le \prod_{p\le x}(1-1/p)$.
  have h_prod_le : M_layer lam k * ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) := by
    by_cases h : ⌊Y_val lam ( k + 1 ) ⌋₊ ≤ ⌊ ( n : ℝ ) / Y_val lam k ⌋₊ <;> simp_all +decide [ M_layer, primesUpTo ];
    · rw [ ← Finset.prod_union ];
      · refine le_of_eq ?_;
        refine Finset.prod_bij ( fun x hx => x ) ?_ ?_ ?_ ?_ <;> simp_all +decide [ Finset.mem_union, Finset.mem_filter ];
        · rintro a ( ⟨ ha₁, ha₂ ⟩ | ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ ) <;> [ exact ⟨ le_trans ha₁ ( Nat.floor_mono <| le_max_left _ _ ), ha₂ ⟩ ; exact ⟨ le_trans ha₂ ( Nat.floor_mono <| le_max_right _ _ ), ha₃ ⟩ ];
        · grind;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    · rw [ max_eq_left ];
      · norm_num [ Finset.Ioc_eq_empty_of_le h.le ];
      · contrapose! h;
        exact Nat.floor_mono h.le;
  -- By definition of $x$, we have $x \geq \sqrt{\lambda n}$.
  have hx_ge_sqrt : x ≥ Real.sqrt (lam * n) := by
    have hx_ge_sqrt : Y_val lam (k + 1) * (n / Y_val lam k) ≥ lam * n := by
      unfold Y_val; ring_nf; norm_num [ show lam ≠ 0 by positivity ] ;
      nlinarith [ mul_inv_cancel_left₀ ( by positivity : ( lam ^ k : ℝ ) ≠ 0 ) ( lam * n ) ];
    refine Real.sqrt_le_iff.mpr ⟨ ?_, ?_ ⟩;
    · exact le_max_of_le_left ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) );
    · cases max_cases ( Y_val lam ( k + 1 ) ) ( n / Y_val lam k ) <;> nlinarith [ show 0 ≤ Y_val lam ( k + 1 ) from by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ), show 0 ≤ ( n : ℝ ) / Y_val lam k from by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ];
  -- Since $x \geq \sqrt{\lambda n}$, we have $\log x \geq \frac{1}{2} \log n$.
  have hlogx_ge_halflogn : Real.log x ≥ (1 / 2) * Real.log n := by
    have hlogx_ge_halflogn : Real.log x ≥ Real.log (Real.sqrt (lam * n)) := by
      exact Real.log_le_log ( Real.sqrt_pos.mpr ( mul_pos ( by positivity ) ( Nat.cast_pos.mpr ( by nlinarith ) ) ) ) hx_ge_sqrt;
    rw [ Real.log_sqrt ( by positivity ), Real.log_mul ( by positivity ) ( by norm_cast; nlinarith ) ] at hlogx_ge_halflogn ; linarith [ Real.log_nonneg hlam.le ];
  -- Since $x \geq \sqrt{\lambda n}$, we have $x \geq X₀$.
  have hx_ge_X₀ : x ≥ X₀ := by
    refine le_trans ?_ hx_ge_sqrt;
    refine le_trans ?_ ( Real.sqrt_le_sqrt <| show lam * n ≥ ⌈X₀⌉₊ ^ 2 by nlinarith [ Nat.le_ceil X₀, show ( n : ℝ ) ≥ ⌈X₀⌉₊ ^ 2 + ⌈lam ^ 2⌉₊ ^ 2 + 2 by exact_mod_cast hn, show ( ⌈lam ^ 2⌉₊ : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| Nat.ceil_pos.mpr <| by positivity ] );
    rw [ Real.sqrt_sq ] <;> linarith [ Nat.le_ceil X₀ ];
  refine le_trans h_prod_le ?_;
  refine le_trans ( show ∏ p ∈ primesUpTo x, ( 1 - 1 / ( p : ℝ ) ) ≤ Real.exp ( -γ ) / Real.log x + δ / 2 / Real.log x from ?_ ) ?_;
  · linarith [ abs_le.mp ( hX₀ x hx_ge_X₀ ) ];
  · rw [ ← add_div, div_le_div_iff₀ ];
    · nlinarith [ Real.exp_pos ( -γ ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; nlinarith ) ];
    · exact lt_of_lt_of_le ( mul_pos ( by norm_num ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by nlinarith ) ) ) ) hlogx_ge_halflogn;
    · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by nlinarith;

lemma wip_large_k (lam : ℝ) (hlam : 1 < lam)
    (g : ℕ → ℝ) (hg1 : ∀ k, 1 ≤ g k)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : ε > 0) :
    ∃ K : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, K < k →
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ, M_layer lam k * ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ)) ≤ 2 * (Real.exp (-γ) + ε / 2) / Real.log n := by
    apply wip_mertens_bound lam hlam (ε / 2) (half_pos hε);
  -- Choose K such that for all k > K, g_k ≥ 2(e^{-γ} + ε/2)/(e^{-γ} + ε).
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k : ℕ, k > K → g k ≥ 2 * (Real.exp (-γ) + ε / 2) / (Real.exp (-γ) + ε) := by
    exact Filter.eventually_atTop.mp ( hg.eventually_ge_atTop _ ) |> fun ⟨ K, hK ⟩ => ⟨ K, fun k hk => hK k hk.le ⟩;
  use K, N₁;
  intro n hn k hk; specialize hN₁ n hn k; specialize hK k hk; rw [ div_mul_eq_mul_div, div_le_iff₀ ] at * <;> try linarith [ hg1 k ];
  rw [ div_mul_eq_mul_div, le_div_iff₀ ] at *;
  · rw [ ge_iff_le, div_le_iff₀ ] at hK <;> nlinarith [ Real.exp_pos ( -γ ) ];
  · rcases n with ( _ | _ | n ) <;> norm_num at *;
    · contrapose! hN₁;
      exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    · contrapose! hN₁;
      refine mul_pos ?_ ?_;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
      · refine Finset.prod_pos fun p hp => sub_pos.mpr ?_;
        exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
    · exact Real.log_pos <| by linarith;
  · rcases n with ( _ | _ | n ) <;> norm_num at *;
    · contrapose! hN₁;
      exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
    · contrapose! hN₁;
      refine mul_pos ?_ ?_;
      · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ;
      · refine Finset.prod_pos fun p hp => sub_pos.mpr ?_;
        exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
    · exact Real.log_pos <| by linarith

/-- M_{λ,k}/g_k · ∏_{Y_{λ,k+1} < p ≤ n/Y_{λ,k}} (1-1/p) ≤ (e^{-γ}+o(1))/log n -/
theorem weighted_interval_product (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (hlam : 1 < lam) (g : ℕ → ℝ)
    (hg1 : ∀ k, 1 ≤ g k)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ,
      M_layer lam k / g k *
        ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime),
          (1 - 1 / (p : ℝ)) ≤
        (Real.exp (-γ) + ε) / Real.log n := by
  obtain ⟨K, N₂, hN₂⟩ := wip_large_k lam hlam g hg1 hg ε hε
  obtain ⟨N₁, hN₁⟩ := wip_finitely_many lam hlam g hg1 ε hε K
  exact ⟨max N₁ N₂, fun n hn k => by
    by_cases hk : k ≤ K
    · exact hN₁ n (le_of_max_le_left hn) k hk
    · exact hN₂ n (le_of_max_le_right hn) k (by omega)⟩

/-
Product over common primes above Y_{λ,k+1} is bounded by D_{λ,m}.
-/
theorem high_product (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
    (k : ℕ) (A B : Finset ℕ) (n : ℕ)
    (hL : ∀ j, k < j → (L_common lam j A B).card ≤ m j) :
    ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ n).filter Nat.Prime).filter
        (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty),
      (1 - 1 / (p : ℝ))⁻¹ ≤ D_val lam m := by
  -- By layer_decomp_common_primes, each such p ∈ I_layer lam j for some j > k.
  have h_layer : ∀ p ∈ ((Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n).filter Nat.Prime).filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), ∃ j > k, p ∈ I_layer lam j := by
    apply layer_decomp_common_primes;
    linarith;
  choose! j hj using h_layer;
  -- By definition of $j$, we can rewrite the product as a product over the layers $j > k$.
  have h_prod_layers : ∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ))⁻¹ = ∏ j' ∈ Finset.image j (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (∏ p ∈ Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))⁻¹) := by
    rw [ Finset.prod_image' ] ; aesop;
  -- By definition of $j$, we know that for each $j'$ in the image of $j$, the product over the primes in layer $j'$ is bounded by $E_{λ,j'}(m_{j'})$.
  have h_prod_layer_bound : ∀ j' ∈ Finset.image j (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (∏ p ∈ Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))⁻¹) ≤ E_val lam j' (m j') := by
    intros j' hj'
    have h_card : (Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty))).card ≤ m j' := by
      refine le_trans ?_ ( hL j' ?_ );
      · refine Finset.card_le_card ?_;
        simp +contextual [ Finset.subset_iff, L_common ];
        grind;
      · grind;
    convert prod_le_E_val lam j' ( m j' ) _ _ h_card using 1;
    grind;
  refine h_prod_layers ▸ le_trans ( Finset.prod_le_prod ?_ h_prod_layer_bound ) ?_;
  · exact fun _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
  · apply_rules [ partial_prod_le_D_val ]

/-
If |L_{λ,k}(A,B)| ≤ m_k for all k, then
    ∏_{p≤n, A[p]≠∅, B[p]≠∅} (1-1/p)⁻¹ ≤ D_{λ,m}.
-/
theorem euler_common_product (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
    (n : ℕ) (A B : Finset ℕ)
    (hL : ∀ k, (L_common lam k A B).card ≤ m k) :
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p =>
        Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty),
      (1 - 1 / (p : ℝ))⁻¹ ≤ D_val lam m := by
  -- By definition of $L_{\lambda,k}(A,B)$, we know that every prime $p$ in the product satisfies $p \leq Y_{\lambda,k+1}$.
  have h_subset : ∀ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), ∃ k, p ∈ I_layer lam k := by
    intro p hp; by_cases hp2 : p ≥ 2 <;> simp_all +decide [ I_layer ] ;
    · have h_log : ∃ k : ℕ, Y_val lam k ≤ p ∧ p < Y_val lam (k + 1) := by
        have h_unbounded : ∀ M : ℝ, ∃ k : ℕ, Y_val lam k > M := by
          exact fun M => by rcases pow_unbounded_of_one_lt ( M / 2 ) hlam with ⟨ k, hk ⟩ ; exact ⟨ k, by rw [ Y_val ] ; linarith ⟩ ;
        contrapose! h_unbounded;
        exact ⟨ p, fun k => Nat.recOn k ( by norm_num [ Y_val ] ; linarith ) h_unbounded ⟩;
      exact ⟨ h_log.choose, h_log.choose_spec.1, Nat.lt_ceil.mpr h_log.choose_spec.2 ⟩;
    · interval_cases p <;> simp_all +decide;
  choose! k hk using h_subset;
  have h_group : ∏ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)), (1 - 1 / (p : ℝ))⁻¹ ≤ ∏ j ∈ Finset.image k (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))), (∏ p ∈ (Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)))), (1 - 1 / (p : ℝ))⁻¹) := by
    rw [ Finset.prod_image' ] ; aesop;
  have h_bound : ∀ j ∈ Finset.image k (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))), (∏ p ∈ (Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)))), (1 - 1 / (p : ℝ))⁻¹) ≤ E_val lam j (m j) := by
    intros j hj
    have h_subset : Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))) ⊆ L_common lam j A B := by
      simp +contextual [ Finset.subset_iff, L_common ];
      grind;
    apply prod_le_E_val;
    · exact fun x hx => Finset.mem_filter.mp ( h_subset hx ) |>.1;
    · exact le_trans ( Finset.card_le_card h_subset ) ( hL j );
  refine le_trans h_group <| le_trans ( Finset.prod_le_prod ?_ h_bound ) ?_;
  · exact fun _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
  · apply_rules [ partial_prod_le_D_val ]

set_option maxHeartbeats 1600000
-- The weighted deletion estimate expands several generated inequalities.

/-
If either |A| or |B| is small relative to the weighted sieve bound,
    then |A|·|B| ≤ (e^γ + ε + o(1)) · D · n²/log n.
-/
theorem weighted_small_alternative (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        ∀ k : ℕ, (∀ j, k < j → (L_common lam j A B).card ≤ m j) →
          ((A.card : ℝ) < (Real.exp γ + ε) * M_layer lam k / g k * n *
            Pi_sieve n lam k A ∨
           (B.card : ℝ) < (Real.exp γ + ε) * M_layer lam k / g k * n *
            Pi_sieve n lam k B) →
          ((A.card : ℝ) * B.card ≤
            (Real.exp γ + 2 * ε) * D_val lam m * n ^ 2 / Real.log n) := by
  -- Choose ε₁, ε₂ small enough such that (e^γ + ε) * (e^γ + ε₁) * (e^{-γ} + ε₂) ≤ (e^γ + 2 * ε).
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ : ∃ ε₁ > 0, (Real.exp γ + ε) * (Real.exp γ + ε₁) * (Real.exp (-γ) + ε₁) ≤ (Real.exp γ + 2 * ε) * (Real.exp γ) * (Real.exp (-γ)) := by
    -- By continuity of the exponential function and properties of limits, we can find such an ε₁.
    have h_cont : Filter.Tendsto (fun ε₁ => (Real.exp γ + ε) * (Real.exp γ + ε₁) * (Real.exp (-γ) + ε₁) / ((Real.exp γ + 2 * ε) * Real.exp γ * Real.exp (-γ))) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.exp γ + ε) * Real.exp γ * Real.exp (-γ) / ((Real.exp γ + 2 * ε) * Real.exp γ * Real.exp (-γ)))) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
    have := h_cont.eventually ( gt_mem_nhds <| show ( Real.exp γ + ε ) * Real.exp γ * Real.exp ( -γ ) / ( ( Real.exp γ + 2 * ε ) * Real.exp γ * Real.exp ( -γ ) ) < 1 from by rw [ div_lt_iff₀ <| by positivity ] ; nlinarith [ Real.exp_pos γ, Real.exp_pos ( -γ ), mul_pos ( Real.exp_pos γ ) ( Real.exp_pos ( -γ ) ) ] ) ; have := this.and self_mem_nhdsWithin; obtain ⟨ ε₁, hε₁₁, hε₁₂ ⟩ := this.exists; exact ⟨ ε₁, hε₁₂, by rw [ div_lt_iff₀ <| by positivity ] at hε₁₁; linarith ⟩ ;
  -- Choose N₀ such that for all n ≥ N₀, the inequalities from sifted_bound_set, high_product, and weighted_interval_product hold.
  obtain ⟨N₀₁, hN₀₁⟩ : ∃ N₀₁ : ℕ, ∀ n : ℕ, N₀₁ ≤ n → ∀ A B : Finset ℕ, ProductAdmissible n A B → ∀ k : ℕ, (∀ j, k < j → (L_common lam j A B).card ≤ m j) → ((A.card : ℝ) ≤ (Real.exp γ + ε₁) * n * Pi_sieve n lam k A ∧ (B.card : ℝ) ≤ (Real.exp γ + ε₁) * n * Pi_sieve n lam k B) := by
    have := @sifted_bound_set;
    exact Exists.elim ( this ε₁ hε₁_pos lam hadm.1 ) fun N₀ hN₀ => ⟨ N₀, fun n hn A B hAB k hk => ⟨ hN₀ n hn k A hAB.1, hN₀ n hn k B hAB.2.1 ⟩ ⟩;
  obtain ⟨N₀₂, hN₀₂⟩ : ∃ N₀₂ : ℕ, ∀ n : ℕ, N₀₂ ≤ n → ∀ k : ℕ, M_layer lam k / g k * ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ)) ≤ (Real.exp (-γ) + ε₁) / Real.log n := by
    apply weighted_interval_product ε₁ hε₁_pos lam (by
    exact hadm.1) g (by exact hadm.2.2.2.2.2.1) (by
    exact hadm.2.2.2.2.2.2);
  use Max.max N₀₁ N₀₂ + 1;
  intros n hn A B hadm k hk h
  have h_prod : Pi_sieve n lam k A * Pi_sieve n lam k B ≤ (∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ))) * D_val lam m := by
    have h_prod : (∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime).filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ))⁻¹) ≤ D_val lam m := by
      apply high_product;
      · exact ‹AdmissibleTriple lam m g›.1;
      · exact ‹AdmissibleTriple lam m g›.2.2.1;
      · assumption;
    refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_prod ?_ );
    · unfold Pi_sieve;
      unfold P_sieve; simp +decide [ Finset.prod_filter ] ;
      rw [ ← div_eq_mul_inv, le_div_iff₀ ];
      · rw [ ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib ];
        refine Finset.prod_le_prod ?_ ?_ <;> norm_num;
        · intro i hi₁ hi₂; split_ifs <;> norm_num;
          any_goals exact inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_›;
          · exact mul_nonneg ( mul_nonneg ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_›;
          · exact mul_self_nonneg _;
          · exact mul_self_nonneg _;
          · exact mul_self_nonneg _;
        · intro i hi₁ hi₂; split_ifs <;> norm_num;
          · aesop;
          · grind;
          · exact mul_le_of_le_one_left ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _;
          · exact mul_le_of_le_one_left ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _;
          · exact False.elim <| ‹¬ ( ( sdiv A i ).Nonempty ∧ ( sdiv B i ).Nonempty ) › ⟨ Finset.nonempty_of_ne_empty ‹_›, Finset.nonempty_of_ne_empty ‹_› ⟩;
      · refine Finset.prod_pos fun p hp => ?_;
        split_ifs <;> norm_num;
        exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt ‹_›;
    · exact Finset.prod_nonneg fun p hp => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
  have h_combined : (A.card : ℝ) * (B.card : ℝ) ≤ (Real.exp γ + ε) * (Real.exp γ + ε₁) * (M_layer lam k / g k) * n^2 * (∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ))) * D_val lam m := by
    have h_combined : (A.card : ℝ) * (B.card : ℝ) ≤ (Real.exp γ + ε) * (Real.exp γ + ε₁) * (M_layer lam k / g k) * n^2 * Pi_sieve n lam k A * Pi_sieve n lam k B := by
      rcases h with h | h <;> have := hN₀₁ n ( by linarith [ le_max_left N₀₁ N₀₂ ] ) A B hadm k hk <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      · refine le_trans
          (mul_le_mul h.le this.2 (by positivity)
            (by exact le_trans (by positivity) h.le)) ?_
        ring_nf
        exact le_rfl
      · refine le_trans
          (mul_le_mul this.1 h.le (by positivity)
            (by grind +splitImp)) ?_
        ring_nf
        exact le_rfl
    refine le_trans h_combined ?_;
    convert mul_le_mul_of_nonneg_left h_prod ( show 0 ≤ ( Real.exp γ + ε ) * ( Real.exp γ + ε₁ ) * ( M_layer lam k / g k ) * n ^ 2 by
                                                exact mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( div_nonneg ( by exact M_layer_nonneg lam k ) ( by linarith [ show 1 ≤ g k from by { have := ‹AdmissibleTriple lam m g›; exact this.2.2.2.2.2.1 k } ] ) ) ) ( sq_nonneg _ ) ) using 1
    focus
      ring
    ring;
  have h_combined : (A.card : ℝ) * (B.card : ℝ) ≤ (Real.exp γ + ε) * (Real.exp γ + ε₁) * (Real.exp (-γ) + ε₁) * n^2 * D_val lam m / Real.log n := by
    refine le_trans h_combined ?_;
    convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( hN₀₂ n ( by linarith [ Nat.le_max_right N₀₁ N₀₂ ] ) k ) ( show 0 ≤ ( Real.exp γ + ε ) * ( Real.exp γ + ε₁ ) * n ^ 2 * D_val lam m by
                                                                                                                                exact mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( by positivity ) ) ( by exact Real.exp_nonneg _ ) ) ) ( show 0 ≤ 1 by norm_num ) using 1 <;> ring;
  refine le_trans h_combined ?_;
  convert mul_le_mul_of_nonneg_right hε₁ ( show 0 ≤ ( n : ℝ ) ^ 2 * D_val lam m / Real.log n by exact div_nonneg ( mul_nonneg ( sq_nonneg _ ) ( show 0 ≤ D_val lam m by exact Real.exp_nonneg _ ) ) ( Real.log_natCast_nonneg _ ) ) using 1
  focus
    ring
  norm_num [ mul_assoc, ← Real.exp_add ] ; ring

/-
The sum of sinv cardinalities exceeds M * union cardinality,
    enabling multiplicity_lemma application.
-/
lemma sinv_sum_exceeds_union (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hg1 : ∀ k, 1 ≤ g k) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n →
        Regular lam m g S →
        ∀ k : ℕ, m k < N_layer lam k →
          ((S.card : ℝ) ≥ (Real.exp γ + ε) * M_layer lam k / g k * n *
            Pi_sieve n lam k S) →
          ∀ L : Finset ℕ,
            L ⊆ (I_layer lam k).filter (fun p => (sdiv S p).Nonempty) →
            m k < L.card →
            ∃ x ∈ L.biUnion (sinv S ·),
              ⌊Real.sqrt ((m k : ℝ) + 1)⌋₊ < (L.filter (x ∈ sinv S ·)).card := by
  -- Apply the multiplicity_lemma with M = ⌊√(m k + 1)⌋₊.
  apply Classical.byContradiction
  intro h_contra;
  push Not at h_contra;
  obtain ⟨ N₀, hN₀ ⟩ := sifted_bound_union ( ε / 2 ) ( half_pos hε ) lam hlam;
  obtain ⟨ n, hn₁, S, hS₁, hS₂, k, hk₁, hk₂, L, hL₁, hL₂, hL₃ ⟩ := h_contra N₀;
  -- Apply the multiplicity_lemma with M = ⌊√(m k + 1)⌋₊ and the given conditions.
  have h_mult : ⌊Real.sqrt (m k + 1)⌋₊ * (L.biUnion (sinv S ·)).card < ∑ p ∈ L, (sinv S p).card := by
    have h_mult : ∑ p ∈ L, (sinv S p).card > ∑ p ∈ L, (layerWeight lam m g k) * S.card := by
      have h_mult : ∀ p ∈ L, (sinv S p).card > (layerWeight lam m g k) * S.card := by
        intros p hp
        have h_div : (sdiv S p).card > layerWeight lam m g k * S.card := by
          apply hS₂ k p;
          · exact Finset.mem_filter.mp ( hL₁ hp ) |>.1;
          · simp [layerWeight, hk₁];
            refine div_pos ( by linarith [ hg1 k ] ) ( mul_pos ( mul_pos ( ?_ ) ( ?_ ) ) ( Real.sqrt_pos.mpr ( by positivity ) ) );
            · exact mul_pos zero_lt_two ( pow_pos ( zero_lt_one.trans hlam ) _ );
            · refine Finset.prod_pos fun p hp => sub_pos.mpr ?_;
              rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ) ];
          · exact Finset.mem_filter.mp ( hL₁ hp ) |>.2;
        convert h_div using 1;
        exact_mod_cast division_lemma S p ( Finset.mem_filter.mp ( hL₁ hp ) |>.1 |> Finset.mem_filter.mp |>.2 );
      simpa using Finset.sum_lt_sum_of_nonempty ( Finset.card_pos.mp ( pos_of_gt hL₂ ) ) h_mult;
    have h_mult : ∑ p ∈ L, (layerWeight lam m g k) * S.card ≥ (m k + 1) * (Real.exp γ + ε) * n / (Y_val lam k * Real.sqrt (m k + 1)) * Pi_sieve n lam k S := by
      have h_mult : layerWeight lam m g k = g k / (Y_val lam k * M_layer lam k * Real.sqrt (m k + 1)) := by
        exact if_pos hk₁;
      simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      field_simp at *;
      rw [ div_le_iff₀ ] at *;
      · rw [ div_mul_eq_mul_div, le_div_iff₀ ];
        · refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( show g k * ↑ ( #S ) * ↑ ( #L ) ≥ g k * ↑ ( #S ) * ( m k + 1 ) by exact mul_le_mul_of_nonneg_left ( mod_cast hL₂ ) ( by exact mul_nonneg ( by linarith [ hg1 k ] ) ( Nat.cast_nonneg _ ) ) ) ( show 0 ≤ Y_val lam k by exact mul_nonneg zero_le_two ( pow_nonneg ( by linarith ) _ ) ) );
          convert mul_le_mul_of_nonneg_right hk₂ ( show 0 ≤ ( m k + 1 : ℝ ) * Y_val lam k by exact mul_nonneg ( by positivity ) ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ ) ) ) using 1 <;> ring;
        · refine mul_pos ?_ ?_;
          · exact mul_pos zero_lt_two ( pow_pos ( by positivity ) _ );
          · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ] ;
      · linarith [ hg1 k ];
      · exact mul_pos zero_lt_two ( pow_pos ( by positivity ) _ );
    have h_mult : (m k + 1) * (Real.exp γ + ε) * n / (Y_val lam k * Real.sqrt (m k + 1)) * Pi_sieve n lam k S > ⌊Real.sqrt (m k + 1)⌋₊ * (Real.exp γ + ε / 2) * n / Y_val lam k * Pi_sieve n lam k S := by
      have h_mult : (m k + 1) * (Real.exp γ + ε) / Real.sqrt (m k + 1) > ⌊Real.sqrt (m k + 1)⌋₊ * (Real.exp γ + ε / 2) := by
        rw [ gt_iff_lt, lt_div_iff₀ ] <;> try positivity;
        nlinarith [ show 0 < Real.exp γ * Real.sqrt ( m k + 1 ) by positivity, show 0 < ε * Real.sqrt ( m k + 1 ) by positivity, Real.mul_self_sqrt ( show ( m k:ℝ ) + 1 ≥ 0 by positivity ), Real.exp_pos γ, Real.sqrt_nonneg ( m k + 1 ), Nat.floor_le ( Real.sqrt_nonneg ( m k + 1 ) ), Nat.lt_floor_add_one ( Real.sqrt ( m k + 1 ) ) ];
      refine mul_lt_mul_of_pos_right ?_ ?_;
      · convert mul_lt_mul_of_pos_right h_mult ( show 0 < ( n : ℝ ) / Y_val lam k by exact div_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; exact absurd hn₁ <| by linarith [ show N₀ > 0 from Nat.pos_of_ne_zero <| by rintro rfl; exact absurd ( h_contra 0 ) <| by aesop ] ) <| by exact mul_pos zero_lt_two <| pow_pos ( by linarith ) _ ) using 1
        focus
          ring
        ring;
      · refine Finset.prod_pos fun p hp => sub_pos.mpr ?_;
        simp +zetaDelta at *;
        exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| by unfold P_sieve at hp; aesop;
    have := hN₀ n hn₁ k S hS₁ L hL₁;
    norm_num [ mul_assoc, mul_div_assoc ] at *;
    rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; nlinarith [ show 0 ≤ ( ⌊Real.sqrt ( m k + 1 ) ⌋₊ : ℝ ) by positivity ];
  have h_mult : ∑ p ∈ L, (sinv S p).card ≤ ∑ x ∈ L.biUnion (sinv S ·), (L.filter (x ∈ sinv S ·)).card := by
    simp +decide only [card_eq_sum_ones, sum_filter];
    rw [ Finset.sum_comm ];
    simp +decide;
    exact Finset.sum_le_sum fun x hx => by rw [ Finset.inter_eq_right.mpr ( Finset.subset_biUnion_of_mem _ hx ) ] ;
  exact not_lt_of_ge h_mult ( lt_of_le_of_lt ( Finset.sum_le_sum fun x hx => hL₃ x hx ) ( by simpa [ mul_comm ] using ‹⌊Real.sqrt ( m k + 1 ) ⌋₊ * # ( L.biUnion fun x => sinv S x ) < ∑ p ∈ L, # ( sinv S p ) › ) )

/-
If S is regular and |S| ≥ the weighted sieve bound, then regularity gives
    a lower bound on the sum of sinv cardinalities that exceeds the sifted
    union bound. Combined with multiplicity_lemma (M=1), this produces
    two distinct primes sharing an element in sinv S.
-/
lemma regularity_pigeonhole (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hg1 : ∀ k, 1 ≤ g k) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 n →
        Regular lam m g S →
        ∀ k : ℕ, m k < N_layer lam k →
          ((S.card : ℝ) ≥ (Real.exp γ + ε) * M_layer lam k / g k * n *
            Pi_sieve n lam k S) →
          ∀ L : Finset ℕ,
            L ⊆ (I_layer lam k).filter (fun p => (sdiv S p).Nonempty) →
            ⌊Real.sqrt ((m k : ℝ) + 1)⌋₊ < L.card →
            ∃ p ∈ L, ∃ q ∈ L, p ≠ q ∧ (sinv S p ∩ sinv S q).Nonempty := by
  have := @sifted_bound_union;
  obtain ⟨ N₀, hN₀ ⟩ := this ( ε / 2 ) ( half_pos hε ) lam hlam;
  refine ⟨ N₀, fun n hn S hS hreg k hk hS' L hL hL' => ?_ ⟩;
  have h_sum : ∑ p ∈ L, (sinv S p).card > (Real.exp γ + ε) * n / Y_val lam k * Pi_sieve n lam k S := by
    have h_sum : ∀ p ∈ L, (sinv S p).card > layerWeight lam m g k * S.card := by
      intros p hp
      have h_div : (sdiv S p).card > layerWeight lam m g k * S.card := by
        apply hreg k p;
        · exact Finset.mem_filter.mp ( hL hp ) |>.1;
        · unfold layerWeight;
          simp [hk];
          refine div_pos ( by linarith [ hg1 k ] ) ( mul_pos ( mul_pos ( by exact mul_pos zero_lt_two ( pow_pos ( by linarith ) _ ) ) ( Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ] ) ) ( Real.sqrt_pos.mpr <| by positivity ) );
        · exact Finset.mem_filter.mp ( hL hp ) |>.2;
      convert h_div using 1;
      convert division_lemma S p _;
      · norm_cast;
      · exact Finset.mem_filter.mp ( hL hp ) |>.1 |> Finset.mem_filter.mp |>.2;
    have h_sum : ∑ p ∈ L, (sinv S p).card > L.card * layerWeight lam m g k * S.card := by
      simpa [ mul_assoc ] using Finset.sum_lt_sum_of_nonempty ( Finset.card_pos.mp ( pos_of_gt hL' ) ) h_sum;
    have h_sum : layerWeight lam m g k * S.card ≥ (Real.exp γ + ε) * n / Y_val lam k * Pi_sieve n lam k S / Real.sqrt ((m k : ℝ) + 1) := by
      unfold layerWeight; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
      field_simp at *;
      rw [ le_div_iff₀ ];
      · rw [ div_mul_eq_mul_div, div_le_iff₀ ] at * <;> try nlinarith [ show 0 < Y_val lam k from mul_pos zero_lt_two ( pow_pos ( by linarith ) _ ) ];
        linarith [ hg1 k ];
      · refine mul_pos ?_ ?_;
        · exact mul_pos zero_lt_two ( pow_pos ( zero_lt_one.trans hlam ) _ );
        · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ] ;
    have h_sum : L.card > Real.sqrt ((m k : ℝ) + 1) := by
      exact Nat.lt_of_floor_lt hL';
    have h_sum : L.card * layerWeight lam m g k * S.card > (Real.exp γ + ε) * n / Y_val lam k * Pi_sieve n lam k S := by
      rw [ mul_assoc ];
      refine lt_of_le_of_lt ?_ ( mul_lt_mul_of_pos_right h_sum ( ?_ ) );
      · rw [ ge_iff_le, div_le_iff₀ ] at * <;> first | positivity | linarith;
      · refine mul_pos ?_ ?_;
        · unfold layerWeight;
          rw [ if_pos hk ];
          refine div_pos ( by linarith [ hg1 k ] ) ( mul_pos ( mul_pos ( by exact mul_pos zero_lt_two ( pow_pos ( by linarith ) _ ) ) ( ?_ ) ) ( Real.sqrt_pos.mpr ( by positivity ) ) );
          exact Finset.prod_pos fun p hp => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ] ;
        · contrapose! hL'; aesop;
    grind;
  contrapose! h_sum;
  rw [ ← Finset.card_biUnion ];
  · refine le_trans ( hN₀ n hn k S hS L hL ) ?_;
    gcongr;
    · refine Finset.prod_nonneg fun p hp => sub_nonneg.2 ?_;
      exact div_le_self zero_le_one ( mod_cast Nat.Prime.pos ( by unfold P_sieve at hp; aesop ) );
    · exact mul_nonneg zero_le_two ( pow_nonneg ( by positivity ) _ );
    · linarith;
  · exact fun p hp q hq hpq => Finset.disjoint_iff_inter_eq_empty.mpr ( h_sum p hp q hq hpq )

/-
If both |A| and |B| are large and regular, then collision_lemma is violated for large n.
-/
theorem large_interval_contradiction (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hg1 : ∀ k, 1 ≤ g k) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        Regular lam m g A → Regular lam m g B →
        ∀ k : ℕ, m k < (L_common lam k A B).card →
          ((A.card : ℝ) ≥ (Real.exp γ + ε) * M_layer lam k / g k * n *
            Pi_sieve n lam k A) →
          ((B.card : ℝ) ≥ (Real.exp γ + ε) * M_layer lam k / g k * n *
            Pi_sieve n lam k B) →
          False := by
  obtain ⟨N₁, hN₁⟩ := sinv_sum_exceeds_union ε hε lam hlam m g hg1
  obtain ⟨N₂, hN₂⟩ := regularity_pigeonhole ε hε lam hlam m g hg1
  use max N₁ N₂
  intro n hn A B hadm hA hB k hk hA' hB';
  -- Let L = L_common lam k A B.
  set L := L_common lam k A B;
  obtain ⟨x, hx⟩ := hN₁ n (le_trans (le_max_left N₁ N₂) hn) A hadm.1 hA k (by
  exact hk.trans_le ( Finset.card_le_card <| Finset.filter_subset _ _ )) hA' L (by
  exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hp |>.1, Finset.mem_filter.mp hp |>.2.1 ⟩) hk
  obtain ⟨p, hp, q, hq, hpq, h_inter⟩ := hN₂ n (le_trans (le_max_right N₁ N₂) hn) B hadm.2.1 hB k (by
  exact lt_of_lt_of_le hk ( Finset.card_le_card <| Finset.filter_subset _ _ )) hB' (L.filter (x ∈ sinv A ·)) (by
  simp +zetaDelta at *;
  simp +contextual [ Finset.subset_iff, L_common ]) (by
  exact hx.2);
  have := collision_lemma n A B p q hadm (by
  exact Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 |> fun h => Finset.mem_filter.mp h |>.2) (by
  exact Finset.mem_filter.mp ( Finset.mem_filter.mp hq |>.1 ) |>.1 |> fun h => Finset.mem_filter.mp h |>.2) hpq (by
  exact ⟨ x, by aesop ⟩);
  exact h_inter.ne_empty this

/-
If A,B are regular and there is a layer k with |L_k| > m_k and
    all higher layers have |L_j| ≤ m_j, then the product bound holds.
-/
theorem weighted_large_interval (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        Regular lam m g A → Regular lam m g B →
        ∀ k : ℕ, m k < (L_common lam k A B).card →
          (∀ j, k < j → (L_common lam j A B).card ≤ m j) →
          ((A.card : ℝ) * B.card ≤
            (Real.exp γ + 2 * ε) * D_val lam m * n ^ 2 / Real.log n) := by
  -- Extract N₁ from weighted_small_alternative.
  obtain ⟨N₁, hN₁⟩ := weighted_small_alternative ε hε lam m g hadm;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → ∀ A B : Finset ℕ, ProductAdmissible n A B → Regular lam m g A → Regular lam m g B → ∀ k : ℕ, m k < (L_common lam k A B).card → ¬((A.card : ℝ) ≥ (Real.exp γ + ε) * M_layer lam k / g k * n * Pi_sieve n lam k A ∧ (B.card : ℝ) ≥ (Real.exp γ + ε) * M_layer lam k / g k * n * Pi_sieve n lam k B) := by
    convert large_interval_contradiction ε hε lam hadm.1 m g hadm.2.2.2.2.2.1 using 1;
    grind;
  exact ⟨ Max.max N₁ N₂, fun n hn A B hAB hA hB k hk₁ hk₂ => hN₁ n ( le_trans ( le_max_left _ _ ) hn ) A B hAB k hk₂ <| by specialize hN₂ n ( le_trans ( le_max_right _ _ ) hn ) A B hAB hA hB k hk₁; contrapose! hN₂; aesop ⟩

/-! ## Small interval case -/

/-
If |L_{λ,k}(A,B)| ≤ m_k for all k, then
    |A|·|B| ≤ (e^γ + o(1)) · D · n²/log n.
-/
theorem small_interval_case (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (m : ℕ → ℕ)
    (hlam : 1 < lam)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k)))) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        (∀ k, (L_common lam k A B).card ≤ m k) →
        ((A.card : ℝ) * B.card ≤
          (Real.exp γ + ε) * D_val lam m * n ^ 2 / Real.log n) := by
  -- Choose ε₁ > 0 small so that (e^γ + ε₁)² · (e^{-γ} + ε₁) < e^γ + ε.
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ : ∃ ε₁ > 0, (Real.exp γ + ε₁) ^ 2 * (Real.exp (-γ) + ε₁) < Real.exp γ + ε := by
    have h_lim : Filter.Tendsto (fun ε₁ : ℝ => (Real.exp γ + ε₁) ^ 2 * (Real.exp (-γ) + ε₁)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.exp γ) ^ 2 * Real.exp (-γ))) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
    have := h_lim.eventually ( gt_mem_nhds <| show ( Real.exp γ ^ 2 * Real.exp ( -γ ) ) < Real.exp γ + ε by rw [ ← Real.exp_nat_mul, ← Real.exp_add ] ; ring_nf; norm_num; linarith ) ; have := this.and self_mem_nhdsWithin; obtain ⟨ x, hx₁, hx₂ ⟩ := this.exists; exact ⟨ x, hx₂, hx₁ ⟩ ;
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ (p : ℝ) ≤ n) → ((Finset.range (n + 1)).filter (fun m => m ≥ 1 ∧ ∀ p ∈ P, ¬(p ∣ m))).card ≤ (Real.exp γ + ε₁) * n * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    obtain ⟨ X₀, hX₀ ⟩ := sieve_bound ε₁ hε₁_pos;
    exact ⟨ ⌈X₀⌉₊, fun n hn P hP => by simpa using hX₀ n ( Nat.le_of_ceil_le hn ) P fun p hp => ⟨ hP p hp |>.1, mod_cast hP p hp |>.2 ⟩ ⟩;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → |∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ)) - Real.exp (-γ) / Real.log n| ≤ ε₁ / Real.log n := by
    have := mertens_product_estimate ε₁ hε₁_pos;
    exact ⟨ ⌈this.choose⌉₊ + 1, fun n hn => this.choose_spec n <| le_of_lt <| Nat.lt_of_ceil_lt hn ⟩;
  use Max.max N₁ N₂ + 2;
  intro n hn A B hadm hL
  have hA : (A.card : ℝ) ≤ (Real.exp γ + ε₁) * n * ∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ)) := by
    refine le_trans ?_
      ( hN₁ n ( by linarith [ Nat.le_max_left N₁ N₂ ] )
        ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty)) ?_ );
    · refine mod_cast Finset.card_le_card ?_;
      intro x hx; have := hadm.1 hx; simp_all +decide ;
      intro p hp₁ hp₂ hp₃ hp₄; simp_all +decide [ Finset.ext_iff, sdiv ] ;
    · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2.1, mod_cast Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ⟩
  have hB : (B.card : ℝ) ≤ (Real.exp γ + ε₁) * n * ∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ)) := by
    refine le_trans ?_
      ( hN₁ n ( by linarith [ Nat.le_max_left N₁ N₂ ] )
        ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty)) ?_ );
    · refine mod_cast Finset.card_le_card ?_;
      intro x hx; have := hadm.2.1 hx; simp_all +decide [ sdiv ] ;
    · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2.1, mod_cast Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ⟩;
  have h_prod : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ))) ≤ (∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ)))⁻¹ := by
    have h_prod : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ))) ≤ (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (¬(sdiv A p).Nonempty ∨ ¬(sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))) := by
      convert prod_union_le_of_le_one _ _ using 1;
      · congr with p ; aesop;
      · aesop;
      · aesop;
    refine le_trans h_prod ?_;
    rw [ ← div_eq_mul_inv, le_div_iff₀ ];
    · rw [ ← Finset.prod_union ];
      · refine le_of_eq ?_;
        refine Finset.prod_subset ?_ ?_ <;> intro p hp <;> simp_all +decide [ primesUpTo ];
        grind;
      · exact Finset.disjoint_filter.mpr ( by aesop );
    · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop;
  have h_prod_bound : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ)))⁻¹ ≤ D_val lam m := by
    convert euler_common_product lam hlam m hsumm n A B hL using 1;
    rw [ Finset.prod_inv_distrib ];
  have h_prod_bound : (∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε₁) / Real.log n := by
    grind;
  have h_final : (A.card : ℝ) * (B.card : ℝ) ≤ (Real.exp γ + ε₁) ^ 2 * n ^ 2 * ((Real.exp (-γ) + ε₁) / Real.log n) * D_val lam m := by
    refine le_trans ( mul_le_mul hA hB ?_ ?_ ) ?_;
    · positivity;
    · exact mul_nonneg ( mul_nonneg ( add_nonneg ( Real.exp_nonneg _ ) hε₁_pos.le ) ( Nat.cast_nonneg _ ) ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop );
    · convert mul_le_mul_of_nonneg_left ( h_prod.trans ( mul_le_mul h_prod_bound ‹_› ( ?_ ) ( ?_ ) ) ) ( show 0 ≤ ( Real.exp γ + ε₁ ) ^ 2 * n ^ 2 by positivity ) using 1 <;> ring_nf;
      · exact inv_nonneg.mpr ( Finset.prod_nonneg fun x hx => sub_nonneg.mpr <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop );
      · exact add_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) ) ( mul_nonneg hε₁_pos.le ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) );
  refine le_trans h_final ?_;
  convert mul_le_mul_of_nonneg_right hε₁.le ( show 0 ≤ ( n : ℝ ) ^ 2 * D_val lam m / Real.log n by exact div_nonneg ( mul_nonneg ( sq_nonneg _ ) ( show 0 ≤ D_val lam m by exact Real.exp_nonneg _ ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) using 1
  focus
    ring
  ring

/-
For any admissible triple (λ,m,g):
    For all C > e^γ · D / (1-Ω)², eventually |A|·|B| < C · n²/log n
    for all n-admissible (A,B).
-/
theorem layer_weighted_bound (lam : ℝ) (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hadm : AdmissibleTriple lam m g) (C : ℝ)
    (hC : C > Real.exp γ * D_val lam m / (1 - Omega_val lam m g) ^ 2) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        (A.card : ℝ) * B.card < C * n ^ 2 / Real.log n := by
  obtain ⟨ε, hε⟩ : ∃ ε > 0, Real.exp γ * D_val lam m / (1 - Omega_val lam m g) ^ 2 < (Real.exp γ + 2 * ε) * D_val lam m / (1 - Omega_val lam m g) ^ 2 ∧ (Real.exp γ + 2 * ε) * D_val lam m / (1 - Omega_val lam m g) ^ 2 < C := by
    -- We can choose ε small enough such that (Real.exp γ + 2 * ε) * D_val lam m / (1 - Omega_val lam m g) ^ 2 < C.
    obtain ⟨ε, hε⟩ : ∃ ε > 0, (Real.exp γ + 2 * ε) * D_val lam m / (1 - Omega_val lam m g) ^ 2 < C := by
      have h_cont : Filter.Tendsto (fun ε => (Real.exp γ + 2 * ε) * D_val lam m / (1 - Omega_val lam m g) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp γ * D_val lam m / (1 - Omega_val lam m g) ^ 2)) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
      have := h_cont.eventually ( gt_mem_nhds hC ) ; have := this.and self_mem_nhdsWithin; obtain ⟨ ε, hε₁, hε₂ ⟩ := this.exists; exact ⟨ ε, hε₂, hε₁ ⟩ ;
    refine ⟨ ε, hε.1, ?_, hε.2 ⟩;
    gcongr;
    · exact sq_pos_of_pos ( sub_pos_of_lt hadm.2.2.2.2.1 );
    · exact Real.exp_pos _;
    · linarith;
  obtain ⟨N₁, hN₁⟩ := small_interval_case ε hε.left lam m hadm.left hadm.right.right.left
  obtain ⟨N₂, hN₂⟩ := weighted_large_interval ε hε.left lam m g hadm;
  use Nat.max N₁ N₂ + 3;
  intro n hn A B hadm'
  by_cases h_empty : A = ∅ ∨ B = ∅;
  · cases h_empty <;> simp_all +decide;
    · refine div_pos ( mul_pos ?_ ?_ ) ( Real.log_pos ?_ );
      · exact lt_of_le_of_lt ( div_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( show 0 ≤ D_val lam m by exact Real.exp_nonneg _ ) ) ( sq_nonneg _ ) ) hC;
      · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) );
      · exact_mod_cast by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ;
    · exact div_pos ( mul_pos ( lt_of_le_of_lt ( by exact div_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( show 0 ≤ D_val lam m by exact Real.exp_nonneg _ ) ) ( sq_nonneg _ ) ) hC ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) );
  · obtain ⟨A', B', hA', hB', hadm'', hregA, hregB, hprod⟩ := weighted_regular_reduction n lam m g hadm A B hadm';
    by_cases h_case : ∀ k, (L_common lam k A' B').card ≤ m k;
    · have := hN₁ n ( by linarith [ Nat.le_max_left N₁ N₂ ] ) A' B' hadm'' h_case;
      rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ] at *;
      rw [ lt_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ];
      rw [ div_lt_iff₀ ] at hε;
      · rw [ div_mul_cancel₀ ] at hε <;> try nlinarith [ hadm.2.2.2.2.1 ];
        rw [ div_lt_iff₀ ] at hε;
        · nlinarith [ show 0 < D_val lam m by exact Real.exp_pos _, show 0 < Real.log n by exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ], show 0 < ( n : ℝ ) ^ 2 by exact sq_pos_of_pos <| Nat.cast_pos.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ];
        · exact sq_pos_of_pos ( sub_pos_of_lt hadm.2.2.2.2.1 );
      · exact sq_pos_of_pos ( sub_pos_of_lt hadm.2.2.2.2.1 );
    · obtain ⟨k₀, hk₀⟩ : ∃ k₀, m k₀ < (L_common lam k₀ A' B').card ∧ ∀ j, k₀ < j → (L_common lam j A' B').card ≤ m j := by
        have h_finite : Set.Finite {k | m k < (L_common lam k A' B').card} := by
          have h_finite : ∃ K, ∀ k ≥ K, (L_common lam k A' B').card = 0 := by
            have h_finite : ∃ K, ∀ k ≥ K, ∀ p ∈ I_layer lam k, p > n := by
              have h_finite : ∃ K, ∀ k ≥ K, Y_val lam k > n := by
                have h_finite : Filter.Tendsto (fun k => Y_val lam k) Filter.atTop Filter.atTop := by
                  exact Filter.Tendsto.const_mul_atTop ( by norm_num ) ( tendsto_pow_atTop_atTop_of_one_lt hadm.1 );
                exact Filter.eventually_atTop.mp ( h_finite.eventually_gt_atTop n );
              obtain ⟨ K, hK ⟩ := h_finite;
              use K;
              intros k hk p hp;
              exact_mod_cast lt_of_lt_of_le ( hK k hk ) ( Nat.le_of_ceil_le ( Finset.mem_Ico.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) );
            obtain ⟨ K, hK ⟩ := h_finite; use K; intro k hk; rw [ Finset.card_eq_zero ] ; ext p; simp +decide [ L_common ] ;
            intro hp hA; specialize hK k hk p hp; simp_all +decide [ sdiv ] ;
            exact fun x hx => Nat.not_dvd_of_pos_of_lt ( Nat.pos_of_ne_zero ( by intro t; have := hadm''.2.1 hx; aesop ) ) ( by linarith [ Finset.mem_Icc.mp ( hadm''.2.1 hx ) ] );
          exact Set.finite_iff_bddAbove.mpr ⟨ h_finite.choose, fun k hk => not_lt.1 fun contra => by have := h_finite.choose_spec k contra.le; linarith [ hk.out ] ⟩;
        obtain ⟨k₀, hk₀⟩ : ∃ k₀ ∈ {k | m k < (L_common lam k A' B').card}, ∀ k ∈ {k | m k < (L_common lam k A' B').card}, k₀ ≥ k := by
          exact ⟨ Finset.max' ( h_finite.toFinset ) ⟨ Classical.choose ( not_forall.mp h_case ), h_finite.mem_toFinset.mpr ( lt_of_not_ge ( Classical.choose_spec ( not_forall.mp h_case ) ) ) ⟩, h_finite.mem_toFinset.mp ( Finset.max'_mem _ _ ), fun k hk => Finset.le_max' _ _ ( h_finite.mem_toFinset.mpr hk ) ⟩;
        exact ⟨ k₀, hk₀.1, fun j hj => not_lt.1 fun contra => hj.not_ge <| hk₀.2 j contra ⟩;
      have := hN₂ n ( by linarith [ Nat.le_max_right N₁ N₂ ] ) A' B' hadm'' hregA hregB k₀ hk₀.1 hk₀.2;
      rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ] at *;
      rw [ lt_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ];
      rw [ div_lt_iff₀ ] at hε;
      · rw [ div_lt_iff₀ ] at hε;
        · nlinarith [ show 0 < Real.log n from Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ], show 0 < ( n : ℝ ) ^ 2 from sq_pos_of_pos <| Nat.cast_pos.mpr <| by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ];
        · exact sq_pos_of_pos ( sub_pos_of_lt hadm.2.2.2.2.1 );
      · exact sq_pos_of_pos ( sub_pos_of_lt hadm.2.2.2.2.1 )

/-! ## Dusart explicit inputs -/

/-- π_U(x) = x/log x + x/log²x + 2.53816·x/log³x -/
def piU (x : ℝ) : ℝ := x / Real.log x + x / Real.log x ^ 2 + 2.53816 * x / Real.log x ^ 3

/-- π_L(x) = x/log x + x/log²x + 2·x/log³x -/
def piL (x : ℝ) : ℝ := x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3

/-- For x ≥ 88789, π_L(x) ≤ π(x) ≤ π_U(x) -/
theorem dusart_pi_bounds (x : ℝ) (hx : x ≥ 88789) :
    piL x ≤ ((primesUpTo x).card : ℝ) ∧ ((primesUpTo x).card : ℝ) ≤ piU x := by
  exact ⟨dusart_pi_lower x hx, dusart_pi_upper x (by linarith)⟩

/-
For x ≥ 2278382, ∏_{p≤x}(1-1/p) ≥ e^{-γ}/log(x) · (1 - 0.2/log³x)
-/
theorem dusart_mertens_lower (x : ℝ) (hx : x ≥ 2278382) :
    Real.exp (-γ) / Real.log x * (1 - 0.2 / Real.log x ^ 3) ≤
      ∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) := by
  have h_mertens_bound : ∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) ≥ 1 / (Real.exp γ * Real.log x) - 1 / (5 * Real.exp γ * Real.log x ^ 4) := by
    have h0 : |∏ p ∈ primesUpTo x, (1 - 1 / (p : ℝ)) -
        1 / (Real.exp γ * Real.log x)| ≤
        1 / (5 * Real.exp γ * Real.log x ^ 4) := by
      simpa [primesUpTo, γ] using dusart_mertens_product x hx
    linarith [ abs_le.mp h0 ];
  convert h_mertens_bound.le using 1 ; norm_num [ Real.exp_neg ] ; ring

/-- For k ≤ 24, mSeq k = N_layer lam0 k, so s_val(k, mSeq k) = 0 -/
theorem s_val_mSeq_zero (k : ℕ) (hk : k ≤ 24) : s_val lam0 k (mSeq k) = 0 := by
  simp only [mSeq, if_pos hk, s_val]
  rw [if_neg (not_lt.mpr le_rfl)]

/-- Y_25 ≥ 2278382 -/
lemma Y_25_ge : Y_val lam0 25 ≥ 2278382 := by
  unfold Y_val lam0; norm_num

/-- Dusart Mertens gives a lower bound on M_layer 24 directly at Y_25 -/
lemma M_layer_24_lower : M_layer lam0 24 ≥ Real.exp (-γ) / Real.log (Y_val lam0 25) * (1 - 0.2 / Real.log (Y_val lam0 25) ^ 3) := by
  exact dusart_mertens_lower (Y_val lam0 25) Y_25_ge

/-
-log(M_24) < 3.43
-/
lemma neg_log_M_24_lt : -Real.log (M_layer lam0 24) < 3.43 := by
  -- We'll use that $\log(Y_{25}) > 17.1$ and $\log(Y_{25}) < 17.2$.
  have h_log_bounds : 17.1 < Real.log (Y_val lam0 25) ∧ Real.log (Y_val lam0 25) < 17.2 := by
    constructor <;> norm_num [ Y_val, lam0 ];
    · rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
      have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 171 = ( Real.exp 1 ) ^ 171 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ;
    · rw [ lt_div_iff₀' ] <;> norm_num;
      rw [ ← Real.log_rpow, Real.log_lt_iff_lt_exp ] <;> norm_num;
      have := Real.exp_one_gt_d9.le ; norm_num1 at * ; rw [ show Real.exp 86 = ( Real.exp 1 ) ^ 86 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( by norm_num ) ( pow_le_pow_left₀ ( by positivity ) this _ );
  -- We'll use that $\log(\log(Y_{25})) < \log(17.2) < 2.845$.
  have h_log_log_bounds : Real.log (Real.log (Y_val lam0 25)) < 2.845 := by
    -- Since $e^{2.845} > 17.2$, we have $\log(17.2) < 2.845$.
    have h_exp : Real.exp 2.845 > 17.2 := by
      norm_num [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ] at *;
      exact lt_of_lt_of_le ( by norm_num ) ( Summable.sum_le_tsum ( Finset.range 20 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) );
    exact Real.log_lt_iff_lt_exp ( by linarith ) |>.2 ( by linarith );
  -- We'll use that $\log(1 - 0.2 / \log(Y_{25})^3) > \log(1 - 0.2 / 17.1^3) > -0.00005$.
  have h_log_term_bounds : Real.log (1 - 0.2 / Real.log (Y_val lam0 25) ^ 3) > -0.00005 := by
    have h_log_term_bounds : Real.log (1 - 0.2 / Real.log (Y_val lam0 25) ^ 3) > Real.log (1 - 0.2 / 17.1 ^ 3) := by
      gcongr ; norm_num at * ; linarith;
    refine lt_of_le_of_lt ?_ h_log_term_bounds ; norm_num [ Real.log_le_iff_le_exp ];
    rw [ Real.le_log_iff_exp_le ] <;> norm_num;
    rw [ Real.exp_neg ];
    rw [ inv_eq_one_div, div_le_iff₀ ] <;> linarith [ Real.add_one_le_exp ( 1 / 20000 ) ];
  have h_log_M24 : Real.log (M_layer lam0 24) ≥ Real.log (Real.exp (-γ) / Real.log (Y_val lam0 25) * (1 - 0.2 / Real.log (Y_val lam0 25) ^ 3)) := by
    apply Real.log_le_log;
    · exact mul_pos ( div_pos ( Real.exp_pos _ ) ( by linarith ) ) ( sub_pos_of_lt ( by rw [ div_lt_iff₀ ] <;> nlinarith [ pow_pos ( by linarith : 0 < Real.log ( Y_val lam0 25 ) ) 2, pow_pos ( by linarith : 0 < Real.log ( Y_val lam0 25 ) ) 3 ] ) );
    · apply M_layer_24_lower;
  rw [ Real.log_mul, Real.log_div, Real.log_exp ] at h_log_M24 <;> norm_num at *;
  · grind +suggestions;
  · exact ⟨ by unfold Y_val; norm_num [ lam0 ], by unfold Y_val; norm_num [ lam0 ], by unfold Y_val; norm_num [ lam0 ] ⟩;
  · exact ⟨ by norm_num [ Y_val, lam0 ], by norm_num [ Y_val, lam0 ], by norm_num [ Y_val, lam0 ] ⟩;
  · exact ne_of_gt ( sub_pos_of_lt ( by rw [ div_lt_iff₀ ] <;> nlinarith [ pow_pos ( sub_pos.mpr h_log_bounds.1 ) 2 ] ) )

/-
Telescoping: ∑_{k=0}^{24} ell_val(k, N_k) = -log(M_24)
-/
lemma finite_ell_sum_eq_neg_log_M :
    ∑ k ∈ Finset.range 25, ell_val lam0 k (N_layer lam0 k) = -Real.log (M_layer lam0 24) := by
  -- By definition of $E_val$, we know that $E_val(k, N_k) = \prod_{p \in I_k} (1 - 1/p)^{-1}$.
  have h_E_val_def : ∀ k, E_val lam0 k (N_layer lam0 k) = ∏ p ∈ I_layer lam0 k, (1 - 1 / (p : ℝ))⁻¹ := by
    unfold E_val;
    intro k; refine le_antisymm ?_ ?_ <;> norm_num;
    · intro b hb hb'; rw [ ← Finset.prod_sdiff hb ] ;
      gcongr;
      · refine mul_pos ( Finset.prod_pos fun x hx => sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| by have := Finset.mem_filter.mp ( Finset.mem_sdiff.mp hx |>.1 ) ; aesop ) ( Finset.prod_pos fun x hx => sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| by have := Finset.mem_filter.mp ( hb hx ) ; aesop );
      · exact mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by have := hb ‹_›; unfold I_layer at this; aesop ) <| Finset.prod_le_one ( fun _ _ => sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by have := Finset.mem_sdiff.mp ‹_›; unfold I_layer at this; aesop ) fun _ _ => sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _;
    · exact ⟨ I_layer lam0 k, ⟨ Finset.Subset.refl _, le_rfl ⟩, le_rfl ⟩;
  -- By definition of $ell_val$, we know that $ell_val(k, N_k) = \log(\prod_{p \in I_k} (1 - 1/p)^{-1})$.
  have h_ell_val_def : ∀ k, ell_val lam0 k (N_layer lam0 k) = ∑ p ∈ I_layer lam0 k, Real.log ((1 - 1 / (p : ℝ))⁻¹) := by
    intro k
    simp [ell_val, h_E_val_def];
    apply Real.log_prod;
    exact fun p hp => sub_ne_zero_of_ne <| ne_of_gt <| inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
  -- By definition of $M_layer$, we know that $M_layer lam0 24 = \prod_{p \leq Y_{25}} (1 - 1/p)$.
  have h_M_layer_def : M_layer lam0 24 = ∏ p ∈ Finset.biUnion (Finset.range 25) (fun k => I_layer lam0 k), (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_bij ( fun p hp => p ) ?_ ?_ ?_ ?_ <;> norm_num;
    · intro p hp;
      -- By definition of $I_layer$, we know that $p \in I_layer lam0 k$ for some $k$.
      have h_exists_k : ∃ k < 25, p ∈ Finset.Ico ⌈Y_val lam0 k⌉₊ ⌈Y_val lam0 (k + 1)⌉₊ := by
        have h_exists_k : ∃ k < 25, p < ⌈Y_val lam0 (k + 1)⌉₊ := by
          use 24;
          exact ⟨ by norm_num, Nat.lt_ceil.mpr <| lt_of_le_of_lt ( Nat.cast_le.mpr <| Finset.mem_range_succ_iff.mp <| Finset.mem_filter.mp hp |>.1 ) <| Nat.floor_le ( show 0 ≤ Y_val lam0 25 by exact mul_nonneg zero_le_two <| pow_nonneg ( by norm_num [ lam0 ] ) _ ) |> lt_of_le_of_ne <| Ne.symm <| by
                                                                                                                                                                        unfold Y_val lam0; norm_num; ⟩;
        obtain ⟨ k, hk₁, hk₂ ⟩ := Nat.findX h_exists_k;
        use k;
        rcases k <;> simp_all +decide [ Nat.lt_succ_iff ];
        · unfold Y_val at * ; norm_num at *;
          exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 );
        · exact hk₂ _ le_rfl ( by linarith );
      obtain ⟨ k, hk₁, hk₂ ⟩ := h_exists_k; use k; simp_all +decide [ I_layer ] ;
      exact Finset.mem_filter.mp hp |>.2;
    · intro b x hx hb; unfold I_layer primesUpTo at *; simp_all +decide [ Nat.lt_succ_iff ] ;
      refine Nat.le_floor ?_;
      refine le_trans ?_ ( show Y_val lam0 ( x + 1 ) ≤ Y_val lam0 25 from ?_ );
      · exact le_of_lt ( Nat.lt_ceil.mp hb.1.2 );
      · exact mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_num [ lam0 ] ) ( by linarith ) ) zero_le_two;
  rw [ h_M_layer_def, Real.log_prod ] <;> norm_num [ h_ell_val_def ];
  · rw [ Finset.sum_biUnion ];
    intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left ] ;
    intro p hp hp'; simp_all +decide [ I_layer ] ;
    -- Since $k \neq l$, without loss of generality, assume $k < l$.
    wlog hkl' : k < l generalizing k l;
    · exact this hl hk ( Ne.symm hkl ) ⟨ hp', hp.2 ⟩ hp.1 ( lt_of_le_of_ne ( le_of_not_gt hkl' ) ( Ne.symm hkl ) );
    · -- Since $k < l$, we have $Y_{k+1} \leq Y_l$.
      have h_Y_le : Y_val lam0 (k + 1) ≤ Y_val lam0 l := by
        exact mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_num [ lam0 ] ) hkl' ) zero_le_two;
      grind +suggestions;
  · intro p k hk hp; rw [ sub_eq_zero ] ; norm_num;
    exact Nat.Prime.ne_one ( Finset.mem_filter.mp hp |>.2 )

/-- ∑_{k=0}^{24} ℓ_k(mSeq k) < 3.43 -/
theorem finite_log_sum :
    ∑ k ∈ Finset.range 25, ell_val lam0 k (mSeq k) < 3.43 := by
  have h : ∑ k ∈ Finset.range 25, ell_val lam0 k (mSeq k) =
    ∑ k ∈ Finset.range 25, ell_val lam0 k (N_layer lam0 k) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mSeq, if_pos (by linarith [Finset.mem_range.mp hk] : k ≤ 24)]
  rw [h, finite_ell_sum_eq_neg_log_M]
  exact neg_log_M_24_lt

/-
I_layer contains the difference of primesUpTo sets (for k ≥ 1, Y_k non-integer)
-/
lemma N_layer_ge_pi_diff (k : ℕ) (hk : 1 ≤ k) :
    (N_layer lam0 k : ℤ) ≥ (primesUpTo (Y_val lam0 (k+1))).card - (primesUpTo (Y_val lam0 k)).card := by
  simp +zetaDelta at *;
  -- For k ≥ 1, Y_k = 2 * (1931/1000)^k is never an integer, so ⌊Y_k⌋ + 1 = ⌈Y_k⌉.
  have h_not_int : ∀ k ≥ 1, ¬∃ m : ℕ, Y_val lam0 k = m := by
    intros k hk
    simp [Y_val, lam0];
    intro x hx; rw [ div_pow, mul_div, div_eq_iff ] at hx <;> norm_cast at *
    focus
      have := congr_arg ( · % 1000 ) hx
    focus
      norm_num [ Nat.mul_mod, Nat.pow_mod ] at this
    · replace hx := congr_arg ( · % 5 ) hx ; norm_num [ Nat.mul_mod, Nat.pow_mod, show k ≠ 0 by linarith ] at hx;
    · positivity;
  -- For any prime p ≤ ⌊Y_{k+1}⌋, either p ≤ ⌊Y_k⌋ or p ∈ I_layer(k).
  have h_prime_cases : ∀ p : ℕ, Nat.Prime p → p ≤ Nat.floor (Y_val lam0 (k + 1)) → p ≤ Nat.floor (Y_val lam0 k) ∨ p ∈ I_layer lam0 k := by
    intro p hp hp'; contrapose! hp'; simp_all +decide [ I_layer ] ;
    rw [ Nat.floor_lt ];
    · exact lt_of_le_of_ne ( hp'.2 ( le_of_lt ( Nat.lt_of_floor_lt hp'.1 ) ) ) ( h_not_int _ ( by linarith ) _ );
    · exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ );
  -- By definition of $primesUpTo$, we know that every prime in $primesUpTo (Y_val lam0 (k + 1))$ is either in $primesUpTo (Y_val lam0 k)$ or in $I_layer k$.
  have h_subset : primesUpTo (Y_val lam0 (k + 1)) ⊆ primesUpTo (Y_val lam0 k) ∪ I_layer lam0 k := by
    intro p hp; specialize h_prime_cases p; unfold primesUpTo at *; aesop;
  exact_mod_cast le_trans ( Finset.card_le_card h_subset ) ( Finset.card_union_le _ _ ) |> le_trans <| by norm_num [ add_comm, N_layer ] ;

/-
log(Y_k) ≥ 11 for k ≥ 25
-/
lemma log_Y_k_ge_11 (k : ℕ) (hk : 25 ≤ k) : Real.log (Y_val lam0 k) ≥ 11 := by
  -- We'll use that $Y_val lam0 k \geq 88789$ for $k \geq 25$.
  have h_Y_val_ge : Y_val lam0 k ≥ 88789 := by
    exact Y_val_ge_88789 k hk;
  rw [ ge_iff_le, Real.le_log_iff_exp_le ] <;> try linarith;
  exact le_trans ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 11 = ( Real.exp 1 ) ^ 11 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact le_trans ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num ) ) h_Y_val_ge

/-
Lower bound on piL(Y_{k+1}) - piU(Y_k) for k ≥ 25
-/
lemma piL_minus_piU_large (k : ℕ) (hk : 25 ≤ k) :
    piL (Y_val lam0 (k+1)) - piU (Y_val lam0 k) > mu0 * (Y_val lam0 k) ^ ((2:ℝ)/3) := by
  -- Set L = log(Y_k) and L1 = log(Y_{k+1}) = L + log(lam0).
  set L := Real.log (Y_val lam0 k)
  set L1 := Real.log (Y_val lam0 (k + 1));
  -- We need: Y^{1/3} * 950161/(121000*L*(L+1)) > mu0 = 29607/20000
  suffices h_suff : (Y_val lam0 k)^(1 / 3 : ℝ) * 950161 / (121000 * L * (L + 1)) > mu0 by
    -- We'll use that $piL(Y_{k+1}) \geq lam0 * Y / (L + 1)$ and $piU(Y) \leq 135 * Y / (121 * L)$.
    have h_piL : piL (Y_val lam0 (k + 1)) ≥ lam0 * Y_val lam0 k / (L + 1) := by
      refine le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ?_ ?_ ) ?_;
      · rw [ show Y_val lam0 ( k + 1 ) = lam0 * Y_val lam0 k from ?_ ];
        · gcongr;
          · exact mul_nonneg ( by norm_num [ lam0 ] ) ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) );
          · exact Real.log_pos ( by exact one_lt_mul_of_lt_of_le ( by norm_num [ lam0 ] ) ( by exact one_le_mul_of_one_le_of_one_le ( by norm_num ) ( one_le_pow₀ ( by norm_num [ lam0 ] ) ) ) );
          · rw [ Real.log_mul ( by norm_num [ lam0 ] ) ( by exact ne_of_gt ( show 0 < Y_val lam0 k from by exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ) ) ];
            linarith [ show Real.log lam0 ≤ 1 by exact Real.log_le_iff_le_exp ( by norm_num [ lam0 ] ) |>.2 <| by exact Real.exp_one_gt_d9.le.trans' <| by norm_num [ lam0 ] ];
        · unfold Y_val; ring;
      · exact div_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) ( sq_nonneg _ );
      · exact div_nonneg ( mul_nonneg zero_le_two ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) ) ( pow_nonneg ( Real.log_nonneg ( by exact le_trans ( by norm_num [ lam0 ] ) ( show Y_val lam0 ( k + 1 ) ≥ 1 by exact one_le_mul_of_one_le_of_one_le ( by norm_num ) ( one_le_pow₀ ( by norm_num [ lam0 ] ) ) ) ) ) _ )
    have h_piU : piU (Y_val lam0 k) ≤ 135 * Y_val lam0 k / (121 * L) := by
      -- We'll use that $piU(Y) \leq 135 * Y / (121 * L)$.
      have h_piU : piU (Y_val lam0 k) ≤ Y_val lam0 k / L + Y_val lam0 k / L^2 + 3 * Y_val lam0 k / L^3 := by
        unfold piU;
        gcongr;
        · exact pow_nonneg ( Real.log_nonneg ( by exact le_trans ( by norm_num [ Y_val ] ) ( Y_val_ge_88789 k hk ) ) ) _;
        · exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ );
        · norm_num;
      -- We'll use that $L \geq 11$.
      have hL_ge_11 : L ≥ 11 := by
        exact log_Y_k_ge_11 k hk;
      refine le_trans h_piU ?_;
      field_simp;
      nlinarith [ mul_le_mul_of_nonneg_left hL_ge_11 <| show 0 ≤ Y_val lam0 k from by exact mul_nonneg zero_le_two <| pow_nonneg ( by norm_num [ lam0 ] ) _, pow_two_nonneg ( L - 11 ) ];
    -- We'll use that $98651*L - 135000 \geq 950161$ for $L \geq 11$.
    have h_ineq : 98651 * L - 135000 ≥ 950161 := by
      have h_ineq : L ≥ 11 := by
        exact log_Y_k_ge_11 k hk;
      linarith;
    -- We'll use that $Y^{1/3} * 950161/(121000*L*(L+1)) > mu0$ to conclude the proof.
    have h_final : Y_val lam0 k * (98651 * L - 135000) / (121000 * L * (L + 1)) > mu0 * Y_val lam0 k ^ (2 / 3 : ℝ) := by
      refine lt_of_lt_of_le ( mul_lt_mul_of_pos_right h_suff ( Real.rpow_pos_of_pos ( show 0 < Y_val lam0 k from ?_ ) _ ) ) ?_;
      · exact mul_pos zero_lt_two ( pow_pos ( by norm_num : ( 0 : ℝ ) < 1931 / 1000 ) _ );
      · rw [ div_mul_eq_mul_div, div_le_div_iff_of_pos_right ];
        · rw [ mul_right_comm, ← Real.rpow_add ] <;> norm_num;
          · exact mul_le_mul_of_nonneg_left h_ineq <| by exact mul_nonneg zero_le_two <| pow_nonneg ( by norm_num [ lam0 ] ) _;
          · exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ );
        · exact mul_pos ( mul_pos ( by norm_num ) ( Real.log_pos ( by exact lt_of_lt_of_le ( by norm_num [ Y_val, lam0 ] ) ( Y_val_ge_88789 k hk ) ) ) ) ( add_pos_of_nonneg_of_pos ( Real.log_nonneg ( by exact le_trans ( by norm_num [ Y_val, lam0 ] ) ( Y_val_ge_88789 k hk ) ) ) zero_lt_one );
    refine lt_of_lt_of_le h_final ?_;
    refine le_trans ?_ ( sub_le_sub h_piL h_piU );
    rw [ div_sub_div, div_le_div_iff₀ ] <;> try nlinarith [ show 0 < L by exact Real.log_pos <| by exact lt_of_lt_of_le ( by norm_num [ Y_val, lam0 ] ) <| Y_val_ge_88789 k hk ];
    rw [ show lam0 = 1931 / 1000 by rfl ] ; ring_nf; norm_num;
  -- Since $L \geq 11$, we have $Y^{1/3} = \exp(L/3)$.
  have h_exp : (Y_val lam0 k)^(1 / 3 : ℝ) = Real.exp (L / 3) := by
    rw [ Real.rpow_def_of_pos ( by exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ), mul_one_div ];
  -- Since $L \geq 11$, we have $\exp(L/3) / (L * (L + 1)) \geq \exp(11/3) / (11 * 12)$.
  have h_exp_div : Real.exp (L / 3) / (L * (L + 1)) ≥ Real.exp (11 / 3) / (11 * 12) := by
    have h_exp_div : ∀ x : ℝ, 11 ≤ x → Real.exp (x / 3) / (x * (x + 1)) ≥ Real.exp (11 / 3) / (11 * 12) := by
      -- We'll use the fact that $f(x) = \frac{e^{x/3}}{x(x+1)}$ is increasing for $x \geq 11$.
      have h_inc : ∀ x : ℝ, 11 ≤ x → deriv (fun x => Real.exp (x / 3) / (x * (x + 1))) x ≥ 0 := by
        intro x hx
        have h_deriv :
            deriv (fun x : ℝ => Real.exp (x / 3) / (x * (x + 1))) x =
              Real.exp (x / 3) * (x ^ 2 - 5 * x - 3) /
                (3 * (x * (x + 1)) ^ 2) := by
          have hderiv0 :
              deriv
                  ((Real.exp ∘ fun y : ℝ => y / 3) /
                    (fun y : ℝ => y * (y + 1))) x =
                (Real.exp (x / 3) * (1 / 3) * (x * (x + 1)) -
                    (Real.exp ∘ fun y : ℝ => y / 3) x *
                      (1 * (id x + 1) + id x * 1)) /
                  (x * (x + 1)) ^ 2 :=
            HasDerivAt.deriv
              (HasDerivAt.div
                ((Real.hasDerivAt_exp (x / 3)).comp x ((hasDerivAt_id x).div_const 3))
                ((hasDerivAt_id x).mul ((hasDerivAt_id x).add_const 1))
                (show x * (x + 1) ≠ 0 by exact mul_ne_zero (by linarith) (by linarith)))
          rw [show
              deriv (fun y : ℝ => Real.exp (y / 3) / (y * (y + 1))) x =
                deriv
                  ((Real.exp ∘ fun y : ℝ => y / 3) /
                    (fun y : ℝ => y * (y + 1))) x by rfl]
          rw [hderiv0]
          simp
          field_simp
          ring
        rw [h_deriv]
        have hpoly : 0 ≤ x ^ 2 - 5 * x - 3 := by nlinarith [sq_nonneg (x - 11)]
        exact div_nonneg (mul_nonneg (Real.exp_nonneg _) hpoly) (by positivity)
      intro x hx; by_contra h_contra; push Not at h_contra;
      have := exists_deriv_eq_slope ( f := fun x => Real.exp ( x / 3 ) / ( x * ( x + 1 ) ) ) ( show x > 11 from lt_of_le_of_ne hx <| Ne.symm <| by rintro rfl; norm_num at h_contra ) ; norm_num at *;
      exact absurd ( this ( continuousOn_of_forall_continuousAt fun y hy => DifferentiableAt.continuousAt <| by exact DifferentiableAt.div ( DifferentiableAt.exp <| differentiableAt_id.div_const _ ) ( DifferentiableAt.mul ( differentiableAt_id ) <| differentiableAt_id.add_const _ ) <| by nlinarith [ hy.1 ] ) ( fun y hy => DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.div ( DifferentiableAt.exp <| differentiableAt_id.div_const _ ) ( DifferentiableAt.mul ( differentiableAt_id ) <| differentiableAt_id.add_const _ ) <| by nlinarith [ hy.1 ] ) ) ( by rintro ⟨ c, ⟨ hc1, hc2 ⟩, hc3 ⟩ ; rw [ eq_div_iff ] at hc3 <;> nlinarith [ h_inc c <| by linarith ] );
    exact h_exp_div L ( log_Y_k_ge_11 k hk );
  -- We need to show that $\exp(11/3) / (11 * 12) * 950161 / 121000 > mu0$.
  have h_final : Real.exp (11 / 3) / (11 * 12) * 950161 / 121000 > mu0 := by
    have := Real.exp_one_gt_d9.le ; norm_num1 at * ; rw [ show Real.exp ( 11 / 3 ) = ( Real.exp 1 ) ^ 3 * Real.exp ( 2 / 3 ) by rw [ ← Real.exp_nat_mul, ← Real.exp_add ] ; ring_nf ] ; norm_num at *;
    rw [ show ( 3 : ℝ ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add ] ; norm_num [ mu0 ] at * ; nlinarith [ Real.add_one_le_exp ( 2 / 3 : ℝ ), pow_le_pow_left₀ ( by positivity ) this 3 ] ;
  convert h_final.trans_le _ using 1;
  convert mul_le_mul_of_nonneg_right h_exp_div ( show ( 0 : ℝ ) ≤ 950161 / 121000 by norm_num ) using 1
  focus
    ring
  grind

/-
For k ≥ 25, m_k < N_k
-/
theorem tail_cardinalities (k : ℕ) (hk : 25 ≤ k) : mSeq k < N_layer lam0 k := by
  -- By N_layer_ge_pi_diff (already proved), N_layer lam0 k ≥ primesUpTo(Y_{k+1}).card - primesUpTo(Y_k).card.
  have hN_layer_ge_pi_diff : (N_layer lam0 k : ℝ) ≥ (primesUpTo (Y_val lam0 (k+1))).card - (primesUpTo (Y_val lam0 k)).card := by
    exact_mod_cast N_layer_ge_pi_diff k ( by linarith );
  -- By dusart_pi_bounds, primesUpTo(Y_{k+1}).card ≥ piL(Y_{k+1}) and primesUpTo(Y_k).card ≤ piU(Y_k).
  have hpi_bounds : (primesUpTo (Y_val lam0 (k+1))).card ≥ piL (Y_val lam0 (k+1)) ∧ (primesUpTo (Y_val lam0 k)).card ≤ piU (Y_val lam0 k) := by
    have := dusart_pi_bounds ( Y_val lam0 ( k + 1 ) ) ( by linarith [ Y_val_ge_88789 ( k + 1 ) ( by linarith ) ] ) ; ( have := dusart_pi_bounds ( Y_val lam0 k ) ( by linarith [ Y_val_ge_88789 k ( by linarith ) ] ) ; aesop; );
  -- By piL_minus_piU_large, piL(Y_{k+1}) - piU(Y_k) > μ₀ · Y_k^{2/3}.
  have hpi_diff_large : piL (Y_val lam0 (k+1)) - piU (Y_val lam0 k) > mu0 * (Y_val lam0 k) ^ ((2:ℝ)/3) := by
    exact piL_minus_piU_large k hk;
  unfold mSeq;
  split_ifs <;> norm_num at *;
  · omega;
  · rw [ Nat.floor_lt ];
    · linarith;
    · exact mul_nonneg ( by norm_num [ mu0 ] ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ )

/-
I_layer is contained in the difference of primesUpTo sets.
-/
lemma I_layer_subset_diff (k : ℕ) (hk : 1 ≤ k) :
    I_layer lam0 k ⊆ primesUpTo (Y_val lam0 (k+1)) \ primesUpTo (Y_val lam0 k) := by
  intro p hp;
  simp_all +decide [Finset.mem_sdiff];
  constructor <;> simp_all +decide [ primesUpTo ];
  · exact ⟨ Nat.le_floor <| le_of_lt <| Nat.lt_ceil.mp <| Finset.mem_Ico.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2, Finset.mem_filter.mp hp |>.2 ⟩;
  · intro h; have := Finset.mem_filter.mp hp; simp_all +decide [ I_layer ] ;
    -- Since $Y_k$ is not an integer for $k \geq 1$, we have $\lfloor Y_k \rfloor < Y_k$.
    have h_floor_lt : ⌊Y_val lam0 k⌋₊ < Y_val lam0 k := by
      refine lt_of_le_of_ne ( Nat.floor_le <| by exact mul_nonneg zero_le_two <| pow_nonneg ( by norm_num [ lam0 ] ) _ ) fun con => ?_;
      -- If $Y_k$ were an integer, then $2 \cdot (1931/1000)^k$ would also be an integer, which contradicts the fact that $1931$ and $1000$ are coprime.
      have h_contra : ∃ m : ℕ, 2 * 1931 ^ k = m * 1000 ^ k := by
        use ⌊Y_val lam0 k⌋₊;
        rw [ ← @Nat.cast_inj ℝ ] ; push_cast ; rw [ con ] ; norm_num [ Y_val, lam0 ] ; ring_nf;
        norm_num [ ← mul_pow ];
      obtain ⟨ m, hm ⟩ := h_contra; have := congr_arg ( · % 5 ) hm; norm_num [ Nat.mul_mod, Nat.pow_mod ] at this;
      cases k <;> norm_num at *;
    linarith [ show ( p : ℝ ) ≤ ⌊Y_val lam0 k⌋₊ by exact_mod_cast h ]

/-
N_layer is at most piU(Y_{k+1}) - piL(Y_k) for k ≥ 25
-/
lemma N_layer_le_piU_minus_piL (k : ℕ) (hk : 25 ≤ k) :
    (N_layer lam0 k : ℝ) ≤ piU (Y_val lam0 (k+1)) - piL (Y_val lam0 k) := by
  -- Since N_layer lam0 k is the cardinality of I_layer lam0 k, which is a subset of primesUpTo (Y_val lam0 (k + 1)) \ primesUpTo (Y_val lam0 k), we have N_layer lam0 k ≤ (primesUpTo (Y_val lam0 (k + 1))).card - (primesUpTo (Y_val lam0 k)).card.
  have hN_layer_le : (N_layer lam0 k : ℝ) ≤ (primesUpTo (Y_val lam0 (k + 1))).card - (primesUpTo (Y_val lam0 k)).card := by
    have hprime_subset :
        primesUpTo (Y_val lam0 k) ⊆ primesUpTo (Y_val lam0 (k + 1)) := by
      intro p hp
      have hYmono : Y_val lam0 k ≤ Y_val lam0 (k + 1) := by
        unfold Y_val
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num [lam0]) (Nat.le_succ k)) zero_le_two
      have hp_le_floor : p ≤ ⌊Y_val lam0 k⌋₊ :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hp_le_Y : (p : ℝ) ≤ Y_val lam0 k :=
        le_trans (Nat.cast_le.mpr hp_le_floor)
          (Nat.floor_le (by exact mul_nonneg zero_le_two <| pow_nonneg (by norm_num [lam0]) _))
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr <|
            Nat.lt_succ_of_le <| Nat.le_floor <| le_trans hp_le_Y hYmono,
          (Finset.mem_filter.mp hp).2⟩
    have hcard :
        (N_layer lam0 k : ℕ) ≤
          (primesUpTo (Y_val lam0 (k + 1)) \ primesUpTo (Y_val lam0 k)).card := by
      unfold N_layer
      exact Finset.card_le_card (I_layer_subset_diff k (by linarith))
    have hsdiff :
        (primesUpTo (Y_val lam0 (k + 1)) \ primesUpTo (Y_val lam0 k)).card =
          (primesUpTo (Y_val lam0 (k + 1))).card -
            (primesUpTo (Y_val lam0 k)).card := by
      rw [Finset.card_sdiff]
      rw [Finset.inter_eq_left.mpr hprime_subset]
    have hcard_real :
        (N_layer lam0 k : ℝ) ≤
          ((primesUpTo (Y_val lam0 (k + 1)) \ primesUpTo (Y_val lam0 k)).card : ℝ) := by
      exact_mod_cast hcard
    rw [hsdiff] at hcard_real
    rw [Nat.cast_sub (Finset.card_le_card hprime_subset)] at hcard_real
    exact hcard_real
  refine le_trans hN_layer_le <| sub_le_sub ?_ ?_;
  · exact dusart_pi_bounds _ ( Y_val_ge_88789 _ ( by linarith ) ) |>.2;
  · apply dusart_pi_lower (Y_val lam0 k) (Y_val_ge_88789 k hk) |> le_trans (by
    rfl)

/-
exp(γ) < 1785/1000
-/
lemma exp_gamma_lt : Real.exp γ < 1785 / 1000 := by
  have h_exp_bound : Real.exp (579 / 1000) < 1785 / 1000 := by
    have := Real.exp_bound ( show |579 / 1000| ≤ 1 by norm_num [ abs_le ] ) ( show 0 < 20 by norm_num ) ; norm_num at this;
    linarith [ abs_le.mp this ];
  exact lt_of_le_of_lt ( Real.exp_le_exp.mpr ( show γ ≤ 579 / 1000 by exact le_of_lt gamma_lt_tight ) ) h_exp_bound

/-
M_layer is positive for all k
-/
lemma M_layer_pos (k : ℕ) : M_layer lam0 k > 0 := by
  refine Finset.prod_pos fun p hp => ?_;
  exact sub_pos_of_lt ( by simpa using inv_lt_one_of_one_lt₀ ( Nat.one_lt_cast.mpr ( Nat.Prime.one_lt ( by unfold primesUpTo at hp; aesop ) ) ) )

/-- Y_{k+1} = lam0 * Y_k -/
lemma Y_val_succ (k : ℕ) : Y_val lam0 (k + 1) = lam0 * Y_val lam0 k := by
  simp [Y_val, pow_succ]; ring

/-
The analytical ratio bound for tail layers
-/
lemma tail_ratio_bound (k : ℕ) (hk : 25 ≤ k) :
    (piU (Y_val lam0 (k + 1)) - piL (Y_val lam0 k)) /
      (Y_val lam0 k * (Real.exp (-γ) / Real.log (Y_val lam0 (k + 1)) *
        (1 - 0.2 / Real.log (Y_val lam0 (k + 1)) ^ 3))) < 1.71 := by
  -- Set L = log(Y_k) and L1 = log(Y_{k+1}), so L1 = L + d where d = log(lam0). From Y_gt_one, d is positive.
  set L := Real.log (Y_val lam0 k)
  set L1 := Real.log (Y_val lam0 (k + 1))
  set d := Real.log lam0
  have hd_pos : 0 < d := by
    exact Real.log_pos <| by norm_num [ lam0 ] ;
  have hL_ge_11 : 11 ≤ L := by
    apply log_Y_k_ge_11 k hk
  have hL1_ge_14_6 : 14.6 ≤ L1 := by
    have hL1_ge_14_6 : Real.log (2278382) ≥ 14.6 := by
      norm_num [ Real.le_log_iff_exp_le ];
      have := Real.exp_one_lt_d9.le;
      rw [ show Real.exp ( 73 / 5 ) = ( Real.exp 1 ) ^ 14 * Real.exp ( 3 / 5 ) by rw [ ← Real.exp_nat_mul, ← Real.exp_add ] ; ring_nf ];
      exact le_trans ( mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by positivity ) ) ( by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp ( 3 / 5 ) = ( Real.exp ( 1 / 5 ) ) ^ 3 by rw [ ← Real.exp_nat_mul ] ; ring_nf ] ; exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( show Real.exp ( 1 / 5 ) ≤ 1.222 by have := Real.exp_one_lt_d9.le; norm_num1 at *; rw [ show Real.exp 1 = ( Real.exp ( 1 / 5 ) ) ^ 5 by rw [ ← Real.exp_nat_mul ] ; norm_num ] at this; nlinarith [ pow_pos ( Real.exp_pos ( 1 / 5 ) ) 1, pow_pos ( Real.exp_pos ( 1 / 5 ) ) 2, pow_pos ( Real.exp_pos ( 1 / 5 ) ) 3, pow_pos ( Real.exp_pos ( 1 / 5 ) ) 4 ] ) _ ) ( by positivity ) ) ( by norm_num ) ) ;
    exact hL1_ge_14_6.trans ( Real.log_le_log ( by norm_num ) ( Y_val_succ_ge_2278382 k hk ) )
  have hd_bounds : 0.658 < d ∧ d < 0.659 := by
    have := log_lam0_gt; ( have := log_lam0_lt; ( norm_num at *; aesop; ) );
  -- We'll use that $e^{-\gamma} > 0.56$ to bound the denominator from below.
  have h_exp_gamma_pos : Real.exp (-γ) > 0.56 := by
    have := exp_gamma_lt;
    rw [ Real.exp_neg ] ; norm_num at * ; nlinarith [ Real.exp_pos γ, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos γ ) ) ];
  -- Substitute the bounds into the inequality.
  have h_subst_bounds : (lam0 + lam0 / L1 + 2.53816 * lam0 / L1 ^ 2 - L1 / L - L1 / L ^ 2 - 2 * L1 / L ^ 3) < 1.71 * Real.exp (-γ) * (1 - 0.2 / L1 ^ 3) := by
    -- Substitute the bounds into the inequality and simplify.
    have h_subst_bounds_simplified : (lam0 + lam0 / L1 + 2.53816 * lam0 / L1 ^ 2 - L1 / L - L1 / L ^ 2 - 2 * L1 / L ^ 3) < 1.71 * 0.56 * (1 - 0.2 / L1 ^ 3) := by
      unfold lam0 at *;
      field_simp;
      have h_subst_bounds_simplified : L1 = L + d := by
        simp +zetaDelta at *;
        rw [ ← Real.log_mul ( by exact ne_of_gt <| by exact mul_pos zero_lt_two <| pow_pos ( by norm_num [ lam0 ] ) _ ) ( by exact ne_of_gt <| by norm_num [ lam0 ] ), show Y_val lam0 ( k + 1 ) = Y_val lam0 k * lam0 by exact Y_val_succ k ▸ by ring ];
      rw [ h_subst_bounds_simplified ] ; ring_nf at * ; norm_num at *;
      nlinarith [ pow_pos ( by linarith : 0 < L ) 3, pow_pos ( by linarith : 0 < L ) 4, pow_pos ( by linarith : 0 < L ) 5, pow_pos ( by linarith : 0 < L ) 6, pow_pos hd_pos 3, pow_pos hd_pos 4, pow_pos hd_pos 5, pow_pos hd_pos 6, mul_le_mul_of_nonneg_left hL_ge_11 ( sq_nonneg ( L - 11 ) ), mul_le_mul_of_nonneg_left hL_ge_11 ( sq_nonneg ( d - 329 / 500 ) ) ];
    exact h_subst_bounds_simplified.trans_le ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_exp_gamma_pos.le <| by norm_num ) <| sub_nonneg.mpr <| div_le_one_of_le₀ ( by norm_num at *; nlinarith [ pow_two_nonneg ( L1 - 14.6 ) ] ) <| by positivity );
  -- By definition of $piU$ and $piL$, we can rewrite the left-hand side of the inequality.
  have h_rewrite : (piU (Y_val lam0 (k + 1)) - piL (Y_val lam0 k)) = Y_val lam0 k * (lam0 / L1 + lam0 / L1 ^ 2 + 2.53816 * lam0 / L1 ^ 3 - 1 / L - 1 / L ^ 2 - 2 / L ^ 3) := by
    unfold piU piL Y_val; ring_nf;
    unfold L L1; ring_nf;
    unfold Y_val; ring_nf;
  rw [ h_rewrite, div_lt_iff₀ ];
  · convert mul_lt_mul_of_pos_left h_subst_bounds ( show 0 < Y_val lam0 k / L1 by exact div_pos ( by exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ) ( by positivity ) ) using 1 <;> ring_nf;
    norm_num [ show L1 ≠ 0 by positivity ];
  · exact mul_pos ( by exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ) ( mul_pos ( div_pos ( Real.exp_pos _ ) ( by positivity ) ) ( sub_pos.mpr ( by rw [ div_lt_iff₀ ] <;> norm_num at * <;> nlinarith [ pow_pos ( by positivity : 0 < L1 ) 2, pow_pos ( by positivity : 0 < L1 ) 3 ] ) ) )

/-
For k ≥ 25, N_k / (Y_k · M_k) < 1.71
-/
theorem tail_comparison (k : ℕ) (hk : 25 ≤ k) :
    (N_layer lam0 k : ℝ) / (Y_val lam0 k * M_layer lam0 k) < 1.71 := by
  have hN_le := N_layer_le_piU_minus_piL k hk
  have hM_lower := dusart_mertens_lower (Y_val lam0 (k + 1)) (by linarith [Y_val_succ_ge_2278382 k hk])
  have hM_pos := M_layer_pos k
  have hY_pos := Y_val_pos' k
  have h_main := tail_ratio_bound k hk
  have h_denom_pos : Y_val lam0 k * (Real.exp (-γ) / Real.log (Y_val lam0 (k + 1)) *
      (1 - 0.2 / Real.log (Y_val lam0 (k + 1)) ^ 3)) > 0 := by
    refine mul_pos hY_pos ( mul_pos ?_ ?_ );
    · refine div_pos ( Real.exp_pos _ ) ( Real.log_pos ?_ );
      exact lt_of_lt_of_le ( by norm_num [ lam0 ] ) ( Y_val_succ_ge_2278382 k hk ) |> lt_of_lt_of_le <| le_rfl; -- Y_{k+1} ≥ 2278382
    · rw [ sub_pos, div_lt_iff₀ ] <;> norm_num;
      · refine lt_of_lt_of_le ?_ ( pow_le_pow_left₀ ( by positivity ) ( show Real.log ( Y_val lam0 ( k + 1 ) ) ≥ 1 by
                                                                          rw [ ge_iff_le, Real.le_log_iff_exp_le ] <;> norm_num [ Y_val ] at *;
                                                                          · exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num [ lam0 ] ; linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 1931 / 1000 ) ( by linarith : k + 1 ≥ 26 ) ] );
                                                                          · exact pow_pos ( by norm_num [ lam0 ] ) _ ) 3 ) ; norm_num;
      · exact pow_pos ( Real.log_pos <| by exact lt_of_lt_of_le ( by norm_num [ lam0, Y_val ] ) ( Y_val_succ_ge_2278382 k hk ) ) _ -- log(Y_{k+1}) > 0
  have h_num_nonneg : piU (Y_val lam0 (k + 1)) - piL (Y_val lam0 k) ≥ 0 := by
    exact le_trans ( Nat.cast_nonneg _ ) hN_le
  have h_step1 : (N_layer lam0 k : ℝ) / (Y_val lam0 k * M_layer lam0 k) ≤
      (piU (Y_val lam0 (k + 1)) - piL (Y_val lam0 k)) /
        (Y_val lam0 k * M_layer lam0 k) := by
    gcongr
  have h_step2 : (piU (Y_val lam0 (k + 1)) - piL (Y_val lam0 k)) /
      (Y_val lam0 k * M_layer lam0 k) ≤
      (piU (Y_val lam0 (k + 1)) - piL (Y_val lam0 k)) /
        (Y_val lam0 k * (Real.exp (-γ) / Real.log (Y_val lam0 (k + 1)) *
          (1 - 0.2 / Real.log (Y_val lam0 (k + 1)) ^ 3))) := by
    apply div_le_div_of_nonneg_left (by linarith) h_denom_pos
    exact mul_le_mul_of_nonneg_left hM_lower (le_of_lt hY_pos)
  linarith

/-
∑_{k≥25} Y_k^{-1/3} < 1/57
-/
lemma geom_series_tight :
    ∑' k, (if 25 ≤ k then (Y_val lam0 k) ^ (-(1:ℝ)/3) else 0) < 1/57 := by
  -- We'll use the fact that the sum of the series is less than 1/57.
  have h_sum_lt : (∑' k, if 25 ≤ k then (Y_val lam0 k) ^ (-(1:ℝ)/3) else 0) = (∑' k, (Y_val lam0 (k + 25)) ^ (-(1:ℝ)/3)) := by
    rw [ ←Summable.sum_add_tsum_nat_add 25 ]
    focus
      norm_num [ Finset.sum_range_succ ]
    -- The series is a geometric series with ratio less than 1, so it converges.
    have h_geo_series : Summable (fun k : ℕ => (Y_val lam0 (k + 25)) ^ (-(1:ℝ)/3)) := by
      -- We'll use the fact that if the denominator grows faster than the numerator, the series converges.
      have h_series_conv : Summable (fun k : ℕ => (2 * (1931 / 1000 : ℝ) ^ k) ^ (-1 / 3 : ℝ)) := by
        -- We can factor out the constant $2^{-1/3}$ from the series.
        suffices h_factor : Summable (fun k : ℕ => (1931 / 1000 : ℝ) ^ (-k / 3 : ℝ)) by
          refine (h_factor.mul_left (2 ^ (-1 / 3 : ℝ))).congr ?_
          intro k
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity)]
          ring_nf
        norm_num [ Real.rpow_def_of_pos ];
        refine (summable_geometric_of_lt_one (by positivity)
          (show Real.exp (-Real.log (1931 / 1000) / 3) < 1 from by
            rw [Real.exp_lt_one_iff]
            ring_nf
            norm_num [Real.log_pos])).congr ?_
        intro k
        rw [← Real.exp_nat_mul]
        ring_nf
      refine (h_series_conv.comp_injective (add_left_injective 25)).congr ?_
      intro k
      rfl
    rw [ ← summable_nat_add_iff 25 ] ; aesop;
  -- We'll use the fact that $Y_{k+25} = 2 \cdot (1.931)^{k+25}$ to simplify the expression.
  have h_Y_simplified : ∀ k : ℕ, (Y_val lam0 (k + 25)) ^ (-(1:ℝ)/3) = (2 : ℝ) ^ (-(1:ℝ)/3) * (1.931 : ℝ) ^ (-(k + 25:ℝ)/3) := by
    intro k
    simp [Y_val, lam0];
    rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
    push_cast; ring_nf;
  -- We'll use the fact that $\sum_{k=0}^{\infty} (1.931)^{-k/3}$ is a geometric series with the first term $a = (1.931)^{-25/3}$ and the common ratio $r = (1.931)^{-1/3}$.
  have h_geo_series : ∑' k : ℕ, (1.931 : ℝ) ^ (-(k + 25:ℝ)/3) = (1.931 : ℝ) ^ (-(25:ℝ)/3) / (1 - (1.931 : ℝ) ^ (-(1:ℝ)/3)) := by
    have h_geo_series : ∑' k : ℕ, (1.931 : ℝ) ^ (-(k + 25:ℝ)/3) = (1.931 : ℝ) ^ (-(25:ℝ)/3) * ∑' k : ℕ, ((1.931 : ℝ) ^ (-(1:ℝ)/3)) ^ k := by
      rw [ ← tsum_mul_left ] ; congr ; ext k ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by norm_num ) ] ; rw [ ← Real.rpow_add ( by norm_num ) ] ; ring_nf;
    rw [ h_geo_series, tsum_geometric_of_lt_one ( by positivity ) ( by exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( by norm_num ) ( show ( -1 / 3 : ℝ ) < 0 by norm_num ) ) ( by norm_num ) ) ] ; ring;
  rw [ h_sum_lt, tsum_congr h_Y_simplified, tsum_mul_left, h_geo_series ];
  rw [ mul_div, div_lt_iff₀ ] <;> norm_num [ Real.rpow_neg, Real.rpow_one ];
  · rw [ show ( 25 / 3 : ℝ ) = 8 + 1 / 3 by norm_num, Real.rpow_add ] <;> norm_num;
    -- Let $y = (1931 / 1000)^{1/3}$. Then we have $y^3 = 1931 / 1000$.
    set y : ℝ := (1931 / 1000) ^ (1 / 3 : ℝ)
    have hy3 : y ^ 3 = 1931 / 1000 := by
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
    -- Let $z = 2^{1/3}$. Then we have $z^3 = 2$.
    set z : ℝ := 2 ^ (1 / 3 : ℝ)
    have hz3 : z ^ 3 = 2 := by
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
    field_simp;
    rw [ div_lt_iff₀ ] <;> nlinarith [ show 0 < y by positivity, show 0 < z by positivity, mul_pos ( show 0 < y by positivity ) ( show 0 < z by positivity ), pow_two_nonneg ( y - z ), pow_two_nonneg ( y - 1 ), pow_two_nonneg ( z - 1 ), mul_div_cancel₀ 1 ( show y ≠ 0 by positivity ) ];
  · exact inv_lt_one_of_one_lt₀ ( Real.one_lt_rpow ( by norm_num ) ( by norm_num ) )

/-
∑_{k≥25} m_k/(Y_k - 1) < 0.026
-/
theorem tail_log_sum :
    HasSum (fun k => if 25 ≤ k then (mSeq k : ℝ) / (Y_val lam0 k - 1) else 0)
      (∑' k, if 25 ≤ k then (mSeq k : ℝ) / (Y_val lam0 k - 1) else 0) ∧
    ∑' k, (if 25 ≤ k then (mSeq k : ℝ) / (Y_val lam0 k - 1) else 0) < 0.026 := by
  constructor;
  · refine Summable.hasSum ?_;
    -- We'll use the comparison test. Since \( \frac{m_k}{Y_k - 1} \leq \frac{\mu_0 Y_k^{2/3}}{Y_k - 1} \), it suffices to show that \( \sum_{k=25}^{\infty} \frac{\mu_0 Y_k^{2/3}}{Y_k - 1} \) converges.
    suffices h_comp : Summable (fun k : ℕ => if 25 ≤ k then (mu0 * (Y_val lam0 k) ^ (2/3 : ℝ)) / (Y_val lam0 k - 1) else 0) by
      refine h_comp.of_nonneg_of_le ( fun k => ?_ ) ( fun k => ?_ );
      · split_ifs <;> norm_num;
        exact div_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg_of_le ( by exact le_trans ( by norm_num ) ( Y_val_ge_88789 k ‹_› ) ) );
      · split_ifs <;> norm_num [ mSeq ];
        split_ifs;
        · linarith;
        · gcongr;
          · exact sub_nonneg_of_le ( by exact le_trans ( by norm_num [ lam0 ] ) ( mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_num [ lam0 ] ) ‹25 ≤ k› ) zero_le_two ) );
          · exact Nat.floor_le ( mul_nonneg ( by norm_num [ mu0 ] ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ ) );
    -- We'll use the comparison test. Since \( \frac{\mu_0 Y_k^{2/3}}{Y_k - 1} \leq \frac{\mu_0 Y_k^{2/3}}{Y_k / 2} = \frac{2 \mu_0}{Y_k^{1/3}} \), it suffices to show that \( \sum_{k=25}^{\infty} \frac{2 \mu_0}{Y_k^{1/3}} \) converges.
    suffices h_comp : Summable (fun k : ℕ => if 25 ≤ k then (2 * mu0) / (Y_val lam0 k) ^ (1/3 : ℝ) else 0) by
      refine h_comp.of_nonneg_of_le ( fun k => ?_ ) ( fun k => ?_ );
      · split_ifs <;> norm_num [ mu0, Y_val ];
        exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ ) ) ( sub_nonneg_of_le ( by exact one_le_mul_of_one_le_of_one_le ( by norm_num ) ( one_le_pow₀ ( by norm_num [ lam0 ] ) ) ) );
      · split_ifs <;> norm_num;
        rw [ div_le_div_iff₀ ] <;> norm_num [ Y_val ];
        · rw [ mul_assoc, ← Real.rpow_add ] <;> norm_num;
          · nlinarith [ show ( lam0 : ℝ ) ^ k ≥ 1 by exact one_le_pow₀ ( by norm_num [ lam0 ] ), show ( mu0 : ℝ ) ≥ 1 by norm_num [ mu0 ] ];
          · exact pow_pos ( by norm_num : ( 0 : ℝ ) < 1931 / 1000 ) _;
        · exact one_lt_mul_of_lt_of_le ( by norm_num ) ( one_le_pow₀ ( by norm_num [ lam0 ] ) );
        · exact Real.rpow_pos_of_pos ( by exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ) _;
    -- The series $\sum_{k=25}^{\infty} \frac{1}{Y_k^{1/3}}$ is a geometric series with ratio $1 / \lambda^{1/3}$.
    have h_geo_series : Summable (fun k : ℕ => (1 : ℝ) / (Y_val lam0 k) ^ (1 / 3 : ℝ)) := by
      have h_summable : Summable (fun k : ℕ => (1 : ℝ) / (2 ^ (1 / 3 : ℝ) * (lam0 ^ (1 / 3 : ℝ)) ^ k)) := by
        norm_num [ lam0 ];
        exact Summable.mul_right _ ( by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ ( Real.one_lt_rpow ( by norm_num ) ( by norm_num ) ) ) );
      convert h_summable using 2 ; norm_num [ Y_val ] ; ring_nf;
      rw [ Real.mul_rpow ( by exact pow_nonneg ( by norm_num [ lam0 ] ) _ ) ( by norm_num ), ← Real.rpow_natCast, ← Real.rpow_mul ( by norm_num [ lam0 ] ) ] ; ring_nf;
      rw [ inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul ( by norm_num [ lam0 ] ) ] ; ring_nf;
    rw [ ← summable_nat_add_iff 25 ] at *;
    simpa [ div_eq_mul_inv ] using h_geo_series.mul_left ( 2 * mu0 );
  · refine lt_of_le_of_lt
      ( Summable.tsum_le_tsum
        (g := fun k => if 25 ≤ k then ( 29607 / 20000 ) * ( Y_val lam0 k ) ^ ( - ( 1 : ℝ ) / 3 ) * ( 1 + 1 / 88788 ) else 0)
        ?_ ?_ ?_ ) ?_;
    · intro k
      by_cases hk : 25 ≤ k
      · simp [hk]
      -- By definition of $mSeq$, we know that $mSeq k \leq mu0 * Y_val lam0 k ^ (2 / 3 : ℝ)$.
        have h_mSeq_le : (mSeq k : ℝ) ≤ (29607 / 20000) * (Y_val lam0 k) ^ (2 / 3 : ℝ) := by
          unfold mSeq;
          split_ifs <;> norm_num [ mu0 ];
          · grind;
          · exact Nat.floor_le ( by exact mul_nonneg ( by norm_num ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ ) );
        rw [ div_le_iff₀ ] <;> norm_num [ Y_val ] at *;
        · rw [ show ( 2 / 3 : ℝ ) = -1 / 3 + 1 by norm_num, Real.rpow_add ] at * <;> norm_num at *;
          · have h_Y_val_ge : (2 * lam0 ^ k : ℝ) ≥ 88789 := by
              exact le_trans ( by norm_num [ lam0 ] ) ( mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_num [ lam0 ] ) hk ) zero_le_two );
            nlinarith [ show ( 29607 / 20000 : ℝ ) * ( ( 2 * lam0 ^ k ) ^ ( - ( 1 / 3 : ℝ ) ) ) > 0 by positivity ];
          · exact pow_pos ( by norm_num [ lam0 ] ) _;
        · exact one_lt_mul_of_lt_of_le ( by norm_num ) ( one_le_pow₀ ( by norm_num [ lam0 ] ) );
      · simp [hk]
    · refine Summable.of_nonneg_of_le ( fun k => ?_ ) ( fun k => ?_ ) ( show Summable fun k : ℕ => if 25 ≤ k then ( 29607 / 20000 : ℝ ) * ( 1 + 1 / 88788 ) * ( Y_val lam0 k ) ^ ( - ( 1 : ℝ ) / 3 ) else 0 from ?_ );
      · split_ifs <;> norm_num;
        exact div_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg_of_le ( by exact le_trans ( by norm_num ) ( Y_val_ge_88789 k ‹_› ) ) );
      · split_ifs <;> norm_num;
        -- By definition of $mSeq$, we know that $mSeq k \leq \mu_0 \cdot Y_k^{2/3}$.
        have h_mSeq_le : (mSeq k : ℝ) ≤ mu0 * (Y_val lam0 k) ^ ((2 : ℝ) / 3) := by
          unfold mSeq;
          split_ifs <;> norm_num;
          · linarith;
          · exact Nat.floor_le ( mul_nonneg ( by norm_num [ mu0 ] ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ ) );
        rw [ div_le_iff₀ ] <;> norm_num [ mu0, Y_val ] at *;
        · rw [ show ( 2 / 3 : ℝ ) = -1 / 3 + 1 by norm_num, Real.rpow_add ] at * <;> norm_num at *;
          · have h_Y_k_ge_88789 : (2 * lam0 ^ k : ℝ) ≥ 88789 := by
              exact le_trans ( by norm_num [ lam0 ] ) ( mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_num [ lam0 ] ) ‹25 ≤ k› ) zero_le_two );
            nlinarith [ Real.rpow_pos_of_pos ( by positivity : 0 < ( 2 * lam0 ^ k : ℝ ) ) ( - ( 1 / 3 ) ) ];
          · exact pow_pos ( by norm_num [ lam0 ] ) _;
        · exact one_lt_mul_of_lt_of_le ( by norm_num ) ( one_le_pow₀ ( by norm_num [ lam0 ] ) );
      · -- We'll use the fact that if the series $\sum_{k=25}^\infty a_k$ converges, then $\sum_{k=25}^\infty c a_k$ also converges for any constant $c$.
        have h_summable : Summable (fun k : ℕ => if 25 ≤ k then (Y_val lam0 k) ^ (-(1 : ℝ) / 3) else 0) := by
          have h_summable : Summable (fun k : ℕ => (Y_val lam0 k) ^ (-(1 : ℝ) / 3)) := by
            norm_num [ Y_val ];
            norm_num [ Real.mul_rpow, Real.rpow_neg, lam0 ];
            norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( by norm_num : ( 0 : ℝ ) ≤ 1931 / 1000 ), ← Real.rpow_neg ( by norm_num : ( 0 : ℝ ) ≤ 1931 / 1000 ) ];
            norm_num [ Real.rpow_def_of_pos ];
            -- The series $\sum_{k=0}^{\infty} \exp(-(k \cdot \log(1931/1000) \cdot (1/3)))$ is a geometric series with common ratio $r = \exp(-\log(1931/1000) \cdot (1/3))$.
            have h_geo_series : Summable (fun k : ℕ => (Real.exp (-Real.log (1931 / 1000) * (1 / 3))) ^ k) := by
              exact summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; norm_num [ Real.log_pos ] );
            refine (h_geo_series.mul_right ((Real.exp (Real.log 2 * (1 / 3)))⁻¹)).congr ?_
            intro k
            rw [← Real.exp_nat_mul]
            ring_nf
          rw [ ← summable_nat_add_iff 25 ] at * ; aesop;
        refine (h_summable.mul_left (29607 / 20000 * (1 + 1 / 88788))).congr ?_
        intro k
        by_cases hk : 25 ≤ k <;> simp [hk, mul_comm]
    · -- We'll use the fact that if the series $\sum_{k=25}^{\infty} a_k$ converges, then $\sum_{k=25}^{\infty} c a_k$ also converges for any constant $c$.
      have h_summable : Summable (fun k : ℕ => if 25 ≤ k then (Y_val lam0 k) ^ (-(1 : ℝ) / 3) else 0) := by
        have h_summable : Summable (fun k : ℕ => (Y_val lam0 k) ^ (-(1 : ℝ) / 3)) := by
          norm_num [ Y_val ];
          norm_num [ Real.mul_rpow, Real.rpow_neg, lam0 ];
          norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( by norm_num : ( 0 : ℝ ) ≤ 1931 / 1000 ), ← Real.rpow_neg ( by norm_num : ( 0 : ℝ ) ≤ 1931 / 1000 ) ];
          norm_num [ Real.rpow_def_of_pos ];
          -- The series $\sum_{k=0}^{\infty} \exp(-(k \cdot \log(1931/1000) \cdot (1/3)))$ is a geometric series with common ratio $r = \exp(-\log(1931/1000) \cdot (1/3))$.
          have h_geo_series : Summable (fun k : ℕ => (Real.exp (-Real.log (1931 / 1000) * (1 / 3))) ^ k) := by
            exact summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; norm_num [ Real.log_pos ] );
          refine (h_geo_series.mul_right ((Real.exp (Real.log 2 * (1 / 3)))⁻¹)).congr ?_
          intro k
          rw [← Real.exp_nat_mul]
          ring_nf
        rw [ ← summable_nat_add_iff 25 ] at * ; aesop;
      refine (h_summable.mul_left (29607 / 20000 * (1 + 1 / 88788))).congr ?_
      intro k
      by_cases hk : 25 ≤ k <;> simp [hk, mul_assoc, mul_comm]
    · -- Factor out the constant term $(29607 / 20000) * (1 + 1 / 88788)$ from the sum.
      suffices h_factor : (∑' i, if 25 ≤ i then (Y_val lam0 i) ^ (-1 / 3 : ℝ) else 0) < (26e-3 / ((29607 / 20000) * (1 + 1 / 88788))) by
        convert mul_lt_mul_of_pos_left h_factor ( show 0 < ( 29607 / 20000 : ℝ ) * ( 1 + 1 / 88788 ) by norm_num ) using 1 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ← tsum_mul_left ];
      exact lt_of_lt_of_le ( geom_series_tight ) ( by norm_num )

def lam0' : ℝ := 1931 / 1000
def Y_val' (k : ℕ) : ℝ := 2 * lam0' ^ k

/-- g_k = 1 for k ≤ 150, (k-149)² for k > 150 -/
def gSeq' (k : ℕ) : ℝ :=
  if k ≤ 150 then 1 else ((k : ℝ) - 149) ^ 2

lemma lam0'_pos : (0 : ℝ) < lam0' := by norm_num [lam0']
lemma lam0'_gt_one : (1 : ℝ) < lam0' := by norm_num [lam0']
lemma Y_val'_pos (k : ℕ) : 0 < Y_val' k := by unfold Y_val' lam0'; positivity

lemma gSeq'_ge_one (k : ℕ) : 1 ≤ gSeq' k := by
  unfold gSeq'; split_ifs with h
  · exact le_refl 1
  · push Not at h; have hk : (k : ℝ) ≥ 151 := by exact_mod_cast h
    nlinarith

/-
lam0'^{-1/3} < 81/100
-/
lemma lam0'_rpow_neg_third_lt : lam0' ^ (-(1:ℝ)/3) < 81/100 := by
  -- We'll use that $lam0'^{-1/3} = \left(\frac{1931}{1000}\right)^{-1/3} = \left(\frac{1000}{1931}\right)^{1/3}$
  suffices h_suff : (1000 / 1931 : ℝ) ^ (1 / 3 : ℝ) < 81 / 100 by
    convert h_suff using 1 ; norm_num [ Real.rpow_neg, lam0' ];
    rw [ ← Real.inv_rpow ] <;> norm_num;
  exact lt_of_lt_of_le ( Real.rpow_lt_rpow ( by norm_num ) ( show ( 1000 / 1931 : ℝ ) < ( 81 / 100 ) ^ 3 by norm_num ) ( by norm_num ) ) ( by norm_num )

/-
Summability of Y_k^{-1/3}
-/
lemma summable_Y'_rpow :
    Summable (fun k : ℕ => (Y_val' k) ^ (-(1 : ℝ)/3)) := by
  norm_num [ Y_val' ];
  -- Factor out the constant $2^{-1/3}$ from the series.
  suffices h_factor : Summable (fun k : ℕ => (lam0' ^ k : ℝ) ^ (-(1 / 3 : ℝ))) by
    refine (h_factor.mul_left (2 ^ (-(1 / 3) : ℝ))).congr ?_
    intro k
    rw [Real.mul_rpow (by positivity)
      (by exact pow_nonneg (by exact div_nonneg (by norm_num) (by norm_num)) _)]
  -- Recognize that this is a geometric series with common ratio $r = \left(\frac{1}{lam0'}\right)^{1/3}$.
  have h_geo_series : Summable (fun k => ((1 / lam0') ^ (1 / 3 : ℝ)) ^ k) := by
    exact summable_geometric_of_lt_one ( by exact Real.rpow_nonneg ( by exact div_nonneg zero_le_one ( by exact le_of_lt ( show 0 < lam0' by exact lam0'_pos ) ) ) _ ) ( by exact Real.rpow_lt_one ( by exact div_nonneg zero_le_one ( by exact le_of_lt ( show 0 < lam0' by exact lam0'_pos ) ) ) ( by exact div_lt_one ( by exact lam0'_pos ) |>.2 ( by exact show 1 < lam0' by exact lam0'_gt_one ) ) ( by norm_num ) );
  refine h_geo_series.congr ?_
  intro k
  rw [show (1 / lam0') ^ (1 / 3 : ℝ) = lam0' ^ (-1 / 3 : ℝ) by
    rw [one_div, Real.inv_rpow (by exact le_of_lt lam0'_pos),
      ← Real.rpow_neg (by exact le_of_lt lam0'_pos)]
    congr 1
    ring]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact le_of_lt lam0'_pos)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact le_of_lt lam0'_pos)]
  ring_nf

-- Summability of the conditional sum
lemma summable_Y'_rpow_ite :
    Summable (fun k : ℕ => if 25 ≤ k then (Y_val' k) ^ (-(1:ℝ)/3) else 0) := by
  apply Summable.of_nonneg_of_le
  · intro k; split_ifs with h
    · exact Real.rpow_nonneg (le_of_lt (Y_val'_pos k)) _
    · exact le_refl 0
  · intro k; split_ifs
    · exact le_refl _
    · exact Real.rpow_nonneg (le_of_lt (Y_val'_pos k)) _
  · exact summable_Y'_rpow

/-
geom_series_bound: ∑_{k≥25} Y_k^{-1/3} < 0.02
-/
lemma geom_series_bound' :
    ∑' k, (if 25 ≤ k then (Y_val' k) ^ (-(1:ℝ)/3) else 0) < 0.02 := by
  have h_eq :
      (fun k : ℕ => if 25 ≤ k then (Y_val' k) ^ (-(1:ℝ) / 3) else 0) =
        fun k : ℕ => if 25 ≤ k then (Y_val lam0 k) ^ (-(1:ℝ) / 3) else 0 := by
    funext k
    simp [Y_val', Y_val, lam0', lam0]
  rw [h_eq]
  exact lt_trans geom_series_tight (by norm_num)

/-
Summability of gSeq' * Y_k^{-1/3}
-/
lemma summable_gSeq'_Y :
    Summable (fun k : ℕ => if 25 ≤ k then gSeq' k * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) := by
  have h_summable_cond : Summable (fun k : ℕ => if 25 ≤ k then (k : ℝ) ^ 2 * Y_val' k ^ (-1 / 3 : ℝ) else 0) := by
    have hgeom :
        Summable (fun k : ℕ => (k : ℝ) ^ 2 * (lam0' ^ (-1 / 3 : ℝ)) ^ k) := by
      refine summable_pow_mul_geometric_of_norm_lt_one 2 ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos lam0'_pos _)]
      exact lt_of_lt_of_le
        (Real.rpow_lt_rpow_of_exponent_lt lam0'_gt_one
          (show (-1 / 3 : ℝ) < 0 by norm_num))
        (by norm_num)
    have hfull :
        Summable (fun k : ℕ => (k : ℝ) ^ 2 * (Y_val' k) ^ (-1 / 3 : ℝ)) := by
      refine (hgeom.mul_left (2 ^ (-1 / 3 : ℝ))).congr ?_
      intro k
      simp [Y_val']
      rw [Real.mul_rpow (by norm_num)
        (by exact pow_nonneg (by exact le_of_lt lam0'_pos) _)]
      have hpow :
          (lam0' ^ k) ^ (-1 / 3 : ℝ) = (lam0' ^ (-1 / 3 : ℝ)) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact le_of_lt lam0'_pos)]
        rw [mul_comm, Real.rpow_mul (by exact le_of_lt lam0'_pos), Real.rpow_natCast]
      rw [hpow]
      ring
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hfull
    · by_cases hk : 25 ≤ k
      · simp [hk]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (Y_val'_pos k)) _)
      · simp [hk]
    · by_cases hk : 25 ≤ k
      · simp [hk]
      · simp [hk]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (Y_val'_pos k)) _)
  -- Since $gSeq' k \leq k^2 + 1$ for all $k$, we can use the comparison test.
  have h_bound : ∀ k : ℕ, gSeq' k ≤ k^2 + 1 := by
    intro k
    by_cases hk : k ≤ 150;
    · unfold gSeq';
      split_ifs ; nlinarith;
    · unfold gSeq';
      rw [ if_neg hk ] ; nlinarith [ show ( k : ℝ ) ≥ 151 by exact_mod_cast not_le.mp hk ];
  refine .of_nonneg_of_le ( fun k => ?_ ) ( fun k => ?_ ) ( h_summable_cond.add ( show Summable fun k : ℕ => if 25 ≤ k then 1 * Y_val' k ^ ( -1 / 3 : ℝ ) else 0 from ?_ ) );
  · split_ifs <;> first | positivity | exact mul_nonneg ( le_trans ( by norm_num ) ( gSeq'_ge_one _ ) ) ( Real.rpow_nonneg ( by exact le_trans ( by norm_num ) ( Y_val'_pos _ |> le_of_lt ) ) _ ) ;
  · split_ifs <;> nlinarith [ h_bound k, show 0 ≤ Y_val' k ^ ( -1 / 3 : ℝ ) by exact Real.rpow_nonneg ( le_of_lt ( Y_val'_pos k ) ) _ ];
  · convert summable_Y'_rpow_ite using 2 ; aesop

/-
The sum decomposes as Y-part + excess-part
-/
lemma tail_split :
    ∑' k, (if 25 ≤ k then gSeq' k * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) ≤
    ∑' k, (if 25 ≤ k then (Y_val' k) ^ (-(1 : ℝ)/3) else 0) +
    ∑' k, (if 151 ≤ k then (gSeq' k - 1) * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) := by
  have h_excess :
      (fun k : ℕ => if 151 ≤ k then (gSeq' k - 1) * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) =
        fun k : ℕ =>
          (if 25 ≤ k then gSeq' k * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) -
            (if 25 ≤ k then (Y_val' k) ^ (-(1 : ℝ)/3) else 0) := by
    funext k
    by_cases h151 : 151 ≤ k
    · have h25 : 25 ≤ k := by omega
      simp [h151, h25]
      ring
    · by_cases h25 : 25 ≤ k
      · have hk : k ≤ 150 := by omega
        simp [h151, h25, gSeq', hk]
      · simp [h151, h25]
  rw [h_excess]
  rw [← Summable.tsum_add summable_Y'_rpow_ite
    (summable_gSeq'_Y.sub summable_Y'_rpow_ite)]
  exact le_of_eq (tsum_congr fun k => by ring)

-- Summability of the excess part
lemma summable_excess :
    Summable (fun k : ℕ => if 151 ≤ k then (gSeq' k - 1) * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) := by
  exact summable_gSeq'_Y.sub summable_Y'_rpow_ite |>.congr fun n => by
    simp only [gSeq', Y_val']
    split_ifs with h1 h2 h3 <;> ring_nf <;> simp_all <;> omega

/-
The excess tail is tiny
-/
lemma tail_excess_bound :
    ∑' k, (if 151 ≤ k then (gSeq' k - 1) * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) < 1/10^8 := by
  -- Let's simplify the sum by shifting the index.
  suffices h_simp' : (∑' j : ℕ, if 0 ≤ j then (gSeq' (j + 151) - 1) * (Y_val' (j + 151)) ^ (-1 / 3 : ℝ) else 0) < 1 / 10 ^ 8 by
    rw [ ←Summable.sum_add_tsum_nat_add 151 ];
    · rw [ Finset.sum_eq_zero ] <;> aesop;
    · convert summable_excess using 1;
  -- We'll use the fact that $(j+2)^2 \leq 16 \cdot (j+1)^2$ for all $j \geq 0$.
  have h_bound : ∀ j : ℕ, (gSeq' (j + 151) - 1) * (Y_val' (j + 151)) ^ (-1 / 3 : ℝ) ≤ 16 * (j + 1) ^ 2 * (81 / 100) ^ (j + 151) := by
    -- We'll use the fact that $(j+2)^2 \leq 16 \cdot (j+1)^2$ for all $j \geq 0$ to bound the term.
    have h_bound : ∀ j : ℕ, (gSeq' (j + 151) - 1) ≤ 16 * (j + 1) ^ 2 := by
      intro j; unfold gSeq'; norm_num; ring_nf;
      split_ifs <;> nlinarith;
    -- We'll use the fact that $(Y_val' (j + 151)) ^ (-1 / 3 : ℝ) \leq (81 / 100) ^ (j + 151)$.
    have h_exp_bound : ∀ j : ℕ, (Y_val' (j + 151)) ^ (-1 / 3 : ℝ) ≤ (81 / 100) ^ (j + 151) := by
      intros j
      have h_exp_bound : (Y_val' (j + 151)) ^ (-1 / 3 : ℝ) ≤ (lam0') ^ (-(j + 151) / 3 : ℝ) := by
        unfold Y_val';
        rw [ Real.mul_rpow ( by positivity ) ( by exact pow_nonneg ( by exact div_nonneg ( by norm_num ) ( by norm_num ) ) _ ), ← Real.rpow_natCast, ← Real.rpow_mul ( by exact div_nonneg ( by norm_num ) ( by norm_num ) ) ] ; ring_nf ; norm_num;
        rw [ show ( - ( ( 151 + j : ℝ ) * ( 1 / 3 ) ) ) = - ( 151 / 3 ) + - ( j * ( 1 / 3 ) ) by ring ] ; norm_num [ Real.rpow_def_of_pos ] ; ring_nf ; norm_num;
        exact mul_le_of_le_one_left ( Real.rpow_nonneg ( by exact div_nonneg ( by norm_num ) ( by norm_num ) ) _ ) ( Real.exp_le_one_iff.mpr ( by linarith [ Real.log_nonneg one_le_two ] ) );
      have h_exp_bound : (lam0') ^ (-(j + 151) / 3 : ℝ) ≤ (81 / 100) ^ (j + 151) := by
        have h_exp_bound : (lam0') ^ (-1 / 3 : ℝ) ≤ 81 / 100 := by
          exact le_of_lt lam0'_rpow_neg_third_lt
        have hpow :
            (lam0') ^ ((-151 + -(j : ℝ)) / 3) =
              (lam0' ^ (-1 / 3 : ℝ)) ^ (j + 151) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact le_of_lt lam0'_pos)]
          congr 1
          norm_num [Nat.cast_add]
          ring
        simpa [hpow] using
          pow_le_pow_left₀
            (Real.rpow_nonneg (by exact le_of_lt lam0'_pos) _)
            h_exp_bound (j + 151)
      linarith;
    exact fun j => mul_le_mul ( h_bound j ) ( h_exp_bound j ) ( by exact Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0' ] ) _ ) ) _ ) ( by positivity );
  -- We'll use the fact that $\sum_{j=0}^{\infty} (j+1)^2 x^j = \frac{1 + x}{(1 - x)^3}$ for $|x| < 1$.
  have h_sum : ∀ x : ℝ, |x| < 1 → ∑' j : ℕ, (j + 1 : ℝ) ^ 2 * x ^ j = (1 + x) / (1 - x) ^ 3 := by
    -- Let's choose any $x$ such that $|x| < 1$.
    intro x hx
    have h_series : ∑' j : ℕ, (j + 1 : ℝ) ^ 2 * x ^ j = (∑' j : ℕ, x ^ j) + 2 * (∑' j : ℕ, j * x ^ j) + (∑' j : ℕ, j ^ 2 * x ^ j) := by
      nontriviality;
      rw [ ← tsum_mul_left, ← Summable.tsum_add, ← Summable.tsum_add ]
      focus
        congr
      focus
        ext j
      focus
        ring
      · refine Summable.add ( summable_geometric_of_abs_lt_one hx ) ?_;
        refine summable_of_ratio_norm_eventually_le (r := (( 1 + |x| ) / 2)) ?_ ?_;
        · linarith;
        · norm_num [ abs_of_nonneg, add_nonneg ];
          refine ⟨ ⌈ ( 1 + |x| ) / ( 1 - |x| ) ⌉₊ + 1, fun n hn => ?_ ⟩ ; replace := Nat.lt_of_ceil_lt hn ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ pow_nonneg ( abs_nonneg x ) n, pow_succ' ( |x| ) n, abs_nonneg x, abs_lt.mp hx ] ;
      · refine summable_of_ratio_norm_eventually_le (r := (( 1 + |x| ) / 2)) ?_ ?_;
        · linarith;
        · -- We'll use the fact that |x| < 1 to find such an N.
          have h_eventually : ∃ N, ∀ n ≥ N, |x| * (n + 1) ^ 2 ≤ (1 + |x|) / 2 * n ^ 2 := by
            exact ⟨ 2 * ( 1 + |x| ) / ( 1 - |x| ), fun n hn => by nlinarith [ abs_nonneg x, mul_div_cancel₀ ( 2 * ( 1 + |x| ) ) ( by linarith : ( 1 - |x| ) ≠ 0 ), sq_nonneg ( n - 2 * ( 1 + |x| ) / ( 1 - |x| ) ) ] ⟩;
          simp +zetaDelta at *;
          exact ⟨ ⌈h_eventually.choose⌉₊, fun n hn => by have := h_eventually.choose_spec n ( Nat.le_of_ceil_le hn ) ; ring_nf at this ⊢; nlinarith [ pow_nonneg ( abs_nonneg x ) n ] ⟩;
      · exact summable_geometric_of_abs_lt_one hx;
      · refine summable_of_ratio_norm_eventually_le (r := (( 1 + |x| ) / 2)) ?_ ?_;
        · linarith;
        · norm_num [ abs_of_nonneg, add_nonneg ];
          refine ⟨ ⌈ ( 1 + |x| ) / ( 1 - |x| ) ⌉₊ + 1, fun n hn => ?_ ⟩ ; have := Nat.lt_of_ceil_lt hn ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ pow_nonneg ( abs_nonneg x ) n, pow_succ' ( |x| ) n, abs_nonneg x, abs_lt.mp hx ] ;
    -- We'll use the fact that $\sum_{j=0}^{\infty} j x^j = \frac{x}{(1-x)^2}$ and $\sum_{j=0}^{\infty} j^2 x^j = \frac{x(1+x)}{(1-x)^3}$.
    have h_series_j : ∑' j : ℕ, (j : ℝ) * x ^ j = x / (1 - x) ^ 2 := by
      exact tsum_coe_mul_geometric_of_norm_lt_one hx
    have h_series_j2 : ∑' j : ℕ, (j : ℝ) ^ 2 * x ^ j = x * (1 + x) / (1 - x) ^ 3 := by
      have h_series_j2 : ∑' j : ℕ, (j : ℝ) ^ 2 * x ^ j = x * (∑' j : ℕ, (j + 1 : ℝ) ^ 2 * x ^ j) := by
        rw [ ← tsum_mul_left ] ; rw [ Summable.tsum_eq_zero_add ]
        focus
          norm_num
        · exact tsum_congr fun n => by ring;
        · refine summable_of_ratio_norm_eventually_le (r := (( 1 + |x| ) / 2)) ?_ ?_;
          · linarith;
          · -- We'll use the fact that |x| < 1 to find such an N.
            have h_eventually : ∃ N, ∀ n ≥ N, |x| * (n + 1 : ℝ) ^ 2 ≤ (1 + |x|) / 2 * n ^ 2 := by
              exact ⟨ 2 * ( 1 + |x| ) / ( 1 - |x| ), fun n hn => by nlinarith [ abs_nonneg x, mul_div_cancel₀ ( 2 * ( 1 + |x| ) ) ( by linarith [ abs_nonneg x ] : ( 1 - |x| ) ≠ 0 ), sq_nonneg ( n - 2 * ( 1 + |x| ) / ( 1 - |x| ) ) ] ⟩;
            simp +zetaDelta at *;
            exact ⟨ ⌈h_eventually.choose⌉₊, fun n hn => by have := h_eventually.choose_spec n ( Nat.le_of_ceil_le hn ) ; ring_nf at this ⊢; nlinarith [ pow_nonneg ( abs_nonneg x ) n ] ⟩;
      rw [ tsum_geometric_of_abs_lt_one hx ] at *;
      rw [ eq_div_iff ] at * <;> nlinarith [ abs_lt.mp hx, inv_mul_cancel₀ ( by linarith [ abs_lt.mp hx ] : ( 1 - x ) ≠ 0 ), pow_pos ( by linarith [ abs_lt.mp hx ] : 0 < 1 - x ) 2, pow_pos ( by linarith [ abs_lt.mp hx ] : 0 < 1 - x ) 3 ];
    rw [ h_series, tsum_geometric_of_abs_lt_one hx, h_series_j, h_series_j2 ];
    grind;
  -- Applying the bound and the sum formula, we get:
  have h_final_bound : (∑' j : ℕ, (gSeq' (j + 151) - 1) * (Y_val' (j + 151)) ^ (-1 / 3 : ℝ)) ≤ 16 * (81 / 100) ^ 151 * ((1 + 81 / 100) / (1 - 81 / 100) ^ 3) := by
    refine le_trans ( Summable.tsum_le_tsum h_bound ?_ ?_ ) ?_;
    · refine Summable.of_nonneg_of_le ( fun j => ?_ ) ( fun j => h_bound j ) ?_;
      · unfold gSeq' Y_val';
        split_ifs <;> norm_num;
        exact mul_nonneg ( by ring_nf; positivity ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by unfold lam0'; norm_num ) _ ) ) _ );
      · have := h_sum ( 81 / 100 ) ( by norm_num [ abs_of_pos ] );
        refine (Summable.mul_left ( 16 * ( 81 / 100 ) ^ 151 )
          ( show Summable fun j : ℕ => ( j + 1 : ℝ ) ^ 2 * ( 81 / 100 ) ^ j from by
            contrapose! this; erw [ tsum_eq_zero_of_not_summable this ] ; norm_num )).congr ?_
        intro j
        rw [pow_add]
        ring
    · have := h_sum ( 81 / 100 ) ( by norm_num [ abs_of_pos ] );
      refine (Summable.mul_left ( 16 * ( 81 / 100 ) ^ 151 )
        ( show Summable fun j : ℕ => ( j + 1 : ℝ ) ^ 2 * ( 81 / 100 ) ^ j from by
          contrapose! this; erw [ tsum_eq_zero_of_not_summable this ] ; norm_num )).congr ?_
      intro j
      rw [pow_add]
      ring
    · rw [ ← h_sum ] <;> norm_num [ abs_of_pos ];
      rw [ ← tsum_mul_left ] ; exact le_of_eq <| tsum_congr fun n => by
        rw [pow_add]
        ring
  grind

-- Final theorem
theorem tail_omega_sum' :
    ∑' k, (if 25 ≤ k then gSeq' k * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) < 0.0200001 := by
  calc ∑' k, (if 25 ≤ k then gSeq' k * (Y_val' k) ^ (-(1 : ℝ)/3) else 0)
      ≤ ∑' k, (if 25 ≤ k then (Y_val' k) ^ (-(1 : ℝ)/3) else 0) +
        ∑' k, (if 151 ≤ k then (gSeq' k - 1) * (Y_val' k) ^ (-(1 : ℝ)/3) else 0) := tail_split
    _ < 0.02 + 1/10^8 := add_lt_add geom_series_bound' tail_excess_bound
    _ < 0.0200001 := by norm_num

/-
∑_{k≥25} g_k · Y_k^{-1/3} < 0.0200001
-/
theorem tail_omega_sum :
    ∑' k, (if 25 ≤ k then gSeq k * (Y_val lam0 k) ^ (-(1 : ℝ)/3) else 0) < 0.0200001 := by
  have : ∀ k, gSeq k = gSeq' k := fun k => by simp [gSeq, gSeq']
  have : ∀ k, Y_val lam0 k = Y_val' k := fun k => by simp [Y_val, Y_val', lam0, lam0']
  simp_rw [this, ‹∀ k, gSeq k = gSeq' k›]
  exact tail_omega_sum'

/-! ## Numerical certificate -/

lemma lam0_gt_one : (1 : ℝ) < lam0 := by norm_num [lam0]

lemma gSeq_ge_one (k : ℕ) : 1 ≤ gSeq k := by
  unfold gSeq
  split_ifs with h
  · exact le_refl 1
  · push Not at h
    have : (k : ℝ) ≥ 151 := by exact_mod_cast h
    nlinarith

set_option maxRecDepth 1000 in
-- The growth proof for `gSeq` expands nested generated arithmetic comparisons.
lemma gSeq_tendsto : Filter.Tendsto gSeq Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  use max 151 (⌈Real.sqrt (max b 0)⌉₊ + 150)
  intro k hk
  unfold gSeq
  split_ifs with h
  · have : k ≥ 151 := le_of_max_le_left hk
    omega
  · push Not at h
    have hk1 : (k : ℝ) ≥ ⌈Real.sqrt (max b 0)⌉₊ + 150 := by
      exact_mod_cast le_of_max_le_right hk
    have hk2 : (k : ℝ) - 149 ≥ Real.sqrt (max b 0) := by
      have := Nat.le_ceil (Real.sqrt (max b 0))
      linarith
    have hk3 : ((k : ℝ) - 149) ^ 2 ≥ max b 0 := by
      calc ((k : ℝ) - 149) ^ 2 ≥ (Real.sqrt (max b 0)) ^ 2 := by
              exact sq_le_sq' (by linarith [Real.sqrt_nonneg (max b 0)]) hk2
            _ = max b 0 := Real.sq_sqrt (le_max_right b 0)
    linarith [le_max_left b 0]

lemma mSeq_le_N (k : ℕ) : mSeq k ≤ N_layer lam0 k := by
  by_cases hk : k ≤ 24
  · simp only [mSeq, if_pos hk]; exact le_rfl
  · exact Nat.le_of_lt (tail_cardinalities k (by omega))

lemma logE_summable : Summable (fun k => Real.log (E_val lam0 k (mSeq k))) := by
  -- For k ≥ 25, we have log(E_val(k, m_k)) ≤ m_k / (Y_k - 1).
  have h_log_bound : ∀ k ≥ 25, Real.log (E_val lam0 k (mSeq k)) ≤ mSeq k / (Y_val lam0 k - 1) := by
    intro k hk
    have h_E_val_bound : E_val lam0 k (mSeq k) ≤ (Y_val lam0 k / (Y_val lam0 k - 1)) ^ (mSeq k) := by
      -- Each term in the product is less than or equal to $Y_k / (Y_k - 1)$.
      have h_term_bound : ∀ p ∈ I_layer lam0 k, (1 - 1 / (p : ℝ))⁻¹ ≤ Y_val lam0 k / (Y_val lam0 k - 1) := by
        intro p hp
        have h_p_ge_Yk : (p : ℝ) ≥ Y_val lam0 k := by
          exact le_trans ( Nat.le_ceil _ ) ( mod_cast Finset.mem_Ico.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 );
        rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_num at *;
        · nlinarith [ inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; linarith [ show p > 0 from Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ] ), show ( p : ℝ ) ≥ 1 by norm_cast; linarith [ show p > 0 from Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ] ];
        · exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2;
        · exact one_lt_mul_of_lt_of_le ( by norm_num ) ( one_le_pow₀ ( by norm_num [ lam0 ] ) );
      refine Finset.sup'_le (f := fun T : Finset ℕ => ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹) ?_ ?_;
      intro b hb;
      refine le_trans ( Finset.prod_le_prod ?_ fun x hx => h_term_bound x <| Finset.mem_powerset.mp ( Finset.mem_filter.mp hb |>.1 ) hx ) ?_ <;> norm_num;
      · exact fun i a => Nat.cast_inv_le_one i;
      · rw [ div_pow ];
        rw [ ← div_pow, ← div_pow ];
        exact pow_le_pow_right₀ ( by rw [ le_div_iff₀ ] <;> linarith [ show ( Y_val lam0 k : ℝ ) ≥ 2 by exact le_trans ( by norm_num [ Y_val, lam0 ] ) ( mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_num [ lam0 ] ) ( show k ≥ 1 by linarith ) ) zero_le_two ) ] ) ( Finset.mem_filter.mp hb |>.2 );
    refine le_trans ( Real.log_le_log ( ?_ ) h_E_val_bound ) ?_;
    · exact lt_of_lt_of_le zero_lt_one (E_val_ge_one _ _ _)
    · rw [ Real.log_pow ];
      refine mul_le_mul_of_nonneg_left ?_ ( Nat.cast_nonneg _ );
      refine le_trans ( Real.log_le_sub_one_of_pos ( div_pos ?_ ?_ ) ) ?_ <;> norm_num [ Y_val ];
      · exact pow_pos ( by norm_num [ lam0 ] ) _;
      · exact one_lt_mul_of_lt_of_le ( by norm_num ) ( one_le_pow₀ ( by norm_num [ lam0 ] ) );
      · rw [ inv_eq_one_div, div_add_one, div_le_div_iff_of_pos_right ] <;> nlinarith [ show ( lam0 : ℝ ) ^ k > 1 by exact one_lt_pow₀ ( by norm_num [ lam0 ] ) ( by linarith ) ];
  -- The series ∑_{k ≥ 25} m_k/(Y_k - 1) is summable by the provided solution.
  have h_tail_summable : Summable (fun k => (if 25 ≤ k then (mSeq k : ℝ) / (Y_val lam0 k - 1) else 0)) := by
    exact tail_log_sum.1.summable;
  rw [ ← summable_nat_add_iff 25 ] at *;
  refine .of_nonneg_of_le ( fun n => ?_ ) ( fun n => ?_ ) h_tail_summable;
  · exact Real.log_nonneg (E_val_ge_one _ _ _)
  · grind

lemma gs_summable : Summable (fun k => gSeq k * s_val lam0 k (mSeq k)) := by
  have h_comparison : ∃ C > 0, ∀ k ≥ 25, gSeq k * s_val lam0 k (mSeq k) ≤ C * k^3 * (lam0 ^ (-1 / 3 : ℝ)) ^ k := by
    obtain ⟨C, hC⟩ : ∃ C > 0, ∀ k ≥ 25, s_val lam0 k (mSeq k) ≤ C * k / (lam0 ^ (k / 3 : ℝ)) := by
      have h_comparison : ∃ C > 0, ∀ k ≥ 25, s_val lam0 k (mSeq k) ≤ C * k / (Y_val lam0 k ^ (1 / 3 : ℝ)) := by
        obtain ⟨C, hC⟩ : ∃ C > 0, ∀ k ≥ 25, (N_layer lam0 k : ℝ) / (Y_val lam0 k * M_layer lam0 k) ≤ C * k := by
          use 1.71, by norm_num, fun k hk => le_trans ( tail_comparison k hk |> le_of_lt ) ( by nlinarith [ show ( k : ℝ ) ≥ 25 by norm_cast ] ) ;
        obtain ⟨C', hC'⟩ : ∃ C' > 0, ∀ k ≥ 25, Real.sqrt ((mSeq k : ℝ) + 1) ≥ C' * (Y_val lam0 k) ^ (1 / 3 : ℝ) := by
          have h_sqrt_bound : ∀ k ≥ 25, Real.sqrt ((mSeq k : ℝ) + 1) ≥ Real.sqrt (mu0 * (Y_val lam0 k) ^ (2 / 3 : ℝ)) := by
            intros k hk
            simp [mSeq];
            rw [ if_neg ( by linarith ) ] ; exact Real.sqrt_le_sqrt <| by linarith [ Nat.lt_floor_add_one ( mu0 * Y_val lam0 k ^ ( 2 / 3 : ℝ ) ) ] ;
          refine ⟨ Real.sqrt mu0, ?_, ?_ ⟩ <;> norm_num;
          · exact div_pos ( by norm_num ) ( by norm_num );
          · intro k hk; convert h_sqrt_bound k hk |> le_trans _ using 1; rw [ Real.sqrt_mul <| by exact div_nonneg ( by norm_num ) <| by norm_num ] ; rw [ Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ( by exact mul_nonneg zero_le_two <| pow_nonneg ( by norm_num [ lam0 ] ) _ ) ] ; norm_num;
        refine ⟨ C / C', div_pos hC.1 hC'.1, fun k hk => ?_ ⟩ ; simp_all +decide [ s_val ] ;
        split_ifs <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        · convert mul_le_mul_of_nonneg_right ( hC.2 k hk ) ( inv_nonneg.2 ( show 0 ≤ Real.sqrt ( mSeq k + 1 ) by positivity ) ) |> le_trans <| mul_le_mul_of_nonneg_left ( inv_anti₀ ( show 0 < C' * Y_val lam0 k ^ ( 3⁻¹ : ℝ ) by exact mul_pos hC'.1 <| Real.rpow_pos_of_pos ( show 0 < Y_val lam0 k by exact mul_pos zero_lt_two <| pow_pos ( show 0 < lam0 by exact by unfold lam0; norm_num ) _ ) _ ) <| hC'.2 k hk ) <| show 0 ≤ C * k by exact mul_nonneg hC.1.le <| Nat.cast_nonneg _ using 1
          · rfl
          · ring
          · rw [mul_inv]
            ring;
        · exact mul_nonneg ( Nat.cast_nonneg _ ) ( inv_nonneg.2 ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ ) );
      obtain ⟨ C, hC₀, hC ⟩ := h_comparison
      refine ⟨ C * 2 ^ ( 1 / 3 : ℝ ), by positivity, fun k hk => ?_ ⟩
      norm_num [ Y_val ] at *
      refine le_trans ( hC k hk ) ?_
      rw [ Real.mul_rpow ( by positivity ) ( by exact pow_nonneg ( by exact le_of_lt ( show 0 < lam0 by exact div_pos ( by norm_num ) ( by norm_num ) ) ) _ ) ] ; ring_nf ; norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( show 0 ≤ lam0 by exact div_nonneg ( by norm_num ) ( by norm_num ) ) ] ;
      exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( by rw [ ← Real.rpow_neg ( by positivity ) ] ; exact Real.rpow_le_rpow_of_exponent_le ( by norm_num ) ( by norm_num ) ) ( by positivity ) ) ( by exact inv_nonneg.2 ( Real.rpow_nonneg ( by exact le_of_lt ( show 0 < lam0 by exact div_pos ( by norm_num ) ( by norm_num ) ) ) _ ) );
    refine ⟨ C, hC.1, fun k hk => ?_ ⟩;
    refine le_trans ( mul_le_mul_of_nonneg_left ( hC.2 k hk ) ( show 0 ≤ gSeq k from ?_ ) ) ?_;
    · exact le_trans ( by norm_num ) ( gSeq_ge_one k );
    · have h_gSeq_bound : gSeq k ≤ k^2 := by
        unfold gSeq; split_ifs <;> norm_num
        focus
          nlinarith
        nlinarith only [ show ( k : ℝ ) ≥ 151 by norm_cast; linarith ];
      convert mul_le_mul_of_nonneg_right h_gSeq_bound ( show 0 ≤ C * ( k : ℝ ) / lam0 ^ ( k / 3 : ℝ ) by exact div_nonneg ( mul_nonneg hC.1.le ( Nat.cast_nonneg _ ) ) ( Real.rpow_nonneg ( by norm_num [ lam0 ] ) _ ) ) using 1 ; ring_nf;
      norm_num [ Real.rpow_neg ( by norm_num [ lam0 ] : 0 ≤ lam0 ), Real.rpow_mul ( by norm_num [ lam0 ] : 0 ≤ lam0 ) ];
      exact Or.inl ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by norm_num [ lam0 ] ), mul_comm, Real.rpow_mul ( by norm_num [ lam0 ] ), Real.rpow_natCast ] );
  -- The series ∑_{k=25}^∞ k^3 ρ^k converges for |ρ| < 1.
  have h_series_conv : ∀ ρ : ℝ, |ρ| < 1 → Summable (fun k : ℕ => (k : ℝ) ^ 3 * ρ ^ k) := by
    intro ρ hρ;
    refine summable_of_ratio_norm_eventually_le (r := (( 1 + |ρ| ) / 2)) ?_ ?_;
    · linarith;
    · have h_eventually : ∃ N, ∀ n ≥ N, |ρ| * (n + 1 : ℝ) ^ 3 ≤ (1 + |ρ|) / 2 * n ^ 3 := by
        use 8 / (1 - |ρ|);
        intro n hn;
        rw [ ge_iff_le, div_le_iff₀ ] at hn <;> nlinarith [ abs_nonneg ρ, pow_two_nonneg ( n - 2 ), pow_two_nonneg ( n - 1 ), pow_two_nonneg n, abs_mul_abs_self ρ ];
      simp +zetaDelta at *;
      obtain ⟨ N, hN ⟩ := h_eventually; exact ⟨ ⌈N⌉₊, fun n hn => by rw [ abs_of_nonneg ( by positivity ) ] ; have := hN n ( Nat.le_of_ceil_le hn ) ; ring_nf at this ⊢; nlinarith [ pow_nonneg ( abs_nonneg ρ ) n ] ⟩ ;
  obtain ⟨ C, hC₀, hC ⟩ := h_comparison;
  rw [ ← summable_nat_add_iff 25 ];
  refine Summable.of_nonneg_of_le ( fun n => ?_ ) ( fun n => hC (n + 25) ( by linarith ) ) ?_;
  · refine mul_nonneg ?_ ?_ <;> norm_num [ gSeq, s_val ];
    · split_ifs <;> positivity;
    · split_ifs <;> norm_num;
      refine div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( mul_nonneg ?_ ?_ ) ( Real.sqrt_nonneg _ ) );
      · exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ );
      · exact Finset.prod_nonneg fun p hp => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2;
  · have hrho : |lam0 ^ ( -1 / 3 : ℝ )| < 1 := by
      rw [ abs_of_pos ( by exact Real.rpow_pos_of_pos ( by exact div_pos ( by norm_num ) ( by norm_num ) ) _ ),
        Real.rpow_lt_one_iff_of_pos ] <;> norm_num [ lam0 ]
    exact ((h_series_conv ( lam0 ^ ( -1 / 3 : ℝ ) ) hrho).comp_injective
      ( add_left_injective 25 )).mul_left C |>.congr fun n => by
        dsimp
        rw [pow_add]
        ring

/-
log D < 3.476
-/
set_option maxHeartbeats 1600000 in
-- The log-D estimate combines finite generated arithmetic with a tail comparison.
theorem logD_bound :
    ∑' k, Real.log (E_val lam0 k (mSeq k)) < 3.456 := by
  -- Split the tsum into finite (k < 25) and tail (k ≥ 25).
  have h_split : ∑' k, Real.log (E_val lam0 k (mSeq k)) = ∑ k ∈ Finset.range 25, Real.log (E_val lam0 k (mSeq k)) + ∑' k, Real.log (E_val lam0 (k + 25) (mSeq (k + 25))) := by
    exact (Summable.sum_add_tsum_nat_add 25 logE_summable).symm;
  -- For k ≥ 25, log(E_val(k, mSeq(k))) ≤ mSeq(k)/(Y_k - 1).
  have h_tail_bound : ∀ k ≥ 25, Real.log (E_val lam0 k (mSeq k)) ≤ (mSeq k : ℝ) / (Y_val lam0 k - 1) := by
    intro k hk
    have h_log_E_val : Real.log (E_val lam0 k (mSeq k)) ≤ mSeq k * Real.log (1 / (1 - 1 / (Y_val lam0 k))) := by
      have h_E_val_bound : ∀ T ⊆ I_layer lam0 k, T.card ≤ mSeq k → ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹ ≤ (1 / (1 - 1 / (Y_val lam0 k))) ^ T.card := by
        intros T hT_sub hT_card
        have h_prod_bound : ∀ p ∈ T, (1 - 1 / (p : ℝ))⁻¹ ≤ (1 / (1 - 1 / (Y_val lam0 k))) := by
          intros p hp
          have h_p_ge_Yk : (p : ℝ) ≥ Y_val lam0 k := by
            exact le_trans ( Nat.le_ceil _ ) ( mod_cast Finset.mem_Ico.mp ( Finset.mem_filter.mp ( hT_sub hp ) |>.1 ) |>.1 );
          rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_num at *;
          · linarith [ inv_anti₀ ( show 0 < Y_val lam0 k from mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ) h_p_ge_Yk ];
          · exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt <| by have := hT_sub hp; exact Finset.mem_filter.mp this |>.2;
          · exact inv_lt_one_of_one_lt₀ ( by exact lt_of_lt_of_le ( by norm_num [ Y_val, lam0 ] ) ( mul_le_mul_of_nonneg_left ( pow_le_pow_right₀ ( by norm_num [ lam0 ] ) hk ) zero_le_two ) );
        calc
          ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹
              ≤ ∏ _p ∈ T, (1 / (1 - 1 / (Y_val lam0 k))) := by
            refine Finset.prod_le_prod ?_ h_prod_bound
            intro p hp
            exact inv_nonneg.2 <| sub_nonneg.2 <|
              div_le_self zero_le_one <| mod_cast Nat.Prime.pos <|
                Finset.mem_filter.mp (hT_sub hp) |>.2
          _ = (1 / (1 - 1 / (Y_val lam0 k))) ^ T.card := by
            rw [Finset.prod_const]
      have h_E_val_bound : E_val lam0 k (mSeq k) ≤ (1 / (1 - 1 / (Y_val lam0 k))) ^ mSeq k := by
        refine Finset.sup'_le (f := fun T : Finset ℕ => ∏ p ∈ T, (1 - 1 / (p : ℝ))⁻¹) ?_ ?_;
        simp +zetaDelta at *;
        exact fun T hT₁ hT₂ => le_trans ( h_E_val_bound T hT₁ hT₂ ) ( inv_anti₀ ( pow_pos ( sub_pos.mpr <| inv_lt_one_of_one_lt₀ <| by exact one_lt_mul_of_lt_of_le one_lt_two <| one_le_pow₀ <| by norm_num [ lam0 ] ) _ ) <| pow_le_pow_of_le_one ( sub_nonneg.mpr <| inv_le_one_of_one_le₀ <| by exact one_le_mul_of_one_le_of_one_le one_le_two <| one_le_pow₀ <| by norm_num [ lam0 ] ) ( sub_le_self _ <| inv_nonneg.mpr <| by exact mul_nonneg zero_le_two <| pow_nonneg ( by norm_num [ lam0 ] ) _ ) hT₂ );
      convert Real.log_le_log ( show 0 < E_val lam0 k ( mSeq k ) from ?_ ) h_E_val_bound using 1
      focus
        norm_num [ Real.log_pow ]
      exact lt_of_lt_of_le zero_lt_one ( E_val_ge_one _ _ _ );
    have h_log_ineq : Real.log (1 / (1 - 1 / (Y_val lam0 k))) ≤ 1 / (Y_val lam0 k - 1) := by
      have h_log_ineq : ∀ x : ℝ, 0 < x ∧ x < 1 → Real.log (1 / (1 - x)) ≤ x / (1 - x) := by
        norm_num +zetaDelta at *;
        exact fun x hx₁ hx₂ => by rw [ le_div_iff₀ ] <;> nlinarith [ Real.log_inv ( 1 - x ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - x ) ), mul_inv_cancel₀ ( by linarith : ( 1 - x ) ≠ 0 ) ] ;
      convert h_log_ineq ( 1 / Y_val lam0 k ) ⟨ one_div_pos.mpr ( show 0 < Y_val lam0 k from by exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ), by rw [ div_lt_iff₀ ] <;> linarith [ show Y_val lam0 k > 1 from by exact one_lt_mul_of_lt_of_le one_lt_two ( one_le_pow₀ ( by norm_num [ lam0 ] ) ) ] ⟩ using 1 ; ring_nf;
      rw [ ← mul_inv, mul_sub, mul_one, mul_inv_cancel₀ ( ne_of_gt ( show 0 < Y_val lam0 k from by exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ) ) ] ; ring;
    simpa only [ mul_one_div ] using h_log_E_val.trans ( mul_le_mul_of_nonneg_left h_log_ineq <| Nat.cast_nonneg _ );
  -- The tail sum is bounded.
  have h_tail_sum_bound : ∑' k, Real.log (E_val lam0 (k + 25) (mSeq (k + 25))) ≤ ∑' k, (mSeq (k + 25) : ℝ) / (Y_val lam0 (k + 25) - 1) := by
    refine Summable.tsum_le_tsum
      (g := fun k => (mSeq (k + 25) : ℝ) / (Y_val lam0 (k + 25) - 1)) ?_ ?_ ?_;
    · exact fun k => h_tail_bound _ le_add_self;
    · have := logE_summable;
      exact this.comp_injective ( add_left_injective 25 );
    · have := tail_log_sum.1;
      exact (this.summable.comp_injective ( add_left_injective 25 )).congr fun k => by
        simp
  have h_tail_sum_bound : ∑' k, (mSeq (k + 25) : ℝ) / (Y_val lam0 (k + 25) - 1) < 0.026 := by
    have := tail_log_sum;
    have hshift :
        (∑' k, (mSeq (k + 25) : ℝ) / (Y_val lam0 (k + 25) - 1)) =
          ∑' k, (if 25 ≤ k then (mSeq k : ℝ) / (Y_val lam0 k - 1) else 0) := by
      have hzero :
          (∑ k ∈ Finset.range 25,
            (if 25 ≤ k then (mSeq k : ℝ) / (Y_val lam0 k - 1) else 0)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        simp [not_le_of_gt (Finset.mem_range.mp hk)]
      have hsplit := Summable.sum_add_tsum_nat_add 25 this.1.summable
      have htail :
          (∑' k, (if 25 ≤ k + 25 then
              (mSeq (k + 25) : ℝ) / (Y_val lam0 (k + 25) - 1) else 0)) =
            ∑' k, (if 25 ≤ k then (mSeq k : ℝ) / (Y_val lam0 k - 1) else 0) := by
        rw [← hsplit, hzero, zero_add]
      calc
        (∑' k, (mSeq (k + 25) : ℝ) / (Y_val lam0 (k + 25) - 1))
            = ∑' k, (if 25 ≤ k + 25 then
                (mSeq (k + 25) : ℝ) / (Y_val lam0 (k + 25) - 1) else 0) := by
              exact tsum_congr fun k => by simp
        _ = ∑' k, (if 25 ≤ k then (mSeq k : ℝ) / (Y_val lam0 k - 1) else 0) := htail
    exact hshift.trans_lt this.2
  have h_finite_sum_bound : ∑ k ∈ Finset.range 25, Real.log (E_val lam0 k (mSeq k)) < 3.43 := by
    simpa [ell_val] using finite_log_sum
  grind

/-
Ω < 0.024
-/
set_option maxHeartbeats 800000 in
-- The omega estimate combines finite generated arithmetic with a summability tail.
theorem omega_bound : Omega_val lam0 mSeq gSeq < 0.029 := by
  -- We'll use the fact that s_val(k, mSeq(k)) ≤ 1.71 / √μ₀ · gSeq(k) · Y_k^{-1/3} for k ≥ 25.
  have h_bound : ∀ k ≥ 25, gSeq k * s_val lam0 k (mSeq k) ≤ 1.71 / Real.sqrt (29607 / 20000) * gSeq k * (Y_val lam0 k) ^ (-(1 : ℝ) / 3) := by
    intro k hk
    have h_s_val_bound : s_val lam0 k (mSeq k) ≤ (1.71 / Real.sqrt (29607 / 20000)) * (Y_val lam0 k) ^ (-(1 : ℝ) / 3) := by
      have h_s_val_bound : s_val lam0 k (mSeq k) = (N_layer lam0 k : ℝ) / (Y_val lam0 k * M_layer lam0 k * Real.sqrt ((mSeq k : ℝ) + 1)) := by
        exact if_pos ( tail_cardinalities k hk );
      have h_s_val_bound : (N_layer lam0 k : ℝ) / (Y_val lam0 k * M_layer lam0 k) < 1.71 := by
        apply tail_comparison k hk;
      have h_s_val_bound : (mSeq k : ℝ) ≥ (29607 / 20000) * (Y_val lam0 k) ^ (2 / 3 : ℝ) - 1 := by
        unfold mSeq; norm_num [ hk ] ;
        split_ifs <;> norm_num [ mu0 ] at *;
        · linarith;
        · exact le_of_lt <| Nat.lt_floor_add_one _;
      have h_s_val_bound : Real.sqrt ((mSeq k : ℝ) + 1) ≥ Real.sqrt (29607 / 20000) * (Y_val lam0 k) ^ (1 / 3 : ℝ) := by
        refine Real.le_sqrt_of_sq_le ?_;
        rw [ mul_pow, Real.sq_sqrt <| by positivity, ← Real.rpow_natCast, ← Real.rpow_mul ( by exact mul_nonneg zero_le_two <| pow_nonneg ( by norm_num [ lam0 ] ) _ ) ] ; norm_num ; linarith;
      have h_s_val_bound : (N_layer lam0 k : ℝ) / (Y_val lam0 k * M_layer lam0 k * Real.sqrt ((mSeq k : ℝ) + 1)) ≤ (1.71 : ℝ) / (Real.sqrt (29607 / 20000) * (Y_val lam0 k) ^ (1 / 3 : ℝ)) := by
        rw [ ← div_div ];
        gcongr;
        exact mul_pos ( Real.sqrt_pos.mpr ( by norm_num ) ) ( Real.rpow_pos_of_pos ( by exact mul_pos zero_lt_two ( pow_pos ( by norm_num [ lam0 ] ) _ ) ) _ );
      convert h_s_val_bound using 1 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.rpow_neg ];
      rw [ Real.rpow_neg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) ];
    have hg_nonneg : 0 ≤ gSeq k := by
      exact le_trans zero_le_one (gSeq_ge_one k)
    calc
      gSeq k * s_val lam0 k (mSeq k)
          ≤ gSeq k *
              ((1.71 / Real.sqrt (29607 / 20000)) *
                (Y_val lam0 k) ^ (-(1 : ℝ) / 3)) :=
            mul_le_mul_of_nonneg_left h_s_val_bound hg_nonneg
      _ = 1.71 / Real.sqrt (29607 / 20000) * gSeq k *
            (Y_val lam0 k) ^ (-(1 : ℝ) / 3) := by
          ring
  -- Summing the inequalities from h_bound over all k ≥ 25.
  have h_sum_bound : ∑' k, (if k ≥ 25 then gSeq k * s_val lam0 k (mSeq k) else 0) ≤ 1.71 / Real.sqrt (29607 / 20000) * ∑' k, (if k ≥ 25 then gSeq k * (Y_val lam0 k) ^ (-(1 : ℝ) / 3) else 0) := by
    rw [ ← tsum_mul_left ];
    refine Summable.tsum_le_tsum ?_ ?_ ?_;
    · intro k; split_ifs <;> simp_all +decide [ mul_assoc ] ;
    · convert gs_summable using 1;
      ext k; by_cases hk : 25 ≤ k <;> simp +decide [ hk ] ;
      exact Or.inr ( s_val_mSeq_zero k ( by linarith ) );
    · refine Summable.mul_left (1.71 / Real.sqrt (29607 / 20000)) ?_;
      refine Summable.of_nonneg_of_le ( fun k => ?_ ) ( fun k => ?_ ) ( show Summable fun k : ℕ => ( k : ℝ ) ^ 2 * ( Y_val lam0 k ) ^ ( - ( 1 : ℝ ) / 3 ) from ?_ );
      · split_ifs <;> first | positivity | exact mul_nonneg ( by unfold gSeq; split_ifs <;> positivity ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by exact div_nonneg ( by norm_num ) ( by norm_num ) ) _ ) ) _ ) ;
      · split_ifs <;> norm_num [ gSeq ];
        · split_ifs;
          · exact le_mul_of_one_le_left ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ ) ( by norm_cast; nlinarith );
          · exact mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by linarith [ show ( k : ℝ ) ≥ 151 by norm_cast; linarith ] ) ( by linarith [ show ( k : ℝ ) ≥ 151 by norm_cast; linarith ] ) _ ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ );
        · exact mul_nonneg ( sq_nonneg _ ) ( Real.rpow_nonneg ( by exact mul_nonneg zero_le_two ( pow_nonneg ( by norm_num [ lam0 ] ) _ ) ) _ );
      · have h_summable : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (lam0 ^ k) ^ (-(1 : ℝ) / 3)) := by
          have h_summable : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (lam0 ^ (-(1 : ℝ) / 3)) ^ k) := by
            have h_summable : ∀ r : ℝ, 0 < r ∧ r < 1 → Summable (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) := by
              intro r hr;
              refine summable_of_ratio_norm_eventually_le (r := (( 1 + r ) / 2)) ?_ ?_;
              · linarith;
              · have h_eventually : ∃ N, ∀ n ≥ N, (n + 1 : ℝ) ^ 2 * r ≤ (1 + r) / 2 * n ^ 2 := by
                  exact ⟨ 2 * ( 1 + r ) / ( 1 - r ), fun n hn => by nlinarith [ mul_div_cancel₀ ( 2 * ( 1 + r ) ) ( by linarith : ( 1 - r ) ≠ 0 ), sq_nonneg ( n - 2 * ( 1 + r ) / ( 1 - r ) ) ] ⟩;
                norm_num +zetaDelta at *;
                obtain ⟨ N, hN ⟩ := h_eventually; exact ⟨ ⌈N⌉₊, fun n hn => by
                  rw [ abs_of_pos hr.1 ]
                  convert mul_le_mul_of_nonneg_right ( hN n ( Nat.le_of_ceil_le hn ) ) ( pow_nonneg hr.1.le n ) using 1
                  · rfl
                  · rw [pow_succ]
                    ring
                  · ring ⟩ ;
            exact h_summable _ ⟨ by exact Real.rpow_pos_of_pos ( by norm_num [ lam0 ] ) _, by exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( by norm_num [ lam0 ] ) ( show ( -1 / 3 : ℝ ) < 0 by norm_num ) ) ( by norm_num [ lam0 ] ) ⟩;
          convert h_summable using 2 ; norm_num [ Real.rpow_neg, Real.rpow_mul ];
          exact Or.inl ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by exact div_nonneg ( by norm_num ) ( by norm_num ) ), mul_comm, Real.rpow_mul ( by exact div_nonneg ( by norm_num ) ( by norm_num ) ), Real.rpow_natCast ] );
        refine (h_summable.mul_left ( 2 ^ ( -1 / 3 : ℝ ) )).congr ?_
        intro k
        simp only [Y_val]
        rw [ Real.mul_rpow
          ( by norm_num )
          ( by exact pow_nonneg ( by norm_num [lam0] ) _ ) ]
        ring
  -- Since the sum of the terms for k ≤ 24 is zero, we can simplify the expression for Omega_val.
  have h_Omega_val_simplified : Omega_val lam0 mSeq gSeq = ∑' k, (if k ≥ 25 then gSeq k * s_val lam0 k (mSeq k) else 0) := by
    exact tsum_congr fun k => if hk : k < 25 then by rw [ s_val_mSeq_zero k ( Nat.le_of_lt_succ hk ) ] ; norm_num [ hk ] else by aesop;
  refine h_Omega_val_simplified ▸ h_sum_bound.trans_lt ?_;
  refine lt_of_lt_of_le ( mul_lt_mul_of_pos_left ( tail_omega_sum ) ( by positivity ) ) ?_ ; norm_num;
  rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 29607, Real.sqrt_nonneg 20000, Real.sq_sqrt ( show 0 ≤ 29607 by norm_num ), Real.sq_sqrt ( show 0 ≤ 20000 by norm_num ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 29607 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 20000 by norm_num ) ), mul_div_cancel₀ ( Real.sqrt 29607 ) ( ne_of_gt ( Real.sqrt_pos.mpr ( show 0 < 20000 by norm_num ) ) ) ]

/-- The triple (λ₀, m, g) is admissible -/
theorem admissible_triple_certificate : AdmissibleTriple lam0 mSeq gSeq :=
  ⟨lam0_gt_one, mSeq_le_N, logE_summable, gs_summable,
   by linarith [omega_bound], gSeq_ge_one, gSeq_tendsto⟩ -- Ω < 0.029 < 1

/-
exp(1) < 27183/10000
-/
lemma exp_one_lt : Real.exp 1 < 27183/10000 := by
  exact Real.exp_one_lt_d9.trans_le <| by norm_num;

/-
exp(7/200) < 103563/100000
-/
lemma exp_small_lt : Real.exp (7/200 : ℝ) < 103563/100000 := by
  rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
  rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
  have := Real.exp_one_lt_d9.le ; norm_num1 at * ; rw [ show Real.exp 7 = ( Real.exp 1 ) ^ 7 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num )

lemma exp_4035_bound : Real.exp (4035/1000 : ℝ) < 5657/100 := by
  have h1 := exp_one_lt
  have h2 := exp_small_lt
  have h3 : Real.exp (4035/1000 : ℝ) = Real.exp 1 ^ 4 * Real.exp (7/200 : ℝ) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [h3]
  calc Real.exp 1 ^ 4 * Real.exp (7/200 : ℝ)
      < (27183/10000 : ℝ)^4 * (103563/100000 : ℝ) := by
        apply mul_lt_mul
        · exact pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
        · exact h2.le
        · exact Real.exp_pos _
        · positivity
    _ < 5657/100 := by norm_num

-- Final numerical inequality
lemma numerical_ineq : (5657 : ℝ)/100 / (971/1000 : ℝ)^2 < 60 := by
  norm_num

/-
e^γ · D / (1-Ω)² < 60
-/
theorem numerical_certificate :
    Real.exp γ * D_val lam0 mSeq / (1 - Omega_val lam0 mSeq gSeq) ^ 2 < 60 := by
  -- Step 1: exp(γ) * D = exp(γ + logD) < exp(4.035)
  have hγ := gamma_lt_tight
  have hD := logD_bound
  have hΩ := omega_bound
  -- D_val = exp(∑ log E_k)
  have hD_eq : D_val lam0 mSeq = Real.exp (∑' k, Real.log (E_val lam0 k (mSeq k))) := rfl
  -- exp(γ) * D = exp(γ + ∑ log E_k)
  have h_prod : Real.exp γ * D_val lam0 mSeq = Real.exp (γ + ∑' k, Real.log (E_val lam0 k (mSeq k))) := by
    rw [hD_eq, ← Real.exp_add]
  rw [h_prod]
  -- exp(γ + logD) < exp(4.035)
  have h_exp_bound : Real.exp (γ + ∑' k, Real.log (E_val lam0 k (mSeq k))) < Real.exp (4035/1000 : ℝ) := by
    exact Real.exp_strictMono (by linarith)
  -- (1 - Ω)^2 > (1 - 0.029)^2 = 0.971^2
  have h_denom : (971/1000 : ℝ)^2 ≤ (1 - Omega_val lam0 mSeq gSeq)^2 := by
    apply sq_le_sq'
    · linarith
    · linarith
  have h_denom_pos : (0 : ℝ) < (1 - Omega_val lam0 mSeq gSeq)^2 := by
    apply sq_pos_of_pos; linarith
  calc Real.exp (γ + ∑' k, Real.log (E_val lam0 k (mSeq k))) / (1 - Omega_val lam0 mSeq gSeq) ^ 2
      < Real.exp (4035/1000 : ℝ) / (1 - Omega_val lam0 mSeq gSeq) ^ 2 := by
        exact div_lt_div_of_pos_right h_exp_bound h_denom_pos
    _ ≤ Real.exp (4035/1000 : ℝ) / (971/1000 : ℝ)^2 := by
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) h_denom
    _ < (5657/100 : ℝ) / (971/1000 : ℝ)^2 := by
        apply div_lt_div_of_pos_right exp_4035_bound (by positivity)
    _ < 60 := numerical_ineq

/-- If n is large enough, then every n-admissible pair satisfies
    |A|·|B| < 60 · n²/log n. -/
theorem main_theorem :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ,
        A ⊆ Finset.Icc 1 n → B ⊆ Finset.Icc 1 n →
        (∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
          a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂) →
        A.card * B.card < 60 * n ^ 2 / Real.log n := by
  have hcert := numerical_certificate
  have hadm := admissible_triple_certificate
  obtain ⟨N₀, hN₀⟩ := layer_weighted_bound lam0 mSeq gSeq hadm 60 hcert
  exact ⟨N₀, fun n hn A B hA hB hinj => hN₀ n hn A B ⟨hA, hB, hinj⟩⟩

#print axioms main_theorem

end Erdos490
