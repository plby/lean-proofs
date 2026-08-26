/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 464.
Informal author: Bernard de Mathan.
Formal authors: Aristotle, JoshuaB.
Source: https://www.erdosproblems.com/forum/thread/464#post-7120
https://aristotle.harmonic.fun/dashboard/requests/f9894d2d-4bb1-42da-9301-e508aa881b17
Original Lean version: 4.28.0, confirmed by the user who supplied the source files.
The original Mathlib revision and a license notice were not supplied.
-/
import Mathlib
import ErdosProblems.Erdos464.NDist
import ErdosProblems.Erdos464.Uncountable

set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos464

/-!
# de Mathan's nested-interval construction

Given a positive real sequence `Q` with ratios in `[λ₀, μ₀]` (`1 < λ₀ ≤ μ₀`), we construct, via a
binary Cantor scheme of nested intervals, an uncountable set of reals `θ` such that
`‖Q m · θ‖ ≥ ε` for all `m ≥ 1`, where `ε` is a fixed positive constant.

The data is bundled in `Setup`.
-/

/-- The data for de Mathan's construction. -/
structure Setup where
  Q : ℕ → ℝ
  lam : ℝ
  mu : ℝ
  n0 : ℕ
  eps : ℝ
  hlam : 1 < lam
  hlammu : lam ≤ mu
  hn0 : 1 ≤ n0
  hn0big : (2 * (n0 : ℝ) + 4) ≤ lam ^ n0
  hQpos : ∀ n, 0 < Q n
  hlo : ∀ n, lam * Q n ≤ Q (n + 1)
  hhi : ∀ n, Q (n + 1) ≤ mu * Q n
  heps : eps = 1 / (4 * mu ^ (2 * n0 - 1))

namespace Setup

variable (S : Setup)

/-- The scale at depth `s`: `Q ((s+1) * n0)`. -/
noncomputable def scale (s : ℕ) : ℝ := S.Q ((s + 1) * S.n0)

/-- The full unit interval at depth `s` defined by integer `K`. -/
noncomputable def Jfull (s : ℕ) (K : ℤ) : Set ℝ :=
  Set.Icc ((K : ℝ) / S.scale s) (((K : ℝ) + 1) / S.scale s)

/-- The `eps`-shrunk interval at depth `s` defined by integer `K`. -/
noncomputable def Jshr (s : ℕ) (K : ℤ) : Set ℝ :=
  Set.Icc (((K : ℝ) + S.eps) / S.scale s) (((K : ℝ) + 1 - S.eps) / S.scale s)

/-- The constraint set: `θ` with `‖Q m · θ‖ ≥ eps` for all `1 ≤ m ≤ N`. -/
def Gset (N : ℕ) : Set ℝ := {θ : ℝ | ∀ m, 1 ≤ m → m ≤ N → S.eps ≤ ndist (S.Q m * θ)}

/-- The induction invariant at depth `s` for the chosen integer `K`. -/
def Inv (s : ℕ) (K : ℤ) : Prop := S.Jfull s K ⊆ S.Gset (s * S.n0)

/-! ## Basic facts about the constants -/

lemma mu_pos : 0 < S.mu := lt_trans (by norm_num) (lt_of_lt_of_le S.hlam S.hlammu)

lemma lam_pos : 0 < S.lam := lt_trans (by norm_num) S.hlam

lemma eps_pos : 0 < S.eps := by
  exact S.heps.symm ▸ one_div_pos.mpr ( mul_pos zero_lt_four ( pow_pos ( by linarith [ S.hlam, S.hlammu ] ) _ ) )

lemma eps_le_half : S.eps ≤ 1 / 2 := by
  rw [ S.heps, div_le_div_iff₀ ] <;> norm_num;
  · exact le_trans ( by norm_num ) ( mul_le_mul_of_nonneg_left ( one_le_pow₀ ( show 1 ≤ S.mu by linarith [ S.hlam, S.hlammu ] ) ) zero_le_four );
  · exact pow_pos ( by linarith [ S.hlam, S.hlammu ] ) _

lemma scale_pos (s : ℕ) : 0 < S.scale s := S.hQpos _

/-
`Q` is monotone.
-/
lemma Q_le_Q {i j : ℕ} (hij : i ≤ j) : S.Q i ≤ S.Q j := by
  exact monotone_nat_of_le_succ ( fun n => by nlinarith [ S.hlam, S.hlo n, S.hhi n, S.hQpos n ] ) hij

/-
`Q` is strictly monotone.
-/
lemma Q_lt_Q {i j : ℕ} (hij : i < j) : S.Q i < S.Q j := by
  induction' hij with k hk;
  · exact lt_of_lt_of_le ( lt_mul_of_one_lt_left ( S.hQpos _ ) S.hlam ) ( S.hlo _ );
  · exact lt_of_lt_of_le ‹_› ( S.Q_le_Q ( Nat.le_succ _ ) )

/-
Lower geometric bound on ratios of `Q`.
-/
lemma Q_ratio_ge {i j : ℕ} (hij : i ≤ j) : S.lam ^ (j - i) * S.Q i ≤ S.Q j := by
  induction' j using Nat.strong_induction_on with j ih;
  rcases hij with ( _ | hij );
  · norm_num;
  · rw [ Nat.succ_sub hij, pow_succ' ];
    simpa only [ mul_assoc ] using le_trans ( mul_le_mul_of_nonneg_left ( ih _ ( Nat.lt_succ_self _ ) hij ) ( by linarith [ S.hlam ] ) ) ( S.hlo _ )

/-
Upper geometric bound on ratios of `Q`.
-/
lemma Q_ratio_le {i j : ℕ} (hij : i ≤ j) : S.Q j ≤ S.mu ^ (j - i) * S.Q i := by
  induction' hij with j hj ih <;> simp_all +decide [ Nat.succ_sub, pow_succ' ];
  simpa only [ mul_assoc ] using le_trans ( S.hhi j ) ( mul_le_mul_of_nonneg_left ih ( by linarith [ S.hlam, S.hlammu ] ) )

/-
`Q` tends to infinity.
-/
lemma Q_tendsto_atTop : Filter.Tendsto S.Q Filter.atTop Filter.atTop := by
  have hQ_lower_bound : ∀ n, S.Q n ≥ S.Q 0 * S.lam ^ n := by
    intro n; induction' n with n ih <;> norm_num [ pow_succ, mul_assoc ] at * ; nlinarith [ S.hlo n, S.hlam, S.hQpos n, S.hQpos 0 ] ;
  exact Filter.tendsto_atTop_mono hQ_lower_bound ( tendsto_pow_atTop_atTop_of_one_lt S.hlam |> Filter.Tendsto.const_mul_atTop ( S.hQpos 0 ) )

lemma scale_tendsto_atTop : Filter.Tendsto S.scale Filter.atTop Filter.atTop := by
  exact S.Q_tendsto_atTop.comp
    (Filter.tendsto_atTop_mono (f := fun s : ℕ => s)
      (g := fun s => (s + 1) * S.n0) (fun s => by nlinarith [S.hn0])
      Filter.tendsto_id)

/-! ## Interval lemmas -/

lemma Jshr_subset_Jfull (s : ℕ) (K : ℤ) : S.Jshr s K ⊆ S.Jfull s K := by
  apply Set.Icc_subset_Icc;
  · exact div_le_div_of_nonneg_right ( by linarith [ S.eps_pos ] ) ( le_of_lt ( S.scale_pos s ) );
  · exact div_le_div_of_nonneg_right ( sub_le_self _ ( by exact le_of_lt ( S.eps_pos ) ) ) ( by exact le_of_lt ( S.scale_pos s ) )

lemma Jshr_nonempty (s : ℕ) (K : ℤ) : (S.Jshr s K).Nonempty := by
  refine' Set.nonempty_Icc.mpr _;
  rw [ div_le_div_iff_of_pos_right ] <;> linarith [ S.scale_pos s, S.eps_le_half ]

lemma Jshr_isClosed (s : ℕ) (K : ℤ) : IsClosed (S.Jshr s K) := isClosed_Icc

/-
Distinct integers give disjoint shrunk intervals.
-/
lemma Jshr_disjoint (s : ℕ) {K0 K1 : ℤ} (h : K0 ≠ K1) :
    Disjoint (S.Jshr s K0) (S.Jshr s K1) := by
  cases lt_or_gt_of_ne h;
  · refine' Set.disjoint_left.mpr _;
    intro x hx₁ hx₂
    have h_upper : (K0 + 1 - S.eps) / S.scale s < (K1 + S.eps) / S.scale s := by
      gcongr;
      · exact S.scale_pos s;
      · linarith [ show ( K0 : ℝ ) + 1 ≤ K1 by norm_cast, S.eps_pos ];
    linarith [ hx₁.2, hx₂.1 ];
  · refine' Set.disjoint_left.mpr fun x hx0 hx1 => _;
    simp_all +decide [ Setup.Jshr ];
    rw [ div_le_iff₀ ( S.scale_pos s ), le_div_iff₀ ( S.scale_pos s ) ] at *;
    linarith [ show ( K0 : ℝ ) ≥ K1 + 1 by norm_cast, S.eps_pos ]

/-
Membership in a shrunk interval forces the nearest-integer distance bound at the scale index.
-/
lemma ndist_ge_of_mem_Jshr (s : ℕ) (K : ℤ) {θ : ℝ} (hθ : θ ∈ S.Jshr s K) :
    S.eps ≤ ndist (S.Q ((s + 1) * S.n0) * θ) := by
  -- Unfold the definition of `S.Jshr`.
  unfold Setup.Jshr at hθ;
  convert le_ndist_of_mem_Icc ( S.Q ( ( s + 1 ) * S.n0 ) * θ ) S.eps K _ _ _ _ using 1 <;> norm_num at *;
  · exact le_of_lt ( S.eps_pos );
  · exact S.eps_le_half;
  · rw [ div_le_iff₀ ] at hθ <;> nlinarith! [ S.scale_pos s ];
  · rw [ le_div_iff₀ ( S.scale_pos s ) ] at hθ ; linarith!

/-! ## The key combinatorial step -/

/-
A finite set of integers in which every pair differs by at most `1` has at most two elements.
-/
lemma card_le_two_of_close (t : Finset ℤ) (h : ∀ a ∈ t, ∀ b ∈ t, |a - b| ≤ 1) : t.card ≤ 2 := by
  by_contra h_contra;
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ : ∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t, a < b ∧ b < c := by
    obtain ⟨s, hs⟩ : ∃ s : Fin 3 → ℤ, (∀ i, s i ∈ t) ∧ StrictMono s := by
      exact ⟨ fun i => t.orderEmbOfFin rfl ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i => by simp +decide, by simp +decide [ StrictMono ] ⟩;
    exact ⟨ s 0, hs.1 0, s 1, hs.1 1, s 2, hs.1 2, hs.2 ( by decide ), hs.2 ( by decide ) ⟩;
  linarith [ abs_le.mp ( h a ha b hb ), abs_le.mp ( h b hb c hc ), abs_le.mp ( h a ha c hc ) ]

/-
A child whose full interval sits between the parent's shrunk endpoints is contained in the
parent's shrunk interval.
-/
lemma child_subset_of (s : ℕ) (K K' : ℤ)
    (h1 : S.scale (s + 1) * (((K : ℝ) + S.eps) / S.scale s) ≤ (K' : ℝ))
    (h2 : (K' : ℝ) + 1 ≤ S.scale (s + 1) * (((K : ℝ) + 1 - S.eps) / S.scale s)) :
    S.Jfull (s + 1) K' ⊆ S.Jshr s K := by
  exact Set.Icc_subset_Icc ( by rw [ le_div_iff₀ ( S.scale_pos _ ) ] ; linarith ) ( by rw [ div_le_iff₀ ( S.scale_pos _ ) ] ; linarith )

/-
If a child interval lies in the parent's shrunk interval and avoids the bad sets of all
intermediate indices, then it satisfies the invariant at the next depth.
-/
lemma inv_succ_of (s : ℕ) (K K' : ℤ) (h : S.Inv s K)
    (hsub : S.Jfull (s + 1) K' ⊆ S.Jshr s K)
    (hmid : ∀ m, s * S.n0 < m → m < (s + 1) * S.n0 →
      ∀ θ ∈ S.Jfull (s + 1) K', S.eps ≤ ndist (S.Q m * θ)) :
    S.Inv (s + 1) K' := by
  intro θ hθ m hm₁ hm₂;
  by_cases hm₃ : m ≤ s * S.n0;
  · exact h ( show θ ∈ S.Jfull s K from hsub hθ |> fun h => S.Jshr_subset_Jfull s K h ) m hm₁ hm₃;
  · cases eq_or_lt_of_le hm₂ <;> simp_all +decide [ Nat.succ_mul ];
    simpa only [Nat.succ_mul] using S.ndist_ge_of_mem_Jshr s K (hsub hθ)

/-
Two children that both contain a point where the index-`m` constraint fails must have integer
labels differing by at most `1`.
-/
lemma bad_close (s : ℕ) (K : ℤ) (m : ℕ) (hm1 : s * S.n0 < m) (hm2 : m < (s + 1) * S.n0)
    (K1 K2 : ℤ)
    (hs1 : S.Jfull (s + 1) K1 ⊆ S.Jshr s K) (hs2 : S.Jfull (s + 1) K2 ⊆ S.Jshr s K)
    (hb1 : ∃ θ ∈ S.Jfull (s + 1) K1, ndist (S.Q m * θ) < S.eps)
    (hb2 : ∃ θ ∈ S.Jfull (s + 1) K2, ndist (S.Q m * θ) < S.eps) :
    |K1 - K2| ≤ 1 := by
  obtain ⟨ θ1, hθ1, hθ1' ⟩ := hb1
  obtain ⟨ θ2, hθ2, hθ2' ⟩ := hb2
  have hθ1θ2 : |θ1 - θ2| < 2 * S.eps / S.Q m := by
    have hθ1θ2 : |S.Q m * θ1 - S.Q m * θ2| < 2 * S.eps := by
      have hθ1θ2 : |S.Q m * θ1 - round (S.Q m * θ1)| < S.eps ∧ |S.Q m * θ2 - round (S.Q m * θ2)| < S.eps := by
        exact ⟨ hθ1', hθ2' ⟩;
      have hθ1θ2 : round (S.Q m * θ1) = round (S.Q m * θ2) := by
        have h_dist : |S.Q m * θ1 - S.Q m * θ2| < 1 - 2 * S.eps := by
          have hθ1θ2 : |θ1 - θ2| ≤ (1 - 2 * S.eps) / S.scale s := by
            grind +locals;
          have hθ1θ2 : |S.Q m * θ1 - S.Q m * θ2| ≤ S.Q m * (1 - 2 * S.eps) / S.scale s := by
            rw [← mul_sub, abs_mul, abs_of_nonneg (S.hQpos m).le]
            simpa only [mul_div_assoc] using
              mul_le_mul_of_nonneg_left hθ1θ2 (S.hQpos m).le
          generalize_proofs at *; (
          refine lt_of_le_of_lt hθ1θ2 ?_;
          rw [ div_lt_iff₀ ] <;> norm_num [ Setup.scale ] at *;
          · rw [ mul_comm ] ; gcongr;
            · rw [ S.heps ] ; ring_nf ;
              nlinarith [ show ( S.mu⁻¹ : ℝ ) ^ ( S.n0 * 2 - 1 ) ≤ 1 by exact pow_le_one₀ ( by exact inv_nonneg.2 ( by linarith [ S.mu_pos ] ) ) ( inv_le_one_of_one_le₀ ( by linarith [ S.hlam, S.hlammu ] ) ) ];
            · exact S.Q_lt_Q ( by linarith );
          · exact S.hQpos _)
        generalize_proofs at *; (
        exact Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ abs_lt.mp h_dist, abs_lt.mp hθ1θ2.1, abs_lt.mp hθ1θ2.2 ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ abs_lt.mp h_dist, abs_lt.mp hθ1θ2.1, abs_lt.mp hθ1θ2.2 ] ));
      grind;
    rw [ lt_div_iff₀ ( S.hQpos m ) ] ; rw [ ← mul_sub ] at * ; rw [ abs_mul, abs_of_pos ( S.hQpos m ) ] at * ; linarith;
  -- Now use the given bounds on `S.Q` to simplify the expression.
  have h_bound : 2 * S.eps * S.scale (s + 1) / S.Q m ≤ 1 / 2 := by
    have hratio : S.scale (s + 1) / S.Q m ≤ S.mu ^ ((s + 2) * S.n0 - m) := by
      rw [div_le_iff₀ (S.hQpos m)]
      simpa only [scale, Nat.add_assoc] using
        S.Q_ratio_le (show m ≤ (s + 2) * S.n0 by linarith)
    have hpow : S.mu ^ ((s + 2) * S.n0 - m) ≤ S.mu ^ (2 * S.n0 - 1) := by
      exact pow_le_pow_right₀ (by linarith [S.hlam, S.hlammu])
        (by rw [tsub_le_iff_left]; linarith [Nat.sub_add_cancel (by nlinarith : 1 ≤ 2 * S.n0)])
    calc
      2 * S.eps * S.scale (s + 1) / S.Q m =
          (2 * S.eps) * (S.scale (s + 1) / S.Q m) := by ring
      _ ≤ (2 * S.eps) * S.mu ^ (2 * S.n0 - 1) :=
        mul_le_mul_of_nonneg_left (hratio.trans hpow) (mul_nonneg zero_le_two S.eps_pos.le)
      _ = 1 / 2 := by rw [S.heps]; field_simp [ne_of_gt S.mu_pos]; norm_num
  have h_bound : |(K1 : ℝ) - K2| ≤ S.scale (s + 1) * |θ1 - θ2| + 1 := by
    have h_bound : (K1 : ℝ) ≤ S.scale (s + 1) * θ1 ∧ S.scale (s + 1) * θ1 ≤ (K1 : ℝ) + 1 ∧ (K2 : ℝ) ≤ S.scale (s + 1) * θ2 ∧ S.scale (s + 1) * θ2 ≤ (K2 : ℝ) + 1 := by
      exact ⟨ by have := hθ1.1; rw [ div_le_iff₀ ( S.scale_pos _ ) ] at this; linarith, by have := hθ1.2; rw [ le_div_iff₀ ( S.scale_pos _ ) ] at this; linarith, by have := hθ2.1; rw [ div_le_iff₀ ( S.scale_pos _ ) ] at this; linarith, by have := hθ2.2; rw [ le_div_iff₀ ( S.scale_pos _ ) ] at this; linarith ⟩;
    cases abs_cases ( θ1 - θ2 ) <;> cases abs_cases ( ( K1 : ℝ ) - K2 ) <;> nlinarith [ show 0 < S.scale ( s + 1 ) from S.scale_pos _ ];
  exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; ring_nf at *; nlinarith [ abs_nonneg ( θ1 - θ2 ), S.hQpos m, mul_inv_cancel₀ ( ne_of_gt ( S.hQpos m ) ) ] )

/-
The child/parent scale ratio leaves room for at least `2·n0 + 3` unit intervals.
-/
lemma scale_ratio_gap (s : ℕ) :
    (2 * (S.n0 : ℝ) + 3) ≤ S.scale (s + 1) / S.scale s * (1 - 2 * S.eps) := by
  refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show S.scale ( s + 1 ) / S.scale s ≥ S.lam ^ S.n0 from _ ) _ );
  · -- By definition of $S.eps$, we have $S.eps = 1 / (4 * S.mu ^ (2 * S.n0 - 1))$.
    have h_eps : S.eps = 1 / (4 * S.mu ^ (2 * S.n0 - 1)) := by
      exact S.heps;
    rw [ h_eps, mul_sub, mul_one, mul_div ];
    rw [ mul_div, sub_div', le_div_iff₀ ];
    · have h_mu_pow : S.mu ^ (2 * S.n0 - 1) ≥ S.lam ^ S.n0 := by
        exact le_trans ( pow_le_pow_left₀ ( by linarith [ S.hlam ] ) ( show S.lam ≤ S.mu from S.hlammu ) _ ) ( pow_le_pow_right₀ ( by linarith [ S.hlam, S.hlammu ] ) ( Nat.le_sub_one_of_lt ( by linarith [ S.hn0 ] ) ) );
      nlinarith [ S.hn0big, show ( S.lam ^ S.n0 : ℝ ) ≥ 2 * S.n0 + 4 by exact_mod_cast S.hn0big ];
    · exact mul_pos zero_lt_four ( pow_pos ( by linarith [ S.lam_pos, S.mu_pos ] ) _ );
    · exact mul_ne_zero four_ne_zero ( pow_ne_zero _ ( by linarith [ S.hlam, S.hlammu ] ) );
  · rw [ ge_iff_le, le_div_iff₀ ];
    · have hidx : (s + 2) * S.n0 - (s + 1) * S.n0 = S.n0 := by
        rw [show (s + 2) * S.n0 = (s + 1) * S.n0 + S.n0 by ring]
        omega
      simpa only [hidx, scale, Nat.add_assoc] using
        S.Q_ratio_ge (show (s + 1) * S.n0 ≤ (s + 2) * S.n0 by nlinarith)
    · exact S.scale_pos s;
  · linarith [ S.eps_le_half ]

/-- The key step: from a valid parent interval we can find **two** distinct admissible children
whose full intervals are contained in the parent's shrunk interval and satisfy the invariant at the
next depth. -/
lemma step (s : ℕ) (K : ℤ) (h : S.Inv s K) :
    ∃ K0 K1 : ℤ, K0 ≠ K1 ∧
      S.Inv (s + 1) K0 ∧ S.Inv (s + 1) K1 ∧
      S.Jfull (s + 1) K0 ⊆ S.Jshr s K ∧ S.Jfull (s + 1) K1 ⊆ S.Jshr s K := by
  classical
  have hRpos := S.scale_pos s
  have hPpos := S.scale_pos (s + 1)
  set a0 : ℝ := S.scale (s + 1) * (((K : ℝ) + S.eps) / S.scale s) with ha0
  set b0 : ℝ := S.scale (s + 1) * (((K : ℝ) + 1 - S.eps) / S.scale s) with hb0
  -- the gap between the parent's shrunk endpoints, in child-scale coordinates
  have hgapr : (2 * (S.n0 : ℝ) + 3) ≤ b0 - a0 := by
    have hba : b0 - a0 = S.scale (s + 1) / S.scale s * (1 - 2 * S.eps) := by
      rw [ha0, hb0]; field_simp; ring
    rw [hba]; exact S.scale_ratio_gap s
  set Kst : ℤ := ⌈a0⌉ with hKst
  set availF : Finset ℤ := Finset.Icc Kst (Kst + (2 * (S.n0 : ℤ) + 1)) with havailF
  -- every available child is contained in the parent's shrunk interval
  have havsub : ∀ K' ∈ availF, S.Jfull (s + 1) K' ⊆ S.Jshr s K := by
    intro K' hK'
    rw [havailF, Finset.mem_Icc] at hK'
    have hle : a0 ≤ (Kst : ℝ) := Int.le_ceil _
    have hlt : (Kst : ℝ) < a0 + 1 := Int.ceil_lt_add_one _
    have hKlow : (Kst : ℝ) ≤ (K' : ℝ) := by exact_mod_cast hK'.1
    have hKhigh : (K' : ℝ) ≤ (Kst : ℝ) + (2 * (S.n0 : ℝ) + 1) := by exact_mod_cast hK'.2
    refine S.child_subset_of s K K' ?_ ?_
    · rw [← ha0]; linarith
    · rw [← hb0]; linarith
  -- bad children for an intermediate index
  set badF : ℕ → Finset ℤ :=
    fun m => availF.filter (fun K' => ∃ θ ∈ S.Jfull (s + 1) K', ndist (S.Q m * θ) < S.eps)
    with hbadF
  have hbad_card : ∀ m, s * S.n0 < m → m < (s + 1) * S.n0 → (badF m).card ≤ 2 := by
    intro m hm1 hm2
    apply card_le_two_of_close
    intro a ha b hb
    rw [hbadF, Finset.mem_filter] at ha hb
    exact S.bad_close s K m hm1 hm2 a b (havsub a ha.1) (havsub b hb.1) ha.2 hb.2
  set Iset : Finset ℕ := Finset.Ioo (s * S.n0) ((s + 1) * S.n0) with hIset
  set bigU : Finset ℤ := Iset.biUnion badF with hbigU
  have hbigU_sub : bigU ⊆ availF := by
    rw [hbigU]
    refine Finset.biUnion_subset.mpr ?_
    intro m _; rw [hbadF]; exact Finset.filter_subset _ _
  have hIset_card : Iset.card = S.n0 - 1 := by
    rw [hIset, Nat.card_Ioo]
    have : (s + 1) * S.n0 = s * S.n0 + S.n0 := by ring
    omega
  have hbigU_card : bigU.card ≤ 2 * (S.n0 - 1) := by
    calc bigU.card ≤ ∑ m ∈ Iset, (badF m).card := by rw [hbigU]; exact Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ Iset, 2 := by
          refine Finset.sum_le_sum ?_
          intro m hm; rw [hIset, Finset.mem_Ioo] at hm; exact hbad_card m hm.1 hm.2
      _ = 2 * Iset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ = 2 * (S.n0 - 1) := by rw [hIset_card]
  have havail_card : availF.card = 2 * S.n0 + 2 := by
    rw [havailF, Int.card_Icc]; omega
  have hgood_card : 2 ≤ (availF \ bigU).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hbigU_sub, havail_card]
    have := S.hn0
    omega
  obtain ⟨K0, hK0, K1, hK1, hne⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le one_lt_two hgood_card)
  -- the invariant-avoidance for any good child
  have hmid : ∀ K' ∈ availF \ bigU, ∀ m, s * S.n0 < m → m < (s + 1) * S.n0 →
      ∀ θ ∈ S.Jfull (s + 1) K', S.eps ≤ ndist (S.Q m * θ) := by
    intro K' hK' m hm1 hm2 θ hθ
    rw [Finset.mem_sdiff] at hK'
    have hmI : m ∈ Iset := by rw [hIset, Finset.mem_Ioo]; exact ⟨hm1, hm2⟩
    have hnotbad : K' ∉ badF m := by
      intro hc
      exact hK'.2 (by rw [hbigU]; exact Finset.subset_biUnion_of_mem badF hmI hc)
    rw [hbadF, Finset.mem_filter, not_and] at hnotbad
    have := hnotbad hK'.1
    push Not at this
    exact this θ hθ
  refine ⟨K0, K1, hne, ?_, ?_, ?_, ?_⟩
  · exact S.inv_succ_of s K K0 h (havsub K0 (Finset.mem_sdiff.1 hK0).1) (hmid K0 hK0)
  · exact S.inv_succ_of s K K1 h (havsub K1 (Finset.mem_sdiff.1 hK1).1) (hmid K1 hK1)
  · exact havsub K0 (Finset.mem_sdiff.1 hK0).1
  · exact havsub K1 (Finset.mem_sdiff.1 hK1).1

/-! ## Assembling the Cantor scheme -/

/-- The child integer chosen by a bit `b`, given the parent depth `s` and integer `K`. -/
noncomputable def childK (s : ℕ) (K : ℤ) (b : Bool) : ℤ := by
  classical
  exact
    if h : S.Inv s K then
      (if b then (S.step s K h).choose
        else (S.step s K h).choose_spec.choose)
    else 0

/-- Distinct bits give distinct child integers. -/
lemma childK_ne (s : ℕ) (K : ℤ) (h : S.Inv s K) : S.childK s K false ≠ S.childK s K true := by
  obtain ⟨ K0, K1, hne, h0, h1, hfull0, hfull1 ⟩ := S.step s K h; simp_all +decide [ Setup.childK ] ;
  grind

/-- A child's full interval lies in the parent's shrunk interval. -/
lemma childK_Jfull_subset (s : ℕ) (K : ℤ) (h : S.Inv s K) (b : Bool) :
    S.Jfull (s + 1) (S.childK s K b) ⊆ S.Jshr s K := by
  unfold Setup.childK;
  grind

/-- A chosen child satisfies the invariant at the next depth. -/
lemma childK_inv (s : ℕ) (K : ℤ) (h : S.Inv s K) (b : Bool) :
    S.Inv (s + 1) (S.childK s K b) := by
  obtain ⟨ K0, K1, hne, h0, h1, hfull0, hfull1 ⟩ := S.step s K h; cases b <;> simp_all +decide [ Setup.childK ] ;
  · grind;
  · grind +qlia

/-- The integer chosen for a list of bits (the branch up to that depth). -/
noncomputable def node (S : Setup) : List Bool → ℤ
  | [] => 0
  | (b :: l) => S.childK l.length (node S l) b

/-- The scheme: the shrunk interval at the appropriate depth and chosen integer. -/
noncomputable def scheme (l : List Bool) : Set ℝ := S.Jshr l.length (S.node l)

/-- The invariant holds all along the recursion. -/
lemma node_inv : ∀ l : List Bool, S.Inv l.length (S.node l) := by
  intro l
  induction l with
  | nil =>
    intro θ _ m hm1 hm0
    simp only [List.length_nil, Nat.zero_mul] at hm0
    omega
  | cons b l ih =>
    exact S.childK_inv l.length (S.node l) ih b

lemma scheme_antitone : CantorScheme.Antitone S.scheme := by
  intro l a;
  refine' Set.Subset.trans _ ( S.childK_Jfull_subset _ _ ( S.node_inv l ) a );
  exact S.Jshr_subset_Jfull _ _

lemma scheme_closed (l : List Bool) : IsClosed (S.scheme l) := S.Jshr_isClosed _ _

lemma scheme_nonempty (l : List Bool) : (S.scheme l).Nonempty := S.Jshr_nonempty _ _

lemma scheme_disjoint : CantorScheme.Disjoint S.scheme := by
  intro l a b hab
  change Disjoint (S.Jshr (l.length + 1) (S.childK l.length (S.node l) a))
    (S.Jshr (l.length + 1) (S.childK l.length (S.node l) b))
  apply S.Jshr_disjoint
  have h := S.childK_ne l.length (S.node l) (S.node_inv l)
  cases a <;> cases b <;> tauto

lemma scheme_vanishingDiam : CantorScheme.VanishingDiam S.scheme := by
  have h_ediam : ∀ l : List Bool, Metric.ediam (S.scheme l) = ENNReal.ofReal ((1 - 2 * S.eps) / S.scale l.length) := by
    intro l
    unfold Setup.scheme Setup.Jshr
    rw [Real.ediam_Icc]
    congr 1
    ring
  intro x
  have h_tendsto : Filter.Tendsto (fun n => ENNReal.ofReal ((1 - 2 * S.eps) / S.scale n)) Filter.atTop (nhds (ENNReal.ofReal 0)) := by
    refine' ENNReal.tendsto_ofReal _;
    exact tendsto_const_nhds.div_atTop ( S.scale_tendsto_atTop );
  simpa [ h_ediam, PiNat.res_length ] using h_tendsto

/-
Every branch intersection lands in the full constraint set.
-/
lemma scheme_branch_subset (x : ℕ → Bool) :
    (⋂ n, S.scheme (PiNat.res x n)) ⊆ {θ : ℝ | ∀ m, 1 ≤ m → S.eps ≤ ndist (S.Q m * θ)} := by
  intro θ hθ m hm;
  simp_all +decide [ Set.mem_iInter ];
  have := hθ m;
  unfold Setup.scheme at this;
  have := S.node_inv ( PiNat.res x m ) ; simp_all +decide [ Setup.Inv ] ;
  exact this ( S.Jshr_subset_Jfull _ _ <| by assumption ) m hm ( by nlinarith [ S.hn0 ] )

/-- **Main construction theorem.** The set of `θ` with `‖Q m · θ‖ ≥ eps` for all `m ≥ 1` is
uncountable. -/
theorem solution_uncountable :
    ¬ ({θ : ℝ | ∀ m, 1 ≤ m → S.eps ≤ ndist (S.Q m * θ)}).Countable := by
  apply not_countable_of_cantorScheme S.scheme S.scheme_antitone S.scheme_closed
    S.scheme_nonempty S.scheme_disjoint S.scheme_vanishingDiam
  exact S.scheme_branch_subset

end Setup

/-
For `lam > 1`, the geometric sequence `lam^n` eventually dominates `2n+4`.
-/
lemma exists_pow_ge_linear (lam : ℝ) (h : 1 < lam) : ∃ n : ℕ, 1 ≤ n ∧ (2 * (n : ℝ) + 4) ≤ lam ^ n := by
  -- By definition of exponentiation, we know that if $1 < \lambda$, then $\lambda^n$ grows faster than $2n + 4$.
  have h_exp_growth : Filter.Tendsto (fun n : ℕ => lam^n / (n : ℝ)) Filter.atTop Filter.atTop := by
    have h_exp_growth : Filter.Tendsto (fun n : ℕ => Real.exp (n * Real.log lam) / (n : ℝ)) Filter.atTop Filter.atTop := by
      -- Let $y = n \log \lambda$, therefore the limit becomes $\lim_{y \to \infty} \frac{e^y}{y}$.
      suffices h_lim_y : Filter.Tendsto (fun y : ℝ => Real.exp y / y) Filter.atTop Filter.atTop by
        have h_subst : Filter.Tendsto (fun n : ℕ => Real.exp (n * Real.log lam) / (n * Real.log lam) * Real.log lam) Filter.atTop Filter.atTop := by
          exact Filter.Tendsto.atTop_mul_const ( Real.log_pos h ) ( h_lim_y.comp <| tendsto_natCast_atTop_atTop.atTop_mul_const <| Real.log_pos h );
        simpa [ div_mul, ne_of_gt, Real.log_pos h ] using h_subst;
      simpa using Real.tendsto_exp_div_pow_atTop 1;
    simpa only [ Real.exp_nat_mul, Real.exp_log ( zero_lt_one.trans h ) ] using h_exp_growth;
  exact Filter.eventually_atTop.mp ( h_exp_growth.eventually_ge_atTop 6 ) |> fun ⟨ n, hn ⟩ ↦ ⟨ n + 1, by linarith, by have := hn ( n + 1 ) ( by linarith ) ; rw [ le_div_iff₀ ] at this <;> norm_num at * <;> linarith ⟩

/-
Packaging: from a positive sequence with bounded ratios, produce a `Setup`.
-/
lemma exists_setup (Q : ℕ → ℝ) (lam mu : ℝ) (hlam : 1 < lam) (hlammu : lam ≤ mu)
    (hQpos : ∀ n, 0 < Q n) (hlo : ∀ n, lam * Q n ≤ Q (n + 1)) (hhi : ∀ n, Q (n + 1) ≤ mu * Q n) :
    ∃ S : Setup, S.Q = Q := by
  obtain ⟨ n0, hn0 ⟩ := exists_pow_ge_linear lam hlam;
  exact ⟨ ⟨ Q, lam, mu, n0, 1 / ( 4 * mu ^ ( 2 * n0 - 1 ) ), hlam, hlammu, hn0.1, hn0.2, hQpos, hlo, hhi, rfl ⟩, rfl ⟩

end Erdos464
