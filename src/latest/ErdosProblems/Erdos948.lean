/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 948.
https://www.erdosproblems.com/forum/thread/948

Informal authors:
- Lisa Price
- GPT-5.5 Pro

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos948.md
-/
import Mathlib

open scoped BigOperators
open scoped Classical

/-!
# A Negative Answer to an Erdős–Galvin Problem

We formalise the main theorem and corollary of the note *A Negative Answer to an
Erdős–Galvin Problem*.

For a sequence `a : ℕ → ℤ` we write `FS(a)` for its (nonempty) finite-sums set,
`{ ∑_{i ∈ I} a i : ∅ ≠ I ⊆ ℕ finite }`.

**Theorem.** For every `f : ℕ → ℕ` there is a colouring `χ_f : ℤ → ℕ` such that for
every strictly increasing sequence `a` of integers with `a n < f n` for infinitely
many `n`, the image `χ_f (FS(a))` is all of `ℕ`.

**Corollary.** For every `f` and every `k ≥ 2` there is a `k`-colouring with the same
property, so no pair `(f, k)` has the property asked for by Erdős and Galvin.
-/

namespace Erdos948

open Nat List Finset

/-! ## The colouring -/

/-- The nondecreasing envelope `F(n) = max{2, f(0),…,f(n)}` of `f`. -/
def Fenv (f : ℕ → ℕ) (n : ℕ) : ℕ := max 2 ((Finset.range (n + 1)).sup f)

/-- The growth function `G(L) = L + 1 + max_{0 ≤ j ≤ L} ⌈log₂ F(2^{j+3})⌉`. -/
def Gfun (f : ℕ → ℕ) (L : ℕ) : ℕ :=
  L + 1 + (Finset.range (L + 1)).sup (fun j => Nat.clog 2 (Fenv f (2 ^ (j + 3))))

/-- Auxiliary greedy cluster counter operating on a *sorted ascending* list of binary
exponents. The first component is the number of cluster starts seen so far; the second
component is the current threshold (the next allowed cluster start). -/
def clusterAux2 (G : ℕ → ℕ) : ℕ → List ℕ → ℕ × ℕ
  | bound, [] => (0, bound)
  | bound, e :: rest =>
      if bound ≤ e then
        ((clusterAux2 G (G e) rest).1 + 1, (clusterAux2 G (G e) rest).2)
      else clusterAux2 G bound rest

/-- The number of `G`-cluster starts of `n` (the greedy clustering of its binary support). -/
def rho (G : ℕ → ℕ) (n : ℕ) : ℕ := (clusterAux2 G 0 n.bitIndices).1

/-- The colouring `χ_f`. -/
def chi (f : ℕ → ℕ) (x : ℤ) : ℕ := if 0 < x then rho (Gfun f) x.toNat - 1 else 0

/-! ## Elementary properties of `Fenv` and `Gfun` -/

lemma Fenv_ge_self (f : ℕ → ℕ) (n : ℕ) : f n ≤ Fenv f n := by
  exact le_max_of_le_right ( Finset.le_sup ( f := f ) ( Finset.mem_range.mpr ( Nat.lt_succ_self _ ) ) )

lemma Fenv_ge_two (f : ℕ → ℕ) (n : ℕ) : 2 ≤ Fenv f n := by
  -- By definition of $Fenv$, we know that $Fenv f n \geq 2$ because $2$ is the first term in the maximum.
  simp [Fenv]

lemma Fenv_pos (f : ℕ → ℕ) (n : ℕ) : 0 < Fenv f n := lt_of_lt_of_le (by norm_num) (Fenv_ge_two f n)

lemma Fenv_mono (f : ℕ → ℕ) : Monotone (Fenv f) := by
  refine' fun n m hnm => max_le_max le_rfl _;
  exact Finset.sup_mono ( Finset.range_mono ( Nat.succ_le_succ hnm ) )

lemma Gfun_mono (f : ℕ → ℕ) : Monotone (Gfun f) := by
  intro L L' hLL';
  exact Nat.add_le_add ( by linarith ) ( Finset.sup_mono ( Finset.range_mono ( by linarith ) ) )

lemma Gfun_self_lt (f : ℕ → ℕ) (L : ℕ) : L < Gfun f L := by
  exact lt_add_of_lt_of_nonneg ( lt_add_of_pos_right _ zero_lt_one ) ( Nat.zero_le _ )

/-
The key growth inequality `2^L · F(2^{L+3}) < 2^{G(L)}`.
-/
lemma Gfun_growth (f : ℕ → ℕ) (L : ℕ) :
    2 ^ L * Fenv f (2 ^ (L + 3)) < 2 ^ (Gfun f L) := by
      rw [ Gfun ];
      refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( show Fenv f ( 2 ^ ( L + 3 ) ) ≤ 2 ^ ( ( Finset.range ( L + 1 ) ).sup fun j => clog 2 ( Fenv f ( 2 ^ ( j + 3 ) ) ) ) from _ ) ( by positivity ) ) _;
      · refine' le_trans _ ( pow_le_pow_right₀ ( by decide ) ( Finset.le_sup ( f := fun j => clog 2 ( Fenv f ( 2 ^ ( j + 3 ) ) ) ) ( Finset.mem_range.mpr ( Nat.lt_succ_self L ) ) ) );
        exact Nat.le_pow_clog ( by decide ) _;
      · grind

/-! ## Properties of the cluster counter -/

/-
If every element of the list is below the current threshold, nothing new is counted
and the threshold is unchanged.
-/
lemma clusterAux2_all_below (G : ℕ → ℕ) (bd : ℕ) :
    ∀ (L : List ℕ), (∀ e ∈ L, e < bd) → clusterAux2 G bd L = (0, bd) := by
      intro L h; induction L <;> simp_all +decide [ clusterAux2 ] ;

/-
Appending lists composes the counter.
-/
lemma clusterAux2_append (G : ℕ → ℕ) (b : ℕ) :
    ∀ (L1 L2 : List ℕ),
      clusterAux2 G b (L1 ++ L2) =
        ((clusterAux2 G b L1).1 + (clusterAux2 G (clusterAux2 G b L1).2 L2).1,
         (clusterAux2 G (clusterAux2 G b L1).2 L2).2) := by
           intros L1 L2; induction' L1 with hd tl ih generalizing b <;> simp_all +decide [ clusterAux2 ] ;
           grind

/-
A single cluster block: a nonempty list whose head is `v` and all of whose elements
lie below `G v`, counted starting from a threshold `b ≤ v`, contributes exactly one
cluster and leaves threshold `G v`.
-/
lemma clusterAux2_block (G : ℕ → ℕ) (L : List ℕ) (v b : ℕ)
    (hhead : L.head? = some v) (hb : b ≤ v) (hlt : ∀ e ∈ L, e < G v) :
    clusterAux2 G b L = (1, G v) := by
      induction' L with e L ih generalizing b;
      · contradiction;
      · simp_all +decide [ clusterAux2 ];
        exact clusterAux2_all_below G ( G v ) L ( fun x hx => hlt.2 x hx ) ▸ by norm_num;

/-! ## Binary support manipulations -/

/-
If `2^L ∣ m` then every binary exponent of `m` is at least `L`.
-/
lemma le_of_mem_bitIndices_of_dvd {m L : ℕ} (h : 2 ^ L ∣ m) :
    ∀ e ∈ m.bitIndices, L ≤ e := by
      rcases h with ⟨ k, rfl ⟩;
      induction' L with L ih generalizing k <;> simp_all +decide [ Nat.pow_succ', Nat.mul_assoc ];
      grind

/-
If `m < 2^k` then every binary exponent of `m` is below `k`.
-/
lemma lt_of_mem_bitIndices_of_lt {m k : ℕ} (h : m < 2 ^ k) :
    ∀ e ∈ m.bitIndices, e < k := by
      contrapose! h;
      obtain ⟨ e, he₁, he₂ ⟩ := h;
      refine' le_trans _ ( Nat.le_of_not_lt fun h => _ );
      exact Nat.pow_le_pow_right ( by decide ) he₂;
      have h_contra : m.testBit e = false := by
        grind +suggestions;
      grind +suggestions

/-
For a sorted-ascending list, the head is the minimum element.
-/
lemma head?_eq_of_mem_of_forall_le {L : List ℕ} {v : ℕ}
    (hsorted : L.Pairwise (· ≤ ·)) (hv : v ∈ L) (hle : ∀ e ∈ L, v ≤ e) :
    L.head? = some v := by
      induction' L with hd tl ih;
      · contradiction;
      · simp_all +decide [ List.pairwise_cons ];
        grind

/-
If all binary exponents of `x` are strictly below all binary exponents of `y`, then the
binary support of `x + y` is the concatenation of the two supports.
-/
lemma bitIndices_add_separated {x y : ℕ}
    (h : ∀ e ∈ x.bitIndices, ∀ d ∈ y.bitIndices, e < d) :
    (x + y).bitIndices = x.bitIndices ++ y.bitIndices := by
      have h_sum : x + y = ((x.bitIndices ++ y.bitIndices).map (fun i => 2^i)).sum := by
        simp +zetaDelta at *;
      grind +suggestions

/-! ## Eventually positive -/

/-
A strictly increasing integer sequence is eventually positive.
-/
lemma strictMono_eventually_pos (a : ℕ → ℤ) (ha : StrictMono a) :
    ∃ q0 : ℕ, ∀ i, q0 < i → 0 < a i := by
      by_contra! h;
      -- By definition of strict monotonicity, if $a$ is strictly increasing, then $a(n) \geq a(0) + n$ for all $n$.
      have h_lower_bound : ∀ n, a n ≥ a 0 + n := by
        exact fun n => by induction' n with n ih <;> norm_num ; linarith [ ha n.lt_succ_self ] ;
      exact absurd ( h ( Int.toNat ( -a 0 ) ) ) ( by rintro ⟨ i, hi₁, hi₂ ⟩ ; linarith [ Int.self_le_toNat ( -a 0 ), h_lower_bound i ] )

/-! ## The compact packet lemma -/

/-
**Compact packet lemma.** Given a strictly increasing integer sequence with
`a n < f n` infinitely often, eventually positive past index `q`, and any threshold `T`,
there is a nonempty index set `I` of indices `> q` whose sum `y` is positive, whose binary
support lies in `[v, G v)` for `v = v₂(y) ≥ T`.
-/
lemma packet (f : ℕ → ℕ) (a : ℕ → ℤ) (hmono : StrictMono a)
    (hinf : {n | a n < (f n : ℤ)}.Infinite) (q : ℕ)
    (hpos : ∀ i, q < i → 0 < a i) (T : ℕ) :
    ∃ (I : Finset ℕ) (v : ℕ),
      I.Nonempty ∧ (∀ i ∈ I, q < i) ∧ 0 < (∑ i ∈ I, a i) ∧
      v ∈ ((∑ i ∈ I, a i).toNat).bitIndices ∧ T ≤ v ∧
      (∀ e ∈ ((∑ i ∈ I, a i).toNat).bitIndices, v ≤ e ∧ e < Gfun f v) := by
  -- Since {n | a n < f n} is infinite, pick n in this set with n ≥ max(4, 2*q+1, 2^(T+2)).
  obtain ⟨n, hn⟩ : ∃ n, n ∈ {n | (a n) < f n} ∧ n ≥ max 4 (2 * q + 1) ∧ n ≥ 2 ^ (T + 2) := by
    exact Exists.elim ( hinf.exists_gt ( Max.max ( max 4 ( 2 * q + 1 ) ) ( 2 ^ ( T + 2 ) ) ) ) fun n hn => ⟨ n, hn.1, le_of_lt ( lt_of_le_of_lt ( le_max_left _ _ ) hn.2 ), le_of_lt ( lt_of_le_of_lt ( le_max_right _ _ ) hn.2 ) ⟩;
  -- Set L := Nat.log 2 n - 2.
  set L := Nat.log 2 n - 2;
  -- Consider the map Fin (2^L+1) → ZMod (2^L) sending j ↦ (P j.val : ZMod (2^L)).
  obtain ⟨r, s, hrs, h_eq⟩ : ∃ r s : Fin (2 ^ L + 1), r < s ∧ (∑ i ∈ Finset.Ioc q (q + r.val), a i) ≡ (∑ i ∈ Finset.Ioc q (q + s.val), a i) [ZMOD 2 ^ L] := by
    by_contra! h;
    exact absurd ( Finset.card_le_card ( show Finset.image ( fun r : Fin ( 2 ^ L + 1 ) => ( ∑ i ∈ Finset.Ioc q ( q + r.val ), a i ) % ( 2 ^ L ) ) Finset.univ ⊆ Finset.Ico 0 ( 2 ^ L ) from Finset.image_subset_iff.mpr fun r _ => Finset.mem_Ico.mpr ⟨ Int.emod_nonneg _ ( by positivity ), Int.emod_lt_of_pos _ ( by positivity ) ⟩ ) ) ( by rw [ Finset.card_image_of_injective _ fun r s hrs => le_antisymm ( not_lt.mp fun hlt => h _ _ hlt hrs.symm ) ( not_lt.mp fun hlt => h _ _ hlt hrs ), Finset.card_fin ] ; simp +arith +decide );
  -- Set I := Finset.Ioc (q+r) (q+s) (nonempty since r < s, q+r < q+s).
  set I := Finset.Ioc (q + r.val) (q + s.val) with hI_def
  have hI_nonempty : I.Nonempty := by
    exact Finset.nonempty_Ioc.mpr ( by simpa using hrs )
  have hI_pos : 0 < ∑ i ∈ I, a i := by
    exact Finset.sum_pos ( fun i hi => hpos i <| by linarith [ Finset.mem_Ioc.mp hi ] ) hI_nonempty
  have hI_div : (2 ^ L : ℤ) ∣ ∑ i ∈ I, a i := by
    convert h_eq.dvd using 1 ; ring_nf!;
    exact eq_tsub_of_add_eq <| by rw [ add_comm, ← Finset.sum_union ( Finset.disjoint_right.mpr fun x hx => by aesop ) ] ; congr ; ext ; simp +decide ; omega;
  have hI_lt : ∑ i ∈ I, a i < 2 ^ (Gfun f L) := by
    -- Each index i ∈ I satisfies i ≤ q+s ≤ q+2^L < n, so a i < a n by hmono, and a n < f n ≤ Fenv f n ≤ Fenv f (2^(L+3)) (n ≤ 2^(L+3) via Fenv_mono and Fenv_ge_self).
    have hI_lt_f : ∀ i ∈ I, a i < Fenv f (2 ^ (L + 3)) := by
      intros i hi
      have h_i_lt_n : i < n := by
        have h_i_lt_n : 2 ^ (L + 2) ≤ n := by
          rw [ Nat.sub_add_cancel ( show 2 ≤ Nat.log 2 n from Nat.le_log_of_pow_le ( by decide ) ( by linarith [ Nat.le_max_left 4 ( 2 * q + 1 ), Nat.le_max_right 4 ( 2 * q + 1 ) ] ) ) ] ; exact Nat.pow_log_le_self 2 ( by linarith [ Nat.le_max_left 4 ( 2 * q + 1 ), Nat.le_max_right 4 ( 2 * q + 1 ) ] ) ;
        grind
      have h_a_i_lt_f_n : a i < f n := by
        exact lt_of_le_of_lt ( hmono.monotone h_i_lt_n.le ) hn.1
      have h_f_n_le_Fenv : f n ≤ Fenv f n := by
        exact Fenv_ge_self f n
      have h_Fenv_le_Fenv_2L3 : Fenv f n ≤ Fenv f (2 ^ (L + 3)) := by
        refine' Fenv_mono f _;
        have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) n;
        exact this.le.trans ( Nat.pow_le_pow_right ( by decide ) ( by omega ) )
      linarith [h_a_i_lt_f_n, h_f_n_le_Fenv, h_Fenv_le_Fenv_2L3];
    -- Since $I$ is a subset of $\{q+1, q+2, \ldots, q+2^L\}$, we have $|I| \leq 2^L$.
    have hI_card : I.card ≤ 2 ^ L := by
      simp +zetaDelta at *;
      linarith [ show ( s : ℕ ) ≤ 2 ^ L from Nat.le_of_lt_succ s.2, show ( r : ℕ ) ≥ 0 from Nat.zero_le _ ];
    refine' lt_of_le_of_lt ( Finset.sum_le_sum fun i hi => show a i ≤ Fenv f ( 2 ^ ( L + 3 ) ) from le_of_lt ( hI_lt_f i hi ) ) _ ; norm_num;
    exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hI_card ) ( Nat.cast_nonneg _ ) ) ( by norm_cast; linarith [ Gfun_growth f L ] );
  -- Set v := y.toNat.bitIndices.min' (nonempty since y.toNat > 0 so bitIndices nonempty).
  obtain ⟨v, hv⟩ : ∃ v, v ∈ (∑ i ∈ I, a i).toNat.bitIndices ∧ ∀ e ∈ (∑ i ∈ I, a i).toNat.bitIndices, v ≤ e := by
    have h_bitIndices_nonempty : (∑ i ∈ I, a i).toNat.bitIndices ≠ [] := by
      intro h
      have h_bitIndices_nonempty : ∀ {m : ℕ}, 0 < m → m.bitIndices ≠ [] := by
        intro m hm hnil
        have hsum := Nat.sum_map_two_pow_bitIndices m
        rw [hnil] at hsum
        simp only [List.map_nil, List.sum_nil] at hsum
        exact (Nat.ne_of_gt hm) hsum.symm
      exact h_bitIndices_nonempty ( by linarith [ Int.toNat_of_nonneg hI_pos.le ] ) h;
    exact ⟨ Nat.find <| List.length_pos_iff_exists_mem.mp <| List.length_pos_iff.mpr h_bitIndices_nonempty, Nat.find_spec <| List.length_pos_iff_exists_mem.mp <| List.length_pos_iff.mpr h_bitIndices_nonempty, fun e he => Nat.find_min' _ he ⟩;
  refine' ⟨ I, v, hI_nonempty, _, hI_pos, hv.1, _, _ ⟩;
  · exact fun i hi => by linarith [ Finset.mem_Ioc.mp hi ] ;
  · -- Since $2^L \mid y$, we have $L \leq v$.
    have hL_le_v : L ≤ v := by
      apply le_of_mem_bitIndices_of_dvd;
      any_goals exact hv.1;
      simpa [ ← Int.natCast_dvd_natCast, Int.toNat_of_nonneg hI_pos.le ] using hI_div;
    refine' le_trans _ hL_le_v;
    refine' Nat.le_sub_of_add_le _;
    exact Nat.le_log_of_pow_le ( by decide ) hn.2.2;
  · -- Since $v \geq L$, we have $Gfun f v \geq Gfun f L$.
    have hGfun_ge : Gfun f v ≥ Gfun f L := by
      apply Gfun_mono;
      apply le_of_mem_bitIndices_of_dvd;
      any_goals exact hv.1;
      simpa [ ← Int.natCast_dvd_natCast, Int.toNat_of_nonneg hI_pos.le ] using hI_div;
    have h_bitIndices_lt : ∀ e ∈ (∑ i ∈ I, a i).toNat.bitIndices, e < Gfun f L := by
      apply lt_of_mem_bitIndices_of_lt;
      linarith [ Int.toNat_of_nonneg hI_pos.le ];
    exact fun e he => ⟨ hv.2 e he, lt_of_lt_of_le ( h_bitIndices_lt e he ) hGfun_ge ⟩

/-! ## The packet chain -/

/-
For every `t` there is a nonempty finite index set `I` of indices `> q0` whose sum is
positive and has exactly `t + 1` cluster starts (so colour `t`).
-/
lemma packet_chain (f : ℕ → ℕ) (a : ℕ → ℤ) (hmono : StrictMono a)
    (hinf : {n | a n < (f n : ℤ)}.Infinite) (q0 : ℕ)
    (hpos : ∀ i, q0 < i → 0 < a i) :
    ∀ t : ℕ, ∃ (I : Finset ℕ) (B : ℕ),
      I.Nonempty ∧ (∀ i ∈ I, q0 < i) ∧ 0 < (∑ i ∈ I, a i) ∧
      clusterAux2 (Gfun f) 0 ((∑ i ∈ I, a i).toNat).bitIndices = (t + 1, B) ∧
      (∀ e ∈ ((∑ i ∈ I, a i).toNat).bitIndices, e < B) := by
  intro t;
  induction' t with t ih generalizing q0;
  · -- Apply `packet` to get $I$, $v$ with $I.Nonempty$, $hI : ∀ i ∈ I, q0 < i$, $hSpos : 0 < (∑ i ∈ I, a i)$, $hv_mem : v ∈ S.toNat.bitIndices$, $0 ≤ v$, $hbits : ∀ e ∈ S.toNat.bitIndices, v ≤ e ∧ e < Gfun f v$.
    obtain ⟨I, v, hI_nonempty, hI_pos, hv_mem, hv_bound⟩ : ∃ I : Finset ℕ, ∃ v : ℕ, I.Nonempty ∧ (∀ i ∈ I, q0 < i) ∧ 0 < (∑ i ∈ I, a i) ∧ v ∈ ((∑ i ∈ I, a i).toNat).bitIndices ∧ 0 ≤ v ∧ ∀ e ∈ ((∑ i ∈ I, a i).toNat).bitIndices, v ≤ e ∧ e < Gfun f v := by
      exact packet f a hmono hinf q0 hpos 0;
    refine' ⟨ I, Gfun f v, hI_nonempty, hI_pos, hv_mem, _, _ ⟩;
    · convert clusterAux2_block ( Gfun f ) _ _ _ _ _ _ using 1;
      · apply head?_eq_of_mem_of_forall_le;
        · have h_sorted : ∀ n : ℕ, List.Pairwise (· ≤ ·) n.bitIndices := by
            intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.bitIndices ] ;
            rw [ binaryRec ];
            cases Nat.mod_two_eq_zero_or_one ( n + 1 + 1 ) <;> simp +decide [ *, Nat.shiftRight_eq_div_pow ];
            · exact List.pairwise_map.mpr ( by simpa using ih _ ( Nat.div_le_of_le_mul <| by linarith ) );
            · grind;
          exact h_sorted _;
        · exact hv_bound.1;
        · exact fun e he => hv_bound.2.2 e he |>.1;
      · linarith;
      · exact fun e he => hv_bound.2.2 e he |>.2;
    · exact fun e he => hv_bound.2.2 e he |>.2;
  · obtain ⟨ I, B, hI₁, hI₂, hI₃, hI₄, hI₅ ⟩ := ih q0 hpos;
    obtain ⟨J, w, hJ₁, hJ₂, hJ₃, hw_mem, hw_bound, hybits⟩ : ∃ J : Finset ℕ, ∃ w : ℕ, J.Nonempty ∧ (∀ j ∈ J, I.max' hI₁ < j) ∧ 0 < (∑ j ∈ J, a j) ∧ w ∈ ((∑ j ∈ J, a j).toNat).bitIndices ∧ B ≤ w ∧ (∀ e ∈ ((∑ j ∈ J, a j).toNat).bitIndices, w ≤ e ∧ e < Gfun f w) := by
      apply packet f a hmono hinf (I.max' hI₁) (fun i hi => hpos i (by
      exact lt_of_le_of_lt ( Finset.le_max' _ _ ( hI₁.choose_spec ) |> le_trans ( le_of_lt ( hI₂ _ hI₁.choose_spec ) ) ) hi)) B;
    refine' ⟨ I ∪ J, Gfun f w, _, _, _, _, _ ⟩;
    · exact ⟨ _, Finset.mem_union_left _ ( hI₁.choose_spec ) ⟩;
    · exact fun i hi => by cases Finset.mem_union.mp hi <;> [ exact hI₂ i ‹_›; exact lt_trans ( hI₂ _ ( Finset.max'_mem _ hI₁ ) ) ( hJ₂ _ ‹_› ) ] ;
    · rw [ Finset.sum_union ( Finset.disjoint_left.mpr fun x hxI hxJ => by linarith [ Finset.le_max' I x hxI, hJ₂ x hxJ ] ) ] ; linarith;
    · have h_bitIndices_union : (∑ i ∈ I ∪ J, a i).toNat.bitIndices = (∑ i ∈ I, a i).toNat.bitIndices ++ (∑ j ∈ J, a j).toNat.bitIndices := by
        convert bitIndices_add_separated _;
        · rw [ Finset.sum_union ( Finset.disjoint_left.mpr fun x hxI hxJ => by linarith [ Finset.le_max' I x hxI, hJ₂ x hxJ ] ) ];
          grind;
        · grind;
      rw [ h_bitIndices_union, clusterAux2_append ];
      rw [ hI₄, clusterAux2_block ];
      · apply head?_eq_of_mem_of_forall_le;
        · have h_bitIndices_sorted : ∀ n : ℕ, List.Pairwise (· < ·) n.bitIndices := by
            intro n
            exact Nat.bitIndices_sorted.pairwise
          exact List.Pairwise.imp_of_mem ( fun x y h => le_of_lt h ) ( h_bitIndices_sorted _ );
        · assumption;
        · exact fun e he => hybits e he |>.1;
      · linarith;
      · exact fun e he => hybits e he |>.2;
    · -- By definition of $S$, we know that $S.toNat = St.toNat + Sy.toNat$.
      have hS_toNat : (∑ i ∈ I ∪ J, a i).toNat = (∑ i ∈ I, a i).toNat + (∑ j ∈ J, a j).toNat := by
        rw [ Finset.sum_union ( Finset.disjoint_left.mpr fun x hxI hxJ => by linarith [ Finset.le_max' I x hxI, hJ₂ x hxJ ] ) ];
        grind;
      rw [ hS_toNat, bitIndices_add_separated ]; all_goals grind

/-! ## Main theorem and corollary -/

/-
**Main theorem.** For every `f : ℕ → ℕ` there is a colouring `χ : ℤ → ℕ` such that for
every strictly increasing integer sequence `a` with `a n < f n` infinitely often, every
colour `c` occurs on the finite-sums set `FS(a)`.
-/
theorem countable (f : ℕ → ℕ) :
    ∃ χ : ℤ → ℕ, ∀ a : ℕ → ℤ, StrictMono a →
      {n | a n < (f n : ℤ)}.Infinite →
      ∀ c : ℕ, ∃ I : Finset ℕ, I.Nonempty ∧ χ (∑ i ∈ I, a i) = c := by
  -- Use χ = chi f.
  use chi f;
  -- Introduce the arbitrary strictly increasing sequence `a`, the infinite condition `hinf`, and the colour `c`.
  intro a hmono hinf c
  -- Use `strictMono_eventually_pos` to obtain an index `q0` such that `a i > 0` for all `i > q0`.
  obtain ⟨q0, hpos⟩ := strictMono_eventually_pos a hmono
  -- Use `packet_chain` to get a finite subset `I` such that `chi f (∑ i ∈ I, a i) = c`.
  obtain ⟨I, hI⟩ := packet_chain f a hmono hinf q0 hpos c
  use I
  simp [chi];
  unfold rho; aesop;

/-
**Corollary.** For every `f` and every `k ≥ 2` there is a `k`-colouring with the same
property; hence no pair `(f, k)` has the property asked for by Erdős and Galvin.
-/
theorem finite_int (f : ℕ → ℕ) (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℤ → ZMod k, ∀ a : ℕ → ℤ, StrictMono a →
      {n | a n < (f n : ℤ)}.Infinite →
      ∀ col : ZMod k, ∃ I : Finset ℕ, I.Nonempty ∧ c (∑ i ∈ I, a i) = col := by
  obtain ⟨ χ, hχ ⟩ := countable f;
  use fun x => (χ x : ZMod k);
  intro a ha hinf col;
  obtain ⟨I, hI⟩ := hχ a ha hinf (col.val);
  cases k <;> aesop

/-
The exact finite-colour consequence, with colours represented by `Fin k`.  Unlike
`finite_int`, this includes the harmless one-colour case and only assumes `0 < k`.
-/
theorem finite (f : ℕ → ℕ) (k : ℕ) (hk : 0 < k) :
    ∃ c : ℤ → Fin k, ∀ a : ℕ → ℤ, StrictMono a →
      {n | a n < (f n : ℤ)}.Infinite →
      ∀ col : Fin k, ∃ I : Finset ℕ, I.Nonempty ∧ c (∑ i ∈ I, a i) = col := by
  obtain ⟨χ, hχ⟩ := countable f
  refine ⟨fun x ↦ ⟨χ x % k, Nat.mod_lt _ hk⟩, ?_⟩
  intro a ha hinf col
  obtain ⟨I, hI, hcol⟩ := hχ a ha hinf col.1
  refine ⟨I, hI, Fin.ext ?_⟩
  change χ (∑ i ∈ I, a i) % k = col.1
  rw [hcol, Nat.mod_eq_of_lt col.isLt]

/-
Restriction of the integer colouring to natural numbers, giving the companion
natural-number formulation.
-/
theorem finite_nat (f : ℕ → ℕ) (k : ℕ) (hk : 0 < k) :
    ∃ c : ℕ → Fin k, ∀ a : ℕ → ℕ, StrictMono a →
      {n | a n < f n}.Infinite →
      ∀ col : Fin k, ∃ I : Finset ℕ, I.Nonempty ∧ c (∑ i ∈ I, a i) = col := by
  obtain ⟨c, hc⟩ := finite f k hk
  refine ⟨fun n ↦ c (n : ℤ), ?_⟩
  intro a ha hinf col
  have ha' : StrictMono (fun n ↦ (a n : ℤ)) := by
    intro m n hmn
    exact Int.ofNat_lt.mpr (ha hmn)
  have hinf' : {n | (a n : ℤ) < (f n : ℤ)}.Infinite := by
    simpa only [Int.ofNat_lt] using hinf
  obtain ⟨I, hI, hcol⟩ := hc (fun n ↦ (a n : ℤ)) ha' hinf' col
  refine ⟨I, hI, ?_⟩
  convert hcol using 1
  norm_cast

/-- The positive assertion asked in Problem 948, restricted to natural-number colourings. -/
def Erdos948NatStatement : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
    ∀ colouring : ℕ → Fin k,
      ∃ a : ℕ → ℕ, StrictMono a ∧
        {n | a n < f n}.Infinite ∧
        ∃ omitted : Fin k, ∀ I : Finset ℕ,
          colouring (∑ i ∈ I, a i) ≠ omitted

/-- The positive assertion asked in Problem 948, with colourings and sequences on the integers. -/
def Erdos948Statement : Prop :=
  ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
    ∀ colouring : ℤ → Fin k,
      ∃ a : ℕ → ℤ, StrictMono a ∧
        {n | a n < (f n : ℤ)}.Infinite ∧
        ∃ omitted : Fin k, ∀ I : Finset ℕ,
          colouring (∑ i ∈ I, a i) ≠ omitted

/-- The natural-number version of Erdős Problem 948 has a negative answer. -/
theorem erdos_948_nat : ¬ Erdos948NatStatement := by
  rintro ⟨f, k, hk, hclaimed⟩
  obtain ⟨colouring, hcolouring⟩ := finite_nat f k hk
  obtain ⟨a, ha, hinf, omitted, homitted⟩ := hclaimed colouring
  obtain ⟨I, _hI, hhit⟩ := hcolouring a ha hinf omitted
  exact homitted I hhit

/-- Erdős Problem 948 has a negative answer, verbatim for integer colourings and sequences. -/
theorem not_erdos_948 : ¬ (∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
  ∀ colouring : ℤ → Fin k,
    ∃ a : ℕ → ℤ, StrictMono a ∧
      {n | a n < (f n : ℤ)}.Infinite ∧
      ∃ omitted : Fin k, ∀ I : Finset ℕ,
        colouring (∑ i ∈ I, a i) ≠ omitted) := by
  rintro ⟨f, k, hk, hclaimed⟩
  obtain ⟨colouring, hcolouring⟩ := finite f k hk
  obtain ⟨a, ha, hinf, omitted, homitted⟩ := hclaimed colouring
  obtain ⟨I, _hI, hhit⟩ := hcolouring a ha hinf omitted
  exact homitted I hhit

#print axioms not_erdos_948

end Erdos948

alias _root_.Erdos948.erdos_948 := _root_.Erdos948.not_erdos_948
