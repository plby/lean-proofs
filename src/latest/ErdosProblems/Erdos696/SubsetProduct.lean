/-
# The subset-product successor lemma (abstract form)

Mirrors §6.1 of `erdos_696_paper.tex`, Lemma 5.1 (paper numbering Lemma 6.1).

**Statement.**  Let `G` be a finite abelian group of order `N`, and let
`g₁, …, g_K` be independent uniform elements of `G`.  Let
`Z = #{∅ ≠ S ⊆ {1,…,K} : ∏_{i ∈ S} g_i = 1_G}`.  Then

* `E[Z] = (2^K - 1) / N`,
* `Var[Z] ≤ E[Z]`,
* `P(Z = 0) ≤ N / (2^K - 1)`.

The variance bound rests on the pairwise-independence assertion:
for distinct nonempty `S, T`, `X_S = ∏_{i ∈ S} g_i` and
`X_T = ∏_{i ∈ T} g_i` are independent, both uniform on `G`.

The abstract statement is given here, with full proof of
`subset_product_main` (mean, second moment, Chebyshev tail bound, plus
the measure-theoretic pairwise-independence step).
-/

import Mathlib

namespace Erdos696

open scoped BigOperators
open MeasureTheory

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The product `∏_{i ∈ S} f i` of a function `f : Fin K → G` indexed by
a subset `S` of `Fin K`. -/
noncomputable def subsetProd {K : ℕ} (S : Finset (Fin K)) (f : Fin K → G) : G :=
  ∏ i ∈ S, f i

/-- The random variable `Z(g) = #{∅ ≠ S ⊆ Fin K : subsetProd S g = 1}`. -/
noncomputable def Zsubset {K : ℕ} (g : Fin K → G) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin K))).filter
    (fun S => S.Nonempty ∧ subsetProd S g = 1)).card

/-- For a fixed nonempty `S`, the pushforward of the uniform distribution
on `G^K` under `g ↦ subsetProd S g` is uniform on `G`.

This is the assertion `X_S ~ Unif(G)` for `S ≠ ∅`.  Sketch: pick
`i₀ ∈ S`; conditioning on `(g_j)_{j ≠ i₀}`, the function
`g_{i₀} ↦ subsetProd S g` is a translation by a fixed group element,
which sends uniform to uniform.  Marginalizing gives the claim.

Proved below using the product measure on `G^K`. -/
lemma subsetProd_uniform {K : ℕ} (S : Finset (Fin K)) (hS : S.Nonempty) (a : G) :
    -- The number of `g ∈ G^K` with `subsetProd S g = a` is `|G|^(K-1)`,
    -- expressing that the pushforward is uniform.
    (Finset.univ.filter (fun g : Fin K → G => subsetProd S g = a)).card =
      (Fintype.card G) ^ (K - 1) := by
  classical
  rcases hS with ⟨i0, hi0⟩
  let P : ({j : Fin K // j ≠ i0} → G) → G :=
    fun h => ∏ x ∈ S.erase i0, if hx : x = i0 then 1 else h ⟨x, hx⟩
  let e : {g : Fin K → G // subsetProd S g = a} ≃ ({j : Fin K // j ≠ i0} → G) :=
  { toFun := fun g j => g.1 j.1
    invFun := fun h =>
      ⟨fun j => if hj : j = i0 then a * (P h)⁻¹ else h ⟨j, hj⟩, by
        dsimp [subsetProd]
        rw [← Finset.mul_prod_erase S
          (fun j => if hj : j = i0 then a * (P h)⁻¹ else h ⟨j, hj⟩) hi0]
        have hprod :
            (∏ x ∈ S.erase i0,
              (if hx : x = i0 then a * (P h)⁻¹ else h ⟨x, hx⟩)) = P h := by
          dsimp [P]
          apply Finset.prod_congr rfl
          intro x hxmem
          have hxne : x ≠ i0 := (Finset.mem_erase.mp hxmem).1
          simp [hxne]
        simp [hprod]
      ⟩
    left_inv := by
      intro g
      ext j
      by_cases hj : j = i0
      · subst j
        dsimp
        have hprod : P (fun j : {j : Fin K // j ≠ i0} => g.1 j.1) =
            (∏ x ∈ S.erase i0, g.1 x) := by
          dsimp [P]
          apply Finset.prod_congr rfl
          intro x hxmem
          have hxne : x ≠ i0 := (Finset.mem_erase.mp hxmem).1
          simp [hxne]
        have hg : g.1 i0 * (∏ x ∈ S.erase i0, g.1 x) = a := by
          rw [Finset.mul_prod_erase S (fun j => g.1 j) hi0]
          exact g.2
        simp only [↓reduceIte]
        rw [hprod]
        let q := ∏ x ∈ S.erase i0, g.1 x
        have hg' : (g.1 i0 * q) * q⁻¹ = a * q⁻¹ := congrArg (fun y => y * q⁻¹) hg
        have hcancel : (g.1 i0 * q) * q⁻¹ = g.1 i0 := by group
        exact hg'.symm.trans hcancel
      · dsimp
        simp [hj]
    right_inv := by
      intro h
      funext j
      dsimp
      simp [j.2] }
  have hcard_filter :
      (Finset.univ.filter (fun g : Fin K → G => subsetProd S g = a)).card =
        Fintype.card {g : Fin K → G // subsetProd S g = a} := by
    simpa using (Fintype.card_subtype (α := Fin K → G)
      (fun g => subsetProd S g = a)).symm
  rw [hcard_filter]
  rw [Fintype.card_congr e]
  rw [Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl (fun j : Fin K => j = i0)]
  have h : Fintype.card {j : Fin K // j = i0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨i0, rfl⟩, ?_⟩
    intro x
    exact Subtype.ext x.2
  rw [h, Fintype.card_fin]

private lemma subsetProd_pair_uniform_aux {K : ℕ}
    (S T : Finset (Fin K)) (hi : ∃ i ∈ S, i ∉ T) (hT : T.Nonempty) (a b : G) :
    (Finset.univ.filter
        (fun g : Fin K → G => subsetProd S g = a ∧ subsetProd T g = b)).card =
      (Fintype.card G) ^ (K - 2) := by
  classical
  rcases hi with ⟨i0, hi0S, hi0T⟩
  rcases hT with ⟨j0, hj0T⟩
  have hij : i0 ≠ j0 := by
    intro h
    exact hi0T (by simpa [h] using hj0T)
  let Rest := {j : Fin K // ¬(j = i0 ∨ j = j0)}
  let Q : (Rest → G) → G :=
    fun h => ∏ x ∈ T.erase j0,
      if hxi : x = i0 then 1 else if hxj : x = j0 then 1 else h ⟨x, by
        exact not_or.mpr ⟨hxi, hxj⟩⟩
  let J : (Rest → G) → G := fun h => b * (Q h)⁻¹
  let P : (Rest → G) → G :=
    fun h => ∏ x ∈ S.erase i0,
      if hxi : x = i0 then 1 else if hxj : x = j0 then J h else h ⟨x, by
        exact not_or.mpr ⟨hxi, hxj⟩⟩
  let e :
      {g : Fin K → G // subsetProd S g = a ∧ subsetProd T g = b} ≃ (Rest → G) :=
  { toFun := fun g j => g.1 j.1
    invFun := fun h =>
      ⟨fun j =>
        if hji : j = i0 then a * (P h)⁻¹
        else if hjj : j = j0 then J h
        else h ⟨j, by exact not_or.mpr ⟨hji, hjj⟩⟩, by
        constructor
        · dsimp [subsetProd]
          rw [← Finset.mul_prod_erase S
            (fun j =>
              if hji : j = i0 then a * (P h)⁻¹
              else if hjj : j = j0 then J h
              else h ⟨j, by exact not_or.mpr ⟨hji, hjj⟩⟩) hi0S]
          have hprod :
              (∏ x ∈ S.erase i0,
                (if hxi : x = i0 then a * (P h)⁻¹
                else if hxj : x = j0 then J h
                else h ⟨x, by exact not_or.mpr ⟨hxi, hxj⟩⟩)) = P h := by
            dsimp [P]
            apply Finset.prod_congr rfl
            intro x hxmem
            have hxi : x ≠ i0 := (Finset.mem_erase.mp hxmem).1
            simp [hxi]
          simp [hprod]
        · dsimp [subsetProd]
          rw [← Finset.mul_prod_erase T
            (fun j =>
              if hji : j = i0 then a * (P h)⁻¹
              else if hjj : j = j0 then J h
              else h ⟨j, by exact not_or.mpr ⟨hji, hjj⟩⟩) hj0T]
          have hprod :
              (∏ x ∈ T.erase j0,
                (if hxi : x = i0 then a * (P h)⁻¹
                else if hxj : x = j0 then J h
                else h ⟨x, by exact not_or.mpr ⟨hxi, hxj⟩⟩)) = Q h := by
            dsimp [Q]
            apply Finset.prod_congr rfl
            intro x hxmem
            have hxj : x ≠ j0 := (Finset.mem_erase.mp hxmem).1
            have hxT : x ∈ T := (Finset.mem_erase.mp hxmem).2
            have hxi : x ≠ i0 := by
              intro hx
              exact hi0T (by simpa [hx] using hxT)
            simp [hxi, hxj]
          have hj0_ne_i0 : j0 ≠ i0 := fun h => hij h.symm
          simp [hj0_ne_i0, hprod, J]
      ⟩
    left_inv := by
      intro g
      have hJ : J (fun j : Rest => g.1 j.1) = g.1 j0 := by
        have hprodT :
            Q (fun j : Rest => g.1 j.1) = (∏ x ∈ T.erase j0, g.1 x) := by
          dsimp [Q]
          apply Finset.prod_congr rfl
          intro x hxmem
          have hxj : x ≠ j0 := (Finset.mem_erase.mp hxmem).1
          have hxT : x ∈ T := (Finset.mem_erase.mp hxmem).2
          have hxi : x ≠ i0 := by
            intro hx
            exact hi0T (by simpa [hx] using hxT)
          simp [hxi, hxj]
        have hgT : g.1 j0 * (∏ x ∈ T.erase j0, g.1 x) = b := by
          rw [Finset.mul_prod_erase T (fun j => g.1 j) hj0T]
          exact g.2.2
        dsimp [J]
        rw [hprodT]
        let q := ∏ x ∈ T.erase j0, g.1 x
        have hg' : (g.1 j0 * q) * q⁻¹ = b * q⁻¹ := congrArg (fun y => y * q⁻¹) hgT
        have hcancel : (g.1 j0 * q) * q⁻¹ = g.1 j0 := by group
        exact hg'.symm.trans hcancel
      ext j
      by_cases hji : j = i0
      · subst j
        dsimp
        have hprodS :
            P (fun j : Rest => g.1 j.1) = (∏ x ∈ S.erase i0, g.1 x) := by
          dsimp [P]
          apply Finset.prod_congr rfl
          intro x hxmem
          have hxi : x ≠ i0 := (Finset.mem_erase.mp hxmem).1
          by_cases hxj : x = j0
          · have hj0_ne_i0 : j0 ≠ i0 := fun h => hij h.symm
            simp [hxj, hj0_ne_i0, hJ]
          · simp [hxi, hxj]
        have hgS : g.1 i0 * (∏ x ∈ S.erase i0, g.1 x) = a := by
          rw [Finset.mul_prod_erase S (fun j => g.1 j) hi0S]
          exact g.2.1
        simp only [↓reduceIte]
        rw [hprodS]
        let q := ∏ x ∈ S.erase i0, g.1 x
        have hg' : (g.1 i0 * q) * q⁻¹ = a * q⁻¹ := congrArg (fun y => y * q⁻¹) hgS
        have hcancel : (g.1 i0 * q) * q⁻¹ = g.1 i0 := by group
        exact hg'.symm.trans hcancel
      · by_cases hjj : j = j0
        · subst j
          dsimp
          have hj0_ne_i0 : j0 ≠ i0 := fun h => hij h.symm
          simp [hj0_ne_i0, hJ]
        · dsimp
          simp [hji, hjj]
    right_inv := by
      intro h
      funext j
      dsimp
      have hji : (j : Fin K) ≠ i0 := by
        intro hj
        exact j.2 (Or.inl hj)
      have hjj : (j : Fin K) ≠ j0 := by
        intro hj
        exact j.2 (Or.inr hj)
      simp [hji, hjj] }
  have hcard_filter :
      (Finset.univ.filter
          (fun g : Fin K → G => subsetProd S g = a ∧ subsetProd T g = b)).card =
        Fintype.card {g : Fin K → G // subsetProd S g = a ∧ subsetProd T g = b} := by
    simpa using (Fintype.card_subtype (α := Fin K → G)
      (fun g => subsetProd S g = a ∧ subsetProd T g = b)).symm
  rw [hcard_filter]
  rw [Fintype.card_congr e]
  rw [Fintype.card_fun]
  congr 1
  dsimp [Rest]
  rw [Fintype.card_subtype_compl (fun j : Fin K => j = i0 ∨ j = j0)]
  rw [Fintype.card_subtype_eq_or_eq_of_ne hij, Fintype.card_fin]

/-- For distinct nonempty `S, T ⊆ Fin K`, the pair
`(X_S, X_T) := (subsetProd S, subsetProd T)` is uniformly distributed
on `G × G`.  This is the *pairwise-independence* assertion (5.6) in the
paper.

Sketch: pick `i₀ ∈ S △ T`, WLOG `i₀ ∈ S \ T`.  Conditioning on
`(g_j)_{j ≠ i₀}` fixes `X_T` and turns `X_S` into a translation of `g_{i₀}`,
which is uniform on `G`; hence `X_S ⟂ X_T`. -/
lemma subsetProd_pair_uniform {K : ℕ}
    (S T : Finset (Fin K)) (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ≠ T)
    (a b : G) :
    (Finset.univ.filter
        (fun g : Fin K → G => subsetProd S g = a ∧ subsetProd T g = b)).card =
      (Fintype.card G) ^ (K - 2) := by
  classical
  have hdiff : (∃ i ∈ S, i ∉ T) ∨ ∃ i ∈ T, i ∉ S := by
    by_contra h
    apply hST
    ext i
    constructor
    · intro hiS
      by_contra hiT
      exact h (Or.inl ⟨i, hiS, hiT⟩)
    · intro hiT
      by_contra hiS
      exact h (Or.inr ⟨i, hiT, hiS⟩)
  rcases hdiff with hdiff | hdiff
  · exact subsetProd_pair_uniform_aux S T hdiff hT a b
  · have hswap := subsetProd_pair_uniform_aux T S hdiff hS b a
    rw [← hswap]
    congr 1
    ext g
    simp [and_comm]

/-- **Subset-product successor lemma (abstract form), inequality (5.4).**

`Σ_{∅ ≠ S} P(X_S = 1) = (2^K - 1) / N`.

This follows from `subsetProd_uniform` (each summand is `N^(K-1)`) and the
fact that the number of nonempty subsets of `Fin K` is `2^K - 1`.  The
proof is "structurally trivial" given `subsetProd_uniform`, but requires
elementary `Finset.card` / `Finset.sum_const` bookkeeping. -/
lemma subset_product_mean_count {K : ℕ} :
    let N := Fintype.card G
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin K))).filter (·.Nonempty),
        (Finset.univ.filter (fun g : Fin K → G => subsetProd S g = 1)).card)
        =
    (2 ^ K - 1) * N ^ (K - 1) := by
  -- Each summand is `N^(K-1)` by `subsetProd_uniform` with `a = 1`.  Then
  -- the sum is constant across the filter, so it equals `(filter.card) ·
  -- N^(K-1)`.  The filter `Finset.univ.filter (·.Nonempty)` over
  -- `Finset (Fin K)` has cardinality `2^K - 1` (= card of all subsets minus
  -- the empty subset).
  intro N
  -- Step 1: each summand = N^(K-1).
  have step1 : ∀ S ∈ (Finset.univ : Finset (Finset (Fin K))).filter (·.Nonempty),
      (Finset.univ.filter (fun g : Fin K → G => subsetProd S g = 1)).card = N ^ (K - 1) := by
    intro S hS
    have hSne : S.Nonempty := (Finset.mem_filter.mp hS).2
    exact subsetProd_uniform S hSne 1
  rw [Finset.sum_congr rfl step1, Finset.sum_const]
  -- Step 2: filter card = 2^K - 1.
  have card_filter :
      ((Finset.univ : Finset (Finset (Fin K))).filter (·.Nonempty)).card = 2 ^ K - 1 := by
    -- `Finset.univ : Finset (Finset (Fin K))` has card `2^K`.
    -- Filter excludes only `S = ∅`, so we lose 1.
    have huniv : (Finset.univ : Finset (Finset (Fin K))).card = 2 ^ K := by
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    -- Express filter as univ.erase ∅
    rw [show ((Finset.univ : Finset (Finset (Fin K))).filter (·.Nonempty)) =
        Finset.univ.erase (∅ : Finset (Fin K)) from ?_]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), huniv]
    · ext S
      simp [Finset.mem_filter, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
  rw [card_filter, smul_eq_mul]

/-- **Subset-product successor lemma (Lemma 5.1 / Lemma 6.1 of paper).**

For a finite abelian group `G` of order `N` and `K` independent uniform
samples `g₁, …, g_K ∈ G`, the probability that no nonempty subset
multiplies to `1_G` is at most `N / (2^K - 1)`.

Sketch (matching equations (5.4)–(5.7) of the paper):
* `E[Z] = (2^K - 1) / N` (`subset_product_mean_count` divided by `|Ω|`).
* `Var[Z] ≤ E[Z]` (using `subsetProd_pair_uniform`).
* Chebyshev: `P(Z = 0) ≤ Var[Z] / (E[Z])^2 ≤ 1 / E[Z] = N / (2^K - 1)`.

Structural assembly of the three steps above.  The numerical
inequality `Var Z ≤ E Z` is (5.8) of the paper. -/
theorem subset_product_main {K : ℕ} (hK : 1 ≤ K) :
    -- The number of `g ∈ G^K` with no nonempty `S` such that
    -- `subsetProd S g = 1` is at most `N · |G|^K / (2^K - 1)`, where `N = |G|`.
    ((Finset.univ.filter
        (fun g : Fin K → G =>
          ∀ S : Finset (Fin K), S.Nonempty → subsetProd S g ≠ 1)).card : ℝ) ≤
      (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) ^ K) / ((2 : ℝ) ^ K - 1) := by
  classical
  dsimp
  let A : Finset (Finset (Fin K)) := (Finset.univ : Finset (Finset (Fin K))).filter (·.Nonempty)
  let bad : Finset (Fin K → G) :=
    Finset.univ.filter
      (fun g : Fin K → G => ∀ S : Finset (Fin K), S.Nonempty → subsetProd S g ≠ 1)
  let Z : (Fin K → G) → ℕ := fun g => (A.filter (fun S => subsetProd S g = (1 : G))).card
  have hA_card : A.card = 2 ^ K - 1 := by
    have huniv : (Finset.univ : Finset (Finset (Fin K))).card = 2 ^ K := by
      rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    rw [show A = Finset.univ.erase (∅ : Finset (Fin K)) from ?_]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ _), huniv]
    · ext S
      simp [A, Finset.mem_filter, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
  have hK_ne : K ≠ 0 := by omega
  have hpow_ge_one_nat : 1 ≤ 2 ^ K := le_of_lt (Nat.one_lt_two_pow hK_ne)
  have hA_card_real : (A.card : ℝ) = (2 : ℝ) ^ K - 1 := by
    rw [hA_card, Nat.cast_sub hpow_ge_one_nat]
    norm_num
  have hA_pos : 0 < A.card := by
    rw [hA_card]
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hK_ne)
  have hA_pos_real : 0 < (A.card : ℝ) := by exact_mod_cast hA_pos
  have hOmega_card : (Finset.univ : Finset (Fin K → G)).card = (Fintype.card G) ^ K := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  by_cases hK2 : 2 ≤ K
  · have hZ_card : ∀ g : Fin K → G,
        Z g = ∑ S ∈ A, if subsetProd S g = (1 : G) then 1 else 0 := by
      intro g
      dsimp [Z]
      rw [Finset.card_filter]
    have hsumZ :
        (∑ g : Fin K → G, Z g) = A.card * (Fintype.card G) ^ (K - 1) := by
      calc
        (∑ g : Fin K → G, Z g)
            = ∑ g : Fin K → G,
                ∑ S ∈ A, if subsetProd S g = (1 : G) then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro g _
              exact hZ_card g
        _ = ∑ S ∈ A,
                ∑ g : Fin K → G, if subsetProd S g = (1 : G) then 1 else 0 := by
              rw [Finset.sum_comm]
        _ = ∑ S ∈ A,
                (Finset.univ.filter (fun g : Fin K → G => subsetProd S g = (1 : G))).card := by
              apply Finset.sum_congr rfl
              intro S _
              rw [Finset.card_filter]
        _ = A.card * (Fintype.card G) ^ (K - 1) := by
              have hconst : ∀ S ∈ A,
                  (Finset.univ.filter
                    (fun g : Fin K → G => subsetProd S g = (1 : G))).card =
                    (Fintype.card G) ^ (K - 1) := by
                intro S hS
                exact subsetProd_uniform S (Finset.mem_filter.mp hS).2 1
              rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    have hZ_sq : ∀ g : Fin K → G,
        (Z g) ^ 2 =
          ∑ S ∈ A, ∑ T ∈ A,
            if subsetProd S g = (1 : G) ∧ subsetProd T g = (1 : G) then 1 else 0 := by
      intro g
      rw [hZ_card g, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro T _
      by_cases hS : subsetProd S g = (1 : G) <;>
        by_cases hT : subsetProd T g = (1 : G) <;> simp [hS, hT]
    have hpair_count :
        ∀ S ∈ A, ∀ T ∈ A,
          (∑ g : Fin K → G,
              if subsetProd S g = (1 : G) ∧ subsetProd T g = (1 : G) then 1 else 0)
            =
          if S = T then (Fintype.card G) ^ (K - 1) else (Fintype.card G) ^ (K - 2) := by
      intro S hS T hT
      by_cases hST : S = T
      · subst T
        simp only [and_self, Finset.sum_boole, Nat.cast_id, ↓reduceIte]
        exact subsetProd_uniform S (Finset.mem_filter.mp hS).2 1
      · simp only [Finset.sum_boole, Nat.cast_id, hST, ↓reduceIte]
        exact subsetProd_pair_uniform S T (Finset.mem_filter.mp hS).2
          (Finset.mem_filter.mp hT).2 hST 1 1
    have hinner_bound : ∀ S ∈ A,
        (∑ T ∈ A,
          if S = T then (Fintype.card G) ^ (K - 1) else (Fintype.card G) ^ (K - 2))
          ≤ (Fintype.card G) ^ (K - 1) + A.card * (Fintype.card G) ^ (K - 2) := by
      intro S hS
      rw [← Finset.sum_erase_add A
        (fun T => if S = T then (Fintype.card G) ^ (K - 1)
          else (Fintype.card G) ^ (K - 2)) hS]
      have herase :
          (∑ T ∈ A.erase S,
            if S = T then (Fintype.card G) ^ (K - 1) else (Fintype.card G) ^ (K - 2))
            = (A.card - 1) * (Fintype.card G) ^ (K - 2) := by
        calc
          (∑ T ∈ A.erase S,
            if S = T then (Fintype.card G) ^ (K - 1)
              else (Fintype.card G) ^ (K - 2))
              = ∑ T ∈ A.erase S, (Fintype.card G) ^ (K - 2) := by
                apply Finset.sum_congr rfl
                intro T hT
                have hTS : T ≠ S := (Finset.mem_erase.mp hT).1
                have hST' : S ≠ T := fun h => hTS h.symm
                simp [hST']
          _ = (A.card - 1) * (Fintype.card G) ^ (K - 2) := by
                rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hS]
      rw [herase]
      simp only [↓reduceIte, ge_iff_le]
      have hmul :
          (A.card - 1) * (Fintype.card G) ^ (K - 2) ≤
            A.card * (Fintype.card G) ^ (K - 2) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      omega
    have hsumZ2 :
        (∑ g : Fin K → G, (Z g) ^ 2) ≤
          A.card * (Fintype.card G) ^ (K - 1) +
            A.card * A.card * (Fintype.card G) ^ (K - 2) := by
      calc
        (∑ g : Fin K → G, (Z g) ^ 2)
            = ∑ g : Fin K → G,
                ∑ S ∈ A, ∑ T ∈ A,
                  if subsetProd S g = (1 : G) ∧ subsetProd T g = (1 : G) then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro g _
              exact hZ_sq g
        _ = ∑ S ∈ A, ∑ T ∈ A,
                ∑ g : Fin K → G,
                  if subsetProd S g = (1 : G) ∧ subsetProd T g = (1 : G) then 1 else 0 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro S _
              rw [Finset.sum_comm]
        _ = ∑ S ∈ A, ∑ T ∈ A,
                if S = T then (Fintype.card G) ^ (K - 1) else (Fintype.card G) ^ (K - 2) := by
              apply Finset.sum_congr rfl
              intro S hS
              apply Finset.sum_congr rfl
              intro T hT
              exact hpair_count S hS T hT
        _ ≤ ∑ S ∈ A,
                ((Fintype.card G) ^ (K - 1) + A.card * (Fintype.card G) ^ (K - 2)) := by
              apply Finset.sum_le_sum
              intro S hS
              exact hinner_bound S hS
        _ = A.card * (Fintype.card G) ^ (K - 1) +
              A.card * A.card * (Fintype.card G) ^ (K - 2) := by
              rw [Finset.sum_const, smul_eq_mul]
              ring_nf
    let D : (Fin K → G) → ℝ :=
      fun g => (Fintype.card G : ℝ) * (Z g : ℝ) - (A.card : ℝ)
    have hbad_Z : ∀ g ∈ bad, Z g = 0 := by
      intro g hg
      dsimp [bad, Z] at hg ⊢
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro S hSA hprod
      exact ((Finset.mem_filter.mp hg).2 S (Finset.mem_filter.mp hSA).2) hprod
    have hbad_lower :
        (bad.card : ℝ) * (A.card : ℝ) ^ 2 ≤ ∑ g : Fin K → G, (D g) ^ 2 := by
      calc
        (bad.card : ℝ) * (A.card : ℝ) ^ 2
            = ∑ g ∈ bad, (A.card : ℝ) ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ g ∈ bad, (D g) ^ 2 := by
              apply Finset.sum_congr rfl
              intro g hg
              dsimp [D]
              rw [hbad_Z g hg]
              ring
        _ ≤ ∑ g : Fin K → G, (D g) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun g _ _ => sq_nonneg (D g))
    have hsumZ_real :
        (∑ g : Fin K → G, (Z g : ℝ)) =
          (A.card * (Fintype.card G) ^ (K - 1) : ℕ) := by
      exact_mod_cast hsumZ
    have hsumZ2_real :
        (∑ g : Fin K → G, (Z g : ℝ) ^ 2) ≤
          (A.card * (Fintype.card G) ^ (K - 1) +
            A.card * A.card * (Fintype.card G) ^ (K - 2) : ℕ) := by
      exact_mod_cast hsumZ2
    have hsumD_expand :
        (∑ g : Fin K → G, (D g) ^ 2) =
          (Fintype.card G : ℝ) ^ 2 * (∑ g : Fin K → G, (Z g : ℝ) ^ 2)
          - 2 * (Fintype.card G : ℝ) * (A.card : ℝ) *
              (∑ g : Fin K → G, (Z g : ℝ))
          + ((Finset.univ : Finset (Fin K → G)).card : ℝ) * (A.card : ℝ) ^ 2 := by
      dsimp [D]
      calc
        (∑ g : Fin K → G,
            ((Fintype.card G : ℝ) * (Z g : ℝ) - (A.card : ℝ)) ^ 2)
            = ∑ g : Fin K → G,
                ((Fintype.card G : ℝ) ^ 2 * (Z g : ℝ) ^ 2
                  - 2 * (Fintype.card G : ℝ) * (A.card : ℝ) * (Z g : ℝ)
                  + (A.card : ℝ) ^ 2) := by
              apply Finset.sum_congr rfl
              intro g _
              ring
        _ = (Fintype.card G : ℝ) ^ 2 * (∑ g : Fin K → G, (Z g : ℝ) ^ 2)
            - 2 * (Fintype.card G : ℝ) * (A.card : ℝ) *
                (∑ g : Fin K → G, (Z g : ℝ))
            + ((Finset.univ : Finset (Fin K → G)).card : ℝ) * (A.card : ℝ) ^ 2 := by
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
                Finset.sum_const, nsmul_eq_mul]
    have hsumD_le :
        (∑ g : Fin K → G, (D g) ^ 2) ≤
          ((Finset.univ : Finset (Fin K → G)).card : ℝ) *
            (A.card : ℝ) * (Fintype.card G : ℝ) := by
      rw [hsumD_expand, hsumZ_real]
      have hnonneg : 0 ≤ (Fintype.card G : ℝ) ^ 2 := sq_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hsumZ2_real hnonneg
      have halg :
          (Fintype.card G : ℝ) ^ 2 *
              (A.card * (Fintype.card G) ^ (K - 1) +
                A.card * A.card * (Fintype.card G) ^ (K - 2) : ℕ)
            - 2 * (Fintype.card G : ℝ) * (A.card : ℝ) *
                (A.card * (Fintype.card G) ^ (K - 1) : ℕ)
            + ((Finset.univ : Finset (Fin K → G)).card : ℝ) * (A.card : ℝ) ^ 2
          =
          ((Finset.univ : Finset (Fin K → G)).card : ℝ) *
            (A.card : ℝ) * (Fintype.card G : ℝ) := by
        rw [hOmega_card]
        let n : ℕ := Fintype.card G
        let q : ℕ := A.card
        change
          ((n : ℝ) ^ 2 * ((q * n ^ (K - 1) + q * q * n ^ (K - 2) : ℕ) : ℝ)
              - 2 * (n : ℝ) * (q : ℝ) * ((q * n ^ (K - 1) : ℕ) : ℝ)
              + ((n ^ K : ℕ) : ℝ) * (q : ℝ) ^ 2) =
            ((n ^ K : ℕ) : ℝ) * (q : ℝ) * (n : ℝ)
        have hk1 : K - 1 = (K - 2) + 1 := by omega
        have hk2 : K = (K - 2) + 2 := by omega
        rw [hk1, hk2]
        norm_num [pow_add, pow_succ, pow_two]
        ring
      nlinarith [hmul, halg]
    have hscaled_sq :
        (bad.card : ℝ) * (A.card : ℝ) ^ 2 ≤
          ((Finset.univ : Finset (Fin K → G)).card : ℝ) *
            (A.card : ℝ) * (Fintype.card G : ℝ) :=
      le_trans hbad_lower hsumD_le
    have hscaled :
        (bad.card : ℝ) * (A.card : ℝ) ≤
          ((Finset.univ : Finset (Fin K → G)).card : ℝ) * (Fintype.card G : ℝ) := by
      exact le_of_mul_le_mul_right (by nlinarith [hscaled_sq]) hA_pos_real
    have hbad_le :
        (bad.card : ℝ) ≤
          ((Finset.univ : Finset (Fin K → G)).card : ℝ) *
            (Fintype.card G : ℝ) / (A.card : ℝ) :=
      (le_div_iff₀ hA_pos_real).2 hscaled
    simpa [bad, hOmega_card, hA_card_real, mul_comm, mul_left_comm, mul_assoc] using hbad_le
  · have hK_eq : K = 1 := by omega
    subst K
    have hbad_le_univ :
        (bad.card : ℝ) ≤ (Fintype.card G : ℝ) := by
      have hbad_le_nat : bad.card ≤ (Finset.univ : Finset (Fin 1 → G)).card :=
        Finset.card_le_univ _
      rw [hOmega_card] at hbad_le_nat
      simpa using (by exact_mod_cast hbad_le_nat : (bad.card : ℝ) ≤ ((Fintype.card G) ^ 1 : ℕ))
    have hN_ge_one : (1 : ℝ) ≤ (Fintype.card G : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := G)
    have hN_le_sq : (Fintype.card G : ℝ) ≤ (Fintype.card G : ℝ) * (Fintype.card G : ℝ) := by
      nlinarith [hN_ge_one]
    calc
      (Finset.univ.filter
          (fun g : Fin 1 → G =>
            ∀ S : Finset (Fin 1), S.Nonempty → subsetProd S g ≠ 1)).card
          ≤ (Fintype.card G : ℝ) := by simpa [bad] using hbad_le_univ
      _ ≤ (Fintype.card G : ℝ) * (Fintype.card G : ℝ) ^ 1 / ((2 : ℝ) ^ 1 - 1) := by
        norm_num [pow_one]
        exact hN_le_sq

/-- **Near-uniformity remark (Remark 5.2).**

If the `g_i` are not exactly uniform but only `ε`-close in total
variation (jointly), then the conclusion of `subset_product_main` holds
with an additive error `K · ε`.

Proof: decompose
`∑_{g ∈ bad} μ(g) = ∑_{g ∈ bad} (μ(g) - u) + ∑_{g ∈ bad} u`
where `u = 1 / N^K`.  The first sum is bounded by `∑_g |μ(g) - u| ≤ K·ε`
by hypothesis.  The second sum equals `bad.card / N^K`, which by
`subset_product_main` is at most `N / (2^K - 1)`. -/
theorem subset_product_near_uniform
    {K : ℕ} (hK : 1 ≤ K) (ε : ℝ) (_hε : 0 ≤ ε) :
    ∀ (μ : (Fin K → G) → ℝ),
      (∀ g, 0 ≤ μ g) →
      (∑ g : Fin K → G, μ g) = 1 →
      (∑ g : Fin K → G,
         |μ g - 1 / ((Fintype.card G : ℝ) ^ K)|) ≤ (K : ℝ) * ε →
      (∑ g ∈ Finset.univ.filter
          (fun g : Fin K → G =>
            ∀ S : Finset (Fin K), S.Nonempty → subsetProd S g ≠ 1),
         μ g) ≤
        (Fintype.card G : ℝ) / ((2 : ℝ) ^ K - 1) + (K : ℝ) * ε := by
  intro μ _hμ_nn _hμ_sum hTV
  set bad := Finset.univ.filter
      (fun g : Fin K → G =>
        ∀ S : Finset (Fin K), S.Nonempty → subsetProd S g ≠ 1) with hbad_def
  set u : ℝ := 1 / ((Fintype.card G : ℝ) ^ K) with hu_def
  -- Decomposition: ∑_{g ∈ bad} μ(g) = ∑_{g ∈ bad} (μ(g) - u) + ∑_{g ∈ bad} u
  have decomp : (∑ g ∈ bad, μ g) = (∑ g ∈ bad, (μ g - u)) + (∑ g ∈ bad, u) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros g _
    ring
  rw [decomp]
  -- Bound 1: ∑_{g ∈ bad} (μ(g) - u) ≤ ∑_{g ∈ bad} |μ(g) - u| ≤ ∑_g |μ(g) - u| ≤ K·ε
  have diff_bound : ∑ g ∈ bad, (μ g - u) ≤ (K : ℝ) * ε := by
    have h1 : ∀ g ∈ bad, (μ g - u) ≤ |μ g - u| := fun g _ => le_abs_self _
    have h2 : (∑ g ∈ bad, (μ g - u)) ≤ ∑ g ∈ bad, |μ g - u| :=
      Finset.sum_le_sum h1
    have h3 : (∑ g ∈ bad, |μ g - u|) ≤ ∑ g, |μ g - u| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun g _ _ => abs_nonneg _)
    linarith
  -- Bound 2: ∑_{g ∈ bad} u = bad.card * u ≤ N / (2^K - 1)
  have uniform_bound : ∑ g ∈ bad, u ≤ (Fintype.card G : ℝ) / ((2 : ℝ) ^ K - 1) := by
    -- ∑_{g ∈ bad} u = bad.card * u, then use subset_product_main + algebra.
    simp only [Finset.sum_const, nsmul_eq_mul, hu_def]
    -- Goal now: (bad.card : ℝ) * (1 / N^K) ≤ N / (2^K - 1)
    have h_main := subset_product_main (G := G) hK
    -- h_main : (Finset.univ.filter ...).card : ℝ ≤ N * N^K / (2^K - 1)
    have hN_pow_pos : (0 : ℝ) < (Fintype.card G : ℝ) ^ K :=
      pow_pos (by exact_mod_cast Fintype.card_pos) K
    have h2K_pos : (0 : ℝ) < (2 : ℝ) ^ K - 1 := by
      have h2K_ge : (2 : ℝ) ≤ 2 ^ K := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
          _ ≤ 2 ^ K := pow_le_pow_right₀ one_le_two hK
      linarith
    -- (bad.card : ℝ) * (1 / N^K) = bad.card / N^K
    rw [show ((bad.card : ℝ) * (1 / (Fintype.card G : ℝ) ^ K)) =
        (bad.card : ℝ) / (Fintype.card G : ℝ) ^ K from by ring]
    rw [div_le_div_iff₀ hN_pow_pos h2K_pos]
    -- After cross-multiplication: bad.card * (2^K - 1) ≤ N * N^K
    have h_main_bad :
        (bad.card : ℝ) ≤
          (Fintype.card G : ℝ) * (Fintype.card G : ℝ) ^ K / ((2 : ℝ) ^ K - 1) := by
      simpa [bad] using h_main
    exact (le_div_iff₀ h2K_pos).1 h_main_bad
  linarith

end Erdos696
