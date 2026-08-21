/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos88.SignedSliceConcentration

/-!
# Concentration for a dependent family of finite slices

The buckets in the conditional half of KSSS Lemma 11.2 are the random
complements `I k \ R k`.  They are not the fibers of a fixed partition of
the original coordinate type.  This module gives the same exact
permutation concentration theorem directly for an arbitrary finite family
of ambient finsets.
-/

open scoped BigOperators

namespace Erdos88
namespace BooleanSlices

open Classical Finset

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A dependent product of signed slices with arbitrary ambient finsets. -/
abbrev SignedSliceFamilyPoint {K : ℕ} (I : Fin K → Finset α)
    (plus minus : Fin K → ℕ) :=
  ∀ k, SignedSlicePoint (I k) (plus k) (minus k)

/-- Independent permutation samplers for an arbitrary family of finsets. -/
abbrev SignedSliceFamilySampler {K : ℕ} (I : Fin K → Finset α) :=
  ∀ k, Equiv.Perm (Fin (I k).card)

lemma signedSliceFamilyPoint_nonempty {K : ℕ} (I : Fin K → Finset α)
    (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card) :
    Nonempty (SignedSliceFamilyPoint I plus minus) := by
  exact ⟨fun k ↦ Classical.choice (signedSlicePoint_nonempty (hcount k))⟩

/-- Coordinatewise explicit permutation decoder. -/
noncomputable def signedSliceFamilyDecode {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (σ : SignedSliceFamilySampler I) :
    SignedSliceFamilyPoint I plus minus :=
  fun k ↦ signedSliceDecode (I k) (plus k) (minus k)
    (hcount k) (e k) (σ k)

/-- Fibers of the family decoder split coordinatewise. -/
noncomputable def signedSliceFamilyDecodeFiberEquiv {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (S : SignedSliceFamilyPoint I plus minus) :
    {σ : SignedSliceFamilySampler I //
      signedSliceFamilyDecode I plus minus hcount e σ = S} ≃
      ∀ k, {τ : Equiv.Perm (Fin (I k).card) //
        signedSliceDecode (I k) (plus k) (minus k)
          (hcount k) (e k) τ = S k} where
  toFun σ k := ⟨σ.1 k, by
    have hk := congrArg
      (fun T : SignedSliceFamilyPoint I plus minus ↦ T k) σ.2
    exact hk⟩
  invFun τ := ⟨fun k ↦ (τ k).1, by
    funext k
    exact (τ k).2⟩
  left_inv σ := by
    apply Subtype.ext
    funext k
    rfl
  right_inv τ := by
    funext k
    apply Subtype.ext
    rfl

/-- The explicit common fiber factor of the family decoder. -/
def signedSliceFamilyFiberFactor {K : ℕ} (I : Fin K → Finset α)
    (plus minus : Fin K → ℕ) : ℕ :=
  ∏ k, (plus k).factorial * (minus k).factorial *
    ((I k).card - plus k - minus k).factorial

lemma signedSliceFamilyFiberFactor_pos {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ) :
    0 < signedSliceFamilyFiberFactor I plus minus := by
  apply Finset.prod_pos
  intro k _
  positivity

lemma card_signedSliceFamilyDecode_fiber {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (S : SignedSliceFamilyPoint I plus minus) :
    Nat.card {σ : SignedSliceFamilySampler I //
        signedSliceFamilyDecode I plus minus hcount e σ = S} =
      signedSliceFamilyFiberFactor I plus minus := by
  rw [Nat.card_congr
      (signedSliceFamilyDecodeFiberEquiv I plus minus hcount e S),
    Nat.card_pi]
  apply Finset.prod_congr rfl
  intro k _
  exact card_signedSliceDecode_fiber (I k) (plus k) (minus k)
    (hcount k) (e k) (S k)

/-- Exact uniform expectation pushforward for the family decoder. -/
lemma uniformExpectation_signedSliceFamilyDecode {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (g : SignedSliceFamilyPoint I plus minus → ℝ) :
    letI : Nonempty (SignedSliceFamilyPoint I plus minus) :=
      signedSliceFamilyPoint_nonempty I plus minus hcount
    Concentration.uniformExpectation
        (fun σ ↦ g (signedSliceFamilyDecode I plus minus hcount e σ)) =
      Concentration.uniformExpectation g := by
  letI : Nonempty (SignedSliceFamilyPoint I plus minus) :=
    signedSliceFamilyPoint_nonempty I plus minus hcount
  exact uniformExpectation_comp_of_card_fiber
    (signedSliceFamilyDecode I plus minus hcount e)
    (signedSliceFamilyFiberFactor I plus minus)
    (signedSliceFamilyFiberFactor_pos I plus minus)
    (card_signedSliceFamilyDecode_fiber I plus minus hcount e) g

/-- Exact uniform event-probability pushforward for the family decoder. -/
lemma uniformProbability_signedSliceFamilyDecode {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (Q : SignedSliceFamilyPoint I plus minus → Prop) :
    letI : Nonempty (SignedSliceFamilyPoint I plus minus) :=
      signedSliceFamilyPoint_nonempty I plus minus hcount
    Concentration.uniformProbability
        (fun σ ↦ Q (signedSliceFamilyDecode I plus minus hcount e σ)) =
      Concentration.uniformProbability Q := by
  letI : Nonempty (SignedSliceFamilyPoint I plus minus) :=
    signedSliceFamilyPoint_nonempty I plus minus hcount
  exact uniformProbability_comp_of_card_fiber
    (signedSliceFamilyDecode I plus minus hcount e)
    (signedSliceFamilyFiberFactor I plus minus)
    (signedSliceFamilyFiberFactor_pos I plus minus)
    (card_signedSliceFamilyDecode_fiber I plus minus hcount e) Q

/-- A legal switch in one member of a family of signed slices. -/
def IsSignedSliceFamilySwitch {K : ℕ} (I : Fin K → Finset α)
    {plus minus : Fin K → ℕ}
    (S T : SignedSliceFamilyPoint I plus minus) : Prop :=
  ∃ (k : Fin K) (p q : α), p ∈ I k ∧ q ∈ I k ∧ p ≠ q ∧
    ∀ j v, signedSliceValue (T j) v =
      if j = k then
        if v = p then signedSliceValue (S k) q
        else if v = q then signedSliceValue (S k) p
        else signedSliceValue (S k) v
      else signedSliceValue (S j) v

/-- The family decoder only depends on the prescribed prefixes. -/
lemma signedSliceFamilyDecode_eq_of_prefix {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (σ τ : SignedSliceFamilySampler I)
    (hστ : ∀ k (i : Fin (plus k + minus k)),
      σ k (Fin.castLE (hcount k) i) =
        τ k (Fin.castLE (hcount k) i)) :
    signedSliceFamilyDecode I plus minus hcount e σ =
      signedSliceFamilyDecode I plus minus hcount e τ := by
  funext k
  exact signedSliceDecode_eq_of_prefix (I k) (plus k) (minus k)
    (hcount k) (e k) (σ k) (τ k) (hστ k)

/-- Left-transposing one family permutation either changes nothing or gives
one legal family switch. -/
lemma signedSliceFamilyDecode_left_swap {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (σ τ : SignedSliceFamilySampler I) (k : Fin K)
    (p q : Fin (I k).card)
    (hk : τ k = Equiv.swap p q * σ k)
    (hsame : ∀ j, j ≠ k → τ j = σ j) :
    signedSliceFamilyDecode I plus minus hcount e τ =
        signedSliceFamilyDecode I plus minus hcount e σ ∨
      IsSignedSliceFamilySwitch I
        (signedSliceFamilyDecode I plus minus hcount e σ)
        (signedSliceFamilyDecode I plus minus hcount e τ) := by
  classical
  by_cases hpq : p = q
  · left
    apply congrArg (signedSliceFamilyDecode I plus minus hcount e)
    funext j
    by_cases hj : j = k
    · subst j
      rw [hpq, Equiv.swap_self] at hk
      exact hk.trans (by ext x; rfl)
    · exact hsame j hj
  · right
    let x : α := (e k p).1
    let y : α := (e k q).1
    have hx : x ∈ I k := (e k p).2
    have hy : y ∈ I k := (e k q).2
    have hxy : x ≠ y := by
      intro hxy
      apply hpq
      apply (e k).injective
      apply Subtype.ext
      exact hxy
    refine ⟨k, x, y, hx, hy, hxy, ?_⟩
    intro j v
    by_cases hj : j = k
    · subst j
      simp only [signedSliceFamilyDecode]
      rw [hk, signedSliceValue_decode_left_swap]
      by_cases hvx : v = x
      · subst v
        simp [x, y, hxy]
      · by_cases hvy : v = y
        · subst v
          simp [x, y, hxy, hxy.symm]
        · rw [Equiv.swap_apply_of_ne_of_ne hvx hvy]
          simp [x, y, hvx, hvy]
    · simp only [signedSliceFamilyDecode]
      rw [hsame j hj]
      simp [hj]

/-- Exact KSSS Lemma 4.17 for an arbitrary dependent family of finite
signed slices. -/
theorem signedSliceFamily_two_sided_probability {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (f : SignedSliceFamilyPoint I plus minus → ℝ) (a t : ℝ)
    (hL : 0 < ∑ k : Fin K, (plus k + minus k : ℕ))
    (ha : 0 < a) (ht : 0 ≤ t)
    (hlip : ∀ S T, IsSignedSliceFamilySwitch I S T →
      |f S - f T| ≤ a) :
    letI : Nonempty (SignedSliceFamilyPoint I plus minus) :=
      signedSliceFamilyPoint_nonempty I plus minus hcount
    Concentration.uniformProbability (fun S ↦
        t ≤ |f S - Concentration.uniformExpectation f|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 *
          (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * a ^ 2)) := by
  letI : Nonempty (SignedSliceFamilyPoint I plus minus) :=
    signedSliceFamilyPoint_nonempty I plus minus hcount
  let decode : SignedSliceFamilySampler I →
      SignedSliceFamilyPoint I plus minus :=
    signedSliceFamilyDecode I plus minus hcount e
  let G : SignedSliceFamilySampler I → ℝ := fun σ ↦ f (decode σ)
  have hprefix : FiniteSliceConcentration.PermutationProductPrefixDependent
      hcount G := by
    intro σ τ hστ
    dsimp only [G, decode]
    rw [signedSliceFamilyDecode_eq_of_prefix I plus minus hcount e σ τ hστ]
  have hswitch : FiniteSliceConcentration.PermutationProductSwitchLipschitz
      G a := by
    intro σ τ k p q hk hsame
    rcases signedSliceFamilyDecode_left_swap I plus minus hcount e
        σ τ k p q hk hsame with heq | hsw
    · dsimp only [G, decode]
      rw [heq]
      simpa using ha.le
    · exact hlip _ _ hsw
  have hmean : Concentration.uniformExpectation G =
      Concentration.uniformExpectation f :=
    uniformExpectation_signedSliceFamilyDecode I plus minus hcount e f
  have htail := FiniteSliceConcentration.permutationProduct_two_sided_probability
    hcount G a t hL ha ht hprefix hswitch
  rw [hmean] at htail
  let Q : SignedSliceFamilyPoint I plus minus → Prop := fun S ↦
    t ≤ |f S - Concentration.uniformExpectation f|
  calc
    Concentration.uniformProbability Q =
        Concentration.uniformProbability (fun σ ↦ Q (decode σ)) := by
      symm
      exact uniformProbability_signedSliceFamilyDecode
        I plus minus hcount e Q
    _ ≤ 2 * Real.exp
        (-t ^ 2 / (2 *
          (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * a ^ 2)) := by
      simpa only [Nat.cast_sum] using htail

/-! ### Linear forms on full-support signed slices -/

/-- A linear form on a family of signed slices. -/
noncomputable def signedSliceFamilyLinear {K : ℕ}
    (I : Fin K → Finset α) {plus minus : Fin K → ℕ}
    (c : Fin K → α → ℝ) (S : SignedSliceFamilyPoint I plus minus) : ℝ :=
  ∑ k, ∑ i ∈ I k, c k i * signedSliceValue (S k) i

/-- A one-bucket family switch changes a bounded linear form by at most
`4C`.  The factor four is the two switched signs, each moving by at most
two. -/
lemma abs_signedSliceFamilyLinear_sub_le {K : ℕ}
    (I : Fin K → Finset α) {plus minus : Fin K → ℕ}
    (c : Fin K → α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ k i, |c k i| ≤ C)
    {S T : SignedSliceFamilyPoint I plus minus}
    (hST : IsSignedSliceFamilySwitch I S T) :
    |signedSliceFamilyLinear I c S - signedSliceFamilyLinear I c T| ≤
      4 * C := by
  obtain ⟨k, p, q, hp, hq, hpq, hswap⟩ := hST
  rw [signedSliceFamilyLinear, signedSliceFamilyLinear,
    ← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin K,
        ((∑ i ∈ I j, c j i * signedSliceValue (S j) i) -
          ∑ i ∈ I j, c j i * signedSliceValue (T j) i)| ≤
        ∑ j : Fin K,
          |(∑ i ∈ I j, c j i * signedSliceValue (S j) i) -
            ∑ i ∈ I j, c j i * signedSliceValue (T j) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin K, if j = k then 4 * C else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = k
      · subst j
        simp only [if_true]
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ i ∈ I k,
              (c k i * signedSliceValue (S k) i -
                c k i * signedSliceValue (T k) i)| ≤
              ∑ i ∈ I k,
                |c k i * signedSliceValue (S k) i -
                  c k i * signedSliceValue (T k) i| := by
            exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ I k, if i = p ∨ i = q then 2 * C else 0 := by
            apply Finset.sum_le_sum
            intro i hi
            by_cases hip : i = p
            · subst i
              simp only [true_or, if_true]
              rw [hswap k p, if_pos rfl, if_pos rfl]
              calc
                |c k p * signedSliceValue (S k) p -
                    c k p * signedSliceValue (S k) q| =
                    |c k p| * |signedSliceValue (S k) p -
                      signedSliceValue (S k) q| := by
                  rw [← mul_sub, abs_mul]
                _ ≤ C * (1 + 1) := by
                  exact mul_le_mul (hc k p)
                    ((abs_sub _ _).trans (add_le_add
                      (abs_signedSliceValue_le_one (S k) p)
                      (abs_signedSliceValue_le_one (S k) q)))
                    (abs_nonneg _) hC
                _ = 2 * C := by ring
            · by_cases hiq : i = q
              · subst i
                simp only [hip, or_true, if_true]
                rw [hswap k q, if_pos rfl, if_neg hpq.symm, if_pos rfl]
                calc
                  |c k q * signedSliceValue (S k) q -
                      c k q * signedSliceValue (S k) p| =
                      |c k q| * |signedSliceValue (S k) q -
                        signedSliceValue (S k) p| := by
                    rw [← mul_sub, abs_mul]
                  _ ≤ C * (1 + 1) := by
                    exact mul_le_mul (hc k q)
                      ((abs_sub _ _).trans (add_le_add
                        (abs_signedSliceValue_le_one (S k) q)
                        (abs_signedSliceValue_le_one (S k) p)))
                      (abs_nonneg _) hC
                  _ = 2 * C := by ring
              · simp only [hip, hiq, or_false, if_false]
                rw [hswap k i, if_pos rfl, if_neg hip, if_neg hiq,
                  sub_self, abs_zero]
          _ = 4 * C := by
            rw [Finset.sum_ite]
            have hfilter : (I k).filter (fun i ↦ i = p ∨ i = q) = {p, q} := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_insert,
                Finset.mem_singleton]
              constructor
              · exact fun hi ↦ hi.2
              · intro hi
                exact ⟨hi.elim (fun h ↦ h ▸ hp) (fun h ↦ h ▸ hq), hi⟩
            rw [hfilter]
            simp [hpq]
            ring
      · have heq : (∑ i ∈ I j, c j i * signedSliceValue (S j) i) =
            ∑ i ∈ I j, c j i * signedSliceValue (T j) i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hswap j i, if_neg hj]
        rw [heq, sub_self, abs_zero, if_neg hj]
    _ = 4 * C := by simp

/-- The resulting exact two-sided tail for bounded linear forms on an
arbitrary family of signed slices. -/
theorem signedSliceFamilyLinear_two_sided_probability {K : ℕ}
    (I : Fin K → Finset α) (plus minus : Fin K → ℕ)
    (hcount : ∀ k, plus k + minus k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (c : Fin K → α → ℝ) (C t : ℝ)
    (hL : 0 < ∑ k : Fin K, (plus k + minus k : ℕ))
    (hC : 0 < C) (ht : 0 ≤ t)
    (hc : ∀ k i, |c k i| ≤ C) :
    letI : Nonempty (SignedSliceFamilyPoint I plus minus) :=
      signedSliceFamilyPoint_nonempty I plus minus hcount
    Concentration.uniformProbability
        (fun S : SignedSliceFamilyPoint I plus minus ↦
          t ≤ |signedSliceFamilyLinear (plus := plus) (minus := minus) I c S -
            Concentration.uniformExpectation
              (signedSliceFamilyLinear (plus := plus) (minus := minus) I c)|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 *
          (∑ k : Fin K, ((plus k + minus k : ℕ) : ℝ)) * (4 * C) ^ 2)) := by
  apply signedSliceFamily_two_sided_probability
    I plus minus hcount e
      (signedSliceFamilyLinear (plus := plus) (minus := minus) I c)
      (4 * C) t
      hL (mul_pos (by norm_num) hC) ht
  intro S T hST
  exact abs_signedSliceFamilyLinear_sub_le I c C hC.le hc hST

/-! ### Boolean full-support specialization -/

/-- A dependent product of ordinary Boolean slices with arbitrary ambient
finsets. -/
abbrev BooleanSliceFamilyPoint {K : ℕ} (I : Fin K → Finset α)
    (ell : Fin K → ℕ) :=
  ∀ k, BooleanSlicePoint (I k) (ell k)

lemma booleanSliceFamilyPoint_nonempty {K : ℕ}
    (I : Fin K → Finset α) (ell : Fin K → ℕ)
    (hell : ∀ k, ell k ≤ (I k).card) :
    Nonempty (BooleanSliceFamilyPoint I ell) := by
  exact ⟨fun k ↦ Classical.choice (booleanSlicePoint_nonempty (hell k))⟩

/-- A full-support signed slice is exactly an ordinary Boolean slice: its
negative support is the complement of its positive support. -/
noncomputable def fullSignedSliceEquiv (I : Finset α) (ell : ℕ)
    (hell : ell ≤ I.card) :
    SignedSlicePoint I ell (I.card - ell) ≃ BooleanSlicePoint I ell where
  toFun S := ⟨S.1.1, mem_booleanSlice.mpr ⟨
    (mem_signedSlice.mp S.2).1,
    (mem_signedSlice.mp S.2).2.2.2.1⟩⟩
  invFun S := ⟨(S.1, I \ S.1), mem_signedSlice.mpr ⟨
    (mem_booleanSlice.mp S.2).1, Finset.sdiff_subset,
    Finset.disjoint_sdiff, (mem_booleanSlice.mp S.2).2, by
      rw [Finset.card_sdiff_of_subset (mem_booleanSlice.mp S.2).1,
        (mem_booleanSlice.mp S.2).2]⟩⟩
  left_inv S := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hP := (mem_signedSlice.mp S.2).1
      have hN := (mem_signedSlice.mp S.2).2.1
      have hPN := (mem_signedSlice.mp S.2).2.2.1
      have hPcard := (mem_signedSlice.mp S.2).2.2.2.1
      have hNcard := (mem_signedSlice.mp S.2).2.2.2.2
      have hunion : S.1.1 ∪ S.1.2 = I := by
        apply Finset.eq_of_subset_of_card_le (Finset.union_subset hP hN)
        rw [Finset.card_union_of_disjoint hPN, hPcard, hNcard,
          Nat.add_sub_of_le hell]
      ext i
      constructor
      · intro hi
        rcases Finset.mem_sdiff.mp hi with ⟨hiI, hiP⟩
        have hiU : i ∈ S.1.1 ∪ S.1.2 := by simpa [hunion] using hiI
        exact (Finset.mem_union.mp hiU).resolve_left hiP
      · intro hiN
        exact Finset.mem_sdiff.mpr ⟨hN hiN,
          fun hiP ↦ Finset.disjoint_left.mp hPN hiP hiN⟩
  right_inv S := by
    apply Subtype.ext
    rfl

/-- Coordinatewise full-support equivalence. -/
noncomputable def fullSignedSliceFamilyEquiv {K : ℕ}
    (I : Fin K → Finset α) (ell : Fin K → ℕ)
    (hell : ∀ k, ell k ≤ (I k).card) :
    SignedSliceFamilyPoint I ell (fun k ↦ (I k).card - ell k) ≃
      BooleanSliceFamilyPoint I ell :=
  Equiv.piCongrRight fun k ↦ fullSignedSliceEquiv (I k) (ell k) (hell k)

/-- Linear form in the usual `{-1,1}` encoding of Boolean slices. -/
noncomputable def booleanSliceFamilyLinearOfCounts {K : ℕ}
    (I : Fin K → Finset α) {ell : Fin K → ℕ}
    (c : Fin K → α → ℝ) (S : BooleanSliceFamilyPoint I ell) : ℝ :=
  ∑ k, ∑ i ∈ I k, c k i * signOfSet (S k).1 i

lemma signedLinear_fullSignedSliceFamilyEquiv_symm {K : ℕ}
    (I : Fin K → Finset α) (ell : Fin K → ℕ)
    (hell : ∀ k, ell k ≤ (I k).card)
    (c : Fin K → α → ℝ) (S : BooleanSliceFamilyPoint I ell) :
    signedSliceFamilyLinear
        (plus := ell) (minus := fun k ↦ (I k).card - ell k) I c
        ((fullSignedSliceFamilyEquiv I ell hell).symm S) =
      booleanSliceFamilyLinearOfCounts I c S := by
  unfold signedSliceFamilyLinear booleanSliceFamilyLinearOfCounts
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i hi
  change c k i *
      (if i ∈ (S k).1 then 1 else if i ∈ I k \ (S k).1 then -1 else 0) =
    c k i * (if i ∈ (S k).1 then 1 else -1)
  by_cases hiS : i ∈ (S k).1 <;> simp [hiS, hi]

private lemma uniformProbability_comp_equiv_family {Ω Ω' : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Ω'] [Nonempty Ω']
    (E : Ω ≃ Ω') (Q : Ω' → Prop) :
    Concentration.uniformProbability (fun ω ↦ Q (E ω)) =
      Concentration.uniformProbability Q := by
  classical
  have h : (𝔼 ω : Ω, if Q (E ω) then (1 : ℝ) else 0) =
      𝔼 τ : Ω', if Q τ then (1 : ℝ) else 0 := by
    apply Fintype.expect_equiv E
    intro ω
    rfl
  simpa [Concentration.uniformProbability, Fintype.expect_eq_sum_div_card,
    Finset.sum_ite] using h

/-- Exact two-sided concentration for bounded linear forms on an arbitrary
family of Boolean slices. -/
theorem booleanSliceFamilyLinear_two_sided_probability {K : ℕ}
    (I : Fin K → Finset α) (ell : Fin K → ℕ)
    (hell : ∀ k, ell k ≤ (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (c : Fin K → α → ℝ) (C t : ℝ)
    (hL : 0 < ∑ k : Fin K, (I k).card)
    (hC : 0 < C) (ht : 0 ≤ t)
    (hc : ∀ k i, |c k i| ≤ C) :
    letI : Nonempty (BooleanSliceFamilyPoint I ell) :=
      booleanSliceFamilyPoint_nonempty I ell hell
    Concentration.uniformProbability
        (fun S : BooleanSliceFamilyPoint I ell ↦
          t ≤ |booleanSliceFamilyLinearOfCounts (ell := ell) I c S -
            Concentration.uniformExpectation
              (booleanSliceFamilyLinearOfCounts (ell := ell) I c)|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 * (∑ k : Fin K, ((I k).card : ℝ)) *
          (4 * C) ^ 2)) := by
  let minus : Fin K → ℕ := fun k ↦ (I k).card - ell k
  have hcount : ∀ k, ell k + minus k ≤ (I k).card := by
    intro k
    dsimp only [minus]
    rw [Nat.add_sub_of_le (hell k)]
  letI : Nonempty (SignedSliceFamilyPoint I ell minus) :=
    signedSliceFamilyPoint_nonempty I ell minus hcount
  letI : Nonempty (BooleanSliceFamilyPoint I ell) :=
    booleanSliceFamilyPoint_nonempty I ell hell
  let E := fullSignedSliceFamilyEquiv I ell hell
  let fs : SignedSliceFamilyPoint I ell minus → ℝ :=
    signedSliceFamilyLinear I c
  let fb : BooleanSliceFamilyPoint I ell → ℝ :=
    booleanSliceFamilyLinearOfCounts (ell := ell) I c
  have hE (S : BooleanSliceFamilyPoint I ell) : fs (E.symm S) = fb S := by
    exact signedLinear_fullSignedSliceFamilyEquiv_symm I ell hell c S
  have hmean : Concentration.uniformExpectation fs =
      Concentration.uniformExpectation fb := by
    unfold Concentration.uniformExpectation
    rw [Fintype.card_congr E]
    congr 1
    calc
      ∑ S, fs S = ∑ S, fb (E S) := by
        apply Finset.sum_congr rfl
        intro S _
        have h := hE (E S)
        simpa using h
      _ = ∑ T, fb T := E.sum_comp fb
  have hsum : (∑ k : Fin K,
      (((ell k + minus k : ℕ)) : ℝ)) =
        ∑ k : Fin K, ((I k).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [minus]
    rw [Nat.add_sub_of_le (hell k)]
  have hsumNat : (∑ k : Fin K, (ell k + minus k)) =
      ∑ k : Fin K, (I k).card := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [minus]
    rw [Nat.add_sub_of_le (hell k)]
  have htail := signedSliceFamilyLinear_two_sided_probability
    I ell minus hcount e c C t
      (by rw [hsumNat]; exact hL) hC ht hc
  change Concentration.uniformProbability (fun S ↦
      t ≤ |fs S - Concentration.uniformExpectation fs|) ≤ _ at htail
  rw [hmean] at htail
  let Q : BooleanSliceFamilyPoint I ell → Prop := fun S ↦
    t ≤ |fb S - Concentration.uniformExpectation fb|
  have hforward (S : SignedSliceFamilyPoint I ell minus) :
      fs S = fb (E S) := by
    have h := hE (E S)
    simpa using h
  have hevent : (fun S : SignedSliceFamilyPoint I ell minus ↦ Q (E S)) =
      (fun S ↦ t ≤ |fs S - Concentration.uniformExpectation fb|) := by
    funext S
    simp only [Q]
    rw [hforward]
  calc
    Concentration.uniformProbability Q =
        Concentration.uniformProbability (fun S ↦ Q (E S)) := by
      symm
      exact uniformProbability_comp_equiv_family E Q
    _ ≤ 2 * Real.exp
        (-t ^ 2 / (2 * (∑ k : Fin K, ((I k).card : ℝ)) *
          (4 * C) ^ 2)) := by
      rw [hevent]
      simpa only [hsum] using htail

/-- Complementation preserves a balanced Boolean slice. -/
noncomputable def balancedBooleanSliceComplementEquiv (I : Finset α)
    (ell : ℕ) (hbal : 2 * ell = I.card) :
    BooleanSlicePoint I ell ≃ BooleanSlicePoint I ell where
  toFun S := ⟨I \ S.1, mem_booleanSlice.mpr ⟨Finset.sdiff_subset, by
    rw [Finset.card_sdiff_of_subset (mem_booleanSlice.mp S.2).1,
      (mem_booleanSlice.mp S.2).2]
    omega⟩⟩
  invFun S := ⟨I \ S.1, mem_booleanSlice.mpr ⟨Finset.sdiff_subset, by
    rw [Finset.card_sdiff_of_subset (mem_booleanSlice.mp S.2).1,
      (mem_booleanSlice.mp S.2).2]
    omega⟩⟩
  left_inv S := by
    apply Subtype.ext
    change I \ (I \ S.1) = S.1
    rw [Finset.sdiff_sdiff_eq_self (mem_booleanSlice.mp S.2).1]
  right_inv S := by
    apply Subtype.ext
    change I \ (I \ S.1) = S.1
    rw [Finset.sdiff_sdiff_eq_self (mem_booleanSlice.mp S.2).1]

/-- Coordinatewise complementation of a family of balanced slices. -/
noncomputable def balancedBooleanSliceFamilyComplementEquiv {K : ℕ}
    (I : Fin K → Finset α) (ell : Fin K → ℕ)
    (hbal : ∀ k, 2 * ell k = (I k).card) :
    BooleanSliceFamilyPoint I ell ≃ BooleanSliceFamilyPoint I ell :=
  Equiv.piCongrRight fun k ↦
    balancedBooleanSliceComplementEquiv (I k) (ell k) (hbal k)

lemma booleanSliceFamilyLinear_complement {K : ℕ}
    (I : Fin K → Finset α) (ell : Fin K → ℕ)
    (hbal : ∀ k, 2 * ell k = (I k).card)
    (c : Fin K → α → ℝ) (S : BooleanSliceFamilyPoint I ell) :
    booleanSliceFamilyLinearOfCounts I c
        (balancedBooleanSliceFamilyComplementEquiv I ell hbal S) =
      -booleanSliceFamilyLinearOfCounts I c S := by
  unfold booleanSliceFamilyLinearOfCounts
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change c k i * signOfSet (I k \ (S k).1) i =
    -(c k i * signOfSet (S k).1 i)
  by_cases hiS : i ∈ (S k).1 <;>
    simp [signOfSet, hiS, hi]

/-- Every linear form on a product of balanced slices has mean zero, by the
exact complement involution. -/
lemma uniformExpectation_booleanSliceFamilyLinear_eq_zero {K : ℕ}
    (I : Fin K → Finset α) (ell : Fin K → ℕ)
    (hbal : ∀ k, 2 * ell k = (I k).card)
    (c : Fin K → α → ℝ) :
    Concentration.uniformExpectation
      (booleanSliceFamilyLinearOfCounts (ell := ell) I c) = 0 := by
  let E := balancedBooleanSliceFamilyComplementEquiv I ell hbal
  let f : BooleanSliceFamilyPoint I ell → ℝ :=
    booleanSliceFamilyLinearOfCounts I c
  have hsum : (∑ S, f S) = -(∑ S, f S) := by
    calc
      ∑ S, f S = ∑ S, f (E S) := (E.sum_comp f).symm
      _ = ∑ S, -f S := by
        apply Finset.sum_congr rfl
        intro S _
        exact booleanSliceFamilyLinear_complement I ell hbal c S
      _ = -(∑ S, f S) := by simp
  have hzero : (∑ S, f S) = 0 := by linarith
  rw [Concentration.uniformExpectation, hzero, zero_div]

/-- Balanced specialization of the family linear tail, centered exactly at
zero. -/
theorem balancedBooleanSliceFamilyLinear_two_sided_probability {K : ℕ}
    (I : Fin K → Finset α) (ell : Fin K → ℕ)
    (hbal : ∀ k, 2 * ell k = (I k).card)
    (e : ∀ k, Fin (I k).card ≃ ↑(I k))
    (c : Fin K → α → ℝ) (C t : ℝ)
    (hL : 0 < ∑ k : Fin K, (I k).card)
    (hC : 0 < C) (ht : 0 ≤ t)
    (hc : ∀ k i, |c k i| ≤ C) :
    let hell : ∀ k, ell k ≤ (I k).card := fun k ↦ by
      have := hbal k
      omega
    letI : Nonempty (BooleanSliceFamilyPoint I ell) :=
      booleanSliceFamilyPoint_nonempty I ell hell
    Concentration.uniformProbability
        (fun S : BooleanSliceFamilyPoint I ell ↦
          t ≤ |booleanSliceFamilyLinearOfCounts I c S|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 * (∑ k : Fin K, ((I k).card : ℝ)) *
          (4 * C) ^ 2)) := by
  let hell : ∀ k, ell k ≤ (I k).card := fun k ↦ by
    have := hbal k
    omega
  letI : Nonempty (BooleanSliceFamilyPoint I ell) :=
    booleanSliceFamilyPoint_nonempty I ell hell
  have htail := booleanSliceFamilyLinear_two_sided_probability
    I ell hell e c C t hL hC ht hc
  rw [uniformExpectation_booleanSliceFamilyLinear_eq_zero I ell hbal c] at htail
  simpa only [sub_zero] using htail

end BooleanSlices
end Erdos88
