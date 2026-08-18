/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos13.Erdos13Additive
import ErdosProblems.Erdos1211.External.Erdos587Core.Main
import ErdosProblems.Erdos1211.External.Erdos360.Main
import ErdosProblems.Erdos697.Erdos697Bernoulli

/-!
# Erdős Problem 344

The mathematical proof and the formal dependency map are in `tex/344.tex`.
-/

namespace Erdos344

universe u

open BigOperators Filter Set
open scoped Pointwise Topology

attribute [local instance] Classical.propDecidable
noncomputable local instance (A : Set ℕ) : DecidablePred A := Classical.decPred A

/-- Finite subset sums of a set of natural numbers. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ b ∈ B, b}

/-- The number of members of `A` in the positive initial interval `[1, N]`. -/
noncomputable def counting (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter (· ∈ A)).card

/-- The literal eventual square-root density condition in Problem 344. -/
def SqrtDense (C : ℝ) (A : Set ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, C * Real.sqrt (N : ℝ) ≤ (counting A N : ℝ)

/-- `S` contains a nonconstant finite arithmetic progression of length `k`. -/
def ContainsFiniteAP (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S

/-- `S` contains an infinite arithmetic progression with positive difference. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, a + i * d ∈ S

/-- A set has arbitrarily long finite progressions with one fixed positive
common difference. -/
def HasFixedStepProgressions (S : Set ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ, ∃ a : ℕ, ∀ i < k, a + i * d ∈ S

/-- An additive `q`-net with width `K`: every interval
`[n*q, (n+K)*q]` contains a member of `S` divisible by `q`. -/
def IsAddNet (q K : ℕ) (S : Set ℕ) : Prop :=
  0 < q ∧ ∀ n : ℕ, ∃ s ∈ S, q ∣ s ∧ n * q ≤ s ∧ s ≤ (n + K) * q

lemma sqrtDense_mono_constant {A : Set ℕ} {c C : ℝ} (hcC : c ≤ C)
    (hC : SqrtDense C A) : SqrtDense c A := by
  filter_upwards [hC] with N hN
  have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  exact (mul_le_mul_of_nonneg_right hcC hsqrt).trans hN

lemma subsetSums_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    subsetSums A ⊆ subsetSums B := by
  rintro n ⟨F, hF, rfl⟩
  exact ⟨F, hF.trans hAB, rfl⟩

@[simp] lemma zero_mem_subsetSums (A : Set ℕ) : 0 ∈ subsetSums A := by
  exact ⟨∅, by simp, by simp⟩

lemma singleton_mem_subsetSums {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∈ subsetSums A := by
  exact ⟨{a}, by simpa, by simp⟩

lemma add_mem_subsetSums_of_disjoint {A B : Set ℕ} (hAB : Disjoint A B)
    {x y : ℕ} (hx : x ∈ subsetSums A) (hy : y ∈ subsetSums B) :
    x + y ∈ subsetSums (A ∪ B) := by
  obtain ⟨X, hXA, rfl⟩ := hx
  obtain ⟨Y, hYB, rfl⟩ := hy
  have hXY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro z hzX hzY
    exact Set.disjoint_left.1 hAB (hXA hzX) (hYB hzY)
  refine ⟨X ∪ Y, ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_union] at hz
    exact hz.elim (fun h ↦ Or.inl (hXA h)) (fun h ↦ Or.inr (hYB h))
  · rw [Finset.sum_union hXY]

lemma subsetSums_union_subset_add {A B : Set ℕ} (hAB : Disjoint A B) :
    subsetSums A + subsetSums B ⊆ subsetSums (A ∪ B) := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact add_mem_subsetSums_of_disjoint hAB hx hy

lemma containsFiniteAP_mono {S T : Set ℕ} (hST : S ⊆ T) {k : ℕ}
    (hS : ContainsFiniteAP S k) : ContainsFiniteAP T k := by
  obtain ⟨a, d, hd, h⟩ := hS
  exact ⟨a, d, hd, fun i hi ↦ hST (h i hi)⟩

lemma containsInfiniteAP_mono {S T : Set ℕ} (hST : S ⊆ T)
    (hS : ContainsInfiniteAP S) : ContainsInfiniteAP T := by
  obtain ⟨a, d, hd, h⟩ := hS
  exact ⟨a, d, hd, fun i ↦ hST (h i)⟩

/-! ### Counting and increasing enumerations -/

lemma counting_eq_count {A : Set ℕ} (hApos : A ⊆ Set.Ici 1) (N : ℕ) :
    counting A N = Nat.count (· ∈ A) (N + 1) := by
  classical
  rw [Nat.count_eq_card_filter_range]
  simp only [counting]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨hx1, hxN⟩, hxA⟩
    exact ⟨by omega, hxA⟩
  · rintro ⟨hxN, hxA⟩
    exact ⟨⟨hApos hxA, by omega⟩, hxA⟩

lemma counting_nth {A : Set ℕ} (hApos : A ⊆ Set.Ici 1)
    (hAinf : A.Infinite) (m : ℕ) :
    counting A (Nat.nth (· ∈ A) m) = m + 1 := by
  rw [counting_eq_count hApos]
  exact Nat.count_nth_succ_of_infinite hAinf m

lemma nth_mem {A : Set ℕ} (hAinf : A.Infinite) (m : ℕ) :
    Nat.nth (· ∈ A) m ∈ A := by
  exact Nat.nth_mem_of_infinite hAinf m

lemma nth_strictMono {A : Set ℕ} (hAinf : A.Infinite) :
    StrictMono (Nat.nth (· ∈ A)) := by
  exact Nat.nth_strictMono hAinf

lemma counting_le_ncard {A : Set ℕ} (hAfin : A.Finite) (N : ℕ) :
    counting A N ≤ A.ncard := by
  classical
  rw [counting, Set.ncard_eq_toFinset_card A hAfin]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx
  exact hAfin.mem_toFinset.mpr hx.2

lemma infinite_of_sqrtDense {A : Set ℕ} {C : ℝ} (hC : 0 < C)
    (hdense : SqrtDense C A) : A.Infinite := by
  intro hAfin
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ ↦ C * Real.sqrt (N : ℝ)) atTop atTop :=
    hsqrt.const_mul_atTop hC
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (A.ncard : ℝ) + 1 ≤ C * Real.sqrt (N : ℝ) :=
    hscale.eventually (eventually_ge_atTop ((A.ncard : ℝ) + 1))
  obtain ⟨N, hdenseN, hlargeN⟩ := (hdense.and hlarge).exists
  have hcount : (counting A N : ℝ) ≤ A.ncard := by
    exact_mod_cast counting_le_ncard hAfin N
  linarith

lemma counting_le_counting_sdiff_add_ncard {A F : Set ℕ}
    (hFfin : F.Finite) (N : ℕ) :
    counting A N ≤ counting (A \ F) N + F.ncard := by
  let X := (Finset.Icc 1 N).filter (· ∈ A)
  let Y := (Finset.Icc 1 N).filter (· ∈ A \ F)
  have hsub : X ⊆ Y ∪ hFfin.toFinset := by
    intro x hx
    simp only [X, Y, Finset.mem_filter, Finset.mem_union,
      hFfin.mem_toFinset, Set.mem_sdiff] at hx ⊢
    by_cases hxF : x ∈ F
    · exact Or.inr hxF
    · exact Or.inl ⟨hx.1, hx.2, hxF⟩
  have hcardY : Y.card = counting (A \ F) N := by
    unfold counting
    apply congrArg Finset.card
    ext x
    simp only [Y, Finset.mem_filter, Finset.mem_Icc]
  calc
    counting A N = X.card := rfl
    _ ≤ (Y ∪ hFfin.toFinset).card := Finset.card_le_card hsub
    _ ≤ Y.card + hFfin.toFinset.card := Finset.card_union_le Y hFfin.toFinset
    _ = counting (A \ F) N + F.ncard := by
      rw [hcardY, Set.ncard_eq_toFinset_card F hFfin]

lemma sqrtDense_sdiff_finite {A F : Set ℕ} {c C : ℝ}
    (hcC : c < C) (hFfin : F.Finite) (hdense : SqrtDense C A) :
    SqrtDense c (A \ F) := by
  have hgap : 0 < C - c := sub_pos.mpr hcC
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ ↦ (C - c) * Real.sqrt (N : ℝ))
      atTop atTop := hsqrt.const_mul_atTop hgap
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (F.ncard : ℝ) ≤ (C - c) * Real.sqrt (N : ℝ) :=
    hscale.eventually (eventually_ge_atTop (F.ncard : ℝ))
  filter_upwards [hdense, hlarge] with N hN hlargeN
  have hcountNat := counting_le_counting_sdiff_add_ncard (A := A) hFfin N
  have hcount : (counting A N : ℝ) ≤
      counting (A \ F) N + F.ncard := by exact_mod_cast hcountNat
  nlinarith

/-- The elements in one parity class of their zero-based rank in `A`. -/
def rankPart (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {x ∈ A | Nat.count (· ∈ A) x % 2 = r}

lemma nth_mem_rankPart {A : Set ℕ} (hAinf : A.Infinite) (j : ℕ) :
    Nat.nth (· ∈ A) j ∈ rankPart A (j % 2) := by
  refine ⟨nth_mem hAinf j, ?_⟩
  rw [Nat.count_nth_of_infinite (p := fun x ↦ x ∈ A) hAinf]

lemma rankPart_subset (A : Set ℕ) (r : ℕ) : rankPart A r ⊆ A :=
  fun _ hx ↦ hx.1

lemma rankPart_disjoint (A : Set ℕ) : Disjoint (rankPart A 0) (rankPart A 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hx0⟩ ⟨-, hx1⟩
  omega

lemma rankPart_zero_union_one {A : Set ℕ} :
    rankPart A 0 ∪ rankPart A 1 = A := by
  ext x
  constructor
  · rintro (hx | hx) <;> exact hx.1
  · intro hx
    have hmod : Nat.count (· ∈ A) x % 2 = 0 ∨ Nat.count (· ∈ A) x % 2 = 1 := by
      omega
    rcases hmod with hmod | hmod
    · exact Or.inl ⟨hx, hmod⟩
    · exact Or.inr ⟨hx, hmod⟩

lemma half_counting_le_rankPart {A : Set ℕ} (hApos : A ⊆ Set.Ici 1)
    (hAinf : A.Infinite) {r : ℕ} (hr : r < 2) (N : ℕ) :
    counting A N / 2 ≤ counting (rankPart A r) N := by
  let k := counting A N
  let I := Finset.range (k / 2)
  let f : ℕ → ℕ := fun i ↦ Nat.nth (· ∈ A) (2 * i + r)
  have hcountEq : Nat.count (· ∈ A) (N + 1) = k := by
    symm
    exact counting_eq_count hApos N
  have himage : I.image f ⊆ (Finset.Icc 1 N).filter (· ∈ rankPart A r) := by
    intro x hx
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hx
    have hi : i < k / 2 := Finset.mem_range.mp hiI
    have hij : 2 * i + r < k := by omega
    have hlt : f i < N + 1 := by
      apply Nat.nth_lt_of_lt_count
      simpa [hcountEq] using hij
    have hfA : f i ∈ A := nth_mem hAinf _
    have hfpos : 1 ≤ f i := hApos hfA
    have hfrank : f i ∈ rankPart A r := by
      refine ⟨hfA, ?_⟩
      dsimp [f]
      rw [Nat.count_nth_of_infinite (p := fun x ↦ x ∈ A) hAinf]
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hfpos, by omega⟩, hfrank⟩
  have hfinj : Function.Injective f := (nth_strictMono hAinf).injective.comp
    (fun _ _ h ↦ by omega)
  calc
    counting A N / 2 = I.card := by simp [I, k]
    _ = (I.image f).card := (Finset.card_image_iff.mpr hfinj.injOn).symm
    _ ≤ ((Finset.Icc 1 N).filter (· ∈ rankPart A r)).card :=
      Finset.card_le_card himage
    _ = counting (rankPart A r) N := rfl

lemma sqrtDense_rankPart {A : Set ℕ} {c C : ℝ}
    (hApos : A ⊆ Set.Ici 1) (hc : 0 < c) (hgap : c < C / 2)
    (hdense : SqrtDense C A) {r : ℕ} (hr : r < 2) :
    SqrtDense c (rankPart A r) := by
  have hCpos : 0 < C := by linarith
  have hAinf := infinite_of_sqrtDense hCpos hdense
  have hmargin : 0 < C / 2 - c := sub_pos.mpr hgap
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      1 ≤ (C / 2 - c) * Real.sqrt (N : ℝ) :=
    (hsqrt.const_mul_atTop hmargin).eventually (eventually_ge_atTop 1)
  filter_upwards [hdense, hlarge] with N hN hlargeN
  have hhalfNat := half_counting_le_rankPart hApos hAinf hr N
  have hhalf : (counting A N / 2 : ℕ) ≤ counting (rankPart A r) N := hhalfNat
  have hfloor : (counting A N : ℝ) / 2 - 1 ≤ (counting A N / 2 : ℕ) := by
    have hkNat : counting A N ≤ 2 * (counting A N / 2) + 1 := by omega
    have hkReal : (counting A N : ℝ) ≤
        2 * ((counting A N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hkNat
    linarith
  have hhalfReal : (counting A N / 2 : ℕ) ≤
      (counting (rankPart A r) N : ℝ) := by exact_mod_cast hhalf
  nlinarith

lemma eventually_density_inversion {A : Set ℕ} {C : ℝ}
    (hApos : A ⊆ Set.Ici 1) (hC : 0 < C) (hdense : SqrtDense C A) :
    ∀ᶠ m : ℕ in atTop,
      C ^ 2 * (Nat.nth (· ∈ A) m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
  have hAinf : A.Infinite := infinite_of_sqrtDense hC hdense
  have hnthTop : Tendsto (Nat.nth (· ∈ A)) atTop atTop :=
    (nth_strictMono hAinf).tendsto_atTop
  have hdenseNth : ∀ᶠ m : ℕ in atTop,
      C * Real.sqrt (Nat.nth (· ∈ A) m : ℝ) ≤
        (counting A (Nat.nth (· ∈ A) m) : ℝ) :=
    hnthTop.eventually hdense
  filter_upwards [hdenseNth] with m hm
  rw [counting_nth hApos hAinf] at hm
  have hleft : 0 ≤ C * Real.sqrt (Nat.nth (· ∈ A) m : ℝ) :=
    mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hsquare := (sq_le_sq₀ hleft (by positivity)).2 hm
  calc
    C ^ 2 * (Nat.nth (· ∈ A) m : ℝ) =
        (C * Real.sqrt (Nat.nth (· ∈ A) m : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt]
      positivity
    _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := hsquare

lemma addNet_add_finiteAP {S T : Set ℕ} {q K a : ℕ}
    (hnet : IsAddNet q K T)
    (hAP : ∀ i < K + 1, a + i * q ∈ S) :
    ContainsInfiniteAP (S + T) := by
  refine ⟨a + K * q, q, hnet.1, ?_⟩
  intro n
  obtain ⟨s, hsT, hq, hlo, hhi⟩ := hnet.2 n
  obtain ⟨t, rfl⟩ := hq
  have hnle : n ≤ t := by
    rw [Nat.mul_comm n q] at hlo
    exact Nat.le_of_mul_le_mul_left hlo hnet.1
  have htle : t ≤ n + K := by
    rw [Nat.mul_comm (n + K) q] at hhi
    exact Nat.le_of_mul_le_mul_left hhi hnet.1
  let i := n + K - t
  have hiK : i ≤ K := by
    dsimp [i]
    omega
  have hi : i < K + 1 := by omega
  have hit : i + t = n + K := by
    dsimp [i]
    omega
  have hsum : (a + i * q) + q * t = (a + K * q) + n * q := by
    calc
      (a + i * q) + q * t = a + (i + t) * q := by ring
      _ = a + (n + K) * q := by rw [hit]
      _ = (a + K * q) + n * q := by ring
  rw [← hsum]
  exact ⟨a + i * q, hAP i hi, q * t, hsT, rfl⟩

/-! ### Lowering a finite progression's common difference -/

/-- Explicit membership form of common-difference lowering. -/
lemma lowerStep_of_residue_translates_mem {S U : Set ℕ}
    {a q M L Z : ℕ} (hq : 0 < q) (hM : 0 < M)
    (hAP : ∀ j < L, a + j * (q * M) ∈ S)
    (hres : ∀ i < M, ∃ u ∈ U, ∃ z ≤ Z, u = i * q + (q * M) * z) :
    ∀ n < M * (L - Z),
      (a + (q * M) * Z) + n * q ∈ S + U := by
  intro n hn
  let i := n % M
  let k := n / M
  have hi : i < M := Nat.mod_lt n hM
  obtain ⟨u, huU, z, hzZ, rfl⟩ := hres i hi
  let j := Z + k - z
  have hk : k < L - Z := by
    apply (Nat.div_lt_iff_lt_mul hM).2
    simpa [Nat.mul_comm] using hn
  have hzsum : z ≤ Z + k := hzZ.trans (Nat.le_add_right Z k)
  have hjEq : j + z = Z + k := by
    dsimp [j]
    omega
  have hsubpos : 0 < L - Z := (Nat.zero_le k).trans_lt hk
  have hZL : Z ≤ L := (Nat.sub_pos_iff_lt.mp hsubpos).le
  have hsubadd : L - Z + Z = L := Nat.sub_add_cancel hZL
  have hjL : j < L := by
    dsimp [j]
    omega
  have hnDecomp : n = k * M + i := by
    simpa [k, i] using (Nat.div_add_mod' n M).symm
  have hsum :
      (a + j * (q * M)) + (i * q + (q * M) * z) =
        (a + (q * M) * Z) + n * q := by
    calc
      (a + j * (q * M)) + (i * q + (q * M) * z) =
          a + (j + z) * (q * M) + i * q := by ring
      _ = a + (Z + k) * (q * M) + i * q := by rw [hjEq]
      _ = (a + (q * M) * Z) + (k * M + i) * q := by ring
      _ = (a + (q * M) * Z) + n * q := by rw [← hnDecomp]
  rw [← hsum]
  exact ⟨a + j * (q * M), hAP j hjL,
    i * q + (q * M) * z, huU, rfl⟩

/-- If `U` supplies a bounded translate in every residue class modulo `M`,
then adding `U` to a long `q*M` progression produces a `q` progression. -/
lemma lowerStep_of_residue_translates {S U : Set ℕ}
    {a q M L Z : ℕ} (hq : 0 < q) (hM : 0 < M)
    (hAP : ∀ j < L, a + j * (q * M) ∈ S)
    (hres : ∀ i < M, ∃ u ∈ U, ∃ z ≤ Z, u = i * q + (q * M) * z) :
    ContainsFiniteAP (S + U) (M * (L - Z)) := by
  exact ⟨a + (q * M) * Z, q, hq,
    lowerStep_of_residue_translates_mem hq hM hAP hres⟩

lemma fixedStep_addNet_of_disjoint {B C : Set ℕ} (hBC : Disjoint B C)
    {d K : ℕ}
    (hlong : ∀ k : ℕ, ∃ a : ℕ, ∀ i < k, a + i * d ∈ subsetSums B)
    (hnet : IsAddNet d K (subsetSums C)) :
    ContainsInfiniteAP (subsetSums (B ∪ C)) := by
  obtain ⟨a, ha⟩ := hlong (K + 1)
  have hsum : ContainsInfiniteAP (subsetSums B + subsetSums C) :=
    addNet_add_finiteAP hnet ha
  exact containsInfiniteAP_mono (subsetSums_union_subset_add hBC) hsum

/-! ### Graham's bounded-gap argument, in a finite coverage form -/

private def prefixSum (y : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, y i

private lemma prefixSum_succ (y : ℕ → ℕ) (n : ℕ) :
    prefixSum y (n + 1) = prefixSum y n + y n := by
  simp only [prefixSum, Finset.sum_range_succ]

private lemma twice_triangular_le_prefixSum (y : ℕ → ℕ)
    (hy : StrictMono y) (hypos : ∀ i, 0 < y i) :
    ∀ n, n * (n + 1) ≤ 2 * prefixSum y n := by
  intro n
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
      have hyn : n + 1 ≤ y n := by
        have hstep : n + y 0 ≤ y n := by
          simpa using hy.add_le_nat n 0
        have hyzero : 1 ≤ y 0 := hypos 0
        omega
      calc
        (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
        _ ≤ 2 * prefixSum y n + 2 * y n :=
          Nat.add_le_add ih (Nat.mul_le_mul_left 2 hyn)
        _ = 2 * prefixSum y (n + 1) := by rw [prefixSum_succ]; ring

/-- Above the constant `3`, square-root density forces the eventual growth
condition in Graham's bounded-gap argument. -/
lemma eventually_nth_le_prefixSum {A : Set ℕ} (hApos : A ⊆ Set.Ici 1)
    (hdense : SqrtDense 3 A) :
    ∀ᶠ m : ℕ in atTop,
      Nat.nth (· ∈ A) m ≤ prefixSum (Nat.nth (· ∈ A)) m := by
  have hAinf : A.Infinite := infinite_of_sqrtDense (by norm_num) hdense
  have hinv := eventually_density_inversion hApos (by norm_num : (0 : ℝ) < 3) hdense
  filter_upwards [hinv, eventually_ge_atTop 1] with m hinv hm
  have hlower := twice_triangular_le_prefixSum
    (Nat.nth (· ∈ A)) (nth_strictMono hAinf)
    (fun i ↦ hApos (nth_mem hAinf i)) m
  have hlowerReal :
      (m : ℝ) * (m + 1) ≤
        2 * (prefixSum (Nat.nth (· ∈ A)) m : ℝ) := by
    exact_mod_cast hlower
  have hresult :
      (Nat.nth (· ∈ A) m : ℝ) ≤
        (prefixSum (Nat.nth (· ∈ A)) m : ℝ) := by
    norm_num at hinv
    have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hcompare : 2 * ((m : ℝ) + 1) ^ 2 ≤ 9 * m * (m + 1) := by
      nlinarith
    nlinarith
  exact_mod_cast hresult

/-- If every new term is at most the sum of its predecessors, subset sums of
each sufficiently long prefix cover that prefix's total interval with a fixed
additive error. -/
private lemma exists_prefix_subsetSum_near (y : ℕ → ℕ) (m₀ : ℕ)
    (hgrowth : ∀ m, m₀ ≤ m → y m ≤ prefixSum y m) :
    ∀ n, m₀ ≤ n → ∀ x ≤ prefixSum y n,
      ∃ F : Finset ℕ, F ⊆ Finset.range n ∧
        (∑ i ∈ F, y i) ≤ x ∧ x ≤ (∑ i ∈ F, y i) + prefixSum y m₀ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro x hx
      exact ⟨∅, by simp, by simp, by simpa using hx⟩
  | succ n hn ih =>
      intro x hx
      by_cases hsmall : x ≤ prefixSum y n
      · obtain ⟨F, hF, hFlo, hFhi⟩ := ih x hsmall
        exact ⟨F, hF.trans (by simp), hFlo, hFhi⟩
      · have hyn : y n ≤ prefixSum y n := hgrowth n hn
        have hyx : y n ≤ x := hyn.trans (Nat.le_of_lt (Nat.lt_of_not_ge hsmall))
        have hsub : x - y n ≤ prefixSum y n := by
          rw [prefixSum_succ] at hx
          omega
        obtain ⟨F, hF, hFlo, hFhi⟩ := ih (x - y n) hsub
        have hnF : n ∉ F := fun h ↦ by
          have := hF h
          simp at this
        refine ⟨insert n F, ?_, ?_, ?_⟩
        · intro i hi
          simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp
          · exact Finset.mem_range.mpr ((Finset.mem_range.mp (hF hi)).trans
              (Nat.lt_succ_self n))
        · rw [Finset.sum_insert hnF]
          omega
        · rw [Finset.sum_insert hnF]
          omega

private lemma id_le_prefixSum (y : ℕ → ℕ) (hy : ∀ i, 0 < y i) (n : ℕ) :
    n ≤ prefixSum y n := by
  calc
    n = ∑ _i ∈ Finset.range n, 1 := by simp
    _ ≤ ∑ i ∈ Finset.range n, y i := by
      exact Finset.sum_le_sum fun i _ ↦ hy i
    _ = prefixSum y n := rfl

/-- A strictly enumerated positive sequence satisfying Graham's growth
condition and lying in one residue subgroup has a subset-sum additive net. -/
theorem exists_addNet_subsetSums_of_sequence {C : Set ℕ} {q : ℕ}
    (hqpos : 0 < q) (y : ℕ → ℕ) (hyinj : Function.Injective y)
    (hypos : ∀ i, 0 < y i) (hyC : ∀ i, y i ∈ C)
    (hyq : ∀ i, q ∣ y i)
    (hgrowth : ∃ m₀, ∀ m, m₀ ≤ m → y m ≤ prefixSum y m) :
    ∃ K : ℕ, IsAddNet q K (subsetSums C) := by
  obtain ⟨m₀, hgrowth⟩ := hgrowth
  let K := prefixSum y m₀
  refine ⟨K, hqpos, ?_⟩
  intro n
  let x := (n + K) * q
  let N := max m₀ x
  have hmN : m₀ ≤ N := le_max_left _ _
  have hxN : x ≤ N := le_max_right _ _
  have hxsum : x ≤ prefixSum y N :=
    hxN.trans (id_le_prefixSum y hypos N)
  obtain ⟨F, hFN, hFlo, hFhi⟩ :=
    exists_prefix_subsetSum_near y m₀ hgrowth N hmN x hxsum
  let G := F.image y
  have hsum : ∑ z ∈ G, z = ∑ i ∈ F, y i := by
    dsimp [G]
    rw [Finset.sum_image hyinj.injOn]
  have hGC : ↑G ⊆ C := by
    intro z hz
    rw [Finset.mem_coe] at hz
    change z ∈ F.image y at hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, -, rfl⟩ := hz
    exact hyC i
  have hmem : (∑ z ∈ G, z) ∈ subsetSums C :=
    ⟨G, hGC, rfl⟩
  have hdiv : q ∣ ∑ z ∈ G, z := by
    rw [hsum]
    exact Finset.dvd_sum fun i _ ↦ hyq i
  have hKq : K ≤ K * q := by
    have : 1 ≤ q := hqpos
    nlinarith
  refine ⟨∑ z ∈ G, z, hmem, hdiv, ?_, ?_⟩
  · rw [hsum]
    have hFhi' : x ≤ (∑ i ∈ F, y i) + K * q := by
      exact hFhi.trans (Nat.add_le_add_left (by simpa [K] using hKq) _)
    dsimp [x] at hFhi'
    rw [Nat.add_mul] at hFhi'
    exact Nat.le_of_add_le_add_right hFhi'
  · rw [hsum]
    exact hFlo

/-- Graham's argument specialized to a square-root-dense set in one
divisibility class. -/
theorem exists_addNet_subsetSums_of_sqrtDense {C : Set ℕ} {q : ℕ}
    (hCpos : C ⊆ Set.Ici 1) (hdense : SqrtDense 3 C)
    (hqpos : 0 < q) (hq : ∀ c ∈ C, q ∣ c) :
    ∃ K : ℕ, IsAddNet q K (subsetSums C) := by
  have hCinf : C.Infinite := infinite_of_sqrtDense (by norm_num) hdense
  let y : ℕ → ℕ := Nat.nth (· ∈ C)
  have hyinj : Function.Injective y := (nth_strictMono hCinf).injective
  have hypos : ∀ i, 0 < y i := fun i ↦ hCpos (nth_mem hCinf i)
  have hyC : ∀ i, y i ∈ C := nth_mem hCinf
  have hyq : ∀ i, q ∣ y i := fun i ↦ hq _ (hyC i)
  obtain ⟨m₀, hm₀⟩ := (eventually_atTop.1 (eventually_nth_le_prefixSum hCpos hdense))
  exact exists_addNet_subsetSums_of_sequence hqpos y hyinj hypos hyC hyq ⟨m₀, hm₀⟩

/-! ### Subgroups of a finite cyclic group -/

/-- Every additive subgroup of `ZMod d` consists exactly of the multiples
of a positive divisor `q` of `d`.  The formulation records the two directions
needed for the residue-stabilization argument below. -/
lemma exists_generator_modulus {d : ℕ} (hd : 0 < d)
    (K : AddSubgroup (ZMod d)) :
    ∃ q : ℕ, 0 < q ∧ q ∣ d ∧
      (∀ x : ZMod d, x ∈ K → q ∣ x.val) ∧
      (∀ i : ℕ, (i * q : ZMod d) ∈ K) := by
  letI : NeZero d := ⟨hd.ne'⟩
  let V := Finset.univ.filter fun x : ZMod d ↦ x ∈ K ∧ x ≠ 0
  by_cases hV : V.Nonempty
  · obtain ⟨g, hgV, hgmin⟩ := Finset.exists_min_image V ZMod.val hV
    have hgK : g ∈ K := (Finset.mem_filter.mp hgV).2.1
    have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgV).2.2
    let q := g.val
    have hqpos : 0 < q :=
      Nat.pos_of_ne_zero (fun h ↦ hg0 ((ZMod.val_eq_zero g).mp h))
    have hqd : q < d := g.val_lt
    have hmin : ∀ x : ZMod d, x ∈ K → x ≠ 0 → q ≤ x.val := by
      intro x hxK hx0
      exact hgmin x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxK, hx0⟩)
    have hcastg : (q : ZMod d) = g := ZMod.natCast_zmod_val g
    have hqdvd : q ∣ d := by
      let r := d % q
      have hrq : r < q := Nat.mod_lt d hqpos
      have hrd : r < d := hrq.trans hqd
      have hsumZ : ((d / q * q : ℕ) : ZMod d) + (r : ZMod d) = 0 := by
        have hsum := congrArg (fun n : ℕ ↦ (n : ZMod d)) (Nat.div_add_mod' d q)
        push_cast at hsum
        simpa [r] using hsum
      have hcast : (r : ZMod d) = -((d / q : ℕ) • g) := by
        rw [← hcastg]
        simp only [nsmul_eq_mul, Nat.cast_mul]
        apply (eq_neg_iff_add_eq_zero).2
        simpa [add_comm] using hsumZ
      have hrK : (r : ZMod d) ∈ K := by
        rw [hcast]
        exact K.neg_mem (K.nsmul_mem hgK _)
      have hr0 : r = 0 := by
        by_contra hrne
        have hcast0 : (r : ZMod d) ≠ 0 := by
          intro hz
          apply hrne
          have hv := congrArg ZMod.val hz
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] using hv
        have := hmin (r : ZMod d) hrK hcast0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] at this
        omega
      exact Nat.dvd_of_mod_eq_zero hr0
    refine ⟨q, hqpos, hqdvd, ?_, ?_⟩
    · intro x hxK
      let r := x.val % q
      have hrq : r < q := Nat.mod_lt x.val hqpos
      have hrd : r < d := hrq.trans hqd
      have hmul : x.val / q * q ≤ x.val := by
        simpa [mul_comm] using Nat.mul_div_le x.val q
      have hdecomp : x.val % q + x.val / q * q = x.val := by
        simpa [mul_comm] using Nat.mod_add_div x.val q
      have hsub : x.val - x.val / q * q = r := by
        dsimp [r]
        omega
      have hcast : (r : ZMod d) = x - (x.val / q : ℕ) • g := by
        calc
          (r : ZMod d) = ((x.val - x.val / q * q : ℕ) : ZMod d) := by rw [hsub]
          _ = (x.val : ZMod d) - (x.val / q * q : ℕ) := by
            rw [Nat.cast_sub hmul]
          _ = x - (x.val / q : ℕ) • g := by
            rw [ZMod.natCast_zmod_val x, Nat.cast_mul, hcastg]
            simp [nsmul_eq_mul]
      have hrK : (r : ZMod d) ∈ K := by
        rw [hcast]
        exact K.sub_mem hxK (K.nsmul_mem hgK _)
      have hr0 : r = 0 := by
        by_contra hrne
        have hcast0 : (r : ZMod d) ≠ 0 := by
          intro hz
          apply hrne
          have hv := congrArg ZMod.val hz
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] using hv
        have := hmin (r : ZMod d) hrK hcast0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrd] at this
        omega
      exact Nat.dvd_of_mod_eq_zero hr0
    · intro i
      have hi : (i * q : ZMod d) = i • g := by
        rw [← hcastg]
        simp [nsmul_eq_mul]
      rw [hi]
      exact K.nsmul_mem hgK i
  · refine ⟨d, hd, dvd_rfl, ?_, ?_⟩
    · intro x hxK
      have hx0 : x = 0 := by
        by_contra hxne
        exact hV ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxK, hxne⟩⟩
      rw [hx0]
      simp
    · intro i
      simp

/-- The two membership directions supplied by `exists_generator_modulus`
identify the subgroup with the usual cyclic subgroup generated by `q`. -/
lemma subgroup_eq_zmultiples_of_generator_modulus
    {d q : ℕ} [NeZero d] (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    H = AddSubgroup.zmultiples (q : ZMod d) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := hHdiv x hx
    rw [← ZMod.natCast_zmod_val x, hi, Nat.cast_mul]
    change ((q : ZMod d) * (i : ZMod d)) ∈
      AddSubgroup.zmultiples (q : ZMod d)
    rw [mul_comm]
    simpa [nsmul_eq_mul] using
      ((AddSubgroup.zmultiples (q : ZMod d)).nsmul_mem
        (AddSubgroup.mem_zmultiples (q : ZMod d)) i)
  · intro x hx
    obtain ⟨i, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    cases i with
    | ofNat i =>
        simpa [nsmul_eq_mul, mul_comm] using hmult i
    | negSucc i =>
        have hi : (i + 1) • (q : ZMod d) ∈ H := by
          simpa [nsmul_eq_mul, mul_comm] using hmult (i + 1)
        have hneg := H.neg_mem hi
        convert hneg using 1 <;> simp [nsmul_eq_mul] <;> ring

/-- Cardinality of the subgroup of multiples of `q` in `ZMod d`. -/
lemma natCard_subgroup_of_generator_modulus
    {d q : ℕ} (hd : 0 < d) (_hq : 0 < q) (hqd : q ∣ d)
    (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    Nat.card H = d / q := by
  letI : NeZero d := ⟨hd.ne'⟩
  rw [subgroup_eq_zmultiples_of_generator_modulus H hHdiv hmult,
    Nat.card_zmultiples, ZMod.addOrderOf_coe q hd.ne']
  have hgcd : d.gcd q = q := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left_iff_dvd.mpr hqd
  rw [hgcd]

lemma ncard_addSubgroup_eq_natCard {G : Type*} [AddGroup G]
    (H : AddSubgroup G) : (H : Set G).ncard = Nat.card H := by
  rw [← Set.ncard_univ H]
  apply Set.ncard_congr (fun x hx => (⟨x, hx⟩ : H))
  · simp
  · intro a b ha hb hab
    exact congrArg Subtype.val hab
  · intro b _
    exact ⟨b.1, b.2, Subtype.ext rfl⟩

/-- Set-cardinality form used for normalized coset fibres. -/
lemma ncard_subgroup_of_generator_modulus
    {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (hqd : q ∣ d)
    (H : AddSubgroup (ZMod d))
    (hHdiv : ∀ x : ZMod d, x ∈ H → q ∣ x.val)
    (hmult : ∀ i : ℕ, (i * q : ZMod d) ∈ H) :
    (H : Set (ZMod d)).ncard = d / q := by
  rw [ncard_addSubgroup_eq_natCard H]
  exact natCard_subgroup_of_generator_modulus hd hq hqd H hHdiv hmult

/-! ### Divisor-sensitive modular completeness -/

/-- A homomorphism sends the subset sums of a list onto the subset sums of
the mapped list. -/
lemma image_listSubsetSums_map {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
    (f : G →+ H) (A : List G) :
    (Erdos587.listSubsetSums A).image f =
      Erdos587.listSubsetSums (A.map f) := by
  have image_addTranslate (a : G) (S : Finset G) :
      (Erdos587.addTranslate a S).image f =
        Erdos587.addTranslate (f a) (S.image f) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      rw [Erdos587.mem_addTranslate] at hx ⊢
      apply Finset.mem_image.mpr
      refine ⟨-a + x, hx, ?_⟩
      rw [map_add, map_neg, hxy]
    · intro hy
      rw [Erdos587.mem_addTranslate] at hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      apply Finset.mem_image.mpr
      refine ⟨a + x, ?_, ?_⟩
      · rw [Erdos587.mem_addTranslate]
        simpa
      · rw [map_add, hxy]
        abel
  induction A with
  | nil => simp [Erdos587.listSubsetSums]
  | cons a A ih =>
      simp only [Erdos587.listSubsetSums_cons, List.map_cons,
        Finset.image_union, ih]
      rw [image_addTranslate, ih]

lemma zmod_castHom_eq_zero_iff_val_dvd {q d : ℕ} [NeZero q]
    (hdq : d ∣ q) (x : ZMod q) :
    ZMod.castHom hdq (ZMod d) x = 0 ↔ d ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- If a surjective homomorphism has exactly the translation stabilizer of
`S` as its kernel, the image of `S` has trivial translation stabilizer. -/
lemma image_stabilizer_eq_bot {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (S : Finset G)
    (hker : ∀ x, f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S) :
    Erdos587.finsetAddStabilizer (S.image f) = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  have hy' : Erdos587.addTranslate (f x) (S.image f) = S.image f := hy
  have hxsub : Erdos587.addTranslate x S ⊆ S := by
    intro z hz
    have hs : -x + z ∈ S := Erdos587.mem_addTranslate.mp hz
    have hfs : f (-x + z) ∈ S.image f :=
      Finset.mem_image.mpr ⟨_, hs, rfl⟩
    have hfztrans : f z ∈ Erdos587.addTranslate (f x) (S.image f) := by
      apply Finset.mem_image.mpr
      refine ⟨f (-x + z), hfs, ?_⟩
      simp only [map_add, map_neg]
      abel
    rw [hy'] at hfztrans
    obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp hfztrans
    have hzero : f (z - t) = 0 := by
      rw [map_sub, hft]
      simp
    have hstab : z - t ∈ Erdos587.finsetAddStabilizer S :=
      (hker _).mp hzero
    have hmem : (z - t) + t ∈ Erdos587.addTranslate (z - t) S := by
      apply Finset.mem_image.mpr
      exact ⟨t, ht, rfl⟩
    rw [Erdos587.mem_finsetAddStabilizer.mp hstab] at hmem
    simpa using hmem
  have hxstab : Erdos587.addTranslate x S = S := by
    exact Finset.eq_of_subset_of_card_le hxsub (by
      rw [Erdos587.card_addTranslate])
  have hxker : f x = 0 := (hker x).mpr hxstab
  simpa [hxker]

/-- Under the same kernel hypothesis, a proper set has proper image. -/
lemma image_ne_univ_of_stabilizer_kernel {G H : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] [Fintype H]
    (f : G →+ H) (S : Finset G) (hSproper : S ≠ Finset.univ)
    (hker : ∀ x, f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S) :
    S.image f ≠ Finset.univ := by
  intro himage
  apply hSproper
  apply Finset.eq_univ_of_forall
  intro x
  have hfx : f x ∈ S.image f := by rw [himage]; simp
  obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp hfx
  have hzero : f (x - t) = 0 := by rw [map_sub, hft]; simp
  have hstab : x - t ∈ Erdos587.finsetAddStabilizer S :=
    (hker _).mp hzero
  have hmem : (x - t) + t ∈ Erdos587.addTranslate (x - t) S := by
    apply Finset.mem_image.mpr
    exact ⟨t, ht, rfl⟩
  rw [Erdos587.mem_finsetAddStabilizer.mp hstab] at hmem
  simpa using hmem

/-- If the final subset-sum stabilizer is trivial and the subset sums are
proper, fewer than `|G|-1` list occurrences are nonzero. -/
lemma nonzero_length_add_one_lt_card_of_stabilizer_bot
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : List G)
    (hproper : Erdos587.listSubsetSums A ≠ Finset.univ)
    (hstab : Erdos587.finsetAddStabilizer
      (Erdos587.listSubsetSums A) = ⊥) :
    (A.filter fun a => a ≠ 0).length + 1 < Fintype.card G := by
  have hstable :
      (Erdos587.subsetSumStableTerms A).filter (fun a => a ≠ 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have haStab : a ∈ Erdos587.finsetAddStabilizer
        (Erdos587.listSubsetSums A) :=
      Erdos587.mem_stable_stabilizes_listSubsetSums ha
    rw [hstab] at haStab
    simpa using haStab
  have hperm :=
    (Erdos587.stable_append_growth_perm A).filter (fun a => a ≠ 0)
  have hlen :
      (A.filter fun a => a ≠ 0).length ≤
        (Erdos587.subsetSumGrowthTerms A).length := by
    rw [← hperm.length_eq, List.filter_append, hstable]
    exact List.length_filter_le _ _
  have hcardlt : (Erdos587.listSubsetSums A).card < Fintype.card G := by
    have hss : Erdos587.listSubsetSums A ⊂ (Finset.univ : Finset G) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hproper⟩
    exact Finset.card_lt_card hss
  have hgrowth := Erdos587.growth_length_add_one_le_card_listSubsetSums A
  omega

lemma length_filter_zmod_castHom_ne_zero
    {q d : ℕ} [NeZero q] [NeZero d] (hdq : d ∣ q) (A : List ℕ) :
    ((A.map fun a : ℕ => ZMod.castHom hdq (ZMod d) (a : ZMod q)).filter
      fun x => x ≠ 0).length =
      (A.filter fun a => ¬ d ∣ a).length := by
  induction A with
  | nil => simp
  | cons a A ih =>
      simp only [List.map_cons, map_natCast]
      have ih' :
          ((A.map fun a : ℕ => (a : ZMod d)).filter fun x => x ≠ 0).length =
            (A.filter fun a => ¬ d ∣ a).length := by
        simpa only [map_natCast] using ih
      by_cases ha : d ∣ a
      · have ha0 : (a : ZMod d) = 0 :=
          (ZMod.natCast_eq_zero_iff a d).mpr ha
        rw [List.filter_cons_of_neg (by simpa using ha0),
          List.filter_cons_of_neg (by simpa using ha)]
        exact ih'
      · have ha0 : (a : ZMod d) ≠ 0 :=
          fun h => ha ((ZMod.natCast_eq_zero_iff a d).mp h)
        rw [List.filter_cons_of_pos (by simp [ha0]),
          List.filter_cons_of_pos (by simp [ha]),
          List.length_cons, List.length_cons, ih']

/-- A divisor-diverse list is complete modulo `q`.  This is the
Conlon--Fox--Pham modular completeness criterion: for every divisor `d > 1`
of `q`, `d - 1` nonmultiples force all residues to occur as subset sums. -/
theorem listSubsetSums_mod_eq_univ_of_divisor_diverse
    {q : ℕ} [NeZero q] (hq : 0 < q) (A : List ℕ)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ q →
      d - 1 ≤ (A.filter fun a => ¬ d ∣ a).length) :
    Erdos587.listSubsetSums (A.map fun a : ℕ => (a : ZMod q)) =
      Finset.univ := by
  let M : List (ZMod q) := A.map fun a : ℕ => (a : ZMod q)
  let S : Finset (ZMod q) := Erdos587.listSubsetSums M
  by_contra hproper
  have hproperS : S ≠ Finset.univ := by simpa [S, M] using hproper
  let K : AddSubgroup (ZMod q) := Erdos587.finsetAddStabilizer S
  have hKproper : K ≠ ⊤ :=
    Erdos587.finsetAddStabilizer_ne_top
      (by simpa [S] using Erdos587.zero_mem_listSubsetSums M) hproperS
  obtain ⟨d, hdpos, hdq, hKdiv, hmultK⟩ := exists_generator_modulus hq K
  have hdgt : 1 < d := by
    by_contra hnot
    have hd1 : d = 1 := by omega
    apply hKproper
    apply top_unique
    intro x _
    rw [← ZMod.natCast_zmod_val x]
    simpa [hd1] using hmultK x.val
  letI : NeZero d := ⟨hdpos.ne'⟩
  let f : ZMod q →+ ZMod d :=
    (ZMod.castHom hdq (ZMod d)).toAddMonoidHom
  have hfsurj : Function.Surjective f := by
    intro y
    refine ⟨(y.val : ZMod q), ?_⟩
    have hdqle : d ≤ q := Nat.le_of_dvd hq hdq
    have hyq : y.val < q := y.val_lt.trans_le hdqle
    dsimp [f]
    rw [ZMod.cast_eq_val, ZMod.val_natCast, Nat.mod_eq_of_lt hyq]
    exact ZMod.natCast_zmod_val y
  have hker : ∀ x : ZMod q,
      f x = 0 ↔ x ∈ Erdos587.finsetAddStabilizer S := by
    intro x
    constructor
    · intro hx
      have hdval : d ∣ x.val :=
        (zmod_castHom_eq_zero_iff_val_dvd hdq x).mp (by
          simpa [f] using hx)
      obtain ⟨i, hi⟩ := hdval
      have hxrepr : x = (i * d : ℕ) := by
        calc
          x = (x.val : ZMod q) := (ZMod.natCast_zmod_val x).symm
          _ = (d * i : ℕ) := by rw [hi]
          _ = (i * d : ℕ) := by rw [mul_comm]
      rw [hxrepr]
      change ((i * d : ℕ) : ZMod q) ∈ K
      simpa only [Nat.cast_mul] using hmultK i
    · intro hx
      apply (zmod_castHom_eq_zero_iff_val_dvd hdq x).mpr
      exact hKdiv x hx
  let B : List (ZMod d) := M.map f
  have himage : S.image f = Erdos587.listSubsetSums B := by
    simpa [S, B] using image_listSubsetSums_map f M
  have hproperB : Erdos587.listSubsetSums B ≠ Finset.univ := by
    intro hall
    have himageProper := image_ne_univ_of_stabilizer_kernel
      f S hproperS hker
    apply himageProper
    rw [himage, hall]
  have hstabB : Erdos587.finsetAddStabilizer
      (Erdos587.listSubsetSums B) = ⊥ := by
    have hstab := image_stabilizer_eq_bot f hfsurj S hker
    rwa [himage] at hstab
  have hfew := nonzero_length_add_one_lt_card_of_stabilizer_bot
    B hproperB hstabB
  have hfew' : (B.filter fun a => a ≠ 0).length + 1 < d := by
    simpa [ZMod.card] using hfew
  have hfilter :
      (B.filter fun a => a ≠ 0).length =
        (A.filter fun a => ¬ d ∣ a).length := by
    simpa [B, M, f, List.map_map, Function.comp_def] using
      length_filter_zmod_castHom_ne_zero hdq A
  rw [hfilter] at hfew'
  have hlower := hdiverse d hdgt hdq
  omega

/-! ### The unsaturated modular-growth step -/

/-- A finite set containing zero and generating the ambient finite group is
not contained in a coset of a proper subgroup. -/
lemma notContainedInProperCoset_of_zero_mem_closure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {P : Finset G} (hzero : 0 ∈ P)
    (hclosure : AddSubgroup.closure (P : Set G) = ⊤) :
    Erdos360.NotContainedInProperCoset P := by
  intro H hH a hsub
  have hPa : ∀ x ∈ P, ∃ y : G, y ∈ H ∧ a + y = x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hsub (by simpa using hx)
    exact ⟨y, by simpa using hy, by simpa using hxy⟩
  obtain ⟨y0, hy0, hay0⟩ := hPa 0 hzero
  have hPsub : (P : Set G) ⊆ H := by
    intro x hx
    obtain ⟨y, hy, hay⟩ := hPa x (by simpa using hx)
    have haH : a ∈ H := by
      have hneg : -y0 ∈ H := H.neg_mem hy0
      have haeq : a = -y0 := by
        rw [← add_left_inj y0]
        simpa [add_comm] using hay0
      simpa [haeq] using hneg
    have hsum : a + y ∈ H := H.add_mem haH hy
    simpa [hay] using hsum
  have htop_le : (⊤ : AddSubgroup G) ≤ H := by
    rw [← hclosure, AddSubgroup.closure_le]
    exact hPsub
  exact hH (top_unique htop_le)

/-- Iterated sums of shifts which each add at most `e` points add at most
`k*e` points. -/
lemma iteratedFinsetSum_almostPeriods_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (U : Finset G) (e k : ℕ) :
    Erdos360.iteratedFinsetSum (Erdos360.almostPeriods U e) k ⊆
      Erdos360.almostPeriods U (k * e) := by
  induction k with
  | zero => simp
  | succ k ih =>
      intro x hx
      rw [Erdos360.iteratedFinsetSum_succ, Finset.mem_add] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have ha' := ih ha
      have hab := Erdos360.add_mem_almostPeriods ha' hb
      simpa [Nat.succ_mul, Nat.add_comm] using hab

/-- CFP's unsaturated-phase estimate.  If `X` generates a finite abelian
group and `U` lies below one quarter of that group but above one quarter of
`X`, some translate by a member of `X` adds at least `|X|/16` new points. -/
lemma exists_translationNew_large_of_closure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {U X : Finset G} (hU : U.Nonempty) (hX : X.Nonempty)
    (hXU : X.card < 4 * U.card)
    (hUG : 4 * U.card < Fintype.card G)
    (hclosure : AddSubgroup.closure (X : Set G) = ⊤) :
    ∃ x ∈ X, X.card ≤ 16 * (Erdos360.translationNew U x).card := by
  classical
  by_contra hnone
  push Not at hnone
  let e := X.card / 16
  let k := 4 * U.card / X.card
  let P := Erdos360.almostPeriods U e
  have hXpos : 0 < X.card := Finset.card_pos.mpr hX
  have hUP : 0 < U.card := Finset.card_pos.mpr hU
  have hXP : X ⊆ P := by
    intro x hx
    rw [Erdos360.mem_almostPeriods_iff_card_translationNew_le]
    have hsmall := hnone x hx
    dsimp [e]
    omega
  have hzeroP : 0 ∈ P := by simp [P]
  have hclosureP : AddSubgroup.closure (P : Set G) = ⊤ := by
    apply top_unique
    rw [← hclosure]
    apply AddSubgroup.closure_mono
    exact_mod_cast hXP
  have hPcoset : Erdos360.NotContainedInProperCoset P :=
    notContainedInProperCoset_of_zero_mem_closure_eq_top hzeroP hclosureP
  have hkpos : 1 ≤ k := by
    dsimp [k]
    rw [Nat.le_div_iff_mul_le hXpos]
    omega
  have hke : 2 * (k * e) ≤ U.card := by
    have he : 16 * e ≤ X.card := by
      dsimp [e]
      exact Nat.mul_div_le _ _
    have hkX : k * X.card ≤ 4 * U.card := by
      dsimp [k]
      exact Nat.div_mul_le_self _ _
    nlinarith
  have hiterSub : Erdos360.iteratedFinsetSum P k ⊆
      Erdos360.almostPeriods U (k * e) := by
    simpa [P] using iteratedFinsetSum_almostPeriods_subset U e k
  have hAPbound := Erdos360.card_sub_mul_card_almostPeriods_le_sq U (k * e)
  have hden : U.card ≤ 2 * (U.card - k * e) := by omega
  have hAPcard : (Erdos360.almostPeriods U (k * e)).card ≤ 2 * U.card := by
    have hmul : U.card * (Erdos360.almostPeriods U (k * e)).card ≤
        U.card * (2 * U.card) := by
      calc
        U.card * (Erdos360.almostPeriods U (k * e)).card ≤
            2 * ((U.card - k * e) *
              (Erdos360.almostPeriods U (k * e)).card) := by nlinarith
        _ ≤ 2 * U.card ^ 2 := Nat.mul_le_mul_left 2 hAPbound
        _ = U.card * (2 * U.card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hUP
  have hiterCard : (Erdos360.iteratedFinsetSum P k).card ≤ 2 * U.card :=
    (Finset.card_le_card hiterSub).trans hAPcard
  have hlower :=
    Erdos360.min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzeroP⟩ hPcoset k hkpos
  have hiter4 : 2 * (Erdos360.iteratedFinsetSum P k).card ≤
      4 * U.card := by omega
  have htarget : (k + 1) * P.card ≤ 4 * U.card := by
    rcases le_total (2 * Fintype.card G) ((k + 1) * P.card) with hle | hle
    · have hgroup : 2 * Fintype.card G ≤
          2 * (Erdos360.iteratedFinsetSum P k).card := by
        simpa [min_eq_left hle] using hlower
      have : 2 * Fintype.card G ≤ 4 * U.card := hgroup.trans hiter4
      omega
    · have hmain : (k + 1) * P.card ≤
          2 * (Erdos360.iteratedFinsetSum P k).card := by
        simpa [min_eq_right hle] using hlower
      exact hmain.trans hiter4
  have hXcardP : X.card ≤ P.card := Finset.card_le_card hXP
  have hupper : (k + 1) * X.card ≤ 4 * U.card :=
    (Nat.mul_le_mul_left (k + 1) hXcardP).trans htarget
  have hstrict : 4 * U.card < X.card * (k + 1) := by
    dsimp [k]
    exact Nat.lt_mul_div_succ (4 * U.card) hXpos
  nlinarith [hupper]

/-- The quantitative choice used in a CFP growth phase: if the current
internal subset-sum set has fewer than half as many points as the remaining
set, one remaining shift grows it by a factor of at least `3/2`. -/
lemma exists_three_halves_growth
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {T X : Finset G} (hT : T.Nonempty) (_hX : X.Nonempty)
    (hsmall : 2 * T.card < X.card) :
    ∃ x ∈ X,
      3 * T.card ≤ 2 * (T ∪ Erdos587.addTranslate x T).card := by
  classical
  let e := T.card / 2
  let P := Erdos360.almostPeriods T e
  have hTpos : 0 < T.card := Finset.card_pos.mpr hT
  have hden : T.card ≤ 2 * (T.card - e) := by
    dsimp [e]
    omega
  have hAPbound := Erdos360.card_sub_mul_card_almostPeriods_le_sq T e
  have hPcard : P.card ≤ 2 * T.card := by
    have hmul : T.card * P.card ≤ T.card * (2 * T.card) := by
      calc
        T.card * P.card ≤ 2 * ((T.card - e) * P.card) := by nlinarith
        _ ≤ 2 * T.card ^ 2 := by
          exact Nat.mul_le_mul_left 2 (by simpa [P] using hAPbound)
        _ = T.card * (2 * T.card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hTpos
  have hnot : ¬ X ⊆ P := by
    intro hXP
    have := (Finset.card_le_card hXP).trans hPcard
    omega
  obtain ⟨x, hxX, hxP⟩ := Finset.not_subset.mp hnot
  refine ⟨x, hxX, ?_⟩
  have hnew : e < (Erdos360.translationNew T x).card := by
    contrapose! hxP
    exact Erdos360.mem_almostPeriods_iff_card_translationNew_le.mpr hxP
  have hsdiff := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x T) T
  have hunion : (T ∪ Erdos587.addTranslate x T).card =
      T.card + (Erdos360.translationNew T x).card := by
    dsimp [Erdos360.translationNew] at hsdiff ⊢
    rw [Finset.union_comm] at hsdiff
    omega
  rw [hunion]
  dsimp [e] at hnew
  omega

/-- The remaining elements of a modular phase, regarded inside the subgroup
which they generate. -/
noncomputable def liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (X : Finset G) :
    Finset (AddSubgroup.closure (X : Set G)) := by
  classical
  letI : Fintype (AddSubgroup.closure (X : Set G)) :=
    Fintype.ofInjective (fun x : AddSubgroup.closure (X : Set G) => x.1)
      Subtype.val_injective
  exact Finset.univ.filter fun x => x.1 ∈ X

@[simp] lemma mem_liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {X : Finset G} {x : AddSubgroup.closure (X : Set G)} :
    x ∈ liftFinsetToClosure X ↔ x.1 ∈ X := by
  letI : Fintype (AddSubgroup.closure (X : Set G)) :=
    Fintype.ofInjective (fun x : AddSubgroup.closure (X : Set G) => x.1)
      Subtype.val_injective
  simp [liftFinsetToClosure]

lemma card_liftFinsetToClosure
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) : (liftFinsetToClosure X).card = X.card := by
  classical
  let H := AddSubgroup.closure (X : Set G)
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  have himage : (liftFinsetToClosure X).image (fun x : H => x.1) = X := by
    ext x
    simp only [Finset.mem_image, mem_liftFinsetToClosure]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_liftFinsetToClosure.mp hy
    · intro hx
      exact ⟨⟨x, AddSubgroup.subset_closure hx⟩,
        mem_liftFinsetToClosure.mpr hx, rfl⟩
  calc
    (liftFinsetToClosure X).card =
        ((liftFinsetToClosure X).image (fun x : H => x.1)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = X.card := by rw [himage]

lemma closure_liftFinsetToClosure_eq_top
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) :
    AddSubgroup.closure ((liftFinsetToClosure X :
      Finset (AddSubgroup.closure (X : Set G))) :
        Set (AddSubgroup.closure (X : Set G))) = ⊤ := by
  let H := AddSubgroup.closure (X : Set G)
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  have hset : ((liftFinsetToClosure X : Finset H) : Set H) =
      H.subtype ⁻¹' (X : Set G) := by
    ext x
    simp [H]
  rw [hset]
  exact AddSubgroup.closure_preimage_eq_top (X : Set G)

/-- A coset fibre of `S`, translated back into its subgroup. -/
noncomputable def normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G) (u : G) : Finset H := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  exact Finset.univ.filter fun h => u + h.1 ∈ S

@[simp] lemma mem_normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {S : Finset G} {u : G} {h : H} :
    h ∈ normalizedCosetFiber H S u ↔ u + h.1 ∈ S := by
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  simp [normalizedCosetFiber]

lemma card_translationNew_normalizedCosetFiber_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G) (u : G) (x : H) :
    (Erdos360.translationNew (normalizedCosetFiber H S u) x).card ≤
      (Erdos360.translationNew S x.1).card := by
  classical
  let f : H → G := fun h => u + h.1
  apply Finset.card_le_card_of_injOn f
  · intro h hh
    rw [Finset.mem_coe, Erdos360.translationNew, Finset.mem_sdiff] at hh
    rw [Finset.mem_coe, Erdos360.translationNew, Finset.mem_sdiff]
    constructor
    · rw [Erdos587.mem_addTranslate] at hh ⊢
      simpa [f, add_assoc, add_left_comm, add_comm] using hh.1
    · simpa [f] using hh.2
  · intro a _ b _ hab
    apply Subtype.ext
    exact add_left_cancel hab

/-- Unsaturated growth in one coset implies the same quantitative growth of
the entire modular subset-sum set. -/
lemma exists_translationNew_large_of_normalizedCosetFiber
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S X : Finset G} {u : G}
    (hU : (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).Nonempty)
    (hX : X.Nonempty)
    (hXU : X.card < 4 *
      (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).card)
    (hUG : 4 *
      (normalizedCosetFiber (AddSubgroup.closure (X : Set G)) S u).card <
        (AddSubgroup.closure (X : Set G) : Set G).ncard) :
    ∃ x ∈ X, X.card ≤ 16 * (Erdos360.translationNew S x).card := by
  classical
  let H := AddSubgroup.closure (X : Set G)
  letI : Fintype H :=
    Fintype.ofInjective (fun x : H => x.1) Subtype.val_injective
  let XH : Finset H := liftFinsetToClosure X
  let U : Finset H := normalizedCosetFiber H S u
  have hXH : XH.Nonempty := by
    apply Finset.card_pos.mp
    rw [show XH.card = X.card by exact card_liftFinsetToClosure X]
    exact Finset.card_pos.mpr hX
  have hXcard : XH.card = X.card := card_liftFinsetToClosure X
  have hUG' : 4 * U.card < Fintype.card H := by
    have hcardH : Fintype.card H = (H : Set G).ncard := by
      exact Set.fintypeCard_eq_ncard (H : Set G)
    rw [hcardH]
    simpa [U, H] using hUG
  obtain ⟨x, hxXH, hxlarge⟩ :=
    exists_translationNew_large_of_closure_eq_top hU hXH
      (by simpa [U, hXcard] using hXU)
      hUG'
      (closure_liftFinsetToClosure_eq_top X)
  refine ⟨x.1, (mem_liftFinsetToClosure.mp hxXH), ?_⟩
  have hle := card_translationNew_normalizedCosetFiber_le H S u x
  rw [← hXcard]
  exact hxlarge.trans (Nat.mul_le_mul_left 16 hle)

/-! ### Coset fibres of ordinary finite subset sums -/

/-- Adjoining a genuinely new group element replaces the finite subset-sum
set by its union with one translate. -/
lemma subsetSum_insert_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (a : G) (haA : a ∉ A) :
    (insert a A).subsetSum =
      A.subsetSum ∪ Erdos587.addTranslate a A.subsetSum := by
  ext x
  simp only [Finset.mem_subsetSum_iff, Finset.mem_union]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases ha : a ∈ B
    · right
      rw [Erdos587.mem_addTranslate, Finset.mem_subsetSum_iff]
      refine ⟨B.erase a, ?_, ?_⟩
      · intro y hy
        have hy' := Finset.mem_erase.mp hy
        exact (Finset.mem_insert.mp (hB hy'.2)).resolve_left
          (fun h => hy'.1 h)
      · have he := Finset.sum_erase_add B id ha
        simp only [id_eq] at he
        rw [← he]
        abel
    · left
      exact ⟨B, fun y hy => (Finset.mem_insert.mp (hB hy)).resolve_left
        (fun h => ha (h ▸ hy)), rfl⟩
  · rintro (⟨B, hB, rfl⟩ | hx)
    · exact ⟨B, hB.trans (Finset.subset_insert a A), rfl⟩
    · rw [Erdos587.mem_addTranslate] at hx
      obtain ⟨B, hB, hsum⟩ := Finset.mem_subsetSum_iff.mp hx
      have ha : a ∉ B := fun haB => haA (hB haB)
      refine ⟨insert a B, Finset.insert_subset_insert a hB, ?_⟩
      rw [Finset.sum_insert ha, hsum]
      abel

lemma listSubsetSums_eq_of_perm
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A B : List G} (h : A.Perm B) :
    Erdos587.listSubsetSums A = Erdos587.listSubsetSums B := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Erdos587.listSubsetSums_cons, ih]
  | swap a b l =>
      simp only [Erdos587.listSubsetSums_cons,
        Erdos587.addTranslate_union, Erdos587.addTranslate_add]
      rw [add_comm a b]
      ac_rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Mathlib's finite-set subset sums and the occurrence-list recursion agree
when the list is the duplicate-free list of a finset. -/
lemma listSubsetSums_toList_eq_subsetSum
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    Erdos587.listSubsetSums A.toList = A.subsetSum := by
  induction A using Finset.induction with
  | empty =>
      simp [Erdos587.listSubsetSums_nil, Finset.subsetSum]
  | @insert a A ha ih =>
      rw [listSubsetSums_eq_of_perm (Finset.toList_insert ha)]
      simp only [Erdos587.listSubsetSums_cons, ih]
      symm
      exact subsetSum_insert_eq A a ha

/-- The elements of a finite ambient set which lie in a subgroup, lifted to
the subgroup subtype. -/
noncomputable def elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) : Finset H := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  exact Finset.univ.filter fun h => h.1 ∈ A

@[simp] lemma mem_elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {A : Finset G} {h : H} :
    h ∈ elementsInSubgroup H A ↔ h.1 ∈ A := by
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  simp [elementsInSubgroup]

lemma exists_finset_sum_val_of_mem_subsetSum_elementsInSubgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} {A : Finset G} {t : H}
    (ht : t ∈ (elementsInSubgroup H A).subsetSum) :
    ∃ U : Finset G, U ⊆ A ∧ (∀ x ∈ U, x ∈ H) ∧
      ∑ x ∈ U, x = t.1 := by
  rw [Finset.mem_subsetSum_iff] at ht
  obtain ⟨T, hT, hsum⟩ := ht
  let U : Finset G := T.image fun h : H => h.1
  have hU : U ⊆ A := by
    intro x hx
    obtain ⟨h, hhT, rfl⟩ := Finset.mem_image.mp hx
    exact mem_elementsInSubgroup.mp (hT hhT)
  refine ⟨U, hU, ?_, ?_⟩
  · intro x hx
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hx
    exact h.2
  · change ∑ x ∈ T.image (fun h : H => h.1), x = t.1
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    have he := congrArg Subtype.val hsum
    simpa using he

/-- CFP Lemma 5.11: every occupied subgroup coset of a subset-sum set
contains at least as many points as the subset sums made only from elements
of that subgroup. -/
lemma subsetSum_fiber_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (u : G)
    (hU : (normalizedCosetFiber H A.subsetSum u).Nonempty) :
    (elementsInSubgroup H A).subsetSum.card ≤
      (normalizedCosetFiber H A.subsetSum u).card := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  obtain ⟨h₀, hh₀⟩ := hU
  have hy : u + h₀.1 ∈ A.subsetSum :=
    mem_normalizedCosetFiber.mp hh₀
  rw [Finset.mem_subsetSum_iff] at hy
  obtain ⟨B, hBA, hBsum⟩ := hy
  let B₀ := B.filter fun x => x ∉ H
  let B₁ := B.filter fun x => x ∈ H
  let y := ∑ x ∈ B₀, x
  have hBsplit : B₀ ∪ B₁ = B := by
    ext x
    by_cases hx : x ∈ H <;> simp [B₀, B₁, hx]
  have hBdisj : Disjoint B₀ B₁ := by
    rw [Finset.disjoint_left]
    intro x hx₀ hx₁
    exact (Finset.mem_filter.mp hx₀).2 (Finset.mem_filter.mp hx₁).2
  have hysum : y + ∑ x ∈ B₁, x = u + h₀.1 := by
    rw [← Finset.sum_union hBdisj, hBsplit, hBsum]
  have hB₁H : ∑ x ∈ B₁, x ∈ H := by
    apply H.sum_mem
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hycoset : -u + y ∈ H := by
    have heq : -u + y = h₀.1 - ∑ x ∈ B₁, x := by
      calc
        -u + y = (-u + (y + ∑ x ∈ B₁, x)) - ∑ x ∈ B₁, x := by abel
        _ = (-u + (u + h₀.1)) - ∑ x ∈ B₁, x := by rw [hysum]
        _ = h₀.1 - ∑ x ∈ B₁, x := by abel
    rw [heq]
    exact H.sub_mem h₀.2 hB₁H
  let base : H := ⟨-u + y, hycoset⟩
  let f : H → H := fun t => base + t
  apply Finset.card_le_card_of_injOn f
  · intro t ht
    rw [Finset.mem_coe, mem_normalizedCosetFiber]
    obtain ⟨T, hTA, hTH, hTsum⟩ :=
      exists_finset_sum_val_of_mem_subsetSum_elementsInSubgroup ht
    rw [Finset.mem_subsetSum_iff]
    have hBT : Disjoint B₀ T := by
      rw [Finset.disjoint_left]
      intro x hxB hxT
      exact (Finset.mem_filter.mp hxB).2 (hTH x hxT)
    refine ⟨B₀ ∪ T, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_union] at hx
      exact hx.elim
        (fun h => hBA (Finset.filter_subset _ _ h))
        (fun h => hTA h)
    · rw [Finset.sum_union hBT, hTsum]
      change y + t.1 = u + (base + t).1
      dsimp [base]
      abel
  · intro a _ b _ hab
    exact add_left_cancel hab

/-- Seeded form of CFP Lemma 5.11.  This is the form used in Lemma 6.2,
where the seed contributes exactly one summand and subsequent phases adjoin
ordinary subset sums. -/
lemma seededSubsetSum_fiber_lower
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (E A : Finset G) (u : G)
    (hU : (normalizedCosetFiber H (E + A.subsetSum) u).Nonempty) :
    (elementsInSubgroup H A).subsetSum.card ≤
      (normalizedCosetFiber H (E + A.subsetSum) u).card := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  obtain ⟨h₀, hh₀⟩ := hU
  have hsum : u + h₀.1 ∈ E + A.subsetSum :=
    mem_normalizedCosetFiber.mp hh₀
  rw [Finset.mem_add] at hsum
  obtain ⟨e, he, x, hx, hex⟩ := hsum
  have hxcoset : -(u - e) + x ∈ H := by
    have heq : -(u - e) + x = h₀.1 := by
      calc
        -(u - e) + x = -u + (e + x) := by abel
        _ = -u + (u + h₀.1) := by rw [hex]
        _ = h₀.1 := by abel
    rw [heq]
    exact h₀.2
  let hxH : H := ⟨-(u - e) + x, hxcoset⟩
  have hxEq : (u - e) + hxH.1 = x := by
    dsimp [hxH]
    abel
  have hfiberA :
      (normalizedCosetFiber H A.subsetSum (u - e)).Nonempty := by
    refine ⟨hxH, ?_⟩
    rw [mem_normalizedCosetFiber, hxEq]
    exact hx
  have hcard := subsetSum_fiber_lower H A (u - e) hfiberA
  exact hcard.trans (Finset.card_le_card (by
    intro h hh
    rw [mem_normalizedCosetFiber] at hh ⊢
    rw [Finset.mem_add]
    refine ⟨e, he, (u - e) + h.1, hh, ?_⟩
    abel))

/-! ### The cyclic modulus attached to a remaining phase set -/

/-- The positive divisor `q ∣ b` for which the subgroup generated by `R`
is the subgroup of multiples of `q`. -/
noncomputable def closureModulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : ℕ :=
  Classical.choose (exists_generator_modulus hb
    (AddSubgroup.closure (R : Set (ZMod b))))

lemma closureModulus_spec {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    0 < closureModulus hb R ∧ closureModulus hb R ∣ b ∧
      (∀ x : ZMod b, x ∈ AddSubgroup.closure (R : Set (ZMod b)) →
        closureModulus hb R ∣ x.val) ∧
      (∀ i : ℕ, (i * closureModulus hb R : ZMod b) ∈
        AddSubgroup.closure (R : Set (ZMod b))) :=
  Classical.choose_spec (exists_generator_modulus hb
    (AddSubgroup.closure (R : Set (ZMod b))))

lemma closureModulus_pos {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : 0 < closureModulus hb R :=
  (closureModulus_spec hb R).1

lemma closureModulus_dvd {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : closureModulus hb R ∣ b :=
  (closureModulus_spec hb R).2.1

lemma closure_eq_zmultiples_modulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    AddSubgroup.closure (R : Set (ZMod b)) =
      AddSubgroup.zmultiples (closureModulus hb R : ZMod b) :=
  subgroup_eq_zmultiples_of_generator_modulus _
    (closureModulus_spec hb R).2.2.1
    (closureModulus_spec hb R).2.2.2

lemma mem_closure_iff_modulus_dvd_val {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) (x : ZMod b) :
    x ∈ AddSubgroup.closure (R : Set (ZMod b)) ↔
      closureModulus hb R ∣ x.val := by
  constructor
  · exact (closureModulus_spec hb R).2.2.1 x
  · rintro ⟨i, hi⟩
    have hmultiple := (closureModulus_spec hb R).2.2.2 i
    have hx : x = (i * closureModulus hb R : ℕ) := by
      calc
        x = (x.val : ZMod b) := (ZMod.natCast_zmod_val x).symm
        _ = (closureModulus hb R * i : ℕ) := by rw [hi]
        _ = (i * closureModulus hb R : ℕ) := by rw [mul_comm]
    rw [hx]
    simpa only [Nat.cast_mul] using hmultiple

lemma ncard_closure_eq_div_modulus {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) :
    (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard =
      b / closureModulus hb R :=
  ncard_subgroup_of_generator_modulus hb (closureModulus_pos hb R)
    (closureModulus_dvd hb R) _
    (closureModulus_spec hb R).2.2.1
    (closureModulus_spec hb R).2.2.2

lemma card_elementsInSubgroup_of_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (hAH : (A : Set G) ⊆ H) :
    (elementsInSubgroup H A).card = A.card := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  have himage : (elementsInSubgroup H A).image (fun h : H => h.1) = A := by
    ext x
    simp only [Finset.mem_image, mem_elementsInSubgroup]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hh
    · intro hx
      exact ⟨⟨x, hAH hx⟩, hx, rfl⟩
  calc
    (elementsInSubgroup H A).card =
        ((elementsInSubgroup H A).image (fun h : H => h.1)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := by rw [himage]

/-- The remaining residue set injects into its closure, so the defining
modulus times the number of remaining residues is at most `b`. -/
lemma closureModulus_mul_card_le {b : ℕ} [NeZero b] (hb : 0 < b)
    (R : Finset (ZMod b)) : closureModulus hb R * R.card ≤ b := by
  let H := AddSubgroup.closure (R : Set (ZMod b))
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  have hRcard : R.card ≤ Fintype.card H := by
    rw [← card_elementsInSubgroup_of_subset H R
      (fun _ hx => AddSubgroup.subset_closure hx)]
    exact Finset.card_le_univ _
  have hHcard : Fintype.card H = b / closureModulus hb R := by
    rw [show Fintype.card H = (H : Set (ZMod b)).ncard by
      exact Set.fintypeCard_eq_ncard (H : Set (ZMod b))]
    exact ncard_closure_eq_div_modulus hb R
  rw [hHcard] at hRcard
  calc
    closureModulus hb R * R.card ≤
        closureModulus hb R * (b / closureModulus hb R) :=
      Nat.mul_le_mul_left _ hRcard
    _ = b := Nat.mul_div_cancel' (closureModulus_dvd hb R)

/-- Shrinking the remaining set can only enlarge its cyclic modulus. -/
lemma closureModulus_dvd_of_subset {b : ℕ} [NeZero b] (hb : 0 < b)
    {R T : Finset (ZMod b)} (hTR : T ⊆ R) :
    closureModulus hb R ∣ closureModulus hb T := by
  let q := closureModulus hb R
  let r := closureModulus hb T
  have hrb : r ∣ b := closureModulus_dvd hb T
  have hrle : r ≤ b := Nat.le_of_dvd hb hrb
  by_cases hrEq : r = b
  · change q ∣ r
    rw [hrEq]
    exact closureModulus_dvd hb R
  · have hrlt : r < b := lt_of_le_of_ne hrle hrEq
    have hmemT : (r : ZMod b) ∈ AddSubgroup.closure (T : Set (ZMod b)) := by
      have := (closureModulus_spec hb T).2.2.2 1
      simpa [r] using this
    have hmemR : (r : ZMod b) ∈ AddSubgroup.closure (R : Set (ZMod b)) := by
      apply AddSubgroup.closure_mono (by exact_mod_cast hTR)
      exact hmemT
    have hqval := (closureModulus_spec hb R).2.2.1 (r : ZMod b) hmemR
    simpa [q, r, ZMod.val_natCast, Nat.mod_eq_of_lt hrlt] using hqval

/-- Divisor diversity in an original residue set implies that, after a
remaining set `R` has been set aside, the already-used elements represent
every coset of the subgroup generated by `R`.  Adding any nonempty seed
therefore makes every normalized subgroup fibre nonempty. -/
lemma normalizedCosetFiber_nonempty_of_diverse_used
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
    ∀ u : ZMod b,
      (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
        (E + (R₀ \ R).subsetSum) u).Nonempty := by
  classical
  let q := closureModulus hb R
  have hq : 0 < q := closureModulus_pos hb R
  letI : NeZero q := ⟨hq.ne'⟩
  let U := R₀ \ R
  let f : ZMod b →+ ZMod q :=
    (ZMod.castHom (closureModulus_dvd hb R) (ZMod q)).toAddMonoidHom
  have hUdiverse : ∀ d : ℕ, 1 < d → d ∣ q →
      d - 1 ≤ ((U.toList.map fun x : ZMod b => x.val).filter
        fun a => ¬d ∣ a).length := by
    intro d hd hdq
    have hnonmult : R₀.filter (fun x => ¬d ∣ x.val) ⊆
        U.filter (fun x => ¬d ∣ x.val) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      refine ⟨?_, hx.2⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hx.1, ?_⟩
      intro hxR
      have hqval : q ∣ x.val :=
        (closureModulus_spec hb R).2.2.1 x
          (AddSubgroup.subset_closure hxR)
      exact hx.2 (hdq.trans hqval)
    have hcard := Finset.card_le_card hnonmult
    have hlen : ((U.toList.map fun x : ZMod b => x.val).filter
        fun a => ¬d ∣ a).length =
        (U.filter fun x => ¬d ∣ x.val).card := by
      rw [List.filter_map]
      rw [List.length_map]
      rw [← List.toFinset_card_of_nodup (U.nodup_toList.filter _)]
      rw [List.toFinset_filter]
      simp [Function.comp_def]
    rw [hlen]
    exact (hdiverse d hd (by simpa [q] using hdq)).trans hcard
  have hallVal : Erdos587.listSubsetSums
      ((U.toList.map fun x : ZMod b => x.val).map
        fun a : ℕ => (a : ZMod q)) = Finset.univ :=
    listSubsetSums_mod_eq_univ_of_divisor_diverse hq _ hUdiverse
  have hmap : U.toList.map f =
      (U.toList.map fun x : ZMod b => x.val).map
        fun a : ℕ => (a : ZMod q) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    simp [f, ZMod.castHom_apply]
  have hall : (U.subsetSum.image f) = Finset.univ := by
    rw [← listSubsetSums_toList_eq_subsetSum]
    rw [image_listSubsetSums_map, hmap, hallVal]
  intro u
  obtain ⟨e, he⟩ := hE
  have htarget : f (u - e) ∈ U.subsetSum.image f := by
    rw [hall]
    simp
  obtain ⟨t, ht, hft⟩ := Finset.mem_image.mp htarget
  let H := AddSubgroup.closure (R : Set (ZMod b))
  have hker : e + t - u ∈ H := by
    apply (mem_closure_iff_modulus_dvd_val hb R (e + t - u)).2
    apply (zmod_castHom_eq_zero_iff_val_dvd
      (closureModulus_dvd hb R) (e + t - u)).mp
    change f (e + t - u) = 0
    rw [map_sub, map_add, hft]
    simp [map_sub]
  refine ⟨⟨e + t - u, hker⟩, ?_⟩
  rw [mem_normalizedCosetFiber]
  rw [Finset.mem_add]
  refine ⟨e, he, t, ht, ?_⟩
  simp [sub_eq_add_neg]

/-- If every coset of a nonzero finite subgroup is occupied and every fibre
contains at least one quarter of that subgroup, then the whole set occupies
at least one quarter of the ambient group. -/
lemma card_le_four_mul_card_of_all_coset_fibers_large
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (S : Finset G)
    (hlarge : ∀ u : G,
      (H : Set G).ncard ≤ 4 * (normalizedCosetFiber H S u).card) :
    Fintype.card G ≤ 4 * S.card := by
  classical
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  let I : Finset (Σ _u : G, H) :=
    (Finset.univ : Finset G).sigma fun u => normalizedCosetFiber H S u
  let J : Finset (G × H) := S ×ˢ (Finset.univ : Finset H)
  have hIJ : I.card = J.card := by
    apply Finset.card_bij'
        (fun p _ => (p.1 + p.2.1, p.2))
        (fun p _ => ⟨p.1 - p.2.1, p.2⟩)
    · rintro ⟨u, h⟩ hp
      simp [sub_eq_add_neg]
    · rintro ⟨s, h⟩ hp
      simp [sub_eq_add_neg]
    · intro p hp
      dsimp only [J]
      rw [Finset.mem_product]
      dsimp only [I] at hp
      have hpFiber := (Finset.mem_sigma.mp hp).2
      exact ⟨mem_normalizedCosetFiber.mp hpFiber, Finset.mem_univ _⟩
    · intro p hp
      dsimp only [I]
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mem_normalizedCosetFiber]
      dsimp only [J] at hp
      rw [Finset.mem_product] at hp
      simpa [sub_eq_add_neg] using hp.1
  have hsum : Fintype.card G * (H : Set G).ncard ≤ 4 * I.card := by
    calc
      Fintype.card G * (H : Set G).ncard =
          ∑ _u : G, (H : Set G).ncard := by simp
      _ ≤ ∑ u : G, 4 * (normalizedCosetFiber H S u).card := by
        exact Finset.sum_le_sum fun u _ => hlarge u
      _ = 4 * I.card := by
        simp only [I, Finset.card_sigma]
        simp [Finset.mul_sum]
  have hHcard : (H : Set G).ncard = Fintype.card H := by
    exact (Set.fintypeCard_eq_ncard (H : Set G)).symm
  have hHpos : 0 < (H : Set G).ncard := by
    rw [hHcard]
    exact Fintype.card_pos
  have hIcard : I.card = S.card * (H : Set G).ncard := by
    simp only [hIJ, J, Finset.card_product, Finset.card_univ, hHcard]
  rw [hIcard] at hsum
  have hmul : Fintype.card G * (H : Set G).ncard ≤
      (4 * S.card) * (H : Set G).ncard := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  exact Nat.le_of_mul_le_mul_right hmul hHpos

/-- The modular subset-sum set after adjoining one unused element is the
old set together with one translate. -/
lemma seededSubsetSum_insert_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (E A : Finset G) (x : G) (hx : x ∉ A) :
    E + (insert x A).subsetSum =
      (E + A.subsetSum) ∪
        Erdos587.addTranslate x (E + A.subsetSum) := by
  rw [subsetSum_insert_eq A x hx, Finset.add_union]
  congr 1
  ext z
  constructor
  · intro hz
    obtain ⟨e, he, t, ht, hzt⟩ := Finset.mem_add.mp hz
    rw [Erdos587.mem_addTranslate]
    apply Finset.mem_add.mpr
    refine ⟨e, he, -x + t, ?_, ?_⟩
    · exact Erdos587.mem_addTranslate.mp ht
    · calc
        e + (-x + t) = -x + (e + t) := by abel
        _ = -x + z := by rw [hzt]
  · intro hz
    rw [Erdos587.mem_addTranslate] at hz
    obtain ⟨e, he, t, ht, hzt⟩ := Finset.mem_add.mp hz
    apply Finset.mem_add.mpr
    refine ⟨e, he, x + t, ?_, ?_⟩
    · rw [Erdos587.mem_addTranslate]
      simpa using ht
    · calc
        e + (x + t) = x + (e + t) := by abel
        _ = x + (-x + z) := by rw [hzt]
        _ = z := by abel

lemma sdiff_erase_eq_insert_sdiff
    {α : Type*} [DecidableEq α] {R₀ R : Finset α} {x : α}
    (hxR : x ∈ R) (hR : R ⊆ R₀) :
    R₀ \ R.erase x = insert x (R₀ \ R) := by
  ext y
  by_cases hyx : y = x
  · subst y
    simp [hxR, hR hxR]
  · simp [hyx]

/-- A growth phase is witnessed by a coset fibre no larger than one quarter
of the remaining residue set. -/
def IsModularGrowthPhase {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) : Prop :=
  ∃ u : ZMod b,
    4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) u).card ≤ R.card

/-- An unsaturated fibre has less than one quarter of its subgroup. -/
def HasUnsaturatedFiber {b : ℕ} [NeZero b] (R₀ R E : Finset (ZMod b)) :
    Prop :=
  ∃ u : ZMod b,
    4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) u).card <
        (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard

lemma exists_internal_growth_of_modularGrowthPhase
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hRne : R.Nonempty) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hgrowth : IsModularGrowthPhase hb R₀ R E) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    ∃ x : H, x.1 ∈ R ∧
      3 * T.card ≤ 2 * (T ∪ Erdos587.addTranslate x T).card := by
  classical
  dsimp only
  let H := AddSubgroup.closure (R : Set (ZMod b))
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
  let X := liftFinsetToClosure R
  obtain ⟨u, huSmall⟩ := hgrowth
  have huNe := normalizedCosetFiber_nonempty_of_diverse_used
    hb R₀ R E hE hdiverse u
  have hTle : T.card ≤ (normalizedCosetFiber H
      (E + (R₀ \ R).subsetSum) u).card := by
    exact seededSubsetSum_fiber_lower H E (R₀ \ R) u huNe
  have hTne : T.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp only [T]
    rw [Finset.mem_subsetSum_iff]
    exact ⟨∅, Finset.empty_subset _, by simp⟩
  have hXne : X.Nonempty := by
    apply Finset.card_pos.mp
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    exact Finset.card_pos.mpr hRne
  have hsmall : 2 * T.card < X.card := by
    rw [show X.card = R.card by exact card_liftFinsetToClosure R]
    have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
    have : 4 * T.card ≤ R.card :=
      (Nat.mul_le_mul_left 4 hTle).trans huSmall
    omega
  obtain ⟨x, hx, hxGrowth⟩ := exists_three_halves_growth hTne hXne hsmall
  exact ⟨x, mem_liftFinsetToClosure.mp hx, hxGrowth⟩

lemma exists_large_step_of_unsaturatedFiber
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hRne : R.Nonempty) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hnotGrowth : ¬IsModularGrowthPhase hb R₀ R E)
    (hunsat : HasUnsaturatedFiber R₀ R E) :
    ∃ x ∈ R, R.card ≤ 16 *
      (Erdos360.translationNew (E + (R₀ \ R).subsetSum) x).card := by
  classical
  obtain ⟨u, huSmall⟩ := hunsat
  have huNe := normalizedCosetFiber_nonempty_of_diverse_used
    hb R₀ R E hE hdiverse u
  have hlarge : R.card < 4 *
      (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
        (E + (R₀ \ R).subsetSum) u).card := by
    by_contra hnot
    apply hnotGrowth
    exact ⟨u, by omega⟩
  exact exists_translationNew_large_of_normalizedCosetFiber
    huNe hRne hlarge huSmall

lemma saturated_modularPhase_card
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card)
    (hsaturated : ¬HasUnsaturatedFiber R₀ R E) :
    b ≤ 4 * (E + (R₀ \ R).subsetSum).card := by
  have hlarge : ∀ u : ZMod b,
      (AddSubgroup.closure (R : Set (ZMod b)) : Set (ZMod b)).ncard ≤
        4 * (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
          (E + (R₀ \ R).subsetSum) u).card := by
    intro u
    have huNe := normalizedCosetFiber_nonempty_of_diverse_used
      hb R₀ R E hE hdiverse u
    by_contra hnot
    apply hsaturated
    exact ⟨u, by omega⟩
  simpa [ZMod.card] using
    (card_le_four_mul_card_of_all_coset_fibers_large
      (AddSubgroup.closure (R : Set (ZMod b)))
      (E + (R₀ \ R).subsetSum) hlarge)

/-! ### The deterministic modular phase recursion -/

/-- Diversity only where it can be used by a phase whose remainder still
contains at least half of the original residues. -/
def PhaseDiverse {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ : Finset (ZMod b)) : Prop :=
  ∀ R : Finset (ZMod b), R₀.card ≤ 2 * R.card →
    ∀ d : ℕ, 1 < d → d ∣ closureModulus hb R →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card

lemma phaseDiverse_of_bounded
    {b : ℕ} [NeZero b] (hb : 0 < b) (R₀ : Finset (ZMod b))
    (hdiverse : ∀ d : ℕ, 1 < d → d ∣ b →
      d * R₀.card ≤ 2 * b →
      d - 1 ≤ (R₀.filter fun x => ¬d ∣ x.val).card) :
    PhaseDiverse hb R₀ := by
  intro R hwide d hd hdq
  apply hdiverse d hd (hdq.trans (closureModulus_dvd hb R))
  have hdle : d ≤ closureModulus hb R :=
    Nat.le_of_dvd (closureModulus_pos hb R) hdq
  have hclosure := closureModulus_mul_card_le hb R
  nlinarith

/-- A canonical choice for the next phase.  In a growth phase it uses the
internal multiplicative-growth witness; in an unsaturated phase it uses the
large-translation witness; otherwise it removes an arbitrary remaining
element. -/
noncomputable def modularPhasePick
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) : ZMod b := by
  classical
  by_cases hR : R.Nonempty
  · by_cases hwide : R₀.card ≤ 2 * R.card
    · by_cases hg : IsModularGrowthPhase hb R₀ R E
      · exact (Classical.choose
          (exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
            (hdiverse R hwide) hg)).1
      · by_cases hu : HasUnsaturatedFiber R₀ R E
        · exact Classical.choose
            (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
              (hdiverse R hwide) hg hu)
        · exact hR.choose
    · exact hR.choose
  · exact 0

lemma modularPhasePick_mem
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty) :
    modularPhasePick hb R₀ E hE hdiverse R ∈ R := by
  classical
  unfold modularPhasePick
  rw [dif_pos hR]
  by_cases hwide : R₀.card ≤ 2 * R.card
  · rw [dif_pos hwide]
    by_cases hg : IsModularGrowthPhase hb R₀ R E
    · rw [dif_pos hg]
      exact (Classical.choose_spec
          (exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
            (hdiverse R hwide) hg)).1
    · rw [dif_neg hg]
      by_cases hu : HasUnsaturatedFiber R₀ R E
      · rw [dif_pos hu]
        exact (Classical.choose_spec
          (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
            (hdiverse R hwide) hg hu)).1
      · rw [dif_neg hu]
        exact hR.choose_spec
  · rw [dif_neg hwide]
    exact hR.choose_spec

lemma modularPhasePick_internal_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty)
    (hwide : R₀.card ≤ 2 * R.card)
    (hg : IsModularGrowthPhase hb R₀ R E) :
    let H := AddSubgroup.closure (R : Set (ZMod b))
    let T := (elementsInSubgroup H (R₀ \ R)).subsetSum
    3 * T.card ≤ 2 *
      (T ∪ Erdos587.addTranslate
        (⟨modularPhasePick hb R₀ E hE hdiverse R,
          AddSubgroup.subset_closure
            (modularPhasePick_mem hb R₀ E hE hdiverse R hR)⟩ : H) T).card := by
  classical
  dsimp only
  let hex := exists_internal_growth_of_modularGrowthPhase hb R₀ R E hR hE
    (hdiverse R hwide) hg
  let x := Classical.choose hex
  have hxSpec := (Classical.choose_spec hex).2
  have hpick : modularPhasePick hb R₀ E hE hdiverse R = x.1 := by
    simp only [modularPhasePick, dif_pos hR, dif_pos hwide, dif_pos hg, hex, x]
  have hsubtype :
      (⟨modularPhasePick hb R₀ E hE hdiverse R,
        AddSubgroup.subset_closure
          (modularPhasePick_mem hb R₀ E hE hdiverse R hR)⟩ :
          AddSubgroup.closure (R : Set (ZMod b))) = x := by
    exact Subtype.ext hpick
  rw [hsubtype]
  exact hxSpec

lemma modularPhasePick_unsaturated_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (R : Finset (ZMod b)) (hR : R.Nonempty)
    (hwide : R₀.card ≤ 2 * R.card)
    (hg : ¬IsModularGrowthPhase hb R₀ R E)
    (hu : HasUnsaturatedFiber R₀ R E) :
    R.card ≤ 16 * (Erdos360.translationNew
      (E + (R₀ \ R).subsetSum)
      (modularPhasePick hb R₀ E hE hdiverse R)).card := by
  classical
  unfold modularPhasePick
  rw [dif_pos hR, dif_pos hwide, dif_neg hg, dif_pos hu]
  exact (Classical.choose_spec
    (exists_large_step_of_unsaturatedFiber hb R₀ R E hR hE
      (hdiverse R hwide) hg hu)).2

noncomputable def modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    ℕ → Finset (ZMod b)
  | 0 => R₀
  | i + 1 =>
      let R := modularRemainder hb R₀ E hE hdiverse i
      if R.Nonempty then
        R.erase (modularPhasePick hb R₀ E hE hdiverse R)
      else R

noncomputable def modularPhaseSums
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) : Finset (ZMod b) :=
  E + (R₀ \ modularRemainder hb R₀ E hE hdiverse i).subsetSum

@[simp] lemma modularRemainder_zero
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    modularRemainder hb R₀ E hE hdiverse 0 = R₀ := rfl

lemma modularRemainder_succ_of_nonempty
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) (hne : (modularRemainder hb R₀ E hE hdiverse i).Nonempty) :
    modularRemainder hb R₀ E hE hdiverse (i + 1) =
      (modularRemainder hb R₀ E hE hdiverse i).erase
        (modularPhasePick hb R₀ E hE hdiverse
          (modularRemainder hb R₀ E hE hdiverse i)) := by
  change (if (modularRemainder hb R₀ E hE hdiverse i).Nonempty then
      (modularRemainder hb R₀ E hE hdiverse i).erase
        (modularPhasePick hb R₀ E hE hdiverse
          (modularRemainder hb R₀ E hE hdiverse i))
    else modularRemainder hb R₀ E hE hdiverse i) = _
  rw [if_pos hne]

lemma modularRemainder_succ_subset
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    modularRemainder hb R₀ E hE hdiverse (i + 1) ⊆
      modularRemainder hb R₀ E hE hdiverse i := by
  let R := modularRemainder hb R₀ E hE hdiverse i
  change (if R.Nonempty then
      R.erase (modularPhasePick hb R₀ E hE hdiverse R) else R) ⊆ R
  split_ifs
  · exact Finset.erase_subset _ _
  · exact fun _ hx => hx

lemma modularRemainder_subset_initial
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) :
    ∀ i : ℕ, modularRemainder hb R₀ E hE hdiverse i ⊆ R₀ := by
  intro i
  induction i with
  | zero => exact fun _ hx => hx
  | succ i ih =>
      exact (modularRemainder_succ_subset hb R₀ E hE hdiverse i).trans ih

lemma card_modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (modularRemainder hb R₀ E hE hdiverse i).card = R₀.card - i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hi' : i ≤ R₀.card := by omega
      have hcard := ih hi'
      have hne : (modularRemainder hb R₀ E hE hdiverse i).Nonempty := by
        apply Finset.card_pos.mp
        rw [hcard]
        omega
      rw [modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hne]
      rw [Finset.card_erase_of_mem
        (modularPhasePick_mem hb R₀ E hE hdiverse _ hne)]
      omega

lemma card_used_modularRemainder
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i ≤ R₀.card) :
    (R₀ \ modularRemainder hb R₀ E hE hdiverse i).card = i := by
  rw [Finset.card_sdiff_of_subset
    (modularRemainder_subset_initial hb R₀ E hE hdiverse i)]
  rw [card_modularRemainder hb R₀ E hE hdiverse hi]
  omega

lemma modularPhaseSums_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card) :
    modularPhaseSums hb R₀ E hE hdiverse (i + 1) =
      modularPhaseSums hb R₀ E hE hdiverse i ∪
        Erdos587.addTranslate
          (modularPhasePick hb R₀ E hE hdiverse
            (modularRemainder hb R₀ E hE hdiverse i))
          (modularPhaseSums hb R₀ E hE hdiverse i) := by
  let R := modularRemainder hb R₀ E hE hdiverse i
  have hcard : R.card = R₀.card - i :=
    card_modularRemainder hb R₀ E hE hdiverse (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hRsub : R ⊆ R₀ :=
    modularRemainder_subset_initial hb R₀ E hE hdiverse i
  have hxR := modularPhasePick_mem hb R₀ E hE hdiverse R hRne
  have hxNot : modularPhasePick hb R₀ E hE hdiverse R ∉ R₀ \ R := by
    simp only [Finset.mem_sdiff]
    exact fun h => h.2 hxR
  rw [modularPhaseSums, modularPhaseSums]
  rw [modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hRne]
  rw [sdiff_erase_eq_insert_sdiff hxR hRsub]
  exact seededSubsetSum_insert_eq E (R₀ \ R)
    (modularPhasePick hb R₀ E hE hdiverse R) hxNot

/-- The numerical size of the subset sums made from already-used elements
which lie in the subgroup generated by the current remainder. -/
noncomputable def modularInternalCard
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) : ℕ :=
  let H := AddSubgroup.closure (R : Set (ZMod b))
  (elementsInSubgroup H (R₀ \ R)).subsetSum.card

lemma elementsInSubgroup_mono
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) {A B : Finset G} (hAB : A ⊆ B) :
    elementsInSubgroup H A ⊆ elementsInSubgroup H B := by
  intro x hx
  rw [mem_elementsInSubgroup] at hx ⊢
  exact hAB hx

lemma modularInternalCard_mono_of_subset_of_closure_eq
    {b : ℕ} [NeZero b] (R₀ : Finset (ZMod b))
    {R T : Finset (ZMod b)} (hTR : T ⊆ R)
    (hclosure : AddSubgroup.closure (T : Set (ZMod b)) =
      AddSubgroup.closure (R : Set (ZMod b))) :
    modularInternalCard R₀ R ≤ modularInternalCard R₀ T := by
  classical
  let HR := AddSubgroup.closure (R : Set (ZMod b))
  let HT := AddSubgroup.closure (T : Set (ZMod b))
  have hused : R₀ \ R ⊆ R₀ \ T := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hx.1, fun hxT => hx.2 (hTR hxT)⟩
  have hsub : elementsInSubgroup HR (R₀ \ R) ⊆
      elementsInSubgroup HR (R₀ \ T) :=
    elementsInSubgroup_mono HR hused
  have hsums := Finset.subsetSum_mono hsub
  have hcard := Finset.card_le_card hsums
  dsimp only [modularInternalCard]
  rw [hclosure]
  exact hcard

lemma closure_eq_of_closureModulus_eq
    {b : ℕ} [NeZero b] (hb : 0 < b) {R T : Finset (ZMod b)}
    (hmod : closureModulus hb R = closureModulus hb T) :
    AddSubgroup.closure (R : Set (ZMod b)) =
      AddSubgroup.closure (T : Set (ZMod b)) := by
  rw [closure_eq_zmultiples_modulus hb R,
    closure_eq_zmultiples_modulus hb T, hmod]

lemma modularRemainder_antitone
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j) :
    modularRemainder hb R₀ E hE hdiverse j ⊆
      modularRemainder hb R₀ E hE hdiverse i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction k with
  | zero => exact fun _ hx => hx
  | succ k ih =>
      exact (modularRemainder_succ_subset hb R₀ E hE hdiverse (i + k)).trans
        (ih (by omega))

lemma modularInternalCard_mono_of_modulus_eq
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j)
    (hmod : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse j)) :
    modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse i) ≤
      modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse j) := by
  apply modularInternalCard_mono_of_subset_of_closure_eq R₀
    (modularRemainder_antitone hb R₀ E hE hdiverse hij)
  exact (closure_eq_of_closureModulus_eq hb hmod).symm

lemma elementsInSubgroup_insert
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G) (A : Finset G) (x : H) (hx : x.1 ∉ A) :
    elementsInSubgroup H (insert x.1 A) =
      insert x (elementsInSubgroup H A) := by
  ext y
  simp only [mem_elementsInSubgroup, Finset.mem_insert, Subtype.coe_inj]

lemma modularInternalCard_growth_step
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card)
    (hwide : R₀.card ≤ 2 *
      (modularRemainder hb R₀ E hE hdiverse i).card)
    (hg : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E)
    (hmod : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse (i + 1))) :
    3 * modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse i) ≤
      2 * modularInternalCard R₀
        (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
  classical
  let R := modularRemainder hb R₀ E hE hdiverse i
  let T := modularRemainder hb R₀ E hE hdiverse (i + 1)
  let H := AddSubgroup.closure (R : Set (ZMod b))
  let U := R₀ \ R
  let x := modularPhasePick hb R₀ E hE hdiverse R
  have hRcard : R.card = R₀.card - i :=
    card_modularRemainder hb R₀ E hE hdiverse (by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
  have hxR : x ∈ R := modularPhasePick_mem hb R₀ E hE hdiverse R hRne
  have hxU : x ∉ U := by
    simp only [U, Finset.mem_sdiff]
    exact fun h => h.2 hxR
  have hT : T = R.erase x := by
    exact modularRemainder_succ_of_nonempty hb R₀ E hE hdiverse i hRne
  have hused : R₀ \ T = insert x U := by
    rw [hT]
    exact sdiff_erase_eq_insert_sdiff hxR
      (modularRemainder_subset_initial hb R₀ E hE hdiverse i)
  let xH : H := ⟨x, AddSubgroup.subset_closure hxR⟩
  have hgrowth := modularPhasePick_internal_growth
    hb R₀ E hE hdiverse R hRne hwide hg
  have hclosure : AddSubgroup.closure (T : Set (ZMod b)) = H := by
    exact (closure_eq_of_closureModulus_eq hb hmod).symm
  have hnext : elementsInSubgroup H (R₀ \ T) =
      insert xH (elementsInSubgroup H U) := by
    rw [hused]
    exact elementsInSubgroup_insert H U xH hxU
  have hsumNext : (elementsInSubgroup H (R₀ \ T)).subsetSum =
      (elementsInSubgroup H U).subsetSum ∪
        Erdos587.addTranslate xH (elementsInSubgroup H U).subsetSum := by
    rw [hnext]
    exact subsetSum_insert_eq _ _ (by
      rw [mem_elementsInSubgroup]
      exact hxU)
  dsimp only [modularInternalCard]
  rw [show AddSubgroup.closure (T : Set (ZMod b)) = H by exact hclosure]
  rw [hsumNext]
  exact hgrowth

lemma log_two_lt_of_double_le {a c : ℕ} (ha : 0 < a)
    (hac : 2 * a ≤ c) : Nat.log 2 a < Nat.log 2 c := by
  have hstep : Nat.log 2 a < Nat.log 2 (a * 2) := by
    rw [Nat.log_mul_base (by omega) ha.ne']
    omega
  exact hstep.trans_le (Nat.log_mono_right (by simpa [mul_comm] using hac))

lemma eq_of_dvd_of_log_two_eq {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hac : a ∣ c) (hlog : Nat.log 2 a = Nat.log 2 c) : a = c := by
  obtain ⟨r, rfl⟩ := hac
  have hr : 0 < r := by
    by_contra h
    have : r = 0 := Nat.eq_zero_of_not_pos h
    subst r
    simp at hc
  by_contra hne
  have hrne : r ≠ 1 := by
    intro hrone
    subst r
    simp at hne
  have hr2 : 2 ≤ r := by
    omega
  have hdouble : 2 * a ≤ a * r := by
    nlinarith
  exact (Nat.ne_of_lt (log_two_lt_of_double_le ha hdouble)) hlog

lemma modularInternalCard_pos
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) :
    0 < modularInternalCard R₀ R := by
  classical
  apply Finset.card_pos.mpr
  exact ⟨0, Finset.zero_mem_subsetSum⟩

lemma modularInternalCard_le
    {b : ℕ} [NeZero b] (R₀ R : Finset (ZMod b)) :
    modularInternalCard R₀ R ≤ b := by
  classical
  let H := AddSubgroup.closure (R : Set (ZMod b))
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H => h.1) Subtype.val_injective
  calc
    modularInternalCard R₀ R =
        (elementsInSubgroup H (R₀ \ R)).subsetSum.card := rfl
    _ ≤ Fintype.card H := Finset.card_le_univ _
    _ ≤ Fintype.card (ZMod b) :=
      Fintype.card_le_of_injective (fun h : H => h.1) Subtype.val_injective
    _ = b := ZMod.card b

lemma closureModulus_eq_between
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i t j : ℕ} (hit : i ≤ t) (htj : t ≤ j)
    (hij : closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse j)) :
    closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse i) =
      closureModulus hb
        (modularRemainder hb R₀ E hE hdiverse t) := by
  apply Nat.dvd_antisymm
  · exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hit)
  · rw [hij]
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse htj)

/-- The phase indices at which the selector invokes the internal
multiplicative-growth alternative. -/
noncomputable def modularGrowthIndices
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i =>
    IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E

/-- Binary logarithms of the current subgroup modulus and its internal
subset-sum cardinality.  Both coordinates lie between zero and `log₂ b`. -/
noncomputable def modularGrowthCode
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) : Fin (Nat.log 2 b + 1) × Fin (Nat.log 2 b + 1) :=
  (⟨Nat.log 2 (closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse i)), by
      have hle : closureModulus hb
          (modularRemainder hb R₀ E hE hdiverse i) ≤ b :=
        Nat.le_of_dvd hb (closureModulus_dvd hb _)
      exact Nat.lt_succ_of_le (Nat.log_mono_right hle)⟩,
   ⟨Nat.log 2 (modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse i)), by
      exact Nat.lt_succ_of_le (Nat.log_mono_right
        (modularInternalCard_le R₀ _))⟩)

lemma exists_three_ordered_of_two_lt_card {S : Finset ℕ}
    (hS : 2 < S.card) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ k ∈ S, i < j ∧ j < k := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hS
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · exact ⟨a, ha, b, hb, c, hc, hab', hbc'⟩
      · exact ⟨a, ha, c, hc, b, hb, hac', hcb'⟩
    · exact ⟨c, hc, a, ha, b, hb, hca', hab'⟩
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · exact ⟨b, hb, a, ha, c, hc, hba', hac'⟩
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
      · exact ⟨b, hb, c, hc, a, ha, hbc', hca'⟩
      · exact ⟨c, hc, b, hb, a, ha, hcb', hba'⟩

lemma modularGrowthCode_not_three
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j k : ℕ} (hij : i < j) (hjk : j < k)
    (hk : 2 * (k + 1) ≤ R₀.card)
    (hgi : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E)
    (hgj : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse j) E)
    (hcodeIJ : modularGrowthCode hb R₀ E hE hdiverse i =
      modularGrowthCode hb R₀ E hE hdiverse j)
    (hcodeJK : modularGrowthCode hb R₀ E hE hdiverse j =
      modularGrowthCode hb R₀ E hE hdiverse k) : False := by
  let Ri := modularRemainder hb R₀ E hE hdiverse i
  let Rj := modularRemainder hb R₀ E hE hdiverse j
  let Rk := modularRemainder hb R₀ E hE hdiverse k
  let qi := closureModulus hb Ri
  let qj := closureModulus hb Rj
  let qk := closureModulus hb Rk
  let ci := modularInternalCard R₀ Ri
  let cj := modularInternalCard R₀ Rj
  let ck := modularInternalCard R₀ Rk
  have hqLogIJ : Nat.log 2 qi = Nat.log 2 qj :=
    congrArg (fun z => z.1.val) hcodeIJ
  have hqLogJK : Nat.log 2 qj = Nat.log 2 qk :=
    congrArg (fun z => z.1.val) hcodeJK
  have hcLogIJ : Nat.log 2 ci = Nat.log 2 cj :=
    congrArg (fun z => z.2.val) hcodeIJ
  have hcLogJK : Nat.log 2 cj = Nat.log 2 ck :=
    congrArg (fun z => z.2.val) hcodeJK
  have hqDivIJ : qi ∣ qj := by
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hij.le)
  have hqDivJK : qj ∣ qk := by
    exact closureModulus_dvd_of_subset hb
      (modularRemainder_antitone hb R₀ E hE hdiverse hjk.le)
  have hqEqIJ : qi = qj :=
    eq_of_dvd_of_log_two_eq (closureModulus_pos hb Ri)
      (closureModulus_pos hb Rj) hqDivIJ hqLogIJ
  have hqEqJK : qj = qk :=
    eq_of_dvd_of_log_two_eq (closureModulus_pos hb Rj)
      (closureModulus_pos hb Rk) hqDivJK hqLogJK
  have hqiSucc : closureModulus hb Ri = closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
    exact closureModulus_eq_between hb R₀ E hE hdiverse
      (by omega) (by omega) hqEqIJ
  have hqjSucc : closureModulus hb Rj = closureModulus hb
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) := by
    exact closureModulus_eq_between hb R₀ E hE hdiverse
      (by omega) (by omega) hqEqJK
  have hgrowI : 3 * ci ≤ 2 * modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) := by
    exact modularInternalCard_growth_step hb R₀ E hE hdiverse
      (by omega) (by
        rw [card_modularRemainder hb R₀ E hE hdiverse (by omega)]
        omega) hgi hqiSucc
  have hmonoIJ : modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (i + 1)) ≤ cj := by
    apply modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega)
    exact hqiSucc.symm.trans hqEqIJ
  have hgrowJ : 3 * cj ≤ 2 * modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) := by
    exact modularInternalCard_growth_step hb R₀ E hE hdiverse
      (by omega) (by
        rw [card_modularRemainder hb R₀ E hE hdiverse (by omega)]
        omega) hgj hqjSucc
  have hmonoJK : modularInternalCard R₀
      (modularRemainder hb R₀ E hE hdiverse (j + 1)) ≤ ck := by
    apply modularInternalCard_mono_of_modulus_eq hb R₀ E hE hdiverse
      (by omega)
    exact hqjSucc.symm.trans hqEqJK
  have hthreeI : 3 * ci ≤ 2 * cj := hgrowI.trans (Nat.mul_le_mul_left 2 hmonoIJ)
  have hthreeJ : 3 * cj ≤ 2 * ck := hgrowJ.trans (Nat.mul_le_mul_left 2 hmonoJK)
  have hdouble : 2 * ci ≤ ck := by
    have hcipos : 0 < ci := modularInternalCard_pos R₀ Ri
    omega
  have hloglt : Nat.log 2 ci < Nat.log 2 ck :=
    log_two_lt_of_double_le (modularInternalCard_pos R₀ Ri) hdouble
  exact (Nat.ne_of_lt hloglt) (hcLogIJ.trans hcLogJK)

theorem card_modularGrowthIndices_le
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card) :
    (modularGrowthIndices hb R₀ E hE hdiverse k).card ≤
      2 * (Nat.log 2 b + 1) ^ 2 := by
  classical
  let G := modularGrowthIndices hb R₀ E hE hdiverse k
  let C := Fin (Nat.log 2 b + 1) × Fin (Nat.log 2 b + 1)
  let f : ℕ → C := modularGrowthCode hb R₀ E hE hdiverse
  by_contra hnot
  have hlarge : (Finset.univ : Finset C).card * 2 < G.card := by
    simp only [Finset.card_univ, C, Fintype.card_prod, Fintype.card_fin]
    dsimp only [G] at hnot ⊢
    have hgt : 2 * (Nat.log 2 b + 1) ^ 2 <
        (modularGrowthIndices hb R₀ E hE hdiverse k).card :=
      Nat.lt_of_not_ge hnot
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hgt
  obtain ⟨y, -, hy⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := G) (t := Finset.univ) (f := f)
      (n := 2) (fun _ _ => Finset.mem_univ _) hlarge
  let S := G.filter fun i => f i = y
  have hScard : 2 < S.card := by
    simpa only [S] using hy
  obtain ⟨i, hiS, j, hjS, q, hqS, hij, hjq⟩ :=
    exists_three_ordered_of_two_lt_card hScard
  have hiG : i ∈ G := (Finset.mem_filter.mp hiS).1
  have hjG : j ∈ G := (Finset.mem_filter.mp hjS).1
  have hqG : q ∈ G := (Finset.mem_filter.mp hqS).1
  have hfi : f i = y := (Finset.mem_filter.mp hiS).2
  have hfj : f j = y := (Finset.mem_filter.mp hjS).2
  have hfq : f q = y := (Finset.mem_filter.mp hqS).2
  have hiData := Finset.mem_filter.mp hiG
  have hjData := Finset.mem_filter.mp hjG
  have hqData := Finset.mem_filter.mp hqG
  exact modularGrowthCode_not_three hb R₀ E hE hdiverse hij hjq
    (by
      have hqk : q < k := Finset.mem_range.mp hqData.1
      omega)
    hiData.2 hjData.2 (hfi.trans hfj.symm) (hfj.trans hfq.symm)

lemma card_union_addTranslate_eq
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (x : G) :
    (S ∪ Erdos587.addTranslate x S).card =
      S.card + (Erdos360.translationNew S x).card := by
  have hsdiff := Finset.card_sdiff_add_card
    (Erdos587.addTranslate x S) S
  dsimp only [Erdos360.translationNew] at hsdiff ⊢
  rw [Finset.union_comm] at hsdiff
  omega

lemma card_modularPhaseSums_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i : ℕ} (hi : i < R₀.card) :
    (modularPhaseSums hb R₀ E hE hdiverse (i + 1)).card =
      (modularPhaseSums hb R₀ E hE hdiverse i).card +
        (Erdos360.translationNew
          (modularPhaseSums hb R₀ E hE hdiverse i)
          (modularPhasePick hb R₀ E hE hdiverse
            (modularRemainder hb R₀ E hE hdiverse i))).card := by
  rw [modularPhaseSums_succ hb R₀ E hE hdiverse hi]
  exact card_union_addTranslate_eq _ _

lemma card_modularGrowthIndices_succ
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    (modularGrowthIndices hb R₀ E hE hdiverse (i + 1)).card =
      if IsModularGrowthPhase hb R₀
          (modularRemainder hb R₀ E hE hdiverse i) E then
        (modularGrowthIndices hb R₀ E hE hdiverse i).card + 1
      else (modularGrowthIndices hb R₀ E hE hdiverse i).card := by
  classical
  by_cases hg : IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E <;>
    simp [modularGrowthIndices, Finset.range_add_one, Finset.filter_insert, hg]

lemma card_modularGrowthIndices_le_index
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    (i : ℕ) :
    (modularGrowthIndices hb R₀ E hE hdiverse i).card ≤ i := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_range i)

lemma mul_pred_potential_le (u r : ℕ) (hr : 0 < r) :
    (u + 1) * (r - 1) ≤ u * r + r := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simp only [Nat.succ_sub_one]
  nlinarith

/-- If no saturated phase occurs, every nongrowth phase contributes a
linear number of genuinely new residues.  This potential packages all those
increments while allowing the remainder to shrink. -/
theorem unsaturated_modularPhase_potential
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card)
    (hu : ∀ i < k, HasUnsaturatedFiber R₀
      (modularRemainder hb R₀ E hE hdiverse i) E) :
    (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
        (R₀.card - k) ≤
      16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < R₀.card := by omega
      have hkprev : k ≤ R₀.card := hklt.le
      have hhalfPrev : 2 * k ≤ R₀.card := by omega
      have huPrev : ∀ i < k, HasUnsaturatedFiber R₀
          (modularRemainder hb R₀ E hE hdiverse i) E := by
        intro i hi
        exact hu i (by omega)
      have hIH := ih hhalfPrev huPrev
      let R := modularRemainder hb R₀ E hE hdiverse k
      let S := modularPhaseSums hb R₀ E hE hdiverse k
      let x := modularPhasePick hb R₀ E hE hdiverse R
      let D := Erdos360.translationNew S x
      have hRcard : R.card = R₀.card - k :=
        card_modularRemainder hb R₀ E hE hdiverse hkprev
      have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hRcard]; omega)
      have hwide : R₀.card ≤ 2 * R.card := by rw [hRcard]; omega
      have huK : HasUnsaturatedFiber R₀ R E := hu k (by omega)
      have hScard :
          (modularPhaseSums hb R₀ E hE hdiverse (k + 1)).card =
            S.card + D.card := by
        exact card_modularPhaseSums_succ hb R₀ E hE hdiverse hklt
      by_cases hg : IsModularGrowthPhase hb R₀ R E
      · have hGcard := card_modularGrowthIndices_succ
          hb R₀ E hE hdiverse k
        rw [if_pos hg] at hGcard
        rw [hGcard, hScard]
        have hGle := card_modularGrowthIndices_le_index
          hb R₀ E hE hdiverse k
        have hrem : R₀.card - (k + 1) ≤ R₀.card - k := by omega
        have hleft :
            (k + 1 - ((modularGrowthIndices hb R₀ E hE hdiverse k).card + 1)) *
                (R₀.card - (k + 1)) ≤
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
                (R₀.card - k) := by
          apply Nat.mul_le_mul
          · omega
          · exact hrem
        exact hleft.trans (hIH.trans (Nat.mul_le_mul_left 16
          (Nat.le_add_right S.card D.card)))
      · have hGcard := card_modularGrowthIndices_succ
          hb R₀ E hE hdiverse k
        rw [if_neg hg] at hGcard
        have hnew : R.card ≤ 16 * D.card := by
          exact modularPhasePick_unsaturated_growth
            hb R₀ E hE hdiverse R hRne hwide hg huK
        rw [hGcard, hScard]
        have hGle := card_modularGrowthIndices_le_index
          hb R₀ E hE hdiverse k
        have hremSucc : R₀.card - (k + 1) = (R₀.card - k) - 1 := by
          omega
        have hphaseSucc :
            k + 1 - (modularGrowthIndices hb R₀ E hE hdiverse k).card =
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) + 1 := by
          omega
        rw [hremSucc, hphaseSucc]
        calc
          ((k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) + 1) *
                ((R₀.card - k) - 1) ≤
              (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
                (R₀.card - k) + R.card := by
            rw [hRcard]
            exact mul_pred_potential_le _ _ (by omega)
          _ ≤ 16 * S.card + 16 * D.card := Nat.add_le_add hIH hnew
          _ = 16 * (S.card + D.card) := by ring

lemma modularPhaseSums_mono
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {i j : ℕ} (hij : i ≤ j) :
    modularPhaseSums hb R₀ E hE hdiverse i ⊆
      modularPhaseSums hb R₀ E hE hdiverse j := by
  rw [modularPhaseSums, modularPhaseSums]
  apply Finset.add_subset_add_left
  apply Finset.subsetSum_mono
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨hx.1, ?_⟩
  intro hxj
  exact hx.2 (modularRemainder_antitone hb R₀ E hE hdiverse hij hxj)

/-- Exact output of the deterministic modular phase machine: either one
phase has already filled a quarter of the cyclic group, or the accumulated
unsaturated phases satisfy the quantitative potential bound. -/
theorem modularPhase_dichotomy
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hhalf : 2 * k ≤ R₀.card) :
    b ≤ 4 * (modularPhaseSums hb R₀ E hE hdiverse k).card ∨
      (k - (modularGrowthIndices hb R₀ E hE hdiverse k).card) *
          (R₀.card - k) ≤
        16 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  classical
  by_cases hu : ∀ i < k, HasUnsaturatedFiber R₀
      (modularRemainder hb R₀ E hE hdiverse i) E
  · exact Or.inr (unsaturated_modularPhase_potential
      hb R₀ E hE hdiverse hhalf hu)
  · push Not at hu
    obtain ⟨i, hi, hsat⟩ := hu
    left
    have hiCard : i ≤ R₀.card := by omega
    have hwide : R₀.card ≤ 2 *
        (modularRemainder hb R₀ E hE hdiverse i).card := by
      rw [card_modularRemainder hb R₀ E hE hdiverse hiCard]
      omega
    have hquarter := saturated_modularPhase_card hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E hE
      (hdiverse _ hwide) hsat
    exact hquarter.trans (Nat.mul_le_mul_left 4 (Finset.card_le_card
      (modularPhaseSums_mono hb R₀ E hE hdiverse hi.le)))

/-- Bounded modular subset-sum growth with explicit, deliberately coarse
constants.  Once the number of exposed phases dominates the logarithmic
growth count and no more than half the residues have been used, either a
quarter of the group is filled or the sumset has quadratic-size growth. -/
theorem bounded_modular_subsetSum_growth
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hlog : 4 * (Nat.log 2 b + 1) ^ 2 ≤ k)
    (hhalf : 2 * k ≤ R₀.card) :
    b ≤ 4 * (modularPhaseSums hb R₀ E hE hdiverse k).card ∨
      k * R₀.card ≤
        64 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  have hk : k ≤ R₀.card := by omega
  rcases modularPhase_dichotomy hb R₀ E hE hdiverse hhalf with hfill | hpot
  · exact Or.inl hfill
  · right
    let g := (modularGrowthIndices hb R₀ E hE hdiverse k).card
    have hg := card_modularGrowthIndices_le hb R₀ E hE hdiverse hhalf
    have hgk : 2 * g ≤ k := by
      dsimp only [g]
      nlinarith
    have hg_le : g ≤ k := by omega
    have hkleft : k ≤ 2 * (k - g) := by omega
    have hmright : R₀.card ≤ 2 * (R₀.card - k) := by omega
    have hprod : k * R₀.card ≤
        4 * ((k - g) * (R₀.card - k)) := by
      calc
        k * R₀.card ≤ (2 * (k - g)) * (2 * (R₀.card - k)) :=
          Nat.mul_le_mul hkleft hmright
        _ = 4 * ((k - g) * (R₀.card - k)) := by ring
    calc
      k * R₀.card ≤ 4 * ((k - g) * (R₀.card - k)) := hprod
      _ ≤ 4 * (16 * (modularPhaseSums hb R₀ E hE hdiverse k).card) :=
        Nat.mul_le_mul_left 4 hpot
      _ = 64 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by ring

/-! ### Finite-tree layer needed for Erdős 1211 -/

/-- A perfect binary tree of natural-number sumsets. -/
inductive SumTree : ℕ → Type
  | leaf (S : Finset ℕ) : SumTree 0
  | node {t : ℕ} (left right : SumTree t) : SumTree (t + 1)

/-- A perfect binary tree whose leaves form a disjoint partition. -/
inductive PartitionTree (ι : Type u) : ℕ → Type u
  | leaf (S : Finset ι) : PartitionTree ι 0
  | node {t : ℕ} (left right : PartitionTree ι t) : PartitionTree ι (t + 1)

namespace PartitionTree

variable {ι : Type*} [DecidableEq ι]

def carrier : {t : ℕ} → PartitionTree ι t → Finset ι
  | 0, .leaf S => S
  | _ + 1, .node left right => carrier left ∪ carrier right

def AllLeaves (P : Finset ι → Prop) : {t : ℕ} → PartitionTree ι t → Prop
  | 0, .leaf S => P S
  | _ + 1, .node left right => AllLeaves P left ∧ AllLeaves P right

def PairwiseDisjoint : {t : ℕ} → PartitionTree ι t → Prop
  | 0, .leaf _ => True
  | _ + 1, .node left right =>
      PairwiseDisjoint left ∧ PairwiseDisjoint right ∧
        Disjoint left.carrier right.carrier

lemma AllLeaves.mono {t : ℕ} {T : PartitionTree ι t}
    {P Q : Finset ι → Prop} (h : T.AllLeaves P)
    (hPQ : ∀ S, P S → Q S) : T.AllLeaves Q := by
  induction T with
  | leaf S => exact hPQ S h
  | node left right ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

lemma allLeaves_subset_carrier {t : ℕ} (T : PartitionTree ι t) :
    T.AllLeaves fun S ↦ S ⊆ T.carrier := by
  induction T with
  | leaf S => exact fun _ h ↦ h
  | node left right ihl ihr =>
      exact ⟨
        ihl.mono fun S hS x hx ↦ Finset.mem_union_left _ (hS hx),
        ihr.mono fun S hS x hx ↦ Finset.mem_union_right _ (hS hx)⟩

end PartitionTree

/-! Bounded integer subset sums and modular pivots. -/

noncomputable def boundedSubsetSum (C : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (C.powerset.filter fun H ↦ H.card ≤ k).image fun H ↦ ∑ h ∈ H, h

lemma mem_boundedSubsetSum_iff {C : Finset ℕ} {k u : ℕ} :
    u ∈ boundedSubsetSum C k ↔
      ∃ H : Finset ℕ, H ⊆ C ∧ H.card ≤ k ∧ u = ∑ h ∈ H, h := by
  classical
  simp only [boundedSubsetSum, Finset.mem_image, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨H, ⟨hHC, hHk⟩, rfl⟩
    exact ⟨H, hHC, hHk, rfl⟩
  · rintro ⟨H, hHC, hHk, rfl⟩
    exact ⟨H, ⟨hHC, hHk⟩, rfl⟩

@[simp] lemma zero_mem_boundedSubsetSum (C : Finset ℕ) (k : ℕ) :
    0 ∈ boundedSubsetSum C k := by
  rw [mem_boundedSubsetSum_iff]
  exact ⟨∅, by simp⟩

lemma boundedSubsetSum_subset_subsetSum (C : Finset ℕ) (k : ℕ) :
    boundedSubsetSum C k ⊆ C.subsetSum := by
  intro u hu
  obtain ⟨H, hHC, _hHk, rfl⟩ := mem_boundedSubsetSum_iff.mp hu
  exact Finset.mem_subsetSum_iff.mpr ⟨H, hHC, rfl⟩

lemma exists_preimage_finset_of_subset_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C : Finset α) (f : α → β) (hinj : Set.InjOn f C)
    (G : Finset β) (hG : G ⊆ C.image f) :
    ∃ H : Finset α, H ⊆ C ∧ H.card = G.card ∧ H.image f = G := by
  let H := C.filter fun c ↦ f c ∈ G
  have hHC : H ⊆ C := Finset.filter_subset _ _
  have himage : H.image f = G := by
    ext g
    simp only [H, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨c, ⟨_hcC, hfcG⟩, rfl⟩
      exact hfcG
    · intro hg
      obtain ⟨c, hcC, hcg⟩ := Finset.mem_image.mp (hG hg)
      exact ⟨c, ⟨hcC, hcg ▸ hg⟩, hcg⟩
  refine ⟨H, hHC, ?_, himage⟩
  rw [← himage, Finset.card_image_iff.mpr (hinj.mono hHC)]

lemma natCast_zmod_injOn_of_lt {b : ℕ} [NeZero b] {C : Finset ℕ}
    (hC : ∀ c ∈ C, c < b) : Set.InjOn (fun c : ℕ ↦ (c : ZMod b)) C := by
  intro x hx y hy hxy
  have hmod := (ZMod.natCast_eq_natCast_iff' x y b).mp hxy
  simpa [Nat.mod_eq_of_lt (hC x hx), Nat.mod_eq_of_lt (hC y hy)] using hmod

noncomputable def pivotExtended (S P : Finset ℕ) : Finset ℕ :=
  S + P.subsetSum

lemma zero_mem_pivotExtended {S P : Finset ℕ} (hzero : 0 ∈ S) :
    0 ∈ pivotExtended S P := by
  exact Finset.add_mem_add hzero Finset.zero_mem_subsetSum

lemma subset_pivotExtended_left (S P : Finset ℕ) : S ⊆ pivotExtended S P := by
  intro s hs
  exact Finset.add_mem_add hs Finset.zero_mem_subsetSum

lemma pivotExtended_subset_subsetSum_union
    {C P S : Finset ℕ} (hCP : Disjoint C P)
    (hS : S ⊆ C.subsetSum) :
    pivotExtended S P ⊆ (C ∪ P).subsetSum := by
  intro x hx
  obtain ⟨s, hs, p, hp, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨H, hHC, hHsum⟩ := Finset.mem_subsetSum_iff.mp (hS hs)
  obtain ⟨Q, hQP, hQsum⟩ := Finset.mem_subsetSum_iff.mp hp
  have hHQ : Disjoint H Q := hCP.mono hHC hQP
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨H ∪ Q, Finset.union_subset_union hHC hQP, ?_⟩
  rw [Finset.sum_union hHQ, hHsum, hQsum]

namespace SumTree

def carrier : {t : ℕ} → SumTree t → Finset ℕ
  | 0, .leaf S => S
  | _ + 1, .node left right => carrier left + carrier right

def AllLeaves (P : Finset ℕ → Prop) : {t : ℕ} → SumTree t → Prop
  | 0, .leaf S => P S
  | _ + 1, .node left right => AllLeaves P left ∧ AllLeaves P right

lemma zero_mem_carrier {t : ℕ} {T : SumTree t}
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S) : 0 ∈ T.carrier := by
  induction T with
  | leaf S => exact hzero
  | node left right ihl ihr =>
      exact Finset.add_mem_add (ihl hzero.1) (ihr hzero.2)

lemma carrier_subset_Icc {t m : ℕ} {T : SumTree t}
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m) :
    T.carrier ⊆ Finset.Icc 0 (2 ^ t * m) := by
  induction T with
  | leaf S => simpa [carrier, AllLeaves] using hbox
  | @node t left right ihl ihr =>
      intro z hz
      rw [carrier, Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      have hx' := Finset.mem_Icc.mp (ihl hbox.1 hx)
      have hy' := Finset.mem_Icc.mp (ihr hbox.2 hy)
      apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.zero_le _
      · calc
          x + y ≤ 2 ^ t * m + 2 ^ t * m := Nat.add_le_add hx'.2 hy'.2
          _ = 2 ^ t * 2 * m := by ring
          _ = 2 ^ (t + 1) * m := by rw [pow_succ]

lemma card_carrier_le {t m : ℕ} {T : SumTree t}
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m) :
    T.carrier.card ≤ 2 ^ t * m + 1 := by
  exact (Finset.card_le_card (carrier_subset_Icc hbox)).trans_eq (by simp)

def growthLower (k : ℕ) : ℕ → ℕ
  | 0 => k
  | t + 1 => 3 * growthLower k t - 3

lemma growthLower_ge {k : ℕ} (hk : 2 ≤ k) :
    ∀ t, k ≤ growthLower k t := by
  intro t
  induction t with
  | zero => simp [growthLower]
  | succ t ih =>
      rw [growthLower]
      omega

lemma growthLower_ge_pow_mul {k : ℕ} (hk : 2 ≤ k) :
    ∀ t, 3 ^ t * (k - 2) + 2 ≤ growthLower k t := by
  intro t
  induction t with
  | zero => simp only [pow_zero, one_mul, growthLower]; omega
  | succ t ih =>
      rw [growthLower, pow_succ]
      have hmul := Nat.mul_le_mul_left 3 ih
      have hge := growthLower_ge hk t
      rw [show 3 ^ t * 3 * (k - 2) = 3 * (3 ^ t * (k - 2)) by ring]
      omega

end SumTree

namespace PartitionTree

variable {ι : Type*} [DecidableEq ι]

noncomputable def pairedPivotSumTree (k : ℕ) :
    {t : ℕ} → PartitionTree ℕ t → PartitionTree ℕ t → SumTree t
  | 0, .leaf C, .leaf P => .leaf (pivotExtended (boundedSubsetSum C k) P)
  | _ + 1, .node C₁ C₂, .node P₁ P₂ =>
      .node (pairedPivotSumTree k C₁ P₁) (pairedPivotSumTree k C₂ P₂)

def AllLeafPairs (Q : Finset ℕ → Finset ℕ → Prop) :
    {t : ℕ} → PartitionTree ℕ t → PartitionTree ℕ t → Prop
  | 0, .leaf C, .leaf P => Q C P
  | _ + 1, .node C₁ C₂, .node P₁ P₂ =>
      AllLeafPairs Q C₁ P₁ ∧ AllLeafPairs Q C₂ P₂

lemma allLeafPairs_of_allLeaves {t : ℕ}
    {A B : PartitionTree ℕ t} {PA PB : Finset ℕ → Prop}
    (hA : A.AllLeaves PA) (hB : B.AllLeaves PB)
    {Q : Finset ℕ → Finset ℕ → Prop}
    (hQ : ∀ C P, PA C → PB P → Q C P) :
    AllLeafPairs Q A B := by
  induction A with
  | leaf C =>
      cases B with
      | leaf P => exact hQ C P hA hB
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ => exact ⟨ih₁ hA.1 hB.1, ih₂ hA.2 hB.2⟩

lemma allLeaves_pairedPivotSumTree_iff {t k : ℕ}
    (A B : PartitionTree ℕ t) (Q : Finset ℕ → Prop) :
    (pairedPivotSumTree k A B).AllLeaves Q ↔
      AllLeafPairs (fun C P ↦
        Q (pivotExtended (boundedSubsetSum C k) P)) A B := by
  induction A with
  | leaf C => cases B; rfl
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          simp only [pairedPivotSumTree, SumTree.AllLeaves, AllLeafPairs,
            ih₁, ih₂]

lemma subsetSum_add_subset_union {A B : Finset ℕ} (hAB : Disjoint A B) :
    A.subsetSum + B.subsetSum ⊆ (A ∪ B).subsetSum := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨P, hPA, rfl⟩ := Finset.mem_subsetSum_iff.mp ha
  obtain ⟨Q, hQB, rfl⟩ := Finset.mem_subsetSum_iff.mp hb
  have hPQ := hAB.mono hPA hQB
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨P ∪ Q, Finset.union_subset_union hPA hQB, ?_⟩
  rw [Finset.sum_union hPQ]

lemma carrier_pairedPivotSumTree_subset_subsetSum {t k : ℕ}
    (A B : PartitionTree ℕ t)
    (hA : A.PairwiseDisjoint) (hB : B.PairwiseDisjoint)
    (hAB : Disjoint A.carrier B.carrier) :
    (pairedPivotSumTree k A B).carrier ⊆
      (A.carrier ∪ B.carrier).subsetSum := by
  induction A with
  | leaf C =>
      cases B with
      | leaf P =>
          exact pivotExtended_subset_subsetSum_union hAB
            (boundedSubsetSum_subset_subsetSum C k)
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ =>
          rcases hA with ⟨hA₁, hA₂, hA12⟩
          rcases hB with ⟨hB₁, hB₂, hB12⟩
          have hA₁B₁ : Disjoint A₁.carrier B₁.carrier :=
            hAB.mono (fun x hx ↦ Finset.mem_union_left _ hx)
              (fun x hx ↦ Finset.mem_union_left _ hx)
          have hA₂B₂ : Disjoint A₂.carrier B₂.carrier :=
            hAB.mono (fun x hx ↦ Finset.mem_union_right _ hx)
              (fun x hx ↦ Finset.mem_union_right _ hx)
          have hsupport : Disjoint
              (A₁.carrier ∪ B₁.carrier) (A₂.carrier ∪ B₂.carrier) := by
            rw [Finset.disjoint_left]
            intro x hx₁ hx₂
            rw [Finset.mem_union] at hx₁ hx₂
            rcases hx₁ with hxA₁ | hxB₁ <;> rcases hx₂ with hxA₂ | hxB₂
            · exact Finset.disjoint_left.mp hA12 hxA₁ hxA₂
            · exact Finset.disjoint_left.mp hAB
                (Finset.mem_union_left _ hxA₁) (Finset.mem_union_right _ hxB₂)
            · exact Finset.disjoint_left.mp hAB
                (Finset.mem_union_right _ hxA₂) (Finset.mem_union_left _ hxB₁)
            · exact Finset.disjoint_left.mp hB12 hxB₁ hxB₂
          have hsub := (Finset.add_subset_add (ih₁ B₁ hA₁ hB₁ hA₁B₁)
            (ih₂ B₂ hA₂ hB₂ hA₂B₂)).trans
              (subsetSum_add_subset_union hsupport)
          simpa only [pairedPivotSumTree, SumTree.carrier, carrier,
            Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
            using hsub

end PartitionTree

end Erdos344
