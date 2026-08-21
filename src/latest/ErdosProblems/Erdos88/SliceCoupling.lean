/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos88.SliceFamilyConcentration

/-!
# The KSSS two-stage slice coupling

This module connects the exact two-stage sampler in `BooleanSlices` to the
signed-slice concentration theorem.  It begins by identifying the revealed
part of one two-stage outcome with a uniform signed slice.
-/

open scoped BigOperators

namespace Erdos88
namespace BooleanSlices

open Classical Finset

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The revealed left vector in a two-stage bucket: `+1` on the left set,
`-1` on the remainder of the exceptional set, and zero elsewhere. -/
def twoStageSignedLeft (I : Finset α) (r a b h : ℕ)
    (ω : TwoStageSlicePoint I r a b h) : SignedSlicePoint I a (r - a) := by
  let R : Finset α := ω.1.1
  let A : Finset α := ω.2.1.1
  have hR : R ⊆ I ∧ R.card = r := mem_booleanSlice.mp ω.1.2
  have hA : A ⊆ R ∧ A.card = a := mem_booleanSlice.mp ω.2.1.2
  refine ⟨(A, R \ A), mem_signedSlice.mpr ⟨hA.1.trans hR.1,
    Finset.sdiff_subset.trans hR.1, Finset.disjoint_sdiff,
    hA.2, ?_⟩⟩
  rw [Finset.card_sdiff_of_subset hA.1, hR.2, hA.2]

/-- The exceptional set reconstructed from a signed revealed vector. -/
def signedSliceCarrier (I : Finset α) (r a : ℕ) (ha : a ≤ r)
    (S : SignedSlicePoint I a (r - a)) : BooleanSlicePoint I r := by
  refine ⟨S.1.1 ∪ S.1.2, mem_booleanSlice.mpr ⟨
    Finset.union_subset (mem_signedSlice.mp S.2).1
      (mem_signedSlice.mp S.2).2.1, ?_⟩⟩
  rw [Finset.card_union_of_disjoint (mem_signedSlice.mp S.2).2.2.1,
    (mem_signedSlice.mp S.2).2.2.2.1,
    (mem_signedSlice.mp S.2).2.2.2.2,
    Nat.add_sub_of_le ha]

/-- The positive support of a signed revealed vector is a Boolean slice of
its reconstructed exceptional set. -/
def signedSlicePositiveInCarrier (I : Finset α) (r a : ℕ) (ha : a ≤ r)
    (S : SignedSlicePoint I a (r - a)) :
    BooleanSlicePoint (signedSliceCarrier I r a ha S).1 a := by
  refine ⟨S.1.1, mem_booleanSlice.mpr ⟨?_,
    (mem_signedSlice.mp S.2).2.2.2.1⟩⟩
  exact Finset.subset_union_left

@[simp] lemma twoStageSignedLeft_carrier
    (I : Finset α) (r a b h : ℕ) (ha : a ≤ r)
    (ω : TwoStageSlicePoint I r a b h) :
    signedSliceCarrier I r a ha (twoStageSignedLeft I r a b h ω) = ω.1 := by
  apply Subtype.ext
  change ω.2.1.1 ∪ (ω.1.1 \ ω.2.1.1) = ω.1.1
  exact Finset.union_sdiff_of_subset (mem_booleanSlice.mp ω.2.1.2).1

@[simp] lemma twoStageSignedLeft_positive
    (I : Finset α) (r a b h : ℕ) (ha : a ≤ r)
    (ω : TwoStageSlicePoint I r a b h) :
    (signedSlicePositiveInCarrier I r a ha
      (twoStageSignedLeft I r a b h ω)).1 = ω.2.1.1 := by
  rfl

/-- The fiber of the revealed signed vector consists exactly of the
independent right slice inside its carrier and the shared slice outside. -/
noncomputable def twoStageSignedLeftFiberEquiv
    (I : Finset α) (r a b h : ℕ) (ha : a ≤ r)
    (S : SignedSlicePoint I a (r - a)) :
    {ω : TwoStageSlicePoint I r a b h //
      twoStageSignedLeft I r a b h ω = S} ≃
      BooleanSlicePoint (signedSliceCarrier I r a ha S).1 b ×
        BooleanSlicePoint (I \ (signedSliceCarrier I r a ha S).1) h := by
  let R : BooleanSlicePoint I r := signedSliceCarrier I r a ha S
  let A : BooleanSlicePoint R.1 a := signedSlicePositiveInCarrier I r a ha S
  let build :
      BooleanSlicePoint R.1 b × BooleanSlicePoint (I \ R.1) h →
        TwoStageSlicePoint I r a b h :=
    fun T ↦ ⟨R, A, T.1, T.2⟩
  have hbuild (T : BooleanSlicePoint R.1 b ×
      BooleanSlicePoint (I \ R.1) h) :
      twoStageSignedLeft I r a b h (build T) = S := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp only [build, R, A, twoStageSignedLeft,
        signedSliceCarrier, signedSlicePositiveInCarrier]
      ext i
      have hdisj := (mem_signedSlice.mp S.2).2.2.1
      constructor
      · intro hi
        have hiU := (Finset.mem_sdiff.mp hi).1
        have hiN : i ∈ S.1.2 := by
          rcases Finset.mem_union.mp hiU with hiP | hiN
          · exact ((Finset.mem_sdiff.mp hi).2 hiP).elim
          · exact hiN
        exact hiN
      · intro hiN
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hiN,
          fun hiP ↦ Finset.disjoint_left.mp hdisj hiP hiN⟩
  refine {
    toFun := fun ω ↦ ?_
    invFun := fun T ↦ ⟨build T, hbuild T⟩
    left_inv := ?_
    right_inv := ?_
  }
  · have hR : R = ω.1.1 := by
      calc
        R = signedSliceCarrier I r a ha
            (twoStageSignedLeft I r a b h ω.1) := by rw [ω.2]
        _ = ω.1.1 := twoStageSignedLeft_carrier I r a b h ha ω.1
    have hRval : R.1 = ω.1.1.1 := congrArg Subtype.val hR
    have hcomp : I \ ω.1.1.1 = I \ R.1 := by rw [hRval]
    exact ⟨hRval.symm ▸ ω.1.2.2.1, hcomp ▸ ω.1.2.2.2⟩
  · intro ω
    apply Subtype.ext
    rcases ω with ⟨⟨Rω, Aω, Bω, Cω⟩, hω⟩
    dsimp only at hω ⊢
    have hR : R = Rω := by
      calc
        R = signedSliceCarrier I r a ha
            (twoStageSignedLeft I r a b h ⟨Rω, Aω, Bω, Cω⟩) := by
              rw [hω]
        _ = Rω := twoStageSignedLeft_carrier I r a b h ha
          ⟨Rω, Aω, Bω, Cω⟩
    cases hR
    dsimp only [build]
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Prod.ext
    · apply Subtype.ext
      have hpos := congrArg (fun T : SignedSlicePoint I a (r - a) ↦ T.1.1) hω
      change S.1.1 = Aω.1
      exact hpos.symm
    · apply Prod.ext <;> apply Subtype.ext <;> rfl
  · intro T
    rcases T with ⟨B, C⟩
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- Every fiber of the revealed-left map has the same explicit cardinality. -/
lemma card_twoStageSignedLeft_fiber
    (I : Finset α) (r a b h : ℕ) (ha : a ≤ r)
    (S : SignedSlicePoint I a (r - a)) :
    Nat.card {ω : TwoStageSlicePoint I r a b h //
        twoStageSignedLeft I r a b h ω = S} =
      r.choose b * (I.card - r).choose h := by
  rw [Nat.card_congr (twoStageSignedLeftFiberEquiv I r a b h ha S),
    Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    card_booleanSlicePoint, card_booleanSlicePoint]
  have hcarrier : (signedSliceCarrier I r a ha S).1.card = r :=
    (mem_booleanSlice.mp (signedSliceCarrier I r a ha S).2).2
  have hsubset : (signedSliceCarrier I r a ha S).1 ⊆ I :=
    (mem_booleanSlice.mp (signedSliceCarrier I r a ha S).2).1
  rw [hcarrier, Finset.card_sdiff_of_subset hsubset, hcarrier]

universe v

variable {κ : Type v}

/-- Coordinatewise revealed-left signed vector for the product sampler. -/
def productTwoStageSignedLeft [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) :
    ProductSignedSlicePoint P a (fun k ↦ r k - a k) :=
  fun k ↦ twoStageSignedLeft (P.fiber k) (r k) (a k) (b k) (h k) (ω k)

/-- Fibers of the product revealed-left map split coordinatewise. -/
noncomputable def productTwoStageSignedLeftFiberEquiv
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (S : ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :
    {ω : ProductTwoStageSlicePoint P r a b h //
      productTwoStageSignedLeft P r a b h ω = S} ≃
      ∀ k, {τ : TwoStageSlicePoint (P.fiber k)
          (r k) (a k) (b k) (h k) //
        twoStageSignedLeft (P.fiber k) (r k) (a k) (b k) (h k) τ = S k} where
  toFun ω k := ⟨ω.1 k, by
    have hk := congrArg
      (fun T : ProductSignedSlicePoint P a (fun j ↦ r j - a j) ↦ T k) ω.2
    exact hk⟩
  invFun τ := ⟨fun k ↦ (τ k).1, by
    funext k
    exact (τ k).2⟩
  left_inv ω := by
    apply Subtype.ext
    funext k
    rfl
  right_inv τ := by
    funext k
    apply Subtype.ext
    rfl

/-- Common fiber factor for the product revealed-left map. -/
def productTwoStageSignedLeftFiberFactor [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r b h : κ → ℕ) : ℕ :=
  ∏ k, (r k).choose (b k) * ((P.fiber k).card - r k).choose (h k)

lemma productTwoStageSignedLeftFiberFactor_pos
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r b h : κ → ℕ)
    (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k) :
    0 < productTwoStageSignedLeftFiberFactor P r b h := by
  apply Finset.prod_pos
  intro k _
  exact Nat.mul_pos
    (Nat.choose_pos (hb k))
    (Nat.choose_pos (hh k))

lemma card_productTwoStageSignedLeft_fiber
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ha : ∀ k, a k ≤ r k)
    (S : ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :
    Nat.card {ω : ProductTwoStageSlicePoint P r a b h //
        productTwoStageSignedLeft P r a b h ω = S} =
      productTwoStageSignedLeftFiberFactor P r b h := by
  rw [Nat.card_congr (productTwoStageSignedLeftFiberEquiv P r a b h S),
    Nat.card_pi]
  apply Finset.prod_congr rfl
  intro k _
  exact card_twoStageSignedLeft_fiber (P.fiber k)
    (r k) (a k) (b k) (h k) (ha k) (S k)

/-- The revealed-left vector of a uniform product two-stage outcome is
exactly uniform on its product signed slice. -/
lemma uniformProbability_productTwoStageSignedLeft
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (Q : ProductSignedSlicePoint P a (fun k ↦ r k - a k) → Prop) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    letI : Nonempty (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
      productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k)
        (fun k ↦ by rw [Nat.add_sub_of_le (ha k)]; exact hr k)
    Concentration.uniformProbability
        (fun ω ↦ Q (productTwoStageSignedLeft P r a b h ω)) =
      Concentration.uniformProbability Q := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
    productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k)
      (fun k ↦ by rw [Nat.add_sub_of_le (ha k)]; exact hr k)
  exact uniformProbability_comp_of_card_fiber
    (productTwoStageSignedLeft P r a b h)
    (productTwoStageSignedLeftFiberFactor P r b h)
    (productTwoStageSignedLeftFiberFactor_pos P r b h hb hh)
    (card_productTwoStageSignedLeft_fiber P r a b h ha) Q

/-- Expectation form of the same exact pushforward law. -/
lemma uniformExpectation_productTwoStageSignedLeft
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (g : ProductSignedSlicePoint P a (fun k ↦ r k - a k) → ℝ) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    letI : Nonempty (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
      productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k)
        (fun k ↦ by rw [Nat.add_sub_of_le (ha k)]; exact hr k)
    Concentration.uniformExpectation
        (fun ω ↦ g (productTwoStageSignedLeft P r a b h ω)) =
      Concentration.uniformExpectation g := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
    productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k)
      (fun k ↦ by rw [Nat.add_sub_of_le (ha k)]; exact hr k)
  exact uniformExpectation_comp_of_card_fiber
    (productTwoStageSignedLeft P r a b h)
    (productTwoStageSignedLeftFiberFactor P r b h)
    (productTwoStageSignedLeftFiberFactor_pos P r b h hb hh)
    (card_productTwoStageSignedLeft_fiber P r a b h ha) g

/-- The exposed linear--quadratic portion of the left vector in the actual
two-stage sample satisfies the signed-slice concentration bound. -/
theorem productTwoStageSignedLeft_quadratic_two_sided_probability {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f : α → ℝ) (F : α → α → ℝ) (A B t : ℝ)
    (hL : 0 < ∑ k : Fin K, r k)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hlip : 0 < 4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability (fun ω =>
        t ≤ |signedSliceQuadratic P a (fun k ↦ r k - a k) f F
            (productTwoStageSignedLeft P r a b h ω) -
          Concentration.uniformExpectation (fun τ =>
            signedSliceQuadratic P a (fun k ↦ r k - a k) f F
              (productTwoStageSignedLeft P r a b h τ))|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
          (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty
      (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
    productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k)
      (fun k ↦ by rw [Nat.add_sub_of_le (ha k)]; exact hr k)
  have hcount : ∀ k, a k + (r k - a k) ≤ (P.fiber k).card := by
    intro k
    rw [Nat.add_sub_of_le (ha k)]
    exact hr k
  have hmean := uniformExpectation_productTwoStageSignedLeft
    P r a b h hr ha hb hh
      (signedSliceQuadratic P a (fun k ↦ r k - a k) f F)
  rw [hmean]
  let Q : ProductSignedSlicePoint P a (fun k ↦ r k - a k) → Prop :=
    fun S ↦ t ≤ |signedSliceQuadratic P a (fun k ↦ r k - a k) f F S -
      Concentration.uniformExpectation
        (signedSliceQuadratic P a (fun k ↦ r k - a k) f F)|
  change Concentration.uniformProbability
      (fun ω ↦ Q (productTwoStageSignedLeft P r a b h ω)) ≤ _
  rw [uniformProbability_productTwoStageSignedLeft
    P r a b h hr ha hb hh Q]
  have hsum : (∑ k : Fin K,
      (((a k + (r k - a k) : ℕ)) : ℝ)) = ∑ k : Fin K, (r k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_sub_of_le (ha k)]
  have hlip' : 0 < 4 * B + 8 *
      (∑ k : Fin K, (((a k + (r k - a k) : ℕ)) : ℝ)) * A := by
    rw [hsum]
    exact hlip
  have htail := signedSliceQuadratic_two_sided_probability
    P a (fun k ↦ r k - a k) hcount e f F A B t
      (by simpa [Nat.add_sub_of_le (ha _)] using hL)
      hA hB ht hlip' hf hF
  simpa only [hsum] using htail

/-! ### The symmetric revealed-right marginal -/

/-- Swap the independent left and right slices inside the exceptional set. -/
noncomputable def twoStageSwapEquiv (I : Finset α) (r a b h : ℕ) :
    TwoStageSlicePoint I r a b h ≃ TwoStageSlicePoint I r b a h where
  toFun ω := ⟨ω.1, ω.2.2.1, ω.2.1, ω.2.2.2⟩
  invFun ω := ⟨ω.1, ω.2.2.1, ω.2.1, ω.2.2.2⟩
  left_inv ω := by
    rcases ω with ⟨R, A, B, C⟩
    rfl
  right_inv ω := by
    rcases ω with ⟨R, B, A, C⟩
    rfl

/-- Coordinatewise swap equivalence for the product two-stage sampler. -/
noncomputable def productTwoStageSwapEquiv [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ) :
    ProductTwoStageSlicePoint P r a b h ≃
      ProductTwoStageSlicePoint P r b a h :=
  Equiv.piCongrRight fun k ↦
    twoStageSwapEquiv (P.fiber k) (r k) (a k) (b k) (h k)

/-- The revealed right vector, expressed through the left-vector map after
the exact sampler symmetry. -/
noncomputable def productTwoStageSignedRight [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) :
    ProductSignedSlicePoint P b (fun k ↦ r k - b k) :=
  productTwoStageSignedLeft P r b a h
    (productTwoStageSwapEquiv P r a b h ω)

/-- Uniform event probabilities are invariant under a finite equivalence. -/
lemma uniformProbability_comp_equiv {Ω Ω' : Type*}
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

/-- The revealed-right vector of a uniform product two-stage outcome is
exactly uniform on the corresponding product signed slice. -/
lemma uniformProbability_productTwoStageSignedRight
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (Q : ProductSignedSlicePoint P b (fun k ↦ r k - b k) → Prop) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    letI : Nonempty (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
      productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k)
        (fun k ↦ by rw [Nat.add_sub_of_le (hb k)]; exact hr k)
    Concentration.uniformProbability
        (fun ω ↦ Q (productTwoStageSignedRight P r a b h ω)) =
      Concentration.uniformProbability Q := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty (ProductTwoStageSlicePoint P r b a h) :=
    productTwoStageSlicePoint_nonempty P r b a h hr hb ha hh
  letI : Nonempty (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
    productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k)
      (fun k ↦ by rw [Nat.add_sub_of_le (hb k)]; exact hr k)
  calc
    Concentration.uniformProbability
        (fun ω ↦ Q (productTwoStageSignedRight P r a b h ω)) =
        Concentration.uniformProbability (fun τ ↦
          Q (productTwoStageSignedLeft P r b a h τ)) := by
      exact uniformProbability_comp_equiv
        (productTwoStageSwapEquiv P r a b h)
        (fun τ ↦ Q (productTwoStageSignedLeft P r b a h τ))
    _ = Concentration.uniformProbability Q :=
      uniformProbability_productTwoStageSignedLeft
        P r b a h hr hb ha hh Q

/-- Expectation form of the revealed-right pushforward law. -/
lemma uniformExpectation_productTwoStageSignedRight
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (g : ProductSignedSlicePoint P b (fun k ↦ r k - b k) → ℝ) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    letI : Nonempty (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
      productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k)
        (fun k ↦ by rw [Nat.add_sub_of_le (hb k)]; exact hr k)
    Concentration.uniformExpectation
        (fun ω ↦ g (productTwoStageSignedRight P r a b h ω)) =
      Concentration.uniformExpectation g := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty (ProductTwoStageSlicePoint P r b a h) :=
    productTwoStageSlicePoint_nonempty P r b a h hr hb ha hh
  letI : Nonempty (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
    productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k)
      (fun k ↦ by rw [Nat.add_sub_of_le (hb k)]; exact hr k)
  calc
    Concentration.uniformExpectation
        (fun ω ↦ g (productTwoStageSignedRight P r a b h ω)) =
        Concentration.uniformExpectation (fun τ ↦
          g (productTwoStageSignedLeft P r b a h τ)) := by
      have heq := Fintype.expect_equiv
        (productTwoStageSwapEquiv P r a b h)
        (fun ω ↦ g (productTwoStageSignedRight P r a b h ω))
        (fun τ ↦ g (productTwoStageSignedLeft P r b a h τ)) (by
          intro ω
          rfl)
      simpa [Concentration.uniformExpectation,
        Fintype.expect_eq_sum_div_card] using heq
    _ = Concentration.uniformExpectation g :=
      uniformExpectation_productTwoStageSignedLeft
        P r b a h hr hb ha hh g

/-- Symmetric exposed-quadratic concentration for the right vector. -/
theorem productTwoStageSignedRight_quadratic_two_sided_probability {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f : α → ℝ) (F : α → α → ℝ) (A B t : ℝ)
    (hL : 0 < ∑ k : Fin K, r k)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hlip : 0 < 4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability (fun ω ↦
        t ≤ |signedSliceQuadratic P b (fun k ↦ r k - b k) f F
            (productTwoStageSignedRight P r a b h ω) -
          Concentration.uniformExpectation (fun τ ↦
            signedSliceQuadratic P b (fun k ↦ r k - b k) f F
              (productTwoStageSignedRight P r a b h τ))|) ≤
      2 * Real.exp
        (-t ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
          (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty
      (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
    productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k)
      (fun k ↦ by rw [Nat.add_sub_of_le (hb k)]; exact hr k)
  have hcount : ∀ k, b k + (r k - b k) ≤ (P.fiber k).card := by
    intro k
    rw [Nat.add_sub_of_le (hb k)]
    exact hr k
  have hmean := uniformExpectation_productTwoStageSignedRight
    P r a b h hr ha hb hh
      (signedSliceQuadratic P b (fun k ↦ r k - b k) f F)
  rw [hmean]
  let Q : ProductSignedSlicePoint P b (fun k ↦ r k - b k) → Prop :=
    fun S ↦ t ≤ |signedSliceQuadratic P b (fun k ↦ r k - b k) f F S -
      Concentration.uniformExpectation
        (signedSliceQuadratic P b (fun k ↦ r k - b k) f F)|
  change Concentration.uniformProbability
      (fun ω ↦ Q (productTwoStageSignedRight P r a b h ω)) ≤ _
  rw [uniformProbability_productTwoStageSignedRight
    P r a b h hr ha hb hh Q]
  have hsum : (∑ k : Fin K,
      (((b k + (r k - b k) : ℕ)) : ℝ)) = ∑ k : Fin K, (r k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_sub_of_le (hb k)]
  have hlip' : 0 < 4 * B + 8 *
      (∑ k : Fin K, (((b k + (r k - b k) : ℕ)) : ℝ)) * A := by
    rw [hsum]
    exact hlip
  have htail := signedSliceQuadratic_two_sided_probability
    P b (fun k ↦ r k - b k) hcount e f F A B t
      (by simpa [Nat.add_sub_of_le (hb _)] using hL)
      hA hB ht hlip' hf hF
  simpa only [hsum] using htail

/-! ### Deterministic decomposition of the coupled quadratic -/

lemma mem_productTwoStageSliceLeft_iff [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) (i : α) :
    i ∈ (productTwoStageSliceLeft P r a b h ω).1 ↔
      i ∈ (ω (P.bucket i)).2.1.1 ∪ (ω (P.bucket i)).2.2.2.1 := by
  let T : ∀ k, BooleanSlicePoint (P.fiber k) (a k + h k) :=
    fun k ↦ twoStageSliceLeft (P.fiber k) (r k) (a k) (b k) (h k) (ω k)
  have happly := congrArg
    (fun S : ∀ k, BooleanSlicePoint (P.fiber k) (a k + h k) ↦
      (S (P.bucket i)).1)
    ((productSliceEquiv P (fun k ↦ a k + h k)).apply_symm_apply T)
  change ((productTwoStageSliceLeft P r a b h ω).1 ∩
      P.fiber (P.bucket i)) =
    (ω (P.bucket i)).2.1.1 ∪ (ω (P.bucket i)).2.2.2.1 at happly
  constructor
  · intro hi
    have : i ∈ (productTwoStageSliceLeft P r a b h ω).1 ∩
        P.fiber (P.bucket i) :=
      Finset.mem_inter.mpr ⟨hi, P.mem_ownFiber i⟩
    rw [happly] at this
    exact this
  · intro hi
    rw [← happly] at hi
    exact (Finset.mem_inter.mp hi).1

lemma mem_productTwoStageSliceRight_iff [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) (i : α) :
    i ∈ (productTwoStageSliceRight P r a b h ω).1 ↔
      i ∈ (ω (P.bucket i)).2.2.1.1 ∪ (ω (P.bucket i)).2.2.2.1 := by
  let T : ∀ k, BooleanSlicePoint (P.fiber k) (b k + h k) :=
    fun k ↦ twoStageSliceRight (P.fiber k) (r k) (a k) (b k) (h k) (ω k)
  have happly := congrArg
    (fun S : ∀ k, BooleanSlicePoint (P.fiber k) (b k + h k) ↦
      (S (P.bucket i)).1)
    ((productSliceEquiv P (fun k ↦ b k + h k)).apply_symm_apply T)
  change ((productTwoStageSliceRight P r a b h ω).1 ∩
      P.fiber (P.bucket i)) =
    (ω (P.bucket i)).2.2.1.1 ∪ (ω (P.bucket i)).2.2.2.1 at happly
  constructor
  · intro hi
    have : i ∈ (productTwoStageSliceRight P r a b h ω).1 ∩
        P.fiber (P.bucket i) :=
      Finset.mem_inter.mpr ⟨hi, P.mem_ownFiber i⟩
    rw [happly] at this
    exact this
  · intro hi
    rw [← happly] at hi
    exact (Finset.mem_inter.mp hi).1

/-- The common outside sign, extended by zero on the exceptional set. -/
def productTwoStageSharedValue [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) (i : α) : ℝ :=
  if i ∈ (ω (P.bucket i)).1.1 then 0
  else signOfSet (ω (P.bucket i)).2.2.2.1 i

lemma productTwoStageSignedLeft_value [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) (i : α) :
    productSignedSliceValue P (productTwoStageSignedLeft P r a b h ω) i =
      if i ∈ (ω (P.bucket i)).2.1.1 then 1
      else if i ∈ (ω (P.bucket i)).1.1 \ (ω (P.bucket i)).2.1.1
        then -1 else 0 := by
  rfl

lemma productTwoStageSignedRight_value [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) (i : α) :
    productSignedSliceValue P (productTwoStageSignedRight P r a b h ω) i =
      if i ∈ (ω (P.bucket i)).2.2.1.1 then 1
      else if i ∈ (ω (P.bucket i)).1.1 \ (ω (P.bucket i)).2.2.1.1
        then -1 else 0 := by
  rfl

/-- Pointwise decomposition of the left sign vector into its revealed and
shared-outside parts. -/
lemma signOf_productTwoStageSliceLeft_eq [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) (i : α) :
    signOfSet (productTwoStageSliceLeft P r a b h ω).1 i =
      productSignedSliceValue P (productTwoStageSignedLeft P r a b h ω) i +
        productTwoStageSharedValue P r a b h ω i := by
  let k := P.bucket i
  have hiFiber : i ∈ P.fiber k := P.mem_ownFiber i
  have hR := (mem_booleanSlice.mp (ω k).1.2).1
  have hA := (mem_booleanSlice.mp (ω k).2.1.2).1
  have hC := (mem_booleanSlice.mp (ω k).2.2.2.2).1
  have hmem := mem_productTwoStageSliceLeft_iff P r a b h ω i
  by_cases hiR : i ∈ (ω k).1.1
  · have hiC : i ∉ (ω k).2.2.2.1 := fun hiC ↦
      (Finset.mem_sdiff.mp (hC hiC)).2 hiR
    by_cases hiA : i ∈ (ω k).2.1.1
    · rw [signOfSet, if_pos (hmem.mpr (Finset.mem_union_left _ hiA))]
      rw [productTwoStageSignedLeft_value]
      simp [productTwoStageSharedValue, k, hiR, hiA]
    · have hiRA : i ∈ (ω k).1.1 \ (ω k).2.1.1 :=
        Finset.mem_sdiff.mpr ⟨hiR, hiA⟩
      rw [signOfSet, if_neg (fun hi ↦ by
        rcases Finset.mem_union.mp (hmem.mp hi) with hi | hi
        · exact hiA hi
        · exact hiC hi)]
      rw [productTwoStageSignedLeft_value]
      simp [productTwoStageSharedValue, k, hiR, hiA, hiRA]
  · have hiA : i ∉ (ω k).2.1.1 := fun hiA ↦ hiR (hA hiA)
    have hiRA : i ∉ (ω k).1.1 \ (ω k).2.1.1 := fun hi ↦
      hiR (Finset.mem_sdiff.mp hi).1
    by_cases hiC : i ∈ (ω k).2.2.2.1
    · rw [signOfSet, if_pos (hmem.mpr (Finset.mem_union_right _ hiC))]
      rw [productTwoStageSignedLeft_value]
      simp [productTwoStageSharedValue, signOfSet, k, hiR, hiA, hiRA, hiC]
    · rw [signOfSet, if_neg (fun hi ↦ by
        rcases Finset.mem_union.mp (hmem.mp hi) with hi | hi
        · exact hiA hi
        · exact hiC hi)]
      rw [productTwoStageSignedLeft_value]
      simp [productTwoStageSharedValue, signOfSet, k, hiR, hiA, hiRA, hiC]

/-- Symmetric pointwise decomposition for the right sign vector. -/
lemma signOf_productTwoStageSliceRight_eq [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a b h : κ → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h) (i : α) :
    signOfSet (productTwoStageSliceRight P r a b h ω).1 i =
      productSignedSliceValue P (productTwoStageSignedRight P r a b h ω) i +
        productTwoStageSharedValue P r a b h ω i := by
  let k := P.bucket i
  have hiFiber : i ∈ P.fiber k := P.mem_ownFiber i
  have hR := (mem_booleanSlice.mp (ω k).1.2).1
  have hB := (mem_booleanSlice.mp (ω k).2.2.1.2).1
  have hC := (mem_booleanSlice.mp (ω k).2.2.2.2).1
  have hmem := mem_productTwoStageSliceRight_iff P r a b h ω i
  by_cases hiR : i ∈ (ω k).1.1
  · have hiC : i ∉ (ω k).2.2.2.1 := fun hiC ↦
      (Finset.mem_sdiff.mp (hC hiC)).2 hiR
    by_cases hiB : i ∈ (ω k).2.2.1.1
    · rw [signOfSet, if_pos (hmem.mpr (Finset.mem_union_left _ hiB))]
      rw [productTwoStageSignedRight_value]
      simp [productTwoStageSharedValue, k, hiR, hiB]
    · have hiRB : i ∈ (ω k).1.1 \ (ω k).2.2.1.1 :=
        Finset.mem_sdiff.mpr ⟨hiR, hiB⟩
      rw [signOfSet, if_neg (fun hi ↦ by
        rcases Finset.mem_union.mp (hmem.mp hi) with hi | hi
        · exact hiB hi
        · exact hiC hi)]
      rw [productTwoStageSignedRight_value]
      simp [productTwoStageSharedValue, k, hiR, hiB, hiRB]
  · have hiB : i ∉ (ω k).2.2.1.1 := fun hiB ↦ hiR (hB hiB)
    have hiRB : i ∉ (ω k).1.1 \ (ω k).2.2.1.1 := fun hi ↦
      hiR (Finset.mem_sdiff.mp hi).1
    by_cases hiC : i ∈ (ω k).2.2.2.1
    · rw [signOfSet, if_pos (hmem.mpr (Finset.mem_union_right _ hiC))]
      rw [productTwoStageSignedRight_value]
      simp [productTwoStageSharedValue, signOfSet, k, hiR, hiB, hiRB, hiC]
    · rw [signOfSet, if_neg (fun hi ↦ by
        rcases Finset.mem_union.mp (hmem.mp hi) with hi | hi
        · exact hiB hi
        · exact hiC hi)]
      rw [productTwoStageSignedRight_value]
      simp [productTwoStageSharedValue, signOfSet, k, hiR, hiB, hiRB, hiC]

section QuadraticDecomposition

variable {n K : ℕ}

/-- Linear plus quadratic terms, without the constant coefficient. -/
noncomputable def exposedQuadratic (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, f i * x i) + ∑ i, ∑ j, F i j * x i * x j

/-- Coefficient of one shared outside sign after two exposed vectors are
subtracted.  Both orientations of the quadratic matrix are retained. -/
noncomputable def quadraticCrossCoefficient (F : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (j : Fin n) : ℝ :=
  (∑ i, F i j * (x i - y i)) +
    ∑ i, F j i * (x i - y i)

/-- The cross term as a linear form in the common outside vector. -/
noncomputable def quadraticCrossLinear (F : Fin n → Fin n → ℝ)
    (x y z : Fin n → ℝ) : ℝ :=
  ∑ j, quadraticCrossCoefficient F x y j * z j

/-- Pure algebra: adding the same vector `z` to `x` and `y` leaves the
exposed difference plus the cross-linear term. -/
lemma quadraticPolynomial_add_common_sub (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (x y z : Fin n → ℝ) :
    quadraticPolynomial f₀ f F (fun i ↦ x i + z i) -
        quadraticPolynomial f₀ f F (fun i ↦ y i + z i) =
      exposedQuadratic f F x - exposedQuadratic f F y +
        quadraticCrossLinear F x y z := by
  have hxx : (∑ i, ∑ j, x i * F i j * x j) =
      ∑ i, ∑ j, F i j * x i * x j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hyy : (∑ i, ∑ j, y i * F i j * y j) =
      ∑ i, ∑ j, F i j * y i * y j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hxz : (∑ i, ∑ j, x i * F i j * z j) =
      ∑ j, (∑ i, F i j * x i) * z j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hyz : (∑ i, ∑ j, y i * F i j * z j) =
      ∑ j, (∑ i, F i j * y i) * z j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hzx : (∑ i, ∑ j, z i * F i j * x j) =
      ∑ j, (∑ i, F j i * x i) * z j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hzy : (∑ i, ∑ j, z i * F i j * y j) =
      ∑ j, (∑ i, F j i * y i) * z j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [quadraticPolynomial, linearPart, quadraticPart,
    exposedQuadratic, quadraticCrossLinear, quadraticCrossCoefficient]
  simp_rw [mul_add, mul_sub, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hxx, hyy, hxz, hyz, hzx, hzy]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- Exact deterministic decomposition of the two coupled quadratic values
into their two exposed signed-slice pieces and one shared outside linear
form. -/
lemma productTwoStage_quadratic_sub_decomposition
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (ω : ProductTwoStageSlicePoint P r a b h)
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ) :
    productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
        (productTwoStageSliceLeft P r a b h ω) -
      productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
        (productTwoStageSliceRight P r a b h ω) =
      signedSliceQuadratic P a (fun k ↦ r k - a k) f F
          (productTwoStageSignedLeft P r a b h ω) -
        signedSliceQuadratic P b (fun k ↦ r k - b k) f F
          (productTwoStageSignedRight P r a b h ω) +
        quadraticCrossLinear F
          (productSignedSliceValue P
            (productTwoStageSignedLeft P r a b h ω))
          (productSignedSliceValue P
            (productTwoStageSignedRight P r a b h ω))
          (productTwoStageSharedValue P r a b h ω) := by
  let x : Fin n → ℝ := productSignedSliceValue P
    (productTwoStageSignedLeft P r a b h ω)
  let y : Fin n → ℝ := productSignedSliceValue P
    (productTwoStageSignedRight P r a b h ω)
  let z : Fin n → ℝ := productTwoStageSharedValue P r a b h ω
  have hx : signOfSet (productTwoStageSliceLeft P r a b h ω).1 =
      fun i ↦ x i + z i := by
    funext i
    exact signOf_productTwoStageSliceLeft_eq P r a b h ω i
  have hy : signOfSet (productTwoStageSliceRight P r a b h ω).1 =
      fun i ↦ y i + z i := by
    funext i
    exact signOf_productTwoStageSliceRight_eq P r a b h ω i
  rw [productSliceQuadratic, productSliceQuadratic, sliceQuadratic,
    sliceQuadratic, hx, hy,
    quadraticPolynomial_add_common_sub]
  rfl

end QuadraticDecomposition

/-! ### Conditional shared-slice concentration -/

/-- The revealed signed vector determined by an exceptional set and one
inner Boolean slice. -/
def productRevealedSigned [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (r a : κ → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (A : ∀ k, BooleanSlicePoint (R k).1 (a k)) :
    ProductSignedSlicePoint P a (fun k ↦ r k - a k) := fun k ↦ by
  refine ⟨((A k).1, (R k).1 \ (A k).1), mem_signedSlice.mpr ⟨
    (mem_booleanSlice.mp (A k).2).1.trans
      (mem_booleanSlice.mp (R k).2).1,
    Finset.sdiff_subset.trans (mem_booleanSlice.mp (R k).2).1,
    Finset.disjoint_sdiff,
    (mem_booleanSlice.mp (A k).2).2, ?_⟩⟩
  rw [Finset.card_sdiff_of_subset (mem_booleanSlice.mp (A k).2).1,
    (mem_booleanSlice.mp (R k).2).2,
    (mem_booleanSlice.mp (A k).2).2]

/-- Reassemble a revealed triple and a family of outside slices into the
original dependent two-stage sample. -/
def assembleTwoStage {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b h : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (A : ∀ k, BooleanSlicePoint (R k).1 (a k))
    (B : ∀ k, BooleanSlicePoint (R k).1 (b k))
    (C : BooleanSliceFamilyPoint (fun k ↦ P.fiber k \ (R k).1) h) :
    ProductTwoStageSlicePoint P r a b h :=
  fun k ↦ ⟨R k, A k, B k, C k⟩

@[simp] lemma productTwoStageSignedLeft_assemble {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b h : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (A : ∀ k, BooleanSlicePoint (R k).1 (a k))
    (B : ∀ k, BooleanSlicePoint (R k).1 (b k))
    (C : BooleanSliceFamilyPoint (fun k ↦ P.fiber k \ (R k).1) h) :
    productTwoStageSignedLeft P r a b h
        (assembleTwoStage P r a b h R A B C) =
      productRevealedSigned P r a R A := by
  rfl

@[simp] lemma productTwoStageSignedRight_assemble {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b h : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (A : ∀ k, BooleanSlicePoint (R k).1 (a k))
    (B : ∀ k, BooleanSlicePoint (R k).1 (b k))
    (C : BooleanSliceFamilyPoint (fun k ↦ P.fiber k \ (R k).1) h) :
    productTwoStageSignedRight P r a b h
        (assembleTwoStage P r a b h R A B C) =
      productRevealedSigned P r b R B := by
  rfl

/-- On a fixed revealed fiber, the shared cross term is literally the
Boolean-slice family linear form with the cross coefficients. -/
lemma quadraticCrossLinear_assemble_eq {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (A : ∀ k, BooleanSlicePoint (R k).1 (a k))
    (B : ∀ k, BooleanSlicePoint (R k).1 (b k))
    (C : BooleanSliceFamilyPoint (fun k ↦ P.fiber k \ (R k).1) h)
    (F : Fin n → Fin n → ℝ) :
    quadraticCrossLinear F
        (productSignedSliceValue P (productRevealedSigned P r a R A))
        (productSignedSliceValue P (productRevealedSigned P r b R B))
        (productTwoStageSharedValue P r a b h
          (assembleTwoStage P r a b h R A B C)) =
      booleanSliceFamilyLinearOfCounts
        (fun k ↦ P.fiber k \ (R k).1)
        (fun _ i ↦ quadraticCrossCoefficient F
          (productSignedSliceValue P (productRevealedSigned P r a R A))
          (productSignedSliceValue P (productRevealedSigned P r b R B)) i) C := by
  unfold quadraticCrossLinear booleanSliceFamilyLinearOfCounts
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) P.bucket
    (fun i ↦ quadraticCrossCoefficient F
      (productSignedSliceValue P (productRevealedSigned P r a R A))
      (productSignedSliceValue P (productRevealedSigned P r b R B)) i *
        productTwoStageSharedValue P r a b h
          (assembleTwoStage P r a b h R A B C) i)]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ i ∈ P.fiber k,
      quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R A))
        (productSignedSliceValue P (productRevealedSigned P r b R B)) i *
          productTwoStageSharedValue P r a b h
            (assembleTwoStage P r a b h R A B C) i) =
    ∑ i ∈ P.fiber k \ (R k).1,
      quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R A))
        (productSignedSliceValue P (productRevealedSigned P r b R B)) i *
          signOfSet (C k).1 i
  have hRsub : (R k).1 ⊆ P.fiber k :=
    (mem_booleanSlice.mp (R k).2).1
  let g : Fin n → ℝ := fun i ↦
    quadraticCrossCoefficient F
      (productSignedSliceValue P (productRevealedSigned P r a R A))
      (productSignedSliceValue P (productRevealedSigned P r b R B)) i *
        productTwoStageSharedValue P r a b h
          (assembleTwoStage P r a b h R A B C) i
  have hsplit : (∑ i ∈ P.fiber k, g i) =
      (∑ i ∈ (R k).1, g i) +
        ∑ i ∈ P.fiber k \ (R k).1, g i := by
    calc
      (∑ i ∈ P.fiber k, g i) =
          ∑ i ∈ (R k).1 ∪ (P.fiber k \ (R k).1), g i := by
        rw [Finset.union_sdiff_of_subset hRsub]
      _ = (∑ i ∈ (R k).1, g i) +
          ∑ i ∈ P.fiber k \ (R k).1, g i := by
        rw [Finset.sum_union Finset.disjoint_sdiff]
  change (∑ i ∈ P.fiber k, g i) = _
  rw [hsplit]
  have hzero : (∑ i ∈ (R k).1,
      g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hbucket : P.bucket i = k := (P.mem_fiber k i).mp (hRsub hi)
    change quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R A))
        (productSignedSliceValue P (productRevealedSigned P r b R B)) i *
      (if i ∈ (R (P.bucket i)).1 then 0
       else signOfSet (C (P.bucket i)).1 i) = 0
    rw [hbucket]
    simp [hi]
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  have hbucket : P.bucket i = k :=
    (P.mem_fiber k i).mp (Finset.mem_sdiff.mp hi).1
  have hiR : i ∉ (R k).1 := (Finset.mem_sdiff.mp hi).2
  change quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R A))
        (productSignedSliceValue P (productRevealedSigned P r b R B)) i *
      (if i ∈ (R (P.bucket i)).1 then 0
       else signOfSet (C (P.bucket i)).1 i) = _
  rw [hbucket]
  simp [hiR]

lemma sum_abs_productRevealedSigned {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (A : ∀ k, BooleanSlicePoint (R k).1 (a k)) :
    (∑ i : α,
        |productSignedSliceValue P (productRevealedSigned P r a R A) i|) =
      ∑ k : Fin K, (r k : ℝ) := by
  have ha : ∀ k, a k ≤ r k := by
    intro k
    calc
      a k = (A k).1.card := (mem_booleanSlice.mp (A k).2).2.symm
      _ ≤ (R k).1.card :=
        Finset.card_le_card (mem_booleanSlice.mp (A k).2).1
      _ = r k := (mem_booleanSlice.mp (R k).2).2
  calc
    (∑ i : α,
        |productSignedSliceValue P (productRevealedSigned P r a R A) i|) =
        ∑ k : Fin K, (((a k + (r k - a k) : ℕ)) : ℝ) :=
      sum_abs_productSignedSliceValue P a (fun k ↦ r k - a k)
        (productRevealedSigned P r a R A)
    _ = ∑ k : Fin K, (r k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_sub_of_le (ha k)]

/-- The two revealed sign vectors differ in total `ℓ¹` norm by at most
twice the total exceptional-set size. -/
lemma sum_abs_revealed_sub_le {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (A : ∀ k, BooleanSlicePoint (R k).1 (a k))
    (B : ∀ k, BooleanSlicePoint (R k).1 (b k)) :
    (∑ i : α, |productSignedSliceValue P
          (productRevealedSigned P r a R A) i -
        productSignedSliceValue P
          (productRevealedSigned P r b R B) i|) ≤
      2 * ∑ k : Fin K, (r k : ℝ) := by
  calc
    (∑ i : α, |productSignedSliceValue P
          (productRevealedSigned P r a R A) i -
        productSignedSliceValue P
          (productRevealedSigned P r b R B) i|) ≤
        ∑ i : α,
          (|productSignedSliceValue P (productRevealedSigned P r a R A) i| +
            |productSignedSliceValue P
              (productRevealedSigned P r b R B) i|) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_sub _ _
    _ = 2 * ∑ k : Fin K, (r k : ℝ) := by
      rw [Finset.sum_add_distrib,
        sum_abs_productRevealedSigned P r a R A,
        sum_abs_productRevealedSigned P r b R B]
      ring

/-- Uniform entry bounds turn the revealed `ℓ¹` estimate into the exact
cross-coefficient bound used by the conditional slice concentration. -/
lemma abs_quadraticCrossCoefficient_revealed_le {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (Aset : ∀ k, BooleanSlicePoint (R k).1 (a k))
    (Bset : ∀ k, BooleanSlicePoint (R k).1 (b k))
    (F : Fin n → Fin n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ i j, |F i j| ≤ M) (j : Fin n) :
    |quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R Aset))
        (productSignedSliceValue P (productRevealedSigned P r b R Bset)) j| ≤
      4 * (∑ k : Fin K, (r k : ℝ)) * M := by
  let x : Fin n → ℝ :=
    productSignedSliceValue P (productRevealedSigned P r a R Aset)
  let y : Fin n → ℝ :=
    productSignedSliceValue P (productRevealedSigned P r b R Bset)
  let L : ℝ := ∑ k : Fin K, (r k : ℝ)
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hdx : (∑ i : Fin n, |x i - y i|) ≤ 2 * L := by
    exact sum_abs_revealed_sub_le P r a b R Aset Bset
  have hfirst : |∑ i : Fin n, F i j * (x i - y i)| ≤ M * (2 * L) := by
    calc
      |∑ i : Fin n, F i j * (x i - y i)| ≤
          ∑ i : Fin n, |F i j * (x i - y i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, M * |x i - y i| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hF i j) (abs_nonneg _)
      _ = M * ∑ i : Fin n, |x i - y i| := by
        rw [Finset.mul_sum]
      _ ≤ M * (2 * L) := mul_le_mul_of_nonneg_left hdx hM
  have hsecond : |∑ i : Fin n, F j i * (x i - y i)| ≤ M * (2 * L) := by
    calc
      |∑ i : Fin n, F j i * (x i - y i)| ≤
          ∑ i : Fin n, |F j i * (x i - y i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, M * |x i - y i| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hF j i) (abs_nonneg _)
      _ = M * ∑ i : Fin n, |x i - y i| := by
        rw [Finset.mul_sum]
      _ ≤ M * (2 * L) := mul_le_mul_of_nonneg_left hdx hM
  unfold quadraticCrossCoefficient
  calc
    |(∑ i, F i j * (x i - y i)) +
        ∑ i, F j i * (x i - y i)| ≤
        |∑ i, F i j * (x i - y i)| +
          |∑ i, F j i * (x i - y i)| := abs_add_le _ _
    _ ≤ M * (2 * L) + M * (2 * L) := add_le_add hfirst hsecond
    _ = 4 * L * M := by ring

/-- Conditional on the exceptional set and its two revealed inner slices,
the shared quadratic cross term has the exact balanced-slice subgaussian
tail.  This is the conditional concentration step in KSSS Lemma 11.2. -/
theorem quadraticCrossLinear_assemble_two_sided_probability {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (Aset : ∀ k, BooleanSlicePoint (R k).1 (a k))
    (Bset : ∀ k, BooleanSlicePoint (R k).1 (b k))
    (hbal : ∀ k, 2 * h k = (P.fiber k \ (R k).1).card)
    (e : ∀ k, Fin (P.fiber k \ (R k).1).card ≃
      ↑(P.fiber k \ (R k).1))
    (F : Fin n → Fin n → ℝ) (M t : ℝ)
    (hL : 0 < ∑ k : Fin K, (P.fiber k \ (R k).1).card)
    (hR : 0 < ∑ k : Fin K, (r k : ℝ))
    (hM : 0 < M) (ht : 0 ≤ t)
    (hF : ∀ i j, |F i j| ≤ M) :
    let I : Fin K → Finset (Fin n) :=
      fun k ↦ P.fiber k \ (R k).1
    let hell : ∀ k, h k ≤ (I k).card := fun k ↦ by
      change h k ≤ (P.fiber k \ (R k).1).card
      have := hbal k
      omega
    letI : Nonempty (BooleanSliceFamilyPoint I h) :=
      booleanSliceFamilyPoint_nonempty I h hell
    Concentration.uniformProbability
        (fun C : BooleanSliceFamilyPoint I h ↦
          t ≤ |quadraticCrossLinear F
            (productSignedSliceValue P
              (productRevealedSigned P r a R Aset))
            (productSignedSliceValue P
              (productRevealedSigned P r b R Bset))
            (productTwoStageSharedValue P r a b h
              (assembleTwoStage P r a b h R Aset Bset C))|) ≤
      2 * Real.exp
        (-t ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k \ (R k).1).card : ℕ) : ℝ)) *
            (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * M)) ^ 2)) := by
  let I : Fin K → Finset (Fin n) :=
    fun k ↦ P.fiber k \ (R k).1
  let hell : ∀ k, h k ≤ (I k).card := fun k ↦ by
    change h k ≤ (P.fiber k \ (R k).1).card
    have := hbal k
    omega
  letI : Nonempty (BooleanSliceFamilyPoint I h) :=
    booleanSliceFamilyPoint_nonempty I h hell
  have hC : 0 < 4 * (∑ k : Fin K, (r k : ℝ)) * M := by
    positivity
  have hc : ∀ (k : Fin K) (i : Fin n),
      |quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R Aset))
        (productSignedSliceValue P (productRevealedSigned P r b R Bset)) i| ≤
        4 * (∑ k : Fin K, (r k : ℝ)) * M := by
    intro k i
    exact abs_quadraticCrossCoefficient_revealed_le
      P r a b R Aset Bset F M hM.le hF i
  have htail := balancedBooleanSliceFamilyLinear_two_sided_probability
    I h hbal e
      (fun _ i ↦ quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R Aset))
        (productSignedSliceValue P (productRevealedSigned P r b R Bset)) i)
      (4 * (∑ k : Fin K, (r k : ℝ)) * M) t hL hC ht hc
  simpa only [I, quadraticCrossLinear_assemble_eq] using htail

/-! ### Averaging the conditional shared-slice tail -/

/-- Finite conditional probabilities bounded on every fiber remain bounded
after averaging over the base point. -/
lemma uniformProbability_sigma_le
    {A : Type*} {B : A → Type*}
    [Fintype A] [Nonempty A]
    [(a : A) → Fintype (B a)] [(a : A) → Nonempty (B a)]
    (E : (Σ a, B a) → Prop) (q : ℝ)
    (hq : ∀ a, Concentration.uniformProbability
      (fun b ↦ E ⟨a, b⟩) ≤ q) :
    Concentration.uniformProbability E ≤ q := by
  let a₀ : A := Classical.choice inferInstance
  letI : Nonempty (Σ a, B a) :=
    ⟨⟨a₀, Classical.choice (inferInstance : Nonempty (B a₀))⟩⟩
  have hfiber : ∀ a,
      (((Finset.univ.filter fun b : B a ↦ E ⟨a, b⟩).card : ℕ) : ℝ) ≤
        q * Fintype.card (B a) := by
    intro a
    have ha := hq a
    rw [Concentration.uniformProbability,
      div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
        (0 : ℝ) < Fintype.card (B a))] at ha
    simpa [mul_comm] using ha
  have hnumNat :
      (Finset.univ.filter E).card =
        ∑ a, (Finset.univ.filter fun b : B a ↦ E ⟨a, b⟩).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_sigma]
  rw [Concentration.uniformProbability,
    div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
      (0 : ℝ) < Fintype.card (Σ a, B a))]
  rw [Fintype.card_sigma, hnumNat, Nat.cast_sum]
  calc
    ∑ a, (((Finset.univ.filter fun b : B a ↦ E ⟨a, b⟩).card : ℕ) : ℝ) ≤
        ∑ a, q * Fintype.card (B a) :=
      Finset.sum_le_sum fun a _ ↦ hfiber a
    _ = q * ((∑ a, Fintype.card (B a) : ℕ) : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum]

lemma uniformProbability_or_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P Q : Ω → Prop) :
    Concentration.uniformProbability (fun ω ↦ P ω ∨ Q ω) ≤
      Concentration.uniformProbability P +
        Concentration.uniformProbability Q := by
  classical
  rw [Concentration.uniformProbability, Concentration.uniformProbability,
    Concentration.uniformProbability, ← add_div,
    div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos :
      (0 : ℝ) < Fintype.card Ω)]
  simp only [Finset.card_filter]
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

lemma FiniteUniformCoupling.isClose_of_bad_probability_le
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    (r q : ℝ)
    (hbad : C.probability
      (fun ω ↦ r < |X (C.left ω) - Y (C.right ω)|) ≤ q) :
    C.IsClose X Y r q := by
  classical
  let good : Fin C.size → Prop :=
    fun ω ↦ |X (C.left ω) - Y (C.right ω)| ≤ r
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin C.size))) good
  have hcard' :
      ((Finset.univ.filter fun ω ↦ r <
          |X (C.left ω) - Y (C.right ω)|).card : ℝ) +
        ((Finset.univ.filter good).card : ℝ) = C.size := by
    exact_mod_cast (by simpa [good, not_le, add_comm] using hcard)
  have hsize : (0 : ℝ) < C.size := by exact_mod_cast C.size_pos
  change ((Finset.univ.filter fun ω ↦ r <
      |X (C.left ω) - Y (C.right ω)|).card : ℝ) / C.size ≤ q at hbad
  change 1 - q ≤
    ((Finset.univ.filter good).card : ℝ) / C.size
  rw [le_div_iff₀ hsize]
  rw [div_le_iff₀ hsize] at hbad
  nlinarith

/-- Reindexing a finite sample by `Fin` preserves a bad-event probability
bound and therefore produces an `IsClose` certificate. -/
lemma FiniteUniformCoupling.ofMaps_isClose_of_uniformProbability_bad
    {Ω A B : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (left : Ω → A) (right : Ω → B)
    (hleft : ∀ g : A → ℂ, (𝔼 ω, g (left ω)) = 𝔼 a, g a)
    (hright : ∀ g : B → ℂ, (𝔼 ω, g (right ω)) = 𝔼 b, g b)
    (X : A → ℝ) (Y : B → ℝ) (r q : ℝ)
    (hbad : Concentration.uniformProbability
      (fun ω ↦ r < |X (left ω) - Y (right ω)|) ≤ q) :
    (FiniteUniformCoupling.ofMaps left right hleft hright).IsClose X Y r q := by
  classical
  let C := FiniteUniformCoupling.ofMaps left right hleft hright
  apply FiniteUniformCoupling.isClose_of_bad_probability_le C X Y r q
  letI : Nonempty (Fin (Fintype.card Ω)) :=
    Fin.pos_iff_nonempty.mp Fintype.card_pos
  let Q : Ω → Prop := fun ω ↦ r < |X (left ω) - Y (right ω)|
  have hprob :
      C.probability
          (fun i ↦ r < |X (C.left i) - Y (C.right i)|) =
        Concentration.uniformProbability
          (fun i : Fin C.size ↦ r < |X (C.left i) - Y (C.right i)|) := by
    rw [FiniteUniformCoupling.probability,
      Concentration.uniformProbability, Fintype.card_fin]
  rw [hprob]
  have hcomp : Concentration.uniformProbability
      (fun i : Fin (Fintype.card Ω) ↦
        Q ((Fintype.equivFin Ω).symm i)) ≤ q := by
    rw [uniformProbability_comp_equiv (Fintype.equivFin Ω).symm Q]
    exact hbad
  convert hcomp using 1 <;> rfl

/-- The data revealed before sampling the common outside slice in every
bucket. -/
abbrev ProductTwoStageRevealedPoint {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b : Fin K → ℕ) :=
  Σ R : ∀ k, BooleanSlicePoint (P.fiber k) (r k),
    (∀ k, BooleanSlicePoint (R k).1 (a k)) ×
      (∀ k, BooleanSlicePoint (R k).1 (b k))

/-- Rebracket a two-stage sample into its revealed data and its remaining
family of common outside slices. -/
noncomputable def productTwoStageSigmaEquiv {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b h : Fin K → ℕ) :
    ProductTwoStageSlicePoint P r a b h ≃
      Σ ρ : ProductTwoStageRevealedPoint P r a b,
        BooleanSliceFamilyPoint
          (fun k ↦ P.fiber k \ (ρ.1 k).1) h where
  toFun ω := ⟨⟨(fun k ↦ (ω k).1),
      (fun k ↦ (ω k).2.1), (fun k ↦ (ω k).2.2.1)⟩,
    fun k ↦ (ω k).2.2.2⟩
  invFun σ := assembleTwoStage P r a b h
    σ.1.1 σ.1.2.1 σ.1.2.2 σ.2
  left_inv ω := by
    funext k
    unfold assembleTwoStage
    apply Sigma.ext rfl
    rfl
  right_inv σ := by
    rcases σ with ⟨⟨R, Aset, Bset⟩, C⟩
    rfl

/-- Under the natural size constraints, the space of revealed data is
nonempty. -/
lemma productTwoStageRevealedPoint_nonempty {K : ℕ}
    (P : BucketPartition α (Fin K)) (r a b : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k) :
    Nonempty (ProductTwoStageRevealedPoint P r a b) := by
  let R : ∀ k, BooleanSlicePoint (P.fiber k) (r k) :=
    fun k ↦ Classical.choice (booleanSlicePoint_nonempty (hr k))
  let Aset : ∀ k, BooleanSlicePoint (R k).1 (a k) := fun k ↦
    Classical.choice (booleanSlicePoint_nonempty (by
      rw [(mem_booleanSlice.mp (R k).2).2]
      exact ha k))
  let Bset : ∀ k, BooleanSlicePoint (R k).1 (b k) := fun k ↦
    Classical.choice (booleanSlicePoint_nonempty (by
      rw [(mem_booleanSlice.mp (R k).2).2]
      exact hb k))
  exact ⟨⟨R, Aset, Bset⟩⟩

lemma card_fiber_sdiff_revealed {K : ℕ}
    (P : BucketPartition α (Fin K)) (r : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k)) (k : Fin K) :
    (P.fiber k \ (R k).1).card = (P.fiber k).card - r k := by
  rw [Finset.card_sdiff_of_subset (mem_booleanSlice.mp (R k).2).1,
    (mem_booleanSlice.mp (R k).2).2]

/-- The conditional cross-term tail, averaged over all revealed data of the
two-stage sampler.  This is the unconditional shared-slice estimate in KSSS
Lemma 11.2. -/
theorem quadraticCrossLinear_two_sided_probability {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (hbal : ∀ k, 2 * h k = (P.fiber k).card - r k)
    (F : Fin n → Fin n → ℝ) (M t : ℝ)
    (hL : 0 < ∑ k : Fin K, ((P.fiber k).card - r k : ℕ))
    (hR : 0 < ∑ k : Fin K, (r k : ℝ))
    (hM : 0 < M) (ht : 0 ≤ t)
    (hF : ∀ i j, |F i j| ≤ M) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability
        (fun ω : ProductTwoStageSlicePoint P r a b h ↦
          t ≤ |quadraticCrossLinear F
            (productSignedSliceValue P
              (productTwoStageSignedLeft P r a b h ω))
            (productSignedSliceValue P
              (productTwoStageSignedRight P r a b h ω))
            (productTwoStageSharedValue P r a b h ω)|) ≤
      2 * Real.exp
        (-t ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k).card - r k : ℕ) : ℝ)) *
            (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * M)) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  let A : Type := ProductTwoStageRevealedPoint P r a b
  let B : A → Type := fun ρ ↦ BooleanSliceFamilyPoint
    (fun k ↦ P.fiber k \ (ρ.1 k).1) h
  letI : Fintype A := by
    dsimp only [A, ProductTwoStageRevealedPoint]
    infer_instance
  letI : Nonempty A := productTwoStageRevealedPoint_nonempty P r a b hr ha hb
  letI : (ρ : A) → Fintype (B ρ) := fun ρ ↦ by
    dsimp only [B, BooleanSliceFamilyPoint]
    infer_instance
  letI : (ρ : A) → Nonempty (B ρ) := fun ρ ↦ by
    apply booleanSliceFamilyPoint_nonempty
    intro k
    rw [card_fiber_sdiff_revealed P r ρ.1 k]
    exact hh k
  let ρ₀ : A := Classical.choice inferInstance
  letI : Nonempty (Σ ρ : A, B ρ) :=
    ⟨⟨ρ₀, Classical.choice (inferInstance : Nonempty (B ρ₀))⟩⟩
  let E : ProductTwoStageSlicePoint P r a b h ≃ Σ ρ : A, B ρ :=
    productTwoStageSigmaEquiv P r a b h
  let Q : (Σ ρ : A, B ρ) → Prop := fun σ ↦
    t ≤ |quadraticCrossLinear F
      (productSignedSliceValue P
        (productTwoStageSignedLeft P r a b h (E.symm σ)))
      (productSignedSliceValue P
        (productTwoStageSignedRight P r a b h (E.symm σ)))
      (productTwoStageSharedValue P r a b h (E.symm σ))|
  have hcond : ∀ ρ : A,
      Concentration.uniformProbability (fun C : B ρ ↦ Q ⟨ρ, C⟩) ≤
        2 * Real.exp
          (-t ^ 2 /
            (2 * (∑ k : Fin K,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * M)) ^ 2)) := by
    intro ρ
    let R := ρ.1
    let Aset := ρ.2.1
    let Bset := ρ.2.2
    have hbalR : ∀ k,
        2 * h k = (P.fiber k \ (R k).1).card := by
      intro k
      rw [card_fiber_sdiff_revealed P r R k]
      exact hbal k
    have hLR : 0 < ∑ k : Fin K,
        (P.fiber k \ (R k).1).card := by
      simpa only [card_fiber_sdiff_revealed P r R] using hL
    have htail := quadraticCrossLinear_assemble_two_sided_probability
      P r a b h R Aset Bset hbalR
        (fun k ↦ (Finset.equivFin (P.fiber k \ (R k).1)).symm)
        F M t hLR hR hM ht hF
    let QR : B ρ → Prop := fun C ↦
      t ≤ |quadraticCrossLinear F
        (productSignedSliceValue P
          (productRevealedSigned P r a R Aset))
        (productSignedSliceValue P
          (productRevealedSigned P r b R Bset))
        (productTwoStageSharedValue P r a b h
          (assembleTwoStage P r a b h R Aset Bset C))|
    have hfun : (fun C : B ρ ↦ Q ⟨ρ, C⟩) = QR := by
      funext C
      apply propext
      have hEsymm : E.symm ⟨ρ, C⟩ =
          assembleTwoStage P r a b h R Aset Bset C := by
        rfl
      simp only [Q, hEsymm, QR,
        productTwoStageSignedLeft_assemble,
        productTwoStageSignedRight_assemble]
    rw [hfun]
    simpa only [A, B, R, Aset, Bset, QR,
      card_fiber_sdiff_revealed P r R] using htail
  calc
    Concentration.uniformProbability
        (fun ω : ProductTwoStageSlicePoint P r a b h ↦
          t ≤ |quadraticCrossLinear F
            (productSignedSliceValue P
              (productTwoStageSignedLeft P r a b h ω))
            (productSignedSliceValue P
              (productTwoStageSignedRight P r a b h ω))
            (productTwoStageSharedValue P r a b h ω)|) =
        Concentration.uniformProbability Q := by
      rw [← uniformProbability_comp_equiv E Q]
      apply congrArg Concentration.uniformProbability
      funext ω
      apply propext
      change (t ≤ |quadraticCrossLinear F
        (productSignedSliceValue P
          (productTwoStageSignedLeft P r a b h ω))
        (productSignedSliceValue P
          (productTwoStageSignedRight P r a b h ω))
        (productTwoStageSharedValue P r a b h ω)|) ↔
        (t ≤ |quadraticCrossLinear F
          (productSignedSliceValue P
            (productTwoStageSignedLeft P r a b h (E.symm (E ω))))
          (productSignedSliceValue P
            (productTwoStageSignedRight P r a b h (E.symm (E ω))))
          (productTwoStageSharedValue P r a b h (E.symm (E ω)))|)
      rw [E.symm_apply_apply]
    _ ≤ 2 * Real.exp
          (-t ^ 2 /
            (2 * (∑ k : Fin K,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * M)) ^ 2)) :=
      uniformProbability_sigma_le Q _ hcond

/-! ### The complete abstract two-stage quadratic estimate -/

/-- Union of the two exposed signed-slice tails and the averaged shared
cross-term tail.  This is the probability-theoretic core of KSSS Lemma 11.2,
before its source-specific powers of `n` are substituted. -/
theorem productTwoStage_quadratic_difference_probability {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (hbal : ∀ k, 2 * h k = (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (A B tE tC : ℝ)
    (hRnat : 0 < ∑ k : Fin K, r k)
    (hLnat : 0 < ∑ k : Fin K, ((P.fiber k).card - r k : ℕ))
    (hA : 0 < A) (hB : 0 ≤ B) (htE : 0 ≤ tE) (htC : 0 ≤ tC)
    (hlip : 0 < 4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a a h) :=
      productTwoStageSlicePoint_nonempty P r a a h hr ha ha hh
    Concentration.uniformProbability
        (fun ω : ProductTwoStageSlicePoint P r a a h ↦
          2 * tE + tC ≤
            |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
                (productTwoStageSliceLeft P r a a h ω) -
              productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
                (productTwoStageSliceRight P r a a h ω)|) ≤
      4 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
        2 * Real.exp
          (-tC ^ 2 /
            (2 * (∑ k : Fin K,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a a h) :=
    productTwoStageSlicePoint_nonempty P r a a h hr ha ha hh
  let XL : ProductTwoStageSlicePoint P r a a h → ℝ := fun ω ↦
    signedSliceQuadratic P a (fun k ↦ r k - a k) f F
      (productTwoStageSignedLeft P r a a h ω)
  let XR : ProductTwoStageSlicePoint P r a a h → ℝ := fun ω ↦
    signedSliceQuadratic P a (fun k ↦ r k - a k) f F
      (productTwoStageSignedRight P r a a h ω)
  let Z : ProductTwoStageSlicePoint P r a a h → ℝ := fun ω ↦
    quadraticCrossLinear F
      (productSignedSliceValue P (productTwoStageSignedLeft P r a a h ω))
      (productSignedSliceValue P (productTwoStageSignedRight P r a a h ω))
      (productTwoStageSharedValue P r a a h ω)
  let μ : ℝ := Concentration.uniformExpectation XL
  have hmean : Concentration.uniformExpectation XR = μ := by
    dsimp only [μ]
    calc
      Concentration.uniformExpectation XR =
          Concentration.uniformExpectation
            (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) :=
        uniformExpectation_productTwoStageSignedRight
          P r a a h hr ha ha hh _
      _ = Concentration.uniformExpectation XL :=
        (uniformExpectation_productTwoStageSignedLeft
          P r a a h hr ha ha hh _).symm
  have hleft := productTwoStageSignedLeft_quadratic_two_sided_probability
    P r a a h hr ha ha hh e f F A B tE hRnat hA.le hB htE hlip hf hF
  have hright := productTwoStageSignedRight_quadratic_two_sided_probability
    P r a a h hr ha ha hh e f F A B tE hRnat hA.le hB htE hlip hf hF
  have hcross := quadraticCrossLinear_two_sided_probability
    P r a a h hr ha ha hh hbal F A tC hLnat
      (by exact_mod_cast hRnat) hA htC hF
  change Concentration.uniformProbability
      (fun ω ↦ 2 * tE + tC ≤
        |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
            (productTwoStageSliceLeft P r a a h ω) -
          productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
            (productTwoStageSliceRight P r a a h ω)|) ≤ _
  change Concentration.uniformProbability
      (fun ω ↦ tE ≤ |XL ω - μ|) ≤ _ at hleft
  change Concentration.uniformProbability
      (fun ω ↦ tE ≤ |XR ω - Concentration.uniformExpectation XR|) ≤ _ at hright
  rw [hmean] at hright
  change Concentration.uniformProbability (fun ω ↦ tC ≤ |Z ω|) ≤ _ at hcross
  have hbad : ∀ ω : ProductTwoStageSlicePoint P r a a h,
      2 * tE + tC ≤
          |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a a h ω) -
            productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceRight P r a a h ω)| →
        (tE ≤ |XL ω - μ|) ∨
          (tE ≤ |XR ω - μ|) ∨ tC ≤ |Z ω| := by
    intro ω hlarge
    by_contra hgood
    push_neg at hgood
    have hdecomp := productTwoStage_quadratic_sub_decomposition
      P r a a h ω f₀ f F
    change _ = XL ω - XR ω + Z ω at hdecomp
    have hcenter : XL ω - XR ω + Z ω =
        (XL ω - μ) - (XR ω - μ) + Z ω := by ring
    have habs :
        |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a a h ω) -
            productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceRight P r a a h ω)| <
          2 * tE + tC := by
      rw [hdecomp, hcenter]
      calc
        |(XL ω - μ) - (XR ω - μ) + Z ω| ≤
            |(XL ω - μ) - (XR ω - μ)| + |Z ω| := abs_add_le _ _
        _ ≤ (|XL ω - μ| + |XR ω - μ|) + |Z ω| := by
          gcongr
          exact abs_sub _ _
        _ < 2 * tE + tC := by linarith [hgood.1, hgood.2.1, hgood.2.2]
    exact (not_lt_of_ge hlarge) habs
  calc
    Concentration.uniformProbability
        (fun ω ↦ 2 * tE + tC ≤
          |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a a h ω) -
            productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceRight P r a a h ω)|) ≤
        Concentration.uniformProbability
          (fun ω ↦ (tE ≤ |XL ω - μ|) ∨
            (tE ≤ |XR ω - μ|) ∨ tC ≤ |Z ω|) :=
      Concentration.uniformProbability_mono hbad
    _ ≤ Concentration.uniformProbability (fun ω ↦ tE ≤ |XL ω - μ|) +
          Concentration.uniformProbability
            (fun ω ↦ (tE ≤ |XR ω - μ|) ∨ tC ≤ |Z ω|) :=
      uniformProbability_or_le _ _
    _ ≤ Concentration.uniformProbability (fun ω ↦ tE ≤ |XL ω - μ|) +
          (Concentration.uniformProbability (fun ω ↦ tE ≤ |XR ω - μ|) +
            Concentration.uniformProbability (fun ω ↦ tC ≤ |Z ω|)) := by
      gcongr
      exact uniformProbability_or_le _ _
    _ ≤ (2 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2))) +
          ((2 * Real.exp
            (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
              (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2))) +
            (2 * Real.exp
              (-tC ^ 2 /
                (2 * (∑ k : Fin K,
                    (((P.fiber k).card - r k : ℕ) : ℝ)) *
                  (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2)))) := by
      exact add_le_add hleft (add_le_add hright hcross)
    _ = 4 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
        2 * Real.exp
          (-tC ^ 2 /
            (2 * (∑ k : Fin K,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2)) := by ring

/-- Coupling form of the complete abstract two-stage quadratic estimate.
Both marginals are the same product slice, and the exact probability bound
from `productTwoStage_quadratic_difference_probability` is packaged as an
`IsClose` certificate. -/
theorem productTwoStage_quadratic_isClose {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (hbal : ∀ k, 2 * h k = (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (A B tE tC : ℝ)
    (hRnat : 0 < ∑ k : Fin K, r k)
    (hLnat : 0 < ∑ k : Fin K, ((P.fiber k).card - r k : ℕ))
    (hA : 0 < A) (hB : 0 ≤ B) (htE : 0 ≤ tE) (htC : 0 ≤ tC)
    (hlip : 0 < 4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a a h) :=
      productTwoStageSlicePoint_nonempty P r a a h hr ha ha hh
    letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
      productSlicePoint_nonempty P (fun k ↦ a k + h k) (fun k ↦ by
        calc
          a k + h k ≤ r k + ((P.fiber k).card - r k) :=
            Nat.add_le_add (ha k) (hh k)
          _ = (P.fiber k).card := Nat.add_sub_of_le (hr k))
    (FiniteUniformCoupling.ofMaps
      (productTwoStageSliceLeft P r a a h)
      (productTwoStageSliceRight P r a a h)
      (complexExpectation_productTwoStageSliceLeft P r a a h hr ha ha hh)
      (complexExpectation_productTwoStageSliceRight P r a a h hr ha ha hh)).IsClose
        (productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F)
        (productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F)
        (2 * tE + tC)
        (4 * Real.exp
            (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
              (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
          2 * Real.exp
            (-tC ^ 2 /
              (2 * (∑ k : Fin K,
                  (((P.fiber k).card - r k : ℕ) : ℝ)) *
                (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2))) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a a h) :=
    productTwoStageSlicePoint_nonempty P r a a h hr ha ha hh
  have hell : ∀ k, a k + h k ≤ (P.fiber k).card := fun k ↦ by
    calc
      a k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (ha k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ a k + h k) hell
  let X := productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
  let q :=
    4 * Real.exp
        (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
          (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
      2 * Real.exp
        (-tC ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k).card - r k : ℕ) : ℝ)) *
            (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2))
  have htail := productTwoStage_quadratic_difference_probability
    P r a h hr ha hh hbal e f₀ f F A B tE tC hRnat hLnat hA hB
      htE htC hlip hf hF
  change Concentration.uniformProbability
      (fun ω : ProductTwoStageSlicePoint P r a a h ↦
        2 * tE + tC ≤
          |X (productTwoStageSliceLeft P r a a h ω) -
            X (productTwoStageSliceRight P r a a h ω)|) ≤ q at htail
  have hstrict : Concentration.uniformProbability
      (fun ω : ProductTwoStageSlicePoint P r a a h ↦
        2 * tE + tC <
          |X (productTwoStageSliceLeft P r a a h ω) -
            X (productTwoStageSliceRight P r a a h ω)|) ≤ q :=
    (Concentration.uniformProbability_mono fun _ hω ↦ hω.le).trans htail
  exact FiniteUniformCoupling.ofMaps_isClose_of_uniformProbability_bad
    (productTwoStageSliceLeft P r a a h)
    (productTwoStageSliceRight P r a a h)
    (complexExpectation_productTwoStageSliceLeft P r a a h hr ha ha hh)
    (complexExpectation_productTwoStageSliceRight P r a a h hr ha ha hh)
    X X (2 * tE + tC) q hstrict

/-- The same abstract two-stage estimate for two different target slice
sizes.  The only additional deterministic input is a bound for the gap
between the two exposed signed-slice means.  This is the form used in the
source proof of KSSS Lemma 11.2. -/
theorem productTwoStage_quadratic_difference_probability_of_meanGap
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (hbal : ∀ k, 2 * h k = (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (A B tE tC dMean : ℝ)
    (hRnat : 0 < ∑ k : Fin K, r k)
    (hLnat : 0 < ∑ k : Fin K, ((P.fiber k).card - r k : ℕ))
    (hA : 0 < A) (hB : 0 ≤ B) (htE : 0 ≤ tE) (htC : 0 ≤ tC)
    (hlip : 0 < 4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A)
    (hmean :
      |Concentration.uniformExpectation
          (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) -
        Concentration.uniformExpectation
          (signedSliceQuadratic P b (fun k ↦ r k - b k) f F)| ≤ dMean) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability
        (fun ω : ProductTwoStageSlicePoint P r a b h ↦
          2 * tE + tC + dMean ≤
            |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
                (productTwoStageSliceLeft P r a b h ω) -
              productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
                (productTwoStageSliceRight P r a b h ω)|) ≤
      4 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
        2 * Real.exp
          (-tC ^ 2 /
            (2 * (∑ k : Fin K,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  let XL : ProductTwoStageSlicePoint P r a b h → ℝ := fun ω ↦
    signedSliceQuadratic P a (fun k ↦ r k - a k) f F
      (productTwoStageSignedLeft P r a b h ω)
  let XR : ProductTwoStageSlicePoint P r a b h → ℝ := fun ω ↦
    signedSliceQuadratic P b (fun k ↦ r k - b k) f F
      (productTwoStageSignedRight P r a b h ω)
  let Z : ProductTwoStageSlicePoint P r a b h → ℝ := fun ω ↦
    quadraticCrossLinear F
      (productSignedSliceValue P (productTwoStageSignedLeft P r a b h ω))
      (productSignedSliceValue P (productTwoStageSignedRight P r a b h ω))
      (productTwoStageSharedValue P r a b h ω)
  let μL : ℝ := Concentration.uniformExpectation XL
  let μR : ℝ := Concentration.uniformExpectation XR
  have hμL : μL = Concentration.uniformExpectation
      (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) := by
    dsimp only [μL, XL]
    exact uniformExpectation_productTwoStageSignedLeft
      P r a b h hr ha hb hh _
  have hμR : μR = Concentration.uniformExpectation
      (signedSliceQuadratic P b (fun k ↦ r k - b k) f F) := by
    dsimp only [μR, XR]
    exact uniformExpectation_productTwoStageSignedRight
      P r a b h hr ha hb hh _
  have hleft := productTwoStageSignedLeft_quadratic_two_sided_probability
    P r a b h hr ha hb hh e f F A B tE hRnat hA.le hB htE hlip hf hF
  have hright := productTwoStageSignedRight_quadratic_two_sided_probability
    P r a b h hr ha hb hh e f F A B tE hRnat hA.le hB htE hlip hf hF
  have hcross := quadraticCrossLinear_two_sided_probability
    P r a b h hr ha hb hh hbal F A tC hLnat
      (by exact_mod_cast hRnat) hA htC hF
  change Concentration.uniformProbability
      (fun ω ↦ tE ≤ |XL ω - μL|) ≤ _ at hleft
  change Concentration.uniformProbability
      (fun ω ↦ tE ≤ |XR ω - μR|) ≤ _ at hright
  change Concentration.uniformProbability (fun ω ↦ tC ≤ |Z ω|) ≤ _ at hcross
  have hmean' : |μL - μR| ≤ dMean := by
    rw [hμL, hμR]
    exact hmean
  have hbad : ∀ ω : ProductTwoStageSlicePoint P r a b h,
      2 * tE + tC + dMean ≤
          |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a b h ω) -
            productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
              (productTwoStageSliceRight P r a b h ω)| →
        (tE ≤ |XL ω - μL|) ∨
          (tE ≤ |XR ω - μR|) ∨ tC ≤ |Z ω| := by
    intro ω hlarge
    by_contra hgood
    push Not at hgood
    have hdecomp := productTwoStage_quadratic_sub_decomposition
      P r a b h ω f₀ f F
    change _ = XL ω - XR ω + Z ω at hdecomp
    have hcenter : XL ω - XR ω + Z ω =
        ((XL ω - μL) - (XR ω - μR) + Z ω) + (μL - μR) := by
      ring
    have habs :
        |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a b h ω) -
            productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
              (productTwoStageSliceRight P r a b h ω)| <
          2 * tE + tC + dMean := by
      rw [hdecomp, hcenter]
      calc
        |((XL ω - μL) - (XR ω - μR) + Z ω) + (μL - μR)| ≤
            |(XL ω - μL) - (XR ω - μR) + Z ω| + |μL - μR| :=
          abs_add_le _ _
        _ ≤ (|XL ω - μL| + |XR ω - μR|) + |Z ω| +
            |μL - μR| := by
          gcongr
          calc
            |(XL ω - μL) - (XR ω - μR) + Z ω| ≤
                |(XL ω - μL) - (XR ω - μR)| + |Z ω| := abs_add_le _ _
            _ ≤ (|XL ω - μL| + |XR ω - μR|) + |Z ω| := by
              gcongr
              exact abs_sub _ _
        _ < 2 * tE + tC + dMean := by
          linarith [hgood.1, hgood.2.1, hgood.2.2, hmean']
    exact (not_lt_of_ge hlarge) habs
  calc
    Concentration.uniformProbability
        (fun ω ↦ 2 * tE + tC + dMean ≤
          |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a b h ω) -
            productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
              (productTwoStageSliceRight P r a b h ω)|) ≤
        Concentration.uniformProbability
          (fun ω ↦ (tE ≤ |XL ω - μL|) ∨
            (tE ≤ |XR ω - μR|) ∨ tC ≤ |Z ω|) :=
      Concentration.uniformProbability_mono hbad
    _ ≤ Concentration.uniformProbability (fun ω ↦ tE ≤ |XL ω - μL|) +
          Concentration.uniformProbability
            (fun ω ↦ (tE ≤ |XR ω - μR|) ∨ tC ≤ |Z ω|) :=
      uniformProbability_or_le _ _
    _ ≤ Concentration.uniformProbability (fun ω ↦ tE ≤ |XL ω - μL|) +
          (Concentration.uniformProbability (fun ω ↦ tE ≤ |XR ω - μR|) +
            Concentration.uniformProbability (fun ω ↦ tC ≤ |Z ω|)) := by
      gcongr
      exact uniformProbability_or_le _ _
    _ ≤ (2 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2))) +
          ((2 * Real.exp
            (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
              (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2))) +
            (2 * Real.exp
              (-tC ^ 2 /
                (2 * (∑ k : Fin K,
                    (((P.fiber k).card - r k : ℕ) : ℝ)) *
                  (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2)))) := by
      exact add_le_add hleft (add_le_add hright hcross)
    _ = 4 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
        2 * Real.exp
          (-tC ^ 2 /
            (2 * (∑ k : Fin K,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2)) := by ring

/-- Coupling form of the asymmetric two-stage estimate. -/
theorem productTwoStage_quadratic_isClose_of_meanGap {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (hbal : ∀ k, 2 * h k = (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (A B tE tC dMean : ℝ)
    (hRnat : 0 < ∑ k : Fin K, r k)
    (hLnat : 0 < ∑ k : Fin K, ((P.fiber k).card - r k : ℕ))
    (hA : 0 < A) (hB : 0 ≤ B) (htE : 0 ≤ tE) (htC : 0 ≤ tC)
    (hlip : 0 < 4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A)
    (hmean :
      |Concentration.uniformExpectation
          (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) -
        Concentration.uniformExpectation
          (signedSliceQuadratic P b (fun k ↦ r k - b k) f F)| ≤ dMean) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
      productSlicePoint_nonempty P (fun k ↦ a k + h k) (fun k ↦ by
        calc
          a k + h k ≤ r k + ((P.fiber k).card - r k) :=
            Nat.add_le_add (ha k) (hh k)
          _ = (P.fiber k).card := Nat.add_sub_of_le (hr k))
    letI : Nonempty (ProductSlicePoint P (fun k ↦ b k + h k)) :=
      productSlicePoint_nonempty P (fun k ↦ b k + h k) (fun k ↦ by
        calc
          b k + h k ≤ r k + ((P.fiber k).card - r k) :=
            Nat.add_le_add (hb k) (hh k)
          _ = (P.fiber k).card := Nat.add_sub_of_le (hr k))
    (FiniteUniformCoupling.ofMaps
      (productTwoStageSliceLeft P r a b h)
      (productTwoStageSliceRight P r a b h)
      (complexExpectation_productTwoStageSliceLeft P r a b h hr ha hb hh)
      (complexExpectation_productTwoStageSliceRight P r a b h hr ha hb hh)).IsClose
        (productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F)
        (productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F)
        (2 * tE + tC + dMean)
        (4 * Real.exp
            (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
              (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
          2 * Real.exp
            (-tC ^ 2 /
              (2 * (∑ k : Fin K,
                  (((P.fiber k).card - r k : ℕ) : ℝ)) *
                (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2))) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  have hell : ∀ k, a k + h k ≤ (P.fiber k).card := fun k ↦ by
    calc
      a k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (ha k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  have hell' : ∀ k, b k + h k ≤ (P.fiber k).card := fun k ↦ by
    calc
      b k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (hb k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ a k + h k) hell
  letI : Nonempty (ProductSlicePoint P (fun k ↦ b k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ b k + h k) hell'
  let X := productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
  let Y := productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
  let q :=
    4 * Real.exp
        (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
          (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
      2 * Real.exp
        (-tC ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k).card - r k : ℕ) : ℝ)) *
            (4 * (4 * (∑ k : Fin K, (r k : ℝ)) * A)) ^ 2))
  have htail := productTwoStage_quadratic_difference_probability_of_meanGap
    P r a b h hr ha hb hh hbal e f₀ f F A B tE tC dMean
      hRnat hLnat hA hB htE htC hlip hf hF hmean
  change Concentration.uniformProbability
      (fun ω : ProductTwoStageSlicePoint P r a b h ↦
        2 * tE + tC + dMean ≤
          |X (productTwoStageSliceLeft P r a b h ω) -
            Y (productTwoStageSliceRight P r a b h ω)|) ≤ q at htail
  have hstrict : Concentration.uniformProbability
      (fun ω : ProductTwoStageSlicePoint P r a b h ↦
        2 * tE + tC + dMean <
          |X (productTwoStageSliceLeft P r a b h ω) -
            Y (productTwoStageSliceRight P r a b h ω)|) ≤ q :=
    (Concentration.uniformProbability_mono fun _ hω ↦ hω.le).trans htail
  exact FiniteUniformCoupling.ofMaps_isClose_of_uniformProbability_bad
    (productTwoStageSliceLeft P r a b h)
    (productTwoStageSliceRight P r a b h)
    (complexExpectation_productTwoStageSliceLeft P r a b h hr ha hb hh)
    (complexExpectation_productTwoStageSliceRight P r a b h hr ha hb hh)
    X Y (2 * tE + tC + dMean) q hstrict

/-! ### Integer bookkeeping for the source coupling -/

/-- Exceptional-set size after reserving two common half-slices of size
`core`. -/
def twoStageExceptionalSize {κ : Type*} (bucketSize core : κ → ℕ)
    (k : κ) : ℕ :=
  bucketSize k - 2 * core k

/-- Number of positive coordinates sampled inside the exceptional set. -/
def twoStageInnerSize {κ : Type*} (ell core : κ → ℕ) (k : κ) : ℕ :=
  ell k - core k

lemma twoStageExceptionalSize_le {κ : Type*} (bucketSize core : κ → ℕ)
    (k : κ) : twoStageExceptionalSize bucketSize core k ≤ bucketSize k := by
  exact Nat.sub_le _ _

lemma twoStageExceptionalSize_complement {κ : Type*}
    (bucketSize core : κ → ℕ) (hcore : ∀ k, 2 * core k ≤ bucketSize k)
    (k : κ) :
    bucketSize k - twoStageExceptionalSize bucketSize core k = 2 * core k := by
  simp only [twoStageExceptionalSize]
  have hk := hcore k
  omega

lemma twoStageInnerSize_add_core {κ : Type*} (ell core : κ → ℕ)
    (hlow : ∀ k, core k ≤ ell k) (k : κ) :
    twoStageInnerSize ell core k + core k = ell k := by
  simp only [twoStageInnerSize]
  have hk := hlow k
  omega

lemma twoStageInnerSize_le_exceptional {κ : Type*}
    (bucketSize ell core : κ → ℕ)
    (hlow : ∀ k, core k ≤ ell k)
    (hhigh : ∀ k, ell k + core k ≤ bucketSize k) (k : κ) :
    twoStageInnerSize ell core k ≤
      twoStageExceptionalSize bucketSize core k := by
  simp only [twoStageInnerSize, twoStageExceptionalSize]
  have hlowk := hlow k
  have hhighk := hhigh k
  omega

/-- All cardinality obligations of the two-stage sampler follow from the
source's central-window inequalities `core ≤ ell ≤ bucketSize - core`. -/
lemma twoStage_source_cardinality_data {κ : Type*}
    (bucketSize ell ell' core : κ → ℕ)
    (hcore : ∀ k, 2 * core k ≤ bucketSize k)
    (hlow : ∀ k, core k ≤ ell k) (hlow' : ∀ k, core k ≤ ell' k)
    (hhigh : ∀ k, ell k + core k ≤ bucketSize k)
    (hhigh' : ∀ k, ell' k + core k ≤ bucketSize k) :
    let r := twoStageExceptionalSize bucketSize core
    let a := twoStageInnerSize ell core
    let b := twoStageInnerSize ell' core
    (∀ k, r k ≤ bucketSize k) ∧
      (∀ k, a k ≤ r k) ∧ (∀ k, b k ≤ r k) ∧
      (∀ k, core k ≤ bucketSize k - r k) ∧
      (∀ k, 2 * core k = bucketSize k - r k) ∧
      (∀ k, a k + core k = ell k) ∧
      (∀ k, b k + core k = ell' k) := by
  dsimp only
  refine ⟨twoStageExceptionalSize_le bucketSize core,
    twoStageInnerSize_le_exceptional bucketSize ell core hlow hhigh,
    twoStageInnerSize_le_exceptional bucketSize ell' core hlow' hhigh',
    ?_, ?_, twoStageInnerSize_add_core ell core hlow,
    twoStageInnerSize_add_core ell' core hlow'⟩
  · intro k
    rw [twoStageExceptionalSize_complement bucketSize core hcore k]
    omega
  · intro k
    exact (twoStageExceptionalSize_complement bucketSize core hcore k).symm

/-- Width of the near-balanced window in KSSS Section 11. -/
noncomputable def ksssSliceMargin (n : ℕ) (δ : ℝ) : ℝ :=
  scale n ((1 - δ) / 2) * Real.log n

/-- The common half-slice reserved outside the exceptional set in the
source coupling. -/
noncomputable def ksssCoreSize (n : ℕ) (δ : ℝ) (bucketSize : ℕ) : ℕ :=
  Nat.floor ((bucketSize : ℝ) / 2 - ksssSliceMargin n δ)

lemma ksssCoreSize_window (n bucketSize ell : ℕ) (δ : ℝ)
    (hmargin0 : 0 ≤ ksssSliceMargin n δ)
    (hmargin : ksssSliceMargin n δ ≤ (bucketSize : ℝ) / 2)
    (hnear : |(ell : ℝ) - (bucketSize : ℝ) / 2| ≤
      ksssSliceMargin n δ) :
    ksssCoreSize n δ bucketSize ≤ ell ∧
      ell + ksssCoreSize n δ bucketSize ≤ bucketSize ∧
      2 * ksssCoreSize n δ bucketSize ≤ bucketSize := by
  let x : ℝ := (bucketSize : ℝ) / 2 - ksssSliceMargin n δ
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hfloor : (ksssCoreSize n δ bucketSize : ℝ) ≤ x := by
    exact Nat.floor_le hx0
  have hnear' := abs_le.mp hnear
  have hlowR : (ksssCoreSize n δ bucketSize : ℝ) ≤ ell := by
    dsimp only [x] at hfloor
    linarith
  have hhighR : (ell : ℝ) + ksssCoreSize n δ bucketSize ≤ bucketSize := by
    dsimp only [x] at hfloor
    linarith
  have hcoreR : (2 * ksssCoreSize n δ bucketSize : ℕ) ≤ bucketSize := by
    exact_mod_cast (show (2 : ℝ) * ksssCoreSize n δ bucketSize ≤ bucketSize by
      dsimp only [x] at hfloor
      linarith)
  exact ⟨by exact_mod_cast hlowR, by exact_mod_cast hhighR, hcoreR⟩

/-- `IsNearBalanced` supplies all integral central-window inequalities for
the floor choice in the source coupling, once the asymptotic margin fits
inside half a bucket. -/
lemma ksssCoreSize_source_windows {n m : ℕ}
    (δ : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (ell ell' : Fin m → ℕ)
    (hmargin0 : 0 ≤ ksssSliceMargin n δ)
    (hmargin : ∀ k, ksssSliceMargin n δ ≤
      ((P.fiber k).card : ℝ) / 2)
    (hell : IsNearBalanced δ P ell)
    (hell' : IsNearBalanced δ P ell') :
    let core : Fin m → ℕ := fun k ↦
      ksssCoreSize n δ (P.fiber k).card
    (∀ k, core k ≤ ell k) ∧ (∀ k, core k ≤ ell' k) ∧
      (∀ k, ell k + core k ≤ (P.fiber k).card) ∧
      (∀ k, ell' k + core k ≤ (P.fiber k).card) ∧
      (∀ k, 2 * core k ≤ (P.fiber k).card) := by
  dsimp only
  have hw : ∀ k (s : Fin m → ℕ), IsNearBalanced δ P s →
      ksssCoreSize n δ (P.fiber k).card ≤ s k ∧
        s k + ksssCoreSize n δ (P.fiber k).card ≤ (P.fiber k).card ∧
        2 * ksssCoreSize n δ (P.fiber k).card ≤ (P.fiber k).card := by
    intro k s hs
    apply ksssCoreSize_window n (P.fiber k).card (s k) δ hmargin0 (hmargin k)
    simpa only [ksssSliceMargin] using hs k
  exact ⟨fun k ↦ (hw k ell hell).1, fun k ↦ (hw k ell' hell').1,
    fun k ↦ (hw k ell hell).2.1, fun k ↦ (hw k ell' hell').2.1,
    fun k ↦ (hw k ell hell).2.2⟩

/-! ### Exchangeability of signed slices -/

/-- Relabel both colour classes of a signed slice along an embedding. -/
noncomputable def signedSliceMap {I J : Finset α} {plus minus : ℕ}
    (ρ : α ↪ α) (hIJ : I.map ρ = J) (S : SignedSlicePoint I plus minus) :
    SignedSlicePoint J plus minus := by
  classical
  refine ⟨(S.1.1.map ρ, S.1.2.map ρ), mem_signedSlice.mpr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    rw [← hIJ]
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr
      ⟨y, (mem_signedSlice.mp S.2).1 hy, rfl⟩
  · intro x hx
    rw [← hIJ]
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr
      ⟨y, (mem_signedSlice.mp S.2).2.1 hy, rfl⟩
  · exact (Finset.disjoint_map ρ).2 (mem_signedSlice.mp S.2).2.2.1
  · rw [Finset.card_map]
    exact (mem_signedSlice.mp S.2).2.2.2.1
  · rw [Finset.card_map]
    exact (mem_signedSlice.mp S.2).2.2.2.2

/-- A permutation preserving the ambient set acts on its signed slices. -/
noncomputable def signedSlicePermEquiv (I : Finset α) (plus minus : ℕ)
    (ρ : Equiv.Perm α) (hI : I.map ρ.toEmbedding = I) :
    SignedSlicePoint I plus minus ≃ SignedSlicePoint I plus minus := by
  classical
  have hIinv : I.map ρ.symm.toEmbedding = I := by
    calc
      I.map ρ.symm.toEmbedding =
          (I.map ρ.toEmbedding).map ρ.symm.toEmbedding := by rw [hI]
      _ = I := by
        rw [Finset.map_map]
        simpa using Finset.map_refl I
  exact {
    toFun := signedSliceMap ρ.toEmbedding hI
    invFun := signedSliceMap ρ.symm.toEmbedding hIinv
    left_inv := by
      intro S
      apply Subtype.ext
      apply Prod.ext <;> simp [signedSliceMap, Finset.map_map]
    right_inv := by
      intro S
      apply Subtype.ext
      apply Prod.ext <;> simp [signedSliceMap, Finset.map_map]
  }

@[simp] lemma signedSliceValue_signedSlicePermEquiv
    (I : Finset α) (plus minus : ℕ) (ρ : Equiv.Perm α)
    (hI : I.map ρ.toEmbedding = I) (S : SignedSlicePoint I plus minus)
    (i : α) :
    signedSliceValue (signedSlicePermEquiv I plus minus ρ hI S) (ρ i) =
      signedSliceValue S i := by
  classical
  change signedSliceValue (signedSliceMap ρ.toEmbedding hI S) (ρ i) =
    signedSliceValue S i
  simp only [signedSliceValue, signedSliceMap]
  simp

/-- Apply one ambient permutation simultaneously to every bucket signed
slice. -/
noncomputable def productSignedSlicePermEquiv
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (ρ : Equiv.Perm α)
    (hP : ∀ k, (P.fiber k).map ρ.toEmbedding = P.fiber k) :
    ProductSignedSlicePoint P plus minus ≃ ProductSignedSlicePoint P plus minus :=
  Equiv.piCongrRight fun k ↦
    signedSlicePermEquiv (P.fiber k) (plus k) (minus k) ρ (hP k)

@[simp] lemma productSignedSliceValue_productSignedSlicePermEquiv
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (ρ : Equiv.Perm α)
    (hP : ∀ k, (P.fiber k).map ρ.toEmbedding = P.fiber k)
    (S : ProductSignedSlicePoint P plus minus) (i : α) :
    productSignedSliceValue P
        (productSignedSlicePermEquiv P plus minus ρ hP S) (ρ i) =
      productSignedSliceValue P S i := by
  have hb : P.bucket (ρ i) = P.bucket i := by
    apply (P.mem_fiber (P.bucket i) (ρ i)).mp
    rw [← hP (P.bucket i)]
    exact Finset.mem_map.mpr
      ⟨i, (P.mem_fiber (P.bucket i) i).mpr rfl, rfl⟩
  unfold productSignedSliceValue
  rw [hb]
  exact signedSliceValue_signedSlicePermEquiv
    (P.fiber (P.bucket i)) (plus (P.bucket i)) (minus (P.bucket i))
      ρ (hP (P.bucket i)) (S (P.bucket i)) i

lemma bucketSwap_preserves_fibers [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) {i j : α}
    (hij : P.bucket i = P.bucket j) (k : κ) :
    (P.fiber k).map (Equiv.swap i j).toEmbedding = P.fiber k := by
  have hb : ∀ x : α, P.bucket (Equiv.swap i j x) = P.bucket x := by
    intro x
    by_cases hxi : x = i
    · subst x
      simp [hij]
    · by_cases hxj : x = j
      · subst x
        simp [hij]
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    apply (P.mem_fiber k _).mpr
    change P.bucket (Equiv.swap i j y) = k
    rw [hb]
    exact (P.mem_fiber k y).mp hy
  · rw [Finset.card_map]

/-- All coordinates in one bucket have the same signed-slice first moment. -/
lemma uniformExpectation_productSignedSliceValue_eq_of_sameBucket
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    {i j : α} (hij : P.bucket i = P.bucket j) :
    Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S i) =
      Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S j) := by
  let ρ : Equiv.Perm α := Equiv.swap i j
  have hP : ∀ k, (P.fiber k).map ρ.toEmbedding = P.fiber k :=
    bucketSwap_preserves_fibers P hij
  let E := productSignedSlicePermEquiv P plus minus ρ hP
  have heq := Fintype.expect_equiv E
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S i)
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S j) (by
      intro S
      have hv := productSignedSliceValue_productSignedSlicePermEquiv
        P plus minus ρ hP S i
      dsimp only [ρ] at hv
      simpa using hv.symm)
  simpa [Concentration.uniformExpectation,
    Fintype.expect_eq_sum_div_card] using heq

/-- The signed values in one bucket have deterministic total equal to the
positive support size minus the negative support size. -/
lemma sum_fiber_productSignedSliceValue
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (S : ProductSignedSlicePoint P plus minus) (k : κ) :
    ∑ i ∈ P.fiber k, productSignedSliceValue P S i =
      (plus k : ℝ) - minus k := by
  have hb : ∀ i ∈ P.fiber k, P.bucket i = k := fun i hi ↦
    (P.mem_fiber k i).mp hi
  have hreduce : (∑ i ∈ P.fiber k, productSignedSliceValue P S i) =
      ∑ i ∈ P.fiber k, signedSliceValue (S k) i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [productSignedSliceValue]
    rw [hb i hi]
  rw [hreduce]
  let Pos : Finset α := (S k).1.1
  let Neg : Finset α := (S k).1.2
  have hdisj : Disjoint Pos Neg := (mem_signedSlice.mp (S k).2).2.2.1
  have hpos : (P.fiber k).filter (fun i ↦ i ∈ Pos) = Pos := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi ↦ hi.2
    · intro hi
      exact ⟨(mem_signedSlice.mp (S k).2).1 hi, hi⟩
  have hneg : (P.fiber k).filter (fun i ↦ i ∈ Neg) = Neg := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi ↦ hi.2
    · intro hi
      exact ⟨(mem_signedSlice.mp (S k).2).2.1 hi, hi⟩
  have hval (i : α) : signedSliceValue (S k) i =
      (if i ∈ Pos then 1 else 0) - (if i ∈ Neg then 1 else 0) := by
    by_cases hip : i ∈ Pos
    · have hin : i ∉ Neg := fun hin ↦
        Finset.disjoint_left.mp hdisj hip hin
      simp [signedSliceValue, Pos, Neg, hip, hin]
    · by_cases hin : i ∈ Neg
      · simp [signedSliceValue, Pos, Neg, hip, hin]
      · simp [signedSliceValue, Pos, Neg, hip, hin]
  simp_rw [hval, Finset.sum_sub_distrib]
  rw [Finset.sum_ite, Finset.sum_ite, hpos, hneg]
  have hPosCard : Pos.card = plus k :=
    (mem_signedSlice.mp (S k).2).2.2.2.1
  have hNegCard : Neg.card = minus k :=
    (mem_signedSlice.mp (S k).2).2.2.2.2
  simp [hPosCard, hNegCard]

/-- The squared signed values in one bucket have deterministic total support
size. -/
lemma sum_sq_fiber_productSignedSliceValue
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (S : ProductSignedSlicePoint P plus minus) (k : κ) :
    ∑ i ∈ P.fiber k, productSignedSliceValue P S i ^ 2 =
      (plus k + minus k : ℕ) := by
  have hb : ∀ i ∈ P.fiber k, P.bucket i = k := fun i hi ↦
    (P.mem_fiber k i).mp hi
  have hreduce : (∑ i ∈ P.fiber k,
      productSignedSliceValue P S i ^ 2) =
      ∑ i ∈ P.fiber k, signedSliceValue (S k) i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [productSignedSliceValue]
    rw [hb i hi]
  rw [hreduce]
  let Pos : Finset α := (S k).1.1
  let Neg : Finset α := (S k).1.2
  have hdisj : Disjoint Pos Neg := (mem_signedSlice.mp (S k).2).2.2.1
  have hpos : (P.fiber k).filter (fun i ↦ i ∈ Pos) = Pos := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi ↦ hi.2
    · intro hi
      exact ⟨(mem_signedSlice.mp (S k).2).1 hi, hi⟩
  have hneg : (P.fiber k).filter (fun i ↦ i ∈ Neg) = Neg := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi ↦ hi.2
    · intro hi
      exact ⟨(mem_signedSlice.mp (S k).2).2.1 hi, hi⟩
  have hsq (i : α) : signedSliceValue (S k) i ^ 2 =
      (if i ∈ Pos then 1 else 0) + (if i ∈ Neg then 1 else 0) := by
    by_cases hip : i ∈ Pos
    · have hin : i ∉ Neg := fun hin ↦
        Finset.disjoint_left.mp hdisj hip hin
      simp [signedSliceValue, Pos, Neg, hip, hin]
    · by_cases hin : i ∈ Neg
      · simp [signedSliceValue, Pos, Neg, hip, hin]
      · simp [signedSliceValue, Pos, Neg, hip, hin]
  simp_rw [hsq, Finset.sum_add_distrib]
  rw [Finset.sum_ite, Finset.sum_ite, hpos, hneg]
  have hPosCard : Pos.card = plus k :=
    (mem_signedSlice.mp (S k).2).2.2.2.1
  have hNegCard : Neg.card = minus k :=
    (mem_signedSlice.mp (S k).2).2.2.2.2
  simp [hPosCard, hNegCard]

/-- Two ordered pairs of distinct coordinates in one bucket are carried to
one another by an ambient permutation that preserves every bucket. -/
lemma exists_bucketPerm_map_pair [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (k : κ) {i j u v : α}
    (hi : i ∈ P.fiber k) (hj : j ∈ P.fiber k)
    (hu : u ∈ P.fiber k) (hv : v ∈ P.fiber k)
    (hij : i ≠ j) (huv : u ≠ v) :
    ∃ ρ : Equiv.Perm α, ρ i = u ∧ ρ j = v ∧
      ∀ h, (P.fiber h).map ρ.toEmbedding = P.fiber h := by
  let ii : ↑(P.fiber k) := ⟨i, hi⟩
  let jj : ↑(P.fiber k) := ⟨j, hj⟩
  let uu : ↑(P.fiber k) := ⟨u, hu⟩
  let vv : ↑(P.fiber k) := ⟨v, hv⟩
  let src : Bool → ↑(P.fiber k)
    | false => ii
    | true => jj
  let dst : Bool → ↑(P.fiber k)
    | false => uu
    | true => vv
  have hsrc : Function.Injective src := by
    intro a b hab
    cases a <;> cases b <;> simp only [src] at hab
    · rfl
    · exact (hij (congrArg Subtype.val hab)).elim
    · exact (hij (congrArg Subtype.val hab.symm)).elim
    · rfl
  have hdst : Function.Injective dst := by
    intro a b hab
    cases a <;> cases b <;> simp only [dst] at hab
    · rfl
    · exact (huv (congrArg Subtype.val hab)).elim
    · exact (huv (congrArg Subtype.val hab.symm)).elim
    · rfl
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair src dst hsrc hdst
  let ρ : Equiv.Perm α := σ.extendDomain (Equiv.refl ↑(P.fiber k))
  have hρi : ρ i = u := by
    have hs := hσ false
    change σ.extendDomain (Equiv.refl ↑(P.fiber k)) i = u
    rw [show i = ((Equiv.refl ↑(P.fiber k)) ii : α) by rfl,
      Equiv.Perm.extendDomain_apply_image]
    exact congrArg Subtype.val hs
  have hρj : ρ j = v := by
    have hs := hσ true
    change σ.extendDomain (Equiv.refl ↑(P.fiber k)) j = v
    rw [show j = ((Equiv.refl ↑(P.fiber k)) jj : α) by rfl,
      Equiv.Perm.extendDomain_apply_image]
    exact congrArg Subtype.val hs
  refine ⟨ρ, hρi, hρj, ?_⟩
  intro h
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    by_cases hyk : y ∈ P.fiber k
    · have hkh : k = h := by
        exact ((P.mem_fiber k y).mp hyk).symm.trans
          ((P.mem_fiber h y).mp hy)
      subst h
      apply (P.mem_fiber k _).mpr
      apply (P.mem_fiber k _).mp
      change σ.extendDomain (Equiv.refl ↑(P.fiber k)) y ∈ P.fiber k
      rw [Equiv.Perm.extendDomain_apply_subtype _ _ hyk]
      exact (σ _).property
    · change ρ y ∈ P.fiber h
      rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hyk]
      exact hy
  · rw [Finset.card_map]

/-- The mixed second moment is the same for all ordered distinct pairs in a
fixed bucket. -/
lemma uniformExpectation_productSignedSliceValue_mul_eq_of_sameBucket
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    (k : κ) {i j u v : α}
    (hi : i ∈ P.fiber k) (hj : j ∈ P.fiber k)
    (hu : u ∈ P.fiber k) (hv : v ∈ P.fiber k)
    (hij : i ≠ j) (huv : u ≠ v) :
    Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S i * productSignedSliceValue P S j) =
      Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S u * productSignedSliceValue P S v) := by
  obtain ⟨ρ, hρi, hρj, hP⟩ :=
    exists_bucketPerm_map_pair P k hi hj hu hv hij huv
  let E := productSignedSlicePermEquiv P plus minus ρ hP
  have heq := Fintype.expect_equiv E
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S i * productSignedSliceValue P S j)
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S u * productSignedSliceValue P S v) (by
      intro S
      have hvi := productSignedSliceValue_productSignedSlicePermEquiv
        P plus minus ρ hP S i
      have hvj := productSignedSliceValue_productSignedSlicePermEquiv
        P plus minus ρ hP S j
      calc
        productSignedSliceValue P S i * productSignedSliceValue P S j =
            productSignedSliceValue P (E S) (ρ i) *
              productSignedSliceValue P (E S) (ρ j) :=
          congrArg₂ (fun x y : ℝ ↦ x * y) hvi.symm hvj.symm
        _ = productSignedSliceValue P (E S) u *
              productSignedSliceValue P (E S) v := by rw [hρi, hρj])
  simpa [Concentration.uniformExpectation,
    Fintype.expect_eq_sum_div_card] using heq

/-- Uniform expectation commutes with a sum over an arbitrary finite set. -/
lemma uniformExpectation_finset_sum {I : Type*} [DecidableEq I]
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (s : Finset I) (X : I → Omega → ℝ) :
    Concentration.uniformExpectation (fun omega ↦ ∑ i ∈ s, X i omega) =
      ∑ i ∈ s, Concentration.uniformExpectation (X i) := by
  unfold Concentration.uniformExpectation
  rw [Finset.sum_comm, Finset.sum_div]

/-- Expanding the square of a finite sum separates its diagonal and ordered
off-diagonal terms. -/
lemma sum_sq_eq_sum_sq_add_offDiag {I : Type*} [DecidableEq I]
    (s : Finset I) (x : I → ℝ) :
    (∑ i ∈ s, x i) ^ 2 =
      (∑ i ∈ s, x i ^ 2) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, x i * x j := by
  calc
    (∑ i ∈ s, x i) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, x i * x j := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ i ∈ s, (x i ^ 2 + ∑ j ∈ s.erase i, x i * x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_erase_add _ _ hi]
      ring
    _ = (∑ i ∈ s, x i ^ 2) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, x i * x j := by
      rw [Finset.sum_add_distrib]

/-- The ordered off-diagonal sum in one bucket is deterministic. -/
lemma sum_offDiag_fiber_productSignedSliceValue
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    (S : ProductSignedSlicePoint P plus minus) (k : κ) :
    ∑ i ∈ P.fiber k, ∑ j ∈ (P.fiber k).erase i,
        productSignedSliceValue P S i * productSignedSliceValue P S j =
      ((plus k : ℝ) - minus k) ^ 2 - (plus k + minus k : ℕ) := by
  have h := sum_sq_eq_sum_sq_add_offDiag (P.fiber k)
    (productSignedSliceValue P S)
  rw [sum_fiber_productSignedSliceValue P plus minus S k,
    sum_sq_fiber_productSignedSliceValue P plus minus S k] at h
  linarith

/-- Exact same-bucket ordered-pair moment.  It is stated without division,
so it remains useful at small bucket sizes. -/
lemma card_mul_pred_mul_uniformExpectation_pair
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    (k : κ) {i j : α}
    (hi : i ∈ P.fiber k) (hj : j ∈ P.fiber k) (hij : i ≠ j) :
    ((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ) *
        Concentration.uniformExpectation
          (fun S : ProductSignedSlicePoint P plus minus ↦
            productSignedSliceValue P S i * productSignedSliceValue P S j) =
      ((plus k : ℝ) - minus k) ^ 2 - (plus k + minus k : ℕ) := by
  let mu : ℝ := Concentration.uniformExpectation
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S i * productSignedSliceValue P S j)
  have hpoint : ∀ S : ProductSignedSlicePoint P plus minus,
      (∑ u ∈ P.fiber k, ∑ v ∈ (P.fiber k).erase u,
          productSignedSliceValue P S u * productSignedSliceValue P S v) =
        ((plus k : ℝ) - minus k) ^ 2 - (plus k + minus k : ℕ) :=
    fun S ↦ sum_offDiag_fiber_productSignedSliceValue P plus minus S k
  have hexpect : Concentration.uniformExpectation
      (fun S : ProductSignedSlicePoint P plus minus ↦
        ∑ u ∈ P.fiber k, ∑ v ∈ (P.fiber k).erase u,
          productSignedSliceValue P S u * productSignedSliceValue P S v) =
      ((plus k : ℝ) - minus k) ^ 2 - (plus k + minus k : ℕ) := by
    calc
      Concentration.uniformExpectation
          (fun S : ProductSignedSlicePoint P plus minus ↦
            ∑ u ∈ P.fiber k, ∑ v ∈ (P.fiber k).erase u,
              productSignedSliceValue P S u * productSignedSliceValue P S v) =
          Concentration.uniformExpectation (fun _ ↦
            ((plus k : ℝ) - minus k) ^ 2 - (plus k + minus k : ℕ)) :=
        congrArg Concentration.uniformExpectation (funext hpoint)
      _ = ((plus k : ℝ) - minus k) ^ 2 -
          (plus k + minus k : ℕ) := Concentration.uniformExpectation_const _
  rw [uniformExpectation_finset_sum] at hexpect
  simp_rw [uniformExpectation_finset_sum] at hexpect
  have heach : ∀ u ∈ P.fiber k, ∀ v ∈ (P.fiber k).erase u,
      Concentration.uniformExpectation
          (fun S : ProductSignedSlicePoint P plus minus ↦
            productSignedSliceValue P S u * productSignedSliceValue P S v) = mu := by
    intro u hu v hv
    apply uniformExpectation_productSignedSliceValue_mul_eq_of_sameBucket
      P plus minus k hu (Finset.mem_of_mem_erase hv) hi hj
      (Finset.ne_of_mem_erase hv).symm hij
  have hrewrite :
      (∑ u ∈ P.fiber k, ∑ v ∈ (P.fiber k).erase u,
        Concentration.uniformExpectation
          (fun S : ProductSignedSlicePoint P plus minus ↦
            productSignedSliceValue P S u * productSignedSliceValue P S v)) =
        ∑ u ∈ P.fiber k, ∑ v ∈ (P.fiber k).erase u, mu := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    exact heach u hu v hv
  rw [hrewrite] at hexpect
  have hcard : ∀ u ∈ P.fiber k,
      ((P.fiber k).erase u).card = (P.fiber k).card - 1 := by
    intro u hu
    rw [Finset.card_erase_of_mem hu]
  have hsum : (∑ u ∈ P.fiber k,
      ∑ _v ∈ (P.fiber k).erase u, mu) =
      ((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ) * mu := by
    calc
      (∑ u ∈ P.fiber k, ∑ _v ∈ (P.fiber k).erase u, mu) =
          ∑ u ∈ P.fiber k, (((P.fiber k).erase u).card : ℝ) * mu := by
        apply Finset.sum_congr rfl
        intro u hu
        simp
      _ = ∑ _u ∈ P.fiber k,
          (((P.fiber k).card - 1 : ℕ) : ℝ) * mu := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hcard u hu]
      _ = ((P.fiber k).card : ℝ) *
          ((P.fiber k).card - 1 : ℕ) * mu := by
        simp
        ring
  rw [hsum] at hexpect
  simpa only [mu] using hexpect

/-- Squared-coordinate moments are equal within a bucket. -/
lemma uniformExpectation_productSignedSliceValue_sq_eq_of_sameBucket
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    {i u : α} (hiu : P.bucket i = P.bucket u) :
    Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S i ^ 2) =
      Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S u ^ 2) := by
  let ρ : Equiv.Perm α := Equiv.swap i u
  have hP : ∀ k, (P.fiber k).map ρ.toEmbedding = P.fiber k :=
    bucketSwap_preserves_fibers P hiu
  let E := productSignedSlicePermEquiv P plus minus ρ hP
  have heq := Fintype.expect_equiv E
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S i ^ 2)
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S u ^ 2) (by
      intro S
      have hv := productSignedSliceValue_productSignedSlicePermEquiv
        P plus minus ρ hP S i
      dsimp only [ρ] at hv
      simpa using congrArg (fun x : ℝ ↦ x ^ 2) hv.symm)
  simpa [Concentration.uniformExpectation,
    Fintype.expect_eq_sum_div_card] using heq

/-- Composing bucket-preserving permutations preserves every bucket. -/
lemma bucketPerm_trans_preserves_fibers [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (rho sigma : Equiv.Perm α)
    (hrho : ∀ k, (P.fiber k).map rho.toEmbedding = P.fiber k)
    (hsigma : ∀ k, (P.fiber k).map sigma.toEmbedding = P.fiber k)
    (k : κ) :
    (P.fiber k).map (rho.trans sigma).toEmbedding = P.fiber k := by
  calc
    (P.fiber k).map (rho.trans sigma).toEmbedding =
        ((P.fiber k).map rho.toEmbedding).map sigma.toEmbedding := by
      rw [Finset.map_map]
      rfl
    _ = P.fiber k := by rw [hrho k, hsigma k]

/-- Mixed moments are constant on a product of two distinct buckets. -/
lemma uniformExpectation_productSignedSliceValue_mul_eq_of_buckets
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    {k h : κ} (hkh : k ≠ h) {i u j v : α}
    (hi : i ∈ P.fiber k) (hu : u ∈ P.fiber k)
    (hj : j ∈ P.fiber h) (hv : v ∈ P.fiber h) :
    Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S i * productSignedSliceValue P S j) =
      Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S u * productSignedSliceValue P S v) := by
  have hbi : P.bucket i = k := (P.mem_fiber k i).mp hi
  have hbu : P.bucket u = k := (P.mem_fiber k u).mp hu
  have hbj : P.bucket j = h := (P.mem_fiber h j).mp hj
  have hbv : P.bucket v = h := (P.mem_fiber h v).mp hv
  have hiu : P.bucket i = P.bucket u := hbi.trans hbu.symm
  have hjv : P.bucket j = P.bucket v := hbj.trans hbv.symm
  have huj : u ≠ j := fun e ↦ hkh (hbu.symm.trans (e ▸ hbj))
  have huv : u ≠ v := fun e ↦ hkh (hbu.symm.trans (e ▸ hbv))
  have hji : j ≠ i := fun e ↦ hkh ((e ▸ hbi).symm.trans hbj)
  have hju : j ≠ u := huj.symm
  let rho1 : Equiv.Perm α := Equiv.swap i u
  let rho2 : Equiv.Perm α := Equiv.swap j v
  let rho : Equiv.Perm α := rho1.trans rho2
  have hP1 : ∀ q, (P.fiber q).map rho1.toEmbedding = P.fiber q :=
    bucketSwap_preserves_fibers P hiu
  have hP2 : ∀ q, (P.fiber q).map rho2.toEmbedding = P.fiber q :=
    bucketSwap_preserves_fibers P hjv
  have hP : ∀ q, (P.fiber q).map rho.toEmbedding = P.fiber q :=
    bucketPerm_trans_preserves_fibers P rho1 rho2 hP1 hP2
  have hrhoi : rho i = u := by
    dsimp only [rho, rho1, rho2]
    rw [Equiv.trans_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne huj huv]
  have hrhoj : rho j = v := by
    dsimp only [rho, rho1, rho2]
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hji hju,
      Equiv.swap_apply_left]
  let E := productSignedSlicePermEquiv P plus minus rho hP
  have heq := Fintype.expect_equiv E
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S i * productSignedSliceValue P S j)
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S u * productSignedSliceValue P S v) (by
      intro S
      have hvi := productSignedSliceValue_productSignedSlicePermEquiv
        P plus minus rho hP S i
      have hvj := productSignedSliceValue_productSignedSlicePermEquiv
        P plus minus rho hP S j
      calc
        productSignedSliceValue P S i * productSignedSliceValue P S j =
            productSignedSliceValue P (E S) (rho i) *
              productSignedSliceValue P (E S) (rho j) :=
          congrArg₂ (fun x y : ℝ ↦ x * y) hvi.symm hvj.symm
        _ = productSignedSliceValue P (E S) u *
              productSignedSliceValue P (E S) v := by rw [hrhoi, hrhoj])
  simpa [Concentration.uniformExpectation,
    Fintype.expect_eq_sum_div_card] using heq

lemma concentration_uniformExpectation_const_mul
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (c : ℝ) (X : Omega → ℝ) :
    Concentration.uniformExpectation (fun omega ↦ c * X omega) =
      c * Concentration.uniformExpectation X := by
  unfold Concentration.uniformExpectation
  rw [← Finset.mul_sum, mul_div_assoc]

/-- The balanced linear coefficient condition kills the entire signed-slice
linear expectation, for every choice of signed counts. -/
lemma uniformExpectation_signedSliceLinear_eq_zero
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    (f : α → ℝ) (hbal : ∀ k, ∑ i ∈ P.fiber k, f i = 0) :
    Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          ∑ i, f i * productSignedSliceValue P S i) = 0 := by
  rw [uniformExpectation_finset_sum]
  simp_rw [concentration_uniformExpectation_const_mul]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset α) P.bucket
    (fun i ↦ f i * Concentration.uniformExpectation
      (fun S : ProductSignedSlicePoint P plus minus ↦
        productSignedSliceValue P S i))]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hne : (P.fiber k).Nonempty
  · obtain ⟨i, hi⟩ := hne
    change (∑ j ∈ P.fiber k,
      f j * Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S j)) = 0
    have hfactor : ∀ j ∈ P.fiber k,
        Concentration.uniformExpectation
            (fun S : ProductSignedSlicePoint P plus minus ↦
              productSignedSliceValue P S j) =
          Concentration.uniformExpectation
            (fun S : ProductSignedSlicePoint P plus minus ↦
              productSignedSliceValue P S i) := by
      intro j hj
      exact uniformExpectation_productSignedSliceValue_eq_of_sameBucket
        P plus minus (((P.mem_fiber k j).mp hj).trans
          ((P.mem_fiber k i).mp hi).symm)
    calc
      ∑ j ∈ P.fiber k,
          f j * Concentration.uniformExpectation
            (fun S : ProductSignedSlicePoint P plus minus ↦
              productSignedSliceValue P S j) =
          ∑ j ∈ P.fiber k,
            f j * Concentration.uniformExpectation
              (fun S : ProductSignedSlicePoint P plus minus ↦
                productSignedSliceValue P S i) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hfactor j hj]
      _ = (∑ j ∈ P.fiber k, f j) *
          Concentration.uniformExpectation
            (fun S : ProductSignedSlicePoint P plus minus ↦
              productSignedSliceValue P S i) := by
        rw [Finset.sum_mul]
      _ = 0 := by rw [hbal k, zero_mul]
  · change (∑ j ∈ P.fiber k,
      f j * Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S j)) = 0
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Exact diagonal second moment, again in division-free form. -/
lemma card_mul_uniformExpectation_sq
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    (k : κ) {i : α} (hi : i ∈ P.fiber k) :
    ((P.fiber k).card : ℝ) *
        Concentration.uniformExpectation
          (fun S : ProductSignedSlicePoint P plus minus ↦
            productSignedSliceValue P S i ^ 2) =
      (plus k + minus k : ℕ) := by
  let d : ℝ := Concentration.uniformExpectation
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S i ^ 2)
  have hpoint : ∀ S : ProductSignedSlicePoint P plus minus,
      (∑ u ∈ P.fiber k, productSignedSliceValue P S u ^ 2) =
        (plus k + minus k : ℕ) :=
    fun S ↦ sum_sq_fiber_productSignedSliceValue P plus minus S k
  have hexpect : Concentration.uniformExpectation
      (fun S : ProductSignedSlicePoint P plus minus ↦
        ∑ u ∈ P.fiber k, productSignedSliceValue P S u ^ 2) =
      (plus k + minus k : ℕ) := by
    calc
      Concentration.uniformExpectation
          (fun S : ProductSignedSlicePoint P plus minus ↦
            ∑ u ∈ P.fiber k, productSignedSliceValue P S u ^ 2) =
          Concentration.uniformExpectation (fun _ ↦
            (plus k + minus k : ℕ)) :=
        congrArg Concentration.uniformExpectation (funext hpoint)
      _ = (plus k + minus k : ℕ) :=
        Concentration.uniformExpectation_const _
  rw [uniformExpectation_finset_sum] at hexpect
  have heach : ∀ u ∈ P.fiber k,
      Concentration.uniformExpectation
          (fun S : ProductSignedSlicePoint P plus minus ↦
            productSignedSliceValue P S u ^ 2) = d := by
    intro u hu
    exact uniformExpectation_productSignedSliceValue_sq_eq_of_sameBucket
      P plus minus (((P.mem_fiber k u).mp hu).trans
        ((P.mem_fiber k i).mp hi).symm)
  have hrewrite :
      (∑ u ∈ P.fiber k,
        Concentration.uniformExpectation
          (fun S : ProductSignedSlicePoint P plus minus ↦
            productSignedSliceValue P S u ^ 2)) =
        ∑ _u ∈ P.fiber k, d := by
    apply Finset.sum_congr rfl
    intro u hu
    exact heach u hu
  rw [hrewrite] at hexpect
  have hsum : (∑ _u ∈ P.fiber k, d) = ((P.fiber k).card : ℝ) * d := by
    simp
  rw [hsum] at hexpect
  simpa only [d] using hexpect

/-- If two signed slices expose the same total number of coordinates in a
nonempty bucket, their coordinate-square expectations agree. -/
lemma uniformExpectation_sq_eq_of_same_support
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (plus minus plus' minus' : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    [Nonempty (ProductSignedSlicePoint P plus' minus')]
    (k : κ) {i : α} (hi : i ∈ P.fiber k)
    (hsupport : plus k + minus k = plus' k + minus' k) :
    Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus minus ↦
          productSignedSliceValue P S i ^ 2) =
      Concentration.uniformExpectation
        (fun S : ProductSignedSlicePoint P plus' minus' ↦
          productSignedSliceValue P S i ^ 2) := by
  have hcard : 0 < ((P.fiber k).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
  have hleft := card_mul_uniformExpectation_sq P plus minus k hi
  have hright := card_mul_uniformExpectation_sq P plus' minus' k hi
  rw [hsupport] at hleft
  exact (mul_left_cancel₀ hcard.ne' (hleft.trans hright.symm))

/-- Uniform second-moment matrix of a product signed slice. -/
noncomputable def signedSliceSecondMoment
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    (i j : α) : ℝ :=
  Concentration.uniformExpectation
    (fun S : ProductSignedSlicePoint P plus minus ↦
      productSignedSliceValue P S i * productSignedSliceValue P S j)

/-- Under balanced linear coefficients, the mean of the restricted
linear--quadratic polynomial is exactly the contraction of `F` against the
signed-slice second-moment matrix. -/
lemma uniformExpectation_signedSliceQuadratic_eq_secondMoments
    {K : ℕ} (P : BucketPartition α (Fin K))
    (plus minus : Fin K → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    (f : α → ℝ) (F : α → α → ℝ)
    (hf : ∀ k, ∑ i ∈ P.fiber k, f i = 0) :
    Concentration.uniformExpectation (signedSliceQuadratic P plus minus f F) =
      ∑ i, ∑ j, F i j * signedSliceSecondMoment P plus minus i j := by
  unfold signedSliceQuadratic
  rw [Concentration.uniformExpectation_add,
    uniformExpectation_signedSliceLinear_eq_zero P plus minus f hf,
    zero_add]
  rw [uniformExpectation_finset_sum]
  simp_rw [uniformExpectation_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (fun S : ProductSignedSlicePoint P plus minus ↦
      F i j * productSignedSliceValue P S i * productSignedSliceValue P S j) =
      (fun S ↦ F i j * (productSignedSliceValue P S i *
        productSignedSliceValue P S j)) by
      funext S
      ring]
  rw [concentration_uniformExpectation_const_mul]
  rfl

/-- A matrix block joining two distinct buckets has zero contraction with
the signed-slice second moments when its row sums vanish. -/
lemma sum_crossBucket_secondMoment_eq_zero
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (plus minus : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    (F : α → α → ℝ)
    (hrow : ∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0)
    {k h : κ} (hkh : k ≠ h) :
    ∑ i ∈ P.fiber k, ∑ j ∈ P.fiber h,
        F i j * signedSliceSecondMoment P plus minus i j = 0 := by
  by_cases hkne : (P.fiber k).Nonempty
  · by_cases hhne : (P.fiber h).Nonempty
    · obtain ⟨i0, hi0⟩ := hkne
      obtain ⟨j0, hj0⟩ := hhne
      let mu : ℝ := signedSliceSecondMoment P plus minus i0 j0
      have hmoment : ∀ i ∈ P.fiber k, ∀ j ∈ P.fiber h,
          signedSliceSecondMoment P plus minus i j = mu := by
        intro i hi j hj
        simpa only [signedSliceSecondMoment, mu] using
          uniformExpectation_productSignedSliceValue_mul_eq_of_buckets
            P plus minus hkh hi hi0 hj hj0
      calc
        ∑ i ∈ P.fiber k, ∑ j ∈ P.fiber h,
            F i j * signedSliceSecondMoment P plus minus i j =
            ∑ i ∈ P.fiber k, ∑ j ∈ P.fiber h, F i j * mu := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hmoment i hi j hj]
        _ = ∑ i ∈ P.fiber k, (∑ j ∈ P.fiber h, F i j) * mu := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
        _ = 0 := by simp [hrow]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hhne]
      simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hkne]
    simp

/-- Inside one bucket, two signed laws with the same exposed support differ
only through their common off-diagonal moment. -/
lemma sum_sameBucket_secondMoment_sub
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (plus minus plus' minus' : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    [Nonempty (ProductSignedSlicePoint P plus' minus')]
    (F : α → α → ℝ)
    (hrow : ∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0)
    (k : κ) {i0 j0 : α}
    (hi0 : i0 ∈ P.fiber k) (hj0 : j0 ∈ P.fiber k) (hij0 : i0 ≠ j0)
    (hsupport : plus k + minus k = plus' k + minus' k) :
    ∑ i ∈ P.fiber k, ∑ j ∈ P.fiber k, F i j *
        (signedSliceSecondMoment P plus minus i j -
          signedSliceSecondMoment P plus' minus' i j) =
      -(signedSliceSecondMoment P plus minus i0 j0 -
          signedSliceSecondMoment P plus' minus' i0 j0) *
        ∑ i ∈ P.fiber k, F i i := by
  let d : ℝ := signedSliceSecondMoment P plus minus i0 j0 -
    signedSliceSecondMoment P plus' minus' i0 j0
  have hdiag : ∀ i ∈ P.fiber k,
      signedSliceSecondMoment P plus minus i i =
        signedSliceSecondMoment P plus' minus' i i := by
    intro i hi
    have hsquare := uniformExpectation_sq_eq_of_same_support
      P plus minus plus' minus' k hi hsupport
    simpa only [signedSliceSecondMoment, pow_two] using hsquare
  have hoff : ∀ i ∈ P.fiber k, ∀ j ∈ P.fiber k, i ≠ j →
      signedSliceSecondMoment P plus minus i j -
        signedSliceSecondMoment P plus' minus' i j = d := by
    intro i hi j hj hij
    have hleft :=
      uniformExpectation_productSignedSliceValue_mul_eq_of_sameBucket
        P plus minus k hi hj hi0 hj0 hij hij0
    have hright :=
      uniformExpectation_productSignedSliceValue_mul_eq_of_sameBucket
        P plus' minus' k hi hj hi0 hj0 hij hij0
    dsimp only [signedSliceSecondMoment, d]
    rw [hleft, hright]
  have hinner : ∀ i ∈ P.fiber k,
      (∑ j ∈ P.fiber k, F i j *
        (signedSliceSecondMoment P plus minus i j -
          signedSliceSecondMoment P plus' minus' i j)) = -F i i * d := by
    intro i hi
    have hrowi := hrow k k i hi
    have herase : (∑ j ∈ (P.fiber k).erase i, F i j) = -F i i := by
      rw [← Finset.sum_erase_add _ _ hi] at hrowi
      linarith
    calc
      (∑ j ∈ P.fiber k, F i j *
          (signedSliceSecondMoment P plus minus i j -
            signedSliceSecondMoment P plus' minus' i j)) =
          (∑ j ∈ (P.fiber k).erase i, F i j *
            (signedSliceSecondMoment P plus minus i j -
              signedSliceSecondMoment P plus' minus' i j)) +
            F i i * (signedSliceSecondMoment P plus minus i i -
              signedSliceSecondMoment P plus' minus' i i) := by
        rw [Finset.sum_erase_add _ _ hi]
      _ = ∑ j ∈ (P.fiber k).erase i, F i j * d := by
        rw [hdiag i hi, sub_self, mul_zero, add_zero]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hoff i hi j (Finset.mem_of_mem_erase hj)
          (Finset.ne_of_mem_erase hj).symm]
      _ = (∑ j ∈ (P.fiber k).erase i, F i j) * d := by
        rw [Finset.sum_mul]
      _ = -F i i * d := by rw [herase]
  calc
    ∑ i ∈ P.fiber k, ∑ j ∈ P.fiber k, F i j *
        (signedSliceSecondMoment P plus minus i j -
          signedSliceSecondMoment P plus' minus' i j) =
        ∑ i ∈ P.fiber k, -F i i * d := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hinner i hi
    _ = -d * ∑ i ∈ P.fiber k, F i i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = -(signedSliceSecondMoment P plus minus i0 j0 -
          signedSliceSecondMoment P plus' minus' i0 j0) *
        ∑ i ∈ P.fiber k, F i i := by rfl

/-- Closed form of the preceding block identity. -/
lemma sum_sameBucket_secondMoment_sub_eq
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (plus minus plus' minus' : κ → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    [Nonempty (ProductSignedSlicePoint P plus' minus')]
    (F : α → α → ℝ)
    (hrow : ∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0)
    (k : κ) (hcard : 2 ≤ (P.fiber k).card)
    (hsupport : plus k + minus k = plus' k + minus' k) :
    ∑ i ∈ P.fiber k, ∑ j ∈ P.fiber k, F i j *
        (signedSliceSecondMoment P plus minus i j -
          signedSliceSecondMoment P plus' minus' i j) =
      -((((plus k : ℝ) - minus k) ^ 2 -
            ((plus' k : ℝ) - minus' k) ^ 2) /
          (((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ))) *
        ∑ i ∈ P.fiber k, F i i := by
  have hne : (P.fiber k).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i0, hi0⟩ := hne
  have heraseCard : 0 < ((P.fiber k).erase i0).card := by
    rw [Finset.card_erase_of_mem hi0]
    omega
  obtain ⟨j0, hj0erase⟩ := Finset.card_pos.mp heraseCard
  have hj0 : j0 ∈ P.fiber k := Finset.mem_of_mem_erase hj0erase
  have hij0 : i0 ≠ j0 := (Finset.ne_of_mem_erase hj0erase).symm
  have hblock := sum_sameBucket_secondMoment_sub P plus minus plus' minus'
    F hrow k hi0 hj0 hij0 hsupport
  let d : ℝ := signedSliceSecondMoment P plus minus i0 j0 -
    signedSliceSecondMoment P plus' minus' i0 j0
  let D : ℝ := ((P.fiber k).card : ℝ) *
    ((P.fiber k).card - 1 : ℕ)
  have hDpos : 0 < D := by
    dsimp only [D]
    have hcardPos : (0 : ℝ) < (P.fiber k).card := by
      exact_mod_cast (show 0 < (P.fiber k).card by omega)
    have hpredPos : (0 : ℝ) < ((P.fiber k).card - 1 : ℕ) := by
      exact_mod_cast (show 0 < (P.fiber k).card - 1 by omega)
    exact mul_pos hcardPos hpredPos
  have hleft := card_mul_pred_mul_uniformExpectation_pair
    P plus minus k hi0 hj0 hij0
  have hright := card_mul_pred_mul_uniformExpectation_pair
    P plus' minus' k hi0 hj0 hij0
  have hsupportR : ((plus k + minus k : ℕ) : ℝ) =
      (plus' k + minus' k : ℕ) := by exact_mod_cast hsupport
  have hmul : D * d = ((plus k : ℝ) - minus k) ^ 2 -
      ((plus' k : ℝ) - minus' k) ^ 2 := by
    dsimp only [D, d, signedSliceSecondMoment]
    calc
      ((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ) *
          (Concentration.uniformExpectation
              (fun S : ProductSignedSlicePoint P plus minus ↦
                productSignedSliceValue P S i0 * productSignedSliceValue P S j0) -
            Concentration.uniformExpectation
              (fun S : ProductSignedSlicePoint P plus' minus' ↦
                productSignedSliceValue P S i0 * productSignedSliceValue P S j0)) =
          (((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ) *
            Concentration.uniformExpectation
              (fun S : ProductSignedSlicePoint P plus minus ↦
                productSignedSliceValue P S i0 * productSignedSliceValue P S j0)) -
          (((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ) *
            Concentration.uniformExpectation
              (fun S : ProductSignedSlicePoint P plus' minus' ↦
                productSignedSliceValue P S i0 * productSignedSliceValue P S j0)) := by
        ring
      _ = (((plus k : ℝ) - minus k) ^ 2 -
            (plus k + minus k : ℕ)) -
          (((plus' k : ℝ) - minus' k) ^ 2 -
            (plus' k + minus' k : ℕ)) := by rw [hleft, hright]
      _ = ((plus k : ℝ) - minus k) ^ 2 -
          ((plus' k : ℝ) - minus' k) ^ 2 := by rw [hsupportR]; ring
  have hd : d = ((((plus k : ℝ) - minus k) ^ 2 -
      ((plus' k : ℝ) - minus' k) ^ 2) / D) := by
    apply (eq_div_iff hDpos.ne').2
    simpa [mul_comm] using hmul
  rw [hblock, show signedSliceSecondMoment P plus minus i0 j0 -
      signedSliceSecondMoment P plus' minus' i0 j0 = d by rfl, hd]

/-- Reindex a double sum by the two buckets containing its coordinates. -/
lemma sum_eq_sum_fiber_blocks [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ) (G : α → α → ℝ) :
    (∑ i, ∑ j, G i j) =
      ∑ k, ∑ h, ∑ i ∈ P.fiber k, ∑ j ∈ P.fiber h, G i j := by
  calc
    (∑ i, ∑ j, G i j) =
        ∑ k, ∑ i ∈ P.fiber k, ∑ j, G i j := by
      rw [← Finset.sum_fiberwise (Finset.univ : Finset α) P.bucket
        (fun i ↦ ∑ j, G i j)]
      rfl
    _ = ∑ k, ∑ i ∈ P.fiber k,
        ∑ h, ∑ j ∈ P.fiber h, G i j := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_fiberwise (Finset.univ : Finset α) P.bucket
        (fun j ↦ G i j)]
      rfl
    _ = ∑ k, ∑ h, ∑ i ∈ P.fiber k,
        ∑ j ∈ P.fiber h, G i j := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]

/-- Exact change in the mean of a balanced linear--quadratic polynomial
between two product signed-slice laws with the same exposed support. -/
lemma uniformExpectation_signedSliceQuadratic_sub_eq
    {K : ℕ} (P : BucketPartition α (Fin K))
    (plus minus plus' minus' : Fin K → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    [Nonempty (ProductSignedSlicePoint P plus' minus')]
    (f : α → ℝ) (F : α → α → ℝ)
    (hf : ∀ k, ∑ i ∈ P.fiber k, f i = 0)
    (hrow : ∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0)
    (hcard : ∀ k, 2 ≤ (P.fiber k).card)
    (hsupport : ∀ k, plus k + minus k = plus' k + minus' k) :
    Concentration.uniformExpectation
          (signedSliceQuadratic P plus minus f F) -
        Concentration.uniformExpectation
          (signedSliceQuadratic P plus' minus' f F) =
      ∑ k, -((((plus k : ℝ) - minus k) ^ 2 -
              ((plus' k : ℝ) - minus' k) ^ 2) /
            (((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ))) *
          ∑ i ∈ P.fiber k, F i i := by
  rw [uniformExpectation_signedSliceQuadratic_eq_secondMoments P plus minus f F hf,
    uniformExpectation_signedSliceQuadratic_eq_secondMoments P plus' minus' f F hf]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have hfactor :
      (∑ i, ∑ j,
          (F i j * signedSliceSecondMoment P plus minus i j -
            F i j * signedSliceSecondMoment P plus' minus' i j)) =
        ∑ i, ∑ j, F i j *
          (signedSliceSecondMoment P plus minus i j -
            signedSliceSecondMoment P plus' minus' i j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfactor, sum_eq_sum_fiber_blocks (α := α) (κ := Fin K) P
    (fun i j ↦ F i j *
      (signedSliceSecondMoment P plus minus i j -
        signedSliceSecondMoment P plus' minus' i j))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · exact sum_sameBucket_secondMoment_sub_eq P plus minus plus' minus'
      F hrow k (hcard k) (hsupport k)
  · intro h hh hhk
    have hkh : k ≠ h := fun hEq ↦ hhk hEq.symm
    calc
      ∑ i ∈ P.fiber k, ∑ j ∈ P.fiber h, F i j *
          (signedSliceSecondMoment P plus minus i j -
            signedSliceSecondMoment P plus' minus' i j) =
          (∑ i ∈ P.fiber k, ∑ j ∈ P.fiber h,
            F i j * signedSliceSecondMoment P plus minus i j) -
          (∑ i ∈ P.fiber k, ∑ j ∈ P.fiber h,
            F i j * signedSliceSecondMoment P plus' minus' i j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by
        rw [sum_crossBucket_secondMoment_eq_zero P plus minus F hrow hkh,
          sum_crossBucket_secondMoment_eq_zero P plus' minus' F hrow hkh,
          sub_self]
  · simp

/-- A uniform bound for the preceding exact mean formula.  If every bucket
imbalance is at most `W`, only the reciprocal bucket size remains. -/
lemma abs_uniformExpectation_signedSliceQuadratic_sub_le
    {K : ℕ} (P : BucketPartition α (Fin K))
    (plus minus plus' minus' : Fin K → ℕ)
    [Nonempty (ProductSignedSlicePoint P plus minus)]
    [Nonempty (ProductSignedSlicePoint P plus' minus')]
    (f : α → ℝ) (F : α → α → ℝ) (A W : ℝ)
    (hf : ∀ k, ∑ i ∈ P.fiber k, f i = 0)
    (hrow : ∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0)
    (hcard : ∀ k, 2 ≤ (P.fiber k).card)
    (hsupport : ∀ k, plus k + minus k = plus' k + minus' k)
    (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hdiag : ∀ i, |F i i| ≤ A)
    (himb : ∀ k, |(plus k : ℝ) - minus k| ≤ W)
    (himb' : ∀ k, |(plus' k : ℝ) - minus' k| ≤ W) :
    |Concentration.uniformExpectation
          (signedSliceQuadratic P plus minus f F) -
        Concentration.uniformExpectation
          (signedSliceQuadratic P plus' minus' f F)| ≤
      ∑ k, 2 * W ^ 2 * A / (((P.fiber k).card - 1 : ℕ) : ℝ) := by
  rw [uniformExpectation_signedSliceQuadratic_sub_eq P plus minus plus' minus'
    f F hf hrow hcard hsupport]
  calc
    |∑ k, -((((plus k : ℝ) - minus k) ^ 2 -
            ((plus' k : ℝ) - minus' k) ^ 2) /
          (((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ))) *
        ∑ i ∈ P.fiber k, F i i| ≤
        ∑ k, |-((((plus k : ℝ) - minus k) ^ 2 -
            ((plus' k : ℝ) - minus' k) ^ 2) /
          (((P.fiber k).card : ℝ) * ((P.fiber k).card - 1 : ℕ))) *
        ∑ i ∈ P.fiber k, F i i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, 2 * W ^ 2 * A /
        (((P.fiber k).card - 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      let N : ℝ := (P.fiber k).card
      let D : ℝ := ((P.fiber k).card - 1 : ℕ)
      have hN : 0 < N := by
        dsimp only [N]
        have hkcard := hcard k
        exact_mod_cast (show 0 < (P.fiber k).card by omega)
      have hD : 0 < D := by
        dsimp only [D]
        have hkcard := hcard k
        exact_mod_cast (show 0 < (P.fiber k).card - 1 by omega)
      have hsq : |((plus k : ℝ) - minus k) ^ 2 -
          ((plus' k : ℝ) - minus' k) ^ 2| ≤ 2 * W ^ 2 := by
        calc
          |((plus k : ℝ) - minus k) ^ 2 -
              ((plus' k : ℝ) - minus' k) ^ 2| ≤
              |((plus k : ℝ) - minus k) ^ 2| +
                |((plus' k : ℝ) - minus' k) ^ 2| := abs_sub _ _
          _ = |(plus k : ℝ) - minus k| ^ 2 +
                |(plus' k : ℝ) - minus' k| ^ 2 := by
              rw [abs_pow, abs_pow]
          _ ≤ 2 * W ^ 2 := by
              have h1 : |(plus k : ℝ) - minus k| ^ 2 ≤ W ^ 2 :=
                (sq_le_sq₀ (abs_nonneg _) hW).2 (himb k)
              have h2 : |(plus' k : ℝ) - minus' k| ^ 2 ≤ W ^ 2 :=
                (sq_le_sq₀ (abs_nonneg _) hW).2 (himb' k)
              linarith
      have htrace : |∑ i ∈ P.fiber k, F i i| ≤ N * A := by
        calc
          |∑ i ∈ P.fiber k, F i i| ≤
              ∑ i ∈ P.fiber k, |F i i| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ P.fiber k, A := by
            exact Finset.sum_le_sum fun i hi ↦ hdiag i
          _ = N * A := by simp [N]
      rw [abs_mul, abs_neg, abs_div,
        abs_of_pos (mul_pos hN hD)]
      change
        |((plus k : ℝ) - minus k) ^ 2 -
            ((plus' k : ℝ) - minus' k) ^ 2| / (N * D) *
            |∑ i ∈ P.fiber k, F i i| ≤
          2 * W ^ 2 * A / D
      calc
        |((plus k : ℝ) - minus k) ^ 2 -
            ((plus' k : ℝ) - minus' k) ^ 2| / (N * D) *
            |∑ i ∈ P.fiber k, F i i| ≤
            (2 * W ^ 2) / (N * D) * (N * A) := by
          gcongr
        _ = 2 * W ^ 2 * A / D := by field_simp

/-- In the source two-stage sampler, the imbalance remaining inside the
exceptional set is exactly the original slice imbalance. -/
lemma twoStageInner_imbalance_eq {κ : Type*}
    (bucketSize ell core : κ → ℕ) (k : κ)
    (hlow : core k ≤ ell k)
    (hhigh : ell k + core k ≤ bucketSize k) :
    (twoStageInnerSize ell core k : ℝ) -
        (twoStageExceptionalSize bucketSize core k -
          twoStageInnerSize ell core k : ℕ) =
      2 * (ell k : ℝ) - bucketSize k := by
  have hcore : 2 * core k ≤ bucketSize k := by omega
  have hinner : ell k - core k ≤ bucketSize k - 2 * core k := by omega
  simp only [twoStageInnerSize, twoStageExceptionalSize]
  rw [Nat.cast_sub hlow, Nat.cast_sub hinner, Nat.cast_sub hcore,
    Nat.cast_sub hlow]
  push_cast
  ring

/-- Near-balance of an original slice gives a twice-margin imbalance bound
for the signed exceptional slice used by the coupling. -/
lemma twoStageInner_imbalance_le {κ : Type*}
    (bucketSize ell core : κ → ℕ)
    (margin : ℝ) (hlow : ∀ k, core k ≤ ell k)
    (hhigh : ∀ k, ell k + core k ≤ bucketSize k)
    (hnear : ∀ k, |(ell k : ℝ) - (bucketSize k : ℝ) / 2| ≤ margin)
    (k : κ) :
    |(twoStageInnerSize ell core k : ℝ) -
        (twoStageExceptionalSize bucketSize core k -
          twoStageInnerSize ell core k : ℕ)| ≤ 2 * margin := by
  rw [show (twoStageInnerSize ell core k : ℝ) -
      (twoStageExceptionalSize bucketSize core k -
        twoStageInnerSize ell core k : ℕ) =
      2 * (ell k : ℝ) - bucketSize k by
    exact twoStageInner_imbalance_eq bucketSize ell core k
      (hlow k) (hhigh k)]
  calc
    |2 * (ell k : ℝ) - bucketSize k| =
        2 * |(ell k : ℝ) - (bucketSize k : ℝ) / 2| := by
      rw [← abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), ← abs_mul]
      congr 1
      ring
    _ ≤ 2 * margin := mul_le_mul_of_nonneg_left (hnear k) (by norm_num)

/-- Mean-gap estimate in the notation of the abstract two-stage sampler. -/
lemma abs_uniformExpectation_twoStageSignedQuadratic_sub_le
    {n K : ℕ} (P : BucketPartition (Fin n) (Fin K))
    (r a b : Fin K → ℕ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (A W : ℝ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hcard : ∀ k, 2 ≤ (P.fiber k).card)
    (hf : ∀ k, ∑ i ∈ P.fiber k, f i = 0)
    (hrow : ∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hdiag : ∀ i, |F i i| ≤ A)
    (himb : ∀ k, |(a k : ℝ) - (r k - a k : ℕ)| ≤ W)
    (himb' : ∀ k, |(b k : ℝ) - (r k - b k : ℕ)| ≤ W) :
    letI : Nonempty (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
      productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k) (fun k ↦ by
        have hak := ha k
        rw [Nat.add_sub_of_le hak]
        exact hr k)
    letI : Nonempty (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
      productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k) (fun k ↦ by
        have hbk := hb k
        rw [Nat.add_sub_of_le hbk]
        exact hr k)
    |Concentration.uniformExpectation
          (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) -
        Concentration.uniformExpectation
          (signedSliceQuadratic P b (fun k ↦ r k - b k) f F)| ≤
      ∑ k, 2 * W ^ 2 * A / (((P.fiber k).card - 1 : ℕ) : ℝ) := by
  letI : Nonempty (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
    productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k) (fun k ↦ by
      have hak := ha k
      rw [Nat.add_sub_of_le hak]
      exact hr k)
  letI : Nonempty (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
    productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k) (fun k ↦ by
      have hbk := hb k
      rw [Nat.add_sub_of_le hbk]
      exact hr k)
  apply abs_uniformExpectation_signedSliceQuadratic_sub_le
    P a (fun k ↦ r k - a k) b (fun k ↦ r k - b k)
      f F A W hf hrow hcard
  · intro k
    have hak := ha k
    have hbk := hb k
    omega
  · exact hA
  · exact hW
  · exact hdiag
  · exact himb
  · exact himb'

/-- The explicit deterministic mean-error term used in the source
specialization of KSSS Lemma 11.2. -/
noncomputable def ksssExposedMeanGap {n m : ℕ} (δ : ℝ)
    (P : BucketPartition (Fin n) (Fin m)) : ℝ :=
  ∑ k, 8 * ksssSliceMargin n δ ^ 2 /
    (((P.fiber k).card - 1 : ℕ) : ℝ)

/-- Near-balanced target slices and the KSSS coefficient cancellations
automatically supply the exposed-mean hypothesis of the asymmetric
two-stage coupling. -/
lemma ksss_exposedMeanGap_le {n m : ℕ}
    (δ : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (ell ell' : Fin m → ℕ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ)
    (hmargin0 : 0 ≤ ksssSliceMargin n δ)
    (hmargin : ∀ k, ksssSliceMargin n δ ≤
      ((P.fiber k).card : ℝ) / 2)
    (hcard : ∀ k, 2 ≤ (P.fiber k).card)
    (hell : IsNearBalanced δ P ell)
    (hell' : IsNearBalanced δ P ell')
    (hcoeff : HasKSSSBalancedCoefficients δ P f F) :
    let core : Fin m → ℕ := fun k ↦
      ksssCoreSize n δ (P.fiber k).card
    let bucketSize : Fin m → ℕ := fun k ↦ (P.fiber k).card
    let r := twoStageExceptionalSize bucketSize core
    let a := twoStageInnerSize ell core
    let b := twoStageInnerSize ell' core
    letI : Nonempty (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
      productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k) (fun k ↦ by
        have hw := ksssCoreSize_source_windows δ P ell ell'
          hmargin0 hmargin hell hell'
        have hc := twoStage_source_cardinality_data bucketSize ell ell' core
          hw.2.2.2.2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
        have hak := hc.2.1 k
        rw [Nat.add_sub_of_le hak]
        exact (hc.1 k))
    letI : Nonempty (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
      productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k) (fun k ↦ by
        have hw := ksssCoreSize_source_windows δ P ell ell'
          hmargin0 hmargin hell hell'
        have hc := twoStage_source_cardinality_data bucketSize ell ell' core
          hw.2.2.2.2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
        have hbk := hc.2.2.1 k
        rw [Nat.add_sub_of_le hbk]
        exact (hc.1 k))
    |Concentration.uniformExpectation
          (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) -
        Concentration.uniformExpectation
          (signedSliceQuadratic P b (fun k ↦ r k - b k) f F)| ≤
      ksssExposedMeanGap δ P := by
  dsimp only
  let core : Fin m → ℕ := fun k ↦ ksssCoreSize n δ (P.fiber k).card
  let bucketSize : Fin m → ℕ := fun k ↦ (P.fiber k).card
  let r := twoStageExceptionalSize bucketSize core
  let a := twoStageInnerSize ell core
  let b := twoStageInnerSize ell' core
  have hw := ksssCoreSize_source_windows δ P ell ell'
    hmargin0 hmargin hell hell'
  have hc := twoStage_source_cardinality_data bucketSize ell ell' core
    hw.2.2.2.2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
  letI : Nonempty (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
    productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k) (fun k ↦ by
      have hak := hc.2.1 k
      rw [Nat.add_sub_of_le hak]
      exact hc.1 k)
  letI : Nonempty (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
    productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k) (fun k ↦ by
      have hbk := hc.2.2.1 k
      rw [Nat.add_sub_of_le hbk]
      exact hc.1 k)
  have hmean := abs_uniformExpectation_twoStageSignedQuadratic_sub_le
    P r a b f F 1 (2 * ksssSliceMargin n δ)
      hc.1 hc.2.1 hc.2.2.1 hcard hcoeff.2.2.2.1
      hcoeff.2.2.2.2.1 (by norm_num)
      (mul_nonneg (by norm_num) hmargin0) (fun i ↦ hcoeff.2.2.1 i i)
      (twoStageInner_imbalance_le bucketSize ell core
        (ksssSliceMargin n δ) hw.1 hw.2.2.1 hell)
      (twoStageInner_imbalance_le bucketSize ell' core
        (ksssSliceMargin n δ) hw.2.1 hw.2.2.2.1 hell')
  refine hmean.trans ?_
  rw [ksssExposedMeanGap]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The cardinalities of all bucket fibers add to the ambient cardinality. -/
lemma sum_card_bucketPartition_fiber {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) :
    ∑ k, (P.fiber k).card = n := by
  simpa [BucketPartition.fiber] using
    (Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) P.bucket
      (fun _ ↦ (1 : ℕ)))

/-- A common lower bound on the predecessor of every bucket size converts
the exact exposed mean error into one scalar expression. -/
lemma ksssExposedMeanGap_le_of_pred_fiber_lower {n m : ℕ}
    (δ : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (D : ℝ) (hD : 0 < D)
    (hpred : ∀ k, D ≤ (((P.fiber k).card - 1 : ℕ) : ℝ)) :
    ksssExposedMeanGap δ P ≤
      (m : ℝ) * (8 * ksssSliceMargin n δ ^ 2 / D) := by
  rw [ksssExposedMeanGap]
  calc
    (∑ k, 8 * ksssSliceMargin n δ ^ 2 /
        (((P.fiber k).card - 1 : ℕ) : ℝ)) ≤
        ∑ _k : Fin m, 8 * ksssSliceMargin n δ ^ 2 / D := by
      apply Finset.sum_le_sum
      intro k hk
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (sq_nonneg _)) hD (hpred k)
    _ = (m : ℝ) * (8 * ksssSliceMargin n δ ^ 2 / D) := by simp

/-! ### Source-strength cross-row concentration -/

/-- Linear form whose difference on the two revealed sign vectors is one
coefficient of the shared quadratic cross term. -/
noncomputable def crossRowLinear {n : ℕ}
    (F : Fin n → Fin n → ℝ) (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (F i j + F j i) * x i

lemma quadraticCrossCoefficient_eq_crossRowLinear_sub {n : ℕ}
    (F : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) (j : Fin n) :
    quadraticCrossCoefficient F x y j =
      crossRowLinear F j x - crossRowLinear F j y := by
  unfold quadraticCrossCoefficient crossRowLinear
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The row and column block cancellations imply that every cross-row
linear coefficient vector is balanced on every bucket. -/
lemma sum_crossRowCoefficient_fiber_eq_zero {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K))
    (F : Fin n → Fin n → ℝ)
    (hrow : ∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0)
    (hcol : ∀ k h j, j ∈ P.fiber h → ∑ i ∈ P.fiber k, F i j = 0)
    (k : Fin K) (j : Fin n) :
    ∑ i ∈ P.fiber k, (F i j + F j i) = 0 := by
  rw [Finset.sum_add_distrib, hcol k (P.bucket j) j (P.mem_ownFiber j),
    hrow (P.bucket j) k j (P.mem_ownFiber j), zero_add]

lemma signedSliceQuadratic_zeroMatrix_eq_crossRowLinear {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (plus minus : Fin K → ℕ)
    (F : Fin n → Fin n → ℝ) (j : Fin n)
    (S : ProductSignedSlicePoint P plus minus) :
    signedSliceQuadratic P plus minus (fun i ↦ F i j + F j i)
        (fun _ _ ↦ 0) S =
      crossRowLinear F j (productSignedSliceValue P S) := by
  simp [signedSliceQuadratic, crossRowLinear]

/-- Each revealed-left cross row has the subgaussian tail obtained by the
extra application of KSSS Lemma 4.17 in the proof of Lemma 11.2. -/
theorem productTwoStageSignedLeft_crossRow_two_sided_probability
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (F : Fin n → Fin n → ℝ) (M t : ℝ)
    (hR : 0 < ∑ k : Fin K, r k) (hM : 0 < M) (ht : 0 ≤ t)
    (hF : ∀ i j, |F i j| ≤ M)
    (hrow : ∀ k h i, i ∈ P.fiber k → ∑ j ∈ P.fiber h, F i j = 0)
    (hcol : ∀ k h j, j ∈ P.fiber h → ∑ i ∈ P.fiber k, F i j = 0)
    (j : Fin n) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability
        (fun ω ↦ t ≤ |crossRowLinear F j
          (productSignedSliceValue P
            (productTwoStageSignedLeft P r a b h ω))|) ≤
      2 * Real.exp (-t ^ 2 /
        (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty
      (ProductSignedSlicePoint P a (fun k ↦ r k - a k)) :=
    productSignedSlicePoint_nonempty P a (fun k ↦ r k - a k)
      (fun k ↦ by rw [Nat.add_sub_of_le (ha k)]; exact hr k)
  let g : Fin n → ℝ := fun i ↦ F i j + F j i
  let Z : Fin n → Fin n → ℝ := fun _ _ ↦ 0
  have hg : ∀ i, |g i| ≤ 2 * M := by
    intro i
    dsimp only [g]
    calc
      |F i j + F j i| ≤ |F i j| + |F j i| := abs_add_le _ _
      _ ≤ M + M := add_le_add (hF i j) (hF j i)
      _ = 2 * M := by ring
  have hZ : ∀ i q, |Z i q| ≤ (0 : ℝ) := by simp [Z]
  have hbalanced : ∀ k, ∑ i ∈ P.fiber k, g i = 0 := by
    intro k
    exact sum_crossRowCoefficient_fiber_eq_zero P F hrow hcol k j
  have hmeanSigned : Concentration.uniformExpectation
      (signedSliceQuadratic P a (fun k ↦ r k - a k) g Z) = 0 := by
    rw [show signedSliceQuadratic P a (fun k ↦ r k - a k) g Z =
        (fun S ↦ ∑ i, g i * productSignedSliceValue P S i) by
      funext S
      simp [signedSliceQuadratic, Z]]
    exact uniformExpectation_signedSliceLinear_eq_zero
      P a (fun k ↦ r k - a k) g hbalanced
  have htail := productTwoStageSignedLeft_quadratic_two_sided_probability
    P r a b h hr ha hb hh e g Z 0 (2 * M) t hR
      (by norm_num) (mul_nonneg (by norm_num) hM.le) ht (by
        have : 0 < 8 * M := mul_pos (by norm_num) hM
        simpa [Z] using this) hg hZ
  have hmean : Concentration.uniformExpectation (fun τ ↦
      signedSliceQuadratic P a (fun k ↦ r k - a k) g Z
        (productTwoStageSignedLeft P r a b h τ)) = 0 := by
    rw [uniformExpectation_productTwoStageSignedLeft
      P r a b h hr ha hb hh _]
    exact hmeanSigned
  rw [hmean] at htail
  have hden :
      (4 * (2 * M) + (8 * (∑ k : Fin K, (r k : ℝ))) * 0) ^ 2 =
        (8 * M) ^ 2 := by
    ring
  simpa only [sub_zero, g, Z,
    signedSliceQuadratic_zeroMatrix_eq_crossRowLinear, hden] using htail

/-- The symmetric source-strengthened cross-row tail for the revealed-right
vector. -/
theorem productTwoStageSignedRight_crossRow_two_sided_probability
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (F : Fin n → Fin n → ℝ) (M t : ℝ)
    (hR : 0 < ∑ k : Fin K, r k) (hM : 0 < M) (ht : 0 ≤ t)
    (hF : ∀ i j, |F i j| ≤ M)
    (hrow : ∀ k q i, i ∈ P.fiber k → ∑ j ∈ P.fiber q, F i j = 0)
    (hcol : ∀ k q j, j ∈ P.fiber q → ∑ i ∈ P.fiber k, F i j = 0)
    (j : Fin n) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability
        (fun ω ↦ t ≤ |crossRowLinear F j
          (productSignedSliceValue P
            (productTwoStageSignedRight P r a b h ω))|) ≤
      2 * Real.exp (-t ^ 2 /
        (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  letI : Nonempty
      (ProductSignedSlicePoint P b (fun k ↦ r k - b k)) :=
    productSignedSlicePoint_nonempty P b (fun k ↦ r k - b k)
      (fun k ↦ by rw [Nat.add_sub_of_le (hb k)]; exact hr k)
  let g : Fin n → ℝ := fun i ↦ F i j + F j i
  let Z : Fin n → Fin n → ℝ := fun _ _ ↦ 0
  have hg : ∀ i, |g i| ≤ 2 * M := by
    intro i
    dsimp only [g]
    calc
      |F i j + F j i| ≤ |F i j| + |F j i| := abs_add_le _ _
      _ ≤ M + M := add_le_add (hF i j) (hF j i)
      _ = 2 * M := by ring
  have hZ : ∀ i q, |Z i q| ≤ (0 : ℝ) := by simp [Z]
  have hbalanced : ∀ k, ∑ i ∈ P.fiber k, g i = 0 := by
    intro k
    exact sum_crossRowCoefficient_fiber_eq_zero P F hrow hcol k j
  have hmeanSigned : Concentration.uniformExpectation
      (signedSliceQuadratic P b (fun k ↦ r k - b k) g Z) = 0 := by
    rw [show signedSliceQuadratic P b (fun k ↦ r k - b k) g Z =
        (fun S ↦ ∑ i, g i * productSignedSliceValue P S i) by
      funext S
      simp [signedSliceQuadratic, Z]]
    exact uniformExpectation_signedSliceLinear_eq_zero
      P b (fun k ↦ r k - b k) g hbalanced
  have htail := productTwoStageSignedRight_quadratic_two_sided_probability
    P r a b h hr ha hb hh e g Z 0 (2 * M) t hR
      (by norm_num) (mul_nonneg (by norm_num) hM.le) ht (by
        have : 0 < 8 * M := mul_pos (by norm_num) hM
        simpa [Z] using this) hg hZ
  have hmean : Concentration.uniformExpectation (fun τ ↦
      signedSliceQuadratic P b (fun k ↦ r k - b k) g Z
        (productTwoStageSignedRight P r a b h τ)) = 0 := by
    rw [uniformExpectation_productTwoStageSignedRight
      P r a b h hr ha hb hh _]
    exact hmeanSigned
  rw [hmean] at htail
  have hden :
      (4 * (2 * M) + (8 * (∑ k : Fin K, (r k : ℝ))) * 0) ^ 2 =
        (8 * M) ^ 2 := by
    ring
  simpa only [sub_zero, g, Z,
    signedSliceQuadratic_zeroMatrix_eq_crossRowLinear, hden] using htail

/-- Union bound for a finite family of events under the uniform law. -/
lemma uniformProbability_exists_le_sum {Ω ι : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype ι]
    (Q : ι → Ω → Prop) :
    Concentration.uniformProbability (fun ω ↦ ∃ i, Q i ω) ≤
      ∑ i, Concentration.uniformProbability (Q i) := by
  classical
  have hfin : ∀ s : Finset ι,
      Concentration.uniformProbability (fun ω ↦ ∃ i ∈ s, Q i ω) ≤
        ∑ i ∈ s, Concentration.uniformProbability (Q i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Concentration.uniformProbability]
    | @insert i s hi ih =>
        calc
          Concentration.uniformProbability
              (fun ω ↦ ∃ j ∈ insert i s, Q j ω) ≤
              Concentration.uniformProbability
                (fun ω ↦ Q i ω ∨ ∃ j ∈ s, Q j ω) :=
            Concentration.uniformProbability_mono (by simp)
          _ ≤ Concentration.uniformProbability (Q i) +
                Concentration.uniformProbability
                  (fun ω ↦ ∃ j ∈ s, Q j ω) :=
            uniformProbability_or_le _ _
          _ ≤ Concentration.uniformProbability (Q i) +
                ∑ j ∈ s, Concentration.uniformProbability (Q j) :=
            add_le_add le_rfl ih
          _ = ∑ j ∈ insert i s, Concentration.uniformProbability (Q j) := by
            rw [Finset.sum_insert hi]
  simpa only [Finset.mem_univ, true_and, Finset.sum_filter,
    Finset.filter_true_of_mem] using hfin (Finset.univ : Finset ι)

/-- A single coefficient of the shared quadratic cross term is small except
when one of its two independently revealed row-linear forms is large. -/
theorem quadraticCrossCoefficient_two_sided_probability
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (F : Fin n → Fin n → ℝ) (M t : ℝ)
    (hR : 0 < ∑ k : Fin K, r k) (hM : 0 < M) (ht : 0 ≤ t)
    (hF : ∀ i j, |F i j| ≤ M)
    (hrow : ∀ k q i, i ∈ P.fiber k → ∑ j ∈ P.fiber q, F i j = 0)
    (hcol : ∀ k q j, j ∈ P.fiber q → ∑ i ∈ P.fiber k, F i j = 0)
    (j : Fin n) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability (fun ω ↦
        2 * t ≤ |quadraticCrossCoefficient F
          (productSignedSliceValue P
            (productTwoStageSignedLeft P r a b h ω))
          (productSignedSliceValue P
            (productTwoStageSignedRight P r a b h ω)) j|) ≤
      4 * Real.exp (-t ^ 2 /
        (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  let XL : ProductTwoStageSlicePoint P r a b h → ℝ := fun ω ↦
    crossRowLinear F j (productSignedSliceValue P
      (productTwoStageSignedLeft P r a b h ω))
  let XR : ProductTwoStageSlicePoint P r a b h → ℝ := fun ω ↦
    crossRowLinear F j (productSignedSliceValue P
      (productTwoStageSignedRight P r a b h ω))
  have hleft := productTwoStageSignedLeft_crossRow_two_sided_probability
    P r a b h hr ha hb hh e F M t hR hM ht hF hrow hcol j
  have hright := productTwoStageSignedRight_crossRow_two_sided_probability
    P r a b h hr ha hb hh e F M t hR hM ht hF hrow hcol j
  change Concentration.uniformProbability (fun ω ↦ t ≤ |XL ω|) ≤ _ at hleft
  change Concentration.uniformProbability (fun ω ↦ t ≤ |XR ω|) ≤ _ at hright
  have hbad : ∀ ω : ProductTwoStageSlicePoint P r a b h,
      2 * t ≤ |quadraticCrossCoefficient F
          (productSignedSliceValue P
            (productTwoStageSignedLeft P r a b h ω))
          (productSignedSliceValue P
            (productTwoStageSignedRight P r a b h ω)) j| →
        t ≤ |XL ω| ∨ t ≤ |XR ω| := by
    intro ω hlarge
    by_contra hgood
    push_neg at hgood
    have hrewrite := quadraticCrossCoefficient_eq_crossRowLinear_sub F
      (productSignedSliceValue P
        (productTwoStageSignedLeft P r a b h ω))
      (productSignedSliceValue P
        (productTwoStageSignedRight P r a b h ω)) j
    change _ = XL ω - XR ω at hrewrite
    rw [hrewrite] at hlarge
    have habs : |XL ω - XR ω| < 2 * t := by
      calc
        |XL ω - XR ω| ≤ |XL ω| + |XR ω| := abs_sub _ _
        _ < t + t := add_lt_add hgood.1 hgood.2
        _ = 2 * t := by ring
    exact (not_lt_of_ge hlarge) habs
  calc
    Concentration.uniformProbability (fun ω ↦
        2 * t ≤ |quadraticCrossCoefficient F
          (productSignedSliceValue P
            (productTwoStageSignedLeft P r a b h ω))
          (productSignedSliceValue P
            (productTwoStageSignedRight P r a b h ω)) j|) ≤
        Concentration.uniformProbability
          (fun ω ↦ t ≤ |XL ω| ∨ t ≤ |XR ω|) :=
      Concentration.uniformProbability_mono hbad
    _ ≤ Concentration.uniformProbability (fun ω ↦ t ≤ |XL ω|) +
          Concentration.uniformProbability (fun ω ↦ t ≤ |XR ω|) :=
      uniformProbability_or_le _ _
    _ ≤ 2 * Real.exp (-t ^ 2 /
          (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2)) +
        2 * Real.exp (-t ^ 2 /
          (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2)) :=
      add_le_add hleft hright
    _ = 4 * Real.exp (-t ^ 2 /
          (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2)) := by ring

/-- Simultaneously, all cross coefficients are at most twice the row
threshold outside an event controlled by the finite union bound. -/
theorem exists_large_quadraticCrossCoefficient_probability
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (F : Fin n → Fin n → ℝ) (M t : ℝ)
    (hR : 0 < ∑ k : Fin K, r k) (hM : 0 < M) (ht : 0 ≤ t)
    (hF : ∀ i j, |F i j| ≤ M)
    (hrow : ∀ k q i, i ∈ P.fiber k → ∑ j ∈ P.fiber q, F i j = 0)
    (hcol : ∀ k q j, j ∈ P.fiber q → ∑ i ∈ P.fiber k, F i j = 0) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability (fun ω ↦ ∃ j : Fin n,
        2 * t ≤ |quadraticCrossCoefficient F
          (productSignedSliceValue P
            (productTwoStageSignedLeft P r a b h ω))
          (productSignedSliceValue P
            (productTwoStageSignedRight P r a b h ω)) j|) ≤
      (n : ℝ) * (4 * Real.exp (-t ^ 2 /
        (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2))) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  calc
    Concentration.uniformProbability (fun ω ↦ ∃ j : Fin n,
        2 * t ≤ |quadraticCrossCoefficient F
          (productSignedSliceValue P
            (productTwoStageSignedLeft P r a b h ω))
          (productSignedSliceValue P
            (productTwoStageSignedRight P r a b h ω)) j|) ≤
        ∑ j : Fin n, Concentration.uniformProbability (fun ω ↦
          2 * t ≤ |quadraticCrossCoefficient F
            (productSignedSliceValue P
              (productTwoStageSignedLeft P r a b h ω))
            (productSignedSliceValue P
              (productTwoStageSignedRight P r a b h ω)) j|) :=
      uniformProbability_exists_le_sum _
    _ ≤ ∑ _j : Fin n, 4 * Real.exp (-t ^ 2 /
          (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact quadraticCrossCoefficient_two_sided_probability
        P r a b h hr ha hb hh e F M t hR hM ht hF hrow hcol j
    _ = (n : ℝ) * (4 * Real.exp (-t ^ 2 /
          (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2))) := by simp

/-- Conditional shared-slice concentration with an externally supplied bound
on every cross coefficient.  This is the form used after the extra row-wise
application of Lemma 4.17. -/
theorem quadraticCrossLinear_assemble_two_sided_probability_of_coeff_bound
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (R : ∀ k, BooleanSlicePoint (P.fiber k) (r k))
    (Aset : ∀ k, BooleanSlicePoint (R k).1 (a k))
    (Bset : ∀ k, BooleanSlicePoint (R k).1 (b k))
    (hbal : ∀ k, 2 * h k = (P.fiber k \ (R k).1).card)
    (e : ∀ k, Fin (P.fiber k \ (R k).1).card ≃
      ↑(P.fiber k \ (R k).1))
    (F : Fin n → Fin n → ℝ) (C t : ℝ)
    (hL : 0 < ∑ k : Fin K, (P.fiber k \ (R k).1).card)
    (hC : 0 < C) (ht : 0 ≤ t)
    (hc : ∀ (k : Fin K) (i : Fin n),
      |quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R Aset))
        (productSignedSliceValue P (productRevealedSigned P r b R Bset)) i| ≤
          C) :
    let I : Fin K → Finset (Fin n) :=
      fun k ↦ P.fiber k \ (R k).1
    let hell : ∀ k, h k ≤ (I k).card := fun k ↦ by
      change h k ≤ (P.fiber k \ (R k).1).card
      have := hbal k
      omega
    letI : Nonempty (BooleanSliceFamilyPoint I h) :=
      booleanSliceFamilyPoint_nonempty I h hell
    Concentration.uniformProbability
        (fun S : BooleanSliceFamilyPoint I h ↦
          t ≤ |quadraticCrossLinear F
            (productSignedSliceValue P
              (productRevealedSigned P r a R Aset))
            (productSignedSliceValue P
              (productRevealedSigned P r b R Bset))
            (productTwoStageSharedValue P r a b h
              (assembleTwoStage P r a b h R Aset Bset S))|) ≤
      2 * Real.exp
        (-t ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k \ (R k).1).card : ℕ) : ℝ)) *
            (4 * C) ^ 2)) := by
  let I : Fin K → Finset (Fin n) :=
    fun k ↦ P.fiber k \ (R k).1
  let hell : ∀ k, h k ≤ (I k).card := fun k ↦ by
    change h k ≤ (P.fiber k \ (R k).1).card
    have := hbal k
    omega
  letI : Nonempty (BooleanSliceFamilyPoint I h) :=
    booleanSliceFamilyPoint_nonempty I h hell
  have htail := balancedBooleanSliceFamilyLinear_two_sided_probability
    I h hbal e
      (fun _ i ↦ quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R Aset))
        (productSignedSliceValue P (productRevealedSigned P r b R Bset)) i)
      C t hL hC ht hc
  simpa only [I, quadraticCrossLinear_assemble_eq] using htail

/-- Source-strengthened shared cross-term estimate.  The first term pays for
an exceptional revealed row coefficient; on its complement every coefficient
is bounded by `2 * tRow`, so the shared balanced slice has the second tail. -/
theorem quadraticCrossLinear_two_sided_probability_refined
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (hbal : ∀ k, 2 * h k = (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (F : Fin n → Fin n → ℝ) (M tRow tCross : ℝ)
    (hL : 0 < ∑ k : Fin K, ((P.fiber k).card - r k : ℕ))
    (hR : 0 < ∑ k : Fin K, r k)
    (hM : 0 < M) (htRow : 0 < tRow) (htCross : 0 ≤ tCross)
    (hF : ∀ i j, |F i j| ≤ M)
    (hrow : ∀ k q i, i ∈ P.fiber k → ∑ j ∈ P.fiber q, F i j = 0)
    (hcol : ∀ k q j, j ∈ P.fiber q → ∑ i ∈ P.fiber k, F i j = 0) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability
        (fun ω : ProductTwoStageSlicePoint P r a b h ↦
          tCross ≤ |quadraticCrossLinear F
            (productSignedSliceValue P
              (productTwoStageSignedLeft P r a b h ω))
            (productSignedSliceValue P
              (productTwoStageSignedRight P r a b h ω))
            (productTwoStageSharedValue P r a b h ω)|) ≤
      (n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
        (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2))) +
      2 * Real.exp (-tCross ^ 2 /
        (2 * (∑ k : Fin K,
            (((P.fiber k).card - r k : ℕ) : ℝ)) * (8 * tRow) ^ 2)) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  let bad : ProductTwoStageSlicePoint P r a b h → Prop := fun ω ↦
    ∃ j : Fin n, 2 * tRow ≤ |quadraticCrossCoefficient F
      (productSignedSliceValue P
        (productTwoStageSignedLeft P r a b h ω))
      (productSignedSliceValue P
        (productTwoStageSignedRight P r a b h ω)) j|
  let shared : ProductTwoStageSlicePoint P r a b h → Prop := fun ω ↦
    tCross ≤ |quadraticCrossLinear F
      (productSignedSliceValue P
        (productTwoStageSignedLeft P r a b h ω))
      (productSignedSliceValue P
        (productTwoStageSignedRight P r a b h ω))
      (productTwoStageSharedValue P r a b h ω)|
  have hbad := exists_large_quadraticCrossCoefficient_probability
    P r a b h hr ha hb hh e F M tRow hR hM htRow.le hF hrow hcol
  change Concentration.uniformProbability bad ≤ _ at hbad
  let A : Type := ProductTwoStageRevealedPoint P r a b
  let B : A → Type := fun ρ ↦ BooleanSliceFamilyPoint
    (fun k ↦ P.fiber k \ (ρ.1 k).1) h
  letI : Fintype A := by
    dsimp only [A, ProductTwoStageRevealedPoint]
    infer_instance
  letI : Nonempty A := productTwoStageRevealedPoint_nonempty P r a b hr ha hb
  letI : (ρ : A) → Fintype (B ρ) := fun ρ ↦ by
    dsimp only [B, BooleanSliceFamilyPoint]
    infer_instance
  letI : (ρ : A) → Nonempty (B ρ) := fun ρ ↦ by
    apply booleanSliceFamilyPoint_nonempty
    intro k
    rw [card_fiber_sdiff_revealed P r ρ.1 k]
    exact hh k
  let ρ₀ : A := Classical.choice inferInstance
  letI : Nonempty (Σ ρ : A, B ρ) :=
    ⟨⟨ρ₀, Classical.choice (inferInstance : Nonempty (B ρ₀))⟩⟩
  let E : ProductTwoStageSlicePoint P r a b h ≃ Σ ρ : A, B ρ :=
    productTwoStageSigmaEquiv P r a b h
  let goodTail : ProductTwoStageSlicePoint P r a b h → Prop :=
    fun ω ↦ ¬bad ω ∧ shared ω
  let Q : (Σ ρ : A, B ρ) → Prop := fun σ ↦ goodTail (E.symm σ)
  have hcond : ∀ ρ : A,
      Concentration.uniformProbability (fun C : B ρ ↦ Q ⟨ρ, C⟩) ≤
        2 * Real.exp (-tCross ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k).card - r k : ℕ) : ℝ)) *
            (8 * tRow) ^ 2)) := by
    intro ρ
    let R := ρ.1
    let Aset := ρ.2.1
    let Bset := ρ.2.2
    let badR : Prop := ∃ j : Fin n,
      2 * tRow ≤ |quadraticCrossCoefficient F
        (productSignedSliceValue P (productRevealedSigned P r a R Aset))
        (productSignedSliceValue P (productRevealedSigned P r b R Bset)) j|
    by_cases hbadR : badR
    · have hfalse : (fun C : B ρ ↦ Q ⟨ρ, C⟩) = fun _ ↦ False := by
        funext C
        apply propext
        have hEsymm : E.symm ⟨ρ, C⟩ =
            assembleTwoStage P r a b h R Aset Bset C := by rfl
        change (¬bad (E.symm ⟨ρ, C⟩) ∧
          shared (E.symm ⟨ρ, C⟩)) ↔ False
        rw [hEsymm]
        constructor
        · intro hQ
          apply hQ.1
          simpa only [bad, productTwoStageSignedLeft_assemble,
            productTwoStageSignedRight_assemble] using hbadR
        · intro hFalse
          contradiction
      rw [hfalse]
      simp [Concentration.uniformProbability]
      positivity
    · have hbalR : ∀ k,
          2 * h k = (P.fiber k \ (R k).1).card := by
        intro k
        rw [card_fiber_sdiff_revealed P r R k]
        exact hbal k
      have hLR : 0 < ∑ k : Fin K,
          (P.fiber k \ (R k).1).card := by
        simpa only [card_fiber_sdiff_revealed P r R] using hL
      have hc : ∀ (k : Fin K) (i : Fin n),
          |quadraticCrossCoefficient F
            (productSignedSliceValue P (productRevealedSigned P r a R Aset))
            (productSignedSliceValue P (productRevealedSigned P r b R Bset)) i| ≤
              2 * tRow := by
        intro k i
        exact (lt_of_not_ge (fun hi ↦ hbadR ⟨i, hi⟩)).le
      have htail :=
        quadraticCrossLinear_assemble_two_sided_probability_of_coeff_bound
          P r a b h R Aset Bset hbalR
          (fun k ↦ (Finset.equivFin (P.fiber k \ (R k).1)).symm)
          F (2 * tRow) tCross hLR (mul_pos (by norm_num) htRow)
          htCross hc
      have hmono : Concentration.uniformProbability (fun C : B ρ ↦
          Q ⟨ρ, C⟩) ≤ Concentration.uniformProbability (fun C : B ρ ↦
            tCross ≤ |quadraticCrossLinear F
              (productSignedSliceValue P
                (productRevealedSigned P r a R Aset))
              (productSignedSliceValue P
                (productRevealedSigned P r b R Bset))
              (productTwoStageSharedValue P r a b h
                (assembleTwoStage P r a b h R Aset Bset C))|) := by
        apply Concentration.uniformProbability_mono
        intro C hQC
        have hEsymm : E.symm ⟨ρ, C⟩ =
            assembleTwoStage P r a b h R Aset Bset C := by rfl
        simpa only [Q, goodTail, shared, hEsymm,
          productTwoStageSignedLeft_assemble,
          productTwoStageSignedRight_assemble] using hQC.2
      refine hmono.trans ?_
      have hden : (4 * (2 * tRow)) ^ 2 = (8 * tRow) ^ 2 := by ring
      simpa only [A, B, R, Aset, Bset,
        card_fiber_sdiff_revealed P r R, hden] using htail
  have hgood : Concentration.uniformProbability goodTail ≤
      2 * Real.exp (-tCross ^ 2 /
        (2 * (∑ k : Fin K,
            (((P.fiber k).card - r k : ℕ) : ℝ)) *
          (8 * tRow) ^ 2)) := by
    calc
      Concentration.uniformProbability goodTail =
          Concentration.uniformProbability Q := by
        rw [← uniformProbability_comp_equiv E Q]
        apply congrArg Concentration.uniformProbability
        funext ω
        apply propext
        change goodTail ω ↔ goodTail (E.symm (E ω))
        rw [E.symm_apply_apply]
      _ ≤ _ := uniformProbability_sigma_le Q _ hcond
  have hsplit : ∀ ω : ProductTwoStageSlicePoint P r a b h,
      shared ω → bad ω ∨ goodTail ω := by
    intro ω hω
    by_cases hbω : bad ω
    · exact Or.inl hbω
    · exact Or.inr ⟨hbω, hω⟩
  calc
    Concentration.uniformProbability shared ≤
        Concentration.uniformProbability (fun ω ↦ bad ω ∨ goodTail ω) :=
      Concentration.uniformProbability_mono hsplit
    _ ≤ Concentration.uniformProbability bad +
          Concentration.uniformProbability goodTail :=
      uniformProbability_or_le _ _
    _ ≤ (n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
          (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * M) ^ 2))) +
        2 * Real.exp (-tCross ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k).card - r k : ℕ) : ℝ)) *
            (8 * tRow) ^ 2)) := add_le_add hbad hgood

/-- The complete asymmetric two-stage quadratic estimate with the
source-strengthened cross-term bound. -/
theorem productTwoStage_quadratic_difference_probability_refined_of_meanGap
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (hbal : ∀ k, 2 * h k = (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (A B tE tRow tC dMean : ℝ)
    (hRnat : 0 < ∑ k : Fin K, r k)
    (hLnat : 0 < ∑ k : Fin K, ((P.fiber k).card - r k : ℕ))
    (hA : 0 < A) (hB : 0 ≤ B) (htE : 0 ≤ tE)
    (htRow : 0 < tRow) (htC : 0 ≤ tC)
    (hlip : 0 < 4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A)
    (hrow : ∀ k q i, i ∈ P.fiber k → ∑ j ∈ P.fiber q, F i j = 0)
    (hcol : ∀ k q j, j ∈ P.fiber q → ∑ i ∈ P.fiber k, F i j = 0)
    (hmean :
      |Concentration.uniformExpectation
          (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) -
        Concentration.uniformExpectation
          (signedSliceQuadratic P b (fun k ↦ r k - b k) f F)| ≤ dMean) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    Concentration.uniformProbability
        (fun ω : ProductTwoStageSlicePoint P r a b h ↦
          2 * tE + tC + dMean ≤
            |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
                (productTwoStageSliceLeft P r a b h ω) -
              productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
                (productTwoStageSliceRight P r a b h ω)|) ≤
      4 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
        ((n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
          (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * A) ^ 2))) +
        2 * Real.exp (-tC ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k).card - r k : ℕ) : ℝ)) * (8 * tRow) ^ 2))) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  let XL : ProductTwoStageSlicePoint P r a b h → ℝ := fun ω ↦
    signedSliceQuadratic P a (fun k ↦ r k - a k) f F
      (productTwoStageSignedLeft P r a b h ω)
  let XR : ProductTwoStageSlicePoint P r a b h → ℝ := fun ω ↦
    signedSliceQuadratic P b (fun k ↦ r k - b k) f F
      (productTwoStageSignedRight P r a b h ω)
  let Z : ProductTwoStageSlicePoint P r a b h → ℝ := fun ω ↦
    quadraticCrossLinear F
      (productSignedSliceValue P (productTwoStageSignedLeft P r a b h ω))
      (productSignedSliceValue P (productTwoStageSignedRight P r a b h ω))
      (productTwoStageSharedValue P r a b h ω)
  let μL : ℝ := Concentration.uniformExpectation XL
  let μR : ℝ := Concentration.uniformExpectation XR
  have hμL : μL = Concentration.uniformExpectation
      (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) := by
    dsimp only [μL, XL]
    exact uniformExpectation_productTwoStageSignedLeft
      P r a b h hr ha hb hh _
  have hμR : μR = Concentration.uniformExpectation
      (signedSliceQuadratic P b (fun k ↦ r k - b k) f F) := by
    dsimp only [μR, XR]
    exact uniformExpectation_productTwoStageSignedRight
      P r a b h hr ha hb hh _
  have hleft := productTwoStageSignedLeft_quadratic_two_sided_probability
    P r a b h hr ha hb hh e f F A B tE hRnat hA.le hB htE hlip hf hF
  have hright := productTwoStageSignedRight_quadratic_two_sided_probability
    P r a b h hr ha hb hh e f F A B tE hRnat hA.le hB htE hlip hf hF
  have hcross := quadraticCrossLinear_two_sided_probability_refined
    P r a b h hr ha hb hh hbal e F A tRow tC hLnat hRnat hA
      htRow htC hF hrow hcol
  change Concentration.uniformProbability
      (fun ω ↦ tE ≤ |XL ω - μL|) ≤ _ at hleft
  change Concentration.uniformProbability
      (fun ω ↦ tE ≤ |XR ω - μR|) ≤ _ at hright
  change Concentration.uniformProbability (fun ω ↦ tC ≤ |Z ω|) ≤ _ at hcross
  have hmean' : |μL - μR| ≤ dMean := by
    rw [hμL, hμR]
    exact hmean
  have hbad : ∀ ω : ProductTwoStageSlicePoint P r a b h,
      2 * tE + tC + dMean ≤
          |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a b h ω) -
            productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
              (productTwoStageSliceRight P r a b h ω)| →
        (tE ≤ |XL ω - μL|) ∨
          (tE ≤ |XR ω - μR|) ∨ tC ≤ |Z ω| := by
    intro ω hlarge
    by_contra hgood
    push Not at hgood
    have hdecomp := productTwoStage_quadratic_sub_decomposition
      P r a b h ω f₀ f F
    change _ = XL ω - XR ω + Z ω at hdecomp
    have hcenter : XL ω - XR ω + Z ω =
        ((XL ω - μL) - (XR ω - μR) + Z ω) + (μL - μR) := by
      ring
    have habs :
        |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a b h ω) -
            productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
              (productTwoStageSliceRight P r a b h ω)| <
          2 * tE + tC + dMean := by
      rw [hdecomp, hcenter]
      calc
        |((XL ω - μL) - (XR ω - μR) + Z ω) + (μL - μR)| ≤
            |(XL ω - μL) - (XR ω - μR) + Z ω| + |μL - μR| :=
          abs_add_le _ _
        _ ≤ (|XL ω - μL| + |XR ω - μR|) + |Z ω| +
            |μL - μR| := by
          gcongr
          calc
            |(XL ω - μL) - (XR ω - μR) + Z ω| ≤
                |(XL ω - μL) - (XR ω - μR)| + |Z ω| := abs_add_le _ _
            _ ≤ (|XL ω - μL| + |XR ω - μR|) + |Z ω| := by
              gcongr
              exact abs_sub _ _
        _ < 2 * tE + tC + dMean := by
          linarith [hgood.1, hgood.2.1, hgood.2.2, hmean']
    exact (not_lt_of_ge hlarge) habs
  calc
    Concentration.uniformProbability
        (fun ω ↦ 2 * tE + tC + dMean ≤
          |productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
              (productTwoStageSliceLeft P r a b h ω) -
            productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
              (productTwoStageSliceRight P r a b h ω)|) ≤
        Concentration.uniformProbability
          (fun ω ↦ (tE ≤ |XL ω - μL|) ∨
            (tE ≤ |XR ω - μR|) ∨ tC ≤ |Z ω|) :=
      Concentration.uniformProbability_mono hbad
    _ ≤ Concentration.uniformProbability (fun ω ↦ tE ≤ |XL ω - μL|) +
          Concentration.uniformProbability
            (fun ω ↦ (tE ≤ |XR ω - μR|) ∨ tC ≤ |Z ω|) :=
      uniformProbability_or_le _ _
    _ ≤ Concentration.uniformProbability (fun ω ↦ tE ≤ |XL ω - μL|) +
          (Concentration.uniformProbability (fun ω ↦ tE ≤ |XR ω - μR|) +
            Concentration.uniformProbability (fun ω ↦ tC ≤ |Z ω|)) := by
      gcongr
      exact uniformProbability_or_le _ _
    _ ≤ (2 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2))) +
        ((2 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2))) +
          ((n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
            (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * A) ^ 2))) +
          2 * Real.exp (-tC ^ 2 /
            (2 * (∑ k : Fin K,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (8 * tRow) ^ 2)))) :=
      add_le_add hleft (add_le_add hright hcross)
    _ = 4 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
            (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
        ((n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
          (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * A) ^ 2))) +
        2 * Real.exp (-tC ^ 2 /
          (2 * (∑ k : Fin K,
              (((P.fiber k).card - r k : ℕ) : ℝ)) *
            (8 * tRow) ^ 2))) := by ring

/-- Coupling form of the refined asymmetric two-stage estimate. -/
theorem productTwoStage_quadratic_isClose_refined_of_meanGap
    {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (r a b h : Fin K → ℕ)
    (hr : ∀ k, r k ≤ (P.fiber k).card)
    (ha : ∀ k, a k ≤ r k) (hb : ∀ k, b k ≤ r k)
    (hh : ∀ k, h k ≤ (P.fiber k).card - r k)
    (hbal : ∀ k, 2 * h k = (P.fiber k).card - r k)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (A B tE tRow tC dMean : ℝ)
    (hRnat : 0 < ∑ k : Fin K, r k)
    (hLnat : 0 < ∑ k : Fin K, ((P.fiber k).card - r k : ℕ))
    (hA : 0 < A) (hB : 0 ≤ B) (htE : 0 ≤ tE)
    (htRow : 0 < tRow) (htC : 0 ≤ tC)
    (hlip : 0 < 4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A)
    (hf : ∀ i, |f i| ≤ B) (hF : ∀ i j, |F i j| ≤ A)
    (hrow : ∀ k q i, i ∈ P.fiber k → ∑ j ∈ P.fiber q, F i j = 0)
    (hcol : ∀ k q j, j ∈ P.fiber q → ∑ i ∈ P.fiber k, F i j = 0)
    (hmean :
      |Concentration.uniformExpectation
          (signedSliceQuadratic P a (fun k ↦ r k - a k) f F) -
        Concentration.uniformExpectation
          (signedSliceQuadratic P b (fun k ↦ r k - b k) f F)| ≤ dMean) :
    letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
      productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
    letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
      productSlicePoint_nonempty P (fun k ↦ a k + h k) (fun k ↦ by
        calc
          a k + h k ≤ r k + ((P.fiber k).card - r k) :=
            Nat.add_le_add (ha k) (hh k)
          _ = (P.fiber k).card := Nat.add_sub_of_le (hr k))
    letI : Nonempty (ProductSlicePoint P (fun k ↦ b k + h k)) :=
      productSlicePoint_nonempty P (fun k ↦ b k + h k) (fun k ↦ by
        calc
          b k + h k ≤ r k + ((P.fiber k).card - r k) :=
            Nat.add_le_add (hb k) (hh k)
          _ = (P.fiber k).card := Nat.add_sub_of_le (hr k))
    (FiniteUniformCoupling.ofMaps
      (productTwoStageSliceLeft P r a b h)
      (productTwoStageSliceRight P r a b h)
      (complexExpectation_productTwoStageSliceLeft P r a b h hr ha hb hh)
      (complexExpectation_productTwoStageSliceRight P r a b h hr ha hb hh)).IsClose
        (productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F)
        (productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F)
        (2 * tE + tC + dMean)
        (4 * Real.exp
            (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
              (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
          ((n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
            (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * A) ^ 2))) +
          2 * Real.exp (-tC ^ 2 /
            (2 * (∑ k : Fin K,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (8 * tRow) ^ 2)))) := by
  letI : Nonempty (ProductTwoStageSlicePoint P r a b h) :=
    productTwoStageSlicePoint_nonempty P r a b h hr ha hb hh
  have hell : ∀ k, a k + h k ≤ (P.fiber k).card := fun k ↦ by
    calc
      a k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (ha k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  have hell' : ∀ k, b k + h k ≤ (P.fiber k).card := fun k ↦ by
    calc
      b k + h k ≤ r k + ((P.fiber k).card - r k) :=
        Nat.add_le_add (hb k) (hh k)
      _ = (P.fiber k).card := Nat.add_sub_of_le (hr k)
  letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ a k + h k) hell
  letI : Nonempty (ProductSlicePoint P (fun k ↦ b k + h k)) :=
    productSlicePoint_nonempty P (fun k ↦ b k + h k) hell'
  let X := productSliceQuadratic P (fun k ↦ a k + h k) f₀ f F
  let Y := productSliceQuadratic P (fun k ↦ b k + h k) f₀ f F
  let q :=
    4 * Real.exp
        (-tE ^ 2 / (2 * (∑ k : Fin K, (r k : ℝ)) *
          (4 * B + 8 * (∑ k : Fin K, (r k : ℝ)) * A) ^ 2)) +
      ((n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
        (2 * (∑ k : Fin K, (r k : ℝ)) * (8 * A) ^ 2))) +
      2 * Real.exp (-tC ^ 2 /
        (2 * (∑ k : Fin K,
            (((P.fiber k).card - r k : ℕ) : ℝ)) *
          (8 * tRow) ^ 2)))
  have htail :=
    productTwoStage_quadratic_difference_probability_refined_of_meanGap
      P r a b h hr ha hb hh hbal e f₀ f F A B tE tRow tC dMean
        hRnat hLnat hA hB htE htRow htC hlip hf hF hrow hcol hmean
  change Concentration.uniformProbability
      (fun ω : ProductTwoStageSlicePoint P r a b h ↦
        2 * tE + tC + dMean ≤
          |X (productTwoStageSliceLeft P r a b h ω) -
            Y (productTwoStageSliceRight P r a b h ω)|) ≤ q at htail
  have hstrict : Concentration.uniformProbability
      (fun ω : ProductTwoStageSlicePoint P r a b h ↦
        2 * tE + tC + dMean <
          |X (productTwoStageSliceLeft P r a b h ω) -
            Y (productTwoStageSliceRight P r a b h ω)|) ≤ q :=
    (Concentration.uniformProbability_mono fun _ hω ↦ hω.le).trans htail
  exact FiniteUniformCoupling.ofMaps_isClose_of_uniformProbability_bad
    (productTwoStageSliceLeft P r a b h)
    (productTwoStageSliceRight P r a b h)
    (complexExpectation_productTwoStageSliceLeft P r a b h hr ha hb hh)
    (complexExpectation_productTwoStageSliceRight P r a b h hr ha hb hh)
    X Y (2 * tE + tC + dMean) q hstrict

/-- Enlarging the permitted error and failure probability preserves an
`IsClose` certificate. -/
lemma FiniteUniformCoupling.IsClose.mono
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (C : FiniteUniformCoupling A B) (X : A → ℝ) (Y : B → ℝ)
    {r q r' q' : ℝ} (h : C.IsClose X Y r q)
    (hr : r ≤ r') (hq : q ≤ q') : C.IsClose X Y r' q' := by
  have hprob : C.probability (fun ω ↦
      |X (C.left ω) - Y (C.right ω)| ≤ r) ≤
      C.probability (fun ω ↦
        |X (C.left ω) - Y (C.right ω)| ≤ r') := by
    rw [FiniteUniformCoupling.probability,
      FiniteUniformCoupling.probability,
      div_le_div_iff_of_pos_right (by exact_mod_cast C.size_pos :
        (0 : ℝ) < C.size)]
    exact_mod_cast Finset.card_le_card (by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hω.trans hr)
  unfold FiniteUniformCoupling.IsClose at h ⊢
  linarith

/-- Existence of a finite uniform coupling, including the nonemptiness data
for its two product-slice marginal spaces. -/
def HasQuadraticSliceCoupling {n K : ℕ}
    (P : BucketPartition (Fin n) (Fin K)) (ell ell' : Fin K → ℕ)
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Fin n → Fin n → ℝ)
    (radius failure : ℝ) : Prop :=
  ∃ hleft : Nonempty (ProductSlicePoint P ell),
    ∃ hright : Nonempty (ProductSlicePoint P ell'),
      letI := hleft
      letI := hright
      ∃ C : FiniteUniformCoupling
          (ProductSlicePoint P ell) (ProductSlicePoint P ell'),
        C.IsClose (productSliceQuadratic P ell f₀ f F)
          (productSliceQuadratic P ell' f₀ f F) radius failure

/-- Finite, source-facing specialization of KSSS Lemma 11.2.  All
probabilistic work is discharged; the remaining hypotheses are precisely the
eventual numerical inequalities for the displayed choices of thresholds. -/
theorem ksssLemma112_of_numerical {n m : ℕ}
    (δ : ℝ) (P : BucketPartition (Fin n) (Fin m))
    (ell ell' : Fin m → ℕ) (f₀ : ℝ) (f : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (tE tRow tC : ℝ)
    (hmargin0 : 0 ≤ ksssSliceMargin n δ)
    (hmargin : ∀ k, ksssSliceMargin n δ ≤
      ((P.fiber k).card : ℝ) / 2)
    (hcard : ∀ k, 2 ≤ (P.fiber k).card)
    (hell : IsNearBalanced δ P ell)
    (hell' : IsNearBalanced δ P ell')
    (hcoeff : HasKSSSBalancedCoefficients δ P f F)
    (hRnat : 0 < ∑ k : Fin m,
      twoStageExceptionalSize (fun q ↦ (P.fiber q).card)
        (fun q ↦ ksssCoreSize n δ (P.fiber q).card) k)
    (hLnat : 0 < ∑ k : Fin m,
      ((P.fiber k).card -
        twoStageExceptionalSize (fun q ↦ (P.fiber q).card)
          (fun q ↦ ksssCoreSize n δ (P.fiber q).card) k : ℕ))
    (htE : 0 ≤ tE) (htRow : 0 < tRow) (htC : 0 ≤ tC)
    (hdist : 2 * tE + tC + ksssExposedMeanGap δ P ≤
      scale n (3 / 4 + 4 * δ))
    (hprob :
      let r : Fin m → ℕ := fun k ↦
        twoStageExceptionalSize (fun q ↦ (P.fiber q).card)
          (fun q ↦ ksssCoreSize n δ (P.fiber q).card) k
      4 * Real.exp
          (-tE ^ 2 / (2 * (∑ k : Fin m, (r k : ℝ)) *
            (4 * scale n (1 / 2 + 3 * δ) +
              8 * (∑ k : Fin m, (r k : ℝ))) ^ 2)) +
        ((n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
          (2 * (∑ k : Fin m, (r k : ℝ)) * 8 ^ 2))) +
        2 * Real.exp (-tC ^ 2 /
          (2 * (∑ k : Fin m,
              (((P.fiber k).card - r k : ℕ) : ℝ)) *
            (8 * tRow) ^ 2))) ≤
        Real.exp (-scale n (δ / 2))) :
    HasQuadraticSliceCoupling P ell ell' f₀ f F
      (scale n (3 / 4 + 4 * δ)) (Real.exp (-scale n (δ / 2))) := by
  let core : Fin m → ℕ := fun k ↦ ksssCoreSize n δ (P.fiber k).card
  let bucketSize : Fin m → ℕ := fun k ↦ (P.fiber k).card
  let r := twoStageExceptionalSize bucketSize core
  let a := twoStageInnerSize ell core
  let b := twoStageInnerSize ell' core
  have hw := ksssCoreSize_source_windows δ P ell ell'
    hmargin0 hmargin hell hell'
  have hc := twoStage_source_cardinality_data bucketSize ell ell' core
    hw.2.2.2.2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
  have hmean := ksss_exposedMeanGap_le δ P ell ell' f F
    hmargin0 hmargin hcard hell hell' hcoeff
  have hEqL : (fun k ↦ a k + core k) = ell := by
    funext k
    exact hc.2.2.2.2.2.1 k
  have hEqR : (fun k ↦ b k + core k) = ell' := by
    funext k
    exact hc.2.2.2.2.2.2 k
  have hellValid : ∀ k, ell k ≤ (P.fiber k).card := by
    intro k
    have hhigh := hw.2.2.1 k
    omega
  have hellValid' : ∀ k, ell' k ≤ (P.fiber k).card := by
    intro k
    have hhigh := hw.2.2.2.1 k
    omega
  have hleftCount : ∀ k, a k + core k ≤ (P.fiber k).card := by
    intro k
    rw [show a k + core k = ell k from congrFun hEqL k]
    exact hellValid k
  have hrightCount : ∀ k, b k + core k ≤ (P.fiber k).card := by
    intro k
    rw [show b k + core k = ell' k from congrFun hEqR k]
    exact hellValid' k
  have hsource : HasQuadraticSliceCoupling P
      (fun k ↦ a k + core k) (fun k ↦ b k + core k) f₀ f F
      (scale n (3 / 4 + 4 * δ)) (Real.exp (-scale n (δ / 2))) := by
    unfold HasQuadraticSliceCoupling
    refine ⟨productSlicePoint_nonempty P _ hleftCount,
      productSlicePoint_nonempty P _ hrightCount, ?_⟩
    letI : Nonempty (ProductTwoStageSlicePoint P r a b core) :=
      productTwoStageSlicePoint_nonempty P r a b core
        hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
    letI : Nonempty (ProductSlicePoint P (fun k ↦ a k + core k)) :=
      productSlicePoint_nonempty P _ hleftCount
    letI : Nonempty (ProductSlicePoint P (fun k ↦ b k + core k)) :=
      productSlicePoint_nonempty P _ hrightCount
    have hRnat' : 0 < ∑ k : Fin m, r k := by
      simpa only [r, bucketSize, core] using hRnat
    have hLnat' : 0 < ∑ k : Fin m, ((P.fiber k).card - r k : ℕ) := by
      simpa only [r, bucketSize, core] using hLnat
    have hlip : 0 < 4 * scale n (1 / 2 + 3 * δ) +
        8 * (∑ k : Fin m, (r k : ℝ)) := by
      have hRreal : 0 < ∑ k : Fin m, (r k : ℝ) := by exact_mod_cast hRnat'
      have hsecond : 0 < 8 * (∑ k : Fin m, (r k : ℝ)) :=
        mul_pos (by norm_num) hRreal
      nlinarith [scale_nonneg n (1 / 2 + 3 * δ)]
    have hclose := productTwoStage_quadratic_isClose_refined_of_meanGap
      P r a b core hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
        (fun k ↦ (Finset.equivFin (P.fiber k)).symm)
        f₀ f F 1 (scale n (1 / 2 + 3 * δ)) tE tRow tC
        (ksssExposedMeanGap δ P) hRnat' hLnat' (by norm_num)
        (scale_nonneg n _) htE htRow htC (by simpa using hlip)
        hcoeff.2.1 hcoeff.2.2.1 hcoeff.2.2.2.2.1 hcoeff.2.2.2.2.2 hmean
    let C₀ := FiniteUniformCoupling.ofMaps
      (productTwoStageSliceLeft P r a b core)
      (productTwoStageSliceRight P r a b core)
      (complexExpectation_productTwoStageSliceLeft P r a b core
        hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1)
      (complexExpectation_productTwoStageSliceRight P r a b core
        hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1)
    have hclose' : C₀.IsClose
        (productSliceQuadratic P (fun k ↦ a k + core k) f₀ f F)
        (productSliceQuadratic P (fun k ↦ b k + core k) f₀ f F)
        (2 * tE + tC + ksssExposedMeanGap δ P)
        (4 * Real.exp
            (-tE ^ 2 / (2 * (∑ k : Fin m, (r k : ℝ)) *
              (4 * scale n (1 / 2 + 3 * δ) +
                8 * (∑ k : Fin m, (r k : ℝ))) ^ 2)) +
          ((n : ℝ) * (4 * Real.exp (-tRow ^ 2 /
            (2 * (∑ k : Fin m, (r k : ℝ)) * 8 ^ 2))) +
          2 * Real.exp (-tC ^ 2 /
            (2 * (∑ k : Fin m,
                (((P.fiber k).card - r k : ℕ) : ℝ)) *
              (8 * tRow) ^ 2)))) := by
      simpa only [one_mul, mul_one] using hclose
    refine ⟨C₀, hclose'.mono C₀ _ _ hdist ?_⟩
    simpa only [r, bucketSize, core] using hprob
  simpa only [hEqL, hEqR] using hsource

end BooleanSlices
end Erdos88
