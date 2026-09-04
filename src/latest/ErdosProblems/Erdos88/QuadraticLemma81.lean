import ErdosProblems.Erdos88.QuadraticLemma83
import ErdosProblems.Erdos88.LinearLCDCancellation

/-!
# KSSS Lemma 8.1: conditioned quadratic cancellation

This file starts the assembly of Lemma 8.1.  The first step is the form of
Lemma 8.3 needed after conditioning on the number of selected vertices in the
`I`-part of the Lemma 8.2 partition: the remaining random set is a uniform
fixed-size slice of `J`, rather than a slice of the whole ambient vertex set.
-/

namespace Erdos88
namespace QuadraticCancellation

open scoped BigOperators
open Erdos88.Fourier

/-- The function-valued Boolean slice on the subtype of a finset is
equivalent to the finset-valued slice used for finite concentration. -/
def boolSliceEquivBooleanSlicePoint
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (I : Finset alpha) (ell : ℕ) :
    BoolSlice ↑I ell ≃ BooleanSlices.BooleanSlicePoint I ell :=
  (boolSliceEquivFinsetLen ↑I ell).trans
    { toFun := fun S ↦ ⟨S.1.map (Function.Embedding.subtype _), by
        rw [BooleanSlices.mem_booleanSlice]
        constructor
        · intro x hx
          rw [Finset.mem_map] at hx
          obtain ⟨i, _, rfl⟩ := hx
          exact i.property
        · rw [Finset.card_map]
          exact S.2⟩
      invFun := fun S ↦
        ⟨BooleanSlices.finsetLift I S.1, by
          have hS := (BooleanSlices.mem_booleanSlice.mp S.2)
          exact (BooleanSlices.card_finsetLift I S.1 hS.1).trans hS.2⟩
      left_inv := by
        intro S
        apply Subtype.ext
        ext i
        simp [BooleanSlices.finsetLift]
      right_inv := by
        intro S
        apply Subtype.ext
        exact BooleanSlices.map_finsetLift I S.1
          (BooleanSlices.mem_booleanSlice.mp S.2).1 }

/-- The ambient finset selected by a function-valued Boolean slice. -/
def boolSliceSupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (ell : ℕ) (x : BoolSlice ↑I ell) : Finset α :=
  (boolSliceEquivBooleanSlicePoint I ell x).1

lemma boolSliceSupport_subset
    {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (ell : ℕ) (x : BoolSlice ↑I ell) :
    boolSliceSupport I ell x ⊆ I :=
  (BooleanSlices.mem_booleanSlice.mp
    (boolSliceEquivBooleanSlicePoint I ell x).2).1

lemma boolSlice_size_le_card
    {I : Type*} [Fintype I] [DecidableEq I] {ell : ℕ}
    (x : BoolSlice I ell) : ell ≤ Fintype.card I := by
  rw [← x.2]
  unfold boolWeight
  simpa only [Finset.card_univ] using
    Finset.card_le_card
      (Finset.filter_subset (fun i ↦ x.1 i) (Finset.univ : Finset I))

/-- Summing a weight against the Boolean function is the same as summing
over its selected ambient support. -/
lemma sum_boolIndicator_eq_sum_boolSliceSupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (ell : ℕ) (x : BoolSlice ↑I ell) (c : α → ℝ) :
    (∑ i : ↑I, c i.1 * boolIndicator (x.1 i)) =
      ∑ v ∈ boolSliceSupport I ell x, c v := by
  classical
  have hsupport : boolSliceSupport I ell x =
      ((Finset.univ : Finset ↑I).filter fun i ↦ x.1 i).map
        (Function.Embedding.subtype _) := rfl
  rw [hsupport, Finset.sum_map, Finset.sum_filter]
  simp [boolIndicator]

/-- A fixed fiber of a global slice, indexed by the number of selected
coordinates in the first part of a partition. -/
def BooleanSlicePartitionFiber
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (I : Finset alpha) (k a : ℕ) :=
  {S : BooleanSlices.BooleanSlicePoint (Finset.univ : Finset alpha) k //
    (S.1 ∩ I).card = a}

/-- Conditioning a global Boolean slice on its cardinality in `I` gives
the product of the corresponding slices on the two partition parts. -/
def booleanSlicePartitionFiberEquiv
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (I J : Finset alpha) (k a : ℕ) (ha : a ≤ k)
    (hcover : I ∪ J = Finset.univ) (hdisjoint : Disjoint I J) :
    BooleanSlicePartitionFiber I k a ≃
      BooleanSlices.BooleanSlicePoint I a ×
        BooleanSlices.BooleanSlicePoint J (k - a) where
  toFun S := by
    let A := S.1.1 ∩ I
    let B := S.1.1 ∩ J
    have hS : S.1.1 ⊆ I ∪ J := by rw [hcover]; exact Finset.subset_univ _
    have hdecomp : S.1.1 = A ∪ B := by
      ext x
      simp only [A, B, Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        have hx' := Finset.mem_union.mp (hS hx)
        exact hx'.imp (fun hxI ↦ ⟨hx, hxI⟩) (fun hxJ ↦ ⟨hx, hxJ⟩)
      · rintro (hx | hx) <;> exact hx.1
    have hAB : Disjoint A B := by
      exact hdisjoint.mono (Finset.inter_subset_right)
        (Finset.inter_subset_right)
    have hScard := (BooleanSlices.mem_booleanSlice.mp S.1.2).2
    have hAcard : A.card = a := S.2
    have hcard : A.card + B.card = k := by
      rw [← Finset.card_union_of_disjoint hAB, ← hdecomp, hScard]
    refine (⟨A, BooleanSlices.mem_booleanSlice.mpr
      ⟨Finset.inter_subset_right, S.2⟩⟩,
      ⟨B, BooleanSlices.mem_booleanSlice.mpr
        ⟨Finset.inter_subset_right, ?_⟩⟩)
    omega
  invFun p := by
    let A := p.1.1
    let B := p.2.1
    have hA := BooleanSlices.mem_booleanSlice.mp p.1.2
    have hB := BooleanSlices.mem_booleanSlice.mp p.2.2
    have hAB : Disjoint A B := hdisjoint.mono hA.1 hB.1
    have hcard : (A ∪ B).card = k := by
      rw [Finset.card_union_of_disjoint hAB, hA.2, hB.2]
      omega
    have hinter : (A ∪ B) ∩ I = A := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxB, hxI⟩
        · exact hxA
        · exact False.elim (Finset.disjoint_left.mp hdisjoint hxI (hB.1 hxB))
      · intro hxA
        exact ⟨Or.inl hxA, hA.1 hxA⟩
    exact ⟨⟨A ∪ B, BooleanSlices.mem_booleanSlice.mpr
      ⟨Finset.subset_univ _, hcard⟩⟩, by rw [hinter, hA.2]⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    have hS : S.1.1 ⊆ I ∪ J := by
      rw [hcover]
      exact Finset.subset_univ _
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      exact (Finset.mem_union.mp (hS hx)).imp
        (fun hxI ↦ ⟨hx, hxI⟩) (fun hxJ ↦ ⟨hx, hxJ⟩)
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      ext x
      have hA := (BooleanSlices.mem_booleanSlice.mp p.1.2).1
      have hB := (BooleanSlices.mem_booleanSlice.mp p.2.2).1
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxB, hxI⟩
        · exact hxA
        · exact False.elim (Finset.disjoint_left.mp hdisjoint hxI (hB hxB))
      · intro hxA
        exact ⟨Or.inl hxA, hA hxA⟩
    · apply Subtype.ext
      ext x
      have hA := (BooleanSlices.mem_booleanSlice.mp p.1.2).1
      have hB := (BooleanSlices.mem_booleanSlice.mp p.2.2).1
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxB, hxJ⟩
        · exact False.elim (Finset.disjoint_left.mp hdisjoint (hA hxA) hxJ)
        · exact hxB
      · intro hxB
        exact ⟨Or.inr hxB, hB hxB⟩

/-- The number of selected coordinates in the first part of a partition,
viewed as a finite statistic on a global `k`-slice. -/
def booleanSlicePartitionCount
    {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (k : ℕ)
    (S : BooleanSlices.BooleanSlicePoint (Finset.univ : Finset α) k) :
    Fin (k + 1) :=
  ⟨(S.1 ∩ I).card, by
    have hle : (S.1 ∩ I).card ≤ S.1.card :=
      Finset.card_le_card Finset.inter_subset_left
    have hcard := (BooleanSlices.mem_booleanSlice.mp S.2).2
    omega⟩

/-- The subtype fiber of `booleanSlicePartitionCount` is the explicit
partition fiber used above. -/
def booleanSlicePartitionCountFiberEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (k : ℕ) (a : Fin (k + 1)) :
    {S : BooleanSlices.BooleanSlicePoint (Finset.univ : Finset α) k //
        booleanSlicePartitionCount I k S = a} ≃
      BooleanSlicePartitionFiber I k a.1 where
  toFun S := ⟨S.1, by
    have h := congrArg Fin.val S.2
    simpa only [booleanSlicePartitionCount] using h⟩
  invFun S := ⟨S.1, by
    apply Fin.ext
    simpa only [booleanSlicePartitionCount] using S.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A nonempty cardinality fiber of a global slice is uniformly equivalent
to the corresponding product of the two conditioned slices. -/
def booleanSlicePartitionProductEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (I J : Finset α) (k : ℕ) (a : Fin (k + 1))
    (hcover : I ∪ J = Finset.univ) (hdisjoint : Disjoint I J) :
    {S : BooleanSlices.BooleanSlicePoint (Finset.univ : Finset α) k //
        booleanSlicePartitionCount I k S = a} ≃
      BooleanSlices.BooleanSlicePoint I a.1 ×
        BooleanSlices.BooleanSlicePoint J (k - a.1) :=
  (booleanSlicePartitionCountFiberEquiv I k a).trans
    (booleanSlicePartitionFiberEquiv I J k a.1 (Nat.lt_succ_iff.mp a.2)
      hcover hdisjoint)

/-- Function-valued form of the conditional product-slice equivalence. -/
def booleanSlicePartitionBoolProductEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (I J : Finset α) (k : ℕ) (a : Fin (k + 1))
    (hcover : I ∪ J = Finset.univ) (hdisjoint : Disjoint I J) :
    {S : BooleanSlices.BooleanSlicePoint (Finset.univ : Finset α) k //
        booleanSlicePartitionCount I k S = a} ≃
      BoolSlice ↑I a.1 × BoolSlice ↑J (k - a.1) :=
  (booleanSlicePartitionProductEquiv I J k a hcover hdisjoint).trans
    ((boolSliceEquivBooleanSlicePoint I a.1).prodCongr
      (boolSliceEquivBooleanSlicePoint J (k - a.1))).symm

/-- A finite expectation is bounded when every nonempty fiber of a finite
statistic has the same norm bound.  This is the exact finite conditioning
principle used to average Claim 8.5 over the possible sizes of the `I`-part. -/
theorem norm_finExpectation_le_of_fiberwise
    {Ω κ : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype κ] [DecidableEq κ]
    (f : Ω → ℂ) (d : Ω → κ) (B : ℝ)
    (h : ∀ a,
      0 < (Finset.univ.filter (fun ω ↦ d ω = a)).card →
        ‖(∑ ω ∈ Finset.univ.filter (fun ω ↦ d ω = a), f ω) /
            ((Finset.univ.filter (fun ω ↦ d ω = a)).card : ℂ)‖ ≤ B) :
    ‖finExpectation Ω f‖ ≤ B := by
  classical
  let F : κ → Finset Ω := fun a ↦
    Finset.univ.filter (fun ω ↦ d ω = a)
  have hsum : (∑ a, ∑ ω ∈ F a, f ω) = ∑ ω, f ω := by
    simpa only [F] using Finset.sum_fiberwise (Finset.univ : Finset Ω) d f
  have hfiber : ∀ a, ‖∑ ω ∈ F a, f ω‖ ≤ (F a).card * B := by
    intro a
    by_cases ha : (F a).card = 0
    · have hF : F a = ∅ := Finset.card_eq_zero.mp ha
      simp [hF]
    · have haPos : 0 < (F a).card := Nat.pos_of_ne_zero ha
      have havg := h a (by simpa only [F] using haPos)
      rw [norm_div, Complex.norm_natCast] at havg
      have hcardPos : (0 : ℝ) < (F a).card := by exact_mod_cast haPos
      have hmul := (div_le_iff₀ hcardPos).mp havg
      simpa only [F, mul_comm] using hmul
  have htotal : ‖∑ ω, f ω‖ ≤ (Fintype.card Ω : ℝ) * B := by
    rw [← hsum]
    calc
      ‖∑ a, ∑ ω ∈ F a, f ω‖ ≤ ∑ a, ‖∑ ω ∈ F a, f ω‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a, (F a).card * B :=
        Finset.sum_le_sum (fun a _ ↦ hfiber a)
      _ = (Fintype.card Ω : ℝ) * B := by
        rw [← Finset.sum_mul]
        congr 1
        have hnat : ∑ a, (F a).card = Fintype.card Ω := by
          simpa only [F, Finset.mem_univ, Finset.filter_true,
            Finset.card_univ] using
            (Finset.sum_card_fiberwise_eq_card_filter
              (Finset.univ : Finset Ω) (Finset.univ : Finset κ) d)
        exact_mod_cast hnat
  rw [finExpectation, norm_div, Complex.norm_natCast]
  have hcardPos : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ hcardPos).2 (by simpa [mul_comm] using htotal)

/-- Squared-norm form of finite conditioning.  The explicit `Nonempty`
argument lets each conditional expectation use the canonical finite subtype
without assuming that empty fibers exist as probability spaces. -/
theorem norm_finExpectation_sq_le_of_fiberwise
    {Ω κ : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype κ] [DecidableEq κ]
    (f : Ω → ℂ) (d : Ω → κ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ a (ha : Nonempty {ω : Ω // d ω = a}),
      ‖@finExpectation {ω : Ω // d ω = a} inferInstance ha
          ℂ inferInstance (fun ω ↦ f ω.1)‖ ^ 2 ≤ B) :
    ‖finExpectation Ω f‖ ^ 2 ≤ B := by
  have hglobal : ‖finExpectation Ω f‖ ≤ Real.sqrt B := by
    apply norm_finExpectation_le_of_fiberwise f d (Real.sqrt B)
    intro a hpos
    have hω : ∃ ω : Ω, d ω = a := by
      obtain ⟨ω, hω⟩ := Finset.card_pos.mp hpos
      exact ⟨ω, by simpa using hω⟩
    let : Nonempty {ω : Ω // d ω = a} :=
      ⟨⟨Classical.choose hω, Classical.choose_spec hω⟩⟩
    have heq :
        (∑ ω ∈ Finset.univ.filter (fun ω ↦ d ω = a), f ω) /
            ((Finset.univ.filter (fun ω ↦ d ω = a)).card : ℂ) =
          finExpectation {ω : Ω // d ω = a} (fun ω ↦ f ω.1) := by
      classical
      rw [finExpectation]
      congr 1
      · rw [← Finset.sum_subtype
            (Finset.univ.filter (fun ω ↦ d ω = a)) (by simp) f]
      · norm_cast
        rw [Fintype.card_subtype]
    rw [heq]
    have hcond := h a inferInstance
    nlinarith [Real.sq_sqrt hB,
      norm_nonneg
        (finExpectation {ω : Ω // d ω = a} (fun ω ↦ f ω.1)),
      Real.sqrt_nonneg B]
  nlinarith [Real.sq_sqrt hB, norm_nonneg (finExpectation Ω f),
    Real.sqrt_nonneg B]

/-- Conditional Jensen with an exceptional set of fibers.  When the input
has pointwise norm at most one, a squared-norm bound `B` on every good
conditional expectation loses only the probability of the bad statistic. -/
theorem norm_finExpectation_sq_le_of_fiberwise_except
    {Ω κ : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype κ] [DecidableEq κ]
    (f : Ω → ℂ) (d : Ω → κ) (Bad : κ → Prop)
    [DecidablePred Bad] (B eps : ℝ) (hB : 0 ≤ B)
    (hnorm : ∀ ω, ‖f ω‖ ≤ 1)
    (hgood : ∀ a (ha : Nonempty {ω : Ω // d ω = a}), ¬Bad a →
      ‖@finExpectation {ω : Ω // d ω = a} inferInstance ha
          ℂ inferInstance (fun ω ↦ f ω.1)‖ ^ 2 ≤ B)
    (hbad : finProbability Ω (fun ω ↦ Bad (d ω)) ≤ eps) :
    ‖finExpectation Ω f‖ ^ 2 ≤ B + eps := by
  classical
  let F : κ → Finset Ω := fun a ↦
    Finset.univ.filter (fun ω ↦ d ω = a)
  let avg : κ → ℂ := fun a ↦
    (∑ ω ∈ F a, f ω) / ((F a).card : ℂ)
  have havg_norm : ∀ a, ‖avg a‖ ≤ 1 := by
    intro a
    by_cases ha : (F a).card = 0
    · have hF : F a = ∅ := Finset.card_eq_zero.mp ha
      simp [avg, hF]
    · have haPos : 0 < (F a).card := Nat.pos_of_ne_zero ha
      dsimp only [avg]
      rw [norm_div, Complex.norm_natCast]
      apply (div_le_iff₀ (by exact_mod_cast haPos)).2
      calc
        ‖∑ ω ∈ F a, f ω‖ ≤ ∑ ω ∈ F a, ‖f ω‖ := norm_sum_le _ _
        _ ≤ ∑ _ω ∈ F a, (1 : ℝ) :=
          Finset.sum_le_sum (fun ω _ ↦ hnorm ω)
        _ = 1 * (F a).card := by simp
  have havg_good : ∀ a (ha : Nonempty {ω : Ω // d ω = a}),
      ¬Bad a → ‖avg a‖ ^ 2 ≤ B := by
    intro a ha hnot
    have heq : avg a =
        @finExpectation {ω : Ω // d ω = a} inferInstance ha
          ℂ inferInstance (fun ω ↦ f ω.1) := by
      dsimp only [avg]
      rw [finExpectation]
      congr 1
      · rw [← Finset.sum_subtype (F a) (by simp [F]) f]
      · norm_cast
        rw [Fintype.card_subtype]
    rw [heq]
    exact hgood a ha hnot
  have hmean : finExpectation Ω (fun ω ↦ avg (d ω)) =
      finExpectation Ω f := by
    rw [finExpectation, finExpectation]
    congr 1
    have hsum : (∑ a, ∑ ω ∈ F a, f ω) = ∑ ω, f ω := by
      simpa only [F] using
        Finset.sum_fiberwise (Finset.univ : Finset Ω) d f
    rw [← hsum]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset Ω) d
      (fun ω ↦ avg (d ω))]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : (F a).card = 0
    · have hF : F a = ∅ := Finset.card_eq_zero.mp ha
      simp [F, hF]
    · have hd : ∀ ω ∈ F a, d ω = a := by
        intro ω hω
        simpa [F] using hω
      calc
        (∑ ω ∈ F a, avg (d ω)) = ∑ ω ∈ F a, avg a := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [hd ω hω]
        _ = ((F a).card : ℂ) * avg a := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ ω ∈ F a, f ω := by
          dsimp only [avg]
          have hcardC : ((F a).card : ℂ) ≠ 0 := by exact_mod_cast ha
          field_simp
  calc
    ‖finExpectation Ω f‖ ^ 2 =
        ‖finExpectation Ω (fun ω ↦ avg (d ω))‖ ^ 2 := by rw [hmean]
    _ ≤ finExpectation Ω (fun ω ↦ ‖avg (d ω)‖ ^ 2) := by
      simpa [finExpectation] using
        norm_finExpectation_sq_le Ω (fun ω ↦ avg (d ω))
    _ ≤ B + eps := by
      apply finExpectation_le_add_probability Ω
        (fun ω ↦ ‖avg (d ω)‖ ^ 2) (fun ω ↦ Bad (d ω)) hB
      · intro ω
        nlinarith [havg_norm (d ω), norm_nonneg (avg (d ω))]
      · intro ω hω
        have ha : Nonempty {u : Ω // d u = d ω} := ⟨⟨ω, rfl⟩⟩
        exact havg_good (d ω) ha hω
      · exact hbad

/-- Finite conditioning specialized to a two-part partition of a Boolean
slice.  A uniform squared characteristic-function bound on every nonempty
conditional product slice gives the same bound before conditioning. -/
theorem norm_finCharFun_sq_le_of_partition
    {α : Type*} [Fintype α] [DecidableEq α]
    (I J : Finset α) (k : ℕ)
    [Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset α) k)]
    (hcover : I ∪ J = Finset.univ) (hdisjoint : Disjoint I J)
    (X : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset α) k → ℝ)
    (t B : ℝ) (hB : 0 ≤ B)
    (h : ∀ (a : Fin (k + 1))
      (ha : Nonempty (BooleanSlices.BooleanSlicePoint I a.1 ×
        BooleanSlices.BooleanSlicePoint J (k - a.1))),
      ‖@finCharFun
          (BooleanSlices.BooleanSlicePoint I a.1 ×
            BooleanSlices.BooleanSlicePoint J (k - a.1))
          inferInstance ha
          (fun p ↦ X ((booleanSlicePartitionProductEquiv I J k a
            hcover hdisjoint).symm p).1) t‖ ^ 2 ≤ B) :
    ‖finCharFun
        (BooleanSlices.BooleanSlicePoint (Finset.univ : Finset α) k)
        X t‖ ^ 2 ≤ B := by
  classical
  unfold finCharFun
  apply norm_finExpectation_sq_le_of_fiberwise _
    (booleanSlicePartitionCount I k) B hB
  intro a ha
  let Fiber := {S : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset α) k //
    booleanSlicePartitionCount I k S = a}
  let Product := BooleanSlices.BooleanSlicePoint I a.1 ×
    BooleanSlices.BooleanSlicePoint J (k - a.1)
  let e : Fiber ≃ Product :=
    booleanSlicePartitionProductEquiv I J k a hcover hdisjoint
  let : Nonempty Product := Nonempty.map e ha
  let g : Product → ℂ := fun p ↦
    Complex.exp ((t * X (e.symm p).1 : ℝ) * Complex.I)
  have heq :
      finExpectation Fiber
          (fun S ↦ Complex.exp ((t * X S.1 : ℝ) * Complex.I)) =
        finExpectation Product g := by
    have hfun :
        (fun S : Fiber ↦ Complex.exp ((t * X S.1 : ℝ) * Complex.I)) =
          (fun S ↦ g (e S)) := by
      funext S
      simp only [g, Equiv.symm_apply_apply]
    rw [hfun]
    exact finExpectation_equiv Fiber Product e g
  rw [heq]
  have hcond := h a inferInstance
  change ‖finExpectation Product g‖ ^ 2 ≤ B
  simpa only [finCharFun, Product, g, e] using hcond

/-- Function-valued Boolean-slice form of the preceding conditioning
principle, matching the Fourier formulation of Claim 8.5. -/
theorem norm_finCharFun_sq_le_of_partition_boolSlices
    {α : Type*} [Fintype α] [DecidableEq α]
    (I J : Finset α) (k : ℕ)
    [Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset α) k)]
    (hcover : I ∪ J = Finset.univ) (hdisjoint : Disjoint I J)
    (X : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset α) k → ℝ)
    (t B : ℝ) (hB : 0 ≤ B)
    (h : ∀ (a : Fin (k + 1))
      (ha : Nonempty (BoolSlice ↑I a.1 × BoolSlice ↑J (k - a.1))),
      ‖@finCharFun
          (BoolSlice ↑I a.1 × BoolSlice ↑J (k - a.1))
          inferInstance ha
          (fun p ↦ X ((booleanSlicePartitionBoolProductEquiv I J k a
            hcover hdisjoint).symm p).1) t‖ ^ 2 ≤ B) :
    ‖finCharFun
        (BooleanSlices.BooleanSlicePoint (Finset.univ : Finset α) k)
        X t‖ ^ 2 ≤ B := by
  classical
  unfold finCharFun
  apply norm_finExpectation_sq_le_of_fiberwise _
    (booleanSlicePartitionCount I k) B hB
  intro a ha
  let Fiber := {S : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset α) k //
    booleanSlicePartitionCount I k S = a}
  let Product := BoolSlice ↑I a.1 × BoolSlice ↑J (k - a.1)
  let e : Fiber ≃ Product :=
    booleanSlicePartitionBoolProductEquiv I J k a hcover hdisjoint
  let : Nonempty Product := Nonempty.map e ha
  let g : Product → ℂ := fun p ↦
    Complex.exp ((t * X (e.symm p).1 : ℝ) * Complex.I)
  have heq :
      finExpectation Fiber
          (fun S ↦ Complex.exp ((t * X S.1 : ℝ) * Complex.I)) =
        finExpectation Product g := by
    have hfun :
        (fun S : Fiber ↦ Complex.exp ((t * X S.1 : ℝ) * Complex.I)) =
          (fun S ↦ g (e S)) := by
      funext S
      simp only [g, Equiv.symm_apply_apply]
    rw [hfun]
    exact finExpectation_equiv Fiber Product e g
  rw [heq]
  have hcond := h a inferInstance
  change ‖finExpectation Product g‖ ^ 2 ≤ B
  simpa only [finCharFun, Product, g, e] using hcond

/-- Exceptional-fiber version of partition conditioning.  Bad cardinality
fibers contribute only their probability, while all other fibers are
transported to function-valued product slices. -/
theorem norm_finCharFun_sq_le_of_partition_boolSlices_except
    {α : Type*} [Fintype α] [DecidableEq α]
    (I J : Finset α) (k : ℕ)
    [Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset α) k)]
    (hcover : I ∪ J = Finset.univ) (hdisjoint : Disjoint I J)
    (X : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset α) k → ℝ)
    (t : ℝ) (Bad : Fin (k + 1) → Prop) [DecidablePred Bad]
    (B eps : ℝ) (hB : 0 ≤ B)
    (hgood : ∀ (a : Fin (k + 1))
      (ha : Nonempty (BoolSlice ↑I a.1 × BoolSlice ↑J (k - a.1))),
      ¬Bad a →
      ‖@finCharFun
          (BoolSlice ↑I a.1 × BoolSlice ↑J (k - a.1))
          inferInstance ha
          (fun p ↦ X ((booleanSlicePartitionBoolProductEquiv I J k a
            hcover hdisjoint).symm p).1) t‖ ^ 2 ≤ B)
    (hbad : finProbability
      (BooleanSlices.BooleanSlicePoint (Finset.univ : Finset α) k)
      (fun S ↦ Bad (booleanSlicePartitionCount I k S)) ≤ eps) :
    ‖finCharFun
        (BooleanSlices.BooleanSlicePoint (Finset.univ : Finset α) k)
        X t‖ ^ 2 ≤ B + eps := by
  classical
  unfold finCharFun
  apply norm_finExpectation_sq_le_of_fiberwise_except _
    (booleanSlicePartitionCount I k) Bad B eps hB
  · intro S
    rw [Complex.norm_exp]
    simp
  · intro a ha hnot
    let Fiber := {S : BooleanSlices.BooleanSlicePoint
        (Finset.univ : Finset α) k //
      booleanSlicePartitionCount I k S = a}
    let Product := BoolSlice ↑I a.1 × BoolSlice ↑J (k - a.1)
    let e : Fiber ≃ Product :=
      booleanSlicePartitionBoolProductEquiv I J k a hcover hdisjoint
    let : Nonempty Product := Nonempty.map e ha
    let g : Product → ℂ := fun p ↦
      Complex.exp ((t * X (e.symm p).1 : ℝ) * Complex.I)
    have heq :
        finExpectation Fiber
            (fun S ↦ Complex.exp ((t * X S.1 : ℝ) * Complex.I)) =
          finExpectation Product g := by
      have hfun :
          (fun S : Fiber ↦ Complex.exp ((t * X S.1 : ℝ) * Complex.I)) =
            (fun S ↦ g (e S)) := by
        funext S
        simp only [g, Equiv.symm_apply_apply]
      rw [hfun]
      exact finExpectation_equiv Fiber Product e g
    rw [heq]
    have hcond := hgood a inferInstance hnot
    change ‖finExpectation Product g‖ ^ 2 ≤ B
    simpa only [finCharFun, Product, g, e] using hcond
  · exact hbad

/-- Degrees split additively over disjoint finite sets. -/
lemma degreeInto_union_of_disjoint_lemma81
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) {A B : Finset V} (hAB : Disjoint A B) :
    AKSGraph.degreeInto G v (A ∪ B) =
      AKSGraph.degreeInto G v A + AKSGraph.degreeInto G v B := by
  classical
  rw [AKSGraph.degreeInto, AKSGraph.degreeInto, AKSGraph.degreeInto]
  have hinter : G.neighborFinset v ∩ (A ∪ B) =
      (G.neighborFinset v ∩ A) ∪ (G.neighborFinset v ∩ B) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    aesop
  rw [hinter, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x hxA hxB
  exact Finset.disjoint_left.mp hAB
    (Finset.mem_inter.mp hxA).2 (Finset.mem_inter.mp hxB).2

/-- Induced edges in a disjoint union split into the two internal counts
and the cross-degrees.  This local form avoids importing the later switching
development into the quadratic-cancellation module. -/
lemma edgeCount_union_of_disjoint_lemma81
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B : Finset V} (hAB : Disjoint A B) :
    AKSGraph.edgeCount G (A ∪ B) = AKSGraph.edgeCount G A +
      AKSGraph.edgeCount G B + ∑ v ∈ B, AKSGraph.degreeInto G v A := by
  classical
  revert hAB
  induction B using Finset.induction_on with
  | empty =>
      intro _
      simp [AKSGraph.edgeCount]
  | @insert v B hv ih =>
      intro hAB
      have hvA : v ∉ A := by
        intro hvA
        exact Finset.disjoint_left.mp hAB hvA (Finset.mem_insert_self v B)
      have hAB' : Disjoint A B := hAB.mono_right (Finset.subset_insert v B)
      have hvUnion : v ∉ A ∪ B := by simp [hv, hvA]
      calc
        AKSGraph.edgeCount G (A ∪ insert v B) =
            AKSGraph.edgeCount G (insert v (A ∪ B)) := by
          congr 2
          ext x
          simp
        _ = AKSGraph.edgeCount G (A ∪ B) +
            AKSGraph.degreeInto G v (A ∪ B) :=
          AKSGraph.edgeCount_insert G v (A ∪ B) hvUnion
        _ = (AKSGraph.edgeCount G A + AKSGraph.edgeCount G B +
              ∑ x ∈ B, AKSGraph.degreeInto G x A) +
            (AKSGraph.degreeInto G v A + AKSGraph.degreeInto G v B) := by
          rw [ih hAB', degreeInto_union_of_disjoint_lemma81 G v hAB']
        _ = AKSGraph.edgeCount G A +
              AKSGraph.edgeCount G (insert v B) +
              ∑ x ∈ insert v B, AKSGraph.degreeInto G x A := by
          rw [AKSGraph.edgeCount_insert G v B hv, Finset.sum_insert hv]
          omega

/-- The two local induced-edge counters use the same filtered edge set;
this lemma bridges their (possibly different) decidability instances. -/
lemma inducedEdgeCount_eq_edgeCount_lemma81
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Probability.inducedEdgeCount G S = AKSGraph.edgeCount G S := by
  unfold Probability.inducedEdgeCount AKSGraph.edgeCount
  congr 1
  ext e
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]

/-- The real indicator of graph adjacency. -/
noncomputable def lemma81AdjacencyIndicator
    {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) : ℝ := by
  classical
  exact if G.Adj i j then 1 else 0

/-- The adjacency matrix across the two parts of a Lemma 8.2 witness. -/
noncomputable def lemma81CrossMatrix
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize) : ↑w.I → ↑w.J → ℝ :=
  fun i j ↦ lemma81AdjacencyIndicator G i.1 j.1

/-- The adjacency sum against a Boolean slice is the graph degree into its
ambient positive-coordinate set. -/
lemma degreeInto_boolSliceSupport
    {n ell : ℕ} (G : SimpleGraph (Fin n)) (J : Finset (Fin n))
    (y : BoolSlice ↑J ell) (v : Fin n) :
    (AKSGraph.degreeInto G v
        ((boolSliceEquivBooleanSlicePoint J ell y).1 ∩ J) : ℝ) =
      ∑ j : ↑J, lemma81AdjacencyIndicator G v j.1 *
        boolIndicator (y.1 j) := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  rw [Finset.inter_eq_left.mpr
    (BooleanSlices.mem_booleanSlice.mp
      (boolSliceEquivBooleanSlicePoint J ell y).2).1]
  rw [AKSGraph.degreeInto_eq_sum]
  have hsupport : (boolSliceEquivBooleanSlicePoint J ell y).1 =
      ((Finset.univ : Finset ↑J).filter fun j ↦ y.1 j).map
        (Function.Embedding.subtype _) := rfl
  rw [hsupport]
  push_cast
  rw [Finset.sum_map, Finset.sum_filter]
  simp [lemma81AdjacencyIndicator, boolIndicator]
  rfl

/-- The bilinear adjacency term is the sum of degrees from the selected
`I`-vertices into the selected `J`-vertices. -/
lemma crossTerm_eq_sum_degreeInto_boolSliceSupport
    {n q familySize s ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (x : BoolSlice ↑w.I s) (y : BoolSlice ↑w.J ell) :
    (∑ i : ↑w.I, ∑ j : ↑w.J,
        lemma81CrossMatrix w i j * boolIndicator (x.1 i) *
          boolIndicator (y.1 j)) =
      ∑ v ∈ boolSliceSupport w.I s x,
        (AKSGraph.degreeInto G v (boolSliceSupport w.J ell y) : ℝ) := by
  classical
  calc
    (∑ i : ↑w.I, ∑ j : ↑w.J,
        lemma81CrossMatrix w i j * boolIndicator (x.1 i) *
          boolIndicator (y.1 j)) =
        ∑ i : ↑w.I,
          (AKSGraph.degreeInto G i.1 (boolSliceSupport w.J ell y) : ℝ) *
            boolIndicator (x.1 i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hdegree := degreeInto_boolSliceSupport G w.J y i.1
      change (AKSGraph.degreeInto G i.1
          (boolSliceSupport w.J ell y ∩ w.J) : ℝ) = _ at hdegree
      rw [Finset.inter_eq_left.mpr (boolSliceSupport_subset w.J ell y)] at hdegree
      rw [hdegree]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      change lemma81AdjacencyIndicator G i.1 j.1 * _ * _ = _
      ring
    _ = _ := sum_boolIndicator_eq_sum_boolSliceSupport w.I s x
      (fun v ↦ (AKSGraph.degreeInto G v (boolSliceSupport w.J ell y) : ℝ))

/-- The part of a perturbed edge polynomial depending only on the selected
`I`-slice, including the global constant term. -/
noncomputable def lemma81PureI
    {n q familySize s : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {beta : ℝ}
    (w : Lemma82Witness G beta q familySize) (e₀ : ℝ) (c : Fin n → ℝ)
    (x : BoolSlice ↑w.I s) : ℝ :=
  e₀ + Probability.edgePolynomial G (boolSliceSupport w.I s x) +
    ∑ i : ↑w.I, c i.1 * boolIndicator (x.1 i)

/-- The part of a perturbed edge polynomial depending only on the selected
`J`-slice. -/
noncomputable def lemma81PureJ
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {beta : ℝ}
    (w : Lemma82Witness G beta q familySize) (c : Fin n → ℝ)
    (y : BoolSlice ↑w.J ell) : ℝ :=
  Probability.edgePolynomial G (boolSliceSupport w.J ell y) +
    ∑ j : ↑w.J, c j.1 * boolIndicator (y.1 j)

/-- On a conditioned product slice, the original linearly perturbed edge
polynomial is exactly the split quadratic polynomial used in Claim 8.5. -/
lemma perturbedEdgePolynomial_boolSliceSupport_union
    {n q familySize s ell : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {beta : ℝ}
    (w : Lemma82Witness G beta q familySize) (e₀ : ℝ) (c : Fin n → ℝ)
    (x : BoolSlice ↑w.I s) (y : BoolSlice ↑w.J ell) :
    Probability.perturbedEdgePolynomial G e₀ c
        (boolSliceSupport w.I s x ∪ boolSliceSupport w.J ell y) =
      splitQuadraticValue (lemma81PureI w e₀ c) (lemma81PureJ w c)
        (lemma81CrossMatrix w) x y := by
  classical
  let XI := boolSliceSupport w.I s x
  let YJ := boolSliceSupport w.J ell y
  have hXY : Disjoint XI YJ :=
    w.disjoint.mono (boolSliceSupport_subset w.I s x)
      (boolSliceSupport_subset w.J ell y)
  have hedgeNat :
      AKSGraph.edgeCount G (XI ∪ YJ) =
        AKSGraph.edgeCount G XI + AKSGraph.edgeCount G YJ +
          ∑ v ∈ XI, AKSGraph.degreeInto G v YJ := by
    rw [Finset.union_comm]
    simpa only [add_comm] using
      (edgeCount_union_of_disjoint_lemma81 G hXY.symm)
  have hedge :
      Probability.edgePolynomial G (XI ∪ YJ) =
        Probability.edgePolynomial G XI + Probability.edgePolynomial G YJ +
          ∑ v ∈ XI, (AKSGraph.degreeInto G v YJ : ℝ) := by
    rw [Probability.edgePolynomial_eq_inducedEdgeCount,
      Probability.edgePolynomial_eq_inducedEdgeCount,
      Probability.edgePolynomial_eq_inducedEdgeCount]
    rw [inducedEdgeCount_eq_edgeCount_lemma81,
      inducedEdgeCount_eq_edgeCount_lemma81,
      inducedEdgeCount_eq_edgeCount_lemma81]
    exact_mod_cast hedgeNat
  have hcross :
      (∑ i : ↑w.I, ∑ j : ↑w.J,
          lemma81CrossMatrix w i j * boolIndicator (x.1 i) *
            boolIndicator (y.1 j)) =
        ∑ v ∈ XI, (AKSGraph.degreeInto G v YJ : ℝ) := by
    exact crossTerm_eq_sum_degreeInto_boolSliceSupport w x y
  have hlinI :
      (∑ i : ↑w.I, c i.1 * boolIndicator (x.1 i)) =
        ∑ v ∈ XI, c v :=
    sum_boolIndicator_eq_sum_boolSliceSupport w.I s x c
  have hlinJ :
      (∑ j : ↑w.J, c j.1 * boolIndicator (y.1 j)) =
        ∑ v ∈ YJ, c v :=
    sum_boolIndicator_eq_sum_boolSliceSupport w.J ell y c
  have hlin :
      (∑ v, c v * Probability.bit v (XI ∪ YJ)) =
        (∑ i : ↑w.I, c i.1 * boolIndicator (x.1 i)) +
          ∑ j : ↑w.J, c j.1 * boolIndicator (y.1 j) := by
    calc
      (∑ v, c v * Probability.bit v (XI ∪ YJ)) =
          ∑ v ∈ XI ∪ YJ, c v := by
        simp only [Probability.bit, mul_ite, mul_one, mul_zero]
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext v
          simp
        · intro v _
          rfl
      _ = (∑ v ∈ XI, c v) + ∑ v ∈ YJ, c v :=
        Finset.sum_union hXY
      _ = _ := by rw [← hlinI, ← hlinJ]
  change Probability.perturbedEdgePolynomial G e₀ c (XI ∪ YJ) = _
  rw [Probability.perturbedEdgePolynomial, hedge, hlin]
  change _ = lemma81PureI w e₀ c x + lemma81PureJ w c y + _
  rw [hcross]
  unfold lemma81PureI lemma81PureJ
  ring

/-- Pulling a perturbed edge polynomial through the conditional product
equivalence produces exactly its split quadratic form. -/
lemma perturbedEdgePolynomial_partitionBoolProduct
    {n q familySize k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {beta : ℝ} (w : Lemma82Witness G beta q familySize)
    (a : Fin (k + 1)) (e₀ : ℝ) (c : Fin n → ℝ)
    (p : BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1)) :
    Probability.perturbedEdgePolynomial G e₀ c
        ((booleanSlicePartitionBoolProductEquiv w.I w.J k a
          w.partition w.disjoint).symm p).1.1 =
      splitQuadraticValue (lemma81PureI w e₀ c) (lemma81PureJ w c)
        (lemma81CrossMatrix w) p.1 p.2 := by
  let e := booleanSlicePartitionBoolProductEquiv w.I w.J k a
    w.partition w.disjoint
  have hval : (e.symm p).1.1 =
      boolSliceSupport w.I a.1 p.1 ∪
        boolSliceSupport w.J (k - a.1) p.2 := by
    rfl
  rw [hval]
  exact perturbedEdgePolynomial_boolSliceSupport_union w e₀ c p.1 p.2

/-- The outer conditioning step for the original perturbed edge polynomial:
it suffices to prove the same squared characteristic-function bound for the
split polynomial on every nonempty conditioned product slice. -/
theorem norm_perturbedEdgePolynomial_booleanSlice_sq_le_of_split
    {n q familySize k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {beta : ℝ} (w : Lemma82Witness G beta q familySize)
    [Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) k)]
    (e₀ : ℝ) (c : Fin n → ℝ) (t B : ℝ) (hB : 0 ≤ B)
    (h : ∀ (a : Fin (k + 1))
      (ha : Nonempty (BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1))),
      ‖@finCharFun
          (BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1))
          inferInstance ha
          (fun p ↦ splitQuadraticValue
            (lemma81PureI w e₀ c) (lemma81PureJ w c)
            (lemma81CrossMatrix w) p.1 p.2) t‖ ^ 2 ≤ B) :
    ‖finCharFun
        (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)
        (fun S ↦ Probability.perturbedEdgePolynomial G e₀ c S.1) t‖ ^ 2 ≤ B := by
  apply norm_finCharFun_sq_le_of_partition_boolSlices w.I w.J k
    w.partition w.disjoint
    (fun S ↦ Probability.perturbedEdgePolynomial G e₀ c S.1)
    t B hB
  intro a ha
  let : Nonempty (BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1)) := ha
  have hfun :
      (fun p : BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1) ↦
        Probability.perturbedEdgePolynomial G e₀ c
          ((booleanSlicePartitionBoolProductEquiv w.I w.J k a
            w.partition w.disjoint).symm p).1.1) =
      (fun p ↦ splitQuadraticValue
        (lemma81PureI w e₀ c) (lemma81PureJ w c)
        (lemma81CrossMatrix w) p.1 p.2) := by
    funext p
    exact perturbedEdgePolynomial_partitionBoolProduct w a e₀ c p
  rw [hfun]
  exact h a ha

/-- Exceptional-cardinality version of the outer perturbed-edge wrapper. -/
theorem norm_perturbedEdgePolynomial_booleanSlice_sq_le_of_split_except
    {n q familySize k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {beta : ℝ} (w : Lemma82Witness G beta q familySize)
    [Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) k)]
    (e₀ : ℝ) (c : Fin n → ℝ) (t : ℝ)
    (Bad : Fin (k + 1) → Prop) [DecidablePred Bad]
    (B eps : ℝ) (hB : 0 ≤ B)
    (hgood : ∀ (a : Fin (k + 1))
      (ha : Nonempty (BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1))),
      ¬Bad a →
      ‖@finCharFun
          (BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1))
          inferInstance ha
          (fun p ↦ splitQuadraticValue
            (lemma81PureI w e₀ c) (lemma81PureJ w c)
            (lemma81CrossMatrix w) p.1 p.2) t‖ ^ 2 ≤ B)
    (hbad : finProbability
      (BooleanSlices.BooleanSlicePoint
        (Finset.univ : Finset (Fin n)) k)
      (fun S ↦ Bad (booleanSlicePartitionCount w.I k S)) ≤ eps) :
    ‖finCharFun
        (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)
        (fun S ↦ Probability.perturbedEdgePolynomial G e₀ c S.1) t‖ ^ 2 ≤
      B + eps := by
  apply norm_finCharFun_sq_le_of_partition_boolSlices_except w.I w.J k
    w.partition w.disjoint
    (fun S ↦ Probability.perturbedEdgePolynomial G e₀ c S.1)
    t Bad B eps hB
  · intro a ha hnot
    let : Nonempty (BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1)) := ha
    have hfun :
        (fun p : BoolSlice ↑w.I a.1 × BoolSlice ↑w.J (k - a.1) ↦
          Probability.perturbedEdgePolynomial G e₀ c
            ((booleanSlicePartitionBoolProductEquiv w.I w.J k a
              w.partition w.disjoint).symm p).1.1) =
        (fun p ↦ splitQuadraticValue
          (lemma81PureI w e₀ c) (lemma81PureJ w c)
          (lemma81CrossMatrix w) p.1 p.2) := by
      funext p
      exact perturbedEdgePolynomial_partitionBoolProduct w a e₀ c p
    rw [hfun]
    exact hgood a ha hnot
  · exact hbad

/-- For the adjacency cross matrix, the coefficient left by two-copy
decoupling is exactly the difference of the two graph degrees. -/
lemma crossSliceCoefficient_lemma81CrossMatrix
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (y z : BoolSlice ↑w.J ell) (i : ↑w.I) :
    crossSliceCoefficient (lemma81CrossMatrix w) y.1 z.1 i =
      (AKSGraph.degreeInto G i.1
          ((boolSliceEquivBooleanSlicePoint w.J ell y).1 ∩ w.J) : ℝ) -
        (AKSGraph.degreeInto G i.1
          ((boolSliceEquivBooleanSlicePoint w.J ell z).1 ∩ w.J) : ℝ) := by
  classical
  rw [crossSliceCoefficient]
  calc
    (∑ j, lemma81CrossMatrix w i j *
        (boolIndicator (y.1 j) - boolIndicator (z.1 j))) =
        (∑ j, lemma81CrossMatrix w i j * boolIndicator (y.1 j)) -
          ∑ j, lemma81CrossMatrix w i j * boolIndicator (z.1 j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [degreeInto_boolSliceSupport G w.J y,
        degreeInto_boolSliceSupport G w.J z]
      rfl

/-- The degree event from Lemma 8.3 on an arbitrary sampling set. -/
def lemma83DegreeEventOn
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (I : Finset (Fin n)) (a : Fin familySize)
    (tau delta : ℝ) (x : Fin q → ℝ) (r : Fin q)
    (U : BooleanSlices.BooleanSlicePoint I ell) : Prop :=
  RLCD.distToInt
    (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
        (U.1 ∩ w.J) : ℝ) -
      tau * (AKSGraph.degreeInto G (w.tuple a 0)
        (U.1 ∩ w.J) : ℝ) + x r) ≤ delta

lemma lemma83DegreePrefixOn_invariant
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (I : Finset (Fin n)) (a : Fin familySize)
    (tau delta : ℝ) (x : Fin q → ℝ)
    (k : Fin q) (b : Lemma83BlockPair w a k.succ)
    (U V : BooleanSlices.BooleanSlicePoint I ell)
    (hUV : U.1 \ (b.A ∪ b.B) = V.1 \ (b.A ∪ b.B)) :
    (U ∈ prefixEventFinset (lemma83DegreeEventOn w I a tau delta x) k.val ↔
      V ∈ prefixEventFinset (lemma83DegreeEventOn w I a tau delta x) k.val) := by
  classical
  simp only [prefixEventFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h r hr
    have hrk : r.succ < k.succ := Fin.succ_lt_succ_iff.mpr hr
    have h0k : (0 : Fin (q + 1)) < k.succ := Fin.succ_pos k
    have hUr := lemma83Blocks_prior_degree_eq_outside
      w a k.succ r.succ b.A b.B U.1 b.A_subset b.B_subset hrk
    have hVr := lemma83Blocks_prior_degree_eq_outside
      w a k.succ r.succ b.A b.B V.1 b.A_subset b.B_subset hrk
    have hU0 := lemma83Blocks_prior_degree_eq_outside
      w a k.succ 0 b.A b.B U.1 b.A_subset b.B_subset h0k
    have hV0 := lemma83Blocks_prior_degree_eq_outside
      w a k.succ 0 b.A b.B V.1 b.A_subset b.B_subset h0k
    have hdegR : AKSGraph.degreeInto G (w.tuple a r.succ) (U.1 ∩ w.J) =
        AKSGraph.degreeInto G (w.tuple a r.succ) (V.1 ∩ w.J) := by
      calc
        _ = AKSGraph.degreeInto G (w.tuple a r.succ)
            ((U.1 \ (b.A ∪ b.B)) ∩ w.J) := hUr
        _ = AKSGraph.degreeInto G (w.tuple a r.succ)
            ((V.1 \ (b.A ∪ b.B)) ∩ w.J) := by rw [hUV]
        _ = _ := hVr.symm
    have hdeg0 : AKSGraph.degreeInto G (w.tuple a 0) (U.1 ∩ w.J) =
        AKSGraph.degreeInto G (w.tuple a 0) (V.1 ∩ w.J) := by
      calc
        _ = AKSGraph.degreeInto G (w.tuple a 0)
            ((U.1 \ (b.A ∪ b.B)) ∩ w.J) := hU0
        _ = AKSGraph.degreeInto G (w.tuple a 0)
            ((V.1 \ (b.A ∪ b.B)) ∩ w.J) := by rw [hUV]
        _ = _ := hV0.symm
    simpa only [lemma83DegreeEventOn, hdegR, hdeg0] using h r hr
  · intro h r hr
    have hrk : r.succ < k.succ := Fin.succ_lt_succ_iff.mpr hr
    have h0k : (0 : Fin (q + 1)) < k.succ := Fin.succ_pos k
    have hUr := lemma83Blocks_prior_degree_eq_outside
      w a k.succ r.succ b.A b.B U.1 b.A_subset b.B_subset hrk
    have hVr := lemma83Blocks_prior_degree_eq_outside
      w a k.succ r.succ b.A b.B V.1 b.A_subset b.B_subset hrk
    have hU0 := lemma83Blocks_prior_degree_eq_outside
      w a k.succ 0 b.A b.B U.1 b.A_subset b.B_subset h0k
    have hV0 := lemma83Blocks_prior_degree_eq_outside
      w a k.succ 0 b.A b.B V.1 b.A_subset b.B_subset h0k
    have hdegR : AKSGraph.degreeInto G (w.tuple a r.succ) (V.1 ∩ w.J) =
        AKSGraph.degreeInto G (w.tuple a r.succ) (U.1 ∩ w.J) := by
      calc
        _ = AKSGraph.degreeInto G (w.tuple a r.succ)
            ((V.1 \ (b.A ∪ b.B)) ∩ w.J) := hVr
        _ = AKSGraph.degreeInto G (w.tuple a r.succ)
            ((U.1 \ (b.A ∪ b.B)) ∩ w.J) := by rw [hUV]
        _ = _ := hUr.symm
    have hdeg0 : AKSGraph.degreeInto G (w.tuple a 0) (V.1 ∩ w.J) =
        AKSGraph.degreeInto G (w.tuple a 0) (U.1 ∩ w.J) := by
      calc
        _ = AKSGraph.degreeInto G (w.tuple a 0)
            ((V.1 \ (b.A ∪ b.B)) ∩ w.J) := hV0
        _ = AKSGraph.degreeInto G (w.tuple a 0)
            ((U.1 \ (b.A ∪ b.B)) ∩ w.J) := by rw [hUV]
        _ = _ := hU0.symm
    simpa only [lemma83DegreeEventOn, hdegR, hdeg0] using h r hr

theorem lemma83DegreePrefixOn_probability_step
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (I : Finset (Fin n)) (hJI : w.J ⊆ I)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ I.card) (hm : 1 ≤ lemma83BlockSize n beta)
    (heta : 0 < eta) (hellower : eta * (I.card : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * I.card)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) (k : Fin q) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
          U ∈ prefixEventFinset
            (lemma83DegreeEventOn w I a tau delta x) (k.val + 1)) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + 1 /
              Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) / |tau|)) *
        Concentration.uniformProbability
          (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
            U ∈ prefixEventFinset
              (lemma83DegreeEventOn w I a tau delta x) k.val) +
      2 * Real.exp
        (-(eta * lemma83BlockSize n beta) ^ 2 /
          (8 * (2 * lemma83BlockSize n beta : ℕ))) := by
  classical
  let b := selectedLemma83BlockPair w a k.succ
  have hAinJ : b.A ⊆ w.J :=
    b.A_subset.trans Finset.inter_subset_right
  have hBinJ : b.B ⊆ w.J :=
    b.B_subset.trans Finset.inter_subset_right
  have hABinI : b.A ∪ b.B ⊆ I :=
    Finset.union_subset (hAinJ.trans hJI) (hBinJ.trans hJI)
  have hABcard : (b.A ∪ b.B).card =
      2 * lemma83BlockSize n beta := by
    rw [Finset.card_union_of_disjoint b.disjoint, b.card_A, b.card_B]
    omega
  have hstep := lemma83Blocks_oneStep_probability
    w a k.succ 0 (Fin.succ_pos k) I b.A b.B
      (lemma83BlockSize n beta) ell b.disjoint b.card_A b.card_B
      b.A_subset b.B_subset hABinI hell hm eta tau (x k) delta heta
      hellower hellupper htau hdelta hdeltaUpper
      (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
        U ∈ prefixEventFinset
          (lemma83DegreeEventOn w I a tau delta x) k.val)
      (lemma83DegreePrefixOn_invariant w I a tau delta x k b)
  rw [hABcard] at hstep
  have hevent :
      (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
        U ∈ prefixEventFinset
          (lemma83DegreeEventOn w I a tau delta x) (k.val + 1)) =
      (fun U ↦
        U ∈ prefixEventFinset
            (lemma83DegreeEventOn w I a tau delta x) k.val ∧
          lemma83DegreeEventOn w I a tau delta x k U) := by
    funext U
    apply propext
    exact mem_prefixEventFinset_succ
      (lemma83DegreeEventOn w I a tau delta x) k.isLt U
  rw [hevent]
  simpa only [lemma83DegreeEventOn] using hstep

theorem lemma83DegreePrefixOn_probability
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (I : Finset (Fin n)) (hJI : w.J ⊆ I)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ I.card) (hm : 1 ≤ lemma83BlockSize n beta)
    (heta : 0 < eta) (hellower : eta * (I.card : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * I.card)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
          U ∈ prefixEventFinset
            (lemma83DegreeEventOn w I a tau delta x) q) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + 1 /
              Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) / |tau|)) ^ q +
      (q : ℝ) *
        (2 * Real.exp
          (-(eta * lemma83BlockSize n beta) ^ 2 /
            (8 * (2 * lemma83BlockSize n beta : ℕ)))) := by
  let : Nonempty (BooleanSlices.BooleanSlicePoint I ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  let p : ℕ → ℝ := fun k ↦ Concentration.uniformProbability
    (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
      U ∈ prefixEventFinset
        (lemma83DegreeEventOn w I a tau delta x) k)
  let C : ℝ := 4096 / (eta / 2) *
    ((|tau| + delta) *
      (|tau| + 1 / Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) / |tau|)
  let eps : ℝ := 2 * Real.exp
    (-(eta * lemma83BlockSize n beta) ^ 2 /
      (8 * (2 * lemma83BlockSize n beta : ℕ)))
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    have htauAbs : 0 < |tau| := abs_pos.mpr htau
    positivity
  have heps : 0 ≤ eps := by dsimp only [eps]; positivity
  have hp0 : p 0 ≤ 1 := by
    dsimp only [p]
    exact Concentration.uniformProbability_le_one _
  have hstep : ∀ k < q, p (k + 1) ≤ C * p k + eps := by
    intro k hk
    have hs := lemma83DegreePrefixOn_probability_step
      w I hJI a tau delta eta x hell hm heta hellower hellupper htau
        hdelta hdeltaUpper ⟨k, hk⟩
    simpa only [p, C, eps] using hs
  by_cases hC1 : C ≤ 1
  · have hrec := affine_recurrence_le_pow_add p C eps q hC0 hC1 heps hp0 hstep
    simpa only [p, C, eps] using hrec
  · have hprob : p q ≤ 1 := by
      dsimp only [p]
      exact Concentration.uniformProbability_le_one _
    have hpow : 1 ≤ C ^ q := one_le_pow₀ (le_of_not_ge hC1)
    have herr : 0 ≤ (q : ℝ) * eps := mul_nonneg (by positivity) heps
    have hfinal : p q ≤ C ^ q + (q : ℝ) * eps := by linarith
    simpa only [p, C, eps] using hfinal

/-- Lemma 8.3 on a conditioned slice of an arbitrary sampling set. -/
theorem lemma83DegreeJointOn_probability
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (I : Finset (Fin n)) (hJI : w.J ⊆ I)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ I.card) (hm : 1 ≤ lemma83BlockSize n beta)
    (heta : 0 < eta) (hellower : eta * (I.card : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * I.card)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
          ∀ r : Fin q,
            RLCD.distToInt
              (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                  (U.1 ∩ w.J) : ℝ) -
                tau * (AKSGraph.degreeInto G (w.tuple a 0)
                  (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + 1 /
              Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) / |tau|)) ^ q +
      (q : ℝ) *
        (2 * Real.exp
          (-(eta * lemma83BlockSize n beta) ^ 2 /
            (8 * (2 * lemma83BlockSize n beta : ℕ)))) := by
  let E : Fin q → BooleanSlices.BooleanSlicePoint I ell → Prop :=
    lemma83DegreeEventOn w I a tau delta x
  have hevent :
      (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
        U ∈ prefixEventFinset E q) =
      (fun U ↦ ∀ r : Fin q,
        RLCD.distToInt
          (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
              (U.1 ∩ w.J) : ℝ) -
            tau * (AKSGraph.degreeInto G (w.tuple a 0)
              (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) := by
    funext U
    apply propext
    rw [mem_prefixEventFinset_full]
    rfl
  rw [← hevent]
  simpa only [E] using lemma83DegreePrefixOn_probability
    w I hJI a tau delta eta x hell hm heta hellower hellupper htau
      hdelta hdeltaUpper

/-- Source-scale normalization of the conditioned-slice Lemma 8.3 bound,
before absorbing the exponentially small residue imbalance. -/
theorem lemma83DegreeJointOn_probability_sourceScale_additive
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (I : Finset (Fin n)) (hJI : w.J ⊆ I)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ I.card) (hn : 1 ≤ n)
    (heta : 0 < eta) (hellower : eta * (I.card : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * I.card)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
          ∀ r : Fin q,
            RLCD.distToInt
              (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                  (U.1 ∩ w.J) : ℝ) -
                tau * (AKSGraph.degreeInto G (w.tuple a 0)
                  (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q +
      (q : ℝ) *
        (2 * Real.exp
          (-(eta * lemma83BlockSize n beta) ^ 2 /
            (8 * (2 * lemma83BlockSize n beta : ℕ)))) := by
  have hraw := lemma83DegreeJointOn_probability
    w I hJI a tau delta eta x hell
      (one_le_lemma83BlockSize n beta hn) heta hellower hellupper htau
      hdelta hdeltaUpper
  have hcoef := lemma83_coefficient_le_sourceScale
    n beta eta tau delta hn heta htau hdelta.le
  have hraw0 : 0 ≤ 4096 / (eta / 2) *
      ((|tau| + delta) *
        (|tau| + 1 / Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) /
          |tau|) := by
    have htauabs : 0 < |tau| := abs_pos.mpr htau
    positivity
  exact hraw.trans (add_le_add (pow_le_pow_left₀ hraw0 hcoef q) le_rfl)

/-- Finite absorbed form of conditioned-slice Lemma 8.3. -/
theorem lemma83DegreeJointOn_probability_sourcePower_of_imbalance
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (I : Finset (Fin n)) (hJI : w.J ⊆ I)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ I.card) (hn : 1 ≤ n)
    (heta : 0 < eta) (hellower : eta * (I.card : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * I.card)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2)
    (himbalance :
      (q : ℝ) *
          (2 * Real.exp
            (-(eta * lemma83BlockSize n beta) ^ 2 /
              (8 * (2 * lemma83BlockSize n beta : ℕ)))) ≤
        ((n : ℝ) ^ (-(1 - beta) / 2)) ^ q) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
          ∀ r : Fin q,
            RLCD.distToInt
              (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                  (U.1 ∩ w.J) : ℝ) -
                tau * (AKSGraph.degreeInto G (w.tuple a 0)
                  (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
      (8192 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q := by
  classical
  let : Nonempty (BooleanSlices.BooleanSlicePoint I ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  by_cases hq0 : q = 0
  · subst q
    simpa using Concentration.uniformProbability_le_one
      (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
        ∀ r : Fin 0,
          RLCD.distToInt
            (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                (U.1 ∩ w.J) : ℝ) -
              tau * (AKSGraph.degreeInto G (w.tuple a 0)
                (U.1 ∩ w.J) : ℝ) + x r) ≤ delta)
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    let s : ℝ := (n : ℝ) ^ (-(1 - beta) / 2)
    let T : ℝ := ((|tau| + delta) * (|tau| + s) / |tau|)
    let A : ℝ := 4096 / (eta / 2)
    let B : ℝ := A * T
    have htauabs : 0 < |tau| := abs_pos.mpr htau
    have hs0 : 0 ≤ s := by dsimp only [s]; positivity
    let b0 := selectedLemma83BlockPair w a (0 : Fin (q + 1))
    have hAinI : b0.A ⊆ I :=
      (b0.A_subset.trans Finset.inter_subset_right).trans hJI
    have hIposNat : 0 < I.card := by
      have hApos : 0 < b0.A.card := by
        rw [b0.card_A]
        exact one_le_lemma83BlockSize n beta hn
      exact hApos.trans_le (Finset.card_le_card hAinI)
    have hIpos : (0 : ℝ) < I.card := by exact_mod_cast hIposNat
    have hetaHalf : eta ≤ 1 / 2 := by
      have hboth : eta * (I.card : ℝ) ≤ (1 - eta) * I.card :=
        hellower.trans hellupper
      have hmul : (2 * eta) * (I.card : ℝ) ≤ 1 * I.card := by
        nlinarith
      have := le_of_mul_le_mul_right hmul hIpos
      linarith
    have hA1 : 1 ≤ A := by
      dsimp only [A]
      rw [le_div_iff₀ (div_pos heta (by norm_num))]
      nlinarith
    have hT0 : 0 ≤ T := by dsimp only [T]; positivity
    have hsT : s ≤ T := by
      dsimp only [T]
      apply (le_div_iff₀ htauabs).mpr
      rw [mul_comm s |tau|]
      exact mul_le_mul (le_add_of_nonneg_right hdelta.le)
        (le_add_of_nonneg_left htauabs.le) hs0 (by positivity)
    have hTB : T ≤ B := by
      dsimp only [B]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA1 hT0
    have hsB : s ≤ B := hsT.trans hTB
    have hB0 : 0 ≤ B := mul_nonneg (le_trans zero_le_one hA1) hT0
    have hraw := lemma83DegreeJointOn_probability_sourceScale_additive
      w I hJI a tau delta eta x hell hn heta hellower hellupper htau
        hdelta hdeltaUpper
    have hsPow : s ^ q ≤ B ^ q := pow_le_pow_left₀ hs0 hsB q
    calc
      Concentration.uniformProbability
          (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
            ∀ r : Fin q,
              RLCD.distToInt
                (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                    (U.1 ∩ w.J) : ℝ) -
                  tau * (AKSGraph.degreeInto G (w.tuple a 0)
                    (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
          B ^ q + (q : ℝ) *
            (2 * Real.exp
              (-(eta * lemma83BlockSize n beta) ^ 2 /
                (8 * (2 * lemma83BlockSize n beta : ℕ)))) := by
            simpa only [B, A, T, s] using hraw
      _ ≤ B ^ q + s ^ q := add_le_add le_rfl himbalance
      _ ≤ B ^ q + B ^ q := add_le_add le_rfl hsPow
      _ ≤ (2 * B) ^ q := add_self_pow_le_two_mul_pow hB0 hq1
      _ = (8192 / (eta / 2) *
            ((|tau| + delta) *
              (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q := by
        congr 1
        dsimp only [B, A, T, s]
        ring

/-- Source-shaped Lemma 8.3 after conditioning on a fixed-size slice of
`J`, in the logarithmic tuple regime supplied by Lemma 8.2. -/
theorem eventually_lemma83DegreeJointOn_probability_sourcePower
    (beta eta zeta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heta : 0 < eta) (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (q familySize ell : ℕ) (G : SimpleGraph (Fin n))
        (w : Lemma82Witness G beta (q + 1) familySize)
        (I : Finset (Fin n)), w.J ⊆ I →
        ∀ (a : Fin familySize) (tau delta : ℝ) (x : Fin q → ℝ),
        (q : ℝ) ≤ zeta * Real.log n →
        ell ≤ I.card → eta * (I.card : ℝ) ≤ ell →
        (ell : ℝ) ≤ (1 - eta) * I.card →
        tau ≠ 0 → 0 < delta → delta ≤ 1 / 2 →
        Concentration.uniformProbability
            (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
              ∀ r : Fin q,
                RLCD.distToInt
                  (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                      (U.1 ∩ w.J) : ℝ) -
                    tau * (AKSGraph.degreeInto G (w.tuple a 0)
                      (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
          (8192 / (eta / 2) *
              ((|tau| + delta) *
                (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q := by
  have himbalance := eventually_lemma83_imbalance_le_sourcePower
    beta eta zeta hbeta0 hbeta1 heta hzeta
  filter_upwards [Filter.eventually_ge_atTop 1, himbalance]
    with n hn hnImbalance
  intro q familySize ell G w I hJI a tau delta x hq hell hellower
    hellupper htau hdelta hdeltaUpper
  exact lemma83DegreeJointOn_probability_sourcePower_of_imbalance
    w I hJI a tau delta eta x hell hn heta hellower hellupper htau
      hdelta hdeltaUpper (hnImbalance q hq)

/-! ### The finite Markov step in Claim 8.5 -/

/-- Number of members of a finite family whose event is bad at an outcome. -/
noncomputable def badFamilyCount {Omega A : Type*}
    [Fintype A] (Bad : A → Omega → Prop) (omega : Omega) : ℕ := by
  classical
  exact (Finset.univ.filter fun a ↦ Bad a omega).card

/-- Finite Fubini identity for the number of bad members of a family. -/
lemma sum_badFamilyCount {Omega A : Type*} [Fintype Omega] [Fintype A]
    (Bad : A → Omega → Prop) :
    (∑ omega : Omega, (badFamilyCount Bad omega : ℝ)) =
      ∑ a : A, (Nat.card {omega : Omega // Bad a omega} : ℝ) := by
  classical
  calc
    (∑ omega : Omega, (badFamilyCount Bad omega : ℝ)) =
        ∑ a : A,
          (((Finset.univ : Finset Omega).filter (Bad a)).card : ℝ) := by
      unfold badFamilyCount
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]
      rw [Finset.sum_comm]
    _ = ∑ a : A, (Nat.card {omega : Omega // Bad a omega} : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- If every member of a finite family is bad with probability at most `p`,
then the probability that at least half the family is bad is at most `2p`.
This is the exact averaging/Markov step in Claim 8.5. -/
theorem uniformProbability_half_le_badFamilyCount
    {Omega A : Type*} [Fintype Omega] [Nonempty Omega]
    [Fintype A] [Nonempty A]
    (Bad : A → Omega → Prop) (p : ℝ)
    (hbad : ∀ a, Concentration.uniformProbability (Bad a) ≤ p) :
    Concentration.uniformProbability
        (fun omega ↦ (Fintype.card A : ℝ) / 2 ≤ badFamilyCount Bad omega) ≤
      2 * p := by
  classical
  let Large : Omega → Prop := fun omega ↦
    (Fintype.card A : ℝ) / 2 ≤ badFamilyCount Bad omega
  let S : Finset Omega := Finset.univ.filter Large
  have hOmega : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  have hA : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  have hlower : (S.card : ℝ) * ((Fintype.card A : ℝ) / 2) ≤
      ∑ omega ∈ S, (badFamilyCount Bad omega : ℝ) := by
    have hraw := Finset.card_nsmul_le_sum S
      (fun omega ↦ (badFamilyCount Bad omega : ℝ))
      ((Fintype.card A : ℝ) / 2) (by
        intro omega homega
        exact (Finset.mem_filter.mp homega).2)
    simpa only [nsmul_eq_mul] using hraw
  have hsubsum :
      (∑ omega ∈ S, (badFamilyCount Bad omega : ℝ)) ≤
        ∑ omega : Omega, (badFamilyCount Bad omega : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun _ _ _ ↦ by positivity)
  have hsingle : ∀ a : A,
      (Nat.card {omega : Omega // Bad a omega} : ℝ) ≤
        p * Fintype.card Omega := by
    intro a
    have ha := hbad a
    rw [uniformProbability_eq_card_subtype] at ha
    exact (div_le_iff₀ hOmega).mp ha
  have htotal :
      (∑ omega : Omega, (badFamilyCount Bad omega : ℝ)) ≤
        Fintype.card A * (p * Fintype.card Omega) := by
    rw [sum_badFamilyCount]
    calc
      (∑ a : A, (Nat.card {omega : Omega // Bad a omega} : ℝ)) ≤
          ∑ _a : A, p * Fintype.card Omega :=
        Finset.sum_le_sum fun a _ ↦ hsingle a
      _ = Fintype.card A * (p * Fintype.card Omega) := by simp
  have hcount : (S.card : ℝ) ≤ 2 * p * Fintype.card Omega := by
    nlinarith [hlower.trans (hsubsum.trans htotal)]
  rw [uniformProbability_eq_filter_div]
  change (S.card : ℝ) / Fintype.card Omega ≤ 2 * p
  exact (div_le_iff₀ hOmega).2 (by simpa [mul_assoc] using hcount)

/-- A uniform conditional probability bound on every second-coordinate
fiber gives the same bound on the product space. -/
theorem uniformProbability_prod_le_of_right
    {Omega Psi : Type*} [Fintype Omega] [Nonempty Omega]
    [Fintype Psi] [Nonempty Psi]
    (P : Omega → Psi → Prop) (p : ℝ)
    (hP : ∀ y, Concentration.uniformProbability (fun x ↦ P x y) ≤ p) :
    Concentration.uniformProbability (fun z : Omega × Psi ↦ P z.1 z.2) ≤ p := by
  classical
  rw [uniformProbability_eq_filter_div]
  have hOmega : (0 : ℝ) < Fintype.card Omega := by
    exact_mod_cast Fintype.card_pos
  have hPsi : (0 : ℝ) < Fintype.card Psi := by
    exact_mod_cast Fintype.card_pos
  have hfiber : ∀ y : Psi,
      (((Finset.univ : Finset Omega).filter fun x ↦ P x y).card : ℝ) ≤
        p * Fintype.card Omega := by
    intro y
    have hy := hP y
    rw [uniformProbability_eq_filter_div] at hy
    exact (div_le_iff₀ hOmega).mp hy
  have hcard :
      (((Finset.univ : Finset (Omega × Psi)).filter
          fun z ↦ P z.1 z.2).card : ℝ) ≤
        Fintype.card Psi * (p * Fintype.card Omega) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc
      (∑ y : Psi, ∑ x : Omega, if P x y then (1 : ℝ) else 0) ≤
          ∑ _y : Psi, p * Fintype.card Omega :=
        Finset.sum_le_sum fun y _ ↦ by
          simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
            Nat.cast_one, Nat.cast_zero] using hfiber y
      _ = Fintype.card Psi * (p * Fintype.card Omega) := by simp
  have hprod : (Fintype.card (Omega × Psi) : ℝ) =
      Fintype.card Omega * Fintype.card Psi := by
    simp
  rw [hprod]
  apply (div_le_iff₀ (mul_pos hOmega hPsi)).2
  calc
    (((Finset.univ : Finset (Omega × Psi)).filter
        fun z ↦ P z.1 z.2).card : ℝ) ≤
        Fintype.card Psi * (p * Fintype.card Omega) := hcard
    _ = p * (Fintype.card Omega * Fintype.card Psi) := by ring

/-! ### Tuple averaging for Claim 8.5 -/

/-- A tuple is bad when none of its later vertices gives a coefficient
separated from its first vertex after the two-copy `J` exposure. -/
def lemma85TupleBad
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta : ℝ)
    (YZ : BooleanSlices.BooleanSlicePoint w.J ell ×
      BooleanSlices.BooleanSlicePoint w.J ell) : Prop :=
  ∀ r : Fin q,
    RLCD.distToInt
      (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
          (YZ.1.1 ∩ w.J) : ℝ) -
        tau * (AKSGraph.degreeInto G (w.tuple a 0)
          (YZ.1.1 ∩ w.J) : ℝ) +
        (-tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
          (YZ.2.1 ∩ w.J) : ℝ) +
        tau * (AKSGraph.degreeInto G (w.tuple a 0)
          (YZ.2.1 ∩ w.J) : ℝ))) ≤ delta

/-- A joint one-slice bound gives the corresponding two-copy tuple bound by
conditioning on the second copy.  Keeping this finite step separate avoids
unfolding the eventual Lemma 8.3 theorem while normalizing the event. -/
theorem lemma85TupleBad_probability_of_jointOn
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta p : ℝ)
    [Nonempty (BooleanSlices.BooleanSlicePoint w.J ell)]
    (hjoint : ∀ x : Fin q → ℝ,
      Concentration.uniformProbability
          (fun Y : BooleanSlices.BooleanSlicePoint w.J ell ↦
            ∀ r : Fin q,
              RLCD.distToInt
                (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                    (Y.1 ∩ w.J) : ℝ) -
                  tau * (AKSGraph.degreeInto G (w.tuple a 0)
                    (Y.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤ p) :
    Concentration.uniformProbability
        (lemma85TupleBad (ell := ell) w a tau delta) ≤ p := by
  refine uniformProbability_prod_le_of_right
    (P := fun Y Z ↦ lemma85TupleBad (ell := ell) w a tau delta (Y, Z)) p ?_
  intro Z
  let x : Fin q → ℝ := fun r ↦
    -tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
      (Z.1 ∩ w.J) : ℝ) +
      tau * (AKSGraph.degreeInto G (w.tuple a 0)
        (Z.1 ∩ w.J) : ℝ)
  have hevent :
      (fun Y : BooleanSlices.BooleanSlicePoint w.J ell ↦
        lemma85TupleBad (ell := ell) w a tau delta (Y, Z)) =
      (fun Y ↦ ∀ r : Fin q,
        RLCD.distToInt
          (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
              (Y.1 ∩ w.J) : ℝ) -
            tau * (AKSGraph.degreeInto G (w.tuple a 0)
              (Y.1 ∩ w.J) : ℝ) + x r) ≤ delta) := by
    rfl
  rw [hevent]
  exact hjoint x

/-- The conditioned form of Lemma 8.3 bounds the probability that one fixed
tuple is bad under the two-copy `J` exposure. -/
theorem eventually_lemma85TupleBad_probability
    (beta eta zeta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heta : 0 < eta) (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (q familySize ell : ℕ) (G : SimpleGraph (Fin n))
        (w : Lemma82Witness G beta (q + 1) familySize)
        (a : Fin familySize) (tau delta : ℝ),
        (q : ℝ) ≤ zeta * Real.log n →
        ell ≤ w.J.card → eta * (w.J.card : ℝ) ≤ ell →
        (ell : ℝ) ≤ (1 - eta) * w.J.card →
        tau ≠ 0 → 0 < delta → delta ≤ 1 / 2 →
        Concentration.uniformProbability
            (lemma85TupleBad (ell := ell) w a tau delta) ≤
          (8192 / (eta / 2) *
              ((|tau| + delta) *
                (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q := by
  have hsource := eventually_lemma83DegreeJointOn_probability_sourcePower
    beta eta zeta hbeta0 hbeta1 heta hzeta
  filter_upwards [hsource] with n hn
  intro q familySize ell G w a tau delta hq hell hellower hellupper
    htau hdelta hdeltaUpper
  let : Nonempty (BooleanSlices.BooleanSlicePoint w.J ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  apply lemma85TupleBad_probability_of_jointOn
  intro x
  exact hn q familySize ell G w w.J Finset.Subset.rfl a tau delta x hq
    hell hellower hellupper htau hdelta hdeltaUpper

/-- Claim 8.5's Markov conclusion before choosing the separated pairs:
except with probability `2p`, fewer than half of the disjoint tuples are
bad. -/
theorem lemma85_half_bad_probability
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (tau delta p : ℝ) (hfamily : 0 < familySize)
    (hell : ell ≤ w.J.card)
    (hbad : ∀ a : Fin familySize,
      Concentration.uniformProbability
        (lemma85TupleBad (ell := ell) w a tau delta) ≤ p) :
    Concentration.uniformProbability
        (fun YZ : BooleanSlices.BooleanSlicePoint w.J ell ×
            BooleanSlices.BooleanSlicePoint w.J ell ↦
          (familySize : ℝ) / 2 ≤
            badFamilyCount
              (fun a ↦ lemma85TupleBad (ell := ell) w a tau delta) YZ) ≤
      2 * p := by
  let : Nonempty (BooleanSlices.BooleanSlicePoint w.J ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  let : Nonempty (Fin familySize) := Fin.pos_iff_nonempty.mp hfamily
  simpa only [Fintype.card_fin] using
    uniformProbability_half_le_badFamilyCount
      (fun a ↦ lemma85TupleBad (ell := ell) w a tau delta) p hbad

/-- Source-power version of the probabilistic part of Claim 8.5. -/
theorem eventually_lemma85_half_bad_probability
    (beta eta zeta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heta : 0 < eta) (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (q familySize ell : ℕ) (G : SimpleGraph (Fin n))
        (w : Lemma82Witness G beta (q + 1) familySize)
        (tau delta : ℝ),
        (q : ℝ) ≤ zeta * Real.log n → 0 < familySize →
        ell ≤ w.J.card → eta * (w.J.card : ℝ) ≤ ell →
        (ell : ℝ) ≤ (1 - eta) * w.J.card →
        tau ≠ 0 → 0 < delta → delta ≤ 1 / 2 →
        Concentration.uniformProbability
            (fun YZ : BooleanSlices.BooleanSlicePoint w.J ell ×
                BooleanSlices.BooleanSlicePoint w.J ell ↦
              (familySize : ℝ) / 2 ≤
                badFamilyCount
                  (fun a ↦ lemma85TupleBad (ell := ell) w a tau delta) YZ) ≤
          2 * (8192 / (eta / 2) *
              ((|tau| + delta) *
                (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q := by
  have htuple := eventually_lemma85TupleBad_probability
    beta eta zeta hbeta0 hbeta1 heta hzeta
  filter_upwards [htuple] with n hn
  intro q familySize ell G w tau delta hq hfamily hell hellower
    hellupper htau hdelta hdeltaUpper
  let : Nonempty (BooleanSlices.BooleanSlicePoint w.J ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  apply lemma85_half_bad_probability w tau delta _ hfamily hell
  intro a
  exact hn q familySize ell G w a tau delta hq hell hellower hellupper
    htau hdelta hdeltaUpper

/-! ### Choosing the separated pairs in Claim 8.5 -/

/-- If fewer than half of the Lemma 8.2 tuples are bad, one can index
`familySize / 2` distinct tuples and choose in each of them a later vertex
whose two-copy degree difference is separated modulo one from the first
vertex. -/
theorem exists_lemma85_separated_indices
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (tau delta : ℝ)
    (YZ : BooleanSlices.BooleanSlicePoint w.J ell ×
      BooleanSlices.BooleanSlicePoint w.J ell)
    (hgood : badFamilyCount
        (fun a ↦ lemma85TupleBad (ell := ell) w a tau delta) YZ <
      (familySize : ℝ) / 2) :
    ∃ e : Fin (familySize / 2) ↪ Fin familySize,
      ∃ r : Fin (familySize / 2) → Fin q,
        ∀ k,
          delta < RLCD.distToInt
            (tau * (AKSGraph.degreeInto G (w.tuple (e k) (r k).succ)
                (YZ.1.1 ∩ w.J) : ℝ) -
              tau * (AKSGraph.degreeInto G (w.tuple (e k) 0)
                (YZ.1.1 ∩ w.J) : ℝ) +
              (-tau * (AKSGraph.degreeInto G (w.tuple (e k) (r k).succ)
                (YZ.2.1 ∩ w.J) : ℝ) +
              tau * (AKSGraph.degreeInto G (w.tuple (e k) 0)
                (YZ.2.1 ∩ w.J) : ℝ))) := by
  classical
  let Bad : Fin familySize → Prop := fun a ↦
    lemma85TupleBad (ell := ell) w a tau delta YZ
  let B : Finset (Fin familySize) := Finset.univ.filter Bad
  let S : Finset (Fin familySize) := Finset.univ \ B
  have hBcard : B.card =
      badFamilyCount
        (fun a ↦ lemma85TupleBad (ell := ell) w a tau delta) YZ := by
    rfl
  have hScard : S.card = familySize - B.card := by
    rw [show S = Finset.univ \ B by rfl, Finset.card_sdiff]
    simp
  have htwiceReal : (2 : ℝ) * B.card < familySize := by
    rw [hBcard]
    linarith
  have htwice : 2 * B.card < familySize := by
    exact_mod_cast htwiceReal
  have hk : familySize / 2 ≤ S.card := by
    rw [hScard]
    omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hk
  let eT : Fin (familySize / 2) ↪ T :=
    (T.equivFinOfCardEq hTcard).symm.toEmbedding
  let e : Fin (familySize / 2) ↪ Fin familySize :=
    eT.trans (Function.Embedding.subtype _)
  have hex : ∀ k : Fin (familySize / 2), ∃ r : Fin q,
      delta < RLCD.distToInt
        (tau * (AKSGraph.degreeInto G (w.tuple (e k) r.succ)
            (YZ.1.1 ∩ w.J) : ℝ) -
          tau * (AKSGraph.degreeInto G (w.tuple (e k) 0)
            (YZ.1.1 ∩ w.J) : ℝ) +
          (-tau * (AKSGraph.degreeInto G (w.tuple (e k) r.succ)
            (YZ.2.1 ∩ w.J) : ℝ) +
          tau * (AKSGraph.degreeInto G (w.tuple (e k) 0)
            (YZ.2.1 ∩ w.J) : ℝ))) := by
    intro k
    have heT : e k ∈ T := (eT k).property
    have heS : e k ∈ S := hTS heT
    have heNotBad : ¬Bad (e k) := by
      have heB : e k ∉ B := (Finset.mem_sdiff.mp heS).2
      intro heBad
      exact heB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heBad⟩)
    simp only [Bad, lemma85TupleBad] at heNotBad
    push Not at heNotBad
    exact heNotBad
  choose r hr using hex
  exact ⟨e, r, hr⟩

/-- The vertex pairs obtained from distinct Lemma 8.2 tuples form a genuine
pair embedding in the `I`-part.  The `false` endpoint is the chosen later
vertex and the `true` endpoint is the tuple's first vertex. -/
def lemma85PairEmbedding
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (e : Fin (familySize / 2) ↪ Fin familySize)
    (r : Fin (familySize / 2) → Fin q) :
    PairEmbedding (Fin (familySize / 2)) ↑w.I where
  toFun kb :=
    ⟨w.tuple (e kb.1) (if kb.2 then 0 else (r kb.1).succ),
      w.tuple_mem_I _ _⟩
  inj' := by
    intro x y hxy
    rcases x with ⟨kx, bx⟩
    rcases y with ⟨ky, byy⟩
    have hv :
        w.tuple (e kx) (if bx then 0 else (r kx).succ) =
          w.tuple (e ky) (if byy then 0 else (r ky).succ) := by
      exact Subtype.ext_iff.mp hxy
    have he : e kx = e ky := by
      by_contra hne
      exact w.tuple_disjoint hne _ _ hv
    have hk : kx = ky := e.injective he
    subst ky
    have hi := w.tuple_injective (e kx) hv
    have hb : bx = byy := by
      cases bx <;> cases byy <;> simp_all only [Bool.true_eq_false]
      exact Fin.succ_ne_zero _ hi.symm
    exact Prod.ext rfl hb

@[simp] theorem lemma85PairEmbedding_false
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (e : Fin (familySize / 2) ↪ Fin familySize)
    (r : Fin (familySize / 2) → Fin q) (k : Fin (familySize / 2)) :
    lemma85PairEmbedding w e r (k, false) =
      ⟨w.tuple (e k) (r k).succ, w.tuple_mem_I _ _⟩ := rfl

@[simp] theorem lemma85PairEmbedding_true
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (e : Fin (familySize / 2) ↪ Fin familySize)
    (r : Fin (familySize / 2) → Fin q) (k : Fin (familySize / 2)) :
    lemma85PairEmbedding w e r (k, true) =
      ⟨w.tuple (e k) 0, w.tuple_mem_I _ _⟩ := rfl

/-- The good two-copy exposures in Claim 8.5, transported to the
function-valued Boolean slice used by the Fourier argument. -/
def lemma85GoodExposure
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (tau delta : ℝ)
    (p : BoolSlice ↑w.J ell × BoolSlice ↑w.J ell) : Prop :=
  badFamilyCount
      (fun a ↦ lemma85TupleBad (ell := ell) w a tau delta)
      (boolSliceEquivBooleanSlicePoint w.J ell p.1,
        boolSliceEquivBooleanSlicePoint w.J ell p.2) <
    (familySize : ℝ) / 2

/-- The Markov exceptional-probability estimate is unchanged when the two
slice copies are transported to the function-valued Fourier model. -/
theorem finProbability_not_lemma85GoodExposure_le
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    [Nonempty (BoolSlice ↑w.J ell)]
    (tau delta eps : ℝ) (hell : ell ≤ w.J.card)
    (hbad : Concentration.uniformProbability
        (fun YZ : BooleanSlices.BooleanSlicePoint w.J ell ×
            BooleanSlices.BooleanSlicePoint w.J ell ↦
          (familySize : ℝ) / 2 ≤
            badFamilyCount
              (fun a ↦ lemma85TupleBad (ell := ell) w a tau delta) YZ) ≤
      eps) :
    finProbability (BoolSlice ↑w.J ell × BoolSlice ↑w.J ell)
        (fun p ↦ ¬lemma85GoodExposure w tau delta p) ≤ eps := by
  let : Nonempty (BooleanSlices.BooleanSlicePoint w.J ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  let E := (boolSliceEquivBooleanSlicePoint w.J ell).prodCongr
    (boolSliceEquivBooleanSlicePoint w.J ell)
  let Q : (BooleanSlices.BooleanSlicePoint w.J ell ×
      BooleanSlices.BooleanSlicePoint w.J ell) → Prop := fun YZ ↦
    (familySize : ℝ) / 2 ≤
      badFamilyCount
        (fun a ↦ lemma85TupleBad (ell := ell) w a tau delta) YZ
  have htransport := uniformProbability_comp_equiv E Q
  calc
    finProbability (BoolSlice ↑w.J ell × BoolSlice ↑w.J ell)
        (fun p ↦ ¬lemma85GoodExposure w tau delta p) =
        Concentration.uniformProbability (fun p ↦ Q (E p)) := by
          have hpred :
              (fun p : BoolSlice ↑w.J ell × BoolSlice ↑w.J ell ↦
                ¬lemma85GoodExposure w tau delta p) =
              (fun p ↦ Q (E p)) := by
            funext p
            apply propext
            rcases p with ⟨p1, p2⟩
            simp only [Q, E, lemma85GoodExposure, not_lt]
            rfl
          rw [hpred]
          rfl
    _ = Concentration.uniformProbability Q := htransport
    _ ≤ eps := hbad

/-- The complete analytic conclusion of Claim 8.5 for a Lemma 8.2 witness.
The probabilistic input is precisely the Markov bound proved above; the
conclusion combines the selected disjoint tuple pairs with Lemma 4.8. -/
theorem norm_splitQuadraticCharFun_sq_le_lemma85
    {n q familySize s ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    [Nonempty (BoolSlice ↑w.I s)] [Nonempty (BoolSlice ↑w.J ell)]
    (fI : BoolSlice ↑w.I s → ℝ) (fJ : BoolSlice ↑w.J ell → ℝ)
    (t delta c eps : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card ↑w.I ≤ s)
    (hunsel : c * Fintype.card ↑w.I ≤ Fintype.card ↑w.I - s)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1 / 2)
    (hell : ell ≤ w.J.card)
    (hbad : Concentration.uniformProbability
        (fun YZ : BooleanSlices.BooleanSlicePoint w.J ell ×
            BooleanSlices.BooleanSlicePoint w.J ell ↦
          (familySize : ℝ) / 2 ≤
            badFamilyCount
              (fun a ↦ lemma85TupleBad (ell := ell) w a
                (t / (2 * Real.pi)) delta) YZ) ≤ eps) :
    ‖finCharFun (BoolSlice ↑w.I s × BoolSlice ↑w.J ell)
        (fun p ↦ splitQuadraticValue fI fJ (lemma81CrossMatrix w)
          p.1 p.2) t‖ ^ 2 ≤
      Real.exp 1 * Real.exp
        (-(c ^ 3 / 256) * ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) + eps := by
  classical
  let Good : BoolSlice ↑w.J ell × BoolSlice ↑w.J ell → Prop :=
    lemma85GoodExposure w (t / (2 * Real.pi)) delta
  have hselect : ∀ p, Good p →
      ∃ e : Fin (familySize / 2) ↪ Fin familySize,
        ∃ r : Fin (familySize / 2) → Fin q,
          ∀ k,
            delta < RLCD.distToInt
              ((t / (2 * Real.pi)) *
                  (AKSGraph.degreeInto G (w.tuple (e k) (r k).succ)
                    (((boolSliceEquivBooleanSlicePoint w.J ell p.1).1) ∩
                      w.J) : ℝ) -
                (t / (2 * Real.pi)) *
                  (AKSGraph.degreeInto G (w.tuple (e k) 0)
                    (((boolSliceEquivBooleanSlicePoint w.J ell p.1).1) ∩
                      w.J) : ℝ) +
                (-(t / (2 * Real.pi)) *
                    (AKSGraph.degreeInto G (w.tuple (e k) (r k).succ)
                      (((boolSliceEquivBooleanSlicePoint w.J ell p.2).1) ∩
                        w.J) : ℝ) +
                  (t / (2 * Real.pi)) *
                    (AKSGraph.degreeInto G (w.tuple (e k) 0)
                      (((boolSliceEquivBooleanSlicePoint w.J ell p.2).1) ∩
                        w.J) : ℝ))) := by
    intro p hp
    exact exists_lemma85_separated_indices w (t / (2 * Real.pi)) delta
      (boolSliceEquivBooleanSlicePoint w.J ell p.1,
        boolSliceEquivBooleanSlicePoint w.J ell p.2) hp
  let selectedE : ∀ p, Good p → Fin (familySize / 2) ↪ Fin familySize :=
    fun p hp ↦ Classical.choose (hselect p hp)
  let selectedR : ∀ p (hp : Good p), Fin (familySize / 2) → Fin q :=
    fun p hp ↦ Classical.choose (Classical.choose_spec (hselect p hp))
  have selected_separated : ∀ p (hp : Good p) k,
      delta < RLCD.distToInt
        ((t / (2 * Real.pi)) *
            (AKSGraph.degreeInto G
              (w.tuple (selectedE p hp k) (selectedR p hp k).succ)
              (((boolSliceEquivBooleanSlicePoint w.J ell p.1).1) ∩ w.J) : ℝ) -
          (t / (2 * Real.pi)) *
            (AKSGraph.degreeInto G (w.tuple (selectedE p hp k) 0)
              (((boolSliceEquivBooleanSlicePoint w.J ell p.1).1) ∩ w.J) : ℝ) +
          (-(t / (2 * Real.pi)) *
              (AKSGraph.degreeInto G
                (w.tuple (selectedE p hp k) (selectedR p hp k).succ)
                (((boolSliceEquivBooleanSlicePoint w.J ell p.2).1) ∩ w.J) : ℝ) +
            (t / (2 * Real.pi)) *
              (AKSGraph.degreeInto G (w.tuple (selectedE p hp k) 0)
                (((boolSliceEquivBooleanSlicePoint w.J ell p.2).1) ∩ w.J) : ℝ))) := by
    intro p hp k
    exact Classical.choose_spec (Classical.choose_spec (hselect p hp)) k
  let pairing : ∀ p, Good p → PairEmbedding (Fin (familySize / 2)) ↑w.I :=
    fun p hp ↦ lemma85PairEmbedding w (selectedE p hp) (selectedR p hp)
  let center : ∀ p (hp : Good p), Fin (familySize / 2) → ℝ :=
    fun p hp k ↦ LinearLCDCancellation.centeredResidue
      (t * (crossSliceCoefficient (lemma81CrossMatrix w) p.1.1 p.2.1
          (pairing p hp (k, false)) -
        crossSliceCoefficient (lemma81CrossMatrix w) p.1.1 p.2.1
          (pairing p hp (k, true))) / (2 * Real.pi))
  have hcentered : ∀ p (hp : Good p) k,
      IsCenteredModOne
        (t * (crossSliceCoefficient (lemma81CrossMatrix w) p.1.1 p.2.1
            (pairing p hp (k, false)) -
          crossSliceCoefficient (lemma81CrossMatrix w) p.1.1 p.2.1
            (pairing p hp (k, true))) / (2 * Real.pi))
        (center p hp k) := by
    intro p hp k
    exact LinearLCDCancellation.centeredResidue_isCenteredModOne _
  have hseparated : ∀ p (hp : Good p) k,
      delta ≤ |center p hp k| := by
    intro p hp k
    dsimp only [center]
    rw [LinearLCDCancellation.abs_centeredResidue]
    have harg :
        t * (crossSliceCoefficient (lemma81CrossMatrix w) p.1.1 p.2.1
              (pairing p hp (k, false)) -
            crossSliceCoefficient (lemma81CrossMatrix w) p.1.1 p.2.1
              (pairing p hp (k, true))) / (2 * Real.pi) =
          (t / (2 * Real.pi)) *
              (AKSGraph.degreeInto G
                (w.tuple (selectedE p hp k) (selectedR p hp k).succ)
                (((boolSliceEquivBooleanSlicePoint w.J ell p.1).1) ∩ w.J) : ℝ) -
            (t / (2 * Real.pi)) *
              (AKSGraph.degreeInto G (w.tuple (selectedE p hp k) 0)
                (((boolSliceEquivBooleanSlicePoint w.J ell p.1).1) ∩ w.J) : ℝ) +
            (-(t / (2 * Real.pi)) *
                (AKSGraph.degreeInto G
                  (w.tuple (selectedE p hp k) (selectedR p hp k).succ)
                  (((boolSliceEquivBooleanSlicePoint w.J ell p.2).1) ∩ w.J) : ℝ) +
              (t / (2 * Real.pi)) *
                (AKSGraph.degreeInto G (w.tuple (selectedE p hp k) 0)
                  (((boolSliceEquivBooleanSlicePoint w.J ell p.2).1) ∩ w.J) : ℝ)) := by
      simp only [pairing, lemma85PairEmbedding_false,
        lemma85PairEmbedding_true]
      rw [crossSliceCoefficient_lemma81CrossMatrix,
        crossSliceCoefficient_lemma81CrossMatrix]
      field_simp [ne_of_gt Real.pi_pos]
      ring
    rw [harg]
    exact (selected_separated p hp k).le
  have hbad' : finProbability (BoolSlice ↑w.J ell × BoolSlice ↑w.J ell)
      (fun p ↦ ¬Good p) ≤ eps := by
    exact finProbability_not_lemma85GoodExposure_le w
      (t / (2 * Real.pi)) delta eps hell hbad
  have hmain := norm_splitQuadraticCharFun_sq_le_balanced
    fI fJ (lemma81CrossMatrix w) t delta c eps Good pairing center
    hc0 hc1 hsel hunsel hdelta0 hdelta1 hcentered hseparated hbad'
  simpa only [Fintype.card_fin] using hmain

/-- The outer cardinality fibers on which the `I`-slice is not balanced
enough to apply Claim 8.5. -/
def lemma85UnbalancedFiber
    {n q familySize k : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize) (c : ℝ)
    (a : Fin (k + 1)) : Prop :=
  ¬(c * (Fintype.card ↑w.I : ℝ) ≤ (a.1 : ℝ) ∧
    c * (Fintype.card ↑w.I : ℝ) ≤
      (Fintype.card ↑w.I : ℝ) - (a.1 : ℝ))

/-- A direct hypergeometric bound for the exceptional outer fibers.  The
two margin hypotheses say that the mean intersection with `I` is at least
`d` away from both balance thresholds. -/
theorem lemma85UnbalancedFiber_probability_le
    {n q familySize k : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    [Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) k)]
    (c d : ℝ) (hIpos : 0 < w.I.card) (hd : 0 ≤ d)
    (hleft : c * (w.I.card : ℝ) + d ≤
      (w.I.card : ℝ) * k / n)
    (hright : (w.I.card : ℝ) * k / n + d ≤
      (w.I.card : ℝ) - c * w.I.card) :
    finProbability
        (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)
        (fun S ↦ lemma85UnbalancedFiber w c
          (booleanSlicePartitionCount w.I k S)) ≤
      2 * Real.exp (-d ^ 2 / (8 * w.I.card)) := by
  classical
  let S₀ : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) k := Classical.choice inferInstance
  have hk : k ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [← (BooleanSlices.mem_booleanSlice.mp S₀.2).2]
    exact Finset.card_le_card
      (BooleanSlices.mem_booleanSlice.mp S₀.2).1
  have htail := booleanSlice_intersection_two_sided_probability
    (Finset.univ : Finset (Fin n)) w.I k (Finset.subset_univ _)
      hk hIpos d hd
  apply (Concentration.uniformProbability_mono (fun S hS ↦ ?_)).trans htail
  simp only [lemma85UnbalancedFiber, booleanSlicePartitionCount,
    Fintype.card_coe] at hS
  simp only [Finset.card_univ, Fintype.card_fin]
  by_cases hlow : c * (w.I.card : ℝ) ≤ (S.1 ∩ w.I).card
  · have hnotHigh : ¬ c * (w.I.card : ℝ) ≤
        (w.I.card : ℝ) - (S.1 ∩ w.I).card := by
      intro hhigh
      exact hS ⟨hlow, hhigh⟩
    have hhigh := lt_of_not_ge hnotHigh
    have hdev : d ≤ (((S.1 ∩ w.I).card : ℝ) -
        (w.I.card : ℝ) * k / n) := by
      linarith
    exact hdev.trans (le_abs_self _)
  · have hlow' := lt_of_not_ge hlow
    have hdev : (((S.1 ∩ w.I).card : ℝ) -
        (w.I.card : ℝ) * k / n) ≤ -d := by
      linarith
    exact le_trans (by linarith : d ≤
      -(((S.1 ∩ w.I).card : ℝ) - (w.I.card : ℝ) * k / n))
      (neg_le_abs _)

/-- Claim 8.5 plus outer cardinality conditioning, now stated directly for
the original perturbed induced-edge polynomial.  The two remaining inputs
are exactly the outer balance tail and the fiberwise Lemma 8.3/Markov count
bound; all Fourier, splitting, and conditioning steps are discharged. -/
theorem norm_perturbedEdgePolynomial_booleanSlice_sq_le_lemma85
    {n q familySize k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {beta : ℝ} (w : Lemma82Witness G beta (q + 1) familySize)
    [Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) k)]
    (e₀ : ℝ) (coeff : Fin n → ℝ)
    (t delta c epsInner epsOuter : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1 / 2)
    (hepsInner : 0 ≤ epsInner)
    (houter : finProbability
      (BooleanSlices.BooleanSlicePoint
        (Finset.univ : Finset (Fin n)) k)
      (fun S ↦ lemma85UnbalancedFiber w c
        (booleanSlicePartitionCount w.I k S)) ≤ epsOuter)
    (hinnerCount : ∀ a : Fin (k + 1),
      ¬ lemma85UnbalancedFiber w c a →
      let ell := k - a.1
      ((Finset.univ.filter (fun YZ :
          BooleanSlices.BooleanSlicePoint w.J ell ×
            BooleanSlices.BooleanSlicePoint w.J ell ↦
        (familySize : ℝ) / 2 ≤
          badFamilyCount
            (fun b ↦ lemma85TupleBad (ell := ell) w b
              (t / (2 * Real.pi)) delta) YZ)).card : ℝ) ≤
        epsInner * Fintype.card
          (BooleanSlices.BooleanSlicePoint w.J ell ×
            BooleanSlices.BooleanSlicePoint w.J ell)) :
    ‖finCharFun
        (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)
        (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
      Real.exp 1 * Real.exp
        (-(c ^ 3 / 256) * ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
          epsInner + epsOuter := by
  classical
  let badOuter : Fin (k + 1) → Prop :=
    fun a ↦ lemma85UnbalancedFiber w c a
  let : DecidablePred badOuter := Classical.decPred _
  let B := Real.exp 1 * Real.exp
    (-(c ^ 3 / 256) * ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) + epsInner
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  apply norm_perturbedEdgePolynomial_booleanSlice_sq_le_of_split_except
    w e₀ coeff t badOuter B epsOuter hB
  · intro a ha hnot
    let ell := k - a.1
    let : Nonempty (BoolSlice ↑w.I a.1 × BoolSlice ↑w.J ell) := ha
    let : Nonempty (BoolSlice ↑w.I a.1) := Nonempty.map Prod.fst ha
    let : Nonempty (BoolSlice ↑w.J ell) := Nonempty.map Prod.snd ha
    let : Nonempty (BooleanSlices.BooleanSlicePoint w.J ell) :=
      Nonempty.map (boolSliceEquivBooleanSlicePoint w.J ell) inferInstance
    have hbal :
        c * (Fintype.card ↑w.I : ℝ) ≤ (a.1 : ℝ) ∧
          c * (Fintype.card ↑w.I : ℝ) ≤
            (Fintype.card ↑w.I : ℝ) - (a.1 : ℝ) := by
      simpa only [badOuter, lemma85UnbalancedFiber, not_not] using hnot
    have hell : ell ≤ w.J.card := by
      let y : BoolSlice ↑w.J ell := Classical.choice inferInstance
      have hy := boolSlice_size_le_card y
      simpa only [Fintype.card_coe] using hy
    have hbad : Concentration.uniformProbability
        (fun YZ : BooleanSlices.BooleanSlicePoint w.J ell ×
            BooleanSlices.BooleanSlicePoint w.J ell ↦
          (familySize : ℝ) / 2 ≤
            badFamilyCount
              (fun b ↦ lemma85TupleBad (ell := ell) w b
                (t / (2 * Real.pi)) delta) YZ) ≤ epsInner := by
      rw [Concentration.uniformProbability]
      have hcardPos : (0 : ℝ) < Fintype.card
          (BooleanSlices.BooleanSlicePoint w.J ell ×
            BooleanSlices.BooleanSlicePoint w.J ell) := by
        exact_mod_cast Fintype.card_pos
      apply (div_le_iff₀ hcardPos).2
      exact hinnerCount a (by simpa only [badOuter] using hnot)
    have hclaim := norm_splitQuadraticCharFun_sq_le_lemma85
      w (lemma81PureI w e₀ coeff) (lemma81PureJ w coeff)
      t delta c epsInner hc0 hc1 hbal.1 hbal.2 hdelta0 hdelta1 hell hbad
    simpa only [ell, B] using hclaim
  · simpa only [badOuter] using houter

/-- The asymptotic Lemma 8.3 estimate, the finite Markov step, the exact
Claim 8.5 estimate, and the outer hypergeometric balance tail assembled in
one statement for the original perturbed induced-edge polynomial. -/
theorem eventually_norm_perturbedEdgePolynomial_booleanSlice_sq_le_lemma85
    (beta eta zeta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heta : 0 < eta) (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (q familySize k : ℕ) (G : SimpleGraph (Fin n))
        [DecidableRel G.Adj]
        (w : Lemma82Witness G beta (q + 1) familySize)
        [Nonempty (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)]
        (e₀ : ℝ) (coeff : Fin n → ℝ) (t delta c d : ℝ),
        (q : ℝ) ≤ zeta * Real.log n → 0 < familySize → t ≠ 0 →
        0 < delta → delta ≤ 1 / 2 → 0 < c → c ≤ 1 / 2 →
        0 < w.I.card → 0 ≤ d →
        c * (w.I.card : ℝ) + d ≤ (w.I.card : ℝ) * k / n →
        (w.I.card : ℝ) * k / n + d ≤
          (w.I.card : ℝ) - c * w.I.card →
        (∀ a : Fin (k + 1), ¬ lemma85UnbalancedFiber w c a →
          let ell := k - a.1
          ell ≤ w.J.card ∧ eta * (w.J.card : ℝ) ≤ ell ∧
            (ell : ℝ) ≤ (1 - eta) * w.J.card) →
        ‖finCharFun
            (BooleanSlices.BooleanSlicePoint
              (Finset.univ : Finset (Fin n)) k)
            (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
          Real.exp 1 * Real.exp
            (-(c ^ 3 / 256) * ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
          2 * (8192 / (eta / 2) *
            ((|t / (2 * Real.pi)| + delta) *
              (|t / (2 * Real.pi)| +
                (n : ℝ) ^ (-(1 - beta) / 2)) /
              |t / (2 * Real.pi)|)) ^ q +
          2 * Real.exp (-d ^ 2 / (8 * w.I.card)) := by
  have hhalf := eventually_lemma85_half_bad_probability
    beta eta zeta hbeta0 hbeta1 heta hzeta
  filter_upwards [hhalf] with n hn
  intro q familySize k G _instAdj w _instSlice e₀ coeff t delta c d
    hq hfamily ht hdelta hdeltaUpper hc0 hc1 hIpos hd hleft hright hJ
  let tau : ℝ := t / (2 * Real.pi)
  let p : ℝ := (8192 / (eta / 2) *
    ((|tau| + delta) *
      (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q
  have htau : tau ≠ 0 := by
    dsimp only [tau]
    exact div_ne_zero ht (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    positivity
  have houter := lemma85UnbalancedFiber_probability_le
    w c d hIpos hd hleft hright
  apply norm_perturbedEdgePolynomial_booleanSlice_sq_le_lemma85
    w e₀ coeff t delta c (2 * p)
      (2 * Real.exp (-d ^ 2 / (8 * w.I.card)))
      hc0 hc1 hdelta.le hdeltaUpper (mul_nonneg (by norm_num) hp0) houter
  intro a hbal
  let ell := k - a.1
  obtain ⟨hell, hellower, hellupper⟩ := hJ a hbal
  let : Nonempty (BooleanSlices.BooleanSlicePoint w.J ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  have hprob := hn q familySize ell G w tau delta hq hfamily hell
    hellower hellupper htau hdelta hdeltaUpper
  rw [Concentration.uniformProbability] at hprob
  have hcardPos : (0 : ℝ) < Fintype.card
      (BooleanSlices.BooleanSlicePoint w.J ell ×
        BooleanSlices.BooleanSlicePoint w.J ell) := by
    exact_mod_cast Fintype.card_pos
  have hcount := (div_le_iff₀ hcardPos).mp hprob
  simpa only [ell, tau, p] using hcount

/-- The preceding assembly with the source's fixed quarter-balance regime.
It is enough that the global slice size lies in `[3n/8,5n/8]` and that the
tuple support occupies at most `n/4` vertices; all outer- and inner-slice
balance hypotheses then follow arithmetically. -/
theorem eventually_norm_perturbedEdgePolynomial_booleanSlice_sq_le_quarter
    (beta zeta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (q familySize k : ℕ) (G : SimpleGraph (Fin n))
        [DecidableRel G.Adj]
        (w : Lemma82Witness G beta (q + 1) familySize)
        [Nonempty (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)]
        (e₀ : ℝ) (coeff : Fin n → ℝ) (t delta : ℝ),
        (q : ℝ) ≤ zeta * Real.log n → 0 < familySize → t ≠ 0 →
        0 < delta → delta ≤ 1 / 2 →
        (w.I.card : ℝ) ≤ (n : ℝ) / 4 →
        3 * (n : ℝ) / 8 ≤ k → (k : ℝ) ≤ 5 * n / 8 →
        ‖finCharFun
            (BooleanSlices.BooleanSlicePoint
              (Finset.univ : Finset (Fin n)) k)
            (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
          Real.exp 1 * Real.exp
            (-(((1 : ℝ) / 4) ^ 3 / 256) *
              ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
          2 * (8192 / (((1 : ℝ) / 4) / 2) *
            ((|t / (2 * Real.pi)| + delta) *
              (|t / (2 * Real.pi)| +
                (n : ℝ) ^ (-(1 - beta) / 2)) /
              |t / (2 * Real.pi)|)) ^ q +
          2 * Real.exp
            (-((w.I.card : ℝ) / 16) ^ 2 / (8 * w.I.card)) := by
  have hbase :=
    eventually_norm_perturbedEdgePolynomial_booleanSlice_sq_le_lemma85
      beta (1 / 4) zeta hbeta0 hbeta1 (by norm_num) hzeta
  filter_upwards [hbase] with n hn
  intro q familySize k G _instAdj w _instSlice e₀ coeff t delta
    hq hfamily ht hdelta hdeltaUpper hIupper hkLower hkUpper
  have hIposNat : 0 < w.I.card := by
    rw [w.card_I]
    exact Nat.mul_pos hfamily (Nat.succ_pos q)
  have hIpos : (0 : ℝ) < w.I.card := by exact_mod_cast hIposNat
  have hnposNat : 0 < n := by
    have hIle : w.I.card ≤ n := by
      simpa using Finset.card_le_univ w.I
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hmeanLower : (3 : ℝ) / 8 * w.I.card ≤
      (w.I.card : ℝ) * k / n := by
    apply (le_div_iff₀ hnpos).2
    calc
      (3 / 8 : ℝ) * w.I.card * n =
          (w.I.card : ℝ) * (3 * n / 8) := by ring
      _ ≤ (w.I.card : ℝ) * k :=
        mul_le_mul_of_nonneg_left hkLower (Nat.cast_nonneg _)
  have hmeanUpper : (w.I.card : ℝ) * k / n ≤
      (5 : ℝ) / 8 * w.I.card := by
    apply (div_le_iff₀ hnpos).2
    calc
      (w.I.card : ℝ) * k ≤
          (w.I.card : ℝ) * (5 * n / 8) :=
        mul_le_mul_of_nonneg_left hkUpper (Nat.cast_nonneg _)
      _ = (5 / 8 : ℝ) * w.I.card * n := by ring
  have hleft : ((1 : ℝ) / 4) * w.I.card + w.I.card / 16 ≤
      (w.I.card : ℝ) * k / n := by
    linarith
  have hright : (w.I.card : ℝ) * k / n + w.I.card / 16 ≤
      (w.I.card : ℝ) - ((1 : ℝ) / 4) * w.I.card := by
    linarith
  apply hn q familySize k G w e₀ coeff t delta (1 / 4)
    (w.I.card / 16) hq hfamily ht hdelta hdeltaUpper
      (by norm_num) (by norm_num) hIposNat (by positivity) hleft hright
  intro a hbalanced
  let ell := k - a.1
  have hbal : ((1 : ℝ) / 4) * w.I.card ≤ (a.1 : ℝ) ∧
      ((1 : ℝ) / 4) * w.I.card ≤
        (w.I.card : ℝ) - (a.1 : ℝ) := by
    simpa only [lemma85UnbalancedFiber, Fintype.card_coe, not_not]
      using hbalanced
  have haUpper : (a.1 : ℝ) ≤ (3 : ℝ) / 4 * w.I.card := by
    linarith [hbal.2]
  have haK : a.1 ≤ k := Nat.lt_succ_iff.mp a.2
  have hellCast : (ell : ℝ) = (k : ℝ) - a.1 := by
    dsimp only [ell]
    rw [Nat.cast_sub haK]
  have hpartitionNat := w.card_I_add_card_J
  have hpartition : (w.I.card : ℝ) + w.J.card = n := by
    exact_mod_cast hpartitionNat
  have hquarterJ : ((1 : ℝ) / 4) * w.J.card ≤ ell := by
    rw [hellCast]
    nlinarith
  have hthreeQuarterJ : (ell : ℝ) ≤
      (1 - (1 : ℝ) / 4) * w.J.card := by
    rw [hellCast]
    nlinarith
  have hellReal : (ell : ℝ) ≤ w.J.card := by
    calc
      (ell : ℝ) ≤ (1 - (1 : ℝ) / 4) * w.J.card := hthreeQuarterJ
      _ ≤ w.J.card := by
        have : (0 : ℝ) ≤ w.J.card := Nat.cast_nonneg _
        norm_num
        linarith
  have hell : ell ≤ w.J.card := by exact_mod_cast hellReal
  exact ⟨hell, hquarterJ, hthreeQuarterJ⟩

/-- The source's general `η`-central fixed-size regime.  Once the tuple
support occupies at most `η n / 4` vertices, both conditioned slices retain
`η / 4` balance. -/
theorem eventually_norm_perturbedEdgePolynomial_booleanSlice_sq_le_sourceBalance
    (beta eta zeta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2) (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (q familySize k : ℕ) (G : SimpleGraph (Fin n))
        [DecidableRel G.Adj]
        (w : Lemma82Witness G beta (q + 1) familySize)
        [Nonempty (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)]
        (e₀ : ℝ) (coeff : Fin n → ℝ) (t delta : ℝ),
        (q : ℝ) ≤ zeta * Real.log n → 0 < familySize → t ≠ 0 →
        0 < delta → delta ≤ 1 / 2 →
        (w.I.card : ℝ) ≤ eta * n / 4 →
        eta * n ≤ k → (k : ℝ) ≤ (1 - eta) * n →
        ‖finCharFun
            (BooleanSlices.BooleanSlicePoint
              (Finset.univ : Finset (Fin n)) k)
            (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
          Real.exp 1 * Real.exp
            (-((eta / 4) ^ 3 / 256) *
              ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
          2 * (8192 / (((eta / 4) / 2)) *
            ((|t / (2 * Real.pi)| + delta) *
              (|t / (2 * Real.pi)| +
                (n : ℝ) ^ (-(1 - beta) / 2)) /
              |t / (2 * Real.pi)|)) ^ q +
          2 * Real.exp
            (-((eta * (w.I.card : ℝ) / 2) ^ 2) /
              (8 * w.I.card)) := by
  have hbase :=
    eventually_norm_perturbedEdgePolynomial_booleanSlice_sq_le_lemma85
      beta (eta / 4) zeta hbeta0 hbeta1 (by positivity) hzeta
  filter_upwards [hbase] with n hn
  intro q familySize k G _instAdj w _instSlice e₀ coeff t delta
    hq hfamily ht hdelta hdeltaUpper hIupper hkLower hkUpper
  have hIposNat : 0 < w.I.card := by
    rw [w.card_I]
    exact Nat.mul_pos hfamily (Nat.succ_pos q)
  have hIpos : (0 : ℝ) < w.I.card := by exact_mod_cast hIposNat
  have hnposNat : 0 < n := by
    have hIle : w.I.card ≤ n := by
      simpa using Finset.card_le_univ w.I
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hmeanLower : eta * (w.I.card : ℝ) ≤
      (w.I.card : ℝ) * k / n := by
    apply (le_div_iff₀ hnpos).2
    calc
      eta * (w.I.card : ℝ) * n =
          (w.I.card : ℝ) * (eta * n) := by ring
      _ ≤ (w.I.card : ℝ) * k :=
        mul_le_mul_of_nonneg_left hkLower (Nat.cast_nonneg _)
  have hmeanUpper : (w.I.card : ℝ) * k / n ≤
      (1 - eta) * w.I.card := by
    apply (div_le_iff₀ hnpos).2
    calc
      (w.I.card : ℝ) * k ≤
          (w.I.card : ℝ) * ((1 - eta) * n) :=
        mul_le_mul_of_nonneg_left hkUpper (Nat.cast_nonneg _)
      _ = (1 - eta) * (w.I.card : ℝ) * n := by ring
  have hleft : (eta / 4) * (w.I.card : ℝ) +
      eta * w.I.card / 2 ≤ (w.I.card : ℝ) * k / n := by
    nlinarith [mul_pos heta0 hIpos]
  have hright : (w.I.card : ℝ) * k / n +
      eta * w.I.card / 2 ≤
        (w.I.card : ℝ) - (eta / 4) * w.I.card := by
    nlinarith [mul_pos heta0 hIpos]
  apply hn q familySize k G w e₀ coeff t delta (eta / 4)
    (eta * w.I.card / 2) hq hfamily ht hdelta hdeltaUpper
      (by positivity) (by linarith) hIposNat (by positivity) hleft hright
  intro a hbalanced
  let ell := k - a.1
  have hbal : (eta / 4) * (w.I.card : ℝ) ≤ (a.1 : ℝ) ∧
      (eta / 4) * (w.I.card : ℝ) ≤
        (w.I.card : ℝ) - (a.1 : ℝ) := by
    simpa only [lemma85UnbalancedFiber, Fintype.card_coe, not_not]
      using hbalanced
  have haUpper : (a.1 : ℝ) ≤
      (1 - eta / 4) * w.I.card := by linarith [hbal.2]
  have haK : a.1 ≤ k := Nat.lt_succ_iff.mp a.2
  have hellCast : (ell : ℝ) = (k : ℝ) - a.1 := by
    dsimp only [ell]
    rw [Nat.cast_sub haK]
  have hpartitionNat := w.card_I_add_card_J
  have hpartition : (w.I.card : ℝ) + w.J.card = n := by
    exact_mod_cast hpartitionNat
  have hslack : (1 - eta / 2) * (w.I.card : ℝ) ≤
      eta * n / 4 := by
    calc
      (1 - eta / 2) * (w.I.card : ℝ) ≤ w.I.card := by
        nlinarith [mul_pos heta0 hIpos]
      _ ≤ eta * n / 4 := hIupper
  have hlowerJ : (eta / 4) * (w.J.card : ℝ) ≤ ell := by
    rw [hellCast]
    nlinarith
  have hupperJ : (ell : ℝ) ≤
      (1 - eta / 4) * w.J.card := by
    rw [hellCast]
    nlinarith
  have hellReal : (ell : ℝ) ≤ w.J.card := by
    calc
      (ell : ℝ) ≤ (1 - eta / 4) * w.J.card := hupperJ
      _ ≤ w.J.card := by
        have hJ0 : (0 : ℝ) ≤ w.J.card := Nat.cast_nonneg _
        nlinarith
  have hell : ell ≤ w.J.card := by exact_mod_cast hellReal
  exact ⟨hell, hlowerJ, hupperJ⟩

/-- Lemma 8.1 at the unabsorbed source-parameter boundary.  Lemma 8.2 now
supplies the canonical tuple family internally; the only remaining
hypotheses are the central fixed-size slice, nonzero frequency, and the
choice of the separation scale `delta`. -/
theorem ksssLemma81_raw_quarter
    (C beta : ℝ) (hC : 0 < C) (hbeta : 0 < beta)
    (hbetaHalf : beta ≤ 1 / 2) :
    ∃ zeta : ℝ, 0 < zeta ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        RamseyFree C G →
        let totalQ := Nat.floor (zeta * Real.log n)
        let q := totalQ - 1
        let familySize := Nat.ceil ((n : ℝ) ^ (1 - beta))
        ∀ (k : ℕ) [Nonempty (BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) k)]
          (e₀ : ℝ) (coeff : Fin n → ℝ) (t delta : ℝ),
          3 * (n : ℝ) / 8 ≤ k → (k : ℝ) ≤ 5 * n / 8 →
          t ≠ 0 → 0 < delta → delta ≤ 1 / 2 →
          ‖finCharFun
              (BooleanSlices.BooleanSlicePoint
                (Finset.univ : Finset (Fin n)) k)
              (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
            Real.exp 1 * Real.exp
              (-(((1 : ℝ) / 4) ^ 3 / 256) *
                ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
            2 * (8192 / (((1 : ℝ) / 4) / 2) *
              ((|t / (2 * Real.pi)| + delta) *
                (|t / (2 * Real.pi)| +
                  (n : ℝ) ^ (-(1 - beta) / 2)) /
                |t / (2 * Real.pi)|)) ^ q +
            2 * Real.exp
              (-((familySize * totalQ : ℕ) : ℝ) / (16 ^ 2 * 8)) := by
  obtain ⟨zeta, hzeta, N₈₂, hcanonical⟩ :=
    ksssLemma82_canonical_smallBeta C beta hC hbeta hbetaHalf
  have hclaim :=
    eventually_norm_perturbedEdgePolynomial_booleanSlice_sq_le_quarter
      beta zeta hbeta (hbetaHalf.trans_lt (by norm_num)) hzeta
  have hsupport := eventually_ceil_rpow_mul_floor_log_le_quarter
    beta zeta hbeta (hbetaHalf.trans (by norm_num)) hzeta.le
  have hqpos := eventually_floor_mul_log_pos zeta hzeta
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      N₈₂ ≤ n ∧
      ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤ (n : ℝ) / 4 ∧
      0 < Nat.floor (zeta * Real.log n) ∧ 1 ≤ n ∧
      (∀ (q familySize k : ℕ) (G : SimpleGraph (Fin n))
        [DecidableRel G.Adj]
        (w : Lemma82Witness G beta (q + 1) familySize)
        [Nonempty (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)]
        (e₀ : ℝ) (coeff : Fin n → ℝ) (t delta : ℝ),
        (q : ℝ) ≤ zeta * Real.log n → 0 < familySize → t ≠ 0 →
        0 < delta → delta ≤ 1 / 2 →
        (w.I.card : ℝ) ≤ (n : ℝ) / 4 →
        3 * (n : ℝ) / 8 ≤ k → (k : ℝ) ≤ 5 * n / 8 →
        ‖finCharFun
            (BooleanSlices.BooleanSlicePoint
              (Finset.univ : Finset (Fin n)) k)
            (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
          Real.exp 1 * Real.exp
            (-(((1 : ℝ) / 4) ^ 3 / 256) *
              ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
          2 * (8192 / (((1 : ℝ) / 4) / 2) *
            ((|t / (2 * Real.pi)| + delta) *
              (|t / (2 * Real.pi)| +
                (n : ℝ) ^ (-(1 - beta) / 2)) /
              |t / (2 * Real.pi)|)) ^ q +
          2 * Real.exp
            (-((w.I.card : ℝ) / 16) ^ 2 / (8 * w.I.card))) := by
    filter_upwards [Filter.eventually_ge_atTop N₈₂, hsupport, hqpos,
      Filter.eventually_ge_atTop 1, hclaim] with n hn₈₂ hsupportN hqposN hn1 hclaimN
    exact ⟨hn₈₂, hsupportN, hqposN, hn1, hclaimN⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  refine ⟨zeta, hzeta, N, ?_⟩
  intro n hn G _instAdj hG
  have hdata := hN n hn
  dsimp only
  intro k _instSlice e₀ coeff t delta hkLower hkUpper ht hdelta hdeltaUpper
  let totalQ := Nat.floor (zeta * Real.log n)
  let q := totalQ - 1
  let familySize := Nat.ceil ((n : ℝ) ^ (1 - beta))
  let w₀ : Lemma82Witness G beta totalQ familySize :=
    Classical.choice (hcanonical n hdata.1 G hG)
  have hqSucc : q + 1 = totalQ := by
    dsimp only [q]
    exact Nat.sub_add_cancel hdata.2.2.1
  let w : Lemma82Witness G beta (q + 1) familySize := by
    simpa only [hqSucc] using w₀
  have hqLeTotal : q ≤ totalQ := Nat.sub_le _ _
  have htotalCast : (totalQ : ℝ) ≤ zeta * Real.log n := by
    dsimp only [totalQ]
    exact Nat.floor_le (zero_le_one.trans (Nat.floor_pos.mp hdata.2.2.1))
  have hqCast : (q : ℝ) ≤ zeta * Real.log n := by
    exact (by exact_mod_cast hqLeTotal : (q : ℝ) ≤ totalQ).trans htotalCast
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfamily : 0 < familySize := by
    dsimp only [familySize]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos _)
  have hIupper : (w.I.card : ℝ) ≤ (n : ℝ) / 4 := by
    rw [w.card_I, hqSucc]
    simpa only [familySize, totalQ] using hdata.2.1
  have hraw := hdata.2.2.2.2 q familySize k G w e₀ coeff t delta
    hqCast hfamily ht hdelta hdeltaUpper hIupper hkLower hkUpper
  have hIcard : w.I.card = familySize * totalQ := by
    rw [w.card_I, hqSucc]
  rw [hIcard] at hraw
  have hsupportPos : (0 : ℝ) < familySize * totalQ := by
    exact_mod_cast Nat.mul_pos hfamily hdata.2.2.1
  have htail : -(((familySize * totalQ : ℕ) : ℝ) / 16) ^ 2 /
        (8 * (familySize * totalQ : ℕ)) =
      -((familySize * totalQ : ℕ) : ℝ) / (16 ^ 2 * 8) := by
    field_simp [ne_of_gt hsupportPos]
  rw [htail] at hraw
  simpa only [familySize, totalQ, q] using hraw

/-- Lemma 8.1 at the unabsorbed source balance boundary.  This version has
the full `η n ≤ k ≤ (1-η)n` range and already installs the canonical
Lemma 8.2 family. -/
theorem ksssLemma81_raw_sourceBalance
    (C beta eta : ℝ) (hC : 0 < C) (hbeta : 0 < beta)
    (hbetaHalf : beta ≤ 1 / 2) (heta : 0 < eta)
    (hetaHalf : eta < 1 / 2) :
    ∃ zeta : ℝ, 0 < zeta ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        RamseyFree C G →
        let totalQ := Nat.floor (zeta * Real.log n)
        let q := totalQ - 1
        let familySize := Nat.ceil ((n : ℝ) ^ (1 - beta))
        ∀ (k : ℕ) [Nonempty (BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) k)]
          (e₀ : ℝ) (coeff : Fin n → ℝ) (t delta : ℝ),
          eta * n ≤ k → (k : ℝ) ≤ (1 - eta) * n →
          t ≠ 0 → 0 < delta → delta ≤ 1 / 2 →
          ‖finCharFun
              (BooleanSlices.BooleanSlicePoint
                (Finset.univ : Finset (Fin n)) k)
              (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
            Real.exp 1 * Real.exp
              (-((eta / 4) ^ 3 / 256) *
                ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
            2 * (8192 / (((eta / 4) / 2)) *
              ((|t / (2 * Real.pi)| + delta) *
                (|t / (2 * Real.pi)| +
                  (n : ℝ) ^ (-(1 - beta) / 2)) /
                |t / (2 * Real.pi)|)) ^ q +
            2 * Real.exp
              (-(eta ^ 2 * ((familySize * totalQ : ℕ) : ℝ) / 32)) := by
  obtain ⟨zeta, hzeta, N₈₂, hcanonical⟩ :=
    ksssLemma82_canonical_smallBeta C beta hC hbeta hbetaHalf
  have hclaim :=
    eventually_norm_perturbedEdgePolynomial_booleanSlice_sq_le_sourceBalance
      beta eta zeta hbeta (hbetaHalf.trans_lt (by norm_num))
        heta hetaHalf hzeta
  have hsupport := eventually_ceil_rpow_mul_floor_log_le_mul
    beta zeta (eta / 4) hbeta (hbetaHalf.trans (by norm_num))
      hzeta.le (by positivity)
  have hqpos := eventually_floor_mul_log_pos zeta hzeta
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      N₈₂ ≤ n ∧
      ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤ eta * n / 4 ∧
      0 < Nat.floor (zeta * Real.log n) ∧ 1 ≤ n ∧
      (∀ (q familySize k : ℕ) (G : SimpleGraph (Fin n))
        [DecidableRel G.Adj]
        (w : Lemma82Witness G beta (q + 1) familySize)
        [Nonempty (BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) k)]
        (e₀ : ℝ) (coeff : Fin n → ℝ) (t delta : ℝ),
        (q : ℝ) ≤ zeta * Real.log n → 0 < familySize → t ≠ 0 →
        0 < delta → delta ≤ 1 / 2 →
        (w.I.card : ℝ) ≤ eta * n / 4 →
        eta * n ≤ k → (k : ℝ) ≤ (1 - eta) * n →
        ‖finCharFun
            (BooleanSlices.BooleanSlicePoint
              (Finset.univ : Finset (Fin n)) k)
            (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
          Real.exp 1 * Real.exp
            (-((eta / 4) ^ 3 / 256) *
              ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
          2 * (8192 / (((eta / 4) / 2)) *
            ((|t / (2 * Real.pi)| + delta) *
              (|t / (2 * Real.pi)| +
                (n : ℝ) ^ (-(1 - beta) / 2)) /
              |t / (2 * Real.pi)|)) ^ q +
          2 * Real.exp
            (-((eta * (w.I.card : ℝ) / 2) ^ 2) /
              (8 * w.I.card))) := by
    filter_upwards [Filter.eventually_ge_atTop N₈₂, hsupport, hqpos,
      Filter.eventually_ge_atTop 1, hclaim]
      with n hn₈₂ hsupportN hqposN hn1 hclaimN
    have hsupportN' :
        ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤ eta * n / 4 := by
      convert hsupportN using 1 <;> ring
    exact ⟨hn₈₂, hsupportN', hqposN, hn1, hclaimN⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  refine ⟨zeta, hzeta, N, ?_⟩
  intro n hn G _instAdj hG
  have hdata := hN n hn
  dsimp only
  intro k _instSlice e₀ coeff t delta hkLower hkUpper ht hdelta hdeltaUpper
  let totalQ := Nat.floor (zeta * Real.log n)
  let q := totalQ - 1
  let familySize := Nat.ceil ((n : ℝ) ^ (1 - beta))
  let w₀ : Lemma82Witness G beta totalQ familySize :=
    Classical.choice (hcanonical n hdata.1 G hG)
  have hqSucc : q + 1 = totalQ := by
    dsimp only [q]
    exact Nat.sub_add_cancel hdata.2.2.1
  let w : Lemma82Witness G beta (q + 1) familySize := by
    simpa only [hqSucc] using w₀
  have hqLeTotal : q ≤ totalQ := Nat.sub_le _ _
  have htotalCast : (totalQ : ℝ) ≤ zeta * Real.log n := by
    dsimp only [totalQ]
    exact Nat.floor_le (zero_le_one.trans (Nat.floor_pos.mp hdata.2.2.1))
  have hqCast : (q : ℝ) ≤ zeta * Real.log n := by
    exact (by exact_mod_cast hqLeTotal : (q : ℝ) ≤ totalQ).trans htotalCast
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfamily : 0 < familySize := by
    dsimp only [familySize]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos _)
  have hIupper : (w.I.card : ℝ) ≤ eta * n / 4 := by
    rw [w.card_I, hqSucc]
    simpa only [familySize, totalQ] using hdata.2.1
  have hraw := hdata.2.2.2.2 q familySize k G w e₀ coeff t delta
    hqCast hfamily ht hdelta hdeltaUpper hIupper hkLower hkUpper
  have hIcard : w.I.card = familySize * totalQ := by
    rw [w.card_I, hqSucc]
  rw [hIcard] at hraw
  have hsupportPos : (0 : ℝ) < familySize * totalQ := by
    exact_mod_cast Nat.mul_pos hfamily hdata.2.2.1
  have htail : -((eta * ((familySize * totalQ : ℕ) : ℝ) / 2) ^ 2) /
        (8 * (familySize * totalQ : ℕ)) =
      -(eta ^ 2 * ((familySize * totalQ : ℕ) : ℝ) / 32) := by
    field_simp [ne_of_gt hsupportPos]
    ring
  rw [htail] at hraw
  simpa only [familySize, totalQ, q] using hraw

/-- The fixed small base used to turn the logarithmic tuple length into
`n⁻²⁶` decay. -/
noncomputable def lemma81DecayBase (zeta : ℝ) : ℝ := Real.exp (-26 / zeta)

/-- An explicit positive upper-frequency cutoff for Lemma 8.1. -/
noncomputable def lemma81Cutoff (eta zeta : ℝ) : ℝ :=
  lemma81DecayBase zeta /
    (4 * (8192 / (((eta / 4) / 2))))

lemma lemma81DecayBase_pos (zeta : ℝ) : 0 < lemma81DecayBase zeta := by
  simp only [lemma81DecayBase]
  positivity

lemma lemma81Cutoff_pos {eta zeta : ℝ} (heta : 0 < eta) :
    0 < lemma81Cutoff eta zeta := by
  unfold lemma81Cutoff
  have hrho := lemma81DecayBase_pos zeta
  positivity

/-- The source choices `β=η/3`, `δ=n⁻¹ᐟ²⁺ηᐟ³` make the Lemma 8.3
one-tuple base uniformly small throughout the Lemma 8.1 frequency band. -/
lemma eventually_lemma81_middle_base_le
    (eta zeta : ℝ) (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ t : ℝ,
      (n : ℝ) ^ (-1 + eta) ≤ |t| →
      |t| ≤ lemma81Cutoff eta zeta →
      8192 / (((eta / 4) / 2)) *
          ((|t / (2 * Real.pi)| + (n : ℝ) ^ (-1 / 2 + eta / 3)) *
            (|t / (2 * Real.pi)| +
              (n : ℝ) ^ (-(1 - eta / 3) / 2)) /
            |t / (2 * Real.pi)|) ≤ lemma81DecayBase zeta := by
  let K : ℝ := 8192 / (((eta / 4) / 2))
  let rho : ℝ := lemma81DecayBase zeta
  have hK : 0 < K := by dsimp only [K]; positivity
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lemma81DecayBase_pos zeta
  have hdExp : -1 / 2 + eta / 3 < 0 := by linarith
  have hsExp : -(1 - eta / 3) / 2 < 0 := by linarith
  have hcrossExp : -eta / 2 < 0 := by linarith
  have hdEvent := eventually_const_mul_rpow_le_rpow
    (4 * K / rho) (-1 / 2 + eta / 3) 0 (by positivity) hdExp
  have hsEvent := eventually_const_mul_rpow_le_rpow
    (4 * K / rho) (-(1 - eta / 3) / 2) 0 (by positivity) hsExp
  have hcrossEvent := eventually_const_mul_rpow_le_rpow
    (4 * K * (2 * Real.pi) / rho) (-eta / 2) 0
      (by positivity) hcrossExp
  filter_upwards [hdEvent, hsEvent, hcrossEvent,
    Filter.eventually_ge_atTop 1] with n hdN hsN hcrossN hn
  intro t htLower htUpper
  let a : ℝ := |t / (2 * Real.pi)|
  let d : ℝ := (n : ℝ) ^ (-1 / 2 + eta / 3)
  let s : ℝ := (n : ℝ) ^ (-(1 - eta / 3) / 2)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have haEq : a = |t| / (2 * Real.pi) := by
    dsimp only [a]
    rw [abs_div, abs_mul]
    rw [abs_of_pos Real.pi_pos]
    norm_num
  have htAbsPos : 0 < |t| :=
    (Real.rpow_pos_of_pos hnpos _).trans_le htLower
  have haPos : 0 < a := by rw [haEq]; positivity
  have hd0 : 0 ≤ d := Real.rpow_nonneg hnpos.le _
  have hs0 : 0 ≤ s := Real.rpow_nonneg hnpos.le _
  have haUpper : a ≤ lemma81Cutoff eta zeta := by
    rw [haEq]
    calc
      |t| / (2 * Real.pi) ≤ |t| := by
        apply div_le_self (abs_nonneg t)
        nlinarith [Real.pi_gt_three]
      _ ≤ lemma81Cutoff eta zeta := htUpper
  have hKnu : K * lemma81Cutoff eta zeta = rho / 4 := by
    dsimp only [K, rho, lemma81Cutoff]
    field_simp [ne_of_gt heta]
  have hKa : K * a ≤ rho / 4 := by
    rw [← hKnu]
    exact mul_le_mul_of_nonneg_left haUpper hK.le
  have hKd : K * d ≤ rho / 4 := by
    have hdN' : (4 * K / rho) * d ≤ 1 := by
      simpa only [d, Real.rpow_zero] using hdN
    calc
      K * d = (rho / 4) * ((4 * K / rho) * d) := by
        field_simp [ne_of_gt hrho]
      _ ≤ (rho / 4) * 1 :=
        mul_le_mul_of_nonneg_left hdN' (by positivity)
      _ = rho / 4 := by ring
  have hKs : K * s ≤ rho / 4 := by
    have hsN' : (4 * K / rho) * s ≤ 1 := by
      simpa only [s, Real.rpow_zero] using hsN
    calc
      K * s = (rho / 4) * ((4 * K / rho) * s) := by
        field_simp [ne_of_gt hrho]
      _ ≤ (rho / 4) * 1 :=
        mul_le_mul_of_nonneg_left hsN' (by positivity)
      _ = rho / 4 := by ring
  have hds : d * s = (n : ℝ) ^ (-1 + eta / 2) := by
    dsimp only [d, s]
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hcross : d * s / a ≤
      2 * Real.pi * (n : ℝ) ^ (-eta / 2) := by
    rw [hds, haEq]
    calc
      (n : ℝ) ^ (-1 + eta / 2) / (|t| / (2 * Real.pi)) =
          2 * Real.pi * ((n : ℝ) ^ (-1 + eta / 2) / |t|) := by
        field_simp [ne_of_gt htAbsPos, ne_of_gt Real.pi_pos]
      _ ≤ 2 * Real.pi *
          ((n : ℝ) ^ (-1 + eta / 2) /
            (n : ℝ) ^ (-1 + eta)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_left
          (Real.rpow_nonneg hnpos.le _) (Real.rpow_pos_of_pos hnpos _)
            htLower
      _ = 2 * Real.pi * (n : ℝ) ^ (-eta / 2) := by
        rw [← Real.rpow_sub hnpos]
        congr 2
        ring
  have hKcross : K * (d * s / a) ≤ rho / 4 := by
    calc
      K * (d * s / a) ≤
          K * (2 * Real.pi * (n : ℝ) ^ (-eta / 2)) :=
        mul_le_mul_of_nonneg_left hcross hK.le
      _ = (rho / 4) *
          ((4 * K * (2 * Real.pi) / rho) *
            (n : ℝ) ^ (-eta / 2)) := by
        field_simp [ne_of_gt hrho]
      _ ≤ (rho / 4) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Real.rpow_zero] using hcrossN
      _ = rho / 4 := by ring
  have hsplit : (a + d) * (a + s) / a =
      a + d + s + d * s / a := by
    field_simp [ne_of_gt haPos]
    ring
  change K * ((a + d) * (a + s) / a) ≤ rho
  rw [hsplit]
  calc
    K * (a + d + s + d * s / a) =
        K * a + K * d + K * s + K * (d * s / a) := by ring
    _ ≤ rho / 4 + rho / 4 + rho / 4 + rho / 4 :=
      add_le_add (add_le_add (add_le_add hKa hKd) hKs) hKcross
    _ = rho := by ring

/-- With the source parameter choices, all three terms in the raw squared
characteristic-function estimate are together at most `n⁻¹²`. -/
lemma eventually_lemma81_raw_rhs_le
    (eta zeta : ℝ) (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ t : ℝ,
      (n : ℝ) ^ (-1 + eta) ≤ |t| →
      |t| ≤ lemma81Cutoff eta zeta →
      let totalQ := Nat.floor (zeta * Real.log n)
      let q := totalQ - 1
      let familySize := Nat.ceil ((n : ℝ) ^ (1 - eta / 3))
      Real.exp 1 * Real.exp
          (-((eta / 4) ^ 3 / 256) *
            ((familySize / 2 : ℕ) : ℝ) *
            ((n : ℝ) ^ (-1 / 2 + eta / 3)) ^ 2) +
        2 * (8192 / (((eta / 4) / 2)) *
          ((|t / (2 * Real.pi)| + (n : ℝ) ^ (-1 / 2 + eta / 3)) *
            (|t / (2 * Real.pi)| +
              (n : ℝ) ^ (-(1 - eta / 3) / 2)) /
            |t / (2 * Real.pi)|)) ^ q +
        2 * Real.exp
          (-(eta ^ 2 * ((familySize * totalQ : ℕ) : ℝ) / 32)) ≤
        (n : ℝ) ^ (-12 : ℝ) := by
  let cFirst : ℝ := (eta / 4) ^ 3 / 1024
  have hcFirst : 0 < cFirst := by dsimp only [cFirst]; positivity
  have hpFirst : 0 < eta / 3 := by positivity
  have hpTail : 0 < 1 - eta / 3 := by linarith
  have hmiddleBase := eventually_lemma81_middle_base_le
    eta zeta heta hetaHalf hzeta
  have hfamilyGrow := eventually_const_le_natCast_rpow
    2 (1 - eta / 3) hpTail
  have hqpos := eventually_floor_mul_log_pos zeta hzeta
  have hfirstDecay := eventually_const_mul_exp_neg_const_rpow_le_rpow
    (3 * Real.exp 1) cFirst (eta / 3) 12 (by positivity)
      hcFirst hpFirst (by norm_num)
  have htailDecay := eventually_const_mul_exp_neg_const_rpow_le_rpow
    6 (eta ^ 2 / 32) (1 - eta / 3) 12 (by norm_num)
      (by positivity) hpTail (by norm_num)
  have hmiddleDecay :=
    eventually_const_mul_exp_neg_div_pow_floor_log_sub_one_le
      6 zeta 26 12 (by norm_num) hzeta (by norm_num) (by norm_num)
  filter_upwards [hmiddleBase, hfamilyGrow, hqpos, hfirstDecay,
    htailDecay, hmiddleDecay, Filter.eventually_ge_atTop 1]
    with n hbaseN hfamilyGrowN hqposN hfirstN htailN hmiddleN hn
  intro t htLower htUpper
  dsimp only
  let totalQ : ℕ := Nat.floor (zeta * Real.log n)
  let q : ℕ := totalQ - 1
  let familySize : ℕ := Nat.ceil ((n : ℝ) ^ (1 - eta / 3))
  let delta : ℝ := (n : ℝ) ^ (-1 / 2 + eta / 3)
  let base : ℝ := 8192 / (((eta / 4) / 2)) *
    ((|t / (2 * Real.pi)| + delta) *
      (|t / (2 * Real.pi)| +
        (n : ℝ) ^ (-(1 - eta / 3) / 2)) /
      |t / (2 * Real.pi)|)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfamilyLower : (n : ℝ) ^ (1 - eta / 3) ≤ familySize := by
    dsimp only [familySize]
    exact Nat.le_ceil _
  have hfamilyHalf : (n : ℝ) ^ (1 - eta / 3) / 4 ≤
      ((familySize / 2 : ℕ) : ℝ) := by
    have hfamilyGrowN' : 2 ≤ (n : ℝ) ^ (1 - eta / 3) := hfamilyGrowN
    have hnat : familySize ≤ 2 * (familySize / 2) + 1 := by omega
    have hcast : (familySize : ℝ) ≤
        2 * ((familySize / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
    nlinarith
  have hdeltaSq : delta ^ 2 =
      (n : ℝ) ^ (-1 + 2 * eta / 3) := by
    dsimp only [delta]
    rw [pow_two, ← Real.rpow_add hnpos]
    congr 1
    ring
  have hscaleProduct :
      ((n : ℝ) ^ (1 - eta / 3) / 4) * delta ^ 2 =
        (n : ℝ) ^ (eta / 3) / 4 := by
    rw [hdeltaSq]
    rw [div_mul_eq_mul_div, ← Real.rpow_add hnpos]
    congr 1
    ring_nf
  have hfirstExponent : cFirst * (n : ℝ) ^ (eta / 3) ≤
      ((eta / 4) ^ 3 / 256) *
        ((familySize / 2 : ℕ) : ℝ) * delta ^ 2 := by
    calc
      cFirst * (n : ℝ) ^ (eta / 3) =
          ((eta / 4) ^ 3 / 256) *
            ((n : ℝ) ^ (eta / 3) / 4) := by
        dsimp only [cFirst]
        ring
      _ = ((eta / 4) ^ 3 / 256) *
          (((n : ℝ) ^ (1 - eta / 3) / 4) * delta ^ 2) := by
        rw [hscaleProduct]
      _ = ((eta / 4) ^ 3 / 256) *
          ((n : ℝ) ^ (1 - eta / 3) / 4) * delta ^ 2 := by ring
      _ ≤ ((eta / 4) ^ 3 / 256) *
          ((familySize / 2 : ℕ) : ℝ) * delta ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfamilyHalf (by positivity))
          (sq_nonneg delta)
  have hfirst : Real.exp 1 * Real.exp
      (-((eta / 4) ^ 3 / 256) *
        ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) ≤
      (n : ℝ) ^ (-12 : ℝ) / 3 := by
    have hmono : Real.exp
        (-((eta / 4) ^ 3 / 256) *
          ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) ≤
        Real.exp (-cFirst * (n : ℝ) ^ (eta / 3)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ Real.exp 1)
    have hdecay : 3 * (Real.exp 1 *
        Real.exp (-cFirst * (n : ℝ) ^ (eta / 3))) ≤
        (n : ℝ) ^ (-12 : ℝ) := by
      simpa only [mul_assoc] using hfirstN
    nlinarith
  have htotalQ : 1 ≤ totalQ := by
    dsimp only [totalQ]
    omega
  have hsupportLower : (n : ℝ) ^ (1 - eta / 3) ≤
      ((familySize * totalQ : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    calc
      (n : ℝ) ^ (1 - eta / 3) ≤ familySize := hfamilyLower
      _ ≤ (familySize : ℝ) * totalQ := by
        nlinarith [show (0 : ℝ) ≤ familySize by positivity,
          (by exact_mod_cast htotalQ : (1 : ℝ) ≤ totalQ)]
  have htail : 2 * Real.exp
      (-(eta ^ 2 * ((familySize * totalQ : ℕ) : ℝ) / 32)) ≤
      (n : ℝ) ^ (-12 : ℝ) / 3 := by
    have hcoef : 0 < eta ^ 2 / 32 := by positivity
    have hmono : Real.exp
        (-(eta ^ 2 * ((familySize * totalQ : ℕ) : ℝ) / 32)) ≤
        Real.exp (-(eta ^ 2 / 32) *
          (n : ℝ) ^ (1 - eta / 3)) := by
      apply Real.exp_le_exp.mpr
      have hscaled := mul_le_mul_of_nonneg_left hsupportLower hcoef.le
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 6)
    have htailN' : 6 * Real.exp
        (-(eta ^ 2 / 32) * (n : ℝ) ^ (1 - eta / 3)) ≤
        (n : ℝ) ^ (-12 : ℝ) := htailN
    nlinarith
  have hbase : base ≤ lemma81DecayBase zeta := by
    simpa only [base, delta] using hbaseN t htLower htUpper
  have hbase0 : 0 ≤ base := by
    dsimp only [base, delta]
    positivity
  have hmiddle : 2 * base ^ q ≤ (n : ℝ) ^ (-12 : ℝ) / 3 := by
    have hpow : base ^ q ≤ lemma81DecayBase zeta ^ q :=
      pow_le_pow_left₀ hbase0 hbase q
    have hscaled := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 6)
    have hmiddleN' : 6 * lemma81DecayBase zeta ^ q ≤
        (n : ℝ) ^ (-12 : ℝ) := by
      simpa only [lemma81DecayBase, totalQ, q] using hmiddleN
    nlinarith
  change Real.exp 1 * Real.exp
          (-((eta / 4) ^ 3 / 256) *
            ((familySize / 2 : ℕ) : ℝ) * delta ^ 2) +
        2 * base ^ q +
        2 * Real.exp
          (-(eta ^ 2 * ((familySize * totalQ : ℕ) : ℝ) / 32)) ≤
      (n : ℝ) ^ (-12 : ℝ)
  linarith

/-- Kwan--Sah--Sauermann--Sawhney Lemma 8.1, with an explicit positive
cutoff.  The characteristic function is that of the original perturbed
induced-edge count on a uniform fixed-size vertex slice. -/
theorem ksssLemma81
    (C eta : ℝ) (hC : 0 < C) (heta : 0 < eta)
    (hetaHalf : eta < 1 / 2) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        RamseyFree C G →
        ∀ (k : ℕ) [Nonempty (BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) k)]
          (e₀ : ℝ) (coeff : Fin n → ℝ) (t : ℝ),
          eta * n ≤ k → (k : ℝ) ≤ (1 - eta) * n →
          (n : ℝ) ^ (-1 + eta) ≤ |t| → |t| ≤ nu →
          ‖finCharFun
              (BooleanSlices.BooleanSlicePoint
                (Finset.univ : Finset (Fin n)) k)
              (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ≤
            (n : ℝ) ^ (-5 : ℝ) := by
  have hbeta : 0 < eta / 3 := by positivity
  have hbetaHalf : eta / 3 ≤ (1 : ℝ) / 2 := by linarith
  obtain ⟨zeta, hzeta, Nraw, hraw⟩ :=
    ksssLemma81_raw_sourceBalance C (eta / 3) eta hC hbeta
      hbetaHalf heta hetaHalf
  let nu : ℝ := lemma81Cutoff eta zeta
  have hnu : 0 < nu := by
    dsimp only [nu]
    exact lemma81Cutoff_pos heta
  have hnumeric := eventually_lemma81_raw_rhs_le
    eta zeta heta hetaHalf hzeta
  have hdeltaUpper := eventually_const_mul_rpow_le_rpow
    2 (-1 / 2 + eta / 3) 0 (by norm_num) (by linarith)
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      Nraw ≤ n ∧
      (∀ t : ℝ, (n : ℝ) ^ (-1 + eta) ≤ |t| →
        |t| ≤ nu →
        let totalQ := Nat.floor (zeta * Real.log n)
        let q := totalQ - 1
        let familySize := Nat.ceil ((n : ℝ) ^ (1 - eta / 3))
        Real.exp 1 * Real.exp
            (-((eta / 4) ^ 3 / 256) *
              ((familySize / 2 : ℕ) : ℝ) *
              ((n : ℝ) ^ (-1 / 2 + eta / 3)) ^ 2) +
          2 * (8192 / (((eta / 4) / 2)) *
            ((|t / (2 * Real.pi)| + (n : ℝ) ^ (-1 / 2 + eta / 3)) *
              (|t / (2 * Real.pi)| +
                (n : ℝ) ^ (-(1 - eta / 3) / 2)) /
              |t / (2 * Real.pi)|)) ^ q +
          2 * Real.exp
            (-(eta ^ 2 * ((familySize * totalQ : ℕ) : ℝ) / 32)) ≤
          (n : ℝ) ^ (-12 : ℝ)) ∧
      2 * (n : ℝ) ^ (-1 / 2 + eta / 3) ≤ 1 ∧ 1 ≤ n := by
    filter_upwards [Filter.eventually_ge_atTop Nraw, hnumeric,
      hdeltaUpper, Filter.eventually_ge_atTop 1]
      with n hnRaw hnumericN hdeltaN hn1
    have hdeltaN' : 2 * (n : ℝ) ^ (-1 / 2 + eta / 3) ≤ 1 := by
      simpa only [Real.rpow_zero] using hdeltaN
    exact ⟨hnRaw, by simpa only [nu] using hnumericN, hdeltaN', hn1⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  refine ⟨nu, hnu, N, ?_⟩
  intro n hn G _instAdj hG k _instSlice e₀ coeff t
    hkLower hkUpper htLower htUpper
  have hdata := hN n hn
  let delta : ℝ := (n : ℝ) ^ (-1 / 2 + eta / 3)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdata.2.2.2)
  have ht : t ≠ 0 := by
    have : 0 < |t| := (Real.rpow_pos_of_pos hnpos _).trans_le htLower
    exact abs_pos.mp this
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact Real.rpow_pos_of_pos hnpos _
  have hdeltaUpper' : delta ≤ 1 / 2 := by
    dsimp only [delta]
    linarith [hdata.2.2.1]
  have hrawN := hraw n hdata.1 G hG k e₀ coeff t delta
    hkLower hkUpper ht hdelta hdeltaUpper'
  have hnumericN := hdata.2.1 t htLower htUpper
  have hsq :
      ‖finCharFun
          (BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) k)
          (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ^ 2 ≤
        (n : ℝ) ^ (-12 : ℝ) := by
    exact hrawN.trans (by simpa only [delta] using hnumericN)
  have hpowSq : ((n : ℝ) ^ (-6 : ℝ)) ^ 2 =
      (n : ℝ) ^ (-12 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hnpos]
    norm_num
  have hroot :
      ‖finCharFun
          (BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) k)
          (fun S ↦ Probability.perturbedEdgePolynomial G e₀ coeff S.1) t‖ ≤
        (n : ℝ) ^ (-6 : ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (Real.rpow_nonneg hnpos.le _)).mp
    rwa [hpowSq]
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hdata.2.2.2) (by norm_num))

end QuadraticCancellation
end Erdos88
