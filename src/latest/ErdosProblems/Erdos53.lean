/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 53.
https://www.erdosproblems.com/forum/thread/53

Informal authors:
- Paul Erdős
- Endre Szemerédi
- Mei-Chu Chang

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos53.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 53.
https://www.erdosproblems.com/forum/thread/53

Informal authors:
- Paul Erdős
- Endre Szemerédi
- Mei-Chu Chang

Formal authors:
- OpenAI Codex

Primary references:
- P. Erdős and E. Szemerédi, "On sums and products of integers" (1983).
- M.-C. Chang, "The Erdős--Szemerédi problem on sum set and product set",
  Annals of Mathematics 157 (2003), 939--957.
-/
import Mathlib.Combinatorics.Additive.SubsetSum
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecificLimits.Normed

namespace Erdos53

open scoped BigOperators Pointwise

noncomputable section

section CoordinateProjection

/-- A finite-dimensional subspace of a finitely-supported coordinate space
can be separated by no more coordinates than its dimension. -/
theorem exists_finset_coord_restrict_injective_of_injective
    {R ι V : Type*} [Field R] [AddCommGroup V] [Module R V]
    [FiniteDimensional R V]
    (f : V →ₗ[R] ι →₀ R) (hf : Function.Injective f) :
    ∃ s : Finset ι, s.card ≤ Module.finrank R V ∧
      Function.Injective (fun x : V ↦ fun i : s ↦ f x i) := by
  classical
  induction hdim : Module.finrank R V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hn : n = 0
      · have hzero : Module.finrank R V = 0 := hdim.trans hn
        let _ : Subsingleton V := Module.finrank_zero_iff.mp hzero
        exact ⟨∅, by simp, fun _ _ _ ↦ Subsingleton.elim _ _⟩
      · have hpos : 0 < Module.finrank R V := hdim ▸ Nat.pos_of_ne_zero hn
        obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
        have hfx : f x ≠ 0 := fun h ↦ hx (hf (h.trans (map_zero f).symm))
        obtain ⟨j, hj⟩ : ∃ j, f x j ≠ 0 := by
          by_contra! hall
          apply hfx
          apply Finsupp.ext
          intro j
          simpa using hall j
        let e : V →ₗ[R] R := (Finsupp.lapply j).comp f
        have he : e ≠ 0 := by
          intro heq
          have := LinearMap.congr_fun heq x
          apply hj
          simpa [e] using this
        have hker : Module.finrank R (LinearMap.ker e) + 1 =
            Module.finrank R V := Module.Dual.finrank_ker_add_one_of_ne_zero he
        have hlt : Module.finrank R (LinearMap.ker e) < n := by
          rw [← hdim]
          omega
        let g : LinearMap.ker e →ₗ[R] ι →₀ R := f.comp (LinearMap.ker e).subtype
        have hg : Function.Injective g := hf.comp Subtype.val_injective
        obtain ⟨s, hs_card, hs_inj⟩ :=
          ih (Module.finrank R (LinearMap.ker e)) hlt g hg rfl
        refine ⟨insert j s, ?_, ?_⟩
        · calc
            (insert j s).card ≤ s.card + 1 := Finset.card_insert_le _ _
            _ ≤ Module.finrank R (LinearMap.ker e) + 1 := Nat.add_le_add_right hs_card 1
            _ = Module.finrank R V := hker
            _ = n := hdim
        · intro a b hab
          have habj : f a j = f b j := congrFun hab ⟨j, Finset.mem_insert_self j s⟩
          have hzmem : a - b ∈ LinearMap.ker e := by
            rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
            simpa [e] using habj
          let z : LinearMap.ker e := ⟨a - b, hzmem⟩
          have hz : z = 0 := hs_inj (by
            funext i
            simpa only [z, g, LinearMap.comp_apply, Submodule.coe_subtype, map_sub,
              map_zero, Finsupp.sub_apply, Finsupp.zero_apply, sub_eq_zero] using
              congrFun hab ⟨i, Finset.mem_insert_of_mem i.property⟩)
          exact sub_eq_zero.mp (congrArg Subtype.val hz)

theorem exists_finset_coord_restrict_injective
    {R ι : Type*} [Field R] (W : Submodule R (ι →₀ R))
    [FiniteDimensional R W] :
    ∃ s : Finset ι, s.card ≤ Module.finrank R W ∧
      Function.Injective (fun x : W ↦ fun i : s ↦ (x : ι →₀ R) i) := by
  simpa using
    (exists_finset_coord_restrict_injective_of_injective
      (R := R) (ι := ι) (V := W) W.subtype W.injective_subtype)

end CoordinateProjection

section CoefficientBox

/-- Linear independence makes the bounded coefficient box injective. -/
theorem coefficientBox_injective
    {R M : Type*} [Field R] [CharZero R]
    [AddCommGroup M] [Module R M]
    {d H : ℕ} {v : Fin d → M} (hv : LinearIndependent R v) :
    Function.Injective
      (fun a : Fin d → Fin H ↦ ∑ i, (a i : R) • v i) := by
  intro a b hab
  funext i
  apply Fin.ext
  have hcoord : (a i : R) = (b i : R) := hv.eq_coords_of_eq hab i
  exact_mod_cast hcoord

theorem card_coefficientBox
    {R M : Type*} [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [DecidableEq M]
    {d H : ℕ} {v : Fin d → M} (hv : LinearIndependent R v) :
    (Finset.univ.image
      (fun a : Fin d → Fin H ↦ ∑ i, (a i : R) • v i)).card = H ^ d := by
  classical
  rw [Finset.card_image_of_injective Finset.univ (coefficientBox_injective hv)]
  simp

/-- A finite set contains a linearly independent family of size its span rank. -/
theorem finiteSet_exists_independent_spanning_family
    {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    (A : Finset M) :
    ∃ v : Fin (Module.finrank R (Submodule.span R (A : Set M))) → M,
      (∀ i, v i ∈ A) ∧
      Submodule.span R (Set.range v) = Submodule.span R (A : Set M) ∧
      LinearIndependent R v := by
  exact Submodule.exists_fun_fin_finrank_span_eq R (A : Set M)

end CoefficientBox

section SimpleProducts

variable {M : Type*} [CommMonoid M] [DecidableEq M]

/-- Products of subsets of `A`; every member of `A` is used at most once.
The empty subset contributes `1`. -/
def subsetProducts (A : Finset M) : Finset M :=
  A.powerset.image fun B ↦ ∏ b ∈ B, b

@[simp] lemma mem_subsetProducts_iff {A : Finset M} {x : M} :
    x ∈ subsetProducts A ↔ ∃ B ⊆ A, ∏ b ∈ B, b = x := by
  simp [subsetProducts]

@[simp] lemma one_mem_subsetProducts (A : Finset M) : 1 ∈ subsetProducts A := by
  exact mem_subsetProducts_iff.mpr ⟨∅, Finset.empty_subset _, by simp⟩

@[simp] lemma subsetProducts_nonempty (A : Finset M) : (subsetProducts A).Nonempty :=
  ⟨1, one_mem_subsetProducts A⟩

lemma subset_subsetProducts (A : Finset M) : A ⊆ subsetProducts A := by
  intro a ha
  exact mem_subsetProducts_iff.mpr ⟨{a}, by simpa, by simp⟩

@[gcongr] lemma subsetProducts_mono {A B : Finset M} (hAB : A ⊆ B) :
    subsetProducts A ⊆ subsetProducts B := by
  intro x hx
  obtain ⟨C, hCA, rfl⟩ := mem_subsetProducts_iff.mp hx
  exact mem_subsetProducts_iff.mpr ⟨C, hCA.trans hAB, rfl⟩

end SimpleProducts

/-- The integers obtainable as a sum or a product of distinct elements of `A`. -/
def sumProdValues (A : Finset ℤ) : Finset ℤ :=
  A.subsetSum ∪ subsetProducts A

@[simp] lemma zero_mem_sumProdValues (A : Finset ℤ) : 0 ∈ sumProdValues A := by
  simp [sumProdValues]

@[simp] lemma one_mem_sumProdValues (A : Finset ℤ) : 1 ∈ sumProdValues A := by
  exact Finset.mem_union_right _ (one_mem_subsetProducts A)

lemma subsetSum_subset_sumProdValues (A : Finset ℤ) :
    A.subsetSum ⊆ sumProdValues A := Finset.subset_union_left

lemma subsetProducts_subset_sumProdValues (A : Finset ℤ) :
    subsetProducts A ⊆ sumProdValues A := Finset.subset_union_right

@[gcongr] lemma sumProdValues_mono {A B : Finset ℤ} (hAB : A ⊆ B) :
    sumProdValues A ⊆ sumProdValues B := by
  exact Finset.union_subset_union (Finset.subsetSum_mono hAB) (subsetProducts_mono hAB)

lemma card_subsetSum_le_card_sumProdValues (A : Finset ℤ) :
    A.subsetSum.card ≤ (sumProdValues A).card :=
  Finset.card_le_card (subsetSum_subset_sumProdValues A)

lemma card_subsetProducts_le_card_sumProdValues (A : Finset ℤ) :
    (subsetProducts A).card ≤ (sumProdValues A).card :=
  Finset.card_le_card (subsetProducts_subset_sumProdValues A)

/-- The positive-natural version used in the prime-valuation argument. -/
def natSumProdValues (A : Finset ℕ) : Finset ℕ :=
  A.subsetSum ∪ subsetProducts A

@[gcongr] lemma natSumProdValues_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    natSumProdValues A ⊆ natSumProdValues B :=
  Finset.union_subset_union (Finset.subsetSum_mono hAB) (subsetProducts_mono hAB)

lemma card_subsetSum_le_card_natSumProdValues (A : Finset ℕ) :
    A.subsetSum.card ≤ (natSumProdValues A).card :=
  Finset.card_le_card Finset.subset_union_left

lemma card_subsetProducts_le_card_natSumProdValues (A : Finset ℕ) :
    (subsetProducts A).card ≤ (natSumProdValues A).card :=
  Finset.card_le_card Finset.subset_union_right

section CubePartition

variable {α : Type*} [DecidableEq α]

/-- An exact `m^2`-by-`m` block decomposition of an `m^3`-element finset. -/
theorem exists_cube_blocks (A : Finset α) (m : ℕ) (hm : m ≠ 0)
    (hA : A.card = m ^ 3) :
    ∃ B : Fin (m ^ 2) → Finset α,
      (∀ i, (B i).card = m) ∧
      (∀ i, B i ⊆ A) ∧
      (∀ ⦃i j⦄, i ≠ j → Disjoint (B i) (B j)) ∧
      Finset.univ.biUnion B = A := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hq0 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hqle : m ^ 2 ≤ A.card := by
    rw [hA]
    exact Nat.pow_le_pow_right hmpos (by omega)
  obtain ⟨P, hPeq, hPcard⟩ :=
    Finpartition.exists_equipartition_card_eq A hq0 hqle
  let e : Fin (m ^ 2) ≃ P.parts :=
    (finCongr hPcard.symm).trans P.parts.equivFin.symm
  let B : Fin (m ^ 2) → Finset α := fun i ↦ (e i).1
  have havg : A.card / P.parts.card = m := by
    rw [hA, hPcard]
    simpa [pow_succ, mul_comm] using Nat.mul_div_left m (pow_pos hmpos 2)
  have hmod : A.card % P.parts.card = 0 := by
    rw [hA, hPcard]
    simpa [pow_succ] using Nat.mul_mod_right (m ^ 2) m
  have hlarge :
      {p ∈ P.parts | p.card = A.card / P.parts.card + 1}.card = 0 := by
    simpa [hmod] using hPeq.card_large_parts_eq_mod
  have hBcard : ∀ i, (B i).card = m := by
    intro i
    rcases hPeq.card_parts_eq_average (e i).2 with hsmall | hbig
    · simpa [B, havg] using hsmall
    · exfalso
      have hmem : (e i).1 ∈ {p ∈ P.parts | p.card = A.card / P.parts.card + 1} := by
        simp only [Finset.mem_filter]
        exact ⟨(e i).2, hbig⟩
      have hpos : 0 < {p ∈ P.parts | p.card = A.card / P.parts.card + 1}.card :=
        Finset.card_pos.mpr ⟨(e i).1, hmem⟩
      omega
  have hBsub : ∀ i, B i ⊆ A := fun i ↦ P.subset (e i).2
  have hBpair : ∀ ⦃i j⦄, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    apply P.disjoint (e i).2 (e j).2
    intro heq
    apply hij
    exact e.injective (Subtype.ext heq)
  have hBunion : Finset.univ.biUnion B = A := by
    rw [← P.biUnion_parts]
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e i, (e i).2, hi⟩
    · rintro ⟨p, hp, hap⟩
      obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
      refine ⟨i, ?_⟩
      change a ∈ (e i).1
      rw [hi]
      exact hap
  exact ⟨B, hBcard, hBsub, hBpair, hBunion⟩

/-- Extend a finite indexed block family by empty blocks. -/
def blockAt {q : ℕ} (B : Fin q → Finset α) (i : ℕ) : Finset α :=
  if hi : i < q then B ⟨i, hi⟩ else ∅

/-- Union of the first `i` blocks. -/
def prefixUnion {q : ℕ} (B : Fin q → Finset α) (i : ℕ) : Finset α :=
  (Finset.range i).biUnion (blockAt B)

@[simp] lemma prefixUnion_zero {q : ℕ} (B : Fin q → Finset α) :
    prefixUnion B 0 = ∅ := by
  simp [prefixUnion]

lemma prefixUnion_succ {q : ℕ} (B : Fin q → Finset α) {i : ℕ} (hi : i < q) :
    prefixUnion B (i + 1) = prefixUnion B i ∪ B ⟨i, hi⟩ := by
  have hrange : Finset.range (i + 1) = insert i (Finset.range i) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  rw [prefixUnion, hrange, Finset.biUnion_insert]
  simp only [blockAt, dif_pos hi]
  exact Finset.union_comm _ _

lemma prefixUnion_subset {q : ℕ} (B : Fin q → Finset α) (A : Finset α)
    (hBA : ∀ i, B i ⊆ A) (i : ℕ) : prefixUnion B i ⊆ A := by
  rw [prefixUnion, Finset.biUnion_subset_iff_forall_subset]
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [blockAt]
  split_ifs
  · exact hBA _
  · simp

lemma disjoint_prefixUnion_block {q : ℕ} (B : Fin q → Finset α)
    (hpair : ∀ ⦃i j⦄, i ≠ j → Disjoint (B i) (B j))
    {i : ℕ} (hi : i < q) : Disjoint (prefixUnion B i) (B ⟨i, hi⟩) := by
  rw [Finset.disjoint_left]
  intro a ha
  simp only [prefixUnion, Finset.mem_biUnion, Finset.mem_range] at ha
  obtain ⟨j, hji, haj⟩ := ha
  have hjq : j < q := hji.trans hi
  have hne : (⟨j, hjq⟩ : Fin q) ≠ ⟨i, hi⟩ := by
    intro h
    have hval := congrArg (fun z : Fin q ↦ z.1) h
    change j = i at hval
    omega
  have hd := hpair hne
  rw [Finset.disjoint_left] at hd
  simp only [blockAt, dif_pos hjq] at haj
  exact hd haj

lemma prefixUnion_all {q : ℕ} (B : Fin q → Finset α) :
    prefixUnion B q = Finset.univ.biUnion B := by
  ext a
  simp only [prefixUnion, Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hjq, haj⟩
    exact ⟨⟨j, hjq⟩, by simpa [blockAt, hjq] using haj⟩
  · rintro ⟨j, haj⟩
    exact ⟨j.1, j.2, by simpa [blockAt, j.2] using haj⟩

end CubePartition

section HigherEnergy

variable {α : Type*} [DecidableEq α] [AddCommMonoid α]

/-- All ordered `h`-tuples with entries in `A`. -/
def orderedTuples (h : ℕ) (A : Finset α) : Finset (Fin h → α) :=
  Fintype.piFinset fun _ : Fin h ↦ A

/-- The sum of the coordinates of an ordered tuple. -/
def tupleSum (h : ℕ) (x : Fin h → α) : α := ∑ i, x i

/-- Ordered tuples whose coordinates are pairwise distinct. -/
def distinctTuples (h : ℕ) (A : Finset α) : Finset (Fin h → α) := by
  classical
  exact (orderedTuples h A).filter Function.Injective

/-- An injective tuple in `A` is equivalently an embedding `Fin h ↪ A`. -/
noncomputable def distinctTuplesEquivEmbedding (h : ℕ) (A : Finset α) :
    ↥(distinctTuples h A) ≃ (Fin h ↪ ↥A) where
  toFun x :=
    { toFun := fun i ↦
        ⟨x.1 i, (Fintype.mem_piFinset.mp (Finset.mem_filter.mp x.2).1) i⟩
      inj' := fun i j hij ↦
        (Finset.mem_filter.mp x.2).2 (congrArg Subtype.val hij) }
  invFun e :=
    ⟨fun i ↦ (e i : α), Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr fun i ↦ (e i).2,
        fun i j hij ↦ e.injective (Subtype.ext hij)⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    rfl

omit [AddCommMonoid α] in
@[simp] theorem card_distinctTuples (h : ℕ) (A : Finset α) :
    (distinctTuples h A).card = A.card.descFactorial h := by
  classical
  calc
    (distinctTuples h A).card = Fintype.card ↥(distinctTuples h A) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (Fin h ↪ ↥A) :=
      Fintype.card_congr (distinctTuplesEquivEmbedding h A)
    _ = (Fintype.card ↥A).descFactorial (Fintype.card (Fin h)) :=
      Fintype.card_embedding_eq
    _ = A.card.descFactorial h := by simp

omit [AddCommMonoid α] in
theorem card_add_one_sub_pow_le_card_distinctTuples (h : ℕ) (A : Finset α) :
    (A.card + 1 - h) ^ h ≤ (distinctTuples h A).card := by
  rw [card_distinctTuples]
  exact Nat.pow_sub_le_descFactorial A.card h

omit [AddCommMonoid α] in
theorem card_div_two_pow_le_card_distinctTuples (h : ℕ) (A : Finset α)
    (hA : 2 * h ≤ A.card) :
    (A.card / 2) ^ h ≤ (distinctTuples h A).card := by
  rw [card_distinctTuples]
  apply (Nat.pow_le_pow_left ?_ h).trans (Nat.pow_sub_le_descFactorial A.card h)
  omega

/-- Sums of exactly `h` distinct elements of `A`. -/
def distinctHSums (h : ℕ) (A : Finset α) : Finset α := by
  classical
  exact (distinctTuples h A).image (tupleSum h)

/-- The number of tuples in `T` having a prescribed sum. -/
def sumFiberCount (h : ℕ) (T : Finset (Fin h → α)) (z : α) : ℕ :=
  (T.filter fun x ↦ tupleSum h x = z).card

/-- Ordered `h`-fold additive energy, as a sum of squared representation counts. -/
def hAddEnergy (h : ℕ) (A : Finset α) : ℕ := by
  classical
  exact ∑ z ∈ (orderedTuples h A).image (tupleSum h),
    sumFiberCount h (orderedTuples h A) z ^ 2

omit [AddCommMonoid α] in
lemma distinctTuples_subset_orderedTuples (h : ℕ) (A : Finset α) :
    distinctTuples h A ⊆ orderedTuples h A := by
  classical
  exact Finset.filter_subset _ _

lemma distinctHSums_subset_allHSums (h : ℕ) (A : Finset α) :
    distinctHSums h A ⊆ (orderedTuples h A).image (tupleSum h) := by
  classical
  exact Finset.image_mono _ (distinctTuples_subset_orderedTuples h A)

lemma distinct_sumFiberCount_le (h : ℕ) (A : Finset α) (z : α) :
    sumFiberCount h (distinctTuples h A) z ≤
      sumFiberCount h (orderedTuples h A) z := by
  classical
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨distinctTuples_subset_orderedTuples h A hx.1, hx.2⟩

/-- Finite Cauchy--Schwarz for distinct-coordinate tuples. -/
theorem card_distinctTuples_sq_le_card_distinctHSums_mul_hAddEnergy
    (h : ℕ) (A : Finset α) :
    (distinctTuples h A).card ^ 2 ≤
      (distinctHSums h A).card * hAddEnergy h A := by
  classical
  rw [Finset.card_eq_sum_card_image (tupleSum h) (distinctTuples h A)]
  calc
    (∑ z ∈ distinctHSums h A, sumFiberCount h (distinctTuples h A) z) ^ 2
        ≤ (distinctHSums h A).card *
            ∑ z ∈ distinctHSums h A,
              sumFiberCount h (distinctTuples h A) z ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ (distinctHSums h A).card *
          ∑ z ∈ distinctHSums h A,
            sumFiberCount h (orderedTuples h A) z ^ 2 := by
      gcongr with z hz
      exact distinct_sumFiberCount_le h A z
    _ ≤ (distinctHSums h A).card *
          ∑ z ∈ (orderedTuples h A).image (tupleSum h),
            sumFiberCount h (orderedTuples h A) z ^ 2 := by
      gcongr
      exact distinctHSums_subset_allHSums h A
    _ = (distinctHSums h A).card * hAddEnergy h A := by rfl

theorem card_distinctTuples_sq_le_card_distinctHSums_mul_of_energy_le
    (h : ℕ) (A : Finset α) (E : ℕ) (hE : hAddEnergy h A ≤ E) :
    (distinctTuples h A).card ^ 2 ≤ (distinctHSums h A).card * E :=
  (card_distinctTuples_sq_le_card_distinctHSums_mul_hAddEnergy h A).trans
    (Nat.mul_le_mul_left _ hE)

theorem energy_quotient_le_card_distinctHSums
    (h : ℕ) (A : Finset α) (E : ℕ) (hE : hAddEnergy h A ≤ E) :
    (distinctTuples h A).card ^ 2 / E ≤ (distinctHSums h A).card := by
  apply Nat.div_le_of_le_mul
  simpa [mul_comm] using
    card_distinctTuples_sq_le_card_distinctHSums_mul_of_energy_le h A E hE

lemma distinctHSums_subset_subsetSum (h : ℕ) (A : Finset α) :
    distinctHSums h A ⊆ A.subsetSum := by
  classical
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have hxA : ∀ i, x i ∈ A := by
    intro i
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1 i
  let B := Finset.univ.image x
  have hBA : B ⊆ A := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hxA i
  refine Finset.mem_subsetSum_iff.mpr ⟨B, hBA, ?_⟩
  change ∑ b ∈ Finset.univ.image x, b = tupleSum h x
  rw [Finset.sum_image (Finset.mem_filter.mp hx).2.injOn]
  rfl

/-- The numerical estimate converting the Cauchy--Schwarz quotient into one
full power less than the block size. -/
lemma power_energy_scale_le {m C h : ℕ} (hh : 0 < h) (hm : 2 * h ≤ m)
    (hlarge : (4 * C) ^ h ≤ m) :
    m ^ (h - 1) * (C ^ h * m ^ h) ≤ ((m + 1 - h) ^ h) ^ 2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  let b := m + 1 - (r + 1)
  have hmb : m ≤ 2 * b := by
    dsimp [b]
    omega
  have htwo : 2 * 2 ^ (2 * r + 1) = 4 ^ (r + 1) := by
    rw [mul_comm, ← pow_succ, show 2 * r + 1 + 1 = 2 * (r + 1) by omega, pow_mul]
    norm_num
  have hdouble :
      2 * (C ^ (r + 1) * 2 ^ (2 * r + 1)) = (4 * C) ^ (r + 1) := by
    rw [mul_pow]
    calc
      2 * (C ^ (r + 1) * 2 ^ (2 * r + 1))
          = C ^ (r + 1) * (2 * 2 ^ (2 * r + 1)) := by ring
      _ = C ^ (r + 1) * 4 ^ (r + 1) := by rw [htwo]
      _ = 4 ^ (r + 1) * C ^ (r + 1) := by ac_rfl
  have hscale : C ^ (r + 1) * 2 ^ (2 * r + 1) ≤ b := by
    have hs : 2 * (C ^ (r + 1) * 2 ^ (2 * r + 1)) ≤ m :=
      hdouble.trans_le hlarge
    dsimp [b]
    omega
  calc
    m ^ r * (C ^ (r + 1) * m ^ (r + 1))
        ≤ (2 * b) ^ r * (C ^ (r + 1) * (2 * b) ^ (r + 1)) := by
      gcongr
    _ = (C ^ (r + 1) * 2 ^ (2 * r + 1)) * b ^ (2 * r + 1) := by
      simp only [mul_pow]
      rw [show 2 * r + 1 = r + (r + 1) by omega, pow_add]
      ring
    _ ≤ b * b ^ (2 * r + 1) := by gcongr
    _ = (b ^ (r + 1)) ^ 2 := by
      rw [pow_two, show 2 * r + 1 = r + (r + 1) by omega, pow_add, pow_succ]
      ring
    _ = ((m + 1 - (r + 1)) ^ (r + 1)) ^ 2 := by rfl

/-- An energy bound of order `C^h m^h` and the explicit size threshold
`(4C)^h ≤ m` force at least `m^(h-1)` subset sums. -/
theorem card_pow_pred_le_card_subsetSum_of_hAddEnergy_le
    (h C : ℕ) (A : Finset α) (hh : 0 < h) (hC : 0 < C)
    (hcard : 2 * h ≤ A.card)
    (henergy : hAddEnergy h A ≤ C ^ h * A.card ^ h)
    (hlarge : (4 * C) ^ h ≤ A.card) :
    A.card ^ (h - 1) ≤ A.subsetSum.card := by
  have hA : 0 < A.card := by omega
  have hden : 0 < C ^ h * A.card ^ h := by positivity
  have hquotient :
      (distinctTuples h A).card ^ 2 / (C ^ h * A.card ^ h) ≤
        (distinctHSums h A).card :=
    energy_quotient_le_card_distinctHSums h A _ henergy
  have hnumerator :
      A.card ^ (h - 1) * (C ^ h * A.card ^ h) ≤
        (distinctTuples h A).card ^ 2 :=
    (power_energy_scale_le hh hcard hlarge).trans <|
      Nat.pow_le_pow_left (card_add_one_sub_pow_le_card_distinctTuples h A) 2
  calc
    A.card ^ (h - 1)
        ≤ (distinctTuples h A).card ^ 2 / (C ^ h * A.card ^ h) :=
      (Nat.le_div_iff_mul_le hden).mpr hnumerator
    _ ≤ (distinctHSums h A).card := hquotient
    _ ≤ A.subsetSum.card :=
      Finset.card_le_card (distinctHSums_subset_subsetSum h A)

end HigherEnergy

section BlockGrowth

/-- A crude finite form of `(1 + 1 / m)^m ≤ m + 1`. -/
lemma add_one_pow_le (m j : ℕ) (hj : j ≤ m) :
    (m + 1) ^ j ≤ (j + 1) * m ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjm : j + 1 ≤ m := by omega
      calc
        (m + 1) ^ (j + 1) = (m + 1) ^ j * (m + 1) := by rw [pow_succ]
        _ ≤ ((j + 1) * m ^ j) * (m + 1) := by
          gcongr
          exact ih (by omega)
        _ = (j + 1) * m ^ (j + 1) + (j + 1) * m ^ j := by ring
        _ ≤ (j + 1) * m ^ (j + 1) + m ^ (j + 1) := by
          gcongr
          rw [pow_succ]
          simpa [mul_comm] using Nat.mul_le_mul_left (m ^ j) hjm
        _ = (j + 1 + 1) * m ^ (j + 1) := by ring

/-- The elementary ratio bound used in the slow-growth case. -/
lemma ratio_pow_le (m : ℕ) (hm : 1 ≤ m) :
    ((m + 1 : ℚ≥0) / m) ^ (m + 2) ≤ 8 * m := by
  have hm_two : m + 1 ≤ 2 * m := by omega
  have hpow := add_one_pow_le m m le_rfl
  have hnat : (m + 1) ^ (m + 2) ≤ 8 * m * m ^ (m + 2) := by
    calc
      (m + 1) ^ (m + 2) = (m + 1) ^ m * (m + 1) ^ 2 := by ring
      _ ≤ ((m + 1) * m ^ m) * (m + 1) ^ 2 := by gcongr
      _ ≤ ((2 * m) * m ^ m) * (2 * m) ^ 2 := by gcongr
      _ = 8 * m * m ^ (m + 2) := by ring
  rw [div_pow, div_le_iff₀]
  · exact_mod_cast hnat
  · positivity

lemma two_mul_pow_le_add_one_pow (m : ℕ) (hm : 1 ≤ m) :
    2 * m ^ m ≤ (m + 1) ^ m := by
  have hbern : m ^ m + m * m ^ (m - 1) * 1 ≤ (m + 1) ^ m := by
    simpa using
      (pow_add_mul_le_add_pow (R := ℕ) (a := m) (b := 1)
        (Nat.zero_le m) (Nat.zero_le (2 * m + 1)) m)
  have hpow : m * m ^ (m - 1) = m ^ m := by
    rw [← pow_succ']
    congr 1
    omega
  simpa [hpow, two_mul] using hbern

lemma growth_telescope
    (m N : ℕ) (c : ℕ → ℕ) (hc0 : 1 ≤ c 0)
    (hstep : ∀ i < N, (m + 1) * c i ≤ m * c (i + 1)) :
    (m + 1) ^ N ≤ m ^ N * c N := by
  have hind : ∀ i ≤ N, (m + 1) ^ i ≤ m ^ i * c i := by
    intro i hi
    induction i with
    | zero => simpa using hc0
    | succ i ih =>
        calc
          (m + 1) ^ (i + 1) = (m + 1) ^ i * (m + 1) := by rw [pow_succ]
          _ ≤ (m ^ i * c i) * (m + 1) := by
            gcongr
            exact ih (by omega)
          _ = m ^ i * ((m + 1) * c i) := by ring
          _ ≤ m ^ i * (m * c (i + 1)) := by
            exact Nat.mul_le_mul_left (m ^ i) (hstep i (by omega))
          _ = m ^ (i + 1) * c (i + 1) := by ring
  exact hind N le_rfl

theorem fast_growth_forces_large_prefix
    (m : ℕ) (hm : 1 ≤ m) (c : ℕ → ℕ) (hc0 : 1 ≤ c 0)
    (hstep : ∀ i < m * (m - 1), (m + 1) * c i ≤ m * c (i + 1)) :
    2 ^ (m - 1) ≤ c (m * (m - 1)) := by
  let N := m * (m - 1)
  have htelescope : (m + 1) ^ N ≤ m ^ N * c N :=
    growth_telescope m N c hc0 hstep
  have hblock := two_mul_pow_le_add_one_pow m hm
  have hblockpow : (2 * m ^ m) ^ (m - 1) ≤ ((m + 1) ^ m) ^ (m - 1) := by
    exact Nat.pow_le_pow_left hblock (m - 1)
  have hlower : 2 ^ (m - 1) * m ^ N ≤ (m + 1) ^ N := by
    calc
      2 ^ (m - 1) * m ^ N = (2 * m ^ m) ^ (m - 1) := by
        simp only [mul_pow, pow_mul, N]
      _ ≤ ((m + 1) ^ m) ^ (m - 1) := hblockpow
      _ = (m + 1) ^ N := by simp only [pow_mul, N]
  have hcancel : m ^ N * 2 ^ (m - 1) ≤ m ^ N * c N := by
    simpa [mul_comm] using hlower.trans htelescope
  exact Nat.le_of_mul_le_mul_left hcancel (by positivity)

theorem slow_growth_forces_large_prefix
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (m t : ℕ) (X Y : Finset G)
    (hm : 8 ≤ m) (hX : X.Nonempty)
    (hslow : m * (X + Y).card ≤ (m + 1) * X.card)
    (hbox : m ^ (3 * t + 2) ≤ ((m + 1) • Y - Y).card) :
    m ^ (3 * t) ≤ X.card := by
  have hm0 : 0 < m := by omega
  have hXcard : 0 < X.card := Finset.card_pos.mpr hX
  have hratio :
      ((↑(X + Y).card : ℚ≥0) / X.card) ≤ (m + 1 : ℚ≥0) / m := by
    rw [div_le_div_iff₀]
    · exact_mod_cast (show (X + Y).card * m ≤ (m + 1) * X.card by
        simpa [mul_comm] using hslow)
    · exact_mod_cast hXcard
    · exact_mod_cast hm0
  have hPR := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add
    hX Y (m + 1) 1
  have hPR' :
      (↑((m + 1) • Y - Y).card : ℚ≥0) ≤ 8 * m * X.card := by
    calc
      (↑((m + 1) • Y - Y).card : ℚ≥0)
          = ↑((m + 1) • Y - 1 • Y).card := by
            congr 2
            rw [one_nsmul]
      _ ≤ ((↑(X + Y).card / ↑X.card : ℚ≥0) ^ ((m + 1) + 1)) * ↑X.card := hPR
      _ ≤ (((m + 1 : ℚ≥0) / m) ^ (m + 2)) * X.card := by gcongr
      _ ≤ (8 * m) * X.card := by
        gcongr
        exact ratio_pow_le m hm0
      _ = 8 * m * X.card := by ring
  have hupper : ((m + 1) • Y - Y).card ≤ 8 * m * X.card := by
    exact_mod_cast hPR'
  have hmain : m ^ (3 * t + 2) ≤ 8 * m * X.card := hbox.trans hupper
  have hfactor : 8 * m * m ^ (3 * t) ≤ m ^ (3 * t + 2) := by
    calc
      8 * m * m ^ (3 * t) ≤ m * m * m ^ (3 * t) := by gcongr
      _ = m ^ (3 * t + 2) := by ring
  have hcancel : 8 * m * m ^ (3 * t) ≤ 8 * m * X.card := hfactor.trans hmain
  exact Nat.le_of_mul_le_mul_left hcancel (by positivity)

theorem cube_block_dichotomy
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (m t S : ℕ) (X Y : ℕ → Finset G)
    (hm : 8 ≤ m)
    (hX : ∀ i ≤ m * (m - 1), (X i).Nonempty)
    (hrec : ∀ i < m * (m - 1), X (i + 1) = X i + Y i)
    (hblock : ∀ i < m * (m - 1),
      m ^ (3 * t) ≤ S ∨ m ^ (3 * t + 2) ≤ ((m + 1) • Y i - Y i).card)
    (hexp : m ^ (3 * t) ≤ 2 ^ (m - 1)) :
    m ^ (3 * t) ≤ S ∨
      ∃ i ≤ m * (m - 1), m ^ (3 * t) ≤ (X i).card := by
  by_cases hS : m ^ (3 * t) ≤ S
  · exact Or.inl hS
  right
  have hboxes : ∀ i < m * (m - 1),
      m ^ (3 * t + 2) ≤ ((m + 1) • Y i - Y i).card := by
    intro i hi
    exact (hblock i hi).resolve_left hS
  by_cases hfast : ∀ i < m * (m - 1),
      (m + 1) * (X i).card < m * (X (i + 1)).card
  · refine ⟨m * (m - 1), le_rfl, hexp.trans ?_⟩
    apply fast_growth_forces_large_prefix m (by omega) (fun i ↦ (X i).card)
    · exact Finset.card_pos.mpr (hX 0 (Nat.zero_le _))
    · intro i hi
      exact (hfast i hi).le
  · push Not at hfast
    obtain ⟨i, hi, hslow⟩ := hfast
    refine ⟨i, hi.le, slow_growth_forces_large_prefix m t (X i) (Y i) hm (hX i hi.le) ?_
      (hboxes i hi)⟩
    rw [← hrec i hi]
    omega

end BlockGrowth

section Factorization

/-- In an additive relation between positive integers, the least exponent of
a fixed prime cannot occur at exactly one summand. -/
lemma prime_factorization_min_repeated
    {I : Type*} [Fintype I] [DecidableEq I]
    (L R : Finset I) (hdisj : Disjoint L R) (hcover : L ∪ R = Finset.univ)
    (x : I → ℕ) (hx : ∀ i, 0 < x i) (p : ℕ) (hp : p.Prime)
    (hsum : ∑ i ∈ L, x i = ∑ i ∈ R, x i)
    (i₀ : I) (hmin : ∀ j, (x i₀).factorization p ≤ (x j).factorization p) :
    ∃ j ≠ i₀, (x j).factorization p = (x i₀).factorization p := by
  by_contra! huniq
  let d := p ^ ((x i₀).factorization p + 1)
  have hdvd (j : I) (hji : j ≠ i₀) : d ∣ x j := by
    apply (hp.pow_dvd_iff_le_factorization (hx j).ne').mpr
    exact Nat.add_one_le_iff.mpr (lt_of_le_of_ne (hmin j) (Ne.symm (huniq j hji)))
  have hnot : ¬d ∣ x i₀ := by
    intro hd
    have := (hp.pow_dvd_iff_le_factorization (hx i₀).ne').mp hd
    omega
  have hi : i₀ ∈ L ∪ R := by rw [hcover]; simp
  rcases Finset.mem_union.mp hi with hiL | hiR
  · have hLR : i₀ ∉ R := fun hiR ↦ Finset.disjoint_left.mp hdisj hiL hiR
    have hdL : d ∣ ∑ j ∈ L.erase i₀, x j := by
      apply Finset.dvd_sum
      intro j hj
      exact hdvd j (Finset.ne_of_mem_erase hj)
    have hdR : d ∣ ∑ j ∈ R, x j := by
      apply Finset.dvd_sum
      intro j hj
      exact hdvd j (ne_of_mem_of_not_mem hj hLR)
    apply hnot
    apply (Nat.dvd_add_iff_left hdL).mpr
    rw [add_comm, Finset.sum_erase_add L x hiL, hsum]
    exact hdR
  · have hRL : i₀ ∉ L := fun hiL ↦ Finset.disjoint_left.mp hdisj hiL hiR
    have hdR : d ∣ ∑ j ∈ R.erase i₀, x j := by
      apply Finset.dvd_sum
      intro j hj
      exact hdvd j (Finset.ne_of_mem_erase hj)
    have hdL : d ∣ ∑ j ∈ L, x j := by
      apply Finset.dvd_sum
      intro j hj
      exact hdvd j (ne_of_mem_of_not_mem hj hRL)
    apply hnot
    apply (Nat.dvd_add_iff_left hdR).mpr
    rw [add_comm, Finset.sum_erase_add R x hiR, ← hsum]
    exact hdL

/-- The prime-exponent vector of a natural number, embedded in a rational vector
space so that linear dimension is available. -/
noncomputable def exponentVector (n : ℕ) : ℕ →₀ ℚ :=
  (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℚ)) n.factorization

@[simp] lemma exponentVector_apply (n p : ℕ) :
    exponentVector n p = (n.factorization p : ℚ) := by
  rfl

@[simp] lemma exponentVector_zero : exponentVector 0 = 0 := by
  simp [exponentVector]

@[simp] lemma exponentVector_one : exponentVector 1 = 0 := by
  simp [exponentVector]

lemma exponentVector_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    exponentVector (a * b) = exponentVector a + exponentVector b := by
  rw [exponentVector, Nat.factorization_mul ha hb]
  exact map_add _ _ _

lemma exponentVector_prod {ι : Type*} (S : Finset ι) (g : ι → ℕ)
    (hS : ∀ x ∈ S, g x ≠ 0) :
    exponentVector (∏ x ∈ S, g x) = ∑ x ∈ S, exponentVector (g x) := by
  rw [exponentVector, Nat.factorization_prod hS, map_sum]
  rfl

lemma exponentVector_injectiveOn_nonzero :
    Set.InjOn exponentVector {n : ℕ | n ≠ 0} := by
  intro a ha b hb hab
  apply Nat.factorization_inj ha hb
  ext p
  have hp := congrArg (fun f : ℕ →₀ ℚ ↦ f p) hab
  exact_mod_cast (show (a.factorization p : ℚ) = b.factorization p by
    simpa [exponentVector] using hp)

lemma exponentVector_injectiveOn_pos :
    Set.InjOn exponentVector {n : ℕ | 0 < n} := by
  intro a ha b hb hab
  exact exponentVector_injectiveOn_nonzero ha.ne' hb.ne' hab

/-- The sums of prime-exponent vectors indexed by subsets of `A`.  For a
positive set this is exactly the exponent-vector image of its subset products. -/
noncomputable def exponentSubsetSums (A : Finset ℕ) : Finset (ℕ →₀ ℚ) :=
  A.powerset.image fun B ↦ ∑ b ∈ B, exponentVector b

@[simp] lemma mem_exponentSubsetSums_iff {A : Finset ℕ} {v : ℕ →₀ ℚ} :
    v ∈ exponentSubsetSums A ↔
      ∃ B ⊆ A, ∑ b ∈ B, exponentVector b = v := by
  simp [exponentSubsetSums]

@[simp] lemma zero_mem_exponentSubsetSums (A : Finset ℕ) :
    0 ∈ exponentSubsetSums A := by
  exact mem_exponentSubsetSums_iff.mpr ⟨∅, Finset.empty_subset _, by simp⟩

lemma exponentSubsetSums_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    exponentSubsetSums A ⊆ exponentSubsetSums B := by
  intro v hv
  obtain ⟨C, hCA, rfl⟩ := mem_exponentSubsetSums_iff.mp hv
  exact mem_exponentSubsetSums_iff.mpr ⟨C, hCA.trans hAB, rfl⟩

lemma image_exponentVector_subsetProducts (A : Finset ℕ)
    (hA : ∀ a ∈ A, a ≠ 0) :
    (subsetProducts A).image exponentVector = exponentSubsetSums A := by
  ext v
  constructor
  · simp only [Finset.mem_image, mem_subsetProducts_iff]
    rintro ⟨x, ⟨B, hBA, rfl⟩, rfl⟩
    exact mem_exponentSubsetSums_iff.mpr
      ⟨B, hBA, (exponentVector_prod B id (fun b hb ↦ hA b (hBA hb))).symm⟩
  · intro hv
    obtain ⟨B, hBA, rfl⟩ := mem_exponentSubsetSums_iff.mp hv
    refine Finset.mem_image.mpr ⟨∏ b ∈ B, b, ?_, ?_⟩
    · exact mem_subsetProducts_iff.mpr ⟨B, hBA, rfl⟩
    · exact exponentVector_prod B id (fun b hb ↦ hA b (hBA hb))

lemma subsetProducts_ne_zero (A : Finset ℕ) (hA : ∀ a ∈ A, a ≠ 0) :
    ∀ x ∈ subsetProducts A, x ≠ 0 := by
  intro x hx
  obtain ⟨B, hBA, rfl⟩ := mem_subsetProducts_iff.mp hx
  exact Finset.prod_ne_zero_iff.mpr fun b hb ↦ hA b (hBA hb)

lemma card_exponentSubsetSums_eq_card_subsetProducts (A : Finset ℕ)
    (hA : ∀ a ∈ A, a ≠ 0) :
    (exponentSubsetSums A).card = (subsetProducts A).card := by
  rw [← image_exponentVector_subsetProducts A hA]
  exact Finset.card_image_of_injOn fun a ha b hb hab ↦
    exponentVector_injectiveOn_nonzero (subsetProducts_ne_zero A hA a ha)
      (subsetProducts_ne_zero A hA b hb) hab

lemma exponentSubsetSums_union {A B : Finset ℕ} (hAB : Disjoint A B) :
    exponentSubsetSums (A ∪ B) = exponentSubsetSums A + exponentSubsetSums B := by
  ext v
  constructor
  · intro hv
    obtain ⟨C, hCAB, rfl⟩ := mem_exponentSubsetSums_iff.mp hv
    let U := C ∩ A
    let V := C \ A
    have hUA : U ⊆ A := Finset.inter_subset_right
    have hVB : V ⊆ B := by
      intro x hx
      have hxC : x ∈ C := (Finset.mem_sdiff.mp hx).1
      have hxA : x ∉ A := (Finset.mem_sdiff.mp hx).2
      exact (Finset.mem_union.mp (hCAB hxC)).resolve_left hxA
    have hUV : Disjoint U V := by
      rw [Finset.disjoint_left]
      intro x hxU hxV
      exact (Finset.mem_sdiff.mp hxV).2 (Finset.mem_inter.mp hxU).2
    have hCUV : U ∪ V = C := by
      ext x
      rw [Finset.mem_union]
      constructor
      · rintro (hx | hx)
        · exact (Finset.mem_inter.mp hx).1
        · exact (Finset.mem_sdiff.mp hx).1
      · intro hxC
        by_cases hxA : x ∈ A
        · exact Or.inl (show x ∈ U from Finset.mem_inter.mpr ⟨hxC, hxA⟩)
        · exact Or.inr (show x ∈ V from Finset.mem_sdiff.mpr ⟨hxC, hxA⟩)
    rw [← hCUV, Finset.sum_union hUV]
    exact Finset.mem_add.mpr
      ⟨∑ u ∈ U, exponentVector u,
        mem_exponentSubsetSums_iff.mpr ⟨U, hUA, rfl⟩,
       ∑ w ∈ V, exponentVector w,
        mem_exponentSubsetSums_iff.mpr ⟨V, hVB, rfl⟩, rfl⟩
  · intro hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Finset.mem_add.mp hv
    obtain ⟨U, hUA, rfl⟩ := mem_exponentSubsetSums_iff.mp hu
    obtain ⟨V, hVB, rfl⟩ := mem_exponentSubsetSums_iff.mp hw
    have hUV : Disjoint U V := hAB.mono hUA hVB
    rw [← Finset.sum_union hUV]
    exact mem_exponentSubsetSums_iff.mpr
      ⟨U ∪ V, Finset.union_subset (hUA.trans Finset.subset_union_left)
        (hVB.trans Finset.subset_union_right), rfl⟩

/-- Prime-exponent subset-sum sets of successive block prefixes. -/
noncomputable def prefixExponentSums {q : ℕ} (B : Fin q → Finset ℕ) (i : ℕ) :
    Finset (ℕ →₀ ℚ) :=
  exponentSubsetSums (prefixUnion B i)

@[simp] lemma prefixExponentSums_zero {q : ℕ} (B : Fin q → Finset ℕ) :
    prefixExponentSums B 0 = {0} := by
  ext x
  simp [prefixExponentSums, exponentSubsetSums]

lemma prefixExponentSums_succ {q : ℕ} (B : Fin q → Finset ℕ)
    (hpair : ∀ ⦃i j⦄, i ≠ j → Disjoint (B i) (B j))
    {i : ℕ} (hi : i < q) :
    prefixExponentSums B (i + 1) =
      prefixExponentSums B i + exponentSubsetSums (B ⟨i, hi⟩) := by
  unfold prefixExponentSums
  rw [prefixUnion_succ B hi]
  exact exponentSubsetSums_union (disjoint_prefixUnion_block B hpair hi)

lemma prefixExponentSums_subset_full {q : ℕ} (B : Fin q → Finset ℕ)
    (A : Finset ℕ) (hBA : ∀ i, B i ⊆ A) (i : ℕ) :
    prefixExponentSums B i ⊆ exponentSubsetSums A :=
  exponentSubsetSums_mono (prefixUnion_subset B A hBA i)

@[simp] lemma prefixExponentSums_nonempty {q : ℕ} (B : Fin q → Finset ℕ) (i : ℕ) :
    (prefixExponentSums B i).Nonempty :=
  ⟨0, zero_mem_exponentSubsetSums _⟩

end Factorization

section SignReduction

def natCastEmbedding : ℕ ↪ ℤ where
  toFun n := (n : ℤ)
  inj' := fun _ _ h ↦ Int.ofNat.inj h

def negNatCastEmbedding : ℕ ↪ ℤ where
  toFun n := -(n : ℤ)
  inj' := fun _ _ h ↦ Int.ofNat.inj (neg_injective h)

@[simp] lemma natCastEmbedding_apply (n : ℕ) : natCastEmbedding n = (n : ℤ) := rfl

@[simp] lemma negNatCastEmbedding_apply (n : ℕ) :
    negNatCastEmbedding n = -(n : ℤ) := rfl

lemma cast_natSumProdValues_mapsTo (B : Finset ℕ) :
    Set.MapsTo (fun n : ℕ ↦ (n : ℤ)) (natSumProdValues B)
      (sumProdValues (B.map natCastEmbedding)) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨C, hCB, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
    apply Finset.mem_union_left
    refine Finset.mem_subsetSum_iff.mpr ⟨C.map natCastEmbedding, ?_, ?_⟩
    · exact Finset.map_subset_map.mpr hCB
    · simp only [Finset.sum_map]
      change ∑ x ∈ C, (x : ℤ) = (↑(∑ x ∈ C, x) : ℤ)
      simpa using (Nat.cast_sum (R := ℤ) C id).symm
  · obtain ⟨C, hCB, rfl⟩ := mem_subsetProducts_iff.mp hx
    apply Finset.mem_union_right
    refine mem_subsetProducts_iff.mpr ⟨C.map natCastEmbedding, ?_, ?_⟩
    · exact Finset.map_subset_map.mpr hCB
    · simp only [Finset.prod_map]
      change ∏ x ∈ C, (x : ℤ) = (↑(∏ x ∈ C, x) : ℤ)
      simpa using (Nat.cast_prod (R := ℤ) id C).symm

lemma card_natSumProdValues_le_cast (B : Finset ℕ) :
    (natSumProdValues B).card ≤ (sumProdValues (B.map natCastEmbedding)).card := by
  exact Finset.card_le_card_of_injOn (fun n : ℕ ↦ (n : ℤ))
    (cast_natSumProdValues_mapsTo B) natCastEmbedding.injective.injOn

lemma natSumProdValues_subset_natAbs_image_neg (B : Finset ℕ) :
    natSumProdValues B ⊆
      (sumProdValues (B.map negNatCastEmbedding)).image Int.natAbs := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨C, hCB, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
    refine Finset.mem_image.mpr ⟨-(∑ c ∈ C, c : ℤ), ?_, ?_⟩
    apply Finset.mem_union_left
    refine Finset.mem_subsetSum_iff.mpr ⟨C.map negNatCastEmbedding, ?_, ?_⟩
    · exact Finset.map_subset_map.mpr hCB
    · simp only [Finset.sum_map]
      change ∑ x ∈ C, -(x : ℤ) = -∑ c ∈ C, (c : ℤ)
      rw [Finset.sum_neg_distrib]
    · rw [Int.natAbs_neg]
      have hcast : (∑ c ∈ C, (c : ℤ)) = (↑(∑ c ∈ C, c) : ℤ) := by
        simpa using (Nat.cast_sum (R := ℤ) C id).symm
      rw [hcast, Int.natAbs_natCast]
  · obtain ⟨C, hCB, rfl⟩ := mem_subsetProducts_iff.mp hx
    let z : ℤ := ∏ c ∈ C.map negNatCastEmbedding, c
    refine Finset.mem_image.mpr ⟨z, ?_, ?_⟩
    · apply Finset.mem_union_right
      exact mem_subsetProducts_iff.mpr ⟨C.map negNatCastEmbedding,
        Finset.map_subset_map.mpr hCB, rfl⟩
    · dsimp [z]
      change Int.natAbsHom (∏ c ∈ C.map negNatCastEmbedding, c) = ∏ b ∈ C, b
      rw [map_prod Int.natAbsHom]
      simp only [Finset.prod_map, Int.natAbsHom_apply, Int.natAbs_neg,
        Int.natAbs_natCast, negNatCastEmbedding_apply]

lemma card_natSumProdValues_le_neg (B : Finset ℕ) :
    (natSumProdValues B).card ≤ (sumProdValues (B.map negNatCastEmbedding)).card := by
  calc
    (natSumProdValues B).card
        ≤ ((sumProdValues (B.map negNatCastEmbedding)).image Int.natAbs).card :=
      Finset.card_le_card (natSumProdValues_subset_natAbs_image_neg B)
    _ ≤ (sumProdValues (B.map negNatCastEmbedding)).card := Finset.card_image_le

lemma natAbs_injOn_of_nonneg {S : Finset ℤ} (hS : ∀ z ∈ S, 0 ≤ z) :
    Set.InjOn Int.natAbs S := by
  intro a ha b hb hab
  have h := congrArg (fun n : ℕ ↦ (n : ℤ)) hab
  simpa [Int.natAbs_of_nonneg (hS a ha), Int.natAbs_of_nonneg (hS b hb)] using h

lemma natAbs_injOn_of_nonpos {S : Finset ℤ} (hS : ∀ z ∈ S, z ≤ 0) :
    Set.InjOn Int.natAbs S := by
  intro a ha b hb hab
  have h := congrArg (fun n : ℕ ↦ (n : ℤ)) hab
  have ha' : (a.natAbs : ℤ) = -a := by
    rw [Int.natCast_natAbs, abs_of_nonpos (hS a ha)]
  have hb' : (b.natAbs : ℤ) = -b := by
    rw [Int.natCast_natAbs, abs_of_nonpos (hS b hb)]
  rw [ha', hb'] at h
  exact neg_injective h

lemma card_image_natAbs_eq_of_nonneg (S : Finset ℤ) (hS : ∀ z ∈ S, 0 ≤ z) :
    (S.image Int.natAbs).card = S.card :=
  Finset.card_image_iff.mpr (natAbs_injOn_of_nonneg hS)

lemma card_image_natAbs_eq_of_nonpos (S : Finset ℤ) (hS : ∀ z ∈ S, z ≤ 0) :
    (S.image Int.natAbs).card = S.card :=
  Finset.card_image_iff.mpr (natAbs_injOn_of_nonpos hS)

lemma map_image_natAbs_natCast_eq_of_nonneg (S : Finset ℤ)
    (hS : ∀ z ∈ S, 0 ≤ z) :
    (S.image Int.natAbs).map natCastEmbedding = S := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, hnz⟩ := Finset.mem_map.mp hz
    obtain ⟨a, ha, han⟩ := Finset.mem_image.mp hn
    have hcast : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg (hS a ha)
    have : z = a := by
      rw [← hnz, ← han]
      exact hcast
    simpa [this] using ha
  · intro hz
    refine Finset.mem_map.mpr ⟨z.natAbs, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    exact Int.natAbs_of_nonneg (hS z hz)

lemma map_image_natAbs_negCast_eq_of_nonpos (S : Finset ℤ)
    (hS : ∀ z ∈ S, z ≤ 0) :
    (S.image Int.natAbs).map negNatCastEmbedding = S := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn, hnz⟩ := Finset.mem_map.mp hz
    obtain ⟨a, ha, han⟩ := Finset.mem_image.mp hn
    have hcast : -(a.natAbs : ℤ) = a := by
      rw [Int.natCast_natAbs, abs_of_nonpos (hS a ha), neg_neg]
    have : z = a := by
      rw [← hnz, ← han]
      exact hcast
    simpa [this] using ha
  · intro hz
    refine Finset.mem_map.mpr ⟨z.natAbs, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    change -(z.natAbs : ℤ) = z
    rw [Int.natCast_natAbs, abs_of_nonpos (hS z hz), neg_neg]

lemma power_le_double_exponent {n m k : ℕ} (hm : 3 ≤ m) (hn : n ≤ 3 * m) :
    n ^ k ≤ m ^ (k + k) := by
  calc
    n ^ k ≤ (3 * m) ^ k := Nat.pow_le_pow_left hn k
    _ = 3 ^ k * m ^ k := mul_pow 3 m k
    _ ≤ m ^ k * m ^ k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm k)
    _ = m ^ (k + k) := (pow_add m k k).symm

/-- A fixed-power lower bound for positive natural sets implies the exact
integer statement, after doubling the exponent and enlarging the threshold. -/
theorem integer_resolution_of_positive_naturals
    (hpos : ∀ t : ℕ, ∃ N : ℕ, ∀ B : Finset ℕ,
      (∀ b ∈ B, 0 < b) → N ≤ B.card →
        B.card ^ t ≤ (natSumProdValues B).card) :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
      A.card ^ k ≤ (sumProdValues A).card := by
  intro k
  obtain ⟨N, hN⟩ := hpos (k + k)
  let M := max N 3
  refine ⟨2 * M + 2, ?_⟩
  intro A hA
  let A0 := A.erase 0
  let P := A0.filter fun z : ℤ ↦ 0 < z
  let Q := A0.filter fun z : ℤ ↦ ¬ 0 < z
  have hparts : P.card + Q.card = A0.card := by
    simpa [P, Q] using A0.card_filter_add_card_filter_not (fun z : ℤ ↦ 0 < z)
  have hpred : A.card - 1 ≤ A0.card := by
    simpa [A0] using (Finset.pred_card_le_card_erase (s := A) (a := 0))
  have hA0large : 2 * M + 1 ≤ A0.card := by omega
  have hNM : N ≤ M := Nat.le_max_left N 3
  have h3M : 3 ≤ M := Nat.le_max_right N 3
  by_cases hQP : Q.card ≤ P.card
  · have hMP : M ≤ P.card := by omega
    have h3P : 3 ≤ P.card := h3M.trans hMP
    have hnP : A.card ≤ 3 * P.card := by omega
    let B := P.image Int.natAbs
    have hPnonneg : ∀ z ∈ P, 0 ≤ z := fun z hz ↦
      (Finset.mem_filter.mp hz).2.le
    have hPsub : P ⊆ A := fun _ hz ↦
      Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1
    have hBcard : B.card = P.card := by
      simpa [B] using card_image_natAbs_eq_of_nonneg P hPnonneg
    have hBpos : ∀ b ∈ B, 0 < b := by
      intro b hb
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
      exact Int.natAbs_pos.mpr (ne_of_gt (Finset.mem_filter.mp hz).2)
    have hNB : N ≤ B.card := by omega
    have hnat := hN B hBpos hNB
    have hmap : B.map natCastEmbedding = P := by
      simpa [B] using map_image_natAbs_natCast_eq_of_nonneg P hPnonneg
    calc
      A.card ^ k ≤ P.card ^ (k + k) := power_le_double_exponent h3P hnP
      _ = B.card ^ (k + k) := by rw [hBcard]
      _ ≤ (natSumProdValues B).card := hnat
      _ ≤ (sumProdValues (B.map natCastEmbedding)).card := card_natSumProdValues_le_cast B
      _ = (sumProdValues P).card := by rw [hmap]
      _ ≤ (sumProdValues A).card := Finset.card_le_card (sumProdValues_mono hPsub)
  · have hPQ : P.card ≤ Q.card := Nat.le_of_lt (Nat.lt_of_not_ge hQP)
    have hMQ : M ≤ Q.card := by omega
    have h3Q : 3 ≤ Q.card := h3M.trans hMQ
    have hnQ : A.card ≤ 3 * Q.card := by omega
    let B := Q.image Int.natAbs
    have hQnonpos : ∀ z ∈ Q, z ≤ 0 := fun z hz ↦
      le_of_not_gt (Finset.mem_filter.mp hz).2
    have hQsub : Q ⊆ A := fun _ hz ↦
      Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1
    have hBcard : B.card = Q.card := by
      simpa [B] using card_image_natAbs_eq_of_nonpos Q hQnonpos
    have hBpos : ∀ b ∈ B, 0 < b := by
      intro b hb
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
      apply Int.natAbs_pos.mpr
      intro hz0
      subst z
      have hzA0 : (0 : ℤ) ∈ A0 := (Finset.mem_filter.mp hz).1
      simpa [A0] using hzA0
    have hNB : N ≤ B.card := by omega
    have hnat := hN B hBpos hNB
    have hmap : B.map negNatCastEmbedding = Q := by
      simpa [B] using map_image_natAbs_negCast_eq_of_nonpos Q hQnonpos
    calc
      A.card ^ k ≤ Q.card ^ (k + k) := power_le_double_exponent h3Q hnQ
      _ = B.card ^ (k + k) := by rw [hBcard]
      _ ≤ (natSumProdValues B).card := hnat
      _ ≤ (sumProdValues (B.map negNatCastEmbedding)).card := card_natSumProdValues_le_neg B
      _ = (sumProdValues Q).card := by rw [hmap]
      _ ≤ (sumProdValues A).card := Finset.card_le_card (sumProdValues_mono hQsub)

end SignReduction

section HighRankCoefficientLayers

/-- A coefficient box with natural coefficients in a linearly independent
family. -/
def natCoefficientBox {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {d : ℕ} (H : ℕ) (v : Fin d → G) : Finset G :=
  Finset.univ.image fun a : Fin d → Fin H ↦ ∑ i, (a i : ℕ) • v i

theorem natCoefficientBox_injective
    {R G : Type*} [Field R] [CharZero R]
    [AddCommGroup G] [Module R G]
    {d H : ℕ} {v : Fin d → G} (hv : LinearIndependent R v) :
    Function.Injective (fun a : Fin d → Fin H ↦ ∑ i, (a i : ℕ) • v i) := by
  intro a b hab
  apply coefficientBox_injective (R := R) hv
  simpa only [Nat.cast_smul_eq_nsmul] using hab

theorem card_natCoefficientBox
    {R G : Type*} [Field R] [CharZero R]
    [AddCommGroup G] [Module R G] [DecidableEq G]
    {d H : ℕ} {v : Fin d → G} (hv : LinearIndependent R v) :
    (natCoefficientBox H v).card = H ^ d := by
  rw [natCoefficientBox, Finset.card_image_of_injective Finset.univ
    (natCoefficientBox_injective (R := R) hv)]
  simp

def coefficientLayer {d H : ℕ} (a : Fin d → Fin H) (j : Fin H) : Finset (Fin d) :=
  Finset.univ.filter fun i ↦ j.1 < (a i).1

lemma sum_coefficientLayers {G : Type*} [AddCommMonoid G]
    {d H : ℕ} (a : Fin d → Fin H) (v : Fin d → G) :
    ∑ j, ∑ i ∈ coefficientLayer a j, v i = ∑ i, (a i : ℕ) • v i := by
  classical
  simp only [coefficientLayer, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (∑ j : Fin H, if j.1 < (a i).1 then v i else 0) =
      (a i : ℕ) • v i by
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ.filter fun j : Fin H ↦ j.1 < (a i).1) =
        Finset.Iio (a i) := by
      ext j
      simp
    rw [hfilter]
    simp only [Finset.sum_const]
    rw [Fin.card_Iio]]

theorem natCoefficientBox_subset_nsmul_exponentSubsetSums
    {d H : ℕ} {B : Finset ℕ} {v : Fin d → (ℕ →₀ ℚ)}
    (hv : LinearIndependent ℚ v)
    (hvB : ∀ i, v i ∈ B.image exponentVector) :
    natCoefficientBox H v ⊆ H • exponentSubsetSums B := by
  let b : Fin d → ℕ := fun i ↦ Classical.choose (Finset.mem_image.mp (hvB i))
  have hbmem (i : Fin d) : b i ∈ B :=
    (Classical.choose_spec (Finset.mem_image.mp (hvB i))).1
  have hbvec (i : Fin d) : exponentVector (b i) = v i :=
    (Classical.choose_spec (Finset.mem_image.mp (hvB i))).2
  have hbinj : Function.Injective b := by
    intro i j hij
    apply hv.injective
    rw [← hbvec i, ← hbvec j, hij]
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  rw [← sum_coefficientLayers a v]
  have hlayer (j : Fin H) :
      (∑ i ∈ coefficientLayer a j, v i) ∈ exponentSubsetSums B := by
    let S := (coefficientLayer a j).image b
    apply mem_exponentSubsetSums_iff.mpr
    refine ⟨S, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hbmem i
    · rw [Finset.sum_image hbinj.injOn]
      apply Finset.sum_congr rfl
      intro i hi
      exact hbvec i
  have hset : (∑ j, ∑ i ∈ coefficientLayer a j, v i) ∈
      H • (exponentSubsetSums B : Set (ℕ →₀ ℚ)) := by
    rw [Set.mem_nsmul_iff_sum]
    exact ⟨fun j ↦ ∑ i ∈ coefficientLayer a j, v i, hlayer, rfl⟩
  change (∑ j, ∑ i ∈ coefficientLayer a j, v i) ∈
    (↑(H • exponentSubsetSums B) : Set (ℕ →₀ ℚ))
  simpa only [Finset.coe_nsmul] using hset

lemma nsmul_subset_succ_nsmul_sub (H : ℕ) (Y : Finset (ℕ →₀ ℚ))
    (hzero : 0 ∈ Y) :
    H • Y ⊆ (H + 1) • Y - Y := by
  intro x hx
  have hx' : x ∈ (H + 1) • Y := by
    rw [add_nsmul, one_nsmul]
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, add_zero x⟩
  exact Finset.mem_sub.mpr ⟨x, hx', 0, hzero, sub_zero x⟩

/-- A block whose exponent vectors have rank at least `D` contains a
coefficient box of cardinality `m ^ D` in the indicated difference set. -/
theorem high_rank_block_box (B : Finset ℕ) (m D : ℕ) (hm : 1 ≤ m)
    (hrank : D ≤ Module.finrank ℚ
      (Submodule.span ℚ (B.image exponentVector : Set (ℕ →₀ ℚ)))) :
    m ^ D ≤ ((m + 1) • exponentSubsetSums B - exponentSubsetSums B).card := by
  obtain ⟨v, hvB, _, hv⟩ :=
    finiteSet_exists_independent_spanning_family (R := ℚ)
      (B.image exponentVector)
  have hboxcard : (natCoefficientBox m v).card =
      m ^ Module.finrank ℚ
        (Submodule.span ℚ (B.image exponentVector : Set (ℕ →₀ ℚ))) :=
    card_natCoefficientBox (R := ℚ) hv
  have hboxsub : natCoefficientBox m v ⊆
      (m + 1) • exponentSubsetSums B - exponentSubsetSums B :=
    (natCoefficientBox_subset_nsmul_exponentSubsetSums hv hvB).trans
      (nsmul_subset_succ_nsmul_sub m _ (zero_mem_exponentSubsetSums B))
  calc
    m ^ D ≤ m ^ Module.finrank ℚ
        (Submodule.span ℚ (B.image exponentVector : Set (ℕ →₀ ℚ))) :=
      Nat.pow_le_pow_right hm hrank
    _ = (natCoefficientBox m v).card := hboxcard.symm
    _ ≤ ((m + 1) • exponentSubsetSums B - exponentSubsetSums B).card :=
      Finset.card_le_card hboxsub

end HighRankCoefficientLayers

section PositiveNaturalOuterArgument

open Filter Asymptotics

lemma le_sqrt_sqrt_of_fourth_pow_le {M n : ℕ} (h : M ^ 4 ≤ n) :
    M ≤ Nat.sqrt (Nat.sqrt n) := by
  apply Nat.le_sqrt.mpr
  apply Nat.le_sqrt.mpr
  simpa [pow_succ, mul_assoc] using h

lemma fourth_pow_sqrt_sqrt_le (n : ℕ) :
    (Nat.sqrt (Nat.sqrt n)) ^ 4 ≤ n := by
  have h1 := Nat.sqrt_le n
  have h2 := Nat.sqrt_le (Nat.sqrt n)
  calc
    (Nat.sqrt (Nat.sqrt n)) ^ 4 =
        (Nat.sqrt (Nat.sqrt n) * Nat.sqrt (Nat.sqrt n)) *
          (Nat.sqrt (Nat.sqrt n) * Nat.sqrt (Nat.sqrt n)) := by
            simp [pow_succ, mul_assoc]
    _ ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul h2 h2
    _ ≤ n := h1

lemma lt_succ_fourth_pow_sqrt_sqrt (n : ℕ) :
    n < (Nat.sqrt (Nat.sqrt n) + 1) ^ 4 := by
  have h1 := Nat.lt_succ_sqrt n
  have h2 := Nat.lt_succ_sqrt (Nat.sqrt n)
  have h1' : n < (Nat.sqrt n + 1) ^ 2 := by
    simpa [pow_two, Nat.succ_eq_add_one] using h1
  have h2' : Nat.sqrt n < (Nat.sqrt (Nat.sqrt n) + 1) ^ 2 := by
    simpa [pow_two, Nat.succ_eq_add_one] using h2
  have h3 : Nat.sqrt n + 1 ≤ (Nat.sqrt (Nat.sqrt n) + 1) ^ 2 :=
    Nat.succ_le_of_lt h2'
  calc
    n < (Nat.sqrt n + 1) ^ 2 := h1'
    _ ≤ ((Nat.sqrt (Nat.sqrt n) + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = (Nat.sqrt (Nat.sqrt n) + 1) ^ 4 := by rw [← pow_mul]

lemma card_pow_le_block_power {n m k : ℕ} (hm : 4 ≤ m)
    (hn : n < (m + 1) ^ 4) :
    n ^ k ≤ m ^ (3 * (2 * k + 1)) := by
  have hm1 : m + 1 ≤ 2 * m := by omega
  have hn' : n ≤ (2 * m) ^ 4 :=
    (Nat.le_of_lt hn).trans (Nat.pow_le_pow_left hm1 4)
  have htwo : 2 ^ (4 * k) = 4 ^ (2 * k) := by
    calc
      2 ^ (4 * k) = 2 ^ (2 * (2 * k)) := by
        congr 1
        omega
      _ = (2 ^ 2) ^ (2 * k) := by rw [pow_mul]
      _ = 4 ^ (2 * k) := by rw [show (2 : ℕ) ^ 2 = 4 by rfl]
  calc
    n ^ k ≤ ((2 * m) ^ 4) ^ k := Nat.pow_le_pow_left hn' k
    _ = (2 * m) ^ (4 * k) := by rw [pow_mul]
    _ = 2 ^ (4 * k) * m ^ (4 * k) := by rw [mul_pow]
    _ = 4 ^ (2 * k) * m ^ (4 * k) := by rw [htwo]
    _ ≤ m ^ (2 * k) * m ^ (4 * k) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm (2 * k))
    _ = m ^ (2 * k + 4 * k) := by rw [pow_add]
    _ ≤ m ^ (3 * (2 * k + 1)) := Nat.pow_le_pow_right (by omega) (by omega)

lemma eventually_nat_pow_le_two_pow_pred (r : ℕ) :
    ∃ M : ℕ, ∀ m, M ≤ m → 1 ≤ m → m ^ r ≤ 2 ^ (m - 1) := by
  have H := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) r
    (show (1 : ℝ) < 2 by norm_num)).def (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [eventually_atTop] at H
  obtain ⟨M, hM⟩ := H
  refine ⟨M, ?_⟩
  intro m hm hm1
  have hr := hM m hm
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ m) r),
    abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)) m)] at hr
  have heq : (1 / 2 : ℝ) * 2 ^ m = 2 ^ (m - 1) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [pow_succ, Nat.succ_sub_one]
    ring
  rw [heq] at hr
  exact_mod_cast hr

/-- End-to-end positive-natural argument, parameterized by the rank-energy
estimate and the high-rank coefficient-box estimate. -/
theorem positive_natural_resolution_of_rank_tools
    (energyRank : ∀ (h : ℕ), 1 < h → ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a) →
      hAddEnergy h A ≤ ((2 * h) ^ 2) ^
        (Module.finrank ℚ
          (Submodule.span ℚ (A.image exponentVector : Set (ℕ →₀ ℚ))) * h) *
          A.card ^ h)
    (highBox : ∀ (B : Finset ℕ) (m D : ℕ), 1 ≤ m →
      D ≤ Module.finrank ℚ
        (Submodule.span ℚ (B.image exponentVector : Set (ℕ →₀ ℚ))) →
      m ^ D ≤ ((m + 1) • exponentSubsetSums B - exponentSubsetSums B).card) :
    ∀ k, ∃ N, ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → N ≤ A.card →
      A.card ^ k ≤ (natSumProdValues A).card := by
  intro k
  let t := 2 * k + 1
  let h := 3 * t + 1
  let q := (2 * h) ^ 2
  let C := q ^ h
  obtain ⟨Mexp, hMexp⟩ := eventually_nat_pow_le_two_pow_pred (3 * t)
  let M := max 8 (max (2 * h) (max ((4 * C) ^ h) (max Mexp 4)))
  refine ⟨M ^ 4, ?_⟩
  intro A hA hNA
  let m := Nat.sqrt (Nat.sqrt A.card)
  have hMm : M ≤ m := le_sqrt_sqrt_of_fourth_pow_le hNA
  have hm8 : 8 ≤ m := (show 8 ≤ M by simp [M]).trans hMm
  have hm4 : 4 ≤ m := (show 4 ≤ M by simp [M]).trans hMm
  have hmpos : 0 < m := by omega
  have hmh : 2 * h ≤ m := (show 2 * h ≤ M by simp [M]).trans hMm
  have hmC : (4 * C) ^ h ≤ m := (show (4 * C) ^ h ≤ M by simp [M]).trans hMm
  have hmexp : Mexp ≤ m := (show Mexp ≤ M by simp [M]).trans hMm
  have hm3 : m ^ 3 ≤ A.card := by
    calc
      m ^ 3 ≤ m ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ A.card := fourth_pow_sqrt_sqrt_le A.card
  obtain ⟨A0, hA0, hA0card⟩ := Finset.exists_subset_card_eq hm3
  have hA0pos : ∀ a ∈ A0, 0 < a := fun a ha ↦ hA a (hA0 ha)
  obtain ⟨B, hBcard, hBsub, hBpair, hBunion⟩ :=
    exists_cube_blocks A0 m hmpos.ne' hA0card
  let X : ℕ → Finset (ℕ →₀ ℚ) := fun i ↦ prefixExponentSums B i
  let Y : ℕ → Finset (ℕ →₀ ℚ) := fun i ↦ exponentSubsetSums (blockAt B i)
  let S := A0.subsetSum.card
  have hindex {i : ℕ} (hi : i < m * (m - 1)) : i < m ^ 2 := by
    have hlt : m * (m - 1) < m * m :=
      Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (by omega) (by omega)) hmpos
    exact hi.trans (by simpa [pow_two] using hlt)
  have hX : ∀ i ≤ m * (m - 1), (X i).Nonempty := by
    intro i hi
    exact prefixExponentSums_nonempty B i
  have hrec : ∀ i < m * (m - 1), X (i + 1) = X i + Y i := by
    intro i hi
    have hiq := hindex hi
    simpa [X, Y, blockAt, hiq] using prefixExponentSums_succ B hBpair hiq
  have hblock : ∀ i < m * (m - 1),
      m ^ (3 * t) ≤ S ∨ m ^ (3 * t + 2) ≤ ((m + 1) • Y i - Y i).card := by
    intro i hi
    have hiq := hindex hi
    let Bi := B ⟨i, hiq⟩
    let d := Module.finrank ℚ
      (Submodule.span ℚ (Bi.image exponentVector : Set (ℕ →₀ ℚ)))
    by_cases hd : 3 * t + 2 ≤ d
    · right
      simpa [Y, blockAt, hiq, Bi] using highBox Bi m (3 * t + 2) (by omega) hd
    · left
      have hdh : d ≤ h := by omega
      have hE := energyRank h (by omega) Bi (fun a ha ↦ hA0pos a (hBsub _ ha))
      have hqpos : 0 < q := by
        dsimp [q, h]
        positivity
      have hqunif : q ^ (d * h) ≤ C ^ h := by
        change q ^ (d * h) ≤ (q ^ h) ^ h
        rw [pow_mul]
        exact Nat.pow_le_pow_left (Nat.pow_le_pow_right hqpos hdh) h
      have hE' : hAddEnergy h Bi ≤ C ^ h * Bi.card ^ h :=
        hE.trans (by gcongr)
      have hsum := card_pow_pred_le_card_subsetSum_of_hAddEnergy_le h C Bi
        (by omega) (by dsimp [C, q, h]; positivity)
        (by simpa [Bi, hBcard, h] using hmh) hE'
        (by simpa [Bi, hBcard] using hmC)
      have hlocal : m ^ (3 * t) ≤ Bi.subsetSum.card := by
        simpa [Bi, hBcard, h] using hsum
      exact hlocal.trans (Finset.card_le_card (Finset.subsetSum_mono (hBsub _)))
  have hexp : m ^ (3 * t) ≤ 2 ^ (m - 1) := hMexp m hmexp (by omega)
  have hdich := cube_block_dichotomy m t S X Y hm8 hX hrec hblock hexp
  have htarget : A.card ^ k ≤ m ^ (3 * t) := by
    simpa [t] using card_pow_le_block_power hm4 (lt_succ_fourth_pow_sqrt_sqrt A.card)
  apply htarget.trans
  have hnatMono : natSumProdValues A0 ⊆ natSumProdValues A :=
    Finset.union_subset_union (Finset.subsetSum_mono hA0) (subsetProducts_mono hA0)
  rcases hdich with hsum | ⟨i, hi, hprod⟩
  · exact hsum.trans <|
      (Finset.card_le_card (show A0.subsetSum ⊆ natSumProdValues A0 from
        Finset.subset_union_left)).trans (Finset.card_le_card hnatMono)
  · calc
      m ^ (3 * t) ≤ (X i).card := hprod
      _ ≤ (exponentSubsetSums A0).card :=
        Finset.card_le_card (prefixExponentSums_subset_full B A0 hBsub i)
      _ = (subsetProducts A0).card :=
        card_exponentSubsetSums_eq_card_subsetProducts A0 (fun a ha ↦ (hA0pos a ha).ne')
      _ ≤ (natSumProdValues A0).card :=
        Finset.card_le_card (show subsetProducts A0 ⊆ natSumProdValues A0 from
          Finset.subset_union_right)
      _ ≤ (natSumProdValues A).card := Finset.card_le_card hnatMono

end PositiveNaturalOuterArgument

/-! ## Integrated checked module: E53Mixed -/

open scoped BigOperators NNReal


noncomputable section

section FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G]

private def subTupleSum {A : Finset G} {h : ℕ} (x : Fin h → ↑A) : G :=
  ∑ i, (x i : G)

/-- Ordered `h`-fold additive energy, presented directly as a solution count. -/
def rawHAddEnergy (h : ℕ) (A : Finset G) : ℕ :=
  by
    classical
    exact ((Finset.univ : Finset ((Fin h → ↑A) × (Fin h → ↑A))).filter
      (fun xy ↦ subTupleSum xy.2 = subTupleSum xy.1)).card

/-- The mixed energy with one variable from `A` and `h-1` variables from `B`
on each side. -/
def rawMixedEnergy (h : ℕ) (A B : Finset G) : ℕ :=
  by
    classical
    exact ((Finset.univ : Finset
        (((↑A) × (Fin (h - 1) → ↑B)) × ((↑A) × (Fin (h - 1) → ↑B)))).filter
      (fun xy : (((↑A) × (Fin (h - 1) → ↑B)) × ((↑A) × (Fin (h - 1) → ↑B))) ↦
        (xy.1.1 : G) + subTupleSum xy.1.2 =
          (xy.2.1 : G) + subTupleSum xy.2.2)).card

def charSum (A : Finset G) (ψ : AddChar G ℂ) : ℂ :=
  ∑ a : ↑A, ψ (a : G)

private def charSumNeg (A : Finset G) (ψ : AddChar G ℂ) : ℂ :=
  ∑ a : ↑A, ψ (-(a : G))

@[simp] private lemma addChar_norm_eq_one (ψ : AddChar G ℂ) (a : G) :
    ‖ψ a‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _)
    (Fintype.card_pos (α := G)).ne').mp ?_
  rw [← norm_pow, ← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero,
    AddChar.map_zero_eq_one, norm_one]

private lemma charSumNeg_eq_conj (A : Finset G) (ψ : AddChar G ℂ) :
    charSumNeg A ψ = star (charSum A ψ) := by
  rw [charSumNeg, charSum, star_sum]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    ψ (-(a : G)) = (ψ (a : G))⁻¹ := AddChar.map_neg_eq_inv ψ (a : G)
    _ = star (ψ (a : G)) := Complex.inv_eq_conj (addChar_norm_eq_one ψ (a : G))

private lemma charSum_pow (h : ℕ) (A : Finset G) (ψ : AddChar G ℂ) :
    charSum A ψ ^ h = ∑ x : Fin h → ↑A, ψ (subTupleSum x) := by
  rw [charSum, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  symm
  change ψ (∑ i, (x i : G)) = ∏ i, ψ (x i : G)
  have hmap (s : Finset (Fin h)) :
      ψ (∑ i ∈ s, (x i : G)) = ∏ i ∈ s, ψ (x i : G) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.sum_insert his, Finset.prod_insert his,
          AddChar.map_add_eq_mul, ih]
  simpa using hmap Finset.univ

private lemma charSumNeg_pow (h : ℕ) (A : Finset G) (ψ : AddChar G ℂ) :
    charSumNeg A ψ ^ h = ∑ x : Fin h → ↑A, ψ (-subTupleSum x) := by
  rw [charSumNeg, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro x
  symm
  change ψ (-(∑ i, (x i : G))) = ∏ i, ψ (-(x i : G))
  rw [← Finset.sum_neg_distrib]
  have hmap (s : Finset (Fin h)) :
      ψ (∑ i ∈ s, -(x i : G)) = ∏ i ∈ s, ψ (-(x i : G)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.sum_insert his, Finset.prod_insert his,
          AddChar.map_add_eq_mul, ih]
  simpa using hmap Finset.univ

private lemma charMoment_eq_energy (h : ℕ) (A : Finset G) :
    ∑ ψ : AddChar G ℂ,
        (charSum A ψ * charSumNeg A ψ) ^ h =
      (Fintype.card G : ℂ) * rawHAddEnergy h A := by
  classical
  simp_rw [mul_pow, charSum_pow, charSumNeg_pow]
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ y : Fin h → ↑A, ∑ x : Fin h → ↑A, ∑ ψ : AddChar G ℂ,
          ψ (subTupleSum x) * ψ (-subTupleSum y) := by
        rw [Finset.sum_comm]
        apply Fintype.sum_congr
        intro y
        rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [← AddChar.map_add_eq_mul, AddChar.sum_apply_eq_ite]
      rw [← Fintype.sum_prod_type']
      simp_rw [show ∀ (xy : (Fin h → ↑A) × (Fin h → ↑A)),
          (if subTupleSum xy.2 + -subTupleSum xy.1 = 0
            then (Fintype.card G : ℂ) else 0) =
          (Fintype.card G : ℂ) *
            (if subTupleSum xy.2 = subTupleSum xy.1 then 1 else 0) by
        intro xy
        by_cases heq : subTupleSum xy.2 = subTupleSum xy.1
        · simp [heq]
        · simp [heq, add_eq_zero_iff_eq_neg]]
      rw [← Finset.mul_sum, Finset.sum_boole]
      rfl

private lemma nnreal_charMoment_eq_energy (h : ℕ) (A : Finset G) :
    ∑ ψ : AddChar G ℂ, ‖charSum A ψ‖₊ ^ (2 * h) =
      (Fintype.card G : ℝ≥0) * rawHAddEnergy h A := by
  apply NNReal.eq
  apply Complex.ofReal_injective
  simpa [charSumNeg_eq_conj, pow_mul, Complex.mul_conj'] using
    charMoment_eq_energy h A

section ArbitraryPair

def familyTupleSum {h : ℕ} (S : Fin h → Finset G)
    (x : ∀ i, ↑(S i)) : G :=
  ∑ i, (x i : G)

/-- Number of additive relations whose left and right coordinate `i` is
restricted to the corresponding set `L i` and `R i`. -/
def rawFamilyEnergy (h : ℕ) (L R : Fin h → Finset G) : ℕ := by
  classical
  exact ((Finset.univ : Finset ((∀ i, ↑(R i)) × (∀ i, ↑(L i)))).filter
    (fun xy ↦ familyTupleSum L xy.2 = familyTupleSum R xy.1)).card

private def familyCharProd {h : ℕ} (S : Fin h → Finset G)
    (ψ : AddChar G ℂ) : ℂ :=
  ∏ i, charSum (S i) ψ

private def familyCharProdNeg {h : ℕ} (S : Fin h → Finset G)
    (ψ : AddChar G ℂ) : ℂ :=
  ∏ i, charSumNeg (S i) ψ

private lemma familyCharProd_eq_sum {h : ℕ} (S : Fin h → Finset G)
    (ψ : AddChar G ℂ) :
    familyCharProd S ψ = ∑ x : ∀ i, ↑(S i), ψ (familyTupleSum S x) := by
  rw [familyCharProd]
  simp_rw [charSum]
  rw [Fintype.prod_sum]
  apply Fintype.sum_congr
  intro x
  symm
  change ψ (∑ i, (x i : G)) = ∏ i, ψ (x i : G)
  have hmap (s : Finset (Fin h)) :
      ψ (∑ i ∈ s, (x i : G)) = ∏ i ∈ s, ψ (x i : G) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.sum_insert his, Finset.prod_insert his,
          AddChar.map_add_eq_mul, ih]
  simpa using hmap Finset.univ

private lemma familyCharProdNeg_eq_sum {h : ℕ} (S : Fin h → Finset G)
    (ψ : AddChar G ℂ) :
    familyCharProdNeg S ψ = ∑ x : ∀ i, ↑(S i), ψ (-familyTupleSum S x) := by
  rw [familyCharProdNeg]
  simp_rw [charSumNeg]
  rw [Fintype.prod_sum]
  apply Fintype.sum_congr
  intro x
  symm
  change ψ (-(∑ i, (x i : G))) = ∏ i, ψ (-(x i : G))
  rw [← Finset.sum_neg_distrib]
  have hmap (s : Finset (Fin h)) :
      ψ (∑ i ∈ s, -(x i : G)) = ∏ i ∈ s, ψ (-(x i : G)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.sum_insert his, Finset.prod_insert his,
          AddChar.map_add_eq_mul, ih]
  simpa using hmap Finset.univ

private lemma familyCharMoment_eq_energy (h : ℕ) (L R : Fin h → Finset G) :
    ∑ ψ : AddChar G ℂ, familyCharProd L ψ * familyCharProdNeg R ψ =
      (Fintype.card G : ℂ) * rawFamilyEnergy h L R := by
  classical
  simp_rw [familyCharProd_eq_sum, familyCharProdNeg_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ y : ((i : Fin h) → ↑(R i)),
          ∑ x : ((i : Fin h) → ↑(L i)), ∑ ψ : AddChar G ℂ,
            ψ (familyTupleSum L x) * ψ (-familyTupleSum R y) := by
        rw [Finset.sum_comm]
        apply Fintype.sum_congr
        intro y
        rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [← AddChar.map_add_eq_mul, AddChar.sum_apply_eq_ite]
      rw [← Fintype.sum_prod_type']
      simp_rw [show ∀ (xy : ((i : Fin h) → ↑(R i)) × ((i : Fin h) → ↑(L i))),
          (if familyTupleSum L xy.2 + -familyTupleSum R xy.1 = 0
            then (Fintype.card G : ℂ) else 0) =
          (Fintype.card G : ℂ) *
            (if familyTupleSum L xy.2 = familyTupleSum R xy.1 then 1 else 0) by
        intro xy
        by_cases heq : familyTupleSum L xy.2 = familyTupleSum R xy.1
        · simp [heq]
        · simp [heq, add_eq_zero_iff_eq_neg]]
      rw [← Finset.mul_sum, Finset.sum_boole]
      rfl

/-- The set imposed at position `p`: `B` at the two selected positions and
`A` everywhere else. -/
def pairPositionSet {h : ℕ} (A B : Finset G)
    (r s p : Fin h ⊕ Fin h) : Finset G :=
  if p = r ∨ p = s then B else A

/-- Additive relations with the variables at the two distinct selected
positions restricted to `B`, and every other variable restricted to `A`.
The positions may be on opposite sides or on the same side. -/
def rawPairRestrictedEnergy (h : ℕ) (A B : Finset G)
    (r s : Fin h ⊕ Fin h) : ℕ :=
  rawFamilyEnergy h
    (fun i ↦ pairPositionSet A B r s (.inl i))
    (fun i ↦ pairPositionSet A B r s (.inr i))

private lemma norm_familyCharProd (h : ℕ) (A B : Finset G)
    (r s : Fin h ⊕ Fin h) (hrs : r ≠ s) (ψ : AddChar G ℂ) :
    ‖familyCharProd (fun i ↦ pairPositionSet A B r s (.inl i)) ψ *
        familyCharProdNeg (fun i ↦ pairPositionSet A B r s (.inr i)) ψ‖₊ =
      ‖charSum B ψ‖₊ ^ 2 * ‖charSum A ψ‖₊ ^ (2 * h - 2) := by
  simp only [familyCharProd, familyCharProdNeg, nnnorm_mul,
    charSumNeg_eq_conj]
  rw [nnnorm_prod, nnnorm_prod]
  simp only [nnnorm_star]
  rw [← Fintype.prod_sum_type (fun p : Fin h ⊕ Fin h ↦
    ‖charSum (pairPositionSet A B r s p) ψ‖₊)]
  change (∏ p : Fin h ⊕ Fin h,
      ‖charSum (pairPositionSet A B r s p) ψ‖₊) = _
  simp only [pairPositionSet]
  have hterm (p : Fin h ⊕ Fin h) :
      ‖charSum (if p = r ∨ p = s then B else A) ψ‖₊ =
        if p = r ∨ p = s then ‖charSum B ψ‖₊ else ‖charSum A ψ‖₊ := by
    split_ifs <;> rfl
  simp_rw [hterm]
  change (∏ p ∈ (Finset.univ : Finset (Fin h ⊕ Fin h)),
      if p = r ∨ p = s then ‖charSum B ψ‖₊ else ‖charSum A ψ‖₊) = _
  rw [Finset.prod_ite]
  have hsel : (Finset.univ.filter fun p : Fin h ⊕ Fin h ↦ p = r ∨ p = s) = {r, s} := by
    ext p
    simp [eq_comm]
  have hnsel : (Finset.univ.filter fun p : Fin h ⊕ Fin h ↦ ¬(p = r ∨ p = s)) =
      Finset.univ \ {r, s} := by
    ext p
    simp [eq_comm]
  have hcardsel : ({r, s} : Finset (Fin h ⊕ Fin h)).card = 2 := by
    simp [hrs]
  have hcardnsel : (Finset.univ \ {r, s} : Finset (Fin h ⊕ Fin h)).card = 2 * h - 2 := by
    rw [Finset.card_sdiff]
    rw [Finset.inter_univ]
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, hcardsel]
    omega
  rw [hsel, hnsel]
  simp only [Finset.prod_const, hcardsel, hcardnsel]

/-- A collision class with any two prescribed positions is bounded by the
common mixed Fourier moment.  This is the form used immediately after the
`p`-adic repeated-minimum cover; it treats LL, RR, and LR pairs uniformly. -/
theorem card_mul_rawPairRestrictedEnergy_le_mixedMoment
    (h : ℕ) (A B : Finset G) (r s : Fin h ⊕ Fin h) (hrs : r ≠ s) :
    (Fintype.card G : ℝ≥0) * rawPairRestrictedEnergy h A B r s ≤
      ∑ ψ : AddChar G ℂ,
        ‖charSum B ψ‖₊ ^ 2 * ‖charSum A ψ‖₊ ^ (2 * h - 2) := by
  have heq := familyCharMoment_eq_energy h
    (fun i ↦ pairPositionSet A B r s (.inl i))
    (fun i ↦ pairPositionSet A B r s (.inr i))
  calc
    (Fintype.card G : ℝ≥0) * rawPairRestrictedEnergy h A B r s =
        ‖(Fintype.card G : ℂ) * rawPairRestrictedEnergy h A B r s‖₊ := by simp
    _ = ‖∑ ψ : AddChar G ℂ,
          familyCharProd (fun i ↦ pairPositionSet A B r s (.inl i)) ψ *
            familyCharProdNeg (fun i ↦ pairPositionSet A B r s (.inr i)) ψ‖₊ := by
        rw [heq]
        rfl
    _ ≤ ∑ ψ : AddChar G ℂ,
          ‖familyCharProd (fun i ↦ pairPositionSet A B r s (.inl i)) ψ *
            familyCharProdNeg (fun i ↦ pairPositionSet A B r s (.inr i)) ψ‖₊ :=
        nnnorm_sum_le _ _
    _ = _ := by
      apply Fintype.sum_congr
      intro ψ
      exact norm_familyCharProd h A B r s hrs ψ

private lemma mixedMoment_holder_nat {X : Type*} (S : Finset X) (f g : X → ℝ≥0)
    {h : ℕ} (hh : 2 ≤ h) :
    ∑ x ∈ S, (f x) ^ (2 : ℝ) * (g x) ^ (2 * ((h : ℝ) - 1)) ≤
      (∑ x ∈ S, (f x) ^ (2 * (h : ℝ))) ^ (1 / (h : ℝ)) *
        (∑ x ∈ S, (g x) ^ (2 * (h : ℝ))) ^ (((h : ℝ) - 1) / (h : ℝ)) := by
  have hc : Real.HolderConjugate (h : ℝ) ((h : ℝ) / ((h : ℝ) - 1)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hh)
    · have h1 : (1 : ℝ) < h := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hh)
      field_simp
      ring
  have H := NNReal.inner_le_Lp_mul_Lq S
    (fun x ↦ (f x) ^ (2 : ℝ))
    (fun x ↦ (g x) ^ (2 * ((h : ℝ) - 1))) hc
  have hhm10 : (h : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < h := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hh)
    linarith
  have hmul : 2 * ((h : ℝ) - 1) * ((h : ℝ) / ((h : ℝ) - 1)) =
      2 * (h : ℝ) := by field_simp
  have hinv : 1 / ((h : ℝ) / ((h : ℝ) - 1)) =
      ((h : ℝ) - 1) / (h : ℝ) := by field_simp
  simpa only [← NNReal.rpow_mul, hmul, hinv, mul_comm (2 : ℝ) (h : ℝ)] using H

/-- Root form of the arbitrary-position mixed-energy inequality. -/
theorem rawPairRestrictedEnergy_rpow_le (h : ℕ) (A B : Finset G)
    (r s : Fin h ⊕ Fin h) (hrs : r ≠ s) (hh : 1 < h) :
    (rawPairRestrictedEnergy h A B r s : ℝ≥0) ≤
      (rawHAddEnergy h B : ℝ≥0) ^ (1 / (h : ℝ)) *
        (rawHAddEnergy h A : ℝ≥0) ^ (((h : ℝ) - 1) / (h : ℝ)) := by
  have hh2 : 2 ≤ h := hh
  have Hpair := card_mul_rawPairRestrictedEnergy_le_mixedMoment h A B r s hrs
  have Hhold := mixedMoment_holder_nat (Finset.univ : Finset (AddChar G ℂ))
    (fun ψ ↦ ‖charSum B ψ‖₊) (fun ψ ↦ ‖charSum A ψ‖₊) hh2
  have Hmixed :
      (∑ ψ : AddChar G ℂ,
          ‖charSum B ψ‖₊ ^ 2 * ‖charSum A ψ‖₊ ^ (2 * h - 2)) ≤
        ((Fintype.card G : ℝ≥0) * rawHAddEnergy h B) ^ (1 / (h : ℝ)) *
          ((Fintype.card G : ℝ≥0) * rawHAddEnergy h A) ^
            (((h : ℝ) - 1) / (h : ℝ)) := by
    rw [← nnreal_charMoment_eq_energy h B, ← nnreal_charMoment_eq_energy h A]
    have hexp : ((2 * h - 2 : ℕ) : ℝ) = 2 * ((h : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * h), Nat.cast_mul]
      norm_num
      ring
    simpa only [← NNReal.rpow_natCast, Nat.cast_ofNat, Nat.cast_mul, hexp] using Hhold
  have H := Hpair.trans Hmixed
  have hc : (0 : ℝ≥0) < Fintype.card G := by positivity
  rw [NNReal.mul_rpow, NNReal.mul_rpow] at H
  have hsum : 1 / (h : ℝ) + ((h : ℝ) - 1) / (h : ℝ) = 1 := by
    field_simp
    ring
  have H' :
      (Fintype.card G : ℝ≥0) * rawPairRestrictedEnergy h A B r s ≤
        ((Fintype.card G : ℝ≥0) ^ (1 / (h : ℝ)) *
          (Fintype.card G : ℝ≥0) ^ (((h : ℝ) - 1) / (h : ℝ))) *
            ((rawHAddEnergy h B : ℝ≥0) ^ (1 / (h : ℝ)) *
              (rawHAddEnergy h A : ℝ≥0) ^ (((h : ℝ) - 1) / (h : ℝ))) := by
    calc
      _ ≤ _ := H
      _ = _ := by ac_rfl
  rw [← NNReal.rpow_add hc.ne', hsum, NNReal.rpow_one] at H'
  exact (mul_le_mul_iff_left₀ hc).mp (by simpa [mul_comm] using H')

/-- Arbitrary-pair mixed-energy Hölder inequality.  Unlike
`rawMixedEnergy_pow_le`, the selected positions may occur on the same side. -/
theorem rawPairRestrictedEnergy_pow_le (h : ℕ) (A B : Finset G)
    (r s : Fin h ⊕ Fin h) (hrs : r ≠ s) (hh : 1 < h) :
    rawPairRestrictedEnergy h A B r s ^ h ≤
      rawHAddEnergy h B * rawHAddEnergy h A ^ (h - 1) := by
  have H := rawPairRestrictedEnergy_rpow_le h A B r s hrs hh
  have Hp := NNReal.rpow_le_rpow H (show (0 : ℝ) ≤ h by positivity)
  have hh0 : (h : ℝ) ≠ 0 := by positivity
  have h₁ : (1 / (h : ℝ)) * h = 1 := by field_simp
  have h₂ : (((h : ℝ) - 1) / (h : ℝ)) * h = ((h - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ h)]
    norm_num
    field_simp
  rw [NNReal.mul_rpow] at Hp
  have Hr :
      (rawPairRestrictedEnergy h A B r s : ℝ≥0) ^ (h : ℝ) ≤
        (rawHAddEnergy h B : ℝ≥0) *
          (rawHAddEnergy h A : ℝ≥0) ^ ((h - 1 : ℕ) : ℝ) := by
    simpa only [← NNReal.rpow_mul, h₁, h₂, NNReal.rpow_one] using Hp
  have Hnn :
      (rawPairRestrictedEnergy h A B r s : ℝ≥0) ^ h ≤
        (rawHAddEnergy h B : ℝ≥0) * (rawHAddEnergy h A : ℝ≥0) ^ (h - 1) := by
    simpa only [NNReal.rpow_natCast] using Hr
  exact_mod_cast Hnn

end ArbitraryPair

section ZModNoWrap

/-- Image of a finite natural set in a sufficiently large cyclic group. -/
def natCastImage (N : ℕ) (A : Finset ℕ) : Finset (ZMod N) :=
  A.image fun a : ℕ ↦ (a : ZMod N)

def natFourierPoly (N : ℕ) [NeZero N] (A : Finset ℕ) (x : ZMod N) : ℂ :=
  ∑ a ∈ A, ZMod.stdAddChar ((a : ZMod N) * x)

lemma charSum_natCastImage_zmodAddEquiv
    (N : ℕ) [NeZero N] (A : Finset ℕ) (hA : ∀ a ∈ A, a < N)
    (x : ZMod N) :
    charSum (natCastImage N A) ((AddChar.zmodAddEquiv (n := N)).toEquiv x) =
      natFourierPoly N A x := by
  classical
  rw [charSum, Finset.sum_coe_sort]
  change ∑ z ∈ natCastImage N A, AddChar.zmodAddEquiv x z = _
  rw [natCastImage, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    change ((AddChar.zmod N x (a : ZMod N) : Circle) : ℂ) = _
    rw [mul_comm]
    rfl
  · intro a ha b hb hab
    have hv := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (hA a ha),
      Nat.mod_eq_of_lt (hA b hb)] using hv

/-- Character reindexing converts the abstract full-dual moment of the cast
image into the standard `ZMod` moment indexed by frequencies `x`. -/
lemma sum_charSum_natCastImage_eq_natFourierMoment
    (N h : ℕ) [NeZero N] (A : Finset ℕ) (hA : ∀ a ∈ A, a < N) :
    ∑ ψ : AddChar (ZMod N) ℂ, ‖charSum (natCastImage N A) ψ‖₊ ^ (2 * h) =
      ∑ x : ZMod N, ‖natFourierPoly N A x‖₊ ^ (2 * h) := by
  rw [← (AddChar.zmodAddEquiv (n := N)).toEquiv.sum_comp]
  apply Fintype.sum_congr
  intro x
  rw [charSum_natCastImage_zmodAddEquiv N A hA x]

/-- The no-wrap raw-energy bridge, reduced to the already proved standard
`ZMod` moment identity. -/
theorem rawHAddEnergy_natCastImage_eq_of_moment
    (N h : ℕ) [NeZero N] (A : Finset ℕ) (hA : ∀ a ∈ A, a < N)
    (hmoment :
      ∑ x : ZMod N, ‖natFourierPoly N A x‖₊ ^ (2 * h) =
        (N : ℝ≥0) * hAddEnergy h A) :
    rawHAddEnergy h (natCastImage N A) = hAddEnergy h A := by
  have habstract := nnreal_charMoment_eq_energy (G := ZMod N) h (natCastImage N A)
  rw [sum_charSum_natCastImage_eq_natFourierMoment N h A hA, hmoment] at habstract
  simp only [ZMod.card] at habstract
  have habstract' :
      (N : ℝ≥0) * rawHAddEnergy h (natCastImage N A) =
        (N : ℝ≥0) * hAddEnergy h A := habstract.symm
  have hN : (0 : ℝ≥0) < N := by exact_mod_cast (NeZero.pos N)
  exact_mod_cast (mul_left_cancel₀ hN.ne' habstract')

end ZModNoWrap

end FiniteFourier

end

/-! ## Integrated checked module: E53Padic -/

open scoped BigOperators NNReal


lemma prime_factorization_tuple_min_repeated
    {h : ℕ} (hh : 0 < h) (u v : Fin h → ℕ)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (p : ℕ) (hp : p.Prime) (hsum : ∑ i, u i = ∑ i, v i) :
    ∃ r s : Sum (Fin h) (Fin h), r ≠ s ∧
      ((Sum.elim u v r).factorization p = (Sum.elim u v s).factorization p) ∧
      ∀ t, (Sum.elim u v r).factorization p ≤ (Sum.elim u v t).factorization p := by
  let y : Sum (Fin h) (Fin h) → ℕ := Sum.elim u v
  let L : Finset (Sum (Fin h) (Fin h)) := Finset.univ.image Sum.inl
  let R : Finset (Sum (Fin h) (Fin h)) := Finset.univ.image Sum.inr
  have hI : (Finset.univ : Finset (Sum (Fin h) (Fin h))).Nonempty := by
    exact ⟨Sum.inl ⟨0, hh⟩, Finset.mem_univ _⟩
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun z ↦ (y z).factorization p) hI
  have hmin' : ∀ z, (y r).factorization p ≤ (y z).factorization p :=
    fun z ↦ hmin z (Finset.mem_univ z)
  have hy : ∀ z, 0 < y z := by
    rintro (i | i) <;> simp [y, hu, hv]
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    rintro z hzL hzR
    simp only [L, R, Finset.mem_image, Finset.mem_univ, true_and] at hzL hzR
    obtain ⟨i, rfl⟩ := hzL
    obtain ⟨j, h⟩ := hzR
    cases h
  have hcover : L ∪ R = Finset.univ := by
    ext z
    rcases z with i | i <;> simp [L, R]
  have hsum' : ∑ z ∈ L, y z = ∑ z ∈ R, y z := by
    calc
      ∑ z ∈ L, y z = ∑ i : Fin h, u i := by
        change (Finset.univ.image Sum.inl).sum y = _
        rw [Finset.sum_image Sum.inl_injective.injOn]
        simp [y]
      _ = ∑ i : Fin h, v i := hsum
      _ = ∑ z ∈ R, y z := by
        change _ = (Finset.univ.image Sum.inr).sum y
        rw [Finset.sum_image Sum.inr_injective.injOn]
        simp [y]
  obtain ⟨s, hsr, heq⟩ := prime_factorization_min_repeated
    L R hdisj hcover y hy p hp hsum' r hmin'
  exact ⟨r, s, Ne.symm hsr, heq.symm, hmin'⟩

def natEnergyPairs' (h : ℕ) (A : Finset ℕ) :
    Finset ((Fin h → ℕ) × (Fin h → ℕ)) :=
  ((orderedTuples h A).product (orderedTuples h A)).filter fun z ↦
    tupleSum h z.1 = tupleSum h z.2

def natPairValue' {h : ℕ} (z : (Fin h → ℕ) × (Fin h → ℕ)) :
    Sum (Fin h) (Fin h) → ℕ := Sum.elim z.1 z.2

def natValuationCollisionPairs' (h : ℕ) (A : Finset ℕ) (p : ℕ)
    (r s : Sum (Fin h) (Fin h)) :
    Finset ((Fin h → ℕ) × (Fin h → ℕ)) :=
  (natEnergyPairs' h A).filter fun z ↦
    (natPairValue' z r).factorization p = (natPairValue' z s).factorization p

def natValuationExponents' (A : Finset ℕ) (p : ℕ) : Finset ℕ :=
  A.image fun a ↦ a.factorization p

def natValuationCell' (A : Finset ℕ) (p e : ℕ) : Finset ℕ :=
  A.filter fun a ↦ a.factorization p = e

def natValuationCollisionCellPairs' (h : ℕ) (A : Finset ℕ) (p e : ℕ)
    (r s : Sum (Fin h) (Fin h)) :
    Finset ((Fin h → ℕ) × (Fin h → ℕ)) :=
  (natEnergyPairs' h A).filter fun z ↦
    (natPairValue' z r).factorization p = e ∧
      (natPairValue' z s).factorization p = e

lemma card_natEnergyPairs'_eq_hAddEnergy (h : ℕ) (A : Finset ℕ) :
    (natEnergyPairs' h A).card = hAddEnergy h A := by
  classical
  let T := orderedTuples h A
  let s : (Fin h → ℕ) → ℕ := tupleSum h
  rw [Finset.card_eq_sum_card_fiberwise
    (t := T.image s) (f := fun z : (Fin h → ℕ) × (Fin h → ℕ) ↦ s z.1) (by
      intro z hz
      change z ∈ (((orderedTuples h A).product (orderedTuples h A)).filter fun z ↦
        tupleSum h z.1 = tupleSum h z.2) at hz
      exact Finset.mem_image.mpr
        ⟨z.1, (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1, rfl⟩)]
  rw [hAddEnergy]
  apply Finset.sum_congr rfl
  intro a ha
  have hfiber :
      ((natEnergyPairs' h A).filter fun z ↦ s z.1 = a) =
        (T.filter fun u ↦ s u = a).product (T.filter fun v ↦ s v = a) := by
    ext z
    simp only [natEnergyPairs', Finset.mem_filter, Finset.mem_product, and_assoc, T, s]
    aesop
  rw [hfiber]
  simp [sumFiberCount, T, s, pow_two]

lemma nat_energy_pair_has_valuation_collision
    {h : ℕ} (hh : 0 < h) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (p : ℕ) (hp : p.Prime)
    {z : (Fin h → ℕ) × (Fin h → ℕ)} (hz : z ∈ natEnergyPairs' h A) :
    ∃ r s : Sum (Fin h) (Fin h), r ≠ s ∧
      (natPairValue' z r).factorization p = (natPairValue' z s).factorization p := by
  have hz' := Finset.mem_filter.mp hz
  have hzprod := Finset.mem_product.mp hz'.1
  have hzA₁ : ∀ i, z.1 i ∈ A := by
    have ht : z.1 ∈ Fintype.piFinset (fun _ : Fin h ↦ A) := by
      simpa [orderedTuples] using hzprod.1
    exact Fintype.mem_piFinset.mp ht
  have hzA₂ : ∀ i, z.2 i ∈ A := by
    have ht : z.2 ∈ Fintype.piFinset (fun _ : Fin h ↦ A) := by
      simpa [orderedTuples] using hzprod.2
    exact Fintype.mem_piFinset.mp ht
  have hsum : ∑ i, z.1 i = ∑ i, z.2 i := by
    simpa [tupleSum] using hz'.2
  obtain ⟨r, s, hrs, heq, hmin⟩ := prime_factorization_tuple_min_repeated
    hh z.1 z.2 (fun i ↦ hA _ (hzA₁ i)) (fun i ↦ hA _ (hzA₂ i)) p hp hsum
  exact ⟨r, s, hrs, heq⟩

lemma natPairValue_mem_of_mem_natEnergyPairs'
    {h : ℕ} {A : Finset ℕ}
    {z : (Fin h → ℕ) × (Fin h → ℕ)} (hz : z ∈ natEnergyPairs' h A)
    (r : Sum (Fin h) (Fin h)) : natPairValue' z r ∈ A := by
  have hz' := Finset.mem_filter.mp hz
  have hzprod := Finset.mem_product.mp hz'.1
  have hleft : ∀ i, z.1 i ∈ A := by
    have ht : z.1 ∈ Fintype.piFinset (fun _ : Fin h ↦ A) := by
      simpa [orderedTuples] using hzprod.1
    exact Fintype.mem_piFinset.mp ht
  have hright : ∀ i, z.2 i ∈ A := by
    have ht : z.2 ∈ Fintype.piFinset (fun _ : Fin h ↦ A) := by
      simpa [orderedTuples] using hzprod.2
    exact Fintype.mem_piFinset.mp ht
  rcases r with i | i
  · exact hleft i
  · exact hright i

/-- Refined cover: in addition to choosing the two repeated-minimum
positions, record their common prime exponent.  This form interfaces directly
with the single-cell mixed-energy inequality. -/
theorem card_natEnergyPairs_le_sum_valuationCollisionCellPairs
    {h : ℕ} (hh : 0 < h) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (p : ℕ) (hp : p.Prime) :
    (natEnergyPairs' h A).card ≤
      ∑ rs ∈ ((Finset.univ ×ˢ Finset.univ).filter fun rs :
          (Sum (Fin h) (Fin h)) × (Sum (Fin h) (Fin h)) ↦ rs.1 ≠ rs.2),
        ∑ e ∈ natValuationExponents' A p,
          (natValuationCollisionCellPairs' h A p e rs.1 rs.2).card := by
  let I := Sum (Fin h) (Fin h)
  let P : Finset (I × I) := (Finset.univ ×ˢ Finset.univ).filter fun rs ↦ rs.1 ≠ rs.2
  let J := natValuationExponents' A p
  let U := P.biUnion fun rs ↦ J.biUnion fun e ↦
    natValuationCollisionCellPairs' h A p e rs.1 rs.2
  have hsub : natEnergyPairs' h A ⊆ U := by
    intro z hz
    obtain ⟨r, s, hrs, heq⟩ := nat_energy_pair_has_valuation_collision hh A hA p hp hz
    let e := (natPairValue' z r).factorization p
    have heJ : e ∈ J := by
      exact Finset.mem_image.mpr
        ⟨natPairValue' z r, natPairValue_mem_of_mem_natEnergyPairs' hz r, rfl⟩
    change z ∈ P.biUnion fun rs ↦ J.biUnion fun e ↦
      natValuationCollisionCellPairs' h A p e rs.1 rs.2
    rw [Finset.mem_biUnion]
    refine ⟨(r, s), by simp [P, hrs], ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨e, heJ, Finset.mem_filter.mpr ⟨hz, rfl, heq.symm⟩⟩
  calc
    _ ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ rs ∈ P, (J.biUnion fun e ↦
          natValuationCollisionCellPairs' h A p e rs.1 rs.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ rs ∈ P, ∑ e ∈ J,
          (natValuationCollisionCellPairs' h A p e rs.1 rs.2).card := by
      apply Finset.sum_le_sum
      intro rs hrs
      exact Finset.card_biUnion_le
    _ = _ := by rfl

/-- Every ordered h-fold additive-energy solution has an off-diagonal pair
of coordinates with the same p-adic valuation. Therefore the energy-solution
set is covered by the corresponding collision classes. -/
theorem card_natEnergyPairs_le_sum_valuationCollisionPairs
    {h : ℕ} (hh : 0 < h) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (p : ℕ) (hp : p.Prime) :
    (natEnergyPairs' h A).card ≤
      ∑ rs ∈ ((Finset.univ ×ˢ Finset.univ).filter fun rs :
          (Sum (Fin h) (Fin h)) × (Sum (Fin h) (Fin h)) ↦ rs.1 ≠ rs.2),
        (natValuationCollisionPairs' h A p rs.1 rs.2).card := by
  let I := Sum (Fin h) (Fin h)
  let P : Finset (I × I) := (Finset.univ ×ˢ Finset.univ).filter fun rs ↦ rs.1 ≠ rs.2
  let U := P.biUnion fun rs ↦ natValuationCollisionPairs' h A p rs.1 rs.2
  have hsub : natEnergyPairs' h A ⊆ U := by
    intro z hz
    obtain ⟨r, s, hrs, heq⟩ := nat_energy_pair_has_valuation_collision hh A hA p hp hz
    change z ∈ P.biUnion fun rs ↦ natValuationCollisionPairs' h A p rs.1 rs.2
    rw [Finset.mem_biUnion]
    exact ⟨(r, s), by simp [P, hrs], Finset.mem_filter.mpr ⟨hz, heq⟩⟩
  calc
    _ ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ rs ∈ P, (natValuationCollisionPairs' h A p rs.1 rs.2).card :=
      Finset.card_biUnion_le
    _ = _ := by rfl

lemma card_offDiagPositionPairs_le (h : ℕ) :
    (((Finset.univ ×ˢ Finset.univ).filter fun rs :
        (Sum (Fin h) (Fin h)) × (Sum (Fin h) (Fin h)) ↦ rs.1 ≠ rs.2).card) ≤
      (2 * h) ^ 2 := by
  calc
    _ ≤ (Finset.univ ×ˢ (Finset.univ : Finset (Sum (Fin h) (Fin h)))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (2 * h) ^ 2 := by simp [pow_two]; ring

/-- A uniform bound for every off-diagonal collision class gives an
`(2h)^2`-multiple bound for all additive-energy solutions. -/
theorem card_natEnergyPairs_le_offDiag_mul
    {h : ℕ} (hh : 0 < h) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (p : ℕ) (hp : p.Prime) (Q : ℕ)
    (hQ : ∀ r s : Sum (Fin h) (Fin h), r ≠ s →
      (natValuationCollisionPairs' h A p r s).card ≤ Q) :
    (natEnergyPairs' h A).card ≤ (2 * h) ^ 2 * Q := by
  let P : Finset ((Sum (Fin h) (Fin h)) × (Sum (Fin h) (Fin h))) :=
    (Finset.univ ×ˢ Finset.univ).filter fun rs ↦ rs.1 ≠ rs.2
  calc
    _ ≤ ∑ rs ∈ P, (natValuationCollisionPairs' h A p rs.1 rs.2).card := by
      simpa [P] using card_natEnergyPairs_le_sum_valuationCollisionPairs hh A hA p hp
    _ ≤ ∑ _rs ∈ P, Q := by
      apply Finset.sum_le_sum
      intro rs hrs
      exact hQ rs.1 rs.2 (Finset.mem_filter.mp hrs).2
    _ = P.card * Q := by simp
    _ ≤ (2 * h) ^ 2 * Q := by
      gcongr
      simpa [P] using card_offDiagPositionPairs_le h

theorem hAddEnergy_le_offDiag_mul
    {h : ℕ} (hh : 0 < h) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (p : ℕ) (hp : p.Prime) (Q : ℕ)
    (hQ : ∀ r s : Sum (Fin h) (Fin h), r ≠ s →
      (natValuationCollisionPairs' h A p r s).card ≤ Q) :
    hAddEnergy h A ≤ (2 * h) ^ 2 * Q := by
  rw [← card_natEnergyPairs'_eq_hAddEnergy]
  exact card_natEnergyPairs_le_offDiag_mul hh A hA p hp Q hQ

/-- The one-prime root recurrence, reduced to the analytic estimate for a
single prescribed valuation cell and pair of positions.  This theorem is the
exact glue between `rawPairRestrictedEnergy_rpow_le` and the p-adic cover. -/
theorem hAddEnergy_root_le_of_valuation_cell_bounds
    {h : ℕ} (hh : 0 < h) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (p : ℕ) (hp : p.Prime)
    (hclass : ∀ e ∈ natValuationExponents' A p,
      ∀ r s : Sum (Fin h) (Fin h), r ≠ s →
        (↑(natValuationCollisionCellPairs' h A p e r s).card : NNReal) ≤
          (↑(hAddEnergy h (natValuationCell' A p e)) : NNReal) ^
              (1 / (h : ℝ)) *
            (↑(hAddEnergy h A) : NNReal) ^
              (((h : ℝ) - 1) / (h : ℝ))) :
    (↑(hAddEnergy h A) : NNReal) ^ (1 / (h : ℝ)) ≤
      ((↑(2 * h) : NNReal) ^ 2) *
        ∑ e ∈ natValuationExponents' A p,
          (↑(hAddEnergy h (natValuationCell' A p e)) : NNReal) ^
            (1 / (h : ℝ)) := by
  let I := Sum (Fin h) (Fin h)
  let P : Finset (I × I) := (Finset.univ ×ˢ Finset.univ).filter fun rs ↦ rs.1 ≠ rs.2
  let J := natValuationExponents' A p
  let E : NNReal := ↑(hAddEnergy h A)
  let Ec : ℕ → NNReal := fun e ↦ ↑(hAddEnergy h (natValuationCell' A p e))
  let R : (I × I) → ℕ → NNReal := fun rs e ↦
    ↑(natValuationCollisionCellPairs' h A p e rs.1 rs.2).card
  have hcover : E ≤ ∑ rs ∈ P, ∑ e ∈ J, R rs e := by
    dsimp [E, P, J, R]
    rw [← card_natEnergyPairs'_eq_hAddEnergy]
    exact_mod_cast
      card_natEnergyPairs_le_sum_valuationCollisionCellPairs hh A hA p hp
  have hR : ∀ rs ∈ P, ∀ e ∈ J,
      R rs e ≤ Ec e ^ (1 / (h : ℝ)) *
        E ^ (((h : ℝ) - 1) / (h : ℝ)) := by
    intro rs hrs e he
    exact hclass e he rs.1 rs.2 (Finset.mem_filter.mp hrs).2
  have H : E ≤ (P.card : NNReal) *
      (E ^ (((h : ℝ) - 1) / (h : ℝ)) *
        ∑ e ∈ J, Ec e ^ (1 / (h : ℝ))) := by
    calc
      E ≤ ∑ rs ∈ P, ∑ e ∈ J, R rs e := hcover
      _ ≤ ∑ _rs ∈ P, ∑ e ∈ J,
          Ec e ^ (1 / (h : ℝ)) *
            E ^ (((h : ℝ) - 1) / (h : ℝ)) := by
        apply Finset.sum_le_sum
        intro rs hrs
        exact Finset.sum_le_sum fun e he ↦ hR rs hrs e he
      _ = (P.card : NNReal) *
          (E ^ (((h : ℝ) - 1) / (h : ℝ)) *
            ∑ e ∈ J, Ec e ^ (1 / (h : ℝ))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        rw [mul_comm]
  have Hroot : E ^ (1 / (h : ℝ)) ≤
      (P.card : NNReal) * ∑ e ∈ J, Ec e ^ (1 / (h : ℝ)) := by
    by_cases hE : E = 0
    · rw [hE, NNReal.zero_rpow (by positivity : (1 / (h : ℝ)) ≠ 0)]
      exact bot_le
    have hexp : 1 / (h : ℝ) + ((h : ℝ) - 1) / (h : ℝ) = 1 := by
      field_simp
      ring
    have hsplit : E = E ^ (1 / (h : ℝ)) *
        E ^ (((h : ℝ) - 1) / (h : ℝ)) := by
      rw [← NNReal.rpow_add hE, hexp, NNReal.rpow_one]
    have H' : E ^ (1 / (h : ℝ)) * E ^ (((h : ℝ) - 1) / (h : ℝ)) ≤
        ((P.card : NNReal) * ∑ e ∈ J, Ec e ^ (1 / (h : ℝ))) *
          E ^ (((h : ℝ) - 1) / (h : ℝ)) := by
      calc
        _ = E := hsplit.symm
        _ ≤ _ := H
        _ = _ := by ring
    have hpos : 0 < E ^ (((h : ℝ) - 1) / (h : ℝ)) :=
      NNReal.rpow_pos (pos_iff_ne_zero.mpr hE)
    exact (mul_le_mul_iff_right₀ hpos).mp (by simpa [mul_comm] using H')
  refine Hroot.trans ?_
  change (P.card : NNReal) * _ ≤ _
  gcongr
  exact_mod_cast card_offDiagPositionPairs_le h

/-! ## Integrated checked module: E53CastBridge -/

open scoped BigOperators


noncomputable section

lemma natCast_zmod_injective_below' (N a b : ℕ) [NeZero N]
    (ha : a < N) (hb : b < N) :
    (a : ZMod N) = (b : ZMod N) ↔ a = b := by
  constructor
  · intro hab
    have hv := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv
  · exact congrArg Nat.cast

def natPositionValue {h : ℕ}
    (z : (Fin h → ℕ) × (Fin h → ℕ)) : Fin h ⊕ Fin h → ℕ :=
  Sum.elim z.1 z.2

private def castPositionValue
    (N h : ℕ) [NeZero N] (A B : Finset ℕ)
    (r s : Fin h ⊕ Fin h)
    (z : (Fin h → ℕ) × (Fin h → ℕ))
    (hzA : ∀ q, natPositionValue z q ∈ A)
    (hzB : natPositionValue z r ∈ B ∧ natPositionValue z s ∈ B)
    (q : Fin h ⊕ Fin h) :
    ↑(pairPositionSet
      (A.image fun a : ℕ ↦ (a : ZMod N))
      (B.image fun b : ℕ ↦ (b : ZMod N)) r s q) := by
  classical
  refine ⟨(natPositionValue z q : ZMod N), ?_⟩
  simp only [pairPositionSet]
  split_ifs with hq
  · apply Finset.mem_image.mpr
    refine ⟨natPositionValue z q, ?_, rfl⟩
    rcases hq with rfl | rfl
    · exact hzB.1
    · exact hzB.2
  · exact Finset.mem_image.mpr ⟨natPositionValue z q, hzA q, rfl⟩

private def castCollisionPair
    (N h : ℕ) [NeZero N] (A B : Finset ℕ)
    (r s : Fin h ⊕ Fin h)
    (z : (Fin h → ℕ) × (Fin h → ℕ))
    (hzA : ∀ q, natPositionValue z q ∈ A)
    (hzB : natPositionValue z r ∈ B ∧ natPositionValue z s ∈ B) :
    ((∀ i, ↑(pairPositionSet
        (A.image fun a : ℕ ↦ (a : ZMod N))
        (B.image fun b : ℕ ↦ (b : ZMod N)) r s (.inr i))) ×
      (∀ i, ↑(pairPositionSet
        (A.image fun a : ℕ ↦ (a : ZMod N))
        (B.image fun b : ℕ ↦ (b : ZMod N)) r s (.inl i)))) :=
  (fun i ↦ castPositionValue N h A B r s z hzA hzB (.inr i),
   fun i ↦ castPositionValue N h A B r s z hzA hzB (.inl i))

/-- A finite class of natural-number additive relations, with two prescribed
coordinates in `B`, injects into the corresponding arbitrary-position mixed
energy over `ZMod N`, provided reduction modulo `N` is injective on `A`. -/
theorem card_le_rawPairRestrictedEnergy_of_natCast
    (N h : ℕ) [NeZero N] (A B : Finset ℕ)
    (C : Finset ((Fin h → ℕ) × (Fin h → ℕ)))
    (r s : Fin h ⊕ Fin h)
    (hCA : ∀ z ∈ C, ∀ q, natPositionValue z q ∈ A)
    (hCB : ∀ z ∈ C,
      natPositionValue z r ∈ B ∧ natPositionValue z s ∈ B)
    (hCsum : ∀ z ∈ C, ∑ i, z.1 i = ∑ i, z.2 i)
    (M : ℕ) (hAM : ∀ a ∈ A, a ≤ M) (hMN : M < N) :
    C.card ≤ rawPairRestrictedEnergy h
      (A.image fun a : ℕ ↦ (a : ZMod N))
      (B.image fun b : ℕ ↦ (b : ZMod N)) r s := by
  classical
  let AZ : Finset (ZMod N) := A.image fun a : ℕ ↦ (a : ZMod N)
  let BZ : Finset (ZMod N) := B.image fun b : ℕ ↦ (b : ZMod N)
  let L : Fin h → Finset (ZMod N) :=
    fun i ↦ pairPositionSet AZ BZ r s (.inl i)
  let R : Fin h → Finset (ZMod N) :=
    fun i ↦ pairPositionSet AZ BZ r s (.inr i)
  let T : Finset ((∀ i, ↑(R i)) × (∀ i, ↑(L i))) :=
    Finset.univ.filter fun xy ↦
      familyTupleSum L xy.2 = familyTupleSum R xy.1
  let F : ↑C → ↑T := fun z ↦ by
    let hzA : ∀ q, natPositionValue z.1 q ∈ A := hCA z.1 z.2
    let hzB : natPositionValue z.1 r ∈ B ∧ natPositionValue z.1 s ∈ B :=
      hCB z.1 z.2
    let w := castCollisionPair N h A B r s z.1 hzA hzB
    have hw : w ∈ T := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (∑ i, ((z.1.1 i : ℕ) : ZMod N)) =
        ∑ i, ((z.1.2 i : ℕ) : ZMod N)
      simpa only [Nat.cast_sum] using
        congrArg (fun n : ℕ ↦ (n : ZMod N)) (hCsum z.1 z.2)
    exact ⟨w, hw⟩
  have hFinj : Function.Injective F := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hcast : (z.1.1 i : ZMod N) = (w.1.1 i : ZMod N) := by
        exact congrArg (fun x ↦ ((x.1.2 i : ↑(L i)) : ZMod N)) hzw
      apply (natCast_zmod_injective_below' N _ _ ?_ ?_).mp hcast
      · exact (hAM _ (hCA z.1 z.2 (.inl i))).trans_lt hMN
      · exact (hAM _ (hCA w.1 w.2 (.inl i))).trans_lt hMN
    · funext i
      have hcast : (z.1.2 i : ZMod N) = (w.1.2 i : ZMod N) := by
        exact congrArg (fun x ↦ ((x.1.1 i : ↑(R i)) : ZMod N)) hzw
      apply (natCast_zmod_injective_below' N _ _ ?_ ?_).mp hcast
      · exact (hAM _ (hCA z.1 z.2 (.inr i))).trans_lt hMN
      · exact (hAM _ (hCA w.1 w.2 (.inr i))).trans_lt hMN
  have hcard := Fintype.card_le_of_injective F hFinj
  simpa only [Fintype.card_coe, rawPairRestrictedEnergy, rawFamilyEnergy,
    AZ, BZ, L, R, T] using hcard

end

/-! ## Integrated checked module: E53CollisionBridge -/

noncomputable section

/-- A refined fixed-valuation collision class maps injectively into the
arbitrary-position mixed additive energy after reduction modulo a modulus
larger than every element of `A`.  The stronger `h * M < N` hypothesis is
the no-wrap assumption also used to identify the full energies. -/
theorem card_natValuationCollisionCellPairs_le_rawPairRestrictedEnergy
    (N h M : ℕ) [NeZero N] (A : Finset ℕ) (p e : ℕ)
    (r s : Fin h ⊕ Fin h) (hh : 0 < h)
    (hAM : ∀ a ∈ A, a ≤ M) (hNM : h * M < N) :
    (natValuationCollisionCellPairs' h A p e r s).card ≤
      rawPairRestrictedEnergy h
        (A.image fun a : ℕ ↦ (a : ZMod N))
        ((natValuationCell' A p e).image fun a : ℕ ↦ (a : ZMod N)) r s := by
  apply card_le_rawPairRestrictedEnergy_of_natCast N h A
    (natValuationCell' A p e)
    (natValuationCollisionCellPairs' h A p e r s) r s
  · intro z hz q
    have hzE : z ∈ natEnergyPairs' h A :=
      (Finset.mem_filter.mp hz).1
    simpa only [natPositionValue, natPairValue'] using
      natPairValue_mem_of_mem_natEnergyPairs' hzE q
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzE : z ∈ natEnergyPairs' h A := hz'.1
    refine ⟨Finset.mem_filter.mpr ⟨?_, hz'.2.1⟩,
      Finset.mem_filter.mpr ⟨?_, hz'.2.2⟩⟩
    · simpa only [natPositionValue, natPairValue'] using
        natPairValue_mem_of_mem_natEnergyPairs' hzE r
    · simpa only [natPositionValue, natPairValue'] using
        natPairValue_mem_of_mem_natEnergyPairs' hzE s
  · intro z hz
    have hzE : z ∈ natEnergyPairs' h A :=
      (Finset.mem_filter.mp hz).1
    simpa only [natEnergyPairs', Finset.mem_filter, tupleSum] using
      (Finset.mem_filter.mp hzE).2
  · exact hAM
  · exact (Nat.le_mul_of_pos_left M hh).trans_lt hNM

end

/-! ## Integrated checked module: E53Fourier -/

open scoped BigOperators ComplexConjugate NNReal


noncomputable section

open ZMod AddChar

lemma addChar_prod_eq_map_sum {G M ι : Type*} [AddCommMonoid G] [CommMonoid M]
    [Fintype ι] (e : AddChar G M) (f : ι → G) :
    ∏ i, e (f i) = e (∑ i, f i) := by
  change Additive.toMul (∑ i, e.toAddMonoidHom (f i)) = e (∑ i, f i)
  rw [← map_sum]
  rfl

def orderedNatTuples (h : ℕ) (A : Finset ℕ) : Finset (Fin h → ℕ) :=
  Fintype.piFinset fun _ : Fin h ↦ A

def natTupleSum (h : ℕ) (t : Fin h → ℕ) : ℕ := ∑ i, t i

def natTupleFiberCount (h : ℕ) (A : Finset ℕ) (z : ℕ) : ℕ :=
  ((orderedNatTuples h A).filter fun t ↦ natTupleSum h t = z).card

def natHAddEnergy (h : ℕ) (A : Finset ℕ) : ℕ :=
  ∑ z ∈ (orderedNatTuples h A).image (natTupleSum h),
    natTupleFiberCount h A z ^ 2

/-- The exponential sum attached to a finite set of natural-number frequencies. -/
def fourierPoly (N : ℕ) [NeZero N] (A : Finset ℕ) (x : ZMod N) : ℂ :=
  ∑ a ∈ A, stdAddChar ((a : ZMod N) * x)

def fourierPolyNeg (N : ℕ) [NeZero N] (A : Finset ℕ) (x : ZMod N) : ℂ :=
  ∑ a ∈ A, stdAddChar (-((a : ZMod N) * x))

lemma fourierPoly_pow (N h : ℕ) [NeZero N] (A : Finset ℕ) (x : ZMod N) :
    fourierPoly N A x ^ h =
      ∑ t ∈ orderedNatTuples h A,
        stdAddChar ((natTupleSum h t : ZMod N) * x) := by
  classical
  rw [fourierPoly, Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro t ht
  rw [addChar_prod_eq_map_sum]
  rw [← Finset.sum_mul]
  simp [natTupleSum]

lemma fourierPolyNeg_pow (N h : ℕ) [NeZero N] (A : Finset ℕ) (x : ZMod N) :
    fourierPolyNeg N A x ^ h =
      ∑ t ∈ orderedNatTuples h A,
        stdAddChar (-((natTupleSum h t : ZMod N) * x)) := by
  classical
  rw [fourierPolyNeg, Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro t ht
  rw [addChar_prod_eq_map_sum]
  congr 2
  simp [natTupleSum]
  rw [Finset.sum_mul]

lemma sum_stdAddChar_mul (N : ℕ) [NeZero N] (b : ZMod N) :
    ∑ x : ZMod N, stdAddChar (b * x) = if b = 0 then (N : ℂ) else 0 := by
  split_ifs with hb
  · simp [hb]
  · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N hb)

def modularEnergyPairs (N h : ℕ) [NeZero N] (A : Finset ℕ) :
    Finset ((Fin h → ℕ) × (Fin h → ℕ)) :=
  (orderedNatTuples h A ×ˢ orderedNatTuples h A).filter fun tu ↦
    (natTupleSum h tu.1 : ZMod N) = (natTupleSum h tu.2 : ZMod N)

def energyPairs (h : ℕ) (A : Finset ℕ) :
    Finset ((Fin h → ℕ) × (Fin h → ℕ)) :=
  (orderedNatTuples h A ×ˢ orderedNatTuples h A).filter fun tu ↦
    natTupleSum h tu.1 = natTupleSum h tu.2

lemma card_energyPairs (h : ℕ) (A : Finset ℕ) :
    (energyPairs h A).card = natHAddEnergy h A := by
  classical
  let T := orderedNatTuples h A
  let s := natTupleSum h
  rw [Finset.card_eq_sum_card_fiberwise
    (t := T.image s) (f := fun tu : (Fin h → ℕ) × (Fin h → ℕ) ↦ s tu.1) (by
      intro tu htu
      have htu' : tu ∈ energyPairs h A := htu
      rw [energyPairs, Finset.mem_filter] at htu'
      exact Finset.mem_image.mpr ⟨tu.1, (Finset.mem_product.mp htu'.1).1, rfl⟩)]
  rw [natHAddEnergy]
  apply Finset.sum_congr rfl
  intro z hz
  have hfiber :
      ((energyPairs h A).filter fun tu ↦ s tu.1 = z) =
        (T.filter fun t ↦ s t = z).product (T.filter fun u ↦ s u = z) := by
    ext tu
    simp only [energyPairs, Finset.mem_filter, Finset.mem_product, and_assoc, T, s]
    aesop
  rw [hfiber]
  calc
    ((T.filter fun t ↦ s t = z).product (T.filter fun t ↦ s t = z)).card =
        (T.filter fun t ↦ s t = z).card * (T.filter fun t ↦ s t = z).card :=
      Finset.card_product _ _
    _ = natTupleFiberCount h A z ^ 2 := by
      simp only [natTupleFiberCount, T, s]
      rw [pow_two]

lemma natTupleSum_lt (N h M : ℕ) (A : Finset ℕ) (t : Fin h → ℕ)
    (ht : t ∈ orderedNatTuples h A) (hAM : ∀ a ∈ A, a ≤ M)
    (hNM : h * M < N) :
    natTupleSum h t < N := by
  calc
    natTupleSum h t ≤ ∑ _i : Fin h, M := by
      apply Finset.sum_le_sum
      intro i hi
      exact hAM (t i) (Fintype.mem_piFinset.mp ht i)
    _ = h * M := by simp
    _ < N := hNM

lemma natCast_zmod_injective_below (N a b : ℕ) [NeZero N]
    (ha : a < N) (hb : b < N) :
    (a : ZMod N) = (b : ZMod N) ↔ a = b := by
  constructor
  · intro hab
    have hv := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv
  · exact congrArg Nat.cast

lemma modularEnergyPairs_eq_energyPairs (N h M : ℕ) [NeZero N]
    (A : Finset ℕ) (hAM : ∀ a ∈ A, a ≤ M) (hNM : h * M < N) :
    modularEnergyPairs N h A = energyPairs h A := by
  classical
  ext tu
  simp only [modularEnergyPairs, energyPairs, Finset.mem_filter]
  constructor
  · rintro ⟨htu, heq⟩
    have hpair := Finset.mem_product.mp htu
    refine ⟨htu, ?_⟩
    exact (natCast_zmod_injective_below N _ _
      (natTupleSum_lt N h M A tu.1 hpair.1 hAM hNM)
      (natTupleSum_lt N h M A tu.2 hpair.2 hAM hNM)).mp heq
  · rintro ⟨htu, heq⟩
    exact ⟨htu, congrArg Nat.cast heq⟩

def rawEvenMoment (N h : ℕ) [NeZero N] (A : Finset ℕ) : ℂ :=
  ∑ x : ZMod N, fourierPoly N A x ^ h * conj (fourierPoly N A x) ^ h

lemma conj_stdAddChar (N : ℕ) [NeZero N] (y : ZMod N) :
    conj (stdAddChar y) = stdAddChar (-y) := by
  exact (AddChar.map_neg_eq_conj (K := ℂ) (G := ZMod N)
    (stdAddChar (N := N)) y).symm

lemma fourierPolyNeg_eq_conj (N : ℕ) [NeZero N] (A : Finset ℕ) (x : ZMod N) :
    fourierPolyNeg N A x = conj (fourierPoly N A x) := by
  rw [fourierPolyNeg, fourierPoly, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact (conj_stdAddChar N _).symm

lemma conj_fourierPoly_pow (N h : ℕ) [NeZero N] (A : Finset ℕ) (x : ZMod N) :
    conj (fourierPoly N A x) ^ h =
      ∑ t ∈ orderedNatTuples h A,
        stdAddChar (-((natTupleSum h t : ZMod N) * x)) := by
  rw [← map_pow, fourierPoly_pow, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [conj_stdAddChar]

def fourierNNMoment (N h : ℕ) [NeZero N] (A : Finset ℕ) : ℝ≥0 :=
  ∑ x : ZMod N, ‖fourierPoly N A x‖₊ ^ (2 * h)

lemma coe_fourierNNMoment (N h : ℕ) [NeZero N] (A : Finset ℕ) :
    (((fourierNNMoment N h A : ℝ≥0) : ℝ) : ℂ) = rawEvenMoment N h A := by
  rw [fourierNNMoment, rawEvenMoment]
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  rw [← mul_pow, Complex.mul_conj']
  push_cast
  rw [← pow_mul]

theorem rawEvenMoment_eq_modularEnergyPairs (N h : ℕ) [NeZero N]
    (A : Finset ℕ) :
    rawEvenMoment N h A = (N : ℂ) * (modularEnergyPairs N h A).card := by
  classical
  let T := orderedNatTuples h A
  calc
    rawEvenMoment N h A =
        ∑ x : ZMod N, ∑ t ∈ T, ∑ u ∈ T,
          stdAddChar ((natTupleSum h t : ZMod N) * x) *
            stdAddChar (-((natTupleSum h u : ZMod N) * x)) := by
      rw [rawEvenMoment]
      simp_rw [fourierPoly_pow, conj_fourierPoly_pow, Finset.sum_mul, Finset.mul_sum]
      rfl
    _ = ∑ t ∈ T, ∑ u ∈ T, ∑ x : ZMod N,
          stdAddChar (((natTupleSum h t : ZMod N) -
            (natTupleSum h u : ZMod N)) * x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro x hx
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ t ∈ T, ∑ u ∈ T,
          if (natTupleSum h t : ZMod N) = (natTupleSum h u : ZMod N)
          then (N : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      rw [sum_stdAddChar_mul]
      simp only [sub_eq_zero]
    _ = (N : ℂ) * (modularEnergyPairs N h A).card := by
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.mul_sum]
      simp only [mul_one, modularEnergyPairs, Finset.sum_filter]
      rw [Finset.sum_product]

theorem rawEvenMoment_eq_energy (N h M : ℕ) [NeZero N]
    (A : Finset ℕ) (hAM : ∀ a ∈ A, a ≤ M) (hNM : h * M < N) :
    rawEvenMoment N h A = (N : ℂ) * natHAddEnergy h A := by
  rw [rawEvenMoment_eq_modularEnergyPairs,
    modularEnergyPairs_eq_energyPairs N h M A hAM hNM,
    card_energyPairs]

theorem fourierNNMoment_eq_energy (N h M : ℕ) [NeZero N]
    (A : Finset ℕ) (hAM : ∀ a ∈ A, a ≤ M) (hNM : h * M < N) :
    fourierNNMoment N h A = N * natHAddEnergy h A := by
  apply NNReal.eq
  have hc := coe_fourierNNMoment N h A
  rw [rawEvenMoment_eq_energy N h M A hAM hNM] at hc
  simpa using congrArg Complex.re hc


end

/-! ## Integrated checked module: E53RawEnergyBridge -/

noncomputable section

lemma natHAddEnergy_eq_hAddEnergy (h : ℕ) (A : Finset ℕ) :
    natHAddEnergy h A = hAddEnergy h A := by
  rfl

/-- Full no-wrap equality between the abstract finite-group energy of the
cast image and the natural additive energy used by the main development. -/
theorem rawHAddEnergy_natCastImage_eq
    (N h M : ℕ) [NeZero N] (A : Finset ℕ)
    (hAM : ∀ a ∈ A, a ≤ M) (hMN : M < N) (hNM : h * M < N) :
    rawHAddEnergy h (natCastImage N A) = hAddEnergy h A := by
  apply rawHAddEnergy_natCastImage_eq_of_moment N h A
  · intro a ha
    exact (hAM a ha).trans_lt hMN
  · have H := fourierNNMoment_eq_energy N h M A hAM hNM
    simpa only [fourierNNMoment, natFourierPoly, fourierPoly,
      natHAddEnergy_eq_hAddEnergy] using H

end

/-! ## Integrated checked module: E53OnePrimeFinal -/

open scoped BigOperators NNReal


noncomputable section

/-- Chang's one-prime lacunary root-energy recurrence for positive natural
frequencies.  All cyclic Fourier arguments are hidden behind a modulus
`h * (sum A) + 1`, so this statement is entirely about natural additive
energy and exact prime-factorization cells. -/
theorem one_prime_hAddEnergy_root
    (h : ℕ) (hh : 1 < h) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (p : ℕ) (hp : p.Prime) :
    (↑(hAddEnergy h A) : ℝ≥0) ^ (1 / (h : ℝ)) ≤
      ((↑(2 * h) : ℝ≥0) ^ 2) *
        ∑ e ∈ natValuationExponents' A p,
          (↑(hAddEnergy h (natValuationCell' A p e)) : ℝ≥0) ^
            (1 / (h : ℝ)) := by
  apply hAddEnergy_root_le_of_valuation_cell_bounds (by omega) A hA p hp
  intro e he r s hrs
  let M : ℕ := ∑ a ∈ A, a
  let N : ℕ := h * M + 1
  let _ : NeZero N := ⟨by simp [N]⟩
  have hAM : ∀ a ∈ A, a ≤ M := by
    intro a ha
    change a ≤ ∑ x ∈ A, x
    exact Finset.single_le_sum (s := A) (f := fun x : ℕ ↦ x)
      (fun _ _ ↦ Nat.zero_le _) ha
  have hMN : M < N := by
    exact (Nat.le_mul_of_pos_left M (by omega : 0 < h)).trans_lt
      (Nat.lt_succ_self (h * M))
  have hNM : h * M < N := Nat.lt_succ_self _
  let AZ : Finset (ZMod N) := A.image fun a : ℕ ↦ (a : ZMod N)
  let B := natValuationCell' A p e
  let BZ : Finset (ZMod N) := B.image fun b : ℕ ↦ (b : ZMod N)
  have hBM : ∀ b ∈ B, b ≤ M := by
    intro b hb
    exact hAM b (Finset.filter_subset _ _ hb)
  have hcardNat := card_natValuationCollisionCellPairs_le_rawPairRestrictedEnergy
    N h M A p e r s (by omega) hAM hNM
  have hcard :
      (↑(natValuationCollisionCellPairs' h A p e r s).card : ℝ≥0) ≤
        (↑(rawPairRestrictedEnergy h AZ BZ r s) : ℝ≥0) := by
    exact_mod_cast hcardNat
  have hmixed := rawPairRestrictedEnergy_rpow_le (G := ZMod N)
    h AZ BZ r s hrs hh
  calc
    (↑(natValuationCollisionCellPairs' h A p e r s).card : ℝ≥0) ≤
        (↑(rawPairRestrictedEnergy h AZ BZ r s) : ℝ≥0) := hcard
    _ ≤ (↑(rawHAddEnergy h BZ) : ℝ≥0) ^ (1 / (h : ℝ)) *
          (↑(rawHAddEnergy h AZ) : ℝ≥0) ^
            (((h : ℝ) - 1) / (h : ℝ)) := hmixed
    _ = (↑(hAddEnergy h B) : ℝ≥0) ^ (1 / (h : ℝ)) *
          (↑(hAddEnergy h A) : ℝ≥0) ^
            (((h : ℝ) - 1) / (h : ℝ)) := by
      rw [show rawHAddEnergy h BZ = hAddEnergy h B by
        simpa [BZ, natCastImage] using
          rawHAddEnergy_natCastImage_eq N h M B hBM hMN hNM]
      rw [show rawHAddEnergy h AZ = hAddEnergy h A by
        simpa [AZ, natCastImage] using
          rawHAddEnergy_natCastImage_eq N h M A hAM hMN hNM]

end

/-! ## Integrated checked module: E53Iterate -/

open scoped BigOperators NNReal


def coordinateCell {α δ β : Type*} [DecidableEq α] [DecidableEq β]
    (v : α → δ → β) (A : Finset α) (i : δ) (b : β) : Finset α :=
  A.filter fun a ↦ v a i = b

lemma coordinateCell_subset {α δ β : Type*} [DecidableEq α] [DecidableEq β]
    (v : α → δ → β) (A : Finset α) (i : δ) (b : β) :
    coordinateCell v A i b ⊆ A := by
  exact Finset.filter_subset _ _

def coordinateMap {α δ β : Type*} (v : α → δ → β)
    (l : List δ) (a : α) : Fin l.length → β :=
  fun k ↦ v a (l.get k)

@[simp] lemma coordinateMap_cons_zero {α δ β : Type*} (v : α → δ → β)
    (i : δ) (l : List δ) (a : α) :
    coordinateMap v (i :: l) a 0 = v a i := by
  rfl

@[simp] lemma coordinateMap_cons_succ {α δ β : Type*} (v : α → δ → β)
    (i : δ) (l : List δ) (a : α) (k : Fin l.length) :
    coordinateMap v (i :: l) a k.succ = coordinateMap v l a k := by
  rfl

lemma sum_card_coordinateCell {α δ β : Type*}
    [DecidableEq α] [DecidableEq β]
    (v : α → δ → β) (A : Finset α) (i : δ) :
    ∑ b ∈ A.image (fun a ↦ v a i), (coordinateCell v A i b).card = A.card := by
  simpa [coordinateCell] using
    (Finset.card_eq_sum_card_image (fun a ↦ v a i) A).symm

/-- Iterating a one-coordinate root-energy recurrence along a separating list
of coordinates.  The terminal hypothesis is only needed for cells of size at
most one.  The conclusion has no residual sum over cells. -/
theorem iterated_coordinate_recurrence
    {α δ β : Type*} [DecidableEq α] [DecidableEq β]
    (v : α → δ → β) (energyNorm : Finset α → ℝ≥0) (C : ℝ≥0)
    (hstep : ∀ (B : Finset α) (i : δ),
      energyNorm B ≤ C * ∑ b ∈ B.image (fun a ↦ v a i),
        energyNorm (coordinateCell v B i b))
    (hterminal : ∀ B : Finset α, B.card ≤ 1 →
      energyNorm B ≤ (B.card : ℝ≥0))
    (l : List δ) (A : Finset α)
    (hinj : Set.InjOn (coordinateMap v l) A) :
    energyNorm A ≤ C ^ l.length * (A.card : ℝ≥0) := by
  induction l generalizing A with
  | nil =>
      have hcard : A.card ≤ 1 := by
        rw [Finset.card_le_one_iff]
        intro a b ha hb
        exact hinj ha hb (by
          funext k
          exact Fin.elim0 k)
      simpa using hterminal A hcard
  | cons i l ih =>
      have hcellinj (b : β) (hb : b ∈ A.image fun a ↦ v a i) :
          Set.InjOn (coordinateMap v l) (coordinateCell v A i b) := by
        intro x hx y hy hxy
        have hxA : x ∈ A := coordinateCell_subset v A i b hx
        have hyA : y ∈ A := coordinateCell_subset v A i b hy
        apply hinj hxA hyA
        funext k
        refine Fin.cases ?_ (fun t ↦ ?_) k
        · exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
        · exact congrFun hxy t
      calc
        energyNorm A ≤ C * ∑ b ∈ A.image (fun a ↦ v a i),
            energyNorm (coordinateCell v A i b) := hstep A i
        _ ≤ C * ∑ b ∈ A.image (fun a ↦ v a i),
            C ^ l.length * ((coordinateCell v A i b).card : ℝ≥0) := by
          gcongr with b hb
          exact ih (coordinateCell v A i b) (hcellinj b hb)
        _ = C ^ (i :: l).length * (A.card : ℝ≥0) := by
          rw [← Finset.mul_sum]
          rw [← Nat.cast_sum]
          rw [sum_card_coordinateCell v A i]
          simp only [List.length_cons, pow_succ']
          ring

/-- If the selected coordinate list has length at most `d`, enlarge the
constant exponent to `d` (for constants at least one). -/
theorem iterated_coordinate_recurrence_le_dimension
    {α δ β : Type*} [DecidableEq α] [DecidableEq β]
    (v : α → δ → β) (energyNorm : Finset α → ℝ≥0) (C : ℝ≥0) (hC : 1 ≤ C)
    (hstep : ∀ (B : Finset α) (i : δ),
      energyNorm B ≤ C * ∑ b ∈ B.image (fun a ↦ v a i),
        energyNorm (coordinateCell v B i b))
    (hterminal : ∀ B : Finset α, B.card ≤ 1 →
      energyNorm B ≤ (B.card : ℝ≥0))
    (l : List δ) (A : Finset α) (d : ℕ) (hld : l.length ≤ d)
    (hinj : Set.InjOn (coordinateMap v l) A) :
    energyNorm A ≤ C ^ d * (A.card : ℝ≥0) := by
  exact (iterated_coordinate_recurrence v energyNorm C hstep hterminal l A hinj).trans (by
    gcongr)

/-! ## Integrated checked module: E53EnergyTerminal -/

open scoped BigOperators NNReal


lemma hAddEnergy_empty_of_pos (h : ℕ) (hh : 0 < h) :
    hAddEnergy h (∅ : Finset ℕ) = 0 := by
  have htuples : orderedTuples h (∅ : Finset ℕ) = ∅ := by
    classical
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hf' : f ∈ Fintype.piFinset (fun _ : Fin h ↦ (∅ : Finset ℕ)) := by
      simpa [orderedTuples] using hf
    have := Fintype.mem_piFinset.mp hf' ⟨0, hh⟩
    simpa using this
  simp [hAddEnergy, htuples]

lemma hAddEnergy_singleton (h a : ℕ) : hAddEnergy h ({a} : Finset ℕ) = 1 := by
  classical
  have htuples : orderedTuples h ({a} : Finset ℕ) = {fun _ ↦ a} := by
    ext f
    simp only [orderedTuples, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro hf
      apply funext
      exact hf
    · intro hf i
      exact congrFun hf i
  rw [hAddEnergy]
  simp only [htuples, Finset.image_singleton, Finset.sum_singleton, sumFiberCount,
    Finset.filter_singleton, if_pos rfl, Finset.card_singleton, one_pow]
  simp only [if_true, Finset.card_singleton, one_pow]

lemma hAddEnergy_root_le_card_of_card_le_one
    (h : ℕ) (hh : 0 < h) (B : Finset ℕ) (hB : B.card ≤ 1) :
    (↑(hAddEnergy h B) : NNReal) ^ (1 / (h : ℝ)) ≤ (B.card : NNReal) := by
  obtain rfl | ⟨b, hb⟩ := B.eq_empty_or_nonempty
  · rw [hAddEnergy_empty_of_pos h hh]
    simp [NNReal.zero_rpow (by positivity : (1 / (h : ℝ)) ≠ 0)] <;> omega
  have hsingle : B = {b} := by
    ext x
    constructor
    · intro hx
      have hxb : x = b := Finset.card_le_one_iff.mp hB hx hb
      simpa [hxb]
    · intro hxb
      have hxb' : x = b := Finset.mem_singleton.mp hxb
      subst x
      exact hb
  subst B
  simp [hAddEnergy_singleton]

/-! ## Integrated checked module: E53PrimeSeparator -/

open scoped BigOperators


noncomputable section

/-- A positive finite set of naturals is separated by prime-factorization
coordinates whose number is at most the rank of its exponent-vector span.
Nonprime coordinates returned by the abstract coordinate-separator theorem
are discarded because every factorization vanishes there. -/
theorem exists_prime_factorization_separator
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    ∃ P : Finset ℕ,
      P.card ≤ Module.finrank ℚ
        (Submodule.span ℚ (A.image exponentVector : Set (ℕ →₀ ℚ))) ∧
      (∀ p ∈ P, p.Prime) ∧
      Set.InjOn (fun a : ℕ ↦ fun p : P ↦ a.factorization p) A := by
  classical
  let W := Submodule.span ℚ (A.image exponentVector : Set (ℕ →₀ ℚ))
  obtain ⟨s, hs_card, hs_inj⟩ := exists_finset_coord_restrict_injective (R := ℚ) W
  let P := s.filter Nat.Prime
  refine ⟨P, (Finset.card_filter_le _ _).trans hs_card, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro a ha b hb hab
    apply exponentVector_injectiveOn_pos (hA a ha) (hA b hb)
    let xa : W := ⟨exponentVector a, Submodule.subset_span (by
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩))⟩
    let xb : W := ⟨exponentVector b, Submodule.subset_span (by
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, hb, rfl⟩))⟩
    have hx : xa = xb := by
      apply hs_inj
      funext i
      by_cases hip : i.1.Prime
      · have hiP : i.1 ∈ P := Finset.mem_filter.mpr ⟨i.2, hip⟩
        have heq := congrFun hab ⟨i.1, hiP⟩
        simpa [xa, xb, exponentVector_apply] using heq
      · simp [xa, xb, exponentVector_apply,
          Nat.factorization_eq_zero_of_not_prime _ hip]
    exact congrArg Subtype.val hx

end

/-! ## Integrated checked module: E53RankFinalGeneric -/

open scoped BigOperators NNReal


noncomputable section

/-- Chang's complete low-rank additive-energy estimate. -/
theorem hAddEnergy_le_rank_bound
    (h : ℕ) (hh : 1 < h) (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    hAddEnergy h A ≤ ((2 * h) ^ 2) ^
        (Module.finrank ℚ
          (Submodule.span ℚ (A.image exponentVector : Set (ℕ →₀ ℚ))) * h) *
      A.card ^ h := by
  let d := Module.finrank ℚ
    (Submodule.span ℚ (A.image exponentVector : Set (ℕ →₀ ℚ)))
  obtain ⟨P, hPd, hPprime, hsep⟩ := exists_prime_factorization_separator A hA
  let v : ℕ → P → ℕ := fun a p ↦ a.factorization p.1
  let l : List P := (Finset.univ : Finset P).toList
  let C : ℝ≥0 := (↑(2 * h) : ℝ≥0) ^ 2
  let energyNorm : Finset ℕ → ℝ≥0 := fun B ↦
    if ∀ b ∈ B, 0 < b then
      (↑(hAddEnergy h B) : ℝ≥0) ^ (1 / (h : ℝ)) else 0
  have hC : 1 ≤ C := by
    dsimp [C]
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ 2 * h by omega))
  have hstep : ∀ (B : Finset ℕ) (q : P),
      energyNorm B ≤ C * ∑ e ∈ B.image (fun b ↦ v b q),
        energyNorm (coordinateCell v B q e) := by
    intro B q
    by_cases hB : ∀ b ∈ B, 0 < b
    · have H := one_prime_hAddEnergy_root h hh B hB q.1 (hPprime q.1 q.2)
      dsimp only [energyNorm, v, coordinateCell]
      rw [if_pos hB]
      rw [show C = (↑(2 * h) : ℝ≥0) ^ 2 by rfl]
      have H' :
          (↑(hAddEnergy h B) : ℝ≥0) ^ (1 / (h : ℝ)) ≤
            (↑(2 * h) : ℝ≥0) ^ 2 *
              ∑ e ∈ B.image (fun b ↦ b.factorization q.1),
                (↑(hAddEnergy h (B.filter fun b ↦ b.factorization q.1 = e)) : ℝ≥0) ^
                  (1 / (h : ℝ)) := by
        simpa only [natValuationExponents', natValuationCell'] using H
      apply H'.trans_eq
      congr 1
      apply Finset.sum_congr rfl
      intro e he
      rw [if_pos]
      intro b hb
      exact hB b (Finset.filter_subset _ _ hb)
    · dsimp only [energyNorm]
      rw [if_neg hB]
      exact bot_le
  have hterminal : ∀ B : Finset ℕ, B.card ≤ 1 →
      energyNorm B ≤ (B.card : ℝ≥0) := by
    intro B hcard
    by_cases hB : ∀ b ∈ B, 0 < b
    · dsimp only [energyNorm]
      rw [if_pos hB]
      exact hAddEnergy_root_le_card_of_card_le_one h (by omega) B hcard
    · dsimp only [energyNorm]
      rw [if_neg hB]
      exact bot_le
  have hinj : Set.InjOn (coordinateMap v l) A := by
    intro a ha b hb hab
    apply hsep ha hb
    funext q
    have hq : q ∈ l := by simp [l]
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hq
    have heq := congrFun hab k
    change v a (l.get k) = v b (l.get k) at heq
    rw [hk] at heq
    exact heq
  have hld : l.length ≤ d := by
    simpa [l, d] using hPd
  have Hroot := iterated_coordinate_recurrence_le_dimension
    v energyNorm C hC hstep hterminal l A d hld hinj
  have Hroot' :
      (↑(hAddEnergy h A) : ℝ≥0) ^ (1 / (h : ℝ)) ≤
        C ^ d * (A.card : ℝ≥0) := by
    dsimp only [energyNorm] at Hroot
    rw [if_pos hA] at Hroot
    exact Hroot
  have Hp := NNReal.rpow_le_rpow Hroot' (show (0 : ℝ) ≤ h by positivity)
  have hinv : (1 / (h : ℝ)) * h = 1 := by field_simp
  have Hnn :
      (↑(hAddEnergy h A) : ℝ≥0) ≤
        (C ^ d) ^ h * ((A.card : ℕ) : ℝ≥0) ^ h := by
    rw [← NNReal.rpow_mul, hinv, NNReal.rpow_one, NNReal.mul_rpow,
      NNReal.rpow_natCast, NNReal.rpow_natCast] at Hp
    exact Hp
  have Hnat : hAddEnergy h A ≤ (((2 * h) ^ 2) ^ d) ^ h * A.card ^ h := by
    dsimp [C] at Hnn
    exact_mod_cast Hnn
  rw [← pow_mul] at Hnat
  simpa [d] using Hnat

end

/-- The fixed-power resolution for finite sets of positive natural numbers. -/
theorem positive_natural_resolution :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a) → N ≤ A.card →
        A.card ^ k ≤ (natSumProdValues A).card := by
  exact positive_natural_resolution_of_rank_tools
    hAddEnergy_le_rank_bound high_rank_block_box

/-- Resolution of Erdős Problem 53: for every fixed power `k`, every
sufficiently large finite set of integers has at least `|A|^k` distinct
integers which occur as a subset sum or a subset product of distinct members
of `A`. -/
theorem erdos_53 :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ,
      N ≤ A.card → A.card ^ k ≤ (sumProdValues A).card := by
  exact integer_resolution_of_positive_naturals positive_natural_resolution

#print axioms erdos_53

end

end Erdos53

alias _root_.Erdos53.erdos53 := _root_.Erdos53.erdos_53
