import ErdosProblems.Erdos121.Weighted
import ErdosProblems.Erdos121.Four

/-!
# Erdős Problem 121: core definitions and finite extraction

For `k N : ℕ`, let `extremalSize k N` be the largest cardinality of a
subset of `{1, ..., N}` containing no `k` distinct elements whose product is
a square.  Tao proved that, for every fixed `k ≥ 4`, this extremal size is at
most `(1 - cₖ)N` for some `cₖ > 0` and all sufficiently large `N`.

The detailed mathematical proof and the correspondence with the declarations
in this development are recorded in `tex/121.tex`.
-/

open Filter
open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

/-- A finite set has square product. -/
def HasSquareProduct (S : Finset ℕ) : Prop :=
  IsSquare (S.prod id)

/-- `A` is admissible for Erdős Problem 121 at parameters `k, N`: it lies in
`{1, ..., N}` and no `k`-element subset of it has square product. -/
def IsAdmissible (k N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ S : Finset ℕ, S ⊆ A → S.card = k → ¬ HasSquareProduct S

/-- Cardinality `m` is attained by an admissible set at parameters `k, N`. -/
def Attainable (k N m : ℕ) : Prop :=
  ∃ A : Finset ℕ, IsAdmissible k N A ∧ A.card = m

/-- The exact extremal function `F_k(N)` from Erdős Problem 121. -/
noncomputable def extremalSize (k N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Attainable k N) N

theorem admissible_empty {k : ℕ} (hk : 0 < k) (N : ℕ) :
    IsAdmissible k N (∅ : Finset ℕ) := by
  refine ⟨by simp, ?_⟩
  intro S hS hcard
  have hEmpty : S = ∅ := Finset.subset_empty.mp hS
  subst S
  simp at hcard
  omega

theorem attainable_zero {k : ℕ} (hk : 0 < k) (N : ℕ) : Attainable k N 0 :=
  ⟨∅, admissible_empty hk N, by simp⟩

theorem admissible_card_le {k N : ℕ} {A : Finset ℕ}
    (hA : IsAdmissible k N A) : A.card ≤ N := by
  have hcard := Finset.card_le_card hA.1
  simpa using hcard

theorem attainable_le {k N m : ℕ} (hm : Attainable k N m) : m ≤ N := by
  obtain ⟨A, hA, rfl⟩ := hm
  exact admissible_card_le hA

theorem extremalSize_le (k N : ℕ) : extremalSize k N ≤ N := by
  classical
  unfold extremalSize
  exact Nat.findGreatest_le N

theorem attainable_extremalSize {k : ℕ} (hk : 0 < k) (N : ℕ) :
    Attainable k N (extremalSize k N) := by
  classical
  unfold extremalSize
  exact Nat.findGreatest_spec (P := Attainable k N) (m := 0)
    (Nat.zero_le N) (attainable_zero hk N)

theorem card_le_extremalSize {k N : ℕ} {A : Finset ℕ}
    (hA : IsAdmissible k N A) : A.card ≤ extremalSize k N := by
  classical
  unfold extremalSize
  exact Nat.le_findGreatest (attainable_le ⟨A, hA, rfl⟩) ⟨A, hA, rfl⟩

theorem exists_extremizer {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∃ A : Finset ℕ, IsAdmissible k N A ∧ A.card = extremalSize k N :=
  attainable_extremalSize hk N

/-- The finite dense-set conclusion used to state Tao's construction without
mentioning the extremal maximum. -/
def DenseSquareTupleBound (k : ℕ) (c : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N →
      (1 - c) * (N : ℝ) < (A.card : ℝ) →
        ∃ S : Finset ℕ,
          S ⊆ A ∧ S.card = k ∧ HasSquareProduct S

/-- A dense-set theorem bounds the exact maximum `F_k(N)`.  This is the
deterministic final step of Tao's argument. -/
theorem extremal_bound_of_denseSquareTupleBound {k : ℕ} (hk : 0 < k)
    {c : ℝ} (h : DenseSquareTupleBound k c) :
    ∀ᶠ N : ℕ in atTop,
      (extremalSize k N : ℝ) ≤ (1 - c) * (N : ℝ) := by
  filter_upwards [h] with N hN
  obtain ⟨A, hA, hcard⟩ := exists_extremizer hk N
  rw [← hcard]
  apply le_of_not_gt
  intro hlarge
  obtain ⟨S, hSA, hSk, hSq⟩ := hN A hA.1 hlarge
  exact hA.2 S hSA hSk hSq

/-- The four-element case, obtained from the squarefree upper bound already
formalized for Erdős Problem 888. -/
theorem denseSquareTupleBound_four : DenseSquareTupleBound 4 (1 / 100) := by
  classical
  filter_upwards [eventually_squarefree_count_ge,
    eventually_squarefreeExtremalSize_le_tenth, eventually_gt_atTop 0]
      with N hSquarefreeCount hExtremal hNpos
  intro A hA hlarge
  let U : Finset ℕ := Finset.Icc 1 N
  let Q : Finset ℕ := U.filter Squarefree
  let B : Finset ℕ := A.filter Squarefree
  by_contra hnone
  have hNoFour : ∀ S : Finset ℕ, S ⊆ B → S.card = 4 →
      ¬ IsSquare (S.prod id) := by
    intro S hSB hcard hSquare
    apply hnone
    refine ⟨S, ?_, hcard, hSquare⟩
    exact hSB.trans (Finset.filter_subset _ _)
  have hA_Ioc : A ⊆ Finset.Ioc 0 N := by
    intro a ha
    have ha' := Finset.mem_Icc.mp (hA ha)
    exact Finset.mem_Ioc.mpr ⟨by omega, ha'.2⟩
  have hB_Ioc : B ⊆ Finset.Ioc 0 N :=
    (Finset.filter_subset _ _).trans hA_Ioc
  have hBsf : ∀ b ∈ B, Squarefree b := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  have hRequired : Erdos888.RequiredCondition B N :=
    requiredCondition_of_squarefree_of_no_four hB_Ioc hBsf hNoFour
  have hBupperNat : B.card ≤ Erdos888.squarefreeExtremalSize N :=
    Erdos888.card_le_squarefreeExtremalSize hRequired hBsf
  have hBupper : (B.card : ℝ) ≤ (1 / 10 : ℝ) * N :=
    (Nat.cast_le.mpr hBupperNat).trans hExtremal
  have hQcover : Q ⊆ B ∪ (U \ A) := by
    intro x hx
    have hxQ := Finset.mem_filter.mp hx
    by_cases hxA : x ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxA, hxQ.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxQ.1, hxA⟩)
  have hQcardNat : Q.card ≤ B.card + (U \ A).card := by
    exact (Finset.card_le_card hQcover).trans (Finset.card_union_le _ _)
  have hQcard : (Q.card : ℝ) ≤ B.card + (U \ A).card := by
    exact_mod_cast hQcardNat
  have hUcard : U.card = N := by simp [U]
  have hcomp : ((U \ A).card : ℝ) = (N : ℝ) - A.card := by
    rw [Finset.cast_card_sdiff hA, hUcard]
  have hcompSmall : ((U \ A).card : ℝ) < (1 / 100 : ℝ) * N := by
    rw [hcomp]
    linarith
  have hQlower : (1 / 5 : ℝ) * N ≤ (Q.card : ℝ) := by
    simpa [Q, U] using hSquarefreeCount
  have hBlower : (19 / 100 : ℝ) * N < (B.card : ℝ) := by
    linarith
  have hNposReal : (0 : ℝ) < N := by exact_mod_cast hNpos
  nlinarith

/-- Finite weighted extraction of a square-product set.  This is the exact
union-bound step used after Tao's construction estimates. -/
theorem exists_squareProduct_of_weightedTuple
    {Ω : Type*} {k : ℕ} (W : FiniteWeight Ω)
    (x : Ω → Fin k → ℕ) (Good : Ω → Prop)
    (hSquare : ∀ ω ∈ W.support, Good ω → IsSquare (∏ i, x ω i))
    (A : Finset ℕ)
    (hmore :
      W.mass (fun ω => ¬ Function.Injective (x ω)) +
          ∑ i, W.mass (fun ω => Good ω ∧ x ω i ∉ A) <
        W.mass Good) :
    ∃ S : Finset ℕ, S ⊆ A ∧ S.card = k ∧ HasSquareProduct S := by
  classical
  let Collision : Ω → Prop := fun ω => ¬ Function.Injective (x ω)
  let Outside : Ω → Prop := fun ω => ∃ i : Fin k, Good ω ∧ x ω i ∉ A
  let Failure : Ω → Prop := fun ω => Collision ω ∨ Outside ω
  have hOutside : W.mass Outside ≤ ∑ i, W.mass (fun ω => Good ω ∧ x ω i ∉ A) := by
    simpa [Outside] using
      (FiniteWeight.mass_biUnion_le W (Finset.univ : Finset (Fin k))
        (fun i ω => Good ω ∧ x ω i ∉ A))
  have hFailure : W.mass Failure < W.mass Good := by
    have hUnion : W.mass Failure ≤ W.mass Collision + W.mass Outside := by
      exact FiniteWeight.mass_or_le W Collision Outside
    have hbound :
        W.mass Failure ≤ W.mass Collision +
          ∑ i, W.mass (fun ω => Good ω ∧ x ω i ∉ A) :=
      hUnion.trans (add_le_add (le_refl _) hOutside)
    exact hbound.trans_lt (by simpa [Collision] using hmore)
  obtain ⟨ω, hω, hGood, hnotFailure⟩ :=
    FiniteWeight.exists_good_not_failure hFailure
  have hinj : Function.Injective (x ω) := by
    simpa [Failure, Collision] using fun h => hnotFailure (Or.inl h)
  have hmem : ∀ i, x ω i ∈ A := by
    intro i
    by_contra hi
    exact hnotFailure (Or.inr ⟨i, hGood, hi⟩)
  let S : Finset ℕ := Finset.univ.image (x ω)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, _hi, rfl⟩
    exact hmem i
  · simp [S, Finset.card_image_of_injective, hinj]
  · have hprod : S.prod id = ∏ i, x ω i := by
      unfold S
      rw [Finset.prod_image hinj.injOn]
      simp
    unfold HasSquareProduct
    rw [hprod]
    exact hSquare ω hω hGood

end Erdos121
