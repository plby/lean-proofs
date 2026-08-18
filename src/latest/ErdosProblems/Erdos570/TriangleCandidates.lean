/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleJensen
import ErdosProblems.Erdos570.TriangleExtension

/-!
# Candidate-set double counting for the triangle case

For every vertex outside a fixed blue clique, its neighbours in the clique
form a finite set.  This file records the exact incidence double count between
common-neighbour candidate sets of `δ`-subsets and binomial coefficients of
the corresponding cross-degrees.
-/

open scoped BigOperators

noncomputable section

namespace Erdos570

/-- The elements of `Y` which belong to every set indexed by `I`. -/
def commonCandidates {T Y : Type*} [DecidableEq T] [Fintype Y]
    [DecidableEq Y]
    (N : T → Finset Y) (I : Finset T) : Finset Y :=
  Finset.univ.filter fun y ↦ ∀ x ∈ I, y ∈ N x

theorem mem_commonCandidates {T Y : Type*} [DecidableEq T] [Fintype Y]
    [DecidableEq Y]
    {N : T → Finset Y} {I : Finset T} {y : Y} :
    y ∈ commonCandidates N I ↔ ∀ x ∈ I, y ∈ N x := by
  simp [commonCandidates]

theorem commonCandidates_subset {T Y : Type*} [DecidableEq T] [Fintype Y]
    [DecidableEq Y]
    (N : T → Finset Y) (I : Finset T) :
    commonCandidates N I ⊆ Finset.univ := by
  exact Finset.subset_univ _

theorem card_commonCandidates_le {T Y : Type*} [DecidableEq T] [Fintype Y]
    [DecidableEq Y]
    (N : T → Finset Y) (I : Finset T) :
    (commonCandidates N I).card ≤ Fintype.card Y := by
  simpa using Finset.card_le_card (commonCandidates_subset N I)

theorem card_commonCandidates_le_of_mem
    {T Y : Type*} [DecidableEq T] [Fintype Y] [DecidableEq Y]
    (N : T → Finset Y) (I : Finset T) {x : T} (hx : x ∈ I) :
    (commonCandidates N I).card ≤ (N x).card := by
  apply Finset.card_le_card
  intro y hy
  exact (mem_commonCandidates.mp hy) x hx

/-- Two subsets of a finite universe, each of size `G`, have intersection
of size at least `2G-|Y|`.  This is the floor used in the degree-two
triangle argument. -/
theorem card_commonCandidates_pair_lower
    {T Y : Type*} [DecidableEq T] [Fintype Y] [DecidableEq Y]
    (N : T → Finset Y) {I : Finset T} {G : ℕ}
    (hI : I.card = 2) (hcard : ∀ x, (N x).card = G) :
    2 * G - Fintype.card Y ≤ (commonCandidates N I).card := by
  classical
  obtain ⟨x, z, hxz, rfl⟩ := Finset.card_eq_two.mp hI
  have hcommon : commonCandidates N {x, z} = N x ∩ N z := by
    ext w
    simp [commonCandidates]
  rw [hcommon]
  have hunion : (N x ∪ N z).card ≤ Fintype.card Y := by
    simpa using Finset.card_le_card (Finset.subset_univ (N x ∪ N z))
  have hinc := Finset.card_union_add_card_inter (N x) (N z)
  rw [hcard x, hcard z] at hinc
  omega

/-- Exact double count of pairs `(I,y)` such that all indices in `I`
contain `y`. -/
theorem sum_card_commonCandidates
    {T Y : Type*} [Fintype T] [DecidableEq T] [Fintype Y] [DecidableEq Y]
    (N : T → Finset Y) (δ : ℕ) :
    ∑ I ∈ (Finset.univ : Finset T).powersetCard δ,
        (commonCandidates N I).card =
      ∑ y : Y, ((Finset.univ.filter fun x : T ↦ y ∈ N x).card).choose δ := by
  classical
  calc
    ∑ I ∈ (Finset.univ : Finset T).powersetCard δ,
        (commonCandidates N I).card =
        ∑ I ∈ (Finset.univ : Finset T).powersetCard δ,
          ∑ y : Y, if ∀ x ∈ I, y ∈ N x then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro I hI
            rw [Finset.card_eq_sum_ite
              (Finset.subset_univ (commonCandidates N I))]
            apply Finset.sum_congr rfl
            intro y hy
            simp [mem_commonCandidates]
    _ = ∑ y : Y,
        ∑ I ∈ (Finset.univ : Finset T).powersetCard δ,
          if ∀ x ∈ I, y ∈ N x then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ y : Y,
        (((Finset.univ : Finset T).powersetCard δ).filter
          (fun I ↦ ∀ x ∈ I, y ∈ N x)).card := by
            apply Finset.sum_congr rfl
            intro y hy
            exact Finset.sum_boole (R := ℕ)
              (fun I : Finset T ↦ ∀ x ∈ I, y ∈ N x)
              ((Finset.univ : Finset T).powersetCard δ)
    _ = ∑ y : Y,
        ((Finset.univ.filter fun x : T ↦ y ∈ N x).card).choose δ := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [← Finset.card_powersetCard]
            congr 1
            ext I
            simp only [Finset.mem_filter, Finset.mem_powersetCard,
              Finset.subset_univ, true_and]
            constructor
            · rintro ⟨hcard, hmem⟩
              refine ⟨?_, hcard⟩
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hmem x hx
            · rintro ⟨hsub, hcard⟩
              refine ⟨hcard, ?_⟩
              intro x hx
              exact (Finset.mem_filter.mp (hsub hx)).2

/-- Subtype-indexed form of `sum_card_commonCandidates`. -/
theorem sum_card_commonCandidates_subtype
    {T Y : Type*} [Fintype T] [DecidableEq T] [Fintype Y] [DecidableEq Y]
    (N : T → Finset Y) (δ : ℕ) :
    ∑ I : ↑((Finset.univ : Finset T).powersetCard δ),
        (commonCandidates N I.1).card =
      ∑ y : Y, ((Finset.univ.filter fun x : T ↦ y ∈ N x).card).choose δ := by
  let P := (Finset.univ : Finset T).powersetCard δ
  calc
    ∑ I : P, (commonCandidates N I.1).card =
        ∑ I ∈ P.attach, (commonCandidates N I.1).card := by
          rw [← Finset.univ_eq_attach P]
    _ = ∑ I ∈ P, (commonCandidates N I).card :=
      Finset.sum_attach P (fun I ↦ (commonCandidates N I).card)
    _ = _ := sum_card_commonCandidates N δ

/-- The sum of the degrees into `Y` equals the sum, over `Y`, of the
corresponding reverse degrees. -/
theorem sum_cross_degrees
    {T Y : Type*} [Fintype T] [DecidableEq T] [Fintype Y] [DecidableEq Y]
    (N : T → Finset Y) :
    ∑ x : T, (N x).card =
      ∑ y : Y, (Finset.univ.filter fun x : T ↦ y ∈ N x).card := by
  classical
  calc
    ∑ x : T, (N x).card =
        ∑ x : T, ∑ y : Y, if y ∈ N x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.card_eq_sum_ite (Finset.subset_univ (N x))]
    _ = ∑ y : Y, ∑ x : T, if y ∈ N x then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ y : Y,
        (Finset.univ.filter fun x : T ↦ y ∈ N x).card := by
          apply Finset.sum_congr rfl
          intro y hy
          exact Finset.sum_boole (R := ℕ)
            (fun x : T ↦ y ∈ N x) (Finset.univ : Finset T)

end Erdos570
