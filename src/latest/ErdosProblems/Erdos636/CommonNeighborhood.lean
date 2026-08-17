import ErdosProblems.Erdos636.External.Erdos88.Richness

/-!
# Counting bad ordered tuples

This file isolates the counting induction used in the common-neighbourhood
lemma for Erdős problem 636. `Good q x` says that the ordered `q`-tuple `x`
has a sufficiently large common neighbourhood. The only graph-theoretic
input needed by the induction is that every good prefix has at most `r`
extensions which cease to be good.
-/

namespace Erdos636

open scoped BigOperators

universe u

section AbstractCounting

variable {V : Type u} [Fintype V] [DecidableEq V]

private lemma card_filter_eq_sum_indicator {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The ordered `q`-tuples which fail a level-dependent predicate. -/
noncomputable def badOrderedTuples (Good : ∀ q : ℕ, (Fin q → V) → Prop) (q : ℕ) :
    Finset (Fin q → V) := by
  classical
  exact Finset.univ.filter fun x ↦ ¬ Good q x

@[simp] lemma mem_badOrderedTuples
    {Good : ∀ q : ℕ, (Fin q → V) → Prop} {q : ℕ} {x : Fin q → V} :
    x ∈ badOrderedTuples Good q ↔ ¬ Good q x := by
  classical
  simp [badOrderedTuples]

/-- The bad one-coordinate extensions of an ordered prefix. -/
noncomputable def badExtensions
    (Good : ∀ q : ℕ, (Fin q → V) → Prop) {q : ℕ} (x : Fin q → V) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ ¬ Good (q + 1) (Fin.cons v x)

@[simp] lemma mem_badExtensions
    {Good : ∀ q : ℕ, (Fin q → V) → Prop} {q : ℕ} {x : Fin q → V} {v : V} :
    v ∈ badExtensions Good x ↔ ¬ Good (q + 1) (Fin.cons v x) := by
  classical
  simp [badExtensions]

/-- Splitting an ordered tuple into its first coordinate and its tail turns
the number of bad tuples at the next level into the corresponding iterated
sum. -/
lemma card_badOrderedTuples_succ_eq_sum
    (Good : ∀ q : ℕ, (Fin q → V) → Prop) (q : ℕ) :
    (badOrderedTuples Good (q + 1)).card =
      ∑ x : Fin q → V, (badExtensions Good x).card := by
  classical
  calc
    (badOrderedTuples Good (q + 1)).card =
        ∑ z : Fin (q + 1) → V,
          if ¬ Good (q + 1) z then 1 else 0 := by
      simpa only [badOrderedTuples] using
        card_filter_eq_sum_indicator Finset.univ
          (fun z : Fin (q + 1) → V ↦ ¬ Good (q + 1) z)
    _ = ∑ x : Fin q → V, ∑ v : V,
          if ¬ Good (q + 1) (Fin.cons v x) then 1 else 0 := by
      rw [← (Fin.consEquiv (fun _ : Fin (q + 1) ↦ V)).sum_comp]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    _ = ∑ x : Fin q → V, (badExtensions Good x).card := by
      apply Finset.sum_congr rfl
      intro x _hx
      simpa only [badExtensions] using
        (card_filter_eq_sum_indicator Finset.univ
          (fun v : V ↦ ¬ Good (q + 1) (Fin.cons v x))).symm

/-- One step of the ordered-tuple induction. Bad prefixes have at most all
`|V|` possible extensions, while good prefixes have at most `r` bad
extensions by hypothesis. -/
lemma card_badOrderedTuples_succ_le
    (Good : ∀ q : ℕ, (Fin q → V) → Prop) (q r : ℕ)
    (hext : ∀ x : Fin q → V, Good q x →
      (badExtensions Good x).card ≤ r) :
    (badOrderedTuples Good (q + 1)).card ≤
      Fintype.card V * (badOrderedTuples Good q).card +
        (Fintype.card V) ^ q * r := by
  classical
  rw [card_badOrderedTuples_succ_eq_sum]
  calc
    (∑ x : Fin q → V, (badExtensions Good x).card) ≤
        ∑ x : Fin q → V,
          ((if ¬ Good q x then 1 else 0) * Fintype.card V + r) := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hx : Good q x
      · simp only [hx, not_true_eq_false, if_false, zero_mul, zero_add]
        exact hext x hx
      · simp only [hx, not_false_eq_true, if_true, one_mul]
        exact (Finset.card_le_univ (badExtensions Good x)).trans
          (Nat.le_add_right _ _)
    _ = Fintype.card V * (badOrderedTuples Good q).card +
          (Fintype.card V) ^ q * r := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      have hbad : (∑ x : Fin q → V, if ¬ Good q x then 1 else 0) =
          (badOrderedTuples Good q).card := by
        simpa only [badOrderedTuples] using
          (card_filter_eq_sum_indicator Finset.univ
            (fun x : Fin q → V ↦ ¬ Good q x)).symm
      rw [hbad]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Nat.nsmul_eq_mul]
      ring

/-- Abstract common-neighbourhood counting lemma.

Assume the empty tuple is good and, at every level below `k`, every good
prefix has at most `r` bad one-coordinate extensions. Then at most
`k * |V|^(k-1) * r` ordered `k`-tuples are bad. This is the exact coarse
bound used in the Kwan--Sudakov common-neighbourhood induction. -/
theorem card_badOrderedTuples_le
    (Good : ∀ q : ℕ, (Fin q → V) → Prop) (k r : ℕ)
    (hk : 1 ≤ k)
    (hroot : ∀ x : Fin 0 → V, Good 0 x)
    (hext : ∀ q : ℕ, q < k → ∀ x : Fin q → V, Good q x →
      (badExtensions Good x).card ≤ r) :
    (badOrderedTuples Good k).card ≤
      k * (Fintype.card V) ^ (k - 1) * r := by
  induction k using Nat.case_strong_induction_on with
  | hz => omega
  | hi k ih =>
      by_cases hk0 : k = 0
      · subst k
        have hstep := card_badOrderedTuples_succ_le Good 0 r (hext 0 (by omega))
        have hempty : (badOrderedTuples Good 0).card = 0 := by
          apply Finset.card_eq_zero.mpr
          ext x
          simp [hroot x]
        simpa [hempty] using hstep
      · have hkpos : 1 ≤ k := by omega
        have hprev : (badOrderedTuples Good k).card ≤
            k * (Fintype.card V) ^ (k - 1) * r :=
          ih k (by omega) hkpos
            (fun q hq x hx ↦ hext q (lt_trans hq (by omega)) x hx)
        have hstep := card_badOrderedTuples_succ_le Good k r
          (hext k (by omega))
        calc
          (badOrderedTuples Good (k + 1)).card ≤
              Fintype.card V * (badOrderedTuples Good k).card +
                Fintype.card V ^ k * r := hstep
          _ ≤ Fintype.card V *
                (k * Fintype.card V ^ (k - 1) * r) +
                Fintype.card V ^ k * r := by gcongr
          _ = (k + 1) * Fintype.card V ^ ((k + 1) - 1) * r := by
            have hpow : Fintype.card V ^ k =
                Fintype.card V * Fintype.card V ^ (k - 1) := by
              calc
                Fintype.card V ^ k =
                    Fintype.card V ^ ((k - 1) + 1) := by
                  congr 1
                  omega
                _ = Fintype.card V ^ (k - 1) * Fintype.card V := pow_succ _ _
                _ = Fintype.card V * Fintype.card V ^ (k - 1) :=
                  Nat.mul_comm _ _
            simp only [Nat.add_sub_cancel]
            rw [hpow]
            ring

end AbstractCounting

section GraphCommonNeighborhood

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The common neighbourhood of an ordered tuple. Repeated coordinates are
allowed, as is appropriate for the intermediate ordered-tuple count. -/
noncomputable def commonNeighbors (G : SimpleGraph V) {q : ℕ}
    (x : Fin q → V) : Finset V := by
  classical
  exact Finset.univ.filter fun w ↦ ∀ i, G.Adj (x i) w

@[simp] lemma mem_commonNeighbors {G : SimpleGraph V} {q : ℕ}
    {x : Fin q → V} {w : V} :
    w ∈ commonNeighbors G x ↔ ∀ i, G.Adj (x i) w := by
  simp [commonNeighbors]

@[simp] lemma commonNeighbors_zero (G : SimpleGraph V) (x : Fin 0 → V) :
    commonNeighbors G x = Finset.univ := by
  ext w
  simp [commonNeighbors]

/-- Adding a first coordinate intersects the old common neighbourhood with
the neighbourhood of that coordinate. -/
lemma commonNeighbors_cons (G : SimpleGraph V) {q : ℕ} (v : V)
    (x : Fin q → V) :
    commonNeighbors G (Fin.cons v x) =
      Erdos88.neighborsIn G v (commonNeighbors G x) := by
  ext w
  simp only [mem_commonNeighbors, Erdos88.mem_neighborsIn]
  constructor
  · intro h
    exact ⟨fun i ↦ by simpa using h i.succ, by simpa using h 0⟩
  · rintro ⟨hx, hv⟩ i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hv
    · simpa using hx j

/-- A level-dependent lower bound on the size of a tuple's common
neighbourhood. -/
def HasLargeCommonNeighborhood (G : SimpleGraph V) (threshold : ℕ → ℕ)
    (q : ℕ) (x : Fin q → V) : Prop :=
  threshold q ≤ (commonNeighbors G x).card

/-- Graph-facing form of the ordered common-neighbourhood count.

The hypothesis `hext` is precisely the portion of corrected richness used
in this argument: whenever the prefix common neighbourhood is large enough,
at most `r` vertices have too few neighbours in it to meet the next
threshold. No dense-exception alternative is needed for this one-sided
lemma, although corrected richness controls the union and hence implies this
hypothesis. -/
theorem card_orderedTuples_small_commonNeighbors_le
    (G : SimpleGraph V) (threshold : ℕ → ℕ) (k r : ℕ)
    (hk : 1 ≤ k)
    (hroot : threshold 0 ≤ Fintype.card V)
    (hext : ∀ q : ℕ, q < k → ∀ x : Fin q → V,
      threshold q ≤ (commonNeighbors G x).card →
      (Finset.univ.filter fun v : V ↦
        (Erdos88.neighborsIn G v (commonNeighbors G x)).card <
          threshold (q + 1)).card ≤ r) :
    (Finset.univ.filter fun x : Fin k → V ↦
      (commonNeighbors G x).card < threshold k).card ≤
        k * (Fintype.card V) ^ (k - 1) * r := by
  classical
  let Good : ∀ q : ℕ, (Fin q → V) → Prop :=
    fun q x ↦ HasLargeCommonNeighborhood G threshold q x
  have hroot' : ∀ x : Fin 0 → V, Good 0 x := by
    intro x
    simpa [Good, HasLargeCommonNeighborhood] using hroot
  have hext' : ∀ q : ℕ, q < k → ∀ x : Fin q → V, Good q x →
      (badExtensions Good x).card ≤ r := by
    intro q hq x hx
    simpa only [badExtensions, Good, HasLargeCommonNeighborhood,
      commonNeighbors_cons, Nat.not_le] using hext q hq x hx
  simpa only [badOrderedTuples, Good, HasLargeCommonNeighborhood,
    Nat.not_le] using card_badOrderedTuples_le Good k r hk hroot' hext'

end GraphCommonNeighborhood

end Erdos636
