/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Basic

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- Finite sums from a tail, with the empty sum allowed. -/
def finiteTailSums {G : Type*} [AddCommMonoid G] (A : Set ℕ) (f : ℕ → G) (N : ℕ) : Set G :=
  {x | ∃ F : Finset ℕ, (∀ a ∈ F, a ∈ A ∧ N ≤ a) ∧ ∑ a ∈ F, f a = x}

def tailLimitSet {G : Type*} [AddCommMonoid G] [TopologicalSpace G]
    (A : Set ℕ) (f : ℕ → G) : Set G := ⋂ N, closure (finiteTailSums A f N)

lemma zero_mem_tailLimitSet {G : Type*} [AddCommMonoid G] [TopologicalSpace G]
    (A : Set ℕ) (f : ℕ → G) : 0 ∈ tailLimitSet A f := by
  apply Set.mem_iInter.mpr
  intro N
  exact subset_closure ⟨∅, by simp, by simp⟩

lemma isClosed_tailLimitSet {G : Type*} [AddCommMonoid G] [TopologicalSpace G]
    (A : Set ℕ) (f : ℕ → G) : IsClosed (tailLimitSet A f) :=
  isClosed_iInter fun _ ↦ isClosed_closure

/-- Bergelson–Simmons, Claim 2.13: the common tail limit set is closed under addition. -/
lemma add_mem_tailLimitSet {G : Type*} [NormedAddCommGroup G]
    {A : Set ℕ} {f : ℕ → G} {x y : G}
    (hx : x ∈ tailLimitSet A f) (hy : y ∈ tailLimitSet A f) :
    x + y ∈ tailLimitSet A f := by
  apply Set.mem_iInter.mpr
  intro N
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨u, ⟨F, hF, rfl⟩, hu⟩ :=
    Metric.mem_closure_iff.mp (Set.mem_iInter.mp hx N) (ε / 2) (by positivity)
  obtain ⟨v, ⟨K, hK, rfl⟩, hv⟩ :=
    Metric.mem_closure_iff.mp (Set.mem_iInter.mp hy (max N (F.sup id + 1)))
      (ε / 2) (by positivity)
  have hdisj : Disjoint F K := by
    apply Finset.disjoint_left.mpr
    intro a haF haK
    have hle : a ≤ F.sup id := Finset.le_sup (f := id) haF
    have hge := (hK a haK).2
    omega
  refine ⟨(∑ a ∈ F, f a) + ∑ a ∈ K, f a, ?_, ?_⟩
  · refine ⟨F ∪ K, ?_, Finset.sum_union hdisj⟩
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hF a ha
    · exact ⟨(hK a ha).1, (le_max_left _ _).trans (hK a ha).2⟩
  · have hd := dist_add_add_le x y (∑ a ∈ F, f a) (∑ a ∈ K, f a)
    linarith

/-- A compact additive submonoid of a normed group is closed under negation. -/
lemma neg_mem_of_compact_add_closed {G : Type*} [NormedAddCommGroup G]
    {S : Set G} (hS : IsCompact S) (hzero : (0 : G) ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) {x : G} (hx : x ∈ S) : -x ∈ S := by
  have hn : ∀ n : ℕ, n • x ∈ S := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih => simpa only [add_nsmul, one_nsmul] using hadd (n • x) ih x hx
  obtain ⟨y, _, k, hk, hlim⟩ := hS.isSeqCompact hn
  have hshift : Tendsto (fun n ↦ k (n + 1) • x) atTop (𝓝 y) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun n ↦ k (n + 1) • x - k n • x - x) atTop (𝓝 (-x)) := by
    simpa only [Function.comp_def, sub_self, zero_sub] using
      (hshift.sub hlim).sub tendsto_const_nhds
  apply hS.isClosed.mem_of_tendsto hdiff
  apply Filter.Eventually.of_forall
  intro n
  have hle : k n + 1 ≤ k (n + 1) := hk (Nat.lt_succ_self n)
  have heq : (k (n + 1) - (k n + 1)) • x = k (n + 1) • x - k n • x - x := by
    have hsum : (k (n + 1) - (k n + 1)) • x + (k n + 1) • x = k (n + 1) • x := by
      rw [← add_nsmul, Nat.sub_add_cancel hle]
    rw [add_nsmul, one_nsmul] at hsum
    exact eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq.mpr
      (by simpa only [add_assoc, add_left_comm, add_comm] using hsum))
  rw [← heq]
  exact hn _

/-- The compact subgroup of the torus used by Bergelson and Simmons.
The construction works in every compact normed additive commutative group. -/
def tailSubgroup {G : Type*} [NormedAddCommGroup G] [CompactSpace G]
    (A : Set ℕ) (f : ℕ → G) : AddSubgroup G where
  carrier := tailLimitSet A f
  zero_mem' := zero_mem_tailLimitSet A f
  add_mem' := add_mem_tailLimitSet
  neg_mem' := neg_mem_of_compact_add_closed (isClosed_tailLimitSet A f).isCompact
    (zero_mem_tailLimitSet A f) (fun _ hx _ hy ↦ add_mem_tailLimitSet hx hy)

lemma finiteTailSums_antitone {G : Type*} [AddCommMonoid G]
    (A : Set ℕ) (f : ℕ → G) : Antitone (finiteTailSums A f) := by
  intro N M hNM x hx
  rcases hx with ⟨F, hF, rfl⟩
  exact ⟨F, fun a ha ↦ ⟨(hF a ha).1, hNM.trans (hF a ha).2⟩, rfl⟩

/-- Every open neighborhood of the common tail limit set contains one entire tail. -/
lemma exists_tail_subset_of_open {G : Type*} [NormedAddCommGroup G] [CompactSpace G]
    (A : Set ℕ) (f : ℕ → G) {U : Set G} (hU : IsOpen U)
    (hsub : tailLimitSet A f ⊆ U) : ∃ N, closure (finiteTailSums A f N) ⊆ U := by
  have hanti : Antitone (fun N ↦ closure (finiteTailSums A f N)) :=
    fun _ _ h ↦ closure_mono (finiteTailSums_antitone A f h)
  have hinter : (Uᶜ ∩ ⋂ N, closure (finiteTailSums A f N)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hlim⟩
    exact hx (hsub hlim)
  have hdir : Directed (· ⊇ ·) (fun N ↦ closure (finiteTailSums A f N)) := by
    intro i j
    exact ⟨max i j, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩
  obtain ⟨N, hN⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun N ↦ closure (finiteTailSums A f N)) (fun _ ↦ isClosed_closure) hinter hdir
  refine ⟨N, ?_⟩
  intro x hx
  by_contra hnot
  have hmem : x ∈ Uᶜ ∩ closure (finiteTailSums A f N) := ⟨hnot, hx⟩
  rw [hN] at hmem
  exact hmem

end Erdos254
