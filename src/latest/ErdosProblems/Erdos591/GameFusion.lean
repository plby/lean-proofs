import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.WellFounded

/-!
# Countable fusion for the positive relation in Erdős problem 591

These lemmas supply the pseudointersections used in the conservative-game
uniformization argument of `tex/591.tex`. No partition relation is assumed
here. In particular, this infrastructure does not assert the positive
endpoint theorem.
-/

namespace Erdos591.Positive.Game

open Set

/-- Inclusion modulo a finite exceptional set. -/
def AlmostSubset (s t : Set ℕ) : Prop := (s \ t).Finite

theorem AlmostSubset.refl (s : Set ℕ) : AlmostSubset s s := by
  simp [AlmostSubset]

theorem AlmostSubset.of_subset {s t : Set ℕ} (h : s ⊆ t) :
    AlmostSubset s t := by
  simp [AlmostSubset, Set.sdiff_eq_empty.mpr h]

theorem AlmostSubset.trans {s t u : Set ℕ}
    (hst : AlmostSubset s t) (htu : AlmostSubset t u) : AlmostSubset s u := by
  apply (hst.union htu).subset
  intro x hx
  by_cases hxt : x ∈ t
  · exact Or.inr ⟨hxt, hx.2⟩
  · exact Or.inl ⟨hx.1, hxt⟩

/-- The elementary diagonal construction, with an exact ambient-set
restriction in addition to the eventual restrictions. -/
theorem pseudointersection_nat {N : Set ℕ} (s : ℕ → Set ℕ)
    (h : ∀ n, {x | x ∈ N ∧ ∀ i ≤ n, x ∈ s i}.Infinite) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∀ i, AlmostSubset H (s i) := by
  choose pick hmem hgt using fun n a => (h n).exists_gt a
  let f : ℕ → ℕ := Nat.rec (pick 0 0) (fun n prev => pick (n + 1) prev)
  have hfmem (n : ℕ) : f n ∈ N ∧ ∀ i ≤ n, f n ∈ s i := by
    cases n with
    | zero => exact hmem 0 0
    | succ n => exact hmem (n + 1) (f n)
  have hfmono : StrictMono f := strictMono_nat_of_lt_succ fun n => hgt (n + 1) (f n)
  refine ⟨Set.range f, ?_, Set.infinite_range_of_injective hfmono.injective, ?_⟩
  · rintro x ⟨n, rfl⟩
    exact (hfmem n).1
  · intro i
    apply ((Set.finite_lt_nat i).image f).subset
    rintro x ⟨⟨n, rfl⟩, hx⟩
    refine ⟨n, ?_, rfl⟩
    exact lt_of_not_ge fun hin => hx ((hfmem n).2 i hin)

/-- A countable family with the infinite finite-intersection property has
an infinite pseudointersection. The index type may be empty. -/
theorem pseudointersection_countable {I : Type*} [Countable I]
    {N : Set ℕ} (s : I → Set ℕ)
    (h : ∀ F : Finset I, {x | x ∈ N ∧ ∀ i ∈ F, x ∈ s i}.Infinite) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∀ i, AlmostSubset H (s i) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hi =>
      refine ⟨N, Set.Subset.rfl, ?_, fun i => isEmptyElim i⟩
      simpa using h ∅
  | inr hi =>
      obtain ⟨e, he⟩ := exists_surjective_nat I
      have hseq (n : ℕ) :
          {x | x ∈ N ∧ ∀ i ≤ n, x ∈ s (e i)}.Infinite := by
        have hn := h ((Finset.range (n + 1)).image e)
        apply hn.mono
        intro x hx
        refine ⟨hx.1, fun i hin => hx.2 (e i) ?_⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
      obtain ⟨H, hHN, hH, hs⟩ := pseudointersection_nat (fun n => s (e n)) hseq
      refine ⟨H, hHN, hH, ?_⟩
      intro i
      obtain ⟨n, rfl⟩ := he i
      exact hs n

theorem AlmostSubset.finset_inter {I : Type*} (F : Finset I)
    {s : Set ℕ} {t : I → Set ℕ} (h : ∀ i ∈ F, AlmostSubset s (t i)) :
    AlmostSubset s {x | ∀ i ∈ F, x ∈ t i} := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [AlmostSubset]
  | @insert i F hi ih =>
      have hs := h i (Finset.mem_insert_self i F)
      have hF := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      apply (hs.union hF).subset
      intro x hx
      by_cases hxi : x ∈ t i
      · refine Or.inr ⟨hx.1, ?_⟩
        intro hxF
        apply hx.2
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hxi
        · exact hxF j hj
      · exact Or.inl ⟨hx.1, hxi⟩

/-- Countably many infinite, almost-decreasing sets can be fused even
when their indexing well-order has limit points. -/
theorem pseudointersection_chain {I : Type*} [Countable I] [LinearOrder I]
    {N : Set ℕ} (hN : N.Infinite) (s : I → Set ℕ)
    (hinf : ∀ i, (s i).Infinite) (hsub : ∀ i, s i ⊆ N)
    (hchain : ∀ i j, i ≤ j → AlmostSubset (s j) (s i)) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∀ i, AlmostSubset H (s i) := by
  classical
  apply pseudointersection_countable s
  intro F
  by_cases hF : F.Nonempty
  · let j := F.max' hF
    have hf : AlmostSubset (s j) {x | ∀ i ∈ F, x ∈ s i} :=
      AlmostSubset.finset_inter F fun i hi => hchain i j (Finset.le_max' F i hi)
    apply ((hinf j).inter_of_finite_sdiff hf).mono
    intro x hx
    exact ⟨hsub j hx.1, hx.2⟩
  · have hFe : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simpa [hFe] using hN

/-- An almost inclusion becomes exact above a finite numerical bound. -/
theorem AlmostSubset.exists_tail_bound {H M : Set ℕ} (h : AlmostSubset H M) :
    ∃ b : ℕ, ∀ x ∈ H, b < x → x ∈ M := by
  classical
  let b := h.toFinset.sup id
  refine ⟨b, ?_⟩
  intro x hx hbx
  by_contra hxm
  have hxfin : x ∈ h.toFinset := h.mem_toFinset.mpr ⟨hx, hxm⟩
  exact (not_le_of_gt hbx) (Finset.le_sup (f := id) hxfin)

/-- A set of possible fresh inputs, retaining its infinitude and the
original ambient-set restriction. -/
structure InfinitePool (N : Set ℕ) where
  carrier : Set ℕ
  subset : carrier ⊆ N
  infinite : carrier.Infinite

/-- The unconditional version used to define a recursive step before
its almost-decreasing invariant has been proved. The conclusion is only
conditional on that invariant; it is established below for the actual
recursion. -/
theorem exists_lower_pool {I : Type*} [Countable I] [LinearOrder I]
    {N : Set ℕ} (hN : N.Infinite) (s : I → InfinitePool N) :
    ∃ L : InfinitePool N,
      (∀ i j, i ≤ j → AlmostSubset (s j).carrier (s i).carrier) →
      ∀ i, AlmostSubset L.carrier (s i).carrier := by
  classical
  by_cases hc : ∀ i j, i ≤ j → AlmostSubset (s j).carrier (s i).carrier
  · obtain ⟨H, hHN, hH, hs⟩ := pseudointersection_chain hN
      (fun i => (s i).carrier) (fun i => (s i).infinite)
      (fun i => (s i).subset) hc
    exact ⟨⟨H, hHN, hH⟩, fun _ => hs⟩
  · exact ⟨⟨N, Set.Subset.rfl, hN⟩, fun h => (hc h).elim⟩

/-- Fusion along a countable well-order. Each step can inspect all
earlier Boolean values and can thin any infinite input pool. The
resulting pools are almost decreasing and all the step properties hold
for one coherent family of values.

`P` is an arbitrary local property, not a partition-relation hypothesis.
For game uniformization its builder clause is supplied by the proved
Nash--Williams theorem, and its other clauses make no thinning.
-/
theorem fusion_recursion {I : Type*} [Countable I] [LinearOrder I]
    [WellFoundedLT I] {N : Set ℕ} (hN : N.Infinite)
    (P : ∀ p : I, (∀ q : I, q < p → Bool) → Set ℕ → Bool → Prop)
    (hstep : ∀ p prev M, M ⊆ N → M.Infinite →
      ∃ L b, L ⊆ M ∧ L.Infinite ∧ P p prev L b) :
    ∃ (v : I → Bool) (s : I → Set ℕ),
      (∀ p, s p ⊆ N ∧ (s p).Infinite ∧ P p (fun q _ => v q) (s p) (v p)) ∧
      (∀ p q, p ≤ q → AlmostSubset (s q) (s p)) := by
  classical
  let Cell := InfinitePool N × Bool
  have make (p : I) (past : ∀ q, q < p → Cell) :
      ∃ c : Cell,
        P p (fun q hq => (past q hq).2) c.1.carrier c.2 ∧
        ((∀ q r (hq : q < p) (hr : r < p), q ≤ r →
          AlmostSubset (past r hr).1.carrier (past q hq).1.carrier) →
          ∀ q (hq : q < p), AlmostSubset c.1.carrier (past q hq).1.carrier) := by
    obtain ⟨M, hM⟩ := exists_lower_pool hN
      (fun q : Set.Iio p => (past q.val q.property).1)
    obtain ⟨L, b, hLM, hL, hb⟩ :=
      hstep p (fun q hq => (past q hq).2) M.carrier M.subset M.infinite
    refine ⟨(⟨L, hLM.trans M.subset, hL⟩, b), hb, ?_⟩
    intro hc q hq
    apply (AlmostSubset.of_subset hLM).trans
    exact hM (fun i j hij => hc i.val j.val i.property j.property hij) ⟨q, hq⟩
  let F (p : I) (past : ∀ q, q < p → Cell) : Cell := (make p past).choose
  let f : I → Cell := wellFounded_lt.fix F
  have hf (p : I) : f p = F p (fun q _ => f q) :=
    WellFounded.fix_eq wellFounded_lt F p
  have hchain (p : I) : ∀ q, q < p →
      AlmostSubset (f p).1.carrier (f q).1.carrier := by
    apply WellFoundedLT.induction p
    intro p ih q hq
    have hspec := (make p (fun r _ => f r)).choose_spec
    have hc : ∀ r t (_hr : r < p) (_ht : t < p), r ≤ t →
        AlmostSubset (f t).1.carrier (f r).1.carrier := by
      intro r t hr ht hrt
      rcases hrt.eq_or_lt with heq | hlt
      · subst t
        exact AlmostSubset.refl _
      · exact ih t ht r hlt
    rw [hf p]
    exact hspec.2 hc q hq
  refine ⟨fun p => (f p).2, fun p => (f p).1.carrier, ?_, ?_⟩
  · intro p
    refine ⟨(f p).1.subset, (f p).1.infinite, ?_⟩
    have hspec := (make p (fun q _ => f q)).choose_spec.1
    change P p (fun q _ => (f q).2) (f p).1.carrier (f p).2
    conv_rhs => rw [hf p]
    rw [hf p]
    exact hspec
  · intro p q hpq
    rcases hpq.eq_or_lt with heq | hlt
    · subst q
      exact AlmostSubset.refl _
    · exact hchain q p hlt

end Erdos591.Positive.Game
