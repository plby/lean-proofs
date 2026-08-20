import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Order

/-!
# Edge-colouring regular finite bipartite multigraphs

For some arguments around Erdős Problem 182 it is useful to keep parallel
edges.  A bipartite multigraph is therefore represented by a finite type of
edges together with its two endpoint maps.  This file proves the regular case
of Kőnig's line-colouring theorem: a finite `D`-regular bipartite multigraph
decomposes into `D` perfect matchings.
-/

open scoped Classical

namespace Erdos182

/-- A bipartite multigraph with labelled edges.  Parallel edges are distinct
elements of `E` having the same two endpoints. -/
structure BipartiteMultigraph (L R E : Type*) where
  left : E → L
  right : E → R

namespace BipartiteMultigraph

variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]

/-- Every vertex on either side has exactly `D` incident labelled edges. -/
def IsRegular (G : BipartiteMultigraph L R E) (D : ℕ) : Prop :=
  (∀ l, Fintype.card {e : E // G.left e = l} = D) ∧
    ∀ r, Fintype.card {e : E // G.right e = r} = D

/-- A proper `D`-edge-colouring, stated in the form needed by its consumers:
the colours are injective on every endpoint fibre. -/
structure ProperColoring (G : BipartiteMultigraph L R E) (D : ℕ) where
  color : E → Fin D
  left_injective : ∀ l, Function.Injective
    (fun e : {e : E // G.left e = l} ↦ color e.1)
  right_injective : ∀ r, Function.Injective
    (fun e : {e : E // G.right e = r} ↦ color e.1)

private lemma card_edges_eq_card_left_mul (G : BipartiteMultigraph L R E)
    {D : ℕ} (hreg : G.IsRegular D) : Fintype.card E = Fintype.card L * D := by
  classical
  calc
    Fintype.card E = ∑ l : L,
        (Finset.univ.filter fun e ↦ G.left e = l).card := by
      change Finset.univ.card = _
      exact Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ) (t := Finset.univ) (f := G.left) (by simp)
    _ = ∑ _l : L, D := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Fintype.card_of_subtype (p := fun e : E ↦ G.left e = l)
        (Finset.univ.filter fun e ↦ G.left e = l) (by simp)]
      exact hreg.1 l
    _ = Fintype.card L * D := by simp

private lemma card_edges_eq_card_right_mul (G : BipartiteMultigraph L R E)
    {D : ℕ} (hreg : G.IsRegular D) : Fintype.card E = Fintype.card R * D := by
  classical
  calc
    Fintype.card E = ∑ r : R,
        (Finset.univ.filter fun e ↦ G.right e = r).card := by
      change Finset.univ.card = _
      exact Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ) (t := Finset.univ) (f := G.right) (by simp)
    _ = ∑ _r : R, D := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Fintype.card_of_subtype (p := fun e : E ↦ G.right e = r)
        (Finset.univ.filter fun e ↦ G.right e = r) (by simp)]
      exact hreg.2 r
    _ = Fintype.card R * D := by simp

private lemma card_sides_eq_of_pos (G : BipartiteMultigraph L R E)
    {D : ℕ} (hD : 0 < D) (hreg : G.IsRegular D) :
    Fintype.card L = Fintype.card R := by
  apply Nat.eq_of_mul_eq_mul_right hD
  rw [← card_edges_eq_card_left_mul G hreg,
    ← card_edges_eq_card_right_mul G hreg]

/-- A matching represented by one edge out of each left vertex.  The
injectivity of its right endpoints says that no two selected edges meet on the
right. -/
structure LeftPerfectMatching (G : BipartiteMultigraph L R E) where
  edge : L → E
  left_edge : ∀ l, G.left (edge l) = l
  right_injective : Function.Injective (G.right ∘ edge)

theorem LeftPerfectMatching.edge_injective {G : BipartiteMultigraph L R E}
    (M : G.LeftPerfectMatching) : Function.Injective M.edge := by
  intro l₁ l₂ h
  rw [← M.left_edge l₁, ← M.left_edge l₂, h]

private theorem exists_leftPerfectMatching (G : BipartiteMultigraph L R E)
    {D : ℕ} (hD : 0 < D) (hreg : G.IsRegular D) :
    Nonempty G.LeftPerfectMatching := by
  classical
  let rel : L → R → Prop := fun l r ↦ ∃ e, G.left e = l ∧ G.right e = r
  have hhall : ∀ A : Finset L,
      A.card ≤ ({r | ∃ l ∈ A, rel l r} : Finset R).card := by
    intro A
    let EA : Finset E := Finset.univ.filter fun e ↦ G.left e ∈ A
    let N : Finset R := {r | ∃ l ∈ A, rel l r}
    have hEA : EA.card = A.card * D := by
      change (Finset.univ.filter fun e ↦ G.left e ∈ A).card = A.card * D
      rw [← Finset.sum_card_fiberwise_eq_card_filter
        (s := Finset.univ) (t := A) (g := G.left)]
      calc
        ∑ l ∈ A, (Finset.univ.filter fun e ↦ G.left e = l).card =
            ∑ _l ∈ A, D := by
          apply Finset.sum_congr rfl
          intro l _
          rw [← Fintype.card_of_subtype (p := fun e : E ↦ G.left e = l)
            (Finset.univ.filter fun e ↦ G.left e = l) (by simp)]
          exact hreg.1 l
        _ = A.card * D := by simp
    have hbound : EA.card ≤ N.card * D := by
      calc
        EA.card = ∑ r ∈ N, (EA.filter (fun e ↦ G.right e = r)).card := by
          rw [Finset.sum_card_fiberwise_eq_card_filter
            (s := EA) (t := N) (g := G.right)]
          apply congrArg Finset.card
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, EA, N, rel]
          constructor
          · intro he
            exact ⟨he, ⟨G.left e, he, e, rfl, rfl⟩⟩
          · exact fun he ↦ he.1
        _ ≤ ∑ _r ∈ N, D := by
          apply Finset.sum_le_sum
          intro r hr
          calc
            (EA.filter (fun e ↦ G.right e = r)).card
                ≤ (Finset.univ.filter (fun e ↦ G.right e = r)).card := by
                  apply Finset.card_le_card
                  intro e he
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
                  exact he.2
            _ = D := by
              rw [← Fintype.card_of_subtype (p := fun e : E ↦ G.right e = r)
                (Finset.univ.filter fun e ↦ G.right e = r) (by simp)]
              exact hreg.2 r
        _ = N.card * D := by simp
    apply Nat.le_of_mul_le_mul_right _ hD
    simpa [hEA] using hbound
  obtain ⟨f, hf_inj, hf_rel⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hhall
  let m : L → E := fun l ↦ Classical.choose (hf_rel l)
  refine ⟨⟨m, ?_, ?_⟩⟩
  · intro l
    exact (Classical.choose_spec (hf_rel l)).1
  · intro l₁ l₂ h
    apply hf_inj
    change G.right (m l₁) = G.right (m l₂) at h
    rw [← (Classical.choose_spec (hf_rel l₁)).2,
      ← (Classical.choose_spec (hf_rel l₂)).2]
    exact h

private def remainingFiberEquiv {X Y : Type*} (f : E → X) (m : Y → E)
    (x : X) (y₀ : Y) (he₀ : f (m y₀) = x)
    (hunique : ∀ y, f (m y) = x → m y = m y₀) :
    {e : {e : E // e ∉ Set.range m} // f e.1 = x} ≃
      {e : {e : E // f e = x} // e.1 ≠ m y₀} where
  toFun e := ⟨⟨e.1.1, e.2⟩, fun h ↦ e.1.2 ⟨y₀, h.symm⟩⟩
  invFun e := ⟨⟨e.1.1, by
    rintro ⟨y, hy⟩
    have hfy : f (m y) = x := (congrArg f hy).trans e.1.2
    exact e.2 (hy.symm.trans (hunique y hfy))⟩, e.1.2⟩
  left_inv e := by rfl
  right_inv e := by rfl

private theorem card_remaining_fiber {X Y : Type*} [Fintype Y]
    (f : E → X) (m : Y → E) (x : X) (y₀ : Y) (he₀ : f (m y₀) = x)
    (hunique : ∀ y, f (m y) = x → m y = m y₀) {D : ℕ}
    (hcard : Fintype.card {e : E // f e = x} = D + 1) :
    Fintype.card {e : {e : E // e ∉ Set.range m} // f e.1 = x} = D := by
  classical
  have hone : Fintype.card {e : {e : E // f e = x} // e.1 = m y₀} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨m y₀, he₀⟩, rfl⟩, ?_⟩
    intro e
    apply Subtype.ext
    apply Subtype.ext
    exact e.2
  calc
    Fintype.card {e : {e : E // e ∉ Set.range m} // f e.1 = x} =
        Fintype.card {e : {e : E // f e = x} // e.1 ≠ m y₀} :=
      Fintype.card_congr (remainingFiberEquiv f m x y₀ he₀ hunique)
    _ = Fintype.card {e : E // f e = x} -
        Fintype.card {e : {e : E // f e = x} // e.1 = m y₀} := by
      exact Fintype.card_subtype_compl (fun e : {e : E // f e = x} ↦ e.1 = m y₀)
    _ = D := by omega

private def remaining (G : BipartiteMultigraph L R E)
    (M : G.LeftPerfectMatching) :
    BipartiteMultigraph L R {e : E // e ∉ Set.range M.edge} where
  left e := G.left e.1
  right e := G.right e.1

private theorem remaining_isRegular (G : BipartiteMultigraph L R E) {D : ℕ}
    (hreg : G.IsRegular (D + 1)) (M : G.LeftPerfectMatching) :
    (remaining G M).IsRegular D := by
  classical
  constructor
  · intro l
    change Fintype.card
      {e : {e : E // e ∉ Set.range M.edge} // G.left e.1 = l} = D
    have hrem := card_remaining_fiber G.left M.edge l l (M.left_edge l)
      (fun l' hl' ↦ by
        have : l' = l := by rw [← M.left_edge l', hl']
        exact congrArg M.edge this) (hreg.1 l)
    rw [← Nat.card_eq_fintype_card] at hrem ⊢
    exact hrem
  · intro r
    have hside : Fintype.card L = Fintype.card R :=
      card_sides_eq_of_pos G (Nat.succ_pos D) hreg
    have hbij : Function.Bijective (G.right ∘ M.edge) :=
      (Fintype.bijective_iff_injective_and_card _).2 ⟨M.right_injective, hside⟩
    obtain ⟨l, hl⟩ := hbij.2 r
    change Fintype.card
      {e : {e : E // e ∉ Set.range M.edge} // G.right e.1 = r} = D
    have hrem := card_remaining_fiber G.right M.edge r l hl
      (fun l' hl' ↦ congrArg M.edge (M.right_injective (hl'.trans hl.symm))) (hreg.2 r)
    rw [← Nat.card_eq_fintype_card] at hrem ⊢
    exact hrem

/-- Kőnig's line-colouring theorem for finite regular bipartite
multigraphs: the labelled edges of a `D`-regular graph receive `D` colours,
with no repeated colour at either endpoint. -/
theorem exists_properColoring (G : BipartiteMultigraph L R E) {D : ℕ}
    (hreg : G.IsRegular D) : Nonempty (G.ProperColoring D) := by
  induction D generalizing E with
  | zero =>
      have hE : Fintype.card E = 0 := by
        simpa using card_edges_eq_card_left_mul G hreg
      letI : IsEmpty E := Fintype.card_eq_zero_iff.mp hE
      exact ⟨{
        color := fun e ↦ isEmptyElim e
        left_injective := fun _ e ↦ isEmptyElim e.1
        right_injective := fun _ e ↦ isEmptyElim e.1 }⟩
  | succ D ih =>
      classical
      obtain ⟨M⟩ := exists_leftPerfectMatching G (Nat.succ_pos D) hreg
      have hremaining : (remaining G M).IsRegular D :=
        remaining_isRegular G hreg M
      obtain ⟨C⟩ := ih (remaining G M) hremaining
      let c : E → Fin (D + 1) := fun e ↦
        if he : e ∈ Set.range M.edge then ⟨0, Nat.succ_pos D⟩
        else Fin.succ (C.color ⟨e, he⟩)
      refine ⟨{
        color := c
        left_injective := ?_
        right_injective := ?_ }⟩
      · intro l e₁ e₂ hc
        by_cases h₁ : e₁.1 ∈ Set.range M.edge
        · by_cases h₂ : e₂.1 ∈ Set.range M.edge
          · rcases h₁ with ⟨l₁, hl₁⟩
            rcases h₂ with ⟨l₂, hl₂⟩
            have hll : l₁ = l₂ := by
              rw [← M.left_edge l₁, ← M.left_edge l₂, hl₁, hl₂,
                e₁.2, e₂.2]
            apply Subtype.ext
            exact hl₁.symm.trans ((congrArg M.edge hll).trans hl₂)
          · dsimp only [c] at hc
            rw [dif_pos h₁, dif_neg h₂] at hc
            have := congrArg Fin.val hc
            simp at this
        · by_cases h₂ : e₂.1 ∈ Set.range M.edge
          · dsimp only [c] at hc
            rw [dif_neg h₁, dif_pos h₂] at hc
            have := congrArg Fin.val hc
            simp at this
          · have hc' : C.color ⟨e₁.1, h₁⟩ = C.color ⟨e₂.1, h₂⟩ := by
              dsimp only [c] at hc
              rw [dif_neg h₁, dif_neg h₂] at hc
              exact Fin.succ_injective D hc
            have he := C.left_injective l
              (a₁ := ⟨⟨e₁.1, h₁⟩, e₁.2⟩)
              (a₂ := ⟨⟨e₂.1, h₂⟩, e₂.2⟩) hc'
            apply Subtype.ext
            exact congrArg (fun e ↦ e.1.1) he
      · intro r e₁ e₂ hc
        by_cases h₁ : e₁.1 ∈ Set.range M.edge
        · by_cases h₂ : e₂.1 ∈ Set.range M.edge
          · rcases h₁ with ⟨l₁, hl₁⟩
            rcases h₂ with ⟨l₂, hl₂⟩
            have hrr : G.right (M.edge l₁) = G.right (M.edge l₂) := by
              rw [hl₁, hl₂, e₁.2, e₂.2]
            have hll : l₁ = l₂ := M.right_injective hrr
            apply Subtype.ext
            exact hl₁.symm.trans ((congrArg M.edge hll).trans hl₂)
          · dsimp only [c] at hc
            rw [dif_pos h₁, dif_neg h₂] at hc
            have := congrArg Fin.val hc
            simp at this
        · by_cases h₂ : e₂.1 ∈ Set.range M.edge
          · dsimp only [c] at hc
            rw [dif_neg h₁, dif_pos h₂] at hc
            have := congrArg Fin.val hc
            simp at this
          · have hc' : C.color ⟨e₁.1, h₁⟩ = C.color ⟨e₂.1, h₂⟩ := by
              dsimp only [c] at hc
              rw [dif_neg h₁, dif_neg h₂] at hc
              exact Fin.succ_injective D hc
            have he := C.right_injective r
              (a₁ := ⟨⟨e₁.1, h₁⟩, e₁.2⟩)
              (a₂ := ⟨⟨e₂.1, h₂⟩, e₂.2⟩) hc'
            apply Subtype.ext
            exact congrArg (fun e ↦ e.1.1) he

end BipartiteMultigraph

end Erdos182
