import ErdosProblems.Erdos1105.Representatives

namespace Erdos1105

open SimpleGraph
open Fin.NatCast

/-- Enumerate the edges of a cycle in their cyclic order. -/
def cycleEdge (n : ℕ) (i : Fin (n + 3)) : (cycleGraph (n + 3)).edgeSet :=
  ⟨s(i, i + 1), by
    change (cycleGraph (n + 3)).Adj i (i + 1)
    rw [cycleGraph_adj]
    exact Or.inr (add_sub_cancel_left i 1)⟩

lemma cycleEdge_injective (n : ℕ) : Function.Injective (cycleEdge n) := by
  intro i j hij
  have h : s(i, i + 1) = s(j, j + 1) := congrArg Subtype.val hij
  rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h₁, h₂⟩
  · exact h
  · have hadd : i + (1 + 1 : Fin (n + 3)) = i := by
      rw [← add_assoc, h₂, ← h₁]
    have htwo : (1 + 1 : Fin (n + 3)) = 0 := by
      exact add_left_cancel (show i + (1 + 1 : Fin (n + 3)) = i + 0 by simpa using hadd)
    have hval := congrArg Fin.val htwo
    norm_num [Fin.val_add, Nat.mod_eq_of_lt (show 1 < n + 3 by omega),
      Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at hval

lemma cycleEdge_surjective (n : ℕ) : Function.Surjective (cycleEdge n) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hadj : (cycleGraph (n + 3)).Adj a b := he
    rw [cycleGraph_adj] at hadj
    rcases hadj with hab | hba
    · have h : a = b + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp hab
      refine ⟨b, Subtype.ext ?_⟩
      change s(b, b + 1) = s(a, b)
      rw [← h, Sym2.eq_swap]
    · have h : b = a + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp hba
      exact ⟨a, Subtype.ext (by change s(a, a + 1) = s(a, b); rw [← h])⟩

lemma isRainbow_cycle_iff {V C : Type*} {G : SimpleGraph V} {n : ℕ}
    (f : (cycleGraph (n + 3)).Copy G) (c : G.edgeSet → C) :
    IsRainbow f c ↔ Function.Injective (fun i ↦ c (f.mapEdgeSet (cycleEdge n i))) := by
  constructor
  · intro h
    exact h.comp (cycleEdge_injective n)
  · intro h e d hed
    obtain ⟨i, rfl⟩ := cycleEdge_surjective n e
    obtain ⟨j, rfl⟩ := cycleEdge_surjective n d
    exact congrArg (cycleEdge n) (h hed)

lemma isRainbow_cycle_iff_pairColors {V C : Type*} {G : SimpleGraph V} {n : ℕ}
    (f : (cycleGraph (n + 3)).Copy G) (c : G.edgeSet → C) :
    IsRainbow f c ↔ Function.Injective
      (fun i : Fin (n + 3) ↦ extendColor c s(f i, f (i + 1))) := by
  rw [isRainbow_cycle_iff]
  have hcol (i : Fin (n + 3)) : extendColor c s(f i, f (i + 1)) =
      some (c (f.mapEdgeSet (cycleEdge n i))) :=
    extendColor_edge c (f.mapEdgeSet (cycleEdge n i))
  simp only [Function.Injective, hcol, Option.some.injEq]

/-- Propagation by one step reaches every position of a finite cycle. -/
lemma forall_of_cyclic_step {n : ℕ} (P : Fin (n + 3) → Prop)
    (hstep : ∀ i, P i → P (i + 1)) {i : Fin (n + 3)} (hi : P i) : ∀ j, P j := by
  have hiter (m : ℕ) : P (i + (m : Fin (n + 3))) := by
    induction m with
    | zero => simpa using hi
    | succ m hm => simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hstep _ hm
  intro j
  have h := hiter (j - i).val
  simpa using h

lemma forall_of_cyclic_step_back {n : ℕ} (P : Fin (n + 3) → Prop)
    (hstep : ∀ i, P i → P (i - 1)) {i : Fin (n + 3)} (hi : P i) : ∀ j, P j := by
  have hiter (m : ℕ) : P (i - (m : Fin (n + 3))) := by
    induction m with
    | zero => simpa using hi
    | succ m hm => simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using hstep _ hm
  intro j
  have h := hiter (i - j).val
  simpa using h

/-- The cyclic propagation argument behind the private-color component lemma.
The two exceptional collision patterns propagate all the way around the cycle,
contradicting the distinguished color outside the cycle palette. -/
lemma cyclic_boundary_constant {C : Type*} {n : ℕ}
    (a b : Fin (n + 3) → C) (hb : Function.Injective b)
    (hrel : ∀ i, a i = a (i + 1) ∨ a i = b (i - 1) ∨ a (i + 1) = b (i + 1))
    (hforward : ∀ i, a i = b i → a i ≠ a (i + 1))
    (hback : ∀ i, a i = b (i - 1) → a i ≠ a (i - 1))
    (hzero : ∀ j, a 0 ≠ b j) : ∀ i, a i = a 0 := by
  have hne (i : Fin (n + 3)) : i - 1 ≠ i := by
    intro hi
    have h10 : (1 : Fin (n + 3)) = 0 := by
      have h := congrArg (fun x ↦ x + 1) hi
      simp only [sub_add_cancel] at h
      exact (add_left_cancel (show i + 0 = i + 1 by simpa only [add_zero] using h)).symm
    exact one_ne_zero h10
  have hP : ∀ i, a i ≠ b i := by
    intro i hi
    have hstep : ∀ j, a j = b j → a (j + 1) = b (j + 1) := by
      intro j hj
      rcases hrel j with h | h | h
      · exact (hforward j hj h).elim
      · exact (hne j (hb (h.symm.trans hj))).elim
      · exact h
    exact hzero 0 (forall_of_cyclic_step (fun j ↦ a j = b j) hstep hi 0)
  have hQ : ∀ i, a i ≠ b (i - 1) := by
    intro i hi
    have hstep : ∀ j, a j = b (j - 1) → a (j - 1) = b (j - 1 - 1) := by
      intro j hj
      have hr := hrel (j - 1)
      simp only [sub_add_cancel] at hr
      rcases hr with h | h | h
      · exact (hback j hj h.symm).elim
      · exact h
      · exact (hP j h).elim
    exact hzero (0 - 1) (forall_of_cyclic_step_back (fun j ↦ a j = b (j - 1)) hstep hi 0)
  have hstep : ∀ i, a i = a 0 → a (i + 1) = a 0 := by
    intro i hi
    rcases hrel i with h | h | h
    · exact h.symm.trans hi
    · exact (hQ i h).elim
    · exact (hP (i + 1) h).elim
  exact forall_of_cyclic_step (fun i ↦ a i = a 0) hstep rfl

end Erdos1105
