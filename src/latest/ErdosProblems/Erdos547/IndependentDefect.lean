import ErdosProblems.Erdos547.SymmetricLoadInterval

/-!
# Fractional saturation from independent-set inequalities with a bounded defect

A universal auxiliary vertex absorbs the allowed defect. Its capacity need
not be at most one; the load-interval theorem is used before deleting it.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V]

def universalExtension (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | none, none => False
    | some u, some v => G.Adj u v
    | _, _ => True
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · trivial
    · trivial
    · exact h.symm⟩
  loopless := ⟨by
    intro x
    cases x with
    | none => exact not_false
    | some u => exact G.loopless.irrefl u⟩

theorem exists_fractional_saturation_of_independent_defect (G : SimpleGraph V)
    (a b : V → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (ha : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ b u) (hb : ∀ u, b u ≤ 1)
    (hI : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∑ u ∈ I, a u) ≤ (∑ v ∈ graphNeighbours G I, b v) + D) :
    ∃ μ : FractionalMatching G, (∀ u, μ.load u ≤ b u) ∧
      (∑ u, a u) - D ≤ ∑ u, min (a u) (μ.load u) := by
  classical
  let H := universalExtension G
  let A : Option V → ℝ := fun x ↦ x.elim 0 a
  let B : Option V → ℝ := fun x ↦ x.elim D b
  have hA : ∀ x, 0 ≤ A x := by
    intro x
    cases x with
    | none => exact le_rfl
    | some u => exact ha u
  have hAB : ∀ x, A x ≤ B x := by
    intro x
    cases x with
    | none => exact hD
    | some u => exact hab u
  have hB : ∀ x, 0 ≤ B x := fun x ↦ (hA x).trans (hAB x)
  have hHall : ∀ I : Finset (Option V), (∀ x ∈ I, ∀ y ∈ I, ¬ H.Adj x y) →
      (∑ x ∈ I, A x) ≤ ∑ y ∈ graphNeighbours H I, B y := by
    intro I hind
    let J := Finset.univ.filter (fun u ↦ some u ∈ I)
    have hsumA : (∑ x ∈ I, A x) = ∑ u ∈ J, a u := by
      calc
        _ = ∑ x : Option V, if x ∈ I then A x else 0 := by simp
        _ = _ := by simp only [Fintype.sum_option, A, Option.elim_none, Option.elim_some,
          ite_self, zero_add, J, Finset.sum_filter]
    by_cases hn : none ∈ I
    · have hz : (∑ x ∈ I, A x) = 0 := Finset.sum_eq_zero fun x hx ↦ by
        cases x with
        | none => rfl
        | some u => exact (hind none hn (some u) hx trivial).elim
      rw [hz]
      exact Finset.sum_nonneg fun y _ ↦ hB y
    · by_cases hJ : J.Nonempty
      · have hJind : ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v := by
          intro u hu v hv huv
          exact hind (some u) (Finset.mem_filter.mp hu).2
            (some v) (Finset.mem_filter.mp hv).2 huv
        have hnone : none ∈ graphNeighbours H I := by
          obtain ⟨u, hu⟩ := hJ
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, some u,
            (Finset.mem_filter.mp hu).2, trivial⟩
        have hsome (v : V) : some v ∈ graphNeighbours H I ↔ v ∈ graphNeighbours G J := by
          constructor
          · intro hv
            obtain ⟨x, hx, hxy⟩ := (Finset.mem_filter.mp hv).2
            cases x with
            | none => exact (hn hx).elim
            | some u => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, hxy⟩
          · intro hv
            obtain ⟨u, hu, huv⟩ := (Finset.mem_filter.mp hv).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, some u,
              (Finset.mem_filter.mp hu).2, huv⟩
        have hsumB : (∑ x ∈ graphNeighbours H I, B x) =
            D + ∑ u ∈ graphNeighbours G J, b u := by
          calc
            _ = ∑ x : Option V, if x ∈ graphNeighbours H I then B x else 0 := by simp
            _ = _ := by
              rw [Fintype.sum_option]
              simp only [hnone, if_true, B, Option.elim_none, Option.elim_some, hsome,
                Finset.sum_ite_mem_eq]
        rw [hsumA, hsumB]
        linarith [hI J hJind]
      · rw [hsumA, Finset.not_nonempty_iff_eq_empty.mp hJ, Finset.sum_empty]
        exact Finset.sum_nonneg fun y _ ↦ hB y
  obtain ⟨f, hf, hsym, hsupp, hload⟩ := exists_symmetric_load_interval H A B hA hAB hHall
  have huBound (u : V) : (∑ v, f (some u) (some v)) ≤ b u := by
    have hh := (hload (some u)).2
    rw [Fintype.sum_option] at hh
    change f (some u) none + (∑ v, f (some u) (some v)) ≤ b u at hh
    linarith [hf (some u) none]
  let μ : FractionalMatching G :=
    { weight := fun u v ↦ f (some u) (some v)
      nonnegative := fun u v ↦ hf _ _
      symmetric := fun u v ↦ hsym _ _
      supported := fun u v huv ↦ hsupp _ _ huv
      capacity := fun u ↦ (huBound u).trans (hb u) }
  have hpoint (u : V) : a u - f (some u) none ≤ min (a u) (μ.load u) := by
    have hh := (hload (some u)).1
    rw [Fintype.sum_option] at hh
    change a u ≤ f (some u) none + μ.load u at hh
    exact le_min (sub_le_self _ (hf _ _)) (by linarith)
  have hdefect : (∑ u, f (some u) none) ≤ D := by
    have hh := (hload none).2
    rw [Fintype.sum_option] at hh
    have hz : f none none = 0 := hsupp _ _ not_false
    rw [hz, zero_add] at hh
    calc
      _ = ∑ u, f none (some u) := Finset.sum_congr rfl fun u _ ↦ hsym _ _
      _ ≤ _ := hh
  refine ⟨μ, huBound, ?_⟩
  have hh := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset V)) ↦ hpoint u)
  rw [Finset.sum_sub_distrib] at hh
  linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_fractional_saturation_of_independent_defect
