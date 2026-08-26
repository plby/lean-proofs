import Mathlib
import ErdosProblems.Erdos336.CompactProjection
import ErdosProblems.Erdos336.CyclicCompactApproximation
import ErdosProblems.Erdos336.CompactPatchTransference

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# End-to-end transference from a finite cyclic bound and a piecewise patch
-/

namespace Erdos336

open scoped Pointwise
open PiecewiseBohrTransfer

private lemma groupRep_of_mem_nsmul'
    {K : Type*} [AddCommGroup K] {E : Set K} {M : ℕ} {y : K}
    (hy : y ∈ M • E) : GroupRepExactly E M y := by
  rw [Set.mem_nsmul] at hy
  obtain ⟨f, hf⟩ := hy
  let xs : List K := List.ofFn (fun i : Fin M => (f i : K))
  exact ⟨xs, by simp [xs], by
    intro z hz
    simp only [xs, List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact (f i).2, hf⟩

/-- Once a BFW-type piecewise patch is supplied, a uniform finite cyclic
removal bound transfers all the way back to eventual exact integer coverage.
The only losses are the one parent summand required by cyclic discretization
and the linear `3h` patch/absorption overhead. -/
theorem eventuallyExactlyZ_of_cyclic_bound_and_patch
    {K : Type*} [NormedAddCommGroup K] [CompactSpace K]
    (φ : ℤ →+ K) (hdense : DenseRange φ)
    {U : Set K} {T P D : Set ℤ} {c : ℤ} {h q M : ℕ}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hzero : 0 ∈ D)
    (hparent : EventuallyWithOneExtra D c h)
    (hexact : EventuallyExactlyZ D q)
    (hT : ThickZ T)
    (hpatch : ∀ n : ℤ, φ n ∈ U → n ∈ T → n ∈ P)
    (hPrep : ∀ p ∈ P, ZRepExactly D (2 * h) p)
    (hcyclic : CyclicRemovalBound (h + 1) M) :
    EventuallyExactlyZ D (M + 3 * h) := by
  let E : Set K := closure (φ '' D)
  have hEclosed : IsClosed E := isClosed_closure
  have hzeroE : 0 ∈ E := by
    apply subset_closure
    exact ⟨0, hzero, by simp⟩
  have hparentPower : h • (E ∪ {φ c}) = (Set.univ : Set K) :=
    closed_parent_power_eq_univ_of_eventuallyWithOneExtra φ hdense hparent
  have hexactPower : q • E = (Set.univ : Set K) :=
    closed_power_eq_univ_of_eventuallyExactlyZ φ hdense hexact
  have hparentRep : ∀ y : K, GroupRepExactly (E ∪ {φ c}) h y := by
    intro y
    apply groupRep_of_mem_nsmul'
    rw [hparentPower]
    exact Set.mem_univ y
  have hexactRep : ∀ y : K, GroupRepExactly E q y := by
    intro y
    apply groupRep_of_mem_nsmul'
    rw [hexactPower]
    exact Set.mem_univ y
  have hMrep : ∀ y : K, GroupRepExactly E M y :=
    compact_removal_of_cyclic_bound φ hdense hEclosed hzeroE
      hparentRep hexactRep hcyclic
  have hMpower : M • E = (Set.univ : Set K) := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨xs, hlen, hxmem, hxsum⟩ := hMrep y
    subst M
    rw [Set.mem_nsmul]
    let f : Fin xs.length → E := fun i =>
      ⟨xs.get i, hxmem (xs.get i) (List.get_mem xs i)⟩
    refine ⟨f, ?_⟩
    change (List.ofFn (fun i : Fin xs.length => xs.get i)).sum = y
    rw [List.ofFn_get]
    exact hxsum
  exact eventuallyExactlyZ_of_compact_power_and_patch φ hUopen hUne hzero
    hparent hT hpatch hPrep hMpower

end Erdos336
