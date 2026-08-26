import Mathlib
import ErdosProblems.Erdos336.CompactProjection
import ErdosProblems.Erdos336.CyclicCompactApproximation
import ErdosProblems.Erdos336.DenseExactPower
import ErdosProblems.Erdos336.MasterTransference

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transference with an arbitrary linear-cost piecewise patch
-/

namespace Erdos336

open scoped Pointwise
open PiecewiseBohrTransfer

private lemma groupRep_of_mem_nsmul_general
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

private lemma mem_nsmul_of_groupRep_general
    {K : Type*} [AddCommGroup K] {E : Set K} {M : ℕ} {y : K}
    (hy : GroupRepExactly E M y) : y ∈ M • E := by
  obtain ⟨xs, hlen, hxmem, hxsum⟩ := hy
  subst M
  rw [Set.mem_nsmul]
  let f : Fin xs.length → E := fun i =>
    ⟨xs.get i, hxmem (xs.get i) (List.get_mem xs i)⟩
  refine ⟨f, ?_⟩
  change (List.ofFn (fun i : Fin xs.length => xs.get i)).sum = y
  rw [List.ofFn_get]
  exact hxsum

/-- Abstract patch transference when the patch lies in an arbitrary exact
`R`-power.  The total order is `M+R+h`: patch cost, compact-cover shift cost,
and one-extra absorption cost. -/
theorem eventuallyExactlyZ_of_general_piecewise_patch
    {K : Type*} {φ : ℤ → K} {U : Set K} {T P D : Set ℤ}
    {S : Finset ℤ} {c : ℤ} {h M R : ℕ}
    (hzero : 0 ∈ D)
    (hparent : EventuallyWithOneExtra D c h)
    (hT : ThickZ T)
    (hpatch : ∀ n : ℤ, φ n ∈ U → n ∈ T → n ∈ P)
    (hcover : ∀ n : ℤ, ∃ s ∈ S, φ (n - s) ∈ U)
    (hPrep : ∀ p ∈ P, ZRepExactly D R p)
    (hSrep : ∀ s ∈ S, ZRepExactly D M s) :
    EventuallyExactlyZ D (M + R + h) := by
  have hthickRep : RepThick D (R + M) := by
    apply repThick_of_patch_cover hT hpatch hcover
    · exact hPrep
    · exact hSrep
  have hthick : ExactPowerThick D (R + M) := hthickRep
  have hout := eventuallyExactlyZ_of_thick_of_oneExtra hzero hthick hparent
  convert hout using 1 <;> omega

/-- Compact-power version of the general patch theorem. -/
theorem eventuallyExactlyZ_of_compact_power_and_general_patch
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] [CompactSpace K]
    (φ : ℤ →+ K)
    {U : Set K} {T P D : Set ℤ} {c : ℤ} {h M R : ℕ}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hzero : 0 ∈ D)
    (hparent : EventuallyWithOneExtra D c h)
    (hT : ThickZ T)
    (hpatch : ∀ n : ℤ, φ n ∈ U → n ∈ T → n ∈ P)
    (hPrep : ∀ p ∈ P, ZRepExactly D R p)
    (hpower : M • closure (φ '' D) = (Set.univ : Set K)) :
    EventuallyExactlyZ D (M + R + h) := by
  obtain ⟨S, hSrep, hcover⟩ :=
    finite_patch_cover_of_closed_power φ hUopen hUne hpower
  exact eventuallyExactlyZ_of_general_piecewise_patch hzero hparent hT
    hpatch hcover hPrep hSrep

/-- End-to-end finite-cyclic-to-integer transference for a patch of any exact
cost `R`. -/
theorem eventuallyExactlyZ_of_cyclic_bound_and_general_patch
    {K : Type*} [NormedAddCommGroup K] [CompactSpace K]
    (φ : ℤ →+ K) (hdense : DenseRange φ)
    {U : Set K} {T P D : Set ℤ} {c : ℤ} {h q M R : ℕ}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hzero : 0 ∈ D)
    (hparent : EventuallyWithOneExtra D c h)
    (hexact : EventuallyExactlyZ D q)
    (hT : ThickZ T)
    (hpatch : ∀ n : ℤ, φ n ∈ U → n ∈ T → n ∈ P)
    (hPrep : ∀ p ∈ P, ZRepExactly D R p)
    (hcyclic : CyclicRemovalBound (h + 1) M) :
    EventuallyExactlyZ D (M + R + h) := by
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
    apply groupRep_of_mem_nsmul_general
    rw [hparentPower]
    exact Set.mem_univ y
  have hexactRep : ∀ y : K, GroupRepExactly E q y := by
    intro y
    apply groupRep_of_mem_nsmul_general
    rw [hexactPower]
    exact Set.mem_univ y
  have hMrep : ∀ y : K, GroupRepExactly E M y :=
    compact_removal_of_cyclic_bound φ hdense hEclosed hzeroE
      hparentRep hexactRep hcyclic
  have hMpower : M • E = (Set.univ : Set K) := by
    apply Set.eq_univ_of_forall
    intro y
    exact mem_nsmul_of_groupRep_general (hMrep y)
  exact eventuallyExactlyZ_of_compact_power_and_general_patch φ hUopen hUne
    hzero hparent hT hpatch hPrep hMpower

end Erdos336
