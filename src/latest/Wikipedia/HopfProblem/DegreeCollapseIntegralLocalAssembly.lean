import Wikipedia.HopfProblem.DegreeCollapseIntegralManifoldSupport

/-!
# Gluing locally represented integral values on compact manifold supports

The compact-support detection theorem turns equality of local values
into actual agreement on compact intersections. Integral Mayer--Vietoris
then glues the original classes. A finite compact-neighborhood cover
proves unique global representation on the given compact support.
Local representability is explicit; this does not construct an orientation
of a manifold or assume a global fundamental class.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralLocalAssembly

open NoExoticSixSphere SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M]

abbrev Values (M : Type) [TopologicalSpace M] (d : ℕ) :=
  (x : M) → (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) ({x}ᶜ : Set M)).homology d

def Represents {d : ℕ} (v : Values M d) (K : Set M)
    (a : Homology (ModuleCat.of ℤ ℤ) K d) : Prop :=
  ∀ (x : M) (hx : x ∈ K), evaluate (ModuleCat.of ℤ ℤ) K x hx d a = v x

theorem Represents.restrict {d : ℕ} {v : Values M d} {K L : Set M} (hKL : K ⊆ L)
    {a : Homology (ModuleCat.of ℤ ℤ) L d} (ha : Represents v L a) :
    Represents v K (restrict (ModuleCat.of ℤ ℤ) hKL d a) := by
  intro x hx
  exact (LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ ℤ) hKL x hx d) a).trans
    (ha x (hKL hx))

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]
  [T2Space M] [ChartedSpace E M]

include E in
theorem exists_union (v : Values M (n + 2)) (K L : Set M) (hK : IsCompact K) (hL : IsCompact L)
    (a : Homology (ModuleCat.of ℤ ℤ) K (n + 2)) (b : Homology (ModuleCat.of ℤ ℤ) L (n + 2))
    (ha : Represents v K a) (hb : Represents v L b) :
    ∃ c : Homology (ModuleCat.of ℤ ℤ) (K ∪ L) (n + 2), Represents v (K ∪ L) c := by
  have haI := ha.restrict (Set.inter_subset_left : K ∩ L ⊆ K)
  have hbI := hb.restrict (Set.inter_subset_right : K ∩ L ⊆ L)
  have hab := IntegralCompactSupport.compactManifold_detected (E := E) n (K ∩ L)
    (hK.inter_right hL.isClosed) _ _ (fun x hx => (haI x hx).trans (hbI x hx).symm)
  obtain ⟨c, hcK, hcL⟩ := IntegralSupportedUnion.exists_lift_union K L hK.isClosed hL.isClosed
    (n + 2) a b hab
  refine ⟨c, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · have he := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ ℤ)
      (Set.subset_union_left : K ⊆ K ∪ L) x hx (n + 2)) c
    change evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2)
      (restrict (ModuleCat.of ℤ ℤ) Set.subset_union_left (n + 2) c) = _ at he
    rw [hcK] at he
    exact he.symm.trans (ha x hx)
  · have he := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ ℤ)
      (Set.subset_union_right : L ⊆ K ∪ L) x hx (n + 2)) c
    change evaluate (ModuleCat.of ℤ ℤ) L x hx (n + 2)
      (restrict (ModuleCat.of ℤ ℤ) Set.subset_union_right (n + 2) c) = _ at he
    rw [hcL] at he
    exact he.symm.trans (hb x hx)

include E in
theorem exists_finiteUnion (v : Values M (n + 2)) {ι : Type*} (s : Finset ι) (K : ι → Set M)
    (hK : ∀ i ∈ s, IsCompact (K i))
    (hc : ∀ i ∈ s, ∃ a : Homology (ModuleCat.of ℤ ℤ) (K i) (n + 2), Represents v (K i) a) :
    ∃ a : Homology (ModuleCat.of ℤ ℤ) (⋃ i ∈ s, K i) (n + 2), Represents v (⋃ i ∈ s, K i) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have he : (⋃ i ∈ (∅ : Finset ι), K i) = ∅ := by simp
      rw [he]
      exact ⟨0, fun _ hx => False.elim hx⟩
  | @insert i s hi ih =>
      have hsmallK : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
      obtain ⟨a, ha⟩ := hc i (Finset.mem_insert_self i s)
      obtain ⟨b, hb⟩ := ih hsmallK (fun j hj => hc j (Finset.mem_insert_of_mem hj))
      have h := exists_union (E := E) n v (K i) (⋃ j ∈ s, K j)
        (hK i (Finset.mem_insert_self i s)) (s.isCompact_biUnion hsmallK) a b ha hb
      have he : (⋃ j ∈ insert i s, K j) = K i ∪ ⋃ j ∈ s, K j := by
        simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
      rw [he]
      exact h

include E in
/-- Local original representatives assemble uniquely on the original compact support. -/
theorem existsUnique_of_local_representatives (v : Values M (n + 2)) (K : Set M) (hK : IsCompact K)
    (hlocal : ∀ x ∈ K, ∃ B : Set M, IsCompact B ∧ x ∈ interior B ∧
      ∃ a : Homology (ModuleCat.of ℤ ℤ) B (n + 2), Represents v B a) :
    ∃! a : Homology (ModuleCat.of ℤ ℤ) K (n + 2), Represents v K a := by
  classical
  have hdata := fun x : K => hlocal x x.property
  choose B hB hxB c hc using hdata
  have hcover : K ⊆ ⋃ x : K, interior (B x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxB ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => interior (B x))
    (fun _ => isOpen_interior) hcover
  have h := exists_finiteUnion (E := E) n v s (fun x => K ∩ B x)
    (fun x _ => hK.inter_right (hB x).isClosed)
    (fun x _ => ⟨restrict (ModuleCat.of ℤ ℤ) (Set.inter_subset_right : K ∩ B x ⊆ B x)
      (n + 2) (c x), (hc x).restrict Set.inter_subset_right⟩)
  have he : (⋃ x ∈ s, K ∩ B x) = K := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, _, hx⟩ := mem_iUnion₂.mp hy
      exact hx.1
    · intro y hy
      obtain ⟨x, hx, hyB⟩ := mem_iUnion₂.mp (hs hy)
      exact mem_iUnion₂.mpr ⟨x, hx, hy, interior_subset hyB⟩
  rw [he] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact IntegralCompactSupport.compactManifold_detected (E := E) n K hK b a
    (fun x hx => (hb x hx).trans (ha x hx).symm)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralLocalAssembly
