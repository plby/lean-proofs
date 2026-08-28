import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportedUnion
import Wikipedia.HopfProblem.DegreeCollapseIntegralEuclideanFundamentalClass
import Wikipedia.NoExoticSixSphere.ConvexLocalEvaluation
import Wikipedia.NoExoticSixSphere.EmptySupportedHomology

/-!
# Integral detection and dimension bounds on finite convex supports

The actual convex-complement comparison gives bijective integral point
evaluation. Integral Mayer--Vietoris then propagates detection and
above-dimensional vanishing through finite unions, including all their
intersections. No orientation or fundamental-class existence is assumed.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupport

open NoExoticSixSphere SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M]

/-- Properties of the original integral groups and their actual local evaluations. -/
structure Properties (d : ℕ) (K : Set M) : Prop where
  compact : IsCompact K
  above : ∀ k : ℕ, d < k → Subsingleton (Homology (ModuleCat.of ℤ ℤ) K k)
  detected : ∀ a b : Homology (ModuleCat.of ℤ ℤ) K d,
    (∀ (x : M) (hx : x ∈ K), evaluate (ModuleCat.of ℤ ℤ) K x hx d a =
      evaluate (ModuleCat.of ℤ ℤ) K x hx d b) → a = b

theorem Properties.empty (d : ℕ) : Properties d (∅ : Set M) where
  compact := isCompact_empty
  above k _ := homology_empty_subsingleton (ModuleCat.of ℤ ℤ) k
  detected a b _ := (homology_empty_subsingleton (ModuleCat.of ℤ ℤ) d).elim a b

variable [T2Space M]

theorem Properties.union (d : ℕ) {K L : Set M}
    (hK : Properties d K) (hL : Properties d L) (hI : Properties d (K ∩ L)) :
    Properties d (K ∪ L) where
  compact := hK.compact.union hL.compact
  above k hk := by
    let := hK.above k hk
    let := hL.above k hk
    let := hI.above (k + 1) (by omega)
    exact IntegralSupportedUnion.homology_union_subsingleton K L
      hK.compact.isClosed hL.compact.isClosed k
  detected a b hab := by
    let := hI.above (d + 1) (by omega)
    apply IntegralSupportedUnion.eq_of_restrict_union_eq K L
      hK.compact.isClosed hL.compact.isClosed d a b
    · apply hK.detected
      intro x hx
      have ha := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ ℤ)
        (Set.subset_union_left : K ⊆ K ∪ L) x hx d) a
      have hb := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ ℤ)
        (Set.subset_union_left : K ⊆ K ∪ L) x hx d) b
      exact ha.trans ((hab x (Or.inl hx)).trans hb.symm)
    · apply hL.detected
      intro x hx
      have ha := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ ℤ)
        (Set.subset_union_right : L ⊆ K ∪ L) x hx d) a
      have hb := LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ ℤ)
        (Set.subset_union_right : L ⊆ K ∪ L) x hx d) b
      exact ha.trans ((hab x (Or.inr hx)).trans hb.symm)

section ConvexEvaluation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_evaluate_bijective (K : Set E) (hK : IsCompact K)
    (hC : Convex ℝ K) (x : E) (hx : x ∈ K) (k : ℕ) :
    Function.Bijective (evaluate (ModuleCat.of ℤ ℤ) K x hx k) := by
  let h := Homeomorph.subRight x
  let L := h '' K
  have hL : IsCompact L := hK.image h.continuous
  have hLC : Convex ℝ L := by
    change Convex ℝ ((fun y : E => y - x) '' K)
    simpa only [sub_eq_add_neg, add_comm] using hC.translate (-x)
  have hL0 : (0 : E) ∈ L := ⟨x, hx, sub_self x⟩
  have hKL : ∀ y, y ∈ K ↔ h y ∈ L := by
    intro y
    constructor
    · exact fun hy => ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, he⟩
      exact h.injective he ▸ hz
  obtain ⟨r, hr, hB⟩ := hL.isBounded.exists_pos_norm_lt
  have hQ : QuasiIso (restrictChain (ModuleCat.of ℤ ℤ)
      (Set.singleton_subset_iff.mpr ((hKL x).mp hx))) :=
    ConvexLocalHomology.evaluationChain_zero_mem_quasiIso L hLC hL0 r hr hB
      (h x) ((hKL x).mp hx)
  let := hQ
  exact (evaluate_bijective_iff_homeomorph (ModuleCat.of ℤ ℤ) h hKL x hx k).mp
    (isoOfQuasiIsoAt (restrictChain (ModuleCat.of ℤ ℤ)
      (Set.singleton_subset_iff.mpr ((hKL x).mp hx))) k).toLinearEquiv.bijective

end ConvexEvaluation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]

theorem local_above_subsingleton (x : E) (k : ℕ) (hk : n + 2 < k) :
    Subsingleton ((RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) ({x}ᶜ : Set E)).homology k) := by
  change Subsingleton (RelativeSingularHomology.LocalHomology x k)
  cases k with
  | zero => omega
  | succ j =>
      let := RelativeSingularHomology.localHomology_subsingleton E n j (by omega) (by omega)
      exact (RelativeSingularHomology.translateLocalEquiv E x (j + 1)).injective.subsingleton

theorem compactConvex (K : Set E) (hK : IsCompact K) (hC : Convex ℝ K) :
    Properties (n + 2) K := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx⟩ := hne
    refine ⟨hK, ?_, ?_⟩
    · intro k hk
      let := local_above_subsingleton n x k hk
      exact (convex_evaluate_bijective K hK hC x hx k).injective.subsingleton
    · intro a b he
      exact (convex_evaluate_bijective K hK hC x hx (n + 2)).injective (he x hx)
  · have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst K
    exact Properties.empty (n + 2)

/-- Intersections needed by induction are themselves finite unions of compact convex sets. -/
theorem finiteUnion_compactConvex {ι : Type*} (s : Finset ι) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i)) (hC : ∀ i ∈ s, Convex ℝ (K i)) :
    Properties (n + 2) (⋃ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => simpa using (Properties.empty (M := E) (n + 2))
  | @insert i s hi ih =>
    have hKi := hK i (Finset.mem_insert_self i s)
    have hCi := hC i (Finset.mem_insert_self i s)
    have hsmallK : ∀ j ∈ s, IsCompact (K j) := fun j hj => hK j (Finset.mem_insert_of_mem hj)
    have hsmallC : ∀ j ∈ s, Convex ℝ (K j) := fun j hj => hC j (Finset.mem_insert_of_mem hj)
    have hleft := compactConvex n (K i) hKi hCi
    have hright := ih K hsmallK hsmallC
    have hinter := ih (fun j => K i ∩ K j)
      (fun j hj => hKi.inter_right (hsmallK j hj).isClosed)
      (fun j hj => hCi.inter (hsmallC j hj))
    have hinter' : Properties (n + 2) (K i ∩ (⋃ j ∈ s, K j)) := by
      simpa only [Set.inter_iUnion] using hinter
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using
      (Properties.union (n + 2) hleft hright hinter')

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupport
