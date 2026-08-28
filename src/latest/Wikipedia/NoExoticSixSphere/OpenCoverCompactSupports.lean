import Wikipedia.NoExoticSixSphere.CompactSupportOpenInclusion
import Wikipedia.NoExoticSixSphere.CompactSupportedCapInclusion

/-!
# Cofinal compact supports subordinate to an actual two-open-set cover

Every compact subset splits into two compact subsets lying in the two
open sets. Their actual subtype supports form a directed family of
ambient union supports. Every compact-support cohomology class has a
representative in this family, and equality can be tested after enlarging
both subtype supports in that same family.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.OpenCoverCompactSupports

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)

abbrev Index := Compacts U × Compacts V

/-- The actual ambient compact union of the two neighborhood supports. -/
def unionCompact (K : Index U V) : Compacts X :=
  CompactSupportCohomology.imageCompact U K.1 ⊔ CompactSupportCohomology.imageCompact V K.2

omit [T2Space X] in
theorem unionCompact_mono : Monotone (unionCompact U V) := by
  intro K L h
  exact sup_le_sup (Set.image_mono h.1) (Set.image_mono h.2)

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover

/-- Every original ambient compact set is exactly such a union of actual subtype supports. -/
theorem exists_union (N : Compacts X) : ∃ K : Index U V, unionCompact U V K = N := by
  obtain ⟨A, B, hA, hB, hAU, hBV, hN⟩ := N.isCompact.binary_compact_cover hU hV
    (by rw [hcover]; exact Set.subset_univ _)
  let K : Compacts U := ⟨SupportedRelativeHomology.supportIn U A,
    SupportedRelativeHomology.supportIn_isCompact U A hA hAU⟩
  let L : Compacts V := ⟨SupportedRelativeHomology.supportIn V B,
    SupportedRelativeHomology.supportIn_isCompact V B hB hBV⟩
  refine ⟨(K, L), ?_⟩
  apply SetLike.coe_injective
  change (Subtype.val '' (Subtype.val ⁻¹' A : Set U)) ∪
    (Subtype.val '' (Subtype.val ⁻¹' B : Set V)) = (N : Set X)
  rw [Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hAU),
    Set.image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hBV)]
  exact hN.symm

/-- The directed family can enlarge two prescribed indices while covering any ambient compact. -/
theorem exists_common_upper (K L : Index U V) (N : Compacts X) :
    ∃ P : Index U V, K ≤ P ∧ L ≤ P ∧ N ≤ unionCompact U V P := by
  obtain ⟨Q, hQ⟩ := exists_union U V hU hV hcover N
  refine ⟨(K ⊔ L) ⊔ Q, (le_sup_left : K ≤ K ⊔ L).trans le_sup_left,
    (le_sup_right : L ≤ K ⊔ L).trans le_sup_left, ?_⟩
  rw [← hQ]
  exact unionCompact_mono U V le_sup_right

/-- Every actual compact-support class has a representative on a subordinate union support. -/
theorem exists_representative (p : ℕ) (a : CompactSupportCohomology.Cohomology X p) :
    ∃ (K : Index U V) (b : CompactSupportCohomology.Component X p (unionCompact U V K)),
      CompactSupportCohomology.of X p (unionCompact U V K) b = a := by
  obtain ⟨N, b, rfl⟩ := CompactSupportCohomology.exists_representative X p a
  obtain ⟨K, rfl⟩ := exists_union U V hU hV hcover N
  exact ⟨K, b, rfl⟩

/-- Genuine direct-limit equality is detected by enlargement in this same subordinate family. -/
theorem of_eq_iff (p : ℕ) (K L : Index U V)
    (a : CompactSupportCohomology.Component X p (unionCompact U V K))
    (b : CompactSupportCohomology.Component X p (unionCompact U V L)) :
    CompactSupportCohomology.of X p (unionCompact U V K) a =
        CompactSupportCohomology.of X p (unionCompact U V L) b ↔
      ∃ (P : Index U V) (hK : K ≤ P) (hL : L ≤ P),
        SupportedModTwoCohomology.extend (unionCompact_mono U V hK) p a =
          SupportedModTwoCohomology.extend (unionCompact_mono U V hL) p b := by
  constructor
  · intro hab
    obtain ⟨N, hKN, hLN, he⟩ := (CompactSupportCohomology.of_eq_iff X p
      (unionCompact U V K) (unionCompact U V L) a b).mp hab
    obtain ⟨P, hKP, hLP, hNP⟩ := exists_common_upper U V hU hV hcover K L N
    refine ⟨P, hKP, hLP, ?_⟩
    have he' := congrArg (SupportedModTwoCohomology.extend hNP p) he
    have ha := LinearMap.congr_fun (SupportedModTwoCohomology.extend_trans hKN hNP p) a
    have hb := LinearMap.congr_fun (SupportedModTwoCohomology.extend_trans hLN hNP p) b
    exact ha.trans (he'.trans hb.symm)
  · rintro ⟨P, hKP, hLP, he⟩
    exact (CompactSupportCohomology.of_eq_iff X p
      (unionCompact U V K) (unionCompact U V L) a b).mpr
      ⟨unionCompact U V P, unionCompact_mono U V hKP, unionCompact_mono U V hLP, he⟩

end NoExoticSixSphere.OpenCoverCompactSupports
