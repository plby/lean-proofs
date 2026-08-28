import Mathlib.Topology.Covering.Quotient

/-!
# Covering neighbourhoods for possibly ineffective group actions

For a properly discontinuous action, a quotient map that is injective on
an open neighbourhood of one point is evenly covered at its image. The
action need not be free: its finite stabilizer fixes a smaller neighbourhood
pointwise. Sheets are indexed by the actual fibre, not by group elements.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularCoverTools

variable {G X Y : Type*} [Group G] [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction G X] [ContinuousConstSMul G X] {q : X → Y}

omit [TopologicalSpace Y] in
/-- Local injectivity makes the finite stabilizer ineffective on a suitably
small open neighbourhood, while proper discontinuity separates all other translates. -/
theorem exists_open_stabilizer_fixed_neighborhood
    [T2Space X] [LocallyCompactSpace X] [ProperlyDiscontinuousSMul G X]
    (hqG : ∀ {a b : X}, q a = q b ↔ a ∈ MulAction.orbit G b)
    (x : X) (V : Set X) (hV : IsOpen V) (hxV : x ∈ V) (hi : Set.InjOn q V) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧
      (∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g • x = x) ∧
      ∀ g : G, g • x = x → ∀ u ∈ U, g • u = u := by
  obtain ⟨N, hxN, hN⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  let H : Set G := {g | g • x = x}
  have hH : H.Finite := ProperlyDiscontinuousSMul.finite_stabilizer' G x
  let U := (interior N ∩ V) ∩ ⋂ g ∈ H, (g • ·) ⁻¹' V
  have hopen : IsOpen U := (isOpen_interior.inter hV).inter
    (hH.isOpen_biInter fun g _ => hV.preimage (continuous_const_smul g))
  have hxU : x ∈ U :=
    ⟨⟨mem_interior_iff_mem_nhds.mpr hxN, hxV⟩,
      mem_iInter₂.mpr fun g hg => by
        change g • x ∈ V
        rw [show g • x = x from hg]
        exact hxV⟩
  refine ⟨U, hopen, hxU, fun _ hu => hu.1.2, ?_, ?_⟩
  · rintro g ⟨_, ⟨u, hu, rfl⟩, hgu⟩
    exact hN g ⟨g • u, ⟨u, interior_subset hu.1.1, rfl⟩, interior_subset hgu.1.1⟩
  · intro g hg u hu
    exact hi ((mem_iInter₂.mp hu.2) g hg) hu.1.2 (hqG.mpr ⟨g, rfl⟩)

/-- Explicit disjoint sheets indexed by the actual fibre give an evenly
covered neighbourhood, even when the stabilizer is nontrivial. -/
theorem isEvenlyCovered_of_stabilizer_fixed_neighborhood
    (hq : IsOpenQuotientMap q)
    (hqG : ∀ {a b : X}, q a = q b ↔ a ∈ MulAction.orbit G b)
    (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) (hi : Set.InjOn q U)
    (htrans : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g • x = x)
    (hfix : ∀ g : G, g • x = x → ∀ u ∈ U, g • u = u) :
    IsEvenlyCovered q (q x) (q ⁻¹' {q x}) := by
  have hsmul (g : G) (u : X) : q (g • u) = q u := hqG.mpr ⟨g, rfl⟩
  let F := q ⁻¹' {q x}
  have : Nonempty F := ⟨⟨x, rfl⟩⟩
  have : Nonempty (Y → X) := ⟨fun _ => x⟩
  choose γ hγ using fun p : F => hqG.mp p.2
  let sheet (p : F) : Set X := (γ p • ·) '' U
  have hopen (p : F) : IsOpen (sheet p) := isOpenMap_smul (γ p) U hU
  have hmem (p : F) : (p : X) ∈ sheet p := ⟨x, hxU, hγ p⟩
  have himage (p : F) : q '' sheet p = q '' U := by
    simp only [sheet, image_image, hsmul]
  have hinj (p : F) : Set.InjOn q (sheet p) := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ he
    rw [hsmul, hsmul] at he
    exact congrArg (γ p • ·) (hi hu hv he)
  have hsurj (p : F) : Set.SurjOn q (sheet p) (q '' U) := (himage p).symm.subset
  have hopen_iff (p : F) {W : Set Y} (hW : W ⊆ q '' U) :
      IsOpen W ↔ IsOpen (q ⁻¹' W ∩ sheet p) := by
    constructor
    · intro ho
      exact (ho.preimage hq.continuous).inter (hopen p)
    · intro ho
      have he : q '' (q ⁻¹' W ∩ sheet p) = W := by
        rw [image_preimage_inter, himage]
        exact inter_eq_left.mpr hW
      rw [← he]
      exact hq.isOpenMap _ ho
  have hdisjoint : Pairwise (Function.onFun Disjoint sheet) := by
    intro p p' hne
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, huz⟩ ⟨v, hv, hvz⟩
    have he : γ p • u = γ p' • v := huz.trans hvz.symm
    have hku : ((γ p')⁻¹ * γ p) • u = v := by
      simpa only [mul_smul, inv_smul_smul] using congrArg ((γ p')⁻¹ • ·) he
    have hk := htrans ((γ p')⁻¹ * γ p) ⟨v, ⟨u, hu, hku⟩, hv⟩
    have he' : γ p • x = γ p' • x := by
      simpa only [mul_smul, smul_inv_smul] using congrArg (γ p' • ·) hk
    exact hne (Subtype.ext ((hγ p).symm.trans (he'.trans (hγ p'))))
  have hexhaustive : q ⁻¹' (q '' U) ⊆ ⋃ p : F, sheet p := by
    intro y hy
    obtain ⟨u, hu, huy⟩ := hy
    obtain ⟨g, hg⟩ := hqG.mp huy.symm
    let p : F := ⟨g • x, hsmul g x⟩
    have hγp : γ p • x = g • x := hγ p
    have hk : ((γ p)⁻¹ * g) • x = x := by
      rw [mul_smul, ← hγp, inv_smul_smul]
    have he : g • u = γ p • u := by
      simpa only [mul_smul, smul_inv_smul] using
        congrArg (γ p • ·) (hfix ((γ p)⁻¹ * g) hk u hu)
    exact mem_iUnion.mpr ⟨p, u, hu, he.symm.trans hg⟩
  have hdiscrete : IsDiscrete F := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro p hp
    let p' : F := ⟨p, hp⟩
    refine ⟨sheet p', hopen p', subset_antisymm ?_
      (singleton_subset_iff.mpr ⟨hmem p', hp⟩)⟩
    rintro z ⟨hzU, hzF⟩
    exact hinj p' hzU (hmem p') (hzF.trans hp.symm)
  let : DiscreteTopology F := isDiscrete_iff_discreteTopology.mp hdiscrete
  let t : Bundle.Trivialization F q :=
    IsOpen.trivializationDiscrete sheet (q '' U) (hq.isOpenMap U hU)
      hopen_iff hinj hsurj hdisjoint hexhaustive
  apply IsEvenlyCovered.of_trivialization (t := t)
  exact ⟨x, hxU, rfl⟩

/-- Proper discontinuity plus local quotient injectivity suffices for an
actual evenly covered neighbourhood; no cancellation or freeness is required. -/
theorem isEvenlyCovered_of_injective_open_neighborhood
    [T2Space X] [LocallyCompactSpace X] [ProperlyDiscontinuousSMul G X]
    (hq : IsOpenQuotientMap q)
    (hqG : ∀ {a b : X}, q a = q b ↔ a ∈ MulAction.orbit G b)
    (x : X) (V : Set X) (hV : IsOpen V) (hxV : x ∈ V) (hi : Set.InjOn q V) :
    IsEvenlyCovered q (q x) (q ⁻¹' {q x}) := by
  obtain ⟨U, hU, hxU, hUV, htrans, hfix⟩ :=
    exists_open_stabilizer_fixed_neighborhood hqG x V hV hxV hi
  exact isEvenlyCovered_of_stabilizer_fixed_neighborhood hq hqG x U hU hxU
    (hi.mono hUV) htrans hfix

end Wikipedia.HopfProblem.SpecialPeriods.ModularCoverTools
