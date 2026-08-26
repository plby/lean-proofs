import ErdosProblems.Erdos538.ReindexedKernelCap

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

noncomputable section

/-- The `(d+1)`-facet of a `(d+2)`-parent obtained by omitting `x`. -/
def parentFacet {m d : ℕ} (T : Finset (Fin m))
    (hT : T.card = d + 2) (x : T) : UniformChildren m d := by
  refine ⟨T.erase x.1, ?_⟩
  rw [Finset.card_erase_of_mem x.2, hT]
  omega

/-- The subtype of an erased parent is canonically the set of parent points
other than the omitted point. -/
def eraseSubtypeEquiv {α : Type*} [DecidableEq α]
    (T : Finset α) (x : T) :
    (T.erase x.1 : Set α) ≃ {y : T // y ≠ x} where
  toFun y :=
    ⟨⟨y.1, Finset.mem_of_mem_erase y.2⟩, by
      intro h
      have := congrArg (fun z : T => z.1) h
      exact (Finset.mem_erase.mp y.2).1 this⟩
  invFun y :=
    ⟨y.1.1, Finset.mem_erase.mpr ⟨by
      intro h
      apply y.2
      exact Subtype.ext h, y.1.2⟩⟩
  left_inv y := Subtype.ext rfl
  right_inv y := Subtype.ext (Subtype.ext rfl)

/-- A child is selected by a global labeling when that labeling lies in the
safe favorable range embedded for the child. -/
def IsRangeSelected
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (ω : GlobalSample K m d) (S : UniformChildren m d) : Prop :=
  ω ∈ Set.range (safeGlobalEmbedding S)

/-- Omitted points whose facets are range-selected in one parent. -/
def selectedOmissions
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (ω : GlobalSample K m d)
    (T : Finset (Fin m)) (hT : T.card = d + 2) : Finset T := by
  classical
  exact Finset.univ.filter fun x =>
    IsRangeSelected ω (parentFacet T hT x)

/-- A safe global-range witness for one facet produces exactly the abstract
selected certificate required by the reindexed kernel cap theorem. -/
def rangeSelectedCertificate
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (ω : GlobalSample K m d)
    (T : Finset (Fin m)) (hT : T.card = d + 2) (x : T)
    (hx : IsRangeSelected ω (parentFacet T hT x)) :
    SelectedCertificate K d (fun y : T => ω y.1) x := by
  let S := parentFacet T hT x
  let gp : SafeGlobalParam K d (m - (d + 1)) := Classical.choose hx
  have hgp : safeGlobalEmbedding S gp = ω := Classical.choose_spec hx
  let ix : Fin (m - (d + 1)) :=
    (outsideEquiv S).symm ⟨x.1, by
      simp [S, parentFacet]⟩
  refine
    { param := gp.1
      childIndex := (childEquiv S).trans (eraseSubtypeEquiv T x)
      outsideCoord := gp.2.1 ix
      child_label := ?_
      outside_label := ?_
      safe := gp.2.2 ix }
  · intro o
    have h := congrFun hgp (childEquiv S o).1
    have hchild := assembleGlobal_child S (safeGlobalParamToSample gp) o
    have hval : (((childEquiv S).trans (eraseSubtypeEquiv T x)) o).1.1 =
        (childEquiv S o).1 := rfl
    change ω (childEquiv S o).1 =
      ((goodParamToSample gp.1).1 o, (goodParamToSample gp.1).2 o)
    rw [← h]
    exact hchild
  · have h := congrFun hgp x.1
    have hix : (outsideEquiv S ix).1 = x.1 := by
      exact congrArg Subtype.val ((outsideEquiv S).apply_symm_apply
        ⟨x.1, by simp [S, parentFacet]⟩)
    have hout := assembleGlobal_outside S (safeGlobalParamToSample gp) ix
    change ω x.1 = outsideActual gp.1 (gp.2.1 ix)
    rw [← h]
    rw [← hix]
    change assembleGlobal S (safeGlobalParamToSample gp)
      (outsideEquiv S ix).1 = outsideActual gp.1 (gp.2.1 ix)
    rw [hout]
    rfl

/-- Every `(d+2)`-parent contains at most two range-selected facets. -/
theorem selectedOmissions_card_le_two
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (ω : GlobalSample K m d)
    (T : Finset (Fin m)) (hT : T.card = d + 2)
    (hd : 0 < d) (htwo : (2 : K) ≠ 0) :
    (selectedOmissions ω T hT).card ≤ 2 := by
  classical
  let selected := selectedOmissions ω T hT
  have hcard : Fintype.card T = d + 2 := by simpa using hT
  let cert : ∀ x ∈ selected,
      SelectedCertificate K d (fun y : T => ω y.1) x := by
    intro x hx
    have hx' : x ∈ selectedOmissions ω T hT := hx
    exact rangeSelectedCertificate ω T hT x
      (Finset.mem_filter.mp hx').2
  exact selectedCertificates_card_le_two
    (fun y : T => ω y.1) selected cert hd hcard htwo

/-- The actual finite family of range-selected children. -/
def rangeSelectedFamily
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (ω : GlobalSample K m d) : Finset (UniformChildren m d) := by
  classical
  exact Finset.univ.filter (IsRangeSelected ω)

/-- The range-selected family obeys the multiplicity-aware facet cap two in
every parent. -/
theorem rangeSelectedFamily_cap_two
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (ω : GlobalSample K m d)
    (hd : 0 < d) (htwo : (2 : K) ≠ 0)
    (T : Finset (Fin m)) (hT : T.card = d + 2) :
    (Finset.univ.filter fun x : T =>
      parentFacet T hT x ∈ rangeSelectedFamily ω).card ≤ 2 := by
  classical
  have heq : (Finset.univ.filter fun x : T =>
      parentFacet T hT x ∈ rangeSelectedFamily ω) =
      selectedOmissions ω T hT := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      rangeSelectedFamily, selectedOmissions]
  rw [heq]
  exact selectedOmissions_card_le_two ω T hT hd htwo

/-- Density and cap combine: one safe-kernel palette retains at least a
`1/(16q)` share of all children and has at most two facets in every parent. -/
theorem exists_dense_rangeSelectedFamily
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (hd : 0 < d) (htwo : (2 : K) ≠ 0)
    (hqsize : 2 * (d + 1) ≤ Fintype.card K)
    (houtside : 2 * (m - (d + 1)) ≤ (Nat.card K) ^ 2) :
    ∃ F : Finset (UniformChildren m d),
      Fintype.card (UniformChildren m d) ≤
        (16 * Fintype.card K) * F.card ∧
      ∀ T : Finset (Fin m), ∀ hT : T.card = d + 2,
        (Finset.univ.filter fun x : T => parentFacet T hT x ∈ F).card ≤ 2 := by
  classical
  obtain ⟨ω, hmass⟩ := exists_globalSample_many_safe_children
    hd hqsize houtside
  refine ⟨rangeSelectedFamily ω, ?_, ?_⟩
  · have hF : rangeSelectedFamily ω =
        Finset.univ.filter fun S =>
          ω ∈ Set.range (safeGlobalEmbedding S) := by
      ext S
      simp only [rangeSelectedFamily, IsRangeSelected]
    rw [hF]
    exact hmass
  · intro T hT
    exact rangeSelectedFamily_cap_two ω hd htwo T hT

end

end Erdos538.IsotropicKernel
