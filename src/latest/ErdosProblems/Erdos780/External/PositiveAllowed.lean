import ErdosProblems.Erdos780.External.PositiveTarget
import ErdosProblems.Erdos780.External.AllowedFaces
import ErdosProblems.Erdos780.External.LabelAllowed
import ErdosProblems.Erdos780.External.FinsetOrientation
import ErdosProblems.Erdos780.External.SignedMap
import ErdosProblems.Erdos780.External.SignedSphereLength
import ErdosProblems.Erdos780.External.LabelChainMap

/-!
Allowed positive target chains and the reduced labeling map.
-/

namespace PositiveAllowed

open TargetChains PositiveTarget AllowedFaces LabelAllowed SignedSphere
open ZpTuckerScratch

noncomputable section

variable {p n m alpha k : ℕ} [NeZero p]

abbrev SourceVertex := NonzeroSignedVector p n
abbrev TargetVertex := AllowedFaces.Label p m

noncomputable local instance targetOrder :
    LinearOrder (TargetVertex (p := p) (m := m)) :=
  LabelChainMap.targetLinearOrder

def listAt {X : Type*}
    (lab : X → TargetVertex (p := p) (m := m)) (l : List X)
    (i : Fin l.length) : TargetVertex (p := p) (m := m) :=
  lab (l.get i)

def listFace {X : Type*}
    (lab : X → TargetVertex (p := p) (m := m)) (l : List X) :
    Finset (TargetVertex (p := p) (m := m)) :=
  Finset.univ.image (listAt lab l)

theorem labelList_eq_map_univ_general {X : Type*}
    (lab : X → TargetVertex (p := p) (m := m)) (l : List X) :
    TargetBridge.labelList lab l =
      TargetChains.map (listAt lab l)
        (Finsupp.single (Finset.univ : Finset (Fin l.length)) 1) := by
  apply (TargetChains.toExterior ℤ (TargetVertex (p := p) (m := m))).injective
  rw [TargetBridge.labelList_eq_ιMulti,
    TargetChains.toExterior_map_single]
  change ExteriorAlgebra.ιMulti ℤ l.length
      (fun i ↦ Finsupp.single (lab (l.get i)) 1) =
    ExteriorAlgebra.map (TargetChains.vertexMap (listAt lab l))
      ((TargetChains.vertexBasis ℤ (Fin l.length)).ExteriorAlgebra Finset.univ)
  have hcard : (Finset.univ : Finset (Fin l.length)).card = l.length := by simp
  rw [ExteriorAlgebra.basis_apply_ofCard
      (TargetChains.vertexBasis ℤ (Fin l.length)) hcard,
    ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, TargetChains.vertexBasis,
    Finsupp.coe_basisSingleOne, TargetChains.vertexMap_single, listAt]
  congr 1
  apply congrArg lab
  apply congrArg l.get
  apply Fin.ext
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_apply, Fin.sort_univ]

theorem labelList_eq_signed_single_general {X : Type*}
    (lab : X → TargetVertex (p := p) (m := m)) (l : List X)
    (hinj : Function.Injective (listAt lab l)) :
    TargetBridge.labelList lab l =
      Finsupp.single (listFace lab l)
        ((Finset.imageSign (Finset.univ : Finset (Fin l.length))
          (listAt lab l) hinj.injOn : ℤˣ) : ℤ) := by
  rw [labelList_eq_map_univ_general]
  let img : Finset (TargetVertex (p := p) (m := m)) :=
    @Finset.image (Fin l.length) (TargetVertex (p := p) (m := m))
      (@LinearOrder.toDecidableEq _ targetOrder)
      (listAt lab l) Finset.univ
  have himg : img = listFace lab l := by
    ext v
    simp [img, listFace]
  rw [← himg]
  exact TargetChains.map_single_of_injOn (listAt lab l)
    (Finset.univ : Finset (Fin l.length)) hinj.injOn

/- The exterior label of a list is the normalized finite-image map from
the canonically ordered `Fin l.length` simplex. -/
theorem labelList_eq_map_univ
    (lab : SourceVertex (p := p) (n := n) → TargetVertex (p := p) (m := m))
    (l : List (SourceVertex (p := p) (n := n))) :
    TargetBridge.labelList lab l =
      TargetChains.map (LabelAllowed.labelAt lab l)
        (Finsupp.single (Finset.univ : Finset (Fin l.length)) 1) := by
  apply (TargetChains.toExterior ℤ (TargetVertex (p := p) (m := m))).injective
  rw [TargetBridge.labelList_eq_ιMulti,
    TargetChains.toExterior_map_single]
  change ExteriorAlgebra.ιMulti ℤ l.length
      (fun i ↦ Finsupp.single (lab (l.get i)) 1) =
    ExteriorAlgebra.map (TargetChains.vertexMap (LabelAllowed.labelAt lab l))
      ((TargetChains.vertexBasis ℤ (Fin l.length)).ExteriorAlgebra Finset.univ)
  have hcard : (Finset.univ : Finset (Fin l.length)).card = l.length := by simp
  rw [ExteriorAlgebra.basis_apply_ofCard
      (TargetChains.vertexBasis ℤ (Fin l.length)) hcard,
    ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, TargetChains.vertexBasis,
    Finsupp.coe_basisSingleOne, TargetChains.vertexMap_single,
    LabelAllowed.labelAt]
  congr 1
  apply congrArg lab
  apply congrArg l.get
  apply Fin.ext
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_apply, Fin.sort_univ]

/- A repeated target label kills the exterior simplex. -/
theorem labelList_eq_zero_of_not_injective
    (lab : SourceVertex (p := p) (n := n) → TargetVertex (p := p) (m := m))
    (l : List (SourceVertex (p := p) (n := n)))
    (hinj : ¬ Function.Injective (LabelAllowed.labelAt lab l)) :
    TargetBridge.labelList lab l = 0 := by
  exact TargetBridge.labelList_eq_zero_of_repeated lab l hinj

/- In the injective case the exterior label is one oriented copy of its
finite label image. -/
theorem labelList_eq_signed_single_of_injective
    (lab : SourceVertex (p := p) (n := n) → TargetVertex (p := p) (m := m))
    (l : List (SourceVertex (p := p) (n := n)))
    (hinj : Function.Injective (LabelAllowed.labelAt lab l)) :
    TargetBridge.labelList lab l =
      Finsupp.single (LabelAllowed.labelFace lab l)
        ((Finset.imageSign (Finset.univ : Finset (Fin l.length))
          (LabelAllowed.labelAt lab l) hinj.injOn : ℤˣ) : ℤ) := by
  rw [labelList_eq_map_univ]
  let img : Finset (TargetVertex (p := p) (m := m)) :=
    @Finset.image (Fin l.length) (TargetVertex (p := p) (m := m))
      (@LinearOrder.toDecidableEq _ targetOrder)
      (LabelAllowed.labelAt lab l) Finset.univ
  have himg : img = LabelAllowed.labelFace lab l := by
    ext v
    simp [img, LabelAllowed.labelFace]
  rw [← himg]
  exact TargetChains.map_single_of_injOn (LabelAllowed.labelAt lab l)
    (Finset.univ : Finset (Fin l.length)) hinj.injOn

/-! ## The positive allowed submodules -/

def allowedPositiveChains (p m alpha : ℕ) [NeZero p] :
    Submodule ℤ
      (PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))) :=
  (AllowedFaces.allowedChains ℤ p m alpha).comap
    (TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m)))

abbrev Chain (p m alpha : ℕ) [NeZero p] :=
  allowedPositiveChains p m alpha

def allowedPositiveDegree (p m alpha q : ℕ) [NeZero p] :
    Submodule ℤ
      (PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))) :=
  (AllowedFaces.allowedDegreeChains ℤ p m alpha q).comap
    (TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m)))

theorem labelLists_basis_mem_allowedPositive
    (hp : p.Prime)
    (lab : SourceVertex (p := p) (n := n) → TargetVertex (p := p) (m := m))
    (hadm : IsAlphaAdmissible alpha lab)
    (l : List (SourceVertex (p := p) (n := n)))
    (hl : IsStrictFlag l) (hlne : l ≠ []) :
    PositiveTarget.labelLists lab (SourceFlags.basis l) ∈
      allowedPositiveChains p m alpha := by
  change TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m))
      (PositiveTarget.labelLists lab (SourceFlags.basis l)) ∈
        AllowedFaces.allowedChains ℤ p m alpha
  rw [PositiveTarget.positiveInclusion_labelLists_basis_of_nonempty lab l hlne]
  by_cases hinj : Function.Injective (LabelAllowed.labelAt lab l)
  · rw [labelList_eq_signed_single_of_injective lab l hinj]
    rw [AllowedFaces.mem_allowedChains]
    intro s hs
    by_cases hsf : s = LabelAllowed.labelFace lab l
    · subst s
      exact LabelAllowed.labelFace_isAllowed hp lab hadm l hl hinj
    · exfalso
      apply (Finsupp.mem_support_iff.mp hs)
      simp [Finsupp.single_apply, hsf]
  · rw [labelList_eq_zero_of_not_injective lab l hinj]
    exact (AllowedFaces.allowedChains ℤ p m alpha).zero_mem

theorem labelLists_basis_mem_allowedPositiveDegree
    (hp : p.Prime)
    (lab : SourceVertex (p := p) (n := n) → TargetVertex (p := p) (m := m))
    (hadm : IsAlphaAdmissible alpha lab)
    (l : List (SourceVertex (p := p) (n := n)))
    (hl : SignedSphere.ExactStrictFlag k l) :
    PositiveTarget.labelLists lab (SourceFlags.basis l) ∈
      allowedPositiveDegree p m alpha (k - 1) := by
  by_cases hlne : l = []
  · subst l
    simp only [PositiveTarget.labelLists_empty]
    exact (allowedPositiveDegree p m alpha (k - 1)).zero_mem
  · change TargetChains.positiveInclusion ℤ
        (TargetVertex (p := p) (m := m))
        (PositiveTarget.labelLists lab (SourceFlags.basis l)) ∈
          AllowedFaces.allowedDegreeChains ℤ p m alpha (k - 1)
    rw [PositiveTarget.positiveInclusion_labelLists_basis_of_nonempty lab l hlne]
    by_cases hinj : Function.Injective (LabelAllowed.labelAt lab l)
    · rw [labelList_eq_signed_single_of_injective lab l hinj]
      change Finsupp.single (LabelAllowed.labelFace lab l) _ ∈
        Finsupp.supported ℤ ℤ
          {s : Finset (TargetVertex (p := p) (m := m)) |
            IsAllowed alpha s ∧ s.card = k - 1 + 1}
      rw [Finsupp.mem_supported]
      intro s hs
      by_cases hsf : s = LabelAllowed.labelFace lab l
      · subst s
        constructor
        · exact LabelAllowed.labelFace_isAllowed hp lab hadm l hl.1 hinj
        · rw [LabelAllowed.labelFace,
              Finset.card_image_of_injective _ hinj]
          simp only [Finset.card_univ, Fintype.card_fin]
          have hlen := hl.2
          have hpos : 0 < l.length := Nat.pos_of_ne_zero (by
            intro hzero
            apply hlne
            exact List.length_eq_zero_iff.mp hzero)
          omega
      · exfalso
        apply (Finsupp.mem_support_iff.mp hs)
        simp [Finsupp.single_apply, hsf]
    · rw [labelList_eq_zero_of_not_injective lab l hinj]
      exact (AllowedFaces.allowedDegreeChains ℤ p m alpha (k - 1)).zero_mem

theorem labelLists_mem_allowedPositive_of_supported
    (hp : p.Prime)
    (lab : SourceVertex (p := p) (n := n) → TargetVertex (p := p) (m := m))
    (hadm : IsAlphaAdmissible alpha lab)
    {c : SourceFlags.Chain (SourceVertex (p := p) (n := n))}
    (hc : SignedSphere.Supported
      (fun l ↦ IsStrictFlag l ∧ l ≠ []) c) :
    PositiveTarget.labelLists lab c ∈ allowedPositiveChains p m alpha := by
  let P : List (SourceVertex (p := p) (n := n)) → Prop :=
    fun l ↦ IsStrictFlag l ∧ l ≠ []
  have hc' : c ∈ Finsupp.supported ℤ ℤ {l | P l} := by
    rw [Finsupp.mem_supported]
    intro l hl
    exact hc l (Finsupp.mem_support_iff.mp hl)
  have hle : Finsupp.supported ℤ ℤ {l | P l} ≤
      (allowedPositiveChains p m alpha).comap
        (PositiveTarget.labelLists lab) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.2
    rintro _ ⟨l, hl, rfl⟩
    exact labelLists_basis_mem_allowedPositive hp lab hadm l hl.1 hl.2
  exact hle hc'

theorem labelLists_mem_allowedPositiveDegree_of_supported_exact
    (hp : p.Prime)
    (lab : SourceVertex (p := p) (n := n) → TargetVertex (p := p) (m := m))
    (hadm : IsAlphaAdmissible alpha lab)
    {c : SourceFlags.Chain (SourceVertex (p := p) (n := n))}
    (hc : SignedSphere.Supported (SignedSphere.ExactStrictFlag k) c) :
    PositiveTarget.labelLists lab c ∈
      allowedPositiveDegree p m alpha (k - 1) := by
  have hc' : c ∈ Finsupp.supported ℤ ℤ
      {l | SignedSphere.ExactStrictFlag k l} := by
    rw [Finsupp.mem_supported]
    intro l hl
    exact hc l (Finsupp.mem_support_iff.mp hl)
  have hle : Finsupp.supported ℤ ℤ
        {l | SignedSphere.ExactStrictFlag k l} ≤
      (allowedPositiveDegree p m alpha (k - 1)).comap
        (PositiveTarget.labelLists lab) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.2
    rintro _ ⟨l, hl, rfl⟩
    exact labelLists_basis_mem_allowedPositiveDegree hp lab hadm l hl
  exact hle hc'

/-! ## Boundary closure of the allowed target complex -/

theorem labelList_id_mem_allowed_of_subset
    {s : Finset (TargetVertex (p := p) (m := m))}
    (hs : IsAllowed alpha s)
    (l : List (TargetVertex (p := p) (m := m)))
    (hl : l.toFinset ⊆ s) :
    TargetBridge.labelList id l ∈ AllowedFaces.allowedChains ℤ p m alpha := by
  by_cases hinj : Function.Injective (listAt id l)
  · rw [labelList_eq_signed_single_general id l hinj]
    rw [AllowedFaces.mem_allowedChains]
    intro t ht
    by_cases htf : t = listFace id l
    · subst t
      apply hs.mono
      intro v hv
      have hv' : ∃ i : Fin l.length, l.get i = v := by
        simpa [listFace, listAt] using hv
      have hvl : v ∈ l := by
        have h := (List.exists_mem_iff_get
          (l := l) (p := fun x ↦ x = v)).2 hv'
        simpa using h
      exact hl (by simpa using hvl)
    · exfalso
      apply (Finsupp.mem_support_iff.mp ht)
      simp [htf]
  · rw [TargetBridge.labelList_eq_zero_of_repeated id l hinj]
    exact (AllowedFaces.allowedChains ℤ p m alpha).zero_mem

theorem labelLists_id_mem_allowed_of_supported_subset
    {s : Finset (TargetVertex (p := p) (m := m))}
    (hs : IsAllowed alpha s)
    {c : SourceFlags.Chain (TargetVertex (p := p) (m := m))}
    (hc : SignedSphere.Supported (fun l ↦ l.toFinset ⊆ s) c) :
    TargetBridge.labelLists id c ∈ AllowedFaces.allowedChains ℤ p m alpha := by
  have hc' : c ∈ Finsupp.supported ℤ ℤ {l | l.toFinset ⊆ s} := by
    rw [Finsupp.mem_supported]
    intro l hl
    exact hc l (Finsupp.mem_support_iff.mp hl)
  have hle : Finsupp.supported ℤ ℤ {l | l.toFinset ⊆ s} ≤
      (AllowedFaces.allowedChains ℤ p m alpha).comap
        (TargetBridge.labelLists id) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.2
    rintro _ ⟨l, hl, rfl⟩
    change TargetBridge.labelLists id (SourceFlags.basis l) ∈
      AllowedFaces.allowedChains ℤ p m alpha
    rw [TargetBridge.labelLists_basis]
    exact labelList_id_mem_allowed_of_subset hs l hl
  exact hle hc'

theorem boundary_single_mem_allowed
    (s : Finset (TargetVertex (p := p) (m := m)))
    (hs : IsAllowed alpha s) :
    TargetChains.boundary ℤ (TargetVertex (p := p) (m := m))
        (Finsupp.single s 1) ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  let l : List (TargetVertex (p := p) (m := m)) := s.sort (· ≤ ·)
  have hlfin : l.toFinset = s := by
    exact Finset.sort_toFinset s (· ≤ ·)
  have hlinj : Function.Injective (listAt id l) := by
    have hget :=
      List.nodup_iff_injective_get.mp (Finset.sort_nodup s (· ≤ ·))
    intro i j hij
    apply hget
    simpa [listAt] using hij
  let u : ℤˣ := Finset.imageSign (Finset.univ : Finset (Fin l.length))
    (listAt id l) hlinj.injOn
  have hface : listFace id l = s := by
    unfold listFace
    rw [← hlfin]
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, listAt, id_eq,
      List.mem_toFinset]
    constructor
    · rintro ⟨i, rfl⟩
      exact List.get_mem l i
    · intro hv
      let i : Fin l.length :=
        ⟨l.idxOf v, List.idxOf_lt_length_iff.mpr hv⟩
      refine ⟨i, ?_⟩
      simpa only [List.get_eq_getElem, i] using
        (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv))
  have hlabel : TargetBridge.labelList id l =
      (u : ℤ) • Finsupp.single s (1 : ℤ) := by
    rw [labelList_eq_signed_single_general id l hlinj, hface]
    simp [u]
  have hsupport : SignedSphere.Supported (fun q ↦ q.toFinset ⊆ s)
      (SourceFlags.boundaryBasis l) := by
    refine SignedSphere.Supported.mono
      (SignedSphere.boundaryBasis_supported_terms l) ?_
    intro q hq
    rw [← hlfin]
    intro v hv
    simp only [List.mem_toFinset] at hv ⊢
    exact hq.1.subset hv
  have hb : TargetChains.boundary ℤ (TargetVertex (p := p) (m := m))
      (TargetBridge.labelList id l) ∈
        AllowedFaces.allowedChains ℤ p m alpha := by
    rw [TargetBridge.boundary_labelList]
    exact labelLists_id_mem_allowed_of_supported_subset hs hsupport
  rw [hlabel, map_smul] at hb
  have hbinv := (AllowedFaces.allowedChains ℤ p m alpha).smul_mem
    ((↑(u⁻¹) : ℤ)) hb
  simpa [smul_smul] using hbinv

theorem boundary_mem_allowed
    {c : TargetChains.FullChain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ AllowedFaces.allowedChains ℤ p m alpha) :
    TargetChains.boundary ℤ (TargetVertex (p := p) (m := m)) c ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  rw [AllowedFaces.allowedChains_eq_span] at hc
  let M : Submodule ℤ (TargetChains.FullChain ℤ
      (TargetVertex (p := p) (m := m))) :=
    (AllowedFaces.allowedChains ℤ p m alpha).comap
      (TargetChains.boundary ℤ (TargetVertex (p := p) (m := m)))
  have hle : Submodule.span ℤ
      ((fun s : Finset (TargetVertex (p := p) (m := m)) ↦
          Finsupp.single s (1 : ℤ)) '' AllowedFaces.allowedFaceSet p m alpha) ≤ M := by
    apply Submodule.span_le.2
    rintro _ ⟨s, hs, rfl⟩
    exact boundary_single_mem_allowed s hs
  exact hle hc

theorem projectPositive_mem_allowed
    {c : TargetChains.FullChain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ AllowedFaces.allowedChains ℤ p m alpha) :
    TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m))
        (TargetChains.projectPositive ℤ (TargetVertex (p := p) (m := m)) c) ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  rw [TargetChains.positiveInclusion_projectPositive]
  apply (AllowedFaces.allowedChains ℤ p m alpha).sub_mem hc
  rw [AllowedFaces.mem_allowedChains]
  intro s hs
  by_cases hsempty : s = ∅
  · subst s
    exact AllowedFaces.isAllowed_empty p m alpha
  · exfalso
    apply (Finsupp.mem_support_iff.mp hs)
    simp [hsempty]

theorem reducedBoundary_mem_allowed
    {c : PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ allowedPositiveChains p m alpha) :
    PositiveTarget.boundary ℤ (TargetVertex (p := p) (m := m)) c ∈
      allowedPositiveChains p m alpha := by
  change TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m))
      (TargetChains.projectPositive ℤ (TargetVertex (p := p) (m := m))
        (TargetChains.boundary ℤ (TargetVertex (p := p) (m := m))
          (TargetChains.positiveInclusion ℤ
            (TargetVertex (p := p) (m := m)) c))) ∈
    AllowedFaces.allowedChains ℤ p m alpha
  apply projectPositive_mem_allowed
  apply boundary_mem_allowed
  exact hc

noncomputable def boundary (p m alpha : ℕ) [NeZero p] :
    Chain p m alpha →ₗ[ℤ] Chain p m alpha where
  toFun c := ⟨PositiveTarget.boundary ℤ
    (TargetVertex (p := p) (m := m)) c.1,
    reducedBoundary_mem_allowed c.2⟩
  map_add' c d := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' z c := by
    apply Subtype.ext
    exact map_smul _ _ _

@[simp]
theorem boundary_coe (c : Chain p m alpha) :
    ((boundary p m alpha c : Chain p m alpha) :
      PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))) =
      PositiveTarget.boundary ℤ (TargetVertex (p := p) (m := m)) c :=
  rfl

theorem boundary_boundary (c : Chain p m alpha) :
    boundary p m alpha (boundary p m alpha c) = 0 := by
  apply Subtype.ext
  exact PositiveTarget.boundary_boundary ℤ
    (TargetVertex (p := p) (m := m)) c

/-! ## The target cyclic action on the restricted complex -/

def targetShift (a : ZMod p) (v : TargetVertex (p := p) (m := m)) :
    TargetVertex (p := p) (m := m) :=
  (a + v.1, v.2)

theorem targetShift_injective (a : ZMod p) :
    Function.Injective (targetShift (m := m) a) := by
  intro x y h
  apply Prod.ext
  · exact add_left_cancel (congrArg Prod.fst h)
  · simpa [targetShift] using congrArg Prod.snd h

theorem fiber_image_targetShift (a : ZMod p)
    (s : Finset (TargetVertex (p := p) (m := m))) (j : Fin m) :
    AllowedFaces.fiber (s.image (targetShift a)) j =
      (AllowedFaces.fiber s j).image (targetShift a) := by
  ext v
  simp only [AllowedFaces.fiber, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨w, hw, hwv⟩, hvj⟩
    refine ⟨w, ⟨hw, ?_⟩, hwv⟩
    simpa [← hwv, targetShift] using hvj
  · rintro ⟨w, ⟨hw, hwj⟩, hwv⟩
    refine ⟨⟨w, hw, hwv⟩, ?_⟩
    simpa [← hwv, targetShift] using hwj

theorem IsAllowed.image_targetShift (hs : IsAllowed alpha s) (a : ZMod p) :
    IsAllowed alpha (s.image (targetShift (m := m) a)) := by
  intro j
  rw [fiber_image_targetShift,
    Finset.card_image_of_injective _ (targetShift_injective a)]
  exact hs j

theorem targetMap_mem_allowed (a : ZMod p)
    {c : TargetChains.FullChain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ AllowedFaces.allowedChains ℤ p m alpha) :
    TargetChains.map (targetShift (m := m) a) c ∈
      AllowedFaces.allowedChains ℤ p m alpha := by
  rw [AllowedFaces.allowedChains_eq_span] at hc
  let M : Submodule ℤ (TargetChains.FullChain ℤ
      (TargetVertex (p := p) (m := m))) :=
    (AllowedFaces.allowedChains ℤ p m alpha).comap
      (TargetChains.map (targetShift (m := m) a))
  have hle : Submodule.span ℤ
      ((fun s : Finset (TargetVertex (p := p) (m := m)) ↦
          Finsupp.single s (1 : ℤ)) '' AllowedFaces.allowedFaceSet p m alpha) ≤ M := by
    apply Submodule.span_le.2
    rintro _ ⟨s, hs, rfl⟩
    change TargetChains.map (targetShift (m := m) a)
      (Finsupp.single s (1 : ℤ)) ∈
        AllowedFaces.allowedChains ℤ p m alpha
    rw [TargetChains.map_single_of_injOn (targetShift a) s
      (targetShift_injective a).injOn]
    rw [AllowedFaces.mem_allowedChains]
    intro t ht
    by_cases hteq : t =
        @Finset.image _ _ (@LinearOrder.toDecidableEq _ targetOrder)
          (targetShift a) s
    · subst t
      change IsAllowed alpha s at hs
      have himg :
          @Finset.image _ _ (@LinearOrder.toDecidableEq _ targetOrder)
              (targetShift a) s =
            s.image (targetShift a) := by
        ext v
        simp
      rw [himg]
      exact PositiveAllowed.IsAllowed.image_targetShift hs a
    · exfalso
      apply (Finsupp.mem_support_iff.mp ht)
      rw [Finsupp.single_apply]
      split
      · rename_i h
        exact (hteq h.symm).elim
      · rfl
  exact hle hc

theorem reducedTargetMap_mem_allowed (a : ZMod p)
    {c : PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))}
    (hc : c ∈ allowedPositiveChains p m alpha) :
    PositiveTarget.map (targetShift (m := m) a) c ∈
      allowedPositiveChains p m alpha := by
  change TargetChains.positiveInclusion ℤ (TargetVertex (p := p) (m := m))
      (TargetChains.projectPositive ℤ (TargetVertex (p := p) (m := m))
        (TargetChains.map (targetShift (m := m) a)
          (TargetChains.positiveInclusion ℤ
            (TargetVertex (p := p) (m := m)) c))) ∈
    AllowedFaces.allowedChains ℤ p m alpha
  apply projectPositive_mem_allowed
  apply targetMap_mem_allowed
  exact hc

noncomputable def targetAct (a : ZMod p) :
    Chain p m alpha →ₗ[ℤ] Chain p m alpha where
  toFun c := ⟨PositiveTarget.map (targetShift (m := m) a) c.1,
    reducedTargetMap_mem_allowed a c.2⟩
  map_add' c d := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' z c := by
    apply Subtype.ext
    exact map_smul _ _ _

@[simp]
theorem targetAct_coe (a : ZMod p) (c : Chain p m alpha) :
    ((targetAct (alpha := alpha) a c : Chain p m alpha) :
      PositiveTarget.Chain ℤ (TargetVertex (p := p) (m := m))) =
      PositiveTarget.map (targetShift (m := m) a) c :=
  rfl

theorem targetAct_boundary (a : ZMod p) (c : Chain p m alpha) :
    targetAct (alpha := alpha) a (boundary p m alpha c) =
      boundary p m alpha (targetAct (alpha := alpha) a c) := by
  apply Subtype.ext
  change TargetChains.reducedMap (targetShift (m := m) a)
      (TargetChains.reducedBoundary ℤ (TargetVertex (p := p) (m := m)) c.1) =
    TargetChains.reducedBoundary ℤ (TargetVertex (p := p) (m := m))
      (TargetChains.reducedMap (targetShift (m := m) a) c.1)
  exact TargetChains.reducedMap_reducedBoundary
    (targetShift (m := m) a) c.1

end

end PositiveAllowed
