import ErdosProblems.Erdos780.External.SourceFlags
import ErdosProblems.Erdos780.External.TargetChains
import ErdosProblems.Erdos780.External.ZpTuckerDefs

/-!
The normalized simplicial chain map induced by a `Z_p`-Tucker labeling.

Source simplices are strict flags, represented by lists in their flag order.
The target is the exterior-algebra chain model: repeated labels therefore
normalize to zero, while a permutation of labels contributes its usual sign.
-/

namespace LabelChainMap

open scoped BigOperators

open ZpTuckerScratch

noncomputable section

abbrev SourceVertex (p n : ℕ) := NonzeroSignedVector p n
abbrev TargetVertex (p m : ℕ) := ZMod p × Fin m
abbrev TargetChain (p m : ℕ) := TargetChains.FullChain ℤ (TargetVertex p m)
abbrev TargetExterior (p m : ℕ) :=
  ExteriorAlgebra ℤ (TargetVertex p m →₀ ℤ)

variable {p n m alpha : ℕ} [NeZero p]

noncomputable local instance targetMax : Max (TargetVertex p m) where
  max x y :=
    let e := Fintype.equivFin (TargetVertex p m)
    e.symm (max (e x) (e y))

noncomputable local instance targetMin : Min (TargetVertex p m) where
  min x y :=
    let e := Fintype.equivFin (TargetVertex p m)
    e.symm (min (e x) (e y))

noncomputable local instance targetLinearOrder :
    LinearOrder (TargetVertex p m) :=
  let e := Fintype.equivFin (TargetVertex p m)
  LinearOrder.lift e e.injective
    (by
      intro x y
      change e (e.symm (max (e x) (e y))) = _
      exact e.apply_symm_apply _)
    (by
      intro x y
      change e (e.symm (min (e x) (e y))) = _
      exact e.apply_symm_apply _)

/-- Exterior product of the labeled vertices, in source-flag order. -/
def exteriorFlag
    {ι : Type*} (lab : ι → TargetVertex p m) :
    List ι → TargetExterior p m
  | [] => 1
  | x :: xs =>
      ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) * exteriorFlag lab xs

@[simp] theorem exteriorFlag_nil
    (lab : SourceVertex p n → TargetVertex p m) :
    exteriorFlag lab [] = 1 := rfl

@[simp] theorem exteriorFlag_cons
    (lab : SourceVertex p n → TargetVertex p m)
    (x : SourceVertex p n) (xs : List (SourceVertex p n)) :
    exteriorFlag lab (x :: xs) =
      ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) * exteriorFlag lab xs := rfl

/-- A source flag list, normalized in the target exterior basis. -/
def normalizedBasis
    (lab : SourceVertex p n → TargetVertex p m)
    (l : List (SourceVertex p n)) : TargetChain p m :=
  (TargetChains.toExterior ℤ (TargetVertex p m)).symm (exteriorFlag lab l)

/-- The exterior-normalized linear map induced by `lab`. -/
def normalizedMap
    (lab : SourceVertex p n → TargetVertex p m) :
    SourceFlags.Chain (SourceVertex p n) →ₗ[ℤ] TargetChain p m :=
  Finsupp.lift (TargetChain p m) ℤ (List (SourceVertex p n))
    (normalizedBasis lab)

@[simp] theorem normalizedMap_basis
    (lab : SourceVertex p n → TargetVertex p m)
    (l : List (SourceVertex p n)) :
    normalizedMap lab (SourceFlags.basis l) = normalizedBasis lab l := by
  simp [normalizedMap, SourceFlags.basis]

@[simp] theorem toExterior_normalizedBasis
    (lab : SourceVertex p n → TargetVertex p m)
    (l : List (SourceVertex p n)) :
    TargetChains.toExterior ℤ (TargetVertex p m) (normalizedBasis lab l) =
      exteriorFlag lab l := by
  simp [normalizedBasis]

/-- Left exterior multiplication by a target vertex. -/
def leftWedge (v : TargetVertex p m) : TargetChain p m →ₗ[ℤ] TargetChain p m :=
  (TargetChains.toExterior ℤ (TargetVertex p m)).symm.toLinearMap.comp
    ((LinearMap.mulLeft ℤ
      (ExteriorAlgebra.ι ℤ (Finsupp.single v 1))).comp
      (TargetChains.toExterior ℤ (TargetVertex p m)).toLinearMap)

@[simp] theorem toExterior_leftWedge
    (v : TargetVertex p m) (c : TargetChain p m) :
    TargetChains.toExterior ℤ (TargetVertex p m) (leftWedge v c) =
      ExteriorAlgebra.ι ℤ (Finsupp.single v 1) *
        TargetChains.toExterior ℤ (TargetVertex p m) c := by
  simp [leftWedge]

theorem normalizedMap_prepend
    (lab : SourceVertex p n → TargetVertex p m)
    (x : SourceVertex p n) (c : SourceFlags.Chain (SourceVertex p n)) :
    normalizedMap lab (SourceFlags.prepend x c) =
      leftWedge (lab x) (normalizedMap lab c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • SourceFlags.basis l by
        simp [SourceFlags.basis]]
      apply (TargetChains.toExterior ℤ (TargetVertex p m)).injective
      simp [exteriorFlag]

theorem boundary_leftWedge
    (v : TargetVertex p m) (c : TargetChain p m) :
    TargetChains.boundary ℤ (TargetVertex p m) (leftWedge v c) =
      c - leftWedge v
        (TargetChains.boundary ℤ (TargetVertex p m) c) := by
  apply (TargetChains.toExterior ℤ (TargetVertex p m)).injective
  simp only [TargetChains.toExterior_boundary, toExterior_leftWedge, map_sub]
  change CliffordAlgebra.contractLeft
      (TargetChains.augmentation ℤ (TargetVertex p m))
      (ExteriorAlgebra.ι ℤ (Finsupp.single v 1) *
        TargetChains.toExterior ℤ (TargetVertex p m) c) =
      TargetChains.toExterior ℤ (TargetVertex p m) c -
        ExteriorAlgebra.ι ℤ (Finsupp.single v 1) *
          CliffordAlgebra.contractLeft
            (TargetChains.augmentation ℤ (TargetVertex p m))
            (TargetChains.toExterior ℤ (TargetVertex p m) c)
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp [TargetChains.augmentation_single]

theorem normalizedBasis_cons
    (lab : SourceVertex p n → TargetVertex p m)
    (x : SourceVertex p n) (xs : List (SourceVertex p n)) :
    normalizedBasis lab (x :: xs) =
      leftWedge (lab x) (normalizedBasis lab xs) := by
  apply (TargetChains.toExterior ℤ (TargetVertex p m)).injective
  simp [exteriorFlag]

theorem boundary_normalizedMap_basis
    (lab : SourceVertex p n → TargetVertex p m)
    (l : List (SourceVertex p n)) :
    TargetChains.boundary ℤ (TargetVertex p m)
        (normalizedMap lab (SourceFlags.basis l)) =
      normalizedMap lab (SourceFlags.boundary (SourceFlags.basis l)) := by
  induction l with
  | nil =>
      apply (TargetChains.toExterior ℤ (TargetVertex p m)).injective
      simp [SourceFlags.boundaryBasis, exteriorFlag,
        TargetChains.exteriorContraction,
        CliffordAlgebra.contractLeft_algebraMap]
  | cons x xs ih =>
      simp only [normalizedMap_basis, SourceFlags.boundary_basis,
        SourceFlags.boundaryBasis_cons, map_sub, normalizedMap_prepend]
      rw [normalizedBasis_cons]
      rw [boundary_leftWedge]
      rw [SourceFlags.boundary_basis] at ih
      simpa only [normalizedMap_basis] using congrArg
        (fun c => normalizedBasis lab xs - leftWedge (lab x) c) ih

/-- The normalized labeling map is a map of augmented chain complexes. -/
theorem boundary_normalizedMap
    (lab : SourceVertex p n → TargetVertex p m)
    (c : SourceFlags.Chain (SourceVertex p n)) :
    TargetChains.boundary ℤ (TargetVertex p m) (normalizedMap lab c) =
      normalizedMap lab (SourceFlags.boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • SourceFlags.basis l by
        simp [SourceFlags.basis]]
      simp only [map_smul]
      rw [boundary_normalizedMap_basis]

/-- The target cyclic shift on vertices. -/
def targetShift (a : ZMod p) (v : TargetVertex p m) : TargetVertex p m :=
  (a + v.1, v.2)

/-- The normalized action of a target vertex map on target chains. -/
def targetAct (a : ZMod p) : TargetChain p m →ₗ[ℤ] TargetChain p m :=
  TargetChains.map (targetShift a)

theorem exteriorFlag_shift
    (lab : SourceVertex p n → TargetVertex p m)
    (heq : IsEquivariant lab) (a : ZMod p)
    (l : List (SourceVertex p n)) :
    exteriorFlag lab (l.map (NonzeroSignedVector.shift a)) =
      ExteriorAlgebra.map (TargetChains.vertexMap (targetShift a))
        (exteriorFlag lab l) := by
  induction l with
  | nil => simp [exteriorFlag]
  | cons x xs ih =>
      simp only [List.map_cons, exteriorFlag_cons, map_mul,
        ExteriorAlgebra.map_apply_ι, TargetChains.vertexMap_single, ih]
      rw [heq a x]
      rfl

/-- Cyclic equivariance of the exterior normalized map. -/
theorem normalizedMap_equivariant
    (lab : SourceVertex p n → TargetVertex p m)
    (heq : IsEquivariant lab) (a : ZMod p)
    (c : SourceFlags.Chain (SourceVertex p n)) :
    normalizedMap lab
        (SourceFlags.mapVertices (NonzeroSignedVector.shift a) c) =
      targetAct a (normalizedMap lab c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single l z =>
      rw [show Finsupp.single l z = z • SourceFlags.basis l by
        simp [SourceFlags.basis]]
      apply (TargetChains.toExterior ℤ (TargetVertex p m)).injective
      simp only [map_smul, SourceFlags.mapVertices_basis, normalizedMap_basis,
        toExterior_normalizedBasis, targetAct, TargetChains.toExterior_map]
      rw [exteriorFlag_shift lab heq]

/-- A one-vertex source flag maps to the exterior generator of its target
label, with coefficient one. -/
theorem toExterior_normalizedMap_singleton
    (lab : SourceVertex p n → TargetVertex p m)
    (x : SourceVertex p n) :
    TargetChains.toExterior ℤ (TargetVertex p m)
        (normalizedMap lab (SourceFlags.basis [x])) =
      ExteriorAlgebra.ι ℤ (Finsupp.single (lab x) 1) := by
  simp [exteriorFlag]

/-- The mapped singleton has augmentation one. -/
theorem augmentation_normalizedMap_singleton
    (lab : SourceVertex p n → TargetVertex p m)
    (x : SourceVertex p n) :
    CliffordAlgebra.contractLeft
        (TargetChains.augmentation ℤ (TargetVertex p m))
        (TargetChains.toExterior ℤ (TargetVertex p m)
          (normalizedMap lab (SourceFlags.basis [x]))) = 1 := by
  rw [toExterior_normalizedMap_singleton,
    CliffordAlgebra.contractLeft_ι]
  simp [TargetChains.augmentation_single]

/-! ## The alpha-split target subcomplex -/

/-- An alpha-split allowed target face: below `alpha`, each absolute label
has only one sign; at and above `alpha`, at least one cyclic sign is absent. -/
def IsAllowedFace (alpha : ℕ) (s : Finset (TargetVertex p m)) : Prop :=
  (∀ ⦃u v⦄, u ∈ s → v ∈ s → u.2 = v.2 → u.2.val < alpha →
      u.1 = v.1) ∧
  (∀ j : Fin m, alpha ≤ j.val → ∃ g : ZMod p, (g, j) ∉ s)

/-- Exterior products of ordered presentations of allowed faces.  This is
the oriented allowed-face span; repetitions automatically represent zero. -/
def allowedFaceSpan (alpha : ℕ) : Submodule ℤ (TargetChain p m) :=
  Submodule.span ℤ
    {c | ∃ l : List (TargetVertex p m),
      IsAllowedFace (p := p) alpha l.toFinset ∧
      c = (TargetChains.toExterior ℤ (TargetVertex p m)).symm
        (exteriorFlag (fun x => x) l)}

theorem comparable_of_flag
    {l : List (SourceVertex p n)}
    (hl : SourceFlags.IsFlag (fun x y => x < y) l)
    {x y : SourceVertex p n} (hx : x ∈ l) (hy : y ∈ l) :
    x ≤ y ∨ y ≤ x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
      change List.Pairwise (fun x y => x < y) (a :: l) at hl
      rw [List.pairwise_cons] at hl
      simp only [List.mem_cons] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact Or.inl le_rfl
        · exact Or.inl (hl.1 _ hy).le
      · rcases hy with rfl | hy
        · exact Or.inr (hl.1 _ hx).le
        · exact ih hl.2 hx hy

theorem labels_low_allowed
    (lab : SourceVertex p n → TargetVertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    {l : List (SourceVertex p n)}
    (hl : SourceFlags.IsFlag (fun x y => x < y) l) :
    ∀ ⦃u v⦄, u ∈ (l.map lab).toFinset → v ∈ (l.map lab).toFinset →
      u.2 = v.2 → u.2.val < alpha → u.1 = v.1 := by
  intro u v hu hv huv hj
  simp only [List.mem_toFinset, List.mem_map] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  rcases comparable_of_flag hl hx hy with hxy | hyx
  · exact hadm.1 hxy huv hj
  · exact (hadm.1 hyx huv.symm (by simpa [huv] using hj)).symm

theorem labels_high_allowed
    (hp : p.Prime)
    (lab : SourceVertex p n → TargetVertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    {l : List (SourceVertex p n)}
    (hl : SourceFlags.IsFlag (fun x y => x < y) l) :
    ∀ j : Fin m, alpha ≤ j.val →
      ∃ g : ZMod p, (g, j) ∉ (l.map lab).toFinset := by
  intro j hj
  by_contra hmissing
  push_neg at hmissing
  let e : Fin p ≃ ZMod p := (ZMod.finEquiv p).toEquiv
  have hex (i : Fin p) :
      ∃ x ∈ l, lab x = (e i, j) := by
    have hi := hmissing (e i)
    simp only [List.mem_toFinset, List.mem_map] at hi
    obtain ⟨x, hx, hxl⟩ := hi
    exact ⟨x, hx, hxl⟩
  choose pick hpick_mem hpick_lab using hex
  have hpick_inj : Function.Injective pick := by
    intro i k hik
    apply e.injective
    have h := congrArg (fun x => (lab x).1) hik
    rw [hpick_lab i, hpick_lab k] at h
    exact h
  let pos (i : Fin p) : Fin l.length :=
    ⟨l.idxOf (pick i), List.idxOf_lt_length_iff.mpr (hpick_mem i)⟩
  have hget_pos (i : Fin p) : l.get (pos i) = pick i := by
    simpa only [List.get_eq_getElem, pos] using
      (List.getElem_idxOf
        (List.idxOf_lt_length_iff.mpr (hpick_mem i)))
  have hpos_inj : Function.Injective pos := by
    intro i k hik
    apply hpick_inj
    rw [← hget_pos i, ← hget_pos k, hik]
  let s : Finset (Fin l.length) := Finset.univ.image pos
  have hs_card : s.card = p := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hpos_inj, Finset.card_univ,
      Fintype.card_fin]
  let ord : Fin p ≃o s := Finset.orderIsoOfFin s hs_card
  let chain (i : Fin p) : SourceVertex p n := l.get (ord i).1
  have hl_le : List.Pairwise (fun x y : SourceVertex p n => x ≤ y) l := by
    exact hl.imp (fun h => h.le)
  have hchain_mono : Monotone chain := by
    intro i k hik
    apply hl_le.rel_get_of_le
    exact ord.monotone hik
  have hchain_eq_of_ord_eq (i k : Fin p)
      (hik : (ord i).1 = pos k) : chain i = pick k := by
    change l.get (ord i).1 = pick k
    rw [hik]
    exact hget_pos k
  have hsecond : ∀ i, (lab (chain i)).2 = j := by
    intro i
    have hi : (ord i).1 ∈ s := (ord i).2
    obtain ⟨k, _hk, hk⟩ := Finset.mem_image.mp hi
    rw [hchain_eq_of_ord_eq i k hk.symm, hpick_lab]
  have hsign_surj : Function.Surjective (fun i => (lab (chain i)).1) := by
    intro g
    let k : Fin p := e.symm g
    have hk_mem : pos k ∈ s := by
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    obtain ⟨i, hi⟩ := ord.surjective ⟨pos k, hk_mem⟩
    refine ⟨i, ?_⟩
    have hix : chain i = pick k :=
      hchain_eq_of_ord_eq i k (congrArg Subtype.val hi)
    change (lab (chain i)).1 = g
    rw [hix, hpick_lab]
    exact e.apply_symm_apply g
  exact (hadm.2 chain hchain_mono ⟨j, hj, hsecond⟩) hsign_surj

theorem labels_allowed
    (hp : p.Prime)
    (lab : SourceVertex p n → TargetVertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    {l : List (SourceVertex p n)}
    (hl : SourceFlags.IsFlag (fun x y => x < y) l) :
    IsAllowedFace (p := p) alpha (l.map lab).toFinset := by
  exact ⟨labels_low_allowed lab hadm hl,
    labels_high_allowed hp lab hadm hl⟩

theorem exteriorFlag_map
    {ι : Type*} (lab : ι → TargetVertex p m) (l : List ι) :
    exteriorFlag (fun x => x) (l.map lab) = exteriorFlag lab l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [exteriorFlag, ih]

/-- Every strict source flag is carried into the oriented alpha-split
allowed-face span. -/
theorem normalizedBasis_mem_allowedFaceSpan
    (hp : p.Prime)
    (lab : SourceVertex p n → TargetVertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    {l : List (SourceVertex p n)}
    (hl : SourceFlags.IsFlag (fun x y => x < y) l) :
    normalizedBasis lab l ∈ allowedFaceSpan (p := p) (m := m) alpha := by
  apply Submodule.subset_span
  refine ⟨l.map lab, labels_allowed hp lab hadm hl, ?_⟩
  apply (TargetChains.toExterior ℤ (TargetVertex p m)).injective
  simp only [toExterior_normalizedBasis, LinearEquiv.apply_symm_apply]
  exact (exteriorFlag_map lab l).symm

theorem normalizedMap_basis_mem_allowedFaceSpan
    (hp : p.Prime)
    (lab : SourceVertex p n → TargetVertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    {l : List (SourceVertex p n)}
    (hl : SourceFlags.IsFlag (fun x y => x < y) l) :
    normalizedMap lab (SourceFlags.basis l) ∈
      allowedFaceSpan (p := p) (m := m) alpha := by
  rw [normalizedMap_basis]
  exact normalizedBasis_mem_allowedFaceSpan hp lab hadm hl

end

end LabelChainMap
