import ErdosProblems.Erdos538.AbstractKernelCap
import ErdosProblems.Erdos538.LocalParentSafety
import ErdosProblems.Erdos538.GlobalAssembly

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

noncomputable section
open scoped BigOperators

/-- Certificate carried by one selected facet in an abstract ordered parent.
The child coordinates are reindexed onto all parent points except the omitted
point `x`; the omitted point's actual label is expressed in the favorable
basis coordinates and is certified safe. -/
structure SelectedCertificate
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (d : ℕ) {I : Type*} [Fintype I] [DecidableEq I]
    (ω : I → VertexLabel K d) (x : I) where
  param : GoodParam K d
  childIndex : Option (Fin d) ≃ {y : I // y ≠ x}
  outsideCoord : VertexLabel K d
  child_label : ∀ o, ω (childIndex o).1 =
    ((goodParamToSample param).1 o, (goodParamToSample param).2 o)
  outside_label : ω x = outsideActual param outsideCoord
  safe : outsideCoord ∉ BadOutside param

/-- Split a finite sum into the distinguished point and its complement. -/
theorem sum_eq_value_add_sum_ne
    {I M : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid M]
    (f : I → M) (x : I) :
    ∑ i, f i = f x + ∑ y : {y : I // y ≠ x}, f y.1 := by
  have hmem : x ∈ (Finset.univ : Finset I) := Finset.mem_univ x
  have herase := Finset.sum_erase_add (Finset.univ : Finset I) f hmem
  have hsub : ∑ y : {y : I // y ≠ x}, f y.1 =
      ∑ y ∈ (Finset.univ.erase x), f y := by
    symm
    exact Finset.sum_subtype (Finset.univ.erase x) (by simp) f
  rw [← hsub] at herase
  rw [← herase]
  ac_rfl

/-- Extend child coordinates by zero at the omitted parent point. -/
def extendChild
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (a : Option (Fin d) → K) : I → K := fun y =>
  if h : y = x then 0 else a (c.childIndex.symm ⟨y, h⟩)

@[simp] theorem extendChild_at_omitted
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (a : Option (Fin d) → K) : extendChild c a x = 0 := by
  simp [extendChild]

@[simp] theorem extendChild_at_child
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (a : Option (Fin d) → K) (o : Option (Fin d)) :
    extendChild c a (c.childIndex o).1 = a o := by
  have hne : (c.childIndex o).1 ≠ x := (c.childIndex o).2
  simp [extendChild, hne]

/-- Transporting a child-coordinate sum to the parent adds only the omitted
zero coordinate. -/
theorem sum_extendChild
    {K M : Type*} [Field K] [Fintype K] [DecidableEq K]
    [AddCommMonoid M]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (a : Option (Fin d) → K) (g : I → K → M)
    (hzero : g x 0 = 0) :
    ∑ y, g y (extendChild c a y) =
      ∑ o, g (c.childIndex o).1 (a o) := by
  rw [sum_eq_value_add_sum_ne]
  rw [extendChild_at_omitted, hzero, zero_add]
  rw [← c.childIndex.sum_comp]
  apply Finset.sum_congr rfl
  intro o _
  rw [extendChild_at_child]

/-- Parent row map for an arbitrary common labeling. -/
def globalParentRowMap
    {K : Type*} [Field K] {d : ℕ} {I : Type*} [Fintype I]
    (ω : I → VertexLabel K d) : (I → K) →ₗ[K] (Fin d → K) :=
  Fintype.linearCombination K (fun i => (ω i).1)

/-- Parent diagonal form for an arbitrary common labeling. -/
def globalParentForm
    {K : Type*} [Field K] {d : ℕ} {I : Type*} [Fintype I]
    (ω : I → VertexLabel K d) : LinearMap.BilinForm K (I → K) :=
  LinearMap.mk₂ K
    (fun u v => ∑ i, (ω i).2 * u i * v i)
    (by
      intro u v w
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro a u v
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro u v w
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro a u v
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

/-- The global diagonal form is symmetric. -/
theorem globalParentForm_isSymm
    {K : Type*} [Field K] {d : ℕ} {I : Type*} [Fintype I]
    (ω : I → VertexLabel K d) : (globalParentForm ω).IsSymm := by
  constructor
  intro u v
  simp only [globalParentForm, LinearMap.mk₂_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A favorable child certificate transports every child linear combination
to the same combination of the common parent rows. -/
theorem globalParentRowMap_extendChild
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (a : Option (Fin d) → K) :
    globalParentRowMap ω (extendChild c a) =
      Fintype.linearCombination K (goodParamToSample c.param).1 a := by
  change (∑ y, extendChild c a y • (ω y).1) =
    ∑ o, a o • (goodParamToSample c.param).1 o
  rw [sum_extendChild c a (fun y t => t • (ω y).1) (by simp)]
  apply Finset.sum_congr rfl
  intro o _
  rw [c.child_label o]

/-- Hence one selected certificate makes the common parent row map
surjective. -/
theorem globalParentRowMap_surjective
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (hd : 0 < d) (c : SelectedCertificate K d ω x) :
    Function.Surjective (globalParentRowMap ω) := by
  have hprops := goodParamToSample_properties hd c.param
  intro v
  obtain ⟨a, ha⟩ := hprops.2.2.1 v
  exact ⟨extendChild c a, (globalParentRowMap_extendChild c a).trans ha⟩

/-- The transported normalized null vector. -/
def certificateRelation
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x) : I → K :=
  extendChild c (normalizedNull fun i => (c.param.1 i : K))

/-- It is a parent row relation. -/
theorem certificateRelation_mem_ker
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x) :
    certificateRelation c ∈ LinearMap.ker (globalParentRowMap ω) := by
  rw [LinearMap.mem_ker, certificateRelation,
    globalParentRowMap_extendChild]
  simpa [goodParamToSample, Fintype.linearCombination_apply] using
    (normalizedNull_generatedRows_relation
      (fun i => (c.param.1 i : K)) c.param.2.1.1)

/-- Its omitted coordinate is zero and every other parent coordinate is
nonzero. -/
theorem certificateRelation_unique_zero
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x) :
    certificateRelation c x = 0 ∧
      ∀ y, y ≠ x → certificateRelation c y ≠ 0 := by
  constructor
  · exact extendChild_at_omitted _ _
  · intro y hy
    rw [certificateRelation]
    simp only [extendChild, dif_neg hy]
    exact normalizedNull_fullSupport one_ne_zero _
      (fun i => (c.param.1 i).ne_zero) _

/-- The transported relation is isotropic for the common parent form. -/
theorem certificateRelation_isotropic
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x) :
    globalParentForm ω (certificateRelation c) (certificateRelation c) = 0 := by
  simp only [globalParentForm, LinearMap.mk₂_apply]
  rw [certificateRelation]
  rw [sum_extendChild c _
    (fun y t => (ω y).2 * t * t) (by simp)]
  have hiso := c.param.2.2.1.2
  change ((dotProductEquiv K (Option (Fin d)))
    (squaredNormalizedNull c.param.1)) c.param.2.2.1.1 = 0 at hiso
  rw [dotProductEquiv_apply_apply] at hiso
  simp only [dotProduct] at hiso
  simp_rw [c.child_label]
  simpa [squaredNormalizedNull, goodParamToSample, pow_two, mul_assoc,
    mul_comm, mul_left_comm] using hiso

/-- The common parent relation space has dimension two whenever one selected
child supplies surjectivity and the parent has `d+2` coordinates. -/
theorem globalParentKernel_finrank_two
    {K : Type*} [Field K] [Fintype K]
    {d : ℕ} {I : Type*} [Fintype I]
    (ω : I → VertexLabel K d) (hcard : Fintype.card I = d + 2)
    (hsurj : Function.Surjective (globalParentRowMap ω)) :
    Module.finrank K (LinearMap.ker (globalParentRowMap ω)) = 2 := by
  have hrange : LinearMap.range (globalParentRowMap ω) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (globalParentRowMap ω)
  rw [hrange, finrank_top,
    Module.finrank_fintype_fun_eq_card K,
    Module.finrank_fintype_fun_eq_card K, hcard] at hrank
  simp only [Fintype.card_fin] at hrank
  omega

/-- Restriction of the common diagonal form to the parent relation space. -/
def globalKernelForm
    {K : Type*} [Field K] {d : ℕ} {I : Type*} [Fintype I]
    (ω : I → VertexLabel K d) :
    LinearMap.BilinForm K (LinearMap.ker (globalParentRowMap ω)) :=
  (globalParentForm ω).restrict (LinearMap.ker (globalParentRowMap ω))

/-- Coordinate evaluation on the common parent relation space. -/
def globalKernelCoord
    {K : Type*} [Field K] {d : ℕ} {I : Type*} [Fintype I]
    (ω : I → VertexLabel K d) (i : I) :
    LinearMap.ker (globalParentRowMap ω) →ₗ[K] K :=
  (LinearMap.proj i).comp (LinearMap.ker (globalParentRowMap ω)).subtype

/-- The restricted global form remains symmetric. -/
theorem globalKernelForm_isSymm
    {K : Type*} [Field K] {d : ℕ} {I : Type*} [Fintype I]
    (ω : I → VertexLabel K d) : (globalKernelForm ω).IsSymm := by
  constructor
  intro u v
  exact (globalParentForm_isSymm ω).eq u.1 v.1

/-- Transport a full local-parent coordinate vector through a selected
certificate's reindexing. -/
def transportLocalParent
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (u : LocalParentIndex d → K) : I → K := fun y =>
  if h : y = x then u none else
    u (some (c.childIndex.symm ⟨y, h⟩))

@[simp] theorem transportLocalParent_at_omitted
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (u : LocalParentIndex d → K) :
    transportLocalParent c u x = u none := by
  simp [transportLocalParent]

@[simp] theorem transportLocalParent_at_child
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (u : LocalParentIndex d → K) (o : Option (Fin d)) :
    transportLocalParent c u (c.childIndex o).1 = u (some o) := by
  have hne : (c.childIndex o).1 ≠ x := (c.childIndex o).2
  simp [transportLocalParent, hne]

/-- Sum transport for a full local-parent vector. -/
theorem sum_transportLocalParent
    {K M : Type*} [Field K] [Fintype K] [DecidableEq K]
    [AddCommMonoid M]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (u : LocalParentIndex d → K) (g : I → K → M) :
    ∑ y, g y (transportLocalParent c u y) =
      g x (u none) + ∑ o, g (c.childIndex o).1 (u (some o)) := by
  rw [sum_eq_value_add_sum_ne]
  rw [transportLocalParent_at_omitted]
  rw [← c.childIndex.sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro o _
  rw [transportLocalParent_at_child]

/-- A local row relation transports to a relation for the common global parent
rows. -/
theorem transportLocalParent_mem_ker
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (u : LocalParentIndex d → K)
    (hu : IsLocalParentRelation c.param c.outsideCoord u) :
    transportLocalParent c u ∈ LinearMap.ker (globalParentRowMap ω) := by
  rw [LinearMap.mem_ker]
  change (∑ y, transportLocalParent c u y • (ω y).1) = 0
  rw [sum_transportLocalParent c u (fun y t => t • (ω y).1)]
  rw [c.outside_label]
  simp_rw [c.child_label]
  simpa [IsLocalParentRelation, localParentRows, Fintype.sum_option]
    using hu

/-- The common global pairing of transported vectors equals the original
local-parent pairing. -/
theorem globalParentForm_transportLocalParent
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x)
    (u v : LocalParentIndex d → K) :
    globalParentForm ω (transportLocalParent c u)
        (transportLocalParent c v) =
      localParentPair c.param c.outsideCoord u v := by
  simp only [globalParentForm, LinearMap.mk₂_apply]
  rw [sum_transportLocalParent c u
    (fun y t => (ω y).2 * t * transportLocalParent c v y)]
  rw [transportLocalParent_at_omitted]
  simp_rw [transportLocalParent_at_child]
  rw [c.outside_label]
  simp_rw [c.child_label]
  simp [localParentPair, localParentCoeff, outsideActual,
    Fintype.sum_option]

/-- A selected certificate's exact safety condition makes the restricted
common parent form nonzero. -/
theorem globalKernelForm_not_total_of_certificate
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {ω : I → VertexLabel K d} {x : I}
    (c : SelectedCertificate K d ω x) :
    ¬ ∀ u v : LinearMap.ker (globalParentRowMap ω),
      globalKernelForm ω u v = 0 := by
  intro htotal
  apply not_localParentTotallyIsotropic_of_not_badOutside
    c.param c.outsideCoord c.safe
  intro u v hu hv
  let gu : LinearMap.ker (globalParentRowMap ω) :=
    ⟨transportLocalParent c u, transportLocalParent_mem_ker c u hu⟩
  let gv : LinearMap.ker (globalParentRowMap ω) :=
    ⟨transportLocalParent c v, transportLocalParent_mem_ker c v hv⟩
  have h := htotal gu gv
  simpa [globalKernelForm, gu, gv,
    globalParentForm_transportLocalParent] using h

/-- Abstract reindexed safe-kernel cap theorem: any collection of parent
facets carrying compatible favorable safe certificates has cardinality at
most two. -/
theorem selectedCertificates_card_le_two
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (ω : I → VertexLabel K d) (selected : Finset I)
    (cert : ∀ x ∈ selected, SelectedCertificate K d ω x)
    (hd : 0 < d) (hcard : Fintype.card I = d + 2)
    (htwo : (2 : K) ≠ 0) :
    selected.card ≤ 2 := by
  by_cases hempty : selected = ∅
  · simp [hempty]
  · have hne : selected.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨x, hx⟩ := hne
    let cx := cert x hx
    let W := LinearMap.ker (globalParentRowMap ω)
    let rel : I → W := fun y =>
      if hy : y ∈ selected then
        ⟨certificateRelation (cert y hy), certificateRelation_mem_ker (cert y hy)⟩
      else 0
    have hfin : Module.finrank K W = 2 := by
      exact globalParentKernel_finrank_two ω hcard
        (globalParentRowMap_surjective hd cx)
    apply uniqueZeroIsotropic_selected_card_le_two
      (globalKernelForm ω) (globalKernelForm_isSymm ω)
      (globalKernelCoord ω) selected rel
    · intro y hy
      simp only [rel, dif_pos hy, globalKernelCoord,
        LinearMap.comp_apply, Submodule.coe_subtype]
      exact (certificateRelation_unique_zero (cert y hy)).1
    · intro y hy z hzy
      simp only [rel, dif_pos hy, globalKernelCoord,
        LinearMap.comp_apply, Submodule.coe_subtype]
      exact (certificateRelation_unique_zero (cert y hy)).2 z hzy
    · intro y hy
      simp only [rel, dif_pos hy, globalKernelForm,
        LinearMap.BilinForm.restrict_apply]
      exact certificateRelation_isotropic (cert y hy)
    · exact hfin
    · exact htwo
    · exact globalKernelForm_not_total_of_certificate cx

end

end Erdos538.IsotropicKernel
