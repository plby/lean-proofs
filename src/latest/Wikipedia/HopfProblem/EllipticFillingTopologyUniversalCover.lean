import Wikipedia.HopfProblem.EllipticSurfaces
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
# The actual affine universal cover of an elliptic filling surface

The covering projection is the composite of the real period-coordinate map
to the complex period torus and the free finite affine quotient. Its fibres
are identified directly with integral translates of iterates of the actual
affine map. No abstract presentation of a fundamental group is assumed.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.HopfProblem.CoveringComposition

structure SheetFamily {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (f : E → X) (x : X) (I : Type*) where
  base : Set X
  mem_base : x ∈ base
  isOpen_base : IsOpen base
  sheet : I → Set E
  isOpen_sheet : ∀ i, IsOpen (sheet i)
  disjoint : Pairwise (Disjoint on sheet)
  bijOn : ∀ i, Set.BijOn f (sheet i) base
  preimage_eq : f ⁻¹' base = ⋃ i, sheet i

theorem exists_sheet_family {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] {f : E → X} {x : X}
    (h : IsEvenlyCovered f x I) :
    ∃ V : Set X, x ∈ V ∧ IsOpen V ∧ ∃ U : I → Set E,
      (∀ i, IsOpen (U i)) ∧ Pairwise (Disjoint on U) ∧
      (∀ i, Set.BijOn f (U i) V) ∧ f ⁻¹' V = ⋃ i, U i := by
  rcases h with ⟨hd, V, hxV, hV, hfV, H, hH⟩
  let : DiscreteTopology I := hd
  let U : I → Set E := fun i ↦ Subtype.val '' {e : f ⁻¹' V | (H e).2 = i}
  refine ⟨V, hxV, hV, U, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hfV.isOpenMap_subtype_val
    exact (isOpen_discrete ({i} : Set I)).preimage (continuous_snd.comp H.continuous)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hab' : b = a := Subtype.ext hab
    subst b
    exact hij (ha.symm.trans hb)
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · rintro e ⟨a, ha, rfl⟩
      exact a.property
    · rintro e ⟨a, ha, rfl⟩ e' ⟨b, hb, rfl⟩ hab
      apply congrArg Subtype.val
      apply H.injective
      apply Prod.ext
      · apply Subtype.ext
        simpa only [hH] using hab
      · exact ha.trans hb.symm
    · intro y hy
      let a : f ⁻¹' V := H.symm (⟨y, hy⟩, i)
      refine ⟨a, ⟨a, ?_, rfl⟩, ?_⟩
      · change (H (H.symm (⟨y, hy⟩, i))).2 = i
        simp
      · rw [← hH]
        change (H (H.symm (⟨y, hy⟩, i))).1.1 = y
        simp
  · ext e
    constructor
    · intro he
      exact Set.mem_iUnion.mpr ⟨(H ⟨e, he⟩).2, ⟨⟨e, he⟩, rfl, rfl⟩⟩
    · intro he
      obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.mp he
      exact a.property

theorem nonempty_sheetFamily {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] {f : E → X} {x : X}
    (h : IsEvenlyCovered f x I) : Nonempty (SheetFamily f x I) := by
  obtain ⟨V, hx, hV, U, hU, hdisj, hbij, hexh⟩ := exists_sheet_family h
  exact ⟨⟨V, hx, hV, U, hU, hdisj, hbij, hexh⟩⟩

theorem evenlyCovered_of_sheets
    {E X I : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace I] [DiscreteTopology I]
    {f : E → X} {x : X} (hf : Continuous f) (hfo : IsOpenMap f)
    (V : Set X) (hx : x ∈ V) (hV : IsOpen V)
    (U : I → Set E) (hU : ∀ i, IsOpen (U i))
    (hinj : ∀ i, (U i).InjOn f) (hsurj : ∀ i, (U i).SurjOn f V)
    (hdisj : Pairwise (Disjoint on U)) (hexh : f ⁻¹' V ⊆ ⋃ i, U i) :
    IsEvenlyCovered f x I := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    exact .of_preimage_eq_empty I (hV.mem_nhds hx)
      (Set.eq_empty_of_subset_empty (by simpa using hexh))
  | inr hI =>
    obtain ⟨e, _, _⟩ := hsurj (Classical.arbitrary I) hx
    let : Nonempty E := ⟨e⟩
    have hopen (i : I) {W : Set X} (hWV : W ⊆ V) :
        IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i) := by
      refine ⟨fun hW => (hW.preimage hf).inter (hU i), fun hW => ?_⟩
      have himage : f '' (f ⁻¹' W ∩ U i) = W := by
        apply Set.Subset.antisymm
        · rintro _ ⟨z, hz, rfl⟩
          exact hz.1
        · intro y hy
          obtain ⟨z, hz, hzy⟩ := hsurj i (hWV hy)
          exact ⟨z, ⟨by simpa only [Set.mem_preimage, hzy] using hy, hz⟩, hzy⟩
      rw [← himage]
      exact hfo _ hW
    exact .of_trivialization
      (t := hV.trivializationDiscrete U V hopen hinj hsurj hdisj hexh) hx

theorem evenlyCovered_comp_of_sheet_families
    {E B X I : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
    [Finite I] {J : I → Type*} [∀ i, TopologicalSpace (J i)]
    [∀ i, DiscreteTopology (J i)] {f : E → B} {g : B → X} {x : X}
    (hf : Continuous f) (hfo : IsOpenMap f) (hg : Continuous g) (hgo : IsOpenMap g)
    (S : SheetFamily g x I) (b : I → B) (hb : ∀ i, b i ∈ S.sheet i)
    (hgb : ∀ i, g (b i) = x) (T : ∀ i, SheetFamily f (b i) (J i)) :
    IsEvenlyCovered (g ∘ f) x (Sigma J) := by
  classical
  let W : Set X := S.base ∩ ⋂ i, g '' (S.sheet i ∩ (T i).base)
  have hxW : x ∈ W := by
    refine ⟨S.mem_base, Set.mem_iInter.mpr fun i => ?_⟩
    exact ⟨b i, ⟨hb i, (T i).mem_base⟩, hgb i⟩
  have hW : IsOpen W :=
    S.isOpen_base.inter (isOpen_iInter_of_finite fun i =>
      hgo _ ((S.isOpen_sheet i).inter (T i).isOpen_base))
  let U : Sigma J → Set E := fun ij => f ⁻¹' S.sheet ij.1 ∩ (T ij.1).sheet ij.2
  apply evenlyCovered_of_sheets (hg.comp hf) (hgo.comp hfo) W hxW hW U
  · intro ij
    exact ((S.isOpen_sheet ij.1).preimage hf).inter ((T ij.1).isOpen_sheet ij.2)
  · intro ij e he e' he' hee'
    exact ((T ij.1).bijOn ij.2).injOn he.2 he'.2
      ((S.bijOn ij.1).injOn he.1 he'.1 hee')
  · rintro ⟨i, j⟩ y hy
    obtain ⟨b', hb', hby⟩ := Set.mem_iInter.mp hy.2 i
    obtain ⟨e, he, hfe⟩ := ((T i).bijOn j).surjOn hb'.2
    refine ⟨e, ⟨?_, he⟩, (congrArg g hfe).trans hby⟩
    change f e ∈ S.sheet i
    rw [hfe]
    exact hb'.1
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    apply Set.disjoint_left.mpr
    intro e he he'
    by_cases hii : i = i'
    · cases hii
      have hjj : j ≠ j' := by
        intro h
        cases h
        exact hne rfl
      exact ((T i).disjoint hjj).le_bot ⟨he.2, he'.2⟩
    · exact (S.disjoint hii).le_bot ⟨he.1, he'.1⟩
  · intro e he
    change g (f e) ∈ W at he
    have houter : f e ∈ g ⁻¹' S.base := he.1
    rw [S.preimage_eq] at houter
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp houter
    obtain ⟨b', hb', hgEq⟩ := Set.mem_iInter.mp he.2 i
    have heq : f e = b' := (S.bijOn i).injOn hi hb'.1 hgEq.symm
    have hinner : e ∈ f ⁻¹' (T i).base := by
      change f e ∈ (T i).base
      rw [heq]
      exact hb'.2
    rw [(T i).preimage_eq] at hinner
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hinner
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, ⟨hi, hj⟩⟩

/-- Covering maps compose when the outer covering has finite fibres.
No separation, surjectivity, or finiteness of the inner fibres is needed. -/
theorem covering_comp_of_finite_fibres
    {E B X : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
    {f : E → B} {g : B → X} (hf : IsCoveringMap f) (hg : IsCoveringMap g)
    (hfin : ∀ x, Finite (g ⁻¹' {x})) : IsCoveringMap (g ∘ f) := by
  classical
  intro x
  let I := g ⁻¹' {x}
  let : Finite I := hfin x
  let S : SheetFamily g x I := Classical.choice (nonempty_sheetFamily (hg x))
  have hbex : ∀ i : I, ∃ b ∈ S.sheet i, g b = x :=
    fun i => (S.bijOn i).surjOn S.mem_base
  choose b hb hgb using hbex
  let : ∀ i : I, DiscreteTopology (f ⁻¹' {b i}) := fun i => (hf (b i)).1
  let T : ∀ i : I, SheetFamily f (b i) (f ⁻¹' {b i}) :=
    fun i => Classical.choice (nonempty_sheetFamily (hf (b i)))
  exact (evenlyCovered_comp_of_sheet_families hf.continuous hf.isOpenMap
    hg.continuous hg.isOpenMap S b hb hgb T).to_isEvenlyCovered_preimage

end Wikipedia.HopfProblem.CoveringComposition

namespace Wikipedia.HopfProblem.Elliptic

/-- The period-lattice projection in real coordinates is an actual covering map. -/
theorem flatProjection_isCoveringMap (p : PeriodDomain) :
    IsCoveringMap (flatProjection p) := by
  have hq : IsAddQuotientCoveringMap p.lattice.mkQ p.lattice.toAddSubgroup := by
    apply p.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    change IsDiscrete (p.lattice : Set ComplexPlane₂)
    let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
    exact DiscreteTopology.isDiscrete
  exact hq.isCoveringMap.comp_homeomorph (periodEquiv p).toHomeomorph

variable (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)

/-- The actual affine covering projection from real coordinates to the surface. -/
def affineCoverProjection : RealCoordinates → Surface j p v hv :=
  surfaceProjection j p v hv ∘ flatProjection p.val

theorem affineCoverProjection_continuous : Continuous (affineCoverProjection j p v hv) :=
  (surfaceProjection_continuous j p v hv).comp (flatProjection_continuous p.val)

theorem affineCoverProjection_surjective :
    Function.Surjective (affineCoverProjection j p v hv) :=
  (surfaceProjection_surjective j p v hv).comp (flatProjection_surjective p.val)

/-- Equality of two projected points is exactly integral congruence after
one of the prescribed three or four affine iterates. -/
theorem affineCoverProjection_eq_iff_flatCongruent (x y : RealCoordinates) :
    affineCoverProjection j p v hv x = affineCoverProjection j p v hv y ↔
      ∃ r : ℕ, r < j.order ∧ FlatCongruent x ((flatAffine j v)^[r] y) := by
  let := affineAction j p v hv.1
  change FiniteQuotient.project (CyclicGroup j) p.val.Torus (flatProjection p.val x) =
    FiniteQuotient.project (CyclicGroup j) p.val.Torus (flatProjection p.val y) ↔ _
  rw [FiniteQuotient.project_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.toAdd.val, ZMod.val_lt _, (flatProjection_eq_iff p.val _ _).mp ?_⟩
    have hA : g • flatProjection p.val y =
        flatProjection p.val ((flatAffine j v)^[g.toAdd.val] y) :=
      affinePermutation_pow_flatProjection j p v g.toAdd.val y
    exact hg.symm.trans hA
  · rintro ⟨r, hr, hxy⟩
    refine ⟨Multiplicative.ofAdd (r : ZMod j.order), ?_⟩
    change (affinePermutation j p v ^ (r : ZMod j.order).val)
      (flatProjection p.val y) = flatProjection p.val x
    rw [ZMod.val_natCast_of_lt hr, affinePermutation_pow_flatProjection]
    exact ((flatProjection_eq_iff p.val _ _).mpr hxy).symm

/-- The fibre relation in actual affine coordinates: integer translations
and the finite list of affine iterates account for every point, exactly. -/
theorem affineCoverProjection_eq_iff_translate (x y : RealCoordinates) :
    affineCoverProjection j p v hv x = affineCoverProjection j p v hv y ↔
      ∃ r : ℕ, r < j.order ∧ ∃ w : Lattice,
        x = realCast w + (flatAffine j v)^[r] y := by
  rw [affineCoverProjection_eq_iff_flatCongruent]
  simp only [FlatCongruent, sub_eq_iff_eq_add]

theorem realCast_injective : Function.Injective realCast := by
  intro w z h
  funext i
  have hi := congrFun h i
  change (w i : ℝ) = (z i : ℝ) at hi
  exact_mod_cast hi

include p hv in
/-- Distinct affine residues and integer translates give distinct points
of the covering fibre. This uses the proved freeness on the actual torus. -/
theorem affineTranslate_unique (x : RealCoordinates) (r s : Fin j.order) (w z : Lattice)
    (h : realCast w + (flatAffine j v)^[r.val] x =
      realCast z + (flatAffine j v)^[s.val] x) : r = s ∧ w = z := by
  let := affineAction j p v hv.1
  let := affineAction_free j p v hv
  have hproj := congrArg (flatProjection p.val) h
  simp only [flatProjection_add, flatProjection_realCast, zero_add] at hproj
  have hsmul : Multiplicative.ofAdd (r.val : ZMod j.order) • flatProjection p.val x =
      Multiplicative.ofAdd (s.val : ZMod j.order) • flatProjection p.val x := by
    change (affinePermutation j p v ^ (r.val : ZMod j.order).val)
      (flatProjection p.val x) =
      (affinePermutation j p v ^ (s.val : ZMod j.order).val) (flatProjection p.val x)
    rw [ZMod.val_natCast_of_lt r.isLt, ZMod.val_natCast_of_lt s.isLt,
      affinePermutation_pow_flatProjection, affinePermutation_pow_flatProjection]
    exact hproj
  have hg := IsCancelSMul.right_cancel _ _ (flatProjection p.val x) hsmul
  have hval := congrArg (fun g : CyclicGroup j => g.toAdd.val) hg
  change (r.val : ZMod j.order).val = (s.val : ZMod j.order).val at hval
  rw [ZMod.val_natCast_of_lt r.isLt, ZMod.val_natCast_of_lt s.isLt] at hval
  have hrs : r = s := Fin.ext hval
  subst s
  exact ⟨rfl, realCast_injective (add_right_cancel h)⟩

/-- Every point of the actual covering fibre has unique affine residue and
integer translation coordinates. This is a fibre bijection, not an assumed
identification of a deck group or a fundamental group. -/
def affineCoverFibreEquiv (y : RealCoordinates) :
    (affineCoverProjection j p v hv ⁻¹' {affineCoverProjection j p v hv y}) ≃
      Fin j.order × Lattice := by
  let f : Fin j.order × Lattice →
      (affineCoverProjection j p v hv ⁻¹' {affineCoverProjection j p v hv y}) :=
    fun a => ⟨realCast a.2 + (flatAffine j v)^[a.1.val] y,
      (affineCoverProjection_eq_iff_translate j p v hv _ _).mpr
        ⟨a.1.val, a.1.isLt, a.2, rfl⟩⟩
  apply (Equiv.ofBijective f ?_).symm
  constructor
  · rintro ⟨r, w⟩ ⟨s, z⟩ h
    have hu := affineTranslate_unique j p v hv y r s w z (congrArg Subtype.val h)
    exact Prod.ext hu.1 hu.2
  · intro x
    obtain ⟨r, hr, w, hw⟩ := (affineCoverProjection_eq_iff_translate j p v hv _ _).mp x.2
    exact ⟨(⟨r, hr⟩, w), Subtype.ext hw.symm⟩

@[simp] theorem affineCoverProjection_realCast_add (w : Lattice) (x : RealCoordinates) :
    affineCoverProjection j p v hv (realCast w + x) =
      affineCoverProjection j p v hv x := by
  simp [affineCoverProjection]

@[simp] theorem affineCoverProjection_flatAffine (x : RealCoordinates) :
    affineCoverProjection j p v hv (flatAffine j v x) =
      affineCoverProjection j p v hv x := by
  apply (affineCoverProjection_eq_iff_translate j p v hv _ _).mpr
  refine ⟨1, by cases j <;> decide, 0, ?_⟩
  have hzero : realCast (0 : Lattice) = 0 := by ext i; simp [realCast]
  rw [hzero, zero_add, Function.iterate_one]

theorem realCoordinates_contractibleSpace : ContractibleSpace RealCoordinates := inferInstance

theorem realCoordinates_simplyConnectedSpace : SimplyConnectedSpace RealCoordinates := inferInstance

/-- The finite outer quotient has finite fibres, proved from its exact
covering degree rather than imposed as an additional assumption. -/
theorem surfaceProjection_fibre_finite (x : Surface j p v hv) :
    Finite (surfaceProjection j p v hv ⁻¹' {x}) := by
  apply Nat.finite_of_card_ne_zero
  rw [surfaceProjection_fibre_card]
  exact Nat.ne_of_gt j.order_pos

/-- The composite real affine projection is a genuine covering map. The
finite outer covering allows a common evenly covered neighbourhood for
all its sheets. -/
theorem affineCoverProjection_isCoveringMap :
    IsCoveringMap (affineCoverProjection j p v hv) :=
  CoveringComposition.covering_comp_of_finite_fibres (flatProjection_isCoveringMap p.val)
    (surfaceProjection_isCoveringMap j p v hv) (surfaceProjection_fibre_finite j p v hv)

/-- The affine cover is a surjective covering with simply connected total
space, hence an actual universal cover of the elliptic surface. -/
theorem affineCoverProjection_universalCover :
    IsCoveringMap (affineCoverProjection j p v hv) ∧
      Function.Surjective (affineCoverProjection j p v hv) ∧
      SimplyConnectedSpace RealCoordinates :=
  ⟨affineCoverProjection_isCoveringMap j p v hv,
    affineCoverProjection_surjective j p v hv, realCoordinates_simplyConnectedSpace⟩

/-- The pointed universal lifting property of the affine projection through
any covering of the actual elliptic surface. -/
theorem affineCoverProjection_existsUnique_lift {Y : Type*} [TopologicalSpace Y]
    {q : Y → Surface j p v hv} (hq : IsCoveringMap q)
    (a : RealCoordinates) (b : Y) (hb : q b = affineCoverProjection j p v hv a) :
    ∃! F : ContinuousMap RealCoordinates Y,
      F a = b ∧ q ∘ F = affineCoverProjection j p v hv :=
  hq.existsUnique_continuousMap_lifts
    ⟨affineCoverProjection j p v hv, affineCoverProjection_continuous j p v hv⟩ a b hb

end Wikipedia.HopfProblem.Elliptic
