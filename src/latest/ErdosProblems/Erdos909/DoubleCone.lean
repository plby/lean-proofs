/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Topology.Maps.Basic
import ErdosProblems.Erdos909.CubeSeparators

open Set Topology

namespace Erdos909.DoubleCone

open CubeSeparators

/-- The ambient vector space of the cubical double cone. -/
abbrev ConeAmbient (n : ℕ) := ℝ × (Fin n → ℝ)

/-- The radius of the section of the double cone at height `s`. -/
def coneScale (s : ℝ) : ℝ := 1 - |s|

/-- The quotient map from the `(n+1)`-cube.  Its first coordinate is the
height of the double cone; all the remaining coordinates are multiplied by
the section radius.  Consequently the two faces normal to coordinate zero
are collapsed to points. -/
def quotientRaw {n : ℕ} (x : Cube (n + 1)) : ConeAmbient n :=
  let s := 2 * x.1 0 - 1
  (s, fun i ↦ coneScale s * (2 * x.1 i.succ - 1))

theorem continuous_quotientRaw {n : ℕ} : Continuous (@quotientRaw n) := by
  let s : Cube (n + 1) → ℝ := fun x ↦ 2 * x.1 0 - 1
  have hs : Continuous s :=
    (continuous_const.mul
      ((continuous_apply (0 : Fin (n + 1))).comp continuous_subtype_val)).sub
      continuous_const
  apply hs.prodMk
  rw [continuous_pi_iff]
  intro i
  exact (continuous_const.sub hs.abs).mul
    ((continuous_const.mul
      ((continuous_apply i.succ).comp continuous_subtype_val)).sub continuous_const)

/-- The compact cubical double cone.  Defining it as the range of the
explicit quotient keeps the quotient property definitional; the geometric
inequality description is recorded below. -/
def DoubleCone (n : ℕ) : Set (ConeAmbient n) := Set.range (@quotientRaw n)

theorem isCompact_doubleCone (n : ℕ) : IsCompact (DoubleCone n) := by
  rw [DoubleCone]
  exact isCompact_range continuous_quotientRaw

instance (n : ℕ) : CompactSpace (DoubleCone n) :=
  isCompact_iff_compactSpace.mp (isCompact_doubleCone n)

/-- The quotient map, with its range as codomain. -/
def quotientMap {n : ℕ} (x : Cube (n + 1)) : DoubleCone n :=
  ⟨quotientRaw x, ⟨x, rfl⟩⟩

theorem continuous_quotientMap {n : ℕ} : Continuous (@quotientMap n) :=
  continuous_quotientRaw.subtype_mk _

theorem quotientMap_surjective {n : ℕ} : Function.Surjective (@quotientMap n) := by
  rintro ⟨p, x, rfl⟩
  exact ⟨x, rfl⟩

private def lowerCubePoint (n : ℕ) : Cube (n + 1) :=
  ⟨0, by constructor <;> simp⟩

private def upperCubePoint (n : ℕ) : Cube (n + 1) :=
  ⟨1, by constructor <;> simp⟩

/-- The lower vertex of the double cone. -/
def lowerEndpoint (n : ℕ) : DoubleCone n :=
  ⟨(-1, 0), lowerCubePoint n, by
    ext <;> simp [quotientRaw, lowerCubePoint, coneScale]⟩

/-- The upper vertex of the double cone. -/
def upperEndpoint (n : ℕ) : DoubleCone n :=
  ⟨(1, 0), upperCubePoint n, by
    ext <;> norm_num [quotientRaw, upperCubePoint, coneScale]⟩

theorem quotientMap_eq_lowerEndpoint_of_mem_lowerFace {n : ℕ}
    {x : Cube (n + 1)} (hx : x ∈ lowerFace (0 : Fin (n + 1))) :
    quotientMap x = lowerEndpoint n := by
  have hx0 : x.1 (0 : Fin (n + 1)) = 0 := hx
  apply Subtype.ext
  apply Prod.ext
  · simp [quotientMap, quotientRaw, lowerEndpoint, hx0]
  · funext i
    simp [quotientMap, quotientRaw, lowerEndpoint, coneScale, hx0]

theorem quotientMap_eq_upperEndpoint_of_mem_upperFace {n : ℕ}
    {x : Cube (n + 1)} (hx : x ∈ upperFace (0 : Fin (n + 1))) :
    quotientMap x = upperEndpoint n := by
  have hx0 : x.1 (0 : Fin (n + 1)) = 1 := hx
  apply Subtype.ext
  apply Prod.ext
  · norm_num [quotientMap, quotientRaw, upperEndpoint, hx0]
  · funext i
    norm_num [quotientMap, quotientRaw, upperEndpoint, coneScale, hx0]

theorem mem_lowerFace_of_quotientMap_eq_lowerEndpoint {n : ℕ}
    {x : Cube (n + 1)} (hx : quotientMap x = lowerEndpoint n) :
    x ∈ lowerFace (0 : Fin (n + 1)) := by
  have h := congrArg (fun p : DoubleCone n ↦ p.1.1) hx
  simp [quotientMap, quotientRaw, lowerEndpoint, lowerFace] at h ⊢
  linarith

theorem mem_upperFace_of_quotientMap_eq_upperEndpoint {n : ℕ}
    {x : Cube (n + 1)} (hx : quotientMap x = upperEndpoint n) :
    x ∈ upperFace (0 : Fin (n + 1)) := by
  have h := congrArg (fun p : DoubleCone n ↦ p.1.1) hx
  simp [quotientMap, quotientRaw, upperEndpoint, upperFace] at h ⊢
  linarith

/-- The cube with the two collapsed faces deleted. -/
abbrev CubeWithoutEndFaces (n : ℕ) :=
  {x : Cube (n + 1) //
    x ∉ lowerFace (0 : Fin (n + 1)) ∧ x ∉ upperFace (0 : Fin (n + 1))}

/-- The double cone with its two vertices deleted. -/
abbrev DoubleConeWithoutEndpoints (n : ℕ) :=
  {p : DoubleCone n // p ≠ lowerEndpoint n ∧ p ≠ upperEndpoint n}

def interiorQuotientMap {n : ℕ} (x : CubeWithoutEndFaces n) :
    DoubleConeWithoutEndpoints n :=
  ⟨quotientMap x.1,
    ⟨fun h ↦ x.2.1 (mem_lowerFace_of_quotientMap_eq_lowerEndpoint h),
      fun h ↦ x.2.2 (mem_upperFace_of_quotientMap_eq_upperEndpoint h)⟩⟩

theorem continuous_interiorQuotientMap {n : ℕ} :
    Continuous (@interiorQuotientMap n) :=
  by
    apply Continuous.subtype_mk
    exact continuous_quotientMap.comp continuous_subtype_val

private theorem first_mem_Icc {n : ℕ} (p : DoubleCone n) :
    p.1.1 ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases p.2 with ⟨x, hx⟩
  rw [← hx]
  have hxlo : (0 : ℝ) ≤ x.1 (0 : Fin (n + 1)) := x.2.1 (0 : Fin (n + 1))
  have hxhi : x.1 (0 : Fin (n + 1)) ≤ (1 : ℝ) := x.2.2 (0 : Fin (n + 1))
  constructor
  · simp only [quotientRaw]
    linarith
  · simp only [quotientRaw]
    linarith

private theorem eq_lowerEndpoint_of_first_eq {n : ℕ} (p : DoubleCone n)
    (hp : p.1.1 = -1) : p = lowerEndpoint n := by
  rcases p.2 with ⟨x, hx⟩
  have hx0 : x.1 (0 : Fin (n + 1)) = 0 := by
    have h := congrArg Prod.fst hx
    simp only [quotientRaw] at h
    linarith
  apply Subtype.ext
  rw [← hx]
  apply Prod.ext
  · norm_num [quotientRaw, lowerEndpoint, hx0]
  · funext i
    norm_num [quotientRaw, lowerEndpoint, coneScale, hx0]

private theorem eq_upperEndpoint_of_first_eq {n : ℕ} (p : DoubleCone n)
    (hp : p.1.1 = 1) : p = upperEndpoint n := by
  rcases p.2 with ⟨x, hx⟩
  have hx0 : x.1 (0 : Fin (n + 1)) = 1 := by
    have h := congrArg Prod.fst hx
    simp only [quotientRaw] at h
    linarith
  apply Subtype.ext
  rw [← hx]
  apply Prod.ext
  · norm_num [quotientRaw, upperEndpoint, hx0]
  · funext i
    norm_num [quotientRaw, upperEndpoint, coneScale, hx0]

private theorem coneScale_pos {n : ℕ} (p : DoubleConeWithoutEndpoints n) :
    0 < coneScale p.1.1.1 := by
  have hpI := first_mem_Icc p.1
  have hlo : -1 < p.1.1.1 := lt_of_le_of_ne hpI.1 (fun h ↦
    p.2.1 (eq_lowerEndpoint_of_first_eq p.1 h.symm))
  have hhi : p.1.1.1 < 1 := lt_of_le_of_ne hpI.2 (fun h ↦
    p.2.2 (eq_upperEndpoint_of_first_eq p.1 h))
  have habs : |p.1.1.1| < 1 := (abs_lt).2 ⟨by linarith, hhi⟩
  simpa [coneScale] using sub_pos.mpr habs

/-- The explicit inverse coordinates away from the two vertices. -/
noncomputable def inverseRaw {n : ℕ} (p : DoubleConeWithoutEndpoints n) : Fin (n + 1) → ℝ :=
  Fin.cases ((p.1.1.1 + 1) / 2)
    (fun i ↦ ((p.1.1.2 i / coneScale p.1.1.1) + 1) / 2)

private theorem inverseRaw_eq_of_quotientMap_eq {n : ℕ}
    (p : DoubleConeWithoutEndpoints n) (x : Cube (n + 1))
    (hx : quotientMap x = p.1) : inverseRaw p = x.1 := by
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · have h := congrArg (fun z : DoubleCone n ↦ z.1.1) hx
    simp only [quotientMap, quotientRaw, inverseRaw, Fin.cases_zero]
    simp only [quotientMap, quotientRaw] at h
    linarith
  · have hs := congrArg (fun z : DoubleCone n ↦ z.1.1) hx
    have hz := congrArg (fun z : DoubleCone n ↦ z.1.2 i) hx
    have hscale : coneScale p.1.1.1 ≠ 0 := ne_of_gt (coneScale_pos p)
    simp only [quotientMap, quotientRaw] at hs hz
    simp only [inverseRaw, Fin.cases_succ]
    rw [← hs] at hscale ⊢
    rw [← hz]
    field_simp
    ring

noncomputable def interiorInverse {n : ℕ} (p : DoubleConeWithoutEndpoints n) :
    CubeWithoutEndFaces n := by
  let x : Cube (n + 1) := Classical.choose p.1.2
  have hx : quotientMap x = p.1 := Subtype.ext (Classical.choose_spec p.1.2)
  have hraw : inverseRaw p = x.1 := inverseRaw_eq_of_quotientMap_eq p x hx
  refine ⟨⟨inverseRaw p, ?_⟩, ?_⟩
  · rw [hraw]
    exact x.2
  · constructor
    · intro hface
      apply p.2.1
      rw [← hx]
      apply quotientMap_eq_lowerEndpoint_of_mem_lowerFace
      simpa [hraw] using hface
    · intro hface
      apply p.2.2
      rw [← hx]
      apply quotientMap_eq_upperEndpoint_of_mem_upperFace
      simpa [hraw] using hface

theorem continuous_inverseRaw {n : ℕ} : Continuous (@inverseRaw n) := by
  rw [continuous_pi_iff]
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact (((continuous_fst.comp
      (continuous_subtype_val.comp continuous_subtype_val)).add continuous_const).div_const 2)
  · have hs : Continuous (fun p : DoubleConeWithoutEndpoints n ↦ p.1.1.1) :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hz : Continuous (fun p : DoubleConeWithoutEndpoints n ↦ p.1.1.2 i) :=
      (continuous_apply i).comp
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))
    have hscale : Continuous (fun p : DoubleConeWithoutEndpoints n ↦
        coneScale p.1.1.1) := continuous_const.sub hs.abs
    exact (((hz.div hscale (fun p ↦ ne_of_gt (coneScale_pos p))).add continuous_const).div_const 2)

theorem continuous_interiorInverse {n : ℕ} : Continuous (@interiorInverse n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  simpa only [interiorInverse] using (@continuous_inverseRaw n)

/-- Away from the two collapsed faces, the quotient is a homeomorphism onto
the double cone with its vertices removed. -/
noncomputable def interiorHomeomorph (n : ℕ) :
    CubeWithoutEndFaces n ≃ₜ DoubleConeWithoutEndpoints n where
  toFun := interiorQuotientMap
  invFun := interiorInverse
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact inverseRaw_eq_of_quotientMap_eq (interiorQuotientMap x) x.1 rfl
  right_inv p := by
    apply Subtype.ext
    let x : Cube (n + 1) := Classical.choose p.1.2
    have hx : quotientMap x = p.1 := Subtype.ext (Classical.choose_spec p.1.2)
    apply Subtype.ext
    change quotientRaw (interiorInverse p).1 = p.1.1
    rw [show (interiorInverse p).1 = x from Subtype.ext
      (inverseRaw_eq_of_quotientMap_eq p x hx)]
    exact Classical.choose_spec p.1.2
  continuous_toFun := continuous_interiorQuotientMap
  continuous_invFun := continuous_interiorInverse

/-! ### A finite cubical open cover away from the vertices -/

/-- One of the `2^n` standard open patches of the punctured double cone.
The Boolean `true` chooses `y_i < 2/3`, and `false` chooses `1/3 < y_i`,
where `y` denotes the inverse cube coordinate. -/
def coordinatePatch {n : ℕ} (sign : Fin n → Bool) :
    Set (DoubleConeWithoutEndpoints n) :=
  {p | ∀ i, if sign i = true then inverseRaw p i.succ < (2 : ℝ) / 3
    else (1 : ℝ) / 3 < inverseRaw p i.succ}

theorem isOpen_coordinatePatch {n : ℕ} (sign : Fin n → Bool) :
    IsOpen (coordinatePatch sign) := by
  rw [show coordinatePatch sign = ⋂ i, {p |
      if sign i = true then inverseRaw p i.succ < (2 : ℝ) / 3
      else (1 : ℝ) / 3 < inverseRaw p i.succ} by
    ext p
    simp [coordinatePatch]]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : sign i
  · simp only [hi, if_true]
    exact isOpen_lt ((continuous_apply i.succ).comp (@continuous_inverseRaw n)) continuous_const
  · have hi' : sign i = false := Bool.eq_false_of_not_eq_true hi
    simp only [hi', Bool.false_eq, if_false]
    exact isOpen_lt continuous_const
      ((continuous_apply i.succ).comp (@continuous_inverseRaw n))

/-- The standard patches cover the punctured double cone. -/
theorem mem_coordinatePatch_some {n : ℕ} (p : DoubleConeWithoutEndpoints n) :
    ∃ sign : Fin n → Bool, p ∈ coordinatePatch sign := by
  classical
  let sign : Fin n → Bool := fun i ↦ decide (inverseRaw p i.succ < (2 : ℝ) / 3)
  refine ⟨sign, fun i ↦ ?_⟩
  by_cases hi : inverseRaw p i.succ < (2 : ℝ) / 3
  · simp [sign, hi]
  · have hi' : (2 : ℝ) / 3 ≤ inverseRaw p i.succ := le_of_not_gt hi
    simp [sign, hi]
    linarith

theorem iUnion_coordinatePatch {n : ℕ} :
    (⋃ sign : Fin n → Bool, coordinatePatch sign) = Set.univ := by
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  exact mem_coordinatePatch_some p

/-- In a `true` patch, the pullback misses the corresponding upper face; in
a `false` patch it misses the corresponding lower face. -/
theorem coordinatePatch_preimage_avoids_tail_face {n : ℕ}
    (sign : Fin n → Bool) (i : Fin n) (x : CubeWithoutEndFaces n)
    (hx : interiorQuotientMap x ∈ coordinatePatch sign) :
    if sign i = true then x.1 ∉ upperFace i.succ else x.1 ∉ lowerFace i.succ := by
  have hinv : inverseRaw (interiorQuotientMap x) = x.1.1 :=
    inverseRaw_eq_of_quotientMap_eq (interiorQuotientMap x) x.1 rfl
  by_cases hi : sign i = true
  · simp only [hi, if_true]
    intro hface
    have hlt := hx i
    simp only [hi, if_true, hinv] at hlt
    have heq : x.1.1 i.succ = 1 := hface
    linarith
  · simp only [hi, if_false]
    intro hface
    have hgt := hx i
    simp only [hi, if_false, hinv] at hgt
    simp at hgt
    have heq : x.1.1 i.succ = 0 := hface
    linarith

private theorem isOpen_nonendpoints (n : ℕ) :
    IsOpen {p : DoubleCone n | p ≠ lowerEndpoint n ∧ p ≠ upperEndpoint n} :=
  isOpen_ne.inter isOpen_ne

/-- The ambient-open version of `coordinatePatch`. -/
def goodOpenPatch {n : ℕ} (sign : Fin n → Bool) : Set (DoubleCone n) :=
  ((↑) : DoubleConeWithoutEndpoints n → DoubleCone n) '' coordinatePatch sign

theorem isOpen_goodOpenPatch {n : ℕ} (sign : Fin n → Bool) :
    IsOpen (goodOpenPatch sign) := by
  exact (isOpen_nonendpoints n).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp
    (isOpen_coordinatePatch sign)

theorem goodOpenPatch_subset_nonendpoints {n : ℕ} (sign : Fin n → Bool) :
    goodOpenPatch sign ⊆
      {p : DoubleCone n | p ≠ lowerEndpoint n ∧ p ≠ upperEndpoint n} := by
  rintro _ ⟨p, -, rfl⟩
  exact p.2

/-- Every non-vertex point belongs to one of the finite family of ambient
open patches. -/
theorem nonendpoint_mem_goodOpenPatch_some {n : ℕ} {p : DoubleCone n}
    (hp : p ≠ lowerEndpoint n ∧ p ≠ upperEndpoint n) :
    ∃ sign : Fin n → Bool, p ∈ goodOpenPatch sign := by
  obtain ⟨sign, hsign⟩ := mem_coordinatePatch_some (⟨p, hp⟩ : DoubleConeWithoutEndpoints n)
  exact ⟨sign, ⟨⟨p, hp⟩, hsign, rfl⟩⟩

theorem nonendpoints_subset_iUnion_goodOpenPatch {n : ℕ} :
    {p : DoubleCone n | p ≠ lowerEndpoint n ∧ p ≠ upperEndpoint n} ⊆
      ⋃ sign : Fin n → Bool, goodOpenPatch sign := by
  intro p hp
  obtain ⟨sign, hsign⟩ := nonendpoint_mem_goodOpenPatch_some hp
  exact mem_iUnion.2 ⟨sign, hsign⟩

/-- No good patch has a pullback meeting both opposite faces in any cube
coordinate.  This is the exact finite-cover input needed by the cubical
Lebesgue partition argument. -/
theorem goodOpenPatch_preimage_not_meets_both_faces {n : ℕ}
    (sign : Fin n → Bool) (j : Fin (n + 1)) :
    ¬ (((quotientMap ⁻¹' goodOpenPatch sign) ∩ lowerFace j).Nonempty ∧
      ((quotientMap ⁻¹' goodOpenPatch sign) ∩ upperFace j).Nonempty) := by
  revert j
  refine Fin.cases ?_ (fun i ↦ ?_)
  · intro hboth
    rcases hboth.1 with ⟨x, hxpatch, hxface⟩
    have hqlo := quotientMap_eq_lowerEndpoint_of_mem_lowerFace hxface
    exact (goodOpenPatch_subset_nonendpoints sign hxpatch).1 hqlo
  · intro hboth
    rcases hboth.1 with ⟨xlo, hxloPatch, hxloFace⟩
    rcases hboth.2 with ⟨xhi, hxhiPatch, hxhiFace⟩
    rcases hxloPatch with ⟨plo, hplo, hploEq⟩
    rcases hxhiPatch with ⟨phi, hphi, hphiEq⟩
    have hxloEnds : xlo ∉ lowerFace (0 : Fin (n + 1)) ∧
        xlo ∉ upperFace (0 : Fin (n + 1)) := by
      constructor
      · intro hface
        exact plo.2.1 (hploEq.trans
          (quotientMap_eq_lowerEndpoint_of_mem_lowerFace hface))
      · intro hface
        exact plo.2.2 (hploEq.trans
          (quotientMap_eq_upperEndpoint_of_mem_upperFace hface))
    have hxhiEnds : xhi ∉ lowerFace (0 : Fin (n + 1)) ∧
        xhi ∉ upperFace (0 : Fin (n + 1)) := by
      constructor
      · intro hface
        exact phi.2.1 (hphiEq.trans
          (quotientMap_eq_lowerEndpoint_of_mem_lowerFace hface))
      · intro hface
        exact phi.2.2 (hphiEq.trans
          (quotientMap_eq_upperEndpoint_of_mem_upperFace hface))
    let xlo' : CubeWithoutEndFaces n := ⟨xlo, hxloEnds⟩
    let xhi' : CubeWithoutEndFaces n := ⟨xhi, hxhiEnds⟩
    have hplo' : interiorQuotientMap xlo' ∈ coordinatePatch sign := by
      rw [show interiorQuotientMap xlo' = plo by
        apply Subtype.ext
        exact hploEq.symm]
      exact hplo
    have hphi' : interiorQuotientMap xhi' ∈ coordinatePatch sign := by
      rw [show interiorQuotientMap xhi' = phi by
        apply Subtype.ext
        exact hphiEq.symm]
      exact hphi
    by_cases hs : sign i = true
    · have hav := coordinatePatch_preimage_avoids_tail_face sign i xhi' hphi'
      simp only [hs, if_true] at hav
      exact hav hxhiFace
    · have hav := coordinatePatch_preimage_avoids_tail_face sign i xlo' hplo'
      simp only [hs, if_false] at hav
      exact hav hxloFace

/-- The finite good-cover package used by the Mazurkiewicz argument.  Each
member is ambient-open, the family covers the complement of the two
vertices, and no pullback member meets both faces in any coordinate. -/
theorem exists_good_open_cover (n : ℕ) :
    ∃ k : ℕ, ∃ U : Fin k → Set (DoubleCone n),
      (∀ a, IsOpen (U a)) ∧
      ({lowerEndpoint n, upperEndpoint n}ᶜ ⊆ ⋃ a, U a) ∧
      (∀ a, lowerEndpoint n ∉ U a ∧ upperEndpoint n ∉ U a) ∧
      ∀ a (j : Fin (n + 1)),
        ¬ (((quotientMap ⁻¹' U a) ∩ lowerFace j).Nonempty ∧
          ((quotientMap ⁻¹' U a) ∩ upperFace j).Nonempty) := by
  classical
  let e : (Fin n → Bool) ≃ Fin (Fintype.card (Fin n → Bool)) := Fintype.equivFin _
  refine ⟨Fintype.card (Fin n → Bool),
    fun a ↦ goodOpenPatch (e.symm a), ?_, ?_, ?_, ?_⟩
  · exact fun a ↦ isOpen_goodOpenPatch (e.symm a)
  · intro p hp
    have hp' : p ≠ lowerEndpoint n ∧ p ≠ upperEndpoint n := by
      simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using hp
    obtain ⟨sign, hsign⟩ := nonendpoint_mem_goodOpenPatch_some hp'
    exact mem_iUnion.2 ⟨e sign, by simpa using hsign⟩
  · intro a
    constructor
    · intro hmem
      exact (goodOpenPatch_subset_nonendpoints (e.symm a) hmem).1 rfl
    · intro hmem
      exact (goodOpenPatch_subset_nonendpoints (e.symm a) hmem).2 rfl
  · intro a j
    exact goodOpenPatch_preimage_not_meets_both_faces (e.symm a) j

/-! ### Pulling endpoint separators back to cube-face separators -/

/-- A separator of the two vertices, with the lower vertex on the `U` side
and the upper vertex on the `V` side. -/
def SeparatesEndpoints {n : ℕ} (L : Set (DoubleCone n)) : Prop :=
  ∃ U V : Set (DoubleCone n), IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
    U ∪ V = Lᶜ ∧ lowerEndpoint n ∈ U ∧ upperEndpoint n ∈ V

/-- Pullback of an endpoint separator is a separator of the two cube faces
normal to coordinate zero. -/
theorem separatesFaces_preimage_quotientMap {n : ℕ} {L : Set (DoubleCone n)}
    (hL : SeparatesEndpoints L) :
    SeparatesFaces (0 : Fin (n + 1)) (quotientMap ⁻¹' L) := by
  rcases hL with ⟨U, V, hU, hV, hUV, hcover, hlo, hhi⟩
  refine ⟨quotientMap ⁻¹' U, quotientMap ⁻¹' V,
    hU.preimage continuous_quotientMap, hV.preimage continuous_quotientMap,
    Set.disjoint_left.mpr (fun _ hxU hxV ↦ Set.disjoint_left.mp hUV hxU hxV), ?_, ?_, ?_⟩
  · rw [← preimage_union, hcover, preimage_compl]
  · intro x hx
    change quotientMap x ∈ U
    simpa [quotientMap_eq_lowerEndpoint_of_mem_lowerFace hx] using hlo
  · intro x hx
    change quotientMap x ∈ V
    simpa [quotientMap_eq_upperEndpoint_of_mem_upperFace hx] using hhi

/-- A direct interface for the closed/open separator decomposition produced
by `MazurkiewiczComponents`. -/
theorem separatesFaces_preimage_of_decomposition {n : ℕ}
    {S P Q : Set (DoubleCone n)} (_hS : IsClosed S)
    (hP : IsOpen P) (hQ : IsOpen Q) (hPQ : Disjoint P Q)
    (hcover : Sᶜ = P ∪ Q) (hlo : lowerEndpoint n ∈ P)
    (hhi : upperEndpoint n ∈ Q) :
    SeparatesFaces (0 : Fin (n + 1)) (quotientMap ⁻¹' S) := by
  apply separatesFaces_preimage_quotientMap
  exact ⟨P, Q, hP, hQ, hPQ, hcover.symm, hlo, hhi⟩

end Erdos909.DoubleCone
