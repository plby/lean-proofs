import Wikipedia.HopfProblem.MappingTorusHomologyCover

/-!
# A shorter two-arc cover of a mapping torus

The two members are the actual images of the open cylinders with time intervals
`(1/8,7/8)` and `(-3/8,3/8)`. Their intersection consists of the two shorter
overlap cylinders, with unchanged fibre coordinates in the first chart.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.RefinedWang

open MappingTorus

variable {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)

/-- The first shortened open cylinder. -/
def U : Set (Torus φ) :=
  mk φ '' (Ioo (1 / 8 : ℝ) (7 / 8) ×ˢ (univ : Set X))

/-- The second shortened open cylinder, crossing time zero. -/
def V : Set (Torus φ) :=
  mk φ '' (Ioo (-(3 / 8 : ℝ)) (3 / 8) ×ˢ (univ : Set X))

theorem mem_U_iff {q : Torus φ} :
    q ∈ U φ ↔ ∃ (t : ℝ) (x : X),
      1 / 8 < t ∧ t < 7 / 8 ∧ mk φ (t, x) = q := by
  constructor
  · rintro ⟨⟨t, x⟩, ⟨ht, _⟩, hq⟩
    exact ⟨t, x, ht.1, ht.2, hq⟩
  · rintro ⟨t, x, ht, ht', hq⟩
    exact ⟨(t, x), ⟨⟨ht, ht'⟩, mem_univ x⟩, hq⟩

theorem mem_V_iff {q : Torus φ} :
    q ∈ V φ ↔ ∃ (t : ℝ) (x : X),
      -(3 / 8) < t ∧ t < 3 / 8 ∧ mk φ (t, x) = q := by
  constructor
  · rintro ⟨⟨t, x⟩, ⟨ht, _⟩, hq⟩
    exact ⟨t, x, ht.1, ht.2, hq⟩
  · rintro ⟨t, x, ht, ht', hq⟩
    exact ⟨(t, x), ⟨⟨ht, ht'⟩, mem_univ x⟩, hq⟩

theorem U_open : IsOpen (U φ) :=
  mk_open φ _ (isOpen_Ioo.prod isOpen_univ)

theorem V_open : IsOpen (V φ) :=
  mk_open φ _ (isOpen_Ioo.prod isOpen_univ)

theorem U_subset : U φ ⊆ HomologyCover.U φ := by
  intro q hq
  obtain ⟨t, x, ht, ht', rfl⟩ := (mem_U_iff φ).mp hq
  exact base_mk_ne_of_mem_Ioo φ 0
    ⟨t, by constructor <;> linarith⟩ x

theorem V_subset : V φ ⊆ HomologyCover.V φ := by
  intro q hq
  obtain ⟨t, x, ht, ht', rfl⟩ := (mem_V_iff φ).mp hq
  exact base_mk_ne_of_mem_Ioo φ (-(1 / 2 : ℝ))
    ⟨t, by constructor <;> linarith⟩ x

/-- The shorter cylinders still cover the actual quotient. -/
theorem cover : U φ ∪ V φ = univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hq : q ∈ HomologyCover.U φ ∪ HomologyCover.V φ := by
    rw [HomologyCover.cover]
    exact mem_univ q
  rcases hq with hq | hq
  · let p := HomologyCover.chartU φ ⟨q, hq⟩
    let t : ℝ := p.1
    have ht : 0 < t ∧ t < 1 := p.1.property
    have hp : mk φ (t, p.2) = q := HomologyCover.chartU_representation φ ⟨q, hq⟩
    by_cases hu : 1 / 8 < t ∧ t < 7 / 8
    · exact Or.inl ((mem_U_iff φ).mpr ⟨t, p.2, hu.1, hu.2, hp⟩)
    · apply Or.inr
      apply (mem_V_iff φ).mpr
      by_cases hs : t < 3 / 8
      · exact ⟨t, p.2, by linarith, hs, hp⟩
      · have hl : 7 / 8 ≤ t := by
          by_contra hl
          apply hu
          constructor <;> linarith
        exact ⟨t - 1, φ p.2, by linarith, by linarith,
          (mk_sub_one φ t p.2).trans hp⟩
  · let p := HomologyCover.chartV φ ⟨q, hq⟩
    let t : ℝ := p.1
    have ht : -(1 / 2) < t ∧ t < 1 / 2 := p.1.property
    have hp : mk φ (t, p.2) = q := HomologyCover.chartV_representation φ ⟨q, hq⟩
    by_cases hv : -(3 / 8) < t ∧ t < 3 / 8
    · exact Or.inr ((mem_V_iff φ).mpr ⟨t, p.2, hv.1, hv.2, hp⟩)
    · apply Or.inl
      apply (mem_U_iff φ).mpr
      by_cases hs : 1 / 8 < t
      · exact ⟨t, p.2, hs, by linarith, hp⟩
      · have hl : t ≤ -(3 / 8) := by
          by_contra hl
          apply hv
          constructor <;> linarith
        refine ⟨t + 1, φ.symm p.2, by linarith, by linarith, ?_⟩
        exact (mk_add_one φ t (φ.symm p.2)).trans
          (by simpa only [Homeomorph.apply_symm_apply] using hp)

/-- Inclusion of the genuine refined intersection into the original one. -/
def intersectionInclusion :
    C(↥(U φ ∩ V φ), ↥(HomologyCover.U φ ∩ HomologyCover.V φ)) :=
  ContinuousMap.inclusion (inter_subset_inter (U_subset φ) (V_subset φ))

@[simp] theorem intersectionInclusion_coe (q : ↥(U φ ∩ V φ)) :
    ((intersectionInclusion φ q : ↥(HomologyCover.U φ ∩ HomologyCover.V φ)) : Torus φ) =
      (q : Torus φ) := rfl

/-- The lower overlap interval. -/
abbrev LowerInterval := Ioo (1 / 8 : ℝ) (3 / 8)

/-- The upper overlap interval, in the first cylinder's coordinates. -/
abbrev UpperInterval := Ioo (5 / 8 : ℝ) (7 / 8)

private def lowerParam (p : LowerInterval × X) : ↥(U φ ∩ V φ) :=
  ⟨mk φ ((p.1 : ℝ), p.2),
    (mem_U_iff φ).mpr ⟨p.1, p.2, p.1.property.1,
      by linarith [p.1.property.2], rfl⟩,
    (mem_V_iff φ).mpr ⟨p.1, p.2,
      by linarith [p.1.property.1], p.1.property.2, rfl⟩⟩

private def upperParam (p : UpperInterval × X) : ↥(U φ ∩ V φ) :=
  ⟨mk φ ((p.1 : ℝ), p.2),
    (mem_U_iff φ).mpr ⟨p.1, p.2,
      by linarith [p.1.property.1], p.1.property.2, rfl⟩,
    (mem_V_iff φ).mpr ⟨(p.1 : ℝ) - 1, φ p.2,
      by linarith [p.1.property.1], by linarith [p.1.property.2],
      mk_sub_one φ (p.1 : ℝ) p.2⟩⟩

private theorem lowerParam_continuous : Continuous (lowerParam φ) :=
  ((mk_continuous φ).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

private theorem upperParam_continuous : Continuous (upperParam φ) :=
  ((mk_continuous φ).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

private theorem lowerParam_open : IsOpenMap (lowerParam φ) :=
  ((mk_open φ).comp
    (isOpen_Ioo.isOpenMap_subtype_val.prodMap IsOpenMap.id)).subtype_mk _

private theorem upperParam_open : IsOpenMap (upperParam φ) :=
  ((mk_open φ).comp
    (isOpen_Ioo.isOpenMap_subtype_val.prodMap IsOpenMap.id)).subtype_mk _

private theorem lowerParam_inclusion (p : LowerInterval × X) :
    intersectionInclusion φ (lowerParam φ p) =
      (HomologyCover.intersectionHomeomorph φ).symm
        (Sum.inl (⟨(p.1 : ℝ), by
          constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2)) := by
  apply Subtype.ext
  rw [HomologyCover.intersectionHomeomorph_symm_inl_coe]
  rfl

private theorem upperParam_inclusion (p : UpperInterval × X) :
    intersectionInclusion φ (upperParam φ p) =
      (HomologyCover.intersectionHomeomorph φ).symm
        (Sum.inr (⟨(p.1 : ℝ), by
          constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2)) := by
  apply Subtype.ext
  rw [HomologyCover.intersectionHomeomorph_symm_inr_coe]
  rfl

private theorem lowerParam_oldChart (p : LowerInterval × X) :
    HomologyCover.intersectionHomeomorph φ (intersectionInclusion φ (lowerParam φ p)) =
      Sum.inl (⟨(p.1 : ℝ), by
        constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2) := by
  rw [lowerParam_inclusion, Homeomorph.apply_symm_apply]

private theorem upperParam_oldChart (p : UpperInterval × X) :
    HomologyCover.intersectionHomeomorph φ (intersectionInclusion φ (upperParam φ p)) =
      Sum.inr (⟨(p.1 : ℝ), by
        constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2) := by
  rw [upperParam_inclusion, Homeomorph.apply_symm_apply]

private def intersectionParam :
    ((LowerInterval × X) ⊕ (UpperInterval × X)) → ↥(U φ ∩ V φ) :=
  Sum.elim (lowerParam φ) (upperParam φ)

private theorem intersectionParam_injective : Function.Injective (intersectionParam φ) := by
  intro p q hpq
  have he := congrArg
    (fun q => HomologyCover.intersectionHomeomorph φ (intersectionInclusion φ q)) hpq
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      simp only [intersectionParam, Sum.elim_inl, lowerParam_oldChart,
        Sum.inl.injEq, Prod.mk.injEq] at he
      have ht : (p.1 : ℝ) = (q.1 : ℝ) :=
        congrArg (fun z : Ioo (0 : ℝ) (1 / 2) => (z : ℝ)) he.1
      exact congrArg Sum.inl (Prod.ext (Subtype.ext ht) he.2)
    | inr q =>
      simp only [intersectionParam, Sum.elim_inl, Sum.elim_inr,
        lowerParam_oldChart, upperParam_oldChart, Sum.inl_ne_inr] at he
  | inr p =>
    cases q with
    | inl q =>
      simp only [intersectionParam, Sum.elim_inl, Sum.elim_inr,
        lowerParam_oldChart, upperParam_oldChart, Sum.inr_ne_inl] at he
    | inr q =>
      simp only [intersectionParam, Sum.elim_inr, upperParam_oldChart,
        Sum.inr.injEq, Prod.mk.injEq] at he
      have ht : (p.1 : ℝ) = (q.1 : ℝ) :=
        congrArg (fun z : Ioo (1 / 2 : ℝ) 1 => (z : ℝ)) he.1
      exact congrArg Sum.inr (Prod.ext (Subtype.ext ht) he.2)

private theorem intersectionParam_surjective : Function.Surjective (intersectionParam φ) := by
  intro q
  obtain ⟨t, x, ht, ht', hu⟩ := (mem_U_iff φ).mp q.property.1
  obtain ⟨s, y, hs, hs', hv⟩ := (mem_V_iff φ).mp q.property.2
  obtain ⟨n, hn, _⟩ := (mk_eq_mk_iff φ (t, x) (s, y)).mp (hu.trans hv.symm)
  dsimp only at hn
  have hnloR : (-2 : ℝ) < (n : ℝ) := by linarith
  have hnhiR : (n : ℝ) < 1 := by linarith
  have hnlo : (-2 : ℤ) < n := by exact_mod_cast hnloR
  have hnhi : n < 1 := by exact_mod_cast hnhiR
  have hn0 : n = 0 ∨ n = -1 := by omega
  rcases hn0 with rfl | rfl
  · simp only [Int.cast_zero, add_zero] at hn
    refine ⟨Sum.inl (⟨t, ht, by linarith⟩, x), ?_⟩
    exact Subtype.ext hu
  · simp only [Int.cast_neg, Int.cast_one] at hn
    refine ⟨Sum.inr (⟨t, by linarith, ht'⟩, x), ?_⟩
    exact Subtype.ext hu

/-- The actual refined overlap is the sum of its two shorter cylinder charts. -/
def intersectionHomeomorph : ↥(U φ ∩ V φ) ≃ₜ
    ((LowerInterval × X) ⊕ (UpperInterval × X)) :=
  ((Equiv.ofBijective (intersectionParam φ)
    ⟨intersectionParam_injective φ, intersectionParam_surjective φ⟩).toHomeomorphOfContinuousOpen
      ((lowerParam_continuous φ).sumElim (upperParam_continuous φ))
      ((lowerParam_open φ).sumElim (upperParam_open φ))).symm

@[simp] theorem intersectionHomeomorph_symm_inl_coe (p : LowerInterval × X) :
    ((intersectionHomeomorph φ).symm (Sum.inl p) : Torus φ) =
      mk φ ((p.1 : ℝ), p.2) := rfl

@[simp] theorem intersectionHomeomorph_symm_inr_coe (p : UpperInterval × X) :
    ((intersectionHomeomorph φ).symm (Sum.inr p) : Torus φ) =
      mk φ ((p.1 : ℝ), p.2) := rfl

/-- Refinement leaves the actual lower-overlap coordinates unchanged. -/
theorem intersectionHomeomorph_symm_inl_inclusion (p : LowerInterval × X) :
    intersectionInclusion φ ((intersectionHomeomorph φ).symm (Sum.inl p)) =
      (HomologyCover.intersectionHomeomorph φ).symm
        (Sum.inl (⟨(p.1 : ℝ), by
          constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2)) :=
  lowerParam_inclusion φ p

/-- Refinement also leaves the actual upper-overlap coordinates unchanged. -/
theorem intersectionHomeomorph_symm_inr_inclusion (p : UpperInterval × X) :
    intersectionInclusion φ ((intersectionHomeomorph φ).symm (Sum.inr p)) =
      (HomologyCover.intersectionHomeomorph φ).symm
        (Sum.inr (⟨(p.1 : ℝ), by
          constructor <;> linarith [p.1.property.1, p.1.property.2]⟩, p.2)) :=
  upperParam_inclusion φ p

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.RefinedWang
