import Wikipedia.HopfProblem.MappingTorusTopologyCharts
import Wikipedia.HopfProblem.MappingTorusHomologyIntervals

/-!
# The actual two-arc open cover of a mapping torus

The cover is pulled back from the additive circle. Both members have
actual interval-product charts, and their intersection is the topological
sum of two interval products. The lower overlap has identity transition;
the upper overlap has transition `f` in the fibre coordinate.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.HopfProblem.MappingTorus.HomologyCover

open PeriodTorusHigherHomology.CircleTopology

variable {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)

/-- The first member omits the fibre over the circle origin. -/
def U : Set (Torus f) := {q | base f q ≠ ((0 : ℝ) : Circle)}

/-- The second member omits the opposite fibre. -/
def V : Set (Torus f) := {q | base f q ≠ ((-(1 / 2 : ℝ)) : Circle)}

theorem U_open : IsOpen (U f) := isOpen_compl_singleton.preimage (base f).continuous

theorem V_open : IsOpen (V f) := isOpen_compl_singleton.preimage (base f).continuous

theorem cover : U f ∪ V f = univ := by
  ext q
  simp only [mem_union, mem_univ, iff_true]
  by_cases hq : base f q = 0
  · right
    change base f q ≠ ((-(1 / 2 : ℝ)) : Circle)
    rw [hq]
    exact Ne.symm negativeHalf_coe_ne_zero
  · exact Or.inl hq

/-- The actual first lift takes values in `(0,1)`. -/
def chartU : U f ≃ₜ Ioo (0 : ℝ) 1 × X :=
  (intervalHomeomorph f 0).trans
    ((Homeomorph.setCongr (by simp : Ioo (0 : ℝ) (0 + 1) = Ioo 0 1)).prodCongr
      (Homeomorph.refl X))

/-- The actual second lift takes values in `(-1/2,1/2)`. -/
def chartV : V f ≃ₜ Ioo (-(1 / 2 : ℝ)) (1 / 2) × X :=
  (intervalHomeomorph f (-(1 / 2 : ℝ))).trans
    ((Homeomorph.setCongr
      (by norm_num : Ioo (-(1 / 2 : ℝ)) (-(1 / 2) + 1) = Ioo (-(1 / 2)) (1 / 2))).prodCongr
      (Homeomorph.refl X))

@[simp] theorem chartU_symm_coe (p : Ioo (0 : ℝ) 1 × X) :
    ((chartU f).symm p : Torus f) = mk f ((p.1 : ℝ), p.2) :=
  intervalHomeomorph_symm_coe f 0 _

@[simp] theorem chartV_symm_coe (p : Ioo (-(1 / 2 : ℝ)) (1 / 2) × X) :
    ((chartV f).symm p : Torus f) = mk f ((p.1 : ℝ), p.2) :=
  intervalHomeomorph_symm_coe f (-(1 / 2 : ℝ)) _

theorem chartU_mk (q : U f) (p : Ioo (0 : ℝ) 1 × X)
    (hq : (q : Torus f) = mk f ((p.1 : ℝ), p.2)) : chartU f q = p := by
  apply (chartU f).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (hq.trans (chartU_symm_coe f p).symm)

theorem chartV_mk (q : V f) (p : Ioo (-(1 / 2 : ℝ)) (1 / 2) × X)
    (hq : (q : Torus f) = mk f ((p.1 : ℝ), p.2)) : chartV f q = p := by
  apply (chartV f).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (hq.trans (chartV_symm_coe f p).symm)

theorem chartU_representation (q : U f) :
    mk f (((chartU f q).1 : ℝ), (chartU f q).2) = (q : Torus f) := by
  rw [← chartU_symm_coe, Homeomorph.symm_apply_apply]

theorem chartV_representation (q : V f) :
    mk f (((chartV f q).1 : ℝ), (chartV f q).2) = (q : Torus f) := by
  rw [← chartV_symm_coe, Homeomorph.symm_apply_apply]

theorem chartU_base (q : U f) :
    (((chartU f q).1 : ℝ) : Circle) = base f q := by
  have h := congrArg (base f) (chartU_representation f q)
  simpa only [base_mk] using h

theorem chartU_mem_V_iff (q : U f) :
    (q : Torus f) ∈ V f ↔ ((chartU f q).1 : ℝ) ≠ 1 / 2 := by
  change base f q ≠ ((-(1 / 2 : ℝ)) : Circle) ↔ _
  rw [← chartU_base]
  exact unitInterval_coe_ne_negativeHalf_iff _

/-- The actual intersection, first expressed as the punctured first chart. -/
def intersectionChart : ↥(U f ∩ V f) ≃ₜ
    {p : Ioo (0 : ℝ) 1 × X // (p.1 : ℝ) ≠ 1 / 2} :=
  (intersectionSubtypeHomeomorph (U f) (V f)).trans
    ((chartU f).subtype (chartU_mem_V_iff f))

/-- Its two genuine components, ordered by the real first-chart coordinate. -/
def intersectionHomeomorph : ↥(U f ∩ V f) ≃ₜ
    ((Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Ioo (1 / 2 : ℝ) 1 × X)) :=
  (intersectionChart f).trans (intervalIntersectionHomeomorph X)

@[simp] theorem intersectionHomeomorph_symm_inl_coe
    (p : Ioo (0 : ℝ) (1 / 2) × X) :
    ((intersectionHomeomorph f).symm (Sum.inl p) : Torus f) =
      mk f ((p.1 : ℝ), p.2) :=
  chartU_symm_coe f _

@[simp] theorem intersectionHomeomorph_symm_inr_coe
    (p : Ioo (1 / 2 : ℝ) 1 × X) :
    ((intersectionHomeomorph f).symm (Sum.inr p) : Torus f) =
      mk f ((p.1 : ℝ), p.2) :=
  chartU_symm_coe f _

def inclusionU : C(U f, Torus f) := ⟨Subtype.val, continuous_subtype_val⟩

def inclusionV : C(V f, Torus f) := ⟨Subtype.val, continuous_subtype_val⟩

def intersectionToU : C(↥(U f ∩ V f), U f) :=
  ContinuousMap.inclusion inter_subset_left

def intersectionToV : C(↥(U f ∩ V f), V f) :=
  ContinuousMap.inclusion inter_subset_right

/-- In the first chart both intersection components retain their fibre coordinate. -/
theorem chartU_intersection_inl (p : Ioo (0 : ℝ) (1 / 2) × X) :
    (chartU f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inl p)))).2 =
      p.2 := by
  exact congrArg Prod.snd
    (chartU_mk f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inl p)))
      ((puncturedIntervalInl p.1).val, p.2) (intersectionHomeomorph_symm_inl_coe f p))

theorem chartU_intersection_inr (p : Ioo (1 / 2 : ℝ) 1 × X) :
    (chartU f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inr p)))).2 =
      p.2 := by
  exact congrArg Prod.snd
    (chartU_mk f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inr p)))
      ((puncturedIntervalInr p.1).val, p.2) (intersectionHomeomorph_symm_inr_coe f p))

/-- On the lower overlap, the two actual fibre coordinates agree. -/
theorem chartV_intersection_inl (p : Ioo (0 : ℝ) (1 / 2) × X) :
    (chartV f (intersectionToV f ((intersectionHomeomorph f).symm (Sum.inl p)))).2 =
      p.2 := by
  let t : Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨p.1, by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  rw [chartV_mk f _ (t, p.2) (intersectionHomeomorph_symm_inl_coe f p)]

/-- On the upper overlap, the second lift is one period lower, so the
fibre coordinate changes by the actual homeomorphism `f`. -/
theorem chartV_intersection_inr (p : Ioo (1 / 2 : ℝ) 1 × X) :
    (chartV f (intersectionToV f ((intersectionHomeomorph f).symm (Sum.inr p)))).2 =
      f p.2 := by
  let t : Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨(p.1 : ℝ) - 1, by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  apply congrArg Prod.snd (chartV_mk f _ (t, f p.2) ?_)
  exact (intersectionHomeomorph_symm_inr_coe f p).trans (mk_sub_one f _ _).symm

end Wikipedia.HopfProblem.MappingTorus.HomologyCover
