import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Reparametrizing simple loops with a common base point

The circle chart obtained by deleting the common base point turns the change
of parameters into an injective continuous real map.  Its monotonicity extends
to the two interval endpoints.
-/

open Set

namespace Puzzling139335.LoopVariation

noncomputable section

private def extendEndpoints (a b u v : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = a then u else if x = b then v else ψ x

private theorem extendEndpoints_left (a b u v : ℝ) (ψ : ℝ → ℝ) :
    extendEndpoints a b u v ψ a = u := by
  simp [extendEndpoints]

private theorem extendEndpoints_right {a b : ℝ} (hab : a < b)
    (u v : ℝ) (ψ : ℝ → ℝ) :
    extendEndpoints a b u v ψ b = v := by
  simp [extendEndpoints, hab.ne']

private theorem extendEndpoints_interior {a b u v x : ℝ} {ψ : ℝ → ℝ}
    (hx : x ∈ Ioo a b) : extendEndpoints a b u v ψ x = ψ x := by
  simp [extendEndpoints, hx.1.ne', hx.2.ne]

private theorem extendEndpoints_mapsTo {a b c d u v : ℝ} {ψ : ℝ → ℝ}
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d)
    (hψ : MapsTo ψ (Ioo a b) (Ioo c d)) :
    MapsTo (extendEndpoints a b u v ψ) (Icc a b) (Icc c d) := by
  intro x hx
  by_cases hxa : x = a
  · simpa only [extendEndpoints, if_pos hxa] using hu
  by_cases hxb : x = b
  · simpa only [extendEndpoints, if_neg hxa, if_pos hxb] using hv
  have hxi : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  simpa only [extendEndpoints, if_neg hxa, if_neg hxb] using
    Ioo_subset_Icc_self (hψ hxi)

private theorem extendEndpoints_monotoneOn {a b c d : ℝ} {ψ : ℝ → ℝ}
    (hab : a < b) (hcd : c ≤ d) (hψ : MonotoneOn ψ (Ioo a b))
    (hm : MapsTo ψ (Ioo a b) (Ioo c d)) :
    MonotoneOn (extendEndpoints a b c d ψ) (Icc a b) := by
  have hmaps := extendEndpoints_mapsTo (left_mem_Icc.mpr hcd) (right_mem_Icc.mpr hcd) hm
  intro x hx y hy hxy
  by_cases hxa : x = a
  · rw [hxa, extendEndpoints_left]
    exact (hmaps hy).1
  by_cases hyb : y = b
  · rw [hyb, extendEndpoints_right hab]
    exact (hmaps hx).2
  have hxi : x ∈ Ioo a b := by constructor <;> grind
  have hyi : y ∈ Ioo a b := by constructor <;> grind
  rw [extendEndpoints_interior hxi, extendEndpoints_interior hyi]
  exact hψ hxi hyi hxy

private theorem extendEndpoints_antitoneOn {a b c d : ℝ} {ψ : ℝ → ℝ}
    (hab : a < b) (hcd : c ≤ d) (hψ : AntitoneOn ψ (Ioo a b))
    (hm : MapsTo ψ (Ioo a b) (Ioo c d)) :
    AntitoneOn (extendEndpoints a b d c ψ) (Icc a b) := by
  have hmaps := extendEndpoints_mapsTo (right_mem_Icc.mpr hcd) (left_mem_Icc.mpr hcd) hm
  intro x hx y hy hxy
  by_cases hxa : x = a
  · rw [hxa, extendEndpoints_left]
    exact (hmaps hy).2
  by_cases hyb : y = b
  · rw [hyb, extendEndpoints_right hab]
    exact (hmaps hx).1
  have hxi : x ∈ Ioo a b := by constructor <;> grind
  have hyi : y ∈ Ioo a b := by constructor <;> grind
  rw [extendEndpoints_interior hxi, extendEndpoints_interior hyi]
  exact hψ hxi hyi hxy

private theorem extendEndpoints_surjOn {a b c d : ℝ} {ψ : ℝ → ℝ}
    (hab : a < b) (hψ : SurjOn ψ (Ioo a b) (Ioo c d)) :
    SurjOn (extendEndpoints a b c d ψ) (Icc a b) (Icc c d) ∧
      SurjOn (extendEndpoints a b d c ψ) (Icc a b) (Icc c d) := by
  constructor <;> intro y hy
  · by_cases hyc : y = c
    · exact ⟨a, left_mem_Icc.mpr hab.le, by simp [hyc, extendEndpoints]⟩
    by_cases hyd : y = d
    · exact ⟨b, right_mem_Icc.mpr hab.le, by simp [hyd, extendEndpoints, hab.ne']⟩
    obtain ⟨x, hx, hxy⟩ := hψ (show y ∈ Ioo c d by constructor <;> grind)
    exact ⟨x, Ioo_subset_Icc_self hx, (extendEndpoints_interior hx).trans hxy⟩
  · by_cases hyc : y = c
    · exact ⟨b, right_mem_Icc.mpr hab.le, by simp [hyc, extendEndpoints, hab.ne']⟩
    by_cases hyd : y = d
    · exact ⟨a, left_mem_Icc.mpr hab.le, by simp [hyd, extendEndpoints]⟩
    obtain ⟨x, hx, hxy⟩ := hψ (show y ∈ Ioo c d by constructor <;> grind)
    exact ⟨x, Ioo_subset_Icc_self hx, (extendEndpoints_interior hx).trans hxy⟩

section CircleLift

variable {X : Type*}
variable {p q a c : ℝ} [Fact (0 < p)] [Fact (0 < q)]
variable {f g : ℝ → X}

private theorem image_Ico_eq_image_Icc (hclose : f a = f (a + p)) :
    f '' Ico a (a + p) = f '' Icc a (a + p) := by
  apply Subset.antisymm (image_mono Ico_subset_Icc_self)
  rintro _ ⟨x, hx, rfl⟩
  rcases lt_or_eq_of_le hx.2 with hlt | rfl
  · exact ⟨x, ⟨hx.1, hlt⟩, rfl⟩
  · exact ⟨a, ⟨le_rfl, lt_add_of_pos_right a (Fact.out : 0 < p)⟩, hclose⟩

private theorem range_liftIco_eq_image :
    range (AddCircle.liftIco p a f) = f '' Ico a (a + p) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(AddCircle.equivIco p a x : ℝ), (AddCircle.equivIco p a x).property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : AddCircle p), AddCircle.liftIco_coe_apply hx⟩

private theorem range_liftIco_eq_closed_image (hclose : f a = f (a + p)) :
    range (AddCircle.liftIco p a f) = f '' Icc a (a + p) :=
  range_liftIco_eq_image.trans (image_Ico_eq_image_Icc hclose)

private theorem liftIco_injective (hfi : InjOn f (Ico a (a + p))) :
    Function.Injective (AddCircle.liftIco p a f) :=
  hfi.injective.comp (AddCircle.equivIco p a).injective

variable [TopologicalSpace X] [T2Space X]

private theorem exists_liftIco_homeomorph
    (hfcont : ContinuousOn f (Icc a (a + p)))
    (hfclose : f a = f (a + p)) (hfi : InjOn f (Ico a (a + p)))
    (hgcont : ContinuousOn g (Icc c (c + q)))
    (hgclose : g c = g (c + q)) (hgi : InjOn g (Ico c (c + q)))
    (hfg : f '' Icc a (a + p) = g '' Icc c (c + q))
    (hbase : f a = g c) :
    ∃ e : AddCircle p ≃ₜ AddCircle q,
      e (a : AddCircle p) = (c : AddCircle q) ∧
      ∀ x, AddCircle.liftIco q c g (e x) = AddCircle.liftIco p a f x := by
  let ef : AddCircle p ≃ₜ range (AddCircle.liftIco p a f) :=
    ((AddCircle.liftIco_continuous hfclose hfcont).isClosedEmbedding
      (liftIco_injective hfi)).toIsEmbedding.toHomeomorph
  let eg : AddCircle q ≃ₜ range (AddCircle.liftIco q c g) :=
    ((AddCircle.liftIco_continuous hgclose hgcont).isClosedEmbedding
      (liftIco_injective hgi)).toIsEmbedding.toHomeomorph
  have hrange : range (AddCircle.liftIco p a f) = range (AddCircle.liftIco q c g) := by
    rw [range_liftIco_eq_closed_image hfclose, range_liftIco_eq_closed_image hgclose]
    exact hfg
  let e : AddCircle p ≃ₜ AddCircle q :=
    ef.trans ((Homeomorph.setCongr hrange).trans eg.symm)
  have he : ∀ x, AddCircle.liftIco q c g (e x) = AddCircle.liftIco p a f x := by
    intro x
    exact congrArg Subtype.val
      (eg.apply_symm_apply ((Homeomorph.setCongr hrange) (ef x)))
  refine ⟨e, ?_, he⟩
  apply liftIco_injective hgi
  calc
    AddCircle.liftIco q c g (e (a : AddCircle p)) =
        AddCircle.liftIco p a f (a : AddCircle p) := he _
    _ = f a := AddCircle.liftIco_coe_apply
      ⟨le_rfl, lt_add_of_pos_right a (Fact.out : 0 < p)⟩
    _ = g c := hbase
    _ = AddCircle.liftIco q c g (c : AddCircle q) :=
      (AddCircle.liftIco_coe_apply
        ⟨le_rfl, lt_add_of_pos_right c (Fact.out : 0 < q)⟩).symm

end CircleLift

section CircleChart

variable {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]

private def cutChart (e : AddCircle p ≃ₜ AddCircle q) (r : ℝ) (x : ℝ) : ℝ :=
  AddCircle.equivIco q r (e (x : AddCircle p))

private theorem circle_coe_ne_of_mem_Ioo {a x : ℝ} (hx : x ∈ Ioo a (a + p)) :
    (x : AddCircle p) ≠ (a : AddCircle p) := by
  intro h
  have hxa := (AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hx)
    (left_mem_Ico.mpr (lt_add_of_pos_right a (Fact.out : 0 < p)))).mp h
  exact hx.1.ne' hxa

private theorem cutChart_continuousOn (e : AddCircle p ≃ₜ AddCircle q) (a r : ℝ)
    (he : e (a : AddCircle p) = (r : AddCircle q)) :
    ContinuousOn (cutChart e r) (Ioo a (a + p)) := by
  intro x hx
  have hne : e (x : AddCircle p) ≠ (r : AddCircle q) := by
    rw [← he]
    exact fun h => circle_coe_ne_of_mem_Ioo hx (e.injective h)
  have hcoe : Continuous (fun t : ℝ => (t : AddCircle p)) := AddCircle.continuous_mk' p
  have hecoe : Continuous (fun t : ℝ => e (t : AddCircle p)) := e.continuous.comp hcoe
  have hchart : ContinuousAt
      (fun z : AddCircle q => (AddCircle.equivIco q r z : ℝ)) (e (x : AddCircle p)) :=
    continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIco q r hne)
  exact (hchart.comp (f := fun t : ℝ => e (t : AddCircle p))
    (x := x) hecoe.continuousAt).continuousWithinAt

private theorem cutChart_injOn (e : AddCircle p ≃ₜ AddCircle q) (a r : ℝ) :
    InjOn (cutChart e r) (Ioo a (a + p)) := by
  intro x hx y hy hxy
  have heq : e (x : AddCircle p) = e (y : AddCircle p) :=
    (AddCircle.equivIco q r).injective (Subtype.ext hxy)
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (Ioo_subset_Ico_self hx) (Ioo_subset_Ico_self hy)).mp (e.injective heq)

private theorem cutChart_mapsTo (e : AddCircle p ≃ₜ AddCircle q) (a r : ℝ)
    (he : e (a : AddCircle p) = (r : AddCircle q)) :
    MapsTo (cutChart e r) (Ioo a (a + p)) (Ioo r (r + q)) := by
  intro x hx
  have hne : e (x : AddCircle p) ≠ (r : AddCircle q) := by
    rw [← he]
    exact fun h => circle_coe_ne_of_mem_Ioo hx (e.injective h)
  exact (AddCircle.openPartialHomeomorphCoe q r).map_target hne

private theorem cutChart_surjOn (e : AddCircle p ≃ₜ AddCircle q) (a r : ℝ)
    (he : e (a : AddCircle p) = (r : AddCircle q)) :
    SurjOn (cutChart e r) (Ioo a (a + p)) (Ioo r (r + q)) := by
  intro y hy
  let z : AddCircle p := e.symm (y : AddCircle q)
  have hza : z ≠ (a : AddCircle p) := by
    intro hza
    have hy' : (y : AddCircle q) = (r : AddCircle q) := by
      calc
        (y : AddCircle q) = e z := (e.apply_symm_apply _).symm
        _ = e (a : AddCircle p) := congrArg e hza
        _ = (r : AddCircle q) := he
    exact circle_coe_ne_of_mem_Ioo hy hy'
  let x : ℝ := AddCircle.equivIco p a z
  have hx : x ∈ Ioo a (a + p) :=
    (AddCircle.openPartialHomeomorphCoe p a).map_target hza
  refine ⟨x, hx, ?_⟩
  change ((AddCircle.equivIco q r (e ((AddCircle.equivIco p a z : ℝ) :
    AddCircle p))) : ℝ) = y
  rw [AddCircle.coe_equivIco]
  dsimp [z]
  rw [e.apply_symm_apply]
  exact AddCircle.equivIco_coe_of_mem (Ioo_subset_Ico_self hy)

private theorem cutChart_strictMonoOn_or_strictAntiOn
    (e : AddCircle p ≃ₜ AddCircle q) (a r : ℝ)
    (he : e (a : AddCircle p) = (r : AddCircle q)) :
    StrictMonoOn (cutChart e r) (Ioo a (a + p)) ∨
      StrictAntiOn (cutChart e r) (Ioo a (a + p)) :=
  (cutChart_continuousOn e a r he).strictMonoOn_of_injOn_Ioo
    (lt_add_of_pos_right a (Fact.out : 0 < p)) (cutChart_injOn e a r)

end CircleChart

variable {X : Type*} [TopologicalSpace X] [T2Space X]
variable {f g : ℝ → X} {a b c d : ℝ}

/-- Two simple closed parametrizations with the same image and base point differ
by a monotone or antitone surjective change of their closed parameter intervals.
Only continuity of the original parametrizations is needed; no regularity of
the curve image or finite-length hypothesis occurs. -/
theorem exists_commonBase_loop_reparam
    (hab : a < b) (hcd : c < d)
    (hfcont : ContinuousOn f (Icc a b)) (hfclose : f a = f b)
    (hfi : InjOn f (Ico a b))
    (hgcont : ContinuousOn g (Icc c d)) (hgclose : g c = g d)
    (hgi : InjOn g (Ico c d))
    (hfg : f '' Icc a b = g '' Icc c d) (hbase : f a = g c) :
    ∃ φ : ℝ → ℝ,
      (MonotoneOn φ (Icc a b) ∨ AntitoneOn φ (Icc a b)) ∧
      MapsTo φ (Icc a b) (Icc c d) ∧
      SurjOn φ (Icc a b) (Icc c d) ∧ EqOn (g ∘ φ) f (Icc a b) := by
  let : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  let : Fact (0 < d - c) := ⟨sub_pos.mpr hcd⟩
  have hp : a + (b - a) = b := by ring
  have hq : c + (d - c) = d := by ring
  obtain ⟨e, hebase, heval⟩ :=
    exists_liftIco_homeomorph (p := b - a) (q := d - c) (a := a) (c := c)
      (by simpa only [hp] using hfcont) (by simpa only [hp] using hfclose)
      (by simpa only [hp] using hfi) (by simpa only [hq] using hgcont)
      (by simpa only [hq] using hgclose) (by simpa only [hq] using hgi)
      (by simpa only [hp, hq] using hfg) hbase
  have hm : MapsTo (cutChart e c) (Ioo a b) (Ioo c d) := by
    simpa only [hp, hq] using cutChart_mapsTo e a c hebase
  have hs : SurjOn (cutChart e c) (Ioo a b) (Ioo c d) := by
    simpa only [hp, hq] using cutChart_surjOn e a c hebase
  have horder : StrictMonoOn (cutChart e c) (Ioo a b) ∨
      StrictAntiOn (cutChart e c) (Ioo a b) := by
    simpa only [hp] using cutChart_strictMonoOn_or_strictAntiOn e a c hebase
  have hvalues : EqOn (g ∘ cutChart e c) f (Ioo a b) := by
    intro x hx
    calc
      g (cutChart e c x) = AddCircle.liftIco (d - c) c g (e (x : AddCircle (b - a))) := rfl
      _ = AddCircle.liftIco (b - a) a f (x : AddCircle (b - a)) := heval _
      _ = f x := AddCircle.liftIco_coe_apply (by simpa only [hp] using Ioo_subset_Ico_self hx)
  rcases horder with hmono | hanti
  · refine ⟨extendEndpoints a b c d (cutChart e c),
      Or.inl (extendEndpoints_monotoneOn hab hcd.le hmono.monotoneOn hm),
      extendEndpoints_mapsTo (left_mem_Icc.mpr hcd.le) (right_mem_Icc.mpr hcd.le) hm,
      (extendEndpoints_surjOn hab hs).1, ?_⟩
    intro x hx
    by_cases hxa : x = a
    · simpa only [Function.comp_apply, hxa, extendEndpoints_left] using hbase.symm
    by_cases hxb : x = b
    · simpa only [Function.comp_apply, hxb, extendEndpoints_right hab] using
        hgclose.symm.trans (hbase.symm.trans hfclose)
    have hxi : x ∈ Ioo a b := by constructor <;> grind
    simpa only [Function.comp_apply, extendEndpoints_interior hxi] using hvalues hxi
  · refine ⟨extendEndpoints a b d c (cutChart e c),
      Or.inr (extendEndpoints_antitoneOn hab hcd.le hanti.antitoneOn hm),
      extendEndpoints_mapsTo (right_mem_Icc.mpr hcd.le) (left_mem_Icc.mpr hcd.le) hm,
      (extendEndpoints_surjOn hab hs).2, ?_⟩
    intro x hx
    by_cases hxa : x = a
    · simpa only [Function.comp_apply, hxa, extendEndpoints_left] using
        hgclose.symm.trans hbase.symm
    by_cases hxb : x = b
    · simpa only [Function.comp_apply, hxb, extendEndpoints_right hab] using
        hbase.symm.trans hfclose
    have hxi : x ∈ Ioo a b := by constructor <;> grind
    simpa only [Function.comp_apply, extendEndpoints_interior hxi] using hvalues hxi

end

end Puzzling139335.LoopVariation
