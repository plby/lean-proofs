import Wikipedia.HopfProblem.MappingTorusTopology

/-!
# Open interval charts of the actual mapping torus

Removing the fibre over `a : AddCircle 1` makes every quotient point admit a
unique representative `(t, x)` with `a < t < a + 1`.  The quotient map is open,
so these representatives give an actual homeomorphism, not merely an
equivalence of sets.  Changing the representative from `t` to `t - 1` applies
the monodromy `f` to the fibre coordinate.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.MappingTorus

variable {X : Type*} [TopologicalSpace X]

/-- An interior interval representative does not lie over its endpoint. -/
theorem base_mk_ne_of_mem_Ioo (f : X ≃ₜ X) (a : ℝ)
    (t : Ioo a (a + 1)) (x : X) :
    base f (mk f ((t : ℝ), x)) ≠ (a : Circle) :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).map_source t.property

/-- The quotient map restricted to one open interval of time. -/
def intervalParam (f : X ≃ₜ X) (a : ℝ) (p : Ioo a (a + 1) × X) :
    {q : Torus f // base f q ≠ (a : Circle)} :=
  ⟨mk f ((p.1 : ℝ), p.2), base_mk_ne_of_mem_Ioo f a p.1 p.2⟩

@[simp] theorem intervalParam_coe (f : X ≃ₜ X) (a : ℝ)
    (p : Ioo a (a + 1) × X) :
    (intervalParam f a p : Torus f) = mk f ((p.1 : ℝ), p.2) := rfl

theorem intervalParam_continuous (f : X ≃ₜ X) (a : ℝ) :
    Continuous (intervalParam f a) :=
  ((mk_continuous f).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

theorem intervalParam_open (f : X ≃ₜ X) (a : ℝ) :
    IsOpenMap (intervalParam f a) :=
  ((mk_open f).comp
    (isOpen_Ioo.isOpenMap_subtype_val.prodMap IsOpenMap.id)).subtype_mk _

theorem intervalParam_injective (f : X ≃ₜ X) (a : ℝ) :
    Function.Injective (intervalParam f a) := by
  intro p q hpq
  have he : mk f ((p.1 : ℝ), p.2) = mk f ((q.1 : ℝ), q.2) :=
    congrArg Subtype.val hpq
  have hc : ((p.1 : ℝ) : Circle) = ((q.1 : ℝ) : Circle) :=
    congrArg (base f) he
  have ht : (p.1 : ℝ) = (q.1 : ℝ) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (Ioo_subset_Ico_self p.1.property) (Ioo_subset_Ico_self q.1.property)).mp hc
  obtain ⟨n, hn, hx⟩ := (mk_eq_mk_iff f _ _).mp he
  have hnR : (n : ℝ) = 0 := by
    dsimp at hn
    linarith
  have hn0 : n = 0 := Int.cast_eq_zero.mp hnR
  apply Prod.ext (Subtype.ext ht)
  simpa [hn0] using hx.symm

theorem intervalParam_surjective (f : X ≃ₜ X) (a : ℝ) :
    Function.Surjective (intervalParam f a) := by
  intro q
  obtain ⟨⟨s, x⟩, hp⟩ := mk_surjective f q.val
  let e := AddCircle.openPartialHomeomorphCoe (1 : ℝ) a
  let t : Ioo a (a + 1) := ⟨e.symm (base f q.val), e.map_target q.property⟩
  have ht : ((t : ℝ) : Circle) = base f q.val := e.right_inv q.property
  have hst : (s : Circle) = ((t : ℝ) : Circle) :=
    (congrArg (base f) hp).trans ht.symm
  obtain ⟨n, hn⟩ := (circle_coe_eq_iff s (t : ℝ)).mp hst
  refine ⟨(t, (f ^ (-n)) x), Subtype.ext ?_⟩
  change mk f ((t : ℝ), (f ^ (-n)) x) = q.val
  rw [hn]
  exact (mk_deck f n (s, x)).trans hp

/-- The actual mapping-torus chart obtained by deleting one fibre. -/
def intervalHomeomorph (f : X ≃ₜ X) (a : ℝ) :
    {q : Torus f // base f q ≠ (a : Circle)} ≃ₜ (Ioo a (a + 1) × X) :=
  ((Equiv.ofBijective (intervalParam f a)
    ⟨intervalParam_injective f a, intervalParam_surjective f a⟩).toHomeomorphOfContinuousOpen
      (intervalParam_continuous f a) (intervalParam_open f a)).symm

@[simp] theorem intervalHomeomorph_symm_coe (f : X ≃ₜ X) (a : ℝ)
    (p : Ioo a (a + 1) × X) :
    ((intervalHomeomorph f a).symm p : Torus f) = mk f ((p.1 : ℝ), p.2) := rfl

@[simp] theorem intervalHomeomorph_apply_param (f : X ≃ₜ X) (a : ℝ)
    (p : Ioo a (a + 1) × X) :
    intervalHomeomorph f a (intervalParam f a p) = p :=
  (intervalHomeomorph f a).apply_symm_apply p

/-- The chart gives exactly the coordinates of any representative in its interval. -/
@[simp] theorem intervalHomeomorph_mk (f : X ≃ₜ X) (a : ℝ)
    (t : Ioo a (a + 1)) (x : X)
    (h : base f (mk f ((t : ℝ), x)) ≠ (a : Circle)) :
    intervalHomeomorph f a ⟨mk f ((t : ℝ), x), h⟩ = (t, x) :=
  intervalHomeomorph_apply_param f a (t, x)

/-- The chosen interval coordinates reconstruct the original quotient point. -/
@[simp] theorem mk_intervalHomeomorph (f : X ≃ₜ X) (a : ℝ)
    (q : {q : Torus f // base f q ≠ (a : Circle)}) :
    mk f (((intervalHomeomorph f a q).1 : ℝ), (intervalHomeomorph f a q).2) = q.val :=
  congrArg Subtype.val ((intervalHomeomorph f a).symm_apply_apply q)

theorem intervalHomeomorph_eq_iff (f : X ≃ₜ X) (a : ℝ)
    (q : {q : Torus f // base f q ≠ (a : Circle)})
    (p : Ioo a (a + 1) × X) :
    intervalHomeomorph f a q = p ↔ q.val = mk f ((p.1 : ℝ), p.2) := by
  constructor
  · intro h
    calc
      q.val = mk f (((intervalHomeomorph f a q).1 : ℝ),
          (intervalHomeomorph f a q).2) := (mk_intervalHomeomorph f a q).symm
      _ = mk f ((p.1 : ℝ), p.2) := by rw [h]
  · intro h
    have hq : q = (intervalHomeomorph f a).symm p := Subtype.ext h
    rw [hq]
    exact (intervalHomeomorph f a).apply_symm_apply p

/-- Any integer change of representative gives the corresponding deck-coordinate change. -/
theorem intervalHomeomorph_mk_add_int (f : X ≃ₜ X) (a t : ℝ) (x : X) (n : ℤ)
    (ht : t + (n : ℝ) ∈ Ioo a (a + 1))
    (h : base f (mk f (t, x)) ≠ (a : Circle)) :
    intervalHomeomorph f a ⟨mk f (t, x), h⟩ =
      (⟨t + (n : ℝ), ht⟩, (f ^ (-n)) x) := by
  apply (intervalHomeomorph_eq_iff f a _ _).mpr
  exact (mk_deck f n (t, x)).symm

/-- Moving a representative one period to the left applies `f`. -/
theorem intervalHomeomorph_mk_sub_one (f : X ≃ₜ X) (a t : ℝ) (x : X)
    (ht : t - 1 ∈ Ioo a (a + 1))
    (h : base f (mk f (t, x)) ≠ (a : Circle)) :
    intervalHomeomorph f a ⟨mk f (t, x), h⟩ = (⟨t - 1, ht⟩, f x) := by
  apply (intervalHomeomorph_eq_iff f a _ _).mpr
  exact (mk_sub_one f t x).symm

/-- On an overlap where the second interval uses time `t - 1`, the chart
transition is exactly `(t, x) ↦ (t - 1, f x)`. -/
theorem intervalHomeomorph_transition_sub_one (f : X ≃ₜ X) (a b : ℝ)
    (p : Ioo a (a + 1) × X)
    (ht : (p.1 : ℝ) - 1 ∈ Ioo b (b + 1))
    (h : base f ((intervalHomeomorph f a).symm p : Torus f) ≠ (b : Circle)) :
    intervalHomeomorph f b ⟨((intervalHomeomorph f a).symm p : Torus f), h⟩ =
      (⟨(p.1 : ℝ) - 1, ht⟩, f p.2) :=
  intervalHomeomorph_mk_sub_one f b (p.1 : ℝ) p.2 ht h

end Wikipedia.HopfProblem.MappingTorus
