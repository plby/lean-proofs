import Wikipedia.SmoothSixDPoincare.GlobalImageAvoidance
import Wikipedia.HopfProblem.DegreeCollapseRelativeAvoidingSmoothing

/-!
# Relative image avoidance with every change inside a prescribed open set

Choose the actual target charts inside the open set. Finite relative
perturbation then retains every coincidence with points outside it, while
removing a closed low-dimensional image. The protected source set is fixed
exactly. No global embeddedness is asserted by this avoidance step.
-/

noncomputable section

open Set Function Filter ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeOpenImageAvoidance

open GeneralPosition

variable {E E' G H H' K X Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ G] in
theorem exists_patch_in_open (f : C(X, N)) {C : Set X} (hC : IsClosed C)
    {V : Set N} (hV : IsOpen V) (x : X) (hxC : x ∉ C) (hxV : f x ∈ V) :
    ∃ p : MapAvoidancePatch I J (N := N) C,
      p.Compatible f ∧ p.cutoff x ≠ 0 ∧ p.chart.source ⊆ V := by
  let c := PartialChart.restrictSource
    (NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)) hV
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxV⟩
  have hU : f ⁻¹' c.source ∩ Cᶜ ∈ 𝓝 x :=
    ((c.open_source.preimage f.continuous).inter hC.isOpen_compl).mem_nhds ⟨hsource, hxC⟩
  obtain ⟨φ, _, hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  let p : MapAvoidancePatch I J (N := N) C := {
    chart := c
    cutoff := φ
    smooth := φ.contMDiff
    compact := φ.hasCompactSupport
    fixed := fun y hy => image_eq_zero_of_notMem_tsupport (fun ht => (hφ ht).2 hy) }
  refine ⟨p, fun y hy => (hφ hy).1, ?_, inter_subset_right⟩
  change φ x ≠ 0
  rw [φ.eq_one]
  exact one_ne_zero

variable [LindelofSpace (X × Y)]

omit [J.Boundaryless] [T2Space X] [IsManifold J ∞ N] in
theorem exists_patch_step_in_open {ι : Type*} [Finite ι] {C : Set X} {V : Set N}
    (p : ι → MapAvoidancePatch I J (N := N) C) (i : ι)
    (hcharts : ∀ j, (p j).chart.source ⊆ V)
    (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      f.HomotopicRel f' C ∧
      (∀ x, (f x ∉ range g ∨ (p i).cutoff x ≠ 0) → f' x ∉ range g) ∧
      (∀ x, f x ∈ V → f' x ∈ V) ∧ (∀ x, f x ∉ V → f' x = f x) := by
  have hkeep : ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply eventually_all.mpr
    intro j
    exact ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf
      (p i).smooth (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  obtain ⟨r, hr, hvalid⟩ := ChartMapPerturbation.exists_radius_valid (p i).chart hf
    (p i).smooth (p i).compact (hcompatible i)
  obtain ⟨a, ha, hva, hsmooth, havoid⟩ := ChartMapPerturbation.exists_small_avoiding_parameter
    (p i).chart hf hg (p i).smooth (p i).compact (hcompatible i) hdim (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let f' : C(X, N) := ⟨_, hsmooth.continuous⟩
  have H := ChartMapPerturbation.homotopyRel (p i).chart hf (p i).smooth
    (hcompatible i) hvalid har
  have hzero (x : X) (hx : (p i).cutoff x = 0) : f' x = f x :=
    ChartMapPerturbation.perturb_eq_of_zero _ _ _ _ hx
  have hsource (x : X) (hx : (p i).cutoff x ≠ 0) : f x ∈ (p i).chart.source :=
    hcompatible i (subset_tsupport _ hx)
  refine ⟨f', hsmooth, ?_, ?_, ?_, ?_, ?_⟩
  · exact hδkeep (by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  · exact ⟨{ toHomotopy := H.toHomotopy
             prop' := fun t x hx => H.prop t x ((p i).fixed x hx) }⟩
  · intro x hx
    by_cases hz : (p i).cutoff x = 0
    · rw [hzero x hz]
      exact hx.resolve_right (not_not.mpr hz)
    · rintro ⟨y, hy⟩
      exact havoid x hz y hy.symm
  · intro x hx
    by_cases hz : (p i).cutoff x = 0
    · rwa [hzero x hz]
    · exact hcharts i
        (ChartMapPerturbation.perturb_mem_source (p i).chart f (p i).cutoff hva (hsource x hz))
  · intro x hx
    exact hzero x (not_not.mp (fun hn => hx (hcharts i (hsource x hn))))

omit [J.Boundaryless] [T2Space X] [IsManifold J ∞ N] in
theorem exists_finite_patch_avoidance_in_open {ι : Type*} [Finite ι] {C : Set X} {V : Set N}
    (p : ι → MapAvoidancePatch I J (N := N) C) (hcharts : ∀ j, (p j).chart.source ⊆ V)
    (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (s : Finset ι) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      f.HomotopicRel f' C ∧
      (∀ x, (f x ∉ range g ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ range g) ∧
      (∀ x, f x ∈ V → f' x ∈ V) ∧ (∀ x, f x ∉ V → f' x = f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, HomotopicRel.refl f, ?_, fun _ hx => hx, fun _ _ => rfl⟩
    intro x hx
    simpa using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hf₁, hc₁, hhom₁, havoid₁, hV₁, hfix₁⟩ := ih
    obtain ⟨f₂, hf₂, hc₂, hhom₂, havoid₂, hV₂, hfix₂⟩ :=
      exists_patch_step_in_open p i hcharts f₁ g hf₁ hg hc₁ hdim
    refine ⟨f₂, hf₂, hc₂, hhom₁.trans hhom₂, ?_, fun x hx => hV₂ x (hV₁ x hx), ?_⟩
    · intro x hx
      apply havoid₂ x
      rcases hx with hold | ⟨j, hj, hnonzero⟩
      · exact Or.inl (havoid₁ x (Or.inl hold))
      · rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact Or.inr hnonzero
        · exact Or.inl (havoid₁ x (Or.inr ⟨j, hjs, hnonzero⟩))
    · intro x hx
      have he := hfix₁ x hx
      exact (hfix₂ x (he.symm ▸ hx)).trans he

variable [CompactSpace X]

theorem exists_disjoint_smooth_map_preserving_complement
    (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (range g))
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {C : Set X} (hC : IsClosed C) (hfixed : ∀ x ∈ C, f x ∉ range g)
    {V : Set N} (hV : IsOpen V) (hbadV : ∀ x, f x ∈ range g → f x ∈ V) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧
      Disjoint (range f') (range g) ∧ ∀ x y, y ∉ V → (f' x = y ↔ f x = y) := by
  classical
  let bad : Set X := f ⁻¹' range g
  have hbad : IsCompact bad := (hclosed.preimage f.continuous).isCompact
  have hp (x : bad) : ∃ p : MapAvoidancePatch I J (N := N) C,
      p.Compatible f ∧ p.cutoff x.val ≠ 0 ∧ p.chart.source ⊆ V :=
    exists_patch_in_open f hC hV x.val (fun hx => hfixed x.val hx x.property)
      (hbadV x.val x.property)
  choose p hpcompatible hpactive hpV using hp
  have hopen (x : bad) : IsOpen (Function.support (p x).cutoff) :=
    isOpen_ne_fun (p x).smooth.continuous continuous_const
  have hcover : bad ⊆ ⋃ x : bad, Function.support (p x).cutoff := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hbad.elim_finite_subcover (fun x : bad => Function.support (p x).cutoff)
    hopen hcover
  obtain ⟨f', hf', _, hhom, havoid, hkeep, hfix⟩ :=
    exists_finite_patch_avoidance_in_open (fun i : s => p i.val) (fun i => hpV i.val)
      f g hf hg (fun i => hpcompatible i.val) hdim Finset.univ
  refine ⟨f', hf', hhom, disjoint_left.mpr ?_, ?_⟩
  · rintro z ⟨x, rfl⟩ hz
    apply havoid x _ hz
    by_cases hx : f x ∈ range g
    · obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hs hx)
      exact Or.inr ⟨⟨i, hi⟩, Finset.mem_univ _, hix⟩
    · exact Or.inl hx
  · intro x y hy
    by_cases hx : f x ∈ V
    · constructor
      · intro he
        exact (hy (he ▸ hkeep x hx)).elim
      · intro he
        exact (hy (he ▸ hx)).elim
    · rw [hfix x hx]

end Wikipedia.HopfProblem.DegreeCollapse.RelativeOpenImageAvoidance
