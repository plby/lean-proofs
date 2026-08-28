import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Separation.Hausdorff

/-!
# Injective neighborhoods of compact sets and uniform normal radii

Continuity and local injectivity near a compact set, together with actual
injectivity on that set, imply injectivity on an open neighborhood. The
proof uses the generalized tube lemma on the genuine relation excluding
collisions. No properness of the map or compactness of its whole domain
is assumed. For a compact base and a metric normal fibre, this gives a
single positive radius for the entire zero section.
-/

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- The actual complement of the off-diagonal collision relation. -/
def injectivityRelation (f : X → Y) : Set (X × X) :=
  {p | f p.1 = f p.2 → p.1 = p.2}

/-- At a pair with no collision, continuity excludes unequal-image collisions,
and local injectivity excludes collisions near a diagonal pair. -/
theorem injectivityRelation_mem_nhds {f : X → Y} {x y : X}
    (hx : ContinuousAt f x) (hy : ContinuousAt f y)
    (hloc : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U)
    (hrel : f x = f y → x = y) :
    injectivityRelation f ∈ 𝓝 (x, y) := by
  by_cases hxy : x = y
  · obtain ⟨U, hU, hxU, hinj⟩ := hloc
    have hUU : U ×ˢ U ∈ 𝓝 (x, y) :=
      (hU.prod hU).mem_nhds ⟨hxU, hxy ▸ hxU⟩
    exact mem_of_superset hUU (fun _ hp he => hinj hp.1 hp.2 he)
  · have hne : f x ≠ f y := fun he => hxy (hrel he)
    have hopen : IsOpen {p : Y × Y | p.1 ≠ p.2} :=
      (isClosed_eq continuous_fst continuous_snd).isOpen_compl
    have hc : ContinuousAt (fun p : X × X => (f p.1, f p.2)) (x, y) :=
      (hx.comp continuousAt_fst).prodMk (hy.comp continuousAt_snd)
    have hN := hc.preimage_mem_nhds (hopen.mem_nhds hne)
    exact mem_of_superset hN (fun _ hp he => (hp he).elim)

/-- For a continuous locally injective map, the no-collision relation is open. -/
theorem isOpen_injectivityRelation {f : X → Y} (hf : Continuous f)
    (hloc : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U) :
    IsOpen (injectivityRelation f) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact injectivityRelation_mem_nhds hf.continuousAt hf.continuousAt (hloc p.1) hp

/-- The genuine off-diagonal collision relation is closed. -/
theorem isClosed_collisionRelation {f : X → Y} (hf : Continuous f)
    (hloc : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U) :
    IsClosed {p : X × X | p.1 ≠ p.2 ∧ f p.1 = f p.2} := by
  have he : {p : X × X | p.1 ≠ p.2 ∧ f p.1 = f p.2} =
      (injectivityRelation f)ᶜ := by
    ext p
    simp only [injectivityRelation, mem_ofPred_eq, mem_compl_iff, Classical.not_imp, and_comm]
  rw [he]
  exact (isOpen_injectivityRelation hf hloc).isClosed_compl

/-- Only continuity and local injectivity at points of the compact set are
needed to obtain a genuinely injective open neighborhood. -/
theorem exists_open_injOn_of_compact_of_continuousAt {f : X → Y} {K : Set X}
    (hK : IsCompact K) (hf : ∀ x ∈ K, ContinuousAt f x)
    (hloc : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U)
    (hinj : InjOn f K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ InjOn f U := by
  have hprod : K ×ˢ K ⊆ interior (injectivityRelation f) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact mem_interior_iff_mem_nhds.mpr
      (injectivityRelation_mem_nhds (hf x hx) (hf y hy) (hloc x hx)
        (fun he => hinj hx hy he))
  obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ :=
    generalized_tube_lemma hK hK isOpen_interior hprod
  refine ⟨U ∩ V, hU.inter hV, fun x hx => ⟨hKU hx, hKV hx⟩, ?_⟩
  intro x hx y hy he
  have hrel : (x, y) ∈ injectivityRelation f :=
    interior_subset (hUV (show (x, y) ∈ U ×ˢ V from ⟨hx.1, hy.2⟩))
  exact hrel he

/-- A continuous locally injective map is injective on some open neighborhood
of every compact set on which it is injective. -/
theorem exists_open_injOn_of_compact {f : X → Y} {K : Set X}
    (hf : Continuous f)
    (hloc : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U)
    (hK : IsCompact K) (hinj : InjOn f K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ InjOn f U :=
  exists_open_injOn_of_compact_of_continuousAt hK (fun _ _ => hf.continuousAt)
    (fun x _ => hloc x) hinj

/-- The same conclusion stays inside the map's given open domain. -/
theorem exists_open_injOn_of_compact_in_open {f : X → Y} {O K : Set X}
    (hO : IsOpen O) (hf : ContinuousOn f O)
    (hloc : ∀ x ∈ O, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U)
    (hK : IsCompact K) (hKO : K ⊆ O) (hinj : InjOn f K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧ InjOn f U := by
  obtain ⟨U, hU, hKU, hUf⟩ := exists_open_injOn_of_compact_of_continuousAt hK
    (fun x hx => (hf x (hKO hx)).continuousAt (hO.mem_nhds (hKO hx)))
    (fun x hx => hloc x (hKO hx)) hinj
  exact ⟨U ∩ O, hU.inter hO, fun _ hx => ⟨hKU hx, hKO hx⟩,
    inter_subset_right, hUf.mono inter_subset_left⟩

/-- The local-homeomorphism specialization uses its actual open local sources. -/
theorem exists_open_injOn_of_isLocalHomeomorphOn {f : X → Y} {O K : Set X}
    (hO : IsOpen O) (hf : IsLocalHomeomorphOn f O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hinj : InjOn f K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧ InjOn f U := by
  apply exists_open_injOn_of_compact_in_open hO hf.continuousOn _ hK hKO hinj
  intro x hx
  obtain ⟨e, he, hfe⟩ := hf x hx
  exact ⟨e.source, e.open_source, he, hfe ▸ e.injOn⟩

section UniformRadius

variable {B F : Type*} [TopologicalSpace B] [CompactSpace B] [PseudoMetricSpace F]

/-- An open set containing a constant section over a compact base contains
one product ball of positive radius over the entire base. -/
theorem exists_pos_prod_ball_subset {O : Set (B × F)} (hO : IsOpen O)
    (z : F) (hz : ∀ b : B, (b, z) ∈ O) :
    ∃ r : ℝ, 0 < r ∧ (univ : Set B) ×ˢ Metric.ball z r ⊆ O := by
  have hsection : (univ : Set B) ×ˢ ({z} : Set F) ⊆ O := by
    rintro ⟨b, y⟩ ⟨_, hy⟩
    have hyz : y = z := mem_singleton_iff.mp hy
    simpa only [hyz] using hz b
  obtain ⟨U, V, _hU, hV, hBU, hzV, hUV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hO hsection
  have hzmem : z ∈ V := hzV (mem_singleton z)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzmem)
  exact ⟨r, hr, fun _ hp => hUV ⟨hBU hp.1, hball hp.2⟩⟩

variable [Zero F]

/-- A local map injective on a compact zero section is injective on one
uniform-radius normal neighborhood, contained in its actual open domain. -/
theorem exists_pos_injOn_prod_ball {f : B × F → Y} {O : Set (B × F)}
    (hO : IsOpen O) (hzero : ∀ b : B, (b, (0 : F)) ∈ O)
    (hf : ContinuousOn f O)
    (hloc : ∀ x ∈ O, ∃ U : Set (B × F), IsOpen U ∧ x ∈ U ∧ InjOn f U)
    (hinjzero : Function.Injective (fun b : B => f (b, (0 : F)))) :
    ∃ r : ℝ, 0 < r ∧ (univ : Set B) ×ˢ Metric.ball (0 : F) r ⊆ O ∧
      InjOn f ((univ : Set B) ×ˢ Metric.ball (0 : F) r) := by
  let K : Set (B × F) := (univ : Set B) ×ˢ ({0} : Set F)
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hKO : K ⊆ O := by
    rintro ⟨b, z⟩ ⟨_, hz⟩
    have hz0 : z = 0 := mem_singleton_iff.mp hz
    simpa only [hz0] using hzero b
  have hKinj : InjOn f K := by
    rintro ⟨b, z⟩ ⟨_, hz⟩ ⟨c, w⟩ ⟨_, hw⟩ he
    have hz0 : z = 0 := mem_singleton_iff.mp hz
    have hw0 : w = 0 := mem_singleton_iff.mp hw
    subst z
    subst w
    exact Prod.ext (hinjzero he) rfl
  obtain ⟨U, hU, hKU, hUO, hUf⟩ :=
    exists_open_injOn_of_compact_in_open hO hf hloc hK hKO hKinj
  obtain ⟨r, hr, hball⟩ := exists_pos_prod_ball_subset hU (0 : F)
    (fun b => hKU ⟨mem_univ b, mem_singleton 0⟩)
  exact ⟨r, hr, hball.trans hUO, hUf.mono hball⟩

/-- The uniform-radius specialization for an actual local homeomorphism. -/
theorem exists_pos_injOn_prod_ball_of_isLocalHomeomorphOn
    {f : B × F → Y} {O : Set (B × F)}
    (hO : IsOpen O) (hzero : ∀ b : B, (b, (0 : F)) ∈ O)
    (hf : IsLocalHomeomorphOn f O)
    (hinjzero : Function.Injective (fun b : B => f (b, (0 : F)))) :
    ∃ r : ℝ, 0 < r ∧ (univ : Set B) ×ˢ Metric.ball (0 : F) r ⊆ O ∧
      InjOn f ((univ : Set B) ×ˢ Metric.ball (0 : F) r) := by
  apply exists_pos_injOn_prod_ball hO hzero hf.continuousOn _ hinjzero
  intro x hx
  obtain ⟨e, he, hfe⟩ := hf x hx
  exact ⟨e.source, e.open_source, he, hfe ▸ e.injOn⟩

end UniformRadius

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
