import Wikipedia.NoExoticSixSphere.SphereConnectivity

/-!
# Relative sphere nullhomotopies on smooth manifolds

Smooth approximation preserves a closed set on whose neighborhood the map is
already smooth. If that set has a constant value, a point-avoidance contraction
can also preserve it. The source may be sigma-compact rather than compact;
this allows application to a real time cylinder with constant end collars.
-/

open scoped Manifold ContDiff Topology
open Set Module

namespace NoExoticSixSphere

section Chart

open unitInterval

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Contract in a full chart to a prescribed chart point, fixing every parameter already there. -/
noncomputable def chartContractionTo (f : C(X, Y)) (c : OpenPartialHomeomorph Y E)
    (ht : c.target = univ) (hf : ∀ x, f x ∈ c.source) (y : Y) (hy : y ∈ c.source)
    (S : Set X) (hS : ∀ x ∈ S, f x = y) : f.HomotopyRel (ContinuousMap.const _ y) S where
  toFun p := c.symm ((1 - (p.1 : ℝ)) • c (f p.2) + (p.1 : ℝ) • c y)
  continuous_toFun := by
    have hc : Continuous (fun x ↦ c (f x)) := c.continuousOn.comp_continuous f.continuous hf
    have hci : Continuous c.symm := by
      apply continuousOn_univ.mp
      rw [← ht]
      exact c.symm.continuousOn
    have htime : Continuous (fun p : I × X ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact hci.comp (((continuous_const.sub htime).smul (hc.comp continuous_snd)).add
      (htime.smul continuous_const))
  map_zero_left x := by
    change c.symm ((1 - (0 : ℝ)) • c (f x) + (0 : ℝ) • c y) = f x
    rw [sub_zero, one_smul, zero_smul, add_zero]
    exact c.left_inv (hf x)
  map_one_left x := by
    change c.symm ((1 - (1 : ℝ)) • c (f x) + (1 : ℝ) • c y) = y
    rw [sub_self, zero_smul, one_smul, zero_add]
    exact c.left_inv hy
  prop' t x hx := by
    change c.symm ((1 - (t : ℝ)) • c (f x) + (t : ℝ) • c y) = f x
    rw [hS x hx, ← add_smul, sub_add_cancel, one_smul]
    exact c.left_inv hy

/-- An omitted sphere point gives a contraction relative to any set with a fixed value. -/
theorem sphereMap_nullhomotopicRel_of_omitted_point (n : ℕ) (f : C(X, Sphere n))
    (p y : Sphere n) (hp : ∀ x, f x ≠ p) (hy : y ≠ p)
    (S : Set X) (hS : ∀ x ∈ S, f x = y) :
    Nonempty (f.HomotopyRel (ContinuousMap.const _ y) S) := by
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let c := stereographic' n p
  have hf : ∀ x, f x ∈ c.source := by
    intro x
    simpa only [c, stereographic'_source, mem_compl_iff, mem_singleton_iff] using hp x
  have hyc : y ∈ c.source := by
    simpa only [c, stereographic'_source, mem_compl_iff, mem_singleton_iff] using hy
  exact ⟨chartContractionTo f c (stereographic'_target (n := n) p) hf y hyc S hS⟩

end Chart

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Sphere smoothing can preserve a closed set on whose neighborhood the original map is smooth. -/
theorem exists_smoothSphereRepresentative_rel (n : ℕ) (f : C(M, Sphere n))
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) U) :
    ∃ g : C(M, Sphere n), ContMDiff I (𝓡 n) ∞ g ∧ Nonempty (f.HomotopyRel g S) := by
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hf : Continuous (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) :=
    continuous_subtype_val.comp f.continuous
  obtain ⟨g, hg, hgS, -⟩ := hf.exists_contMDiff_approx_and_eqOn I (⊤ : ℕ∞)
    (ε := fun _ ↦ 1) continuous_const (fun _ ↦ zero_lt_one) hS hU hfU
  let gC : C(M, EuclideanSpace ℝ (Fin (n + 1))) := ⟨g, g.contMDiff.continuous⟩
  have hn : ∀ x, gC x ≠ 0 := fun x ↦ nearby_unit_ne_zero (f x) (gC x) (hg x)
  let gN := normalizedSphereMap gC hn
  have hgs : ContMDiff I (𝓡 n) ∞ gN :=
    (contMDiff_normalize g.contMDiff hn).codRestrict_sphere (n := n) (fun x ↦ (gN x).2)
  refine ⟨gN, hgs, ⟨{ toHomotopy := nearbyNormalizationHomotopy f gC hg, prop' := ?_ }⟩⟩
  intro t x hx
  apply Subtype.ext
  change NormedSpace.normalize ((f x : EuclideanSpace ℝ (Fin (n + 1))) +
    (t : ℝ) • (gC x - (f x : EuclideanSpace ℝ (Fin (n + 1))))) =
      (f x : EuclideanSpace ℝ (Fin (n + 1)))
  have heq : gC x = (f x : EuclideanSpace ℝ (Fin (n + 1))) := hgS hx
  rw [heq, sub_self, smul_zero, add_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (f x))

/-- A map into a higher-dimensional sphere contracts relative to a nonempty closed constant set,
provided it is already smooth on a neighborhood of that set. -/
theorem sphereMap_nullhomotopicRel_of_dim_lt [I.Boundaryless]
    (n : ℕ) (f : C(M, Sphere n)) (y : Sphere n) {S U : Set M}
    (hS : IsClosed S) (hSne : S.Nonempty) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) U)
    (hfixed : ∀ x ∈ S, f x = y) (hd : finrank ℝ B < n) :
    Nonempty (f.HomotopyRel (ContinuousMap.const _ y) S) := by
  classical
  obtain ⟨g, hg, ⟨Hfg⟩⟩ := exists_smoothSphereRepresentative_rel n f hS hU hfU
  let : Nonempty (Sphere n) := ⟨y⟩
  have hn : ¬ Function.Surjective g := not_surjective_contMDiff_of_dim_lt hg
    (by simpa only [finrank_euclideanSpace_fin] using hd)
  obtain ⟨p, hp⟩ : ∃ p, ∀ x, g x ≠ p := by
    simpa only [Function.Surjective, not_forall, not_exists] using hn
  have hgfixed : ∀ x ∈ S, g x = y :=
    fun x hx ↦ (Hfg.fst_eq_snd hx).symm.trans (hfixed x hx)
  have hyp : y ≠ p := by
    obtain ⟨x, hx⟩ := hSne
    rw [← hgfixed x hx]
    exact hp x
  obtain ⟨Hgy⟩ := sphereMap_nullhomotopicRel_of_omitted_point n g p y hp hyp S hgfixed
  exact ⟨Hfg.trans Hgy⟩

end NoExoticSixSphere
