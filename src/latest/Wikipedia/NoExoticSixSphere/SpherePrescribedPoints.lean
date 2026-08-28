import Wikipedia.NoExoticSixSphere.SphereFiniteHomotopyComparison

/-!
# Prescribing sphere-map values at separated source points

Lift a path of one target vector to actual orthogonal operators and use a
source cutoff to localize that path. This moves the chosen value while
fixing a prescribed disjoint closed set throughout. In particular, the
two suspension poles can be sent to their specified target poles.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths

theorem exists_orthogonal_path_lift {n : ℕ} {a b : UnitSphere (Vector n)} (P : Path a b) :
    ∃ A : C(I, OrthogonalOperators n), A 0 = identity n ∧
      ∀ t, (A t).val.val a.val = (P t).val := by
  let Q : C(I × Unit, UnitSphere (Vector n)) :=
    ⟨fun q ↦ P q.1, P.continuous.comp continuous_fst⟩
  obtain ⟨F, hF0, hFcol, _⟩ := exists_exactColumnLift Q a
    (ContinuousMap.const Unit (identity n)) (fun _ ↦ congrArg Subtype.val P.source.symm)
  let A : C(I, OrthogonalOperators n) :=
    F.comp ⟨fun t ↦ (t, ()), continuous_id.prodMk continuous_const⟩
  exact ⟨A, hF0 (), fun t ↦ hFcol t ()⟩

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [NormalSpace X] [T1Space X]

theorem exists_sphere_map_prescribed_point (f : C(X, UnitSphere (Vector n)))
    {S : Set X} (hS : IsClosed S) (p : X) (hp : p ∉ S)
    (b : UnitSphere (Vector n)) (P : Path (f p) b) :
    ∃ g : C(X, UnitSphere (Vector n)), f.HomotopicRel g S ∧ g p = b := by
  obtain ⟨β, hβS, hβp, hβbound⟩ := exists_continuous_zero_one_of_isClosed hS
    (isClosed_singleton (x := p)) (disjoint_singleton_right.mpr hp)
  let u : C(X, I) := ⟨fun x ↦ ⟨β x, hβbound x⟩, β.continuous.subtype_mk _⟩
  have huS (x : X) (hx : x ∈ S) : u x = 0 := Subtype.ext (hβS hx)
  have hup : u p = 1 := Subtype.ext (hβp (mem_singleton p))
  obtain ⟨A, hA0, hAcol⟩ := exists_orthogonal_path_lift P
  let B : I × X → OrthogonalOperators n := fun q ↦ A (q.1 * u q.2)
  have hB : Continuous B := A.continuous.comp
    (continuous_fst.mul (u.continuous.comp continuous_snd))
  let v : I × X → Vector n := fun q ↦ (B q).val.val (f q.2).val
  have hv : Continuous v :=
    (continuous_subtype_val.comp (continuous_subtype_val.comp hB)).clm_apply
      (continuous_subtype_val.comp (f.continuous.comp continuous_snd))
  have hunit (q : I × X) : v q ∈ UnitSphere (Vector n) := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact ((B q).property (f q.2).val).trans (ClosedHemisphere.unit_norm (f q.2))
  let K : C(I × X, UnitSphere (Vector n)) := ⟨fun q ↦ ⟨v q, hunit q⟩, hv.subtype_mk _⟩
  let g : C(X, UnitSphere (Vector n)) :=
    K.comp ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩
  refine ⟨g, ⟨{
    toContinuousMap := K
    map_zero_left := ?_
    map_one_left := fun _ ↦ rfl
    prop' := ?_ }⟩, ?_⟩
  · intro x
    apply Subtype.ext
    change (A (0 * u x)).val.val (f x).val = (f x).val
    rw [zero_mul, hA0]
    rfl
  · intro t x hx
    apply Subtype.ext
    change (A (t * u x)).val.val (f x).val = (f x).val
    rw [huS x hx, mul_zero, hA0]
    rfl
  · apply Subtype.ext
    change (A (1 * u p)).val.val (f p).val = b.val
    rw [hup, one_mul, hAcol]
    exact congrArg Subtype.val P.target

theorem exists_sphere_map_prescribed_pair [PathConnectedSpace (UnitSphere (Vector n))]
    (f : C(X, UnitSphere (Vector n))) (p q : X) (hpq : p ≠ q)
    (a b : UnitSphere (Vector n)) :
    ∃ g : C(X, UnitSphere (Vector n)), f.Homotopic g ∧ g p = a ∧ g q = b := by
  obtain ⟨g, H, hgp⟩ := exists_sphere_map_prescribed_point f isClosed_empty p (notMem_empty _)
    a (PathConnectedSpace.somePath (f p) a)
  obtain ⟨k, ⟨K⟩, hkq⟩ := exists_sphere_map_prescribed_point g isClosed_singleton q
    (by simpa only [mem_singleton_iff] using hpq.symm)
    b (PathConnectedSpace.somePath (g q) b)
  have hkp : k p = a := (K.apply_one p).symm.trans
    ((K.eq_fst 1 (mem_singleton p)).trans hgp)
  exact ⟨k, H.homotopic.trans ⟨K.toHomotopy⟩, hkp, hkq⟩

end NoExoticSixSphere
