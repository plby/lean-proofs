import Wikipedia.NoExoticSixSphere.SphereSuspension
import Wikipedia.NoExoticSixSphere.PathFamilyCurrying

/-!
# Descending meridian-family homotopies to the actual sphere

A homotopy in a fixed-endpoint path space is constant on each collapsed
suspension slice at every time. It therefore descends through the explicit
sphere quotient. A constant path family descends to a map factoring through
the latitude interval, which is nullhomotopic.
-/

open unitInterval

namespace NoExoticSixSphere.SphereSuspension

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace Y]

noncomputable def meridians (v : UnitSphere E) (f : C(UnitSphere E, Y)) :
    C(Equator v, Path (f v) (f (antipode v))) :=
  PathFamilies.curry (f.comp ⟨point v, continuous_point v⟩)
    (fun x ↦ congrArg f (point_zero v x)) (fun x ↦ congrArg f (point_one v x))

theorem meridians_apply (v : UnitSphere E) (f : C(UnitSphere E, Y))
    (x : Equator v) (t : I) : meridians v f x t = f (point v (t, x)) := rfl

variable (v : UnitSphere E) (f : C(UnitSphere E, Y))
  (γ : Path (f v) (f (antipode v)))
  (H : (meridians v f).Homotopy (ContinuousMap.const _ γ))

noncomputable def homotopyFamily : C(I × (I × Equator v), Y) :=
  (PathFamilies.uncurry H.toContinuousMap).comp {
    toFun z := (z.2.1, (z.1, z.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) }

theorem homotopyFamily_fibers (r : I) (p q : I × Equator v)
    (hpq : point v p = point v q) : homotopyFamily v f γ H (r, p) =
      homotopyFamily v f γ H (r, q) := by
  rcases point_fibers v p q hpq with h | ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [h]
  · change H (r, p.2) p.1 = H (r, q.2) q.1
    rw [hp, hq, Path.source, Path.source]
  · change H (r, p.2) p.1 = H (r, q.2) q.1
    rw [hp, hq, Path.target, Path.target]

variable [Nonempty (Equator v)]

noncomputable def descendFun (z : I × UnitSphere E) : Y :=
  homotopyFamily v f γ H (z.1, Function.surjInv (surjective_point v) z.2)

theorem descendFun_point (r : I) (p : I × Equator v) :
    descendFun v f γ H (r, point v p) = homotopyFamily v f γ H (r, p) :=
  homotopyFamily_fibers v f γ H r _ p
    (Function.surjInv_eq (surjective_point v) (point v p))

variable [FiniteDimensional ℝ E]

theorem isQuotientMap_timePoint :
    Topology.IsQuotientMap (fun z : I × (I × Equator v) ↦ (z.1, point v z.2)) := by
  apply Topology.IsQuotientMap.of_surjective_continuous
  · intro z
    obtain ⟨p, hp⟩ := surjective_point v z.2
    exact ⟨(z.1, p), Prod.ext rfl hp⟩
  · exact continuous_fst.prodMk ((continuous_point v).comp continuous_snd)

noncomputable def descended : C(I × UnitSphere E, Y) where
  toFun := descendFun v f γ H
  continuous_toFun := by
    apply (isQuotientMap_timePoint v).continuous_iff.mpr
    have heq : (fun z : I × (I × Equator v) ↦
        descendFun v f γ H (z.1, point v z.2)) = homotopyFamily v f γ H :=
      funext (fun z ↦ descendFun_point v f γ H z.1 z.2)
    change Continuous (fun z : I × (I × Equator v) ↦
      descendFun v f γ H (z.1, point v z.2))
    rw [heq]
    exact (homotopyFamily v f γ H).continuous

noncomputable def heightPathMap : C(UnitSphere E, Y) :=
  γ.toContinuousMap.comp ⟨height v, continuous_height v⟩

noncomputable def descendedHomotopy : f.Homotopy (heightPathMap v f γ) where
  toContinuousMap := descended v f γ H
  map_zero_left y := by
    obtain ⟨⟨t, x⟩, rfl⟩ := surjective_point v y
    change descendFun v f γ H (0, point v (t, x)) = _
    rw [descendFun_point]
    change H (0, x) t = f (point v (t, x))
    rw [H.apply_zero]
    rfl
  map_one_left y := by
    obtain ⟨⟨t, x⟩, rfl⟩ := surjective_point v y
    change descendFun v f γ H (1, point v (t, x)) = γ (height v (point v (t, x)))
    rw [descendFun_point, height_point]
    change H (1, x) t = γ t
    rw [H.apply_one]
    rfl

omit [Nonempty (Equator v)] [FiniteDimensional ℝ E] in
noncomputable def heightPathNullhomotopy :
    (heightPathMap v f γ).Homotopy (ContinuousMap.const _ (f v)) where
  toFun z := γ (unitInterval.symm z.1 * height v z.2)
  continuous_toFun := γ.continuous.comp
    ((unitInterval.continuous_symm.comp continuous_fst).mul
      ((continuous_height v).comp continuous_snd))
  map_zero_left y := by simp [heightPathMap]
  map_one_left y := by simp [Path.source]

include γ H in
theorem nullhomotopic_of_meridians : f.Homotopic (ContinuousMap.const _ (f v)) :=
  ⟨(descendedHomotopy v f γ H).trans (heightPathNullhomotopy v f γ)⟩

end NoExoticSixSphere.SphereSuspension
