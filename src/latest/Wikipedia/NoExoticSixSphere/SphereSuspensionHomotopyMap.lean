import Wikipedia.NoExoticSixSphere.SphereMapSuspension

/-!
# Suspension acts on actual homotopies

The homotopy is jointly continuous by descent from the compact latitude
cylinder, not merely continuous separately in time and position. Suspension
therefore respects homotopy, and the suspension of a nullhomotopic sphere map
is nullhomotopic. No injectivity or surjectivity on homotopy classes is assumed.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.SphereMapSuspension

open Wikipedia.HopfProblem.SphereHomology

variable {m n : ℕ} {f g : C(Sphere m, Sphere n)}

def slice (H : f.Homotopy g) (u : unitInterval) : C(Sphere m, Sphere n) :=
  H.toContinuousMap.comp ⟨fun x ↦ (u, x), continuous_const.prodMk continuous_id⟩

theorem isQuotientMap_timeLatitude (m : ℕ) :
    Topology.IsQuotientMap (fun z : unitInterval × (unitInterval × Sphere m) ↦
      (z.1, Latitude.point m z.2.1 z.2.2)) := by
  apply Topology.IsQuotientMap.of_surjective_continuous
  · intro z
    obtain ⟨⟨t, x⟩, hx⟩ := Latitude.point_surjective m z.2
    exact ⟨(z.1, (t, x)), Prod.ext rfl hx⟩
  · exact continuous_fst.prodMk ((Latitude.point_continuous m).comp continuous_snd)

def homotopy (H : f.Homotopy g) : (map f).Homotopy (map g) where
  toFun z := map (slice H z.1) z.2
  continuous_toFun := by
    apply (isQuotientMap_timeLatitude m).continuous_iff.mpr
    have hc : Continuous (fun z : unitInterval × (unitInterval × Sphere m) ↦
        Latitude.point n z.2.1 (H (z.1, z.2.2))) :=
      (Latitude.point_continuous n).comp
        ((continuous_fst.comp continuous_snd).prodMk
          (H.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
    convert hc using 1
    funext z
    exact map_point (slice H z.1) z.2.1 z.2.2
  map_zero_left y := by
    have he : slice H 0 = f := by
      apply ContinuousMap.ext
      intro x
      exact H.apply_zero x
    change map (slice H 0) y = map f y
    rw [he]
  map_one_left y := by
    have he : slice H 1 = g := by
      apply ContinuousMap.ext
      intro x
      exact H.apply_one x
    change map (slice H 1) y = map g y
    rw [he]

theorem map_homotopic (h : f.Homotopic g) : (map f).Homotopic (map g) := by
  obtain ⟨H⟩ := h
  exact ⟨homotopy H⟩

theorem parameter_point (m : ℕ) (t : unitInterval) (x : Sphere m) :
    Latitude.parameter m (Latitude.point m t x) = t := by
  apply Latitude.height_injective
  rw [Latitude.height_parameter]
  rfl

theorem continuous_parameter (m : ℕ) : Continuous (Latitude.parameter m) := by
  have hh : Continuous (fun y : Sphere (m + 1) ↦ y.val 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (m + 2) ↦ ℝ) 0).comp continuous_subtype_val
  exact ((hh.add continuous_const).div_const 2).subtype_mk _

theorem map_const_point (b : Sphere n) (y : Sphere (m + 1)) :
    map (ContinuousMap.const (Sphere m) b) y = Latitude.point n (Latitude.parameter m y) b := by
  obtain ⟨⟨t, x⟩, rfl⟩ := Latitude.point_surjective m y
  rw [map_point, parameter_point]
  rfl

/-- Suspension of a constant map factors through the latitude interval, which
contracts. It is not itself defined to be constant. -/
def constantNullhomotopy (b : Sphere n) :
    (map (ContinuousMap.const (Sphere m) b)).Homotopy
      (ContinuousMap.const _ (Latitude.point n 0 b)) where
  toFun z := Latitude.point n (unitInterval.symm z.1 * Latitude.parameter m z.2) b
  continuous_toFun := (Latitude.point_continuous n).comp
    (((unitInterval.continuous_symm.comp continuous_fst).mul
      ((continuous_parameter m).comp continuous_snd)).prodMk continuous_const)
  map_zero_left y := by
    simpa using (map_const_point b y).symm
  map_one_left y := by simp

theorem map_nullhomotopic (h : f.Nullhomotopic) : (map f).Nullhomotopic := by
  obtain ⟨b, H⟩ := h
  exact ⟨Latitude.point n 0 b, (map_homotopic H).trans ⟨constantNullhomotopy b⟩⟩

end NoExoticSixSphere.SphereMapSuspension
