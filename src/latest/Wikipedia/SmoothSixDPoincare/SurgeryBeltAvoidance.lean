import Wikipedia.SmoothSixDPoincare.SurgeryInteriorCoordinates
import Wikipedia.SmoothSixDPoincare.OpenHomotopyExtension
import Wikipedia.SmoothSixDPoincare.Hemisphere
import Wikipedia.NoExoticSixSphere.RelativeZeroAvoidance
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Moving circles off the actual surgery belt sphere

On the open preimage of the disk-times-sphere neighborhood, perturb only the
normal coordinate. The relative zero-avoidance homotopy fixes a whole outer
radial collar. A closed inner tube therefore supports its extension to the
entire original circle. The boundary homeomorphism need only be continuous.
-/

noncomputable section

open Set Function Topology TopologicalSpace ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {N P R X Y : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N] [NormedAddCommGroup P]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair N P R X Y)

/-- Every circle map can be homotoped off the belt when the normal disk
has dimension at least two. -/
theorem exists_belt_avoiding_circle (hdim : 1 < Module.finrank ℝ N)
    (g : C(Hemisphere.Sphere 1, Y)) :
    ∃ g' : C(Hemisphere.Sphere 1, Y),
      (∀ x, g' x ∉ range d.beltSphere) ∧ g.Homotopic g' := by
  let U : Opens (Hemisphere.Sphere 1) :=
    ⟨g ⁻¹' d.NewInterior, d.isOpen_newInterior.preimage g.continuous⟩
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let e := d.newInteriorHomeomorph
  let coord : C(U, OpenUnitBall N × UnitSphere P) :=
    ⟨fun x => e.symm ⟨g x, x.property⟩,
      e.symm.continuous.comp ((g.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  let normal : C(U, N) :=
    ⟨fun x => (coord x).1, continuous_subtype_val.comp coord.continuous.fst⟩
  have hparam (x : U) :
      d.newPiece (⟨(coord x).1, (coord x).1.property.le⟩, (coord x).2) = g x :=
    congrArg (fun y : d.NewInterior => (y : Y)) (e.apply_symm_apply ⟨g x, x.property⟩)
  obtain ⟨q, hq, G, hclose⟩ := NoExoticSixSphere.exists_nonzero_homotopy_small
    (I := 𝓡 1) normal (1 / 8) (by norm_num)
    (by simpa only [finrank_euclideanSpace_fin] using hdim)
  have hnorm (t) (x : U) : ‖G (t, x)‖ < 1 := by
    by_cases hx : 1 / 4 ≤ ‖normal x‖
    · rw [G.eq_fst t (show x ∈ {x | 2 * (1 / 8 : ℝ) ≤ ‖normal x‖} from by
        change 2 * (1 / 8 : ℝ) ≤ ‖normal x‖
        linarith)]
      exact (coord x).1.property
    · have hdist : ‖G (t, x) - normal x‖ < 1 / 8 := by
        simpa only [dist_eq_norm] using hclose t x
      have hbound := norm_add_le (G (t, x) - normal x) (normal x)
      rw [sub_add_cancel] at hbound
      linarith
  let H : C(unitInterval × U, Y) :=
    ⟨fun z => (e (⟨G z, hnorm z.1 z.2⟩, (coord z.2).2) : Y),
      continuous_subtype_val.comp (e.continuous.comp
        ((G.continuous.subtype_mk _).prodMk (coord.continuous.snd.comp continuous_snd)))⟩
  have hreturn (t) (x : U) (hx : G (t, x) = normal x) : H (t, x) = g x := by
    have hu : (⟨G (t, x), hnorm t x⟩ : OpenUnitBall N) = (coord x).1 := Subtype.ext hx
    change (e (⟨G (t, x), _⟩, (coord x).2) : Y) = _
    rw [hu]
    exact hparam x
  have hzero (x : U) : H (0, x) = g x := hreturn 0 x (G.apply_zero x)
  let K₀ : Set Y := d.newPiece '' {p : UnitBall N × UnitSphere P | ‖(p.1 : N)‖ ≤ 1 / 2}
  have hK₀ : IsClosed K₀ := d.newPiece_closed.isClosedMap _
    (isClosed_le (continuous_subtype_val.comp continuous_fst).norm continuous_const)
  have hK₀U : K₀ ⊆ d.NewInterior := by
    rintro _ ⟨p, hp, rfl⟩
    apply (d.newPiece_mem_newInterior_iff p).mpr
    exact hp.trans_lt (by norm_num)
  let K : Set (Hemisphere.Sphere 1) := g ⁻¹' K₀
  have hK : IsClosed K := hK₀.preimage g.continuous
  have hKU : K ⊆ U := fun _ hx => hK₀U hx
  have hfixed (t) (x : U) (hx : (x : Hemisphere.Sphere 1) ∉ K) : H (t, x) = g x := by
    have hlarge : 1 / 2 < ‖normal x‖ := by
      by_contra! hh
      apply hx
      exact ⟨(⟨(coord x).1, (coord x).1.property.le⟩, (coord x).2), hh, hparam x⟩
    have hsafe : x ∈ {x | 2 * (1 / 8 : ℝ) ≤ ‖normal x‖} := by
      change 2 * (1 / 8 : ℝ) ≤ ‖normal x‖
      linarith
    exact hreturn t x (G.eq_fst t hsafe)
  obtain ⟨g', G', hlocal, houtside⟩ :=
    OpenHomotopyExtension.exists_extended_homotopy U g H hK hKU hzero hfixed
  refine ⟨g', ?_, ⟨G'⟩⟩
  intro x hxB
  by_cases hx : x ∈ U
  · have heq : g' x = H (1, ⟨x, hx⟩) := (G'.apply_one x).symm.trans (hlocal 1 ⟨x, hx⟩)
    rw [heq] at hxB
    have hzero' : G (1, ⟨x, hx⟩) = 0 :=
      (d.newInteriorHomeomorph_mem_belt_iff _).mp hxB
    rw [G.apply_one] at hzero'
    exact hq ⟨x, hx⟩ hzero'
  · have heq : g' x = g x := (G'.apply_one x).symm.trans
      (houtside 1 x (fun h => hx (hKU h)))
    rw [heq] at hxB
    obtain ⟨v, hv⟩ := hxB
    apply hx
    change g x ∈ d.NewInterior
    rw [← hv]
    exact d.beltSphere_mem_newInterior v

/-- Circle contractions in the belt complement imply circle contractions
in the entire new boundary. -/
theorem circle_nullhomotopies_of_beltComplement (hdim : 1 < Module.finrank ℝ N)
    (hnull : ∀ g : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, Y), ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  intro g
  obtain ⟨g', havoid, hgg'⟩ := d.exists_belt_avoiding_circle hdim g
  let g₀ : C(Hemisphere.Sphere 1, d.NewComplement) :=
    ⟨fun x => ⟨g' x, havoid x⟩, g'.continuous.subtype_mk _⟩
  let inc : C(d.NewComplement, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨q, hq⟩ := hnull g₀
  have hh : (inc.comp g₀).Homotopic (ContinuousMap.const _ (q : Y)) :=
    (Homotopic.refl inc).comp hq
  exact ⟨q, hgg'.trans hh⟩

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
