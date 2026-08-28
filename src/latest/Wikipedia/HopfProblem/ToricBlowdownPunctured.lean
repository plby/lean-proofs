import Wikipedia.HopfProblem.ToricBlowdownLocal
import Wikipedia.HopfProblem.ProjectivePlanePunctured
import Wikipedia.HopfProblem.AffineBlowupPuncturedBiholomorph

/-!
# The blow-down is biholomorphic away from the three centers

The source is the actual open complement of the three exceptional fibres,
and the target is the ordinary projective plane minus its three coordinate
points. Both use inherited, rather than transported, analytic atlases.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace

local notation "I₂" => modelWithCornersSelf ℂ (CoordinateSpace 2)

def blowdownPuncturedSpace : TopologicalSpace.Opens (rayDivisor 0) :=
  ⟨blowdown ⁻¹' (ProjectivePlane.puncturedSpace : Set ProjectivePlane.Space),
    ProjectivePlane.puncturedSpace.isOpen.preimage blowdown_continuous⟩

def puncturedBlowdown : blowdownPuncturedSpace → ProjectivePlane.puncturedSpace :=
  (ProjectivePlane.puncturedSpace : Set ProjectivePlane.Space).restrictPreimage blowdown

@[simp] theorem puncturedBlowdown_coe (x : blowdownPuncturedSpace) :
    (puncturedBlowdown x : ProjectivePlane.Space) = blowdown x := rfl

theorem puncturedBlowdown_isProperMap : IsProperMap puncturedBlowdown :=
  blowdown_isProperMap.restrictPreimage _

theorem puncturedBlowdown_surjective : Function.Surjective puncturedBlowdown :=
  blowdown_surjective.restrictPreimage _

theorem puncturedBlowdown_injective : Function.Injective puncturedBlowdown := by
  intro x y hxy
  have h : blowdown (x : rayDivisor 0) = blowdown (y : rayDivisor 0) :=
    congrArg Subtype.val hxy
  obtain ⟨k, z, hz⟩ := ProjectivePlane.affineMap_jointly_surjective (blowdown x)
  have hx : (x : rayDivisor 0) ∈ range (blowupMap k) := by
    rw [← blowdown_preimage_affineTarget]
    change blowdown (x : rayDivisor 0) ∈ ProjectivePlane.affineTarget k
    exact hz ▸ ProjectivePlane.affineMap_mem_target k z
  have hy : (y : rayDivisor 0) ∈ range (blowupMap k) := by
    rw [← blowdown_preimage_affineTarget]
    change blowdown (y : rayDivisor 0) ∈ ProjectivePlane.affineTarget k
    rw [← h, ← hz]
    exact ProjectivePlane.affineMap_mem_target k z
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  have hp : AffineBlowup.projection u = AffineBlowup.projection v := by
    apply ProjectivePlane.affineMap_injective k
    rw [← blowdown_blowupMap, ← blowdown_blowupMap, hu, hv]
    exact h
  have hnu : AffineBlowup.projection u ≠ 0 := by
    intro hzero
    apply x.2
    rw [← hu, blowdown_blowupMap, hzero]
    exact ProjectivePlane.coordinatePoint_mem_coordinatePoints k
  have hnv : AffineBlowup.projection v ≠ 0 := hp ▸ hnu
  have huv : u = v := congrArg Subtype.val
    (AffineBlowup.puncturedProjection_bijective.1
      (show AffineBlowup.puncturedProjection ⟨u, hnu⟩ =
        AffineBlowup.puncturedProjection ⟨v, hnv⟩ from Subtype.ext hp))
  apply Subtype.ext
  rw [← hu, ← hv, huv]

theorem puncturedBlowdown_holomorphic : ContMDiff I₂ I₂ ω puncturedBlowdown := by
  intro x
  have he : ContMDiffAt I₂ I₂ ω
      (fun y : blowdownPuncturedSpace => (puncturedBlowdown y : ProjectivePlane.Space)) x ↔
    ContMDiffAt I₂ I₂ ω puncturedBlowdown x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((blowdown_holomorphic.comp contMDiff_subtype_val) x)

def puncturedBlowdownHomeomorph : blowdownPuncturedSpace ≃ₜ ProjectivePlane.puncturedSpace :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective puncturedBlowdown
      ⟨puncturedBlowdown_injective, puncturedBlowdown_surjective⟩)
    puncturedBlowdown_isProperMap.continuous puncturedBlowdown_isProperMap.isClosedMap

@[simp] theorem puncturedBlowdownHomeomorph_apply (x : blowdownPuncturedSpace) :
    puncturedBlowdownHomeomorph x = puncturedBlowdown x := rfl

theorem puncturedBlowdown_inverse_eq_of_blowdown (v : ProjectivePlane.puncturedSpace)
    (x : rayDivisor 0) (hx : blowdown x = (v : ProjectivePlane.Space)) :
    (puncturedBlowdownHomeomorph.symm v : rayDivisor 0) = x := by
  let x' : blowdownPuncturedSpace := ⟨x, by
    change blowdown x ∈ ProjectivePlane.puncturedSpace
    rw [hx]
    exact v.2⟩
  have he : puncturedBlowdownHomeomorph x' = v := Subtype.ext hx
  rw [← he, puncturedBlowdownHomeomorph.symm_apply_apply]

theorem puncturedBlowdown_inverse_eq_left (k : Fin 3) (v : ProjectivePlane.puncturedSpace)
    (ht : (v : ProjectivePlane.Space) ∈ ProjectivePlane.affineTarget k)
    (hv : ProjectivePlane.affineCoords k v 1 ≠ 0) :
    (puncturedBlowdownHomeomorph.symm v : rayDivisor 0) =
      blowupAffine k false ![ProjectivePlane.affineCoords k v 0 /
        ProjectivePlane.affineCoords k v 1, ProjectivePlane.affineCoords k v 1] := by
  apply puncturedBlowdown_inverse_eq_of_blowdown
  rw [blowdown_blowupAffine]
  have he : AffineBlowup.projection (AffineBlowup.affineMap false
      ![ProjectivePlane.affineCoords k v 0 / ProjectivePlane.affineCoords k v 1,
        ProjectivePlane.affineCoords k v 1]) = ProjectivePlane.affineCoords k v := by
    ext i
    fin_cases i
    · exact div_mul_cancel₀ _ hv
    · rfl
  rw [he]
  exact ProjectivePlane.affineMap_affineCoords k v ht

theorem puncturedBlowdown_inverse_eq_right (k : Fin 3) (v : ProjectivePlane.puncturedSpace)
    (ht : (v : ProjectivePlane.Space) ∈ ProjectivePlane.affineTarget k)
    (hv : ProjectivePlane.affineCoords k v 0 ≠ 0) :
    (puncturedBlowdownHomeomorph.symm v : rayDivisor 0) =
      blowupAffine k true ![ProjectivePlane.affineCoords k v 0,
        ProjectivePlane.affineCoords k v 1 / ProjectivePlane.affineCoords k v 0] := by
  apply puncturedBlowdown_inverse_eq_of_blowdown
  rw [blowdown_blowupAffine]
  have he : AffineBlowup.projection (AffineBlowup.affineMap true
      ![ProjectivePlane.affineCoords k v 0,
        ProjectivePlane.affineCoords k v 1 / ProjectivePlane.affineCoords k v 0]) =
        ProjectivePlane.affineCoords k v := by
    ext i
    fin_cases i
    · rfl
    · exact mul_div_cancel₀ _ hv
  rw [he]
  exact ProjectivePlane.affineMap_affineCoords k v ht

theorem puncturedBlowdownHomeomorph_symm_holomorphic :
    ContMDiff I₂ I₂ ω puncturedBlowdownHomeomorph.symm := by
  intro v
  have he : ContMDiffAt I₂ I₂ ω
      (fun w : ProjectivePlane.puncturedSpace =>
        (puncturedBlowdownHomeomorph.symm w : rayDivisor 0)) v ↔
    ContMDiffAt I₂ I₂ ω puncturedBlowdownHomeomorph.symm v :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  obtain ⟨k, z, hz⟩ := ProjectivePlane.affineMap_jointly_surjective v.1
  have ht : v.1 ∈ ProjectivePlane.affineTarget k := hz ▸ ProjectivePlane.affineMap_mem_target k z
  have hcoords : ContMDiffAt I₂ I₂ ω
      (fun w : ProjectivePlane.puncturedSpace => ProjectivePlane.affineCoords k w) v :=
    ((ProjectivePlane.affineCoords_holomorphicOn k).contMDiffAt
      ((ProjectivePlane.affineTarget_isOpen k).mem_nhds ht)).comp _
        contMDiff_subtype_val.contMDiffAt
  have hpatch : ∀ᶠ w : ProjectivePlane.puncturedSpace in 𝓝 v,
      (w : ProjectivePlane.Space) ∈ ProjectivePlane.affineTarget k :=
    ((ProjectivePlane.affineTarget_isOpen k).preimage continuous_subtype_val).mem_nhds ht
  by_cases h1 : ProjectivePlane.affineCoords k v 1 ≠ 0
  · have hc : ContDiffAt ℂ ω (fun w : CoordinateSpace 2 => ![w 0 / w 1, w 1])
        (ProjectivePlane.affineCoords k v) := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · exact (contDiff_apply ℂ ℂ 0).contDiffAt.div (contDiff_apply ℂ ℂ 1).contDiffAt h1
      · exact (contDiff_apply ℂ ℂ 1).contDiffAt
    have hm := (blowupAffine_holomorphic k false).contMDiffAt.comp v
      (hc.contMDiffAt.comp v hcoords)
    apply hm.congr_of_eventuallyEq
    have hn := hcoords.continuousAt.eventually
      ((isOpen_ne_fun (continuous_apply 1) continuous_const).mem_nhds h1)
    filter_upwards [hpatch, hn] with w hw hw1
    exact puncturedBlowdown_inverse_eq_left k w hw hw1
  · have h0 : ProjectivePlane.affineCoords k v 0 ≠ 0 := by
      intro hv0
      have hvzero : ProjectivePlane.affineCoords k v = 0 := by
        ext i
        fin_cases i
        · exact hv0
        · exact not_ne_iff.mp h1
      apply v.2
      rw [← ProjectivePlane.affineMap_affineCoords k v ht, hvzero]
      exact ProjectivePlane.coordinatePoint_mem_coordinatePoints k
    have hc : ContDiffAt ℂ ω (fun w : CoordinateSpace 2 => ![w 0, w 1 / w 0])
        (ProjectivePlane.affineCoords k v) := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · exact (contDiff_apply ℂ ℂ 0).contDiffAt
      · exact (contDiff_apply ℂ ℂ 1).contDiffAt.div (contDiff_apply ℂ ℂ 0).contDiffAt h0
    have hm := (blowupAffine_holomorphic k true).contMDiffAt.comp v
      (hc.contMDiffAt.comp v hcoords)
    apply hm.congr_of_eventuallyEq
    have hn := hcoords.continuousAt.eventually
      ((isOpen_ne_fun (continuous_apply 0) continuous_const).mem_nhds h0)
    filter_upwards [hpatch, hn] with w hw hw0
    exact puncturedBlowdown_inverse_eq_right k w hw hw0

/-- The actual global blow-down is biholomorphic away from exactly the
three exceptional fibres over the projective coordinate points. -/
def puncturedBlowdownBiholomorph :
    Diffeomorph I₂ I₂ blowdownPuncturedSpace ProjectivePlane.puncturedSpace ω where
  toEquiv := puncturedBlowdownHomeomorph.toEquiv
  contMDiff_toFun := puncturedBlowdown_holomorphic
  contMDiff_invFun := puncturedBlowdownHomeomorph_symm_holomorphic

end Wikipedia.HopfProblem.ToricComponent
