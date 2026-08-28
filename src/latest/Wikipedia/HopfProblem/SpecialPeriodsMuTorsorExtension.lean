import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCore

/-!
# Actual extension from precisely invariant triangle patches

A seed satisfying its returning-subgroup equations extends to the literal
union of the triangle translates.  Independence of the word and sheet
representative is proved from the returning-subgroup condition and the
affine cocycle law.  The resulting function is holomorphic on this open
saturation and satisfies the complete free-product action law there.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

namespace PreciselyInvariantPatch

variable {P : PreciselyInvariantPatch} {c : AffineCocycle} (s : P.Seed c)

theorem Seed.translated_values_agree (g h : TriangleGroup) (x y : ℍ)
    (hx : x ∈ P.sheet) (hy : y ∈ P.sheet)
    (he : triangleGeometricRepresentation g x = triangleGeometricRepresentation h y) :
    c.fibreMap g x (s.toFun x) = c.fibreMap h y (s.toFun y) := by
  have hxy : triangleGeometricRepresentation (h⁻¹ * g) x = y := by
    rw [map_mul]
    change triangleGeometricRepresentation h⁻¹ (triangleGeometricRepresentation g x) = y
    rw [he, map_inv]
    exact (triangleGeometricRepresentation h).symm_apply_apply y
  have hk : h⁻¹ * g ∈ P.stabilizer :=
    (P.stabilizer_mem_iff (h⁻¹ * g) x hx).mp (hxy ▸ hy)
  have hs := s.equivariant ⟨h⁻¹ * g, hk⟩ x hx
  change s.toFun (triangleGeometricRepresentation (h⁻¹ * g) x) =
    c.fibreMap (h⁻¹ * g) x (s.toFun x) at hs
  rw [hxy] at hs
  calc
    c.fibreMap g x (s.toFun x) = c.fibreMap (h * (h⁻¹ * g)) x (s.toFun x) := by
      rw [mul_inv_cancel_left]
    _ = c.fibreMap h (triangleGeometricRepresentation (h⁻¹ * g) x)
        (c.fibreMap (h⁻¹ * g) x (s.toFun x)) := c.fibreMap_mul ..
    _ = c.fibreMap h y (s.toFun y) := by rw [hxy, ← hs]

variable (P) in
/-- A representative is chosen only from the proved saturation membership. -/
def representative (z : P.saturation) : TriangleGroup × P.sheet :=
  let hg := z.property.choose_spec
  ⟨z.property.choose, ⟨hg.choose, hg.choose_spec.1⟩⟩

variable (P) in
theorem representative_spec (z : P.saturation) :
    triangleGeometricRepresentation (P.representative z).1 (P.representative z).2 = z :=
  z.property.choose_spec.choose_spec.2

/-- The actual extension, set to zero outside the open saturation. -/
def Seed.extend (z : ℍ) : ℂ := by
  classical
  exact if hz : z ∈ P.saturation then
    let r := P.representative ⟨z, hz⟩
    c.fibreMap r.1 r.2 (s.toFun r.2)
  else 0

theorem Seed.extend_translate (g : TriangleGroup) (x : ℍ) (hx : x ∈ P.sheet) :
    s.extend (triangleGeometricRepresentation g x) = c.fibreMap g x (s.toFun x) := by
  have hz : triangleGeometricRepresentation g x ∈ P.saturation := ⟨g, x, hx, rfl⟩
  rw [Seed.extend, dif_pos hz]
  exact s.translated_values_agree _ g _ x
    (P.representative ⟨_, hz⟩).2.property hx (P.representative_spec ⟨_, hz⟩)

theorem Seed.extend_eq (x : ℍ) (hx : x ∈ P.sheet) : s.extend x = s.toFun x := by
  simpa only [map_one, Equiv.Perm.one_apply, c.fibreMap_one] using s.extend_translate 1 x hx

/-- The extension satisfies all affine laws, not merely the two
generator identities, on the entire saturation. -/
theorem Seed.extend_equivariant : c.EquivariantOn s.extend P.saturation := by
  intro g z hz
  obtain ⟨h, x, hx, rfl⟩ := hz
  have hmul : triangleGeometricRepresentation g (triangleGeometricRepresentation h x) =
      triangleGeometricRepresentation (g * h) x := by simp
  rw [hmul, s.extend_translate (g * h) x hx, s.extend_translate h x hx, c.fibreMap_mul]

/-- There is no ambiguity in extension once the local seed is fixed. -/
theorem Seed.extend_unique {f : ℍ → ℂ}
    (hf : c.EquivariantOn f P.saturation) (he : EqOn f s.toFun P.sheet) :
    EqOn f s.extend P.saturation := by
  rintro z ⟨g, x, hx, rfl⟩
  rw [hf g x (P.mem_saturation x hx), s.extend_translate g x hx, he hx]

/-- On each translated sheet the extension is the original holomorphic
seed composed with the actual inverse deck map and the affine cocycle. -/
theorem Seed.extend_holomorphic :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω s.extend P.saturation := by
  rintro z ⟨g, x, hx, rfl⟩
  apply ContMDiffAt.contMDiffWithinAt
  let v : ℍ → ℍ := triangleGeometricRepresentation g⁻¹
  have hv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω v :=
    triangleGeometricRepresentation_holomorphic g⁻¹
  have hvx : v (triangleGeometricRepresentation g x) = x := by
    simp [v, map_inv]
  have hsx : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s.toFun x :=
    s.holomorphic.contMDiffAt (P.sheet.isOpen.mem_nhds hx)
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (s.toFun ∘ v)
      (triangleGeometricRepresentation g x) :=
    hsx.comp_of_eq (hv _) hvx
  have ha := ((c.scale_holomorphic g).comp hv) (triangleGeometricRepresentation g x)
  have hb := ((c.shift_holomorphic g).comp hv) (triangleGeometricRepresentation g x)
  apply (ha.mul hcomp |>.add hb).congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 (triangleGeometricRepresentation g x), v y ∈ P.sheet := by
    apply hv.continuous.continuousAt.preimage_mem_nhds
    rw [hvx]
    exact P.sheet.isOpen.mem_nhds hx
  filter_upwards [hnear] with y hy
  have hgy : triangleGeometricRepresentation g (v y) = y := by
    simp [v, map_inv]
  have he := s.extend_translate g (v y) hy
  rw [hgy] at he
  exact he

end PreciselyInvariantPatch

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
