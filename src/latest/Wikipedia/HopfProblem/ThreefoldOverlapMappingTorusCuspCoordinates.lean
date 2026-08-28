import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyQuotient
import Wikipedia.HopfProblem.CuspPuncturedDomain
import Wikipedia.HopfProblem.MappingTorusTopology

/-!
# Real logarithmic coordinates for the entire cusp overlap

The actual varying-period family already has its proved real period
coordinates. Separating the real and imaginary parts of its logarithmic
base gives a height half-line times the real mapping-torus cylinder.
The genuine clockwise deck action becomes the defining mapping-torus
deck action, with the literal integral monodromy `M₀`.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp

open SpecialPeriods.CuspFamily CuspUniformization

/-- The actual period-coordinate homeomorphism with integral matrix `M₀`. -/
abbrev monodromy : RealTorus₄ ≃ₜ RealTorus₄ := cuspTorusHomeomorph 1

abbrev Boundary := MappingTorus.Torus monodromy

private def monodromyHom : Multiplicative ℤ →* (RealTorus₄ ≃ₜ RealTorus₄) where
  toFun k := cuspTorusHomeomorph k.toAdd
  map_one' := cuspTorusHomeomorph_zero_eq
  map_mul' k l := by
    apply Homeomorph.ext
    exact cuspTorusHomeomorph_add_apply k.toAdd l.toAdd

/-- Every power is the previously proved actual integral deck transformation. -/
theorem monodromy_zpow (k : ℤ) : monodromy ^ k = cuspTorusHomeomorph k := by
  have h := map_zpow monodromyHom (Multiplicative.ofAdd (1 : ℤ)) k
  change cuspTorusHomeomorph
      (((Multiplicative.ofAdd (1 : ℤ)) ^ k).toAdd) = monodromy ^ k at h
  simpa using h.symm

/-- The lower logarithmic height corresponding to the actual puncture radius. -/
def heightThreshold (r : ℝ) : ℝ := -Real.log r / (2 * Real.pi)

abbrev Height (r : ℝ) := Ioi (heightThreshold r)

theorem mem_logBase_iff_height (r : ℝ) (hr : 0 < r) (s : ℂ) :
    s ∈ logBase r ↔ heightThreshold r < s.im := by
  simpa only [mem_logBase, mem_logDomain, heightThreshold] using
    (mem_logDomain_iff_im r hr (s, (0 : ComplexPlane₂)))

/-- A literal logarithm with specified real coordinate and allowed height. -/
def logPoint (r : ℝ) (hr : 0 < r) (t : ℝ) (h : Height r) : LogBase r :=
  ⟨(t : ℂ) + (h : ℝ) * Complex.I, (mem_logBase_iff_height r hr _).mpr (by
    simpa only [Height, Set.mem_Ioi, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      zero_add, add_zero] using h.property)⟩

@[simp] theorem logPoint_re (r : ℝ) (hr : 0 < r) (t : ℝ) (h : Height r) :
    (logPoint r hr t h : ℂ).re = t := by
  simp [logPoint]

@[simp] theorem logPoint_im (r : ℝ) (hr : 0 < r) (t : ℝ) (h : Height r) :
    (logPoint r hr t h : ℂ).im = (h : ℝ) := by
  simp [logPoint]

/-- The logarithmic base is its genuine height half-line times the real axis. -/
def logBaseHeightHomeomorph (r : ℝ) (hr : 0 < r) : LogBase r ≃ₜ Height r × ℝ where
  toFun s := (⟨(s : ℂ).im, (mem_logBase_iff_height r hr s).mp s.property⟩, (s : ℂ).re)
  invFun p := logPoint r hr p.2 p.1
  left_inv s := by
    apply Subtype.ext
    apply Complex.ext <;> simp [logPoint]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact logPoint_im r hr p.2 p.1
    · exact logPoint_re r hr p.2 p.1
  continuous_toFun :=
    ((Complex.continuous_im.comp continuous_subtype_val).subtype_mk _).prodMk
      (Complex.continuous_re.comp continuous_subtype_val)
  continuous_invFun :=
    ((Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
        continuous_const)).subtype_mk _

@[simp] theorem logBaseHeightHomeomorph_fst (r : ℝ) (hr : 0 < r) (s : LogBase r) :
    ((logBaseHeightHomeomorph r hr s).1 : ℝ) = (s : ℂ).im := rfl

@[simp] theorem logBaseHeightHomeomorph_snd (r : ℝ) (hr : 0 < r) (s : LogBase r) :
    (logBaseHeightHomeomorph r hr s).2 = (s : ℂ).re := rfl

@[simp] theorem logBaseHeightHomeomorph_symm (r : ℝ) (hr : 0 < r) (p : Height r × ℝ) :
    (logBaseHeightHomeomorph r hr).symm p = logPoint r hr p.2 p.1 := rfl

theorem logPoint_translate (r : ℝ) (hr : 0 < r) (k : ℤ) (t : ℝ) (h : Height r) :
    logBaseTranslate r k (logPoint r hr t h) = logPoint r hr (t - (k : ℝ)) h := by
  apply Subtype.ext
  change (t : ℂ) + (h : ℝ) * Complex.I - (k : ℂ) =
    ((t - (k : ℝ) : ℝ) : ℂ) + (h : ℝ) * Complex.I
  push_cast
  ring

/-- Real period coordinates on the whole logarithmic family, not on a chosen fibre. -/
def familyCylinderHomeomorph (D : Data) :
    D.TotalSpace ≃ₜ Height D.radius × (ℝ × RealTorus₄) :=
  ((logBaseHeightHomeomorph D.radius D.radius_pos).prodCongr
    (Homeomorph.refl RealTorus₄)).trans
      (Homeomorph.prodAssoc (Height D.radius) ℝ RealTorus₄)

@[simp] theorem familyCylinderHomeomorph_time (D : Data) (x : D.TotalSpace) :
    (familyCylinderHomeomorph D x).2.1 = (x.1 : ℂ).re := rfl

@[simp] theorem familyCylinderHomeomorph_height (D : Data) (x : D.TotalSpace) :
    ((familyCylinderHomeomorph D x).1 : ℝ) = (x.1 : ℂ).im := rfl

@[simp] theorem familyCylinderHomeomorph_fibre (D : Data) (x : D.TotalSpace) :
    (familyCylinderHomeomorph D x).2.2 = x.2 := rfl

@[simp] theorem familyCylinderHomeomorph_symm (D : Data)
    (p : Height D.radius × (ℝ × RealTorus₄)) :
    (familyCylinderHomeomorph D).symm p =
      (logPoint D.radius D.radius_pos p.2.1 p.1, p.2.2) := rfl

/-- The proved clockwise cusp action is precisely the negative-time deck
action of the actual mapping torus with monodromy `M₀`. -/
theorem familyCylinderHomeomorph_smul (D : Data) (k : Multiplicative ℤ)
    (x : D.TotalSpace) :
    letI := D.totalAction
    familyCylinderHomeomorph D (k • x) =
      ((familyCylinderHomeomorph D x).1,
        MappingTorus.deck monodromy (-k.toAdd) (familyCylinderHomeomorph D x).2) := by
  let := D.totalAction
  apply Prod.ext
  · apply Subtype.ext
    change ((x.1 : ℂ) - (k.toAdd : ℂ)).im = (x.1 : ℂ).im
    simp
  · apply Prod.ext
    · change ((x.1 : ℂ) - (k.toAdd : ℂ)).re =
        (x.1 : ℂ).re + ((-k.toAdd : ℤ) : ℝ)
      simp [sub_eq_add_neg]
    · change cuspTorusHomeomorph k.toAdd x.2 = (monodromy ^ (-(-k.toAdd))) x.2
      rw [neg_neg, monodromy_zpow]

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp
