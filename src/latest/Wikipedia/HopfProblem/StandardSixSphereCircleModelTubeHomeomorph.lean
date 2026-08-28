import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeBasic

/-!
# Open and closed tube parametrizations on the original standard sphere

The two parametrizations have the same literal Euclidean formula.  Their
inverses retain the normal coordinate and normalize the base coordinate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube

abbrev OpenDomain (r : ℝ) := BaseSphere × ↥(normalBall r)
abbrev ClosedDomain (r : ℝ) := BaseSphere × ↥(Metric.closedBall (0 : Normal) r)

theorem normalBall_norm_lt (r : ℝ) (y : ↥(normalBall r)) : ‖y.val‖ < r :=
  (mem_normalBall r y.val).mp y.property

theorem closedBall_norm_le (r : ℝ) (y : ↥(Metric.closedBall (0 : Normal) r)) : ‖y.val‖ ≤ r := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using y.property

def openForward (r : ℝ) (hr1 : r ≤ 1) (q : OpenDomain r) : ↥(openTube r) :=
  ⟨point q.1 q.2.val ((normalBall_norm_lt r q.2).le.trans hr1), by
    change ‖normal (ambient q.1 q.2.val)‖ < r
    rw [normal_ambient]
    exact normalBall_norm_lt r q.2⟩

def openInverse (r : ℝ) (hr1 : r ≤ 1) (p : ↥(openTube r)) : OpenDomain r :=
  (normalizedBase p.val (p.property.trans_le hr1),
    ⟨normal p.val.val, (mem_normalBall r _).mpr p.property⟩)

@[simp] theorem openForward_val_val (r : ℝ) (hr1 : r ≤ 1) (q : OpenDomain r) :
    (openForward r hr1 q).val.val = ambient q.1 q.2.val := rfl

@[simp] theorem openInverse_fst_val (r : ℝ) (hr1 : r ≤ 1) (p : ↥(openTube r)) :
    (openInverse r hr1 p).1.val = ‖base p.val.val‖⁻¹ • base p.val.val := rfl

@[simp] theorem openInverse_snd_val (r : ℝ) (hr1 : r ≤ 1) (p : ↥(openTube r)) :
    (openInverse r hr1 p).2.val = normal p.val.val := rfl

theorem openInverse_openForward (r : ℝ) (hr1 : r ≤ 1) (q : OpenDomain r) :
    openInverse r hr1 (openForward r hr1 q) = q := by
  apply Prod.ext
  · exact normalizedBase_point q.1 q.2.val ((normalBall_norm_lt r q.2).le.trans hr1)
      (by simpa only [normal_point] using (normalBall_norm_lt r q.2).trans_le hr1)
  · apply Subtype.ext
    exact normal_ambient q.1 q.2.val

theorem openForward_openInverse (r : ℝ) (hr1 : r ≤ 1) (p : ↥(openTube r)) :
    openForward r hr1 (openInverse r hr1 p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact ambient_normalizedBase p.val (p.property.trans_le hr1)

theorem continuous_openForward (r : ℝ) (hr1 : r ≤ 1) : Continuous (openForward r hr1) := by
  have hp : Continuous (fun q : OpenDomain r => (q.1, q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have ha : Continuous (fun q : OpenDomain r => ambient q.1 q.2.val) :=
    Continuous.comp (g := fun q : BaseSphere × Normal => ambient q.1 q.2)
      (f := fun q : OpenDomain r => (q.1, q.2.val)) continuous_ambient hp
  exact (ha.subtype_mk _).subtype_mk _

theorem continuous_openInverse (r : ℝ) (hr1 : r ≤ 1) : Continuous (openInverse r hr1) := by
  have hb : Continuous (fun p : ↥(openTube r) =>
      normalizedBase p.val (p.property.trans_le hr1)) :=
    continuous_normalizedBase Subtype.val continuous_subtype_val _
  have hn : Continuous (fun p : ↥(openTube r) => normal p.val.val) :=
    continuous_normal.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact hb.prodMk (hn.subtype_mk _)

/-- The actual open tube; the endpoint `r=1` is allowed and gives the full base-nonzero chart. -/
def openHomeomorph (r : ℝ) (hr1 : r ≤ 1) : OpenDomain r ≃ₜ ↥(openTube r) where
  toFun := openForward r hr1
  invFun := openInverse r hr1
  left_inv := openInverse_openForward r hr1
  right_inv := openForward_openInverse r hr1
  continuous_toFun := continuous_openForward r hr1
  continuous_invFun := continuous_openInverse r hr1

@[simp] theorem openHomeomorph_apply (r : ℝ) (hr1 : r ≤ 1) (q : OpenDomain r) :
    openHomeomorph r hr1 q = openForward r hr1 q := rfl

@[simp] theorem openHomeomorph_symm_apply (r : ℝ) (hr1 : r ≤ 1) (p : ↥(openTube r)) :
    (openHomeomorph r hr1).symm p = openInverse r hr1 p := rfl

@[simp] theorem openHomeomorph_symm_snd_val (r : ℝ) (hr1 : r ≤ 1) (p : ↥(openTube r)) :
    ((openHomeomorph r hr1).symm p).2.val = normal p.val.val := rfl

def closedForward (r : ℝ) (hr1 : r < 1) (q : ClosedDomain r) : ↥(closedTube r) :=
  ⟨point q.1 q.2.val ((closedBall_norm_le r q.2).trans hr1.le), by
    change ‖normal (ambient q.1 q.2.val)‖ ≤ r
    rw [normal_ambient]
    exact closedBall_norm_le r q.2⟩

def closedInverse (r : ℝ) (hr1 : r < 1) (p : ↥(closedTube r)) : ClosedDomain r :=
  (normalizedBase p.val (p.property.trans_lt hr1),
    ⟨normal p.val.val, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (show ‖normal p.val.val‖ ≤ r from p.property)⟩)

@[simp] theorem closedForward_val_val (r : ℝ) (hr1 : r < 1) (q : ClosedDomain r) :
    (closedForward r hr1 q).val.val = ambient q.1 q.2.val := rfl

@[simp] theorem closedInverse_fst_val (r : ℝ) (hr1 : r < 1) (p : ↥(closedTube r)) :
    (closedInverse r hr1 p).1.val = ‖base p.val.val‖⁻¹ • base p.val.val := rfl

@[simp] theorem closedInverse_snd_val (r : ℝ) (hr1 : r < 1) (p : ↥(closedTube r)) :
    (closedInverse r hr1 p).2.val = normal p.val.val := rfl

theorem closedInverse_closedForward (r : ℝ) (hr1 : r < 1) (q : ClosedDomain r) :
    closedInverse r hr1 (closedForward r hr1 q) = q := by
  apply Prod.ext
  · exact normalizedBase_point q.1 q.2.val ((closedBall_norm_le r q.2).trans hr1.le)
      (by simpa only [normal_point] using (closedBall_norm_le r q.2).trans_lt hr1)
  · apply Subtype.ext
    exact normal_ambient q.1 q.2.val

theorem closedForward_closedInverse (r : ℝ) (hr1 : r < 1) (p : ↥(closedTube r)) :
    closedForward r hr1 (closedInverse r hr1 p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact ambient_normalizedBase p.val (p.property.trans_lt hr1)

theorem continuous_closedForward (r : ℝ) (hr1 : r < 1) : Continuous (closedForward r hr1) := by
  have hp : Continuous (fun q : ClosedDomain r => (q.1, q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have ha : Continuous (fun q : ClosedDomain r => ambient q.1 q.2.val) :=
    Continuous.comp (g := fun q : BaseSphere × Normal => ambient q.1 q.2)
      (f := fun q : ClosedDomain r => (q.1, q.2.val)) continuous_ambient hp
  exact (ha.subtype_mk _).subtype_mk _

theorem continuous_closedInverse (r : ℝ) (hr1 : r < 1) : Continuous (closedInverse r hr1) := by
  have hb : Continuous (fun p : ↥(closedTube r) =>
      normalizedBase p.val (p.property.trans_lt hr1)) :=
    continuous_normalizedBase Subtype.val continuous_subtype_val _
  have hn : Continuous (fun p : ↥(closedTube r) => normal p.val.val) :=
    continuous_normal.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact hb.prodMk (hn.subtype_mk _)

/-- A homeomorphism onto the literal closed tube in the original sphere. -/
def closedHomeomorph (r : ℝ) (hr1 : r < 1) : ClosedDomain r ≃ₜ ↥(closedTube r) where
  toFun := closedForward r hr1
  invFun := closedInverse r hr1
  left_inv := closedInverse_closedForward r hr1
  right_inv := closedForward_closedInverse r hr1
  continuous_toFun := continuous_closedForward r hr1
  continuous_invFun := continuous_closedInverse r hr1

@[simp] theorem closedHomeomorph_apply (r : ℝ) (hr1 : r < 1) (q : ClosedDomain r) :
    closedHomeomorph r hr1 q = closedForward r hr1 q := rfl

@[simp] theorem closedHomeomorph_symm_apply (r : ℝ) (hr1 : r < 1)
    (p : ↥(closedTube r)) : (closedHomeomorph r hr1).symm p = closedInverse r hr1 p := rfl

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube
