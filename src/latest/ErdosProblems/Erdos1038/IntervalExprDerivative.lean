import ErdosProblems.Erdos1038.OneCutIntervalExpr

/-!
# Symbolic directional derivatives for interval expressions

This file differentiates the small expression language used by the one-cut
certificate.  The theorem is semantic: whenever the coordinate curves have
the derivatives specified by `d`, the recursively generated expression is
the derivative of the original expression along those curves.
-/

namespace Erdos1038

noncomputable section

namespace IntervalExpr

def directional {n : Nat} (d : Fin n → IntervalExpr n) :
    IntervalExpr n → IntervalExpr n
  | .rat _ => .rat 0
  | .var i => d i
  | .add a b => .add (directional d a) (directional d b)
  | .neg a => .neg (directional d a)
  | .mul a b =>
      .add (.mul (directional d a) b) (.mul a (directional d b))
  | .inv a => .neg (.div (directional d a) (.sq a))
  | .log _ a => .div (directional d a) a
  | .log2Shift _ _ a => .div (directional d a) a

def RegularAt {n : Nat} (x : Fin n → ℝ) : IntervalExpr n → Prop
  | .rat _ => True
  | .var _ => True
  | .add a b => RegularAt x a ∧ RegularAt x b
  | .neg a => RegularAt x a
  | .mul a b => RegularAt x a ∧ RegularAt x b
  | .inv a => RegularAt x a ∧ evalReal x a ≠ 0
  | .log _ a => RegularAt x a ∧ evalReal x a ≠ 0
  | .log2Shift _ _ a => RegularAt x a ∧ evalReal x a ≠ 0

private theorem inv_arg_ne_zero {A J : RatInterval} {x : ℝ}
    (hx : A.Contains x) (h : A.inv? = some J) : x ≠ 0 := by
  by_cases hsign : 0 < A.lo ∨ A.hi < 0
  · rcases hsign with hlo | hhi
    · have hlo' : (0 : ℝ) < (A.lo : ℝ) := by exact_mod_cast hlo
      exact (hlo'.trans_le hx.1).ne'
    · have hhi' : (A.hi : ℝ) < 0 := by exact_mod_cast hhi
      exact (hx.2.trans_lt hhi').ne
  · simp [RatInterval.inv?, hsign] at h

private theorem log_arg_pos {terms : Nat} {A J : RatInterval} {x : ℝ}
    (hx : A.Contains x) (h : A.log? terms = some J) : 0 < x := by
  by_cases hlo : 0 < A.lo
  · have hlo' : (0 : ℝ) < (A.lo : ℝ) := by exact_mod_cast hlo
    exact hlo'.trans_le hx.1
  · simp [RatInterval.log?, hlo] at h

private theorem log2Shift_arg_pos {terms shift : Nat}
    {A J : RatInterval} {x : ℝ} (hx : A.Contains x)
    (h : log2ShiftInterval terms shift A = some J) : 0 < x := by
  let p : Rat := (2 : Rat) ^ shift
  let scaled := RatInterval.mul (RatInterval.point p) A
  cases hscaled : RatInterval.log? terms scaled with
  | none => simp [log2ShiftInterval, p, scaled, hscaled] at h
  | some L =>
      cases htwo : RatInterval.log? terms (RatInterval.point 2) with
      | none => simp [log2ShiftInterval, p, scaled, hscaled, htwo] at h
      | some T =>
          have hscaledContains : scaled.Contains ((p : ℝ) * x) :=
            RatInterval.mul_contains (RatInterval.point_contains p) hx
          have hscaledLo : (0 : Rat) < scaled.lo := by
            by_cases hlo : (0 : Rat) < scaled.lo
            · exact hlo
            · simp [RatInterval.log?, hlo] at hscaled
          have hprod : 0 < (p : ℝ) * x := by
            have hlo : (0 : ℝ) < (scaled.lo : ℝ) := by
              exact_mod_cast hscaledLo
            exact hlo.trans_le hscaledContains.1
          have hp : 0 < (p : ℝ) := by
            dsimp [p]
            positivity
          exact (mul_pos_iff.mp hprod).resolve_right (by
            intro hneg
            exact (not_lt_of_ge hp.le) hneg.1) |>.2

theorem regularAt_of_evalInterval {n : Nat} {X : Fin n → RatInterval}
    {x : Fin n → ℝ} {e : IntervalExpr n} {I : RatInterval}
    (hordered : ∀ i, (X i).Ordered)
    (hcontains : ∀ i, (X i).Contains (x i))
    (h : evalInterval X e = some I) : RegularAt x e := by
  induction e generalizing I with
  | rat r => trivial
  | var i => trivial
  | add a b iha ihb =>
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at h
      | some A =>
          cases hb : evalInterval X b with
          | none => simp [evalInterval, ha, hb] at h
          | some B => exact ⟨iha ha, ihb hb⟩
  | neg a ih =>
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at h
      | some A => exact ih ha
  | mul a b iha ihb =>
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at h
      | some A =>
          cases hb : evalInterval X b with
          | none => simp [evalInterval, ha, hb] at h
          | some B => exact ⟨iha ha, ihb hb⟩
  | inv a ih =>
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at h
      | some A =>
          have hinv : A.inv? = some I := by
            simpa [evalInterval, ha] using! h
          have hAx := (evalInterval_sound hordered hcontains a A ha).2
          exact ⟨ih ha, inv_arg_ne_zero hAx hinv⟩
  | log terms a ih =>
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at h
      | some A =>
          have hlog : A.log? terms = some I := by
            simpa [evalInterval, ha] using! h
          have hAx := (evalInterval_sound hordered hcontains a A ha).2
          exact ⟨ih ha, (log_arg_pos hAx hlog).ne'⟩
  | log2Shift terms shift a ih =>
      cases ha : evalInterval X a with
      | none => simp [evalInterval, ha] at h
      | some A =>
          have hlog : log2ShiftInterval terms shift A = some I := by
            simpa [evalInterval, ha] using! h
          have hAx := (evalInterval_sound hordered hcontains a A ha).2
          exact ⟨ih ha, (log2Shift_arg_pos hAx hlog).ne'⟩

theorem hasDerivAt_evalReal_directional {n : Nat}
    (d : Fin n → IntervalExpr n) (e : IntervalExpr n)
    {x : Fin n → ℝ} {curve : ℝ → Fin n → ℝ} {t : ℝ}
    (hcurve : ∀ i, HasDerivAt (fun s ↦ curve s i)
      (evalReal x (d i)) t)
    (hvalue : curve t = x) (hreg : RegularAt x e) :
    HasDerivAt (fun s ↦ evalReal (curve s) e)
      (evalReal x (directional d e)) t := by
  induction e with
  | rat r => simpa [evalReal, directional] using! hasDerivAt_const t (r : ℝ)
  | var i =>
      simpa [evalReal, directional, congrFun hvalue i] using! hcurve i
  | add a b iha ihb =>
      simpa [evalReal, directional] using!
        (iha hreg.1).add (ihb hreg.2)
  | neg a ih =>
      simpa [evalReal, directional] using! (ih hreg).neg
  | mul a b iha ihb =>
      simpa [evalReal, directional, hvalue] using!
        (iha hreg.1).mul (ihb hreg.2)
  | inv a ih =>
      have hne : evalReal (curve t) a ≠ 0 := by
        simpa [hvalue] using! hreg.2
      have hderiv := (ih hreg.1).inv hne
      convert! hderiv using 1
      simp only [evalReal, directional, div, sq]
      rw [hvalue]
      field_simp [hreg.2]
  | log terms a ih =>
      have hne : evalReal (curve t) a ≠ 0 := by
        simpa [hvalue] using! hreg.2
      have hderiv := (ih hreg.1).log hne
      simpa [evalReal, directional, div, hvalue] using! hderiv
  | log2Shift terms shift a ih =>
      have hne : evalReal (curve t) a ≠ 0 := by
        simpa [hvalue] using! hreg.2
      have hderiv := (ih hreg.1).log hne
      simpa [evalReal, directional, div, hvalue] using! hderiv

end IntervalExpr

end

end Erdos1038
