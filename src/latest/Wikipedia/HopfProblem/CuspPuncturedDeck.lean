import Wikipedia.HopfProblem.CuspPeriodLattice

/-!
# Deck transformations on the logarithmic cusp cover

The integer change of logarithm and the four period translations form a
noncommutative group.  Its multiplication records the integral change of
the period matrix when the logarithm is increased by an integer.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace

@[simp] theorem exponential_add_int (s : ℂ) (k : ℤ) :
    exponential (s + k) = exponential s := by
  rw [exponential_add, exponential_int, mul_one]

theorem logarithmicPeriod_add_int (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (k : ℤ) :
    logarithmicPeriod C (s + k) =
      logarithmicPeriod C s + (k : ℂ) • B₀.map (Int.castRingHom ℂ) := by
  simp only [logarithmicPeriod, exponential_add_int, add_smul]
  abel

theorem logarithmicPeriod_mulVec_add_int (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (k : ℤ) (n : Fin 2 → ℤ) :
    logarithmicPeriod C (s + k) *ᵥ (fun i => (n i : ℂ)) =
      logarithmicPeriod C s *ᵥ (fun i => (n i : ℂ)) +
        fun i => (k : ℂ) * (cuspVector n i : ℂ) := by
  ext i
  simp only [Pi.add_apply, logarithmicPeriod_apply, exponential_add_int]
  ring

/-- A logarithmic shift together with two integral pairs of period coefficients. -/
@[ext] structure LogDeck where
  k : ℤ
  m : Fin 2 → ℤ
  n : Fin 2 → ℤ
  deriving DecidableEq

namespace LogDeck

instance : One LogDeck := ⟨⟨0, 0, 0⟩⟩

instance : Mul LogDeck := ⟨fun g h =>
  ⟨g.k + h.k, g.m + h.m + h.k • cuspVector g.n, g.n + h.n⟩⟩

instance : Inv LogDeck := ⟨fun g =>
  ⟨-g.k, -g.m + g.k • cuspVector g.n, -g.n⟩⟩

@[simp] theorem one_k : (1 : LogDeck).k = 0 := rfl
@[simp] theorem one_m : (1 : LogDeck).m = 0 := rfl
@[simp] theorem one_n : (1 : LogDeck).n = 0 := rfl
@[simp] theorem mul_k (g h : LogDeck) : (g * h).k = g.k + h.k := rfl
@[simp] theorem mul_m (g h : LogDeck) :
    (g * h).m = g.m + h.m + h.k • cuspVector g.n := rfl
@[simp] theorem mul_n (g h : LogDeck) : (g * h).n = g.n + h.n := rfl
@[simp] theorem inv_k (g : LogDeck) : g⁻¹.k = -g.k := rfl
@[simp] theorem inv_m (g : LogDeck) :
    g⁻¹.m = -g.m + g.k • cuspVector g.n := rfl
@[simp] theorem inv_n (g : LogDeck) : g⁻¹.n = -g.n := rfl

instance : Group LogDeck where
  mul_assoc g h l := by
    apply LogDeck.ext
    · simp only [mul_k, add_assoc]
    · simp only [mul_m, mul_k, mul_n, cuspVector_add, smul_add, add_smul]
      abel
    · simp only [mul_n, add_assoc]
  one_mul g := by
    apply LogDeck.ext <;> simp
  mul_one g := by
    apply LogDeck.ext <;> simp
  inv_mul_cancel g := by
    apply LogDeck.ext
    · simp
    · ext i
      fin_cases i <;> simp [cuspVector]
    · simp

end LogDeck

/-- The explicit transformation on the logarithmic cover. -/
def logDeckTransform (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (g : LogDeck) (x : ℂ × ComplexPlane₂) : ℂ × ComplexPlane₂ :=
  (x.1 + g.k, x.2 + (fun i => (g.m i : ℂ)) +
    logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)))

@[simp] theorem logDeckTransform_fst (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (g : LogDeck) (x : ℂ × ComplexPlane₂) :
    (logDeckTransform C g x).1 = x.1 + g.k := rfl

@[simp] theorem logDeckTransform_snd (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (g : LogDeck) (x : ℂ × ComplexPlane₂) :
    (logDeckTransform C g x).2 = x.2 + (fun i => (g.m i : ℂ)) +
      logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)) := rfl

@[simp] theorem logDeckTransform_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (x : ℂ × ComplexPlane₂) : logDeckTransform C 1 x = x := by
  apply Prod.ext
  · simp [logDeckTransform]
  · ext i
    simp [logDeckTransform, Matrix.mulVec, dotProduct]

theorem logDeckTransform_mul (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (g h : LogDeck) (x : ℂ × ComplexPlane₂) :
    logDeckTransform C (g * h) x = logDeckTransform C g (logDeckTransform C h x) := by
  apply Prod.ext
  · simp only [logDeckTransform_fst, LogDeck.mul_k, Int.cast_add]
    ring
  · ext i
    simp only [logDeckTransform_snd, logDeckTransform_fst, LogDeck.mul_m, LogDeck.mul_n,
      logarithmicPeriod_mulVec_add_int, Pi.add_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_id]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- The action includes logarithmic monodromy as well as all period translations. -/
@[instance_reducible] def logDeckAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) :
    MulAction LogDeck (ℂ × ComplexPlane₂) where
  smul := logDeckTransform C
  one_smul := logDeckTransform_one C
  mul_smul := logDeckTransform_mul C

theorem logDeckAction_smul (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (g : LogDeck) (x : ℂ × ComplexPlane₂) :
    letI := logDeckAction C
    g • x = (x.1 + g.k, x.2 + (fun i => (g.m i : ℂ)) +
      logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ))) := rfl

@[simp] theorem exponential_logDeckTransform_fst
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g : LogDeck) (x : ℂ × ComplexPlane₂) :
    exponential (logDeckTransform C g x).1 = exponential x.1 := by
  simp

/-- Nondegeneracy of the imaginary period matrix makes the action free at a point. -/
theorem logDeckTransform_eq_self_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g : LogDeck) (x : ℂ × ComplexPlane₂)
    (hP : Function.Bijective ((logarithmicPeriod C x.1).map Complex.im).mulVecLin) :
    logDeckTransform C g x = x ↔ g = 1 := by
  constructor
  · intro hx
    have hk : g.k = 0 := by
      have he := congrArg Prod.fst hx
      have he' : (g.k : ℂ) = 0 := by
        simpa only [logDeckTransform_fst, add_eq_left] using he
      exact_mod_cast he'
    let p : FullPeriodMatrix := ⟨logarithmicPeriod C x.1, hP⟩
    have he : p.periodLinear ((fun i => (g.m i : ℝ)), fun i => (g.n i : ℝ)) =
        p.periodLinear 0 := by
      have hs : (fun i => (g.m i : ℂ)) +
          logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)) = 0 := by
        have hs := congrArg Prod.snd hx
        simpa only [logDeckTransform_snd, add_assoc, add_eq_left] using hs
      rw [map_zero]
      ext i
      simpa [FullPeriodMatrix.periodLinear, p] using congrFun hs i
    have he' := p.periodLinear_bijective.injective he
    apply LogDeck.ext hk
    · ext i
      have hm := congrFun (congrArg Prod.fst he') i
      change (g.m i : ℝ) = 0 at hm
      change g.m i = 0
      exact_mod_cast hm
    · ext i
      have hn := congrFun (congrArg Prod.snd he') i
      change (g.n i : ℝ) = 0 at hn
      change g.n i = 0
      exact_mod_cast hn
  · rintro rfl
    exact logDeckTransform_one C x

end Wikipedia.HopfProblem.CuspUniformization
