import Wikipedia.NoExoticSixSphere.SymmetricDividedDifference
import Wikipedia.NoExoticSixSphere.EvenImplicitZeroChart

/-!
# Actual double points in midpoint and separation coordinates

For a map `(u,z) ↦ (u,h(u,z))`, equality of images forces the leading
coordinates to agree. Midpoint and signed half-separation then recover the
source pair exactly. The smooth divided difference vanishes at every point
in the closure of the actual off-diagonal double-point set.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FlatDoubleCurve

open SymmetricDifference

variable {U F : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def pair (q : (U × ℝ) × ℝ) : (U × ℝ) × (U × ℝ) :=
  ((q.1.1, q.1.2 + q.2), (q.1.1, q.1.2 - q.2))

def recover (r : (U × ℝ) × (U × ℝ)) : (U × ℝ) × ℝ :=
  ((r.1.1, (r.1.2 + r.2.2) / 2), (r.1.2 - r.2.2) / 2)

omit [FiniteDimensional ℝ U] [NormedSpace ℝ U] in
theorem continuous_pair : Continuous (pair (U := U)) :=
  (continuous_fst.fst.prodMk (continuous_fst.snd.add continuous_snd)).prodMk
    (continuous_fst.fst.prodMk (continuous_fst.snd.sub continuous_snd))

omit [FiniteDimensional ℝ U] [NormedSpace ℝ U] in
theorem continuous_recover : Continuous (recover (U := U)) :=
  (continuous_fst.fst.prodMk ((continuous_fst.snd.add continuous_snd.snd).div_const 2)).prodMk
    ((continuous_fst.snd.sub continuous_snd.snd).div_const 2)

omit [FiniteDimensional ℝ U] in
theorem contDiff_pair : ContDiff ℝ ∞ (pair (U := U)) :=
  (contDiff_fst.fst.prodMk (contDiff_fst.snd.add contDiff_snd)).prodMk
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.sub contDiff_snd))

omit [FiniteDimensional ℝ U] [NormedSpace ℝ U] [NormedAddCommGroup U] in
theorem recover_pair (q : (U × ℝ) × ℝ) : recover (pair q) = q := by
  rcases q with ⟨⟨u, m⟩, s⟩
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · dsimp [recover, pair]
      ring
  · dsimp [recover, pair]
    ring

omit [FiniteDimensional ℝ U] [NormedSpace ℝ U] [NormedAddCommGroup U] in
theorem pair_recover (r : (U × ℝ) × (U × ℝ)) (hr : r.1.1 = r.2.1) :
    pair (recover r) = r := by
  rcases r with ⟨⟨u, z⟩, ⟨v, w⟩⟩
  change u = v at hr
  subst v
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · dsimp [pair, recover]
      ring
  · apply Prod.ext
    · rfl
    · dsimp [pair, recover]
      ring

omit [FiniteDimensional ℝ U] [NormedSpace ℝ U] [NormedAddCommGroup U] in
theorem pair_distinct_iff (q : (U × ℝ) × ℝ) : (pair q).1 ≠ (pair q).2 ↔ q.2 ≠ 0 := by
  rcases q with ⟨⟨u, m⟩, s⟩
  constructor
  · intro h hs
    apply h
    change s = 0 at hs
    subst s
    simp [pair]
  · intro hs he
    have hreal : m + s = m - s := congrArg Prod.snd he
    apply hs
    linarith

def flatMap (h : U × ℝ → F) (q : U × ℝ) : U × F := (q.1, h q)

def doublePoints (h : U × ℝ → F) : Set ((U × ℝ) × (U × ℝ)) :=
  {r | r.1 ≠ r.2 ∧ flatMap h r.1 = flatMap h r.2}

omit [FiniteDimensional ℝ U] in
theorem pair_mem_doublePoints_iff (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    (q : (U × ℝ) × ℝ) :
    pair q ∈ doublePoints h ↔ q.2 ≠ 0 ∧ dividedDifference h q = 0 := by
  change (pair q).1 ≠ (pair q).2 ∧ flatMap h (pair q).1 = flatMap h (pair q).2 ↔ _
  rw [pair_distinct_iff]
  constructor
  · rintro ⟨hs, he⟩
    exact ⟨hs, (dividedDifference_zero_iff h hh q.1.1 q.1.2 q.2 hs).mpr
      (congrArg Prod.snd he)⟩
  · rintro ⟨hs, hz⟩
    exact ⟨hs, Prod.ext rfl ((dividedDifference_zero_iff h hh q.1.1 q.1.2 q.2 hs).mp hz)⟩

omit [FiniteDimensional ℝ U] [NormedSpace ℝ U]
  [CompleteSpace F] [NormedSpace ℝ F] [NormedAddCommGroup F] in
theorem closure_head_eq (h : U × ℝ → F) {r : (U × ℝ) × (U × ℝ)}
    (hr : r ∈ closure (doublePoints h)) : r.1.1 = r.2.1 := by
  apply closure_minimal (s := doublePoints h)
    (t := {r : (U × ℝ) × (U × ℝ) | r.1.1 = r.2.1}) ?_
    (isClosed_eq continuous_fst.fst continuous_snd.fst) hr
  intro q hq
  exact congrArg (fun z : U × F ↦ z.1) hq.2

omit [FiniteDimensional ℝ U] in
theorem recover_doublePoint_zero (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    {r : (U × ℝ) × (U × ℝ)} (hr : r ∈ doublePoints h) :
    dividedDifference h (recover r) = 0 := by
  have hp : pair (recover r) ∈ doublePoints h := by
    rw [pair_recover r (congrArg (fun z : U × F ↦ z.1) hr.2)]
    exact hr
  exact ((pair_mem_doublePoints_iff h hh (recover r)).mp hp).2

theorem recover_closure_zero (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    {r : (U × ℝ) × (U × ℝ)} (hr : r ∈ closure (doublePoints h)) :
    dividedDifference h (recover r) = 0 :=
  closure_minimal (fun _ hp ↦ recover_doublePoint_zero h hh hp)
    (isClosed_eq ((contDiff_dividedDifference h hh).continuous.comp continuous_recover)
      continuous_const) hr

def closedRecover (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h) :
    closure (doublePoints h) → {q : (U × ℝ) × ℝ // dividedDifference h q = 0} :=
  fun r ↦ ⟨recover r.val, recover_closure_zero h hh r.property⟩

theorem continuous_closedRecover (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h) :
    Continuous (closedRecover h hh) :=
  (continuous_recover.comp continuous_subtype_val).subtype_mk _

theorem pair_closedRecover (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    (r : closure (doublePoints h)) : pair (closedRecover h hh r).val = r.val :=
  pair_recover r.val (closure_head_eq h r.property)

end NoExoticSixSphere.FlatDoubleCurve
