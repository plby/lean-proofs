module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ErdosProblems.Erdos515.External.Ray.Analytic.Defs
public import ErdosProblems.Erdos515.External.Ray.Manifold.Defs
public import ErdosProblems.Erdos515.External.Ray.Misc.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
## Dynamics definitions, allowing minimal public imports
-/

open Classical
open Filter (Tendsto atTop)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

/-
## Flat space definitions
-/

/-- `f` has a monic, superattracting fixed point of order `d ≥ 2` at the origin.
    This is a simplified version of `SuperNear` with no smallest requirements. -/
public structure SuperAt (f : ℂ → ℂ) (d : ℕ) : Prop where
  d2 : 2 ≤ d
  fa0 : AnalyticAt ℂ f 0
  fd : orderAt f 0 = d
  fc : leadingCoeff f 0 = 1

/-- `f` has a monic, superattracting fixed point of order `d ≥ 2` at the origin.
    We impose some smallness requirements to make bounds easier later. -/
public structure SuperNear (f : ℂ → ℂ) (d : ℕ) (t : Set ℂ) (a b : ℝ) :
    Prop extends SuperAt f d where
  o : IsOpen t
  t0 : (0 : ℂ) ∈ t
  t2 : ∀ {z}, z ∈ t → ‖z‖ ≤ a
  fa : AnalyticOnNhd ℂ f t
  ft : MapsTo f t t
  gs' : ∀ {z : ℂ}, z ≠ 0 → z ∈ t → ‖f z / z ^ d - 1‖ ≤ b
  a1 : a < 1
  b0 : 0 ≤ b
  b1 : b < 1
  c1' : a * (1 + b) < 1

/-- `SuperAt` everywhere on a parameter set `u`, at `z = 0` -/
public structure SuperAtC (f : ℂ → ℂ → ℂ) (d : ℕ) (u : Set ℂ) : Prop where
  o : IsOpen u
  s : ∀ {c}, c ∈ u → SuperAt (f c) d
  fa : ∀ {c}, c ∈ u → AnalyticAt ℂ (uncurry f) (c, 0)

/-- `SuperNear` everywhere on a parameter set -/
public structure SuperNearC (f : ℂ → ℂ → ℂ) (d : ℕ) (u : Set ℂ) (t : Set (ℂ × ℂ)) (a b : ℝ) :
    Prop where
  o : IsOpen t
  tc : ∀ {p : ℂ × ℂ}, p ∈ t → p.1 ∈ u
  s : ∀ {c}, c ∈ u → SuperNear (f c) d {z | (c, z) ∈ t} a b
  fa : AnalyticOnNhd ℂ (uncurry f) t

/-- `g` such that `f z = z^d * g z` -/
@[expose] public def g (f : ℂ → ℂ) (d : ℕ) : ℂ → ℂ := fun z ↦ if z = 0 then 1 else f z / z ^ d

/-- Terms in our infinite product -/
@[expose] public def term (f : ℂ → ℂ) (d n : ℕ) (z : ℂ) :=
  g f d (f^[n] z) ^ (1 / (d ^ (n + 1) : ℕ) : ℂ)

/-- With `term` in hand, we can define Böttcher coordinates -/
@[expose] public def bottcherNear (f : ℂ → ℂ) (d : ℕ) (z : ℂ) :=
  z * tprod fun n ↦ term f d n z

-- Scale factors for bounds
section Scale
variable {f : ℂ → ℂ} {d : ℕ} {t : Set ℂ} {a b : ℝ}
@[expose] public def SuperNear.c (_ : SuperNear f d t a b) := a * (1 + b)
@[expose] public def SuperNear.kt (_ : SuperNear f d t a b) : ℝ := psg b 2⁻¹ * b / 2
@[expose] public def SuperNear.k (s : SuperNear f d t a b) : ℝ := Real.exp (2 * s.kt)
end Scale

/-!
## Manifold definitions
-/

variable {S : Type} [TopologicalSpace S]
variable {f : ℂ → S → S} {a : S} {d : ℕ}

/-- `f` as `ℂ → ℂ → ℂ` in charts, with the attractor at `0` -/
@[expose] public def fl {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] (f : ℂ → S → S) (a : S) :
    ℂ → ℂ → ℂ :=
  fun c ↦
  (fun z ↦ z - extChartAt I a a) ∘
    (extChartAt I a ∘ f c ∘ (extChartAt I a).symm) ∘ fun z ↦ z + extChartAt I a a

variable [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]

/-- `z` tends to `a` under `f`-iteration -/
@[expose] public def Attracts (f : S → S) (z a : S) :=
  Tendsto (fun n ↦ f^[n] z) atTop (𝓝 a)

/-- `f c` has a monic superattracting fixpoint at `a`, for all `c` -/
public structure Super {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S]
    [IsManifold I ω S] (f : ℂ → S → S) (d : ℕ) (a : S) : Prop where
  d2 : 2 ≤ d
  fa : ContMDiff II I ω (uncurry f)
  f0 : ∀ c, f c a = a
  fd : ∀ c, orderAt (fl f a c) 0 = d
  fc : ∀ c, leadingCoeff (fl f a c) 0 = 1

/-- Potential is everywhere continuous only using an additional assumption.  The most general
    assumption is that the set of preimages is closed, but for the Mandelbrot set we have the
    simpler case that `a` is the only preimage of `a`. -/
public class OnePreimage (s : Super f d a) : Prop where
  eq_a : ∀ c z, f c z = a → z = a

/-- The basin of points that attract to `a` -/
@[expose] public def Super.basin (_ : Super f d a) : Set (ℂ × S) :=
  {p : ℂ × S | Tendsto (fun n ↦ (f p.1)^[n] p.2) atTop (𝓝 a)}

/-- `s.fl` is `fl` with a few arguments filled in -/
@[expose] public def Super.fl (_ : Super f d a) := _root_.fl f a

/-- `bottcherNear` on the manifold -/
@[expose] public def Super.bottcherNear (s : Super f d a) (c : ℂ) (z : S) : ℂ :=
  _root_.bottcherNear (s.fl c) d (extChartAt I a z - extChartAt I a a)

/-- `s.bottcherNear`, uncurried -/
@[expose] public def Super.bottcherNearp (s : Super f d a) : ℂ × S → ℂ :=
  uncurry s.bottcherNear

/-- `s.bottcherNear` after some iterations of `f` -/
@[expose] public def Super.bottcherNearIter (s : Super f d a) (n : ℕ) : ℂ → S → ℂ := fun c z ↦
  s.bottcherNear c ((f c)^[n] z)

/-!
## Potentials and postcritical potentials
-/

/-- `s.potential c z` measures how quickly `z` attracts to `a` under `f c`. -/
@[expose] public def Super.potential (s : Super f d a) (c : ℂ) (z : S) : ℝ :=
  if h : (c, z) ∈ s.basin ∧
    ∃ p : ℝ, 0 ≤ p ∧ ∀ᶠ n in atTop, ‖s.bottcherNear c ((f c)^[n] z)‖ = p ^ d ^ n
  then choose h.2 else 1

/-- The set of potentials of non-`a` critical points of `f c`, with 1 included.
    For compact `S` 1 is automatically a critical value, but we don't want to show this here. -/
@[expose] public def Super.ps (s : Super f d a) (c : ℂ) : Set ℝ :=
  {p | p = 1 ∨ p ≠ 0 ∧ ∃ z, s.potential c z = p ∧ Critical (f c) z}

/-- The critical potential: the least potential of any non-`a` critical point of `f c` -/
@[expose] public def Super.p (s : Super f d a) (c : ℂ) : ℝ :=
  sInf (s.ps c)

/-- `z : S` is postcritical if its potential is smaller than any critical point (except for `a`) -/
@[expose] public def Postcritical (s : Super f d a) (c : ℂ) (z : S) : Prop :=
  s.potential c z < s.p c

/-- The set of postcritical points -/
@[expose] public def Super.post (s : Super f d a) : Set (ℂ × S) :=
  {p : ℂ × S | Postcritical s p.1 p.2}

/-- The domain on which `s.ray` is well behaved: `{(c,z) | s.potential c z < s.p c}`. -/
@[expose] public def Super.ext (s : Super f d a) : Set (ℂ × ℂ) :=
  {y : ℂ × ℂ | ‖y.2‖ < s.p y.1}
