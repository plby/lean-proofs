import Mathlib

/-!
# Scalar coordinates for the proper-rotation case

The two unit directions are `(c,s)` and `(d,-q)`.  This file contains only
real algebra; it makes no assumptions about planar regions.
-/

namespace Puzzling139335.ProperRotation

/-- The scalar coordinates of the two supported placements. -/
structure Data where
  c : ℝ
  s : ℝ
  d : ℝ
  q : ℝ
  a : ℝ
  b : ℝ
  u : ℝ
  v : ℝ
  w : ℝ
  z : ℝ

namespace Data

/-- Sine of the sum of the two acute direction angles. -/
def delta (p : Data) : ℝ := p.s * p.d + p.c * p.q

/-- Cosine of the sum of the two acute direction angles. -/
def cosSum (p : Data) : ℝ := p.c * p.d - p.s * p.q

/-- Numerator of the first unit-segment intersection parameter. -/
def ns (p : Data) : ℝ := p.q * (1 - p.u - p.w) - p.d * (p.v + p.z)

/-- Numerator of the second unit-segment intersection parameter. -/
def nt (p : Data) : ℝ := -p.s * (1 - p.u - p.w) - p.c * (p.v + p.z)

/-- Reflection of the source in its vertical midline, exchanging the placements. -/
def flip (p : Data) : Data where
  c := p.d
  s := p.q
  d := p.c
  q := p.s
  a := p.b
  b := p.a
  u := p.w - p.d
  v := -p.z - p.q
  w := p.u + p.c
  z := -p.v - p.s

@[simp] theorem delta_flip (p : Data) : p.flip.delta = p.delta := by
  dsimp [delta, flip]
  ring

@[simp] theorem cosSum_flip (p : Data) : p.flip.cosSum = p.cosSum := by
  dsimp [cosSum, flip]
  ring

@[simp] theorem ns_flip (p : Data) : p.flip.ns = p.delta - p.nt := by
  dsimp [ns, nt, delta, flip]
  ring

@[simp] theorem nt_flip (p : Data) : p.flip.nt = p.delta - p.ns := by
  dsimp [ns, nt, delta, flip]
  ring

@[simp] theorem flip_flip (p : Data) : p.flip.flip = p := by
  cases p
  simp [flip]

end Data

end Puzzling139335.ProperRotation
