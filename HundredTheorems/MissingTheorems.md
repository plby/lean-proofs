# Missing theorems from Freek Wiedijk's list of 100 theorems

## Background

The Lean community / mathlib site features a page called [Missing
theorems from Freek Wiedijk's list of 100
theorems](https://leanprover-community.github.io/100-missing.html), as
well as a list of formalized results simply called [100
theorems](https://leanprover-community.github.io/100.html).

Both are based off of [Freek Wiedijk](https://www.cs.ru.nl/~freek/)'s
list of [100 theorems](https://www.cs.ru.nl/~freek/100/), which has
served as a benchmark for theorem provers.

As of the time of writing (2026/01/15), the "Missing theorems" page
says:

> These theorems are not yet formalized in Lean. Currently there are
  17 of them. Among these, 0 have their statement formalized.

This is not correct.  I
[attempted](https://github.com/leanprover-community/mathlib4/pull/33388)
to correct the information over on the [mathlib4
GitHub](https://github.com/leanprover-community/mathlib4/).
Eventually I realized it's just easier to do it here.  Below, I
collect some information that is known to me regarding the true state
of affairs.  For theorems that I indeed cannot find, I comment on why
they might be missing.  I do not promise that the information below is
up-to-date nor even correct, but the mathlib page isn't either.

## 8: The Impossibility of Trisecting the Angle and Doubling the Cube

This has been proven [in this repository](Theorem8.md) by Aristotle
(and ChatGPT).  The theorem is proven both as an algebraic statement
about constructible (algebraic) numbers, and as statements about ruler
and compass constructions in Euclidean geometry.

## 12: The Independence of the Parallel Postulate

## 13: Polyhedron Formula

Mathlib doesn't have
[polyhedra](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Polyhedra.20in.20mathlib/with/566539482).

One person [opened a
PR](https://jessealama.net/articles/towards-euler-polyhedron-formula-for-mathlib/)
for mathlib with their version of the polyhedron formula, but ended up
closing the PR.  One amusing (to me)
[discussion](https://leanprover.zulipchat.com/#narrow/channel/144837-PR-reviews/topic/.2329639/near/539974949)
topic raised was that in order to have greater generality, one could
work with the universal map from an abelian category to its
Grothendieck group.

## 21: Green’s Theorem

## 24. The Independence of the Continuum Hypothesis

This is **not** listed as missing, but is only
[available](https://github.com/flypitch/flypitch/blob/master/src/summary.lean)
in Lean 3.  This was known as the
[Flypitch](https://flypitch.github.io/) project.

## 28: Pascal’s Hexagon Theorem

This has been proven [in this repository](Theorem28.md) by Aristotle
(and ChatGPT).  The theorem is proven solely for a circle, as opposed
to a general conic section.

The [HOL Light statement](https://www.cs.ru.nl/~freek/100/hol.html#28)
linked by Freek Wiedijk is only for a circle (which informed the
choice of formalization here).  The [Rocq
statement](https://madiot.fr/rocq100/#28) is for the case of two
lines, which is usually known as Pappus's theorem.  The [Mizar
statement](https://mizar.uwb.edu.pl/100/#28) is for a conic section.

## 29: Feuerbach’s Theorem

## 31. Ramsey’s Theorem

This is **not** listed as missing, but maybe is only
[available](https://github.com/b-mehta/combinatorics/blob/extras/src/inf_ramsey.lean)
in Lean 3.  Presumably it would be easy to do in Lean 4.

## 32: The Four Color Problem

## 33: Fermat’s Last Theorem

This is indeed not yet proven, though the [Fermat's Last Theorem
project](https://github.com/ImperialCollegeLondon/FLT) is working on
it.

However, it is definitely incorrect to say that the statement has not
been formalized.  In fact, it's [in
mathlib](https://github.com/leanprover-community/mathlib4/blob/d4fd214aa75c2dd7572612411560f3060c743a0d/Mathlib/NumberTheory/FLT/Basic.lean#L58-L64)
as `FermatLastTheorem`.

## 36. Brouwer Fixed Point Theorem

This is **not** listed as missing, but maybe is only
[available](https://github.com/Shamrock-Frost/BrouwerFixedPoint/blob/master/src/brouwer_fixed_point.lean)
in Lean 3.

## 41: Puiseux’s Theorem

## 43: The Isoperimetric Theorem

## 47: The Central Limit Theorem

## 50: The Number of Platonic Solids

Mathlib doesn't have
[polyhedra](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Polyhedra.20in.20mathlib/with/566539482).

## 53: Pi is Transcendental

This is in a [PR to
mathlib](https://github.com/leanprover-community/mathlib4/pull/28013)
that has been in process since [August 22,
2023](https://github.com/leanprover-community/mathlib4/pull/6718).  In
particular, it has been formalized in Lean.

## 56: The Hermite-Lindemann Transcendence Theorem

This is in a [PR to
mathlib](https://github.com/leanprover-community/mathlib4/pull/28013)
that has been in process since [August 22,
2023](https://github.com/leanprover-community/mathlib4/pull/6718).  In
particular, it has been formalized in Lean.

## 67. e is Transcendental

This is **not** listed as missing, but the version
[linked](https://github.com/jjaassoonn/transcendental/blob/master/src/e_transcendental.lean)
is in Lean 3.

This is in a [PR to
mathlib](https://github.com/leanprover-community/mathlib4/pull/28013),
which unfortunately has been in process since [August 22,
2023](https://github.com/leanprover-community/mathlib4/pull/6718).
But in particular, it has been formalized in Lean 4.

## 84: Morley’s Theorem

This has been proven [in this repository](Theorem84.md) by Aristotle
(and ChatGPT).  The proof follows Conway's elementary proof.

## 87: Desargues’s Theorem

This has been proven [in this repository](Theorem87.md) by Aristotle
(and ChatGPT).  The setting is the Euclidean geometry of the plane.

## 92: Pick’s Theorem

Mathlib doesn't have
[polyhedra](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Polyhedra.20in.20mathlib/with/566539482),
or even polygons in the plane.

At least one person is [thinking
about](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Pick's.20Theorem)
working on Pick's theorem.

# Summary

Maybe 11 theorems or so are not yet formalized in Lean.  At least 1 of
these has its statement formalized.

At least 3 theorems not listed as missing are only available in Lean 3.
