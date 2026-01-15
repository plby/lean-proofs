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

Someone else tried the [constructible
numbers](https://github.com/Louis-Le-Grand/Formalisation-of-constructable-numbers)
version a couple years ago.

## 12: The Independence of the Parallel Postulate

Perhaps geometry has not been axiomatized.

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

This was done for a [rectangular box](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.23).

A more general version is lacking because mathlib doesn't have
differential forms.

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

For Mathlib, one person
[says](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Remaining.20100.20theorems/near/482189960)
"should be done first for projective spaces over arbitrary fields
(don't know if any complications arise for conics in characteristic 2)
with Euclidean versions only then following as a special case".

## 29: Feuerbach’s Theorem

Maybe the statement has been [formalized](https://meetings.ams.org/math/jmm2026/meetingapp.cgi/Paper/56671)?

## 31. Ramsey’s Theorem

This is **not** listed as missing, but maybe is only
[available](https://github.com/b-mehta/combinatorics/blob/extras/src/inf_ramsey.lean)
in Lean 3.  Presumably it would be easy to do in Lean 4.

## 32: The Four Color Problem

This has only been done in Rocq?  But Mathlib is also missing some
basic definitions.

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

[Quote](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Remaining.20100.20theorems/near/484400866):

> If you want it for power series, you'd better have mathlib being able of computing with them (Maria-Ines and I have a bunch of PR in this direction which are stuck by a redefinition of ring topologies…).
> You can have it for convergent series too, and then you need the inverse function theorem in the analytic category.
> Whatever point if view, some arguments require basics of Newton polygons."

## 43: The Isoperimetric Theorem

This is proven [here](https://github.com/hojonathanho/isoperimetric/)
by Jonathan Ho.  It is discussed on Zulip
[here](https://github.com/hojonathanho/isoperimetric/).

See also
[this](https://github.com/Brunn-Minkowski-in-Lean/BrunnMinkowski),
which hasn't had any updates in a while.  Other people tried working
on this back in
[2022](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Isoperimetric.20Inequality/with/560665680),
motivated by the 100 Theorems list.

## 47: The Central Limit Theorem

This has been [done](https://github.com/RemyDegenne/CLT) "for real
random variables".

## 50: The Number of Platonic Solids

Mathlib doesn't have
[polyhedra](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Polyhedra.20in.20mathlib/with/566539482).

## 53: Pi is Transcendental

This is in a [PR to
mathlib](https://github.com/leanprover-community/mathlib4/pull/28013)
that has been in process since [August 22,
2023](https://github.com/leanprover-community/mathlib4/pull/6718).  In
particular, it has been formalized in Lean.  Apparently it was not
added to the completed list years ago because a PR number is not a
["stable
reference"](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Remaining.20100.20theorems/near/483043532).

## 56: The Hermite-Lindemann Transcendence Theorem

This is in a [PR to
mathlib](https://github.com/leanprover-community/mathlib4/pull/28013)
that has been in process since [August 22,
2023](https://github.com/leanprover-community/mathlib4/pull/6718).  In
particular, it has been formalized in Lean.  Apparently it was not
added to the completed list years ago because a PR number is not a
["stable
reference"](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Remaining.20100.20theorems/near/483043532).

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

Someone else [ran
Aristotle](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Remaining.20100.20theorems/near/558907897),
too, but in a more general setting.

For Mathlib, one person
[says](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Remaining.20100.20theorems/near/482189960)
"should be done first for projective spaces over arbitrary fields
(don't know if any complications arise for conics in characteristic 2)
with Euclidean versions only then following as a special case".

## 92: Pick’s Theorem

Mathlib doesn't have
[polyhedra](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Polyhedra.20in.20mathlib/with/566539482),
or even polygons in the plane.

At least one person is [thinking
about](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Pick's.20Theorem)
working on Pick's theorem.

See also
[this](https://firsching.ch/FormalBook/blueprint/sect0013.html#pick_theorem).

# Summary

Maybe 9 theorems or so are not yet formalized in Lean:

* 12: The Independence of the Parallel Postulate
* 13: Polyhedron Formula
* 21: Green’s Theorem
* 29: Feuerbach’s Theorem
* 32: The Four Color Problem
* 33: Fermat’s Last Theorem
* 41: Puiseux’s Theorem
* 50: The Number of Platonic Solids
* 92: Pick’s Theorem

Maybe 1 or 2 of these have their statements formalized:

* 29: Feuerbach’s Theorem
* 33: Fermat’s Last Theorem

At least 3 theorems not listed as missing are only available in Lean
3:

* 24. The Independence of the Continuum Hypothesis
* 31. Ramsey’s Theorem
* 36. Brouwer Fixed Point Theorem
