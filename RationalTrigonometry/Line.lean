/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Defs
import RationalTrigonometry.Line.Null
import RationalTrigonometry.Line.Proportional
import RationalTrigonometry.Line.Parallel
import RationalTrigonometry.Line.Perpendicular
import RationalTrigonometry.Line.Incidence

/-!
# Lines and points in the affine plane

Foundations for rational trigonometry: the theory of lines and points over an
arbitrary field `K`. This file re-exports the development split across the
`RationalTrigonometry.Line.*` modules.

## Main definitions

* `Line K`: a line `a * x + b * y + c = 0` with the nondegeneracy condition `a ≠ 0 ∨ b ≠ 0`.
* `Line0 K`: a line through the origin (the `c = 0` case).
* `Point K`: a point in the affine plane.
* `Proportional`: two lines are proportional when their coefficients agree up to a nonzero scalar.
* `Parallel`: two lines are parallel when `a₁ * b₂ - a₂ * b₁ = 0`.
* `Perpendicular`: two lines are perpendicular when `a₁ * a₂ + b₁ * b₂ = 0`.
* `Null`: a line whose direction has zero quadrance, `a ^ 2 + b ^ 2 = 0`.
* `HasPoint`: a point lies on a line.
* `line_between`: the line through two distinct points.

## Main results

* `proportionalSetoid` / `parallelSetoid`: `Proportional` and `Parallel` are equivalence relations.
* `para_multiple`: parallel lines differ by a nonzero scalar on their leading coefficients.
* `line_between_uniq`: the line through two points is unique up to proportionality.
* `null_neg_one_square`: a null line forces `(b / a) ^ 2 = -1`, so null lines exist only when
  `-1` is a square in `K`.
-/
